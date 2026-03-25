#!/usr/bin/env python3
"""Convert my_test_data RSV + ego logs into a Lean Trace and run property checks.

This mirrors the original SceneFlow pipeline idea (frame-wise scene-graph monitoring),
but targets this Lean monitor by generating a Lean module from RSV pickle frames.
"""

from __future__ import annotations

import argparse
import json
import pickle
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any


@dataclass(eq=False)
class SimpleNode:
    name: str
    base_class: str | None = None
    attr: dict[str, Any] | None = None

    def __repr__(self) -> str:
        return str(self.name)


class SGUnpickler(pickle.Unpickler):
    """Compatible unpickler for SceneFlow RSV files."""

    def persistent_load(self, pid: Any) -> Any:
        if pid == "please_ignore_me":
            return None
        return super().persistent_load(pid)

    def find_class(self, module: str, name: str) -> Any:
        if (module, name) in {
            ("__main__", "Node"),
            ("carla_sgg.sgg_abstractor", "Node"),
        }:
            return SimpleNode
        return super().find_class(module, name)


REL_LABEL_MAP: dict[str, str] = {
    "isIn": ".isIn",
    "toLeftOf": ".toLeftOf",
    "toRightOf": ".toRightOf",
    "opposes": ".opposes",
    "near": ".near",
    "controlsTrafficOf": ".controls",
    "laneChange": ".laneChange",
    "sameDirection": ".sameDirection",
    "inDFrontOf": ".inFrontOf",
    "inSFrontOf": ".inFrontOf",
    "atDRearOf": ".behind",
    "atSRearOf": ".behind",
}

VEHICLE_TOKENS = {
    "ego",
    "car",
    "truck",
    "van",
    "bus",
    "motorcycle",
    "vehicle",
}


def natural_sort_key(name: str) -> list[Any]:
    return [int(tok) if tok.isdigit() else tok.lower() for tok in re.split(r"(\d+)", name)]


def lean_string(s: str) -> str:
    return s.replace("\\", "\\\\").replace('"', '\\"')


def infer_entity_type(node_name: str, base_class: str | None, sem_class: str | None) -> str:
    text = f"{node_name} {base_class or ''} {sem_class or ''}".lower()

    if any(tok in text for tok in VEHICLE_TOKENS):
        return ".vehicle"
    if "lane" in text:
        return ".lane"
    if "junction" in text:
        return ".junction"
    if "pedestrian" in text or "walker" in text:
        return ".pedestrian"
    if "bicycle" in text or "bike" in text:
        return ".bicycle"
    if "sign" in text or "traffic_light" in text or "stop" in text:
        return ".sign"
    return ".other"


def load_graph(path: Path):
    with path.open("rb") as f:
        return SGUnpickler(f).load()


def build_lean_module(data_dir: Path, output_file: Path) -> tuple[int, int]:
    rsv_dir = data_dir / "rsv"
    ego_logs_path = data_dir / "ego_logs.json"

    if not rsv_dir.exists():
        raise FileNotFoundError(f"RSV folder not found: {rsv_dir}")
    if not ego_logs_path.exists():
        raise FileNotFoundError(f"ego_logs.json not found: {ego_logs_path}")

    ego_logs = json.loads(ego_logs_path.read_text())["records"]

    rsv_files = sorted([p for p in rsv_dir.glob("*.pkl")], key=lambda p: natural_sort_key(p.name))
    if not rsv_files:
        raise ValueError(f"No .pkl files found in {rsv_dir}")

    node_id: dict[str, int] = {}
    node_meta: dict[str, dict[str, Any]] = {}
    next_id = 1

    frame_blocks: list[str] = []
    unmapped_labels: dict[str, int] = {}

    for frame_index, pkl in enumerate(rsv_files):
        g = load_graph(pkl)

        frame_nodes: dict[str, Any] = {}
        for n in g.nodes:
            n_name = getattr(n, "name", str(n))
            frame_nodes[n_name] = n
            if n_name not in node_id:
                node_id[n_name] = next_id
                next_id += 1
            if n_name not in node_meta:
                attr = getattr(n, "attr", {}) or {}
                node_meta[n_name] = {
                    "base_class": getattr(n, "base_class", None),
                    "sem_class": attr.get("sem_class"),
                }

        entities_src: list[str] = []
        for n_name in sorted(frame_nodes.keys(), key=natural_sort_key):
            n = frame_nodes[n_name]
            attr = getattr(n, "attr", {}) or {}
            sem_class = attr.get("sem_class")
            e_ty = infer_entity_type(n_name, getattr(n, "base_class", None), sem_class)

            attrs: list[tuple[str, str]] = [("name", str(n_name))]
            if sem_class is not None:
                attrs.append(("sem_class", str(sem_class)))

            if str(n_name).lower() == "ego" and frame_index < len(ego_logs):
                rec = ego_logs[frame_index]
                attrs.extend(
                    [
                        ("speed", str(rec["state"]["velocity"]["value"])),
                        ("accel", str(rec["state"]["acceleration"]["value"])),
                        ("throttle", str(rec["control"]["throttle"])),
                        ("brake", str(rec["control"]["brake"])),
                        ("steer", str(rec["control"]["steer"])),
                    ]
                )

            attrs_lean = ", ".join([f"(\"{lean_string(k)}\", \"{lean_string(v)}\")" for k, v in attrs])
            entities_src.append(f"mkEntity {node_id[n_name]} {e_ty} [{attrs_lean}]")

        rel_src: list[str] = []
        for u, v, d in g.edges(data=True):
            src_name = getattr(u, "name", str(u))
            tgt_name = getattr(v, "name", str(v))

            raw_label = d.get("label") if isinstance(d, dict) else None
            raw_label = str(raw_label) if raw_label is not None else ""
            mapped = REL_LABEL_MAP.get(raw_label)
            if mapped is None:
                unmapped_labels[raw_label] = unmapped_labels.get(raw_label, 0) + 1
                continue

            rel_src.append(
                f"mkRel {node_id[src_name]} {mapped} {node_id[tgt_name]}"
            )

        frame_block = (
            "    { entities := [" + ", ".join(entities_src) + "],\n"
            "      relations := [" + ", ".join(rel_src) + "] }"
        )
        frame_blocks.append(frame_block)

    lean_lines: list[str] = [
        "/- Generated by scripts/check_my_test_data.py. Do not edit manually. -/",
        "import SceneFlowSpec.Examples",
        "",
        "namespace SceneFlowSpec",
        "",
        "/-- Trace generated from sceneflow_sample/data/rsv with ego attributes from ego_logs.json. -/",
        "def generatedTrace : Trace := [",
        ",\n".join(frame_blocks),
        "]",
        "",
        "/-- Reuse current example properties on generated real-world trace. -/",
        "def generatedProperties : List NamedProperty := [",
        "  yieldAtIntersection,",
        "  safeFollowingDistance,",
        "  oppLaneClear",
        "]",
        "",
        "#eval checkAll generatedTrace generatedProperties",
        "",
        "end SceneFlowSpec",
        "",
    ]

    output_file.parent.mkdir(parents=True, exist_ok=True)
    output_file.write_text("\n".join(lean_lines))

    if unmapped_labels:
        print("Unmapped RSV relation labels (ignored):")
        for k, v in sorted(unmapped_labels.items(), key=lambda x: x[0]):
            label = k if k else "<empty>"
            print(f"  {label}: {v}")

    return len(rsv_files), len(node_id)


def run_lean_check(workspace_root: Path, lean_file: Path) -> int:
    cmd = ["lake", "env", "lean", str(lean_file)]
    proc = subprocess.run(cmd, cwd=workspace_root, capture_output=True, text=True)

    if proc.stdout:
        print(proc.stdout)
    if proc.stderr:
        print(proc.stderr)

    return proc.returncode


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate and check Lean trace from my_test_data")
    parser.add_argument(
        "--data-dir",
        type=Path,
        default=Path("sceneflow_sample/data"),
        help="Directory containing rsv/ and ego_logs.json",
    )
    parser.add_argument(
        "--output",
        type=Path,
        default=Path("SceneFlowSpec/GeneratedTrace.lean"),
        help="Lean output file to generate",
    )
    parser.add_argument(
        "--no-run",
        action="store_true",
        help="Only generate Lean file; do not invoke lake env lean",
    )

    args = parser.parse_args()
    workspace_root = Path.cwd()

    try:
        n_frames, n_entities = build_lean_module(args.data_dir, args.output)
    except Exception as e:  # pragma: no cover
        print(f"Failed to generate Lean trace: {e}")
        return 1

    print(f"Generated {args.output} from {n_frames} frames with {n_entities} unique entities.")

    if args.no_run:
        return 0

    rc = run_lean_check(workspace_root, args.output)
    if rc != 0:
        print("Lean check failed. You can inspect the generated file and rerun manually.")
        return rc

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
