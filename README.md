# scene-flow-spec-lean

Formalized finite-trace scene-flow monitoring in Lean 4.

This project encodes driving-scene safety properties as temporal formulas,
evaluates them on finite traces, and includes mechanized metatheory in Lean.
It also provides a data pipeline that converts RSV graph frames plus ego logs
into a generated Lean trace and runs the monitor on real sample data.

This repository is a quick prototype to see Lean 4's capabilities for this domain. For
the original work that inspired this, see the SGSM & SceneFlowLang projects:
- https://github.com/less-lab-uva/SGSM
- https://github.com/less-lab-uva/SceneFlowLang

## What this repository runs

- Lean specification and semantics in `SceneFlowSpec/*.lean`
- Example properties in `SceneFlowSpec/Examples.lean`
- Theorem proofs in `SceneFlowSpec/Theorems.lean`
- Data adapter/checker in `scripts/run_sceneflow_checks.py`

## Prerequisites

### Lean toolchain

The project is pinned by `lean-toolchain` to Lean `v4.28.0`.

Install Lean/Lake via elan if needed:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Then in this repo:

```bash
lake update
lake build
```

### Python dependencies

Required by the data adapter:

```bash
conda env create -f environment.yml
conda activate scene-flow-spec-lean
```

## How to run

### 1. Run Lean examples/proofs directly

Build/check the Lean project:

```bash
lake build
```

Run evaluators embedded in example files:

```bash
lake env lean SceneFlowSpec/Examples.lean
lake env lean SceneFlowSpec/Theorems.lean
```

### 2. Run the generated-trace pipeline (sample data)

From repo root:

```bash
python scripts/run_sceneflow_checks.py
```

This command:

1. Reads `sceneflow_sample/data/rsv/*.pkl` and `sceneflow_sample/data/ego_logs.json`.
2. Generates `SceneFlowSpec/GeneratedTrace.lean`.
3. Runs `lake env lean` on that generated file.

The generated run checks these current properties:

- `yieldAtIntersection`
- `safeFollowingDistance`
- `oppLaneClear`

### 3. Useful options

Generate only (skip Lean execution):

```bash
python scripts/run_sceneflow_checks.py --no-run
```

Use a different input dataset directory:

```bash
python scripts/run_sceneflow_checks.py --data-dir path/to/data
```

Write generated Lean to a custom output path:

```bash
python scripts/run_sceneflow_checks.py --output SceneFlowSpec/GeneratedTrace.lean
```