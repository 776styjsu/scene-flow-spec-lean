# scene-flow-spec-lean

## Check my_test_data Against Current Properties

This repo now includes a data adapter that reads `my_test_data/data/rsv/*.pkl`
and `my_test_data/data/ego_logs.json`, generates a Lean trace module, and runs
the existing properties from `SceneFlowSpec.Examples`.

### One-time Python dependencies

```bash
python -m pip install networkx shapely
```

### Run the checker

```bash
python scripts/check_my_test_data.py
```

This generates `SceneFlowSpec/GeneratedTrace.lean` and runs:

- `yieldAtIntersection`
- `safeFollowingDistance`
- `oppLaneClear`

using `lake env lean`.

### Generate only (no Lean run)

```bash
python scripts/check_my_test_data.py --no-run
```