# Build Instructions

These instructions reproduce both the Lean artifact and the paper PDF.

## Requirements

- `elan`
- Lean toolchain `leanprover/lean4:v4.29.0-rc6`
- `lake`
- `tectonic`

The project pins Mathlib to commit:

`1f3cdaa7a7f82a2e521d285b11e261110e1e1962`

## Lean Build

From this directory:

```bash
cd /path/to/buildingup/paper_submission
~/.elan/bin/lake update
~/.elan/bin/lake build
```

To typecheck the single Lean file directly:

```bash
cd /path/to/buildingup/paper_submission
~/.elan/bin/lake env lean BuildingUpFormalization.lean
```

## PDF Build

```bash
cd /path/to/buildingup/paper_submission
/opt/homebrew/bin/tectonic paper.tex
```

This produces:

- `paper.pdf`

## Optional AXLE Verification

If AXLE access is configured, the artifact can also be checked using:

```bash
python3 /path/to/scripts/axle_tools.py --dotenv /path/to/.env check BuildingUpFormalization.lean
```

Targeted theorem verification can be run with:

```bash
python3 /path/to/scripts/axle_tools.py --dotenv /path/to/.env verify-theorem BuildingUpFormalization.lean --name paper_binary_cz_kim_equivalence
python3 /path/to/scripts/axle_tools.py --dotenv /path/to/.env verify-theorem BuildingUpFormalization.lean --name paper_qary_building_up_rebuild
python3 /path/to/scripts/axle_tools.py --dotenv /path/to/.env verify-theorem BuildingUpFormalization.lean --name paper_qary_building_up_forward_self_dual
python3 /path/to/scripts/axle_tools.py --dotenv /path/to/.env verify-theorem BuildingUpFormalization.lean --name paper_split_boxed_form_forward_core
python3 /path/to/scripts/axle_tools.py --dotenv /path/to/.env verify-theorem BuildingUpFormalization.lean --name paper_conditional_split_boxed_normalization_core
```

## Expected Outputs

- Lean file builds without `sorry`
- `paper.pdf` renders successfully
- AXLE whole-file check reports:
  - `okay: true`
  - `failed_declarations: []`
