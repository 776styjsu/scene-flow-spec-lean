# Project Report (March 24, 2026)

The aim of this project is to formalize key scene-flow safety requirements for autonomous driving in Lean, so that traffic-scenario rules are specified with precise temporal semantics rather than informal prose. The core idea is to represent driving scenes as finite traces and evaluate temporal formulas over those traces, enabling repeatable and unambiguous property checking.

The current state is a working end-to-end prototype. The codebase defines a scene model, formula language, and monitor pipeline, and includes example safety properties such as yielding at intersections, safe following distance, and opposing-lane clearance. In addition to synthetic examples, the project now includes a data adapter that converts sampled RSV/ego-log data into `SceneFlowSpec/GeneratedTrace.lean` and evaluates the existing properties on generated traces.

Proof technology is used through Lean mechanization of the semantics and metatheory, not only execution. The project proves foundational results (for example, operator dualities, unfolding lemmas, and implications like always-implies-bounded), giving confidence that monitor behavior matches the intended logic. This combination of executable checks (`#eval`) and machine-checked theorems positions the project as both a practical validation tool and a formally grounded specification framework.
