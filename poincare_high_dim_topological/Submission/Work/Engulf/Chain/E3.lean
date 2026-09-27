import Mathlib
import Submission.Work.Engulf.Defs
import Submission.Work.Engulf.Tools
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Chain.C1_of_L7

/-!
# `E3` = Newman §12 (the cone step)

The requested statement was

```
theorem E3 (n p q : ℕ) (T : Work.Engulf.ToolsAll n) (h7 : Work.Engulf.L7 n p q) :
    Work.Engulf.C1 n p (q + 1)
```

which Lean elaborates with **three independent universe parameters** (one for each of `ToolsAll`,
`L7`, `C1`) and which is therefore *not provable*: the goal `C1.{u₃} n p (q+1)` quantifies over
`M : Type u₃`, while the hypothesis `h7 : L7.{u₂} n p q` can only be applied to an `M : Type u₂`
(Lean: "The argument `M` has type `Type u_3` … but is expected to have type `Type u_2`"), and
`u₂`, `u₃` are unrelated.  See the module docstring of
`Submission/Work/Engulf/Chain/C1_of_L7.lean` and the identical remark in
`Submission/Work/NOTES_LEAD_poincare_E1fix.md` for `E1`.

The statement below is the requested one with the universes identified by the file-level
`universe u` (exactly as in the lead's design file `Submission/Work/Engulf/Skeleton.lean`,
`theorem E3 (n p q : ℕ) (h7 : L7.{u} n p q) : C1.{u} n p (q + 1)`), and it is *proved* — the
whole cone step with its five auxiliary lemmas.
-/

open Set Metric PL

namespace Work.Engulf.Chain

universe u

/-- **`E3` = Newman §12** (the cone step): `L7 q ⇒ C1 (q+1)`, where `C1 (q+1)` is `C1` with `σ.card = q+1`.  Choose a generic apex `a` outside `⋃_{s ∈ Γ.faces} affineSpan (σ ∪ s)` (this uses `Cfg.room : 2p+4 ≤ N` and `Cfg.dimΓ`; the tool is `Work.PL.Generic.exists_mem_ball_notMem_iUnion_affineSubspace`, imported by `Submission.Work.Engulf.Basic`), form the cone complex `Γ' = Γ ∪ {insert a s | s ∈ Γ.faces, s ⊆ σ}` (aux `cone_exists`), extend `f` first over `aσ̇` into `V` (using `Amb.connV` and the simplex/ball homeomorphism `Tools.simplexBall`) and then over `aσ` into `M` (using `Amb.connM`), and apply `L7 q` with `τ₀ = {a}`, `τ₁ = σ` and `K := ⋃{simp s | s ∈ Γ.faces, simp s ⊆ H, s ≠ σ} ∪ aσ̇`. -/
theorem E3 (n p q : ℕ) (T : Work.Engulf.ToolsAll.{u} n) (h7 : Work.Engulf.L7.{u} n p q) :
    Work.Engulf.C1.{u} n p (q + 1) :=
  C1_of_L7 n p q T h7

end Work.Engulf.Chain
