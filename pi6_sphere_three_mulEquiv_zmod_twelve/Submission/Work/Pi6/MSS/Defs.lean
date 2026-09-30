import Mathlib
import Submission.Work.SSS.serreE2
import Submission.Work.Pi6.Interfaces
import Submission.Work.Cohomology.CupRing
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The Serre cochain filtration (vocabulary for area MSS)

This file contains only *definitions*: the Serre filtration of the singular cochains of a simplicial
set `X` along a morphism `f : X ⟶ Y`, which is the input of the multiplicative cohomological Serre
spectral sequence over a field (`REFS/NOTES_LEAD_PI6.md` §3).

* `ess x` — the essential dimension of a simplex (the dimension of its nondegenerate core);
* `coFilt 𝕜 f s n` — the `s`-th term `F^s C^n`: the cochains vanishing on the singular simplices
  whose image in `Y` has essential dimension `< s` (equivalently, on the chains over the
  `(s-1)`-skeleton of `Y`);
* `coFiltSub 𝕜 f P n` — the same, phrased with the library's `serreSubcomplex f P`.

The pages and the differentials built from a filtered cochain complex with a product are in
`Submission/Work/Pi6/MSS/CohFilt.lean` and `Submission/Work/Pi6/MSS/Pages.lean`.
-/

set_option autoImplicit false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

noncomputable section

/-- The **essential dimension** of a simplex: the dimension of its nondegenerate core. -/
def ess {X : SSet.{0}} {n : ℕ} (x : X _⦋n⦌) : ℕ := (SSet.S.mk x).toN.dim

/-- **The Serre cochain filtration.**  `coFilt 𝕜 f s n` is the `𝕜`-submodule of the `n`-cochains of
`X` consisting of those cochains which vanish on every singular `n`-simplex whose image in `Y` has
essential dimension `< s` — equivalently, on the chains over the `(s-1)`-skeleton of `Y`. -/
def coFilt (𝕜 : Type) [CommRing 𝕜] {X Y : SSet.{0}} (f : X ⟶ Y) (s n : ℕ) :
    Submodule 𝕜 (Work.Cohomology.Cochain 𝕜 X n) where
  carrier := {c | ∀ τ : X _⦋n⦌, ess (f.app (op ⦋n⦌) τ) < s →
    Work.Cohomology.genEval 𝕜 X c τ = 0}
  zero_mem' := by intro τ _; exact LinearMap.zero_apply _
  add_mem' := by
    intro a b ha hb τ hτ
    rw [Work.Cohomology.genEval_add, ha τ hτ, hb τ hτ, add_zero]
  smul_mem' := by
    intro r c hc τ hτ
    rw [Work.Cohomology.genEval_smul, hc τ hτ, smul_zero]

end

end Work.Pi6.MSS
