import Mathlib
import Submission.Vdw.CaseIRegion
import Submission.Vdw.PrimitiveCase

open Polynomial Asymptotics
open scoped BigOperators
open Filter

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Case I, direct regime: the `C_f ≤ H`, `D_f > H^(2+2δ)` slice of `SubcaseI`

`PrimitiveCase.SubcaseI n H` is the remaining primitive slice of
`IrreducibleBad` (primitive, `DD(u_f) ≠ 0`, `A_large ≤ H`).  The paper's
Case I considers its sub-slice with `C_f = radical D_f ≤ H^(1+δ)` and
`D_f > H^(2+2δ)`.  This module formalizes the *elementary* part of that
sub-slice: the members with `C_f ≤ H` are exactly members of the direct
region `CaseIRegion.CaseIDirect`, hence

    # {f ∈ SubcaseI n H : C_f ≤ H, D_f > H^(2+2δ)} = O(H^(n-1))

by `CaseIRegion.CaseIDirect_isBigO`.  (The remaining part of the paper's
Case-I slice, `H < C_f ≤ H^(1+δ)`, needs the Fourier/Weil extension
`fbound2` — Roadmap Sessions 41–43.)

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw

noncomputable section

/-- **The elementary Case-I slice of `SubcaseI`**: primitive proper
irreducible bad polynomials with `C_f = radical D_f ≤ H` and
`D_f > H^(2+2δ)`. -/
def SubcaseI_direct (n H : ℕ) : Set ℤ[X] :=
  {f | f ∈ SubcaseI n H ∧ ∃ h : Irreducible (f.map φℚ),
      radical (fieldDiscExp f h) ≤ H ∧
      (H : ℝ) ^ (2 + 1 / (n : ℝ)) < (fieldDiscExp f h : ℝ)}

/-- Every member of the elementary Case-I slice lies in the direct region
`CaseIDirect` (squarefullness of `D_f` comes from
`PrimitiveBad_exists_squarefull_fieldDisc`; the box membership from
`IrreducibleBad ⊆ Bad ⊆ Box`). -/
theorem SubcaseI_direct_subset_CaseIDirect (n H : ℕ) (hn : 3 ≤ n) :
    SubcaseI_direct n H ⊆ CaseIDirect n H := by
  intro f hf
  obtain ⟨hsub, h'⟩ := hf
  have hprim := SubcaseI_subset_PrimitiveBad n H hsub
  obtain ⟨h, _hgal, hsq⟩ := PrimitiveBad_exists_squarefull_fieldDisc n H f hprim
  obtain ⟨h', hC', hD'⟩ := h'
  exact ⟨h, Bad_subset_Box n H (irreducibleBad_subset_Bad n H hprim.1), hsq, hC', hD'⟩

/-- **The elementary Case-I slice of `SubcaseI` is `O(H^(n-1))`.** -/
theorem SubcaseI_direct_isBigO (n : ℕ) (hn : 3 ≤ n) :
    (fun H : ℕ => ((SubcaseI_direct n H).ncard : ℝ)) =O[atTop]
      (fun H : ℕ => ((H : ℕ) ^ (n - 1) : ℝ)) := by
  have hle : ∀ᶠ H : ℕ in atTop, (SubcaseI_direct n H).ncard ≤ (CaseIDirect n H).ncard := by
    refine Eventually.of_forall (fun H => ?_)
    have hfin : (CaseIDirect n H).Finite := by
      refine (box_finite n H).subset ?_
      intro f hf
      obtain ⟨h, hbox, _⟩ := hf
      exact hbox
    exact Set.ncard_le_ncard (SubcaseI_direct_subset_CaseIDirect n H hn) hfin
  exact (Commons.Analysis.Asymptotics.isBigO_of_eventually_le _ _ hle).trans
    (CaseIDirect_isBigO n hn)

end

end Submission.Vdw
