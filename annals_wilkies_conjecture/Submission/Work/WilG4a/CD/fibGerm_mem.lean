import Mathlib
import Submission.Work.WilG4a.CD.fibDerivDefs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.CD.germDefs
import Submission.Work.WilG4a.CD.germAux_mem
import Submission.Work.WilG4a.CD.fibGerm_eq_germAux

namespace Work.WilG4a.CD

/-- `Γ`: the `Ω`-membership of the fibre-germ set. `fibGerm f j` is the set of `(l,x)` whose punctured fibre neighbourhood lies in the interior of the joint `C^j` locus; it should have the same format as `derivGraphSet`'s format and degree `b.eval ![D,j]` (all the extra atoms — `ρ>0`, `t ≠ x`, `(t-x)² < ρ²` and the final existential in `ρ` — cost only constants, independent of `j`). -/
theorem fibGerm_mem (S : WilkiesDesign.SOMin) (hder : WilkiesDesign.SOMin.SharpDeriv S) (p F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D j : ℕ) {f : (Fin p → ℝ) → ℝ → ℝ}, Work.WilG4a.graphFam f ∈ S.Ω F0 D (p + 1 + 1) →
        Work.WilG4a.CD.fibGerm f j ∈ S.Ω a (MvPolynomial.eval ![D, j] b) (p + 1) := by
  -- The `C^j` locus of the slice is the projection of the joint derivative graph `SharpDeriv`
  -- exhibits; `fibGerm` is the punctured localisation of that locus, read off by the
  -- `Ω`-construction `germAux`.
  obtain ⟨a₀, b₀, hb₀⟩ := Work.WilG4a.smoothLocus_mem S hder p F0
  obtain ⟨A, C, hA⟩ := germAux_mem S p
  refine ⟨a₀ + 1 + A, b₀ + MvPolynomial.C C, ?_⟩
  intro D j f hf
  have hsm : Work.WilG4a.smoothLocus f j ∈ S.Ω a₀ (MvPolynomial.eval ![D, j] b₀) (p + 1) :=
    hb₀ D j hf
  have hc : (Work.WilG4a.smoothLocus f j)ᶜ ∈
      S.Ω (a₀ + 1) (MvPolynomial.eval ![D, j] b₀) (p + 1) := S.compl hsm
  have hg := hA (a₀ + 1) (MvPolynomial.eval ![D, j] b₀) ((Work.WilG4a.smoothLocus f j)ᶜ) hc
  rw [fibGerm_eq_germAux]
  have hdeg : MvPolynomial.eval ![D, j] (b₀ + MvPolynomial.C C) =
      MvPolynomial.eval ![D, j] b₀ + C := by
    rw [MvPolynomial.eval_add, MvPolynomial.eval_C]
  rw [hdeg]
  exact hg

end Work.WilG4a.CD
