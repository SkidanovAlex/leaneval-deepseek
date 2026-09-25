import Mathlib
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_fundamental_inequality
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_degree_zero_finrank
import Submission.Commons.Algebra.FreeAlgebra.golod_shafarevich_inequality_conclusion

namespace Commons.Algebra.FreeAlgebra

open _root_.FreeAlgebra

set_option linter.unusedVariables false in
theorem golod_shafarevich_finite_dimensional_pos
    {K ι σ : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Fintype σ]
    (hne : 0 < Fintype.card ι)
    (degRel : σ → ℕ) (rel : σ → FreeAlgebra K ι)
    (hdeg : ∀ r, 2 ≤ degRel r)
    (hhom : ∀ r, rel r ∈
      let degreeSubmodule : ℕ → Submodule K (FreeAlgebra K ι) := fun n =>
        Submodule.span K {x | ∃ w : FreeMonoid ι,
          (FreeMonoid.toList w).length = n ∧ x = FreeAlgebra.basisFreeMonoid K ι w}
      degreeSubmodule (degRel r))
    (hfin : ∀ᶠ n : ℕ in Filter.atTop,
      let degreeSubmodule : ℕ → Submodule K (FreeAlgebra K ι) := fun n =>
        Submodule.span K {x | ∃ w : FreeMonoid ι,
          (FreeMonoid.toList w).length = n ∧ x = FreeAlgebra.basisFreeMonoid K ι w}
      let twoSidedSpan : (σ → FreeAlgebra K ι) → Submodule K (FreeAlgebra K ι) := fun rel =>
        Submodule.span K {x | ∃ (r : σ) (v w : FreeMonoid ι),
          x = FreeAlgebra.basisFreeMonoid K ι v * rel r * FreeAlgebra.basisFreeMonoid K ι w}
      Module.finrank K
        (Submodule.map (Submodule.mkQ (twoSidedSpan rel)) (degreeSubmodule n)) = 0) :
    Fintype.card ι * Fintype.card ι < 4 * Fintype.card σ := by
  dsimp only at hfin ⊢
  let d := Fintype.card ι
  let b : ℕ → ℕ := fun n =>
    Module.finrank K (Submodule.map (golodShafarevich_twoSidedIdeal K ι σ rel).mkQ
      (golodShafarevich_gradedPart K ι n))
  have hd : 0 < d := by simpa [d] using hne
  have hb0 : b 0 = 1 := by
    have h := golod_shafarevich_degree_zero_finrank (K := K) (ι := ι) (σ := σ) degRel rel hdeg (by
      intro r
      simpa [golodShafarevich_gradedPart] using hhom r)
    dsimp [b, golodShafarevich_gradedPart, golodShafarevich_twoSidedIdeal] at h ⊢
    exact h
  have hfund : ∀ n : ℕ, 0 < n →
      d * b (n - 1) ≤ b n + ∑ r : σ, if degRel r ≤ n then b (n - degRel r) else 0 := by
    intro n hn
    have h := golod_shafarevich_fundamental_inequality (K := K) (ι := ι) (σ := σ)
      degRel rel hdeg hhom n hn
    dsimp [d, b] at h ⊢
    exact h
  have hfin' : ∀ᶠ n : ℕ in Filter.atTop, b n = 0 := by
    dsimp [b, golodShafarevich_gradedPart, golodShafarevich_twoSidedIdeal] at hfin ⊢
    exact hfin
  have hconc := golod_shafarevich_inequality_conclusion (d := d) (deg := degRel) (b := b)
    hd hb0 hdeg hfund hfin'
  simpa [d] using hconc

end Commons.Algebra.FreeAlgebra
