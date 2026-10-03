/-
# The per-fibre mass bound of the `l₂ = 0` column of §6 (Krause--Mirek--Tao, Lemma `mod-approx`)

The `ℓ¹(ℤ²)`-mass of the Fourier coefficients of the symbol
`(θ₁,θ₂) ↦ φ_N(θ₁) φ̃_N(θ₂) weylAvg P N α₁ 0 θ₁ θ₂` (with `α₁ ≠ 0` a `q`-torsion point of the
circle and `N ≥ 1`) is at most `C q² (1 + S²/N) 2^{k₁+dk₂}/N`, `S = 2^{k₁} + 2^{dk₂}`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.FibreMassKernel

namespace Work.KMTAreas.A7

noncomputable section

theorem FibreMassHolds (P : Polynomial ℤ) : Work.KMTAreas.A7.FibreMassStatement P := by
  refine ⟨fibConst P, fibConst_pos P, ?_⟩
  intro N q k₁ k₂ α₁ hN hq hs hne
  exact ⟨(fibreMass_bound P N q k₁ k₂ α₁ hN hq hs hne).1,
    (fibreMass_bound P N q k₁ k₂ α₁ hN hq hs hne).2⟩

end

end Work.KMTAreas.A7
