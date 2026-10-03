import Mathlib
import Submission.Work.KMTAreas.A7.CwBoundL1
import Submission.Work.KMTAreas.A7.CwBoundSq
import Submission.Work.KMTAreas.A7.TsumIntLeOfBounds

namespace Work.KMTAreas.A7

namespace Work.KMTAreas.A7
open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

/-- The `ℓ¹`-mass of the coefficient kernel of a rescaled bump: if `1 ≤ R` and `m : ℝ → ℂ`
vanishes off `[-1/R,1/R]` (a narrow bump of inverse width `R`) with `‖m‖_∞ ≤ C₀`,
`‖m'‖_∞ ≤ C₀·R`, `‖m''‖_∞ ≤ C₀·R²`, then `∑_j ‖(𝓕⁻m)(j)‖ ≤ C·C₀` with `C` an ABSOLUTE constant,
independent of `R` and `C₀`.

(Equivalently, for `m(θ) = f(Rθ)` with `f` supported in `[-1,1]` and
`C₀ = max(‖f‖_∞, ‖f'‖_∞, ‖f''‖_∞)`, the sum is the Riemann sum `R⁻¹∑_j ‖(𝓕⁻f)(j/R)‖` for
`∫_ℝ‖(𝓕⁻f)(u)‖du`.)  This is the linear ingredient of the Lemma `crude-mult`(ii) of
Krause--Mirek--Tao, Annals 195 (2022), which converts §6 symbol estimates into `ℓ^p` operator
estimates (`Work.KMTAreas.A7.BilinOpLp` for the bilinear version); here
`cw m j = ∫_ℝ m(θ)e(-jθ)dθ` (`A7/Large/Defs.lean`).

Route: two integrations by parts give `‖cw m j‖ ≤ 2C₀/R` and `‖cw m j‖ ≤ 2C₀R/(2πj)²` (the boundary
terms vanish because `m` is supported in the open interval `(-1/R,1/R)`), and splitting the sum at
`|j| ≍ R` gives `∑_j ‖cw m j‖ ≤ C·C₀`, the `1/R`-support being exactly what makes the constant
independent of `R`.  The hypothesis `1 ≤ R` is NECESSARY: for `R < 1` the family `m = f(R·)` with
`f(u) = (C₀/6)(1-u²)³` satisfies all the other hypotheses while `cw m 0 = (∫f)/R → ∞`.  The
support hypothesis cannot be weakened to `[-R,R]` either: spikes at integers interfere
constructively at every integer frequency (`m = C₀∑_{k≤N}g(·-k)` with `g` a fixed bump gives
`cw m j = C₀N ĝ(j)`). -/
theorem CwTsumLe :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℝ → ℂ) (C0 R : ℝ),
      0 ≤ C0 → 1 ≤ R → ContDiff ℝ 2 m →
      (∀ θ, ‖m θ‖ ≤ C0) →
      (∀ θ, ‖deriv m θ‖ ≤ C0 * R) →
      (∀ θ, ‖deriv (deriv m) θ‖ ≤ C0 * R ^ 2) →
      (∀ θ, 1 / R < |θ| → m θ = 0) →
      ∑' j : ℤ, ‖cw m j‖ ≤ C * C0 := by
  -- The three independent ingredients (proved in the sibling modules `CwBoundL1`,
  -- `CwBoundSq`, `TsumIntLeOfBounds`):
  -- * `‖cw m j‖ ≤ C₁·C₀/R` (trivial `L¹` bound),
  -- * `‖cw m j‖ ≤ C₂·C₀·R/j²` for `j ≠ 0` (two integrations by parts),
  -- * an abstract `ℤ`-summation bound on `min(A, B/j²)` with the cut at `K ≈ R`.
  obtain ⟨C1, hC1pos, h1⟩ := _root_.Work.KMTAreas.A7.CwBoundL1
  obtain ⟨C2, hC2pos, h2⟩ := _root_.Work.KMTAreas.A7.CwBoundSq
  obtain ⟨C3, hC3pos, h3⟩ := _root_.Work.KMTAreas.A7.TsumIntLeOfBounds
  refine ⟨max 1 (C3 * (2 * C1 + C2)), lt_max_iff.mpr (Or.inl one_pos), ?_⟩
  intro m C0 R hC0 hR hcd hL hd1 hd2 hsup
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  -- The cut `K = ⌈R⌉`, so that `R ≤ K < R + 1`.
  set K : ℕ := Nat.ceil R with hK
  have hK1 : 1 ≤ K := by
    rw [hK]
    exact Nat.ceil_pos.mpr hRpos
  have hRK : R ≤ (K : ℝ) := Nat.le_ceil R
  have hKlt : (K : ℝ) < R + 1 := Nat.ceil_lt_add_one hRpos.le
  have hKpos : (0 : ℝ) < (K : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hK1)
  have hA : 0 ≤ C1 * C0 / R := div_nonneg (mul_nonneg hC1pos.le hC0) hRpos.le
  have hB : 0 ≤ C2 * C0 * R := mul_nonneg (mul_nonneg hC2pos.le hC0) hRpos.le
  have hbound : ∑' j : ℤ, ‖cw m j‖ ≤
      C3 * ((K : ℝ) * (C1 * C0 / R) + (C2 * C0 * R) / K) :=
    h3 (fun j : ℤ => ‖cw m j‖) (C1 * C0 / R) (C2 * C0 * R) K hA hB hK1
      (fun j => norm_nonneg _)
      (fun j => h1 m C0 R hRpos hC0 hcd hL hsup j)
      (fun j hj => h2 m C0 R hRpos hC0 hcd hL hd1 hd2 hsup j hj)
  -- The two pieces of the majorant are bounded by `2·C₁·C₀` and `C₂·C₀`.
  have hC1C0 : 0 ≤ C1 * C0 := mul_nonneg hC1pos.le hC0
  have hKA : (K : ℝ) * (C1 * C0 / R) ≤ 2 * C1 * C0 := by
    have h1' : (K : ℝ) * (C1 * C0 / R) ≤ (R + 1) * (C1 * C0 / R) :=
      mul_le_mul_of_nonneg_right hKlt.le hA
    have h2' : (R + 1) * (C1 * C0 / R) = C1 * C0 * (1 + 1 / R) := by
      field_simp
    have h3' : (1 : ℝ) + 1 / R ≤ 2 := by
      have h4 : 1 / R ≤ 1 := by
        rw [div_le_one hRpos]
        linarith
      linarith
    calc (K : ℝ) * (C1 * C0 / R) ≤ (R + 1) * (C1 * C0 / R) := h1'
      _ = C1 * C0 * (1 + 1 / R) := h2'
      _ ≤ C1 * C0 * 2 := mul_le_mul_of_nonneg_left h3' hC1C0
      _ = 2 * C1 * C0 := by ring
  have hBK : (C2 * C0 * R) / K ≤ C2 * C0 := by
    rw [div_le_iff₀ hKpos]
    nlinarith [hRK, mul_nonneg hC2pos.le hC0]
  have hsum : (K : ℝ) * (C1 * C0 / R) + (C2 * C0 * R) / K ≤ (2 * C1 + C2) * C0 := by
    linarith
  calc ∑' j : ℤ, ‖cw m j‖
      ≤ C3 * ((K : ℝ) * (C1 * C0 / R) + (C2 * C0 * R) / K) := hbound
    _ ≤ C3 * ((2 * C1 + C2) * C0) := mul_le_mul_of_nonneg_left hsum hC3pos.le
    _ = (C3 * (2 * C1 + C2)) * C0 := by ring
    _ ≤ max 1 (C3 * (2 * C1 + C2)) * C0 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hC0

end Work.KMTAreas.A7

/-- The same statement under the module's own namespace `Work.KMTAreas.A7` (the declaration above
lives at the doubly-nested name `Work.KMTAreas.A7.Work.KMTAreas.A7.CwTsumLe`, inherited from the
statement's own `namespace` line). -/
theorem CwTsumLe :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℝ → ℂ) (C0 R : ℝ),
      0 ≤ C0 → 1 ≤ R → ContDiff ℝ 2 m →
      (∀ θ, ‖m θ‖ ≤ C0) →
      (∀ θ, ‖deriv m θ‖ ≤ C0 * R) →
      (∀ θ, ‖deriv (deriv m) θ‖ ≤ C0 * R ^ 2) →
      (∀ θ, 1 / R < |θ| → m θ = 0) →
      ∑' j : ℤ, ‖cw m j‖ ≤ C * C0 :=
  _root_.Work.KMTAreas.A7.Work.KMTAreas.A7.CwTsumLe

end Work.KMTAreas.A7
