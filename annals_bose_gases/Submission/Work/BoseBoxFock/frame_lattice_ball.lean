import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.BoseBoxFock.kinFT_comp_smul
import Submission.Work.BoseBoxFock.kinFT_plancherel
import Submission.Work.BoseBoxFock.sampling_unitCube
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators Pointwise

/-! ## Auxiliary lemmas

The three analytical inputs of the frame identity are proved elsewhere in this directory:

* `Work.BoseBoxFock.sampling_unitCube` — the torus/sampling identity on the unit cube:
  for `g` supported in `[-1/2,1/2]³`, `Σ_n ‖ĝ(2πn)‖² = ∫‖g‖²`;
* `Work.BoseBoxFock.kinFT_plancherel` — `(2π)⁻³∫_p ‖kinFT u p‖² = ∫_x ‖u x‖²`;
* `Work.BoseBoxFock.kinFT_comp_smul` — the dilation covariance of `kinFT`.

Here we assemble them: rescaling `u` to the unit cube turns the lattice sum into the unit-cube
sampling sum, and Plancherel identifies the unit-cube mass with the continuum transform mass. -/

/-- Pulling a nonzero constant out of a `tsum`.  No summability hypothesis is needed: when the
family is not summable both sides are `0` (`tsum` of a non-summable family, and `c • f` is
summable exactly when `f` is for `c ≠ 0`). -/
lemma flb_tsum_mul_left {ι : Type*} (ψ : ι → ℝ) {c : ℝ} (hc : c ≠ 0) :
    (∑' n, c * ψ n) = c * ∑' n, ψ n := by
  by_cases h : Summable ψ
  · exact h.tsum_mul_left c
  · have hc' : ¬ Summable (fun n => c * ψ n) := by
      intro hs
      have h2 : Summable (fun n => c⁻¹ * (c * ψ n)) := hs.mul_left c⁻¹
      refine h (h2.congr (fun n => ?_))
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    rw [tsum_eq_zero_of_not_summable hc', tsum_eq_zero_of_not_summable h, mul_zero]

/-- Squared norm of a real multiple of a complex number. -/
lemma flb_normSq_ofReal_mul (r : ℝ) (z : ℂ) : ‖(r : ℂ) * z‖ ^ 2 = r ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
  ring

/-- **Support transfer.**  If `u` is supported in the box `Λ(ℓ) = ℓ • [-1/2,1/2]³`, then the
rescaled function `y ↦ u(ℓ y)` is supported in the unit cube `[-1/2,1/2]³`. -/
lemma flb_tsupport_sub {ℓ : ℝ} (hℓ : 0 < ℓ) {u : ℝ³ → ℂ}
    (hsupp : tsupport u ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    tsupport (fun y : ℝ³ => u (ℓ • y)) ⊆ {y : ℝ³ | ∀ i, |y i| ≤ (1 / 2 : ℝ)} := by
  have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
  refine closure_minimal (fun y hy => ?_) Work.BoseB4.isClosed_unitCell
  by_contra hyS
  have hmem : ℓ • y ∉ Work.BoseK15.corpusBox.boxL ℓ := by
    rw [show Work.BoseK15.corpusBox.boxL ℓ
        = (ℓ • ({y : ℝ³ | ∀ i, |y i| ≤ (1 / 2 : ℝ)} : Set ℝ³)) from rfl]
    intro hc
    have hcy : ℓ⁻¹ • (ℓ • y) ∈ ({y : ℝ³ | ∀ i, |y i| ≤ (1 / 2 : ℝ)} : Set ℝ³) :=
      (Set.mem_smul_set_iff_inv_smul_mem₀ hℓ0 _ _).mp hc
    rw [inv_smul_smul₀ hℓ0 y] at hcy
    exact hyS hcy
  exact hy (image_eq_zero_of_notMem_tsupport (fun hc => hmem (hsupp hc)))

/-- Scaling of the `L²`-mass under a dilation by `ℓ > 0` in dimension `3`. -/
lemma flb_integral_norm_sq_comp_smul {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³ → ℂ) :
    (∫ y, ‖u (ℓ • y)‖ ^ 2) = (ℓ ^ 3)⁻¹ * ∫ x, ‖u x‖ ^ 2 := by
  have h := MeasureTheory.Measure.integral_comp_smul (volume : Measure ℝ³)
    (fun x : ℝ³ => ‖u x‖ ^ 2) ℓ
  have hfin : Module.finrank ℝ ℝ³ = 3 := by simp
  rw [hfin] at h
  rw [h, smul_eq_mul, abs_of_pos (show (0:ℝ) < (ℓ ^ 3)⁻¹ by positivity)]

/-- **The frame identity for the box lattice.**  For a smooth compactly supported `u` whose
support lies in the box `boxL ℓ` (the cube of side `ℓ`), the `ℓ⁻³`-weighted lattice samples of its
`p`-convention Fourier transform have the same `ℓ²`-mass as the continuum transform.  This is
`S0 = R0` in the vocabulary of `FINDING_kinRow_lattice.md`:  `Σ_n ℓ⁻³|f(k_n)|² = (2π)⁻³∫|f|²`
with `k_n = (2π/ℓ)n`, and it holds because the `ℓℤ³`-translates of `boxL ℓ` meet only in
measure-zero faces, so the Poisson cross terms `∫u(x)conj(u(x−ℓm))dx` (`m ≠ 0`) vanish. -/
theorem frame_lattice_ball {ℓ : ℝ} (hℓ : 0 < ℓ) {u : ℝ³ → ℂ}
    (hu : ContDiff ℝ (⊤ : ENat) u) (huc : HasCompactSupport u)
    (hsupp : tsupport u ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    (∑' n : Fin 3 → ℤ,
        (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT u (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p, ‖Submission.BoseGases.kinFT u p‖ ^ 2 := by
  have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
  have hℓ3 : (0 : ℝ) < ℓ ^ 3 := by positivity
  -- the rescaled state, supported in the unit cube
  set g : ℝ³ → ℂ := fun y => u (ℓ • y) with hg
  have hg_cd : ContDiff ℝ (⊤ : ENat) g := by
    rw [hg]
    exact hu.comp (contDiff_const_smul ℓ)
  have hg_cs : HasCompactSupport g := by
    rw [hg]
    exact huc.comp_smul hℓ0
  have hg_supp : tsupport g ⊆ {y : ℝ³ | ∀ i, |y i| ≤ (1 / 2 : ℝ)} := by
    rw [hg]
    exact flb_tsupport_sub hℓ hsupp
  -- the unit-cube sampling identity
  have hB := sampling_unitCube (g := g) hg_cd hg_cs hg_supp
  -- the rescaled `L²`-mass
  have hD : (∫ y, ‖g y‖ ^ 2) = (ℓ ^ 3)⁻¹ * ∫ x, ‖u x‖ ^ 2 := by
    rw [hg]
    exact flb_integral_norm_sq_comp_smul hℓ u
  -- each sampling coefficient is `(ℓ³)⁻¹` times the transform at the lattice momentum
  have hpt : ∀ n : Fin 3 → ℤ,
      ‖∫ y, Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ))) * g y‖ ^ 2
        = ((ℓ ^ 3)⁻¹) ^ 2
          * ‖Submission.BoseGases.kinFT u (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2 := by
    intro n
    rw [hg]
    simp only
    rw [kinFT_comp_smul hℓ u (Work.BoseB4.vec n)]
    rw [show ℓ⁻¹ • Work.BoseB4.vec n = Work.BoseBoxFock.kmomInt ℓ n from rfl]
    rw [flb_normSq_ofReal_mul]
  have hA : (∑' n : Fin 3 → ℤ,
        ((ℓ ^ 3)⁻¹) ^ 2 * ‖Submission.BoseGases.kinFT u (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      = (ℓ ^ 3)⁻¹ * ∫ x, ‖u x‖ ^ 2 := by
    calc (∑' n : Fin 3 → ℤ,
          ((ℓ ^ 3)⁻¹) ^ 2 * ‖Submission.BoseGases.kinFT u (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
        = (∑' n : Fin 3 → ℤ,
            ‖∫ y, Complex.exp (-(Complex.I * (inner ℝ (Work.BoseB4.vec n) y : ℂ))) * g y‖ ^ 2) :=
          tsum_congr (fun n => (hpt n).symm)
      _ = ∫ y, ‖g y‖ ^ 2 := hB
      _ = (ℓ ^ 3)⁻¹ * ∫ x, ‖u x‖ ^ 2 := hD
  have hmain : (∑' n : Fin 3 → ℤ,
        (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT u (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      = ∫ x, ‖u x‖ ^ 2 := by
    calc (∑' n : Fin 3 → ℤ,
          (ℓ ^ 3)⁻¹ * ‖Submission.BoseGases.kinFT u (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
        = (∑' n : Fin 3 → ℤ,
            ℓ ^ 3 * (((ℓ ^ 3)⁻¹) ^ 2
              * ‖Submission.BoseGases.kinFT u (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)) :=
          tsum_congr (fun n => by field_simp)
      _ = ℓ ^ 3 * (∑' n : Fin 3 → ℤ,
            ((ℓ ^ 3)⁻¹) ^ 2
              * ‖Submission.BoseGases.kinFT u (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2) :=
          flb_tsum_mul_left _ (ne_of_gt hℓ3)
      _ = ℓ ^ 3 * ((ℓ ^ 3)⁻¹ * ∫ x, ‖u x‖ ^ 2) := by rw [hA]
      _ = ∫ x, ‖u x‖ ^ 2 := by
          rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hℓ3), one_mul]
  -- Plancherel converts the unit-cube mass into the continuum transform mass
  exact hmain.trans (kinFT_plancherel (u := u) hu huc).symm

end Work.BoseBoxFock
