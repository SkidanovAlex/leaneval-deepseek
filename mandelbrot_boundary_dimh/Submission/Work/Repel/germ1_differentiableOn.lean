import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.Spec
import Submission.Work.Repel.pushdown_holo
import Submission.Work.Repel.pushdown_deriv

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology
open Work.Horn.MandelDim

noncomputable section

/-! ## Openness of the natural domain of `germ1 s R`

`germ1 s R` lives on `Dgerm1 s DR = s • (insert 0 (π '' DR))`, so we need the openness of
`insert 0 (π '' DR)`: `π '' DR` is open because `π = exp ∘ (2πi)·` is an open map, and the
missing point `0` is not isolated — every sufficiently small `ζ ≠ 0` has its principal lift
`log ζ / (2πi)` at height `-log‖ζ‖/(2π)`, which lands in `DR` as soon as `‖ζ‖ < e^{-2π|y|}`
by the hypothesis `hy`. -/

/-- The imaginary part of the principal lift: `Im (log ζ / 2πi) = -log‖ζ‖/2π`. -/
lemma im_log_div_two_pi_I (ζ : ℂ) :
    (Complex.log ζ / (2 * ↑Real.pi * Complex.I)).im = -(Real.log ‖ζ‖) / (2 * Real.pi) := by
  have hre : (2 * ↑Real.pi * Complex.I : ℂ).re = 0 := by simp
  have him : (2 * ↑Real.pi * Complex.I : ℂ).im = 2 * Real.pi := by simp
  have hns : Complex.normSq (2 * ↑Real.pi * Complex.I : ℂ) = (2 * Real.pi) ^ 2 := by
    simp [Complex.normSq]; ring
  rw [Complex.div_im, hre, him, hns, Complex.log_re, Complex.log_im]
  field_simp
  ring

/-- `π = exp(2πi ·)` is an open map, hence `π '' DR` is open for open `DR`. -/
lemma isOpen_piExp_image {DR : Set ℂ} (hDR : IsOpen DR) : IsOpen (piExp '' DR) := by
  have h2 : IsOpenMap (fun w : ℂ => 2 * ↑Real.pi * Complex.I * w) := by
    simpa [smul_eq_mul] using isOpenMap_smul₀ (G₀ := ℂ) (α := ℂ) Complex.two_pi_I_ne_zero
  exact (Complex.isOpenMap_exp.comp h2) DR hDR

/-- `insert 0 (π '' DR)` is open whenever `DR` contains the two horizontal half-planes
`|Im w| ≥ y`.  (The point `0` is pushed in by the upper half-plane, whose `π`-image is a
punctured disc around `0`.) -/
lemma isOpen_insert_zero_piExp_image {DR : Set ℂ} {y : ℝ} (hDR : IsOpen DR)
    (hy : ∀ w : ℂ, y ≤ |w.im| → w ∈ DR) : IsOpen (insert 0 (piExp '' DR)) := by
  have hOpenPi : IsOpen (piExp '' DR) := isOpen_piExp_image hDR
  rw [isOpen_iff_mem_nhds]
  intro a ha
  rcases Set.mem_insert_iff.mp ha with rfl | ha
  · refine Filter.mem_of_superset
      (Metric.ball_mem_nhds (0 : ℂ) (Real.exp_pos (-(2 * Real.pi * |y|)))) ?_
    intro ζ hζ
    rcases eq_or_ne ζ 0 with rfl | hζne
    · exact Set.mem_insert_iff.mpr (Or.inl rfl)
    · refine Set.mem_insert_iff.mpr (Or.inr ?_)
      refine ⟨(Complex.log ζ / (2 * ↑Real.pi * Complex.I) : ℂ), hy _ ?_, ?_⟩
      · rw [im_log_div_two_pi_I]
        have hnorm : ‖ζ‖ < Real.exp (-(2 * Real.pi * |y|)) := by
          simpa [dist_eq_norm] using hζ
        have hlog : Real.log ‖ζ‖ < -(2 * Real.pi * |y|) :=
          (Real.log_lt_iff_lt_exp (norm_pos_iff.mpr hζne)).mpr hnorm
        have hA' : |y| < -(Real.log ‖ζ‖) / (2 * Real.pi) := by
          rw [lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
          linarith
        have hApos : 0 ≤ -(Real.log ‖ζ‖) / (2 * Real.pi) :=
          le_of_lt (lt_of_le_of_lt (abs_nonneg y) hA')
        rw [abs_of_nonneg hApos]
        linarith [le_abs_self y]
      · exact piExp_log_div ζ hζne
  · exact Filter.mem_of_superset (hOpenPi.mem_nhds ha) (Set.subset_insert _ _)

/-- The rescaled pushdown `germ1 s R` is holomorphic on its natural domain, which is open and
contains `0`; the lift runs to the upper end with `E w - w + c → 0`. -/
theorem germ1_differentiableOn {R : ℂ → ℂ} {DR : Set ℂ} {s : ℂ} {y : ℝ} {c : ℂ}
    (hs : s ≠ 0) (hDR : IsOpen DR) (heq : IsTEquivariantOn R DR)
    (hdiff : DifferentiableOn ℂ R DR) (hy : ∀ w : ℂ, y ≤ |w.im| → w ∈ DR)
    (hup : Tendsto (fun w => R w - w + c) upperEnd (𝓝 0)) :
    IsOpen (Dgerm1 s DR) ∧ (0 : ℂ) ∈ Dgerm1 s DR ∧
      DifferentiableOn ℂ (germ1 s R) (Dgerm1 s DR) ∧ germ1 s R 0 = 0 := by
  have hOpenPi : IsOpen (piExp '' DR) := isOpen_piExp_image hDR
  have hOpenA : IsOpen (insert 0 (piExp '' DR)) := isOpen_insert_zero_piExp_image hDR hy
  -- `pushdown R` is holomorphic on `π '' DR` (its image under `π` is a neighbourhood of `0`)
  -- and has a derivative at `0` coming from the upper end of `R`.
  have hA : DifferentiableOn ℂ (pushdown R) (insert 0 (piExp '' DR)) := by
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact (pushdown_deriv hDR heq hdiff hy hup).differentiableAt.differentiableWithinAt
    · exact (((pushdown_holo heq hdiff) z hz).differentiableAt
        (hOpenPi.mem_nhds hz)).differentiableWithinAt
  have hS : DifferentiableOn ℂ (fun z => s * pushdown R z) (insert 0 (piExp '' DR)) :=
    hA.const_mul s
  have hdiv : DifferentiableOn ℂ (fun ζ : ℂ => ζ / s) (Dgerm1 s DR) := by
    have := (differentiableOn_id (𝕜 := ℂ) (E := ℂ) (s := Dgerm1 s DR)).div_const s
    simpa using this
  have hmaps : MapsTo (fun ζ : ℂ => ζ / s) (Dgerm1 s DR) (insert 0 (piExp '' DR)) := by
    rintro ζ ⟨z, hz, rfl⟩
    change (s * z) / s ∈ insert 0 (piExp '' DR)
    rw [mul_div_cancel_left₀ z hs]
    exact hz
  have hcomp : DifferentiableOn ℂ (fun ζ => s * pushdown R (ζ / s)) (Dgerm1 s DR) :=
    DifferentiableOn.comp (g := fun z => s * pushdown R z) (f := fun ζ : ℂ => ζ / s)
      hS hdiv hmaps
  refine ⟨?_, ?_, ?_, germ1_zero s R⟩
  · have hmap : IsOpenMap (fun ζ : ℂ => s * ζ) := by
      simpa [smul_eq_mul] using isOpenMap_smul₀ (G₀ := ℂ) (α := ℂ) hs
    exact hmap _ hOpenA
  · exact ⟨0, Set.mem_insert_iff.mpr (Or.inl rfl), by simp⟩
  · exact hcomp

end

end Work.Repel
