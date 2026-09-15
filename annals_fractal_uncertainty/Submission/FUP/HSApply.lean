import Submission.FUP.HSLoc
import Submission.FUP.HSLocalize
import Submission.FUP.HSCellsZ

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set Pointwise
open scoped ENNReal BigOperators Topology ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-!
# Han–Schlag's §5, step 9: applying the single-scale localisation statement at scale `L^{mT}`

This module instantiates `Submission.FUP.LocalizationStatement` for the rescaled function `g_m`,
with `c₁ = (2L)^{-1}`, the `(-L^{mT})`-shifted `2ℤ`-grid, the active cells `activeCells L T m X`
and the chosen holes `holeSel`, and the damping datum of Han–Schlag's Theorem 5.1 at `n = mT`.
-/

namespace Submission.FUP

/-- `(L^{mT})⁻¹ = (L:ℝ)^{-(mT)}` (the exponent convention of `Spec.han_schlag_statement`). -/
lemma inv_rescaleFactor_eq {L T m : ℕ} (hL : 0 < L) :
    (rescaleFactor L T m)⁻¹ = (L : ℝ) ^ (-(m * T : ℤ)) := by
  rw [rescaleFactor, ← zpow_natCast, ← zpow_neg]
  congr 1

/-- `locY L T m Y ⊆ cube (-α₁) α₁` for `Y ⊆ cube (-N) N` and `α₁ = N (L^{mT})⁻¹ + 2`. -/
lemma locY_subset_cube {L T m : ℕ} (hL : 0 < L) {N : ℝ} (hN : 0 ≤ N) {Y : Set ℝᵈ}
    (hY : Y ⊆ cube (-N) N) :
    locY L T m Y ⊆ cube (-(N * (rescaleFactor L T m)⁻¹ + 2))
      (N * (rescaleFactor L T m)⁻¹ + 2) := by
  have hs0 : 0 ≤ (rescaleFactor L T m)⁻¹ := inv_nonneg.mpr (rescaleFactor_pos hL T m).le
  have h1 : (rescaleFactor L T m)⁻¹ • Y
      ⊆ cube (-(N * (rescaleFactor L T m)⁻¹)) (N * (rescaleFactor L T m)⁻¹) := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := hz
    have hy' := smul_cube_subset (c := (rescaleFactor L T m)⁻¹) hs0 ⟨y, hY hy, rfl⟩
    simpa only [mul_comm] using hy'
  have h2 : (closedBall (0:ℝᵈ) 2 : Set ℝᵈ) ⊆ cube (-2) 2 := closedBall_subset_cube
  have h3 := cube_add_subset (d := d) (a := N * (rescaleFactor L T m)⁻¹) (b := 2)
    (mul_nonneg hN hs0) (by norm_num)
  exact (addSet_mono h1 h2).trans h3

/-- **The localisation estimate for `g_m`**, with the corrected (full-grid) localisation set
`locSetZ` (Session 52). -/
theorem localize_gm {L T m : ℕ} (hL : 3 ≤ L) (hT : 1 ≤ T) (Φ : FupCutoff d) (hΦr : Φ.radius ≤ 1)
    {N : ℝ} (hN : 1 ≤ N) {X Y : Set ℝᵈ} (hX : X ⊆ cube (-1) 1) (hY : Y ⊆ cube (-N) N)
    (hpor : BoxPorous L (m * T + 1) X)
    {c₂ c₃ α Cstar : ℝ} (hCstar : 0 < Cstar)
    (hLOC : ∀ (α₁ : ℝ), 1 ≤ α₁ → ∀ (γ : ℝᵈ) (Y' : Set ℝᵈ), Y' ⊆ cube (-α₁) α₁ →
        (∀ η : ℝᵈ, (∀ i : Fin d, η i ∈ Set.Icc (-(α₁ + 1)) (α₁ + 1)) →
          AdmitsL1Damping ((fun z : ℝᵈ => η + z) '' (addSet Y' (cube (-2) 2)))
            (4 * (L : ℝ))⁻¹ c₂ c₃ α) →
        ∀ (a : (Fin d → ℤ) → (Fin d → ℝ)),
          (∀ n : Fin d → ℤ, ∀ i : Fin d, 2 * (n i : ℝ) + γ i ≤ a n i ∧
            a n i + locSide L ≤ 2 * (n i : ℝ) + γ i + 2) →
          ∀ f' : Lp ℂ 2 (volume : Measure ℝᵈ),
            (∀ᵐ ξ ∂(volume : Measure ℝᵈ),
              ((𝓕 f' : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ Y') →
            ‖f'‖ ≤ Cstar * (eLpNorm ((⋃ n : Fin d → ℤ, box (a n) (fun i => a n i + locSide L)).indicator
                (f' : ℝᵈ → ℂ)) 2 (volume : Measure ℝᵈ)).toReal)
    (hdamp : ∀ η : ℝᵈ,
        (∀ i : Fin d, η i ∈ Set.Icc (-(N * (rescaleFactor L T m)⁻¹) - 3)
          (N * (rescaleFactor L T m)⁻¹ + 3)) →
        AdmitsL1Damping ((fun z : ℝᵈ => η + z) ''
          (addSet ((rescaleFactor L T m)⁻¹ • Y) (cube (-4) 4)))
          (4 * (L : ℝ))⁻¹ c₂ c₃ α)
    {f : ℝᵈ → ℂ} (hf : MemLp f 2 (volume : Measure ℝᵈ))
    (hsuppY : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ Y) :
    ‖gmLp (L := L) (T := T) (m := m) (by omega) Φ hX hf‖
      ≤ Cstar * (eLpNorm ((locSetZ L T m X (holeSelZ (by omega) X hpor)).indicator
          (gmFun Φ L T m X f)) 2 (volume : Measure ℝᵈ)).toReal := by
  set s : ℝ := rescaleFactor L T m with hs
  have hspos : 0 < s := by rw [hs]; exact rescaleFactor_pos (by omega) T m
  have hsinv_nonneg : (0:ℝ) ≤ s⁻¹ := inv_nonneg.mpr hspos.le
  have hsN : (0:ℝ) ≤ N * s⁻¹ := mul_nonneg (by linarith) hsinv_nonneg
  -- the Fourier support of `g_m`, in the form required by the localisation statement
  have hsupp : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ((𝓕 (gmLp (L := L) (T := T) (m := m) (by omega) Φ hX hf) :
        Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ locY L T m Y :=
    fourierSupp_gm (L := L) (T := T) (m := m) (by omega) hT Φ hΦr hX hf hsuppY
  -- the damping datum
  have hdamp' : ∀ η : ℝᵈ,
      (∀ i : Fin d, η i ∈ Set.Icc (-(N * s⁻¹ + 2 + 1)) (N * s⁻¹ + 2 + 1)) →
      AdmitsL1Damping ((fun z : ℝᵈ => η + z) ''
        (addSet (locY L T m Y) (cube (-2) 2))) (4 * (L : ℝ))⁻¹ c₂ c₃ α := by
    intro η hη
    refine admitsL1Damping_mono_set (hdamp η ?_) ?_
    · intro i
      have h := hη i
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    · have hset := addSet_closedBall_cube_subset (Y := Y) (s := rescaleFactor L T m)
      rintro z ⟨w, hw, rfl⟩
      exact ⟨w, hset hw, rfl⟩
  have hstep := hLOC (N * s⁻¹ + 2) (by linarith)
    (WithLp.toLp 2 (fun _ : Fin d => -s)) (locY L T m Y)
    (locY_subset_cube (N := N) (by omega) (by linarith) hY) hdamp'
    (fun n => holeLower L T m n (holeSelZ (by omega) X hpor n))
    (fun n i => by
      have h := holeLower_constraint (L := L) (T := T) (m := m) (by omega)
        n (holeSelZ (by omega) X hpor n) i
      rw [two_mul_half_locSide L] at h
      rw [show (WithLp.toLp 2 (fun _ : Fin d => -s) : ℝᵈ) i = -s from rfl]
      rw [hs]
      exact h)
    (gmLp (L := L) (T := T) (m := m) (by omega) Φ hX hf) hsupp
  -- compare the two indicators (the Lp class and its representative)
  have hcoe : ((gmLp (L := L) (T := T) (m := m) (by omega) Φ hX hf :
      Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) =ᵐ[volume] gmFun Φ L T m X f :=
    MemLp.coeFn_toLp _
  have hid : ((locSetZ L T m X (holeSelZ (by omega) X hpor)).indicator (gmFun Φ L T m X f))
      =ᵐ[volume] ((locSetZ L T m X (holeSelZ (by omega) X hpor)).indicator
        ((gmLp (L := L) (T := T) (m := m) (by omega) Φ hX hf : Lp ℂ 2 (volume : Measure ℝᵈ)) :
          ℝᵈ → ℂ)) := by
    filter_upwards [hcoe] with z hz
    by_cases h : z ∈ locSetZ L T m X (holeSelZ (by omega) X hpor)
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, hz]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]
  rw [eLpNorm_congr_ae hid]
  simpa only [locSetZ, holeCube] using hstep

end Submission.FUP
