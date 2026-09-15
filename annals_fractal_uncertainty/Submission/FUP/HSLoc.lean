import Submission.FUP.HSRescale
import Submission.FUP.Damping
import Submission.FUP.HSCellsZ

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set Pointwise
open scoped ENNReal BigOperators Topology ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-!
# Han–Schlag's §5, step 8: from the single-scale localisation estimate to the one-step gain

This module contains the transfer from the conclusion of `LocalizationStatement` (applied to the
rescaled function `g_m`) back to an estimate for `f_m` on the hole set `Ustar L X (mT)`, together
with the measurability of the hole sets and the elementary Minkowski-sum lemmas used to feed the
damping hypotheses in.
-/

namespace Submission.FUP

/-! ## Measurability of the hole sets -/

lemma measurableSet_halfCube (L n : ℕ) (k : Fin d → ℕ) : MeasurableSet (halfCube L n k) :=
  measurableSet_box _ _

lemma measurableSet_Ustar (L : ℕ) (X : Set ℝᵈ) (n : ℕ) : MeasurableSet (Ustar L X n) := by
  have h : Ustar L X n = ⋃ k : Fin d → ℕ, ⋃ (_ : (X ∩ gridBox L n k).Nonempty),
      ⋃ j : Fin d → Fin L, ⋃ (_ : X ∩ gridBox L (n+1) (childIndex L k j) = ∅),
        halfCube L (n+1) (childIndex L k j) := by
    ext z
    simp only [mem_Ustar, Set.mem_iUnion, exists_prop]
  rw [h]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ =>
    MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => measurableSet_halfCube _ _ _

lemma measurableSet_locSet (L T m : ℕ) (X : Set ℝᵈ) (j : (Fin d → ℤ) → Fin d → Fin L) :
    MeasurableSet (locSet L T m X j) := by
  rw [locSet]
  exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ => measurableSet_box _ _

/-! ## Elementary Minkowski sums of cubes -/

lemma smul_cube_subset {c a : ℝ} (hc : 0 ≤ c) :
    c • (cube (-a) a : Set ℝᵈ) ⊆ cube (-(c * a)) (c * a) := by
  rintro z ⟨y, hy, rfl⟩
  rw [mem_cube] at hy ⊢
  intro i
  have h := hy i
  constructor
  · rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    nlinarith [h.1, h.2]
  · rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
    nlinarith [h.1, h.2]

lemma cube_add_subset {a b : ℝ} (_ha : 0 ≤ a) (_hb : 0 ≤ b) :
    addSet (cube (-a) a : Set ℝᵈ) (cube (-b) b) ⊆ cube (-(a + b)) (a + b) := by
  rintro z ⟨u, hu, v, hv, rfl⟩
  rw [mem_cube] at hu hv ⊢
  intro i
  have h1 := hu i
  have h2 := hv i
  simp only [WithLp.ofLp_add, Pi.add_apply]
  constructor <;> linarith

/-- The support set of `g_m` (`L^{-mT}Y + closedBall 0 2`) does satisfy the damping hypotheses of
`LocalizationStatement`, because `closedBall 0 2 ⊆ cube (-2) 2`. -/
lemma addSet_closedBall_cube_subset {Y : Set ℝᵈ} {s : ℝ} :
    addSet (addSet (s⁻¹ • Y) (closedBall (0:ℝᵈ) 2)) (cube (-2) 2)
      ⊆ addSet (s⁻¹ • Y) (cube (-4) 4) := by
  rw [addSet_assoc]
  refine addSet_mono (le_refl _) ?_
  refine (addSet_mono (closedBall_subset_cube) (le_refl _)).trans ?_
  have h := cube_add_subset (d := d) (a := 2) (b := 2) (by norm_num) (by norm_num)
  simpa only [show (-2 : ℝ) + -2 = -4 by norm_num, show (2 : ℝ) + 2 = 4 by norm_num] using h

/-! ## Damping is monotone in the set -/

lemma admitsL1Damping_mono_set {c₁ c₂ c₃ α : ℝ} {Y Y' : Set ℝᵈ}
    (h : AdmitsL1Damping Y' c₁ c₂ c₃ α) (hsub : Y ⊆ Y') : AdmitsL1Damping Y c₁ c₂ c₃ α := by
  obtain ⟨ψ, hsupp, hnorm, hdecay, hYdecay⟩ := h
  exact ⟨ψ, hsupp, hnorm, hdecay, hYdecay.mono (fun x hx hxY => hx (hsub hxY))⟩

/-! ## From the localisation estimate on `g_m` to the estimate on `f_m` at the holes -/

/-- **The transfer.**  If the localisation estimate `‖g_m‖ ≤ C‖g_m·1_S‖` holds for the localisation
set `S = locSetZ L T m X j`, and `S ⊆ L^{mT} • UstarZ L X (mT)`, then
`∫‖f_m‖² ≤ C² ∫_{UstarZ L X (mT)} ‖f_m‖²`. -/
theorem integral_le_UstarZ_of_localize {L T m : ℕ} (hL : 2 ≤ L) (Φ : FupCutoff d)
    {X : Set ℝᵈ} (hX : X ⊆ cube (-1) 1) {f : ℝᵈ → ℂ} (hf : MemLp f 2 (volume : Measure ℝᵈ))
    {j : (Fin d → ℤ) → Fin d → Fin L} {C : ℝ}
    (hsub : locSetZ L T m X j ⊆ rescaleFactor L T m • UstarZ L X (m * T))
    (hLOC : ‖gmLp (L := L) (T := T) (m := m) (by omega) Φ hX hf‖
        ≤ C * (eLpNorm ((locSetZ L T m X j).indicator (gmFun Φ L T m X f)) 2
            (volume : Measure ℝᵈ)).toReal) :
    ∫ z, ‖indFun Φ L T X m f z‖ ^ 2
      ≤ C ^ 2 * ∫ z in UstarZ L X (m * T), ‖indFun Φ L T X m f z‖ ^ 2 := by
  set s : ℝ := rescaleFactor L T m with hs
  have hspos : 0 < s := by rw [hs]; exact rescaleFactor_pos (by omega) T m
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hsmeas : MeasurableSet (locSetZ L T m X j) := measurableSet_locSetZ L T m X j
  have hUmeas : MeasurableSet (UstarZ L X (m * T)) := measurableSet_UstarZ L X (m * T)
  have hFm : MemLp (indFun Φ L T X m f) 2 (volume : Measure ℝᵈ) := memLp_indFun_two (by omega) Φ T m hX hf
  have hFint : Integrable (fun z : ℝᵈ => ‖indFun Φ L T X m f z‖ ^ 2) (volume : Measure ℝᵈ) :=
    (memLp_two_iff_integrable_sq_norm hFm.aestronglyMeasurable).mp hFm
  have hGm : MemLp (gmFun Φ L T m X f) 2 (volume : Measure ℝᵈ) :=
    memLp_gmLp_two (L := L) (T := T) (m := m) (by omega) Φ hX hf
  have hGind : MemLp ((locSetZ L T m X j).indicator (gmFun Φ L T m X f)) 2
      (volume : Measure ℝᵈ) := hGm.indicator hsmeas
  -- the norm of the Lp class of `g_m` is the eLpNorm of the representative
  have hcoe : ((gmLp (L := L) (T := T) (m := m) (by omega) Φ hX hf : Lp ℂ 2 (volume : Measure ℝᵈ)) :
      ℝᵈ → ℂ) =ᵐ[volume] gmFun Φ L T m X f :=
    MemLp.coeFn_toLp _
  have hnorm : ‖gmLp (L := L) (T := T) (m := m) (by omega) Φ hX hf‖
      = (eLpNorm (gmFun Φ L T m X f) 2 (volume : Measure ℝᵈ)).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae hcoe]
  -- square norms are integrals
  have hAg : (eLpNorm (gmFun Φ L T m X f) 2 (volume : Measure ℝᵈ)).toReal ^ 2
      = ∫ z, ‖gmFun Φ L T m X f z‖ ^ 2 := toReal_eLpNorm_two_sq hGm
  have hAi : (eLpNorm ((locSetZ L T m X j).indicator (gmFun Φ L T m X f)) 2
      (volume : Measure ℝᵈ)).toReal ^ 2
      = ∫ z in locSetZ L T m X j, ‖gmFun Φ L T m X f z‖ ^ 2 := by
    rw [toReal_eLpNorm_two_sq hGind, ← integral_indicator hsmeas]
    refine integral_congr_ae ?_
    filter_upwards with z
    by_cases hz : z ∈ locSetZ L T m X j
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, norm_zero]
      norm_num
  -- the scaling of the two integrals
  have hq : (eLpNorm (gmFun Φ L T m X f) 2 (volume : Measure ℝᵈ)).toReal
      = (((s⁻¹ : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ)
        * (eLpNorm (indFun Φ L T X m f) 2 (volume : Measure ℝᵈ)).toReal :=
    Commons.MeasureTheory.Lp.eLpNorm_comp_smul_toReal (c := s⁻¹) (by positivity) hFm
  have hq2 : ((((s⁻¹ : ℝ) ^ d)⁻¹) ^ (1 / 2 : ℝ)) ^ 2 = ((s⁻¹ : ℝ) ^ d)⁻¹ := by
    rw [← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  -- integral of `|g_m|^2` versus integral of `|f_m|^2`
  have hAq : (eLpNorm (indFun Φ L T X m f) 2 (volume : Measure ℝᵈ)).toReal ^ 2
      = ∫ z, ‖indFun Φ L T X m f z‖ ^ 2 := toReal_eLpNorm_two_sq hFm
  have hInt : ∫ z, ‖gmFun Φ L T m X f z‖ ^ 2
      = ((s⁻¹ : ℝ) ^ d)⁻¹ * ∫ z, ‖indFun Φ L T X m f z‖ ^ 2 := by
    rw [← hAg, hq, mul_pow, hq2, hAq]
  -- integral over the localisation set
  have hInt2 : ∫ z in locSetZ L T m X j, ‖gmFun Φ L T m X f z‖ ^ 2
      = ((s⁻¹ : ℝ) ^ d)⁻¹ * ∫ z in s⁻¹ • locSetZ L T m X j, ‖indFun Φ L T X m f z‖ ^ 2 := by
    have hcv := Measure.setIntegral_comp_smul_of_pos (μ := (volume : Measure ℝᵈ))
      (fun z : ℝᵈ => ‖indFun Φ L T X m f z‖ ^ 2) (locSetZ L T m X j) (inv_pos.mpr hspos)
    rw [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at hcv
    rw [← hcv]
    refine integral_congr_ae ?_
    filter_upwards with x
    rw [hs]
    rfl
  -- the hole set contains the rescaled localisation set
  have hsub' : s⁻¹ • locSetZ L T m X j ⊆ UstarZ L X (m * T) := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    obtain ⟨u, hu, hwu⟩ := hsub hw
    rw [← hwu]
    simpa only [inv_smul_smul₀ hsne] using hu
  have hmono : ∫ z in s⁻¹ • locSetZ L T m X j, ‖indFun Φ L T X m f z‖ ^ 2
      ≤ ∫ z in UstarZ L X (m * T), ‖indFun Φ L T X m f z‖ ^ 2 :=
    setIntegral_mono_set hFint.integrableOn
      (Filter.Eventually.of_forall fun z => by positivity)
      (Filter.Eventually.of_forall fun z hz => hsub' hz)
  -- assemble
  have hmain : ((s⁻¹ : ℝ) ^ d)⁻¹ * ∫ z, ‖indFun Φ L T X m f z‖ ^ 2
      ≤ ((s⁻¹ : ℝ) ^ d)⁻¹ * (C ^ 2 * ∫ z in UstarZ L X (m * T), ‖indFun Φ L T X m f z‖ ^ 2) := by
    rw [← hInt]
    calc ∫ z, ‖gmFun Φ L T m X f z‖ ^ 2
        = (eLpNorm (gmFun Φ L T m X f) 2 (volume : Measure ℝᵈ)).toReal ^ 2 := hAg.symm
      _ ≤ (C * (eLpNorm ((locSetZ L T m X j).indicator (gmFun Φ L T m X f)) 2
            (volume : Measure ℝᵈ)).toReal) ^ 2 := by
          rw [← hnorm]
          exact pow_le_pow_left₀ (by positivity) hLOC 2
      _ = C ^ 2 * (eLpNorm ((locSetZ L T m X j).indicator (gmFun Φ L T m X f)) 2
            (volume : Measure ℝᵈ)).toReal ^ 2 := by ring
      _ = C ^ 2 * ∫ z in locSetZ L T m X j, ‖gmFun Φ L T m X f z‖ ^ 2 := by rw [hAi]
      _ = C ^ 2 * (((s⁻¹ : ℝ) ^ d)⁻¹ * ∫ z in s⁻¹ • locSetZ L T m X j,
            ‖indFun Φ L T X m f z‖ ^ 2) := by rw [hInt2]
      _ ≤ C ^ 2 * (((s⁻¹ : ℝ) ^ d)⁻¹ * ∫ z in UstarZ L X (m * T),
            ‖indFun Φ L T X m f z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hmono (by positivity)) (by positivity)
      _ = ((s⁻¹ : ℝ) ^ d)⁻¹ * (C ^ 2 * ∫ z in UstarZ L X (m * T),
            ‖indFun Φ L T X m f z‖ ^ 2) := by ring
  have hpos : 0 < ((s⁻¹ : ℝ) ^ d)⁻¹ := inv_pos.mpr (pow_pos (inv_pos.mpr hspos) d)
  exact le_of_mul_le_mul_left hmain hpos

end Submission.FUP
