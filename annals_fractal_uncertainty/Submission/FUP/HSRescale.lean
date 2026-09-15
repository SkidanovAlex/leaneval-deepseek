import Submission.FUP.HSSupp
import Submission.FUP.HSHoles
import Submission.Commons.Analysis.Fourier.fourier_comp_smul
import Submission.Commons.MeasureTheory.Lp.eLpNorm_comp_smul_toReal

open FractalUncertainty MeasureTheory FourierTransform Metric Filter Set Pointwise
open scoped ENNReal BigOperators Topology ContDiff

set_option autoImplicit false
variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)

/-!
# Han–Schlag's §5, step 7: the rescaling `g_m(x) = f_m(L^{-mT} x)`

This module contains the rescaling layer of the induction on scales: the rescaled function
`g_m(x) = f_m(L^{-mT}x)` (which brings the depth-`mT` `L`-adic cells to unit scale), its `L¹`/`L²`
properties, its a.e. Fourier support, and the transfer of the localisation estimate on `g_m` back
to `f_m`.

NOTE the direction of the rescaling.  With `g(x) = F(c x)` one has
`𝓕g(ξ) = |(c^d)⁻¹| • 𝓕F(c⁻¹ξ)`, hence `supp 𝓕g = c⁻¹ • supp 𝓕F`: to *contract* the Fourier
support (so that the damping data `L^{-mT}Y + [-4,4]^d` applies) one must take `c = L^{mT}`, i.e.
`g_m(x) = f_m(L^{-mT}x)`, and then the depth-`mT` cells of side `2L^{-mT}` do become unit cells.
-/

namespace Submission.FUP

/-! ## Dilations preserve null sets -/

lemma quasiMeasurePreserving_smul {c : ℝ} (hc : c ≠ 0) :
    Measure.QuasiMeasurePreserving (fun x : ℝᵈ => c • x) (volume : Measure ℝᵈ)
      (volume : Measure ℝᵈ) := by
  have hmap : Measure.map (fun x : ℝᵈ => c • x) (volume : Measure ℝᵈ)
      = ENNReal.ofReal |((c : ℝ) ^ d)⁻¹| • (volume : Measure ℝᵈ) := by
    simpa [finrank_euclideanSpace, Fintype.card_fin] using
      (Measure.map_addHaar_smul (μ := (volume : Measure ℝᵈ)) hc)
  refine ⟨(continuous_const_smul c).measurable, ?_⟩
  rw [hmap]
  intro s hs
  rw [Measure.smul_apply, smul_eq_mul, hs, mul_zero]

lemma ae_comp_smul {c : ℝ} (hc : c ≠ 0) {P : ℝᵈ → Prop}
    (h : ∀ᵐ η ∂(volume : Measure ℝᵈ), P η) :
    ∀ᵐ ξ ∂(volume : Measure ℝᵈ), P (c • ξ) :=
  (quasiMeasurePreserving_smul (d := d) hc).ae h

/-- **Dilation of the Fourier transform** (for `c > 0`; the sign is irrelevant for the support).
With `g(x) = F(c x)` one has `𝓕g(ξ) = (c^d)⁻¹ • 𝓕F(c⁻¹ξ)`. -/
lemma fourier_comp_smul_pos {c : ℝ} (hc : 0 < c) (F : ℝᵈ → ℂ) (ξ : ℝᵈ) :
    𝓕 (fun x => F (c • x)) ξ = (((c : ℝ) ^ d)⁻¹) • 𝓕 F (c⁻¹ • ξ) := by
  have h := Measure.integral_comp_smul_of_nonneg (μ := (volume : Measure ℝᵈ))
    (fun y : ℝᵈ => (Real.fourierChar (-(inner ℝ (c⁻¹ • y) ξ)) : ℂ) • F y) c (hR := hc.le)
  rw [finrank_euclideanSpace, Fintype.card_fin] at h
  rw [Real.fourier_eq, Real.fourier_eq]
  trans ∫ x : ℝᵈ, (Real.fourierChar (-(inner ℝ (c⁻¹ • (c • x)) ξ)) : ℂ) • F (c • x)
  · apply integral_congr_ae
    filter_upwards with x
    rw [inv_smul_smul₀ hc.ne', Circle.smul_def, smul_eq_mul]
  · rw [h]
    congr 1
    apply integral_congr_ae
    filter_upwards with y
    have hinner : inner ℝ (c⁻¹ • y) ξ = inner ℝ y (c⁻¹ • ξ) := by
      rw [real_inner_smul_left, real_inner_smul_right]
    rw [hinner, Circle.smul_def, smul_eq_mul]

/-! ## The rescaled function `g_m` -/

/-- `g_m(x) = f_m(L^{-mT} x)`: the `m`-th iterate brought back to unit scale. -/
noncomputable def gmFun (Φ : FupCutoff d) (L T m : ℕ) (X : Set ℝᵈ) (f : ℝᵈ → ℂ) : ℝᵈ → ℂ :=
  fun x => indFun Φ L T X m f ((rescaleFactor L T m)⁻¹ • x)

/-- The `L²` class of `g_m`. -/
noncomputable def gmLp {L T m : ℕ} (hL : 2 ≤ L) (Φ : FupCutoff d) {X : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) {f : ℝᵈ → ℂ} (hf : MemLp f 2 (volume : Measure ℝᵈ)) :
    Lp ℂ 2 (volume : Measure ℝᵈ) :=
  (Commons.MeasureTheory.Lp.memLp_comp_smul (p := 2) (by norm_num)
    (memLp_indFun_two (by omega) Φ T m hX hf)
    (inv_ne_zero (rescaleFactor_ne_zero (by omega : 0 < L) T m))).toLp (gmFun Φ L T m X f)

lemma memLp_gmLp_two {L T m : ℕ} (hL : 2 ≤ L) (Φ : FupCutoff d) {X : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) {f : ℝᵈ → ℂ} (hf : MemLp f 2 (volume : Measure ℝᵈ)) :
    MemLp (gmFun Φ L T m X f) 2 (volume : Measure ℝᵈ) :=
  Commons.MeasureTheory.Lp.memLp_comp_smul (p := 2) (by norm_num)
    (memLp_indFun_two (by omega) Φ T m hX hf) (inv_ne_zero (rescaleFactor_ne_zero (by omega : 0 < L) T m))

lemma memLp_gmLp_one {L T m : ℕ} (hL : 2 ≤ L) (hT : 1 ≤ T) (Φ : FupCutoff d) {X : Set ℝᵈ}
    (hX : X ⊆ cube (-1) 1) {f : ℝᵈ → ℂ} (hf : MemLp f 2 (volume : Measure ℝᵈ)) (hm : 1 ≤ m) :
    MemLp (gmFun Φ L T m X f) 1 (volume : Measure ℝᵈ) :=
  Commons.MeasureTheory.Lp.memLp_comp_smul (p := 1) (by norm_num)
    (memLp_indFun_one (by omega) Φ T m hX hf hm) (inv_ne_zero (rescaleFactor_ne_zero (by omega : 0 < L) T m))

/-! ## The a.e. Fourier support of `g_m` -/

/-- The Fourier support set of `g_m`: `L^{-mT}Y + [-2,2]^d`. -/
noncomputable def locY (L T m : ℕ) (Y : Set ℝᵈ) : Set ℝᵈ :=
  addSet ((rescaleFactor L T m)⁻¹ • Y) (closedBall (0:ℝᵈ) 2)

lemma smul_closedBall_subset {c a : ℝ} (hc : 0 < c) :
    c • closedBall (0:ℝᵈ) a ⊆ closedBall (0:ℝᵈ) (c * a) := by
  rintro z ⟨y, hy, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hy ⊢
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  exact mul_le_mul_of_nonneg_left hy hc.le

/-- **The a.e. Fourier support of the rescaled function `g_m`.** -/
theorem fourierSupp_gm {L T m : ℕ} (hL : 2 ≤ L) (hT : 1 ≤ T) (Φ : FupCutoff d)
    (hΦr : Φ.radius ≤ 1) {X Y : Set ℝᵈ} (hX : X ⊆ cube (-1) 1)
    {f : ℝᵈ → ℂ} (hf : MemLp f 2 (volume : Measure ℝᵈ))
    (hY : ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ((𝓕 (hf.toLp f) : Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ Y) :
    ∀ᵐ ξ ∂(volume : Measure ℝᵈ),
      ((𝓕 (gmLp (L := L) (T := T) (m := m) hL Φ hX hf) : Lp ℂ 2 (volume : Measure ℝᵈ)) :
        ℝᵈ → ℂ) ξ ≠ 0 → ξ ∈ locY L T m Y := by
  by_cases hm : m = 0
  · subst hm
    -- `g_0 = f` and `locY L T 0 Y = Y + closedBall 0 2 ⊇ Y`
    have e0 : rescaleFactor L T 0 = 1 := by simp [rescaleFactor]
    have hYsub : Y ⊆ locY L T 0 Y := by
      intro y hy
      refine ⟨(1:ℝ)⁻¹ • y, ?_, 0, ?_, by simp⟩
      · simpa [e0] using hy
      · rw [Metric.mem_closedBall, dist_zero_right]; norm_num
    have hgm : gmFun Φ L T 0 X f = f := by
      funext x
      rw [gmFun, e0, inv_one, one_smul, indFun_zero]
    have hLp : gmLp (L := L) (T := T) (m := 0) hL Φ hX hf = hf.toLp f := by
      refine MemLp.toLp_congr _ _ ?_
      filter_upwards with x
      exact congrFun hgm x
    rw [hLp]
    filter_upwards [hY] with ξ hξ hne
    exact hYsub (hξ hne)
  · -- `m ≥ 1`
    have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    set s : ℝ := rescaleFactor L T m with hs
    have hspos : 0 < s := by rw [hs]; exact rescaleFactor_pos (by omega) T m
    have hsne : s ≠ 0 := ne_of_gt hspos
    have hsinv : 0 < s⁻¹ := inv_pos.mpr hspos
    -- the Fourier support of `f_m` itself
    have hF : ∀ᵐ η ∂(volume : Measure ℝᵈ), 𝓕 (indFun Φ L T X m f) η ≠ 0 →
        η ∈ addSet Y (closedBall (0:ℝᵈ) (ellSum L T m)) := by
      have hce := Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral
        (memLp_indFun_one (L := L) (by omega) Φ T m hX hf hm1)
        (memLp_indFun_two (L := L) (by omega) Φ T m hX hf)
      filter_upwards [hce, fourierSupp_indFun' (L := L) (T := T) (by omega) hT Φ hΦr hX hf hY m]
        with η h1 h2 hne
      refine h2 ?_
      rw [h1]
      exact hne
    -- the dilation of the Fourier transform
    have hpoint : ∀ ξ : ℝᵈ, 𝓕 (gmFun Φ L T m X f) ξ
        = |((s⁻¹ : ℝ) ^ d)⁻¹| • 𝓕 (indFun Φ L T X m f) (s • ξ) := by
      intro ξ
      have hgm : gmFun Φ L T m X f = fun x => indFun Φ L T X m f (s⁻¹ • x) := rfl
      rw [hgm, fourier_comp_smul_pos (c := s⁻¹) (by positivity) (indFun Φ L T X m f) ξ, inv_inv,
        abs_of_pos (by positivity)]
    have hcoef : (((𝓕 (gmLp hL Φ hX hf (T := T) (m := m)) :
        Lp ℂ 2 (volume : Measure ℝᵈ)) : ℝᵈ → ℂ))
        =ᵐ[volume] 𝓕 (gmFun Φ L T m X f) :=
      Commons.Analysis.Fourier.fourier_toLp_eq_fourier_integral
        (memLp_gmLp_one hL hT Φ hX hf hm1) (memLp_gmLp_two (L := L) (T := T) (m := m) hL Φ hX hf)
    have hae : ∀ᵐ ξ ∂(volume : Measure ℝᵈ), 𝓕 (indFun Φ L T X m f) (s • ξ) ≠ 0 →
        s • ξ ∈ addSet Y (closedBall (0:ℝᵈ) (ellSum L T m)) :=
      ae_comp_smul hsne hF
    have hbe : s⁻¹ * ellSum L T m ≤ 2 := by
      have h := ellSum_mul_inv_pow_le (L := L) (T := T) (by omega) hT m
      have h2 : s⁻¹ * ellSum L T m = ellSum L T m * ((L : ℝ) ^ (m * T))⁻¹ := by
        rw [hs, rescaleFactor]
        rw [mul_comm]
      rw [h2]
      exact h
    have hsub : s⁻¹ • addSet Y (closedBall (0:ℝᵈ) (ellSum L T m)) ⊆ locY L T m Y := by
      rintro z ⟨w, hw, rfl⟩
      obtain ⟨y, hy, b, hb, rfl⟩ := hw
      refine ⟨s⁻¹ • y, ⟨y, hy, rfl⟩, s⁻¹ • b, ?_, by show s⁻¹ • (y + b) = s⁻¹ • y + s⁻¹ • b; rw [smul_add]⟩
      have hmem : ‖s⁻¹ • b‖ ≤ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hsinv]
        calc s⁻¹ * ‖b‖ ≤ s⁻¹ * ellSum L T m :=
              mul_le_mul_of_nonneg_left
                (by simpa [Metric.mem_closedBall, dist_zero_right] using hb) hsinv.le
          _ ≤ 2 := hbe
      simpa [Metric.mem_closedBall, dist_zero_right] using hmem
    filter_upwards [hcoef, hae] with ξ h1 h2 hne
    rw [h1] at hne
    rw [hpoint, smul_ne_zero_iff] at hne
    exact hsub ⟨s • ξ, h2 hne.2, (inv_smul_smul₀ hsne) ξ⟩

end Submission.FUP
