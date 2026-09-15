import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Commons.Analysis.Complex.graph_region_cauchy_mono

open MeasureTheory intervalIntegral Filter Set
open scoped Interval Topology ComplexConjugate

namespace Commons.Analysis.Complex

open _root_.Complex

noncomputable section

/-! # Contour shift with a residue (infrastructure)

Geometry of the boundary curve `y ↦ -β / log (|y|+2) + i y`, its derivative, and the
residue computation `∫_{∂D_T} dz/z = 2πI`. -/

variable {β c : ℝ}

/-- The left boundary function `φ y = -β / log (|y| + 2)`. -/
def phi (β : ℝ) (y : ℝ) : ℝ := -(β / Real.log (|y| + 2))

/-- The derivative of `phi` on `(0,∞)`. -/
def PhiPos (β : ℝ) (y : ℝ) : ℝ := β / ((y + 2) * (Real.log (y + 2)) ^ 2)

/-- The derivative of `phi` on `(-∞,0)`. -/
def PhiNeg (β : ℝ) (y : ℝ) : ℝ := -(β / ((-y + 2) * (Real.log (-y + 2)) ^ 2))

/-- A piecewise formula for the derivative of `phi` (valid off `0`). -/
def Phi' (β : ℝ) (y : ℝ) : ℝ := if 0 ≤ y then PhiPos β y else PhiNeg β y

/-- The boundary curve `y ↦ φ y + i y`. -/
def gam (β : ℝ) (y : ℝ) : ℂ := (phi β y : ℂ) + (y : ℂ) * Complex.I

/-- The curve velocity with the piecewise derivative `Phi'`. -/
def gamDot (β : ℝ) (y : ℝ) : ℂ := (Phi' β y : ℂ) + Complex.I

def gamDotPos (β : ℝ) (y : ℝ) : ℂ := (PhiPos β y : ℂ) + Complex.I
def gamDotNeg (β : ℝ) (y : ℝ) : ℂ := (PhiNeg β y : ℂ) + Complex.I

lemma phi_two_pos (y : ℝ) : (0:ℝ) < |y| + 2 := by have := abs_nonneg y; linarith

lemma phi_log_pos (y : ℝ) : 0 < Real.log (|y| + 2) :=
  Real.log_pos (by have := abs_nonneg y; linarith)

lemma phi_le_zero (hβ : 0 < β) (y : ℝ) : phi β y ≤ 0 := by
  simp only [phi, neg_nonpos]
  exact div_nonneg hβ.le (Real.log_nonneg (by have := abs_nonneg y; linarith))

lemma phi_lt_c (hβ : 0 < β) (hc : 0 < c) (y : ℝ) : phi β y < c :=
  lt_of_le_of_lt (phi_le_zero hβ y) hc

lemma phi_neg (hβ : 0 < β) (y : ℝ) : phi β y < 0 := by
  rw [phi]
  exact neg_lt_zero.mpr (div_pos hβ (phi_log_pos y))

lemma phi_even (β : ℝ) (y : ℝ) : phi β (-y) = phi β y := by
  simp [phi, abs_neg]

lemma continuous_phi (β : ℝ) : Continuous (phi β) := by
  unfold phi
  exact Continuous.neg (Continuous.div continuous_const
    ((continuous_abs.add continuous_const).log (fun y => ne_of_gt (phi_two_pos y)))
    (fun y => ne_of_gt (phi_log_pos y)))

lemma phi_monotoneOn_nonneg (hβ : 0 < β) {T : ℝ} :
    MonotoneOn (phi β) (Set.Icc 0 T) := by
  intro x hx y hy hxy
  have hA : 0 < Real.log (|x| + 2) := phi_log_pos x
  have hAB : Real.log (|x| + 2) ≤ Real.log (|y| + 2) := by
    apply Real.log_le_log (phi_two_pos x)
    rw [abs_of_nonneg hx.1, abs_of_nonneg hy.1]; linarith
  have key : β / Real.log (|y| + 2) ≤ β / Real.log (|x| + 2) :=
    div_le_div_of_nonneg_left hβ.le hA hAB
  simp only [phi]; linarith [key]

lemma phi_antitoneOn_nonpos (hβ : 0 < β) {T : ℝ} :
    AntitoneOn (phi β) (Set.Icc (-T) 0) := by
  intro x hx y hy hxy
  have hB : 0 < Real.log (|y| + 2) := phi_log_pos y
  have hBA : Real.log (|y| + 2) ≤ Real.log (|x| + 2) := by
    apply Real.log_le_log (phi_two_pos y)
    rw [abs_of_nonpos hx.2, abs_of_nonpos hy.2]; linarith
  have key : β / Real.log (|x| + 2) ≤ β / Real.log (|y| + 2) :=
    div_le_div_of_nonneg_left hβ.le hB hBA
  simp only [phi]; linarith [key]

lemma hasDerivAt_phi_pos (β : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (phi β) (PhiPos β y) y := by
  have hy2 : (0:ℝ) < y + 2 := by linarith
  have hlog : Real.log (y + 2) ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  have h1 : HasDerivAt (fun s : ℝ => Real.log (s + 2)) (1 / (y + 2)) y := by
    have hlin : HasDerivAt (fun s : ℝ => s + 2) 1 y := by
      simpa using (hasDerivAt_id y).add_const 2
    exact hlin.log (ne_of_gt hy2)
  have h3 : HasDerivAt (fun s : ℝ => -(β / Real.log (s + 2)))
      (-((0 * Real.log (y + 2) - β * (1 / (y + 2))) / Real.log (y + 2) ^ 2)) y :=
    ((hasDerivAt_const y β).div h1 hlog).neg
  have h4 : HasDerivAt (fun s : ℝ => -(β / Real.log (s + 2))) (PhiPos β y) y := by
    refine h3.congr_deriv ?_
    rw [PhiPos]; field_simp; ring
  have hloc : phi β =ᶠ[𝓝 y] (fun s : ℝ => -(β / Real.log (s + 2))) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with s hs
    rw [phi, abs_of_pos hs]
  exact h4.congr_of_eventuallyEq hloc

lemma hasDerivAt_phi_neg (β : ℝ) {y : ℝ} (hy : y < 0) :
    HasDerivAt (phi β) (PhiNeg β y) y := by
  have hy2 : (0:ℝ) < -y + 2 := by linarith
  have hlog : Real.log (-y + 2) ≠ 0 := ne_of_gt (Real.log_pos (by linarith))
  have h1 : HasDerivAt (fun s : ℝ => Real.log (-s + 2)) (-1 / (-y + 2)) y := by
    have hlin : HasDerivAt (fun s : ℝ => -s + 2) (-1) y := by
      simpa using ((hasDerivAt_id y).neg).add_const 2
    exact hlin.log (ne_of_gt hy2)
  have h3 : HasDerivAt (fun s : ℝ => -(β / Real.log (-s + 2)))
      (-((0 * Real.log (-y + 2) - β * (-1 / (-y + 2))) / Real.log (-y + 2) ^ 2)) y :=
    ((hasDerivAt_const y β).div h1 hlog).neg
  have h4 : HasDerivAt (fun s : ℝ => -(β / Real.log (-s + 2))) (PhiNeg β y) y := by
    refine h3.congr_deriv ?_
    rw [PhiNeg]; field_simp; ring
  have hloc : phi β =ᶠ[𝓝 y] (fun s : ℝ => -(β / Real.log (-s + 2))) := by
    filter_upwards [isOpen_Iio.mem_nhds hy] with s hs
    rw [phi, abs_of_neg hs]
  exact h4.congr_of_eventuallyEq hloc

lemma hasDerivAt_phi {β : ℝ} {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (phi β) (Phi' β y) y := by
  rcases lt_or_gt_of_ne hy with hy | hy
  · rw [Phi', if_neg (not_le.mpr hy)]
    exact hasDerivAt_phi_neg β hy
  · rw [Phi', if_pos hy.le]
    exact hasDerivAt_phi_pos β hy

/-! ## Continuity of the velocity pieces -/

lemma continuousOn_PhiPos (β : ℝ) (T : ℝ) :
    ContinuousOn (PhiPos β) (Set.Icc 0 T) := by
  unfold PhiPos
  have hlin : ContinuousOn (fun y : ℝ => y + 2) (Set.Icc 0 T) :=
    (continuous_id.add continuous_const).continuousOn
  have hlog : ContinuousOn (fun y : ℝ => Real.log (y + 2)) (Set.Icc 0 T) :=
    hlin.log (fun y hy => ne_of_gt (by linarith [hy.1] : (0:ℝ) < y + 2))
  refine ContinuousOn.div continuousOn_const (ContinuousOn.mul hlin (hlog.pow 2)) ?_
  intro y hy
  exact mul_ne_zero (ne_of_gt (by linarith [hy.1] : (0:ℝ) < y + 2))
    (pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith [hy.1]))))

lemma continuousOn_PhiNeg (β : ℝ) (T : ℝ) :
    ContinuousOn (PhiNeg β) (Set.Icc (-T) 0) := by
  unfold PhiNeg
  have hlin : ContinuousOn (fun y : ℝ => -y + 2) (Set.Icc (-T) 0) :=
    (continuous_id.neg.add continuous_const).continuousOn
  have hlog : ContinuousOn (fun y : ℝ => Real.log (-y + 2)) (Set.Icc (-T) 0) :=
    hlin.log (fun y hy => ne_of_gt (by linarith [hy.2] : (0:ℝ) < -y + 2))
  refine ContinuousOn.neg (ContinuousOn.div continuousOn_const (ContinuousOn.mul hlin (hlog.pow 2)) ?_)
  intro y hy
  exact mul_ne_zero (ne_of_gt (by linarith [hy.2] : (0:ℝ) < -y + 2))
    (pow_ne_zero 2 (ne_of_gt (Real.log_pos (by linarith [hy.2]))))

lemma continuousOn_gamDotPos (β T : ℝ) : ContinuousOn (gamDotPos β) (Set.Icc 0 T) := by
  unfold gamDotPos
  exact (Complex.continuous_ofReal.comp_continuousOn (continuousOn_PhiPos β T)).add
    continuousOn_const

lemma continuousOn_gamDotNeg (β T : ℝ) : ContinuousOn (gamDotNeg β) (Set.Icc (-T) 0) := by
  unfold gamDotNeg
  exact (Complex.continuous_ofReal.comp_continuousOn (continuousOn_PhiNeg β T)).add
    continuousOn_const

lemma continuousOn_gamDot_nonneg (β T : ℝ) : ContinuousOn (gamDot β) (Set.Icc 0 T) := by
  refine (continuousOn_gamDotPos β T).congr (fun y hy => ?_)
  simp only [gamDot, gamDotPos, Phi', if_pos hy.1]

/-! ## Basic facts about `gam` -/

lemma gam_continuous (β : ℝ) : Continuous (gam β) := by
  unfold gam
  exact (Complex.continuous_ofReal.comp (continuous_phi β)).add
    (Complex.continuous_ofReal.mul continuous_const)

lemma hasDerivAt_gam {β : ℝ} {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (gam β) (gamDot β y) y := by
  have h1 := (hasDerivAt_phi (β:=β) hy).ofReal_comp
  have h2 : HasDerivAt (fun s : ℝ => (s : ℂ) * Complex.I) Complex.I y := by
    simpa using ((hasDerivAt_id y).ofReal_comp).mul_const Complex.I
  exact h1.add h2

lemma HasDerivAt.clog_real {g : ℝ → ℂ} {g' : ℂ} {y : ℝ} (h : HasDerivAt g g' y)
    (hmem : g y ∈ Complex.slitPlane) :
    HasDerivAt (fun t => Complex.log (g t)) (g' / g y) y := by
  have hc := (Complex.hasDerivAt_log hmem).comp y h
  rw [show (Complex.log ∘ g) = (fun t => Complex.log (g t)) from rfl] at hc
  refine hc.congr_deriv ?_
  rw [div_eq_mul_inv, mul_comm]

lemma gam_im (β : ℝ) (y : ℝ) : (gam β y).im = y := by
  simp [gam, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]

lemma gam_mem_slitPlane {β : ℝ} {y : ℝ} (hy : y ≠ 0) : gam β y ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  exact Or.inr (by rw [gam_im]; exact hy)

lemma gam_zero_re (β : ℝ) : (gam β 0).re = phi β 0 := by simp [gam]
lemma gam_zero_im (β : ℝ) : (gam β 0).im = 0 := by simp [gam]

lemma gam_zero_re_neg (hβ : 0 < β) : (gam β 0).re < 0 := by
  rw [gam_zero_re]; exact phi_neg hβ 0

lemma gam_neg_eq_conj (β : ℝ) (T : ℝ) : gam β (-T) = (starRingEnd ℂ) (gam β T) := by
  apply Complex.ext
  · simp [gam, phi_even]
  · simp [gam]

lemma gam_ne_zero_of_pos {β : ℝ} {y : ℝ} (hy : 0 < y) : gam β y ≠ 0 := by
  intro h
  have : (gam β y).im = 0 := by rw [h]; simp
  rw [gam_im] at this; linarith

lemma gam_ne_zero_of_neg {β : ℝ} {y : ℝ} (hy : y < 0) : gam β y ≠ 0 := by
  intro h
  have : (gam β y).im = 0 := by rw [h]; simp
  rw [gam_im] at this; linarith

lemma gam_ne_zero_of_eq_zero (hβ : 0 < β) : gam β 0 ≠ 0 := by
  intro h
  have : (gam β 0).re = 0 := by rw [h]; simp
  rw [gam_zero_re] at this
  exact absurd this (ne_of_lt (phi_neg hβ 0))

/-! ## The two one-sided limits of `log ∘ gam` at `0` -/

lemma tendsto_log_gam_right (hβ : 0 < β) :
    Tendsto (fun y : ℝ => Complex.log (gam β y)) (𝓝[>] 0)
      (𝓝 ((Real.log ‖gam β 0‖ : ℂ) + (Real.pi : ℂ) * Complex.I)) := by
  have hlog := Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
    (gam_zero_re_neg hβ) (gam_zero_im β)
  have hgam1 : Tendsto (gam β) (𝓝[>] 0) (𝓝 (gam β 0)) :=
    (gam_continuous β).continuousAt.tendsto.mono_left inf_le_left
  have hgam2 : Tendsto (gam β) (𝓝[>] 0) (𝓟 {z : ℂ | 0 ≤ z.im}) := by
    rw [tendsto_principal]
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [gam_im]; exact le_of_lt hy
  exact hlog.comp ((hgam1.inf hgam2).mono_left (le_inf le_rfl le_rfl))

lemma tendsto_log_gam_left (hβ : 0 < β) :
    Tendsto (fun y : ℝ => Complex.log (gam β y)) (𝓝[<] 0)
      (𝓝 ((Real.log ‖gam β 0‖ : ℂ) - (Real.pi : ℂ) * Complex.I)) := by
  have hlog := Complex.tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero
    (gam_zero_re_neg hβ) (gam_zero_im β)
  have hgam1 : Tendsto (gam β) (𝓝[<] 0) (𝓝 (gam β 0)) :=
    (gam_continuous β).continuousAt.tendsto.mono_left inf_le_left
  have hgam2 : Tendsto (gam β) (𝓝[<] 0) (𝓟 {z : ℂ | z.im < 0}) := by
    rw [tendsto_principal]
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [gam_im]; exact hy
  exact hlog.comp ((hgam1.inf hgam2).mono_left (le_inf le_rfl le_rfl))

/-! ## Integrability of the curve integrand on the two halves -/

lemma intervalIntegrable_gamDot_div_right (hβ : 0 < β) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun y : ℝ => gamDot β y / gam β y) volume 0 T := by
  have hcont : ContinuousOn (fun y : ℝ => gamDot β y / gam β y) (Set.uIcc 0 T) := by
    rw [Set.uIcc_of_le hT]
    refine ContinuousOn.div (continuousOn_gamDot_nonneg β T) (gam_continuous β).continuousOn ?_
    intro y hy
    rcases eq_or_lt_of_le hy.1 with h | h
    · rw [← h]; exact gam_ne_zero_of_eq_zero hβ
    · exact gam_ne_zero_of_pos h
  exact hcont.intervalIntegrable

lemma intervalIntegrable_gamDot_div_left (hβ : 0 < β) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun y : ℝ => gamDot β y / gam β y) volume (-T) 0 := by
  have hL : IntervalIntegrable (fun y : ℝ => gamDotNeg β y / gam β y) volume (-T) 0 := by
    have hcont : ContinuousOn (fun y : ℝ => gamDotNeg β y / gam β y) (Set.uIcc (-T) 0) := by
      rw [Set.uIcc_of_le (by linarith : -T ≤ 0)]
      refine ContinuousOn.div (continuousOn_gamDotNeg β T) (gam_continuous β).continuousOn ?_
      intro y hy
      rcases eq_or_lt_of_le hy.2 with h | h
      · rw [h]; exact gam_ne_zero_of_eq_zero hβ
      · exact gam_ne_zero_of_neg h
    exact hcont.intervalIntegrable
  refine (intervalIntegrable_congr_uIoo
    (f := fun y : ℝ => gamDot β y / gam β y)
    (g := fun y : ℝ => gamDotNeg β y / gam β y) ?_).mpr hL
  intro y hy
  rw [Set.uIoo_of_le (by linarith : -T ≤ 0)] at hy
  have hy0 : ¬ (0 ≤ y) := not_le.mpr hy.2
  simp only [gamDot, gamDotNeg, Phi', if_neg hy0]

/-! ## The five boundary integrals -/

lemma integral_curve_right (hβ : 0 < β) {T : ℝ} (hT : 0 < T) :
    ∫ y in 0..T, gamDot β y / gam β y
      = Complex.log (gam β T) - ((Real.log ‖gam β 0‖ : ℂ) + (Real.pi : ℂ) * Complex.I) := by
  have hderiv : ∀ y ∈ Set.Ioo (0:ℝ) T, HasDerivAt (fun y : ℝ => Complex.log (gam β y))
      (gamDot β y / gam β y) y := fun y hy =>
    (hasDerivAt_gam (ne_of_gt hy.1)).clog_real (gam_mem_slitPlane (ne_of_gt hy.1))
  have hlimT : Tendsto (fun y : ℝ => Complex.log (gam β y)) (𝓝[<] T)
      (𝓝 (Complex.log (gam β T))) :=
    (((gam_continuous β).continuousAt (x := T)).clog
      (gam_mem_slitPlane (ne_of_gt hT))).tendsto.mono_left inf_le_left
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a:=0) (b:=T) hT
    hderiv (intervalIntegrable_gamDot_div_right hβ hT.le) (tendsto_log_gam_right hβ) hlimT

lemma integral_curve_left (hβ : 0 < β) {T : ℝ} (hT : 0 < T) :
    ∫ y in (-T)..0, gamDot β y / gam β y
      = ((Real.log ‖gam β 0‖ : ℂ) - (Real.pi : ℂ) * Complex.I) - Complex.log (gam β (-T)) := by
  have hderiv : ∀ y ∈ Set.Ioo (-T) 0, HasDerivAt (fun y : ℝ => Complex.log (gam β y))
      (gamDot β y / gam β y) y := fun y hy =>
    (hasDerivAt_gam (ne_of_lt hy.2)).clog_real (gam_mem_slitPlane (ne_of_lt hy.2))
  have hlima : Tendsto (fun y : ℝ => Complex.log (gam β y)) (𝓝[>] (-T))
      (𝓝 (Complex.log (gam β (-T)))) :=
    (((gam_continuous β).continuousAt (x := -T)).clog
      (gam_mem_slitPlane (ne_of_lt (by linarith : -T < 0)))).tendsto.mono_left inf_le_left
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto (a:=-T) (b:=0) (by linarith)
    hderiv (intervalIntegrable_gamDot_div_left hβ hT.le) hlima (tendsto_log_gam_left hβ)

lemma integral_curve (hβ : 0 < β) {T : ℝ} (hT : 0 < T) :
    ∫ y in (-T)..T, gamDot β y / gam β y
      = Complex.log (gam β T) - Complex.log (gam β (-T)) - 2 * (Real.pi : ℂ) * Complex.I := by
  rw [← intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_gamDot_div_left hβ hT.le)
        (intervalIntegrable_gamDot_div_right hβ hT.le),
      integral_curve_left hβ hT, integral_curve_right hβ hT]
  ring

lemma integral_vertical (hc : 0 < c) {T : ℝ} (hT : 0 ≤ T) :
    Complex.I * (∫ y in (-T)..T, (((c : ℂ) + (y : ℂ) * Complex.I))⁻¹)
      = Complex.log ((c : ℂ) + (T : ℂ) * Complex.I)
        - Complex.log ((c : ℂ) - (T : ℂ) * Complex.I) := by
  have hderiv : ∀ y ∈ Set.Ioo (-T) T,
      HasDerivAt (fun y : ℝ => Complex.log ((c : ℂ) + (y : ℂ) * Complex.I))
        (Complex.I * ((c : ℂ) + (y : ℂ) * Complex.I)⁻¹) y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => (c : ℂ) + (y : ℂ) * Complex.I) Complex.I y := by
      simpa using (((hasDerivAt_id y).ofReal_comp).mul_const Complex.I).const_add (c : ℂ)
    have hmem : (c : ℂ) + (y : ℂ) * Complex.I ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; left; simpa using hc
    exact h1.clog_real hmem
  have hcont : ContinuousOn (fun y : ℝ => Complex.log ((c : ℂ) + (y : ℂ) * Complex.I))
      (Set.Icc (-T) T) := by
    refine ContinuousOn.clog ?_ ?_
    · fun_prop
    · intro y hy; rw [Complex.mem_slitPlane_iff]; left; simpa using hc
  have hint : IntervalIntegrable
      (fun y : ℝ => Complex.I * ((c : ℂ) + (y : ℂ) * Complex.I)⁻¹) volume (-T) T := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.mul continuousOn_const (ContinuousOn.inv₀ ?_ ?_)
    · fun_prop
    · intro y hy h
      have hh : ((c : ℂ) + (y : ℂ) * Complex.I).re = 0 := by rw [h]; simp
      simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im] at hh
      linarith
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (a:=-T) (b:=T) (by linarith)
    hcont hderiv hint
  rw [intervalIntegral.integral_const_mul] at h
  rw [h]
  congr 1
  rw [Complex.ofReal_neg]; ring

lemma integral_horizontal_top (hβ : 0 < β) (hc : 0 < c) {T : ℝ} (hT : 0 < T) :
    ∫ x in (phi β T)..c, ((x : ℂ) + (T : ℂ) * Complex.I)⁻¹
      = Complex.log ((c : ℂ) + (T : ℂ) * Complex.I) - Complex.log (gam β T) := by
  have hderiv : ∀ x ∈ Set.Ioo (phi β T) c,
      HasDerivAt (fun x : ℝ => Complex.log ((x : ℂ) + (T : ℂ) * Complex.I))
        (((x : ℂ) + (T : ℂ) * Complex.I))⁻¹ x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) + (T : ℂ) * Complex.I) 1 x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).const_add ((T : ℂ) * Complex.I)
    have hmem : (x : ℂ) + (T : ℂ) * Complex.I ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; right
      simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, ne_of_gt hT]
    convert (h1.clog_real hmem) using 1
    rw [div_eq_mul_inv, one_mul]
  have hcont : ContinuousOn (fun x : ℝ => Complex.log ((x : ℂ) + (T : ℂ) * Complex.I))
      (Set.Icc (phi β T) c) := by
    refine ContinuousOn.clog ?_ ?_
    · fun_prop
    · intro x hx; rw [Complex.mem_slitPlane_iff]; right
      simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, ne_of_gt hT]
  have hint : IntervalIntegrable
      (fun x : ℝ => (((x : ℂ) + (T : ℂ) * Complex.I))⁻¹) volume (phi β T) c := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.inv₀ ?_ ?_
    · fun_prop
    · intro x hx h
      have hh : ((x : ℂ) + (T : ℂ) * Complex.I).im = 0 := by rw [h]; simp
      simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im] at hh
      linarith
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (le_of_lt (phi_lt_c hβ hc T)) hcont hderiv hint
  rw [h]; congr 1

lemma integral_horizontal_bot (hβ : 0 < β) (hc : 0 < c) {T : ℝ} (hT : 0 < T) :
    ∫ x in (phi β (-T))..c, ((x : ℂ) - (T : ℂ) * Complex.I)⁻¹
      = Complex.log ((c : ℂ) - (T : ℂ) * Complex.I) - Complex.log (gam β (-T)) := by
  have hderiv : ∀ x ∈ Set.Ioo (phi β (-T)) c,
      HasDerivAt (fun x : ℝ => Complex.log ((x : ℂ) - (T : ℂ) * Complex.I))
        (((x : ℂ) - (T : ℂ) * Complex.I))⁻¹ x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => (x : ℂ) - (T : ℂ) * Complex.I) 1 x := by
      simpa using ((hasDerivAt_id x).ofReal_comp).sub_const ((T : ℂ) * Complex.I)
    have hmem : (x : ℂ) - (T : ℂ) * Complex.I ∈ Complex.slitPlane := by
      rw [Complex.mem_slitPlane_iff]; right
      simp [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, ne_of_gt hT]
    convert (h1.clog_real hmem) using 1
    rw [div_eq_mul_inv, one_mul]
  have hcont : ContinuousOn (fun x : ℝ => Complex.log ((x : ℂ) - (T : ℂ) * Complex.I))
      (Set.Icc (phi β (-T)) c) := by
    refine ContinuousOn.clog ?_ ?_
    · fun_prop
    · intro x hx; rw [Complex.mem_slitPlane_iff]; right
      simp [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, ne_of_gt hT]
  have hint : IntervalIntegrable
      (fun x : ℝ => (((x : ℂ) - (T : ℂ) * Complex.I))⁻¹) volume (phi β (-T)) c := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.inv₀ ?_ ?_
    · fun_prop
    · intro x hx h
      have hh : ((x : ℂ) - (T : ℂ) * Complex.I).im = 0 := by rw [h]; simp
      simp [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im] at hh
      linarith
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (le_of_lt (phi_lt_c hβ hc (-T))) hcont hderiv hint
  rw [h, gam, Complex.ofReal_neg]; congr 1; ring

/-- **The residue computation**: the integral of `dz/z` over the closed contour `∂D_T`
equals `2πI`. -/
lemma boundary_inv (hβ : 0 < β) (hc : 0 < c) {T : ℝ} (hT : 0 < T) :
    Complex.I * (∫ y in (-T)..T, (((c : ℂ) + (y : ℂ) * Complex.I))⁻¹)
      - (∫ y in (-T)..T, gamDot β y / gam β y)
      - (∫ x in (phi β T)..c, (((x : ℂ) + (T : ℂ) * Complex.I))⁻¹)
      + (∫ x in (phi β (-T))..c, (((x : ℂ) - (T : ℂ) * Complex.I))⁻¹)
      = 2 * (Real.pi : ℂ) * Complex.I := by
  rw [integral_vertical hc hT.le, integral_curve hβ hT,
    integral_horizontal_top hβ hc hT, integral_horizontal_bot hβ hc hT]
  ring


/-- The boundary integral functional `X ↦ ∫_{∂D_T} X`. -/
def Bfun (β c : ℝ) (X : ℂ → ℂ) (T : ℝ) : ℂ :=
  Complex.I * (∫ y in (-T)..T, X ((c : ℂ) + (y : ℂ) * Complex.I))
    - (∫ y in (-T)..T, X (gam β y) * gamDot β y)
    - (∫ x in (phi β T)..c, X ((x : ℂ) + (T : ℂ) * Complex.I))
    + (∫ x in (phi β (-T))..c, X ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))

lemma Bfun_inv (hβ : 0 < β) (hc : 0 < c) {T : ℝ} (hT : 0 < T) :
    Bfun β c (fun z => z⁻¹) T = 2 * (Real.pi : ℂ) * Complex.I := by
  rw [Bfun]
  have hcurve : (∫ y in (-T)..T, (gam β y)⁻¹ * gamDot β y)
      = (∫ y in (-T)..T, gamDot β y / gam β y) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro y _; rw [div_eq_mul_inv, mul_comm]
  have hbot : (∫ x in (phi β (-T))..c, ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)⁻¹)
      = (∫ x in (phi β (-T))..c, ((x : ℂ) - (T : ℂ) * Complex.I)⁻¹) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro x _
    congr 1
    push_cast
    ring
  rw [hcurve, hbot]
  exact boundary_inv hβ hc hT

/-! ## A holomorphic extension of `z ↦ g z - r/z` at the origin -/

/-- A small radius such that the ball around `0` of this radius is contained in the
domain of holomorphy of `z ↦ g z - r/z`. -/
def rho (β c : ℝ) : ℝ := min (c / 2) (min (β / (2 * Real.log 2)) (1 / 2))

lemma rho_pos (hβ : 0 < β) (hc : 0 < c) : 0 < rho β c := by
  refine lt_min (by linarith) (lt_min (div_pos hβ (by positivity)) (by norm_num))

lemma rho_le_c (β c : ℝ) : rho β c ≤ c / 2 := min_le_left _ _

lemma rho_le_beta (β c : ℝ) : rho β c ≤ β / (2 * Real.log 2) :=
  le_trans (min_le_right _ _) (min_le_left _ _)

lemma rho_le_half (β c : ℝ) : rho β c ≤ 1 / 2 :=
  le_trans (min_le_right _ _) (min_le_right _ _)

lemma phi_le_re_of_mem_ball (hβ : 0 < β) (hc : 0 < c) {z : ℂ}
    (hz : z ∈ Metric.ball 0 (rho β c)) : phi β z.im ≤ z.re ∧ z.re ≤ c := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have hzre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hzim : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have hzn : ‖z‖ < rho β c := by simpa using hz
  refine ⟨?_, ?_⟩
  · have hlog_le : Real.log (|z.im| + 2) ≤ 2 * Real.log 2 := by
      have h2 : (0:ℝ) < |z.im| + 2 := phi_two_pos z.im
      have h3 : |z.im| + 2 ≤ 4 := by
        have h4 : |z.im| < 1/2 := lt_of_lt_of_le (lt_of_le_of_lt hzim hzn) (rho_le_half β c)
        linarith
      calc Real.log (|z.im| + 2) ≤ Real.log 4 := (Real.log_le_log h2 h3)
        _ = 2 * Real.log 2 := by
            rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]; push_cast; ring
    have h5 : β / Real.log (|z.im| + 2) ≥ β / (2 * Real.log 2) := by
      exact div_le_div_of_nonneg_left hβ.le (phi_log_pos z.im) hlog_le
    have h6 : -z.re < rho β c := by
      have := abs_lt.mp (lt_of_le_of_lt hzre hzn)
      linarith [this.2]
    have h7 : β / (2 * Real.log 2) ≥ rho β c := rho_le_beta β c
    simp only [phi]
    linarith
  · have hre : z.re < rho β c := lt_of_le_of_lt (le_trans (le_abs_self _) hzre) hzn
    linarith [rho_le_c β c]

/-- The function `z ↦ g z - r/z`. -/
def f0 (g : ℂ → ℂ) (r : ℂ) : ℂ → ℂ := fun z => g z - r / z

/-- The holomorphic extension of `z ↦ g z - r/z` at the origin (when `z * g z → r`). -/
def gExt (g : ℂ → ℂ) (r : ℂ) : ℂ → ℂ :=
  Function.update (f0 g r) 0 ((𝓝[≠] 0).limUnder (f0 g r))

lemma gExt_eq_of_ne (g : ℂ → ℂ) (r : ℂ) {z : ℂ} (hz : z ≠ 0) :
    gExt g r z = g z - r / z := by
  simp [gExt, f0, Function.update_of_ne hz]

lemma f0_littleO {g : ℂ → ℂ} {r : ℂ}
    (hres : Tendsto (fun z : ℂ => z * g z) (𝓝[≠] 0) (𝓝 r)) :
    (fun z => f0 g r z - f0 g r 0) =o[𝓝[≠] 0] (fun z => z⁻¹) := by
  refine Asymptotics.IsLittleO.of_bound (fun c hc => ?_)
  have hψ : Tendsto (fun z : ℂ => z * g z - r - z * g 0) (𝓝[≠] 0) (𝓝 0) := by
    have h1 : Tendsto (fun z : ℂ => z * g z - r) (𝓝[≠] 0) (𝓝 0) := by
      simpa using hres.sub (tendsto_const_nhds : Tendsto (fun _ : ℂ => r) (𝓝[≠] 0) (𝓝 r))
    have h2 : Tendsto (fun z : ℂ => z * g 0) (𝓝[≠] 0) (𝓝 0) := by
      have : Tendsto (fun z : ℂ => z) (𝓝[≠] 0) (𝓝 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      simpa using this.mul tendsto_const_nhds
    simpa using h1.sub h2
  filter_upwards [(Metric.tendsto_nhds.mp hψ c hc), self_mem_nhdsWithin] with z hzc hzne
  have hz0 : z ≠ 0 := by simpa using hzne
  have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [dist_zero_right] at hzc
  have hkey : z * ((g z - r / z) - (g 0 - r / 0)) = z * g z - r - z * g 0 := by
    rw [div_zero, sub_zero]
    field_simp <;> ring
  have h1 : ‖z * ((g z - r / z) - (g 0 - r / 0))‖ < c := by rw [hkey]; exact hzc
  rw [norm_mul] at h1
  simp only [f0]
  rw [norm_inv, ← div_eq_mul_inv, le_div_iff₀ hzn]
  exact (calc ‖(g z - r / z) - (g 0 - r / 0)‖ * ‖z‖
        = ‖z‖ * ‖(g z - r / z) - (g 0 - r / 0)‖ := by ring
    _ < c := h1).le

lemma gExt_differentiableAt_zero {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {g : ℂ → ℂ} {r : ℂ}
    (hdiff : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ c → z ≠ 0 →
      DifferentiableAt ℂ g z)
    (hres : Tendsto (fun z : ℂ => z * g z) (𝓝[≠] 0) (𝓝 r)) :
    DifferentiableAt ℂ (gExt g r) 0 := by
  have hρ : 0 < rho β c := rho_pos hβ hc
  have hd : DifferentiableOn ℂ (f0 g r) (Metric.ball 0 (rho β c) \ {0}) := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz.2
    have hreg := phi_le_re_of_mem_ball hβ hc hz.1
    refine (hdiff z (by simpa only [phi] using hreg.1) hreg.2 hz0).differentiableWithinAt.sub ?_
    exact ((differentiableAt_const r).div differentiableAt_id hz0).differentiableWithinAt
  have ho : (fun z => f0 g r z - f0 g r 0) =o[𝓝[≠] 0] (fun z => (z - 0)⁻¹) := by
    simpa only [sub_zero] using f0_littleO (g := g) (r := r) hres
  have h := Complex.differentiableOn_update_limUnder_of_isLittleO
    (s := Metric.ball 0 (rho β c)) (Metric.ball_mem_nhds 0 hρ) hd ho
  exact h.differentiableAt (Metric.ball_mem_nhds 0 hρ)

lemma gExt_differentiableAt {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {g : ℂ → ℂ} {r : ℂ}
    (hdiff : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ c → z ≠ 0 →
      DifferentiableAt ℂ g z)
    (hres : Tendsto (fun z : ℂ => z * g z) (𝓝[≠] 0) (𝓝 r)) {z : ℂ} (hz1 : phi β z.im ≤ z.re)
    (hz2 : z.re ≤ c) : DifferentiableAt ℂ (gExt g r) z := by
  rcases eq_or_ne z 0 with rfl | hz
  · exact gExt_differentiableAt_zero hβ hc hdiff hres
  · have hd : DifferentiableAt ℂ (fun w => g w - r / w) z :=
      (hdiff z (by simpa only [phi] using hz1) hz2 hz).sub
        ((differentiableAt_const r).div differentiableAt_id hz)
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [isOpen_ne.mem_nhds hz] with w hw
    exact gExt_eq_of_ne g r hw


/-! ## The graph-region boundary functional and reflection in the real axis -/

/-- Boundary functional of the region `{a ≤ im ≤ b, φ im ≤ re ≤ c}`:
`I ∫ F(c+yi) dy - ∫ F(φ y + y i) (φ' y + i) dy - ∫_{φ b}^c F(x + b i) dx
+ ∫_{φ a}^c F(x + a i) dx`. -/
def GR (F : ℂ → ℂ) (φ φ' : ℝ → ℝ) (c a b : ℝ) : ℂ :=
  Complex.I * (∫ y in a..b, F ((c : ℂ) + (y : ℂ) * Complex.I))
    - (∫ y in a..b, F ((φ y : ℂ) + (y : ℂ) * Complex.I) * ((φ' y : ℂ) + Complex.I))
    - (∫ x in (φ b)..c, F ((x : ℂ) + (b : ℂ) * Complex.I))
    + (∫ x in (φ a)..c, F ((x : ℂ) + (a : ℂ) * Complex.I))

lemma GR_congr {F : ℂ → ℂ} {φ₁ φ₂ φ₁' φ₂' : ℝ → ℝ} {c a b : ℝ}
    (h₁ : φ₁ = φ₂) (h₂ : φ₁' = φ₂') : GR F φ₁ φ₁' c a b = GR F φ₂ φ₂' c a b := by
  rw [h₁, h₂]

/-- Substitution `y ↦ -u` in an interval integral. -/
lemma integral_comp_neg' (f : ℝ → ℂ) (a b : ℝ) :
    (∫ y in a..b, f y) = ∫ u in -b..-a, f (-u) := by
  have h := intervalIntegral.integral_comp_neg (a := -b) (b := -a) (f := f)
  rw [neg_neg, neg_neg] at h
  exact h.symm

/-- Reflection in the real axis: the boundary functional for `F` and `φ` on `[a,b]` equals
minus the conjugate of the boundary functional for `z ↦ conj (F (conj z))` and
`u ↦ φ (-u)` on `[-b,-a]`. -/
lemma GR_conj_reflect (F : ℂ → ℂ) (φ φ' : ℝ → ℝ) (c a b : ℝ) :
    GR F φ φ' c a b
      = - conj (GR (fun z => conj (F (conj z))) (fun u => φ (-u)) (fun u => -φ' (-u))
          c (-b) (-a)) := by
  rw [GR, GR]
  have hconj1 : ∀ u : ℝ, conj ((c : ℂ) + (u : ℂ) * Complex.I)
      = (c : ℂ) + ((-u : ℝ) : ℂ) * Complex.I := by
    intro u
    rw [map_add, map_mul]
    simp only [Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hconj2 : ∀ x : ℝ, conj ((x : ℂ) + ((-a : ℝ) : ℂ) * Complex.I)
      = (x : ℂ) + (a : ℂ) * Complex.I := by
    intro x
    rw [map_add, map_mul]
    simp only [Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have hconj3 : ∀ x : ℝ, conj ((x : ℂ) + ((-b : ℝ) : ℂ) * Complex.I)
      = (x : ℂ) + (b : ℂ) * Complex.I := by
    intro x
    rw [map_add, map_mul]
    simp only [Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have h1 : (∫ y in a..b, F ((c : ℂ) + (y : ℂ) * Complex.I))
      = conj (∫ u in (-b)..(-a), conj (F (conj ((c : ℂ) + (u : ℂ) * Complex.I)))) := by
    have hpt : ∀ u : ℝ, F ((c : ℂ) + ((-u : ℝ) : ℂ) * Complex.I)
        = conj (conj (F (conj ((c : ℂ) + (u : ℂ) * Complex.I)))) := by
      intro u; rw [Complex.conj_conj, hconj1 u]
    rw [integral_comp_neg']
    rw [intervalIntegral.integral_congr (fun u _ => hpt u)]
    exact intervalIntegral_conj
  have h2 : (∫ y in a..b, F ((φ y : ℂ) + (y : ℂ) * Complex.I) * ((φ' y : ℂ) + Complex.I))
      = - conj (∫ u in (-b)..(-a), conj (F (conj ((φ (-u) : ℂ) + (u : ℂ) * Complex.I)))
          * (((-φ' (-u) : ℝ) : ℂ) + Complex.I)) := by
    have hpt : ∀ u : ℝ, F ((φ (-u) : ℂ) + ((-u : ℝ) : ℂ) * Complex.I) * ((φ' (-u) : ℂ) + Complex.I)
        = - conj (conj (F (conj ((φ (-u) : ℂ) + (u : ℂ) * Complex.I)))
          * (((-φ' (-u) : ℝ) : ℂ) + Complex.I)) := by
      intro u
      simp only [map_mul, map_add, Complex.conj_ofReal, Complex.conj_I, Complex.conj_conj]
      push_cast
      ring
    rw [integral_comp_neg']
    rw [intervalIntegral.integral_congr (fun u _ => hpt u)]
    rw [intervalIntegral.integral_neg, intervalIntegral_conj]
  have h3 : (∫ x in (φ a)..c, F ((x : ℂ) + (a : ℂ) * Complex.I))
      = conj (∫ x in (φ (-(-a)))..c, conj (F (conj ((x : ℂ) + ((-a : ℝ) : ℂ) * Complex.I)))) := by
    have hpt : ∀ x : ℝ, F ((x : ℂ) + (a : ℂ) * Complex.I)
        = conj (conj (F (conj ((x : ℂ) + ((-a : ℝ) : ℂ) * Complex.I)))) := by
      intro x; rw [Complex.conj_conj, hconj2 x]
    rw [neg_neg, ← intervalIntegral_conj]
    exact intervalIntegral.integral_congr (fun x _ => hpt x)
  have h4 : (∫ x in (φ b)..c, F ((x : ℂ) + (b : ℂ) * Complex.I))
      = conj (∫ x in (φ (-(-b)))..c, conj (F (conj ((x : ℂ) + ((-b : ℝ) : ℂ) * Complex.I)))) := by
    have hpt : ∀ x : ℝ, F ((x : ℂ) + (b : ℂ) * Complex.I)
        = conj (conj (F (conj ((x : ℂ) + ((-b : ℝ) : ℂ) * Complex.I)))) := by
      intro x; rw [Complex.conj_conj, hconj3 x]
    rw [neg_neg, ← intervalIntegral_conj]
    exact intervalIntegral.integral_congr (fun x _ => hpt x)
  rw [h1, h2, h3, h4]
  simp only [map_add, map_sub, map_mul, Complex.conj_I]
  ring

/-! ## The two half-contour functionals -/

/-- Boundary functional of the upper half region `{0 ≤ im ≤ T, φ im ≤ re ≤ c}`. -/
def Bh (β c : ℝ) (X : ℂ → ℂ) (T : ℝ) : ℂ :=
  Complex.I * (∫ y in (0:ℝ)..T, X ((c : ℂ) + (y : ℂ) * Complex.I))
  - (∫ y in (0:ℝ)..T, X (gam β y) * gamDotPos β y)
  - (∫ x in (phi β T)..c, X ((x : ℂ) + (T : ℂ) * Complex.I))
  + (∫ x in (phi β 0)..c, X ((x : ℂ) + (0 : ℂ) * Complex.I))

/-- Boundary functional of the lower half region `{-T ≤ im ≤ 0, φ im ≤ re ≤ c}`. -/
def Bl (β c : ℝ) (X : ℂ → ℂ) (T : ℝ) : ℂ :=
  Complex.I * (∫ y in (-T)..0, X ((c : ℂ) + (y : ℂ) * Complex.I))
  - (∫ y in (-T)..0, X (gam β y) * gamDotNeg β y)
  - (∫ x in (phi β 0)..c, X ((x : ℂ) + (0 : ℂ) * Complex.I))
  + (∫ x in (phi β (-T))..c, X ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))

lemma Bh_eq_GR (X : ℂ → ℂ) (T : ℝ) : Bh β c X T = GR X (phi β) (PhiPos β) c 0 T := by
  simp only [Bh, GR, gam, gamDotPos]
  norm_num

lemma Bl_eq_GR (X : ℂ → ℂ) (T : ℝ) : Bl β c X T = GR X (phi β) (PhiNeg β) c (-T) 0 := by
  simp only [Bl, GR, gam, gamDotNeg]
  norm_num

/-! ## Continuity of the relevant composed functions -/

lemma continuous_gExt_vert {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {g : ℂ → ℂ} {r : ℂ}
    (hdiff : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ c → z ≠ 0 →
      DifferentiableAt ℂ g z)
    (hres : Tendsto (fun z : ℂ => z * g z) (𝓝[≠] 0) (𝓝 r)) :
    Continuous (fun y : ℝ => gExt g r ((c : ℂ) + (y : ℂ) * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hy : ((c : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
  have hr : ((c : ℂ) + (y : ℂ) * Complex.I).re = c := by simp
  refine (gExt_differentiableAt hβ hc hdiff hres ?_ ?_).continuousAt.comp ?_
  · rw [hy, hr]; exact (phi_lt_c hβ hc y).le
  · rw [hr]
  · fun_prop

lemma continuous_gExt_gam {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {g : ℂ → ℂ} {r : ℂ}
    (hdiff : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ c → z ≠ 0 →
      DifferentiableAt ℂ g z)
    (hres : Tendsto (fun z : ℂ => z * g z) (𝓝[≠] 0) (𝓝 r)) :
    Continuous (fun y : ℝ => gExt g r (gam β y)) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hy : (gam β y).im = y := gam_im β y
  have hr : (gam β y).re = phi β y := by simp [gam]
  refine (gExt_differentiableAt hβ hc hdiff hres ?_ ?_).continuousAt.comp
    (gam_continuous β).continuousAt
  · rw [hy, hr]
  · rw [hr]; exact (phi_lt_c hβ hc y).le

lemma gam_ne_zero (hβ : 0 < β) (y : ℝ) : gam β y ≠ 0 := by
  rcases lt_trichotomy y 0 with h | h | h
  · exact gam_ne_zero_of_neg h
  · subst h; exact gam_ne_zero_of_eq_zero hβ
  · exact gam_ne_zero_of_pos h

lemma continuous_g_gam {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {g : ℂ → ℂ}
    (hdiff : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ c → z ≠ 0 →
      DifferentiableAt ℂ g z) :
    Continuous (fun y : ℝ => g (gam β y)) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hy : (gam β y).im = y := gam_im β y
  have hr : (gam β y).re = phi β y := by simp [gam]
  refine (hdiff (gam β y) ?_ ?_ (gam_ne_zero hβ y)).continuousAt.comp
    (gam_continuous β).continuousAt
  · rw [hy, hr]; simp [phi]
  · rw [hr]; exact (phi_lt_c hβ hc y).le

lemma continuous_inv_gam {β : ℝ} (hβ : 0 < β) : Continuous (fun y : ℝ => (gam β y)⁻¹) := by
  refine Continuous.inv₀ (gam_continuous β) ?_
  intro y
  rcases lt_trichotomy y 0 with h | h | h
  · exact gam_ne_zero_of_neg h
  · subst h; exact gam_ne_zero_of_eq_zero hβ
  · exact gam_ne_zero_of_pos h



/-! ## Applications of the graph-region Cauchy theorem -/

lemma Bh_gExt_zero {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {g : ℂ → ℂ} {r : ℂ}
    (hdiff : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ c → z ≠ 0 →
      DifferentiableAt ℂ g z)
    (hres : Tendsto (fun z : ℂ => z * g z) (𝓝[≠] 0) (𝓝 r)) {T : ℝ} (hT : 0 < T) :
    Bh β c (gExt g r) T = 0 := by
  have h := graph_region_cauchy_mono (gExt g r) (phi β) (PhiPos β) c 0 T hT.le
    (fun y _ => (phi_lt_c hβ hc y).le) (continuous_phi β).continuousOn
    (continuousOn_PhiPos β T)
    (fun y hy => hasDerivAt_phi_pos β hy.1)
    (phi_monotoneOn_nonneg hβ)
    (fun z _ _ h3 h4 => gExt_differentiableAt hβ hc hdiff hres h3 h4)
  rw [Bh_eq_GR]
  exact h

lemma Bl_gExt_zero {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {g : ℂ → ℂ} {r : ℂ}
    (hdiff : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ c → z ≠ 0 →
      DifferentiableAt ℂ g z)
    (hres : Tendsto (fun z : ℂ => z * g z) (𝓝[≠] 0) (𝓝 r)) {T : ℝ} (hT : 0 < T) :
    Bl β c (gExt g r) T = 0 := by
  have hH : ∀ z : ℂ, 0 ≤ z.im → z.im ≤ T → phi β z.im ≤ z.re → z.re ≤ c →
      DifferentiableAt ℂ (fun z => conj (gExt g r (conj z))) z := by
    intro z h1 h2 h3 h4
    have hz : DifferentiableAt ℂ (gExt g r) (conj z) := by
      refine gExt_differentiableAt hβ hc hdiff hres ?_ ?_
      · rw [Complex.conj_im, Complex.conj_re, phi_even]
        exact h3
      · simpa using h4
    exact (differentiableAt_conj_conj_iff (f := gExt g r)).mpr (by simpa using hz)
  have hmono := graph_region_cauchy_mono (fun z => conj (gExt g r (conj z))) (phi β) (PhiPos β)
    c 0 T hT.le (fun y _ => (phi_lt_c hβ hc y).le) (continuous_phi β).continuousOn
    (continuousOn_PhiPos β T) (fun y hy => hasDerivAt_phi_pos β hy.1)
    (phi_monotoneOn_nonneg hβ) hH
  have hfun1 : (fun u : ℝ => phi β (-u)) = phi β := by
    funext u; exact phi_even β u
  have hfun2 : (fun u : ℝ => -PhiNeg β (-u)) = PhiPos β := by
    funext u
    simp only [PhiPos, PhiNeg]
    ring
  have hr := GR_conj_reflect (gExt g r) (phi β) (PhiNeg β) c (-T) 0
  have hcongr := GR_congr (F := fun z => conj (gExt g r (conj z))) (c := c) (a := 0) (b := T)
    hfun1 hfun2
  rw [Bl_eq_GR, hr]
  simp only [neg_zero, neg_neg]
  rw [hcongr]
  rw [show GR (fun z => conj (gExt g r (conj z))) (phi β) (PhiPos β) c 0 T = 0 from hmono]
  simp
lemma integral_congr_Ioc_pos {F G : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (h : ∀ y ∈ Set.Ioc (0:ℝ) T, F y = G y) :
    (∫ y in (0:ℝ)..T, F y) = ∫ y in (0:ℝ)..T, G y := by
  refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro y hy
  rw [Set.uIoc_of_le hT] at hy
  exact h y hy

lemma ae_ne_zero : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ (0:ℝ) := by
  rw [MeasureTheory.ae_iff]; simp

lemma integral_congr_Ioc_neg {F G : ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (h : ∀ y ∈ Set.Ioo (-T) 0, F y = G y) :
    (∫ y in (-T)..0, F y) = ∫ y in (-T)..0, G y := by
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_ne_zero] with y hy hyI
  rw [Set.uIoc_of_le (by linarith : -T ≤ 0)] at hyI
  exact h y ⟨hyI.1, lt_of_le_of_ne hyI.2 hy⟩

lemma Bfun_eq_Bh_Bl {X : ℂ → ℂ} {T : ℝ} (hT : 0 < T)
    (hv1 : IntervalIntegrable (fun y => X ((c : ℂ) + (y : ℂ) * Complex.I)) volume (-T) 0)
    (hv2 : IntervalIntegrable (fun y => X ((c : ℂ) + (y : ℂ) * Complex.I)) volume 0 T)
    (hw1 : IntervalIntegrable (fun y => X (gam β y) * gamDot β y) volume (-T) 0)
    (hw2 : IntervalIntegrable (fun y => X (gam β y) * gamDot β y) volume 0 T)
    (hw1' : IntervalIntegrable (fun y => X (gam β y) * gamDotNeg β y) volume (-T) 0)
    (hw2' : IntervalIntegrable (fun y => X (gam β y) * gamDotPos β y) volume 0 T) :
    Bfun β c X T = Bh β c X T + Bl β c X T := by
  have hcw1 : (∫ y in (-T)..0, X (gam β y) * gamDot β y)
      = ∫ y in (-T)..0, X (gam β y) * gamDotNeg β y :=
    integral_congr_Ioc_neg hT.le (fun y hy => by
      simp only [gamDot, gamDotNeg, Phi', if_neg (not_le.mpr hy.2)])
  have hcw2 : (∫ y in (0:ℝ)..T, X (gam β y) * gamDot β y)
      = ∫ y in (0:ℝ)..T, X (gam β y) * gamDotPos β y :=
    integral_congr_Ioc_pos hT.le (fun y hy => by
      simp only [gamDot, gamDotPos, Phi', if_pos hy.1.le])
  rw [Bfun, Bh, Bl,
    ← intervalIntegral.integral_add_adjacent_intervals hv1 hv2,
    ← intervalIntegral.integral_add_adjacent_intervals hw1 hw2, hcw1, hcw2]
  ring


/-! ## Applications of the graph-region Cauchy theorem -/

lemma integral_gExt_eq {β c : ℝ} {g : ℂ → ℂ} {r : ℂ} {a b : ℝ} {path : ℝ → ℂ}
    (hpath : ∀ t, path t ≠ 0)
    (h1 : IntervalIntegrable (fun t => g (path t)) volume a b)
    (h2 : IntervalIntegrable (fun t => (path t)⁻¹) volume a b) :
    (∫ t in a..b, gExt g r (path t))
      = (∫ t in a..b, g (path t)) - r * ∫ t in a..b, (path t)⁻¹ := by
  have heq : (∫ t in a..b, gExt g r (path t))
      = ∫ t in a..b, (g (path t) - r * (path t)⁻¹) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun t _ => ?_))
    rw [gExt_eq_of_ne g r (hpath t), div_eq_mul_inv]
  rw [heq, intervalIntegral.integral_sub h1 (h2.const_mul r),
    intervalIntegral.integral_const_mul]

lemma integral_gExt_mul {β c : ℝ} {g : ℂ → ℂ} {r : ℂ} {a b : ℝ} {path W : ℝ → ℂ}
    (hpath : ∀ t, path t ≠ 0)
    (h1 : IntervalIntegrable (fun t => g (path t) * W t) volume a b)
    (h2 : IntervalIntegrable (fun t => (path t)⁻¹ * W t) volume a b) :
    (∫ t in a..b, gExt g r (path t) * W t)
      = (∫ t in a..b, g (path t) * W t) - r * ∫ t in a..b, (path t)⁻¹ * W t := by
  have heq : (∫ t in a..b, gExt g r (path t) * W t)
      = ∫ t in a..b, (g (path t) * W t - r * ((path t)⁻¹ * W t)) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun t _ => ?_))
    rw [gExt_eq_of_ne g r (hpath t)]; ring
  rw [heq, intervalIntegral.integral_sub h1 (h2.const_mul r),
    intervalIntegral.integral_const_mul]


/-! ## Integrability on the two halves of the curve -/

lemma intervalIntegrable_gamDot_left {β : ℝ} {X : ℂ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (h : IntervalIntegrable (fun y => X (gam β y) * gamDotNeg β y) volume (-T) 0) :
    IntervalIntegrable (fun y => X (gam β y) * gamDot β y) volume (-T) 0 :=
  (intervalIntegrable_congr_uIoo
    (f := fun y => X (gam β y) * gamDot β y)
    (g := fun y => X (gam β y) * gamDotNeg β y) (by
      intro y hy
      rw [Set.uIoo_of_le (by linarith : -T ≤ 0)] at hy
      simp only [gamDot, gamDotNeg, Phi', if_neg (not_le.mpr hy.2)])).mpr h

lemma intervalIntegrable_X_gamDot_right {β : ℝ} {X : ℂ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (h : ContinuousOn (fun y => X (gam β y) * gamDot β y) (Set.Icc 0 T)) :
    IntervalIntegrable (fun y => X (gam β y) * gamDot β y) volume 0 T := by
  apply ContinuousOn.intervalIntegrable
  rwa [Set.uIcc_of_le hT]

lemma intervalIntegrable_X_gamDot_left {β : ℝ} {X : ℂ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (h : ContinuousOn (fun y => X (gam β y) * gamDotNeg β y) (Set.Icc (-T) 0)) :
    IntervalIntegrable (fun y => X (gam β y) * gamDotNeg β y) volume (-T) 0 := by
  apply ContinuousOn.intervalIntegrable
  rwa [Set.uIcc_of_le (by linarith : -T ≤ 0)]

lemma intervalIntegrable_gamDot {β : ℝ} {X : ℂ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hL : IntervalIntegrable (fun y => X (gam β y) * gamDotNeg β y) volume (-T) 0)
    (hR : IntervalIntegrable (fun y => X (gam β y) * gamDot β y) volume 0 T) :
    IntervalIntegrable (fun y => X (gam β y) * gamDot β y) volume (-T) T :=
  (intervalIntegrable_gamDot_left hT hL).trans hR

/-! ## `Bfun (gExt) = 0` -/

lemma Bfun_gExt_zero {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {g : ℂ → ℂ} {r : ℂ}
    (hdiff : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ c → z ≠ 0 →
      DifferentiableAt ℂ g z)
    (hres : Tendsto (fun z : ℂ => z * g z) (𝓝[≠] 0) (𝓝 r)) {T : ℝ} (hT : 0 < T) :
    Bfun β c (gExt g r) T = 0 := by
  have hv : Continuous (fun y : ℝ => gExt g r ((c : ℂ) + (y : ℂ) * Complex.I)) :=
    continuous_gExt_vert hβ hc hdiff hres
  have hgm : Continuous (fun y : ℝ => gExt g r (gam β y)) :=
    continuous_gExt_gam hβ hc hdiff hres
  have hw1 : IntervalIntegrable (fun y : ℝ => gExt g r (gam β y) * gamDotNeg β y)
      volume (-T) 0 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith : -T ≤ 0)]
    exact hgm.continuousOn.mul (continuousOn_gamDotNeg β T)
  have hw2 : IntervalIntegrable (fun y : ℝ => gExt g r (gam β y) * gamDotPos β y)
      volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT.le]
    exact hgm.continuousOn.mul (continuousOn_gamDotPos β T)
  have hw2' : IntervalIntegrable (fun y : ℝ => gExt g r (gam β y) * gamDot β y)
      volume 0 T := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hT.le]
    exact hgm.continuousOn.mul (continuousOn_gamDot_nonneg β T)
  rw [Bfun_eq_Bh_Bl (X := gExt g r) hT (hv.intervalIntegrable _ _)
      (hv.intervalIntegrable _ _) (intervalIntegrable_gamDot_left hT.le hw1) hw2' hw1 hw2,
    Bh_gExt_zero hβ hc hdiff hres hT, Bl_gExt_zero hβ hc hdiff hres hT]
  ring

/-! ## Linearity of `Bfun` -/

lemma integral_g_eq_one {β : ℝ} {g : ℂ → ℂ} {r : ℂ} {a b : ℝ} {path : ℝ → ℂ}
    (hpath : ∀ t, path t ≠ 0)
    (h1 : IntervalIntegrable (fun t => g (path t)) volume a b)
    (h2 : IntervalIntegrable (fun t => gExt g r (path t)) volume a b)
    (h3 : IntervalIntegrable (fun t => (path t)⁻¹) volume a b) :
    (∫ t in a..b, g (path t))
      = (∫ t in a..b, gExt g r (path t)) + r * ∫ t in a..b, (path t)⁻¹ := by
  have heq : (∫ t in a..b, g (path t))
      = ∫ t in a..b, (gExt g r (path t) + r * (path t)⁻¹) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun t _ => ?_))
    rw [gExt_eq_of_ne g r (hpath t), div_eq_mul_inv]; ring
  rw [heq, intervalIntegral.integral_add h2 (h3.const_mul r),
    intervalIntegral.integral_const_mul]

lemma integral_g_eq_mul {β : ℝ} {g : ℂ → ℂ} {r : ℂ} {a b : ℝ} {path W : ℝ → ℂ}
    (hpath : ∀ t, path t ≠ 0)
    (h1 : IntervalIntegrable (fun t => g (path t) * W t) volume a b)
    (h2 : IntervalIntegrable (fun t => gExt g r (path t) * W t) volume a b)
    (h3 : IntervalIntegrable (fun t => (path t)⁻¹ * W t) volume a b) :
    (∫ t in a..b, g (path t) * W t)
      = (∫ t in a..b, gExt g r (path t) * W t) + r * ∫ t in a..b, (path t)⁻¹ * W t := by
  have heq : (∫ t in a..b, g (path t) * W t)
      = ∫ t in a..b, (gExt g r (path t) * W t + r * ((path t)⁻¹ * W t)) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun t _ => ?_))
    rw [gExt_eq_of_ne g r (hpath t), div_eq_mul_inv]; ring
  rw [heq, intervalIntegral.integral_add h2 (h3.const_mul r),
    intervalIntegral.integral_const_mul]

lemma continuous_g_vert {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {g : ℂ → ℂ}
    (hdiff : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ c → z ≠ 0 →
      DifferentiableAt ℂ g z) :
    Continuous (fun y : ℝ => g ((c : ℂ) + (y : ℂ) * Complex.I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hy : ((c : ℂ) + (y : ℂ) * Complex.I).im = y := by simp
  have hr : ((c : ℂ) + (y : ℂ) * Complex.I).re = c := by simp
  have hz0 : ((c : ℂ) + (y : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have : ((c : ℂ) + (y : ℂ) * Complex.I).re = 0 := by rw [h]; simp
    rw [hr] at this; exact absurd this (ne_of_gt hc)
  exact ContinuousAt.comp (f := fun y : ℝ => (c : ℂ) + (y : ℂ) * Complex.I) (g := g) (x := y)
    (hdiff _ (by rw [hy, hr]; exact (phi_lt_c hβ hc y).le) (by rw [hr]) hz0).continuousAt
    (by fun_prop)

lemma continuousOn_gExt_horiz {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {g : ℂ → ℂ} {r : ℂ}
    (hdiff : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ c → z ≠ 0 →
      DifferentiableAt ℂ g z)
    (hres : Tendsto (fun z : ℂ => z * g z) (𝓝[≠] 0) (𝓝 r)) (s : ℝ) :
    ContinuousOn (fun x : ℝ => gExt g r ((x : ℂ) + (s : ℂ) * Complex.I))
      (Set.Icc (phi β s) c) := by
  intro x hx
  have hi : ((x : ℂ) + (s : ℂ) * Complex.I).im = s := by simp
  have hr : ((x : ℂ) + (s : ℂ) * Complex.I).re = x := by simp
  exact ContinuousAt.comp_continuousWithinAt
    (f := fun x : ℝ => (x : ℂ) + (s : ℂ) * Complex.I)
    (gExt_differentiableAt hβ hc hdiff hres (by rw [hi, hr]; exact hx.1)
      (by rw [hr]; exact hx.2)).continuousAt
    (by fun_prop)

lemma continuousOn_g_horiz {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {g : ℂ → ℂ}
    (hdiff : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ c → z ≠ 0 →
      DifferentiableAt ℂ g z) {s : ℝ} (hs : s ≠ 0) :
    ContinuousOn (fun x : ℝ => g ((x : ℂ) + (s : ℂ) * Complex.I))
      (Set.Icc (phi β s) c) := by
  intro x hx
  have hi : ((x : ℂ) + (s : ℂ) * Complex.I).im = s := by simp
  have hr : ((x : ℂ) + (s : ℂ) * Complex.I).re = x := by simp
  have hz0 : ((x : ℂ) + (s : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have : ((x : ℂ) + (s : ℂ) * Complex.I).im = 0 := by rw [h]; simp
    rw [hi] at this; exact hs this
  exact ContinuousAt.comp_continuousWithinAt
    (f := fun x : ℝ => (x : ℂ) + (s : ℂ) * Complex.I)
    (hdiff _ (by rw [hi, hr]; exact hx.1) (by rw [hr]; exact hx.2) hz0).continuousAt
    (by fun_prop)

lemma continuousOn_inv_horiz {β : ℝ} {s : ℝ} (hs : s ≠ 0) (c : ℝ) :
    ContinuousOn (fun x : ℝ => ((x : ℂ) + (s : ℂ) * Complex.I)⁻¹) (Set.Icc (phi β s) c) := by
  refine ContinuousOn.inv₀ (by fun_prop) (fun x hx => ?_)
  intro h
  have : ((x : ℂ) + (s : ℂ) * Complex.I).im = 0 := by rw [h]; simp
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero] at this
  exact hs (by simpa using this)

lemma Bfun_linear {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {g : ℂ → ℂ} {r : ℂ}
    (hdiff : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ c → z ≠ 0 →
      DifferentiableAt ℂ g z)
    (hres : Tendsto (fun z : ℂ => z * g z) (𝓝[≠] 0) (𝓝 r)) {T : ℝ} (hT : 0 < T) :
    Bfun β c g T = Bfun β c (gExt g r) T + r * Bfun β c (fun z => z⁻¹) T := by
  have hvert_cont : ContinuousOn (fun y : ℝ => (c : ℂ) + (y : ℂ) * Complex.I)
      (Set.uIcc (-T) T) :=
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousOn
  have hvert : ContinuousOn (fun y : ℝ => ((c : ℂ) + (y : ℂ) * Complex.I)⁻¹)
      (Set.uIcc (-T) T) :=
    hvert_cont.inv₀ (fun y hy => by
      intro h
      have hc' : ((c : ℂ) + (y : ℂ) * Complex.I).re = c := by simp
      rw [h] at hc'
      simp at hc'
      linarith)
  have hcurve_g : IntervalIntegrable (fun y : ℝ => g (gam β y) * gamDot β y) volume (-T) T :=
    intervalIntegrable_gamDot (β := β) (X := g) (T := T) hT.le
      (intervalIntegrable_X_gamDot_left (β := β) (X := g) (T := T) hT.le
        ((continuous_g_gam hβ hc hdiff).continuousOn.mul (continuousOn_gamDotNeg β T)))
      (intervalIntegrable_X_gamDot_right (β := β) (X := g) (T := T) hT.le
        ((continuous_g_gam hβ hc hdiff).continuousOn.mul (continuousOn_gamDot_nonneg β T)))
  have hcurve_e : IntervalIntegrable (fun y : ℝ => gExt g r (gam β y) * gamDot β y)
      volume (-T) T :=
    intervalIntegrable_gamDot (β := β) (X := gExt g r) (T := T) hT.le
      (intervalIntegrable_X_gamDot_left (β := β) (X := gExt g r) (T := T) hT.le
        ((continuous_gExt_gam hβ hc hdiff hres).continuousOn.mul (continuousOn_gamDotNeg β T)))
      (intervalIntegrable_X_gamDot_right (β := β) (X := gExt g r) (T := T) hT.le
        ((continuous_gExt_gam hβ hc hdiff hres).continuousOn.mul (continuousOn_gamDot_nonneg β T)))
  have hcurve_i : IntervalIntegrable (fun y : ℝ => (gam β y)⁻¹ * gamDot β y) volume (-T) T :=
    intervalIntegrable_gamDot (β := β) (X := fun z => z⁻¹) (T := T) hT.le
      (intervalIntegrable_X_gamDot_left (β := β) (X := fun z => z⁻¹) (T := T) hT.le
        ((continuous_inv_gam hβ).continuousOn.mul (continuousOn_gamDotNeg β T)))
      (intervalIntegrable_X_gamDot_right (β := β) (X := fun z => z⁻¹) (T := T) hT.le
        ((continuous_inv_gam hβ).continuousOn.mul (continuousOn_gamDot_nonneg β T)))
  rw [Bfun, Bfun, Bfun,
    integral_g_eq_one (β := β) (a := -T) (b := T) (path := fun y => (c : ℂ) + (y : ℂ) * Complex.I)
      (fun y => by
        intro h
        have hc' : ((c : ℂ) + (y : ℂ) * Complex.I).re = c := by simp
        rw [h] at hc'; simp at hc'; linarith)
      ((continuous_g_vert hβ hc hdiff).intervalIntegrable _ _)
      ((continuous_gExt_vert hβ hc hdiff hres).intervalIntegrable _ _)
      (hvert.intervalIntegrable),
    integral_g_eq_mul (β := β) (a := -T) (b := T) (path := gam β) (W := gamDot β) (fun y => gam_ne_zero hβ y)
      hcurve_g hcurve_e hcurve_i]
  have ht_int_g : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + (T : ℂ) * Complex.I))
      volume (phi β T) c := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (le_of_lt (phi_lt_c hβ hc T))]
    exact continuousOn_g_horiz hβ hc hdiff (ne_of_gt hT)
  have ht_int_e : IntervalIntegrable (fun x : ℝ => gExt g r ((x : ℂ) + (T : ℂ) * Complex.I))
      volume (phi β T) c := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (le_of_lt (phi_lt_c hβ hc T))]
    exact continuousOn_gExt_horiz hβ hc hdiff hres T
  have ht_int_i : IntervalIntegrable (fun x : ℝ => ((x : ℂ) + (T : ℂ) * Complex.I)⁻¹)
      volume (phi β T) c := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (le_of_lt (phi_lt_c hβ hc T))]
    exact continuousOn_inv_horiz (ne_of_gt hT) c
  have hb_int_g : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      volume (phi β (-T)) c := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (le_of_lt (phi_lt_c hβ hc (-T)))]
    exact continuousOn_g_horiz hβ hc hdiff (ne_of_lt (by linarith : -T < 0))
  have hb_int_e : IntervalIntegrable (fun x : ℝ => gExt g r ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      volume (phi β (-T)) c := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (le_of_lt (phi_lt_c hβ hc (-T)))]
    exact continuousOn_gExt_horiz hβ hc hdiff hres (-T)
  have hb_int_i : IntervalIntegrable (fun x : ℝ => ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)⁻¹)
      volume (phi β (-T)) c := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (le_of_lt (phi_lt_c hβ hc (-T)))]
    exact continuousOn_inv_horiz (ne_of_lt (by linarith : -T < 0)) c
  rw [integral_g_eq_one (β := β) (a := phi β T) (b := c) (path := fun x => (x : ℂ) + (T : ℂ) * Complex.I)
      (fun x => by
        intro h
        have hi : ((x : ℂ) + (T : ℂ) * Complex.I).im = T := by simp
        rw [h] at hi; simp at hi
        linarith)
      ht_int_g ht_int_e ht_int_i]
  have ht_int_g' : IntervalIntegrable (fun x : ℝ => g ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      volume (phi β (-T)) c := hb_int_g
  rw [integral_g_eq_one (β := β) (a := phi β (-T)) (b := c) (path := fun x => (x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
      (fun x => by
        intro h
        have hi : ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I).im = -T := by simp
        rw [h] at hi; simp at hi
        linarith)
      hb_int_g hb_int_e hb_int_i]
  ring


/-! ## The horizontal term and the limit -/

def horizTerm (β c : ℝ) (g : ℂ → ℂ) (T : ℝ) : ℂ :=
  (∫ x in (phi β T)..c, g ((x : ℂ) + (T : ℂ) * Complex.I))
    - (∫ x in (phi β T)..c, g ((x : ℂ) - (T : ℂ) * Complex.I))

lemma Bfun_eq_horiz {β c : ℝ} {g : ℂ → ℂ} {T : ℝ} (hT : 0 < T) :
    Bfun β c g T = Complex.I * (∫ y in (-T)..T, g ((c : ℂ) + (y : ℂ) * Complex.I))
      - (∫ y in (-T)..T, g (gam β y) * gamDot β y) - horizTerm β c g T := by
  rw [Bfun, horizTerm]
  have hfour : (∫ x in (phi β (-T))..c, g ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      = (∫ x in (phi β T)..c, g ((x : ℂ) - (T : ℂ) * Complex.I)) := by
    rw [phi_even β T]
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall (fun x _ => ?_))
    congr 1
    push_cast; ring
  rw [hfour]; ring

lemma key_identity {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) {g : ℂ → ℂ} {r : ℂ}
    (hdiff : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ c → z ≠ 0 →
      DifferentiableAt ℂ g z)
    (hres : Tendsto (fun z : ℂ => z * g z) (𝓝[≠] 0) (𝓝 r)) {T : ℝ} (hT : 0 < T) :
    Complex.I * (∫ y in (-T)..T, g ((c : ℂ) + (y : ℂ) * Complex.I))
      - (∫ y in (-T)..T, g (gam β y) * gamDot β y)
      = 2 * (Real.pi : ℂ) * Complex.I * r + horizTerm β c g T := by
  have hB : Bfun β c g T = Bfun β c (gExt g r) T + r * Bfun β c (fun z => z⁻¹) T :=
    Bfun_linear hβ hc hdiff hres hT
  have h0 : Bfun β c (gExt g r) T = 0 := Bfun_gExt_zero hβ hc hdiff hres hT
  have hi : Bfun β c (fun z => z⁻¹) T = 2 * (Real.pi : ℂ) * Complex.I := Bfun_inv hβ hc hT
  have hval : Bfun β c g T = 2 * (Real.pi : ℂ) * Complex.I * r := by
    rw [hB, h0, hi]; ring
  have hh := Bfun_eq_horiz (β := β) (c := c) (g := g) hT
  rw [hval] at hh
  rw [hh]; ring

lemma horizTerm_tendsto {β c : ℝ} (hβ : 0 < β) {g : ℂ → ℂ}
    (hhoriz : Tendsto (fun T : ℝ =>
      (∫ u in (-(β / Real.log (T + 2)))..c, g ((u : ℂ) + (T : ℂ) * Complex.I))
        - (∫ u in (-(β / Real.log (T + 2)))..c, g ((u : ℂ) - (T : ℂ) * Complex.I)))
      atTop (𝓝 0)) :
    Tendsto (horizTerm β c g) atTop (𝓝 0) := by
  refine hhoriz.congr' ?_
  filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
  rw [horizTerm, phi, abs_of_pos hT]


open MeasureTheory in
theorem contour_shift_residue {β c : ℝ} (hβ : 0 < β) (hc : 0 < c)
    (g : ℂ → ℂ) (r : ℂ)
    (hdiff : ∀ z : ℂ, -(β / Real.log (|z.im| + 2)) ≤ z.re → z.re ≤ c → z ≠ 0 →
      DifferentiableAt ℂ g z)
    (hres : Filter.Tendsto (fun z : ℂ => z * g z) (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds r))
    (hint1 : MeasureTheory.Integrable
      (fun t : ℝ => g ((c : ℂ) + (t : ℂ) * Complex.I) * Complex.I))
    (hint0 : MeasureTheory.Integrable (fun t : ℝ =>
      g (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t))
    (hhoriz : Filter.Tendsto (fun T : ℝ =>
      (∫ u in (-(β / Real.log (T + 2)))..c, g ((u : ℂ) + (T : ℂ) * Complex.I))
        - (∫ u in (-(β / Real.log (T + 2)))..c, g ((u : ℂ) - (T : ℂ) * Complex.I)))
      Filter.atTop (nhds 0)) :
    (∫ t : ℝ, g ((c : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
      = (∫ t : ℝ, g (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t)
        + 2 * Real.pi * Complex.I * r := by
  have hint_g : MeasureTheory.Integrable (fun t : ℝ => g ((c : ℂ) + (t : ℂ) * Complex.I)) :=
    (hint1.div_const Complex.I).congr (Filter.Eventually.of_forall (fun t => by
      change g ((c : ℂ) + (t : ℂ) * Complex.I) * Complex.I / Complex.I
        = g ((c : ℂ) + (t : ℂ) * Complex.I)
      rw [div_eq_mul_inv, mul_assoc, mul_inv_cancel₀ Complex.I_ne_zero, mul_one]))
  have hd_unf : ∀ t : ℝ, t ≠ 0 →
      deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t
        = gamDot β t := fun t ht => by
    have h := (hasDerivAt_gam (β := β) ht).deriv
    have hfun : (gam β) = (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ)
        + (s : ℂ) * Complex.I)) := by funext s; simp [gam, phi]
    rw [hfun] at h
    exact h
  have hint_c : MeasureTheory.Integrable (fun t : ℝ => g (gam β t) * gamDot β t) :=
    hint0.congr (by
      filter_upwards [ae_ne_zero] with t ht
      rw [hd_unf t ht]
      congr 1)
  have hkey : ∀ᶠ T in Filter.atTop,
      Complex.I * (∫ y in (-T)..T, g ((c : ℂ) + (y : ℂ) * Complex.I))
        - (∫ y in (-T)..T, g (gam β y) * gamDot β y)
      = 2 * (Real.pi : ℂ) * Complex.I * r + horizTerm β c g T := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    exact key_identity hβ hc hdiff hres hT
  have h1 : Tendsto (fun T : ℝ => ∫ y in (-T)..T, g ((c : ℂ) + (y : ℂ) * Complex.I))
      Filter.atTop (𝓝 (∫ y : ℝ, g ((c : ℂ) + (y : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral hint_g tendsto_neg_atTop_atBot tendsto_id
  have h2 : Tendsto (fun T : ℝ => ∫ y in (-T)..T, g (gam β y) * gamDot β y)
      Filter.atTop (𝓝 (∫ y : ℝ, g (gam β y) * gamDot β y)) :=
    intervalIntegral_tendsto_integral hint_c tendsto_neg_atTop_atBot tendsto_id
  have hlim : Tendsto (fun T : ℝ => Complex.I *
        (∫ y in (-T)..T, g ((c : ℂ) + (y : ℂ) * Complex.I))
        - (∫ y in (-T)..T, g (gam β y) * gamDot β y)) Filter.atTop
      (𝓝 (Complex.I * (∫ y : ℝ, g ((c : ℂ) + (y : ℂ) * Complex.I))
        - (∫ y : ℝ, g (gam β y) * gamDot β y))) :=
    (h1.const_mul Complex.I).sub h2
  have h3 : Tendsto (horizTerm β c g) Filter.atTop (𝓝 0) := horizTerm_tendsto hβ hhoriz
  have hlim2 : Tendsto (fun T : ℝ => 2 * (Real.pi : ℂ) * Complex.I * r + horizTerm β c g T)
      Filter.atTop (𝓝 (2 * (Real.pi : ℂ) * Complex.I * r + 0)) :=
    tendsto_const_nhds.add h3
  have huniq : Complex.I * (∫ y : ℝ, g ((c : ℂ) + (y : ℂ) * Complex.I))
      - (∫ y : ℝ, g (gam β y) * gamDot β y) = 2 * (Real.pi : ℂ) * Complex.I * r + 0 :=
    tendsto_nhds_unique (hlim.congr' hkey) hlim2
  rw [add_zero] at huniq
  have hlhs : (∫ t : ℝ, g ((c : ℂ) + (t : ℂ) * Complex.I) * Complex.I)
      = Complex.I * (∫ t : ℝ, g ((c : ℂ) + (t : ℂ) * Complex.I)) := by
    rw [MeasureTheory.integral_mul_const Complex.I (fun t : ℝ =>
      g ((c : ℂ) + (t : ℂ) * Complex.I)), mul_comm]
  have hrhs : (∫ t : ℝ, g (((-(β / Real.log (|t| + 2)) : ℝ) : ℂ) + (t : ℂ) * Complex.I)
        * deriv (fun s : ℝ => (((-(β / Real.log (|s| + 2)) : ℝ) : ℂ) + (s : ℂ) * Complex.I)) t)
      = ∫ t : ℝ, g (gam β t) * gamDot β t := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [ae_ne_zero] with t ht
    rw [hd_unf t ht]
    congr 1
  rw [hlhs, hrhs, ← huniq]
  ring


end

end Commons.Analysis.Complex