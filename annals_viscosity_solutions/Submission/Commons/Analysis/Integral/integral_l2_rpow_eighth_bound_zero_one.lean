import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

open MeasureTheory intervalIntegral Real Set Filter
open scoped Topology

namespace Commons.Analysis.Integral

noncomputable def sv (x : ℝ) : ℝ := Real.sqrt (1 - x^2)
noncomputable def uv (x : ℝ) : ℝ := Real.sqrt (2/(1 + sv x)) * Real.sqrt x
noncomputable def phiv (v : ℝ) : ℝ := 2 * v^2 / (1 + v^4)
noncomputable def dphiv (v : ℝ) : ℝ := 4*v*(1-v^4)/(1+v^4)^2
noncomputable def Ffun (x : ℝ) : ℝ := (1 - x^2)^(-(1/8:ℝ)) * uv x
noncomputable def h1fun (v : ℝ) : ℝ := v^2*(1-v^4)/(1+v^4)^2
noncomputable def h2fun (v : ℝ) : ℝ := v^2/(1+v^4)
noncomputable def RHSfun (v : ℝ) : ℝ :=
  (11/20:ℝ)^(-(1/4:ℝ)) * (3*Real.sqrt 2 * h1fun v + Real.sqrt 2 * (11/20) * h2fun v)
noncomputable def niceG (v : ℝ) : ℝ :=
  4*Real.sqrt 2 * v^2 * (1-v^4)^(3/4:ℝ) * (1+v^4)^(-(7/4):ℝ)
noncomputable def glb (v : ℝ) : ℝ := v^2 - v^6 + v^10 - v^14 + (1/2)*v^18

/-! ### Elementary facts -/

lemma one_sub_pow4_nonneg {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : 0 ≤ 1 - x^4 := by
  have h2 : x^2 ≤ 1 := by nlinarith [hx.1, hx.2]
  have hb : 0 ≤ x^2 * (1 - x^2) := mul_nonneg (sq_nonneg x) (by linarith)
  nlinarith [hb, h2]

lemma one_sub_pow4_pos {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) : 0 < 1 - x^4 := by
  have h2 : x^2 < 1 := by nlinarith [hx.1, hx.2, sq_nonneg x]
  have hb : 0 ≤ x^2 * (1 - x^2) := mul_nonneg (sq_nonneg x) (by linarith)
  nlinarith [hb, h2]

lemma sv_sq {x : ℝ} (hx : x ∈ Icc (0:ℝ) 1) : (sv x)^2 = 1 - x^2 := by
  rw [sv]
  exact Real.sq_sqrt (by nlinarith [hx.1, hx.2, sq_nonneg x])

lemma uv_nonneg (x : ℝ) : 0 ≤ uv x := by rw [uv]; positivity

lemma sv_nonneg (x : ℝ) : 0 ≤ sv x := Real.sqrt_nonneg _

lemma sv_pos {x : ℝ} (hx : x ∈ Ioo (0:ℝ) 1) : 0 < sv x := by
  rw [sv]; apply Real.sqrt_pos.mpr; nlinarith [hx.1, hx.2]

lemma phiv_mem_Ioo {v : ℝ} (hv : v ∈ Ioo (0:ℝ) 1) : phiv v ∈ Ioo (0:ℝ) 1 := by
  constructor
  · rw [phiv]
    apply div_pos
    · nlinarith [sq_pos_of_ne_zero (ne_of_gt hv.1)]
    · positivity
  · rw [phiv, div_lt_one (by positivity : (0:ℝ) < 1+v^4)]
    nlinarith [sq_pos_of_ne_zero (by nlinarith [hv.1, hv.2, sq_nonneg v] : v^2 - 1 ≠ 0)]

lemma phiv_zero : phiv 0 = 0 := by rw [phiv]; norm_num

lemma phiv_one : phiv 1 = 1 := by rw [phiv]; norm_num

lemma sv_phiv {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) :
    sv (phiv v) = (1 - v^4)/(1+v^4) := by
  have hsq : 1 - (phiv v)^2 = ((1-v^4)/(1+v^4))^2 := by
    rw [phiv]; field_simp; ring
  rw [sv, hsq, Real.sqrt_sq]
  exact div_nonneg (one_sub_pow4_nonneg hv) (by positivity)

lemma uv_phiv {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) : uv (phiv v) = Real.sqrt 2 * v := by
  have hden : (0:ℝ) < 1 + v^4 := by positivity
  have hv0 : 0 ≤ v := hv.1
  have hsp := sv_phiv hv
  have hcomb : 1 + sv (phiv v) = 2/(1+v^4) := by
    rw [hsp]; field_simp; ring
  have harg : 2/(1 + sv (phiv v)) = 1 + v^4 := by
    rw [hcomb]; field_simp
  have hphivnn : 0 ≤ phiv v := by rw [phiv]; positivity
  have hsqv : Real.sqrt (phiv v) = Real.sqrt 2 * v / Real.sqrt (1 + v^4) := by
    rw [phiv, Real.sqrt_div (by positivity : (0:ℝ) ≤ 2 * v^2) (1 + v^4)]
    rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_sq hv0]
  rw [uv, harg, hsqv]
  field_simp

lemma hasDerivAt_phiv (v : ℝ) : HasDerivAt phiv (dphiv v) v := by
  have h1 : HasDerivAt (fun v:ℝ => 2*v^2) (4*v) v := by
    have h := (hasDerivAt_pow 2 v).const_mul (2:ℝ)
    rw [show (2:ℕ) - 1 = 1 by norm_num, pow_one] at h
    ring_nf at h
    simpa [mul_comm] using h
  have h2 : HasDerivAt (fun v:ℝ => 1+v^4) (4*v^3) v := by
    have h := (hasDerivAt_pow 4 v).const_add (1:ℝ)
    rw [show (4:ℕ) - 1 = 3 by norm_num] at h
    simpa [add_comm] using h
  have h := h1.div h2 (by positivity : (1:ℝ)+v^4 ≠ 0)
  have hderiv : (4*v*(1+v^4) - 2*v^2*(4*v^3))/(1+v^4)^2 = dphiv v := by
    rw [dphiv]; field_simp; ring
  rw [hderiv] at h
  exact h

lemma continuous_phiv : Continuous phiv := by
  have h := ((continuous_const : Continuous (fun _ : ℝ => (2:ℝ))).mul (continuous_id.pow 2)).div
    ((continuous_const : Continuous (fun _ : ℝ => (1:ℝ))).add (continuous_id.pow 4))
    (by intro v; show (1:ℝ) + v^4 ≠ 0; positivity)
  exact h

lemma dphiv_nonneg {v : ℝ} (hv : v ∈ Ioo (0:ℝ) 1) : 0 ≤ dphiv v := by
  rw [dphiv]
  apply div_nonneg
  · nlinarith [le_of_lt hv.1, one_sub_pow4_pos hv]
  · positivity

/-! ### The AM-GM tangent bound and rpow algebra -/

lemma amgm_s (s c : ℝ) (hs : 0 ≤ s) (hc : 0 < c) :
    s^(3/4:ℝ) ≤ c^(-(1/4):ℝ) * ((3/4)*s + (1/4)*c) := by
  have h := Real.geom_mean_le_arith_mean2_weighted (w₁ := (3/4:ℝ)) (w₂ := (1/4:ℝ))
      (p₁ := s) (p₂ := c) (by norm_num) (by norm_num) hs (le_of_lt hc) (by norm_num)
  have hc4 : 0 < c^(1/4:ℝ) := Real.rpow_pos_of_pos hc _
  have h2 : s^(3/4:ℝ) * c^(1/4:ℝ) / c^(1/4:ℝ) ≤ ((3/4)*s+(1/4)*c)/c^(1/4:ℝ) :=
    div_le_div_of_nonneg_right h (le_of_lt hc4)
  rw [mul_div_cancel_right₀ _ (ne_of_gt hc4)] at h2
  refine h2.trans (le_of_eq ?_)
  rw [div_eq_mul_inv, Real.rpow_neg (le_of_lt hc) (1/4:ℝ)]
  ring

lemma rpow_decomp {s : ℝ} (hs : 0 < s) :
    s^(-(1/4):ℝ) = s^(3/4:ℝ) / s := by
  rw [show (-(1/4):ℝ) = 3/4 - 1 by norm_num, Real.rpow_sub hs, Real.rpow_one]

lemma rpow_one_sub_sq (x : ℝ) (hx : x ∈ Ioo (0:ℝ) 1) :
    (1-x^2)^(-(1/8:ℝ)) = (sv x)^(-(1/4:ℝ)) := by
  have hs2 : (sv x)^2 = 1 - x^2 := sv_sq ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hs : 0 ≤ sv x := le_of_lt (sv_pos hx)
  have key : (sv x)^(-(1/4):ℝ) = ((sv x)^2)^(-(1/8):ℝ) := by
    rw [show (-(1/4):ℝ) = 2 * (-(1/8)) by norm_num, Real.rpow_mul hs, Real.rpow_two]
  rw [← hs2]
  exact key.symm

lemma rpow_key {A B : ℝ} (ha : 0 < A) (hb : 0 < B) :
    (A/B)^(-(1/4):ℝ) * A / B^2 = A^(3/4:ℝ) * B^(-(7/4):ℝ) := by
  have h1 : (A/B)^(-(1/4):ℝ) = A^(-(1/4):ℝ) * B^(1/4:ℝ) := by
    rw [Real.div_rpow (le_of_lt ha) (le_of_lt hb) (-(1/4)), Real.rpow_neg (le_of_lt hb) (1/4)]
    field_simp
  rw [h1]
  have h2 : A^(-(1/4):ℝ) * A = A^(3/4:ℝ) := by
    rw [show (-(1/4):ℝ) = 3/4 - 1 by norm_num, Real.rpow_sub ha, Real.rpow_one]
    field_simp
  have h3 : B^(1/4:ℝ) / B^2 = B^(-(7/4):ℝ) := by
    rw [← Real.rpow_natCast B 2, ← Real.rpow_sub hb]
    norm_num
  rw [show A^(-(1/4):ℝ) * B^(1/4:ℝ) * A / B^2 = (A^(-(1/4):ℝ) * A) * (B^(1/4:ℝ)/B^2) by ring]
  rw [h2, h3]

/-! ### The pointwise bound in the substituted variable -/

lemma niceG_eq {v : ℝ} (hv : v ∈ Ioo (0:ℝ) 1) :
    Ffun (phiv v) * dphiv v = niceG v := by
  have hvIcc : v ∈ Icc (0:ℝ) 1 := ⟨le_of_lt hv.1, le_of_lt hv.2⟩
  have hpv : phiv v ∈ Ioo (0:ℝ) 1 := phiv_mem_Ioo hv
  have hsp : sv (phiv v) = (1 - v^4)/(1+v^4) := sv_phiv hvIcc
  have hu : uv (phiv v) = Real.sqrt 2 * v := uv_phiv hvIcc
  have hdec := rpow_one_sub_sq (phiv v) hpv
  have ha : (0:ℝ) < 1-v^4 := one_sub_pow4_pos hv
  have hb : (0:ℝ) < 1+v^4 := by positivity
  have hkey := rpow_key (A:=1-v^4) (B:=1+v^4) ha hb
  unfold Ffun niceG
  rw [hdec, hu, hsp, dphiv]
  rw [show ((1 - v^4)/(1+v^4))^(-(1/4):ℝ) * (Real.sqrt 2 * v) * (4*v*(1-v^4)/(1+v^4)^2)
      = 4*Real.sqrt 2 * v^2 * (((1-v^4)/(1+v^4))^(-(1/4):ℝ) * (1-v^4)/(1+v^4)^2) by ring]
  rw [hkey]
  ring

lemma pointwise_v (v : ℝ) (hv : v ∈ Ioo (0:ℝ) 1) :
    Ffun (phiv v) * dphiv v ≤ RHSfun v := by
  have hvIcc : v ∈ Icc (0:ℝ) 1 := ⟨le_of_lt hv.1, le_of_lt hv.2⟩
  have hpv : phiv v ∈ Ioo (0:ℝ) 1 := phiv_mem_Ioo hv
  have hsp : sv (phiv v) = (1 - v^4)/(1+v^4) := sv_phiv hvIcc
  have hs : 0 < sv (phiv v) := by
    rw [hsp]; exact div_pos (one_sub_pow4_pos hv) (by positivity)
  have hdec := rpow_one_sub_sq (phiv v) hpv
  have hu := uv_phiv hvIcc
  have hWnn : 0 ≤ Real.sqrt 2 * v * dphiv v / sv (phiv v) :=
    div_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (le_of_lt hv.1))
      (dphiv_nonneg hv)) (le_of_lt hs)
  have hgoal : Ffun (phiv v) * dphiv v
      = (sv (phiv v))^(3/4:ℝ) * (Real.sqrt 2 * v * dphiv v / sv (phiv v)) := by
    unfold Ffun
    rw [hdec, hu, rpow_decomp hs]
    field_simp
  rw [hgoal]
  refine (mul_le_mul_of_nonneg_right
    (amgm_s (sv (phiv v)) (11/20) (le_of_lt hs) (by norm_num)) hWnn).trans (le_of_eq ?_)
  have hv4 : (1:ℝ) - v^4 ≠ 0 := ne_of_gt (one_sub_pow4_pos hv)
  unfold RHSfun h1fun h2fun
  rw [hsp, dphiv]
  field_simp



/-! ### Substitution and comparison -/

lemma continuous_h1 : Continuous h1fun := by
  unfold h1fun
  exact (by fun_prop : Continuous (fun v:ℝ => v^2*(1-v^4))).div
    (by fun_prop : Continuous (fun v:ℝ => (1+v^4)^2))
    (by intro v; exact pow_ne_zero 2 (by positivity))

lemma continuous_h2 : Continuous h2fun := by
  unfold h2fun
  exact (by fun_prop : Continuous (fun v:ℝ => v^2)).div
    (by fun_prop : Continuous (fun v:ℝ => 1+v^4)) (by intro v; positivity)

lemma continuousOn_niceG : ContinuousOn niceG (uIcc (0:ℝ) 1) := by
  unfold niceG
  have h1 : ContinuousOn (fun v : ℝ => 4*Real.sqrt 2 * v^2) (uIcc (0:ℝ) 1) :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ => 4*Real.sqrt 2) (uIcc (0:ℝ) 1)).mul
      (continuousOn_id.pow 2)
  have h2 : ContinuousOn (fun v : ℝ => (1-v^4)^(3/4:ℝ)) (uIcc (0:ℝ) 1) :=
    (continuousOn_const.sub (continuousOn_id.pow 4)).rpow_const
      (by intro v hv; right; norm_num)
  have h3 : ContinuousOn (fun v : ℝ => (1+v^4)^(-(7/4):ℝ)) (uIcc (0:ℝ) 1) :=
    (continuousOn_const.add (continuousOn_id.pow 4)).rpow_const
      (by intro v hv; left; show (1:ℝ)+v^4 ≠ 0; positivity)
  exact (h1.mul h2).mul h3

lemma continuous_RHSfun : Continuous RHSfun := by
  unfold RHSfun
  have h1 : Continuous (fun v : ℝ => 3*Real.sqrt 2 * h1fun v) :=
    (continuous_const : Continuous (fun _ : ℝ => 3*Real.sqrt 2)).mul continuous_h1
  have h2 : Continuous (fun v : ℝ => Real.sqrt 2 * (11/20) * h2fun v) :=
    (continuous_const : Continuous (fun _ : ℝ => Real.sqrt 2 * (11/20))).mul continuous_h2
  exact (continuous_const : Continuous (fun _ : ℝ => (11/20:ℝ)^(-(1/4:ℝ)))).mul (h1.add h2)

lemma substF : (∫ x in (0:ℝ)..1, Ffun x) = ∫ v in (0:ℝ)..1, Ffun (phiv v) * dphiv v := by
  have h := integral_comp_mul_deriv_of_deriv_nonneg (a:=0) (b:=1)
    (f:=phiv) (f':=dphiv) (g:=Ffun) continuous_phiv.continuousOn
    (fun x hx => hasDerivAt_phiv x) (fun x hx => dphiv_nonneg (by simpa using hx))
  rw [phiv_zero, phiv_one] at h
  exact h.symm

lemma integral_G_eq_niceG :
    (∫ v in (0:ℝ)..1, Ffun (phiv v) * dphiv v) = ∫ v in (0:ℝ)..1, niceG v :=
  intervalIntegral.integral_congr_Ioo_of_le (by norm_num) (fun v hv => niceG_eq hv)

lemma intRHS : IntervalIntegrable RHSfun volume (0:ℝ) 1 :=
  continuous_RHSfun.intervalIntegrable _ _

lemma intNiceG : IntervalIntegrable niceG volume (0:ℝ) 1 :=
  continuousOn_niceG.intervalIntegrable

lemma compare : (∫ v in (0:ℝ)..1, niceG v) ≤ ∫ v in (0:ℝ)..1, RHSfun v :=
  intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) intNiceG intRHS
    (fun v hv => by rw [← niceG_eq hv]; exact pointwise_v v hv)

lemma evalRHS :
    (∫ v in (0:ℝ)..1, RHSfun v)
      = (11/20:ℝ)^(-(1/4:ℝ)) * (3*Real.sqrt 2 * (∫ v in (0:ℝ)..1, h1fun v)
          + Real.sqrt 2 * (11/20) * (∫ v in (0:ℝ)..1, h2fun v)) := by
  unfold RHSfun
  rw [intervalIntegral.integral_const_mul]
  have i1 : IntervalIntegrable (fun v : ℝ => 3*Real.sqrt 2 * h1fun v) volume (0:ℝ) 1 :=
    (continuous_h1.intervalIntegrable _ _).const_mul _
  have i2 : IntervalIntegrable (fun v : ℝ => Real.sqrt 2 * (11/20) * h2fun v) volume (0:ℝ) 1 :=
    (continuous_h2.intervalIntegrable _ _).const_mul _
  rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]

/-! ### Fundamental theorem computation -/

lemma hasDerivAt_Gmain (v : ℝ) :
    HasDerivAt (fun x : ℝ => x^3/(1+x^4)) (h2fun v + 2*h1fun v) v := by
  have h1 : HasDerivAt (fun x : ℝ => x^3) (3*v^2) v := by
    have h := hasDerivAt_pow 3 v
    rw [show (3:ℕ)-1=2 by norm_num] at h
    simpa using h
  have h2 : HasDerivAt (fun x : ℝ => 1+x^4) (4*v^3) v := by
    have h := (hasDerivAt_pow 4 v).const_add (1:ℝ)
    rw [show (4:ℕ)-1=3 by norm_num] at h
    simpa [add_comm] using h
  have h := h1.div h2 (by positivity : (1:ℝ)+v^4 ≠ 0)
  have hd : (3*v^2*(1+v^4) - v^3*(4*v^3))/(1+v^4)^2 = h2fun v + 2*h1fun v := by
    unfold h2fun h1fun; field_simp; ring
  rw [hd] at h
  exact h

lemma ftc_main : (∫ v in (0:ℝ)..1, h2fun v) + 2*(∫ v in (0:ℝ)..1, h1fun v) = 1/2 := by
  have hint : IntervalIntegrable (fun v => h2fun v + 2*h1fun v) volume (0:ℝ) 1 :=
    (continuous_h2.intervalIntegrable _ _).add ((continuous_h1.intervalIntegrable _ _).const_mul 2)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=1)
    (f := fun x : ℝ => x^3/(1+x^4)) (f' := fun v => h2fun v + 2*h1fun v)
    (fun v hv => hasDerivAt_Gmain v) hint
  rw [intervalIntegral.integral_add (continuous_h2.intervalIntegrable _ _)
    ((continuous_h1.intervalIntegrable _ _).const_mul 2), intervalIntegral.integral_const_mul] at h
  norm_num at h
  exact h

/-! ### Lower bound for `∫ v²/(1+v⁴)` -/

lemma glb_le_h2 {v : ℝ} (hv : v ∈ Icc (0:ℝ) 1) : glb v ≤ h2fun v := by
  have hv4 : v^4 ≤ 1 := by
    have h2 : v^2 ≤ 1 := by nlinarith [hv.1, hv.2]
    have hb : 0 ≤ v^2*(1-v^2) := mul_nonneg (sq_nonneg v) (by linarith)
    nlinarith [hb, h2]
  have hden : 0 < 1 + v^4 := by positivity
  have hfac : glb v * (1+v^4) = v^2 + (1/2)*v^18*(v^4-1) := by
    unfold glb; ring
  rw [h2fun, le_div_iff₀ hden, hfac]
  have h18 : (0:ℝ) ≤ v^18 := pow_nonneg hv.1 18
  nlinarith [h18, hv4]

lemma hasDerivAt_mon (n : ℕ) (c : ℝ) (v : ℝ) :
    HasDerivAt (fun x : ℝ => x^n / c) ((n:ℝ) * v^(n-1) / c) v :=
  (hasDerivAt_pow n v).div_const c

lemma int_glb : (∫ v in (0:ℝ)..1, glb v) = 10579/43890 := by
  have hderiv : ∀ v ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun x : ℝ => x^3/3 - x^7/7 + x^11/11 - x^15/15 + x^19/38)
        (glb v) v := by
    intro v hv
    have h3 := hasDerivAt_mon 3 3 v
    have h7 := hasDerivAt_mon 7 7 v
    have h11 := hasDerivAt_mon 11 11 v
    have h15 := hasDerivAt_mon 15 15 v
    have h19 := hasDerivAt_mon 19 38 v
    simp only [show (3:ℕ)-1=2 by norm_num, show (7:ℕ)-1=6 by norm_num,
      show (11:ℕ)-1=10 by norm_num, show (15:ℕ)-1=14 by norm_num,
      show (19:ℕ)-1=18 by norm_num] at h3 h7 h11 h15 h19
    have key : HasDerivAt (fun x : ℝ => x^3/3 - x^7/7 + x^11/11 - x^15/15 + x^19/38)
        ((3:ℝ) * v^2 / 3 - (7:ℝ) * v^6 / 7 + (11:ℝ) * v^10 / 11 - (15:ℝ) * v^14 / 15
          + (19:ℝ) * v^18 / 38) v :=
      (((h3.sub h7).add h11).sub h15).add h19
    have hdeq : ((3:ℝ) * v^2 / 3 - (7:ℝ) * v^6 / 7 + (11:ℝ) * v^10 / 11
          - (15:ℝ) * v^14 / 15 + (19:ℝ) * v^18 / 38) = glb v := by
      unfold glb; ring
    rw [hdeq] at key
    exact key
  have hint : IntervalIntegrable glb volume (0:ℝ) 1 := by
    apply Continuous.intervalIntegrable
    unfold glb; fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a:=0) (b:=1)
    (f := fun x : ℝ => x^3/3 - x^7/7 + x^11/11 - x^15/15 + x^19/38) (f' := glb)
    hderiv hint
  norm_num at h
  exact h

lemma K0_lower : (10579/43890:ℝ) ≤ ∫ v in (0:ℝ)..1, h2fun v := by
  have hint : IntervalIntegrable glb volume (0:ℝ) 1 := by
    apply Continuous.intervalIntegrable
    unfold glb; fun_prop
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1)
      hint (continuous_h2.intervalIntegrable _ _) (fun v hv => glb_le_h2 hv)
  rwa [int_glb] at hmono

/-! ### Final numeric assembly -/

lemma sqrt_two_bound : Real.sqrt 2 ≤ 14143/10000 := by
  exact le_of_lt ((Real.sqrt_lt' (by norm_num : (0:ℝ) < 14143/10000)).mpr (by norm_num))

lemma c_pow_bound : (11/20:ℝ)^(-(1/4:ℝ)) ≤ 1000/861 := by
  have hL : (861/1000:ℝ) ≤ (11/20:ℝ)^(1/4:ℝ) := by
    have h4 : (861/1000:ℝ)^4 ≤ 11/20 := by norm_num
    have h := Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ (861/1000)^4) h4
      (by norm_num : (0:ℝ) ≤ 1/4)
    rwa [show ((861/1000:ℝ)^4)^(1/4:ℝ) = 861/1000 by
      rw [← Real.rpow_natCast (861/1000) 4, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 861/1000)]
      norm_num] at h
  have hpos : (0:ℝ) < (11/20:ℝ)^(1/4:ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have h := (inv_le_inv₀ hpos (show (0:ℝ) < 861/1000 by norm_num)).mpr hL
  rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 11/20) (1/4)]
  simpa using h

theorem integral_l2_rpow_eighth_bound_zero_one :
    ∫ x in Set.Ioc (0:ℝ) 1,
        (1 - x ^ 2) ^ (-(1 / 8 : ℝ)) * Real.sqrt (2 / (1 + Real.sqrt (1 - x ^ 2))) * Real.sqrt x
      ≤ 0.87 := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hI : (∫ x in (0:ℝ)..1,
        ((1 - x ^ 2) ^ (-(1/8:ℝ)) * Real.sqrt (2 / (1 + Real.sqrt (1 - x ^ 2)))
          * Real.sqrt x)) = ∫ x in (0:ℝ)..1, Ffun x := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [Ffun, uv, sv]
    ring
  rw [hI]
  have hb : (10579/43890:ℝ) ≤ ∫ v in (0:ℝ)..1, h2fun v := K0_lower
  have ha : (∫ v in (0:ℝ)..1, h1fun v) = 1/4 - (∫ v in (0:ℝ)..1, h2fun v)/2 := by
    linarith [ftc_main]
  have hkey : 3*Real.sqrt 2 * (∫ v in (0:ℝ)..1, h1fun v)
      + Real.sqrt 2 * (11/20) * (∫ v in (0:ℝ)..1, h2fun v)
      ≤ Real.sqrt 2 * (3/4 - (19/20)*(10579/43890:ℝ)) := by
    rw [ha]
    have hs2 := Real.sqrt_nonneg (2:ℝ)
    nlinarith [hb, hs2]
  have hstep : (∫ v in (0:ℝ)..1, RHSfun v)
      ≤ (11/20:ℝ)^(-(1/4:ℝ)) * (Real.sqrt 2 * (3/4 - (19/20)*(10579/43890:ℝ))) := by
    rw [evalRHS]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 11/20) _)
    calc 3*Real.sqrt 2 * (∫ v in (0:ℝ)..1, h1fun v)
            + Real.sqrt 2 * (11/20) * (∫ v in (0:ℝ)..1, h2fun v)
        ≤ Real.sqrt 2 * (3/4 - (19/20)*(10579/43890:ℝ)) := hkey
      _ = Real.sqrt 2 * (3/4 - (19/20)*(10579/43890:ℝ)) := rfl
  calc ∫ x in (0:ℝ)..1, Ffun x
      = ∫ v in (0:ℝ)..1, Ffun (phiv v) * dphiv v := substF
    _ = ∫ v in (0:ℝ)..1, niceG v := integral_G_eq_niceG
    _ ≤ ∫ v in (0:ℝ)..1, RHSfun v := compare
    _ ≤ (11/20:ℝ)^(-(1/4:ℝ)) * (Real.sqrt 2 * (3/4 - (19/20)*(10579/43890:ℝ))) := hstep
    _ ≤ 0.87 := by
        have hA := c_pow_bound
        have hB := sqrt_two_bound
        have hbr : (0:ℝ) ≤ 3/4 - (19/20)*(10579/43890:ℝ) := by norm_num
        calc (11/20:ℝ)^(-(1/4:ℝ)) * (Real.sqrt 2 * (3/4 - (19/20)*(10579/43890:ℝ)))
            = (11/20:ℝ)^(-(1/4:ℝ)) * Real.sqrt 2 * (3/4 - (19/20)*(10579/43890:ℝ)) := by ring
          _ ≤ (1000/861) * (14143/10000) * (3/4 - (19/20)*(10579/43890:ℝ)) := by
              apply mul_le_mul_of_nonneg_right _ hbr
              exact mul_le_mul hA hB (Real.sqrt_nonneg 2) (by norm_num)
          _ ≤ 0.87 := by norm_num

end Commons.Analysis.Integral