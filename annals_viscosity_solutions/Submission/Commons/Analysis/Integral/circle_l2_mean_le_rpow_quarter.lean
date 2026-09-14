import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

namespace Commons.Analysis.Integral

open MeasureTheory Set Real Filter
open scoped Topology

private lemma hasDerivAt_inv_sq_add_sq {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => a⁻¹ * Real.arctan (y/a)) ((x^2 + a^2)⁻¹) x := by
  have h1 : HasDerivAt (fun y : ℝ => y/a) (a⁻¹) x := by
    simpa using (hasDerivAt_id x).div_const a
  have h2 : HasDerivAt (fun y : ℝ => Real.arctan (y/a)) (1/(1+(x/a)^2) * a⁻¹) x :=
    h1.arctan
  have h3 : HasDerivAt (fun y : ℝ => a⁻¹ * Real.arctan (y/a)) (a⁻¹ * (1/(1+(x/a)^2) * a⁻¹)) x :=
    h2.const_mul a⁻¹
  have hden : (1:ℝ) + (x/a)^2 ≠ 0 := by positivity
  have heq : a⁻¹ * (1/(1+(x/a)^2) * a⁻¹) = (x^2 + a^2)⁻¹ := by
    field_simp
    ring
  rwa [heq] at h3

private lemma tendsto_aux {a : ℝ} (ha : 0 < a) :
    Tendsto (fun y : ℝ => a⁻¹ * Real.arctan (y/a)) atTop (𝓝 (Real.pi/(2*a))) := by
  have hbase : Tendsto Real.arctan atTop (𝓝 (Real.pi/2)) :=
    tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop
  have h : Tendsto (fun y : ℝ => y/a) atTop atTop := by
    have := tendsto_id.const_mul_atTop (show (0:ℝ) < a⁻¹ by positivity)
    simpa [div_eq_inv_mul] using this
  have h2 := hbase.comp h
  have h3 := h2.const_mul a⁻¹
  have he : a⁻¹ * (Real.pi/2) = Real.pi/(2*a) := by field_simp
  rwa [he] at h3

lemma integrableOn_Ioi_inv_sq_add_sq {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => (x^2 + a^2)⁻¹) (Ioi (0:ℝ)) := by
  have hderivIoi : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun y => a⁻¹ * Real.arctan (y/a))
      ((x^2 + a^2)⁻¹) x := fun x _ => hasDerivAt_inv_sq_add_sq (ne_of_gt ha) x
  have hcont : ContinuousWithinAt (fun y => a⁻¹ * Real.arctan (y/a)) (Ici (0:ℝ)) 0 :=
    (by fun_prop : Continuous (fun y => a⁻¹ * Real.arctan (y/a))).continuousAt.continuousWithinAt
  have hnonneg : ∀ x ∈ Ioi (0:ℝ), 0 ≤ (x^2 + a^2)⁻¹ := by intro x _; positivity
  exact integrableOn_Ioi_deriv_of_nonneg hcont hderivIoi hnonneg (tendsto_aux ha)

lemma integral_Ioi_inv_sq_add_sq {a : ℝ} (ha : 0 < a) :
    ∫ x in Ioi (0:ℝ), (x^2 + a^2)⁻¹ = Real.pi / (2*a) := by
  have hderivIci : ∀ x ∈ Ici (0:ℝ), HasDerivAt (fun y => a⁻¹ * Real.arctan (y/a))
      ((x^2 + a^2)⁻¹) x := fun x _ => hasDerivAt_inv_sq_add_sq (ne_of_gt ha) x
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a:=0) hderivIci
    (integrableOn_Ioi_inv_sq_add_sq ha) (tendsto_aux ha)
  simpa using h

lemma integral_inv_sqrt_prod_le (P Q : ℝ) (hP : 0 < P) (hQ : 0 < Q) :
    ∫ x in Ioi (0:ℝ), (Real.sqrt ((x^2+P)*(x^2+Q)))⁻¹
      ≤ Real.pi / (2 * (P*Q)^(1/4:ℝ)) := by
  set a : ℝ := Real.sqrt P with ha
  set b : ℝ := Real.sqrt Q with hb
  have hapos : 0 < a := by rw [ha]; exact Real.sqrt_pos.mpr hP
  have hbpos : 0 < b := by rw [hb]; exact Real.sqrt_pos.mpr hQ
  have han : a ≠ 0 := ne_of_gt hapos
  have hbn : b ≠ 0 := ne_of_gt hbpos
  have hP' : P = a^2 := by rw [ha, Real.sq_sqrt hP.le]
  have hQ' : Q = b^2 := by rw [hb, Real.sq_sqrt hQ.le]
  set lam : ℝ := Real.sqrt (b/a) with hlam
  have hlamp : 0 < lam := by rw [hlam]; exact Real.sqrt_pos.mpr (by positivity)
  have hlam2 : lam^2 = b/a := by rw [hlam, Real.sq_sqrt (by positivity)]
  -- pointwise AM-GM
  have hpt : ∀ x : ℝ, (Real.sqrt ((x^2+P)*(x^2+Q)))⁻¹
      ≤ (1/2)*((lam*(x^2+a^2))⁻¹ + lam/(x^2+b^2)) := by
    intro x
    rw [hP', hQ']
    have hU : (0:ℝ) ≤ (lam*(x^2+a^2))⁻¹ := by positivity
    have hV : (0:ℝ) ≤ lam/(x^2+b^2) := by positivity
    have hprod : (lam*(x^2+a^2))⁻¹ * (lam/(x^2+b^2)) = ((x^2+a^2)*(x^2+b^2))⁻¹ := by
      rw [div_eq_mul_inv, mul_inv]
      field_simp
    have hsqrt : Real.sqrt ((lam*(x^2+a^2))⁻¹ * (lam/(x^2+b^2)))
        = (Real.sqrt ((x^2+a^2)*(x^2+b^2)))⁻¹ := by
      rw [hprod, Real.sqrt_inv]
    have hsq : (lam*(x^2+a^2))⁻¹ * (lam/(x^2+b^2))
        ≤ (((lam*(x^2+a^2))⁻¹ + lam/(x^2+b^2))/2)^2 := by
      nlinarith [sq_nonneg ((lam*(x^2+a^2))⁻¹ - lam/(x^2+b^2))]
    have hAM : Real.sqrt ((lam*(x^2+a^2))⁻¹ * (lam/(x^2+b^2)))
        ≤ ((lam*(x^2+a^2))⁻¹ + lam/(x^2+b^2))/2 :=
      (Real.sqrt_le_left (by positivity)).mpr hsq
    calc (Real.sqrt ((x^2+a^2)*(x^2+b^2)))⁻¹
        = Real.sqrt ((lam*(x^2+a^2))⁻¹ * (lam/(x^2+b^2))) := hsqrt.symm
      _ ≤ ((lam*(x^2+a^2))⁻¹ + lam/(x^2+b^2))/2 := hAM
      _ = (1/2)*((lam*(x^2+a^2))⁻¹ + lam/(x^2+b^2)) := by ring
  -- integrability of g
  have hIntA : IntegrableOn (fun x : ℝ => (lam*(x^2+a^2))⁻¹) (Ioi (0:ℝ)) := by
    have he : (fun x : ℝ => (lam*(x^2+a^2))⁻¹) = fun x => lam⁻¹ * (x^2+a^2)⁻¹ := by
      ext x; rw [mul_inv]
    rw [he]
    exact (integrableOn_Ioi_inv_sq_add_sq hapos).const_mul lam⁻¹
  have hIntB : IntegrableOn (fun x : ℝ => lam/(x^2+b^2)) (Ioi (0:ℝ)) := by
    have he : (fun x : ℝ => lam/(x^2+b^2)) = fun x => lam * (x^2+b^2)⁻¹ := by
      ext x; rw [div_eq_mul_inv]
    rw [he]
    exact (integrableOn_Ioi_inv_sq_add_sq hbpos).const_mul lam
  have hIntg : IntegrableOn (fun x : ℝ => (1/2)*((lam*(x^2+a^2))⁻¹ + lam/(x^2+b^2))) (Ioi (0:ℝ)) :=
    (hIntA.add hIntB).const_mul (1/2)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] (fun x : ℝ => (Real.sqrt ((x^2+P)*(x^2+Q)))⁻¹) :=
    Eventually.of_forall fun x => by positivity
  have hle : (fun x : ℝ => (Real.sqrt ((x^2+P)*(x^2+Q)))⁻¹)
      ≤ᵐ[volume.restrict (Ioi (0:ℝ))] (fun x : ℝ => (1/2)*((lam*(x^2+a^2))⁻¹ + lam/(x^2+b^2))) :=
    Eventually.of_forall hpt
  have hmono := integral_mono_of_nonneg (μ := volume.restrict (Ioi (0:ℝ))) hnn hIntg hle
  refine hmono.trans_eq ?_
  rw [integral_const_mul]
  have eA : ∫ x in Ioi (0:ℝ), (lam*(x^2+a^2))⁻¹ = lam⁻¹ * (Real.pi/(2*a)) := by
    have he : (fun x : ℝ => (lam*(x^2+a^2))⁻¹) = fun x => lam⁻¹ * (x^2+a^2)⁻¹ := by
      ext x; rw [mul_inv]
    rw [he, integral_const_mul, integral_Ioi_inv_sq_add_sq hapos]
  have eB : ∫ x in Ioi (0:ℝ), lam/(x^2+b^2) = lam * (Real.pi/(2*b)) := by
    have he : (fun x : ℝ => lam/(x^2+b^2)) = fun x => lam * (x^2+b^2)⁻¹ := by
      ext x; rw [div_eq_mul_inv]
    rw [he, integral_const_mul, integral_Ioi_inv_sq_add_sq hbpos]
  rw [integral_add hIntA hIntB, eA, eB]
  -- final arithmetic
  have hab : Real.sqrt (a*b) = (P*Q)^(1/4:ℝ) := by
    have h1 : (P*Q)^(1/4:ℝ) = Real.sqrt (Real.sqrt (P*Q)) := by
      have h2 : (P*Q)^(1/4:ℝ) = (P*Q)^((1/2:ℝ)*(1/2)) := by
        rw [show (1/2:ℝ)*(1/2) = (1/4:ℝ) by norm_num]
      rw [h2, Real.rpow_mul (show (0:ℝ) ≤ P*Q by positivity),
        ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    rw [h1]; congr 1
    rw [Real.sqrt_mul hP.le, ← ha, ← hb]
  rw [← hab]
  have hla : lam⁻¹ * (1/a) = 1/Real.sqrt (a*b) := by
    rw [hlam, ← Real.sqrt_inv]
    have hba : (b/a)⁻¹ = a/b := by field_simp
    rw [hba, Real.sqrt_div hapos.le, Real.sqrt_mul hapos.le, div_eq_mul_inv]
    field_simp
    rw [Real.sq_sqrt hapos.le]
  have hlb : lam * (1/b) = 1/Real.sqrt (a*b) := by
    rw [hlam, Real.sqrt_div hbpos.le, Real.sqrt_mul hapos.le, div_eq_mul_inv]
    field_simp
    rw [Real.sq_sqrt hbpos.le]
  have key : lam⁻¹ * (Real.pi/(2*a)) + lam * (Real.pi/(2*b)) = Real.pi/Real.sqrt (a*b) := by
    rw [show lam⁻¹ * (Real.pi/(2*a)) = (Real.pi/2) * (lam⁻¹*(1/a)) by ring,
        show lam * (Real.pi/(2*b)) = (Real.pi/2) * (lam*(1/b)) by ring, hla, hlb]
    ring
  rw [key]
  ring


lemma integral_inv_sqrt_prod_landen {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in Ioi (0:ℝ), (Real.sqrt ((x^2+a^2)*(x^2+b^2)))⁻¹
      = ∫ x in Ioi (0:ℝ), (Real.sqrt ((x^2+a*b)*(x^2+((a+b)/2)^2)))⁻¹ := by
  have hab : 0 < a*b := mul_pos ha hb
  set f : ℝ → ℝ := fun t => t + Real.sqrt (t^2 + a*b) with hf
  set c : ℝ := (a+b)/2 with hc
  have hderiv : ∀ t, HasDerivAt f (f t / Real.sqrt (t^2+a*b)) t := by
    intro t
    have hd2 : HasDerivAt (fun s : ℝ => s^2 + a*b) (2*t) t := by
      simpa using (hasDerivAt_pow 2 t).add_const (a*b)
    have hs := hd2.sqrt (by positivity)
    have hd := (hasDerivAt_id t).add hs
    have hd' : HasDerivAt (fun s : ℝ => s + Real.sqrt (s^2+a*b)) (f t / Real.sqrt (t^2+a*b)) t := by
      have heq2 : 1 + (2*t)/(2*Real.sqrt (t^2+a*b)) = f t / Real.sqrt (t^2+a*b) := by
        have hA : 0 < Real.sqrt (t^2+a*b) := Real.sqrt_pos.mpr (by positivity)
        rw [hf]; field_simp; ring
      rw [← heq2]; exact hd
    simpa only [hf] using hd'
  have hfpos : ∀ t, 0 < f t := by
    intro t
    have hX : f t = t + Real.sqrt (t^2+a*b) := by rw [hf]
    rw [hX]
    have habs : |t| < Real.sqrt (t^2+a*b) := by
      rw [Real.lt_sqrt (abs_nonneg t), sq_abs]; nlinarith [hab]
    linarith [neg_abs_le t]
  have hsurj : f '' univ = Ioi (0:ℝ) := by
    ext y
    simp only [mem_image, mem_univ, true_and, mem_Ioi]
    constructor
    · rintro ⟨t, rfl⟩
      exact hfpos t
    · intro hy
      refine ⟨(y^2-a*b)/(2*y), ?_⟩
      have hX : f ((y^2-a*b)/(2*y)) = (y^2-a*b)/(2*y) + Real.sqrt (((y^2-a*b)/(2*y))^2+a*b) := by rw [hf]
      rw [hX]
      have hs : Real.sqrt (((y^2-a*b)/(2*y))^2+a*b) = (y^2+a*b)/(2*y) := by
        rw [show ((y^2-a*b)/(2*y))^2+a*b = ((y^2+a*b)/(2*y))^2 by field_simp; ring]
        rw [Real.sqrt_sq (by positivity)]
      rw [hs]
      field_simp
      ring
  have hinj : InjOn f univ := by
    have hmono : StrictMono f := strictMono_of_deriv_pos (fun x => by
      have hd := hderiv x
      rw [hd.deriv]
      exact div_pos (hfpos x) (Real.sqrt_pos.mpr (by positivity)))
    exact hmono.injective.injOn
  have hpt : ∀ t, |f t / Real.sqrt (t^2+a*b)| • (Real.sqrt (((f t)^2+a^2)*((f t)^2+b^2)))⁻¹
      = (1/2)*(Real.sqrt ((t^2+a*b)*(t^2+c^2)))⁻¹ := by
    intro t
    have hft : 0 < f t := hfpos t
    have hA : 0 < Real.sqrt (t^2+a*b) := Real.sqrt_pos.mpr (by positivity)
    have hC : 0 < Real.sqrt (t^2+c^2) := Real.sqrt_pos.mpr (by positivity)
    have hr : (Real.sqrt (t^2+a*b))^2 = t^2+a*b := Real.sq_sqrt (by positivity)
    have hX : f t = t + Real.sqrt (t^2+a*b) := by rw [hf]
    have hrel : (f t)^2 - a*b = 2*t*(f t) := by rw [hX]; nlinarith [hr]
    have hkey : ((f t)^2+a^2)*((f t)^2+b^2) = 4*(f t)^2*(t^2+c^2) := by
      rw [hc]; nlinarith [hrel]
    have hsq : Real.sqrt (((f t)^2+a^2)*((f t)^2+b^2)) = 2*(f t)*Real.sqrt (t^2+c^2) := by
      rw [hkey, Real.sqrt_mul (by positivity)]
      rw [show Real.sqrt (4*(f t)^2) = 2*(f t) by
        rw [show (4:ℝ)*(f t)^2 = (2*(f t))^2 by ring, Real.sqrt_sq (by positivity)]]
    have hsqrt : Real.sqrt ((t^2+a*b)*(t^2+c^2)) = Real.sqrt (t^2+a*b)*Real.sqrt (t^2+c^2) :=
      Real.sqrt_mul (by positivity) _
    rw [smul_eq_mul, abs_of_pos (div_pos hft hA), hsq, hsqrt]
    field_simp
  have hcv := integral_image_eq_integral_abs_deriv_smul (s := univ)
    (f := f) (f' := fun t => f t / Real.sqrt (t^2+a*b))
    MeasurableSet.univ (fun x _ => (hderiv x).hasDerivWithinAt) hinj
    (fun x => (Real.sqrt ((x^2+a^2)*(x^2+b^2)))⁻¹)
  rw [hsurj] at hcv
  rw [hcv]
  trans ∫ x in univ, (1/2)*(Real.sqrt ((x^2+a*b)*(x^2+c^2)))⁻¹
  · apply setIntegral_congr_fun MeasurableSet.univ
    intro x _
    exact hpt x
  · rw [setIntegral_univ]
    have hcabs := integral_comp_abs (f := fun x => (1/2)*(Real.sqrt ((x^2+a*b)*(x^2+c^2)))⁻¹)
    have heq : (∫ x, (1/2)*(Real.sqrt ((x^2+a*b)*(x^2+c^2)))⁻¹)
        = ∫ x, (fun y => (1/2)*(Real.sqrt ((y^2+a*b)*(y^2+c^2)))⁻¹) |x| := by
      apply integral_congr_ae; filter_upwards with x; rw [sq_abs]
    rw [heq, hcabs]
    rw [show (2:ℝ) * (∫ x in Ioi (0:ℝ), (1/2)*(Real.sqrt ((x^2+a*b)*(x^2+c^2)))⁻¹)
        = ∫ x in Ioi (0:ℝ), (Real.sqrt ((x^2+a*b)*(x^2+c^2)))⁻¹ by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi; intro x _; ring]


private lemma cos_two_arctan (t : ℝ) : Real.cos (2*Real.arctan t) = (1-t^2)/(1+t^2) := by
  rw [Real.cos_two_mul', Real.cos_arctan, Real.sin_arctan, div_pow, div_pow,
    Real.sq_sqrt (by positivity : (0:ℝ) ≤ 1+t^2)]
  field_simp

lemma circle_l2_mean_eq (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (∫ θ in (0)..Real.pi, (Real.sqrt (1+s^2-2*s*Real.cos θ))⁻¹)
      = 2 * ∫ x in Ioi (0:ℝ), (Real.sqrt ((x^2+(1+s)^2)*(x^2+(1-s)^2)))⁻¹ := by
  have hp : 0 < 1+s := by linarith
  have hpn : (1+s) ≠ 0 := ne_of_gt hp
  set g : ℝ → ℝ := fun x => 2*Real.arctan (x/(1+s)) with hg
  have hderiv : ∀ x, HasDerivAt g (2/(1+s)/(1+(x/(1+s))^2)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => y/(1+s)) ((1+s)⁻¹) x := by
      simpa using (hasDerivAt_id x).div_const (1+s)
    have h2 : HasDerivAt (fun y : ℝ => Real.arctan (y/(1+s))) (1/(1+(x/(1+s))^2) * (1+s)⁻¹) x :=
      h1.arctan
    have h3 : HasDerivAt (fun y : ℝ => 2*Real.arctan (y/(1+s)))
        (2*(1/(1+(x/(1+s))^2) * (1+s)⁻¹)) x := h2.const_mul 2
    have heq : 2*(1/(1+(x/(1+s))^2) * (1+s)⁻¹) = 2/(1+s)/(1+(x/(1+s))^2) := by
      field_simp
    rw [heq] at h3
    simpa only [hg] using h3
  have hgpos : ∀ x, 0 < 2/(1+s)/(1+(x/(1+s))^2) := by
    intro x
    exact div_pos (div_pos (by norm_num) hp) (by positivity)
  have hmono : StrictMono g := strictMono_of_deriv_pos (fun x => by
    rw [(hderiv x).deriv]; exact hgpos x)
  have hinj : InjOn g (Ioi (0:ℝ)) := hmono.injective.injOn
  have hgimg : g '' Ioi (0:ℝ) = Ioo (0:ℝ) Real.pi := by
    ext y
    simp only [mem_image, mem_Ioi, mem_Ioo]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have harg : 0 < x/(1+s) := by positivity
      exact ⟨by have := Real.arctan_pos.mpr harg; linarith,
             by have := Real.arctan_lt_pi_div_two (x/(1+s)); linarith⟩
    · rintro ⟨hy0, hyp⟩
      refine ⟨(1+s)*Real.tan (y/2), ?_, ?_⟩
      · have h1 : 0 < y/2 := by linarith
        have h2 : y/2 < Real.pi/2 := by linarith
        have := Real.tan_pos_of_pos_of_lt_pi_div_two h1 h2
        positivity
      · have h2 : y/2 < Real.pi/2 := by linarith
        have h1 : -(Real.pi/2) < y/2 := by linarith
        change 2*Real.arctan (((1+s)*Real.tan (y/2))/(1+s)) = y
        have hxx : (1+s)*Real.tan (y/2)/(1+s) = Real.tan (y/2) := by
          rw [mul_div_cancel_left₀ _ hpn]
        rw [hxx, Real.arctan_tan h1 h2]
        ring
  have hcv := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0:ℝ))
    (f := g) (f' := fun x => 2/(1+s)/(1+(x/(1+s))^2))
    measurableSet_Ioi (fun x _ => (hderiv x).hasDerivWithinAt) hinj
    (fun θ => (Real.sqrt (1+s^2-2*s*Real.cos θ))⁻¹)
  rw [hgimg] at hcv
  rw [intervalIntegral.integral_of_le (by positivity : (0:ℝ) ≤ Real.pi),
    integral_Ioc_eq_integral_Ioo]
  rw [hcv]
  trans ∫ x in Ioi (0:ℝ), 2/(Real.sqrt ((1+s)^2+x^2)*Real.sqrt ((1-s)^2+x^2))
  · apply setIntegral_congr_fun measurableSet_Ioi
    intro x _
    simp only [smul_eq_mul]
    rw [abs_of_pos (hgpos x)]
    have hA : 0 < (1+s)^2+x^2 := by positivity
    have hB : 0 < (1-s)^2+x^2 := by positivity
    have hval : 1+s^2-2*s*Real.cos (g x) = (1+s)^2*((1-s)^2+x^2)/((1+s)^2+x^2) := by
      rw [hg, cos_two_arctan]; field_simp; ring
    have hsqrt : Real.sqrt (1+s^2-2*s*Real.cos (g x))
        = (1+s)*Real.sqrt ((1-s)^2+x^2)/Real.sqrt ((1+s)^2+x^2) := by
      rw [hval, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity),
        Real.sqrt_sq (le_of_lt hp)]
    have hgp : 2/(1+s)/(1+(x/(1+s))^2) = 2*(1+s)/((1+s)^2+x^2) := by
      field_simp
    rw [hsqrt, hgp, inv_div]
    field_simp
    rw [Real.sq_sqrt (le_of_lt hA)]
  · rw [show (∫ x in Ioi (0:ℝ), 2/(Real.sqrt ((1+s)^2+x^2)*Real.sqrt ((1-s)^2+x^2)))
        = 2 * ∫ x in Ioi (0:ℝ), (Real.sqrt ((x^2+(1+s)^2)*(x^2+(1-s)^2)))⁻¹ by
      rw [← integral_const_mul]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x _
      change 2/(Real.sqrt ((1+s)^2+x^2)*Real.sqrt ((1-s)^2+x^2))
        = 2*(Real.sqrt ((x^2+(1+s)^2)*(x^2+(1-s)^2)))⁻¹
      rw [Real.sqrt_mul (by positivity)]
      ring]


theorem circle_l2_mean_le_rpow_quarter {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (1 / Real.pi) * ∫ θ in (0)..Real.pi,
        (Real.sqrt (1 + s ^ 2 - 2 * s * Real.cos θ))⁻¹
      ≤ (1 - s ^ 2) ^ (-(1 / 4 : ℝ)) := by
  have hA : 0 < 1+s := by linarith
  have hB : 0 < 1-s := by linarith
  have hP : 0 < 1 - s^2 := by nlinarith [hs0, hs1]
  have hI := circle_l2_mean_eq s hs0 hs1
  have hland : (∫ x in Ioi (0:ℝ), (Real.sqrt ((x^2+(1+s)^2)*(x^2+(1-s)^2)))⁻¹)
      = ∫ x in Ioi (0:ℝ), (Real.sqrt ((x^2+(1-s^2))*(x^2+1)))⁻¹ := by
    have h := integral_inv_sqrt_prod_landen (a:=1+s) (b:=1-s) hA hB
    simpa only [show (1+s)*(1-s) = 1-s^2 by ring, show ((1+s)+(1-s))/2 = 1 by ring, one_pow]
      using h
  have hcs := integral_inv_sqrt_prod_le (1-s^2) 1 hP (by norm_num)
  have hC : (∫ x in Ioi (0:ℝ), (Real.sqrt ((x^2+(1-s^2))*(x^2+1)))⁻¹)
      ≤ Real.pi/(2*(1-s^2)^(1/4:ℝ)) := by
    simpa only [mul_one] using hcs
  have hrw : (1-s^2)^(-(1/4:ℝ)) = ((1-s^2)^(1/4:ℝ))⁻¹ := Real.rpow_neg (le_of_lt hP) _
  rw [hI, hland, hrw]
  calc (1/Real.pi) * (2 * (∫ x in Ioi (0:ℝ), (Real.sqrt ((x^2+(1-s^2))*(x^2+1)))⁻¹))
      ≤ (1/Real.pi) * (2 * (Real.pi/(2*(1-s^2)^(1/4:ℝ)))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hC (by norm_num)
    _ = ((1-s^2)^(1/4:ℝ))⁻¹ := by
        have hp4 : (1-s^2)^(1/4:ℝ) ≠ 0 := by positivity
        field_simp

end Commons.Analysis.Integral