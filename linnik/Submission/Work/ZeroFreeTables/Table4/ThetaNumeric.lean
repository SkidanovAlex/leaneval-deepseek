import Mathlib

noncomputable section

namespace Work.ZeroFreeTables.Table4

private lemma arctan_lt_self {x : ℝ} (hx : 0 < x) : Real.arctan x < x := by
  have hmono : StrictMonoOn (fun t : ℝ => t - Real.arctan t) (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · exact ContinuousOn.sub continuousOn_id Real.continuous_arctan.continuousOn
    · intro y hy
      rw [interior_Ici, Set.mem_Ioi] at hy
      have hderiv : deriv (fun t : ℝ => t - Real.arctan t) y = 1 - 1/(1+y^2) := by
        have h := (hasDerivAt_id y).sub (Real.hasDerivAt_arctan y)
        exact h.deriv
      rw [hderiv, sub_pos, div_lt_one (by positivity : (0:ℝ) < 1 + y^2)]
      nlinarith [sq_pos_of_ne_zero hy.ne']
  have h0 : (0:ℝ) ∈ Set.Ici 0 := by simp
  have hx' : x ∈ Set.Ici 0 := le_of_lt hx
  have h := hmono h0 hx' hx
  simp only [Real.arctan_zero, sub_zero] at h
  linarith

private def gth (t : ℝ) : ℝ := t * (t^2 + 2) / (2 * (t^2 + 1))

private def Fth (t : ℝ) : ℝ := Real.arctan t - gth t

private lemma gth_hasDerivAt (x : ℝ) :
    HasDerivAt gth (((3*x^2+2)*(2*(x^2+1)) - (x*(x^2+2))*(4*x))/(2*(x^2+1))^2) x := by
  unfold gth
  have hnum : HasDerivAt (fun t : ℝ => t * (t^2+2)) (3*x^2+2) x := by
    have hid : HasDerivAt (fun t : ℝ => t) (1:ℝ) x := hasDerivAt_id x
    have hd2 : HasDerivAt (fun t : ℝ => t^2 + 2) (2*x) x := by
      simpa using ((hasDerivAt_id x).pow 2).add_const 2
    have h : HasDerivAt (fun t : ℝ => t * (t^2+2)) ((1:ℝ)*(x^2+2) + x*(2*x)) x := hid.mul hd2
    have hd : (1:ℝ) * (x ^ 2 + 2) + x * (2 * x) = 3 * x ^ 2 + 2 := by ring
    rw [hd] at h
    exact h
  have hden : HasDerivAt (fun t : ℝ => 2*(t^2+1)) (4*x) x := by
    have hd1 : HasDerivAt (fun t : ℝ => t^2 + 1) (2*x) x := by
      simpa using ((hasDerivAt_id x).pow 2).add_const 1
    have h : HasDerivAt (fun t : ℝ => 2*(t^2+1)) ((2:ℝ)*(2*x)) x := hd1.const_mul 2
    have hd : (2:ℝ) * (2 * x) = 4 * x := by ring
    rw [hd] at h
    exact h
  have hdenne : (2*(x^2+1)) ≠ 0 := by positivity
  exact hnum.div hden hdenne

private lemma gth_deriv_value (x : ℝ) :
    HasDerivAt gth ((x^4+x^2+2)/(2*(1+x^2)^2)) x := by
  have hmain := gth_hasDerivAt x
  have hd : ((3*x^2+2)*(2*(x^2+1)) - (x*(x^2+2))*(4*x))/(2*(x^2+1))^2
      = (x^4+x^2+2)/(2*(1+x^2)^2) := by
    field_simp
    ring
  rw [hd] at hmain
  exact hmain

private lemma Fth_hasDerivAt (x : ℝ) : HasDerivAt Fth (x^2*(1-x^2)/(2*(1+x^2)^2)) x := by
  have hmain : HasDerivAt Fth (1/(1+x^2) - (x^4+x^2+2)/(2*(1+x^2)^2)) x := by
    have h1 : HasDerivAt (fun t : ℝ => Real.arctan t) (1/(1+x^2)) x := Real.hasDerivAt_arctan x
    exact h1.sub (gth_deriv_value x)
  have hd : (1/(1+x^2) - (x^4+x^2+2)/(2*(1+x^2)^2)) = x^2*(1-x^2)/(2*(1+x^2)^2) := by
    field_simp
    ring
  rw [hd] at hmain
  exact hmain

private lemma Fth_continuousOn : ContinuousOn Fth (Set.Ioi 1) := by
  apply Continuous.continuousOn
  unfold Fth gth
  apply Continuous.sub
  · exact Real.continuous_arctan
  · apply Continuous.div
    · exact continuous_id.mul ((continuous_id.pow 2).add continuous_const)
    · exact ((continuous_id.pow 2).add continuous_const).const_mul 2
    · intro x; positivity

private lemma Fth_strictAntiOn : StrictAntiOn Fth (Set.Ioi 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioi 1) Fth_continuousOn
  intro x hx
  rw [interior_Ioi, Set.mem_Ioi] at hx
  rw [(Fth_hasDerivAt x).deriv]
  have hxsq : 1 < x^2 := by nlinarith [hx]
  exact div_neg_of_neg_of_pos (by nlinarith [hxsq]) (by positivity)

private lemma Fth_T_neg : Fth (Real.sqrt (71/29)) < 0 := by
  set T := Real.sqrt (71/29) with hTdef
  have hTpos : 0 < T := by rw [hTdef]; exact Real.sqrt_pos_of_pos (by norm_num)
  have hT2 : T^2 = 71/29 := by rw [hTdef]; exact Real.sq_sqrt (by norm_num)
  have hTgt1 : 1 < T := by
    rw [hTdef, Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 1)]; norm_num
  have hu_lt1 : ((T-1)/(T+1)) < 1 := by
    rw [div_lt_one (by linarith : (0:ℝ) < T+1)]; linarith
  have hu_pos : 0 < (T-1)/(T+1) := by apply div_pos <;> linarith
  have hadd : Real.arctan T = Real.pi/4 + Real.arctan ((T-1)/(T+1)) := by
    have h := Real.arctan_add (x := (T-1)/(T+1)) (y := 1) (by rw [mul_one]; exact hu_lt1)
    rw [Real.arctan_one] at h
    have hTu : (((T-1)/(T+1))+1)/(1-((T-1)/(T+1))*1) = T := by
      rw [mul_one]
      have hT1 : T + 1 ≠ 0 := by linarith
      field_simp
      ring
    rw [hTu] at h
    linarith [h]
  have hkey : (63/20 : ℝ) < 129*T/50 - 4*((T-1)/(T+1)) := by
    have hTlt : T < 313/200 := by
      rw [hTdef, Real.sqrt_lt (by norm_num : (0:ℝ) ≤ 71/29) (by norm_num)]; norm_num
    have hnum : 0 < 258*T^2 - 457*T + 85 := by
      rw [hT2]; nlinarith [hTlt]
    have hden : 0 < 100*(T+1) := by linarith
    have heq : 258*T^2 - 457*T + 85
        = 100*(T+1)*(129*T/50 - 4*((T-1)/(T+1)) - 63/20) := by
      field_simp
      ring
    have hb : 0 < 129*T/50 - 4*((T-1)/(T+1)) - 63/20 :=
      pos_of_mul_pos_right (by rw [← heq]; exact hnum) (le_of_lt hden)
    linarith
  have hW : Real.pi < 129*T/50 - 4*((T-1)/(T+1)) := by
    have hpi : Real.pi < 63/20 := by linarith [Real.pi_lt_d2]
    linarith
  have harctan_u : Real.arctan ((T-1)/(T+1)) < (T-1)/(T+1) := arctan_lt_self hu_pos
  have hmain : Real.arctan T < 129*T/200 := by
    rw [hadd]
    have : Real.pi/4 + (T-1)/(T+1) < 129*T/200 := by linarith
    linarith
  have hphi : T * (T^2 + 2) / (2 * (T^2 + 1)) = 129*T/200 := by
    rw [hT2]; ring
  unfold Fth gth
  rw [hphi]
  exact sub_neg.mpr hmain



theorem ThetaNumeric (θ : ℝ) (h0 : 3 / 4 < θ) (h1 : θ < Real.pi / 2)
    (heq : Real.sin θ ^ 2 = 2 * (1 - θ * (Real.cos θ / Real.sin θ))) :
    (29 / 100 : ℝ) ≤ Real.cos θ ^ 2 := by
  have hθpos : 0 < θ := by linarith
  have hθltpi : θ < Real.pi := by linarith [Real.pi_pos]
  have hcos_pos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], h1⟩
  have hsin_pos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθpos hθltpi
  have hcos_ne : Real.cos θ ≠ 0 := ne_of_gt hcos_pos
  have hsin_ne : Real.sin θ ≠ 0 := ne_of_gt hsin_pos
  set t := Real.tan θ with ht
  have ht_pos : 0 < t := by rw [ht]; exact Real.tan_pos_of_pos_of_lt_pi_div_two hθpos h1
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have hcos_sq : Real.cos θ^2 = (1 + t^2)⁻¹ := by
    have h := Real.inv_one_add_tan_sq (x := θ) hcos_ne
    rw [← ht] at h
    exact h.symm
  have hkey : θ = gth t := by
    unfold gth
    have hsin_sq : Real.sin θ^2 = t^2/(1+t^2) := by
      rw [Real.sin_sq, hcos_sq]
      field_simp
      ring
    have hcot : Real.cos θ / Real.sin θ = 1/t := by
      rw [ht, Real.tan_eq_sin_div_cos, one_div]
      rw [inv_div]
    rw [hsin_sq, hcot] at heq
    field_simp at heq ⊢
    nlinarith [heq]
  have hF_t : Fth t = 0 := by
    have h1' : Real.arctan t = θ := by rw [ht]; exact Real.arctan_tan (by linarith [Real.pi_pos]) h1
    unfold Fth
    rw [h1', hkey.symm]
    ring
  have ht_le_T : t ≤ Real.sqrt (71/29) := by
    by_contra hcon
    rw [not_le] at hcon
    have hTmem : Real.sqrt (71/29) ∈ Set.Ioi 1 := by
      rw [Set.mem_Ioi, Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 1)]; norm_num
    have htmem : t ∈ Set.Ioi 1 := by
      rw [Set.mem_Ioi]; exact lt_of_lt_of_le hTmem hcon.le
    have hh := Fth_strictAntiOn hTmem htmem hcon
    rw [hF_t] at hh
    linarith [Fth_T_neg]
  have hsqrt2 : (Real.sqrt (71/29))^2 = 71/29 := Real.sq_sqrt (by norm_num)
  have hs : 0 ≤ Real.sqrt (71/29) := Real.sqrt_nonneg _
  have ht2 : t^2 ≤ 71/29 := by nlinarith [ht_le_T, le_of_lt ht_pos, hsqrt2, hs]
  rw [hcos_sq]
  have hle : 1 + t^2 ≤ 100/29 := by linarith
  have hp : 0 < (1:ℝ) + t^2 := by positivity
  calc (29/100 : ℝ) = 1/(100/29) := by norm_num
    _ ≤ 1/(1+t^2) := one_div_le_one_div_of_le hp hle
    _ = (1+t^2)⁻¹ := by rw [one_div]
end Work.ZeroFreeTables.Table4
