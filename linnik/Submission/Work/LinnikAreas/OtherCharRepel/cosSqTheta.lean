import Mathlib

namespace Work.LinnikAreas.OtherCharRepel

open Real Filter

noncomputable section

/-- Auxiliary function `ψ(t) = t(2+t²)/(2(1+t²)) - arctan t`. Its zeros on `(1,∞)` are exactly
the values `t = tan θ` for `θ ∈ (π/4, π/2)` solving `θ = (1+cos²θ)/2 · tan θ`. -/
private def psi (t : ℝ) : ℝ := t * (2 + t^2)/(2*(1+t^2)) - Real.arctan t

private lemma continuous_psi : Continuous psi := by
  unfold psi
  apply Continuous.sub
  · apply Continuous.div
    · fun_prop
    · fun_prop
    · intro x; positivity
  · fun_prop

private lemma hasDerivAt_psi (t : ℝ) : HasDerivAt psi (t^2*(t^2-1)/(2*(1+t^2)^2)) t := by
  unfold psi
  have hsq : HasDerivAt (fun s:ℝ => s^2) (2*t) t := by
    have h : HasDerivAt ((id : ℝ → ℝ)^2) (2*t) t := ((hasDerivAt_id t).pow 2).congr_deriv (by simp)
    exact h.congr_of_eventuallyEq (Eventually.of_forall (fun s => by simp [Pi.pow_apply]))
  have h2s : HasDerivAt (fun s:ℝ => 2 + s^2) (2*t) t := by
    have h : HasDerivAt ((fun _ : ℝ => (2:ℝ)) + (fun s:ℝ => s^2)) (2*t) t :=
      ((hasDerivAt_const t (2:ℝ)).add hsq).congr_deriv (by simp)
    exact h.congr_of_eventuallyEq (Eventually.of_forall (fun s => by simp [Pi.add_apply]))
  have hnum : HasDerivAt (fun s:ℝ => s*(2+s^2)) ((2+t^2) + t*(2*t)) t := by
    have h : HasDerivAt ((id : ℝ → ℝ) * (fun s:ℝ => 2+s^2)) ((2+t^2) + t*(2*t)) t :=
      ((hasDerivAt_id t).mul h2s).congr_deriv (by simp)
    exact h.congr_of_eventuallyEq (Eventually.of_forall (fun s => by simp [Pi.mul_apply]))
  have h1s : HasDerivAt (fun s:ℝ => 1 + s^2) (2*t) t := by
    have h : HasDerivAt ((fun _ : ℝ => (1:ℝ)) + (fun s:ℝ => s^2)) (2*t) t :=
      ((hasDerivAt_const t (1:ℝ)).add hsq).congr_deriv (by simp)
    exact h.congr_of_eventuallyEq (Eventually.of_forall (fun s => by simp [Pi.add_apply]))
  have hden : HasDerivAt (fun s:ℝ => 2*(1+s^2)) (2*(2*t)) t := by
    have h : HasDerivAt ((fun _ : ℝ => (2:ℝ)) * (fun s:ℝ => 1+s^2)) (2*(2*t)) t :=
      ((hasDerivAt_const t (2:ℝ)).mul h1s).congr_deriv (by ring)
    exact h.congr_of_eventuallyEq (Eventually.of_forall (fun s => by simp [Pi.mul_apply]))
  have hquot := hnum.div hden (by positivity : (2:ℝ)*(1+t^2) ≠ 0)
  have harc := Real.hasDerivAt_arctan t
  refine (hquot.sub harc).congr_deriv ?_
  have h1 : (1+t^2) ≠ 0 := by positivity
  field_simp
  ring

private lemma deriv_psi (t:ℝ) : deriv psi t = t^2*(t^2-1)/(2*(1+t^2)^2) := (hasDerivAt_psi t).deriv

private lemma psi_zero : psi 0 = 0 := by simp [psi]

private lemma psi_one : psi 1 = (3 - Real.pi)/4 := by
  unfold psi; rw [Real.arctan_one]; norm_num; ring

private lemma psi_strictAntiOn : StrictAntiOn psi (Set.Icc 0 1) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 1) continuous_psi.continuousOn
  intro x hx
  rw [deriv_psi]
  have hx' : x ∈ Set.Ioo 0 1 := by simpa [interior_Icc] using hx
  have hx2 : x^2 < 1 := by
    have ha : 0 < 1 - x := by linarith [hx'.2]
    have hb : 0 < 1 + x := by linarith [hx'.1]
    nlinarith [mul_pos ha hb]
  have h2 : 0 < x^2 := pow_pos hx'.1 2
  refine div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h2 (by linarith)) ?_
  positivity

private lemma psi_strictMonoOn : StrictMonoOn psi (Set.Ici 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 1) continuous_psi.continuousOn
  intro x hx
  rw [deriv_psi]
  have hx' : 1 < x := by simpa [interior_Ici] using hx
  have h2 : 0 < x^2 := pow_pos (by linarith) 2
  refine div_pos (mul_pos h2 ?_) ?_
  · nlinarith
  · positivity

private lemma hasDerivAt_g (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.arctan y - y + y^3/3) (x^4/(1+x^2)) x := by
  have h1 : HasDerivAt (fun y:ℝ => Real.arctan y) (1/(1+x^2)) x := Real.hasDerivAt_arctan x
  have h2 : HasDerivAt (fun y:ℝ => y) 1 x := hasDerivAt_id x
  have h3 : HasDerivAt (fun y:ℝ => y^3/3) (x^2) x := by
    have h := (hasDerivAt_id x).pow 3
    have h' : HasDerivAt ((id:ℝ→ℝ)^3) (3*x^2) x := h.congr_deriv (by simp only [id_eq]; ring)
    have h'' : HasDerivAt (fun y:ℝ => y^3) (3*x^2) x :=
      h'.congr_of_eventuallyEq (Eventually.of_forall (fun s => by simp [Pi.pow_apply]))
    have h4 := h''.div_const 3
    refine h4.congr_deriv ?_
    ring
  have h := (h1.sub h2).add h3
  refine h.congr_deriv ?_
  have hden : (1+x^2) ≠ 0 := by positivity
  field_simp
  ring

private lemma cont_g : Continuous (fun y : ℝ => Real.arctan y - y + y^3/3) := by
  fun_prop

/-- `x - x³/3 ≤ arctan x` for `x ≥ 0`. -/
private lemma arctan_ge (x : ℝ) (hx : 0 ≤ x) : x - x^3/3 ≤ Real.arctan x := by
  have hg : MonotoneOn (fun y : ℝ => Real.arctan y - y + y^3/3) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact cont_g.continuousOn
    · intro y hy
      exact (hasDerivAt_g y).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Ici] at hy
      rw [(hasDerivAt_g y).deriv]
      exact div_nonneg (pow_nonneg (le_of_lt hy) 4) (by positivity)
  have h := hg (show (0:ℝ) ∈ Set.Ici 0 by simp) hx (show (0:ℝ) ≤ x by linarith)
  simp at h
  linarith

/-- `(2+tan²θ)/(2(1+tan²θ)) = (1+cos²θ)/2`. -/
private lemma tan_factor (θ : ℝ) (hc : Real.cos θ ≠ 0) :
    (2 + Real.tan θ^2)/(2*(1+Real.tan θ^2)) = (1 + Real.cos θ^2)/2 := by
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The numerical crux: `ψ(√151/7) > 0`, i.e. `arctan(√151/7) < 249√151/2800`. -/
private lemma psi_tstar_pos : 0 < psi (Real.sqrt 151 / 7) := by
  set r : ℝ := Real.sqrt 151 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; exact Real.sqrt_pos_of_pos (by norm_num)
  have hrne : r ≠ 0 := hrpos.ne'
  have hr2 : r^2 = 151 := by rw [hrdef]; exact Real.sq_sqrt (by norm_num)
  have hrb : r < 25/2 := by
    rw [hrdef, Real.sqrt_lt' (by norm_num : (0:ℝ) < 25/2)]
    norm_num
  have hnum1 : 7/r - (7/r)^3/3 = 2828/(453*r) := by
    field_simp
    nlinarith [hr2]
  have harc : Real.arctan (r/7) < 249*r/2800 := by
    have hr7 : 0 < r/7 := by positivity
    have hinv : (r/7)⁻¹ = 7/r := by rw [inv_div]
    have h := Real.arctan_inv_of_pos hr7
    rw [hinv] at h
    have heq : Real.arctan (r/7) = Real.pi/2 - Real.arctan (7/r) := by linarith
    rw [heq]
    have hlow : 7/r - (7/r)^3/3 ≤ Real.arctan (7/r) := arctan_ge (7/r) (by positivity)
    have hpi : Real.pi/2 < (3927:ℝ)/2500 := by have := Real.pi_lt_d20; linarith
    have hkey : (3927:ℝ)/2500 < 2828/(453*r) + 249*r/2800 := by
      have h1 : (453:ℝ)*r ≠ 0 := by positivity
      have h2 : (2800:ℝ) ≠ 0 := by norm_num
      have h3 : (2500:ℝ) ≠ 0 := by norm_num
      field_simp
      nlinarith [hr2, hrb, hrpos]
    linarith [hlow, hnum1, hpi, hkey]
  have hpsi : psi (r/7) = 249*r/2800 - Real.arctan (r/7) := by
    unfold psi
    have hmain : (r/7)*(2+(r/7)^2)/(2*(1+(r/7)^2)) = 249*r/2800 := by
      have h7 : (7:ℝ) ≠ 0 := by norm_num
      have h : 1 + (r/7)^2 ≠ 0 := by positivity
      field_simp
      nlinarith [hr2]
    rw [hmain]
  rw [hpsi]; linarith [harc]

theorem cosSqTheta : ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
    Real.sin θ ^ 2 = 2 * (1 - θ * (Real.cos θ / Real.sin θ)) → (49/200 : ℝ) < Real.cos θ ^ 2 := by
  intro θ hθ0 hθπ h
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith)
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, hθπ⟩
  have key : θ = (1 + Real.cos θ ^ 2)/2 * Real.tan θ := by
    have hs2 : Real.sin θ ^ 2 = 1 - Real.cos θ ^ 2 := Real.sin_sq θ
    have h1 : 2 * (1 - θ*(Real.cos θ/Real.sin θ)) = 1 - Real.cos θ ^ 2 := by rw [← h, hs2]
    have h2 : θ * (Real.cos θ / Real.sin θ) = (1 + Real.cos θ ^ 2)/2 := by
      field_simp at h1 ⊢
      linarith
    rw [Real.tan_eq_sin_div_cos, ← h2]
    field_simp
  set t : ℝ := Real.tan θ with ht
  have htpos : 0 < t := by rw [ht]; exact Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθπ
  have hpsi0 : psi t = 0 := by
    have harctan : Real.arctan t = θ := by rw [ht]; exact Real.arctan_tan (by linarith) hθπ
    have hfirst : t * (2 + t^2)/(2*(1+t^2)) = (1 + Real.cos θ ^ 2)/2 * Real.tan θ := by
      rw [ht, mul_div_assoc, tan_factor θ hcos.ne']
      ring
    unfold psi
    rw [harctan, hfirst]
    linarith [key]
  have ht_gt_one : 1 < t := by
    by_contra hcon
    have hconle : t ≤ 1 := le_of_not_gt hcon
    have hlt : psi t < psi 0 :=
      psi_strictAntiOn (show (0:ℝ) ∈ Set.Icc 0 1 by simp) (show t ∈ Set.Icc 0 1 from ⟨htpos.le, hconle⟩) htpos
    rw [hpsi0, psi_zero] at hlt
    linarith
  have htlt : t < Real.sqrt 151 / 7 := by
    by_contra hcon
    have hconle : Real.sqrt 151 / 7 ≤ t := le_of_not_gt hcon
    have htstar : Real.sqrt 151 / 7 ∈ Set.Ici 1 := by
      rw [Set.mem_Ici]
      have h7 : (7:ℝ) < Real.sqrt 151 := by
        rw [Real.lt_sqrt (by norm_num : (0:ℝ) ≤ 7)]
        norm_num
      linarith
    have htmem : t ∈ Set.Ici 1 := le_trans htstar hconle
    have hle : psi (Real.sqrt 151/7) ≤ psi t :=
      (psi_strictMonoOn.monotoneOn) htstar htmem hconle
    rw [hpsi0] at hle
    linarith [psi_tstar_pos]
  have hcossq : Real.cos θ ^ 2 = 1/(1+t^2) := by
    rw [ht, Real.tan_eq_sin_div_cos]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [hcossq]
  have htstarpos : 0 < Real.sqrt 151 / 7 := by positivity
  have ht2 : t^2 < (Real.sqrt 151/7)^2 := by nlinarith [htlt, htpos, htstarpos]
  have hst : (Real.sqrt 151/7)^2 = 151/49 := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 151)]; norm_num
  have htt2 : t^2 < 151/49 := by rw [← hst]; exact ht2
  rw [lt_div_iff₀ (by positivity : (0:ℝ) < 1+t^2)]
  nlinarith [htt2]

end

end Work.LinnikAreas.OtherCharRepel
