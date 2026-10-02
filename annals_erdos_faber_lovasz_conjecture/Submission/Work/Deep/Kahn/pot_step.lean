import Submission.Work.ConeSwitch.MathlibNoHG

/-!
# The potential step for Kahn's theorem (Kang--Kelly--Kühn--Methuku--Osthus, 2023)

Given two "states" `(Λ, D)` and `(Λ', D')` (number of edges / maximum degree of a linear
hypergraph) related by

* `Λ' ≥ Λ·(s - 2η)`  (the edge count shrinks by at most a factor `s - 2η`),
* `Λ'/D' ≥ (1 + γ/2)·(Λ/D)`  (the density `Λ/D` grows by a factor `1 + γ/2`),
* `1 - s ≤ (C/K)·(D/Λ)` and `8C/(Kγ) ≤ b`  (the loss factor `1 - s` is controlled by the
  density and by the parameter `b`),

the potential `Φ(Λ,D) = log Λ - b·D/Λ` decreases by at most `8η`:

`log Λ - b·D/Λ - 8η ≤ log Λ' - b·D'/Λ'`.

The proof is elementary but sharp.  Write `X = D/Λ`, `X' = D'/Λ'`, `w = 2η ≢ (0,1/8]` and
`v = bγX/8`.  The hypotheses give `s ≥ max(1/2, 1 - v)`, `X' ≤ X/(1+γ/2)` and hence
`b·X - b·X' ≥ bγX/3 = (8/3)v`.  The inequality therefore reduces to

`log(s - w) ≥ -(8/3)v - 4w`,

which is proved by splitting on `v ≤ 3/8`:

* if `v ≤ 3/8` then `t = 1 - v - w ∈ [1/2,1]` and `log t ≥ -2(1-t) = -2(v+w) ≥ -(8/3)v - 4w`;
* if `v > 3/8` then, using `1/2 - w = (1-2w)/2` and `log 2 ≤ 1` and
  `log(1-2w) ≥ -2w/(1-2w) ≥ -(8/3)w`, we get `log(s-w) ≥ -(8/3)w - 1 ≥ -(8/3)v - 4w`
  because `(8/3)v > 1`.
-/

namespace Work.Deep.Kahn

/-- For `t ∈ [1/2,1]` the logarithm is at least the secant-type lower bound `-2(1-t)`. -/
private lemma log_ge_two_sub (t : ℝ) (h1 : 1/2 ≤ t) (h2 : t ≤ 1) :
    Real.log t ≥ -2*(1 - t) := by
  have hpos : 0 < t := by linarith
  have hA : 1 - t⁻¹ ≤ Real.log t := Real.one_sub_inv_le_log_of_pos hpos
  have hE : (0:ℝ) ≤ (1 - t⁻¹) - (-2*(1 - t)) := by
    have hnum : (0:ℝ) ≤ (2*t - 1)*(1 - t) := mul_nonneg (by linarith) (by linarith)
    have hfrac : (2*t - 1)*(1 - t)/t = (1 - t⁻¹) - (-2*(1 - t)) := by
      field_simp
      try ring
    rw [← hfrac]
    exact div_nonneg hnum (le_of_lt hpos)
  linarith

/-- For `w ∈ (0, 1/8]` we have `log(1/2 - w) ≥ -(8/3)w - 1`. -/
private lemma log_half_sub_ge (w : ℝ) (hw : 0 < w) (hw18 : w ≤ 1/8) :
    Real.log (1/2 - w) ≥ -(8/3)*w - 1 := by
  have hp2 : 0 < 1 - 2*w := by linarith
  have heq : (1:ℝ)/2 - w = (1 - 2*w)/2 := by ring
  have hlg : Real.log (1/2 - w) = Real.log (1 - 2*w) - Real.log 2 := by
    rw [heq, Real.log_div (by linarith : (1:ℝ) - 2*w ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
  have hA : 1 - (1 - 2*w)⁻¹ ≤ Real.log (1 - 2*w) := Real.one_sub_inv_le_log_of_pos hp2
  have hB : 1 - (1 - 2*w)⁻¹ = -(2*w/(1 - 2*w)) := by field_simp; try ring
  have hC : (2*w/(1 - 2*w)) ≤ (8/3)*w := by
    have h34 : (3:ℝ)/4 ≤ 1 - 2*w := by linarith
    rw [div_le_iff₀ hp2]
    nlinarith [hw, h34]
  have hlog1 : Real.log (1 - 2*w) ≥ -(8/3)*w := by linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2)
    linarith
  linarith

/-- The key estimate: `log (s - w) ≥ -(8/3)v - 4w` whenever `s ≥ 1/2`, `s ≥ 1 - v`,
`0 < w ≤ 1/8` and `v ≥ 0`. -/
private lemma pot_key (s v w : ℝ) (hs : 1/2 ≤ s) (hsv : 1 - v ≤ s)
    (hw : 0 < w) (hw18 : w ≤ 1/8) (hv : 0 ≤ v) :
    Real.log (s - w) ≥ -(8/3)*v - 4*w := by
  rcases le_or_gt v (3/8) with hc | hc
  · have ht1 : 1/2 ≤ 1 - v - w := by linarith
    have ht2 : 1 - v - w ≤ 1 := by linarith
    have hp : 0 < 1 - v - w := by linarith
    have hsw : 1 - v - w ≤ s - w := by linarith
    have hlg1 : Real.log (1 - v - w) ≥ -2*(1 - (1 - v - w)) := log_ge_two_sub (1 - v - w) ht1 ht2
    have hlg2 : Real.log (s - w) ≥ Real.log (1 - v - w) := Real.log_le_log hp hsw
    have hid : -2*(1 - (1 - v - w)) = -2*(v + w) := by ring
    have hfin : -2*(v + w) ≥ -(8/3)*v - 4*w := by linarith
    linarith [hlg1, hlg2, hid, hfin]
  · have hs2 : 1/2 - w ≤ s - w := by linarith
    have hp3 : 0 < 1/2 - w := by linarith
    have hlg2 : Real.log (s - w) ≥ Real.log (1/2 - w) := Real.log_le_log hp3 hs2
    have hlog := log_half_sub_ge w hw hw18
    have hfin : -(8/3)*w - 1 ≥ -(8/3)*v - 4*w := by linarith
    linarith [hlg2, hlog, hfin]

theorem pot_step {Λ D Λ' D' : ℕ} {s b η γ C K : ℝ}
    (hΛ : 0 < (Λ : ℝ)) (hD : 0 < (D : ℝ)) (hΛ' : 0 < (Λ' : ℝ)) (hD' : 0 < (D' : ℝ))
    (hs1 : 1 / 2 ≤ s) (hη : 0 < η) (hηs : 8 * η ≤ 1 / 2) (hb0 : 0 ≤ b) (hγ0 : 0 < γ)
    (hγ1 : γ ≤ 1) (hηΛ : 1 ≤ η * (Λ : ℝ))
    (hΛ'mem : (Λ : ℝ) * s - 2 * η * (Λ : ℝ) ≤ (Λ' : ℝ))
    (h1s : 1 - s ≤ C / (K * ((Λ : ℝ) / (D : ℝ))))
    (hρ : (1 + γ / 2) * ((Λ : ℝ) / (D : ℝ)) ≤ (Λ' : ℝ) / (D' : ℝ))
    (hb : 8 * C / (K * γ) ≤ b) :
    Real.log (Λ : ℝ) - b * ((D : ℝ) / (Λ : ℝ)) - 8 * η ≤
      Real.log (Λ' : ℝ) - b * ((D' : ℝ) / (Λ' : ℝ)) := by
  have _hηΛ := hηΛ
  have hX : 0 < (D:ℝ)/(Λ:ℝ) := div_pos hD hΛ
  -- ### Step A: `1 - s ≤ (C/K)·(D/Λ) ≤ (bγ/8)·(D/Λ) = v`, so `s ≥ 1 - v`.
  have hCK : C*K⁻¹ ≤ b*γ/8 := by
    rcases eq_or_ne K 0 with hK | hK
    · rw [hK, inv_zero, mul_zero]
      have h1 : (0:ℝ) ≤ b*γ := mul_nonneg hb0 (le_of_lt hγ0)
      linarith
    · have h1 : (8*C/(K*γ))*γ = 8*(C*K⁻¹) := by
        field_simp
        try ring
      have h2 : (8*C/(K*γ))*γ ≤ b*γ := mul_le_mul_of_nonneg_right hb (le_of_lt hγ0)
      rw [h1] at h2
      linarith
  have h1s' : 1 - s ≤ C*K⁻¹*((D:ℝ)/(Λ:ℝ)) := by
    have he : C/(K*((Λ:ℝ)/(D:ℝ))) = C*K⁻¹*((D:ℝ)/(Λ:ℝ)) := by
      rw [div_eq_mul_inv, mul_inv, inv_div]
      try ring
    rw [he] at h1s
    exact h1s
  have hsv : 1 - b*γ*((D:ℝ)/(Λ:ℝ))/8 ≤ s := by
    have h2 : C*K⁻¹*((D:ℝ)/(Λ:ℝ)) ≤ b*γ*((D:ℝ)/(Λ:ℝ))/8 := by
      have h3 := mul_le_mul_of_nonneg_right hCK (le_of_lt hX)
      calc C*K⁻¹*((D:ℝ)/(Λ:ℝ)) ≤ (b*γ/8)*((D:ℝ)/(Λ:ℝ)) := h3
        _ = b*γ*((D:ℝ)/(Λ:ℝ))/8 := by ring
    linarith
  -- ### Step B: `b·X - b·X' ≥ bγX/3`.
  have hxx : ((D':ℝ)/(Λ':ℝ))*(1 + γ/2) ≤ (D:ℝ)/(Λ:ℝ) := by
    have h := hρ
    field_simp at h ⊢
    linarith
  have hx'le : ((D':ℝ)/(Λ':ℝ)) ≤ ((D:ℝ)/(Λ:ℝ))/(1+γ/2) :=
    (le_div_iff₀ (by linarith : (0:ℝ) < 1 + γ/2)).mpr hxx
  have hX1 : (D:ℝ)/(Λ:ℝ) - (D':ℝ)/(Λ':ℝ) ≥ (D:ℝ)/(Λ:ℝ)*γ/3 := by
    have hidA : (D:ℝ)/(Λ:ℝ) - ((D:ℝ)/(Λ:ℝ))/(1+γ/2) = (D:ℝ)/(Λ:ℝ)*γ/(2+γ) := by
      field_simp
      try ring
    have hstep1 : (D:ℝ)/(Λ:ℝ) - (D':ℝ)/(Λ':ℝ)
        ≥ (D:ℝ)/(Λ:ℝ) - ((D:ℝ)/(Λ:ℝ))/(1+γ/2) := by linarith
    have hstep2 : (D:ℝ)/(Λ:ℝ)*γ/(2+γ) ≥ (D:ℝ)/(Λ:ℝ)*γ/3 := by
      have hpos : (0:ℝ) < 2 + γ := by linarith
      have hle : (2 + γ) ≤ 3 := by linarith
      have hinv : (1:ℝ)/3 ≤ 1/(2+γ) := one_div_le_one_div_of_le hpos hle
      have hXg : 0 ≤ (D:ℝ)/(Λ:ℝ)*γ := mul_nonneg (le_of_lt hX) (le_of_lt hγ0)
      calc (D:ℝ)/(Λ:ℝ)*γ/3 = (D:ℝ)/(Λ:ℝ)*γ*(1/3) := by ring
        _ ≤ (D:ℝ)/(Λ:ℝ)*γ*(1/(2+γ)) := mul_le_mul_of_nonneg_left hinv hXg
        _ = (D:ℝ)/(Λ:ℝ)*γ/(2+γ) := by ring
    linarith
  have hbx : b*((D:ℝ)/(Λ:ℝ)) - b*((D':ℝ)/(Λ':ℝ)) ≥ b*((D:ℝ)/(Λ:ℝ))*γ/3 := by
    have h1 : b*((D:ℝ)/(Λ:ℝ)*γ/3) ≤ b*((D:ℝ)/(Λ:ℝ) - (D':ℝ)/(Λ':ℝ)) :=
      mul_le_mul_of_nonneg_left hX1 hb0
    have h2 : b*((D:ℝ)/(Λ:ℝ) - (D':ℝ)/(Λ':ℝ))
        = b*((D:ℝ)/(Λ:ℝ)) - b*((D':ℝ)/(Λ':ℝ)) := by ring
    have h3 : b*((D:ℝ)/(Λ:ℝ)*γ/3) = b*((D:ℝ)/(Λ:ℝ))*γ/3 := by ring
    rw [h2, h3] at h1
    exact h1
  -- ### Step C: `log(Λ'/Λ) ≥ log(s - 2η)`.
  have hsm : (s - 2*η)*(Λ:ℝ) ≤ (Λ':ℝ) := by
    have h : (s - 2*η)*(Λ:ℝ) = (Λ:ℝ)*s - 2*η*(Λ:ℝ) := by ring
    rw [h]; exact hΛ'mem
  have hs2η : 0 < s - 2*η := by linarith
  have hdiv : s - 2*η ≤ (Λ':ℝ)/(Λ:ℝ) := (le_div_iff₀ hΛ).mpr hsm
  have hlog : Real.log ((Λ':ℝ)/(Λ:ℝ)) ≥ Real.log (s - 2*η) := Real.log_le_log hs2η hdiv
  -- ### Step D: the key estimate, with `v = bγ(D/Λ)/8` and `w = 2η`.
  have hv0 : 0 ≤ b*γ*((D:ℝ)/(Λ:ℝ))/8 := by
    have h1 : (0:ℝ) ≤ b*γ*((D:ℝ)/(Λ:ℝ)) :=
      mul_nonneg (mul_nonneg hb0 (le_of_lt hγ0)) (le_of_lt hX)
    exact div_nonneg h1 (by norm_num)
  have hη18 : 2*η ≤ 1/8 := by linarith
  have hkey : Real.log (s - 2*η) ≥ -(8/3)*(b*γ*((D:ℝ)/(Λ:ℝ))/8) - 4*(2*η) :=
    pot_key s (b*γ*((D:ℝ)/(Λ:ℝ))/8) (2*η) hs1 hsv (by linarith) hη18 hv0
  -- ### Step E: assemble.
  have hid : -(8/3)*(b*γ*((D:ℝ)/(Λ:ℝ))/8) = -(b*((D:ℝ)/(Λ:ℝ))*γ/3) := by ring
  have hld : Real.log ((Λ':ℝ)/(Λ:ℝ)) = Real.log (Λ':ℝ) - Real.log (Λ:ℝ) :=
    Real.log_div hΛ'.ne' hΛ.ne'
  linarith [hlog, hkey, hid, hbx, hld]

end Work.Deep.Kahn
