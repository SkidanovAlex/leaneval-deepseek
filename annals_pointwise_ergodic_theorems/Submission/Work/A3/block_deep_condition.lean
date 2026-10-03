import Mathlib

/-!
# The "deep arc" block condition (Area A3)

This is an elementary but fiddly real-variable inequality used when a block of the
circle-method sum is known to lie in a deep (major) arc: from the size hypothesis

`(N/qn)^{d/(d+1)} / 100 ≤ |β| · N^d`

one deduces

`c₀ · Mr^{d/(d+1)} ≤ 2π d! (|β| ℓ qn^d) Mr^d`

where `c₀ = cdeep / 2^{d+1}` and `cdeep = 2π d! ℓ / 100`, under the two constraints
`Mr ≤ 2N/qn` and `N/2 ≤ qn·Mr` linking the block length `Mr` with `N` and `qn`.

The mathematical content is the chain

`Mr^{d/(d+1)} / (100·2^{d+1}) = (1/2^{d+1}) · Mr^{d/(d+1)}/100
  ≤ (qn Mr/N)^{d - d/(d+1)} · Mr^{d/(d+1)}/100
  = (N/qn)^{d/(d+1)} · qn^d Mr^d / (100 N^d)
  ≤ |β| qn^d Mr^d`,

where the second step uses `qn Mr/N ≥ 1/2` (from `N/2 ≤ qn Mr`) together with
`d - d/(d+1) ≤ d+1`, and the last step is the hypothesis multiplied by `qn^d Mr^d/N^d`.
-/

namespace Work.A3

/-- Exponent algebra: with `D = d` and `0 < a < D`, the quantity `(qn Mr/N)^{D-a}·Mr^a`
equals `(N/qn)^a · (qn Mr/N)^D`. -/
private lemma rpow_identity {a D qn Mr N : ℝ} (hqn : 0 < qn) (hMr : 0 < Mr) (hN : 0 < N) :
    (qn * Mr / N) ^ (D - a) * Mr ^ a = (N / qn) ^ a * (qn * Mr / N) ^ D := by
  have hx : 0 < qn * Mr / N := by positivity
  have hdiv : Mr / (qn * Mr / N) = N / qn := by
    field_simp
  have hstep : (qn * Mr / N) ^ D / (qn * Mr / N) ^ a * Mr ^ a
      = (qn * Mr / N) ^ D * (Mr / (qn * Mr / N)) ^ a := by
    rw [Real.div_rpow (le_of_lt hMr) (le_of_lt hx)]
    ring
  rw [Real.rpow_sub hx, hstep, hdiv, mul_comm]

/-- The analytic core of `block_deep_condition`, with the exponent `a` given abstractly as
`a = d/(d+1)`. -/
private lemma core (d : ℕ) (hd : 2 ≤ d) {qn N β Mr a : ℝ} (hqn1 : 1 ≤ qn) (hMr2 : 2 ≤ Mr)
    (ha : a = (d : ℝ) / ((d : ℝ) + 1))
    (hMrN : Mr ≤ 2 * N / qn) (hqnMr : N / 2 ≤ qn * Mr)
    (hdeep : (N / qn) ^ a / 100 ≤ |β| * N ^ d) :
    Mr ^ a / (100 * 2 ^ (d + 1)) ≤ |β| * qn ^ d * Mr ^ d := by
  have hqnpos : 0 < qn := by linarith
  have hMrpos : 0 < Mr := by linarith
  have hMqn : Mr * qn ≤ 2 * N := by
    have h := mul_le_mul_of_nonneg_right hMrN (le_of_lt hqnpos)
    have h2 : 2 * N / qn * qn = 2 * N := div_mul_cancel₀ (2 * N) (ne_of_gt hqnpos)
    rw [h2] at h
    exact h
  have hNpos : 0 < N := by nlinarith [hMqn, hqn1, hMr2]
  have hapos : 0 < a := by rw [ha]; positivity
  have hDa : 0 ≤ (d : ℝ) - a := by
    rw [ha, sub_nonneg, div_le_iff₀ (by positivity : (0:ℝ) < (d:ℝ)+1)]
    nlinarith
  have hDa' : (d : ℝ) - a ≤ (d : ℝ) + 1 := by linarith [hapos]
  have hratio : (1:ℝ)/2 ≤ qn * Mr / N := by
    rw [le_div_iff₀ hNpos]
    linarith [hqnMr]
  have hpow2 : (1:ℝ)/(2:ℝ)^((d:ℝ)+1) ≤ (qn * Mr / N) ^ ((d:ℝ) - a) := by
    have hb : ((1:ℝ)/2) ^ ((d:ℝ) - a) ≤ (qn * Mr / N) ^ ((d:ℝ) - a) :=
      Real.rpow_le_rpow (by norm_num) hratio hDa
    have hb2 : (1:ℝ)/(2:ℝ)^((d:ℝ)+1) ≤ ((1:ℝ)/2) ^ ((d:ℝ) - a) := by
      have hge := Real.rpow_le_rpow_of_exponent_ge (show (0:ℝ) < 1/2 by norm_num)
        (show (1:ℝ)/2 ≤ 1 by norm_num) hDa'
      have hgoal : ((1:ℝ)/2) ^ ((d:ℝ)+1) = (1:ℝ)/(2:ℝ)^((d:ℝ)+1) := by
        rw [one_div, Real.inv_rpow (show (0:ℝ) ≤ 2 by norm_num)]
        simp
      rwa [hgoal] at hge
    linarith [hb, hb2]
  have h2eq : (2:ℝ)^(d+1) = (2:ℝ)^((d:ℝ)+1) := by
    rw [← Real.rpow_natCast]
    push_cast
    ring
  have hMR : (qn * Mr / N) ^ ((d:ℝ)) = qn ^ d * Mr ^ d / N ^ d := by
    rw [Real.div_rpow (by positivity) (le_of_lt hNpos),
        Real.mul_rpow (le_of_lt hqnpos) (le_of_lt hMrpos),
        Real.rpow_natCast, Real.rpow_natCast, Real.rpow_natCast]
  have hid : (qn * Mr / N) ^ ((d:ℝ) - a) * Mr ^ a = (N / qn) ^ a * (qn ^ d * Mr ^ d / N ^ d) := by
    rw [rpow_identity (D := (d:ℝ)) (a := a) hqnpos hMrpos hNpos, hMR]
  have hscaled : (N / qn) ^ a / 100 * (qn ^ d * Mr ^ d / N ^ d) ≤ |β| * qn ^ d * Mr ^ d := by
    have hnn : (0:ℝ) ≤ qn ^ d * Mr ^ d / N ^ d := by positivity
    refine le_trans (mul_le_mul_of_nonneg_right hdeep hnn) ?_
    refine le_of_eq ?_
    field_simp
  have hsplit : Mr ^ a / (100 * (2:ℝ)^((d:ℝ)+1)) = Mr^a/100 * (1/(2:ℝ)^((d:ℝ)+1)) := by
    field_simp
  have hle2 : Mr^a/100 * (1/(2:ℝ)^((d:ℝ)+1)) ≤ Mr^a/100 * (qn*Mr/N)^((d:ℝ)-a) :=
    mul_le_mul_of_nonneg_left hpow2 (by positivity)
  have hident : Mr^a/100 * (qn*Mr/N)^((d:ℝ)-a) = (N/qn)^a/100 * (qn^d*Mr^d/N^d) := by
    rw [show Mr^a/100 * (qn*Mr/N)^((d:ℝ)-a) = (qn*Mr/N)^((d:ℝ)-a) * Mr^a / 100 by ring, hid]
    ring
  rw [h2eq]
  calc Mr ^ a / (100 * (2:ℝ)^((d:ℝ)+1))
      = Mr^a/100 * (1/(2:ℝ)^((d:ℝ)+1)) := hsplit
    _ ≤ Mr^a/100 * (qn*Mr/N)^((d:ℝ)-a) := hle2
    _ = (N/qn)^a/100 * (qn^d*Mr^d/N^d) := hident
    _ ≤ |β| * qn^d * Mr^d := hscaled

theorem block_deep_condition (d : ℕ) (hd : 2 ≤ d) {ℓ cdeep c₀ qn N β Mr : ℝ}
    (hℓpos : 0 < ℓ) (hcdeep : cdeep = 2 * Real.pi * (d.factorial : ℝ) * ℓ / 100)
    (hc₀ : c₀ = cdeep / 2 ^ (d + 1)) (hqn1 : 1 ≤ qn) (hMr2 : 2 ≤ Mr)
    (hMrN : Mr ≤ 2 * N / qn) (hqnMr : N / 2 ≤ qn * Mr)
    (hdeep : (N / qn) ^ ((d : ℝ) / ((d : ℝ) + 1)) / 100 ≤ |β| * N ^ d) :
    c₀ * Mr ^ ((d : ℝ) / ((d : ℝ) + 1))
      ≤ 2 * Real.pi * (d.factorial : ℝ) * (|β| * ℓ * qn ^ d) * Mr ^ d := by
  have hcore := core d hd (a := (d:ℝ)/((d:ℝ)+1)) hqn1 hMr2 rfl hMrN hqnMr hdeep
  have hApos : 0 < 2 * Real.pi * (d.factorial : ℝ) * ℓ := by positivity
  rw [hc₀, hcdeep]
  have hfac : (2 * Real.pi * (d.factorial : ℝ) * ℓ / 100) / 2 ^ (d + 1)
        * Mr ^ ((d:ℝ)/((d:ℝ)+1))
      = (2 * Real.pi * (d.factorial : ℝ) * ℓ)
        * (Mr ^ ((d:ℝ)/((d:ℝ)+1)) / (100 * 2 ^ (d + 1))) := by
    field_simp
  rw [hfac]
  calc (2 * Real.pi * (d.factorial : ℝ) * ℓ)
        * (Mr ^ ((d:ℝ)/((d:ℝ)+1)) / (100 * 2 ^ (d + 1)))
      ≤ (2 * Real.pi * (d.factorial : ℝ) * ℓ) * (|β| * qn ^ d * Mr ^ d) :=
        mul_le_mul_of_nonneg_left hcore (le_of_lt hApos)
    _ = 2 * Real.pi * (d.factorial : ℝ) * (|β| * ℓ * qn ^ d) * Mr ^ d := by ring

end Work.A3
