import Mathlib

namespace Work.BourgainPlan.Maximal

/-! Real-arithmetic bookkeeping for the two-exponent (strong/weak) interpolation step
in the Calderón-type argument: with `r = p - q`, `s = p₀ - p`, `D = p₀ - q = r + s`,
the two terms `A σ^{-r}` and `B σ^{s}` balance when `σ = (A/B)^{1/D}`, and the common
value is bounded by `2^{p+1} (1/r + 1/s) Kq^{θp} Kp^{(1-θ)p}` with `A = (2Kq)^q/r`,
`B = (2Kp)^{p₀}/s`.

The three auxiliary lemmas below are the pieces:
* `inv_rpow_geom_le` — the weighted AM–GM step `(r^{s/D} s^{r/D})⁻¹ ≤ 1/r + 1/s`;
* `balance_identity` — the exact balance `Aσ^{-r} + Bσ^{s} = 2 A^{s/D} B^{r/D}`;
* `AB_decomp` — the expansion of `A^{s/D} B^{r/D}` in terms of `2^p`, `Kq`, `Kp`.
-/

/-- Weighted AM–GM, in the shape needed here: `(1/r)^{s/D} (1/s)^{r/D} ≤ 1/r + 1/s`
with `D = r + s`; equivalently `(r^{s/D} s^{r/D})⁻¹ ≤ 1/r + 1/s`. -/
lemma inv_rpow_geom_le {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    (r ^ (s / (r + s)) * s ^ (r / (r + s)))⁻¹ ≤ 1 / r + 1 / s := by
  have hD : 0 < r + s := by linarith
  have hw1 : 0 ≤ s / (r + s) := div_nonneg hs.le hD.le
  have hw2 : 0 ≤ r / (r + s) := div_nonneg hr.le hD.le
  have hw : s / (r + s) + r / (r + s) = 1 := by
    field_simp
    ring
  have hgm := Real.geom_mean_le_arith_mean2_weighted hw1 hw2
    (by positivity : (0:ℝ) ≤ 1/r) (by positivity : (0:ℝ) ≤ 1/s) hw
  have hstep1 : (1/r) ^ (s/(r+s)) * (1/s) ^ (r/(r+s))
      = (r ^ (s/(r+s)) * s ^ (r/(r+s)))⁻¹ := by
    rw [one_div, one_div, Real.inv_rpow hr.le (s/(r+s)), Real.inv_rpow hs.le (r/(r+s)),
      ← mul_inv]
  have hstep3 : (s/(r+s)) * (1/r) + (r/(r+s)) * (1/s) ≤ 1/r + 1/s := by
    have h1 : s/(r+s) ≤ 1 := (div_le_one hD).mpr (by linarith)
    have h2 : r/(r+s) ≤ 1 := (div_le_one hD).mpr (by linarith)
    have h1' : (s/(r+s)) * (1/r) ≤ 1/r := by
      have := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ 1/r)
      simpa using this
    have h2' : (r/(r+s)) * (1/s) ≤ 1/s := by
      have := mul_le_mul_of_nonneg_right h2 (by positivity : (0:ℝ) ≤ 1/s)
      simpa using this
    linarith
  rw [← hstep1]
  linarith [hgm, hstep3]

/-- The two interpolation terms balance: with `σ = (A/B)^{1/(r+s)}`,
`A σ^{-r} + B σ^{s} = 2 A^{s/(r+s)} B^{r/(r+s)}`. -/
lemma balance_identity {A B r s : ℝ} (hA : 0 < A) (hB : 0 < B) (hr : 0 < r) (hs : 0 < s) :
    A * ((A / B) ^ (1 / (r + s))) ^ (-r) + B * ((A / B) ^ (1 / (r + s))) ^ s
      = 2 * A ^ (s / (r + s)) * B ^ (r / (r + s)) := by
  have hX : 0 < A / B := div_pos hA hB
  have h1 : (1 / (r + s)) * (-r) = -(r / (r + s)) := by ring_nf
  have h2 : (1 / (r + s)) * s = s / (r + s) := by ring
  have h3 : (1:ℝ) + -(r / (r + s)) = s / (r + s) := by field_simp; ring
  have h4 : (1:ℝ) + -(s / (r + s)) = r / (r + s) := by field_simp; ring
  have e1 : ((A / B) ^ (1 / (r + s))) ^ (-r) = A ^ (-(r/(r+s))) * B ^ (r/(r+s)) := by
    rw [← Real.rpow_mul hX.le (1 / (r + s)) (-r), h1,
        Real.div_rpow hA.le hB.le (-(r/(r+s))),
        Real.rpow_neg hA.le (r/(r+s)), Real.rpow_neg hB.le (r/(r+s)), div_inv_eq_mul]
  have e2 : ((A / B) ^ (1 / (r + s))) ^ s = A ^ (s/(r+s)) * (B ^ (s/(r+s)))⁻¹ := by
    rw [← Real.rpow_mul hX.le (1 / (r + s)) s, h2,
        Real.div_rpow hA.le hB.le (s/(r+s)), div_eq_mul_inv]
  have hA1 : A * A ^ (-(r/(r+s))) = A ^ (s/(r+s)) := by
    rw [show A * A ^ (-(r/(r+s))) = A ^ (1:ℝ) * A ^ (-(r/(r+s))) by rw [Real.rpow_one],
        ← Real.rpow_add hA 1 (-(r/(r+s))), h3]
  have hB1 : B * (B ^ (s/(r+s)))⁻¹ = B ^ (r/(r+s)) := by
    rw [← Real.rpow_neg hB.le (s/(r+s)),
        show B * B ^ (-(s/(r+s))) = B ^ (1:ℝ) * B ^ (-(s/(r+s))) by rw [Real.rpow_one],
        ← Real.rpow_add hB 1 (-(s/(r+s))), h4]
  rw [e1, e2]
  rw [show A * (A ^ (-(r/(r+s))) * B ^ (r/(r+s))) + B * (A ^ (s/(r+s)) * (B ^ (s/(r+s)))⁻¹)
        = A * A ^ (-(r/(r+s))) * B ^ (r/(r+s)) + A ^ (s/(r+s)) * (B * (B ^ (s/(r+s)))⁻¹) by ring,
      hA1, hB1]
  ring

/-- Expansion of the balanced value in terms of `2^p`, `Kq^{θp}`, `Kp^{(1-θ)p}`. -/
lemma AB_decomp {q p p₀ θ Kq Kp : ℝ} (hKq : 0 < Kq) (hKp : 0 < Kp)
    (hr : 0 < p - q) (hs : 0 < p₀ - p)
    (hθ : θ * p = q * (p₀ - p) / (p₀ - q))
    (hθ' : (1 - θ) * p = p₀ * (p - q) / (p₀ - q)) :
    ((2 * Kq) ^ q / (p - q)) ^ ((p₀ - p) / (p₀ - q))
        * ((2 * Kp) ^ p₀ / (p₀ - p)) ^ ((p - q) / (p₀ - q))
      = (2:ℝ) ^ p * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p)
          * ((p - q) ^ ((p₀ - p) / (p₀ - q)) * (p₀ - p) ^ ((p - q) / (p₀ - q)))⁻¹ := by
  have hD : 0 < p₀ - q := by linarith
  have h2 : (0:ℝ) < 2 := by norm_num
  have hA : ((2 * Kq) ^ q / (p - q)) ^ ((p₀ - p) / (p₀ - q))
      = (2:ℝ) ^ (q * (p₀ - p) / (p₀ - q)) * Kq ^ (q * (p₀ - p) / (p₀ - q))
          * (p - q) ^ (-((p₀ - p) / (p₀ - q))) := by
    rw [Real.div_rpow (by positivity) hr.le, div_eq_mul_inv,
        ← Real.rpow_neg hr.le ((p₀ - p) / (p₀ - q)),
        ← Real.rpow_mul (by positivity) q ((p₀ - p) / (p₀ - q)),
        Real.mul_rpow (by norm_num) hKq.le]
    ring_nf
  have hB : ((2 * Kp) ^ p₀ / (p₀ - p)) ^ ((p - q) / (p₀ - q))
      = (2:ℝ) ^ (p₀ * (p - q) / (p₀ - q)) * Kp ^ (p₀ * (p - q) / (p₀ - q))
          * (p₀ - p) ^ (-((p - q) / (p₀ - q))) := by
    rw [Real.div_rpow (by positivity) hs.le, div_eq_mul_inv,
        ← Real.rpow_neg hs.le ((p - q) / (p₀ - q)),
        ← Real.rpow_mul (by positivity) p₀ ((p - q) / (p₀ - q)),
        Real.mul_rpow (by norm_num) hKp.le]
    ring_nf
  have hsum : q * (p₀ - p) / (p₀ - q) + p₀ * (p - q) / (p₀ - q) = p := by
    field_simp
    ring
  have ha : q * (p₀ - p) / (p₀ - q) = θ * p := hθ.symm
  have hb : p₀ * (p - q) / (p₀ - q) = (1 - θ) * p := hθ'.symm
  have h2p : (2:ℝ) ^ (q * (p₀ - p) / (p₀ - q)) * (2:ℝ) ^ (p₀ * (p - q) / (p₀ - q))
      = (2:ℝ) ^ p := by
    rw [← Real.rpow_add h2 (q*(p₀-p)/(p₀-q)) (p₀*(p-q)/(p₀-q)), hsum]
  have hneg : (p - q) ^ (-((p₀ - p) / (p₀ - q))) * (p₀ - p) ^ (-((p - q) / (p₀ - q)))
      = ((p - q) ^ ((p₀ - p) / (p₀ - q)) * (p₀ - p) ^ ((p - q) / (p₀ - q)))⁻¹ := by
    rw [Real.rpow_neg hr.le, Real.rpow_neg hs.le, ← mul_inv]
  rw [hA, hB]
  rw [show (2:ℝ) ^ (q * (p₀ - p) / (p₀ - q)) * Kq ^ (q * (p₀ - p) / (p₀ - q))
          * (p - q) ^ (-((p₀ - p) / (p₀ - q)))
        * ((2:ℝ) ^ (p₀ * (p - q) / (p₀ - q)) * Kp ^ (p₀ * (p - q) / (p₀ - q))
            * (p₀ - p) ^ (-((p - q) / (p₀ - q))))
      = ((2:ℝ) ^ (q*(p₀-p)/(p₀-q)) * (2:ℝ) ^ (p₀*(p-q)/(p₀-q))) * Kq ^ (q*(p₀-p)/(p₀-q))
          * Kp ^ (p₀*(p-q)/(p₀-q))
        * ((p - q) ^ (-((p₀ - p) / (p₀ - q))) * (p₀ - p) ^ (-((p - q) / (p₀ - q)))) by ring]
  rw [h2p, ha, hb, hneg]

theorem two_strong_interp_arith
    {q p p₀ θ Kq Kp A B σ : ℝ} (hq : 1 ≤ q) (hqp : q < p) (hpp : p < p₀)
    (hθp : θ * p = q * (p₀ - p) / (p₀ - q))
    (hθp' : (1 - θ) * p = p₀ * (p - q) / (p₀ - q))
    (hKq : 0 < Kq) (hKp : 0 < Kp)
    (hA : A = (2 * Kq) ^ q / (p - q)) (hB : B = (2 * Kp) ^ p₀ / (p₀ - p))
    (hσ : σ = (A / B) ^ (1 / (p₀ - q))) :
    p * (A * σ ^ (-(p - q)) + B * σ ^ (p₀ - p))
      ≤ p * 2 ^ (p + 1) * (1 / (p - q) + 1 / (p₀ - p)) * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p) := by
  have hp0 : 0 < p := by linarith
  have hp₀0 : 0 < p₀ := by linarith
  have hr : 0 < p - q := by linarith
  have hs : 0 < p₀ - p := by linarith
  have hAp : 0 < A := by rw [hA]; positivity
  have hBp : 0 < B := by rw [hB]; positivity
  have hDs : (p - q) + (p₀ - p) = p₀ - q := by ring
  have hbal := balance_identity (A := A) (B := B) (r := p - q) (s := p₀ - p) hAp hBp hr hs
  rw [hDs] at hbal
  rw [← hσ] at hbal
  have hbal' : A * σ ^ (-(p - q)) + B * σ ^ (p₀ - p)
      = 2 * (A ^ ((p₀ - p) / (p₀ - q)) * B ^ ((p - q) / (p₀ - q))) := by
    rw [hbal]; ring
  have hdec := AB_decomp hKq hKp hr hs hθp hθp'
  rw [← hA, ← hB] at hdec
  have hinv := inv_rpow_geom_le hr hs
  rw [hDs] at hinv
  have hpos : (0:ℝ) ≤ (2:ℝ) ^ p * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p) := by positivity
  have hcore : A ^ ((p₀ - p) / (p₀ - q)) * B ^ ((p - q) / (p₀ - q))
      ≤ (2:ℝ) ^ p * (1 / (p - q) + 1 / (p₀ - p)) * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p) := by
    calc A ^ ((p₀ - p) / (p₀ - q)) * B ^ ((p - q) / (p₀ - q))
        = (2:ℝ) ^ p * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p)
            * ((p - q) ^ ((p₀ - p) / (p₀ - q)) * (p₀ - p) ^ ((p - q) / (p₀ - q)))⁻¹ := hdec
      _ ≤ (2:ℝ) ^ p * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p)
            * (1 / (p - q) + 1 / (p₀ - p)) := mul_le_mul_of_nonneg_left hinv hpos
      _ = (2:ℝ) ^ p * (1 / (p - q) + 1 / (p₀ - p)) * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p) := by
            ring
  have hcore2 : 2 * (A ^ ((p₀ - p) / (p₀ - q)) * B ^ ((p - q) / (p₀ - q)))
      ≤ 2 * ((2:ℝ) ^ p * (1 / (p - q) + 1 / (p₀ - p)) * Kq ^ (θ * p)
              * Kp ^ ((1 - θ) * p)) :=
    mul_le_mul_of_nonneg_left hcore (by norm_num)
  have h2p1 : (2:ℝ) * (2:ℝ) ^ p = (2:ℝ) ^ (p + 1) := by
    rw [add_comm p 1, Real.rpow_add (by norm_num : (0:ℝ) < 2) 1 p, Real.rpow_one]
  have hmain : A * σ ^ (-(p - q)) + B * σ ^ (p₀ - p)
      ≤ (2:ℝ) ^ (p + 1) * (1 / (p - q) + 1 / (p₀ - p)) * Kq ^ (θ * p)
          * Kp ^ ((1 - θ) * p) := by
    calc A * σ ^ (-(p - q)) + B * σ ^ (p₀ - p)
        = 2 * (A ^ ((p₀ - p) / (p₀ - q)) * B ^ ((p - q) / (p₀ - q))) := hbal'
      _ ≤ 2 * ((2:ℝ) ^ p * (1 / (p - q) + 1 / (p₀ - p)) * Kq ^ (θ * p)
                * Kp ^ ((1 - θ) * p)) := hcore2
      _ = (2:ℝ) ^ (p + 1) * (1 / (p - q) + 1 / (p₀ - p)) * Kq ^ (θ * p)
            * Kp ^ ((1 - θ) * p) := by
            rw [← h2p1]; ring
  calc p * (A * σ ^ (-(p - q)) + B * σ ^ (p₀ - p))
      ≤ p * ((2:ℝ) ^ (p + 1) * (1 / (p - q) + 1 / (p₀ - p)) * Kq ^ (θ * p)
              * Kp ^ ((1 - θ) * p)) :=
        mul_le_mul_of_nonneg_left hmain (le_of_lt hp0)
    _ = p * 2 ^ (p + 1) * (1 / (p - q) + 1 / (p₀ - p)) * Kq ^ (θ * p) * Kp ^ ((1 - θ) * p) := by
        ring

end Work.BourgainPlan.Maximal
