import Submission.Work.ConeSwitch.MathlibNoHG

/-!
# The threshold arithmetic of the random-partition route to `RelCoverStatement`

This file proves `Work.Deep.Nibble.relcoverMargins`: the (purely numerical) list of
"for large `n`" conditions needed by the random-partition route to the family nibble's
interface `Work.Deep.Nibble.RelCoverStatement`.

The mathematical content is that every one of the five conditions is implied by
`n` being large enough that `n^{1/100}` (resp. `n^{1/2000}`) dominates a fixed power of
`log n` and of `1/κ`, `1/D₀`.  The workhorse is the elementary bound
`a * log x ≤ x ^ a` for `a > 0`, `x ≥ 1` (`mul_log_le_rpow`), which yields the
domination lemma `log_pow_lt_rpow`: for every `c`, `b > 0` and `k`, eventually
`c * (log x)^k < x^b`.  The remaining thresholds are then explicit constants
(`rcM`, `rcCL`, `rcC1`, `rcC2`, `rcCm`, `rcC45` below).
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.Deep.Nibble

/-- **The basic log bound.**  For `a > 0` and `x ≥ 1`, `a * log x ≤ x ^ a`.
(Proved from `Real.log_le_sub_one_of_pos` and `Real.log_rpow`.) -/
theorem mul_log_le_rpow {a x : ℝ} (_ha : 0 < a) (hx : 1 ≤ x) : a * Real.log x ≤ x ^ a := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have h1 : Real.log (x ^ a) ≤ x ^ a - 1 :=
    Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 a)
  calc a * Real.log x = Real.log (x ^ a) := (Real.log_rpow hx0 a).symm
    _ ≤ x ^ a := le_trans h1 (sub_le_self _ (by norm_num))

/-- **Log powers are dominated by every positive power.**  For every real `c`, every
`b > 0` and every `k : ℕ` there is a threshold `N ≥ 1` such that `c * (log x)^k < x ^ b`
for all `x ≥ N`.

Proof: if `c ≤ 0` this is immediate from `1 ≤ x`.  Otherwise put `e := b/(k+1) > 0` and
`C := c * e^{-k}`; for `x ≥ max 1 (C+1)^{1/e}` one has `C < x ^ e`, and
`log x ≤ x ^ e / e` (from `mul_log_le_rpow`), so
`c (log x)^k ≤ c e^{-k} x^{e k} = C x^{e k} < x ^ e x^{e k} = x ^ {e (k+1)} = x ^ b`. -/
theorem log_pow_lt_rpow {c b : ℝ} (hb : 0 < b) (k : ℕ) :
    ∃ N : ℝ, 1 ≤ N ∧ ∀ x : ℝ, N ≤ x → c * (Real.log x) ^ k < x ^ b := by
  by_cases hc : c ≤ 0
  · refine ⟨1, le_rfl, fun x hx => ?_⟩
    have hx1 : 1 ≤ x := hx
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hlog : 0 ≤ Real.log x := Real.log_nonneg hx1
    have : c * (Real.log x) ^ k ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hc (pow_nonneg hlog k)
    exact lt_of_le_of_lt this (Real.rpow_pos_of_pos hx0 b)
  · push Not at hc
    set e : ℝ := b / ((k : ℝ) + 1) with hedef
    have he : 0 < e := div_pos hb (by positivity)
    set C : ℝ := c * (1 / e) ^ k with hCdef
    have hCpos : 0 < C := by
      rw [hCdef]; exact mul_pos hc (pow_pos (by positivity) k)
    refine ⟨max 1 ((C + 1) ^ (1 / e)), le_max_left _ _, fun x hx => ?_⟩
    have hx1 : 1 ≤ x := le_trans (le_max_left _ _) hx
    have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
    have hCx : C + 1 ≤ x ^ e := by
      have h1 : (C + 1) ^ (1 / e) ≤ x := le_trans (le_max_right _ _) hx
      have h2 : ((C + 1) ^ (1 / e)) ^ e ≤ x ^ e :=
        Real.rpow_le_rpow (by positivity) h1 he.le
      have h3 : ((C + 1) ^ (1 / e)) ^ e = C + 1 := by
        rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ C + 1),
          show (1 / e) * e = 1 by field_simp, Real.rpow_one]
      rwa [h3] at h2
    have hlogx : Real.log x ≤ x ^ e / e := by
      have h := mul_log_le_rpow he hx1
      rw [le_div_iff₀ he]
      linarith
    have hstep1 : c * (Real.log x) ^ k ≤ C * x ^ (e * k) := by
      have h1 : (Real.log x) ^ k ≤ (x ^ e / e) ^ k :=
        pow_le_pow_left₀ (Real.log_nonneg hx1) hlogx k
      have h2 : c * (Real.log x) ^ k ≤ c * (x ^ e / e) ^ k :=
        mul_le_mul_of_nonneg_left h1 hc.le
      have h3 : (x ^ e / e) ^ k = (1 / e) ^ k * (x ^ e) ^ k := by
        rw [div_eq_mul_inv, mul_pow]; ring
      have h4 : (x ^ e) ^ k = x ^ (e * k) := by
        rw [← Real.rpow_natCast (x ^ e) k, ← Real.rpow_mul hx0.le e (k : ℝ)]
      calc c * (Real.log x) ^ k ≤ c * (x ^ e / e) ^ k := h2
        _ = c * ((1 / e) ^ k * (x ^ e) ^ k) := by rw [h3]
        _ = c * ((1 / e) ^ k * x ^ (e * k)) := by rw [h4]
        _ = C * x ^ (e * k) := by rw [hCdef]; ring
    have hstep2 : C * x ^ (e * k) < x ^ b := by
      have hCx' : C < x ^ e := lt_of_lt_of_le (lt_add_one C) hCx
      calc C * x ^ (e * k) < x ^ e * x ^ (e * k) :=
            mul_lt_mul_of_pos_right hCx' (Real.rpow_pos_of_pos hx0 _)
        _ = x ^ (e + e * k) := (Real.rpow_add hx0 e (e * k)).symm
        _ = x ^ b := by
            congr 1
            rw [hedef]
            have hk1 : (((k : ℝ) + 1)) ≠ 0 := by positivity
            field_simp
            ring
    exact lt_of_le_of_lt hstep1 hstep2

/-- The factor `M = (66/κ²)^{r-1}` bounding `p^{r-1}` in terms of `log n`. -/
noncomputable def rcM (r : ℕ) (κ : ℝ) : ℝ := (66 / κ ^ 2) ^ (r - 1)

/-- The constant `log 4 + 1 + 66/κ²` bounding `log (4 n p) / (log n)²`. -/
noncomputable def rcCL (κ : ℝ) : ℝ := Real.log 4 + 1 + 66 / κ ^ 2

/-- The threshold constant for condition 1: it suffices that
`rcC1 * (log n)^{2r} < n^{1/100}`. -/
noncomputable def rcC1 (r : ℕ) (κ : ℝ) : ℝ :=
  rcCL κ * rcM r κ / ((3 / 8) * (κ / 100) ^ 2 * (1 - κ))

/-- The constant `log 4 + 2 + 66/κ²` bounding `log (4 |𝓕| p) / (log n)²`. -/
noncomputable def rcCL2 (κ : ℝ) : ℝ := Real.log 4 + 2 + 66 / κ ^ 2

/-- The threshold constant for condition 2: it suffices that
`rcC2 * (log n)^4 < n^{1/2000}`. -/
noncomputable def rcC2 (κ : ℝ) : ℝ := (8 / 3) * rcCL2 κ * 66 / κ ^ 2

/-- The left-hand coefficient `(1-2.5κ)(1+κ/4)(1+κ/100)(1+κ)` of condition 4. -/
noncomputable def rcA (κ : ℝ) : ℝ := (1 - 2.5 * κ) * (1 + κ / 4) * (1 + κ / 100) * (1 + κ)

/-- The right-hand coefficient `(1-κ/100)(1-κ)` of conditions 4 and 5. -/
noncomputable def rcB (κ : ℝ) : ℝ := (1 - κ / 100) * (1 - κ)

/-- The lower bound on `μ = D/p^{r-1}` required by conditions 4 and 5. -/
noncomputable def rcCm (κ D₀ : ℝ) : ℝ :=
  max ((1 - 2.5 * κ) / (rcB κ - rcA κ)) (max ((D₀ + 1) / rcB κ) (1 / (1 - κ)))

/-- The threshold constant for conditions 4 and 5: it suffices that
`rcC45 * (log n)^{2(r-1)} ≤ n^{1/100}`. -/
noncomputable def rcC45 (r : ℕ) (κ D₀ : ℝ) : ℝ := rcCm κ D₀ * rcM r κ

/-- `log (a * b) ≤ log a + log b` for `a ≥ 0` and `b ≥ 1` (the degenerate case `a = 0`
is where `1 ≤ b` is used). -/
theorem log_mul_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 1 ≤ b) :
    Real.log (a * b) ≤ Real.log a + Real.log b := by
  rcases eq_or_lt_of_le ha with ha0 | ha0
  · rw [← ha0, zero_mul, Real.log_zero]
    have hb0 : 0 ≤ Real.log b := Real.log_nonneg hb
    linarith
  · rw [Real.log_mul (ne_of_gt ha0) (ne_of_gt (lt_of_lt_of_le zero_lt_one hb))]

/-- `log X ≤ 2 (log m)²` when `X ≤ m^{2 log m}` (with `m ≥ 1`, `X ≥ 0`). -/
theorem log_le_two_log_sq {m : ℕ} {X : ℝ} (hXnn : 0 ≤ X) (hm : 1 ≤ (m : ℝ))
    (hX : X ≤ (m : ℝ) ^ (2 * Real.log (m : ℝ))) :
    Real.log X ≤ 2 * (Real.log (m : ℝ)) ^ 2 := by
  have hmpos : 0 < (m : ℝ) := lt_of_lt_of_le zero_lt_one hm
  by_cases hX0 : X = 0
  · rw [hX0, Real.log_zero]
    positivity
  · have hXpos : 0 < X := lt_of_le_of_ne hXnn (Ne.symm hX0)
    have h1 := Real.log_le_log hXpos hX
    rw [Real.log_rpow hmpos] at h1
    have h2 : (2 * Real.log (m : ℝ)) * Real.log (m : ℝ) = 2 * (Real.log (m : ℝ)) ^ 2 := by ring
    linarith [h1, h2]

/-- `log (c * X) ≤ log c + 2 (log m)²` for `c ≥ 1` and `X ≤ m^{2 log m}`. -/
theorem log_const_mul_le {m : ℕ} {c X : ℝ} (hc : 1 ≤ c) (hXnn : 0 ≤ X) (hm : 1 ≤ (m : ℝ))
    (hX : X ≤ (m : ℝ) ^ (2 * Real.log (m : ℝ))) :
    Real.log (c * X) ≤ Real.log c + 2 * (Real.log (m : ℝ)) ^ 2 := by
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  by_cases hX0 : X = 0
  · rw [hX0, mul_zero, Real.log_zero]
    have hc1 : 0 ≤ Real.log c := Real.log_nonneg hc
    positivity
  · have hXpos : 0 < X := lt_of_le_of_ne hXnn (Ne.symm hX0)
    rw [Real.log_mul (ne_of_gt hc0) (ne_of_gt hXpos)]
    have h2 := log_le_two_log_sq hXnn hm hX
    linarith

/-- **The five numerical conditions, reduced to three explicit domination hypotheses.**

Assume `1 ≤ n`, `1 ≤ log n`, the window `32 (log n)²/κ² ≤ p ≤ 33((log n)²/κ² + 1)`,
`n^{1/100} ≤ D`, `|𝓕| ≤ n^{2 log n}`, and the three threshold conditions
`rcC1 (log n)^{2r} < n^{1/100}`, `rcC2 (log n)^4 < n^{1/2000}`,
`rcC45 (log n)^{2(r-1)} ≤ n^{1/100}`.  Then all five conditions of `relcoverMargins`
hold. -/
theorem relcover_aux {r : ℕ} (hr : 2 ≤ r) {κ : ℝ} (hκ0 : 0 < κ) (hκ4 : κ < 1 / 4)
    {D₀ : ℝ} (_hD₀ : 0 < D₀) {n p : ℕ} {D : ℝ} {𝓕 : Set (Set (Fin n))}
    (hn1 : (1 : ℝ) ≤ (n : ℝ)) (hL1 : 1 ≤ Real.log (n : ℝ))
    (hp2 : 2 ≤ p)
    (hplo : 32 * (Real.log (n : ℝ)) ^ 2 / κ ^ 2 ≤ (p : ℝ))
    (hphi : (p : ℝ) ≤ 33 * ((Real.log (n : ℝ)) ^ 2 / κ ^ 2 + 1))
    (hD : (n : ℝ) ^ ((1 : ℝ) / 100) ≤ D)
    (hF : (𝓕.ncard : ℝ) ≤ (n : ℝ) ^ (2 * Real.log (n : ℝ)))
    (hbig1 : rcC1 r κ * (Real.log (n : ℝ)) ^ (2 * r) < (n : ℝ) ^ ((1 : ℝ) / 100))
    (hbig2 : rcC2 κ * (Real.log (n : ℝ)) ^ 4 < (n : ℝ) ^ ((1 : ℝ) / 2000))
    (hbig45 : rcC45 r κ D₀ * (Real.log (n : ℝ)) ^ (2 * (r - 1))
        ≤ (n : ℝ) ^ ((1 : ℝ) / 100)) :
    (Real.log (4 * (n : ℝ) * (p : ℝ))
          < 3 * (κ / 100) ^ 2 * ((1 - κ) * D / (p : ℝ) ^ (r - 1)) / 8
        ∧ (∀ S ∈ 𝓕, D ^ ((1 : ℝ) / 20) ≤ (S.ncard : ℝ) →
              (8 / 3) * Real.log (4 * (𝓕.ncard : ℝ) * (p : ℝ)) < (S.ncard : ℝ) / (p : ℝ))
        ∧ Real.log (2 * (𝓕.ncard : ℝ)) < κ ^ 2 * (p : ℝ) / 4
        ∧ (1 - 2.5 * κ) * ((1 + κ / 4) * (1 + κ / 100) * (1 + κ) * (D / (p : ℝ) ^ (r - 1)) + 1)
            ≤ (1 - κ / 100) * (1 - κ) * (D / (p : ℝ) ^ (r - 1))
        ∧ D₀ + 1 ≤ (1 - κ / 100) * (1 - κ) * (D / (p : ℝ) ^ (r - 1))
        ∧ 1 ≤ (1 - κ) * D / (p : ℝ) ^ (r - 1)) := by
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hLpos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le zero_lt_one hL1
  have hLnn : 0 ≤ Real.log (n : ℝ) := hLpos.le
  have hL2 : 1 ≤ (Real.log (n : ℝ)) ^ 2 := by nlinarith [hL1]
  have hP2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hPpos : 0 < (p : ℝ) := lt_of_lt_of_le (by norm_num) hP2
  have hDpos : 0 < D := lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hD
  have hκ1 : κ < 1 := by linarith
  have hκ2pos : 0 < κ ^ 2 := pow_pos hκ0 2
  have h1mκ : 0 < 1 - κ := by linarith
  have hBpos : 0 < rcB κ := by
    rw [rcB]; exact mul_pos (by linarith) h1mκ
  have hBApos : 0 < rcB κ - rcA κ := by
    rw [rcB, rcA]
    have hfac : (1 - κ/100)*(1-κ) - (1 - 2.5*κ)*(1+κ/4)*(1+κ/100)*(1+κ)
        = κ * (23/100 + (1159/400)*κ + (523/800)*κ^2 + (1/160)*κ^3) := by ring
    rw [hfac]
    exact mul_pos hκ0 (by positivity)
  have hcmpos : 0 < rcCm κ D₀ := by
    rw [rcCm]
    exact lt_max_of_lt_left (div_pos (by linarith) hBApos)
  have h66 : 1 < 66 / κ ^ 2 := by
    rw [lt_div_iff₀ hκ2pos]
    nlinarith [hκ0, hκ4]
  have hMpos : 0 < rcM r κ := by rw [rcM]; positivity
  have hM1 : 1 ≤ rcM r κ := by
    rw [rcM]
    simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (le_of_lt h66) (r - 1)
  have hL2div : 1 ≤ (Real.log (n : ℝ)) ^ 2 / κ ^ 2 := by
    rw [one_le_div hκ2pos]
    nlinarith [hL2, hκ0, hκ4]
  have hP66' : (p : ℝ) ≤ (66 / κ ^ 2) * (Real.log (n : ℝ)) ^ 2 := by
    have h2 : (Real.log (n:ℝ))^2/κ^2 + 1 ≤ 2 * ((Real.log (n:ℝ))^2/κ^2) := by linarith
    calc (p:ℝ) ≤ 33 * ((Real.log (n:ℝ))^2/κ^2 + 1) := hphi
      _ ≤ 33 * (2 * ((Real.log (n:ℝ))^2/κ^2)) := by linarith
      _ = (66/κ^2) * (Real.log (n:ℝ))^2 := by ring
  have hPpow : (p : ℝ) ^ (r - 1) ≤ rcM r κ * (Real.log (n : ℝ)) ^ (2 * (r - 1)) := by
    have h1 : (p : ℝ) ^ (r - 1) ≤ ((66 / κ ^ 2) * (Real.log (n : ℝ)) ^ 2) ^ (r - 1) :=
      pow_le_pow_left₀ hPpos.le hP66' (r - 1)
    have h2 : ((66 / κ ^ 2) * (Real.log (n : ℝ)) ^ 2) ^ (r - 1)
        = rcM r κ * (Real.log (n : ℝ)) ^ (2 * (r - 1)) := by
      rw [mul_pow, rcM, pow_mul]
    rw [h2] at h1
    exact h1
  have hμlow : (n : ℝ) ^ ((1 : ℝ) / 100) / (rcM r κ * (Real.log (n : ℝ)) ^ (2 * (r - 1)))
      ≤ D / (p : ℝ) ^ (r - 1) := by
    have hPpw : 0 < (p : ℝ) ^ (r - 1) := pow_pos hPpos _
    exact le_trans (div_le_div_of_nonneg_left (Real.rpow_nonneg hnpos.le _) hPpw hPpow)
      (div_le_div_of_nonneg_right hD hPpw.le)
  have hμCm : rcCm κ D₀ ≤ D / (p : ℝ) ^ (r - 1) := by
    have hML : 0 < rcM r κ * (Real.log (n : ℝ)) ^ (2 * (r - 1)) :=
      mul_pos hMpos (pow_pos hLpos _)
    have h1 : rcCm κ D₀ ≤
        (n : ℝ) ^ ((1 : ℝ) / 100) / (rcM r κ * (Real.log (n : ℝ)) ^ (2 * (r - 1))) := by
      rw [le_div_iff₀ hML]
      calc rcCm κ D₀ * (rcM r κ * (Real.log (n : ℝ)) ^ (2 * (r - 1)))
          = rcC45 r κ D₀ * (Real.log (n : ℝ)) ^ (2 * (r - 1)) := by rw [rcC45]; ring
        _ ≤ (n : ℝ) ^ ((1 : ℝ) / 100) := hbig45
    exact le_trans h1 hμlow
  have hcond4 : (1 - 2.5*κ) * ((1 + κ/4)*(1 + κ/100)*(1 + κ)*(D/(p:ℝ)^(r-1)) + 1)
      ≤ (1 - κ/100)*(1 - κ)*(D/(p:ℝ)^(r-1)) := by
    have hne : rcB κ - rcA κ ≠ 0 := ne_of_gt hBApos
    have h1 : 1 - 2.5*κ ≤ (rcB κ - rcA κ) * rcCm κ D₀ := by
      have hm : ((1 - 2.5*κ)/(rcB κ - rcA κ)) ≤ rcCm κ D₀ := by
        rw [rcCm]; exact le_max_left _ _
      have heq : (rcB κ - rcA κ) * ((1 - 2.5*κ)/(rcB κ - rcA κ)) = 1 - 2.5*κ := by
        rw [mul_comm]; exact div_mul_cancel₀ _ hne
      rw [← heq]
      exact mul_le_mul_of_nonneg_left hm hBApos.le
    have h3 : (rcB κ - rcA κ) * rcCm κ D₀ ≤ (rcB κ - rcA κ) * (D/(p:ℝ)^(r-1)) :=
      mul_le_mul_of_nonneg_left hμCm hBApos.le
    have h2 : rcA κ * (D/(p:ℝ)^(r-1)) + (1 - 2.5*κ) ≤ rcB κ * (D/(p:ℝ)^(r-1)) := by
      nlinarith [h1, h3]
    calc (1 - 2.5*κ) * ((1 + κ/4)*(1 + κ/100)*(1 + κ)*(D/(p:ℝ)^(r-1)) + 1)
        = rcA κ * (D/(p:ℝ)^(r-1)) + (1 - 2.5*κ) := by rw [rcA]; ring
      _ ≤ rcB κ * (D/(p:ℝ)^(r-1)) := h2
      _ = (1 - κ/100)*(1 - κ)*(D/(p:ℝ)^(r-1)) := rfl
  have hcond5a : D₀ + 1 ≤ (1 - κ/100)*(1 - κ)*(D/(p:ℝ)^(r-1)) := by
    change D₀ + 1 ≤ rcB κ * (D/(p:ℝ)^(r-1))
    have hm : ((D₀ + 1)/rcB κ) ≤ rcCm κ D₀ := by
      rw [rcCm]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have heq : rcB κ * ((D₀ + 1)/rcB κ) = D₀ + 1 := by
      rw [mul_comm]; exact div_mul_cancel₀ _ (ne_of_gt hBpos)
    rw [← heq]
    exact mul_le_mul_of_nonneg_left (le_trans hm hμCm) hBpos.le
  have hcond5b : 1 ≤ (1 - κ) * D / (p:ℝ)^(r-1) := by
    have hm : (1/(1-κ)) ≤ rcCm κ D₀ := by
      rw [rcCm]; exact le_trans (le_max_right _ _) (le_max_right _ _)
    have heq : (1 - κ) * (1/(1-κ)) = 1 := mul_one_div_cancel (ne_of_gt h1mκ)
    have hstep : 1 ≤ (1-κ)*(D/(p:ℝ)^(r-1)) := by
      calc (1:ℝ) = (1-κ)*(1/(1-κ)) := heq.symm
        _ ≤ (1-κ) * rcCm κ D₀ := mul_le_mul_of_nonneg_left hm h1mκ.le
        _ ≤ (1-κ) * (D/(p:ℝ)^(r-1)) := mul_le_mul_of_nonneg_left hμCm h1mκ.le
    calc (1:ℝ) ≤ (1-κ)*(D/(p:ℝ)^(r-1)) := hstep
      _ = (1-κ)*D/(p:ℝ)^(r-1) := by ring
  have hlog4nP : Real.log (4 * (n:ℝ) * (p:ℝ)) ≤ rcCL κ * (Real.log (n:ℝ))^2 := by
    have hsplit : Real.log (4 * (n:ℝ) * (p:ℝ))
        = Real.log 4 + Real.log (n:ℝ) + Real.log (p:ℝ) := by
      rw [show (4:ℝ) * (n:ℝ) * (p:ℝ) = 4 * ((n:ℝ) * (p:ℝ)) by ring]
      rw [Real.log_mul (by norm_num) (mul_ne_zero (ne_of_gt hnpos) (ne_of_gt hPpos))]
      rw [Real.log_mul (ne_of_gt hnpos) (ne_of_gt hPpos)]
      ring
    rw [hsplit]
    have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
    have h1 : Real.log 4 ≤ Real.log 4 * (Real.log (n:ℝ))^2 := by nlinarith [hL2, hl4]
    have h2 : Real.log (n:ℝ) ≤ (Real.log (n:ℝ))^2 := by nlinarith [hL1]
    have h3 : Real.log (p:ℝ) ≤ (66/κ^2) * (Real.log (n:ℝ))^2 := by
      have hl : Real.log (p:ℝ) ≤ (p:ℝ) - 1 := Real.log_le_sub_one_of_pos hPpos
      linarith [hl, hP66']
    have h4 : Real.log 4 * (Real.log (n:ℝ))^2 + (Real.log (n:ℝ))^2
        + (66/κ^2) * (Real.log (n:ℝ))^2 = rcCL κ * (Real.log (n:ℝ))^2 := by
      rw [rcCL]; ring
    linarith [h1, h2, h3, h4]
  have hpowadd : (Real.log (n:ℝ))^2 * (Real.log (n:ℝ))^(2*(r-1))
      = (Real.log (n:ℝ))^(2*r) := by
    rw [← pow_add]
    congr 1
    omega
  have hcond1 : Real.log (4 * (n:ℝ) * (p:ℝ))
      < 3 * (κ/100)^2 * ((1-κ)*D/(p:ℝ)^(r-1)) / 8 := by
    have hcL : 0 < (3/8)*(κ/100)^2*(1-κ) := by
      have h : 0 < 1 - κ := by linarith
      positivity
    have hstep : rcCL κ * rcM r κ * (Real.log (n:ℝ))^(2*r)
        < ((3/8)*(κ/100)^2*(1-κ)) * (n:ℝ)^((1:ℝ)/100) := by
      have hrc1 : rcC1 r κ * ((3/8)*(κ/100)^2*(1-κ)) = rcCL κ * rcM r κ := by
        rw [rcC1]; field_simp
      calc rcCL κ * rcM r κ * (Real.log (n:ℝ))^(2*r)
          = (rcC1 r κ * (Real.log (n:ℝ))^(2*r)) * ((3/8)*(κ/100)^2*(1-κ)) := by
            rw [← hrc1]; ring
        _ < (n:ℝ)^((1:ℝ)/100) * ((3/8)*(κ/100)^2*(1-κ)) :=
            mul_lt_mul_of_pos_right hbig1 hcL
        _ = ((3/8)*(κ/100)^2*(1-κ)) * (n:ℝ)^((1:ℝ)/100) := by ring
    have hgoal : rcCL κ * (Real.log (n:ℝ))^2
        < ((3/8)*(κ/100)^2*(1-κ))
            * ((n:ℝ)^((1:ℝ)/100) / (rcM r κ * (Real.log (n:ℝ))^(2*(r-1)))) := by
      rw [← mul_div_assoc, lt_div_iff₀ (mul_pos hMpos (pow_pos hLpos _))]
      calc rcCL κ * (Real.log (n:ℝ))^2 * (rcM r κ * (Real.log (n:ℝ))^(2*(r-1)))
          = rcCL κ * rcM r κ
              * ((Real.log (n:ℝ))^2 * (Real.log (n:ℝ))^(2*(r-1))) := by ring
        _ = rcCL κ * rcM r κ * (Real.log (n:ℝ))^(2*r) := by rw [hpowadd]
        _ < ((3/8)*(κ/100)^2*(1-κ)) * (n:ℝ)^((1:ℝ)/100) := hstep
    have hmain : Real.log (4 * (n:ℝ) * (p:ℝ))
        < ((3/8)*(κ/100)^2*(1-κ)) * (D/(p:ℝ)^(r-1)) := by
      calc Real.log (4 * (n:ℝ) * (p:ℝ)) ≤ rcCL κ * (Real.log (n:ℝ))^2 := hlog4nP
        _ < ((3/8)*(κ/100)^2*(1-κ))
              * ((n:ℝ)^((1:ℝ)/100) / (rcM r κ * (Real.log (n:ℝ))^(2*(r-1)))) := hgoal
        _ ≤ ((3/8)*(κ/100)^2*(1-κ)) * (D/(p:ℝ)^(r-1)) :=
            mul_le_mul_of_nonneg_left hμlow hcL.le
    have heq : ((3/8)*(κ/100)^2*(1-κ)) * (D/(p:ℝ)^(r-1))
        = 3 * (κ/100)^2 * ((1-κ)*D/(p:ℝ)^(r-1)) / 8 := by ring
    linarith [hmain, heq.le, heq.ge]
  have hlog4XP : Real.log (4 * (𝓕.ncard:ℝ) * (p:ℝ)) ≤ rcCL2 κ * (Real.log (n:ℝ))^2 := by
    have hXnn : 0 ≤ (𝓕.ncard:ℝ) := Nat.cast_nonneg _
    have h1 : Real.log (4 * (𝓕.ncard:ℝ)) ≤ Real.log 4 + 2*(Real.log (n:ℝ))^2 :=
      log_const_mul_le (by norm_num : (1:ℝ) ≤ 4) hXnn hn1 hF
    have h2 : Real.log (4 * (𝓕.ncard:ℝ) * (p:ℝ))
        ≤ Real.log (4 * (𝓕.ncard:ℝ)) + Real.log (p:ℝ) :=
      log_mul_le' (a := 4 * (𝓕.ncard:ℝ)) (b := (p:ℝ)) (by positivity)
        (le_trans (by norm_num : (1:ℝ) ≤ 2) hP2)
    have h3 : Real.log (p:ℝ) ≤ (66/κ^2)*(Real.log (n:ℝ))^2 := by
      have hl : Real.log (p:ℝ) ≤ (p:ℝ) - 1 := Real.log_le_sub_one_of_pos hPpos
      linarith [hl, hP66']
    have h5 : Real.log 4 ≤ Real.log 4 * (Real.log (n:ℝ))^2 := by
      have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
      nlinarith [hL2, hl4]
    have h4 : Real.log 4 * (Real.log (n:ℝ))^2 + 2*(Real.log (n:ℝ))^2
        + (66/κ^2)*(Real.log (n:ℝ))^2 = rcCL2 κ * (Real.log (n:ℝ))^2 := by
      rw [rcCL2]; ring
    linarith [h1, h2, h3, h4, h5]
  have hcond2 : ∀ S ∈ 𝓕, D ^ ((1:ℝ)/20) ≤ (S.ncard:ℝ) →
      (8/3) * Real.log (4 * (𝓕.ncard:ℝ) * (p:ℝ)) < (S.ncard:ℝ)/(p:ℝ) := by
    intro S hS hSbig
    have hDp : (n:ℝ)^((1:ℝ)/2000) ≤ D^((1:ℝ)/20) := by
      have h0 : ((n:ℝ)^((1:ℝ)/100))^((1:ℝ)/20) ≤ D^((1:ℝ)/20) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hnpos.le _) hD (by norm_num)
      have h1 : ((n:ℝ)^((1:ℝ)/100))^((1:ℝ)/20) = (n:ℝ)^((1:ℝ)/2000) := by
        rw [← Real.rpow_mul hnpos.le, show (1:ℝ)/100 * ((1:ℝ)/20) = (1:ℝ)/2000 by norm_num]
      rwa [h1] at h0
    have hmid : (8/3) * rcCL2 κ * (Real.log (n:ℝ))^2
        < (n:ℝ)^((1:ℝ)/2000) * (1/((66/κ^2)*(Real.log (n:ℝ))^2)) := by
      rw [← div_eq_mul_one_div,
        lt_div_iff₀ (by positivity : 0 < (66/κ^2)*(Real.log (n:ℝ))^2)]
      have hfac : (8/3) * rcCL2 κ * (Real.log (n:ℝ))^2 * ((66/κ^2)*(Real.log (n:ℝ))^2)
          = rcC2 κ * (Real.log (n:ℝ))^4 := by rw [rcC2]; ring
      rwa [hfac]
    have hmid2 : (n:ℝ)^((1:ℝ)/2000) * (1/((66/κ^2)*(Real.log (n:ℝ))^2))
        ≤ (S.ncard:ℝ)/(p:ℝ) := by
      have h2 : (1:ℝ)/((66/κ^2)*(Real.log (n:ℝ))^2) ≤ 1/(p:ℝ) :=
        one_div_le_one_div_of_le hPpos hP66'
      have h3 : (n:ℝ)^((1:ℝ)/2000) * (1/((66/κ^2)*(Real.log (n:ℝ))^2))
          ≤ (n:ℝ)^((1:ℝ)/2000) * (1/(p:ℝ)) :=
        mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hnpos.le _)
      have h4 : (n:ℝ)^((1:ℝ)/2000) * (1/(p:ℝ)) ≤ D^((1:ℝ)/20) * (1/(p:ℝ)) :=
        mul_le_mul_of_nonneg_right hDp (by positivity)
      have h5 : D^((1:ℝ)/20) * (1/(p:ℝ)) ≤ (S.ncard:ℝ) * (1/(p:ℝ)) :=
        mul_le_mul_of_nonneg_right hSbig (by positivity)
      have h6 : (S.ncard:ℝ) * (1/(p:ℝ)) = (S.ncard:ℝ)/(p:ℝ) := by rw [mul_one_div]
      linarith [h3, h4, h5, h6]
    calc (8/3) * Real.log (4 * (𝓕.ncard:ℝ) * (p:ℝ))
        ≤ (8/3) * (rcCL2 κ * (Real.log (n:ℝ))^2) :=
          mul_le_mul_of_nonneg_left hlog4XP (by norm_num)
      _ = (8/3) * rcCL2 κ * (Real.log (n:ℝ))^2 := by ring
      _ < (n:ℝ)^((1:ℝ)/2000) * (1/((66/κ^2)*(Real.log (n:ℝ))^2)) := hmid
      _ ≤ (S.ncard:ℝ)/(p:ℝ) := hmid2
  have hcond3 : Real.log (2 * (𝓕.ncard:ℝ)) < κ^2 * (p:ℝ)/4 := by
    have hXnn : 0 ≤ (𝓕.ncard:ℝ) := Nat.cast_nonneg _
    have h1 : Real.log (2 * (𝓕.ncard:ℝ)) ≤ Real.log 2 + 2*(Real.log (n:ℝ))^2 :=
      log_const_mul_le (by norm_num) hXnn hn1 hF
    have hlog2 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
      linarith
    have h2 : Real.log 2 + 2*(Real.log (n:ℝ))^2 < 8*(Real.log (n:ℝ))^2 := by
      nlinarith [hlog2, hL2]
    have h3 : 8*(Real.log (n:ℝ))^2 ≤ κ^2 * (p:ℝ)/4 := by
      have h4 : 32 * (Real.log (n:ℝ))^2 ≤ κ^2 * (p:ℝ) := by
        have h := (div_le_iff₀ hκ2pos).mp hplo
        linarith [h]
      linarith [h4]
    linarith [h1, h2, h3]
  exact ⟨hcond1, hcond2, hcond3, hcond4, hcond5a, hcond5b⟩

/-- **The threshold arithmetic of the random-partition route to `RelCoverStatement`.**  For `r ≥ 2`, `κ ∈ (0,1/4)` and `D₀ > 0` there is a threshold `n₀` such that for `n ≥ n₀`, for every number of parts `p` with `2 ≤ p`, `32 (log n)²/κ² ≤ p ≤ 33 ((log n)²/κ² + 1)`, every degree scale `D ≥ n^{1/100}` and every family `𝓕` of at most `n^{2 log n}` subsets of `Fin n`, the following five numerical conditions hold:

1. `log (4 n p) < 3 ε'² μ / 8` where `ε' = κ/100` and `μ = (1-κ)D/p^{r-1}` (the Chernoff budget of the partition step, `partDegCount` at `τ = ε'μ`);
2. `(8/3) log (4 |𝓕| p) < |S|/p` for every `S ∈ 𝓕` with `D^{1/20} ≤ |S|` (the balance budget of `partBalCount` at `k = ⌈2|S|/p⌉`);
3. `log (2 |𝓕|) < κ² p / 4` (the union bound over `𝓕` for the Hoeffding step, whose tail is `2 exp(-κ²p/4)`);
4. `(1-2.5κ) ((1+κ/4)(1+κ/100)(1+κ) D/p^{r-1} + 1) ≤ (1-κ/100)(1-κ) D/p^{r-1}` (the mean inequality `d_i(v)/c_i ≥ 1-2.5κ` in each part);
5. `D₀ + 1 ≤ (1-κ/100)(1-κ) D/p^{r-1}` (Kahn's maximum-degree threshold is met by every induced part) and `1 ≤ (1-κ) D/p^{r-1}`.

Every condition is a lower bound on `n` of the form "`n^{1/100}` beats a fixed power of `log n` and of `1/κ`, `1/D₀`", so a threshold exists; the content of the claim is that the five conditions hold *simultaneously* and *uniformly* in `D ≥ n^{1/100}`, in `p` in the displayed window and in the family `𝓕` (via its `ncard` bound and the minimum size `D^{1/20}` of its members). -/
theorem relcoverMargins {r : ℕ} (hr : 2 ≤ r) {κ : ℝ} (hκ0 : 0 < κ) (hκ4 : κ < 1 / 4)
    {D₀ : ℝ} (hD₀ : 0 < D₀) :
    ∃ n₀ : ℝ, 0 < n₀ ∧ ∀ n : ℕ, n₀ ≤ (n : ℝ) → ∀ p : ℕ, 2 ≤ p →
      (32 * (Real.log (n : ℝ)) ^ 2 / κ ^ 2 ≤ (p : ℝ)) →
      ((p : ℝ) ≤ 33 * ((Real.log (n : ℝ)) ^ 2 / κ ^ 2 + 1)) →
      ∀ D : ℝ, (n : ℝ) ^ ((1 : ℝ) / 100) ≤ D →
      ∀ 𝓕 : Set (Set (Fin n)), (𝓕.ncard : ℝ) ≤ (n : ℝ) ^ (2 * Real.log (n : ℝ)) →
      (Real.log (4 * (n : ℝ) * (p : ℝ))
          < 3 * (κ / 100) ^ 2 * ((1 - κ) * D / (p : ℝ) ^ (r - 1)) / 8
        ∧ (∀ S ∈ 𝓕, D ^ ((1 : ℝ) / 20) ≤ (S.ncard : ℝ) →
              (8 / 3) * Real.log (4 * (𝓕.ncard : ℝ) * (p : ℝ)) < (S.ncard : ℝ) / (p : ℝ))
        ∧ Real.log (2 * (𝓕.ncard : ℝ)) < κ ^ 2 * (p : ℝ) / 4
        ∧ (1 - 2.5 * κ) * ((1 + κ / 4) * (1 + κ / 100) * (1 + κ) * (D / (p : ℝ) ^ (r - 1)) + 1)
            ≤ (1 - κ / 100) * (1 - κ) * (D / (p : ℝ) ^ (r - 1))
        ∧ D₀ + 1 ≤ (1 - κ / 100) * (1 - κ) * (D / (p : ℝ) ^ (r - 1))
        ∧ 1 ≤ (1 - κ) * D / (p : ℝ) ^ (r - 1)) := by
  obtain ⟨N1, _hN1, h1⟩ :=
    log_pow_lt_rpow (c := rcC1 r κ) (b := (1 : ℝ) / 100) (by norm_num) (2 * r)
  obtain ⟨N2, _hN2, h2⟩ :=
    log_pow_lt_rpow (c := rcC2 κ) (b := (1 : ℝ) / 2000) (by norm_num) 4
  obtain ⟨N45, _hN45, h45⟩ :=
    log_pow_lt_rpow (c := rcC45 r κ D₀) (b := (1 : ℝ) / 100) (by norm_num) (2 * (r - 1))
  refine ⟨max (max N1 (max N2 N45)) (Real.exp 1), lt_max_of_lt_right (Real.exp_pos 1), ?_⟩
  intro n hn p hp2 hplo hphi D hD 𝓕 hF
  have hn_exp : Real.exp 1 ≤ (n : ℝ) := le_trans (le_max_right _ _) hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) :=
    le_trans (by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num)) hn_exp
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1
  have hL1 : 1 ≤ Real.log (n : ℝ) := (Real.le_log_iff_exp_le hnpos).mpr hn_exp
  have hA : max N1 (max N2 N45) ≤ (n : ℝ) := le_trans (le_max_left _ _) hn
  have hN1' : N1 ≤ (n : ℝ) := le_trans (le_max_left _ _) hA
  have hB : max N2 N45 ≤ (n : ℝ) := le_trans (le_max_right _ _) hA
  have hN2' : N2 ≤ (n : ℝ) := le_trans (le_max_left _ _) hB
  have hN45' : N45 ≤ (n : ℝ) := le_trans (le_max_right _ _) hB
  exact relcover_aux hr hκ0 hκ4 hD₀ hn1 hL1 hp2 hplo hphi hD hF
    (h1 (n : ℝ) hN1') (h2 (n : ℝ) hN2') (le_of_lt (h45 (n : ℝ) hN45'))

end Work.Deep.Nibble

