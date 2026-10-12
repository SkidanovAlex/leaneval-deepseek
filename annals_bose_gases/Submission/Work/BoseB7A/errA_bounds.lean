import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7A.errA_pre
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.errA_bounds` — the three bracket bounds of the `N1` arithmetic

With the monomial normal form of `errA_pre` (`X = fsXp h.t 1`, `Kl = X^{-3/2}`,
`KL = X^{-21/2}`, `lille = X^{97/2}`, `eta = X^{1236}`) the three error brackets of
FS §10 are sums of powers of `X`, all with exponent larger than the exponent
`325/2` of `controlErrA = E0·X^{325/2}`:

```
e1A = E0·(X^{2566} + X^{227} + X^{365/2}/E.b + X^{1380})   ≤ E0·X^{365/2}·(3 + 1/b₀)
e23A = E0·X^{1283}                                         ≤ E0·X^{365/2}
e4A ≤ (9/4)E0·√2·X^{337/8}·3·X^{549/4} + E0·X^{191}/E.b
    ≤ E0·X^{1435/8}·((27/4)√2 + 1/b₀)
```

(the `b`-denominators use `b₀ ≤ E.b`; `E0 = μ²aℓ³ ≤ E0·X^{20}·X^{325/2}` supplies
the slack in the final assembly).

The three lemmas are exactly the `e1A ≤`, `e23A ≤`, `e4A ≤` inputs of
`Work.BoseB7A.errA_le`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

open Work.BoseB7
open Work.BoseBox

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]

/-- **The `e1A` bracket**: `e1A E ≤ E0·X^{365/2}·(3 + 1/b₀)`.

The four terms have `X`-exponents `2566, 227, 365/2, 1380`, all `≥ 365/2`; the
third carries the `1/E.b ≤ 1/b₀` factor. -/
theorem e1A_le (b₀ : ℝ) (hb₀ : 0 < b₀) (E : Q3Env Mode) (h : FSParamsView E) (hb : b₀ ≤ E.b) :
    e1A E ≤ E0 E * fsXp h.t (365 / 2) * (3 + 1 / b₀) := by
  have h0 : 0 < h.t := h.t_pos
  have h1t : h.t ≤ 1 := h.t_le_one
  have hEb : 0 < E.b := lt_of_lt_of_le hb₀ hb
  have hE00 : 0 ≤ E0 E := errA_E0_nonneg E h
  -- the first term
  have ht1 : dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * eta E ^ 2 ≤ fsXp h.t (365 / 2) := by
    rw [errA_dil E h, errA_Kl E h, errA_KL E h, errA_eta_sq E h]
    rw [fsXp_pow h0.le, fsXp_pow h0.le]
    simp only [fsXp_mul h0]
    exact fsXp_le_fsXp h0 h1t (by norm_num)
  -- the second term
  have ht2 : dil E (1 / 2) * E.KL ^ 3 * E.lille ^ 2 ≤ fsXp h.t (365 / 2) := by
    rw [errA_dil E h, errA_KL E h, errA_lille E h]
    rw [fsXp_pow h0.le, fsXp_pow h0.le]
    simp only [fsXp_mul h0]
    exact fsXp_le_fsXp h0 h1t (by norm_num)
  -- the third term (the only one with the `b`-denominator)
  have ht3 : E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b ≤ fsXp h.t (365 / 2) / b₀ := by
    have hnum : E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 = fsXp h.t (365 / 2) := by
      rw [errA_Kl E h, errA_KL E h, errA_lille E h]
      rw [fsXp_pow h0.le, fsXp_pow h0.le, fsXp_pow h0.le]
      simp only [fsXp_mul h0]
      congr 1
      norm_num
    rw [hnum, div_le_div_iff₀ hEb hb₀]
    exact mul_le_mul_of_nonneg_left hb (fsXp_pos h0).le
  -- the fourth term
  have ht4 : E.Kl ^ (3 / 2 : ℝ) * E.KL ^ 3 * dil E (1 / 4) * E.lille ^ 2 * eta E ≤
      fsXp h.t (365 / 2) := by
    rw [errA_Kl E h, errA_KL E h, errA_lille E h, errA_dil E h, errA_eta E h]
    rw [fsXp_rpow h0.le]
    simp only [fsXp_pow h0.le, fsXp_mul h0]
    exact fsXp_le_fsXp h0 h1t (by norm_num)
  -- combine
  obtain ⟨Z, hZdef, ht3z⟩ : ∃ Z : ℝ, Z = fsXp h.t (365 / 2) / b₀ ∧
      E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b ≤ Z := ⟨_, rfl, ht3⟩
  have hsum : dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * eta E ^ 2 +
      dil E (1 / 2) * E.KL ^ 3 * E.lille ^ 2 +
      E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b +
      E.Kl ^ (3 / 2 : ℝ) * E.KL ^ 3 * dil E (1 / 4) * E.lille ^ 2 * eta E ≤
      3 * fsXp h.t (365 / 2) + Z := by
    linarith [ht1, ht2, ht3z, ht4]
  have hfin : 3 * fsXp h.t (365 / 2) + Z = fsXp h.t (365 / 2) * (3 + 1 / b₀) := by
    rw [hZdef]; ring
  have hsum' : dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * eta E ^ 2 +
      dil E (1 / 2) * E.KL ^ 3 * E.lille ^ 2 +
      E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b +
      E.Kl ^ (3 / 2 : ℝ) * E.KL ^ 3 * dil E (1 / 4) * E.lille ^ 2 * eta E ≤
      fsXp h.t (365 / 2) * (3 + 1 / b₀) := by
    rw [← hfin]; exact hsum
  rw [e1A]
  calc E0 E * (dil E (1 / 2) * E.Kl ^ 3 * E.KL ^ 6 * eta E ^ 2 +
        dil E (1 / 2) * E.KL ^ 3 * E.lille ^ 2 +
        E.Kl ^ 5 * E.KL ^ 5 * E.lille ^ 5 / E.b +
        E.Kl ^ (3 / 2 : ℝ) * E.KL ^ 3 * dil E (1 / 4) * E.lille ^ 2 * eta E)
      ≤ E0 E * (fsXp h.t (365 / 2) * (3 + 1 / b₀)) :=
        mul_le_mul_of_nonneg_left hsum' hE00
    _ = E0 E * fsXp h.t (365 / 2) * (3 + 1 / b₀) := by ring

/-- **The `e23A` bracket**: `e23A E ≤ E0·X^{365/2}` (`X`-exponent `1283 ≥ 365/2`). -/
theorem e23A_le (E : Q3Env Mode) (h : FSParamsView E) :
    e23A E ≤ E0 E * fsXp h.t (365 / 2) := by
  have h0 : 0 < h.t := h.t_pos
  have hE00 : 0 ≤ E0 E := errA_E0_nonneg E h
  rw [e23A]
  apply mul_le_mul_of_nonneg_left _ hE00
  rw [errA_eta E h, errA_KL E h, errA_Kl E h, errA_dil E h]
  rw [fsXp_pow h0.le, fsXp_rpow h0.le]
  simp only [fsXp_mul h0]
  exact fsXp_le_fsXp h0 h.t_le_one (by norm_num)

/-- **The `e4A` bracket**: `e4A E ≤ E0·X^{1435/8}·((27/4)√2 + 1/b₀)`. -/
theorem e4A_le (b₀ : ℝ) (hb₀ : 0 < b₀) (E : Q3Env Mode) (h : FSParamsView E) (hb : b₀ ≤ E.b) :
    e4A E ≤ E0 E * fsXp h.t (1435 / 8) * (27 / 4 * Real.sqrt 2 + 1 / b₀) := by
  have h0 : 0 < h.t := h.t_pos
  have h1t : h.t ≤ 1 := h.t_le_one
  have hE00 : 0 ≤ E0 E := errA_E0_nonneg E h
  -- the first summand
  have hp1 : E.rho ^ 2 * E.aScat * E.ell ^ 3 * Real.sqrt (E.bigM / E.z ^ 2) *
        (E.KH⁻¹ + (E.Kl * E.KL) ^ (-(E.intM : ℝ)) + (E.Kl * E.KL) ^ (3 / 2 : ℝ) * eta E)
      ≤ (E0 E * fsXp h.t (1435 / 8)) * (27 / 4 * Real.sqrt 2) := by
    set A := E.rho ^ 2 * E.aScat * E.ell ^ 3 with hAdef
    set B := Real.sqrt (E.bigM / E.z ^ 2) with hBdef
    set C := E.KH⁻¹ + (E.Kl * E.KL) ^ (-(E.intM : ℝ)) +
      (E.Kl * E.KL) ^ (3 / 2 : ℝ) * eta E with hCdef
    have hc1 : E.KH⁻¹ = fsXp h.t (549 / 4) := by
      rw [errA_KH E h, fsXp_inv h0]
      norm_num
    have hc2 : (E.Kl * E.KL) ^ (-(E.intM : ℝ)) = fsXp h.t 576 := by
      rw [errA_Kl E h, errA_KL E h, fsXp_mul h0, intM_val E h, fsXp_rpow h0.le]
      norm_num
    have hc3 : (E.Kl * E.KL) ^ (3 / 2 : ℝ) * eta E = fsXp h.t 1218 := by
      rw [errA_Kl E h, errA_KL E h, fsXp_mul h0, fsXp_rpow h0.le, errA_eta E h, fsXp_mul h0]
      norm_num
    have hA1 : A ≤ (9 / 4) * E0 E := by rw [hAdef]; exact errA_rho_sq_le E h
    have hB1 : B ≤ Real.sqrt 2 * fsXp h.t (337 / 8) := by rw [hBdef]; exact errA_sqrt_le E h
    have hC1 : C ≤ 3 * fsXp h.t (549 / 4) := by
      rw [hCdef, hc1, hc2, hc3]
      have h1 : fsXp h.t 576 ≤ fsXp h.t (549 / 4) := fsXp_le_fsXp h0 h1t (by norm_num)
      have h2 : fsXp h.t 1218 ≤ fsXp h.t (549 / 4) := fsXp_le_fsXp h0 h1t (by norm_num)
      linarith
    have hA0 : 0 ≤ A := by
      rw [hAdef]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (a_pos E h).le) (pow_nonneg (ell_pos E h).le 3)
    have hB0 : 0 ≤ B := by rw [hBdef]; exact Real.sqrt_nonneg _
    have hC0 : 0 ≤ C := by
      rw [hCdef, hc1, hc2, hc3]
      exact add_nonneg (add_nonneg (fsXp_pos (t := h.t) (c := 549 / 4) h0).le
        (fsXp_pos (t := h.t) (c := 576) h0).le) (fsXp_pos (t := h.t) (c := 1218) h0).le
    have hAB : A * B ≤ ((9 / 4) * E0 E) * (Real.sqrt 2 * fsXp h.t (337 / 8)) :=
      mul_le_mul hA1 hB1 hB0 (mul_nonneg (by norm_num) hE00)
    have hABC : A * B * C ≤
        (((9 / 4) * E0 E) * (Real.sqrt 2 * fsXp h.t (337 / 8))) * (3 * fsXp h.t (549 / 4)) :=
      mul_le_mul hAB hC1 hC0
        (mul_nonneg (mul_nonneg (by norm_num) hE00)
          (mul_nonneg (Real.sqrt_nonneg 2) (fsXp_pos h0).le))
    have hY12 : fsXp h.t (337 / 8) * fsXp h.t (549 / 4) = fsXp h.t (1435 / 8) := by
      rw [fsXp_mul h0]; norm_num
    calc A * B * C ≤
          (((9 / 4) * E0 E) * (Real.sqrt 2 * fsXp h.t (337 / 8))) * (3 * fsXp h.t (549 / 4)) :=
          hABC
      _ = ((9 / 4) * Real.sqrt 2 * 3) * (E0 E * (fsXp h.t (337 / 8) * fsXp h.t (549 / 4))) := by
          ring
      _ = ((9 / 4) * Real.sqrt 2 * 3) * (E0 E * fsXp h.t (1435 / 8)) := by rw [hY12]
      _ = (E0 E * fsXp h.t (1435 / 8)) * (27 / 4 * Real.sqrt 2) := by ring
  -- the second summand
  have hp2 : E0 E * E.Kl ^ 2 * E.lille ^ 4 / E.b ≤
      (E0 E * fsXp h.t (1435 / 8)) * (1 / b₀) := by
    have hEb : 0 < E.b := lt_of_lt_of_le hb₀ hb
    have hnum : E0 E * E.Kl ^ 2 * E.lille ^ 4 = E0 E * fsXp h.t 191 := by
      rw [errA_Kl E h, errA_lille E h, fsXp_pow h0.le, fsXp_pow h0.le, mul_assoc, fsXp_mul h0]
      norm_num
    rw [hnum]
    have hYle : fsXp h.t 191 ≤ fsXp h.t (1435 / 8) := fsXp_le_fsXp h0 h1t (by norm_num)
    have hmul : E0 E * fsXp h.t 191 ≤ E0 E * fsXp h.t (1435 / 8) :=
      mul_le_mul_of_nonneg_left hYle hE00
    have hstep1 : E0 E * fsXp h.t 191 / E.b ≤ E0 E * fsXp h.t (1435 / 8) / E.b :=
      div_le_div_of_nonneg_right hmul hEb.le
    have hstep2 : E0 E * fsXp h.t (1435 / 8) / E.b ≤ E0 E * fsXp h.t (1435 / 8) / b₀ :=
      div_le_div_of_nonneg_left (mul_nonneg hE00 (fsXp_pos h0).le) hb₀ hb
    have hstep3 : E0 E * fsXp h.t (1435 / 8) / b₀ =
        (E0 E * fsXp h.t (1435 / 8)) * (1 / b₀) := by
      rw [div_eq_mul_inv]; ring
    exact le_trans hstep1 (le_trans hstep2 (le_of_eq hstep3))
  rw [e4A]
  refine le_trans (add_le_add hp1 hp2) (le_of_eq ?_)
  ring

/-! ## 3. Non-negativity of the brackets (needed to replace `Cᵢ` by `|Cᵢ|`) -/

/-- `e1A E ≥ 0` (all four terms are positive monomials in `X`). -/
theorem e1A_nonneg (E : Q3Env Mode) (h : FSParamsView E) (hb : 0 < E.b) : 0 ≤ e1A E := by
  have h0 : 0 < h.t := h.t_pos
  have he : ∀ c : ℝ, 0 ≤ fsXp h.t c := fun c => (fsXp_pos h0).le
  rw [e1A]
  apply mul_nonneg (errA_E0_nonneg E h)
  rw [errA_dil E h, errA_dil E h, errA_Kl E h, errA_KL E h, errA_lille E h,
    errA_eta_sq E h, errA_eta E h]
  simp only [fsXp_pow h0.le, fsXp_rpow h0.le, fsXp_mul h0]
  exact add_nonneg (add_nonneg (add_nonneg (he _) (he _)) (div_nonneg (he _) hb.le)) (he _)

/-- `e23A E ≥ 0`. -/
theorem e23A_nonneg (E : Q3Env Mode) (h : FSParamsView E) : 0 ≤ e23A E := by
  have h0 : 0 < h.t := h.t_pos
  have he : ∀ c : ℝ, 0 ≤ fsXp h.t c := fun c => (fsXp_pos h0).le
  rw [e23A]
  apply mul_nonneg (errA_E0_nonneg E h)
  rw [errA_eta E h, errA_KL E h, errA_Kl E h, errA_dil E h]
  simp only [fsXp_pow h0.le, fsXp_rpow h0.le, fsXp_mul h0]
  exact he _

/-- `e4A E ≥ 0`. -/
theorem e4A_nonneg (E : Q3Env Mode) (h : FSParamsView E) (hb : 0 < E.b) : 0 ≤ e4A E := by
  have h0 : 0 < h.t := h.t_pos
  have he : ∀ c : ℝ, 0 ≤ fsXp h.t c := fun c => (fsXp_pos h0).le
  have hlille : 0 ≤ E.lille := by rw [errA_lille E h]; exact he _
  have hrho : 0 ≤ E.rho ^ 2 * E.aScat * E.ell ^ 3 :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (a_pos E h).le) (pow_nonneg (ell_pos E h).le 3)
  have hKH : 0 < E.KH := lt_of_lt_of_le zero_lt_one h.one_le_KH
  have hKl : 0 < E.Kl := lt_of_lt_of_le zero_lt_one h.one_le_Kl
  have hKL : 0 < E.KL := lt_of_lt_of_le zero_lt_one h.one_le_KL
  have hbase : 0 ≤ E.Kl * E.KL := (mul_pos hKl hKL).le
  have heta : 0 ≤ eta E := by rw [errA_eta E h]; exact he _
  have hsum3 : 0 ≤ E.KH⁻¹ + (E.Kl * E.KL) ^ (-(E.intM : ℝ)) + (E.Kl * E.KL) ^ (3 / 2 : ℝ) * eta E :=
    add_nonneg (add_nonneg (inv_nonneg.mpr hKH.le) (Real.rpow_nonneg hbase _))
      (mul_nonneg (Real.rpow_nonneg hbase _) heta)
  rw [e4A]
  exact add_nonneg (mul_nonneg (mul_nonneg hrho (Real.sqrt_nonneg _)) hsum3)
    (div_nonneg (mul_nonneg (mul_nonneg (errA_E0_nonneg E h) (sq_nonneg _)) (pow_nonneg hlille 4)) hb.le)

/-! ## 4. `fsXp` helpers for the threshold `t₀` -/

/-- `fsXp t c = (fsXp t 1)^c`. -/
theorem fsXp_eq_pow_one {t : ℝ} (ht : 0 ≤ t) (c : ℝ) : fsXp t c = (fsXp t 1) ^ c := by
  rw [fsXp, fsXp, ← Real.rpow_mul ht (1 / 323) c]
  congr 1
  ring

/-- `fsXp t 1 ≤ X₀` gives `fsXp t c ≤ X₀^c` for `c ≥ 0`. -/
theorem fsXp_le_rpow {t X₀ c : ℝ} (ht : 0 ≤ t) (h1 : fsXp t 1 ≤ X₀) (hc : 0 ≤ c) :
    fsXp t c ≤ X₀ ^ c := by
  rw [fsXp_eq_pow_one ht c]
  exact Real.rpow_le_rpow (fsXp_nonneg ht) h1 hc

/-- `t ≤ X₀^{323}` gives `fsXp t 1 ≤ X₀` (for `t > 0`, `X₀ ≥ 0`). -/
theorem fsXp_one_le_of_le {t X₀ : ℝ} (ht : 0 < t) (hX₀ : 0 ≤ X₀)
    (htle : t ≤ X₀ ^ (323 : ℝ)) : fsXp t 1 ≤ X₀ := by
  have h1 : fsXp t 1 = t ^ ((1 : ℝ) / 323) := rfl
  rw [h1]
  calc t ^ ((1 : ℝ) / 323) ≤ (X₀ ^ (323 : ℝ)) ^ ((1 : ℝ) / 323) :=
        Real.rpow_le_rpow ht.le htle (by norm_num)
    _ = X₀ ^ ((323 : ℝ) * ((1 : ℝ) / 323)) :=
        (Real.rpow_mul hX₀ (323 : ℝ) ((1 : ℝ) / 323)).symm
    _ = X₀ := by rw [show ((323 : ℝ) * ((1 : ℝ) / 323)) = 1 by norm_num, Real.rpow_one]

/-- For every `K ≥ 0` and `e > 0` there is `0 < X₀ ≤ 1` with `K·X₀^e ≤ 1`. -/
theorem exists_small_rpow {e : ℝ} (he : 0 < e) {K : ℝ} (hK : 0 ≤ K) :
    ∃ X₀ : ℝ, 0 < X₀ ∧ X₀ ≤ 1 ∧ K * X₀ ^ e ≤ 1 := by
  have hK1 : 0 < K + 1 := by linarith
  have hbase0 : 0 ≤ 1 / (K + 1) := by positivity
  have hbase1 : 1 / (K + 1) ≤ 1 := by rw [div_le_one₀ hK1]; linarith
  refine ⟨(1 / (K + 1)) ^ (1 / e), Real.rpow_pos_of_pos (by positivity) _, ?_, ?_⟩
  · exact Real.rpow_le_one hbase0 hbase1 (by positivity)
  · have hpow : ((1 / (K + 1)) ^ (1 / e)) ^ e = 1 / (K + 1) := by
      rw [← Real.rpow_mul hbase0 (1 / e) e,
        show (1 / e) * e = 1 by field_simp, Real.rpow_one]
    rw [hpow, mul_one_div, div_le_one₀ hK1]
    linarith

end Work.BoseB7A
