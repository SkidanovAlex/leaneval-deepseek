import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.ErrProfile
import Submission.Work.NumberTheory.Chen.APSwitchUpper.errH_transport
import Submission.Work.NumberTheory.Chen.APSwitchUpper.profC_integral_form

/-!
# Geometric decay of `profC j` against the error profile `errH`

`profC j = f_{j+1}` is the delay-difference family of the sharp (Rosser–Iwaniec) linear
sieve (`APSwitchUpper.prof`) and `errH` the explicit exponential error profile
(`APSwitchUpper.ErrProfile`).  This file proves the uniform-in-`j` decay

`profC j σ ≤ 20 · (97/100)^j · errH σ`   for all `j : ℕ` and `σ ≥ 1`

(i.e. with the absolute constant `20`, twice the constant `2e^2` of the sharp induction),
which is the estimate the switched-window upper bound consumes to sum the layer errors of
the cube (`β = 2`) chain sieve.

## The mechanism

The constant `97/100` is exactly the contraction constant of the `errH`-tail transport
inequalities of `APSwitchUpper.errH_transport`:

* `∫_{Ioi s} errH (t−1) dt ≤ (97/100) · s · errH s`  for `s ≥ 2`   (uncapped recursion);
* `∫_2^∞ errH u du ≤ (97/100) · errH 2`              (the `max (s−1) 2` clamp, `s ≤ 2`), which
  is the sharp form `e^{-2} − e^{-3} + ∫_3^∞ errH ≤ (94/100) e^{-2}` obtained from
  `tail3_le`.

Since the recursion step is `profC (k+1) s = (1/s)·∫_a^{k+3} profC k` with `a ≥ 1`, the
induction hypothesis `profC k ≤ C·(97/100)^k·errH` and the tail bound above give, after
dividing by `s > 0`, the same statement with one extra factor `97/100`: the constant is
preserved along the induction.  The base profile `profC 0 s = (3−s)/s` on `[1,3]` is
controlled by `C₀ = 2 e^2`, and `2e^2 ≤ 20` since `e^2 < 7.4 < 10`.
-/

namespace Work.NumberTheory.Chen.APSwitchUpper

open MeasureTheory Set

noncomputable section

/-- The constant of the sharp induction: `C₀ = 2 * exp 2`. -/
private def C0 : ℝ := 2 * Real.exp 2

private lemma C0_pos : 0 < C0 := by unfold C0; positivity

/-! ## §1  The exponential-integral input at the left end -/

/-- `∫_2^∞ errH ≤ (97/100) · errH 2`.  This is the companion of the tail transport
inequality at the bottom of the range; it is the only place where the range `s ≤ 2` of the
clamped recursion is controlled. -/
private lemma integral_Ioi_two_errH_le :
    (∫ u in Set.Ioi (2:ℝ), errH u) ≤ (97/100) * Real.exp (-2) := by
  have hInt2 : IntegrableOn errH (Set.Ioi (2:ℝ)) := integrableOn_errH_Ioi (by norm_num)
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi (f := errH) (a := (2:ℝ)) (b := (3:ℝ))
    hInt2 (by norm_num)
  have h23 : (∫ u in (2:ℝ)..3, errH u) = Real.exp (-2) - Real.exp (-3) := by
    have hcong : (∫ u in (2:ℝ)..3, errH u) = ∫ u in (2:ℝ)..3, Real.exp (-u) := by
      refine intervalIntegral.integral_congr ?_
      intro u hu
      rw [Set.uIcc_of_le (by norm_num : (2:ℝ) ≤ 3)] at hu
      exact errH_eq_exp_neg hu.1 hu.2
    rw [hcong]
    have h := intervalIntegral.integral_Ioi_sub_Ioi (f := fun u : ℝ => Real.exp (-u))
      (a := (2:ℝ)) (b := (3:ℝ)) (integrableOn_exp_neg_Ioi (2:ℝ)) (by norm_num)
    rw [integral_exp_neg_Ioi, integral_exp_neg_Ioi] at h
    linarith
  have hI3 : (∫ u in Set.Ioi (3:ℝ), errH u) ≤ Real.exp (-3) - (3/50) * Real.exp (-2) := by
    have hcong : (∫ u in Set.Ioi (3:ℝ), errH u)
        = ∫ u in Set.Ioi (3:ℝ), 3 * Real.exp (-u) / u :=
      setIntegral_congr_fun measurableSet_Ioi (fun u hu => errH_of_three_lt hu)
    rw [hcong]
    exact tail3_le
  have hkey : (Real.exp (-2) - Real.exp (-3)) + (Real.exp (-3) - (3/50) * Real.exp (-2))
      = (47/50) * Real.exp (-2) := by ring
  have hcut : (47/50 : ℝ) * Real.exp (-2) ≤ (97/100) * Real.exp (-2) :=
    mul_le_mul_of_nonneg_right (by norm_num) (Real.exp_pos _).le
  linarith [hsplit, h23, hI3, hkey, hcut]

/-! ## §2  The `errH`-tail bound used in the clamped parity -/

/-- The two-range bound for the `errH` tail from `max (s-1) 2`:
`∫_{max (s-1) 2}^∞ errH ≤ (97/100) · s · errH s` for `s ≥ 1`.

For `s ≤ 2` the tail is `≤ ∫_2^∞ errH ≤ (97/100) errH s ≤ (97/100) s errH s`; for `s ≥ 2` it
is dominated by `∫_{s-1}^∞ errH = ∫_s^∞ errH (t-1) dt`, which the transport inequality
controls by `(97/100) s errH s`. -/
private lemma errH_Ioi_max_le (s : ℝ) (hs1 : 1 ≤ s) :
    (∫ u in Set.Ioi (max (s - 1) 2), errH u) ≤ (97/100) * s * errH s := by
  by_cases hs2 : s ≤ 2
  · have hmax : max (s - 1) 2 = (2:ℝ) := max_eq_right (by linarith)
    rw [hmax, errH_of_le_two hs2]
    have h := integral_Ioi_two_errH_le
    have he : (0:ℝ) < Real.exp (-2) := Real.exp_pos _
    nlinarith [h, he, hs1]
  · have hs2' : 2 ≤ s := le_of_lt (not_le.mp hs2)
    have hmono : (∫ u in Set.Ioi (max (s - 1) 2), errH u) ≤ ∫ u in Set.Ioi (s - 1), errH u := by
      refine setIntegral_mono_set (integrableOn_errH_Ioi (by linarith))
        (Filter.Eventually.of_forall errH_nonneg) ?_
      exact Filter.Eventually.of_forall (fun x hx => by
        simp only [Set.mem_Ioi] at hx ⊢; exact lt_of_le_of_lt (le_max_left _ _) hx)
    refine le_trans hmono ?_
    rw [← setIntegral_Ioi_comp_sub errH s 1]
    exact errH_transport.1 s hs2'

/-! ## §3  The integral comparison -/

/-- If `profC k ≤ C · (97/100)^k · errH` pointwise then its integral against `errH` over any
interval `[a,b]` with `a ≥ 1` is bounded by `C · (97/100)^k` times the full tail of `errH`
from `a`. -/
private lemma interval_integral_le_geometric (k : ℕ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    (ih : ∀ u : ℝ, profC k u ≤ C0 * (97/100)^k * errH u) :
    (∫ u in a..b, profC k u) ≤ C0 * (97/100)^k * (∫ u in Set.Ioi a, errH u) := by
  have hCk : 0 ≤ C0 * (97/100)^k := mul_nonneg C0_pos.le (pow_nonneg (by norm_num) k)
  have hErrInt : IntegrableOn errH (Set.Ioc a b) :=
    (integrableOn_errH_Ioi ha).mono_set (fun x hx => hx.1)
  have hII : IntervalIntegrable errH volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr hErrInt
  have hmono : (∫ u in a..b, profC k u) ≤ ∫ u in a..b, C0 * (97/100)^k * errH u := by
    refine intervalIntegral.integral_mono_on hab (profC_intervalIntegrable k a b)
      (hII.const_mul (C0 * (97/100)^k)) (fun u _ => ih u)
  rw [intervalIntegral.integral_const_mul] at hmono
  refine le_trans hmono (mul_le_mul_of_nonneg_left ?_ hCk)
  have hInt : IntegrableOn errH (Set.Ioi a) := integrableOn_errH_Ioi ha
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi (f := errH) (a := a) (b := b) hInt hab
  have hnn : 0 ≤ ∫ u in Set.Ioi b, errH u :=
    setIntegral_nonneg_of_ae (Filter.Eventually.of_forall errH_nonneg)
  linarith [hsplit, hnn]

/-! ## §4  The base case -/

/-- The base profile `profC 0 s = (3-s)/s` on `[1,3]` is bounded by `C0 · errH`. -/
private lemma profC_zero_le (u : ℝ) : profC 0 u ≤ C0 * errH u := by
  rw [profC_zero]
  by_cases h : 1 ≤ u ∧ u ≤ 3
  · rw [if_pos h]
    have hu1 : 1 ≤ u := h.1
    have hu3 : u ≤ 3 := h.2
    have hupos : 0 < u := by linarith
    rcases le_or_gt u 2 with hu2 | hu2
    · rw [errH_of_le_two hu2]
      have h1 : Real.exp 2 * Real.exp (-2) = 1 := by rw [← Real.exp_add]; norm_num
      have hC2 : C0 * Real.exp (-2) = 2 := by unfold C0; nlinarith [h1]
      rw [hC2, div_le_iff₀ hupos]
      linarith
    · have hu2' : 2 ≤ u := le_of_lt hu2
      rw [errH_eq_exp_neg hu2' hu3]
      have hhalf : (3 - u)/u ≤ 1/2 := by
        rw [div_le_iff₀ hupos]; linarith
      have h4 : Real.exp 1 ≤ 4 := le_of_lt (lt_trans Real.exp_one_lt_d9 (by norm_num))
      have hlow : C0 * Real.exp (-u) ≥ 2 * Real.exp (-1) := by
        have hexp : Real.exp (-u) ≥ Real.exp (-3) := by
          rw [ge_iff_le, Real.exp_le_exp]; linarith
        have h2 : Real.exp 2 * Real.exp (-3) = Real.exp (-1) := by
          rw [← Real.exp_add]; norm_num
        have hC : C0 * Real.exp (-3) = 2 * Real.exp (-1) := by unfold C0; nlinarith [h2]
        nlinarith [hexp, Real.exp_pos (-3), C0_pos]
      have hfin : (1:ℝ)/2 ≤ 2 * Real.exp (-1) := by
        have h4' : (1:ℝ)/4 ≤ (Real.exp 1)⁻¹ := by
          have := (inv_le_inv₀ (by norm_num : (0:ℝ) < 4) (Real.exp_pos 1)).mpr h4
          simpa using this
        rw [Real.exp_neg]
        have h5 : (2:ℝ) * (1/4) ≤ 2 * (Real.exp 1)⁻¹ :=
          mul_le_mul_of_nonneg_left h4' (by norm_num)
        linarith
      linarith
  · rw [if_neg h]
    exact mul_nonneg C0_pos.le (errH_nonneg u)

/-! ## §5  The induction -/

/-- **Geometric decay of the delay family.**  With `C0 = 2 e^2`,
`profC j u ≤ C0 · (97/100)^j · errH u` for every `j` and `u`. -/
private lemma profC_le_geometric : ∀ j : ℕ, ∀ u : ℝ,
    profC j u ≤ C0 * (97/100)^j * errH u := by
  intro j
  induction j with
  | zero =>
      intro u
      simpa using profC_zero_le u
  | succ k ih =>
      intro s
      have hCk : 0 ≤ C0 * (97/100)^k := mul_nonneg C0_pos.le (pow_nonneg (by norm_num) k)
      have hCk1 : 0 ≤ C0 * (97/100)^(k+1) :=
        mul_nonneg C0_pos.le (pow_nonneg (by norm_num) (k+1))
      have hk3 : (2:ℝ) ≤ (k:ℝ) + 3 := by
        have hk0 : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        linarith
      by_cases hk : k % 2 = 0
      · -- `k` even: the recursion is the unclamped one, valid for `s ≥ 2`
        by_cases hs2 : 2 ≤ s
        · by_cases hs4 : s < (k:ℝ) + 4
          · rw [profC_eq_integral_odd k hk s hs2]
            have ha : (1:ℝ) ≤ s - 1 := by linarith
            have hab : s - 1 ≤ (k:ℝ) + 3 := by linarith
            have hI := interval_integral_le_geometric k ha hab ih
            have htail : (∫ u in Set.Ioi (s - 1), errH u) ≤ (97/100) * s * errH s := by
              rw [← setIntegral_Ioi_comp_sub errH s 1]
              exact errH_transport.1 s hs2
            have hI2 : (∫ u in s - 1..(k:ℝ)+3, profC k u)
                ≤ C0 * (97/100)^k * ((97/100) * s * errH s) :=
              le_trans hI (mul_le_mul_of_nonneg_left htail hCk)
            have hspos : 0 < s := by linarith
            refine le_trans (div_le_div_of_nonneg_right hI2 hspos.le) ?_
            apply le_of_eq
            rw [div_eq_iff (ne_of_gt hspos), pow_succ]
            ring
          · rw [profC_succ, if_neg (by omega : ¬ (k+1) % 2 = 0),
              if_neg (fun h => hs4 h.2)]
            exact mul_nonneg hCk1 (errH_nonneg s)
        · rw [profC_succ, if_neg (by omega : ¬ (k+1) % 2 = 0),
            if_neg (fun h => hs2 h.1)]
          exact mul_nonneg hCk1 (errH_nonneg s)
      · -- `k` odd: the recursion is clamped at `3`, valid for `s ≥ 1`
        have hk1 : k % 2 = 1 := by omega
        by_cases hs1 : 1 ≤ s
        · by_cases hs4 : s < (k:ℝ) + 4
          · rw [profC_eq_integral_even k hk1 s hs1]
            have ha : (1:ℝ) ≤ max (s - 1) 2 := le_trans (by norm_num) (le_max_right _ _)
            have hab : max (s - 1) 2 ≤ (k:ℝ) + 3 := max_le (by linarith) hk3
            have hI := interval_integral_le_geometric k ha hab ih
            have htail := errH_Ioi_max_le s hs1
            have hI2 : (∫ u in max (s - 1) 2..(k:ℝ)+3, profC k u)
                ≤ C0 * (97/100)^k * ((97/100) * s * errH s) :=
              le_trans hI (mul_le_mul_of_nonneg_left htail hCk)
            have hspos : 0 < s := by linarith
            refine le_trans (div_le_div_of_nonneg_right hI2 hspos.le) ?_
            apply le_of_eq
            rw [div_eq_iff (ne_of_gt hspos), pow_succ]
            ring
          · rw [profC_succ, if_pos (by omega : (k+1) % 2 = 0),
              if_neg (fun h => hs4 h.2)]
            exact mul_nonneg hCk1 (errH_nonneg s)
        · rw [profC_succ, if_pos (by omega : (k+1) % 2 = 0),
            if_neg (fun h => hs1 h.1)]
          exact mul_nonneg hCk1 (errH_nonneg s)

/-- **The decay estimate.**  `profC j σ ≤ 20 · (97/100)^j · errH σ` for every `j : ℕ` and
every `σ ≥ 1`; the factor `20` is the rounded-up sharp constant `2 e^2 < 14.8`. -/
theorem profC_le_decay :
    ∀ (j : ℕ) (σ : ℝ), 1 ≤ σ →
      Work.NumberTheory.Chen.APSwitchUpper.profC j σ
        ≤ 20 * ((97:ℝ)/100)^j * Work.NumberTheory.Chen.APSwitchUpper.errH σ := by
  intro j σ _
  have h := profC_le_geometric j σ
  have hK : C0 ≤ 20 := by
    unfold C0
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h2 : Real.exp 2 < 7.4 := by
      rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [h1, Real.exp_pos 1]
    linarith
  have hr : (0:ℝ) ≤ ((97:ℝ)/100)^j := pow_nonneg (by norm_num) j
  have he : (0:ℝ) ≤ errH σ := errH_nonneg σ
  calc profC j σ ≤ C0 * ((97:ℝ)/100)^j * errH σ := h
    _ ≤ 20 * ((97:ℝ)/100)^j * errH σ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK hr) he

end

end Work.NumberTheory.Chen.APSwitchUpper
