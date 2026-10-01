/-
# `lam0_fm_eulFacBounds` — bounds for the Euler-factor part `eulFac q` of the principal corrector

`eulFac q z = ∑_{p | q} log p / (p^z - 1)`.  This module proves, from scratch, that for
`Re s ≥ 1` the function `eulFac q` and its first two derivatives are bounded by twice/four
times/sixteen times the corresponding prime sums:
`‖eulFac q s‖ ≤ 2∑ log p/p`, `‖(eulFac q)'(s)‖ ≤ 4∑ (log p)²/p`, `‖(eulFac q)''(s)‖ ≤ 16∑ (log p)³/p`.

This is a self-contained, `sorry`-free replacement for the placeholder
`Work.ZeroFreeTables.lam0_eulFacBounds` (a colleague's file, which is `sorry`-ed at the time of
writing); the statement is identical apart from the name `lam0_eulFacBounds_fm`, so the
`principalBound4_fm` chain can consume it.  The proof bounds each Euler factor separately
(`p^{Re s} ≥ p` and `|p^s - 1| ≥ p/2`, so `|log p/(p^s-1)| ≤ 2 log p/p`; the derivative
formulas are `-(log p)²p^s/(p^s-1)²` and `(log p)³p^s(p^s+1)/(p^s-1)³`), then sums with the
triangle inequality.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.lam0w.PrincipalDefs

open Complex Filter
open scoped BigOperators Topology
noncomputable section
namespace Work.ZeroFreeTables

/-! ## Elementary bounds for the Euler factor of `eulFac` -/

private lemma norm_ofReal_log (p : ℕ) (hp : 1 ≤ p) :
    ‖(((Real.log (p:ℝ)) : ℝ) : ℂ)‖ = Real.log (p:ℝ) := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hp))]

private lemma cpow_norm_eq (p : ℕ) (hp0 : 0 < p) (z : ℂ) :
    ‖((p:ℂ))^z‖ = (p:ℝ)^z.re := by
  rw [show ((p:ℂ)) = (((p:ℝ)) : ℂ) by simp]
  exact Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hp0) z

private lemma cpow_norm_gt_one (p : ℕ) (hp2 : 2 ≤ p) {z : ℂ} (hz : 0 < z.re) :
    (1:ℝ) < ‖((p:ℂ))^z‖ := by
  rw [cpow_norm_eq p (by omega) z]
  exact Real.one_lt_rpow (by exact_mod_cast (by omega : 1 < p)) hz

private lemma cpow_norm_ge (p : ℕ) (hp2 : 2 ≤ p) {z : ℂ} (hz : 1 ≤ z.re) :
    (p:ℝ) ≤ ‖((p:ℂ))^z‖ := by
  rw [cpow_norm_eq p (by omega) z]
  calc (p:ℝ) = (p:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
    _ ≤ (p:ℝ)^z.re :=
        Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (by omega : 1 ≤ p)) hz

private lemma sub_norm_le (p : ℕ) (hp2 : 2 ≤ p) {z : ℂ} (hz : 0 < z.re) :
    ‖((p:ℂ))^z‖ - 1 ≤ ‖((p:ℂ))^z - 1‖ := by
  have h := abs_norm_sub_norm_le (((p:ℂ))^z) (1:ℂ)
  rw [norm_one] at h
  have h0 : (0:ℝ) ≤ ‖((p:ℂ))^z‖ - 1 := by
    have h1 := cpow_norm_gt_one p hp2 hz
    linarith
  rwa [abs_of_nonneg h0] at h

private lemma sub_one_norm_ge (p : ℕ) (hp2 : 2 ≤ p) {z : ℂ} (hz : 1 ≤ z.re) :
    (p:ℝ)/2 ≤ ‖((p:ℂ))^z - 1‖ := by
  have h := sub_norm_le p hp2 (lt_of_lt_of_le zero_lt_one hz)
  have h2 := cpow_norm_ge p hp2 hz
  have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
  linarith

private lemma cpow_sub_one_ne_zero (p : ℕ) (hp2 : 2 ≤ p) {z : ℂ} (hz : 0 < z.re) :
    ((p:ℂ))^z - 1 ≠ 0 := by
  intro h
  have hz1 : ((p:ℂ))^z = 1 := sub_eq_zero.mp h
  have h2 := cpow_norm_gt_one p hp2 hz
  rw [hz1, norm_one] at h2
  exact lt_irrefl 1 h2

private lemma cpow_hasDerivAt (p : ℕ) (hp0 : 0 < p) (z : ℂ) :
    HasDerivAt (fun w : ℂ => ((p:ℂ))^w) (((p:ℂ))^z * Complex.log ((p:ℂ))) z := by
  have hc : ((p:ℂ)) ≠ 0 := by
    intro h
    have hcast : ((p:ℂ)) = (((p:ℝ)) : ℂ) := by simp
    rw [hcast] at h
    exact absurd (Complex.ofReal_eq_zero.mp h)
      (by exact_mod_cast (by omega : p ≠ 0))
  have h := (hasDerivAt_id z).const_cpow (c := ((p:ℂ))) (Or.inl hc)
  rw [mul_one] at h
  exact h

private lemma log_natCast (p : ℕ) (hp0 : 0 < p) :
    Complex.log ((p:ℂ)) = (((Real.log (p:ℝ)) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_natCast p, ← Complex.ofReal_log (le_of_lt (by exact_mod_cast hp0 : (0:ℝ) < (p:ℝ)))]

/-- The single Euler factor `log p / (p^w - 1)`. -/
private def efTerm (p : ℕ) (w : ℂ) : ℂ :=
  (((Real.log (p:ℝ)) : ℝ) : ℂ) / (((p:ℂ))^w - 1)

/-- The derivative of `efTerm p`. -/
private def efD1 (p : ℕ) (w : ℂ) : ℂ :=
  -((((Real.log (p:ℝ)) : ℝ) : ℂ) * (((p:ℂ))^w * Complex.log ((p:ℂ)))
      / ((((p:ℂ))^w - 1)^2))

/-- The second derivative of `efTerm p`. -/
private def efD2 (p : ℕ) (w : ℂ) : ℂ :=
  (((Real.log (p:ℝ)) : ℝ) : ℂ) * (Complex.log ((p:ℂ)))^2 * ((p:ℂ))^w * (((p:ℂ))^w + 1)
    / ((((p:ℂ))^w - 1)^3)

private lemma efTerm_bound (p : ℕ) (hp2 : 2 ≤ p) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖efTerm p s‖ ≤ 2 * Real.log (p:ℝ) / (p:ℝ) := by
  have hp1 : 1 ≤ p := by omega
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hlogp : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp1)
  have hD : 0 < ‖((p:ℂ))^s - 1‖ := by
    have h := sub_one_norm_ge p hp2 hs
    linarith
  unfold efTerm
  rw [norm_div, norm_ofReal_log p hp1]
  rw [div_le_div_iff₀ hD hp0]
  nlinarith [sub_one_norm_ge p hp2 hs, hlogp]

private lemma efTerm_hasDerivAt (p : ℕ) (hp2 : 2 ≤ p) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (efTerm p) (efD1 p z) z := by
  have hp0 : 0 < p := by omega
  have hDne : ((p:ℂ))^z - 1 ≠ 0 := cpow_sub_one_ne_zero p hp2 hz
  have hbase := (cpow_hasDerivAt p hp0 z).sub_const 1
  have hinv := hbase.inv hDne
  have hmul := hinv.const_mul (((Real.log (p:ℝ)) : ℝ) : ℂ)
  have hfun : efTerm p =ᶠ[𝓝 z]
      (fun w : ℂ => (((Real.log (p:ℝ)) : ℝ) : ℂ) * ((((p:ℂ))^w - 1))⁻¹) :=
    Filter.Eventually.of_forall (fun w => by
      unfold efTerm
      simp only [div_eq_mul_inv])
  have hder : (((Real.log (p:ℝ)) : ℝ) : ℂ)
        * (-(((p:ℂ))^z * Complex.log ((p:ℂ))) / ((((p:ℂ))^z - 1)^2)) = efD1 p z := by
    unfold efD1
    ring
  exact (Filter.EventuallyEq.hasDerivAt_iff hfun).mpr (hmul.congr_deriv hder)

private lemma efD1_bound (p : ℕ) (hp2 : 2 ≤ p) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖efD1 p s‖ ≤ 4 * (Real.log (p:ℝ))^2 / (p:ℝ) := by
  have hp1 : 1 ≤ p := by omega
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
  set x : ℝ := (p:ℝ)^s.re with hx
  have hA : ‖((p:ℂ))^s‖ = x := by rw [hx]; exact cpow_norm_eq p (by omega) s
  have hL : ‖Complex.log ((p:ℂ))‖ = Real.log (p:ℝ) := by
    rw [log_natCast p (by omega), norm_ofReal_log p hp1]
  have hDpos : 0 < ‖((p:ℂ))^s - 1‖ := by
    have h := sub_one_norm_ge p hp2 hs
    linarith
  have hDsub : x - 1 ≤ ‖((p:ℂ))^s - 1‖ := by
    have h := sub_norm_le p hp2 (lt_of_lt_of_le zero_lt_one hs)
    rwa [hA] at h
  have hpx : (p:ℝ) ≤ x := by
    rw [hx]
    calc (p:ℝ) = (p:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ (p:ℝ)^s.re :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp1) hs
  have hx2 : (2:ℝ) ≤ x := le_trans hpR hpx
  have hkey1 : (p:ℝ) * x ≤ 4 * (x - 1)^2 := by
    have h1 : (p:ℝ) * x ≤ x * x := by nlinarith [hpx, hx2]
    have h2 : x * x ≤ 4 * (x - 1)^2 := by nlinarith [hx2]
    linarith
  have hDsq : (x - 1)^2 ≤ ‖((p:ℂ))^s - 1‖^2 :=
    pow_le_pow_left₀ (by linarith) hDsub 2
  have hm1 : (Real.log (p:ℝ))^2 * ((p:ℝ) * x) ≤ (Real.log (p:ℝ))^2 * (4 * (x - 1)^2) :=
    mul_le_mul_of_nonneg_left hkey1 (sq_nonneg _)
  have hm2 : (Real.log (p:ℝ))^2 * (4 * (x - 1)^2)
      ≤ (Real.log (p:ℝ))^2 * (4 * ‖((p:ℂ))^s - 1‖^2) :=
    mul_le_mul_of_nonneg_left (by linarith [hDsq]) (sq_nonneg _)
  unfold efD1
  simp only [norm_div, norm_neg, norm_mul, norm_pow, hA, hL, norm_ofReal_log p hp1]
  rw [div_le_div_iff₀ (pow_pos hDpos 2) hp0]
  linarith [hm1, hm2]

private lemma efD1_hasDerivAt (p : ℕ) (hp2 : 2 ≤ p) {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt (efD1 p) (efD2 p z) z := by
  have hp0 : 0 < p := by omega
  have hDne : ((p:ℂ))^z - 1 ≠ 0 := cpow_sub_one_ne_zero p hp2 hz
  have hD2ne : (((p:ℂ))^z - 1)^2 ≠ 0 := pow_ne_zero 2 hDne
  have hD4ne : ((((p:ℂ))^z - 1)^2)^2 ≠ 0 := pow_ne_zero 2 hD2ne
  have hD3ne : (((p:ℂ))^z - 1)^3 ≠ 0 := pow_ne_zero 3 hDne
  have hAder := cpow_hasDerivAt p hp0 z
  have hD2der : HasDerivAt (fun w : ℂ => (((p:ℂ))^w - 1)^2)
      (2 * (((p:ℂ))^z - 1)^(2-1) * (((p:ℂ))^z * Complex.log ((p:ℂ)))) z :=
    (hAder.sub_const 1).pow 2
  have hinv := hD2der.inv hD2ne
  have hprod := hAder.mul hinv
  have hmul := hprod.const_mul (-((((Real.log (p:ℝ)) : ℝ) : ℂ) * Complex.log ((p:ℂ))))
  have hfun : efD1 p =ᶠ[𝓝 z] (fun w : ℂ =>
      (-((((Real.log (p:ℝ)) : ℝ) : ℂ) * Complex.log ((p:ℂ))))
        * (((p:ℂ))^w * ((((p:ℂ))^w - 1)^2)⁻¹)) :=
    Filter.Eventually.of_forall (fun w => by
      unfold efD1
      simp only [div_eq_mul_inv]
      ring)
  have hder : (-((((Real.log (p:ℝ)) : ℝ) : ℂ) * Complex.log ((p:ℂ))))
        * ((((p:ℂ))^z * Complex.log ((p:ℂ))) * ((((p:ℂ))^z - 1)^2)⁻¹
            + ((p:ℂ))^z * (-(2 * (((p:ℂ))^z - 1)^(2-1)
                * (((p:ℂ))^z * Complex.log ((p:ℂ)))) / ((((p:ℂ))^z - 1)^2)^2))
      = efD2 p z := by
    unfold efD2
    field_simp [hDne, hD2ne, hD4ne, hD3ne]
    ring
  exact (Filter.EventuallyEq.hasDerivAt_iff hfun).mpr (hmul.congr_deriv hder)

private lemma efD2_bound (p : ℕ) (hp2 : 2 ≤ p) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖efD2 p s‖ ≤ 16 * (Real.log (p:ℝ))^3 / (p:ℝ) := by
  have hp1 : 1 ≤ p := by omega
  have hp0 : (0:ℝ) < (p:ℝ) := by exact_mod_cast (by omega : 0 < p)
  have hpR : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
  set x : ℝ := (p:ℝ)^s.re with hx
  have hA : ‖((p:ℂ))^s‖ = x := by rw [hx]; exact cpow_norm_eq p (by omega) s
  have hL : ‖Complex.log ((p:ℂ))‖ = Real.log (p:ℝ) := by
    rw [log_natCast p (by omega), norm_ofReal_log p hp1]
  have hDpos : 0 < ‖((p:ℂ))^s - 1‖ := by
    have h := sub_one_norm_ge p hp2 hs
    linarith
  have hDsub : x - 1 ≤ ‖((p:ℂ))^s - 1‖ := by
    have h := sub_norm_le p hp2 (lt_of_lt_of_le zero_lt_one hs)
    rwa [hA] at h
  have hpx : (p:ℝ) ≤ x := by
    rw [hx]
    calc (p:ℝ) = (p:ℝ)^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ (p:ℝ)^s.re :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp1) hs
  have hx2 : (2:ℝ) ≤ x := le_trans hpR hpx
  have hAadd : ‖((p:ℂ))^s + 1‖ ≤ x + 1 := by
    calc ‖((p:ℂ))^s + 1‖ ≤ ‖((p:ℂ))^s‖ + ‖(1:ℂ)‖ := norm_add_le _ _
      _ = x + 1 := by rw [hA, norm_one]
  have hkey2 : (p:ℝ) * x * (x + 1) ≤ 16 * (x - 1)^3 := by
    have h1 : (p:ℝ) * x * (x + 1) ≤ x * x * (x + 1) := by nlinarith [hpx, hx2]
    have h2 : x * x * (x + 1) ≤ 16 * (x - 1)^3 := by
      nlinarith [hx2, sq_nonneg (x - 19/30)]
    linarith
  have hDcube : (x - 1)^3 ≤ ‖((p:ℂ))^s - 1‖^3 :=
    pow_le_pow_left₀ (by linarith) hDsub 3
  have hC3 : (0:ℝ) ≤ (Real.log (p:ℝ))^3 := by positivity
  have h2 : (Real.log (p:ℝ))^3 * (x * ‖((p:ℂ))^s + 1‖ * (p:ℝ))
      ≤ (Real.log (p:ℝ))^3 * (x * (x + 1) * (p:ℝ)) := by
    have h1 : x * ‖((p:ℂ))^s + 1‖ * (p:ℝ) ≤ x * (x + 1) * (p:ℝ) := by
      have hx0 : 0 ≤ x := by linarith [hx2]
      have hmul1 : x * ‖((p:ℂ))^s + 1‖ ≤ x * (x + 1) :=
        mul_le_mul_of_nonneg_left hAadd hx0
      exact mul_le_mul_of_nonneg_right hmul1 hp0.le
    exact mul_le_mul_of_nonneg_left h1 hC3
  have h3 : (Real.log (p:ℝ))^3 * (x * (x + 1) * (p:ℝ))
      ≤ (Real.log (p:ℝ))^3 * (16 * ‖((p:ℂ))^s - 1‖^3) := by
    have h1 : x * (x + 1) * (p:ℝ) ≤ 16 * ‖((p:ℂ))^s - 1‖^3 := by
      have hh : x * (x + 1) * (p:ℝ) = (p:ℝ) * x * (x + 1) := by ring
      rw [hh]
      linarith [hkey2, hDcube]
    exact mul_le_mul_of_nonneg_left h1 hC3
  unfold efD2
  simp only [norm_div, norm_mul, norm_pow, hA, hL, norm_ofReal_log p hp1]
  rw [div_le_div_iff₀ (pow_pos hDpos 3) hp0]
  linarith [h2, h3]

/-! ## The Euler-factor bounds -/

theorem lam0_eulFacBounds_fm (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 ≤ s.re) :
    ‖Work.ZeroFreeTables.lam0w.eulFac q s‖
        ≤ 2 * (q.primeFactors.sum fun p => Real.log (p : ℝ) / (p : ℝ))
      ∧ ‖iteratedDeriv 1 (Work.ZeroFreeTables.lam0w.eulFac q) s‖
        ≤ 4 * (q.primeFactors.sum fun p => (Real.log (p : ℝ)) ^ 2 / (p : ℝ))
      ∧ ‖iteratedDeriv 2 (Work.ZeroFreeTables.lam0w.eulFac q) s‖
        ≤ 16 * (q.primeFactors.sum fun p => (Real.log (p : ℝ)) ^ 3 / (p : ℝ)) := by
  have hp2 : ∀ p ∈ q.primeFactors, 2 ≤ p :=
    fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have heul : Work.ZeroFreeTables.lam0w.eulFac q
      = fun z : ℂ => ∑ p ∈ q.primeFactors, efTerm p z := rfl
  refine ⟨?_, ?_, ?_⟩
  · calc ‖Work.ZeroFreeTables.lam0w.eulFac q s‖
        = ‖∑ p ∈ q.primeFactors, efTerm p s‖ := by rw [heul]
      _ ≤ ∑ p ∈ q.primeFactors, ‖efTerm p s‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ q.primeFactors, 2 * Real.log (p:ℝ) / (p:ℝ) :=
          Finset.sum_le_sum (fun p hp => efTerm_bound p (hp2 p hp) hs)
      _ = 2 * ∑ p ∈ q.primeFactors, Real.log (p:ℝ) / (p:ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun p _ => by ring)
  · have hd : deriv (Work.ZeroFreeTables.lam0w.eulFac q) s
        = ∑ p ∈ q.primeFactors, efD1 p s := by
      rw [heul]
      rw [show deriv (fun z : ℂ => ∑ p ∈ q.primeFactors, efTerm p z) s
            = deriv (∑ p ∈ q.primeFactors, fun w : ℂ => efTerm p w) s from by
          congr 1
          funext z
          rw [Finset.sum_apply]]
      rw [deriv_sum (fun p hp => (efTerm_hasDerivAt p (hp2 p hp)
        (lt_of_lt_of_le zero_lt_one hs)).differentiableAt)]
      exact Finset.sum_congr rfl (fun p hp =>
        (efTerm_hasDerivAt p (hp2 p hp) (lt_of_lt_of_le zero_lt_one hs)).deriv)
    rw [iteratedDeriv_one, hd]
    calc ‖∑ p ∈ q.primeFactors, efD1 p s‖ ≤ ∑ p ∈ q.primeFactors, ‖efD1 p s‖ :=
          norm_sum_le _ _
      _ ≤ ∑ p ∈ q.primeFactors, 4 * (Real.log (p:ℝ))^2 / (p:ℝ) :=
          Finset.sum_le_sum (fun p hp => efD1_bound p (hp2 p hp) hs)
      _ = 4 * ∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^2 / (p:ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun p _ => by ring)
  · have h2eq : iteratedDeriv 2 (Work.ZeroFreeTables.lam0w.eulFac q)
        = deriv (deriv (Work.ZeroFreeTables.lam0w.eulFac q)) := by
      have htwo : (2:ℕ) = 1 + 1 := rfl
      rw [htwo, iteratedDeriv_succ, iteratedDeriv_one]
    have hev : (fun z : ℂ => ∑ p ∈ q.primeFactors, efD1 p z)
        =ᶠ[𝓝 s] deriv (Work.ZeroFreeTables.lam0w.eulFac q) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (lt_of_lt_of_le zero_lt_one hs)] with z hz
      rw [heul]
      rw [show deriv (fun z : ℂ => ∑ p ∈ q.primeFactors, efTerm p z) z
            = deriv (∑ p ∈ q.primeFactors, fun w : ℂ => efTerm p w) z from by
          congr 1
          funext y
          rw [Finset.sum_apply]]
      rw [deriv_sum (fun p hp => (efTerm_hasDerivAt p (hp2 p hp) hz).differentiableAt)]
      exact Finset.sum_congr rfl (fun p hp =>
        ((efTerm_hasDerivAt p (hp2 p hp) hz).deriv).symm)
    have hd2 : deriv (fun z : ℂ => ∑ p ∈ q.primeFactors, efD1 p z) s
        = ∑ p ∈ q.primeFactors, efD2 p s := by
      rw [show deriv (fun z : ℂ => ∑ p ∈ q.primeFactors, efD1 p z) s
            = deriv (∑ p ∈ q.primeFactors, fun w : ℂ => efD1 p w) s from by
          congr 1
          funext z
          rw [Finset.sum_apply]]
      rw [deriv_sum (fun p hp => (efD1_hasDerivAt p (hp2 p hp)
        (lt_of_lt_of_le zero_lt_one hs)).differentiableAt)]
      exact Finset.sum_congr rfl (fun p hp =>
        (efD1_hasDerivAt p (hp2 p hp) (lt_of_lt_of_le zero_lt_one hs)).deriv)
    rw [h2eq, ← Filter.EventuallyEq.deriv_eq hev, hd2]
    calc ‖∑ p ∈ q.primeFactors, efD2 p s‖ ≤ ∑ p ∈ q.primeFactors, ‖efD2 p s‖ :=
          norm_sum_le _ _
      _ ≤ ∑ p ∈ q.primeFactors, 16 * (Real.log (p:ℝ))^3 / (p:ℝ) :=
          Finset.sum_le_sum (fun p hp => efD2_bound p (hp2 p hp) hs)
      _ = 16 * ∑ p ∈ q.primeFactors, (Real.log (p:ℝ))^3 / (p:ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun p _ => by ring)

end Work.ZeroFreeTables
