import Mathlib
import Submission.Work.FIArea6Hecke.StripCoreDefs
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea6Hecke.R.heckeStripNearOne
import Submission.Work.FIArea5.HeckeZFR.HeckeNonvanishing
import Submission.Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
import Submission.Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators Topology

noncomputable section

/-! ## Elementary summations in the geometric series -/

/-- `∑_n (n+1) r^n = (1-r)^{-2}` for `‖r‖ < 1` (real form of the standard geometric summation). -/
lemma tsum_nat_succ_mul_geometric {r : ℝ} (hr : ‖r‖ < 1) :
    ∑' n : ℕ, ((n : ℝ) + 1) * r ^ n = 1 / (1 - r) ^ 2 := by
  have h1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 (r := r) hr
  have h2 : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_norm_lt_one hr
  have h3 : ∑' n : ℕ, ((n : ℝ) * r ^ n + r ^ n)
      = r / (1 - r) ^ 2 + (1 - r)⁻¹ := by
    rw [Summable.tsum_add h1 h2, tsum_coe_mul_geometric_of_norm_lt_one hr,
      tsum_geometric_of_norm_lt_one hr]
  have hr1 : r ≠ 1 := by
    intro h; rw [h] at hr; simp at hr
  rw [show (∑' n : ℕ, ((n : ℝ) + 1) * r ^ n)
      = ∑' n : ℕ, ((n : ℝ) * r ^ n + r ^ n) from tsum_congr (fun n => by ring), h3]
  have hne : (1 - r) ≠ 0 := by
    intro h; exact hr1 (by linarith [sub_eq_zero.mp h])
  field_simp
  ring

/-- The local Euler factor differs from `1` by `O(p^{-re z})` in the half-plane `re z ≥ 1`. -/
lemma norm_heckeFp_sub_one_le {chi : GaussianInt → ℂ} {k : ℤ} {p : Nat.Primes}
    (h1 : chi 1 = 1) (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) {z : ℂ} (hz : 1 ≤ z.re) :
    ‖Work.FIArea5.S16Hecke.heckeFp chi k p z - 1‖
      ≤ 32 * (((p : ℕ) : ℝ) ^ (-z.re)) := by
  set t : ℝ := (((p : ℕ) : ℝ) ^ (-z.re)) with ht
  have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.pos
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by
    exact_mod_cast p.prop.one_le
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by
    exact_mod_cast p.prop.two_le
  have hz0 : 0 < z.re := lt_of_lt_of_le zero_lt_one hz
  have htpos : 0 < t := Real.rpow_pos_of_pos hppos _
  have htle : t ≤ 1 / 2 := by
    rw [ht]
    have hmono : (((p : ℕ) : ℝ) ^ (-z.re)) ≤ (((p : ℕ) : ℝ) ^ (-1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    have hinv : (((p : ℕ) : ℝ) ^ (-1 : ℝ)) = 1 / ((p : ℕ) : ℝ) := by
      rw [Real.rpow_neg_one, one_div]
    have h3 : (1 : ℝ) / ((p : ℕ) : ℝ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le (by norm_num) hp2
    calc (((p : ℕ) : ℝ) ^ (-z.re)) ≤ (((p : ℕ) : ℝ) ^ (-1 : ℝ)) := hmono
      _ = 1 / ((p : ℕ) : ℝ) := hinv
      _ ≤ 1 / 2 := h3
  have ht1 : t < 1 := by linarith
  have hnorm : ‖(((p : ℕ) : ℂ) ^ (-z))‖ = t := by
    rw [ht]; exact Work.FIArea5.S16Hecke.norm_cpow_neg p z
  have hzlt : ‖(((p : ℕ) : ℂ) ^ (-z))‖ < 1 := by rw [hnorm]; exact ht1
  have hsum : Summable (fun e : ℕ =>
      Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ e) * ((((p : ℕ) : ℂ) ^ (-z)) ^ e)) :=
    Work.FIArea5.S16Hecke.summable_heckeLam_pow_mul p.prop hb hzlt
  have hsplit : Work.FIArea5.S16Hecke.heckeFp chi k p z - 1 =
      ∑' e : ℕ, Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ (e + 1))
        * ((((p : ℕ) : ℂ) ^ (-z)) ^ (e + 1)) := by
    rw [Work.FIArea5.S16Hecke.heckeFp_eq_tsum, hsum.tsum_eq_zero_add]
    have h0 : Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ 0)
        * ((((p : ℕ) : ℂ) ^ (-z)) ^ 0) = 1 := by
      rw [pow_zero, pow_zero, mul_one, Work.FIArea5.S16Hecke.heckeLam_one, h1]
    rw [h0]
    ring
  rw [hsplit]
  have hbnd : ∀ e : ℕ, ‖Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ (e + 1))
      * ((((p : ℕ) : ℂ) ^ (-z)) ^ (e + 1))‖ ≤ 8 * ((e : ℝ) + 1) * t ^ (e + 1) := by
    intro e
    rw [norm_mul, norm_pow, hnorm]
    have hlam := Work.FIArea5.S16Hecke.heckeLam_pow_bound (chi := chi) (k := k) p.prop hb (e + 1)
    have htp : 0 ≤ t ^ (e + 1) := by positivity
    have hcast : ((e + 1 : ℕ) : ℝ) = (e : ℝ) + 1 := by push_cast; ring
    rw [hcast] at hlam
    calc ‖Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ (e + 1))‖ * t ^ (e + 1)
        ≤ (4 * ((e : ℝ) + 1 + 1)) * t ^ (e + 1) :=
          mul_le_mul_of_nonneg_right hlam htp
      _ ≤ 8 * ((e : ℝ) + 1) * t ^ (e + 1) := by
          have : (4 * ((e : ℝ) + 1 + 1)) ≤ 8 * ((e : ℝ) + 1) := by nlinarith [(Nat.cast_nonneg e : (0:ℝ) ≤ (e:ℝ))]
          exact mul_le_mul_of_nonneg_right this htp
  have htail : Summable (fun e : ℕ =>
      Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ (e + 1))
        * ((((p : ℕ) : ℂ) ^ (-z)) ^ (e + 1))) :=
    hsum.comp_injective (Nat.succ_injective)
  have hnormsumm : Summable (fun e : ℕ => ‖Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ (e + 1))
      * ((((p : ℕ) : ℂ) ^ (-z)) ^ (e + 1))‖) := htail.norm
  have hgsumm : Summable (fun e : ℕ => 8 * ((e : ℝ) + 1) * t ^ (e + 1)) := by
    have hb1 : Summable (fun e : ℕ => ((e : ℝ) + 1) * t ^ e) :=
      Work.FIArea5.S16Hecke.summable_nat_succ_mul_geo (by
        rw [Real.norm_eq_abs, abs_of_nonneg htpos.le]; exact ht1)
    have := hb1.mul_left (8 * t)
    refine this.congr (fun e => ?_)
    ring
  refine le_trans (norm_tsum_le_tsum_norm hnormsumm) ?_
  have hstep : ∑' e : ℕ, ‖Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ (e + 1))
      * ((((p : ℕ) : ℂ) ^ (-z)) ^ (e + 1))‖ ≤ ∑' e : ℕ, 8 * ((e : ℝ) + 1) * t ^ (e + 1) :=
    Summable.tsum_le_tsum hbnd hnormsumm hgsumm
  refine le_trans hstep ?_
  have hval : (∑' e : ℕ, 8 * ((e : ℝ) + 1) * t ^ (e + 1)) = 8 * t * (1 / (1 - t) ^ 2) := by
    rw [show (∑' e : ℕ, 8 * ((e : ℝ) + 1) * t ^ (e + 1))
        = ∑' e : ℕ, (8 * t) * (((e : ℝ) + 1) * t ^ e) from tsum_congr (fun e => by ring)]
    rw [tsum_mul_left, tsum_nat_succ_mul_geometric (by
      rw [Real.norm_eq_abs, abs_of_nonneg htpos.le]; exact ht1)]
  rw [hval]
  have hone : (1 : ℝ) / (1 - t) ^ 2 ≤ 4 := by
    have h1t : (1 : ℝ) / 2 ≤ 1 - t := by linarith
    have hsq : (1 / 2 : ℝ) ^ 2 ≤ (1 - t) ^ 2 := by
      apply pow_le_pow_left₀ (by norm_num) h1t
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hsq]
  have : 8 * t * (1 / (1 - t) ^ 2) ≤ 8 * t * 4 :=
    mul_le_mul_of_nonneg_left hone (by positivity)
  linarith

/-- `p^{-re z} ≤ 1/2` when `1 ≤ re z` and `p ≥ 2`. -/
lemma rpow_neg_re_le_half {p : Nat.Primes} {z : ℂ} (hz : 1 ≤ z.re) :
    (((p : ℕ) : ℝ) ^ (-z.re)) ≤ 1 / 2 := by
  have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.one_le
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  have hmono : (((p : ℕ) : ℝ) ^ (-z.re)) ≤ (((p : ℕ) : ℝ) ^ (-1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have hinv : (((p : ℕ) : ℝ) ^ (-1 : ℝ)) = 1 / ((p : ℕ) : ℝ) := by
    rw [Real.rpow_neg_one, one_div]
  have h3 : (1 : ℝ) / ((p : ℕ) : ℝ) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) hp2
  calc (((p : ℕ) : ℝ) ^ (-z.re)) ≤ (((p : ℕ) : ℝ) ^ (-1 : ℝ)) := hmono
    _ = 1 / ((p : ℕ) : ℝ) := hinv
    _ ≤ 1 / 2 := h3

/-- The derivative of `w ↦ (↑↑p : ℂ)^{-w}`. -/
lemma hasDerivAt_cpow_neg (p : Nat.Primes) (w : ℂ) :
    HasDerivAt (fun z : ℂ => (((p : ℕ) : ℂ) ^ (-z)))
      (-(((Real.log ((p : ℕ) : ℝ)) : ℂ) * (((p : ℕ) : ℂ) ^ (-w)))) w := by
  have hc : (((p : ℕ) : ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact p.prop.pos.ne'
  have hlog : Complex.log (((p : ℕ) : ℂ)) = ((Real.log ((p : ℕ) : ℝ) : ℂ)) := by
    rw [← Complex.ofReal_natCast, Complex.ofReal_log (Nat.cast_nonneg _)]
  have h := (hasDerivAt_neg w).const_cpow (Or.inl hc)
  rw [hlog] at h
  convert h using 1
  ring

/-- **The reciprocal local factor is differentiable, with an explicit derivative.** -/
lemma hasDerivAt_heckeGp {chi : GaussianInt → ℂ} {k : ℤ} {p : Nat.Primes} (z : ℂ) :
    HasDerivAt (Work.FIArea5.S16Hecke.heckeGp chi k p)
      (((Real.log ((p : ℕ) : ℝ)) : ℂ) * (((p : ℕ) : ℂ) ^ (-z))
        * (Work.FIArea5.S16Hecke.heckeLam chi k (p : ℕ)
           - 2 * (Work.FIArea5.S16Hecke.heckeLam chi k (p : ℕ) ^ 2
                  - Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ 2))
             * (((p : ℕ) : ℂ) ^ (-z)))) z := by
  have hT := hasDerivAt_cpow_neg p z
  have h1 : HasDerivAt
      (fun w : ℂ => 1 - Work.FIArea5.S16Hecke.heckeLam chi k (p : ℕ) * (((p : ℕ) : ℂ) ^ (-w)))
      (0 - Work.FIArea5.S16Hecke.heckeLam chi k (p : ℕ)
        * (-(((Real.log ((p : ℕ) : ℝ)) : ℂ) * (((p : ℕ) : ℂ) ^ (-z))))) z :=
    (hasDerivAt_const z 1).sub (hT.const_mul _)
  have hpow : ((((p : ℕ) : ℂ) ^ (-z)) ^ (2 - 1)) = (((p : ℕ) : ℂ) ^ (-z)) := by
    rw [show (2 : ℕ) - 1 = 1 from by norm_num, pow_one]
  have h2 : HasDerivAt
      (fun w : ℂ => (Work.FIArea5.S16Hecke.heckeLam chi k (p : ℕ) ^ 2
          - Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ 2)) * ((((p : ℕ) : ℂ) ^ (-w)) ^ 2))
      ((Work.FIArea5.S16Hecke.heckeLam chi k (p : ℕ) ^ 2
          - Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ 2))
        * ((2 : ℂ) * (((p : ℕ) : ℂ) ^ (-z))
            * (-(((Real.log ((p : ℕ) : ℝ)) : ℂ) * (((p : ℕ) : ℂ) ^ (-z)))))) z := by
    refine ((hT.pow 2).const_mul _).congr_deriv ?_
    rw [hpow]; ring
  refine (h1.add h2).congr_deriv ?_
  ring

/-- `heckeFp chi k p` is holomorphic on `re z > 1`. -/
lemma differentiableOn_heckeFp {chi : GaussianInt → ℂ} {k : ℤ} {p : Nat.Primes}
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    DifferentiableOn ℂ (Work.FIArea5.S16Hecke.heckeFp chi k p) {z : ℂ | 1 < z.re} := by
  have hc : (((p : ℕ) : ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact p.prop.pos.ne'
  have hdiff : ∀ e : ℕ, DifferentiableOn ℂ
      (fun w : ℂ => Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ e)
        * ((((p : ℕ) : ℂ) ^ (-w)) ^ e)) {z : ℂ | 1 < z.re} := by
    intro e
    have h1 : Differentiable ℂ (fun w : ℂ => (((p : ℕ) : ℂ) ^ (-w))) := by
      intro w
      exact (differentiableAt_id.neg).const_cpow (Or.inl hc)
    exact ((h1.pow e).const_mul _).differentiableOn
  have hu : Summable (fun e : ℕ => 4 * ((e : ℝ) + 1) * ((1 / 2 : ℝ) ^ e)) := by
    have h := Work.FIArea5.S16Hecke.summable_nat_succ_mul_geo (r := (1 / 2 : ℝ)) (by norm_num)
    have h2 := h.mul_left 4
    refine h2.congr (fun e => ?_)
    ring
  have hle : ∀ (e : ℕ) (w : ℂ), w ∈ {z : ℂ | 1 < z.re} →
      ‖Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ e) * ((((p : ℕ) : ℂ) ^ (-w)) ^ e)‖
        ≤ 4 * ((e : ℝ) + 1) * ((1 / 2 : ℝ) ^ e) := by
    intro e w hw
    rw [norm_mul, norm_pow, Work.FIArea5.S16Hecke.norm_cpow_neg]
    have hlam := Work.FIArea5.S16Hecke.heckeLam_pow_bound (chi := chi) (k := k) p.prop hb e
    have htle : (((p : ℕ) : ℝ) ^ (-w.re)) ≤ 1 / 2 := rpow_neg_re_le_half (le_of_lt hw)
    have hpow : ((((p : ℕ) : ℝ) ^ (-w.re)) ^ e) ≤ (1 / 2 : ℝ) ^ e :=
      pow_le_pow_left₀ (by positivity) htle e
    calc ‖Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ e)‖ * (((p : ℕ) : ℝ) ^ (-w.re)) ^ e
        ≤ (4 * ((e : ℝ) + 1)) * (1 / 2 : ℝ) ^ e :=
          mul_le_mul hlam hpow (by positivity) (by positivity)
      _ = 4 * ((e : ℝ) + 1) * (1 / 2 : ℝ) ^ e := by ring
  have h := Complex.differentiableOn_tsum_of_summable_norm
    (F := fun e w => Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ e)
      * ((((p : ℕ) : ℂ) ^ (-w)) ^ e))
    hu hdiff (isOpen_lt continuous_const Complex.continuous_re) hle
  refine h.congr (fun w _ => ?_)
  exact (Work.FIArea5.S16Hecke.heckeFp_eq_tsum chi k p w)

/-- The local Euler factor does not vanish on `re z > 0`. -/
lemma heckeFp_ne_zero {chi : GaussianInt → ℂ} {k : ℤ} {p : Nat.Primes}
    (h1 : chi 1 = 1) (hmul : ∀ a b : GaussianInt, chi (a * b) = chi a * chi b)
    (hb : ∀ a : GaussianInt, ‖chi a‖ ≤ 1) {z : ℂ} (hz : 0 < z.re) :
    Work.FIArea5.S16Hecke.heckeFp chi k p z ≠ 0 := by
  intro h0
  have h := Work.FIArea5.S16Hecke.heckeFp_mul_heckeGp chi k p z hmul h1 hb hz
  rw [h0, zero_mul] at h
  exact one_ne_zero h.symm

/-- The reciprocal local factor does not vanish on `re z > 0`. -/
lemma heckeGp_ne_zero {chi : GaussianInt → ℂ} {k : ℤ} {p : Nat.Primes}
    (h1 : chi 1 = 1) (hmul : ∀ a b : GaussianInt, chi (a * b) = chi a * chi b)
    (hb : ∀ a : GaussianInt, ‖chi a‖ ≤ 1) {z : ℂ} (hz : 0 < z.re) :
    Work.FIArea5.S16Hecke.heckeGp chi k p z ≠ 0 := by
  intro h0
  have h := Work.FIArea5.S16Hecke.heckeFp_mul_heckeGp chi k p z hmul h1 hb hz
  rw [h0, mul_zero] at h
  exact one_ne_zero h.symm

/-- `‖λ(p)‖ ≤ 2` for every prime `p`, from the two prime-case classifications. -/
lemma norm_heckeLam_prime_le_two {chi : GaussianInt → ℂ} {k : ℤ} {p : ℕ} (hp : p.Prime)
    (hb : ∀ a : GaussianInt, ‖chi a‖ ≤ 1) :
    ‖Work.FIArea5.S16Hecke.heckeLam chi k p‖ ≤ 2 := by
  by_cases h4 : p % 4 = 1
  · exact Work.FIArea5.S16Hecke.heckeLam_prime_norm_le_two hp h4 hb
  · rw [Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four hp h4, norm_zero]
    norm_num

/-- **Derivative bound for the reciprocal local factor.** -/
lemma norm_deriv_heckeGp_le {chi : GaussianInt → ℂ} {k : ℤ} {p : Nat.Primes}
    (hmul : ∀ a b : GaussianInt, chi (a * b) = chi a * chi b)
    (hb : ∀ a : GaussianInt, ‖chi a‖ ≤ 1) {z : ℂ} (hz : 1 ≤ z.re) :
    ‖deriv (Work.FIArea5.S16Hecke.heckeGp chi k p) z‖
      ≤ Real.log ((p : ℕ) : ℝ) * (2 * (((p : ℕ) : ℝ) ^ (-z.re))
          + 2 * ((((p : ℕ) : ℝ) ^ (-z.re)) ^ 2)) := by
  have hLnn : 0 ≤ Real.log ((p : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast p.prop.one_le)
  have ht0 : 0 ≤ (((p : ℕ) : ℝ) ^ (-z.re)) := by positivity
  have htle : (((p : ℕ) : ℝ) ^ (-z.re)) ≤ 1 / 2 := rpow_neg_re_le_half hz
  have hTn : ‖(((p : ℕ) : ℂ) ^ (-z))‖ = (((p : ℕ) : ℝ) ^ (-z.re)) :=
    Work.FIArea5.S16Hecke.norm_cpow_neg p z
  have hA : ‖Work.FIArea5.S16Hecke.heckeLam chi k (p : ℕ)‖ ≤ 2 :=
    norm_heckeLam_prime_le_two p.prop hb
  have hC : ‖Work.FIArea5.S16Hecke.heckeLam chi k (p : ℕ) ^ 2
      - Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ 2)‖ ≤ 1 :=
    (Work.FIArea5.S16Hecke.heckeLam_localRec chi k (p : ℕ) p.prop hmul hb).2
  rw [(hasDerivAt_heckeGp (chi := chi) (k := k) (p := p) z).deriv, norm_mul]
  have h1 : ‖((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-z))‖
      ≤ Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-z.re)) := by
    rw [norm_mul, hTn, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hLnn]
  have h2 : ‖Work.FIArea5.S16Hecke.heckeLam chi k (p : ℕ)
      - 2 * (Work.FIArea5.S16Hecke.heckeLam chi k (p : ℕ) ^ 2
          - Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ 2)) * (((p : ℕ) : ℂ) ^ (-z))‖
      ≤ 2 + 2 * (((p : ℕ) : ℝ) ^ (-z.re)) := by
    have hsub := norm_sub_le (Work.FIArea5.S16Hecke.heckeLam chi k (p : ℕ))
      (2 * (Work.FIArea5.S16Hecke.heckeLam chi k (p : ℕ) ^ 2
          - Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ 2)) * (((p : ℕ) : ℂ) ^ (-z)))
    have hnorm2 : ‖(2 : ℂ) * (Work.FIArea5.S16Hecke.heckeLam chi k (p : ℕ) ^ 2
        - Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ 2)) * (((p : ℕ) : ℂ) ^ (-z))‖
        = 2 * ‖Work.FIArea5.S16Hecke.heckeLam chi k (p : ℕ) ^ 2
            - Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ 2)‖ * (((p : ℕ) : ℝ) ^ (-z.re)) := by
      rw [norm_mul, norm_mul, hTn]
      norm_num
    rw [hnorm2] at hsub
    nlinarith [hsub, hA, hC, ht0, htle]
  calc ‖((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) * (((p : ℕ) : ℂ) ^ (-z))‖
        * ‖Work.FIArea5.S16Hecke.heckeLam chi k (p : ℕ)
          - 2 * (Work.FIArea5.S16Hecke.heckeLam chi k (p : ℕ) ^ 2
              - Work.FIArea5.S16Hecke.heckeLam chi k ((p : ℕ) ^ 2)) * (((p : ℕ) : ℂ) ^ (-z))‖
      ≤ (Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-z.re))) * (2 + 2 * (((p : ℕ) : ℝ) ^ (-z.re))) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = Real.log ((p : ℕ) : ℝ) * (2 * (((p : ℕ) : ℝ) ^ (-z.re))
          + 2 * ((((p : ℕ) : ℝ) ^ (-z.re)) ^ 2)) := by ring

/-- **Local logarithmic-derivative bound.** -/
lemma heckeFp_logDeriv_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (chi : GaussianInt → ℂ) (k : ℤ) (p : Nat.Primes) (z : ℂ),
      chi 1 = 1 → (∀ a b : GaussianInt, chi (a * b) = chi a * chi b) →
      (∀ a : GaussianInt, ‖chi a‖ ≤ 1) → 1 < z.re →
      ‖logDeriv (Work.FIArea5.S16Hecke.heckeFp chi k p) z‖
        ≤ C * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-z.re)) := by
  refine ⟨64, by norm_num, fun chi k p z h1 hmul hb hz => ?_⟩
  have hFG : Work.FIArea5.S16Hecke.heckeFp chi k p z
      * Work.FIArea5.S16Hecke.heckeGp chi k p z = 1 :=
    Work.FIArea5.S16Hecke.heckeFp_mul_heckeGp chi k p z hmul h1 hb (by linarith)
  have hFne : Work.FIArea5.S16Hecke.heckeFp chi k p z ≠ 0 :=
    heckeFp_ne_zero h1 hmul hb (by linarith)
  have hGne : Work.FIArea5.S16Hecke.heckeGp chi k p z ≠ 0 :=
    heckeGp_ne_zero h1 hmul hb (by linarith)
  have hFd : DifferentiableAt ℂ (Work.FIArea5.S16Hecke.heckeFp chi k p) z :=
    (differentiableOn_heckeFp (chi := chi) (k := k) (p := p) hb).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz)
  have hGd : DifferentiableAt ℂ (Work.FIArea5.S16Hecke.heckeGp chi k p) z :=
    (hasDerivAt_heckeGp (chi := chi) (k := k) (p := p) z).differentiableAt
  have hprod : deriv (Work.FIArea5.S16Hecke.heckeFp chi k p
      * Work.FIArea5.S16Hecke.heckeGp chi k p) z = 0 := by
    have hev : (Work.FIArea5.S16Hecke.heckeFp chi k p
        * Work.FIArea5.S16Hecke.heckeGp chi k p)
        =ᶠ[𝓝 z] (fun _ => (1 : ℂ)) := by
      refine Filter.eventually_of_mem
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by linarith : 0 < z.re)) ?_
      intro w hw
      exact Work.FIArea5.S16Hecke.heckeFp_mul_heckeGp chi k p w hmul h1 hb hw
    rw [hev.deriv_eq]
    simp
  rw [deriv_mul hFd hGd] at hprod
  have hkey : logDeriv (Work.FIArea5.S16Hecke.heckeFp chi k p) z
      = -(deriv (Work.FIArea5.S16Hecke.heckeGp chi k p) z)
        * (Work.FIArea5.S16Hecke.heckeFp chi k p z) := by
    have hGinv : ((Work.FIArea5.S16Hecke.heckeGp chi k p z)⁻¹)
        = Work.FIArea5.S16Hecke.heckeFp chi k p z :=
      inv_eq_of_mul_eq_one_left hFG
    have hdiv : deriv (Work.FIArea5.S16Hecke.heckeFp chi k p) z
        / Work.FIArea5.S16Hecke.heckeFp chi k p z
        = -(deriv (Work.FIArea5.S16Hecke.heckeGp chi k p) z)
          / (Work.FIArea5.S16Hecke.heckeGp chi k p z) := by
      rw [div_eq_div_iff hFne hGne]
      have h1 : deriv (Work.FIArea5.S16Hecke.heckeFp chi k p) z
          * Work.FIArea5.S16Hecke.heckeGp chi k p z
          = -(Work.FIArea5.S16Hecke.heckeFp chi k p z
              * deriv (Work.FIArea5.S16Hecke.heckeGp chi k p) z) := by
        rw [eq_neg_iff_add_eq_zero]
        exact hprod
      rw [h1]; ring
    rw [logDeriv_apply, hdiv, div_eq_mul_inv, hGinv]
  rw [hkey, norm_mul, norm_neg]
  have hdG := norm_deriv_heckeGp_le (chi := chi) (k := k) (p := p) hmul hb (le_of_lt hz)
  have hFn : ‖Work.FIArea5.S16Hecke.heckeFp chi k p z‖ ≤ 17 := by
    have hsub := norm_heckeFp_sub_one_le (chi := chi) (k := k) (p := p) h1 hb (le_of_lt hz)
    have h1' : ‖Work.FIArea5.S16Hecke.heckeFp chi k p z - 1‖ ≤ 16 := by
      have := rpow_neg_re_le_half (p := p) (z := z) (le_of_lt hz)
      linarith
    have h2 : ‖Work.FIArea5.S16Hecke.heckeFp chi k p z‖
        ≤ ‖Work.FIArea5.S16Hecke.heckeFp chi k p z - 1‖ + 1 := by
      have h3 := norm_add_le (Work.FIArea5.S16Hecke.heckeFp chi k p z - 1) 1
      have h4 : Work.FIArea5.S16Hecke.heckeFp chi k p z - 1 + 1
          = Work.FIArea5.S16Hecke.heckeFp chi k p z := by ring
      rw [h4] at h3
      simpa using h3
    linarith
  have hLnn : 0 ≤ Real.log ((p : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast p.prop.one_le)
  have ht0 : 0 ≤ (((p : ℕ) : ℝ) ^ (-z.re)) := by positivity
  have htle : (((p : ℕ) : ℝ) ^ (-z.re)) ≤ 1 / 2 := rpow_neg_re_le_half (le_of_lt hz)
  have hfin : (Real.log ((p : ℕ) : ℝ) * (2 * (((p : ℕ) : ℝ) ^ (-z.re))
        + 2 * ((((p : ℕ) : ℝ) ^ (-z.re)) ^ 2))) * 17
      ≤ 64 * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-z.re)) := by
    have hsq : ((((p : ℕ) : ℝ) ^ (-z.re)) ^ 2) ≤ (1 / 2) * (((p : ℕ) : ℝ) ^ (-z.re)) := by
      nlinarith [ht0, htle]
    have hb1 : (2 * (((p : ℕ) : ℝ) ^ (-z.re)) + 2 * ((((p : ℕ) : ℝ) ^ (-z.re)) ^ 2))
        ≤ 3 * (((p : ℕ) : ℝ) ^ (-z.re)) := by linarith
    have hb2 : Real.log ((p : ℕ) : ℝ) * (2 * (((p : ℕ) : ℝ) ^ (-z.re))
          + 2 * ((((p : ℕ) : ℝ) ^ (-z.re)) ^ 2))
        ≤ Real.log ((p : ℕ) : ℝ) * (3 * (((p : ℕ) : ℝ) ^ (-z.re))) :=
      mul_le_mul_of_nonneg_left hb1 hLnn
    calc (Real.log ((p : ℕ) : ℝ) * (2 * (((p : ℕ) : ℝ) ^ (-z.re))
            + 2 * ((((p : ℕ) : ℝ) ^ (-z.re)) ^ 2))) * 17
        ≤ (Real.log ((p : ℕ) : ℝ) * (3 * (((p : ℕ) : ℝ) ^ (-z.re)))) * 17 :=
          mul_le_mul_of_nonneg_right hb2 (by norm_num)
      _ = 51 * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-z.re)) := by ring
      _ ≤ 64 * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-z.re)) := by
          have hP : 0 ≤ Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-z.re)) := mul_nonneg hLnn ht0
          nlinarith [hP]
  calc ‖deriv (Work.FIArea5.S16Hecke.heckeGp chi k p) z‖
        * ‖Work.FIArea5.S16Hecke.heckeFp chi k p z‖
      ≤ (Real.log ((p : ℕ) : ℝ) * (2 * (((p : ℕ) : ℝ) ^ (-z.re))
            + 2 * ((((p : ℕ) : ℝ) ^ (-z.re)) ^ 2))) * 17 :=
        mul_le_mul hdG hFn (norm_nonneg _) (by positivity)
    _ ≤ 64 * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-z.re)) := hfin

/-- **The Euler product of the Hecke `L`-series converges locally uniformly on `re s > 1`.**  The net
of finite products `∏_{p ∈ b} heckeFp chi k p ·` (equivalently, the partial Euler products) converges
locally uniformly on `{z | 1 < z.re}` to `∏'_p heckeFp chi k p ·`, which is `heckeLSeries chi k` there. -/
theorem heckeFp_multipliableLocallyUniformlyOn (chi : GaussianInt → ℂ) (k : ℤ)
    (h1 : chi 1 = 1) (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    MultipliableLocallyUniformlyOn (fun p : Nat.Primes => Work.FIArea5.S16Hecke.heckeFp chi k p)
      {z : ℂ | 1 < z.re} := by
  refine MultipliableLocallyUniformlyOn_congr
    (f := fun p z => 1 + (Work.FIArea5.S16Hecke.heckeFp chi k p z - 1))
    (fun p => ?_) ?_
  · intro z _
    ring
  · refine multipliableLocallyUniformlyOn_of_of_forall_exists_nhds (fun x hx => ?_)
    have hx1 : 1 < x.re := hx
    set r : ℝ := (x.re - 1) / 4 with hr
    have hrpos : 0 < r := by rw [hr]; linarith
    have hK : Metric.closedBall x r ⊆ {z : ℂ | 1 < z.re} := by
      intro z hz
      show 1 < z.re
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      have h1 : |z.re - x.re| ≤ ‖z - x‖ := by simpa using Complex.abs_re_le_norm (z - x)
      have h2 : |z.re - x.re| ≤ r := le_trans h1 hz
      have h3 := (abs_le.mp h2).1
      rw [hr] at h3
      linarith
    refine ⟨Metric.closedBall x r, ?_, ?_⟩
    · rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      exact ⟨Metric.ball x r, Metric.ball_mem_nhds x hrpos,
        fun z hz => Metric.ball_subset_closedBall hz.1⟩
    · set σ₀ : ℝ := (3 * x.re + 1) / 4 with hσ
      have hσ1 : 1 < σ₀ := by rw [hσ]; linarith
      have hbound : ∀ z ∈ Metric.closedBall x r, σ₀ ≤ z.re := by
        intro z hz
        rw [Metric.mem_closedBall, dist_eq_norm] at hz
        have h1 : |z.re - x.re| ≤ ‖z - x‖ := by simpa using Complex.abs_re_le_norm (z - x)
        have h2 : |z.re - x.re| ≤ r := le_trans h1 hz
        have h3 := (abs_le.mp h2).1
        rw [hr] at h3; rw [hσ]; linarith
      have hu : Summable (fun p : Nat.Primes => 32 * (((p : ℕ) : ℝ) ^ (-σ₀))) :=
        (Nat.Primes.summable_rpow.mpr (by linarith)).mul_left 32
      refine Summable.multipliableUniformlyOn_one_add
        (K := Metric.closedBall x r) (isCompact_closedBall x r) hu ?_ ?_
      · filter_upwards with p
        intro z hz
        have hz1 : 1 ≤ z.re := le_trans (le_of_lt hσ1) (hbound z hz)
        have h := norm_heckeFp_sub_one_le (chi := chi) (k := k) (p := p) h1 hb hz1
        have hp1 : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.one_le
        have hle : (((p : ℕ) : ℝ) ^ (-z.re)) ≤ (((p : ℕ) : ℝ) ^ (-σ₀)) :=
          Real.rpow_le_rpow_of_exponent_le hp1 (by linarith [hbound z hz])
        have h32 : (0 : ℝ) ≤ 32 := by norm_num
        linarith [h, mul_le_mul_of_nonneg_left hle h32]
      · intro p
        exact ((differentiableOn_heckeFp (chi := chi) (k := k) (p := p) hb).mono hK).continuousOn.sub
          continuousOn_const


/-! ## The arithmetic input: `Σ_p (log p) p^{-σ} ≪ 1/(σ-1)` -/

/-- Summability of `Σ_p (log p) p^{-σ}` for `σ > 1`. -/
lemma summable_primes_log_mul_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes => Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-σ))) := by
  have h : Summable (fun n : {n : ℕ // n.Prime} =>
      (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ) :=
    (Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow hσ).subtype (fun n => n.Prime)
  refine h.congr (fun p => ?_)
  rw [ArithmeticFunction.vonMangoldt_apply_prime p.2, Real.rpow_neg (Nat.cast_nonneg (p : ℕ)),
    div_eq_mul_inv]

/-- The von Mangoldt series at a real point `σ > 1` equals `-Re(ζ'/ζ)(σ)`. -/
lemma tsum_vonMangoldt_div_eq_zeta_re (σ : ℝ) (hσ : 1 < σ) :
    (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ)
      = (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re := by
  have hsumm : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using hσ)
  have hζid := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := (σ : ℂ)) (by simpa using hσ)
  rw [← hζid, LSeries, Complex.re_tsum hsumm]
  refine tsum_congr (fun n => ?_)
  rw [LSeries.term_def]
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow (Nat.cast_nonneg n) σ,
      ← Complex.ofReal_div, Complex.ofReal_re]

/-- **`Σ_p (log p) p^{-σ} = O(1/(σ-1))` for `1 < σ ≤ 2`.** -/
lemma sum_primes_log_mul_rpow_le :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (∑' p : Nat.Primes, Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-σ))) ≤ C / (σ - 1) := by
  obtain ⟨Cz, hCzpos, hz⟩ := Commons.NumberTheory.Zeta.zeta_logDeriv_re_axis_bound
  refine ⟨Cz + 1, by linarith, fun σ hσ hσ2 => ?_⟩
  have hFsumm : Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ) :=
    Commons.NumberTheory.Zeta.summable_vonMangoldt_div_rpow hσ
  have h1 : (∑' p : Nat.Primes, Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-σ)))
      = ∑' n : {n : ℕ // n.Prime},
          (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ := by
    refine tsum_congr (fun p => ?_)
    rw [ArithmeticFunction.vonMangoldt_apply_prime p.2,
      Real.rpow_neg (Nat.cast_nonneg (p : ℕ)), div_eq_mul_inv]
  rw [h1]
  have hsplit := hFsumm.tsum_subtype_add_tsum_subtype_compl {n : ℕ | n.Prime}
  have hnn : 0 ≤ ∑' n : {n : ℕ // ¬ n.Prime},
      (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ :=
    tsum_nonneg (fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity))
  have h2 : (∑' n : {n : ℕ // n.Prime},
        (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ)
      ≤ ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ :=
    calc (∑' n : {n : ℕ // n.Prime},
          (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ)
        ≤ (∑' n : {n : ℕ // n.Prime},
              (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ)
            + (∑' n : {n : ℕ // ¬ n.Prime},
                (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ) :=
          le_add_of_nonneg_right hnn
      _ = ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ := hsplit
  refine le_trans h2 ?_
  rw [tsum_vonMangoldt_div_eq_zeta_re σ hσ]
  have h4 := hz σ hσ hσ2
  have h5 : (1 : ℝ) / (σ - 1) + Cz ≤ (Cz + 1) / (σ - 1) := by
    have hσ1 : (0 : ℝ) < σ - 1 := by linarith
    rw [le_div_iff₀ hσ1, add_mul, div_mul_cancel₀ (1 : ℝ) (ne_of_gt hσ1)]
    nlinarith [hCzpos, hσ2]
  linarith

/-! ## The main theorem -/

theorem heckeLval_logDeriv_norm_le_of_one_lt_re :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (chi : GaussianInt → ℂ) (m : ℤ) (Lam : ℂ → ℂ), 1 ≤ d →
        Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi →
        AnalyticOn ℂ Lam Set.univ →
        (∀ s : ℂ, 1 + |(m : ℝ)| / 2 < s.re →
          Lam s = Work.FITop4.Bridge.heckeArch d m s *
            Work.FIArea5.S16Hecke.heckeLSeries chi m s) →
        ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
          ‖deriv (Work.FIArea6Hecke.Lval d m Lam) s / Work.FIArea6Hecke.Lval d m Lam s‖
            ≤ C * (1 / (s.re - 1) + Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3))) := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := heckeFp_logDeriv_bound
  obtain ⟨C₃, hC₃pos, hC₃⟩ := sum_primes_log_mul_rpow_le
  refine ⟨C₂ * C₃, by positivity, ?_⟩
  intro d chi m Lam hd hchi hAn hagr s hs1 hs2
  obtain ⟨h1, hmul, hb, -, -⟩ := hchi.1
  -- 1. the `L`-value attached to `Lam` is the `L`-series near `s`
  have hLval : Work.FIArea6Hecke.Lval d m Lam =ᶠ[𝓝 s]
      Work.FIArea5.S16Hecke.heckeLSeries chi m := by
    refine Filter.eventually_of_mem
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs1) (fun z hz => ?_)
    rw [Work.FIArea6Hecke.Lval, Lam_eq_heckeArch_mul_of_one_lt_re hd hAn hb hagr hz]
    exact mul_div_cancel_left₀ _ (heckeArch_ne_zero_of_one_lt_re hd m hz)
  have hcongr : logDeriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s
      = logDeriv (Work.FIArea6Hecke.Lval d m Lam) s :=
    (logDeriv_congr_nhds hLval).eq_of_nhds.symm
  -- 2. the Euler product identity for the logarithmic derivative
  have hdiff : ∀ p : Nat.Primes, DifferentiableOn ℂ (Work.FIArea5.S16Hecke.heckeFp chi m p)
      {z : ℂ | 1 < z.re} :=
    fun p => differentiableOn_heckeFp (chi := chi) (k := m) (p := p) hb
  have hne : ∀ p : Nat.Primes, Work.FIArea5.S16Hecke.heckeFp chi m p s ≠ 0 :=
    fun p => heckeFp_ne_zero h1 hmul hb (by linarith)
  have hsummC : Summable (fun p : Nat.Primes =>
      C₂ * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re))) := by
    have h := (summable_primes_log_mul_rpow hs1).mul_left C₂
    refine h.congr (fun p => ?_)
    ring
  have hsumm : Summable (fun p : Nat.Primes =>
      logDeriv (Work.FIArea5.S16Hecke.heckeFp chi m p) s) :=
    Summable.of_norm_bounded hsummC (fun p => hC₂ chi m p s h1 hmul hb hs1)
  have hnez : (∏' p : Nat.Primes, Work.FIArea5.S16Hecke.heckeFp chi m p s) ≠ 0 := by
    have hL : (∏' p : Nat.Primes, Work.FIArea5.S16Hecke.heckeFp chi m p s)
        = Work.FIArea5.S16Hecke.heckeLSeries chi m s :=
      (Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct_hasProd chi m h1 hmul hb hs1).tprod_eq
    rw [hL]
    exact Work.FIArea5.S16Hecke.heckeLSeries_ne_zero_of_one_lt_re chi m h1 hmul hb hs1
  have hkey := logDeriv_tprod_eq_tsum (s := {z : ℂ | 1 < z.re})
    (f := fun p : Nat.Primes => Work.FIArea5.S16Hecke.heckeFp chi m p)
    (isOpen_lt continuous_const Complex.continuous_re) hs1 hne hdiff hsumm
    (heckeFp_multipliableLocallyUniformlyOn chi m h1 hmul hb) hnez
  have hprod_eq : (fun z : ℂ => ∏' p : Nat.Primes, Work.FIArea5.S16Hecke.heckeFp chi m p z)
      =ᶠ[𝓝 s] Work.FIArea5.S16Hecke.heckeLSeries chi m := by
    refine Filter.eventually_of_mem
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs1) (fun z hz => ?_)
    exact (Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct_hasProd chi m h1 hmul hb hz).tprod_eq
  have hkey2 : logDeriv (Work.FIArea5.S16Hecke.heckeLSeries chi m) s
      = ∑' p : Nat.Primes, logDeriv (Work.FIArea5.S16Hecke.heckeFp chi m p) s := by
    rw [← (logDeriv_congr_nhds hprod_eq).eq_of_nhds, hkey]
  -- 3. the bound
  rw [← logDeriv_apply, ← hcongr, hkey2]
  have hstep1 : ‖∑' p : Nat.Primes, logDeriv (Work.FIArea5.S16Hecke.heckeFp chi m p) s‖
      ≤ ∑' p : Nat.Primes, ‖logDeriv (Work.FIArea5.S16Hecke.heckeFp chi m p) s‖ :=
    norm_tsum_le_tsum_norm hsumm.norm
  have hstep2 : (∑' p : Nat.Primes, ‖logDeriv (Work.FIArea5.S16Hecke.heckeFp chi m p) s‖)
      ≤ ∑' p : Nat.Primes, C₂ * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re)) :=
    Summable.tsum_le_tsum (fun p => hC₂ chi m p s h1 hmul hb hs1) hsumm.norm hsummC
  have hstep3 : (∑' p : Nat.Primes, C₂ * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re)))
      = C₂ * ∑' p : Nat.Primes, Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re)) := by
    rw [show (∑' p : Nat.Primes, C₂ * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re)))
        = ∑' p : Nat.Primes,
            C₂ * (Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re))) from
          tsum_congr (fun p => by ring), tsum_mul_left]
  have hstep4 : (∑' p : Nat.Primes, Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re)))
      ≤ C₃ / (s.re - 1) := hC₃ s.re hs1 hs2
  have hlog0 : 0 ≤ Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) := by
    refine Real.log_nonneg ?_
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have hm0 : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
    have ht0 : (0 : ℝ) ≤ |s.im| := abs_nonneg _
    nlinarith
  calc ‖∑' p : Nat.Primes, logDeriv (Work.FIArea5.S16Hecke.heckeFp chi m p) s‖
      ≤ ∑' p : Nat.Primes, ‖logDeriv (Work.FIArea5.S16Hecke.heckeFp chi m p) s‖ := hstep1
    _ ≤ ∑' p : Nat.Primes, C₂ * Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re)) := hstep2
    _ = C₂ * ∑' p : Nat.Primes,
          Real.log ((p : ℕ) : ℝ) * (((p : ℕ) : ℝ) ^ (-s.re)) := hstep3
    _ ≤ C₂ * (C₃ / (s.re - 1)) := mul_le_mul_of_nonneg_left hstep4 hC₂pos.le
    _ ≤ C₂ * C₃ * (1 / (s.re - 1) + Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3))) := by
        have hle : 1 / (s.re - 1)
            ≤ 1 / (s.re - 1) + Real.log (4 * (d : ℝ) * (|(m : ℝ)| + |s.im| + 3)) :=
          le_add_of_nonneg_right hlog0
        have heq : C₂ * (C₃ / (s.re - 1)) = C₂ * C₃ * (1 / (s.re - 1)) := by ring
        rw [heq]
        exact mul_le_mul_of_nonneg_left hle (by positivity)

end

end Work.FIArea6Hecke.R
