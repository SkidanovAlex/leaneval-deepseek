import Mathlib
import Submission.Commons.NumberTheory.Sieve.moebius_rough_recip_abs_le_two
import Submission.Commons.Analysis.Complex.exists_perron_formula_bound
import Submission.Commons.NumberTheory.LSeries.LSeries_rough_moebius_eq
import Submission.Commons.NumberTheory.Sieve.prod_primes_below_one_sub_cpow_inv_bound
import Submission.Commons.NumberTheory.LSeries.exists_zero_free_region_riemannZeta_log
import Submission.Commons.NumberTheory.Zeta.zeta_zeroFree_compact_width
import Submission.Commons.NumberTheory.Zeta.inv_zeta_le_log_zeroFree
import Submission.Commons.Analysis.ExpLog.case_A_arith
import Submission.Commons.Analysis.ExpLog.case_B_arith
import Submission.Commons.NumberTheory.Moebius.recip_perron_error_sum_le

/-!
# The reciprocal Möbius sum over `z`-rough numbers

Development of the analytic bound
`|∑_{n ≤ w, P⁻(n) ≥ z} μ(n)/n| ≤ C (z^{-c} + exp(-log w/log z) (log z)^6)`
via the truncated Perron formula and a contour shift.
-/

namespace Commons.NumberTheory.Sieve

set_option maxHeartbeats 1000000

attribute [local instance] Classical.propDecidable

open Finset
open scoped BigOperators

/-- `n` is `z`-rough when all its prime factors are `≥ z`. -/
def Rough (z : ℝ) (n : ℕ) : Prop := ∀ p : ℕ, p ∈ n.primeFactors → z ≤ (p : ℝ)

/-- `n` is `z`-smooth when all its prime factors are `< z`. -/
def Smooth (z : ℝ) (n : ℕ) : Prop := ∀ p : ℕ, p ∈ n.primeFactors → (p : ℝ) < z

lemma rough_one (z : ℝ) : Rough z 1 := by simp [Rough]

lemma smooth_one (z : ℝ) : Smooth z 1 := by simp [Smooth]

lemma rough_zero (z : ℝ) : Rough z 0 := by simp [Rough]

lemma rough_mul {z : ℝ} {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    Rough z (m * n) ↔ Rough z m ∧ Rough z n := by
  rw [Rough, Rough, Rough, Nat.primeFactors_mul hm hn]
  constructor
  · intro hpr
    exact ⟨fun p hp => hpr p (Finset.mem_union_left _ hp),
      fun p hp => hpr p (Finset.mem_union_right _ hp)⟩
  · rintro ⟨hm', hn'⟩ p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact hm' p hp
    · exact hn' p hp

/-- The finite product `∏_{p < z} (1 - p^{-u})⁻¹` over the primes below `z`. -/
noncomputable def Pz (z : ℝ) (u : ℂ) : ℂ :=
  ∏ p ∈ Nat.primesBelow ⌈z⌉₊, (1 - (p : ℂ) ^ (-u))⁻¹

/-- The Perron integrand `x^s ∏_{p<z}(1-p^{-(1+s)})⁻¹ / ζ₁(1+s)`. -/
noncomputable def Gfun (x z : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ s * Pz z (1 + s) / riemannZeta₁ (1 + s)

lemma norm_cpow_nat_neg (p : ℕ) {u : ℂ} (hp : p ≠ 0) : ‖(p : ℂ) ^ (-u)‖ = (p : ℝ) ^ (-u.re) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hp
  have hcast : ((p : ℕ) : ℂ) = (((p : ℕ) : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hp0, Complex.neg_re]

lemma one_sub_cpow_ne_zero {p : ℕ} (hp : 2 ≤ p) {u : ℂ} (hu : 0 < u.re) :
    (1 : ℂ) - (p : ℂ) ^ (-u) ≠ 0 := by
  intro h
  have hp0 : p ≠ 0 := by omega
  have hpow : (p : ℂ) ^ (-u) = 1 := (sub_eq_zero.mp h).symm
  have hnorm := norm_cpow_nat_neg p (u := u) hp0
  have hlt : (p : ℝ) ^ (-u.re) < 1 := by
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
    have hneg : -u.re < 0 := by linarith
    calc (p : ℝ) ^ (-u.re) < (p : ℝ) ^ (0 : ℝ) :=
          Real.rpow_lt_rpow_of_exponent_lt hp1 hneg
      _ = 1 := Real.rpow_zero _
  rw [hpow, norm_one, hnorm] at *
  linarith

lemma differentiableAt_cpow_neg {p : ℕ} (hp : p ≠ 0) (u₀ : ℂ) :
    DifferentiableAt ℂ (fun u : ℂ => (p : ℂ) ^ (-u)) u₀ := by
  have hp0 : (p : ℂ) ≠ 0 := by
    exact_mod_cast hp
  have hfun : (fun u : ℂ => (p : ℂ) ^ (-u))
      = fun u : ℂ => Complex.exp ((-u) * Complex.log (p : ℂ)) := by
    funext u
    rw [Complex.cpow_def_of_ne_zero hp0]
    ring_nf
  rw [hfun]
  exact (differentiableAt_id.neg.mul_const _).cexp

lemma differentiableAt_prod_primes (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p) {u : ℂ}
    (hu : 0 < u.re) :
    DifferentiableAt ℂ (fun v : ℂ => ∏ p ∈ S, (1 - (p : ℂ) ^ (-v))⁻¹) u := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert p S hp ih =>
    have hfun : (fun v : ℂ => ∏ p ∈ insert p S, (1 - (p : ℂ) ^ (-v))⁻¹)
        = fun v : ℂ => (1 - (p : ℂ) ^ (-v))⁻¹ * ∏ q ∈ S, (1 - (q : ℂ) ^ (-v))⁻¹ := by
      funext v
      rw [Finset.prod_insert hp]
    rw [hfun]
    have hp2 : 2 ≤ p := (hS p (Finset.mem_insert_self p S)).two_le
    have hp0 : p ≠ 0 := by omega
    have hne : (1 : ℂ) - (p : ℂ) ^ (-u) ≠ 0 := one_sub_cpow_ne_zero hp2 hu
    exact (((differentiableAt_const (1:ℂ)).sub (differentiableAt_cpow_neg hp0 u)).inv hne).mul
      (ih (fun q hq => hS q (Finset.mem_insert_of_mem hq)))

lemma differentiableAt_Pz (z : ℝ) {u : ℂ} (hu : 0 < u.re) :
    DifferentiableAt ℂ (Pz z) u := by
  unfold Pz
  exact differentiableAt_prod_primes _ (fun p hp => Nat.prime_of_mem_primesBelow hp) hu

lemma re_add_im_eq (w : ℂ) : ((w.re : ℂ) + (w.im : ℂ) * Complex.I) = w := by
  apply Complex.ext <;> simp

lemma differentiableAt_cpow_const {x : ℝ} (hx : 0 < x) (s₀ : ℂ) :
    DifferentiableAt ℂ (fun t : ℂ => (x : ℂ) ^ t) s₀ := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hfun : (fun t : ℂ => (x : ℂ) ^ t) = fun t : ℂ => Complex.exp (t * Complex.log (x : ℂ)) := by
    funext t
    rw [Complex.cpow_def_of_ne_zero hx0, mul_comm]
  rw [hfun]
  exact (differentiableAt_id.mul_const _).cexp

lemma differentiableAt_Gfun {x z : ℝ} (hx : 0 < x) {s : ℂ} (hs : -1 < s.re)
    (hz : riemannZeta₁ (1 + s) ≠ 0) : DifferentiableAt ℂ (Gfun x z) s := by
  unfold Gfun
  have h1 : DifferentiableAt ℂ (fun t : ℂ => (x : ℂ) ^ t) s := differentiableAt_cpow_const hx s
  have h2 : DifferentiableAt ℂ (fun t : ℂ => Pz z (1 + t)) s := by
    refine (differentiableAt_Pz z ?_).comp s ?_
    · simp only [Complex.add_re, Complex.one_re]; linarith
    · exact differentiableAt_const 1 |>.add differentiableAt_id
  have h3 : DifferentiableAt ℂ (fun t : ℂ => riemannZeta₁ (1 + t)) s :=
    differentiable_riemannZeta₁.differentiableAt.comp s
      (differentiableAt_const 1 |>.add differentiableAt_id)
  exact (h1.mul h2).div h3 hz

lemma riemannZeta₁_ne_zero {u : ℂ} (hu1 : u ≠ 1) (hζ : riemannZeta u ≠ 0) :
    riemannZeta₁ u ≠ 0 := by
  intro h
  refine hζ ?_
  rw [riemannZeta_eq_inv_sub_mul hu1, h, mul_zero]

/-- `ζ₁(1+s) ≠ 0` on a rectangle whose projection avoids the zero-free region of `ζ`. -/
lemma zeta1_ne_zero_of_rect {δ c T c0 : ℝ} (hc0 : 0 < c0)
    (hZFbig : ∀ σ t : ℝ, 2 ≤ |t| → 1 - c0 / Real.log (|t| + 2) ≤ σ →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hZFsmall : ∀ σ t : ℝ, |t| ≤ 4 → 1 - c0 ≤ σ → σ ≤ 2 →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    {s : ℂ} (hs1 : -δ ≤ s.re) (hs2 : s.re ≤ c) (hδ0 : 0 < δ) (hδc0 : δ ≤ c0)
    (hc2 : c ≤ 1) (hδlog : δ * Real.log (T + 2) ≤ c0) (hsim : |s.im| ≤ T) :
    riemannZeta₁ (1 + s) ≠ 0 := by
  by_cases hs0 : (1 : ℂ) + s = 1
  · rw [hs0, riemannZeta₁_one]; norm_num
  · intro hzero
    have him : (1 + s).im = s.im := by simp
    have hre : (1 + s).re = 1 + s.re := by simp
    have hzeta : riemannZeta ((1 + s).re + (s.im : ℂ) * Complex.I) = 0 := by
      have hz1 : riemannZeta (1 + s) = 0 := by
        rw [riemannZeta_eq_inv_sub_mul hs0, hzero, mul_zero]
      have harg : (1 + s) = ((1 + s).re + (s.im : ℂ) * Complex.I) := by
        apply Complex.ext
        · simp
        · simp [him]
      rwa [harg] at hz1
    by_cases him4 : |s.im| ≤ 4
    · have h1 : 1 - c0 ≤ (1 + s).re := by rw [hre]; linarith
      have h2 : (1 + s).re ≤ 2 := by rw [hre]; linarith
      exact hZFsmall (1 + s).re s.im him4 h1 h2 hzeta
    · have him2 : 2 ≤ |s.im| := by
        have h4 : (4 : ℝ) < |s.im| := not_le.mp him4
        linarith
      have hlogpos : 0 < Real.log (|s.im| + 2) := Real.log_pos (by linarith [abs_nonneg s.im])
      have hlogle : Real.log (|s.im| + 2) ≤ Real.log (T + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have hδle : δ ≤ c0 / Real.log (|s.im| + 2) := by
        rw [le_div_iff₀ hlogpos]
        calc δ * Real.log (|s.im| + 2) ≤ δ * Real.log (T + 2) :=
              mul_le_mul_of_nonneg_left hlogle (le_of_lt hδ0)
          _ ≤ c0 := hδlog
      have h1 : 1 - c0 / Real.log (|s.im| + 2) ≤ (1 + s).re := by
        rw [hre]; linarith
      exact hZFbig (1 + s).re s.im him2 h1 hzeta

lemma exists_riemannZeta₁_inv_le_two_near_one :
    ∃ r : ℝ, 0 < r ∧ ∀ s : ℂ, ‖s‖ ≤ r → ‖(riemannZeta₁ (1 + s))⁻¹‖ ≤ 2 := by
  have hcont : ContinuousAt (fun s : ℂ => riemannZeta₁ ((1:ℂ) + s)) 0 := by
    have h : ContinuousAt (fun s : ℂ => (1:ℂ) + s) 0 := continuousAt_const.add continuousAt_id
    exact differentiable_riemannZeta₁.continuous.continuousAt.comp h
  have hval : riemannZeta₁ ((1:ℂ) + 0) = 1 := by simpa using riemannZeta₁_one
  obtain ⟨r, hr0, hr⟩ := Metric.continuousAt_iff.mp hcont (1/2) (by norm_num)
  refine ⟨r/2, by positivity, fun s hs => ?_⟩
  have h1 : dist (riemannZeta₁ ((1:ℂ) + s)) 1 < 1/2 := by
    have : ‖s‖ < r := by linarith
    have := hr (x := s) (by simpa using this)
    simpa [hval] using this
  rw [dist_eq_norm] at h1
  have h2 : (1:ℝ)/2 ≤ ‖riemannZeta₁ ((1:ℂ) + s)‖ := by
    have h3 := abs_norm_sub_norm_le (riemannZeta₁ ((1:ℂ) + s)) 1
    rw [norm_one] at h3
    have h4 : |‖riemannZeta₁ ((1:ℂ) + s)‖ - 1| < 1/2 := lt_of_le_of_lt h3 h1
    rw [abs_lt] at h4
    linarith [h4.2]
  rw [norm_inv]
  exact inv_le_of_inv_le₀ (by norm_num : (0:ℝ) < 2) (by linarith)

/-- Cauchy's theorem on an axis-parallel rectangle, in the `(right) = (left) + (top - bottom)/I`
form. -/
lemma rect_boundary_identity {f : ℂ → ℂ} {zl wl : ℂ}
    (hdiff : DifferentiableOn ℂ f (Set.uIcc zl.re wl.re ×ℂ Set.uIcc zl.im wl.im)) :
    (∫ y in zl.im..wl.im, f (wl.re + (y : ℂ) * Complex.I))
      = (∫ y in zl.im..wl.im, f (zl.re + (y : ℂ) * Complex.I))
        + ((∫ x in zl.re..wl.re, f ((x : ℂ) + (wl.im : ℂ) * Complex.I))
            - (∫ x in zl.re..wl.re, f ((x : ℂ) + (zl.im : ℂ) * Complex.I))) / Complex.I := by
  set A := ∫ x in zl.re..wl.re, f ((x : ℂ) + (zl.im : ℂ) * Complex.I) with hA
  set B := ∫ x in zl.re..wl.re, f ((x : ℂ) + (wl.im : ℂ) * Complex.I) with hB
  set C := ∫ y in zl.im..wl.im, f ((wl.re : ℂ) + (y : ℂ) * Complex.I) with hC
  set D := ∫ y in zl.im..wl.im, f ((zl.re : ℂ) + (y : ℂ) * Complex.I) with hD
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f zl wl hdiff
  simp only [smul_eq_mul] at h
  rw [← hA, ← hB, ← hC, ← hD] at h
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have h' : (Complex.I * C - Complex.I * D) + (A - B) = 0 := by
    rw [← h]; ring
  have h2 : Complex.I * C - Complex.I * D = B - A := by
    have h4 : Complex.I * C - Complex.I * D = -(A - B) := eq_neg_iff_add_eq_zero.mpr h'
    rw [h4]; ring
  have h3 : C - D = (B - A) / Complex.I := by
    rw [eq_div_iff hI, mul_comm, mul_sub]
    exact h2
  rw [← h3]
  ring

/-- The Dirichlet coefficients `μ(n)·1_{n rough}/n`. -/
noncomputable def aperron (z : ℝ) (n : ℕ) : ℂ := by
  classical
  exact (ArithmeticFunction.moebius n : ℂ) * (if Rough z n then 1 else 0) / (n : ℂ)

/-- The (rough part of the) Möbius function. -/
noncomputable def muRough (z : ℝ) (n : ℕ) : ℂ := by
  classical
  exact (ArithmeticFunction.moebius n : ℂ) * (if Rough z n then 1 else 0)

lemma LSeries_muRough_eq (z : ℝ) (hz : 0 ≤ z) {u : ℂ} (hu : 1 < u.re) :
    LSeries (muRough z) u = (riemannZeta u)⁻¹ * Pz z u := by
  have h1 : LSeries (muRough z) u = LSeries (fun n => (ArithmeticFunction.moebius n : ℂ) *
      (if ∀ p : ℕ, p ∈ n.primeFactors → z ≤ (p : ℝ) then 1 else 0)) u := by
    refine LSeries_congr ?_ u
    intro n hn
    unfold muRough Rough
    by_cases h : ∀ p : ℕ, p ∈ n.primeFactors → z ≤ (p : ℝ)
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
  rw [h1, Commons.NumberTheory.LSeries.LSeries_rough_moebius_eq z hz hu]
  unfold Pz
  rfl

lemma LSeries_aperron_eq_muRough (z : ℝ) (s : ℂ) :
    LSeries (aperron z) s = LSeries (muRough z) (1 + s) := by
  classical
  rw [LSeries, LSeries]
  refine tsum_congr (fun n => ?_)
  by_cases hn : n = 0
  · subst hn
    simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have hx : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    unfold aperron muRough
    rw [Complex.cpow_add (1:ℂ) s hx, Complex.cpow_one]
    field_simp

/-- The Dirichlet series of `μ` over `z`-rough numbers, continued to `Re s > 0`. -/
lemma LSeries_aperron_eq {z : ℝ} (hz : 0 ≤ z) {s : ℂ} (hs : 0 < s.re) :
    LSeries (aperron z) s = s / riemannZeta₁ (1 + s) * Pz z (1 + s) := by
  rw [LSeries_aperron_eq_muRough,
    LSeries_muRough_eq z hz (by simp only [Complex.add_re, Complex.one_re]; linarith)]
  have hs1 : (1 : ℂ) + s ≠ 1 := by
    intro h
    have h0 : s = 0 := by linear_combination h
    rw [h0] at hs
    simp at hs
  have hζ : (riemannZeta (1 + s))⁻¹ = ((1 : ℂ) + s - 1) * (riemannZeta₁ (1 + s))⁻¹ := by
    rw [riemannZeta_eq_inv_sub_mul hs1, mul_inv_rev, inv_inv]
    ring
  rw [hζ]
  rw [show ((1 : ℂ) + s - 1) = s by ring]
  rw [div_eq_mul_inv]

lemma Gfun_eq (x z : ℝ) {s : ℂ} (hs : s ≠ 0) :
    (s / riemannZeta₁ (1 + s) * Pz z (1 + s)) * (x : ℂ) ^ s / s = Gfun x z s := by
  unfold Gfun
  rw [div_eq_mul_inv, div_eq_mul_inv]
  field_simp

lemma norm_aperron_le (z : ℝ) {n : ℕ} (hn : n ≠ 0) : ‖aperron z n‖ ≤ 1 / (n : ℝ) := by
  classical
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hmu : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast, ← Int.cast_abs, ArithmeticFunction.abs_moebius]
    split <;> norm_num
  have hind : ‖(if Rough z n then (1:ℂ) else 0)‖ ≤ 1 := by
    split
    · simp
    · simp
  unfold aperron
  rw [norm_div, norm_mul, Complex.norm_natCast]
  refine div_le_div_of_nonneg_right ?_ hnpos.le
  calc ‖(ArithmeticFunction.moebius n : ℂ)‖ * ‖(if Rough z n then (1:ℂ) else 0)‖
      ≤ 1 * 1 := mul_le_mul hmu hind (norm_nonneg _) zero_le_one
    _ = 1 := mul_one 1

lemma summable_aperron (z : ℝ) {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => ‖aperron z n‖ / (n : ℝ) ^ c) := by
  have hmaj : Summable (fun n : ℕ => (1:ℝ) / (n:ℝ)^(1+c)) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith : 1 < 1 + c)
  refine Summable.of_nonneg_of_le (f := fun n : ℕ => (1:ℝ) / (n:ℝ)^(1+c))
    (fun n => by positivity) (fun n => ?_) hmaj
  by_cases hn : n = 0
  · subst hn
    have h0 : aperron z 0 = 0 := by unfold aperron; simp
    rw [h0, norm_zero, Nat.cast_zero]
    simp [Real.zero_rpow hc.ne', Real.zero_rpow (by linarith : (1:ℝ) + c ≠ 0)]
  · have h1 : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have h2 : (0:ℝ) < (n:ℝ)^c := Real.rpow_pos_of_pos h1 c
    calc ‖aperron z n‖ / (n:ℝ)^c ≤ (1/(n:ℝ)) / (n:ℝ)^c :=
          div_le_div_of_nonneg_right (norm_aperron_le z hn) h2.le
      _ = 1 / ((n:ℝ) * (n:ℝ)^c) := by rw [div_div]
      _ = 1 / (n:ℝ)^(1+c) := by
          congr 1
          rw [Real.rpow_add h1, Real.rpow_one]

/-- Pointwise identification of the Perron integrand with `Gfun`. -/
lemma perron_integrand_eq {x z : ℝ} (hx : 0 < x) (hz : 0 ≤ z) {c t : ℝ} (hc : 0 < c) :
    LSeries (aperron z) ((c : ℂ) + (t : ℂ) * Complex.I)
        * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I) / ((c : ℂ) + (t : ℂ) * Complex.I)
      = Gfun x z ((c : ℂ) + (t : ℂ) * Complex.I) := by
  have hs : 0 < (((c : ℂ) + (t : ℂ) * Complex.I)).re := by
    have h1 : (((c : ℂ) + (t : ℂ) * Complex.I)).re = c := by simp
    rw [h1]; exact hc
  rw [LSeries_aperron_eq hz hs, Gfun_eq x z (by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at this
    linarith)]


open MeasureTheory intervalIntegral in
lemma integral_one_div_max_le (T : ℝ) (hT : 1 ≤ T) :
    (∫ t in (-T)..T, (1:ℝ) / max 1 |t|) ≤ 2 * (Real.log T + 1) := by
  have hcont : Continuous (fun t : ℝ => (1:ℝ) / max 1 |t|) := by
    refine Continuous.div continuous_const (by fun_prop) (fun t => ?_)
    have h : (1:ℝ) ≤ max 1 |t| := le_max_left _ _
    linarith
  have h1 : IntervalIntegrable (fun t : ℝ => (1:ℝ) / max 1 |t|) volume (-T) 0 :=
    hcont.intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun t : ℝ => (1:ℝ) / max 1 |t|) volume 0 T :=
    hcont.intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun t : ℝ => (1:ℝ) / max 1 |t|) volume 0 1 :=
    hcont.intervalIntegrable _ _
  have h4 : IntervalIntegrable (fun t : ℝ => (1:ℝ) / max 1 |t|) volume 1 T :=
    hcont.intervalIntegrable _ _
  have hsub : (∫ t in (-T)..0, (1:ℝ) / max 1 |t|) = (∫ t in (0:ℝ)..T, (1:ℝ) / max 1 |t|) := by
    have h := intervalIntegral.integral_comp_neg (a := -T) (b := 0)
      (f := fun t : ℝ => (1:ℝ)/max 1 |t|)
    simp only [neg_zero, neg_neg] at h
    rw [← h]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only
    rw [abs_neg]
  have hsplit : (∫ t in (-T)..T, (1:ℝ) / max 1 |t|)
      = (∫ t in (-T)..0, (1:ℝ) / max 1 |t|) + (∫ t in (0:ℝ)..T, (1:ℝ) / max 1 |t|) :=
    (intervalIntegral.integral_add_adjacent_intervals h1 h2).symm
  have hsplit2 : (∫ t in (0:ℝ)..T, (1:ℝ) / max 1 |t|)
      = (∫ t in (0:ℝ)..1, (1:ℝ) / max 1 |t|) + (∫ t in (1:ℝ)..T, (1:ℝ) / max 1 |t|) :=
    (intervalIntegral.integral_add_adjacent_intervals h3 h4).symm
  have hone : (∫ t in (0:ℝ)..1, (1:ℝ) / max 1 |t|) = 1 := by
    have hc : (∫ t in (0:ℝ)..1, (1:ℝ) / max 1 |t|) = (∫ t in (0:ℝ)..1, (1:ℝ)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx' : (0:ℝ) ≤ x ∧ x ≤ 1 := by
        rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
        exact hx
      have hx1 : |x| ≤ 1 := abs_le.mpr ⟨by linarith [hx'.1], hx'.2⟩
      simp [max_eq_left hx1]
    rw [hc, intervalIntegral.integral_const]
    norm_num
  have hlog : (∫ t in (1:ℝ)..T, (1:ℝ) / max 1 |t|) = Real.log T := by
    have hc : (∫ t in (1:ℝ)..T, (1:ℝ) / max 1 |t|) = (∫ t in (1:ℝ)..T, (1:ℝ)/t) := by
      apply intervalIntegral.integral_congr
      intro x hx
      have hx1 : (1:ℝ) ≤ x := by
        rw [Set.uIcc_of_le (by linarith : (1:ℝ) ≤ T)] at hx
        exact hx.1
      have hxa : |x| = x := abs_of_nonneg (by linarith)
      simp [hxa, max_eq_right hx1]
    rw [hc]
    simp only [one_div]
    rw [integral_inv_of_pos (by norm_num) (by linarith), div_one]
  rw [hsplit, hsplit2, hsub, hlog, hone]
  linarith

open MeasureTheory intervalIntegral in
lemma integral_majorant_le (T : ℝ) (hT : 1 ≤ T) :
    (∫ t in (-T)..T, (Real.log (|t| + 2) + 1) / max 1 |t|)
      ≤ 2 * (Real.log (T + 2) + 1) * (Real.log T + 1) := by
  have hT0 : (0:ℝ) < T := by linarith
  have hnum : Continuous (fun t : ℝ => Real.log (|t| + 2) + 1) := by
    have h1 : Continuous (fun t : ℝ => |t| + 2) := continuous_abs.add continuous_const
    have h2 : Continuous (fun t : ℝ => Real.log (|t| + 2)) := by
      rw [continuous_iff_continuousAt]
      intro t
      exact ContinuousAt.log h1.continuousAt (by positivity)
    exact h2.add continuous_const
  have hcont : Continuous (fun t : ℝ => (Real.log (|t| + 2) + 1) / max 1 |t|) := by
    apply Continuous.div hnum
    · fun_prop
    · intro t
      have h : (1:ℝ) ≤ max 1 |t| := le_max_left _ _
      positivity
  have hcont2 : Continuous (fun t : ℝ => (Real.log (T + 2) + 1) * ((1:ℝ) / max 1 |t|)) := by
    apply Continuous.mul continuous_const
    apply Continuous.div continuous_const
    · fun_prop
    · intro t
      have h : (1:ℝ) ≤ max 1 |t| := le_max_left _ _
      positivity
  have hmaj : (∫ t in (-T)..T, (Real.log (T + 2) + 1) * ((1:ℝ) / max 1 |t|))
      = (Real.log (T+2)+1) * (∫ t in (-T)..T, (1:ℝ)/max 1 |t|) :=
    intervalIntegral.integral_const_mul _ _
  have hmono : (∫ t in (-T)..T, (Real.log (|t| + 2) + 1) / max 1 |t|)
      ≤ (∫ t in (-T)..T, (Real.log (T + 2) + 1) * ((1:ℝ) / max 1 |t|)) := by
    apply intervalIntegral.integral_mono_on (by linarith : -T ≤ T)
    · exact hcont.intervalIntegrable _ _
    · exact hcont2.intervalIntegrable _ _
    · intro x hx
      have hxT : |x| ≤ T := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
      have hlog : Real.log (|x| + 2) ≤ Real.log (T + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have hd : (0:ℝ) < max 1 |x| := by
        have h := le_max_left (1:ℝ) |x|; linarith
      have h1 : (Real.log (|x| + 2) + 1) / max 1 |x|
          ≤ (Real.log (T + 2) + 1) / max 1 |x| :=
        div_le_div_of_nonneg_right (by linarith) hd.le
      have h2 : (Real.log (T + 2) + 1) / max 1 |x|
          = (Real.log (T + 2) + 1) * (1 / max 1 |x|) := by ring
      rw [h2] at h1
      exact h1
  calc (∫ t in (-T)..T, (Real.log (|t| + 2) + 1) / max 1 |t|)
      ≤ (∫ t in (-T)..T, (Real.log (T + 2) + 1) * ((1:ℝ) / max 1 |t|)) := hmono
    _ = (Real.log (T+2)+1) * (∫ t in (-T)..T, (1:ℝ)/max 1 |t|) := hmaj
    _ ≤ (Real.log (T+2)+1) * (2*(Real.log T + 1)) := by
        apply mul_le_mul_of_nonneg_left (integral_one_div_max_le T hT)
        have h1 : (0:ℝ) ≤ Real.log (T + 2) := Real.log_nonneg (by linarith)
        linarith
    _ = 2 * (Real.log (T + 2) + 1) * (Real.log T + 1) := by ring

noncomputable def Cbig (Cζ r K : ℝ) : ℝ :=
  max (max (K * (1 + r) / (Real.log 2 + 1)) (Cζ * (1 + 1 / r))) Cζ

lemma Cbig_pos {Cζ r K : ℝ} (hCζ : 0 < Cζ) (hr : 0 < r) (hK : 0 < K) : 0 < Cbig Cζ r K := by
  unfold Cbig
  exact lt_of_lt_of_le hCζ (le_max_right _ _)

lemma Cbig_ge_K {Cζ r K : ℝ} (hCζ : 0 < Cζ) (hr : 0 < r) (hK : 0 < K) :
    K * (1 + r) / (Real.log 2 + 1) ≤ Cbig Cζ r K := by
  unfold Cbig
  exact le_trans (le_max_left _ _) (le_max_left _ _)

lemma Cbig_ge_Cζmul {Cζ r K : ℝ} (hCζ : 0 < Cζ) (hr : 0 < r) (hK : 0 < K) :
    Cζ * (1 + 1 / r) ≤ Cbig Cζ r K := by
  unfold Cbig
  exact le_trans (le_max_right _ _) (le_max_left _ _)

lemma Cbig_ge_Cζ {Cζ r K : ℝ} (hCζ : 0 < Cζ) (hr : 0 < r) (hK : 0 < K) :
    Cζ ≤ Cbig Cζ r K := le_max_right _ _

lemma Cbig_ge_one {Cζ r K : ℝ} (h1 : 1 ≤ Cζ) (hr : 0 < r) (hK : 0 < K) :
    1 ≤ Cbig Cζ r K := le_trans h1 (Cbig_ge_Cζ (lt_of_lt_of_le one_pos h1) hr hK)

/-- Pointwise bound for `1/ζ₁` at a point of the shifted strip. -/
lemma inv_zeta1_le_gen {cζ Cζ r K : ℝ} (hCζ : 0 < Cζ) (hr : 0 < r) (hK : 0 < K)
    (hcζ : 0 < cζ)
    (hD1 : ∀ σ t : ℝ, 1 - cζ / Real.log (|t| + 2) ≤ σ → σ ≤ 2 →
      1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Cζ * (Real.log (|t| + 2) + 1))
    (hnear : ∀ s : ℂ, ‖s‖ ≤ r → ‖(riemannZeta₁ (1 + s))⁻¹‖ ≤ K)
    {δ T : ℝ} (hδ : 0 < δ) (hδT : δ * Real.log (T + 2) ≤ cζ)
    {s : ℂ} (hsre : -δ ≤ s.re) (hsre2 : s.re ≤ 1) (hsim : |s.im| ≤ T) :
    ‖(riemannZeta₁ (1 + s))⁻¹‖ ≤ Cbig Cζ r K * ((Real.log (|s.im| + 2) + 1) / max 1 |s.im|) := by
  have him0 : (0:ℝ) ≤ |s.im| := abs_nonneg _
  have hden : 0 < max 1 |s.im| := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hLpos : 0 < Real.log (|s.im| + 2) + 1 := by
    have : 0 ≤ Real.log (|s.im| + 2) := Real.log_nonneg (by linarith)
    linarith
  rw [← mul_div_assoc, le_div_iff₀ hden]
  by_cases hsmall : ‖s‖ ≤ r
  · have h1 : ‖(riemannZeta₁ (1 + s))⁻¹‖ ≤ K := hnear s hsmall
    have hmxle : max 1 |s.im| ≤ max 1 r := by
      apply max_le_max le_rfl
      calc |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
        _ ≤ r := hsmall
    have hlogge : Real.log 2 + 1 ≤ Real.log (|s.im| + 2) + 1 := by
      have h2 : (2:ℝ) ≤ |s.im| + 2 := by linarith
      have h3 : Real.log 2 ≤ Real.log (|s.im| + 2) := Real.log_le_log (by norm_num) h2
      linarith
    have hKle : K ≤ Cbig Cζ r K * (Real.log 2 + 1) / max 1 r := by
      have hb := Cbig_ge_K hCζ hr hK
      have hmr : (0:ℝ) < max 1 r := lt_of_lt_of_le one_pos (le_max_left _ _)
      have hL2 : (0:ℝ) ≤ Real.log 2 + 1 := by
        have h := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2); linarith
      have h2 : K ≤ K * (1 + r) / max 1 r := by
        rw [le_div_iff₀ hmr]
        have hmax : max 1 r ≤ 1 + r := max_le (by linarith) (by linarith)
        nlinarith [hmax, hK]
      have h3 : K * (1 + r) / max 1 r ≤ Cbig Cζ r K * (Real.log 2 + 1) / max 1 r := by
        have h4 : K * (1 + r) / max 1 r
            = (K * (1 + r) / (Real.log 2 + 1)) * ((Real.log 2 + 1) / max 1 r) := by
          field_simp
        rw [h4]
        calc (K * (1 + r) / (Real.log 2 + 1)) * ((Real.log 2 + 1) / max 1 r)
            ≤ Cbig Cζ r K * ((Real.log 2 + 1) / max 1 r) :=
              mul_le_mul_of_nonneg_right hb (div_nonneg hL2 hmr.le)
          _ = Cbig Cζ r K * (Real.log 2 + 1) / max 1 r := by ring
      linarith
    calc ‖(riemannZeta₁ (1 + s))⁻¹‖ * max 1 |s.im| ≤ K * max 1 |s.im| :=
          mul_le_mul_of_nonneg_right h1 (le_of_lt hden)
      _ ≤ K * max 1 r := mul_le_mul_of_nonneg_left hmxle (le_of_lt hK)
      _ ≤ (Cbig Cζ r K * (Real.log 2 + 1) / max 1 r) * max 1 r :=
          mul_le_mul_of_nonneg_right hKle (le_of_lt (lt_of_lt_of_le one_pos (le_max_left _ _)))
      _ = Cbig Cζ r K * (Real.log 2 + 1) := by
          field_simp
      _ ≤ Cbig Cζ r K * (Real.log (|s.im| + 2) + 1) :=
          mul_le_mul_of_nonneg_left hlogge (le_of_lt (Cbig_pos hCζ hr hK))
  · push_neg at hsmall
    have hspos : 0 < ‖s‖ := lt_trans hr hsmall
    have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hsmall
      simp at hsmall
      linarith
    have hne1 : (1:ℂ) + s ≠ 1 := by
      intro h
      apply hs0
      linear_combination h
    have hfac : riemannZeta₁ (1 + s) = s * riemannZeta (1 + s) := by
      have h := riemannZeta_eq_inv_sub_mul hne1
      rw [show (1:ℂ) + s - 1 = s by ring] at h
      rw [h, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
    have hstep : ‖(riemannZeta₁ (1 + s))⁻¹‖ = (1/‖s‖) * (1/‖riemannZeta (1 + s)‖) := by
      rw [hfac]
      simp only [mul_inv_rev, norm_mul, norm_inv, one_div]
      ring
    have hD1app : 1 / ‖riemannZeta (1 + s)‖ ≤ Cζ * (Real.log (|s.im| + 2) + 1) := by
      have hlogpos : 0 < Real.log (|s.im| + 2) := Real.log_pos (by linarith)
      have hTpos : 0 < T + 2 := by linarith [him0]
      have hlogTpos : 0 < Real.log (T + 2) := Real.log_pos (by linarith [him0])
      have hδle : δ ≤ cζ / Real.log (|s.im| + 2) := by
        have h1 : δ ≤ cζ / Real.log (T + 2) := by
          rw [le_div_iff₀ hlogTpos]
          linarith
        have h2 : cζ / Real.log (T + 2) ≤ cζ / Real.log (|s.im| + 2) := by
          apply div_le_div_of_nonneg_left (le_of_lt hcζ) hlogpos
          exact Real.log_le_log (by linarith) (by linarith)
        linarith
      have hσ : 1 - cζ / Real.log (|s.im| + 2) ≤ (1 + s).re := by
        have h1 : (1 + s).re = 1 + s.re := by simp
        rw [h1]
        linarith
      have hσ2 : (1 + s).re ≤ 2 := by
        have h1 : (1 + s).re = 1 + s.re := by simp
        rw [h1]
        linarith
      have h := hD1 (1 + s).re s.im hσ hσ2
      have heq : (((1 + s).re : ℂ) + (s.im : ℂ) * Complex.I) = 1 + s := by
        apply Complex.ext <;> simp
      rwa [heq] at h
    have hCζmax : Cζ * max 1 |s.im| ≤ Cbig Cζ r K * ‖s‖ := by
      have hmxle : max 1 |s.im| ≤ 1 + |s.im| :=
        max_le (by linarith) (by linarith)
      have h1r : (1:ℝ) ≤ ‖s‖ / r := by
        rw [le_div_iff₀ hr]
        simpa using le_of_lt hsmall
      have hbound : 1 + |s.im| ≤ ‖s‖ * (1 + 1/r) := by
        have himle : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
        have h2 : ‖s‖ * (1 + 1/r) = ‖s‖ + ‖s‖/r := by simp only [one_div]; ring
        rw [h2]
        nlinarith [h1r, himle]
      calc Cζ * max 1 |s.im| ≤ Cζ * (1 + |s.im|) :=
            mul_le_mul_of_nonneg_left hmxle (le_of_lt hCζ)
        _ ≤ Cζ * (‖s‖ * (1 + 1/r)) := mul_le_mul_of_nonneg_left hbound (le_of_lt hCζ)
        _ = Cζ * (1 + 1/r) * ‖s‖ := by ring
        _ ≤ Cbig Cζ r K * ‖s‖ :=
            mul_le_mul_of_nonneg_right (Cbig_ge_Cζmul hCζ hr hK) hspos.le
    calc ‖(riemannZeta₁ (1 + s))⁻¹‖ * max 1 |s.im|
        = (1/‖s‖) * (1/‖riemannZeta (1 + s)‖) * max 1 |s.im| := by rw [hstep]
      _ ≤ (1/‖s‖) * (Cζ * (Real.log (|s.im| + 2) + 1)) * max 1 |s.im| := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hden)
          apply mul_le_mul_of_nonneg_left hD1app
          positivity
      _ = Cζ * max 1 |s.im| * (Real.log (|s.im| + 2) + 1) / ‖s‖ := by ring
      _ ≤ Cbig Cζ r K * (Real.log (|s.im| + 2) + 1) := by
          rw [div_le_iff₀ hspos]
          nlinarith [hCζmax, hLpos]

/-- The target real sum `Σ_{n ≤ w, P⁻(n) ≥ z} μ(n)/n`. -/
noncomputable def roughSum (z w : ℝ) : ℝ := by
  classical
  exact ∑ n ∈ (Finset.Icc 1 ⌊w⌋₊).filter (fun n => Rough z n),
    (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)

lemma aperron_eq_ind (z : ℝ) (n : ℕ) :
    aperron z n = (if Rough z n then (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) else 0) := by
  classical
  unfold aperron
  by_cases h : Rough z n
  · rw [if_pos h, if_pos h]; ring
  · rw [if_neg h, if_neg h, mul_zero, zero_div]

lemma sum_aperron_eq (z w x : ℝ) (hfl : ⌊x⌋₊ = ⌊w⌋₊) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, aperron z n = (roughSum z w : ℂ) := by
  classical
  rw [hfl]
  have h1 : ∀ n ∈ Finset.Icc 1 ⌊w⌋₊, aperron z n =
      ((if Rough z n then (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) else 0 : ℝ) : ℂ) := by
    intro n _
    rw [aperron_eq_ind]
    by_cases h : Rough z n
    · rw [if_pos h, if_pos h]; push_cast; ring
    · rw [if_neg h, if_neg h]; simp
  rw [Finset.sum_congr rfl h1, roughSum, Finset.sum_filter]
  push_cast
  rfl

lemma norm_sum_aperron_eq {z w x : ℝ} (hfl : ⌊x⌋₊ = ⌊w⌋₊) :
    ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, aperron z n‖ = |roughSum z w| := by
  rw [sum_aperron_eq z w x hfl, Complex.norm_real, Real.norm_eq_abs]

/-- A usable form of the Perron formula bound. -/
def IsPerronBound (Cper : ℝ) : Prop :=
  ∀ (a : ℕ → ℂ) (c x T : ℝ), 0 < c → 1 < x → 0 < T → (∀ n : ℕ, (n : ℝ) ≠ x) →
    Summable (fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) →
    ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T,
          (LSeries a ((c : ℂ) + (t : ℂ) * Complex.I))
            * (x : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)
            / ((c : ℂ) + (t : ℂ) * Complex.I))
        - ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n‖
      ≤ Cper * (∑' n : ℕ, ‖a n‖ * (x / (n : ℝ)) ^ c *
          min 1 (1 / (T * |Real.log (x / (n:ℝ))|)))

/-- A usable form of the Perron truncation error bound. -/
def IsPerronErrorBound (Cerr : ℝ) : Prop :=
  ∀ x T : ℝ, 3 ≤ x → 2 ≤ T → T ≤ x →
    (∑' n : ℕ, (1 / (n : ℝ)) * (x / (n : ℝ)) ^ (1 / Real.log x) *
        min 1 (1 / (T * |Real.log (x / (n : ℝ))|))) ≤ Cerr * (Real.log x + 1) / T

/-- The Perron approximation of the rough Möbius sum, with the truncation error controlled by a
generic bound for the Perron error sum. -/
lemma perron_approx {z w x T Cper Cerr : ℝ} (hfl : ⌊x⌋₊ = ⌊w⌋₊) (hx3 : 3 ≤ x) (hT2 : 2 ≤ T)
    (hTx : T ≤ x) (hxnn : ∀ n : ℕ, (n : ℝ) ≠ x) (hz : 0 ≤ z) (hCper0 : 0 ≤ Cper)
    (hper : IsPerronBound Cper) (hCerr : IsPerronErrorBound Cerr) :
    ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T,
        Gfun x z (((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)) - (roughSum z w : ℂ)‖
      ≤ Cper * (Cerr * (Real.log x + 1) / T) := by
  have hx1 : (1:ℝ) < x := by linarith
  have hxpos : (0:ℝ) < x := by linarith
  have hTpos : (0:ℝ) < T := by linarith
  have hT1 : (1:ℝ) ≤ T := by linarith
  have hlogxpos : (0:ℝ) < Real.log x := Real.log_pos hx1
  have hcP : (0:ℝ) < 1 / Real.log x := by positivity
  have hsumm := summable_aperron z hcP
  have h := hper (aperron z) (1 / Real.log x) x T hcP hx1 hTpos hxnn hsumm
  have hintegrand : (∫ t in (-T)..T,
        (LSeries (aperron z) (((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I))
          * (x : ℂ) ^ (((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)
          / (((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      = ∫ t in (-T)..T, Gfun x z (((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro t _
    exact perron_integrand_eq hxpos hz hcP
  rw [hintegrand] at h
  have hsum : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, aperron z n) = (roughSum z w : ℂ) :=
    sum_aperron_eq z w x hfl
  rw [hsum] at h
  have hxpow : x ^ (1 / Real.log x) = Real.exp 1 := by
    rw [Real.rpow_def_of_pos hxpos]
    congr 1
    field_simp
  set a : ℝ := 1 / Real.log x with ha
  have hapos : 0 < a := hcP
  set g : ℕ → ℝ := fun n => (1 / (n:ℝ)) * (x / (n:ℝ)) ^ a *
    min 1 (1 / (T * |Real.log (x / (n:ℝ))|)) with hgdef
  set f : ℕ → ℝ := fun n => ‖aperron z n‖ * (x / (n:ℝ)) ^ a *
    min 1 (1 / (T * |Real.log (x / (n:ℝ))|)) with hfdef
  have hmaj : Summable (fun n : ℕ => Real.exp 1 * (1 / (n : ℝ) ^ (1 + a))) :=
    (Real.summable_one_div_nat_rpow.mpr (by linarith)).mul_left (Real.exp 1)
  have hg : Summable g := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
    · positivity
    · by_cases hn : n = 0
      · subst hn
        simp [hgdef, Real.zero_rpow (ne_of_gt hapos),
          Real.zero_rpow (by linarith : (1:ℝ) + a ≠ 0)]
      · have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        have h1 : (1 / (n:ℝ)) * (x / (n:ℝ)) ^ a = Real.exp 1 * (1 / (n:ℝ) ^ (1 + a)) := by
          rw [Real.div_rpow hxpos.le hnpos.le, hxpow, div_eq_mul_inv, Real.rpow_add hnpos,
            Real.rpow_one, div_eq_mul_inv]
          field_simp
        have hmin : min 1 (1 / (T * |Real.log (x / (n:ℝ))|)) ≤ 1 := min_le_left _ _
        have hnn : (0:ℝ) ≤ Real.exp 1 * (1 / (n:ℝ) ^ (1 + a)) := by positivity
        rw [hgdef]
        simp only
        rw [h1]
        calc Real.exp 1 * (1 / (n:ℝ) ^ (1 + a)) * min 1 (1 / (T * |Real.log (x / (n:ℝ))|))
            ≤ Real.exp 1 * (1 / (n:ℝ) ^ (1 + a)) * 1 := mul_le_mul_of_nonneg_left hmin hnn
          _ = Real.exp 1 * (1 / (n:ℝ) ^ (1 + a)) := mul_one _
  have hf : Summable f := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hg
    · positivity
    · have h2 : ‖aperron z n‖ ≤ 1 / (n : ℝ) := by
        by_cases hn : n = 0
        · subst hn; simp [aperron]
        · exact norm_aperron_le z hn
      have h3 : (0:ℝ) ≤ (x / (n : ℝ)) ^ a := Real.rpow_nonneg (by positivity) _
      have h4 : (0:ℝ) ≤ min 1 (1 / (T * |Real.log (x / (n : ℝ))|)) :=
        le_min zero_le_one (div_nonneg zero_le_one (by positivity))
      rw [hfdef, hgdef]
      simp only
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 h3) h4
  calc ‖(1 / (2 * Real.pi)) * (∫ t in (-T)..T,
        Gfun x z (((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I)) - (roughSum z w : ℂ)‖
      ≤ Cper * (∑' n : ℕ, ‖aperron z n‖ * (x / (n : ℝ)) ^ (1 / Real.log x) *
          min 1 (1 / (T * |Real.log (x / (n:ℝ))|))) := h
    _ = Cper * (∑' n : ℕ, f n) := by rw [hfdef, ha]
    _ ≤ Cper * (∑' n : ℕ, g n) := by
        apply mul_le_mul_of_nonneg_left _ hCper0
        exact Summable.tsum_le_tsum (fun n => by
          rw [hfdef, hgdef]; simp only
          have h2 : ‖aperron z n‖ ≤ 1 / (n : ℝ) := by
            by_cases hn : n = 0
            · subst hn; simp [aperron]
            · exact norm_aperron_le z hn
          have h3 : (0:ℝ) ≤ (x / (n : ℝ)) ^ a := Real.rpow_nonneg (by positivity) _
          have h4 : (0:ℝ) ≤ min 1 (1 / (T * |Real.log (x / (n : ℝ))|)) :=
            le_min zero_le_one (div_nonneg zero_le_one (by positivity))
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 h3) h4) hf hg
    _ ≤ Cper * (Cerr * (Real.log x + 1) / T) := by
        apply mul_le_mul_of_nonneg_left _ hCper0
        rw [hgdef]
        exact hCerr x T hx3 hT2 hTx

lemma re_one_add_left (δ t : ℝ) : (1 + (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re = 1 - δ := by
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.I_re, Complex.I_im, mul_zero, add_zero]
  ring

lemma re_one_add_horiz (σ τ : ℝ) :
    (1 + (((σ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I)).re = 1 + σ := by
  simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.I_re, Complex.I_im, mul_zero, add_zero]
  ring

/-- `Gfun` is differentiable on the rectangle used for the contour shift. -/
lemma differentiableOn_Gfun_rect {x z δ cP T c0 : ℝ} (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hT : 0 < T) (hc0 : 0 < c0) (hδc0 : δ ≤ c0) (hcP0 : 0 < cP) (hcP1 : cP ≤ 1)
    (hδlog : δ * Real.log (T + 2) ≤ c0)
    (hZFbig : ∀ σ t : ℝ, 2 ≤ |t| → 1 - c0 / Real.log (|t| + 2) ≤ σ →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0)
    (hZFsmall : ∀ σ t : ℝ, |t| ≤ 4 → 1 - c0 ≤ σ → σ ≤ 2 →
      riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0) :
    DifferentiableOn ℂ (Gfun x z) (Set.uIcc (-δ) cP ×ℂ Set.uIcc (-T) T) := by
  intro s hs
  rw [Complex.mem_reProdIm] at hs
  obtain ⟨h1, h2⟩ := hs
  rw [Set.uIcc_of_le (by linarith : -δ ≤ cP)] at h1
  rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at h2
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  have hsim : |s.im| ≤ T := abs_le.mpr ⟨h2a, h2b⟩
  have hz1 : riemannZeta₁ (1 + s) ≠ 0 :=
    zeta1_ne_zero_of_rect hc0 hZFbig hZFsmall h1a h1b hδ hδc0 hcP1 hδlog hsim
  have hre1 : -1 < s.re := by linarith
  exact (differentiableAt_Gfun hx hre1 hz1).differentiableWithinAt

/-- Pointwise bound for `Gfun` on the left edge of the contour. -/
lemma norm_Gfun_left {x z δ T CP cθ : ℝ} (hx : 0 < x) (hz : 3 ≤ z) (hδ0 : 0 < δ)
    (hδlogz : δ ≤ 1 / Real.log z) (hCP : 0 ≤ CP) (hcθ : 0 ≤ cθ)
    (hPz : ∀ u : ℂ, 1 - 1 / Real.log z ≤ u.re → u.re ≤ 2 →
      ‖Pz z u‖ ≤ CP * (Real.log z) ^ 3)
    (hInv : ∀ t : ℝ, |t| ≤ T →
      ‖(riemannZeta₁ (1 + (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)))⁻¹‖ ≤
        cθ * ((Real.log (|t| + 2) + 1) / max 1 |t|))
    {t : ℝ} (ht : |t| ≤ T) :
    ‖Gfun x z (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      x ^ (-δ) * (CP * (Real.log z) ^ 3) *
        (cθ * ((Real.log (|t| + 2) + 1) / max 1 |t|)) := by
  have h1 : ‖(x : ℂ) ^ (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ = x ^ (-δ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp
  have h3 : ‖Pz z (1 + (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ ≤ CP * (Real.log z) ^ 3 := by
    apply hPz
    · rw [re_one_add_left]; linarith
    · rw [re_one_add_left]; linarith
  have h4 := hInv t ht
  rw [norm_inv] at h4
  unfold Gfun
  rw [norm_div, norm_mul, h1, div_eq_mul_inv]
  have hz3 : (0:ℝ) ≤ (Real.log z) ^ 3 :=
    pow_nonneg (Real.log_nonneg (by linarith)) 3
  exact mul_le_mul (mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg (le_of_lt hx) (-δ))) h4
    (inv_nonneg.mpr (norm_nonneg _))
    (mul_nonneg (Real.rpow_nonneg (le_of_lt hx) (-δ)) (mul_nonneg hCP hz3))

/-- Bound for the integral along the left edge of the contour. -/
lemma left_edge_bound {x z δ T CP cθ : ℝ} (hx : 0 < x) (hz : 3 ≤ z) (hδ0 : 0 < δ)
    (hδlogz : δ ≤ 1 / Real.log z) (hCP : 0 ≤ CP) (hcθ : 0 ≤ cθ) (hT : 1 ≤ T)
    (hcont : ContinuousOn (fun t : ℝ => Gfun x z (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      (Set.uIcc (-T) T))
    (hPz : ∀ u : ℂ, 1 - 1 / Real.log z ≤ u.re → u.re ≤ 2 →
      ‖Pz z u‖ ≤ CP * (Real.log z) ^ 3)
    (hInv : ∀ t : ℝ, |t| ≤ T →
      ‖(riemannZeta₁ (1 + (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)))⁻¹‖ ≤
        cθ * ((Real.log (|t| + 2) + 1) / max 1 |t|)) :
    ‖∫ t in (-T)..T, Gfun x z (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ x ^ (-δ) * (CP * (Real.log z) ^ 3) *
          (cθ * (2 * (Real.log (T + 2) + 1) * (Real.log T + 1))) := by
  have hcontMaj : Continuous (fun t : ℝ => (Real.log (|t| + 2) + 1) / max 1 |t|) := by
    have hnum : Continuous (fun t : ℝ => Real.log (|t| + 2) + 1) := by
      have h1 : Continuous (fun t : ℝ => |t| + 2) := continuous_abs.add continuous_const
      have h2 : Continuous (fun t : ℝ => Real.log (|t| + 2)) := by
        rw [continuous_iff_continuousAt]
        intro t
        exact ContinuousAt.log h1.continuousAt (by positivity)
      exact h2.add continuous_const
    apply Continuous.div hnum
    · fun_prop
    · intro t
      have h : (1:ℝ) ≤ max 1 |t| := le_max_left _ _
      positivity
  have hcontMaj2 : Continuous (fun t : ℝ => x ^ (-δ) * (CP * (Real.log z) ^ 3) *
      (cθ * ((Real.log (|t| + 2) + 1) / max 1 |t|))) :=
    (hcontMaj.const_mul cθ).const_mul (x ^ (-δ) * (CP * (Real.log z) ^ 3))
  have hIntn : IntervalIntegrable
      (fun t : ℝ => ‖Gfun x z (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)
      MeasureTheory.volume (-T) T := (hcont.norm).intervalIntegrable
  have hstep : (∫ t in (-T)..T, ‖Gfun x z (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖)
      ≤ ∫ t in (-T)..T, x ^ (-δ) * (CP * (Real.log z) ^ 3) *
          (cθ * ((Real.log (|t| + 2) + 1) / max 1 |t|)) := by
    apply intervalIntegral.integral_mono_on (by linarith) hIntn
      (hcontMaj2.intervalIntegrable _ _)
    intro t ht
    exact norm_Gfun_left hx hz hδ0 hδlogz hCP hcθ hPz hInv (abs_le.mpr ⟨ht.1, ht.2⟩)
  have hconst : (∫ t in (-T)..T, x ^ (-δ) * (CP * (Real.log z) ^ 3) *
        (cθ * ((Real.log (|t| + 2) + 1) / max 1 |t|)))
      = x ^ (-δ) * (CP * (Real.log z) ^ 3) * cθ *
          (∫ t in (-T)..T, (Real.log (|t| + 2) + 1) / max 1 |t|) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  calc ‖∫ t in (-T)..T, Gfun x z (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ ∫ t in (-T)..T, ‖Gfun x z (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ t in (-T)..T, x ^ (-δ) * (CP * (Real.log z) ^ 3) *
          (cθ * ((Real.log (|t| + 2) + 1) / max 1 |t|)) := hstep
    _ = x ^ (-δ) * (CP * (Real.log z) ^ 3) * cθ *
          (∫ t in (-T)..T, (Real.log (|t| + 2) + 1) / max 1 |t|) := hconst
    _ ≤ x ^ (-δ) * (CP * (Real.log z) ^ 3) * cθ *
          (2 * (Real.log (T + 2) + 1) * (Real.log T + 1)) := by
        have hz3 : (0:ℝ) ≤ (Real.log z) ^ 3 :=
          pow_nonneg (Real.log_nonneg (by linarith)) 3
        have hA : (0:ℝ) ≤ x ^ (-δ) * (CP * (Real.log z) ^ 3) * cθ :=
          mul_nonneg (mul_nonneg (Real.rpow_nonneg (le_of_lt hx) (-δ))
            (mul_nonneg hCP hz3)) hcθ
        exact mul_le_mul_of_nonneg_left (integral_majorant_le T hT) hA
    _ = x ^ (-δ) * (CP * (Real.log z) ^ 3) *
          (cθ * (2 * (Real.log (T + 2) + 1) * (Real.log T + 1))) := by ring

/-- Pointwise bound for `Gfun` on a horizontal edge of the contour. -/
lemma norm_Gfun_horiz {x z δ T CP Cζ cP τ : ℝ} (hx : 1 < x) (hz : 3 ≤ z)
    (hδlogz : δ ≤ 1 / Real.log z) (hcP1 : cP ≤ 1) (hCP : 0 ≤ CP) (hCζ : 0 ≤ Cζ)
    (hcPlog : cP * Real.log x ≤ 1)
    (hPz : ∀ u : ℂ, 1 - 1 / Real.log z ≤ u.re → u.re ≤ 2 →
      ‖Pz z u‖ ≤ CP * (Real.log z) ^ 3)
    (hInv : ∀ σ : ℝ, -δ ≤ σ → σ ≤ cP →
      ‖(riemannZeta₁ (1 + (((σ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I)))⁻¹‖ ≤
        Cζ * ((Real.log (T + 2) + 1) / T))
    {σ : ℝ} (hσ1 : -δ ≤ σ) (hσ2 : σ ≤ cP) :
    ‖Gfun x z (((σ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I)‖ ≤
      Real.exp 1 * (CP * (Real.log z) ^ 3) * (Cζ * ((Real.log (T + 2) + 1) / T)) := by
  have h1 : ‖(x : ℂ) ^ (((σ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I)‖ = x ^ σ := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    simp
  have h3 : ‖Pz z (1 + (((σ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I))‖ ≤
      CP * (Real.log z) ^ 3 := by
    apply hPz
    · rw [re_one_add_horiz]; linarith
    · rw [re_one_add_horiz]; linarith
  have h4 := hInv σ hσ1 hσ2
  rw [norm_inv] at h4
  have hxσ : x ^ σ ≤ Real.exp 1 := by
    have hle : x ^ σ ≤ x ^ cP := Real.rpow_le_rpow_of_exponent_le (le_of_lt hx) hσ2
    have hcPe : x ^ cP ≤ Real.exp 1 := by
      rw [Real.rpow_def_of_pos (by linarith : (0:ℝ) < x)]
      apply Real.exp_le_exp.mpr
      linarith
    linarith
  unfold Gfun
  rw [norm_div, norm_mul, h1, div_eq_mul_inv]
  have hz3 : (0:ℝ) ≤ (Real.log z) ^ 3 :=
    pow_nonneg (Real.log_nonneg (by linarith)) 3
  exact mul_le_mul (mul_le_mul hxσ h3 (norm_nonneg _) (Real.exp_pos 1).le) h4
    (inv_nonneg.mpr (norm_nonneg _))
    (mul_nonneg (Real.exp_pos 1).le (mul_nonneg hCP hz3))

/-- Bound for the integral along a horizontal edge of the contour. -/
lemma horiz_edge_bound {x z δ T CP Cζ cP τ : ℝ} (hx : 1 < x) (hz : 3 ≤ z) (hδ0 : 0 < δ)
    (hδlogz : δ ≤ 1 / Real.log z) (hcP0 : 0 < cP) (hcP1 : cP ≤ 1) (hCP : 0 ≤ CP) (hCζ : 0 ≤ Cζ)
    (hcPlog : cP * Real.log x ≤ 1)
    (hPz : ∀ u : ℂ, 1 - 1 / Real.log z ≤ u.re → u.re ≤ 2 →
      ‖Pz z u‖ ≤ CP * (Real.log z) ^ 3)
    (hInv : ∀ σ : ℝ, -δ ≤ σ → σ ≤ cP →
      ‖(riemannZeta₁ (1 + (((σ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I)))⁻¹‖ ≤
        Cζ * ((Real.log (T + 2) + 1) / T)) :
    ‖∫ σ in (-δ)..cP, Gfun x z (((σ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I)‖
      ≤ (cP + δ) * (Real.exp 1 * (CP * (Real.log z) ^ 3) *
          (Cζ * ((Real.log (T + 2) + 1) / T))) := by
  have hB := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun σ : ℝ => Gfun x z (((σ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I))
    (a := -δ) (b := cP)
    (C := Real.exp 1 * (CP * (Real.log z) ^ 3) * (Cζ * ((Real.log (T + 2) + 1) / T)))
    (fun σ hσ => by
      rw [Set.uIoc_of_le (by linarith : -δ ≤ cP)] at hσ
      exact norm_Gfun_horiz hx hz hδlogz hcP1 hCP hCζ hcPlog hPz hInv (le_of_lt hσ.1) hσ.2)
  have habs : |cP - -δ| = cP + δ := by rw [abs_of_nonneg (by linarith)]; ring
  rw [habs] at hB
  convert hB using 1
  ring

/-- The contour-shift bound for the Perron integral. -/
lemma contour_bound {x z δ T cP CP cθ Cζ : ℝ} (hx : 1 < x) (hz : 3 ≤ z)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hδlogz : δ ≤ 1 / Real.log z)
    (hcP : 0 < cP) (hcP1 : cP ≤ 1) (hcPlog : cP * Real.log x ≤ 1) (hT : 1 ≤ T)
    (hdiff : DifferentiableOn ℂ (Gfun x z) (Set.uIcc (-δ) cP ×ℂ Set.uIcc (-T) T))
    (hcontL : ContinuousOn (fun t : ℝ => Gfun x z (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I))
      (Set.uIcc (-T) T))
    (hPz : ∀ u : ℂ, 1 - 1 / Real.log z ≤ u.re → u.re ≤ 2 →
      ‖Pz z u‖ ≤ CP * (Real.log z) ^ 3)
    (hInvL : ∀ t : ℝ, |t| ≤ T →
      ‖(riemannZeta₁ (1 + (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)))⁻¹‖ ≤
        cθ * ((Real.log (|t| + 2) + 1) / max 1 |t|))
    (hInvH : ∀ σ : ℝ, -δ ≤ σ → σ ≤ cP →
      ‖(riemannZeta₁ (1 + (((σ : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I)))⁻¹‖ ≤
        Cζ * ((Real.log (T + 2) + 1) / T))
    (hInvH' : ∀ σ : ℝ, -δ ≤ σ → σ ≤ cP →
      ‖(riemannZeta₁ (1 + (((σ : ℝ) : ℂ) + (((-T) : ℝ) : ℂ) * Complex.I)))⁻¹‖ ≤
        Cζ * ((Real.log (T + 2) + 1) / T))
    (hCP : 0 ≤ CP) (hcθ : 0 ≤ cθ) (hCζ : 0 ≤ Cζ) :
    ‖∫ t in (-T)..T, Gfun x z (((cP : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ x ^ (-δ) * (CP * (Real.log z) ^ 3) *
            (cθ * (2 * (Real.log (T + 2) + 1) * (Real.log T + 1)))
        + 2 * ((cP + δ) * (Real.exp 1 * (CP * (Real.log z) ^ 3) *
            (Cζ * ((Real.log (T + 2) + 1) / T)))) := by
  set zl : ℂ := ((-δ : ℝ) : ℂ) + (((-T) : ℝ) : ℂ) * Complex.I with hzldef
  set wl : ℂ := ((cP : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I with hwldef
  have hzlre : zl.re = -δ := by simp [hzldef]
  have hzlim : zl.im = -T := by simp [hzldef]
  have hwlre : wl.re = cP := by simp [hwldef]
  have hwlim : wl.im = T := by simp [hwldef]
  have hd : DifferentiableOn ℂ (Gfun x z)
      (Set.uIcc zl.re wl.re ×ℂ Set.uIcc zl.im wl.im) := by
    rw [hzlre, hzlim, hwlre, hwlim]
    exact hdiff
  have hrect := rect_boundary_identity (f := Gfun x z) hd
  rw [hzlre, hzlim, hwlre, hwlim] at hrect
  set R : ℂ := ∫ t in (-T)..T, Gfun x z (((cP : ℝ) : ℂ) + (t : ℂ) * Complex.I) with hR
  set L : ℂ := ∫ t in (-T)..T, Gfun x z (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I) with hL
  set A : ℂ := ∫ σ in (-δ)..cP, Gfun x z (((σ : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I) with hA
  set B : ℂ := ∫ σ in (-δ)..cP, Gfun x z (((σ : ℝ) : ℂ) + (((-T) : ℝ) : ℂ) * Complex.I) with hB
  have hrect' : R = L + (A - B) / Complex.I := by
    rw [hR, hL, hA, hB]
    exact hrect
  have hLL : ‖L‖ ≤ x ^ (-δ) * (CP * (Real.log z) ^ 3) *
        (cθ * (2 * (Real.log (T + 2) + 1) * (Real.log T + 1))) := by
    rw [hL]
    exact left_edge_bound (by linarith : (0:ℝ) < x) hz hδ0 hδlogz hCP hcθ hT hcontL hPz hInvL
  have hH1 : ‖A‖ ≤ (cP + δ) * (Real.exp 1 * (CP * (Real.log z) ^ 3) *
        (Cζ * ((Real.log (T + 2) + 1) / T))) := by
    rw [hA]
    exact horiz_edge_bound hx hz hδ0 hδlogz hcP hcP1 hCP hCζ hcPlog hPz hInvH
  have hH2 : ‖B‖ ≤ (cP + δ) * (Real.exp 1 * (CP * (Real.log z) ^ 3) *
        (Cζ * ((Real.log (T + 2) + 1) / T))) := by
    rw [hB]
    exact horiz_edge_bound (τ := -T) hx hz hδ0 hδlogz hcP hcP1 hCP hCζ hcPlog hPz hInvH'
  have hIp : ‖(A - B) / Complex.I‖ ≤
      (cP + δ) * (Real.exp 1 * (CP * (Real.log z) ^ 3) *
            (Cζ * ((Real.log (T + 2) + 1) / T)))
        + (cP + δ) * (Real.exp 1 * (CP * (Real.log z) ^ 3) *
            (Cζ * ((Real.log (T + 2) + 1) / T))) := by
    rw [norm_div, Complex.norm_I, div_one]
    exact le_trans (norm_sub_le A B) (add_le_add hH1 hH2)
  calc ‖R‖ = ‖L + (A - B) / Complex.I‖ := by rw [hrect']
    _ ≤ ‖L‖ + ‖(A - B) / Complex.I‖ := norm_add_le L _
    _ ≤ x ^ (-δ) * (CP * (Real.log z) ^ 3) *
            (cθ * (2 * (Real.log (T + 2) + 1) * (Real.log T + 1)))
        + 2 * ((cP + δ) * (Real.exp 1 * (CP * (Real.log z) ^ 3) *
            (Cζ * ((Real.log (T + 2) + 1) / T)))) := by
        linarith [hLL, hIp]

/-- Logarithmic bounds used in case A. -/
lemma caseA_log_bounds {c0 z : ℝ} (hc0 : 0 < c0) (hz : 3 ≤ z) (hbig : 100 ≤ c0 * Real.log z) :
    Real.log (z ^ (c0 / 4) + 2) ≤ (c0 / 2) * Real.log z ∧ (1:ℝ) ≤ z ^ (c0 / 4) := by
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hz1 : (1:ℝ) ≤ z := by linarith
  have hT1 : (1:ℝ) ≤ z ^ (c0 / 4) := Real.one_le_rpow hz1 (by positivity)
  refine ⟨?_, hT1⟩
  have hTpos : (0:ℝ) < z ^ (c0 / 4) := Real.rpow_pos_of_pos (by linarith) _
  have hlogT : Real.log (z ^ (c0 / 4)) = (c0 / 4) * Real.log z := Real.log_rpow (by linarith) _
  have hle : z ^ (c0 / 4) + 2 ≤ 3 * z ^ (c0 / 4) := by nlinarith
  calc Real.log (z ^ (c0 / 4) + 2) ≤ Real.log (3 * z ^ (c0 / 4)) :=
        Real.log_le_log (by positivity) hle
    _ = Real.log 3 + Real.log (z ^ (c0 / 4)) := Real.log_mul (by norm_num) hTpos.ne'
    _ = Real.log 3 + (c0 / 4) * Real.log z := by rw [hlogT]
    _ ≤ (c0 / 2) * Real.log z := by
        have hlog3 : Real.log 3 ≤ 2 := by
          have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3)
          linarith
        have h2 : (2:ℝ) ≤ (c0 / 4) * Real.log z := by linarith
        linarith

/-- The pointwise `1/ζ₁` bound on a horizontal edge, from the zero-free region bound for `1/ζ`. -/
lemma inv_zeta1_horiz {cζ Cζ δ T cP τ : ℝ} (hcζ : 0 < cζ) (hT : 0 < T) (hδ0 : 0 < δ)
    (hcP1 : cP ≤ 1) (hδT : δ * Real.log (T + 2) ≤ cζ) (hτT : |τ| = T)
    (hD1 : ∀ σ t : ℝ, 1 - cζ / Real.log (|t| + 2) ≤ σ → σ ≤ 2 →
      1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Cζ * (Real.log (|t| + 2) + 1))
    {σ : ℝ} (hσ1 : -δ ≤ σ) (hσ2 : σ ≤ cP) :
    ‖(riemannZeta₁ (1 + (((σ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I)))⁻¹‖ ≤
      Cζ * ((Real.log (T + 2) + 1) / T) := by
  set s : ℂ := ((σ : ℝ) : ℂ) + ((τ : ℝ) : ℂ) * Complex.I with hsdef
  have hsim : s.im = τ := by simp [hsdef]
  have hsre : s.re = σ := by simp [hsdef]
  have hspos : s ≠ 0 := by
    intro h
    have h2 := congrArg Complex.im h
    simp [hsdef] at h2
    rw [h2] at hτT
    simp at hτT
    linarith
  have hne1 : (1:ℂ) + s ≠ 1 := by
    intro h
    exact hspos (by linear_combination h)
  have hfac : riemannZeta₁ (1 + s) = s * riemannZeta (1 + s) := by
    have h := riemannZeta_eq_inv_sub_mul hne1
    rw [show (1:ℂ) + s - 1 = s by ring] at h
    rw [h, ← mul_assoc, mul_inv_cancel₀ hspos, one_mul]
  have hnorm : ‖(riemannZeta₁ (1 + s))⁻¹‖ = (1/‖s‖) * (1/‖riemannZeta (1 + s)‖) := by
    rw [hfac]
    simp only [mul_inv_rev, norm_mul, norm_inv, one_div]
    ring
  have htpos : 0 < |τ| := by rw [hτT]; exact hT
  have hlogpos : 0 < Real.log (|τ| + 2) := Real.log_pos (by linarith)
  have hlogTpos : 0 < Real.log (T + 2) := Real.log_pos (by linarith)
  have hD1app : 1 / ‖riemannZeta (1 + s)‖ ≤ Cζ * (Real.log (T + 2) + 1) := by
    have h1 : 1 - cζ / Real.log (|τ| + 2) ≤ (1 + s).re := by
      have h2 : (1 + s).re = 1 + σ := by simp [hsdef]
      have h3 : δ ≤ cζ / Real.log (|τ| + 2) := by
        rw [le_div_iff₀ hlogpos]
        have h4 : Real.log (|τ| + 2) ≤ Real.log (T + 2) :=
          Real.log_le_log (by linarith) (by rw [hτT])
        nlinarith [hδT, le_of_lt hcζ]
      rw [h2]
      linarith
    have h2 : (1 + s).re ≤ 2 := by
      have h3 : (1 + s).re = 1 + σ := by simp [hsdef]
      rw [h3]
      linarith
    have h := hD1 (1 + s).re τ h1 h2
    have heq : (((1 + s).re : ℂ) + (τ : ℂ) * Complex.I) = 1 + s := by
      apply Complex.ext <;> simp [hsdef]
    rw [heq] at h
    have h5 : Real.log (|τ| + 2) = Real.log (T + 2) := by rw [hτT]
    rwa [h5] at h
  have hnorm_ge : T ≤ ‖s‖ := by
    calc T = |τ| := hτT.symm
      _ = |s.im| := by rw [hsim]
      _ ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hinv : (1/‖s‖) ≤ 1/T := one_div_le_one_div_of_le hT hnorm_ge
  rw [hnorm]
  calc (1/‖s‖) * (1 / ‖riemannZeta (1 + s)‖)
      ≤ (1/T) * (Cζ * (Real.log (T + 2) + 1)) :=
        mul_le_mul hinv hD1app (by positivity) (by positivity)
    _ = Cζ * ((Real.log (T + 2) + 1) / T) := by ring

/-- Main assembly: given the Perron error bound and the case-B arithmetic input, the bound. -/
lemma main_bound_of_inputs
    (hPerr : ∃ Cerr : ℝ, 0 < Cerr ∧ IsPerronErrorBound Cerr)
    (hCaseB : ∀ c0 Kp : ℝ, 0 < c0 → c0 ≤ 1 → 0 < Kp → ∃ K Z0 : ℝ, 0 ≤ K ∧ 3 ≤ Z0 ∧
      ∀ z w : ℝ, Z0 ≤ z → 3 ≤ w → z ^ 2 ≤ w → Real.log z < Real.log w / Real.log z →
        Kp * ((Real.log z) ^ 3 * (c0 * Real.log z + Real.log (Real.log w / Real.log z) + 23)
            * (c0 * Real.log z + Real.log (Real.log w / Real.log z) + 21)
            * Real.exp (-(c0 * (Real.log w / Real.log z) * Real.log z
                / (c0 * Real.log z + Real.log (Real.log w / Real.log z) + 22)))
          + (Real.log z) ^ 3 * (c0 * Real.log z + Real.log (Real.log w / Real.log z) + 23)
            / Real.exp (c0 * Real.log z + Real.log (Real.log w / Real.log z) + 20)
          + 3 * (Real.log w + 1)
            / Real.exp (c0 * Real.log z + Real.log (Real.log w / Real.log z) + 20))
        ≤ K * z ^ (-(c0 / 16))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z w : ℝ, 3 ≤ z → 2 ≤ w → z ^ 2 ≤ w →
      |roughSum z w| ≤ C * (z ^ (-c) + Real.exp (-(Real.log w / Real.log z)) * (Real.log z) ^ 6) := by
  obtain ⟨Cerr, hCerrpos, hCerr⟩ := hPerr
  obtain ⟨czfr, hczfr, hZFbig0⟩ := Commons.NumberTheory.LSeries.exists_zero_free_region_riemannZeta_log
  obtain ⟨ε4, hε4pos, hZFsmall0⟩ :=
    Commons.NumberTheory.Zeta.zeta_zeroFree_compact_width 4 (by norm_num)
  obtain ⟨cζ, Cζ0, hcζpos, _hCζ0pos, hD10⟩ := Commons.NumberTheory.Zeta.inv_zeta_le_log_zeroFree
  obtain ⟨CP0, _hCP0pos, hPz0⟩ := Commons.NumberTheory.Sieve.prod_primes_below_one_sub_cpow_inv_bound
  obtain ⟨r, hrpos, hnear0⟩ := exists_riemannZeta₁_inv_le_two_near_one
  obtain ⟨Cper0, _hCper0pos, hper0⟩ := Commons.Analysis.Complex.exists_perron_formula_bound
  set CP : ℝ := max CP0 1 with hCPdef
  set Cζ : ℝ := max Cζ0 1 with hCζdef
  set Cper : ℝ := max Cper0 1 with hCperdef
  have hCPpos : 0 < CP := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCζpos : 0 < Cζ := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCperpos : 0 < Cper := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hper : IsPerronBound Cper := by
    intro a c x T hc hx1 hT hxnn hsum
    refine le_trans (hper0 a c x T hc hx1 hT hxnn hsum) ?_
    refine mul_le_mul_of_nonneg_right (le_max_left Cper0 1) ?_
    exact tsum_nonneg (fun n => by
      have h3 : (0:ℝ) ≤ (x / (n : ℝ)) ^ c := Real.rpow_nonneg (by positivity) _
      have h4 : (0:ℝ) ≤ min 1 (1 / (T * |Real.log (x / (n : ℝ))|)) :=
        le_min zero_le_one (div_nonneg zero_le_one (by positivity))
      exact mul_nonneg (mul_nonneg (norm_nonneg _) h3) h4)
  set c0 : ℝ := min (min czfr ε4) (min cζ 1) with hc0def
  have hc0pos : 0 < c0 := lt_min (lt_min hczfr hε4pos) (lt_min hcζpos one_pos)
  have hc0czfr : c0 ≤ czfr := le_trans (min_le_left _ _) (min_le_left _ _)
  have hc0ε4 : c0 ≤ ε4 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hc0cζ : c0 ≤ cζ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hc0le1 : c0 ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
  set Cb : ℝ := Cbig Cζ r 2 with hCbdef
  have hCbpos : 0 < Cb := Cbig_pos hCζpos hrpos (by norm_num)
  set Kp : ℝ := max 1 (max (2*CP*Cb) (max (Real.exp 1 * 3 * CP * Cζ) (Cper * Cerr))) with hKpdef
  have hKp1 : 1 ≤ Kp := le_max_left _ _
  have hKppos : 0 < Kp := lt_of_lt_of_le one_pos hKp1
  have hKp2Cb : 2*CP*Cb ≤ Kp := le_trans (le_max_left _ _) (le_max_right _ _)
  have hKpexp : Real.exp 1 * 3 * CP * Cζ ≤ Kp :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hKperr : Cper * Cerr ≤ Kp :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  obtain ⟨KA, Z0A, hKA0, hZ0A3, hKA⟩ :=
    Commons.Analysis.ExpLog.case_A_arith c0 Kp hc0pos hc0le1 hKppos
  obtain ⟨KB, Z0B, hKB0, hZ0B3, hKB⟩ := hCaseB c0 Kp hc0pos hc0le1 hKppos
  set Z0 : ℝ := max (max Z0A Z0B) (max 4 (Real.exp (400/c0))) with hZ0def
  have hZ0_3 : 3 ≤ Z0 := le_trans hZ0A3 (le_trans (le_max_left _ _) (le_max_left _ _))
  have hZ0pos : (0:ℝ) < Z0 := by linarith
  have hZ0_exp : Real.exp (400/c0) ≤ Z0 := le_trans (le_max_right 4 _) (le_max_right _ _)
  set cf : ℝ := c0/16 with hcfdef
  have hcfpos : 0 < cf := by rw [hcfdef]; positivity
  set Cfin : ℝ := max (max KA KB) (max (2 * Z0 ^ cf) 1) with hCfindef
  have hCfinpos : 0 < Cfin :=
    lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) (le_max_right _ _))
  have hCfin_KA : KA ≤ Cfin := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCfin_KB : KB ≤ Cfin := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCfin_Z0 : 2 * Z0 ^ cf ≤ Cfin := le_trans (le_max_left _ _) (le_max_right _ _)
  refine ⟨cf, Cfin, hcfpos, hCfinpos, ?_⟩
  intro z w hz hw hzw
  have hw3 : 3 ≤ w := by nlinarith
  have hwpos : 0 < w := by linarith
  have hzpos : 0 < z := by linarith
  have hlogzpos : 0 < Real.log z := Real.log_pos (by linarith)
  have hE : 0 ≤ Real.exp (-(Real.log w / Real.log z)) * (Real.log z) ^ 6 :=
    mul_nonneg (Real.exp_nonneg _) (pow_nonneg hlogzpos.le 6)
  by_cases hzs : z ≤ Z0
  · have hsmall :=
      Commons.NumberTheory.Sieve.moebius_rough_recip_abs_le_two z w (by linarith) (by linarith)
    have hzc : Z0 ^ (-cf) ≤ z ^ (-cf) :=
      Real.rpow_le_rpow_of_nonpos hzpos hzs (by linarith : -cf ≤ 0)
    have h2Z : 2 * Z0 ^ cf * Z0 ^ (-cf) = 2 := by
      rw [mul_assoc, ← Real.rpow_add hZ0pos, add_neg_cancel, Real.rpow_zero, mul_one]
    have hkey : (2:ℝ) ≤ Cfin * (z ^ (-cf) + Real.exp (-(Real.log w / Real.log z)) * (Real.log z) ^ 6) := by
      calc (2:ℝ) = 2 * Z0 ^ cf * Z0 ^ (-cf) := h2Z.symm
        _ ≤ Cfin * Z0 ^ (-cf) := mul_le_mul_of_nonneg_right hCfin_Z0 (Real.rpow_nonneg hZ0pos.le _)
        _ ≤ Cfin * z ^ (-cf) := mul_le_mul_of_nonneg_left hzc hCfinpos.le
        _ ≤ Cfin * (z ^ (-cf) + Real.exp (-(Real.log w / Real.log z)) * (Real.log z) ^ 6) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hE) hCfinpos.le
    have hsmall' : |roughSum z w| ≤ 2 := by
      have hf : (Finset.Icc 1 ⌊w⌋₊).filter (fun n => Rough z n)
          = (Finset.Icc 1 ⌊w⌋₊).filter (fun n => ∀ p : ℕ, p ∈ n.primeFactors → z ≤ (p : ℝ)) := by
        apply Finset.filter_congr
        intro n _
        exact Iff.rfl
      rw [roughSum, hf]
      exact hsmall
    exact le_trans hsmall' hkey
  · push_neg at hzs
    have hzA : Z0A ≤ z := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hzs.le
    have hzB : Z0B ≤ z := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hzs.le
    have hbig : 400 ≤ c0 * Real.log z := by
      have h1 : Real.exp (400/c0) < z := lt_of_le_of_lt hZ0_exp hzs
      have h2 : 400/c0 < Real.log z := by
        have h := Real.log_lt_log (Real.exp_pos (400/c0)) h1
        rwa [Real.log_exp] at h
      rw [div_lt_iff₀ hc0pos] at h2
      linarith
    have hbig2 : 100 ≤ c0 * Real.log z := by linarith
    have hlogz400 : 400 ≤ Real.log z := by
      have h : c0 * Real.log z ≤ 1 * Real.log z :=
        mul_le_mul_of_nonneg_right hc0le1 hlogzpos.le
      linarith
    have hZFbig : ∀ σ t : ℝ, 2 ≤ |t| → 1 - c0 / Real.log (|t| + 2) ≤ σ →
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro σ t ht hσ
      have hlog : 0 < Real.log (|t| + 2) := Real.log_pos (by linarith [abs_nonneg t])
      have hle : c0 / Real.log (|t| + 2) ≤ czfr / Real.log (|t| + 2) :=
        div_le_div_of_nonneg_right hc0czfr hlog.le
      exact hZFbig0 σ t ht (by linarith)
    have hZFsmall : ∀ σ t : ℝ, |t| ≤ 4 → 1 - c0 ≤ σ → σ ≤ 2 →
        riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
      intro σ t ht hσ hσ2
      have h1 : 1 - ε4 ≤ σ := by linarith
      simpa only [mul_comm] using hZFsmall0 t σ ht h1 hσ2
    have hD1 : ∀ σ t : ℝ, 1 - cζ / Real.log (|t| + 2) ≤ σ → σ ≤ 2 →
        1 / ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Cζ * (Real.log (|t| + 2) + 1) := by
      intro σ t h1 h2
      refine le_trans (hD10 σ t h1 h2) ?_
      refine mul_le_mul_of_nonneg_right (le_max_left Cζ0 1) ?_
      have h := Real.log_nonneg (by linarith [abs_nonneg t] : (1:ℝ) ≤ |t| + 2)
      linarith
    by_cases hcaseA : Real.log w / Real.log z ≤ Real.log z
    · -- ================= CASE A =================
      set x : ℝ := ⌊w⌋₊ + 1/2 with hxdef
      have hwfloor : (3:ℝ) ≤ ⌊w⌋₊ := by
        have h : 3 ≤ ⌊w⌋₊ := Nat.le_floor (by linarith : (3:ℝ) ≤ w)
        exact_mod_cast h
      have hx3 : (3:ℝ) ≤ x := by rw [hxdef]; linarith
      have hx1 : (1:ℝ) < x := by linarith
      have hxpos : (0:ℝ) < x := by linarith
      have hlogx1 : 1 ≤ Real.log x := by
        have h := Real.log_le_log (by norm_num : (0:ℝ) < 3) hx3
        linarith [Real.log_three_gt_d9, h]
      have hxfloor : ⌊x⌋₊ = ⌊w⌋₊ := by
        rw [hxdef]
        refine (Nat.floor_eq_iff (a := (⌊w⌋₊ : ℝ) + 1/2) (n := ⌊w⌋₊) (by positivity)).mpr
          ⟨by linarith, by linarith⟩
      have hxnn : ∀ n : ℕ, (n : ℝ) ≠ x := by
        intro n h
        have hfl : ⌊(n : ℝ)⌋₊ = ⌊w⌋₊ := by
          rw [h, hxdef]
          refine (Nat.floor_eq_iff (a := (⌊w⌋₊ : ℝ) + 1/2) (n := ⌊w⌋₊) (by positivity)).mpr
            ⟨by linarith, by linarith⟩
        rw [Nat.floor_natCast] at hfl
        rw [hxdef, ← hfl] at h
        norm_num at h
      set δ : ℝ := 1/Real.log z with hδdef
      set T : ℝ := z ^ (c0/4) with hTdef
      set cP : ℝ := 1/Real.log x with hcPdef
      have hδ0 : 0 < δ := by rw [hδdef]; positivity
      have hδ1 : δ < 1 := by
        rw [hδdef, div_lt_one hlogzpos]
        linarith only [hlogz400]
      have hclb := caseA_log_bounds hc0pos hz hbig2
      have hT1 : 1 ≤ T := by rw [hTdef]; exact hclb.2
      have hTpos : 0 < T := lt_of_lt_of_le one_pos hT1
      have hlogT2 : Real.log (T+2) ≤ (c0/2) * Real.log z := by rw [hTdef]; exact hclb.1
      have hlogT2p : Real.log (T+2) + 1 ≤ c0 * Real.log z := by
        have h : (c0/2)*Real.log z + 1 ≤ c0 * Real.log z := by
          linarith only [hbig]
        linarith only [hlogT2, h]
      have hlogTp : Real.log T + 1 ≤ (c0/2)*Real.log z := by
        rw [hTdef, Real.log_rpow (by linarith)]
        have h : (c0/4)*Real.log z + 1 ≤ (c0/2)*Real.log z := by
          linarith only [hbig]
        linarith only [h]
      have hδT : δ * Real.log (T + 2) ≤ c0 := by
        rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ hlogzpos]
        linarith only [hlogT2p]
      have hδc0 : δ ≤ c0 := by
        rw [hδdef, div_le_iff₀ hlogzpos]
        linarith only [hbig]
      have hcPpos : 0 < cP := by rw [hcPdef]; exact div_pos one_pos (Real.log_pos hx1)
      have hcP1 : cP ≤ 1 := by rw [hcPdef, div_le_one (Real.log_pos hx1)]; exact hlogx1
      have hcPlog : cP * Real.log x ≤ 1 := by
        rw [hcPdef, div_mul_cancel₀ _ (ne_of_gt (Real.log_pos hx1))]
      have hcP2 : cP ≤ 2 := by linarith
      have hPz : ∀ u : ℂ, 1 - 1/Real.log z ≤ u.re → u.re ≤ 2 →
          ‖Pz z u‖ ≤ CP * (Real.log z) ^ 3 := by
        intro u h1 h2
        refine le_trans (hPz0 z hz u h1 h2) ?_
        exact mul_le_mul_of_nonneg_right (le_max_left CP0 1)
          (pow_nonneg (Real.log_nonneg (by linarith)) 3)
      have hInvL : ∀ t : ℝ, |t| ≤ T →
          ‖(riemannZeta₁ (1 + (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)))⁻¹‖ ≤
            Cb * ((Real.log (|t| + 2) + 1) / max 1 |t|) := by
        intro t ht
        have h := inv_zeta1_le_gen hCζpos hrpos (by norm_num : (0:ℝ) < 2) hcζpos hD1 hnear0
          hδ0 (le_trans hδT hc0cζ) (s := (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)) (by simp)
          (by simp; linarith) (by simpa using ht)
        have him : (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
        rw [him] at h
        rw [hCbdef]
        exact h
      have hInvH : ∀ σ : ℝ, -δ ≤ σ → σ ≤ cP →
          ‖(riemannZeta₁ (1 + (((σ : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I)))⁻¹‖ ≤
            Cζ * ((Real.log (T + 2) + 1) / T) :=
        fun σ h1 h2 => inv_zeta1_horiz (τ := T) hcζpos hTpos hδ0 hcP1 (le_trans hδT hc0cζ)
          (abs_of_pos hTpos) hD1 h1 h2
      have hInvH' : ∀ σ : ℝ, -δ ≤ σ → σ ≤ cP →
          ‖(riemannZeta₁ (1 + (((σ : ℝ) : ℂ) + (((-T) : ℝ) : ℂ) * Complex.I)))⁻¹‖ ≤
            Cζ * ((Real.log (T + 2) + 1) / T) :=
        fun σ h1 h2 => inv_zeta1_horiz (τ := -T) hcζpos hTpos hδ0 hcP1 (le_trans hδT hc0cζ)
          (by rw [abs_neg, abs_of_pos hTpos]) hD1 h1 h2
      have hdiff : DifferentiableOn ℂ (Gfun x z) (Set.uIcc (-δ) cP ×ℂ Set.uIcc (-T) T) :=
        differentiableOn_Gfun_rect hxpos hδ0 hδ1 hTpos hc0pos hδc0 hcPpos hcP1 hδT hZFbig hZFsmall
      have hcontL : ContinuousOn (fun t : ℝ => Gfun x z (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I))
          (Set.uIcc (-T) T) := by
        refine hdiff.continuousOn.comp (by fun_prop) ?_
        intro t ht
        rw [Complex.mem_reProdIm]
        constructor
        · have h2 : (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = -δ := by simp
          rw [h2, Set.uIcc_of_le (by linarith : -δ ≤ cP)]
          exact ⟨le_rfl, by linarith⟩
        · have h2 : (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
          rw [h2]
          exact ht
      set E1 : ℝ := x ^ (-δ) * (CP * (Real.log z) ^ 3) *
              (Cb * (2 * (Real.log (T + 2) + 1) * (Real.log T + 1))) with hE1def
      set E2 : ℝ := 2 * ((cP + δ) * (Real.exp 1 * (CP * (Real.log z) ^ 3) *
              (Cζ * ((Real.log (T + 2) + 1) / T)))) with hE2def
      set A1 : ℝ := Real.exp (-(Real.log w / Real.log z)) * (Real.log z) ^ 5 with hA1def
      set B1 : ℝ := (Real.log z) ^ 3 * (Real.log (T + 2) + 1) / T with hB1def
      set C1 : ℝ := 3 * (Real.log w + 1) / T with hC1def
      set ER : ℝ := Cper * (Cerr * (Real.log x + 1) / T) with hERdef
      set R : ℝ := ‖∫ t in (-T)..T, Gfun x z (((cP : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ with hRdef
      have hRA : R ≤ E1 + E2 := by
        rw [hE1def, hE2def, hRdef]
        exact contour_bound hx1 hz hδ0 hδ1 le_rfl hcPpos hcP1 hcPlog hT1 hdiff hcontL hPz
          hInvL hInvH hInvH' hCPpos.le hCbpos.le hCζpos.le
      have hT2A : (2:ℝ) ≤ T := by
        rw [hTdef]
        calc (2:ℝ) ≤ Real.exp 100 := by
              rw [← Real.exp_log (by norm_num : (0:ℝ) < 2)]
              apply Real.exp_le_exp.mpr
              have h3 : Real.log 2 ≤ 1 := by
                have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
              linarith
          _ ≤ z ^ (c0/4) := by
              rw [Real.rpow_def_of_pos (by linarith : (0:ℝ) < z)]
              apply Real.exp_le_exp.mpr
              have hbig' : 400 ≤ c0 * Real.log z := hbig
              nlinarith only [hbig', hc0pos, hc0le1]
      have hTxA : T ≤ x := by
        rw [hTdef]
        have hxw : w / 2 ≤ x := by rw [hxdef]; linarith [Nat.lt_floor_add_one w]
        have h4 : (0:ℝ) < z := by linarith
        have h1 : z ^ (c0/4) ≤ z ^ (1/4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ z)
            (by linarith only [hc0le1])
        have h3 : (2:ℝ) ≤ z ^ (7/4 : ℝ) := by
          have h5 : (3:ℝ) ≤ z := by linarith
          have h6 : (3:ℝ) ^ (1:ℝ) ≤ (3:ℝ) ^ (7/4 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          rw [Real.rpow_one] at h6
          have h7 : (3:ℝ) ^ (7/4 : ℝ) ≤ z ^ (7/4 : ℝ) :=
            Real.rpow_le_rpow (by norm_num) h5 (by norm_num)
          linarith only [h6, h7]
        have h5 : z ^ (1/4 : ℝ) * z ^ (7/4 : ℝ) = z ^ 2 := by
          rw [← Real.rpow_add h4]; norm_num
        have hz74 : (0:ℝ) < z ^ (7/4 : ℝ) := Real.rpow_pos_of_pos h4 _
        have h2 : z ^ (1/4 : ℝ) ≤ z ^ 2 / 2 := by
          have ha : z ^ (1/4 : ℝ) = (z ^ (1/4 : ℝ) * z ^ (7/4 : ℝ)) / z ^ (7/4 : ℝ) := by
            field_simp
          rw [ha, h5]
          exact div_le_div_of_nonneg_left (by positivity) (by norm_num) h3
        have h6 : z ^ 2 / 2 ≤ w / 2 := by linarith only [hzw]
        linarith only [h1, h2, h6, hxw]
      have hPA : ‖(1/(2*Real.pi)) * (∫ t in (-T)..T, Gfun x z (((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I))
            - (roughSum z w : ℂ)‖ ≤ ER := by
        rw [hERdef]
        exact perron_approx hxfloor hx3 hT2A hTxA hxnn (by linarith : (0:ℝ) ≤ z) hCperpos.le hper hCerr
      have hstep1 : ‖(roughSum z w : ℂ)‖ ≤ (1/(2*Real.pi)) * R + ER := by
        have h3 : ‖(roughSum z w : ℂ)‖ ≤
            ‖(roughSum z w : ℂ) - (1/(2*Real.pi)) * (∫ t in (-T)..T, Gfun x z (((cP : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
              + ‖(1/(2*Real.pi)) * (∫ t in (-T)..T, Gfun x z (((cP : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ := by
          calc ‖(roughSum z w : ℂ)‖
              = ‖((roughSum z w : ℂ) - (1/(2*Real.pi)) *
                  (∫ t in (-T)..T, Gfun x z (((cP : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
                  + (1/(2*Real.pi)) *
                  (∫ t in (-T)..T, Gfun x z (((cP : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ := by
                congr 1; ring
            _ ≤ _ := norm_add_le _ _
        have h4 : ‖(1/(2*Real.pi)) *
              (∫ t in (-T)..T, Gfun x z (((cP : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
            = (1/(2*Real.pi)) * R := by
          have hc : (1 / (2 * (Real.pi : ℂ))) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
            push_cast; ring
          rw [norm_mul, hc, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by positivity : (0:ℝ) < 1/(2*Real.pi)), hRdef]
        have h5 : ‖(roughSum z w : ℂ) - (1/(2*Real.pi)) *
              (∫ t in (-T)..T, Gfun x z (((cP : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ ≤ ER := by
          rw [norm_sub_rev]
          exact hPA
        rw [h4] at h3
        linarith only [h3, h5]
      have hxdelta : x ^ (-δ) ≤ 2 * Real.exp (-(Real.log w / Real.log z)) := by
        have hxw : w / 2 ≤ x := by rw [hxdef]; linarith [Nat.lt_floor_add_one w]
        have hlog : Real.log w - Real.log 2 ≤ Real.log x := by
          have h1 : Real.log (w / 2) ≤ Real.log x := Real.log_le_log (by positivity) hxw
          rwa [Real.log_div (ne_of_gt hwpos) (by norm_num)] at h1
        have hkey : -(δ * Real.log x) ≤ -(δ * Real.log w) + δ * Real.log 2 := by
          nlinarith only [hlog, hδ0.le]
        have h4 : x ^ (-δ) = Real.exp (-(δ * Real.log x)) := by
          rw [Real.rpow_def_of_pos hxpos]; ring_nf
        have h8 : δ * Real.log 2 ≤ Real.log 2 := by
          have h := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
          nlinarith only [hδ1, h]
        calc x ^ (-δ) = Real.exp (-(δ * Real.log x)) := h4
          _ ≤ Real.exp (-(δ * Real.log w) + δ * Real.log 2) := Real.exp_le_exp.mpr hkey
          _ = Real.exp (δ * Real.log 2) * Real.exp (-(Real.log w / Real.log z)) := by
              rw [← Real.exp_add]
              congr 1
              rw [hδdef]; ring
          _ ≤ 2 * Real.exp (-(Real.log w / Real.log z)) := by
              apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
              calc Real.exp (δ * Real.log 2) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr h8
                _ = 2 := Real.exp_log (by norm_num)
      have hB1 : (1/(2*Real.pi)) * E1 ≤ Kp * A1 := by
        rw [hE1def, hA1def]
        have hQ0 : (0:ℝ) ≤ Real.log (T + 2) + 1 := by
          have h := Real.log_nonneg (by linarith : (1:ℝ) ≤ T + 2); linarith
        have hR0 : (0:ℝ) ≤ Real.log T + 1 := by
          have h := Real.log_nonneg hT1; linarith
        have h5 : (0:ℝ) ≤ c0 * Real.log z := by linarith only [hbig]
        have h6 : (0:ℝ) ≤ (c0/2) * Real.log z := by linarith only [hbig]
        have hQR : 2 * (Real.log (T + 2) + 1) * (Real.log T + 1)
            ≤ 2 * (c0 * Real.log z) * ((c0/2) * Real.log z) := by
          apply mul_le_mul
          · linarith only [hlogT2p]
          · exact hlogTp
          · have h4 : (0:ℝ) ≤ Real.log T + 1 := by
              have h := Real.log_nonneg hT1; linarith
            exact h4
          · linarith only [h5]
        have hkey : x ^ (-δ) * (CP * (Real.log z) ^ 3) *
              (Cb * (2 * (Real.log (T + 2) + 1) * (Real.log T + 1)))
            ≤ (2 * Real.exp (-(Real.log w / Real.log z))) * (CP * (Real.log z) ^ 3) *
              (Cb * (2 * (c0 * Real.log z) * ((c0/2) * Real.log z))) := by
          have hA : x ^ (-δ) * (CP * (Real.log z) ^ 3)
              ≤ (2 * Real.exp (-(Real.log w / Real.log z))) * (CP * (Real.log z) ^ 3) :=
            mul_le_mul_of_nonneg_right hxdelta
              (mul_nonneg hCPpos.le (pow_nonneg hlogzpos.le 3))
          have hB : Cb * (2 * (Real.log (T + 2) + 1) * (Real.log T + 1))
              ≤ Cb * (2 * (c0 * Real.log z) * ((c0/2) * Real.log z)) :=
            mul_le_mul_of_nonneg_left hQR hCbpos.le
          have hc : (0:ℝ) ≤ Cb * (2 * (Real.log (T + 2) + 1) * (Real.log T + 1)) :=
            mul_nonneg hCbpos.le (mul_nonneg (mul_nonneg (by norm_num) hQ0) hR0)
          have hb : (0:ℝ) ≤ (2 * Real.exp (-(Real.log w / Real.log z))) * (CP * (Real.log z) ^ 3) :=
            mul_nonneg (mul_nonneg (by norm_num) (Real.exp_nonneg _))
              (mul_nonneg hCPpos.le (pow_nonneg hlogzpos.le 3))
          calc x ^ (-δ) * (CP * (Real.log z) ^ 3) *
                (Cb * (2 * (Real.log (T + 2) + 1) * (Real.log T + 1)))
              = (x ^ (-δ) * (CP * (Real.log z) ^ 3)) *
                (Cb * (2 * (Real.log (T + 2) + 1) * (Real.log T + 1))) := by ring
            _ ≤ ((2 * Real.exp (-(Real.log w / Real.log z))) * (CP * (Real.log z) ^ 3)) *
                (Cb * (2 * (c0 * Real.log z) * ((c0/2) * Real.log z))) :=
                mul_le_mul hA hB hc hb
            _ = (2 * Real.exp (-(Real.log w / Real.log z))) * (CP * (Real.log z) ^ 3) *
                (Cb * (2 * (c0 * Real.log z) * ((c0/2) * Real.log z))) := by ring
        have hconst : (1/(2*Real.pi)) * ((2 * Real.exp (-(Real.log w / Real.log z))) *
              (CP * (Real.log z) ^ 3) * (Cb * (2 * (c0 * Real.log z) * ((c0/2) * Real.log z))))
            ≤ Kp * (Real.exp (-(Real.log w / Real.log z)) * (Real.log z) ^ 5) := by
          have hfac : (2 * CP * (Cb * (2 * c0 * (c0/2)))) / (2*Real.pi) ≤ 2 * CP * Cb := by
            rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*Real.pi)]
            have h2 : c0 * c0 ≤ 1 := by nlinarith only [hc0pos.le, hc0le1]
            have h3 : 2 * c0 * (c0/2) ≤ 1 := by nlinarith only [h2]
            have h4 : Cb * (2 * c0 * (c0/2)) ≤ Cb := by
              calc Cb * (2 * c0 * (c0/2)) ≤ Cb * 1 := mul_le_mul_of_nonneg_left h3 hCbpos.le
                _ = Cb := mul_one _
            have h5 : 2 * CP * (Cb * (2 * c0 * (c0/2))) ≤ 2 * CP * Cb :=
              mul_le_mul_of_nonneg_left h4 (by positivity)
            have h7 : (1:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
            have h6 : 2 * CP * Cb ≤ 2 * CP * Cb * (2 * Real.pi) := by
              have hX0 : (0:ℝ) ≤ 2 * CP * Cb := by positivity
              nlinarith only [hX0, h7]
            linarith only [h5, h6]
          have hfac' : (2 * CP * (Cb * (2 * c0 * (c0/2)))) / (2*Real.pi) ≤ Kp :=
            le_trans hfac hKp2Cb
          calc (1/(2*Real.pi)) * ((2 * Real.exp (-(Real.log w / Real.log z))) *
                (CP * (Real.log z) ^ 3) * (Cb * (2 * (c0 * Real.log z) * ((c0/2) * Real.log z))))
              = Real.exp (-(Real.log w / Real.log z)) * (Real.log z) ^ 5 *
                ((2 * CP * (Cb * (2 * c0 * (c0/2)))) / (2*Real.pi)) := by ring
            _ ≤ Real.exp (-(Real.log w / Real.log z)) * (Real.log z) ^ 5 * Kp :=
                mul_le_mul_of_nonneg_left hfac'
                  (mul_nonneg (Real.exp_nonneg _) (pow_nonneg hlogzpos.le 5))
            _ = Kp * (Real.exp (-(Real.log w / Real.log z)) * (Real.log z) ^ 5) := by ring
        exact le_trans (mul_le_mul_of_nonneg_left hkey (by positivity)) hconst
      have hB2 : (1/(2*Real.pi)) * E2 ≤ Kp * B1 := by
        rw [hE2def, hB1def]
        have hcore : (1/(2*Real.pi)) * (2 * ((cP + δ) * (Real.exp 1 * CP * Cζ))) ≤ Kp := by
          have h2 : cP + δ ≤ 2 := by linarith only [hcP1, hδ1]
          have hX : (0:ℝ) ≤ Real.exp 1 * CP * Cζ := by positivity
          have hstep : (2 * ((cP + δ) * (Real.exp 1 * CP * Cζ)))
              ≤ 2 * (2 * (Real.exp 1 * CP * Cζ)) := by
            nlinarith only [h2, hX]
          have h1 : (1/(2*Real.pi)) * (2 * ((cP + δ) * (Real.exp 1 * CP * Cζ))) ≤
              Real.exp 1 * 3 * CP * Cζ := by
            have ha : (1/(2*Real.pi)) * (2 * ((cP + δ) * (Real.exp 1 * CP * Cζ)))
                ≤ (1/(2*Real.pi)) * (2 * (2 * (Real.exp 1 * CP * Cζ))) :=
              mul_le_mul_of_nonneg_left hstep (by positivity)
            have hb : (1/(2*Real.pi)) * (2 * (2 * (Real.exp 1 * CP * Cζ)))
                ≤ Real.exp 1 * 3 * CP * Cζ := by
              rw [show (1/(2*Real.pi)) * (2 * (2 * (Real.exp 1 * CP * Cζ)))
                  = (2 * (Real.exp 1 * CP * Cζ)) / Real.pi by field_simp]
              rw [show Real.exp 1 * 3 * CP * Cζ = 3 * (Real.exp 1 * CP * Cζ) by ring]
              rw [div_le_iff₀ Real.pi_pos]
              nlinarith only [Real.pi_gt_three, hX]
            linarith only [ha, hb]
          linarith only [h1, hKpexp]
        have hQ0 : (0:ℝ) ≤ Real.log (T + 2) + 1 := by
          have h := Real.log_nonneg (by linarith : (1:ℝ) ≤ T + 2); linarith
        calc (1/(2*Real.pi)) * (2 * ((cP + δ) * (Real.exp 1 * (CP * (Real.log z) ^ 3) *
              (Cζ * ((Real.log (T + 2) + 1) / T)))))
            = ((Real.log z) ^ 3 * (Real.log (T + 2) + 1) / T) *
              ((1/(2*Real.pi)) * (2 * ((cP + δ) * (Real.exp 1 * CP * Cζ)))) := by
              field_simp
          _ ≤ ((Real.log z) ^ 3 * (Real.log (T + 2) + 1) / T) * Kp :=
              mul_le_mul_of_nonneg_left hcore
                (div_nonneg (mul_nonneg (pow_nonneg hlogzpos.le 3) hQ0) hTpos.le)
          _ = Kp * ((Real.log z) ^ 3 * (Real.log (T + 2) + 1) / T) := by ring
      have hB3 : ER ≤ Kp * C1 := by
        rw [hERdef, hC1def]
        have hlx : Real.log x + 1 ≤ 3 * (Real.log w + 1) := by
          have h1 : x ≤ 2 * w := by rw [hxdef]; linarith [Nat.floor_le (by linarith : (0:ℝ) ≤ w)]
          have h2 : Real.log x ≤ Real.log (2*w) := Real.log_le_log hxpos (by linarith)
          have h3 : Real.log (2*w) = Real.log 2 + Real.log w := Real.log_mul (by norm_num) (ne_of_gt hwpos)
          have h4 : Real.log 2 ≤ 1 := by
            have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
          have h5 : (1:ℝ) ≤ Real.log w := by
            have h := Real.log_le_log (by norm_num : (0:ℝ) < 3) hw3
            linarith [Real.log_three_gt_d9, h]
          rw [h3] at h2
          linarith
        have hnum : Cper * (Cerr * (Real.log x + 1)) ≤ Kp * (3 * (Real.log w + 1)) := by
          have h1 : Cerr * (Real.log x + 1) ≤ Cerr * (3 * (Real.log w + 1)) :=
            mul_le_mul_of_nonneg_left hlx hCerrpos.le
          have h2 : Cper * (Cerr * (Real.log x + 1)) ≤ Cper * (Cerr * (3 * (Real.log w + 1))) :=
            mul_le_mul_of_nonneg_left h1 hCperpos.le
          have h3 : Cper * (Cerr * (3 * (Real.log w + 1))) = (Cper * Cerr) * (3 * (Real.log w + 1)) := by ring
          rw [h3] at h2
          refine le_trans h2 (mul_le_mul_of_nonneg_right hKperr ?_)
          have h := Real.log_nonneg (by linarith : (1:ℝ) ≤ w)
          linarith
        calc Cper * (Cerr * (Real.log x + 1) / T)
            = (Cper * (Cerr * (Real.log x + 1))) / T := by ring
          _ ≤ (Kp * (3 * (Real.log w + 1))) / T := div_le_div_of_nonneg_right hnum hTpos.le
          _ = Kp * (3 * (Real.log w + 1) / T) := by ring
      have hgoal : |roughSum z w| ≤ Kp * (Real.exp (-(Real.log w / Real.log z)) * (Real.log z) ^ 5
            + (Real.log z) ^ 3 * (Real.log (T + 2) + 1) / T + 3 * (Real.log w + 1) / T) := by
        rw [← hA1def, ← hB1def, ← hC1def]
        have h1 : |roughSum z w| = ‖(roughSum z w : ℂ)‖ := (Complex.norm_real _).symm
        rw [h1]
        have hexp : (1/(2*Real.pi)) * (E1 + E2)
            = (1/(2*Real.pi)) * E1 + (1/(2*Real.pi)) * E2 := by ring
        calc ‖(roughSum z w : ℂ)‖ ≤ (1/(2*Real.pi)) * R + ER := hstep1
          _ ≤ (1/(2*Real.pi)) * (E1 + E2) + Kp * C1 := by
              linarith only [mul_le_mul_of_nonneg_left hRA (by positivity : (0:ℝ) ≤ 1/(2*Real.pi)), hB3]
          _ ≤ Kp * A1 + Kp * B1 + Kp * C1 := by
              linarith only [hexp, hB1, hB2]
          _ = Kp * (A1 + B1 + C1) := by ring
      rw [hTdef] at hgoal
      refine le_trans hgoal (le_trans (hKA z w hzA hw3 hzw hcaseA) ?_)
      exact mul_le_mul_of_nonneg_right hCfin_KA (add_nonneg (Real.rpow_nonneg hzpos.le _) hE)
    · -- ================= CASE B =================
      push_neg at hcaseA
      set L : ℝ := Real.log w / Real.log z with hLdef
      have hLgt : Real.log z < L := hcaseA
      have hLge1 : (1:ℝ) ≤ L := by linarith only [hLgt, hlogz400]
      have hLbig : (400:ℝ) ≤ L := by linarith only [hLgt, hlogz400]
      have hlogL : (0:ℝ) ≤ Real.log L := Real.log_nonneg hLge1
      set S : ℝ := c0 * Real.log z + Real.log L + 20 with hSdef
      have hSpos : 0 < S := by rw [hSdef]; linarith only [hbig, hlogL]
      have hS22 : S + 2 = c0 * Real.log z + Real.log L + 22 := by rw [hSdef]; ring
      have hS23 : S + 3 = c0 * Real.log z + Real.log L + 23 := by rw [hSdef]; ring
      have hS21 : S + 1 = c0 * Real.log z + Real.log L + 21 := by rw [hSdef]; ring
      have hc0S2 : 0 < S + 2 := by linarith
      set x : ℝ := ⌊w⌋₊ + 1/2 with hxdef
      have hwfloor : (3:ℝ) ≤ ⌊w⌋₊ := by
        have h : 3 ≤ ⌊w⌋₊ := Nat.le_floor (by linarith : (3:ℝ) ≤ w)
        exact_mod_cast h
      have hx3 : (3:ℝ) ≤ x := by rw [hxdef]; linarith
      have hx1 : (1:ℝ) < x := by linarith
      have hxpos : (0:ℝ) < x := by linarith
      have hlogx1 : 1 ≤ Real.log x := by
        have h := Real.log_le_log (by norm_num : (0:ℝ) < 3) hx3
        linarith [Real.log_three_gt_d9, h]
      have hxfloor : ⌊x⌋₊ = ⌊w⌋₊ := by
        rw [hxdef]
        refine (Nat.floor_eq_iff (a := (⌊w⌋₊ : ℝ) + 1/2) (n := ⌊w⌋₊) (by positivity)).mpr
          ⟨by linarith, by linarith⟩
      have hxnn : ∀ n : ℕ, (n : ℝ) ≠ x := by
        intro n h
        have hfl : ⌊(n : ℝ)⌋₊ = ⌊w⌋₊ := by
          rw [h, hxdef]
          refine (Nat.floor_eq_iff (a := (⌊w⌋₊ : ℝ) + 1/2) (n := ⌊w⌋₊) (by positivity)).mpr
            ⟨by linarith, by linarith⟩
        rw [Nat.floor_natCast] at hfl
        rw [hxdef, ← hfl] at h
        norm_num at h
      set δ : ℝ := c0 / (S + 2) with hδdef
      set T : ℝ := Real.exp S with hTdef
      set cP : ℝ := 1/Real.log x with hcPdef2
      have hδ0 : 0 < δ := by rw [hδdef]; positivity
      have hδ1 : δ ≤ 1 := by rw [hδdef, div_le_one hc0S2]; linarith only [hc0le1, hSpos]
      have hδlt1 : δ < 1 := by rw [hδdef, div_lt_one hc0S2]; linarith only [hc0le1, hSpos]
      have hδlelogz : δ ≤ 1 / Real.log z := by
        rw [hδdef, div_le_div_iff₀ hc0S2 hlogzpos, hS22]
        linarith only [hlogL]
      have hδc0 : δ ≤ c0 := by
        rw [hδdef, div_le_iff₀ hc0S2]
        nlinarith only [hc0pos.le, hSpos]
      have hT1 : 1 ≤ T := by rw [hTdef]; exact Real.one_le_exp hSpos.le
      have hTpos : 0 < T := lt_of_lt_of_le one_pos hT1
      have hlogT : Real.log T = S := by rw [hTdef, Real.log_exp]
      have hlogT2 : Real.log (T + 2) ≤ S + 2 := by
        have h3 : T + 2 ≤ 3 * T := by rw [hTdef]; nlinarith [Real.one_le_exp hSpos.le]
        have h4 : Real.log (T + 2) ≤ Real.log (3 * T) := Real.log_le_log (by positivity) h3
        have h5 : Real.log (3 * T) = Real.log 3 + S := by
          rw [Real.log_mul (by norm_num) (ne_of_gt hTpos), hlogT]
        have h6 : Real.log 3 ≤ 2 := by
          have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 3); linarith
        linarith only [h4, h5, h6]
      have hδT : δ * Real.log (T + 2) ≤ c0 := by
        rw [hδdef, div_mul_eq_mul_div, div_le_iff₀ hc0S2]
        nlinarith only [hlogT2, hc0pos.le]
      have hcPpos : 0 < cP := by rw [hcPdef2]; exact div_pos one_pos (Real.log_pos hx1)
      have hcP1 : cP ≤ 1 := by rw [hcPdef2, div_le_one (Real.log_pos hx1)]; exact hlogx1
      have hcPlog : cP * Real.log x ≤ 1 := by
        rw [hcPdef2, div_mul_cancel₀ _ (ne_of_gt (Real.log_pos hx1))]
      have hPz : ∀ u : ℂ, 1 - 1/Real.log z ≤ u.re → u.re ≤ 2 →
          ‖Pz z u‖ ≤ CP * (Real.log z) ^ 3 := by
        intro u h1 h2
        refine le_trans (hPz0 z hz u h1 h2) ?_
        exact mul_le_mul_of_nonneg_right (le_max_left CP0 1)
          (pow_nonneg (Real.log_nonneg (by linarith)) 3)
      have hInvL : ∀ t : ℝ, |t| ≤ T →
          ‖(riemannZeta₁ (1 + (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)))⁻¹‖ ≤
            Cb * ((Real.log (|t| + 2) + 1) / max 1 |t|) := by
        intro t ht
        have h := inv_zeta1_le_gen hCζpos hrpos (by norm_num : (0:ℝ) < 2) hcζpos hD1 hnear0
          hδ0 (le_trans hδT hc0cζ) (s := (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I)) (by simp)
          (by simp; linarith) (by simpa using ht)
        have him : (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
        rw [him] at h
        rw [hCbdef]
        exact h
      have hInvH : ∀ σ : ℝ, -δ ≤ σ → σ ≤ cP →
          ‖(riemannZeta₁ (1 + (((σ : ℝ) : ℂ) + ((T : ℝ) : ℂ) * Complex.I)))⁻¹‖ ≤
            Cζ * ((Real.log (T + 2) + 1) / T) :=
        fun σ h1 h2 => inv_zeta1_horiz (τ := T) hcζpos hTpos hδ0 hcP1 (le_trans hδT hc0cζ)
          (abs_of_pos hTpos) hD1 h1 h2
      have hInvH' : ∀ σ : ℝ, -δ ≤ σ → σ ≤ cP →
          ‖(riemannZeta₁ (1 + (((σ : ℝ) : ℂ) + (((-T) : ℝ) : ℂ) * Complex.I)))⁻¹‖ ≤
            Cζ * ((Real.log (T + 2) + 1) / T) :=
        fun σ h1 h2 => inv_zeta1_horiz (τ := -T) hcζpos hTpos hδ0 hcP1 (le_trans hδT hc0cζ)
          (by rw [abs_neg, abs_of_pos hTpos]) hD1 h1 h2
      have hdiff : DifferentiableOn ℂ (Gfun x z) (Set.uIcc (-δ) cP ×ℂ Set.uIcc (-T) T) :=
        differentiableOn_Gfun_rect hxpos hδ0 hδlt1 hTpos hc0pos hδc0
          hcPpos hcP1 hδT hZFbig hZFsmall
      have hcontL : ContinuousOn (fun t : ℝ => Gfun x z (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I))
          (Set.uIcc (-T) T) := by
        refine hdiff.continuousOn.comp (by fun_prop) ?_
        intro t ht
        rw [Complex.mem_reProdIm]
        constructor
        · have h2 : (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = -δ := by simp
          rw [h2, Set.uIcc_of_le (by linarith : -δ ≤ cP)]
          exact ⟨le_rfl, by linarith⟩
        · have h2 : (((-δ : ℝ) : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
          rw [h2]
          exact ht
      set E1 : ℝ := x ^ (-δ) * (CP * (Real.log z) ^ 3) *
              (Cb * (2 * (Real.log (T + 2) + 1) * (Real.log T + 1))) with hE1def
      set E2 : ℝ := 2 * ((cP + δ) * (Real.exp 1 * (CP * (Real.log z) ^ 3) *
              (Cζ * ((Real.log (T + 2) + 1) / T)))) with hE2def
      set A1 : ℝ := (Real.log z) ^ 3 * (S + 3) * (S + 1) *
              Real.exp (-(c0 * L * Real.log z / (S + 2))) with hA1def
      set B1 : ℝ := (Real.log z) ^ 3 * (S + 3) / Real.exp S with hB1def
      set C1 : ℝ := 3 * (Real.log w + 1) / Real.exp S with hC1def
      set ER : ℝ := Cper * (Cerr * (Real.log x + 1) / T) with hERdef
      set R : ℝ := ‖∫ t in (-T)..T, Gfun x z (((cP : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ with hRdef
      have hRA : R ≤ E1 + E2 := by
        rw [hE1def, hE2def, hRdef]
        exact contour_bound hx1 hz hδ0 hδlt1 hδlelogz hcPpos hcP1 hcPlog hT1
          hdiff hcontL hPz hInvL hInvH hInvH' hCPpos.le hCbpos.le hCζpos.le
      have hT2B : (2:ℝ) ≤ T := by
        rw [hTdef]
        calc (2:ℝ) ≤ Real.exp 20 := by
              rw [← Real.exp_log (by norm_num : (0:ℝ) < 2)]
              apply Real.exp_le_exp.mpr
              have h3 : Real.log 2 ≤ 1 := by
                have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
              linarith
          _ ≤ Real.exp S := Real.exp_le_exp.mpr (by rw [hSdef]; linarith only [hbig, hlogL])
      have hTxB : T ≤ x := by
        rw [hTdef]
        have hxw : w / 2 ≤ x := by rw [hxdef]; linarith [Nat.lt_floor_add_one w]
        have hlogw : Real.log w = L * Real.log z := by
          rw [hLdef, div_mul_cancel₀ _ (ne_of_gt hlogzpos)]
        have hgoal : S + Real.log 2 ≤ Real.log w := by
          rw [hlogw, hSdef]
          have hc0' : c0 * Real.log z ≤ L * Real.log z / 2 := by
            have h : c0 ≤ L / 2 := by linarith only [hLbig, hc0le1]
            nlinarith only [h, hlogzpos.le]
          have hlogL : Real.log L + 20 + Real.log 2 ≤ L * Real.log z / 2 := by
            have h1 : Real.log L ≤ L - 1 := Real.log_le_sub_one_of_pos (by linarith only [hLge1])
            have h2 : Real.log 2 ≤ 1 := by
              have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
            have h3 : 200 * L ≤ L * Real.log z / 2 := by
              have h : (200:ℝ) ≤ Real.log z / 2 := by linarith only [hlogz400]
              nlinarith only [h, hLge1]
            linarith only [h1, h2, h3, hLge1]
          linarith only [hc0', hlogL]
        calc Real.exp S ≤ Real.exp (Real.log w - Real.log 2) :=
              Real.exp_le_exp.mpr (by linarith only [hgoal])
          _ = w / 2 := by
              rw [Real.exp_sub, Real.exp_log (by linarith : (0:ℝ) < w),
                Real.exp_log (by norm_num : (0:ℝ) < 2)]
          _ ≤ x := hxw
      have hPA : ‖(1/(2*Real.pi)) * (∫ t in (-T)..T, Gfun x z (((1 / Real.log x : ℝ) : ℂ) + (t : ℂ) * Complex.I))
            - (roughSum z w : ℂ)‖ ≤ ER := by
        rw [hERdef]
        exact perron_approx hxfloor hx3 hT2B hTxB hxnn (by linarith : (0:ℝ) ≤ z) hCperpos.le hper hCerr
      have hstep1 : ‖(roughSum z w : ℂ)‖ ≤ (1/(2*Real.pi)) * R + ER := by
        have h3 : ‖(roughSum z w : ℂ)‖ ≤
            ‖(roughSum z w : ℂ) - (1/(2*Real.pi)) * (∫ t in (-T)..T, Gfun x z (((cP : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
              + ‖(1/(2*Real.pi)) * (∫ t in (-T)..T, Gfun x z (((cP : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ := by
          calc ‖(roughSum z w : ℂ)‖
              = ‖((roughSum z w : ℂ) - (1/(2*Real.pi)) *
                  (∫ t in (-T)..T, Gfun x z (((cP : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
                  + (1/(2*Real.pi)) *
                  (∫ t in (-T)..T, Gfun x z (((cP : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ := by
                congr 1; ring
            _ ≤ _ := norm_add_le _ _
        have h4 : ‖(1/(2*Real.pi)) *
              (∫ t in (-T)..T, Gfun x z (((cP : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖
            = (1/(2*Real.pi)) * R := by
          have hc : (1 / (2 * (Real.pi : ℂ))) = ((1 / (2 * Real.pi) : ℝ) : ℂ) := by
            push_cast; ring
          rw [norm_mul, hc, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by positivity : (0:ℝ) < 1/(2*Real.pi)), hRdef]
        have h5 : ‖(roughSum z w : ℂ) - (1/(2*Real.pi)) *
              (∫ t in (-T)..T, Gfun x z (((cP : ℝ) : ℂ) + (t : ℂ) * Complex.I))‖ ≤ ER := by
          rw [norm_sub_rev]
          exact hPA
        rw [h4] at h3
        linarith only [h3, h5]
      have hxdelta : x ^ (-δ) ≤ 2 * Real.exp (-(c0 * L * Real.log z / (S + 2))) := by
        have hxw : w / 2 ≤ x := by rw [hxdef]; linarith [Nat.lt_floor_add_one w]
        have hlog : Real.log w - Real.log 2 ≤ Real.log x := by
          have h1 : Real.log (w / 2) ≤ Real.log x := Real.log_le_log (by positivity) hxw
          rwa [Real.log_div (ne_of_gt hwpos) (by norm_num)] at h1
        have hdw : δ * Real.log w = c0 * L * Real.log z / (S + 2) := by
          rw [hδdef, hLdef]
          field_simp
        have hkey : -(δ * Real.log x) ≤ -(c0 * L * Real.log z / (S + 2)) + δ * Real.log 2 := by
          nlinarith only [hlog, hδ0.le, hdw]
        have h4 : x ^ (-δ) = Real.exp (-(δ * Real.log x)) := by
          rw [Real.rpow_def_of_pos hxpos]; ring_nf
        have h8 : δ * Real.log 2 ≤ Real.log 2 := by
          have h := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
          nlinarith only [hδ1, h]
        calc x ^ (-δ) = Real.exp (-(δ * Real.log x)) := h4
          _ ≤ Real.exp (-(c0 * L * Real.log z / (S + 2)) + δ * Real.log 2) :=
              Real.exp_le_exp.mpr hkey
          _ = Real.exp (δ * Real.log 2) * Real.exp (-(c0 * L * Real.log z / (S + 2))) := by
              rw [← Real.exp_add]; ring_nf
          _ ≤ 2 * Real.exp (-(c0 * L * Real.log z / (S + 2))) := by
              apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
              calc Real.exp (δ * Real.log 2) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr h8
                _ = 2 := Real.exp_log (by norm_num)
      have hQ0 : (0:ℝ) ≤ Real.log (T + 2) + 1 := by
        have h := Real.log_nonneg (by linarith : (1:ℝ) ≤ T + 2); linarith
      have hR0 : (0:ℝ) ≤ Real.log T + 1 := by
        have h := Real.log_nonneg hT1; linarith
      have hS3 : (0:ℝ) ≤ S + 3 := by linarith
      have hS1 : (0:ℝ) ≤ S + 1 := by linarith
      have hB1 : (1/(2*Real.pi)) * E1 ≤ Kp * A1 := by
        rw [hE1def, hA1def]
        have hQR : 2 * (Real.log (T + 2) + 1) * (Real.log T + 1) ≤ 2 * (S + 3) * (S + 1) := by
          have h1 : 2 * (Real.log (T + 2) + 1) ≤ 2 * (S + 3) := by linarith only [hlogT2]
          have h2 : Real.log T + 1 ≤ S + 1 := by linarith only [hlogT]
          exact mul_le_mul h1 h2 (by linarith only [hlogT, hSpos]) (by linarith only [hS3])
        have hkey : x ^ (-δ) * (CP * (Real.log z) ^ 3) *
              (Cb * (2 * (Real.log (T + 2) + 1) * (Real.log T + 1)))
            ≤ (2 * Real.exp (-(c0 * L * Real.log z / (S + 2)))) * (CP * (Real.log z) ^ 3) *
              (Cb * (2 * (S + 3) * (S + 1))) := by
          have hA : x ^ (-δ) * (CP * (Real.log z) ^ 3)
              ≤ (2 * Real.exp (-(c0 * L * Real.log z / (S + 2)))) * (CP * (Real.log z) ^ 3) :=
            mul_le_mul_of_nonneg_right hxdelta
              (mul_nonneg hCPpos.le (pow_nonneg hlogzpos.le 3))
          have hB : Cb * (2 * (Real.log (T + 2) + 1) * (Real.log T + 1))
              ≤ Cb * (2 * (S + 3) * (S + 1)) := mul_le_mul_of_nonneg_left hQR hCbpos.le
          have hc : (0:ℝ) ≤ Cb * (2 * (Real.log (T + 2) + 1) * (Real.log T + 1)) :=
            mul_nonneg hCbpos.le (mul_nonneg (mul_nonneg (by norm_num) hQ0) hR0)
          have hb : (0:ℝ) ≤ (2 * Real.exp (-(c0 * L * Real.log z / (S + 2)))) *
              (CP * (Real.log z) ^ 3) :=
            mul_nonneg (mul_nonneg (by norm_num) (Real.exp_nonneg _))
              (mul_nonneg hCPpos.le (pow_nonneg hlogzpos.le 3))
          calc x ^ (-δ) * (CP * (Real.log z) ^ 3) *
                (Cb * (2 * (Real.log (T + 2) + 1) * (Real.log T + 1)))
              = (x ^ (-δ) * (CP * (Real.log z) ^ 3)) *
                (Cb * (2 * (Real.log (T + 2) + 1) * (Real.log T + 1))) := by ring
            _ ≤ ((2 * Real.exp (-(c0 * L * Real.log z / (S + 2)))) * (CP * (Real.log z) ^ 3)) *
                (Cb * (2 * (S + 3) * (S + 1))) := mul_le_mul hA hB hc hb
            _ = (2 * Real.exp (-(c0 * L * Real.log z / (S + 2)))) * (CP * (Real.log z) ^ 3) *
                (Cb * (2 * (S + 3) * (S + 1))) := by ring
        have hconst : (1/(2*Real.pi)) * ((2 * Real.exp (-(c0 * L * Real.log z / (S + 2)))) *
              (CP * (Real.log z) ^ 3) * (Cb * (2 * (S + 3) * (S + 1))))
            ≤ Kp * ((Real.log z) ^ 3 * (S + 3) * (S + 1) *
              Real.exp (-(c0 * L * Real.log z / (S + 2)))) := by
          have hfac : (2 * CP * (Cb * 2)) / (2*Real.pi) ≤ 2 * CP * Cb := by
            rw [div_le_iff₀ (by positivity : (0:ℝ) < 2*Real.pi)]
            have hX0 : (0:ℝ) ≤ 2 * CP * Cb := by positivity
            have h4 : (4:ℝ) ≤ 4 * Real.pi := by linarith [Real.pi_gt_three]
            nlinarith only [hX0, h4]
          have hfac' : (2 * CP * (Cb * 2)) / (2*Real.pi) ≤ Kp := le_trans hfac hKp2Cb
          have hE : (0:ℝ) ≤ Real.exp (-(c0 * L * Real.log z / (S + 2))) := Real.exp_nonneg _
          calc (1/(2*Real.pi)) * ((2 * Real.exp (-(c0 * L * Real.log z / (S + 2)))) *
                (CP * (Real.log z) ^ 3) * (Cb * (2 * (S + 3) * (S + 1))))
              = Real.exp (-(c0 * L * Real.log z / (S + 2))) * (Real.log z) ^ 3 * (S + 3) * (S + 1) *
                ((2 * CP * (Cb * 2)) / (2*Real.pi)) := by ring
            _ ≤ Real.exp (-(c0 * L * Real.log z / (S + 2))) * (Real.log z) ^ 3 * (S + 3) * (S + 1) * Kp :=
                mul_le_mul_of_nonneg_left hfac'
                  (by positivity)
            _ = Kp * ((Real.log z) ^ 3 * (S + 3) * (S + 1) *
                Real.exp (-(c0 * L * Real.log z / (S + 2)))) := by ring
        exact le_trans (mul_le_mul_of_nonneg_left hkey (by positivity)) hconst
      have hB2 : (1/(2*Real.pi)) * E2 ≤ Kp * B1 := by
        rw [hE2def, hB1def]
        have hcore : (1/(2*Real.pi)) * (2 * ((cP + δ) * (Real.exp 1 * CP * Cζ))) ≤ Kp := by
          have h2 : cP + δ ≤ 2 := by linarith only [hcP1, hδ1]
          have hX : (0:ℝ) ≤ Real.exp 1 * CP * Cζ := by positivity
          have hstep : (2 * ((cP + δ) * (Real.exp 1 * CP * Cζ)))
              ≤ 2 * (2 * (Real.exp 1 * CP * Cζ)) := by nlinarith only [h2, hX]
          have h1 : (1/(2*Real.pi)) * (2 * ((cP + δ) * (Real.exp 1 * CP * Cζ))) ≤
              Real.exp 1 * 3 * CP * Cζ := by
            have ha : (1/(2*Real.pi)) * (2 * ((cP + δ) * (Real.exp 1 * CP * Cζ)))
                ≤ (1/(2*Real.pi)) * (2 * (2 * (Real.exp 1 * CP * Cζ))) :=
              mul_le_mul_of_nonneg_left hstep (by positivity)
            have hb : (1/(2*Real.pi)) * (2 * (2 * (Real.exp 1 * CP * Cζ)))
                ≤ Real.exp 1 * 3 * CP * Cζ := by
              rw [show (1/(2*Real.pi)) * (2 * (2 * (Real.exp 1 * CP * Cζ)))
                  = (2 * (Real.exp 1 * CP * Cζ)) / Real.pi by field_simp]
              rw [show Real.exp 1 * 3 * CP * Cζ = 3 * (Real.exp 1 * CP * Cζ) by ring]
              rw [div_le_iff₀ Real.pi_pos]
              nlinarith only [Real.pi_gt_three, hX]
            linarith only [ha, hb]
          linarith only [h1, hKpexp]
        calc (1/(2*Real.pi)) * (2 * ((cP + δ) * (Real.exp 1 * (CP * (Real.log z) ^ 3) *
              (Cζ * ((Real.log (T + 2) + 1) / T)))))
            = ((Real.log z) ^ 3 * (Real.log (T + 2) + 1) / T) *
              ((1/(2*Real.pi)) * (2 * ((cP + δ) * (Real.exp 1 * CP * Cζ)))) := by
              field_simp
          _ ≤ ((Real.log z) ^ 3 * (S + 3) / Real.exp S) * Kp := by
              have hL1 : (Real.log z) ^ 3 * (Real.log (T + 2) + 1) / T
                  ≤ (Real.log z) ^ 3 * (S + 3) / Real.exp S := by
                apply div_le_div_of_nonneg_right _ (Real.exp_pos S).le
                exact mul_le_mul_of_nonneg_left (by linarith only [hlogT2])
                  (pow_nonneg hlogzpos.le 3)
              have hc0' : (0:ℝ) ≤ 1 / (2*Real.pi) * (2 * ((cP + δ) * (Real.exp 1 * CP * Cζ))) := by
                have h1 : (0:ℝ) ≤ cP + δ := by linarith only [hcPpos.le, hδ0.le]
                have h2 : (0:ℝ) ≤ Real.exp 1 * CP * Cζ := by positivity
                positivity
              exact mul_le_mul hL1 hcore hc0'
                (div_nonneg (mul_nonneg (pow_nonneg hlogzpos.le 3) hS3) (Real.exp_pos S).le)
          _ = Kp * ((Real.log z) ^ 3 * (S + 3) / Real.exp S) := by ring
      have hB3 : ER ≤ Kp * C1 := by
        rw [hERdef, hC1def]
        have hlx : Real.log x + 1 ≤ 3 * (Real.log w + 1) := by
          have h1 : x ≤ 2 * w := by rw [hxdef]; linarith [Nat.floor_le (by linarith : (0:ℝ) ≤ w)]
          have h2 : Real.log x ≤ Real.log (2*w) := Real.log_le_log hxpos (by linarith)
          have h3 : Real.log (2*w) = Real.log 2 + Real.log w := Real.log_mul (by norm_num) (ne_of_gt hwpos)
          have h4 : Real.log 2 ≤ 1 := by
            have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 2); linarith
          have h5 : (1:ℝ) ≤ Real.log w := by
            have h := Real.log_le_log (by norm_num : (0:ℝ) < 3) hw3
            linarith [Real.log_three_gt_d9, h]
          rw [h3] at h2
          linarith
        have hnum : Cper * (Cerr * (Real.log x + 1)) ≤ Kp * (3 * (Real.log w + 1)) := by
          have h1 : Cerr * (Real.log x + 1) ≤ Cerr * (3 * (Real.log w + 1)) :=
            mul_le_mul_of_nonneg_left hlx hCerrpos.le
          have h2 : Cper * (Cerr * (Real.log x + 1)) ≤ Cper * (Cerr * (3 * (Real.log w + 1))) :=
            mul_le_mul_of_nonneg_left h1 hCperpos.le
          have h3 : Cper * (Cerr * (3 * (Real.log w + 1))) = (Cper * Cerr) * (3 * (Real.log w + 1)) := by ring
          rw [h3] at h2
          refine le_trans h2 (mul_le_mul_of_nonneg_right hKperr ?_)
          have h := Real.log_nonneg (by linarith : (1:ℝ) ≤ w)
          linarith
        calc Cper * (Cerr * (Real.log x + 1) / T)
            = (Cper * (Cerr * (Real.log x + 1))) / T := by ring
          _ ≤ (Kp * (3 * (Real.log w + 1))) / T := div_le_div_of_nonneg_right hnum hTpos.le
          _ = Kp * (3 * (Real.log w + 1) / T) := by ring
          _ = Kp * (3 * (Real.log w + 1) / Real.exp S) := by rw [hTdef]
      have hgoal : |roughSum z w| ≤ Kp * ((Real.log z) ^ 3 * (S + 3) * (S + 1) *
            Real.exp (-(c0 * L * Real.log z / (S + 2))) + (Real.log z) ^ 3 * (S + 3) / Real.exp S
            + 3 * (Real.log w + 1) / Real.exp S) := by
        rw [← hA1def, ← hB1def, ← hC1def]
        have h1 : |roughSum z w| = ‖(roughSum z w : ℂ)‖ := (Complex.norm_real _).symm
        rw [h1]
        have hexp : (1/(2*Real.pi)) * (E1 + E2) = (1/(2*Real.pi)) * E1 + (1/(2*Real.pi)) * E2 := by ring
        calc ‖(roughSum z w : ℂ)‖ ≤ (1/(2*Real.pi)) * R + ER := hstep1
          _ ≤ (1/(2*Real.pi)) * (E1 + E2) + Kp * C1 := by
              linarith only [mul_le_mul_of_nonneg_left hRA (by positivity : (0:ℝ) ≤ 1/(2*Real.pi)), hB3]
          _ ≤ Kp * A1 + Kp * B1 + Kp * C1 := by linarith only [hexp, hB1, hB2]
          _ = Kp * (A1 + B1 + C1) := by ring
      have hgoal' : |roughSum z w| ≤ Kp *
          ((Real.log z) ^ 3 * (c0 * Real.log z + Real.log (Real.log w / Real.log z) + 23)
              * (c0 * Real.log z + Real.log (Real.log w / Real.log z) + 21)
              * Real.exp (-(c0 * (Real.log w / Real.log z) * Real.log z
                  / (c0 * Real.log z + Real.log (Real.log w / Real.log z) + 22)))
            + (Real.log z) ^ 3 * (c0 * Real.log z + Real.log (Real.log w / Real.log z) + 23)
              / Real.exp (c0 * Real.log z + Real.log (Real.log w / Real.log z) + 20)
            + 3 * (Real.log w + 1)
              / Real.exp (c0 * Real.log z + Real.log (Real.log w / Real.log z) + 20)) := by
        rw [hS23, hS21, hS22, hSdef, hLdef] at hgoal
        exact hgoal
      refine le_trans hgoal' (le_trans (hKB z w hzB hw3 hzw hcaseA) ?_)
      calc KB * z ^ (-cf) ≤ Cfin * z ^ (-cf) :=
            mul_le_mul_of_nonneg_right hCfin_KB (Real.rpow_nonneg hzpos.le _)
        _ ≤ Cfin * (z ^ (-cf) + Real.exp (-(Real.log w / Real.log z)) * (Real.log z) ^ 6) :=
            mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hE) hCfinpos.le
/-- **The reciprocal Möbius sum over `z`-rough numbers**: there are absolute constants
`c, C > 0` such that for all `z ≥ 3`, `w ≥ 2` with `z ^ 2 ≤ w`,
`|Σ_{n ≤ w, P⁻(n) ≥ z} μ(n)/n| ≤ C (z^{-c} + exp(-log w/log z) (log z)^6)`.

(This is the analytic core of the Friedlander–Iwaniec asymptotic sieve; the proof
proceeds by the truncated Perron formula combined with a contour shift to the left
of the critical line, using the zero-free region and the bound `1/ζ ≪ log`.) -/
theorem moebius_rough_recip_large_z :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ z w : ℝ, 3 ≤ z → 2 ≤ w → z ^ 2 ≤ w →
      |∑ n ∈ (Finset.Icc 1 ⌊w⌋₊).filter (fun n => ∀ p : ℕ, p ∈ n.primeFactors → z ≤ (p : ℝ)),
          (ArithmeticFunction.moebius n : ℝ) / (n : ℝ)|
        ≤ C * (z ^ (-c) + Real.exp (-(Real.log w / Real.log z)) * (Real.log z) ^ 6) := by
  obtain ⟨CR, hCRpos, hCR⟩ := Commons.NumberTheory.Moebius.recip_perron_error_sum_le
  have hPerr : ∃ Cerr : ℝ, 0 < Cerr ∧ IsPerronErrorBound Cerr := by
    refine ⟨CR * (Real.exp 1 + 1), by positivity, ?_⟩
    intro x T hx3 hT2 hTx
    have hx0 : (0:ℝ) < x := by linarith
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hlogx1 : 1 ≤ Real.log x := by
      have h := Real.log_le_log (by norm_num : (0:ℝ) < 3) hx3
      linarith [Real.log_three_gt_d9, h]
    have hσ1 : 1 / Real.log x ≤ 1 := by rw [div_le_one hlogx]; exact hlogx1
    obtain ⟨-, hb⟩ := hCR x (1/Real.log x) T hx3 (by positivity) hσ1 hT2 hTx
    have hxe : x ^ (1 / Real.log x) = Real.exp 1 := by
      rw [Real.rpow_def_of_pos hx0]
      congr 1
      field_simp
    have hinv : 1 / (1 / Real.log x) = Real.log x := by field_simp
    rw [hxe] at hb
    refine le_trans hb ?_
    have hmain : CR * (Real.exp 1 * (1 + 1/(1/Real.log x)) + 1)
        ≤ CR * (Real.exp 1 + 1) * (Real.log x + 1) := by
      rw [hinv]
      have h2 : Real.exp 1 * (1 + Real.log x) + 1 ≤ (Real.exp 1 + 1) * (Real.log x + 1) := by
        have h3 : (0:ℝ) ≤ Real.log x := le_of_lt hlogx
        nlinarith only [h3, Real.exp_pos 1]
      calc CR * (Real.exp 1 * (1 + Real.log x) + 1)
            ≤ CR * ((Real.exp 1 + 1) * (Real.log x + 1)) := mul_le_mul_of_nonneg_left h2 hCRpos.le
        _ = CR * (Real.exp 1 + 1) * (Real.log x + 1) := by ring
    exact div_le_div_of_nonneg_right hmain (by linarith : (0:ℝ) ≤ T)
  obtain ⟨c, C, hc, hC, hbnd⟩ := main_bound_of_inputs hPerr
    (fun c0 Kp h1 h2 h3 => Commons.Analysis.ExpLog.case_B_arith c0 Kp h1 h2 h3)
  refine ⟨c, C, hc, hC, fun z w hz hw hzw => ?_⟩
  have h := hbnd z w hz hw hzw
  rw [roughSum] at h
  have hf : (Finset.Icc 1 ⌊w⌋₊).filter (fun n => Rough z n)
      = (Finset.Icc 1 ⌊w⌋₊).filter (fun n => ∀ p : ℕ, p ∈ n.primeFactors → z ≤ (p : ℝ)) := by
    apply Finset.filter_congr
    intro n _
    exact Iff.rfl
  rw [hf] at h
  exact h

end Commons.NumberTheory.Sieve
