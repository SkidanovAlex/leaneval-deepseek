/-
# `Submission.Work.FIArea5.S16Hecke.heckeL_inv_halfPlane`

**FI (16.23)/(16.24), the "trivial" inverse bound.**  For a completely multiplicative, bounded
`χ : ℤ[i] → ℂ` (with `χ 1 = 1`) and any `k : ℤ`, the Hecke `L`-series
`L(s,ψ) = Σ_n λ(n) n^{-s}` satisfies, uniformly in `t = im s`,

  `‖1/L(s,ψ)‖ ≤ C / (re s - 1)`   for `1 < re s ≤ 2`.

The proof is the Euler product of `L` together with the *reciprocal local factor*

  `1/L(s,ψ) = ∏_p (1 - λ(p) p^{-s} + (λ(p)² - λ(p²)) p^{-2s})`,

whose factors are bounded by `(1 + p^{-σ})²` at the split primes `p ≡ 1 (mod 4)` and by
`1 + p^{-2σ}` at the inert primes.  The resulting product is `O(1/(σ-1))` because
`Σ_{p ≡ 1 (4)} p^{-σ} = (1/2) log(1/(σ-1)) + O(1)`: among the norm-`p` prime ideals of `ℤ[i]`
the class `1 mod 4` occurs twice and the class `3 mod 4` once, so the split primes carry only
"half" of the total prime-norm mass.  This arithmetic input is isolated in the companion lemma
`prime_finset_prod_one_mod_four_bound`.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea5.S16Hecke.heckeLam_bound
import Submission.Work.FIArea5.S16Hecke.heckeLam_localInverse
import Submission.Work.FIArea5.S16Hecke.heckeLam_prime_eq_zero_of_ne_one_mod_four
import Submission.Work.FIArea5.S16Hecke.heckeLam_prime_norm_le_two
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct_hasProd
import Submission.Work.FIArea5.S16Hecke.prime_prod_one_mod_four_bound

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators
open Work.FIPlan

noncomputable section

/-- For a real-valued family with all factors `≥ 1`, every finite product is bounded by the
infinite product (the latter being the limit of the net of finite products). -/
lemma finset_prod_le_tprod {ι : Type*} [DecidableEq ι] (f : ι → ℝ) (h1 : ∀ i, 1 ≤ f i)
    {a : ℝ} (ha : HasProd f a) (s : Finset ι) : ∏ i ∈ s, f i ≤ a := by
  have htend : Filter.Tendsto (fun t : Finset ι => ∏ i ∈ t, f i) Filter.atTop (nhds a) := ha
  refine ge_of_tendsto htend ?_
  filter_upwards [Filter.eventually_atTop.mpr ⟨s, fun t ht => ht⟩] with t hst
  have hsp := Finset.prod_sdiff (f := f) hst
  have h1' : 1 ≤ ∏ x ∈ t \ s, f x := Finset.one_le_prod₀ (fun x _ => h1 x)
  have h3 : 0 ≤ ∏ x ∈ s, f x := Finset.prod_nonneg (fun x _ => le_trans zero_le_one (h1 x))
  calc ∏ i ∈ s, f i = 1 * ∏ i ∈ s, f i := by rw [one_mul]
    _ ≤ (∏ x ∈ t \ s, f x) * ∏ x ∈ s, f x := mul_le_mul_of_nonneg_right h1' h3
    _ = ∏ x ∈ t, f x := hsp

/-! ### The local Euler factor and its reciprocal -/

/-- The local Euler factor at the prime `p`: `Σ_ν λ(p^ν) p^{-νs}`. -/
def heckeFp (chi : GaussianInt → ℂ) (k : ℤ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  ∑' e : ℕ, heckeLam chi k ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ (e * s))

/-- The reciprocal local factor `1 - λ(p) p^{-s} + (λ(p)² - λ(p²)) p^{-2s}`. -/
def heckeGp (chi : GaussianInt → ℂ) (k : ℤ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  1 - heckeLam chi k (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s))
    + ((heckeLam chi k (p : ℕ)) ^ 2 - heckeLam chi k ((p : ℕ) ^ 2))
        * ((((p : ℕ) : ℂ) ^ (-s)) ^ 2)

/-- The majorant of the reciprocal local factors. -/
def heckeB (p : Nat.Primes) (σ : ℝ) : ℝ :=
  if (p : ℕ) % 4 = 1 then (1 + (((p : ℕ) : ℝ) ^ (-σ))) ^ 2
  else (1 + (((p : ℕ) : ℝ) ^ (-2 * σ)))

/-- `p^{-σ} ≤ 1` for `σ > 0`. -/
lemma rpow_neg_le_one (p : Nat.Primes) {σ : ℝ} (hσ : 0 < σ) :
    (((p : ℕ) : ℝ)) ^ (-σ) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos
    (by exact_mod_cast (le_of_lt p.prop.one_lt)) (by linarith)

/-- `p^{-2σ} = (p^{-σ})²`. -/
lemma rpow_neg_two (p : Nat.Primes) (σ : ℝ) :
    (((p : ℕ) : ℝ)) ^ (-2 * σ) = ((((p : ℕ) : ℝ)) ^ (-σ)) ^ 2 := by
  rw [show (-2 * σ) = (-σ) + (-σ) by ring, Real.rpow_add (Nat.cast_pos.mpr p.prop.pos)]
  ring

/-- `1 ≤ heckeB p σ`. -/
lemma heckeB_one_le (p : Nat.Primes) (σ : ℝ) : 1 ≤ heckeB p σ := by
  have ha0 : 0 ≤ (((p : ℕ) : ℝ)) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg (p : ℕ)) (-σ)
  have ha1 : 0 ≤ (((p : ℕ) : ℝ)) ^ (-2 * σ) := Real.rpow_nonneg (Nat.cast_nonneg (p : ℕ)) _
  rw [heckeB]
  by_cases h4 : (p : ℕ) % 4 = 1
  · rw [if_pos h4]; nlinarith
  · rw [if_neg h4]; linarith

/-- The majorant of the reciprocal local factors is multipliable. -/
lemma multipliable_heckeB (σ : ℝ) (hσ : 1 < σ) :
    Multipliable (fun p : Nat.Primes => heckeB p σ) := by
  have hsum : Summable (fun p : Nat.Primes => 3 * (((p : ℕ) : ℝ)) ^ (-σ)) :=
    ((Nat.Primes.summable_rpow (r := -σ)).mpr (by linarith)).mul_left 3
  have hbound : ∀ p : Nat.Primes, ‖heckeB p σ - 1‖ ≤ 3 * (((p : ℕ) : ℝ)) ^ (-σ) := by
    intro p
    have ha0 : 0 ≤ (((p : ℕ) : ℝ)) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg (p : ℕ)) (-σ)
    have ha1 : (((p : ℕ) : ℝ)) ^ (-σ) ≤ 1 := rpow_neg_le_one p (by linarith)
    have hsq : ((((p : ℕ) : ℝ)) ^ (-σ)) ^ 2 ≤ (((p : ℕ) : ℝ)) ^ (-σ) := by nlinarith
    rw [Real.norm_eq_abs, heckeB]
    by_cases h4 : (p : ℕ) % 4 = 1
    · rw [if_pos h4]
      have hnum : (1 + ((p : ℕ) : ℝ) ^ (-σ)) ^ 2 - 1
          = 2 * (((p : ℕ) : ℝ) ^ (-σ)) + (((p : ℕ) : ℝ) ^ (-σ)) ^ 2 := by ring
      rw [hnum, abs_of_nonneg (by positivity)]
      linarith
    · rw [if_neg h4, rpow_neg_two p σ]
      have hnum : 1 + ((((p : ℕ) : ℝ)) ^ (-σ)) ^ 2 - 1 = ((((p : ℕ) : ℝ)) ^ (-σ)) ^ 2 := by ring
      rw [hnum, abs_of_nonneg (by positivity)]
      linarith
  have hbnd : Summable (fun p : Nat.Primes => ‖heckeB p σ - 1‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) hbound hsum
  refine (multipliable_one_add_of_summable
    (f := fun p : Nat.Primes => heckeB p σ - 1) hbnd).congr (fun p => ?_)
  ring

/-- Any finite product of majorants is `O(1/(σ-1))`. -/
theorem heckeB_finset_prod_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 2 → ∀ s : Finset Nat.Primes,
      (∏ p ∈ s, heckeB p σ) ≤ C / (σ - 1) := by
  obtain ⟨C, hC, hCd⟩ := prime_prod_one_mod_four_bound
  refine ⟨C, hC, fun σ hσ1 hσ2 s => ?_⟩
  refine le_trans (finset_prod_le_tprod (fun p : Nat.Primes => heckeB p σ)
    (fun p => heckeB_one_le p σ) (multipliable_heckeB σ hσ1).hasProd s) ?_
  simpa only [heckeB] using hCd σ hσ1 hσ2

/-- `(R ^ (-s)) ^ e = R ^ (-(e * s))` for `R ≠ 0`. -/
lemma cpow_neg_mul_pow (R : ℂ) (hR : R ≠ 0) (s : ℂ) (e : ℕ) :
    R ^ (-(e * s)) = (R ^ (-s)) ^ e := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Nat.cast_succ]
    have harg : (-(((e : ℂ) + 1) * s)) = (-((e : ℂ) * s)) + (-s) := by ring
    rw [harg, Complex.cpow_add _ _ hR, ih, pow_succ]

/-- The Euler factor as a power series in `p^{-s}`. -/
lemma heckeFp_eq_tsum (chi : GaussianInt → ℂ) (k : ℤ) (p : Nat.Primes) (s : ℂ) :
    heckeFp chi k p s
      = ∑' e : ℕ, heckeLam chi k ((p : ℕ) ^ e) * ((((p : ℕ) : ℂ) ^ (-s)) ^ e) := by
  unfold heckeFp
  refine tsum_congr fun e => ?_
  have hR : (((p : ℕ) : ℂ)) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact p.prop.pos.ne'
  rw [div_eq_mul_inv, ← Complex.cpow_neg (((p : ℕ) : ℂ)) ((e : ℂ) * s),
    cpow_neg_mul_pow (((p : ℕ) : ℂ)) hR s e]

/-- The modulus of `p^{-s}`. -/
lemma norm_cpow_neg (p : Nat.Primes) (s : ℂ) :
    ‖(((p : ℕ) : ℂ) ^ (-s))‖ = (((p : ℕ) : ℝ)) ^ (-s.re) := by
  rw [← Complex.ofReal_natCast,
    Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr p.prop.pos), Complex.neg_re]

/-- **(reciprocal local factor)** `F_p(s) * G_p(s) = 1`. -/
lemma heckeFp_mul_heckeGp (chi : GaussianInt → ℂ) (k : ℤ) (p : Nat.Primes) (s : ℂ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) (h1 : chi 1 = 1)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (hs : 0 < s.re) :
    heckeFp chi k p s * heckeGp chi k p s = 1 := by
  have hnorm : ‖(((p : ℕ) : ℂ) ^ (-s))‖ < 1 := by
    rw [norm_cpow_neg p s]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
  rw [heckeFp_eq_tsum]
  unfold heckeGp
  exact heckeLam_localInverse p.prop hmul h1 hb hnorm

/-- `‖G_p(s) - 1‖ ≤ 9 p^{-σ}`. -/
lemma norm_heckeGp_sub_one_le (chi : GaussianInt → ℂ) (k : ℤ) (p : Nat.Primes) (s : ℂ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (hs : 0 < s.re) :
    ‖heckeGp chi k p s - 1‖ ≤ 9 * (((p : ℕ) : ℝ)) ^ (-s.re) := by
  have ha0 : 0 ≤ (((p : ℕ) : ℝ)) ^ (-s.re) :=
    Real.rpow_nonneg (Nat.cast_nonneg (p : ℕ)) (-s.re)
  have ha1 : (((p : ℕ) : ℝ)) ^ (-s.re) ≤ 1 := rpow_neg_le_one p hs
  have hZ : ‖(((p : ℕ) : ℂ) ^ (-s))‖ = (((p : ℕ) : ℝ)) ^ (-s.re) := norm_cpow_neg p s
  have hlam : ‖heckeLam chi k (p : ℕ)‖ ≤ 8 := by
    have h := heckeLam_bound chi k hb (n := (p : ℕ)) (le_of_lt p.prop.one_lt)
    have hcard : (((p : ℕ).divisors.card : ℕ) : ℝ) = 2 := by
      have h2 := Nat.divisors_prime_pow p.prop 1
      rw [pow_one] at h2
      rw [h2, Finset.card_map, Finset.card_range]
      norm_num
    rw [hcard] at h
    linarith
  have hc : ‖(heckeLam chi k (p : ℕ)) ^ 2 - heckeLam chi k ((p : ℕ) ^ 2)‖ ≤ 1 :=
    (heckeLam_localRec chi k (p : ℕ) p.prop hmul hb).2
  have hdecomp : heckeGp chi k p s - 1
      = -(heckeLam chi k (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))
        + ((heckeLam chi k (p : ℕ)) ^ 2 - heckeLam chi k ((p : ℕ) ^ 2))
            * ((((p : ℕ) : ℂ) ^ (-s)) ^ 2) := by
    unfold heckeGp; ring
  rw [hdecomp]
  have h1 : ‖-(heckeLam chi k (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))
        + ((heckeLam chi k (p : ℕ)) ^ 2 - heckeLam chi k ((p : ℕ) ^ 2))
            * ((((p : ℕ) : ℂ) ^ (-s)) ^ 2)‖
      ≤ ‖heckeLam chi k (p : ℕ)‖ * (((p : ℕ) : ℝ)) ^ (-s.re)
        + ‖(heckeLam chi k (p : ℕ)) ^ 2 - heckeLam chi k ((p : ℕ) ^ 2)‖
            * ((((p : ℕ) : ℝ)) ^ (-s.re)) ^ 2 := by
    refine le_trans (norm_add_le _ _) (le_of_eq ?_)
    rw [norm_neg, norm_mul, norm_mul, norm_pow, hZ]
  refine le_trans h1 ?_
  have h2 : ‖heckeLam chi k (p : ℕ)‖ * (((p : ℕ) : ℝ)) ^ (-s.re)
      ≤ 8 * (((p : ℕ) : ℝ)) ^ (-s.re) := mul_le_mul_of_nonneg_right hlam ha0
  have h3 : ‖(heckeLam chi k (p : ℕ)) ^ 2 - heckeLam chi k ((p : ℕ) ^ 2)‖
      * ((((p : ℕ) : ℝ)) ^ (-s.re)) ^ 2 ≤ 1 * ((((p : ℕ) : ℝ)) ^ (-s.re)) ^ 2 :=
    mul_le_mul_of_nonneg_right hc (by positivity)
  have h4 : 8 * (((p : ℕ) : ℝ)) ^ (-s.re) + 1 * ((((p : ℕ) : ℝ)) ^ (-s.re)) ^ 2
      ≤ 9 * (((p : ℕ) : ℝ)) ^ (-s.re) := by nlinarith [ha0, ha1]
  linarith [h2, h3, h4]

/-- The reciprocal local factors are summable/multipliable. -/
lemma multipliable_heckeGp (chi : GaussianInt → ℂ) (k : ℤ) (s : ℂ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (hs : 1 < s.re) :
    Multipliable (fun p : Nat.Primes => heckeGp chi k p s) := by
  have hsum : Summable (fun p : Nat.Primes => 9 * (((p : ℕ) : ℝ)) ^ (-s.re)) :=
    ((Nat.Primes.summable_rpow (r := -s.re)).mpr (by linarith)).mul_left 9
  have hbnd : Summable (fun p : Nat.Primes => ‖heckeGp chi k p s - 1‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _)
      (fun p => norm_heckeGp_sub_one_le chi k p s hmul hb (by linarith)) hsum
  refine (multipliable_one_add_of_summable
    (f := fun p : Nat.Primes => heckeGp chi k p s - 1) hbnd).congr (fun p => ?_)
  ring

/-- **The reciprocal Hecke `L`-series is the product of the reciprocal local factors.** -/
lemma tprod_heckeGp_eq_inv (chi : GaussianInt → ℂ) (k : ℤ) (s : ℂ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w) (h1 : chi 1 = 1)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (hs : 1 < s.re) :
    (∏' p : Nat.Primes, heckeGp chi k p s) = (heckeLSeries chi k s)⁻¹ := by
  have hFp_mult : Multipliable (fun p : Nat.Primes => heckeFp chi k p s) :=
    (heckeLSeries_eulerProduct_hasProd chi k h1 hmul hb hs).multipliable
  have hGp_mult : Multipliable (fun p : Nat.Primes => heckeGp chi k p s) :=
    multipliable_heckeGp chi k s hmul hb hs
  have h := Multipliable.tprod_mul hFp_mult hGp_mult
  rw [show (fun p : Nat.Primes => heckeFp chi k p s * heckeGp chi k p s) = fun _ => (1 : ℂ)
        from funext (fun p => heckeFp_mul_heckeGp chi k p s hmul h1 hb (by linarith))] at h
  have hL : (∏' p : Nat.Primes, heckeFp chi k p s) = heckeLSeries chi k s :=
    (heckeLSeries_eulerProduct_hasProd chi k h1 hmul hb hs).tprod_eq
  rw [tprod_one, hL] at h
  exact (inv_eq_of_mul_eq_one_right h.symm).symm

/-- Pointwise bound of the reciprocal local factor by `heckeB`. -/
lemma norm_heckeGp_le (chi : GaussianInt → ℂ) (k : ℤ) (p : Nat.Primes) (s : ℂ)
    (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (hs : 0 < s.re) :
    ‖heckeGp chi k p s‖ ≤ heckeB p s.re := by
  have hA0 : 0 ≤ (((p : ℕ) : ℝ)) ^ (-s.re) :=
    Real.rpow_nonneg (Nat.cast_nonneg (p : ℕ)) (-s.re)
  have hZ : ‖(((p : ℕ) : ℂ) ^ (-s))‖ = (((p : ℕ) : ℝ)) ^ (-s.re) := norm_cpow_neg p s
  have hc : ‖(heckeLam chi k (p : ℕ)) ^ 2 - heckeLam chi k ((p : ℕ) ^ 2)‖ ≤ 1 :=
    (heckeLam_localRec chi k (p : ℕ) p.prop hmul hb).2
  have hbase : ‖heckeGp chi k p s‖
      ≤ 1 + ‖heckeLam chi k (p : ℕ)‖ * (((p : ℕ) : ℝ)) ^ (-s.re)
          + ‖(heckeLam chi k (p : ℕ)) ^ 2 - heckeLam chi k ((p : ℕ) ^ 2)‖
              * ((((p : ℕ) : ℝ)) ^ (-s.re)) ^ 2 := by
    have hdecomp : heckeGp chi k p s
        = 1 - heckeLam chi k (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s))
          + ((heckeLam chi k (p : ℕ)) ^ 2 - heckeLam chi k ((p : ℕ) ^ 2))
              * ((((p : ℕ) : ℂ) ^ (-s)) ^ 2) := rfl
    rw [hdecomp]
    have hsub : ‖(1 : ℂ) - heckeLam chi k (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s))‖
        ≤ 1 + ‖heckeLam chi k (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s))‖ := by
      simpa using norm_sub_le (1 : ℂ) (heckeLam chi k (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s)))
    have h2 : ‖1 - heckeLam chi k (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s))
            + ((heckeLam chi k (p : ℕ)) ^ 2 - heckeLam chi k ((p : ℕ) ^ 2))
                * ((((p : ℕ) : ℂ) ^ (-s)) ^ 2)‖
        ≤ (1 + ‖heckeLam chi k (p : ℕ) * (((p : ℕ) : ℂ) ^ (-s))‖)
            + ‖((heckeLam chi k (p : ℕ)) ^ 2 - heckeLam chi k ((p : ℕ) ^ 2))
                * ((((p : ℕ) : ℂ) ^ (-s)) ^ 2)‖ :=
      le_trans (norm_add_le _ _) (add_le_add hsub le_rfl)
    refine le_trans h2 (le_of_eq ?_)
    rw [norm_mul, norm_mul, norm_pow, hZ]
  rw [heckeB]
  by_cases h4 : (p : ℕ) % 4 = 1
  · rw [if_pos h4]
    have hlam : ‖heckeLam chi k (p : ℕ)‖ ≤ 2 := heckeLam_prime_norm_le_two p.prop h4 hb
    have h2 : ‖heckeLam chi k (p : ℕ)‖ * (((p : ℕ) : ℝ)) ^ (-s.re)
        ≤ 2 * (((p : ℕ) : ℝ)) ^ (-s.re) := mul_le_mul_of_nonneg_right hlam hA0
    have h3 : ‖(heckeLam chi k (p : ℕ)) ^ 2 - heckeLam chi k ((p : ℕ) ^ 2)‖
        * ((((p : ℕ) : ℝ)) ^ (-s.re)) ^ 2 ≤ 1 * ((((p : ℕ) : ℝ)) ^ (-s.re)) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    calc ‖heckeGp chi k p s‖
        ≤ 1 + ‖heckeLam chi k (p : ℕ)‖ * (((p : ℕ) : ℝ)) ^ (-s.re)
            + ‖(heckeLam chi k (p : ℕ)) ^ 2 - heckeLam chi k ((p : ℕ) ^ 2)‖
                * ((((p : ℕ) : ℝ)) ^ (-s.re)) ^ 2 := hbase
      _ ≤ 1 + 2 * (((p : ℕ) : ℝ)) ^ (-s.re)
            + 1 * ((((p : ℕ) : ℝ)) ^ (-s.re)) ^ 2 := add_le_add (add_le_add le_rfl h2) h3
      _ = (1 + (((p : ℕ) : ℝ)) ^ (-s.re)) ^ 2 := by ring
  · rw [if_neg h4]
    have hlam : heckeLam chi k (p : ℕ) = 0 := heckeLam_prime_eq_zero_of_ne_one_mod_four p.prop h4
    have h2 : ‖heckeLam chi k (p : ℕ)‖ * (((p : ℕ) : ℝ)) ^ (-s.re) = 0 := by
      rw [hlam, norm_zero, zero_mul]
    have h3 : ‖(heckeLam chi k (p : ℕ)) ^ 2 - heckeLam chi k ((p : ℕ) ^ 2)‖
        * ((((p : ℕ) : ℝ)) ^ (-s.re)) ^ 2 ≤ 1 * ((((p : ℕ) : ℝ)) ^ (-s.re)) ^ 2 :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    rw [rpow_neg_two p s.re]
    calc ‖heckeGp chi k p s‖
        ≤ 1 + ‖heckeLam chi k (p : ℕ)‖ * (((p : ℕ) : ℝ)) ^ (-s.re)
            + ‖(heckeLam chi k (p : ℕ)) ^ 2 - heckeLam chi k ((p : ℕ) ^ 2)‖
                * ((((p : ℕ) : ℝ)) ^ (-s.re)) ^ 2 := hbase
      _ ≤ 1 + 0 + 1 * ((((p : ℕ) : ℝ)) ^ (-s.re)) ^ 2 :=
            add_le_add (add_le_add le_rfl (le_of_eq h2)) h3
      _ = 1 + ((((p : ℕ) : ℝ)) ^ (-s.re)) ^ 2 := by ring

/-- **(16.23)/(16.24)** the reciprocal Hecke `L`-series is `O(1/(σ-1))` on `1 < σ ≤ 2`,
uniformly in the imaginary part. -/
theorem heckeL_inv_halfPlane (chi : GaussianInt → ℂ) (k : ℤ)
    (h1 : chi 1 = 1) (hmul : ∀ z w : GaussianInt, chi (z * w) = chi z * chi w)
    (hb : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
      ‖(heckeLSeries chi k s)⁻¹‖ ≤ C / (s.re - 1) := by
  obtain ⟨C0, hC0pos, hC0⟩ := heckeB_finset_prod_bound
  refine ⟨C0, hC0pos, ?_⟩
  intro s hs1 hs2
  have hsigpos : 0 < s.re := by linarith
  have hGp_mult : Multipliable (fun p : Nat.Primes => heckeGp chi k p s) :=
    multipliable_heckeGp chi k s hmul hb hs1
  have hEq : (∏' p : Nat.Primes, heckeGp chi k p s) = (heckeLSeries chi k s)⁻¹ :=
    tprod_heckeGp_eq_inv chi k s hmul h1 hb hs1
  have hnorm : ‖(heckeLSeries chi k s)⁻¹‖ = ∏' p : Nat.Primes, ‖heckeGp chi k p s‖ := by
    rw [← hEq, Multipliable.norm_tprod hGp_mult]
  rw [hnorm]
  refine Multipliable.tprod_le_of_prod_le hGp_mult.norm (fun t => ?_)
  have h1' : ∏ p ∈ t, ‖heckeGp chi k p s‖ ≤ ∏ p ∈ t, heckeB p s.re :=
    Finset.prod_le_prod₀ (fun p _ => norm_nonneg _)
      (fun p _ => norm_heckeGp_le chi k p s hmul hb hsigpos)
  have h2' : ∏ p ∈ t, heckeB p s.re ≤ C0 / (s.re - 1) := hC0 s.re hs1 hs2 t
  linarith

end

end Work.FIArea5.S16Hecke
