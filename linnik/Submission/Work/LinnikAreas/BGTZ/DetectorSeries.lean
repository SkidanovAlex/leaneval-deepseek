/-
# The Dirichlet series of the BGTZ detector coefficient

`detCoeff χ₁ χ θw n = a(n)χ(n)(Σ_{d|n}θ_d)²` (BGTZ §5, `DetectorDefs`) is the coefficient of the
detector sum `S` of BGTZ Proposition 5.1.  This file proves that its Dirichlet series factors as

`Σ_n detCoeff n · n^{-s} = L(s,χ) L(s,χχ₁) G(s,χ)`  (`Re s > 1`),

where `G(s,χ) = sieveG χ₁ R θw s χ` is the Selberg sieve function.

The proof expands the square `(Σ_{d|n}θ_d)² = Σ_{d,e ≤ R} θ_dθ_e [lcm d e | n]`, which reduces
everything to the "multiples of `m`" series `multSer χ₁ χ m s = Σ_{m|n}a(n)χ(n)n^{-s}` and the
local-factor identity `multSer χ₁ χ (p m) s = sieveLocal χ₁ χ s p · multSer χ₁ χ m s` (`p ∤ m`).
-/
import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.BGTZ.DetectorDefs

open DirichletCharacter Complex
open scoped Classical BigOperators
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.LinnikAreas.BGTZ

variable {q : ℕ} [NeZero q]

/-! ## 1. Auxiliary vocabulary -/

/-- A character with `χ ^ 2 = 1` takes only the values `0`, `1`, `-1`. -/
lemma chi_apply_eq_zero_or_one_or_neg_one (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (a : ZMod q) :
    χ a = 0 ∨ χ a = 1 ∨ χ a = -1 :=
  (MulChar.isQuadratic_iff_sq_eq_one.mpr hχ) a

/-- The values of a character with `χ ^ 2 = 1` are real. -/
lemma ofReal_re_chi_apply (χ : DirichletCharacter ℂ q) (hχ : χ ^ 2 = 1) (a : ZMod q) :
    ((χ a).re : ℂ) = χ a := by
  rcases chi_apply_eq_zero_or_one_or_neg_one χ hχ a with h | h | h <;> simp [h]

/-- `aCoeff` as a complex sum of character values. -/
lemma aCoeff_eq_sum_chi (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) (n : ℕ) :
    (aCoeff χ₁ n : ℂ) = ∑ d ∈ n.divisors, χ₁ (d : ZMod q) := by
  rw [aCoeff, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun d _ => ofReal_re_chi_apply χ₁ hχ₁ (d : ZMod q)

/-- The Dirichlet coefficient `a(n) χ(n)` of the product `L(s,χ) L(s,χχ₁)`. -/
def cfun (χ₁ χ : DirichletCharacter ℂ q) (n : ℕ) : ℂ := (aCoeff χ₁ n : ℂ) * χ (n : ZMod q)

/-- The Dirichlet series `Σ_{m ∣ n} a(n) χ(n) n^{-s}`: the "multiples of `m`" part of
`Σ_n a(n)χ(n)n^{-s}`. -/
def multSer (χ₁ χ : DirichletCharacter ℂ q) (m : ℕ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (if m ∣ n then cfun χ₁ χ n else 0) / (n : ℂ) ^ s

/-- `detCoeff` is `a(n)χ(n)` times the square of the sieve-weight divisor sum. -/
lemma detCoeff_eq_mul_sq (χ₁ χ : DirichletCharacter ℂ q) (θw : ℕ → ℝ) (n : ℕ) :
    detCoeff χ₁ χ θw n = cfun χ₁ χ n * (((∑ d ∈ n.divisors, θw d : ℝ)) : ℂ) ^ 2 := by
  simp only [detCoeff, cfun, Complex.ofReal_sum]

@[simp] lemma cfun_zero (χ₁ χ : DirichletCharacter ℂ q) : cfun χ₁ χ 0 = 0 := by
  simp [cfun, aCoeff, Nat.divisors_zero]

/-! ## 2. `a(n)χ(n)` as a Dirichlet convolution -/

/-- Summing over the antidiagonal of divisors is summing over the divisors. -/
lemma sum_divisorsAntidiagonal_eq_sum_divisors (n : ℕ) (hn : n ≠ 0) (F : ℕ → ℕ → ℂ) :
    ∑ p ∈ n.divisorsAntidiagonal, F p.1 p.2 = ∑ d ∈ n.divisors, F d (n / d) := by
  have hinj : Set.InjOn Prod.fst (↑n.divisorsAntidiagonal : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    have hx1 : x.1 * x.2 = n := (Nat.mem_divisorsAntidiagonal.mp hx).1
    have hy1 : y.1 * y.2 = n := (Nat.mem_divisorsAntidiagonal.mp hy).1
    have hx0 : 0 < x.1 := Nat.pos_of_ne_zero fun h => hn (by rw [h, zero_mul] at hx1; exact hx1.symm)
    exact Prod.ext hxy (Nat.mul_left_cancel hx0 (by rw [hx1, hxy, hy1]))
  have himg : (n.divisorsAntidiagonal).image Prod.fst = n.divisors := by
    ext d
    simp only [Finset.mem_image, Nat.mem_divisorsAntidiagonal, Nat.mem_divisors]
    constructor
    · rintro ⟨p, ⟨hp, -⟩, rfl⟩
      exact ⟨⟨p.2, hp.symm⟩, hn⟩
    · rintro ⟨⟨k, hk⟩, -⟩
      exact ⟨(d, k), ⟨⟨by rw [hk], hn⟩, rfl⟩⟩
  have h3 : ∑ d ∈ (n.divisorsAntidiagonal).image Prod.fst, F d (n / d)
      = ∑ p ∈ n.divisorsAntidiagonal, F p.1 p.2 := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp1 : p.1 * p.2 = n := (Nat.mem_divisorsAntidiagonal.mp hp).1
    have h0 : 0 < p.1 := Nat.pos_of_ne_zero fun h => hn (by rw [h, zero_mul] at hp1; exact hp1.symm)
    have hdiv : n / p.1 = p.2 := by rw [← hp1, Nat.mul_comm p.1 p.2, Nat.mul_div_left p.2 h0]
    rw [hdiv]
  rw [← h3, himg]

/-- `a(n)χ(n) = Σ_{d | n} (χχ₁)(d) χ(n/d)`. -/
lemma cfun_eq_sum_divisors (χ₁ χ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) (n : ℕ) :
    cfun χ₁ χ n = ∑ d ∈ n.divisors, (χ * χ₁) (d : ZMod q) * χ ((n / d : ℕ) : ZMod q) := by
  rw [cfun, aCoeff_eq_sum_chi χ₁ hχ₁, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdvd : d ∣ n := (Nat.mem_divisors.mp hd).1
  have hcast : ((n : ℕ) : ZMod q) = (d : ZMod q) * ((n / d : ℕ) : ZMod q) := by
    rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
  have hchi : χ (n : ZMod q) = χ (d : ZMod q) * χ ((n / d : ℕ) : ZMod q) := by
    rw [hcast, map_mul]
  rw [hchi, MulChar.mul_apply]
  ring

/-- `a(n)χ(n)` as a Dirichlet convolution, in antidiagonal form. -/
lemma cfun_eq_antidiag (χ₁ χ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) (n : ℕ) :
    cfun χ₁ χ n = ∑ p ∈ n.divisorsAntidiagonal, (χ * χ₁) (p.1 : ZMod q) * χ (p.2 : ZMod q) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [cfun, aCoeff]
  · rw [cfun_eq_sum_divisors χ₁ χ hχ₁ n,
      ← sum_divisorsAntidiagonal_eq_sum_divisors n hn
        (fun a b => (χ * χ₁) (a : ZMod q) * χ (b : ZMod q))]

/-- The Dirichlet series of `a(n)χ(n)` converges absolutely for `Re s > 1`. -/
lemma summable_cfun (χ₁ χ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => cfun χ₁ χ n / (n : ℂ) ^ s) := by
  have hs0 : s ≠ 0 := ne_zero_of_one_lt_re hs
  have hA : LSeriesSummable (fun n : ℕ => (χ * χ₁) (n : ZMod q)) s :=
    LSeriesSummable_of_one_lt_re (χ * χ₁) hs
  have hB : LSeriesSummable (fun n : ℕ => χ (n : ZMod q)) s :=
    LSeriesSummable_of_one_lt_re χ hs
  have hconv : LSeriesSummable (LSeries.convolution (fun n : ℕ => (χ * χ₁) (n : ZMod q))
      (fun n : ℕ => χ (n : ZMod q))) s :=
    LSeriesSummable.convolution hA hB
  have hfun : (fun n : ℕ => cfun χ₁ χ n)
      = LSeries.convolution (fun n : ℕ => (χ * χ₁) (n : ZMod q))
          (fun n : ℕ => χ (n : ZMod q)) := by
    funext n
    simp only [LSeries.convolution_def, cfun_eq_antidiag χ₁ χ hχ₁ n]
  have hL : LSeriesSummable (fun n : ℕ => cfun χ₁ χ n) s := hfun ▸ hconv
  have hterm : (fun n : ℕ => cfun χ₁ χ n / (n : ℂ) ^ s)
      = LSeries.term (fun n : ℕ => cfun χ₁ χ n) s :=
    funext fun n => (LSeries.term_of_ne_zero' hs0 _ n).symm
  rw [hterm]
  exact hL

/-! ## 3. Reindexing along a divisibility -/

/-- Summing a multiple of `p` is the same as summing over `p * a`. -/
lemma tsum_dvd_indicator {p : ℕ} (hp : p ≠ 0) (G : ℕ → ℂ) :
    (∑' a : ℕ, (if p ∣ a then G a else 0)) = ∑' a' : ℕ, G (p * a') := by
  have h1 : (∑' a : ℕ, (if p ∣ a then G a else 0))
      = ∑' a : ℕ, ({a : ℕ | p ∣ a} : Set ℕ).indicator G a := by
    refine tsum_congr fun a => ?_
    simp [Set.indicator]
  rw [h1, ← tsum_subtype {a : ℕ | p ∣ a} G]
  let φ : ℕ → {a : ℕ // p ∣ a} := fun a' => ⟨p * a', dvd_mul_right p a'⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      have : p * a = p * b := congrArg Subtype.val hab
      exact Nat.mul_left_cancel (Nat.pos_of_ne_zero hp) this
    · rintro ⟨a, ha⟩
      exact ⟨a / p, Subtype.ext (Nat.mul_div_cancel' ha)⟩
  exact (Equiv.tsum_eq (Equiv.ofBijective φ hφ) (fun x : {a : ℕ // p ∣ a} => G x.1)).symm

/-! ## 4. The square of a divisor sum -/

/-- `(Σ_{d|n}θ_d)² = Σ_{d,e ≤ R}θ_dθ_e [lcm d e | n]` for a sieve weight. -/
lemma divisors_sum_sq_eq_lcm_sum {R : ℕ} {θw : ℕ → ℝ} (hθ : IsSieveWeight R θw) {n : ℕ}
    (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, θw d) ^ 2
      = ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
          θw d * θw e * (if Nat.lcm d e ∣ n then (1 : ℝ) else 0) := by
  have hset : (Finset.Icc 1 R).filter (fun d => d ∣ n) = n.divisors.filter (fun d => d ≤ R) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h3, hn⟩, h2⟩
    · rintro ⟨⟨h3, -⟩, h2⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos h3 (Nat.pos_of_ne_zero hn), h2⟩, h3⟩
  have h1 : ∑ d ∈ n.divisors, θw d
      = ∑ d ∈ Finset.Icc 1 R, θw d * (if d ∣ n then (1:ℝ) else 0) := by
    have hz : ∑ d ∈ n.divisors.filter (fun d => ¬ d ≤ R), θw d = 0 := by
      refine Finset.sum_eq_zero fun d hd => ?_
      have hRd : R < d := by simpa using (Finset.mem_filter.mp hd).2
      exact hθ.2.1 d (Or.inr hRd)
    have hs1 : ∑ d ∈ n.divisors.filter (fun d => d ≤ R), θw d
        = ∑ d ∈ Finset.Icc 1 R, θw d * (if d ∣ n then (1:ℝ) else 0) := by
      rw [← hset, Finset.sum_filter]
      refine Finset.sum_congr rfl fun d _ => by rw [mul_ite, mul_one, mul_zero]
    rw [← Finset.sum_filter_add_sum_filter_not (s := n.divisors) (p := fun d => d ≤ R) (f := θw),
      hz, add_zero, hs1]
  rw [h1, pow_two, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => ?_
  have hie : (if d ∣ n then (1:ℝ) else 0) * (if e ∣ n then (1:ℝ) else 0)
      = (if Nat.lcm d e ∣ n then (1:ℝ) else 0) := by
    by_cases hd' : d ∣ n <;> by_cases he' : e ∣ n <;>
      simp [hd', he', Nat.lcm_dvd_iff, hd', he']
  rw [← hie]; ring

/-! ## 5. The pair form of the multiples series -/

/-- Summand of the pair form `Σ_{a,b} [m | ab] (χχ₁)(a)χ(b)(ab)^{-s}` of `multSer`. -/
def pairTerm (χ₁ χ : DirichletCharacter ℂ q) (m : ℕ) (s : ℂ) (ab : ℕ × ℕ) : ℂ :=
  (if m ∣ ab.1 * ab.2 then (χ * χ₁) (ab.1 : ZMod q) * χ (ab.2 : ZMod q) else 0) *
    (((ab.1 * ab.2 : ℕ) : ℂ) ^ (-s))

lemma norm_pairTerm_le (χ₁ χ : DirichletCharacter ℂ q) (m : ℕ) {s : ℂ} (hs : 1 < s.re)
    (ab : ℕ × ℕ) :
    ‖pairTerm χ₁ χ m s ab‖ ≤ (ab.1 : ℝ) ^ (-s.re) * (ab.2 : ℝ) ^ (-s.re) := by
  have hne : (-s).re ≠ 0 := by rw [Complex.neg_re]; linarith
  have h1 : ‖(if m ∣ ab.1 * ab.2 then (χ * χ₁) (ab.1 : ZMod q) * χ (ab.2 : ZMod q) else 0)‖ ≤ 1 := by
    by_cases h : m ∣ ab.1 * ab.2
    · rw [if_pos h, norm_mul]
      exact mul_le_one₀ (DirichletCharacter.norm_le_one _ _) (norm_nonneg _)
        (DirichletCharacter.norm_le_one _ _)
    · rw [if_neg h, norm_zero]; norm_num
  have hb : (((ab.1 * ab.2 : ℕ)) : ℂ) = ((((ab.1 : ℝ) * (ab.2 : ℝ)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [pairTerm, norm_mul, hb,
    Complex.norm_cpow_eq_rpow_re_of_nonneg (by positivity) hne, Complex.neg_re,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  set x : ℝ := (ab.1 : ℝ) ^ (-s.re) * (ab.2 : ℝ) ^ (-s.re) with hx
  have hx0 : 0 ≤ x := by rw [hx]; positivity
  calc ‖(if m ∣ ab.1 * ab.2 then (χ * χ₁) (ab.1 : ZMod q) * χ (ab.2 : ZMod q) else 0)‖ * x
      ≤ 1 * x := mul_le_mul_of_nonneg_right h1 hx0
    _ = x := one_mul x

lemma summable_nat_rpow_neg {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (n : ℝ) ^ (-s.re)) :=
  Summable.congr (Real.summable_nat_rpow_inv.mpr hs) fun n =>
    (Real.rpow_neg (Nat.cast_nonneg n) s.re).symm

lemma summable_pairTerm (χ₁ χ : DirichletCharacter ℂ q) (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (pairTerm χ₁ χ m s) := by
  have hbase := summable_nat_rpow_neg (s := s) hs
  have hg : Summable (fun ab : ℕ × ℕ => (ab.1 : ℝ) ^ (-s.re) * (ab.2 : ℝ) ^ (-s.re)) := by
    refine (summable_prod_of_nonneg (f := fun ab : ℕ × ℕ =>
      (ab.1 : ℝ) ^ (-s.re) * (ab.2 : ℝ) ^ (-s.re)) (fun ab => by positivity)).mpr ?_
    refine ⟨fun a => hbase.mul_left ((a : ℝ) ^ (-s.re)), ?_⟩
    refine Summable.congr (hbase.mul_right (∑' b : ℕ, (b : ℝ) ^ (-s.re))) fun a => ?_
    exact (tsum_mul_left (a := (a : ℝ) ^ (-s.re))).symm
  have hbound : ∀ ab : ℕ × ℕ, ‖pairTerm χ₁ χ m s ab‖
      ≤ (ab.1 : ℝ) ^ (-s.re) * (ab.2 : ℝ) ^ (-s.re) := fun ab => norm_pairTerm_le χ₁ χ m hs ab
  exact Summable.of_norm_bounded hg hbound

lemma tsum_prod_pairTerm (χ₁ χ : DirichletCharacter ℂ q) (m : ℕ) {s : ℂ} (hs : 1 < s.re) :
    (∑' ab : ℕ × ℕ, pairTerm χ₁ χ m s ab)
      = ∑' a : ℕ, ∑' b : ℕ, pairTerm χ₁ χ m s (a, b) :=
  Summable.tsum_prod' (summable_pairTerm χ₁ χ m hs)
    fun a => (summable_pairTerm χ₁ χ m hs).prod_factor a

/-- The pair form of the multiples series is the multiples series. -/
lemma tsum_pairTerm_eq_multSer (χ₁ χ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) (m : ℕ)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' ab : ℕ × ℕ, pairTerm χ₁ χ m s ab) = multSer χ₁ χ m s := by
  have hs0 : s ≠ 0 := ne_zero_of_one_lt_re hs
  have hfib := (summable_pairTerm χ₁ χ m hs).hasSum.tsum_fiberwise
    (fun ab : ℕ × ℕ => ab.1 * ab.2)
  rw [← hfib.tsum_eq, multSer]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · have hzero : ∀ ab : (fun ab : ℕ × ℕ => ab.1 * ab.2) ⁻¹' {0},
        pairTerm χ₁ χ m s ↑ab = 0 := by
      rintro ⟨⟨a, b⟩, hab⟩
      have hab' : a * b = 0 := hab
      rcases Nat.mul_eq_zero.mp hab' with h | h
      · have hz : (((a * b : ℕ)) : ℂ) ^ (-s) = 0 := by
          rw [h, zero_mul, Nat.cast_zero]
          exact zero_cpow (by simpa using neg_ne_zero.mpr hs0)
        simp only [pairTerm, hz, mul_zero]
      · have hz : (((a * b : ℕ)) : ℂ) ^ (-s) = 0 := by
          rw [h, mul_zero, Nat.cast_zero]
          exact zero_cpow (by simpa using neg_ne_zero.mpr hs0)
        simp only [pairTerm, hz, mul_zero]
    rw [show (fun ab : (fun ab : ℕ × ℕ => ab.1 * ab.2) ⁻¹' {0} => pairTerm χ₁ χ m s ↑ab)
          = fun _ => 0 from funext hzero, tsum_zero]
    simp [cfun_zero]
  · have hset : (fun ab : ℕ × ℕ => ab.1 * ab.2) ⁻¹' {n} = ↑(n.divisorsAntidiagonal) := by
      ext ab
      simp [Nat.mem_divisorsAntidiagonal, hn]
    rw [hset, Finset.tsum_subtype' n.divisorsAntidiagonal (pairTerm χ₁ χ m s)]
    have hterm : ∀ ab ∈ n.divisorsAntidiagonal, pairTerm χ₁ χ m s ab
        = (if m ∣ n then (χ * χ₁) (ab.1 : ZMod q) * χ (ab.2 : ZMod q) else 0)
            * ((n : ℂ) ^ (-s)) := by
      intro ab hab
      have hab' : ab.1 * ab.2 = n := (Nat.mem_divisorsAntidiagonal.mp hab).1
      rw [pairTerm]
      simp only [hab']
    rw [Finset.sum_congr rfl hterm]
    by_cases hmn : m ∣ n
    · have h2 : ∀ ab ∈ n.divisorsAntidiagonal,
          (if m ∣ n then (χ * χ₁) (ab.1 : ZMod q) * χ (ab.2 : ZMod q) else 0) * (n : ℂ) ^ (-s)
            = ((χ * χ₁) (ab.1 : ZMod q) * χ (ab.2 : ZMod q)) * (n : ℂ) ^ (-s) := by
        intro ab _; rw [if_pos hmn]
      rw [Finset.sum_congr rfl h2, ← Finset.sum_mul, if_pos hmn, cfun_eq_antidiag χ₁ χ hχ₁ n,
        div_eq_mul_inv, cpow_neg]
    · have h2 : ∀ ab ∈ n.divisorsAntidiagonal,
          (if m ∣ n then (χ * χ₁) (ab.1 : ZMod q) * χ (ab.2 : ZMod q) else 0) * (n : ℂ) ^ (-s)
            = 0 := by
        intro ab _; rw [if_neg hmn, zero_mul]
      rw [Finset.sum_congr rfl h2, Finset.sum_const_zero, if_neg hmn, zero_div]
/-! ## 6. The local recursion `multSer (p m) = sieveLocal p · multSer m` -/

/-- `(χχ₁)(a) = ((χ₁ a).re : ℂ) · χ a` for a real `χ₁`. -/
lemma mul_chi_apply (χ₁ χ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) (a : ZMod q) :
    (χ * χ₁) a = ((χ₁ a).re : ℂ) * χ a := by
  rw [MulChar.mul_apply, ofReal_re_chi_apply χ₁ hχ₁ a, mul_comm]

/-- `p^{-s} · p^{-s} = p^{-(2s)}`. -/
lemma cpow_neg_add_self {p : ℕ} (hp : p ≠ 0) (s : ℂ) :
    (p : ℂ) ^ (-s) * (p : ℂ) ^ (-s) = (p : ℂ) ^ (-(2 * s)) := by
  rw [show -(2 * s) = -s + -s by ring, Complex.cpow_add (-s) (-s) (by simp [hp])]

/-- `(p n)^{-s} = p^{-s} n^{-s}` for integers. -/
lemma natCast_cpow_mul (p n : ℕ) (s : ℂ) :
    (((p * n : ℕ)) : ℂ) ^ (-s) = (p : ℂ) ^ (-s) * (((n : ℕ)) : ℂ) ^ (-s) := by
  rw [show (((p * n : ℕ)) : ℂ) = (((p : ℝ) : ℂ) * (((n : ℝ)) : ℂ)) by push_cast; ring,
    mul_cpow_ofReal_nonneg (Nat.cast_nonneg p) (Nat.cast_nonneg n),
    Complex.ofReal_natCast, Complex.ofReal_natCast]

lemma pairTerm_mul_left (χ₁ χ : DirichletCharacter ℂ q) {m p : ℕ} (hcop : m.Coprime p) (a b : ℕ)
    (s : ℂ) :
    pairTerm χ₁ χ m s (p * a, b)
      = (χ * χ₁) (p : ZMod q) * (p : ℂ) ^ (-s) * pairTerm χ₁ χ m s (a, b) := by
  have hdvd : m ∣ (p * a) * b ↔ m ∣ a * b := by
    rw [show (p * a) * b = p * (a * b) by ring]
    exact hcop.dvd_mul_left
  rw [pairTerm, pairTerm]
  by_cases h : m ∣ a * b
  · rw [if_pos h, if_pos (hdvd.mpr h)]
    have hcpow : (((p * a) * b : ℕ) : ℂ) ^ (-s)
        = (p : ℂ) ^ (-s) * (((a * b : ℕ)) : ℂ) ^ (-s) := by
      rw [show ((p * a) * b : ℕ) = p * (a * b) by ring, natCast_cpow_mul]
    have hchi : (χ * χ₁) (((p * a : ℕ)) : ZMod q)
        = (χ * χ₁) (p : ZMod q) * (χ * χ₁) (a : ZMod q) := by
      rw [Nat.cast_mul, map_mul]
    rw [hcpow, hchi]
    ring
  · simp only [if_neg h, if_neg (fun hc => h (hdvd.mp hc)), mul_zero, zero_mul]

lemma pairTerm_mul_right (χ₁ χ : DirichletCharacter ℂ q) {m p : ℕ} (hcop : m.Coprime p) (a b : ℕ)
    (s : ℂ) :
    pairTerm χ₁ χ m s (a, p * b)
      = χ (p : ZMod q) * (p : ℂ) ^ (-s) * pairTerm χ₁ χ m s (a, b) := by
  have hdvd : m ∣ a * (p * b) ↔ m ∣ a * b := by
    rw [show a * (p * b) = p * (a * b) by ring]
    exact hcop.dvd_mul_left
  rw [pairTerm, pairTerm]
  by_cases h : m ∣ a * b
  · rw [if_pos h, if_pos (hdvd.mpr h)]
    have hcpow : (((a * (p * b)) : ℕ) : ℂ) ^ (-s)
        = (p : ℂ) ^ (-s) * (((a * b : ℕ)) : ℂ) ^ (-s) := by
      rw [show a * (p * b) = p * (a * b) by ring, natCast_cpow_mul]
    have hchi : χ (((p * b : ℕ)) : ZMod q) = χ (p : ZMod q) * χ (b : ZMod q) := by
      rw [Nat.cast_mul, map_mul]
    rw [hcpow, hchi]
    ring
  · simp only [if_neg h, if_neg (fun hc => h (hdvd.mp hc)), mul_zero, zero_mul]

/-- Summability of a pair summand with a bounded factor. -/
lemma summable_pairTerm_mul (χ₁ χ : DirichletCharacter ℂ q) (m : ℕ) {s : ℂ} (hs : 1 < s.re)
    (c : ℕ × ℕ → ℂ) (hc : ∀ ab, ‖c ab‖ ≤ 1) :
    Summable (fun ab : ℕ × ℕ => pairTerm χ₁ χ m s ab * c ab) := by
  refine Summable.of_norm_bounded (summable_pairTerm χ₁ χ m (s := s) hs).norm fun ab => ?_
  rw [norm_mul]
  calc ‖pairTerm χ₁ χ m s ab‖ * ‖c ab‖ ≤ ‖pairTerm χ₁ χ m s ab‖ * 1 :=
        mul_le_mul_of_nonneg_left (hc ab) (norm_nonneg _)
    _ = ‖pairTerm χ₁ χ m s ab‖ := mul_one _

lemma norm_indicator_le_one (p n : ℕ) : ‖(if p ∣ n then (1 : ℂ) else 0)‖ ≤ 1 := by
  by_cases h : p ∣ n <;> simp [h]

lemma norm_indicator_mul_le_one (p a b : ℕ) :
    ‖(if p ∣ a then (1 : ℂ) else 0) * (if p ∣ b then (1 : ℂ) else 0)‖ ≤ 1 := by
  rw [norm_mul]
  calc _ ≤ 1 * 1 := mul_le_mul (norm_indicator_le_one p a) (norm_indicator_le_one p b)
        (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The `[p | a]` part of the pair sum. -/
lemma pairSum_left (χ₁ χ : DirichletCharacter ℂ q) {m p : ℕ} (hp : p ≠ 0) (hcop : m.Coprime p)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' ab : ℕ × ℕ, pairTerm χ₁ χ m s ab * (if p ∣ ab.1 then (1 : ℂ) else 0))
      = (χ * χ₁) (p : ZMod q) * (p : ℂ) ^ (-s) * (∑' ab : ℕ × ℕ, pairTerm χ₁ χ m s ab) := by
  have hS := summable_pairTerm_mul χ₁ χ m hs (fun ab => if p ∣ ab.1 then (1 : ℂ) else 0)
    (fun ab => norm_indicator_le_one p ab.1)
  rw [Summable.tsum_prod' hS (fun a => hS.prod_factor a)]
  have h1 : ∀ a : ℕ, (∑' b : ℕ, pairTerm χ₁ χ m s (a, b) * (if p ∣ a then (1 : ℂ) else 0))
      = (if p ∣ a then (∑' b : ℕ, pairTerm χ₁ χ m s (a, b)) else 0) := by
    intro a
    by_cases h : p ∣ a
    · rw [if_pos h, if_pos h]
      exact tsum_congr fun b => by rw [mul_one]
    · rw [if_neg h, if_neg h]
      simp only [mul_zero, tsum_zero]
  rw [tsum_congr h1, tsum_dvd_indicator hp (fun a => ∑' b : ℕ, pairTerm χ₁ χ m s (a, b))]
  have h2 : ∀ a' : ℕ, (∑' b : ℕ, pairTerm χ₁ χ m s (p * a', b))
      = ((χ * χ₁) (p : ZMod q) * (p : ℂ) ^ (-s)) * (∑' b : ℕ, pairTerm χ₁ χ m s (a', b)) :=
    fun a' => by rw [tsum_congr fun b => pairTerm_mul_left χ₁ χ hcop a' b s, tsum_mul_left]
  rw [tsum_congr h2, tsum_mul_left, ← tsum_prod_pairTerm χ₁ χ m hs]

/-- The `[p | b]` part of the pair sum. -/
lemma pairSum_right (χ₁ χ : DirichletCharacter ℂ q) {m p : ℕ} (hp : p ≠ 0) (hcop : m.Coprime p)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' ab : ℕ × ℕ, pairTerm χ₁ χ m s ab * (if p ∣ ab.2 then (1 : ℂ) else 0))
      = χ (p : ZMod q) * (p : ℂ) ^ (-s) * (∑' ab : ℕ × ℕ, pairTerm χ₁ χ m s ab) := by
  have hS := summable_pairTerm_mul χ₁ χ m hs (fun ab => if p ∣ ab.2 then (1 : ℂ) else 0)
    (fun ab => norm_indicator_le_one p ab.2)
  rw [Summable.tsum_prod' hS (fun a => hS.prod_factor a)]
  have h1 : ∀ a : ℕ, (∑' b : ℕ, pairTerm χ₁ χ m s (a, b) * (if p ∣ b then (1 : ℂ) else 0))
      = ∑' b' : ℕ, pairTerm χ₁ χ m s (a, p * b') := by
    intro a
    have hpoint : ∀ b : ℕ, pairTerm χ₁ χ m s (a, b) * (if p ∣ b then (1 : ℂ) else 0)
        = (if p ∣ b then pairTerm χ₁ χ m s (a, b) else 0) := by
      intro b
      by_cases h : p ∣ b <;> simp [h]
    rw [tsum_congr hpoint, tsum_dvd_indicator hp (fun b => pairTerm χ₁ χ m s (a, b))]
  rw [tsum_congr h1]
  have h2 : ∀ a : ℕ, (∑' b' : ℕ, pairTerm χ₁ χ m s (a, p * b'))
      = (χ (p : ZMod q) * (p : ℂ) ^ (-s)) * (∑' b' : ℕ, pairTerm χ₁ χ m s (a, b')) :=
    fun a => by
      rw [tsum_congr fun b' => pairTerm_mul_right χ₁ χ hcop a b' s, tsum_mul_left]
  rw [tsum_congr h2, tsum_mul_left, ← tsum_prod_pairTerm χ₁ χ m hs]

/-- The `[p | a] [p | b]` part of the pair sum. -/
lemma pairSum_both (χ₁ χ : DirichletCharacter ℂ q) {m p : ℕ} (hp : p ≠ 0) (hcop : m.Coprime p)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' ab : ℕ × ℕ, pairTerm χ₁ χ m s ab
        * ((if p ∣ ab.1 then (1 : ℂ) else 0) * (if p ∣ ab.2 then (1 : ℂ) else 0)))
      = ((χ * χ₁) (p : ZMod q) * (p : ℂ) ^ (-s) * (χ (p : ZMod q) * (p : ℂ) ^ (-s)))
          * (∑' ab : ℕ × ℕ, pairTerm χ₁ χ m s ab) := by
  have hS := summable_pairTerm_mul χ₁ χ m hs
    (fun ab => (if p ∣ ab.1 then (1 : ℂ) else 0) * (if p ∣ ab.2 then (1 : ℂ) else 0))
    (fun ab => norm_indicator_mul_le_one p ab.1 ab.2)
  rw [Summable.tsum_prod' hS (fun a => hS.prod_factor a)]
  have h1 : ∀ a : ℕ, (∑' b : ℕ, pairTerm χ₁ χ m s (a, b)
        * ((if p ∣ a then (1 : ℂ) else 0) * (if p ∣ b then (1 : ℂ) else 0)))
      = (if p ∣ a then (1 : ℂ) else 0)
          * (∑' b : ℕ, pairTerm χ₁ χ m s (a, b) * (if p ∣ b then (1 : ℂ) else 0)) := by
    intro a
    by_cases h : p ∣ a
    · simp only [if_pos h, one_mul]
    · simp only [if_neg h, zero_mul, mul_zero, tsum_zero]
  rw [tsum_congr h1]
  have h1b : ∀ a : ℕ, (∑' b : ℕ, pairTerm χ₁ χ m s (a, b) * (if p ∣ b then (1 : ℂ) else 0))
      = ∑' b' : ℕ, pairTerm χ₁ χ m s (a, p * b') := by
    intro a
    have hpoint : ∀ b : ℕ, pairTerm χ₁ χ m s (a, b) * (if p ∣ b then (1 : ℂ) else 0)
        = (if p ∣ b then pairTerm χ₁ χ m s (a, b) else 0) := by
      intro b
      by_cases h : p ∣ b <;> simp [h]
    rw [tsum_congr hpoint, tsum_dvd_indicator hp (fun b => pairTerm χ₁ χ m s (a, b))]
  simp only [h1b]
  have h3 : ∀ a : ℕ, (if p ∣ a then (1 : ℂ) else 0) * (∑' b' : ℕ, pairTerm χ₁ χ m s (a, p * b'))
      = (if p ∣ a then (∑' b' : ℕ, pairTerm χ₁ χ m s (a, p * b')) else 0) := by
    intro a
    by_cases h : p ∣ a <;> simp [h]
  rw [tsum_congr h3,
    tsum_dvd_indicator hp (fun a => ∑' b' : ℕ, pairTerm χ₁ χ m s (a, p * b'))]
  have h4 : ∀ a' : ℕ, (∑' b' : ℕ, pairTerm χ₁ χ m s (p * a', p * b'))
      = ((χ * χ₁) (p : ZMod q) * (p : ℂ) ^ (-s) * (χ (p : ZMod q) * (p : ℂ) ^ (-s)))
          * (∑' b' : ℕ, pairTerm χ₁ χ m s (a', b')) := by
    intro a'
    have hpt : ∀ b' : ℕ, pairTerm χ₁ χ m s (p * a', p * b')
        = ((χ * χ₁) (p : ZMod q) * (p : ℂ) ^ (-s) * (χ (p : ZMod q) * (p : ℂ) ^ (-s)))
            * pairTerm χ₁ χ m s (a', b') := by
      intro b'
      rw [pairTerm_mul_left χ₁ χ hcop a' (p * b') s, pairTerm_mul_right χ₁ χ hcop a' b' s]
      ring
    rw [tsum_congr hpt, tsum_mul_left]
  rw [tsum_congr h4, tsum_mul_left, ← tsum_prod_pairTerm χ₁ χ m hs]

/-- **The local recursion**: multiplying the level `m` by a prime `p ∤ m` multiplies the
"multiples of `m`" series by the local factor `sieveLocal χ₁ χ s p`. -/
lemma multSer_mul_prime (χ₁ χ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1)
    {p m : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) {s : ℂ} (hs : 1 < s.re) :
    multSer χ₁ χ (p * m) s = sieveLocal χ₁ χ s p * multSer χ₁ χ m s := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hcop : m.Coprime p := (hp.coprime_iff_not_dvd.mpr hpm).symm
  have hsplit : ∀ ab : ℕ × ℕ, pairTerm χ₁ χ (p * m) s ab
      = pairTerm χ₁ χ m s ab * (if p ∣ ab.1 then (1 : ℂ) else 0)
        + pairTerm χ₁ χ m s ab * (if p ∣ ab.2 then (1 : ℂ) else 0)
        - pairTerm χ₁ χ m s ab
            * ((if p ∣ ab.1 then (1 : ℂ) else 0) * (if p ∣ ab.2 then (1 : ℂ) else 0)) := by
    intro ab
    have hpm' : p * m ∣ ab.1 * ab.2 ↔ m ∣ ab.1 * ab.2 ∧ p ∣ ab.1 * ab.2 := by
      rw [show p * m = m.lcm p by rw [Nat.Coprime.lcm_eq_mul hcop]; ring, Nat.lcm_dvd_iff]
    have hind : (if p * m ∣ ab.1 * ab.2 then (1 : ℂ) else 0)
        = (if m ∣ ab.1 * ab.2 then (1 : ℂ) else 0)
          * ((if p ∣ ab.1 then (1 : ℂ) else 0) + (if p ∣ ab.2 then (1 : ℂ) else 0)
              - (if p ∣ ab.1 then (1 : ℂ) else 0) * (if p ∣ ab.2 then (1 : ℂ) else 0)) := by
      by_cases hm : m ∣ ab.1 * ab.2
      · by_cases h1 : p ∣ ab.1
        · rw [if_pos (hpm'.mpr ⟨hm, hp.dvd_mul.mpr (Or.inl h1)⟩), if_pos hm, if_pos h1]
          ring
        · by_cases h2 : p ∣ ab.2
          · rw [if_pos (hpm'.mpr ⟨hm, hp.dvd_mul.mpr (Or.inr h2)⟩), if_pos hm, if_neg h1, if_pos h2]
            ring
          · rw [if_neg (fun hc => (hp.dvd_mul.mp ((hpm'.mp hc).2)).elim h1 h2), if_pos hm, if_neg h1,
              if_neg h2]
            ring
      · rw [if_neg (fun hc => hm (hpm'.mp hc).1), if_neg hm]
        ring
    have hA : (χ * χ₁) (ab.1 : ZMod q) * χ (ab.2 : ZMod q)
        * (((ab.1 * ab.2 : ℕ)) : ℂ) ^ (-s)
        = ((χ * χ₁) (ab.1 : ZMod q) * χ (ab.2 : ZMod q))
            * (((ab.1 * ab.2 : ℕ)) : ℂ) ^ (-s) := by ring
    have hp1 : pairTerm χ₁ χ (p * m) s ab
        = (if p * m ∣ ab.1 * ab.2 then (1 : ℂ) else 0)
            * ((χ * χ₁) (ab.1 : ZMod q) * χ (ab.2 : ZMod q)
                * (((ab.1 * ab.2 : ℕ)) : ℂ) ^ (-s)) := by
      rw [pairTerm]
      by_cases h : p * m ∣ ab.1 * ab.2 <;> simp [h, hA]
    have hp2 : pairTerm χ₁ χ m s ab
        = (if m ∣ ab.1 * ab.2 then (1 : ℂ) else 0)
            * ((χ * χ₁) (ab.1 : ZMod q) * χ (ab.2 : ZMod q)
                * (((ab.1 * ab.2 : ℕ)) : ℂ) ^ (-s)) := by
      rw [pairTerm]
      by_cases h : m ∣ ab.1 * ab.2 <;> simp [h, hA]
    rw [hp1, hp2, hind]
    ring
  have hXA : Summable (fun ab : ℕ × ℕ =>
      pairTerm χ₁ χ m s ab * (if p ∣ ab.1 then (1 : ℂ) else 0)) :=
    summable_pairTerm_mul χ₁ χ m hs _ fun ab => norm_indicator_le_one p ab.1
  have hXB : Summable (fun ab : ℕ × ℕ =>
      pairTerm χ₁ χ m s ab * (if p ∣ ab.2 then (1 : ℂ) else 0)) :=
    summable_pairTerm_mul χ₁ χ m hs _ fun ab => norm_indicator_le_one p ab.2
  have hXC : Summable (fun ab : ℕ × ℕ => pairTerm χ₁ χ m s ab
      * ((if p ∣ ab.1 then (1 : ℂ) else 0) * (if p ∣ ab.2 then (1 : ℂ) else 0))) :=
    summable_pairTerm_mul χ₁ χ m hs _ fun ab => norm_indicator_mul_le_one p ab.1 ab.2
  rw [← tsum_pairTerm_eq_multSer χ₁ χ hχ₁ (p * m) hs,
    ← tsum_pairTerm_eq_multSer χ₁ χ hχ₁ m hs,
    tsum_prod_pairTerm χ₁ χ (p * m) hs, tsum_prod_pairTerm χ₁ χ m hs]
  have hstep : (∑' a : ℕ, ∑' b : ℕ, pairTerm χ₁ χ (p * m) s (a, b))
      = (∑' ab : ℕ × ℕ, pairTerm χ₁ χ m s ab * (if p ∣ ab.1 then (1 : ℂ) else 0))
        + (∑' ab : ℕ × ℕ, pairTerm χ₁ χ m s ab * (if p ∣ ab.2 then (1 : ℂ) else 0))
        - (∑' ab : ℕ × ℕ, pairTerm χ₁ χ m s ab
            * ((if p ∣ ab.1 then (1 : ℂ) else 0) * (if p ∣ ab.2 then (1 : ℂ) else 0))) := by
    rw [tsum_congr fun a => tsum_congr fun b => hsplit (a, b)]
    have hinner : ∀ a : ℕ, (∑' b : ℕ, (pairTerm χ₁ χ m s (a, b) * (if p ∣ a then (1 : ℂ) else 0)
          + pairTerm χ₁ χ m s (a, b) * (if p ∣ b then (1 : ℂ) else 0)
          - pairTerm χ₁ χ m s (a, b)
              * ((if p ∣ a then (1 : ℂ) else 0) * (if p ∣ b then (1 : ℂ) else 0))))
        = (∑' b : ℕ, pairTerm χ₁ χ m s (a, b) * (if p ∣ a then (1 : ℂ) else 0))
          + (∑' b : ℕ, pairTerm χ₁ χ m s (a, b) * (if p ∣ b then (1 : ℂ) else 0))
          - (∑' b : ℕ, pairTerm χ₁ χ m s (a, b)
              * ((if p ∣ a then (1 : ℂ) else 0) * (if p ∣ b then (1 : ℂ) else 0))) := by
      intro a
      rw [Summable.tsum_sub ((hXA.prod_factor a).add (hXB.prod_factor a)) (hXC.prod_factor a),
        Summable.tsum_add (hXA.prod_factor a) (hXB.prod_factor a)]
    rw [tsum_congr hinner]
    rw [Summable.tsum_sub (hXA.prod.add hXB.prod) hXC.prod, Summable.tsum_add hXA.prod hXB.prod]
    rw [← Summable.tsum_prod' hXA (fun a => hXA.prod_factor a),
      ← Summable.tsum_prod' hXB (fun a => hXB.prod_factor a),
      ← Summable.tsum_prod' hXC (fun a => hXC.prod_factor a)]
  rw [hstep, pairSum_left χ₁ χ hp0 hcop hs, pairSum_right χ₁ χ hp0 hcop hs,
    pairSum_both χ₁ χ hp0 hcop hs]
  have hkey : (χ * χ₁) (p : ZMod q) * (p : ℂ) ^ (-s) + χ (p : ZMod q) * (p : ℂ) ^ (-s)
      - (χ * χ₁) (p : ZMod q) * (p : ℂ) ^ (-s) * (χ (p : ZMod q) * (p : ℂ) ^ (-s))
      = sieveLocal χ₁ χ s p := by
    rw [mul_chi_apply χ₁ χ hχ₁ (p : ZMod q), sieveLocal, ← cpow_neg_add_self hp0 s]
    ring
  rw [show (χ * χ₁) (p : ZMod q) * (p : ℂ) ^ (-s) * (∑' ab : ℕ × ℕ, pairTerm χ₁ χ m s ab)
        + χ (p : ZMod q) * (p : ℂ) ^ (-s) * (∑' ab : ℕ × ℕ, pairTerm χ₁ χ m s ab)
        - ((χ * χ₁) (p : ZMod q) * (p : ℂ) ^ (-s) * (χ (p : ZMod q) * (p : ℂ) ^ (-s)))
            * (∑' ab : ℕ × ℕ, pairTerm χ₁ χ m s ab)
      = ((χ * χ₁) (p : ZMod q) * (p : ℂ) ^ (-s) + χ (p : ZMod q) * (p : ℂ) ^ (-s)
          - (χ * χ₁) (p : ZMod q) * (p : ℂ) ^ (-s) * (χ (p : ZMod q) * (p : ℂ) ^ (-s)))
        * (∑' ab : ℕ × ℕ, pairTerm χ₁ χ m s ab) by ring, hkey]
  rw [← tsum_prod_pairTerm χ₁ χ m hs]

/-- Summability of the "multiples of `m`" series. -/
lemma summable_multSer (χ₁ χ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) (m : ℕ) {s : ℂ}
    (hs : 1 < s.re) :
    Summable (fun n : ℕ => (if m ∣ n then cfun χ₁ χ n else 0) / (n : ℂ) ^ s) := by
  refine Summable.of_norm_bounded (summable_cfun χ₁ χ hχ₁ hs).norm fun n => ?_
  by_cases h : m ∣ n
  · rw [if_pos h]
  · rw [if_neg h]
    rw [zero_div, norm_zero, norm_div]
    positivity

/-- The base case `m = 1` of the local-factor recursion. -/
lemma multSer_one (χ₁ χ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) {s : ℂ} (hs : 1 < s.re) :
    multSer χ₁ χ 1 s
      = DirichletCharacter.LFunction χ s * DirichletCharacter.LFunction (χ * χ₁) s := by
  have hA : LSeriesSummable (fun n : ℕ => (χ * χ₁) (n : ZMod q)) s :=
    LSeriesSummable_of_one_lt_re (χ * χ₁) hs
  have hB : LSeriesSummable (fun n : ℕ => χ (n : ZMod q)) s :=
    LSeriesSummable_of_one_lt_re χ hs
  have hfun : (fun n : ℕ => cfun χ₁ χ n)
      = LSeries.convolution (fun n : ℕ => (χ * χ₁) (n : ZMod q)) (fun n : ℕ => χ (n : ZMod q)) := by
    funext n
    simp only [LSeries.convolution_def, cfun_eq_antidiag χ₁ χ hχ₁ n]
  calc multSer χ₁ χ 1 s
      = LSeries (fun n : ℕ => cfun χ₁ χ n) s := by
        rw [multSer, LSeries_def₀ (cfun_zero χ₁ χ) s]
        exact tsum_congr fun n => by rw [if_pos (one_dvd n)]
    _ = LSeries (LSeries.convolution (fun n : ℕ => (χ * χ₁) (n : ZMod q))
          (fun n : ℕ => χ (n : ZMod q))) s := by rw [hfun]
    _ = LSeries (fun n : ℕ => (χ * χ₁) (n : ZMod q)) s
          * LSeries (fun n : ℕ => χ (n : ZMod q)) s := LSeries_convolution' hA hB
    _ = DirichletCharacter.LFunction (χ * χ₁) s * DirichletCharacter.LFunction χ s := by
        rw [← LFunction_eq_LSeries (χ * χ₁) hs, ← LFunction_eq_LSeries χ hs]
    _ = DirichletCharacter.LFunction χ s * DirichletCharacter.LFunction (χ * χ₁) s := mul_comm _ _

/-- The lcm of two squarefree numbers is squarefree. -/
lemma squarefree_lcm {d e : ℕ} (hd : Squarefree d) (he : Squarefree e) :
    Squarefree (Nat.lcm d e) := by
  rcases eq_or_ne d 0 with rfl | hd0
  · exact absurd hd (by
      rw [Nat.squarefree_iff_prime_squarefree]
      intro h
      exact h 2 Nat.prime_two (by norm_num))
  rcases eq_or_ne e 0 with rfl | he0
  · exact absurd he (by
      rw [Nat.squarefree_iff_prime_squarefree]
      intro h
      exact h 2 Nat.prime_two (by norm_num))
  rw [Nat.squarefree_iff_factorization_le_one (Nat.lcm_pos (Nat.pos_of_ne_zero hd0)
    (Nat.pos_of_ne_zero he0)).ne']
  intro x
  rw [Nat.factorization_lcm hd0 he0]
  exact max_le ((Nat.squarefree_iff_factorization_le_one hd0).mp hd x)
    ((Nat.squarefree_iff_factorization_le_one he0).mp he x)

/-- **The local-factor identity**: for squarefree `m`,
`Σ_{m | n} a(n)χ(n)n^{-s} = L(s,χ)L(s,χχ₁)∏_{p | m} sieveLocal χ₁ χ s p`. -/
lemma multSer_squarefree (χ₁ χ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) {s : ℂ}
    (hs : 1 < s.re) :
    ∀ m : ℕ, Squarefree m →
      multSer χ₁ χ m s = DirichletCharacter.LFunction χ s * DirichletCharacter.LFunction (χ * χ₁) s
        * ∏ p ∈ m.primeFactors, sieveLocal χ₁ χ s p := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rcases eq_or_ne m 1 with rfl | hm1
    · rw [multSer_one χ₁ χ hχ₁ hs, Nat.primeFactors_one, Finset.prod_empty, mul_one]
    · rcases eq_or_ne m 0 with rfl | hm0
      · exact absurd hm (by
          rw [Nat.squarefree_iff_prime_squarefree]
          intro h
          exact h 2 Nat.prime_two (by norm_num))
      · obtain ⟨p, hp, hpm⟩ := Nat.exists_prime_and_dvd hm1
        have hdiv0 : m / p ≠ 0 := by
          intro h
          have hc := Nat.mul_div_cancel' hpm
          rw [h, mul_zero] at hc
          exact hm0 hc.symm
        have hnotp : ¬ p ∣ m / p := by
          intro h
          have hp2 : p * p ∣ m := by
            rw [← Nat.mul_div_cancel' hpm]
            exact mul_dvd_mul_left p h
          exact (Nat.squarefree_iff_prime_squarefree.mp hm p hp) hp2
        have hsq : Squarefree (m / p) := Squarefree.squarefree_of_dvd (Nat.div_dvd_of_dvd hpm) hm
        have hlt : m / p < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm0) hp.one_lt
        have hpfs : (p * (m / p)).primeFactors = insert p (m / p).primeFactors := by
          have hp1 : p.primeFactors = {p} := by
            simpa using Nat.primeFactors_prime_pow (k := 1) one_ne_zero hp
          rw [Nat.primeFactors_mul hp.ne_zero hdiv0, hp1, Finset.singleton_union]
        have hnotmem : p ∉ (m / p).primeFactors :=
          fun hmem => hnotp (Nat.mem_primeFactors.mp hmem).2.1
        rw [← Nat.mul_div_cancel' hpm, multSer_mul_prime χ₁ χ hχ₁ hp hnotp hs,
          ih (m / p) hlt hsq, hpfs, Finset.prod_insert hnotmem]
        ring

/-- The detector series splits into the `multSer`s of the lcm's of the sieve weights. -/
lemma detector_eq_lcm_sum (χ₁ χ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1)
    {R : ℕ} {θw : ℕ → ℝ} (hθ : IsSieveWeight R θw) {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, detCoeff χ₁ χ θw n / (n : ℂ) ^ s)
      = ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
          (θw d : ℂ) * (θw e : ℂ) * multSer χ₁ χ (Nat.lcm d e) s := by
  have hterm : ∀ n : ℕ, detCoeff χ₁ χ θw n / (n : ℂ) ^ s
      = ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
          (θw d : ℂ) * (θw e : ℂ)
            * ((if Nat.lcm d e ∣ n then cfun χ₁ χ n else 0) / (n : ℂ) ^ s) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [detCoeff_eq_mul_sq]
      simp [cfun_zero]
    · have hexp := divisors_sum_sq_eq_lcm_sum hθ hn
      have hSq : (((∑ d ∈ n.divisors, θw d : ℝ)) : ℂ) ^ 2
          = ∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R,
              (θw d : ℂ) * (θw e : ℂ) * (if Nat.lcm d e ∣ n then (1 : ℂ) else 0) := by
        rw [← Complex.ofReal_pow, hexp, Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun (d : ℕ) _ => ?_
        rw [Complex.ofReal_sum]
        refine Finset.sum_congr rfl fun (e : ℕ) _ => ?_
        by_cases h : Nat.lcm d e ∣ n <;> simp [h]
      rw [detCoeff_eq_mul_sq, hSq, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun (d : ℕ) _ => ?_
      rw [Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun (e : ℕ) _ => ?_
      by_cases h : Nat.lcm d e ∣ n <;> simp [h, div_eq_mul_inv] <;> ring
  rw [tsum_congr hterm]
  rw [Summable.tsum_finsetSum (s := Finset.Icc 1 R)
    (f := fun d (n : ℕ) => ∑ e ∈ Finset.Icc 1 R, (θw d : ℂ) * (θw e : ℂ)
      * ((if Nat.lcm d e ∣ n then cfun χ₁ χ n else 0) / (n : ℂ) ^ s))
    (fun d _ => summable_sum fun (e : ℕ) _ => (summable_multSer χ₁ χ hχ₁ (Nat.lcm d e) hs).mul_left _)]
  refine Finset.sum_congr rfl fun (d : ℕ) hd => ?_
  rw [Summable.tsum_finsetSum (s := Finset.Icc 1 R)
    (f := fun e (n : ℕ) => (θw d : ℂ) * (θw e : ℂ)
      * ((if Nat.lcm d e ∣ n then cfun χ₁ χ n else 0) / (n : ℂ) ^ s))
    (fun e _ => (summable_multSer χ₁ χ hχ₁ (Nat.lcm d e) hs).mul_left _)]
  refine Finset.sum_congr rfl fun (e : ℕ) he => ?_
  rw [tsum_mul_left]
  rfl

theorem DetectorSeries {q : ℕ} [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1)
    {R : ℕ} {θw : ℕ → ℝ} (hθ : IsSieveWeight R θw) {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, detCoeff χ₁ χ θw n / (n : ℂ) ^ s)
      = DirichletCharacter.LFunction χ s * DirichletCharacter.LFunction (χ * χ₁) s
          * sieveG χ₁ R θw s χ := by
  rw [detector_eq_lcm_sum χ₁ χ hχ₁ hθ hs]
  have hstep : ∀ d ∈ Finset.Icc 1 R, ∀ e ∈ Finset.Icc 1 R,
      (θw d : ℂ) * (θw e : ℂ) * multSer χ₁ χ (Nat.lcm d e) s
        = (θw d : ℂ) * (θw e : ℂ) * (DirichletCharacter.LFunction χ s
            * DirichletCharacter.LFunction (χ * χ₁) s
            * ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ s p) := by
    intro d _ e _
    by_cases hde : θw d * θw e = 0
    · have hdeC : (θw d : ℂ) * (θw e : ℂ) = 0 := by
        rw [← Complex.ofReal_mul, hde, Complex.ofReal_zero]
      rw [hdeC, zero_mul, zero_mul]
    · have hd0 : θw d ≠ 0 := fun h => hde (by rw [h, zero_mul])
      have he0 : θw e ≠ 0 := fun h => hde (by rw [h, mul_zero])
      have hsd : Squarefree d := by
        by_contra h
        exact hd0 (hθ.2.1 d (Or.inl h))
      have hse : Squarefree e := by
        by_contra h
        exact he0 (hθ.2.1 e (Or.inl h))
      rw [multSer_squarefree χ₁ χ hχ₁ hs (Nat.lcm d e) (squarefree_lcm hsd hse)]
  rw [Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun e he => hstep d hd e he]
  rw [sieveG]
  rw [show (∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R, (θw d : ℂ) * (θw e : ℂ)
        * (DirichletCharacter.LFunction χ s * DirichletCharacter.LFunction (χ * χ₁) s
            * ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ s p))
      = DirichletCharacter.LFunction χ s * DirichletCharacter.LFunction (χ * χ₁) s
        * (∑ d ∈ Finset.Icc 1 R, ∑ e ∈ Finset.Icc 1 R, (θw d : ℂ) * (θw e : ℂ)
            * ∏ p ∈ (Nat.lcm d e).primeFactors, sieveLocal χ₁ χ s p) by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun (d : ℕ) hd => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun (e : ℕ) he => ?_
    ring]

end Work.LinnikAreas.BGTZ
