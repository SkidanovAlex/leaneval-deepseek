import Submission.ZagierHoffmanProof.SuperLSeries
import Submission.Commons.Topology.Algebra.Valued.summable_of_v_le_exp_tendsto

/-!
# Evaluating a super-entire series at a point of `K`

This is the piece of the ABP framework that a *coefficientwise* (Tate-algebra) development cannot
see: Anderson–Brownawell–Papanikolas' criterion is about a vector `ψ ∈ Mat(ε)` of series
converging everywhere and the evaluation `ψ(θ)` at the *boundary* point `t = θ` of the unit disc.

Because the coefficients of `f ∈ ε` decay faster than any exponential (`SuperEntire`), the series
`∑ aₙ cⁿ` converges **for every** `c ∈ K` (not only for `v c ≤ 1`), so a genuine evaluation map

  `evalSeries f c = ∑' n, aₙ · cⁿ`

is available on `ε` (and, by the convention that a non-summable `tsum` is `0`, it is defined for
every power series).  The key structural property is that evaluation converts the Frobenius twist
into a power:

  ★★ `evalSeries_frobTwist : evalSeries (f^{(k)}) (c ^ (q^k)) = (evalSeries f c) ^ (q^k)`,

which is the form in which the "MZ property" of Chang (`𝓛(θ^{q^j}) = 𝓛(θ)^{q^j}`) is used.

## Main results

* `SuperEntire.summable_eval` — the defining family is summable for `f ∈ ε` and every `c`.
* `evalSeries` — the evaluation map, with `evalSeries_C`, `evalSeries_X`, `evalSeries_add`,
  `evalSeries_neg`, `evalSeries_sub`, `evalSeries_C_mul`, `evalSeries_finset_sum`,
  `evalSeries_natCast`, `evalSeries_monomial`.
* ★★ `evalSeries_frobTwist`.
* ★★ `evalSeries_mul` — **evaluation is multiplicative**: `(f·g)(c) = f(c)·g(c)` — together with
  `evalSeries_add`/`evalSeries_one` this makes `c ↦ f(c)` a ring homomorphism on `ε`
  (`evalSeriesRingHom`); `evalSeries_pow`, `evalSeries_prod` are the corollaries.
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

/-- **The evaluation of a power series at a point of `K`**: `∑ aₙ cⁿ`.  (Convergence is not part
of the definition; the lemmas below require `SuperEntire`.) -/
noncomputable def evalSeries (f : PowerSeries K) (c : K) : K :=
  ∑' n : ℕ, PowerSeries.coeff n f * c ^ n

lemma evalSeries_def (f : PowerSeries K) (c : K) :
    evalSeries f c = ∑' n : ℕ, PowerSeries.coeff n f * c ^ n := rfl

/-- Every non-zero element of the value group `ℤᵐ⁰` is `exp k` for an integer `k`. -/
lemma exists_exp_eq_of_ne_zero {x : ℤᵐ⁰} (hx : x ≠ 0) : ∃ k : ℤ, x = WithZero.exp k :=
  WithZero.expRecOn x (motive := fun x => x ≠ 0 → ∃ k : ℤ, x = WithZero.exp k)
    (fun h => absurd rfl h) (fun a _ => ⟨a, rfl⟩) hx

section eval

variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- **The defining family of the evaluation of a super-entire series is summable**: this is where
the "faster than any exponential" decay is used. -/
theorem SuperEntire.summable_eval {f : PowerSeries K} (hf : SuperEntire f) (c : K) :
    Summable fun n : ℕ => PowerSeries.coeff n f * c ^ n := by
  rcases eq_or_ne c 0 with rfl | hc
  · refine (summable_of_ne_finset_zero (s := {0}) ?_)
    intro n hn
    rw [Finset.mem_singleton] at hn
    rw [zero_pow (by omega : n ≠ 0), mul_zero]
  · obtain ⟨k, hk⟩ := exists_exp_eq_of_ne_zero (x := Valued.v c) (by simpa using hc)
    obtain ⟨a, ha⟩ := hf (k.natAbs + 1)
    have hcast : (((k.natAbs + 1 : ℕ)) : ℤ) = ((k.natAbs : ℕ) : ℤ) + 1 := by push_cast; ring
    rw [hcast] at ha
    have hpos1 : (1 : ℤ) ≤ ((k.natAbs : ℕ) : ℤ) + 1 - k := by
      have := Int.le_natAbs (a := k)
      omega
    refine Commons.Topology.Algebra.Valued.summable_of_v_le_exp_tendsto
      (a := fun n => a - (((k.natAbs : ℕ) : ℤ) + 1 - k) * (n : ℤ)) ?_ ?_
    · refine Filter.tendsto_atBot.mpr fun b => ?_
      rw [Filter.eventually_atTop]
      refine ⟨b.natAbs + a.natAbs + 1, fun n hn => ?_⟩
      have hb : -(b : ℤ) ≤ ((b.natAbs : ℕ) : ℤ) := by
        have := Int.le_natAbs (a := -b)
        simpa using this
      have ha' : (a : ℤ) ≤ ((a.natAbs : ℕ) : ℤ) := Int.le_natAbs
      have hn' : (((b.natAbs + a.natAbs + 1 : ℕ)) : ℤ) ≤ (n : ℤ) :=
        Int.ofNat_le.mpr (by omega)
      have hsum : (((b.natAbs + a.natAbs + 1 : ℕ)) : ℤ)
          = ((b.natAbs : ℕ) : ℤ) + ((a.natAbs : ℕ) : ℤ) + 1 := by push_cast; ring
      have h1 : a - b ≤ (n : ℤ) := by linarith
      have h2 : (n : ℤ) ≤ (((k.natAbs : ℕ) : ℤ) + 1 - k) * (n : ℤ) :=
        le_mul_of_one_le_left (by positivity) hpos1
      linarith
    · intro n
      rw [Valuation.map_mul, map_pow, hk]
      calc Valued.v (PowerSeries.coeff n f) * (WithZero.exp k) ^ n
          = Valued.v (PowerSeries.coeff n f) * WithZero.exp (k * (n : ℤ)) := by rw [expmul]
        _ ≤ WithZero.exp (a - (((k.natAbs : ℕ) : ℤ) + 1) * (n : ℤ))
              * WithZero.exp (k * (n : ℤ)) := mul_le_mul' (ha n) le_rfl
        _ = WithZero.exp ((a - (((k.natAbs : ℕ) : ℤ) + 1) * (n : ℤ)) + k * (n : ℤ)) := by
            rw [← WithZero.exp_add]
        _ = WithZero.exp (a - (((k.natAbs : ℕ) : ℤ) + 1 - k) * (n : ℤ)) := by
            congr 1
            ring

/-- Evaluation of a constant. -/
@[simp] lemma evalSeries_C (a c : K) : evalSeries (PowerSeries.C a) c = a := by
  rw [evalSeries_def]
  rw [tsum_eq_single (L := SummationFilter.unconditional ℕ) 0
    (fun n hn => by rw [PowerSeries.coeff_C, if_neg hn, zero_mul])]
  rw [PowerSeries.coeff_C, if_pos rfl, pow_zero, mul_one]

/-- Evaluation of `t`. -/
@[simp] lemma evalSeries_X (c : K) : evalSeries (PowerSeries.X : PowerSeries K) c = c := by
  rw [evalSeries_def]
  rw [tsum_eq_single (L := SummationFilter.unconditional ℕ) 1]
  · rw [PowerSeries.coeff_X, if_pos rfl, pow_one, one_mul]
  · intro n hn
    rw [PowerSeries.coeff_X, if_neg hn, zero_mul]

/-- Evaluation of a monomial. -/
@[simp] lemma evalSeries_monomial (a c : K) (n : ℕ) :
    evalSeries (PowerSeries.monomial n a) c = a * c ^ n := by
  rw [evalSeries_def]
  rw [tsum_eq_single (L := SummationFilter.unconditional ℕ) n
    (fun m hm => by rw [PowerSeries.coeff_monomial, if_neg hm, zero_mul])]
  rw [PowerSeries.coeff_monomial, if_pos rfl]

/-- Evaluation is additive (on summable families). -/
lemma evalSeries_add {f g : PowerSeries K} (hf : SuperEntire f) (hg : SuperEntire g) (c : K) :
    evalSeries (f + g) c = evalSeries f c + evalSeries g c := by
  rw [evalSeries_def, evalSeries_def, evalSeries_def]
  rw [show (fun n : ℕ => PowerSeries.coeff n (f + g) * c ^ n)
      = fun n : ℕ => (PowerSeries.coeff n f * c ^ n + PowerSeries.coeff n g * c ^ n) from
    funext fun n => by rw [map_add (PowerSeries.coeff n), add_mul]]
  exact (hf.summable_eval c).tsum_add (hg.summable_eval c)

/-- Evaluation is compatible with negation. -/
@[simp] lemma evalSeries_neg (f : PowerSeries K) (c : K) :
    evalSeries (-f) c = -evalSeries f c := by
  rw [evalSeries_def, evalSeries_def, ← tsum_neg]
  exact tsum_congr fun n => by rw [map_neg (PowerSeries.coeff n), neg_mul]

/-- Evaluation is compatible with subtraction. -/
lemma evalSeries_sub {f g : PowerSeries K} (hf : SuperEntire f) (hg : SuperEntire g) (c : K) :
    evalSeries (f - g) c = evalSeries f c - evalSeries g c := by
  rw [sub_eq_add_neg, evalSeries_add hf hg.neg, evalSeries_neg, sub_eq_add_neg]

/-- Evaluation of a `K`-multiple. -/
lemma evalSeries_C_mul (a : K) (f : PowerSeries K) (c : K) :
    evalSeries (PowerSeries.C a * f) c = a * evalSeries f c := by
  rw [evalSeries_def, evalSeries_def, ← tsum_mul_left]
  exact tsum_congr fun n => by rw [PowerSeries.coeff_C_mul, mul_assoc]

/-- Evaluation of a finite sum. -/
lemma evalSeries_finset_sum {ι : Type*} (s : Finset ι) (g : ι → PowerSeries K)
    (hg : ∀ i ∈ s, SuperEntire (g i)) (c : K) :
    evalSeries (∑ i ∈ s, g i) c = ∑ i ∈ s, evalSeries (g i) c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evalSeries_def]
  | insert a s ha ih =>
    have hga : SuperEntire (g a) := hg a (Finset.mem_insert_self a s)
    have hs : ∀ i ∈ s, SuperEntire (g i) := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, evalSeries_add hga (SuperEntire.sum s g hs) c,
      ih hs]

lemma evalSeries_natCast (n : ℕ) (c : K) :
    evalSeries (n : PowerSeries K) c = (n : K) := by
  have hCN : (n : PowerSeries K) = PowerSeries.C (n : K) := by
    rw [← map_natCast (PowerSeries.C : K →+* PowerSeries K) n]
  rw [hCN, evalSeries_C]

end eval

section twist

variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- **Evaluation converts the Frobenius twist into a power**:
`(f^{(k)})(c^(q^k)) = (f(c))^(q^k)`. -/
theorem evalSeries_frobTwist (q : ℕ) [FrobPow K q] {f : PowerSeries K}
    (hf : SuperEntire f) (c : K) (k : ℕ) :
    evalSeries (frobTwist (R := K) (p := q) k f) (c ^ (q ^ k))
      = (evalSeries f c) ^ (q ^ k) := by
  have hsum := hf.summable_eval c
  have hpt : (∑' n : ℕ, (PowerSeries.coeff n f * c ^ n) ^ (q ^ k))
      = (∑' n : ℕ, PowerSeries.coeff n f * c ^ n) ^ (q ^ k) :=
    (ZagierHoffmanPositiveChar.tsum_pow_frobPow hsum k).symm
  rw [evalSeries_def, evalSeries_def, ← hpt]
  refine tsum_congr fun n => ?_
  rw [frobTwist_coeff, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]

end twist

section mul

variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- **Evaluation is multiplicative** on super-entire series: `(f·g)(c) = f(c)·g(c)`. -/
theorem evalSeries_mul {f g : PowerSeries K} (hf : SuperEntire f) (hg : SuperEntire g) (c : K) :
    evalSeries (f * g) c = evalSeries f c * evalSeries g c := by
  haveI : NonarchimedeanRing K := Commons.Topology.Algebra.Valued.nonarchimedeanRing
  have hf' : Summable fun n : ℕ => PowerSeries.coeff n f * c ^ n := hf.summable_eval c
  have hg' : Summable fun n : ℕ => PowerSeries.coeff n g * c ^ n := hg.summable_eval c
  have hprod : Summable fun p : ℕ × ℕ =>
      (PowerSeries.coeff p.1 f * c ^ p.1) * (PowerSeries.coeff p.2 g * c ^ p.2) :=
    Summable.mul_of_nonarchimedean
      (f := fun n => PowerSeries.coeff n f * c ^ n)
      (g := fun n => PowerSeries.coeff n g * c ^ n) hf' hg'
  have hcauchy : (∑' n : ℕ, PowerSeries.coeff n f * c ^ n) * (∑' n : ℕ, PowerSeries.coeff n g * c ^ n)
      = ∑' n : ℕ, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
          (PowerSeries.coeff kl.1 f * c ^ kl.1) * (PowerSeries.coeff kl.2 g * c ^ kl.2) :=
    hf'.tsum_mul_tsum_eq_tsum_sum_antidiagonal hg' hprod
  simp only [evalSeries_def]
  rw [hcauchy]
  refine tsum_congr fun n => ?_
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
  rw [← hp, pow_add]
  ring

/-- Evaluation of `1`. -/
lemma evalSeries_one (c : K) : evalSeries (1 : PowerSeries K) c = 1 := by
  rw [show (1 : PowerSeries K) = PowerSeries.C 1 from (map_one PowerSeries.C).symm, evalSeries_C]

/-- Evaluation is compatible with powers. -/
theorem evalSeries_pow {f : PowerSeries K} (hf : SuperEntire f) (n : ℕ) (c : K) :
    evalSeries (f ^ n) c = (evalSeries f c) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, evalSeries_one]
  | succ k ih => rw [pow_succ, pow_succ, evalSeries_mul (hf.pow k) hf c, ih]

/-- Evaluation is compatible with finite products. -/
lemma evalSeries_prod {ι : Type*} (s : Finset ι) (g : ι → PowerSeries K)
    (hg : ∀ i ∈ s, SuperEntire (g i)) (c : K) :
    evalSeries (∏ i ∈ s, g i) c = ∏ i ∈ s, evalSeries (g i) c := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evalSeries_one]
  | insert a s ha ih =>
    have hga : SuperEntire (g a) := hg a (Finset.mem_insert_self a s)
    have hs : ∀ i ∈ s, SuperEntire (g i) := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      evalSeries_mul hga (SuperEntire.prod s g hs) c, ih hs]

/-- **Evaluation at `c` is a ring homomorphism** on the ring `ε` of super-entire series. -/
noncomputable def evalSeriesRingHom (c : K) : ↥(superEntireSubring K) →+* K where
  toFun f := evalSeries (f : PowerSeries K) c
  map_one' := by
    show evalSeries ((1 : ↥(superEntireSubring K)) : PowerSeries K) c = 1
    rw [Subring.coe_one, evalSeries_one]
  map_mul' f g := by
    show evalSeries (((f * g : ↥(superEntireSubring K))) : PowerSeries K) c
        = evalSeries (f : PowerSeries K) c * evalSeries (g : PowerSeries K) c
    rw [Subring.coe_mul, evalSeries_mul f.2 g.2 c]
  map_zero' := by
    show evalSeries ((0 : ↥(superEntireSubring K)) : PowerSeries K) c = 0
    rw [Subring.coe_zero]
    simp only [evalSeries_def, map_zero, zero_mul, tsum_zero]
  map_add' f g := by
    show evalSeries (((f + g : ↥(superEntireSubring K))) : PowerSeries K) c
        = evalSeries (f : PowerSeries K) c + evalSeries (g : PowerSeries K) c
    rw [Subring.coe_add, evalSeries_add f.2 g.2 c]

@[simp] lemma evalSeriesRingHom_apply (c : K) (f : ↥(superEntireSubring K)) :
    evalSeriesRingHom c f = evalSeries (f : PowerSeries K) c := rfl

end mul

section poly

variable [CompleteSpace K] [NonarchimedeanAddGroup K]

/-- A polynomial, viewed as a power series, is super-entire. -/
lemma SuperEntire.polynomial (p : Polynomial K) : SuperEntire (p : PowerSeries K) := by
  induction p using Polynomial.induction_on with
  | C a => simpa using SuperEntire.C a
  | add p q hp hq => rw [Polynomial.coe_add]; exact hp.add hq
  | monomial n a _ =>
      rw [Polynomial.coe_mul, Polynomial.coe_C, Polynomial.coe_pow, Polynomial.coe_X]
      exact (SuperEntire.C a).mul (SuperEntire.X.pow (n + 1))

/-- **Evaluation of a polynomial agrees with the polynomial evaluation**: the series evaluation
of `p ∈ K[t] ⊂ ε` at `c` is `p(c)`.  This is the bridge between the analytic evaluation of `ε` and
the algebraic evaluation used in the conclusion `P(θ) = ρ` of the ABP criterion. -/
lemma evalSeries_polynomial (p : Polynomial K) (c : K) :
    evalSeries (p : PowerSeries K) c = p.eval c := by
  have hmain : (∑' n : ℕ, (PowerSeries.coeff n (p : PowerSeries K)) * c ^ n)
      = ∑ n ∈ Finset.range (p.natDegree + 1),
          (PowerSeries.coeff n (p : PowerSeries K)) * c ^ n := by
    refine tsum_eq_sum (L := SummationFilter.unconditional ℕ) (fun n hn => ?_)
    rw [Finset.mem_range, not_lt] at hn
    rw [Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt hn, zero_mul]
  rw [evalSeries_def, hmain, Polynomial.eval_eq_sum_range]
  exact Finset.sum_congr rfl (fun n _ => by rw [Polynomial.coeff_coe])

end poly

end ZagierHoffmanPositiveChar
