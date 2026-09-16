import Submission.ZagierHoffmanProof.EntireTwist
import Submission.Commons.Topology.Algebra.Valued.powerSeries_bounded_mul

/-!
# The ring `ε` of "super-entire" series (Anderson–Brownawell–Papanikolas)

Anderson–Brownawell–Papanikolas attach to `K∞` the ring `ε` of series `∑ aₙ tⁿ` which converge
*everywhere*: `|aₙ|^{1/n} → 0`.  In the coefficient-valuation normalisation of this workspace
(where `entireSubring K` is the Tate algebra `T`, i.e. the series converging on the closed unit
disc), the "convergence everywhere" condition on the coefficients is that for every `M` the
sequence `n ↦ v aₙ + M·n` is bounded above.

We use the equivalent *uniform* formulation
`SuperEntire f := ∀ M, ∃ a, ∀ n, v aₙ ≤ exp (a - M·n)`
(equivalence with the naive "eventually `v aₙ < (exp(-1))^{M·n}`" statement follows from the
boundedness of the coefficients, `SuperEntire.of_eventually`), which makes the closure properties
(`ε` is a subring of the Tate algebra, closed under twists) immediate.

## Main definitions and results

* `SuperEntire f` — ABP's class `ε`.
* `SuperEntire.entire` — `ε ⊆ T`, `SuperEntire.bounded`.
* `superEntireSubring` — `ε` as a subring of `K⟦t⟧`.
* `SuperEntire.mul`, `.pow`, `.sum`, `.prod`, `.frobTwist`, `.of_eventually`.
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

/-- The Anderson–Brownawell–Papanikolas class `ε`: for every `M` the coefficients of `f` decay at
least as fast as `exp (-M·n)`.  Equivalently: the series `∑ aₙ tⁿ` converges everywhere. -/
def SuperEntire (f : PowerSeries K) : Prop :=
  ∀ M : ℕ, ∃ a : ℤ, ∀ n : ℕ,
    Valued.v (PowerSeries.coeff n f) ≤ WithZero.exp (a - (M : ℤ) * (n : ℤ))

section basic

variable {f g : PowerSeries K}

lemma exp_neg_one_le_one : (WithZero.exp (-1) : ℤᵐ⁰) ≤ 1 := by
  rw [show (1 : ℤᵐ⁰) = WithZero.exp 0 from WithZero.exp_zero.symm]
  exact WithZero.exp_le_exp.mpr (by norm_num)

lemma SuperEntire.zero : SuperEntire (0 : PowerSeries K) := by
  refine fun M => ⟨0, fun n => ?_⟩
  rw [map_zero (PowerSeries.coeff n), map_zero (Valued.v)]
  exact bot_le

lemma SuperEntire.C (c : K) : SuperEntire (PowerSeries.C c) := by
  intro M
  obtain ⟨a, ha⟩ := exists_exp_ge (Valued.v c)
  refine ⟨a, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [PowerSeries.coeff_C, if_pos rfl]
    simpa using ha
  · rw [PowerSeries.coeff_C, if_neg (by omega), map_zero (Valued.v)]
    exact bot_le

lemma SuperEntire.one : SuperEntire (1 : PowerSeries K) := by
  simpa using SuperEntire.C (1 : K)

lemma SuperEntire.add (hf : SuperEntire f) (hg : SuperEntire g) : SuperEntire (f + g) := by
  intro M
  obtain ⟨a, ha⟩ := hf (M + 1)
  obtain ⟨b, hb⟩ := hg (M + 1)
  refine ⟨max a b, fun n => ?_⟩
  rw [map_add]
  refine Valued.v.map_add_le (g := WithZero.exp (max a b - (M : ℤ) * (n : ℤ))) ?_ ?_
  · refine le_trans (ha n) (WithZero.exp_le_exp.mpr ?_)
    have : ((M : ℤ) * (n : ℤ)) ≤ ((M + 1 : ℕ) : ℤ) * (n : ℤ) := by push_cast; nlinarith [Nat.cast_nonneg (α := ℤ) n]
    omega
  · refine le_trans (hb n) (WithZero.exp_le_exp.mpr ?_)
    have : ((M : ℤ) * (n : ℤ)) ≤ ((M + 1 : ℕ) : ℤ) * (n : ℤ) := by push_cast; nlinarith [Nat.cast_nonneg (α := ℤ) n]
    omega

lemma SuperEntire.neg (hf : SuperEntire f) : SuperEntire (-f) := by
  intro M
  obtain ⟨a, ha⟩ := hf M
  refine ⟨a, fun n => ?_⟩
  rw [map_neg, Valuation.map_neg]
  exact ha n

lemma SuperEntire.sub (hf : SuperEntire f) (hg : SuperEntire g) : SuperEntire (f - g) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-- The Frobenius twist preserves `ε`. -/
lemma SuperEntire.frobTwist {p : ℕ} [FrobPow K p] (hf : SuperEntire f) (k : ℕ) :
    SuperEntire (frobTwist (R := K) (p := p) k f) := by
  have hp1 : (1 : ℤ) ≤ ((p ^ k : ℕ) : ℤ) := by
    have := Nat.one_le_pow k p (Nat.pos_of_ne_zero (FrobPow.ne_zero K (q := p)))
    exact_mod_cast this
  intro M
  obtain ⟨a, ha⟩ := hf M
  refine ⟨a * ((p ^ k : ℕ) : ℤ), fun n => ?_⟩
  rw [frobTwist_coeff, map_pow]
  refine le_trans (pow_le_pow_left' (ha n) (p ^ k)) ?_
  rw [expmul]
  apply WithZero.exp_le_exp.mpr
  have hMn : (0 : ℤ) ≤ (M : ℤ) * (n : ℤ) := mul_nonneg (Int.natCast_nonneg M) (Int.natCast_nonneg n)
  have hkey : (M : ℤ) * (n : ℤ) ≤ (M : ℤ) * (n : ℤ) * ((p ^ k : ℕ) : ℤ) :=
    le_mul_of_one_le_right hMn hp1
  nlinarith [hkey]

lemma SuperEntire.sum {ι : Type*} (s : Finset ι) (F' : ι → PowerSeries K)
    (h : ∀ i ∈ s, SuperEntire (F' i)) : SuperEntire (∑ i ∈ s, F' i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using SuperEntire.zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- The key closure: `ε` is closed under products. -/
lemma SuperEntire.mul (hf : SuperEntire f) (hg : SuperEntire g) : SuperEntire (f * g) := by
  intro M
  obtain ⟨a, ha⟩ := hf (M + 1)
  obtain ⟨b, hb⟩ := hg (M + 1)
  refine ⟨a + b, fun n => ?_⟩
  rw [PowerSeries.coeff_mul]
  refine Valuation.map_sum_le (v := Valued.v)
    (g := WithZero.exp (a + b - (M : ℤ) * (n : ℤ))) (fun p hp => ?_)
  rw [map_mul]
  have hpp : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  refine le_trans (mul_le_mul' (ha p.1) (hb p.2)) ?_
  rw [← WithZero.exp_add]
  apply WithZero.exp_le_exp.mpr
  have hpn : ((p.1 : ℤ) + (p.2 : ℤ)) = (n : ℤ) := by exact_mod_cast hpp
  have hkey : (M : ℤ) * (n : ℤ)
      ≤ ((M + 1 : ℕ) : ℤ) * ((p.1 : ℤ) + (p.2 : ℤ)) := by
    have h1 : (M : ℤ) ≤ ((M + 1 : ℕ) : ℤ) := by push_cast; linarith
    have h2 : (0 : ℤ) ≤ ((p.1 : ℤ) + (p.2 : ℤ)) := by positivity
    rw [← hpn]
    exact mul_le_mul_of_nonneg_right h1 h2
  linarith

lemma SuperEntire.pow (hf : SuperEntire f) (k : ℕ) : SuperEntire (f ^ k) := by
  induction k with
  | zero => simpa using SuperEntire.one
  | succ k ih => rw [pow_succ]; exact ih.mul hf

lemma SuperEntire.prod {ι : Type*} (s : Finset ι) (F' : ι → PowerSeries K)
    (h : ∀ i ∈ s, SuperEntire (F' i)) : SuperEntire (∏ i ∈ s, F' i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using SuperEntire.one
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma SuperEntire.natCast (k : ℕ) : SuperEntire ((k : ℕ) : PowerSeries K) := by
  rw [show ((k : ℕ) : PowerSeries K) = PowerSeries.C ((k : K)) from rfl]
  exact SuperEntire.C _

lemma SuperEntire.X : SuperEntire (PowerSeries.X : PowerSeries K) := by
  intro M
  refine ⟨(M : ℤ), fun n => ?_⟩
  by_cases h : n = 1
  · subst h
    rw [PowerSeries.coeff_X, if_pos rfl, map_one]
    rw [show (1 : ℤᵐ⁰) = WithZero.exp 0 from WithZero.exp_zero.symm]
    apply WithZero.exp_le_exp.mpr
    ring_nf
    exact le_refl 0
  · rw [PowerSeries.coeff_X, if_neg h, map_zero (Valued.v)]
    exact bot_le

lemma SuperEntire.monomial (c : K) (k : ℕ) :
    SuperEntire (PowerSeries.C c * PowerSeries.X ^ k) :=
  ((SuperEntire.C c).mul (SuperEntire.pow (SuperEntire.X (K := K)) k))

/-- Boundedness is part of super-entireness. -/
lemma SuperEntire.bounded (hf : SuperEntire f) : SeriesBounded f := by
  obtain ⟨a, ha⟩ := hf 0
  exact ⟨a, fun n => by simpa using ha n⟩

/-- `ε ⊆ T`: a super-entire series is entire (a Tate series). -/
lemma SuperEntire.entire (hf : SuperEntire f) : Entire f := by
  intro N
  obtain ⟨a, ha⟩ := hf (N.natAbs + 1)
  refine Filter.eventually_atTop.mpr ⟨max 1 (a.natAbs + N.natAbs + 2), fun n hn => ?_⟩
  refine lt_of_le_of_lt (ha n) (WithZero.exp_lt_exp.mpr ?_)
  have hbig : (a.natAbs : ℤ) + (N.natAbs : ℤ) + 2 ≤ (n : ℤ) := by
    have h := le_trans (le_max_right 1 (a.natAbs + N.natAbs + 2)) hn
    exact_mod_cast h
  have hcast : (((N.natAbs + 1 : ℕ)) : ℤ) = (N.natAbs : ℤ) + 1 := by push_cast; ring
  rw [hcast]
  have hge : (n : ℤ) ≤ ((N.natAbs : ℤ) + 1) * (n : ℤ) := by
    have h1 : (1 : ℤ) ≤ (N.natAbs : ℤ) + 1 := by omega
    have h2 : (0 : ℤ) ≤ (n : ℤ) := by positivity
    calc (n : ℤ) = 1 * (n : ℤ) := (one_mul _).symm
      _ ≤ ((N.natAbs : ℤ) + 1) * (n : ℤ) := mul_le_mul_of_nonneg_right h1 h2
  have h1 : a ≤ (a.natAbs : ℤ) := Int.le_natAbs
  have h2 : (N : ℤ) ≤ (N.natAbs : ℤ) := Int.le_natAbs
  nlinarith [hbig, hge, h1, h2]

end basic

/-- `ε` as a subring of `K⟦t⟧`. -/
def superEntireSubring (K : Type*) [Field K] [Valued K ℤᵐ⁰] : Subring (PowerSeries K) where
  carrier := {f | SuperEntire f}
  mul_mem' := fun hf hg => hf.mul hg
  one_mem' := SuperEntire.one
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := SuperEntire.zero
  neg_mem' := fun hf => hf.neg

lemma superEntireSubring_le_tateSubring (K : Type*) [Field K] [Valued K ℤᵐ⁰] :
    superEntireSubring K ≤ tateSubring K := fun _ hf => hf.entire.bounded

end ZagierHoffmanPositiveChar
