import Mathlib.RingTheory.PowerSeries.Basic
import Submission.ZagierHoffmanProof.CompletionInstances
import Submission.Commons.Topology.Algebra.Valued.powerSeries_bounded_mul
import Submission.Commons.Topology.Algebra.Valued.powerSeries_tendsto_zero_bounded

/-!
# Entire (Tate) power series over a `ℤᵐ⁰`-valued field

For a field `K` with a `ℤᵐ⁰`-valued valuation `Valued.v`, a power series `f = ∑ aₙ zⁿ` is
*entire* (Tate, in the sense of the ring `E` of Anderson–Brownawell–Papanikolas) if its
coefficients tend to zero:

  `Entire f : ∀ N : ℤ, ∀ᶠ n in atTop, v (coeff n f) < exp (-N)`.

The main result of this file is that the entire series form a **subring** of `K⟦z⟧`.
(Multiplication is the subtle point: it uses that the coefficient valuations of an entire
series are bounded above, which is `Entire.bounded`.)  This is the ring `E` of the
Anderson–Brownawell–Papanikolas criterion, the substrate for the Tate algebra / dual
`t`-motive chapter of Ngo Dac's paper.

## Main definitions

* `SeriesBounded f` — the coefficient valuations of `f` are bounded above.
* `Entire f` — the coefficients of `f` tend to zero.
* `entireSubring K` — the subring of entire series.

## Main results

* `Entire.bounded` — entire series have bounded coefficients.
* `Entire.add`, `Entire.mul`, `Entire.neg`, `Entire.sum`, `Entire.prod`, `Entire.pow`, …
-/

set_option autoImplicit false

open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

/-- The coefficient valuations of a power series are bounded above. -/
def SeriesBounded (f : PowerSeries K) : Prop :=
  ∃ M : ℤ, ∀ n : ℕ, Valued.v (PowerSeries.coeff n f) ≤ WithZero.exp M

/-- A power series is *entire* (satisfies the Tate condition) if its coefficients tend
to zero in the topology of the value group. -/
def Entire (f : PowerSeries K) : Prop :=
  ∀ N : ℤ, ∀ᶠ n in atTop, Valued.v (PowerSeries.coeff n f) < WithZero.exp (-N)

section basic

variable {f g : PowerSeries K}

/-- Every element of the value group is bounded above by `exp M` for some `M : ℤ`. -/
lemma exists_exp_ge (x : ℤᵐ⁰) : ∃ M : ℤ, x ≤ WithZero.exp M := by
  by_cases h : x = 0
  · exact ⟨0, by rw [h]; exact bot_le⟩
  · obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp h
    refine ⟨Multiplicative.toAdd a, ?_⟩
    rw [← ha]
    exact le_of_eq (by rfl)

/-- An entire series has bounded coefficients (via the commons lemma
`Commons.Topology.Algebra.Valued.powerSeries_tendsto_zero_bounded`). -/
lemma Entire.bounded (hf : Entire f) : SeriesBounded f :=
  Commons.Topology.Algebra.Valued.powerSeries_tendsto_zero_bounded K f hf

lemma Entire.zero : Entire (0 : PowerSeries K) := by
  intro N
  refine Filter.Eventually.of_forall (fun n => ?_)
  rw [map_zero, map_zero]
  exact lt_of_le_of_ne bot_le (Ne.symm (WithZero.exp_ne_zero))

lemma Entire.one : Entire (1 : PowerSeries K) := by
  intro N
  refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  rw [PowerSeries.coeff_one, if_neg (by omega : n ≠ 0), map_zero]
  exact lt_of_le_of_ne bot_le (Ne.symm (WithZero.exp_ne_zero))

lemma Entire.C (c : K) : Entire (PowerSeries.C c) := by
  intro N
  refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  rw [PowerSeries.coeff_C, if_neg (by omega : n ≠ 0), map_zero]
  exact lt_of_le_of_ne bot_le (Ne.symm (WithZero.exp_ne_zero))

lemma Entire.add (hf : Entire f) (hg : Entire g) : Entire (f + g) := by
  intro N
  filter_upwards [hf (N + 1), hg (N + 1)] with n hn1 hn2
  rw [map_add]
  refine lt_of_le_of_lt (Valuation.map_add_le_max' _ _ _) ?_
  refine lt_of_le_of_lt (max_le (le_of_lt hn1) (le_of_lt hn2)) ?_
  exact WithZero.exp_lt_exp.mpr (by omega)

lemma Entire.neg (hf : Entire f) : Entire (-f) := by
  intro N
  filter_upwards [hf N] with n hn
  have hneg : PowerSeries.coeff n (-f) = -(PowerSeries.coeff n f) := map_neg _ _
  rw [hneg, Valuation.map_neg]
  exact hn

lemma Entire.sub (hf : Entire f) (hg : Entire g) : Entire (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

lemma Entire.mul (hf : Entire f) (hg : Entire g) : Entire (f * g) := by
  obtain ⟨Mf, hMf⟩ := hf.bounded
  obtain ⟨Mg, hMg⟩ := hg.bounded
  intro N
  obtain ⟨N₁, hN₁⟩ :=
    Filter.eventually_atTop.mp (hf (N + Mg + 1))
  obtain ⟨N₂, hN₂⟩ :=
    Filter.eventually_atTop.mp (hg (N + Mf + 1))
  refine Filter.eventually_atTop.mpr ⟨N₁ + N₂, fun n hn => ?_⟩
  rw [PowerSeries.coeff_mul]
  refine Valuation.map_sum_lt (Valued.v) (WithZero.exp_ne_zero) (fun p hp => ?_)
  have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [map_mul]
  rcases lt_or_ge p.1 N₁ with h | h
  · have hp2 : N₂ ≤ p.2 := by omega
    calc Valued.v (PowerSeries.coeff p.1 f) * Valued.v (PowerSeries.coeff p.2 g)
        ≤ WithZero.exp Mf * WithZero.exp (-(N + Mf + 1)) :=
          mul_le_mul' (hMf p.1) (le_of_lt (hN₂ p.2 hp2))
      _ = WithZero.exp (-(N + 1)) := by
          rw [← WithZero.exp_add]; congr 1; ring
      _ < WithZero.exp (-N) := WithZero.exp_lt_exp.mpr (by omega)
  · calc Valued.v (PowerSeries.coeff p.1 f) * Valued.v (PowerSeries.coeff p.2 g)
        ≤ WithZero.exp (-(N + Mg + 1)) * WithZero.exp Mg :=
          mul_le_mul' (le_of_lt (hN₁ p.1 h)) (hMg p.2)
      _ = WithZero.exp (-(N + 1)) := by
          rw [← WithZero.exp_add]; congr 1; ring
      _ < WithZero.exp (-N) := WithZero.exp_lt_exp.mpr (by omega)


lemma Entire.C_mul (c : K) (hf : Entire f) : Entire (PowerSeries.C c * f) := by
  obtain ⟨M, hM⟩ := exists_exp_ge (Valued.v c)
  intro N
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hf (N + M + 1))
  refine Filter.eventually_atTop.mpr ⟨N₀, fun n hn => ?_⟩
  rw [PowerSeries.coeff_C_mul, map_mul]
  calc Valued.v c * Valued.v (PowerSeries.coeff n f)
      ≤ WithZero.exp M * WithZero.exp (-(N + M + 1)) :=
        mul_le_mul' hM (le_of_lt (hN₀ n hn))
    _ = WithZero.exp (-(N + 1)) := by rw [← WithZero.exp_add]; congr 1; ring
    _ < WithZero.exp (-N) := WithZero.exp_lt_exp.mpr (by omega)

lemma Entire.pow (hf : Entire f) (k : ℕ) : Entire (f ^ k) := by
  induction k with
  | zero => simpa using (Entire.one (K := K))
  | succ m ih => rw [pow_succ]; exact ih.mul hf

lemma Entire.natCast (k : ℕ) : Entire ((k : ℕ) : PowerSeries K) := by
  have h : ((k : ℕ) : PowerSeries K) = PowerSeries.C ((k : ℕ) : K) := map_natCast PowerSeries.C k
  rw [h]
  exact Entire.C ((k : ℕ) : K)

lemma Entire.intCast (k : ℤ) : Entire ((k : ℤ) : PowerSeries K) := by
  cases k with
  | ofNat n => simpa using Entire.natCast (K := K) n
  | negSucc n => rw [Int.negSucc_eq]; exact (Entire.natCast (K := K) (n+1)).neg

lemma Entire.sum {ι : Type*} (s : Finset ι) (F' : ι → PowerSeries K)
    (h : ∀ i ∈ s, Entire (F' i)) : Entire (∑ i ∈ s, F' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Entire.zero (K := K))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma Entire.prod {ι : Type*} (s : Finset ι) (F' : ι → PowerSeries K)
    (h : ∀ i ∈ s, Entire (F' i)) : Entire (∏ i ∈ s, F' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (Entire.one (K := K))
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma Entire.X : Entire (PowerSeries.X : PowerSeries K) := by
  intro N
  refine Filter.eventually_atTop.mpr ⟨2, fun n hn => ?_⟩
  rw [PowerSeries.coeff_X, if_neg (by omega : n ≠ 1), map_zero]
  exact lt_of_le_of_ne bot_le (Ne.symm (WithZero.exp_ne_zero))

lemma Entire.X_pow (k : ℕ) : Entire ((PowerSeries.X : PowerSeries K) ^ k) :=
  Entire.X.pow k

lemma Entire.monomial (c : K) (k : ℕ) : Entire (PowerSeries.C c * PowerSeries.X ^ k) :=
  (Entire.C c).mul (Entire.X_pow k)

lemma Entire.mk_of_support (a : ℕ → K) (N₀ : ℕ)
    (h : ∀ n, N₀ ≤ n → a n = 0) : Entire (PowerSeries.mk a) := by
  intro N
  refine Filter.eventually_atTop.mpr ⟨N₀, fun n hn => ?_⟩
  rw [PowerSeries.coeff_mk, h n hn, map_zero]
  exact lt_of_le_of_ne bot_le (Ne.symm (WithZero.exp_ne_zero))

lemma Entire.coeff_eq_zero_of_support (a : ℕ → K) (N₀ : ℕ)
    (h : ∀ n, N₀ ≤ n → a n = 0) : ∀ n, N₀ ≤ n → PowerSeries.coeff n (PowerSeries.mk a) = 0 := by
  intro n hn
  rw [PowerSeries.coeff_mk, h n hn]

/-- To prove the entire condition it suffices to check the natural levels. -/
lemma Entire.of_nat {f : PowerSeries K}
    (h : ∀ N : ℕ, ∀ᶠ n in atTop, Valued.v (PowerSeries.coeff n f) < WithZero.exp (-(N : ℤ))) :
    Entire f := by
  intro N
  rcases lt_or_ge N 1 with hN | hN
  · filter_upwards [h 1] with n hn
    exact lt_trans hn (WithZero.exp_lt_exp.mpr (by omega))
  · have hnat : ((N.toNat : ℕ) : ℤ) = N := Int.toNat_of_nonneg (by omega : 0 ≤ N)
    have hcast : -((N.toNat : ℕ) : ℤ) = -N := by rw [hnat]
    filter_upwards [h N.toNat] with n hn
    rwa [hcast] at hn

end basic

section bounded

/-- The bounded-coefficient (`Tate algebra`) condition is closed under addition. -/
lemma SeriesBounded.add {f g : PowerSeries K} (hf : SeriesBounded f) (hg : SeriesBounded g) :
    SeriesBounded (f + g) := by
  obtain ⟨Mf, hMf⟩ := hf
  obtain ⟨Mg, hMg⟩ := hg
  refine ⟨max Mf Mg, fun n => ?_⟩
  rw [map_add (PowerSeries.coeff n)]
  refine le_trans (Valuation.map_add_le_max' _ _ _) (max_le ?_ ?_)
  · exact le_trans (hMf n) (WithZero.exp_le_exp.mpr (le_max_left _ _))
  · exact le_trans (hMg n) (WithZero.exp_le_exp.mpr (le_max_right _ _))

lemma SeriesBounded.neg {f : PowerSeries K} (hf : SeriesBounded f) : SeriesBounded (-f) := by
  obtain ⟨M, hM⟩ := hf
  refine ⟨M, fun n => ?_⟩
  have hneg : PowerSeries.coeff n (-f) = -(PowerSeries.coeff n f) := map_neg _ _
  rw [hneg, Valuation.map_neg]
  exact hM n

lemma SeriesBounded.sub {f g : PowerSeries K} (hf : SeriesBounded f) (hg : SeriesBounded g) :
    SeriesBounded (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

/-- The bounded-coefficient condition is closed under multiplication. -/
lemma SeriesBounded.mul {f g : PowerSeries K} (hf : SeriesBounded f) (hg : SeriesBounded g) :
    SeriesBounded (f * g) := by
  obtain ⟨Mf, hMf⟩ := hf
  obtain ⟨Mg, hMg⟩ := hg
  exact ⟨Mf + Mg,
    Commons.Topology.Algebra.Valued.powerSeries_bounded_mul K f g Mf Mg hMf hMg⟩

lemma SeriesBounded.zero : SeriesBounded (0 : PowerSeries K) :=
  ⟨0, fun n => by rw [map_zero, map_zero]; exact bot_le⟩

lemma SeriesBounded.one : SeriesBounded (1 : PowerSeries K) := by
  refine ⟨0, fun n => ?_⟩
  rw [PowerSeries.coeff_one]
  by_cases h : n = 0
  · rw [if_pos h, map_one, WithZero.exp_zero]
  · rw [if_neg h, map_zero]; exact bot_le

lemma SeriesBounded.C (c : K) : SeriesBounded (PowerSeries.C c) := by
  obtain ⟨M, hM⟩ := exists_exp_ge (Valued.v c)
  refine ⟨M, fun n => ?_⟩
  rw [PowerSeries.coeff_C]
  by_cases h : n = 0
  · rw [if_pos h]; exact hM
  · rw [if_neg h, map_zero]; exact bot_le

lemma SeriesBounded.C_mul (c : K) {f : PowerSeries K} (hf : SeriesBounded f) :
    SeriesBounded (PowerSeries.C c * f) :=
  (SeriesBounded.C c).mul hf

lemma SeriesBounded.natCast (k : ℕ) : SeriesBounded ((k : ℕ) : PowerSeries K) := by
  have h : ((k : ℕ) : PowerSeries K) = PowerSeries.C ((k : ℕ) : K) := map_natCast PowerSeries.C k
  rw [h]
  exact SeriesBounded.C ((k : ℕ) : K)

lemma SeriesBounded.pow {f : PowerSeries K} (hf : SeriesBounded f) (k : ℕ) :
    SeriesBounded (f ^ k) := by
  induction k with
  | zero => simpa using (SeriesBounded.one (K := K))
  | succ m ih => rw [pow_succ]; exact ih.mul hf

lemma SeriesBounded.sum {ι : Type*} (s : Finset ι) (F' : ι → PowerSeries K)
    (h : ∀ i ∈ s, SeriesBounded (F' i)) : SeriesBounded (∑ i ∈ s, F' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (SeriesBounded.zero (K := K))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma SeriesBounded.prod {ι : Type*} (s : Finset ι) (F' : ι → PowerSeries K)
    (h : ∀ i ∈ s, SeriesBounded (F' i)) : SeriesBounded (∏ i ∈ s, F' i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (SeriesBounded.one (K := K))
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end bounded

/-- The power series with bounded coefficients (the Tate algebra `T`) form a subring. -/
def tateSubring (K : Type*) [Field K] [Valued K ℤᵐ⁰] : Subring (PowerSeries K) where
  carrier := {f | SeriesBounded f}
  mul_mem' := fun hf hg => hf.mul hg
  one_mem' := SeriesBounded.one
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := SeriesBounded.zero
  neg_mem' := fun hf => hf.neg

/-- The Tate algebra of power series with bounded coefficients (carrier of `tateSubring`). -/
abbrev TateAlg (K : Type*) [Field K] [Valued K ℤᵐ⁰] := ↥(tateSubring K)

/-- Every entire series is a Tate (bounded coefficient) series. -/
lemma Entire.toTate {f : PowerSeries K} (hf : Entire f) : SeriesBounded f := hf.bounded


namespace TateAlg

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

@[simp] lemma coe_zero : ((0 : TateAlg K) : PowerSeries K) = 0 := rfl
@[simp] lemma coe_one : ((1 : TateAlg K) : PowerSeries K) = 1 := rfl
@[simp] lemma coe_add (x y : TateAlg K) :
    ((x + y : TateAlg K) : PowerSeries K) = (x : PowerSeries K) + (y : PowerSeries K) := rfl
@[simp] lemma coe_mul (x y : TateAlg K) :
    ((x * y : TateAlg K) : PowerSeries K) = (x : PowerSeries K) * (y : PowerSeries K) := rfl
@[simp] lemma coe_neg (x : TateAlg K) :
    ((-x : TateAlg K) : PowerSeries K) = -(x : PowerSeries K) := rfl
@[simp] lemma coe_sub (x y : TateAlg K) :
    ((x - y : TateAlg K) : PowerSeries K) = (x : PowerSeries K) - (y : PowerSeries K) := rfl
@[simp] lemma coe_pow (x : TateAlg K) (n : ℕ) :
    ((x ^ n : TateAlg K) : PowerSeries K) = (x : PowerSeries K) ^ n := rfl

end TateAlg


/-- The entire power series over `K` form a subring of `K⟦z⟧`. -/
def entireSubring (K : Type*) [Field K] [Valued K ℤᵐ⁰] : Subring (PowerSeries K) where
  carrier := {f | Entire f}
  mul_mem' := fun hf hg => hf.mul hg
  one_mem' := Entire.one
  add_mem' := fun hf hg => hf.add hg
  zero_mem' := Entire.zero
  neg_mem' := fun hf => hf.neg

/-- The ring of entire power series (carrier of `entireSubring`). -/
abbrev EntireRing (K : Type*) [Field K] [Valued K ℤᵐ⁰] := ↥(entireSubring K)

/-- The entire series form a subring of the Tate algebra. -/
lemma entireSubring_le_tateSubring (K : Type*) [Field K] [Valued K ℤᵐ⁰] :
    entireSubring K ≤ tateSubring K := fun _ hf => hf.bounded

namespace EntireRing

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰]

@[simp] lemma coe_zero : ((0 : EntireRing K) : PowerSeries K) = 0 := rfl
@[simp] lemma coe_one : ((1 : EntireRing K) : PowerSeries K) = 1 := rfl
@[simp] lemma coe_add (x y : EntireRing K) :
    ((x + y : EntireRing K) : PowerSeries K) = (x : PowerSeries K) + (y : PowerSeries K) := rfl
@[simp] lemma coe_mul (x y : EntireRing K) :
    ((x * y : EntireRing K) : PowerSeries K) = (x : PowerSeries K) * (y : PowerSeries K) := rfl
@[simp] lemma coe_neg (x : EntireRing K) :
    ((-x : EntireRing K) : PowerSeries K) = -(x : PowerSeries K) := rfl
@[simp] lemma coe_sub (x y : EntireRing K) :
    ((x - y : EntireRing K) : PowerSeries K) = (x : PowerSeries K) - (y : PowerSeries K) := rfl
@[simp] lemma coe_pow (x : EntireRing K) (n : ℕ) :
    ((x ^ n : EntireRing K) : PowerSeries K) = (x : PowerSeries K) ^ n := rfl

end EntireRing

end ZagierHoffmanPositiveChar
