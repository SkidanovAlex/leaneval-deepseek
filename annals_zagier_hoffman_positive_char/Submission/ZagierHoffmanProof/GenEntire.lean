import Submission.ZagierHoffmanProof.EntireTwist
import Submission.Commons.Topology.Algebra.Valued.nonarchimedeanAddGroup
import Submission.Commons.Topology.Algebra.Valued.powerSeries_coeff_mul_le

/-!
# The generic `ε`-chapter: series over an arbitrary valued field

The Anderson–Brownawell–Papanikolas class `ε` (series converging *everywhere*) and the Tate
algebra `T` (series converging on the closed unit disc) are developed in `Entire.lean` and
`SuperEntire.lean` over a field whose valuation has value group `ℤᵐ⁰`.  The Anderson–Brownawell–
Papanikolas criterion, however, is applied over the completion `C_∞` of an algebraic closure of
`K∞`, whose value group is **divisible** (it is `ℚ`), so those results do not apply there.

This file develops the same theory over an arbitrary valued field `Valued K Γ₀`, relative to a
fixed "small" element `γ : Γ₀` with `0 < γ < 1` playing the rôle of `exp (-1)`:

* `GBounded f` — the coefficients of `f` are bounded above in the value group;
* `GEntire f` — the coefficients of `f` tend to `0` (the Tate condition; for `Γ₀ = ℤᵐ⁰` and
  `γ = exp (-1)` this is `Entire` of `Entire.lean`);
* `GSuperEntire γ f` — the coefficients of `f` decay faster than any power of `γ`, i.e. `f`
  converges everywhere (= `SuperEntire` of `SuperEntire.lean` in the case `Γ₀ = ℤᵐ⁰`).

All the closure properties of the `ℤᵐ⁰`-chapter (`add`, `mul`, `pow`, finite sums and products,
Frobenius twists) are proved in this generality, with the same proofs.

## Main results

* `GEntire.mul`, `GSuperEntire.mul` — `ε` and `T` are subrings of `K⟦t⟧`.
* `GSuperEntire.bounded`, `GSuperEntire.entire` — `ε ⊆ T`.
* `GEntire.frobTwist`, `GSuperEntire.frobTwist` — closure under Frobenius twists.
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

/-- In a group with zero, a nonzero element is strictly positive. -/
lemma zero_lt_of_ne_zero {u : Γ₀} (hu : u ≠ 0) : 0 < u :=
  lt_of_le_of_ne (zero_le : (0 : Γ₀) ≤ u) (Ne.symm hu)

/-- The coefficient valuations of a power series are bounded above. -/
def GBounded (f : PowerSeries K) : Prop :=
  ∃ a : Γ₀, ∀ n : ℕ, Valued.v (PowerSeries.coeff n f) ≤ a

/-- A power series is *entire* (Tate) if its coefficients tend to `0` in the value group. -/
def GEntire (f : PowerSeries K) : Prop :=
  ∀ u : Γ₀, u ≠ 0 → ∀ᶠ n in atTop, Valued.v (PowerSeries.coeff n f) < u

/-- `GSuperEntire γ f`: the coefficients of `f` decay faster than any power of `γ`.  For
`γ = exp (-1)` and `Γ₀ = ℤᵐ⁰` this is ABP's "converges everywhere" condition `SuperEntire`. -/
def GSuperEntire (γ : Γ₀) (f : PowerSeries K) : Prop :=
  ∀ M : ℕ, ∃ a : Γ₀, ∀ n : ℕ, Valued.v (PowerSeries.coeff n f) ≤ a * γ ^ (M * n)

lemma GSuperEntire.bounded {γ : Γ₀} {f : PowerSeries K} (hf : GSuperEntire γ f) : GBounded f := by
  obtain ⟨a, ha⟩ := hf 0
  exact ⟨a, fun n => by simpa using ha n⟩

section bounded

variable {f g : PowerSeries K}

lemma GBounded.zero : GBounded (0 : PowerSeries K) :=
  ⟨0, fun n => by rw [map_zero (PowerSeries.coeff n), map_zero (Valued.v)]⟩

lemma GBounded.one : GBounded (1 : PowerSeries K) := by
  refine ⟨1, fun n => ?_⟩
  rw [PowerSeries.coeff_one]
  by_cases h : n = 0
  · rw [if_pos h]
    exact le_of_eq (map_one (Valued.v))
  · rw [if_neg h, map_zero (Valued.v)]
    exact zero_le

lemma GBounded.C (c : K) : GBounded (PowerSeries.C c) := by
  refine ⟨max (Valued.v c) 1, fun n => ?_⟩
  rw [PowerSeries.coeff_C]
  by_cases h : n = 0
  · rw [if_pos h]
    exact le_max_left _ _
  · rw [if_neg h, map_zero (Valued.v)]
    exact zero_le

lemma GBounded.natCast (k : ℕ) : GBounded ((k : ℕ) : PowerSeries K) := by
  rw [show ((k : ℕ) : PowerSeries K) = PowerSeries.C ((k : K)) from rfl]
  exact GBounded.C _

lemma GBounded.X : GBounded (PowerSeries.X : PowerSeries K) := by
  refine ⟨1, fun n => ?_⟩
  rw [PowerSeries.coeff_X]
  by_cases h : n = 1
  · rw [if_pos h]
    exact le_of_eq (map_one (Valued.v))
  · rw [if_neg h, map_zero (Valued.v)]
    exact zero_le

lemma GBounded.add (hf : GBounded f) (hg : GBounded g) : GBounded (f + g) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  refine ⟨max a b, fun n => ?_⟩
  rw [map_add (PowerSeries.coeff n)]
  refine le_trans (Valuation.map_add_le_max' _ _ _) (max_le ?_ ?_)
  · exact le_trans (ha n) (le_max_left _ _)
  · exact le_trans (hb n) (le_max_right _ _)

lemma GBounded.neg (hf : GBounded f) : GBounded (-f) := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨a, fun n => ?_⟩
  rw [map_neg (PowerSeries.coeff n), Valuation.map_neg]
  exact ha n

lemma GBounded.sub (hf : GBounded f) (hg : GBounded g) : GBounded (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

/-- The bounded-coefficient condition is closed under multiplication. -/
lemma GBounded.mul (hf : GBounded f) (hg : GBounded g) : GBounded (f * g) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hg
  exact ⟨a * b, fun n =>
    Commons.Topology.Algebra.Valued.powerSeries_coeff_mul_le (Valued.v) f g ha hb n⟩

lemma GBounded.pow (hf : GBounded f) (k : ℕ) : GBounded (f ^ k) := by
  induction k with
  | zero => simpa using (GBounded.one (K := K))
  | succ k ih => rw [pow_succ]; exact ih.mul hf

lemma GBounded.sum {ι : Type*} (s : Finset ι) (F' : ι → PowerSeries K)
    (h : ∀ i ∈ s, GBounded (F' i)) : GBounded (∑ i ∈ s, F' i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (GBounded.zero (K := K))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma GBounded.prod {ι : Type*} (s : Finset ι) (F' : ι → PowerSeries K)
    (h : ∀ i ∈ s, GBounded (F' i)) : GBounded (∏ i ∈ s, F' i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (GBounded.one (K := K))
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

end bounded

section entire

variable {f g : PowerSeries K}

/-- An entire series has bounded coefficients, with a strictly positive bound. -/
lemma GEntire.bounded_pos (hf : GEntire f) :
    ∃ a : Γ₀, 0 < a ∧ ∀ n : ℕ, Valued.v (PowerSeries.coeff n f) ≤ a := by
  obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp (hf 1 one_ne_zero)
  refine ⟨max 1 ((Finset.range n₀).sup (fun n => Valued.v (PowerSeries.coeff n f))), ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  · intro n
    rcases lt_or_ge n n₀ with hn | hn
    · exact le_trans
        (Finset.le_sup (f := fun n => Valued.v (PowerSeries.coeff n f)) (Finset.mem_range.mpr hn))
        (le_max_right _ _)
    · exact le_trans (le_of_lt (hn₀ n hn)) (le_max_left _ _)

lemma GEntire.bounded (hf : GEntire f) : GBounded f :=
  ⟨_, (hf.bounded_pos).choose_spec.2⟩

lemma GEntire.zero : GEntire (0 : PowerSeries K) := by
  intro u hu
  refine Filter.Eventually.of_forall (fun n => ?_)
  rw [map_zero (PowerSeries.coeff n), map_zero (Valued.v)]
  exact zero_lt_of_ne_zero hu

lemma GEntire.one : GEntire (1 : PowerSeries K) := by
  intro u hu
  refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  rw [PowerSeries.coeff_one, if_neg (by omega : n ≠ 0), map_zero (Valued.v)]
  exact zero_lt_of_ne_zero hu

lemma GEntire.C (c : K) : GEntire (PowerSeries.C c) := by
  intro u hu
  refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
  rw [PowerSeries.coeff_C, if_neg (by omega : n ≠ 0), map_zero (Valued.v)]
  exact zero_lt_of_ne_zero hu

lemma GEntire.natCast (k : ℕ) : GEntire ((k : ℕ) : PowerSeries K) := by
  rw [show ((k : ℕ) : PowerSeries K) = PowerSeries.C ((k : K)) from rfl]
  exact GEntire.C _

lemma GEntire.X : GEntire (PowerSeries.X : PowerSeries K) := by
  intro u hu
  refine Filter.eventually_atTop.mpr ⟨2, fun n hn => ?_⟩
  rw [PowerSeries.coeff_X, if_neg (by omega : n ≠ 1), map_zero (Valued.v)]
  exact zero_lt_of_ne_zero hu

lemma GEntire.add (hf : GEntire f) (hg : GEntire g) : GEntire (f + g) := by
  intro u hu
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hf u hu)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (hg u hu)
  refine Filter.eventually_atTop.mpr ⟨max N₁ N₂, fun n hn => ?_⟩
  rw [map_add (PowerSeries.coeff n)]
  refine lt_of_le_of_lt (Valuation.map_add_le_max' _ _ _) (max_lt ?_ ?_)
  · exact hN₁ n (le_trans (le_max_left _ _) hn)
  · exact hN₂ n (le_trans (le_max_right _ _) hn)

lemma GEntire.neg (hf : GEntire f) : GEntire (-f) := by
  intro u hu
  filter_upwards [hf u hu] with n hn
  rw [map_neg (PowerSeries.coeff n), Valuation.map_neg]
  exact hn

lemma GEntire.sub (hf : GEntire f) (hg : GEntire g) : GEntire (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

/-- The entire (Tate) condition is closed under multiplication. -/
lemma GEntire.mul (hf : GEntire f) (hg : GEntire g) : GEntire (f * g) := by
  obtain ⟨Mf, hMf0, hMf⟩ := hf.bounded_pos
  obtain ⟨Mg, hMg0, hMg⟩ := hg.bounded_pos
  intro u hu
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    (hf (u / Mg) (by simp [hu, hMg0.ne']))
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
    (hg (u / Mf) (by simp [hu, hMf0.ne']))
  refine Filter.eventually_atTop.mpr ⟨N₁ + N₂, fun n hn => ?_⟩
  rw [PowerSeries.coeff_mul]
  refine Valuation.map_sum_lt (Valued.v) hu (fun p hp => ?_)
  have hp' : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [map_mul]
  rcases lt_or_ge p.1 N₁ with h | h
  · have hp2 : N₂ ≤ p.2 := by omega
    have h1 : Valued.v (PowerSeries.coeff p.1 f) * Valued.v (PowerSeries.coeff p.2 g)
        ≤ Mf * Valued.v (PowerSeries.coeff p.2 g) := mul_le_mul_left (hMf p.1) _
    have h2 : Mf * Valued.v (PowerSeries.coeff p.2 g) < Mf * (u / Mf) :=
      mul_lt_mul_of_pos_left (hN₂ p.2 hp2) hMf0
    have h3 : Mf * (u / Mf) = u := by rw [mul_comm, div_mul_cancel₀ u hMf0.ne']
    rw [h3] at h2
    exact lt_of_le_of_lt h1 h2
  · have h1 : Valued.v (PowerSeries.coeff p.1 f) * Valued.v (PowerSeries.coeff p.2 g)
        ≤ Valued.v (PowerSeries.coeff p.1 f) * Mg := mul_le_mul_right (hMg p.2) _
    have h2 : Valued.v (PowerSeries.coeff p.1 f) * Mg < (u / Mg) * Mg :=
      mul_lt_mul_of_pos_right (hN₁ p.1 h) hMg0
    have h3 : (u / Mg) * Mg = u := div_mul_cancel₀ u hMg0.ne'
    rw [h3] at h2
    exact lt_of_le_of_lt h1 h2

lemma GEntire.pow (hf : GEntire f) (k : ℕ) : GEntire (f ^ k) := by
  induction k with
  | zero => simpa using (GEntire.one (K := K))
  | succ k ih => rw [pow_succ]; exact ih.mul hf

lemma GEntire.sum {ι : Type*} (s : Finset ι) (F' : ι → PowerSeries K)
    (h : ∀ i ∈ s, GEntire (F' i)) : GEntire (∑ i ∈ s, F' i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (GEntire.zero (K := K))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma GEntire.prod {ι : Type*} (s : Finset ι) (F' : ι → PowerSeries K)
    (h : ∀ i ∈ s, GEntire (F' i)) : GEntire (∏ i ∈ s, F' i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (GEntire.one (K := K))
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma GEntire.monomial (c : K) (k : ℕ) : GEntire (PowerSeries.C c * PowerSeries.X ^ k) :=
  (GEntire.C c).mul ((GEntire.X (K := K)).pow k)

/-- A series with finite support is entire (its coefficients are eventually `0`). -/
lemma GEntire.mk_of_support (a : ℕ → K) (N₀ : ℕ) (h : ∀ n, N₀ ≤ n → a n = 0) :
    GEntire (PowerSeries.mk a) := by
  intro u hu
  refine Filter.eventually_atTop.mpr ⟨N₀, fun n hn => ?_⟩
  rw [PowerSeries.coeff_mk, h n hn, map_zero (Valued.v)]
  exact zero_lt_of_ne_zero hu

/-- A series whose coefficients vanish in high degree is entire. -/
lemma GEntire.of_support (f : PowerSeries K) (N₀ : ℕ)
    (h : ∀ n, N₀ ≤ n → PowerSeries.coeff n f = 0) : GEntire f := by
  intro u hu
  refine Filter.eventually_atTop.mpr ⟨N₀, fun n hn => ?_⟩
  rw [h n hn, map_zero (Valued.v)]
  exact zero_lt_of_ne_zero hu

/-- Multiplication by a constant preserves entireness. -/
lemma GEntire.C_mul (c : K) (hf : GEntire f) : GEntire (PowerSeries.C c * f) := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [map_zero, zero_mul]
    exact GEntire.zero
  · intro u hu
    have hc0 : 0 < Valued.v c := zero_lt_of_ne_zero (by simpa using hc)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hf (u / Valued.v c) (by simp [hu, hc0.ne']))
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    rw [PowerSeries.coeff_C_mul, map_mul]
    calc Valued.v c * Valued.v (PowerSeries.coeff n f)
        < Valued.v c * (u / Valued.v c) := mul_lt_mul_of_pos_left (hN n hn) hc0
      _ = u := by rw [mul_comm, div_mul_cancel₀ u hc0.ne']

end entire

section superEntire

variable {γ : Γ₀} {f g : PowerSeries K}

lemma GSuperEntire.zero (γ : Γ₀) : GSuperEntire γ (0 : PowerSeries K) := by
  refine fun M => ⟨0, fun n => ?_⟩
  rw [map_zero (PowerSeries.coeff n), map_zero (Valued.v), zero_mul]

lemma GSuperEntire.one (γ : Γ₀) : GSuperEntire γ (1 : PowerSeries K) := by
  refine fun M => ⟨1, fun n => ?_⟩
  rw [PowerSeries.coeff_one]
  by_cases h : n = 0
  · rw [if_pos h, h, mul_zero, pow_zero, mul_one]
    exact le_of_eq (map_one (Valued.v))
  · rw [if_neg h, map_zero (Valued.v)]
    exact zero_le

lemma GSuperEntire.C (γ : Γ₀) (c : K) : GSuperEntire γ (PowerSeries.C c) := by
  refine fun M => ⟨Valued.v c, fun n => ?_⟩
  rw [PowerSeries.coeff_C]
  by_cases h : n = 0
  · rw [if_pos h, h, mul_zero, pow_zero, mul_one]
  · rw [if_neg h, map_zero (Valued.v)]
    exact zero_le

lemma GSuperEntire.natCast (γ : Γ₀) (k : ℕ) : GSuperEntire γ ((k : ℕ) : PowerSeries K) := by
  rw [show ((k : ℕ) : PowerSeries K) = PowerSeries.C ((k : K)) from rfl]
  exact GSuperEntire.C γ _

lemma GSuperEntire.X {γ : Γ₀} (hγ0 : 0 < γ) : GSuperEntire γ (PowerSeries.X : PowerSeries K) := by
  intro M
  refine ⟨(γ ^ M)⁻¹, fun n => ?_⟩
  rw [PowerSeries.coeff_X]
  by_cases h : n = 1
  · rw [if_pos h, h, mul_one, inv_mul_cancel₀ (pow_ne_zero M hγ0.ne')]
    exact le_of_eq (map_one (Valued.v))
  · rw [if_neg h, map_zero (Valued.v)]
    exact zero_le

lemma GSuperEntire.add (hf : GSuperEntire γ f) (hg : GSuperEntire γ g) :
    GSuperEntire γ (f + g) := by
  intro M
  obtain ⟨a, ha⟩ := hf M
  obtain ⟨b, hb⟩ := hg M
  refine ⟨max a b, fun n => ?_⟩
  rw [map_add (PowerSeries.coeff n)]
  refine le_trans (Valuation.map_add_le_max' _ _ _) (max_le ?_ ?_)
  · exact le_trans (ha n) (mul_le_mul_left (le_max_left _ _) _)
  · exact le_trans (hb n) (mul_le_mul_left (le_max_right _ _) _)

lemma GSuperEntire.neg (hf : GSuperEntire γ f) : GSuperEntire γ (-f) := by
  intro M
  obtain ⟨a, ha⟩ := hf M
  refine ⟨a, fun n => ?_⟩
  rw [map_neg (PowerSeries.coeff n), Valuation.map_neg]
  exact ha n

lemma GSuperEntire.sub (hf : GSuperEntire γ f) (hg : GSuperEntire γ g) :
    GSuperEntire γ (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

/-- The key closure: `ε` is closed under products. -/
lemma GSuperEntire.mul (hγ : γ ≤ 1) (hf : GSuperEntire γ f) (hg : GSuperEntire γ g) :
    GSuperEntire γ (f * g) := by
  intro M
  obtain ⟨a, ha⟩ := hf (M + 1)
  obtain ⟨b, hb⟩ := hg (M + 1)
  refine ⟨a * b, fun n => ?_⟩
  rw [PowerSeries.coeff_mul]
  refine Valuation.map_sum_le (v := Valued.v) (g := a * b * γ ^ (M * n)) (fun p hp => ?_)
  rw [map_mul]
  have hpp : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  refine le_trans (mul_le_mul' (ha p.1) (hb p.2)) ?_
  have hpow : γ ^ ((M + 1) * p.1) * γ ^ ((M + 1) * p.2) = γ ^ ((M + 1) * n) := by
    rw [← pow_add, ← hpp, mul_add]
  have hle : γ ^ ((M + 1) * n) ≤ γ ^ (M * n) := by
    refine pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ γ) hγ ?_
    exact Nat.mul_le_mul_right n (Nat.le_succ M)
  calc a * γ ^ ((M + 1) * p.1) * (b * γ ^ ((M + 1) * p.2))
      = a * b * (γ ^ ((M + 1) * p.1) * γ ^ ((M + 1) * p.2)) := by ac_rfl
    _ = a * b * γ ^ ((M + 1) * n) := by rw [hpow]
    _ ≤ a * b * γ ^ (M * n) := mul_le_mul_right hle _

lemma GSuperEntire.pow (hγ : γ ≤ 1) (hf : GSuperEntire γ f) (k : ℕ) :
    GSuperEntire γ (f ^ k) := by
  induction k with
  | zero => simpa using (GSuperEntire.one γ)
  | succ k ih => rw [pow_succ]; exact ih.mul hγ hf

lemma GSuperEntire.sum (_hγ : γ ≤ 1) {ι : Type*} (s : Finset ι) (F' : ι → PowerSeries K)
    (h : ∀ i ∈ s, GSuperEntire γ (F' i)) : GSuperEntire γ (∑ i ∈ s, F' i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (GSuperEntire.zero γ)
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma GSuperEntire.prod (hγ : γ ≤ 1) {ι : Type*} (s : Finset ι) (F' : ι → PowerSeries K)
    (h : ∀ i ∈ s, GSuperEntire γ (F' i)) : GSuperEntire γ (∏ i ∈ s, F' i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (GSuperEntire.one γ)
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact (h a (Finset.mem_insert_self a s)).mul hγ
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- A super-entire series is entire, provided the decay rate `γ` is *cofinal* (which is the case
for `Γ₀ = ℤᵐ⁰`, `γ = exp (-1)`, and for the value group `ℚ` of `C_∞`). -/
lemma GSuperEntire.entire (hγ : γ ≤ 1)
    (hc : ∀ x : Γ₀, x ≠ 0 → ∃ n : ℕ, γ ^ n < x)
    (hf : GSuperEntire γ f) : GEntire f := by
  intro u hu
  obtain ⟨a, ha⟩ := hf 1
  have ha' : ∀ n : ℕ, Valued.v (PowerSeries.coeff n f) ≤ a * γ ^ n := fun n => by simpa using ha n
  rcases eq_or_ne a 0 with ha0 | ha0
  · refine Filter.Eventually.of_forall (fun n => ?_)
    have h0 : Valued.v (PowerSeries.coeff n f) ≤ 0 := by
      simpa [ha0] using ha' n
    exact lt_of_le_of_lt h0 (zero_lt_of_ne_zero hu)
  · have hapos : 0 < a := zero_lt_of_ne_zero ha0
    obtain ⟨n₀, hn₀⟩ := hc (u / a) (by simp [hu, ha0])
    refine Filter.eventually_atTop.mpr ⟨n₀, fun n hn => ?_⟩
    refine lt_of_le_of_lt (ha' n) ?_
    calc a * γ ^ n ≤ a * γ ^ n₀ :=
          mul_le_mul_right (pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ γ) hγ hn) _
      _ < a * (u / a) := mul_lt_mul_of_pos_left hn₀ hapos
      _ = u := by rw [mul_comm, div_mul_cancel₀ u ha0]

end superEntire

section twist

variable {p : ℕ} [FrobPow K p] {γ : Γ₀} {f : PowerSeries K}

lemma GBounded.frobTwist (hf : GBounded f) (k : ℕ) :
    GBounded (frobTwist (R := K) (p := p) k f) := by
  obtain ⟨a, ha⟩ := hf
  refine ⟨a ^ (p ^ k), fun n => ?_⟩
  rw [frobTwist_coeff, map_pow]
  exact pow_le_pow_left' (ha n) (p ^ k)

lemma GEntire.frobTwist (hf : GEntire f) (k : ℕ) :
    GEntire (frobTwist (R := K) (p := p) k f) := by
  have hp1 : p ^ k ≠ 0 := pow_ne_zero k (Nat.pos_of_ne_zero (FrobPow.ne_zero K (q := p))).ne'
  intro u hu
  rcases lt_or_ge (1 : Γ₀) u with h1 | h1
  · obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hf 1 one_ne_zero)
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    rw [frobTwist_coeff, map_pow]
    calc Valued.v (PowerSeries.coeff n f) ^ (p ^ k)
        < 1 ^ (p ^ k) := pow_lt_pow_left₀ (hN n hn) (zero_le : (0 : Γ₀) ≤ _) hp1
      _ = 1 := one_pow _
      _ < u := h1
  · obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hf u hu)
    refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
    rw [frobTwist_coeff, map_pow]
    calc Valued.v (PowerSeries.coeff n f) ^ (p ^ k)
        < u ^ (p ^ k) := pow_lt_pow_left₀ (hN n hn) (zero_le : (0 : Γ₀) ≤ _) hp1
      _ ≤ u ^ 1 := pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ u) h1
          (Nat.one_le_pow k p (Nat.pos_of_ne_zero (FrobPow.ne_zero K (q := p))))
      _ = u := pow_one u

lemma GSuperEntire.frobTwist (hγ : γ ≤ 1) (hf : GSuperEntire γ f) (k : ℕ) :
    GSuperEntire γ (frobTwist (R := K) (p := p) k f) := by
  have hp1 : 1 ≤ p ^ k := Nat.one_le_pow k p (Nat.pos_of_ne_zero (FrobPow.ne_zero K (q := p)))
  intro M
  obtain ⟨a, ha⟩ := hf (M * p ^ k)
  refine ⟨a ^ (p ^ k), fun n => ?_⟩
  rw [frobTwist_coeff, map_pow]
  have h1 : Valued.v (PowerSeries.coeff n f) ^ (p ^ k)
      ≤ (a * γ ^ (M * p ^ k * n)) ^ (p ^ k) := pow_le_pow_left' (ha n) (p ^ k)
  have h2 : (a * γ ^ (M * p ^ k * n)) ^ (p ^ k)
      = a ^ (p ^ k) * γ ^ (M * p ^ k * n * p ^ k) := by
    rw [mul_pow]
    congr 1
    exact (pow_mul γ (M * p ^ k * n) (p ^ k)).symm
  have h3 : γ ^ (M * p ^ k * n * p ^ k) ≤ γ ^ (M * n) := by
    refine pow_le_pow_of_le_one (zero_le : (0 : Γ₀) ≤ γ) hγ ?_
    calc M * n ≤ M * p ^ k * n := by
          exact Nat.mul_le_mul_right n (Nat.le_mul_of_pos_right M (lt_of_lt_of_le Nat.zero_lt_one hp1))
      _ ≤ M * p ^ k * n * p ^ k := by
          simpa using Nat.mul_le_mul_left (M * p ^ k * n) hp1
  refine le_trans h1 ?_
  rw [h2]
  exact mul_le_mul_right h3 _

end twist

end ZagierHoffmanPositiveChar
