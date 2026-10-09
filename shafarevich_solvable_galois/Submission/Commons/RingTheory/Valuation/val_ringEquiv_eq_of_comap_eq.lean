import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.RingTheory.Valuation.valuation_sum_eq_of_unique_max
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Values are invariant under a base-fixing automorphism preserving a valuation subring

Let `L / K` be an algebraic field extension, `A` a valuation subring of `L`, and `σ` a ring
automorphism of `L` that fixes `K` pointwise and preserves `A` (i.e. `A.comap σ = A`).  Then
the canonical valuation attached to `A` is `σ`-invariant: `A.valuation (σ x) = A.valuation x`.

The mathematical content is that `σ` acts on the value group of `A` as an order automorphism
fixing the image of `K`; since `L / K` is algebraic, the value group extension is torsion, so
this action must be the identity.
-/

namespace Commons.RingTheory.Valuation

open Polynomial

set_option maxHeartbeats 800000

/-- **Torsion of the value group over an algebraic extension.**
If `L` is algebraic over `K` and `A` is a valuation subring of `L`, then every value
`A.valuation x` has a positive power lying in the image of `A.valuation ∘ algebraMap K L`.

Proof: `x` satisfies a non-trivial polynomial `∑ aᵢ xⁱ = 0` over `K`.  By the ultrametric
inequality the maximum of `A.valuation (aᵢ xⁱ)` is attained at least twice, say at `i < j`;
comparing the two terms and cancelling `A.valuation x ^ i` shows
`A.valuation x ^ (j - i) = A.valuation (algebraMap K L (aᵢ / aⱼ))`. -/
private theorem exists_pow_valuation_eq_algebraMap {K L : Type*} [Field K] [Field L] [Algebra K L]
    (halg : Algebra.IsAlgebraic K L) (A : ValuationSubring L) (x : L) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : K, A.valuation x ^ n = A.valuation (algebraMap K L c) := by
  by_cases hx : x = 0
  · exact ⟨1, Nat.one_pos, 0, by simp [hx]⟩
  obtain ⟨p, hp, hp0⟩ := halg.isAlgebraic x
  have hval_eq_zero : ∀ y : L, A.valuation y = 0 ↔ y = 0 := by
    intro y
    rw [← map_zero A.valuation, A.valuation_eq_iff y 0]
    simp only [mul_zero, exists_const]
    exact ⟨Eq.symm, Eq.symm⟩
  have hinj : Function.Injective (algebraMap K L) := (algebraMap K L).injective
  have hxpow : ∀ i : ℕ, x ^ i ≠ 0 := fun i => pow_ne_zero i hx
  let f : ℕ → L := fun i => algebraMap K L (p.coeff i) * x ^ i
  have hsum : ∑ i ∈ p.support, f i = 0 := by
    show ∑ i ∈ p.support, algebraMap K L (p.coeff i) * x ^ i = 0
    rw [← hp0, aeval_def, eval₂_eq_sum]
    rfl
  have hf_ne : ∀ i ∈ p.support, f i ≠ 0 := by
    intro i hi
    show algebraMap K L (p.coeff i) * x ^ i ≠ 0
    exact mul_ne_zero (by simpa using hinj.ne (by rwa [Polynomial.mem_support_iff] at hi)) (hxpow i)
  have hvf_ne : ∀ i ∈ p.support, A.valuation (f i) ≠ 0 := by
    intro i hi h
    exact hf_ne i hi ((hval_eq_zero (f i)).mp h)
  have hSne : p.support.Nonempty := by rwa [Polynomial.support_nonempty]
  obtain ⟨j, hjS, hjmax⟩ := Finset.exists_max_image p.support (fun i => A.valuation (f i)) hSne
  have hexists : ∃ k ∈ p.support, k ≠ j ∧ A.valuation (f k) = A.valuation (f j) := by
    by_contra hcon
    have hne : ∀ i ∈ p.support, i ≠ j → A.valuation (f i) ≠ A.valuation (f j) := by
      intro i hi hij heq
      exact hcon ⟨i, hi, hij, heq⟩
    have huniq : ∀ i ∈ p.support, i ≠ j → A.valuation (f i) < A.valuation (f j) :=
      fun i hi hij => lt_of_le_of_ne (hjmax i hi) (hne i hi hij)
    have hh := Commons.RingTheory.Valuation.valuation_sum_eq_of_unique_max A.valuation
      p.support f hjS huniq
    rw [hsum, map_zero] at hh
    exact hvf_ne j hjS hh.symm
  obtain ⟨k, hkS, hkj, hkval⟩ := hexists
  have key : ∀ i j : ℕ, i ∈ p.support → j ∈ p.support → i < j →
      A.valuation (f i) = A.valuation (f j) →
      A.valuation x ^ (j - i) = A.valuation (algebraMap K L (p.coeff i / p.coeff j)) := by
    intro i j hi hj hij hval
    have hj_ne : p.coeff j ≠ 0 := by rwa [Polynomial.mem_support_iff] at hj
    have hXi : A.valuation x ≠ 0 := fun h => hx ((hval_eq_zero x).mp h)
    have hvaj : A.valuation (algebraMap K L (p.coeff j)) ≠ 0 := fun h =>
      (by simpa using hinj.ne hj_ne : algebraMap K L (p.coeff j) ≠ 0)
        ((hval_eq_zero (algebraMap K L (p.coeff j))).mp h)
    have hfi : f i = algebraMap K L (p.coeff i) * x ^ i := rfl
    have hfj : f j = algebraMap K L (p.coeff j) * x ^ j := rfl
    rw [hfi, hfj, map_mul, map_pow, map_mul, map_pow] at hval
    have h1 : A.valuation (algebraMap K L (p.coeff i)) * A.valuation x ^ i
        = (A.valuation (algebraMap K L (p.coeff j)) * A.valuation x ^ (j - i))
            * A.valuation x ^ i := by
      have hpow : A.valuation x ^ j = A.valuation x ^ (j - i) * A.valuation x ^ i := by
        rw [← pow_add]; congr 1; omega
      rw [hval, hpow, mul_assoc]
    have h2 : A.valuation (algebraMap K L (p.coeff i))
        = A.valuation (algebraMap K L (p.coeff j)) * A.valuation x ^ (j - i) :=
      mul_right_cancel₀ (pow_ne_zero i hXi) h1
    have h3 : A.valuation x ^ (j - i)
        = A.valuation (algebraMap K L (p.coeff i)) / A.valuation (algebraMap K L (p.coeff j)) := by
      rw [div_eq_mul_inv]
      rw [h2]
      rw [mul_assoc,
        mul_comm (A.valuation x ^ (j - i)) (A.valuation (algebraMap K L (p.coeff j)))⁻¹,
        ← mul_assoc, mul_inv_cancel₀ hvaj, one_mul]
    rw [h3, map_div₀, Valuation.map_div]
  rcases lt_or_gt_of_ne hkj with hlt | hlt
  · exact ⟨j - k, Nat.sub_pos_of_lt hlt, p.coeff k / p.coeff j, key k j hkS hjS hlt hkval⟩
  · exact ⟨k - j, Nat.sub_pos_of_lt hlt, p.coeff j / p.coeff k, key j k hjS hkS hlt hkval.symm⟩

/-- Let `L / K` be an algebraic extension, `A` a valuation subring of `L`, and `σ` a ring
automorphism of `L` fixing `K` pointwise with `A.comap σ = A`.  Then the valuation of `A`
is invariant under `σ`. -/
theorem val_ringEquiv_eq_of_comap_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    (halg : Algebra.IsAlgebraic K L) (A : ValuationSubring L) (σ : L ≃+* L)
    (hK : ∀ x : K, σ (algebraMap K L x) = algebraMap K L x)
    (hA : A.comap (σ : L →+* L) = A) : ∀ x : L, A.valuation (σ x) = A.valuation x := by
  have hmem : ∀ y : L, σ y ∈ A ↔ y ∈ A := by
    intro y
    have h := congrArg (fun (B : ValuationSubring L) => y ∈ B) hA
    simpa [ValuationSubring.mem_comap] using h
  have hval_eq_zero : ∀ y : L, A.valuation y = 0 ↔ y = 0 := by
    intro y
    rw [← map_zero A.valuation, A.valuation_eq_iff y 0]
    simp only [mul_zero, exists_const]
    exact ⟨Eq.symm, Eq.symm⟩
  intro x
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero]
  obtain ⟨n, hn, c, hc⟩ := exists_pow_valuation_eq_algebraMap halg A x
  have hX : A.valuation x ≠ 0 := fun h => hx ((hval_eq_zero x).mp h)
  have hc0 : c ≠ 0 := by
    intro hc0
    rw [hc0] at hc
    simp only [map_zero] at hc
    rw [pow_eq_zero_iff hn.ne'] at hc
    exact hX hc
  have hcval : A.valuation (algebraMap K L c) ≠ 0 := by
    intro h
    exact hc0 ((algebraMap K L).injective (by simpa using ((hval_eq_zero (algebraMap K L c)).mp h)))
  set z : L := x ^ n / algebraMap K L c with hz
  have hzv : A.valuation z = 1 := by
    rw [hz, Valuation.map_div, map_pow, hc, div_self hcval]
  have hzA : z ∈ A := by
    rw [← ValuationSubring.valuation_le_one_iff, hzv]
  have hzinvA : z⁻¹ ∈ A := by
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hzv, inv_one]
  have hszA : σ z ∈ A := (hmem z).mpr hzA
  have hszinvA : (σ z)⁻¹ ∈ A := by
    have h1 : (σ z)⁻¹ = σ (z⁻¹) := (map_inv₀ σ z).symm
    rw [h1]
    exact (hmem (z⁻¹)).mpr hzinvA
  have hz_ne : z ≠ 0 := by
    rw [hz]
    refine div_ne_zero (pow_ne_zero n hx) ?_
    simpa using (algebraMap K L).injective.ne hc0
  have hsz_ne : σ z ≠ 0 := by
    simpa using σ.injective.ne hz_ne
  have hvsz : A.valuation (σ z) = 1 := by
    have h1 : A.valuation (σ z) ≤ 1 := (ValuationSubring.valuation_le_one_iff A (σ z)).mpr hszA
    have h2 : (A.valuation (σ z))⁻¹ ≤ 1 := by
      rw [← map_inv₀]
      exact (ValuationSubring.valuation_le_one_iff A ((σ z)⁻¹)).mpr hszinvA
    have hne : A.valuation (σ z) ≠ 0 := fun h => hsz_ne ((hval_eq_zero (σ z)).mp h)
    rw [inv_le_one_iff₀] at h2
    rcases h2 with h2 | h2
    · exact absurd (le_antisymm h2 zero_le) hne
    · exact le_antisymm h1 h2
  have hsz_eq : σ z = σ x ^ n / algebraMap K L c := by
    rw [hz, map_div₀, map_pow, hK c]
  have hfinal : A.valuation (σ x) ^ n = A.valuation x ^ n := by
    have h : A.valuation (σ z) = A.valuation (σ x) ^ n / A.valuation (algebraMap K L c) := by
      rw [hsz_eq, Valuation.map_div, map_pow]
    have hd := (div_eq_one_iff_eq hcval).mp (h ▸ hvsz)
    rw [hd, ← hc]
  exact (pow_left_inj₀ (zero_le : (0 : A.ValueGroup) ≤ A.valuation (σ x))
    (zero_le : (0 : A.ValueGroup) ≤ A.valuation x) hn.ne').mp hfinal

end Commons.RingTheory.Valuation