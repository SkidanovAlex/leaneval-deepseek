import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Polynomial

/-- If `G` is a commutative group with zero, `a ≠ 0`, `q ≠ 0` and `p * a ^ m = q * a ^ n`
with `m ≤ n`, then `a ^ (n - m) = q⁻¹ * p`. -/
private lemma pow_sub_eq_of_mul_pow_eq {G : Type*} [CommGroupWithZero G] {a p q : G} {m n : ℕ}
    (ha : a ≠ 0) (hq : q ≠ 0) (h : p * a ^ m = q * a ^ n) (hmn : m ≤ n) :
    a ^ (n - m) = q⁻¹ * p := by
  have h1 : p * a ^ m = (q * a ^ (n - m)) * a ^ m := by
    calc p * a ^ m = q * a ^ n := h
      _ = q * a ^ ((n - m) + m) := by rw [Nat.sub_add_cancel hmn]
      _ = q * (a ^ (n - m) * a ^ m) := by rw [pow_add]
      _ = (q * a ^ (n - m)) * a ^ m := by rw [mul_assoc]
  have h2 : p = q * a ^ (n - m) := mul_right_cancel₀ (pow_ne_zero m ha) h1
  rw [h2, inv_mul_cancel_left₀ hq]

namespace Commons.RingTheory.Valuation

theorem exists_pow_eq_algebraMap_of_isAlgebraic {k K : Type*} [Field k] [Field K] [Algebra k K]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) {x : K}
    (hx : IsAlgebraic k x) (hx0 : x ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ y : k, y ≠ 0 ∧ v x ^ n = v (algebraMap k K y) := by
  classical
  -- A nonzero polynomial `q` over `k` with `q x = 0` and nonzero constant term.
  obtain ⟨q, hq0, hq⟩ := hx.exists_nonzero_coeff_and_aeval_eq_zero
    (mem_nonZeroDivisors_of_ne_zero hx0)
  have hinj : Function.Injective (algebraMap k K) := (algebraMap k K).injective
  have h0mem : 0 ∈ q.support := by rw [Polynomial.mem_support_iff]; exact hq0
  have hSne : q.support.Nonempty := ⟨0, h0mem⟩
  -- The expansion of `q x = 0` as a sum over the support.
  have hsum : ∑ i ∈ q.support, (algebraMap k K (q.coeff i) * x ^ i) = 0 := by
    rw [← hq, Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  have hxne : v x ≠ 0 := v.ne_zero_iff.mpr hx0
  -- Pick an index attaining the maximal value.
  obtain ⟨j, hjS, hjmax⟩ := Finset.exists_max_image q.support
      (fun i => v (algebraMap k K (q.coeff i) * x ^ i)) hSne
  have hf0 : v (algebraMap k K (q.coeff 0)) ≠ 0 := by
    refine v.ne_zero_iff.mpr ?_
    intro h
    exact hq0 (hinj (by rw [h, map_zero]))
  have hfj_ne : v (algebraMap k K (q.coeff j) * x ^ j) ≠ 0 := by
    have hle := hjmax 0 h0mem
    simp only [pow_zero, mul_one] at hle
    exact ne_of_gt (lt_of_lt_of_le (zero_lt_iff.mpr hf0) hle)
  -- If `j` were the unique maximum, the sum would have the value of that term, contradiction,
  -- since the sum is `0` but the maximal value is nonzero.
  have huniq_false : ¬ (∀ i ∈ q.support, i ≠ j →
      v (algebraMap k K (q.coeff i) * x ^ i) < v (algebraMap k K (q.coeff j) * x ^ j)) := by
    intro huniq
    have hval := Valuation.map_sum_eq_of_lt v hjS (fun i hi => by
      rw [Finset.mem_sdiff] at hi
      exact huniq i hi.1 (by simpa using hi.2))
    rw [hsum, Valuation.map_zero] at hval
    exact hfj_ne hval.symm
  -- Hence there is another index `i ≠ j` attaining the maximal value.
  simp only [not_forall, not_lt] at huniq_false
  obtain ⟨i, hiS, hij, hji⟩ := huniq_false
  have hval_eq : v (algebraMap k K (q.coeff i) * x ^ i)
      = v (algebraMap k K (q.coeff j) * x ^ j) := le_antisymm (hjmax i hiS) hji
  have hfi_ne : v (algebraMap k K (q.coeff i) * x ^ i) ≠ 0 := by rw [hval_eq]; exact hfj_ne
  set Ai : Γ := v (algebraMap k K (q.coeff i)) with hAi
  set Aj : Γ := v (algebraMap k K (q.coeff j)) with hAj
  have hfi_ne' : v (algebraMap k K (q.coeff i)) * (v x) ^ i ≠ 0 := by
    have := hfi_ne
    rwa [Valuation.map_mul, Valuation.map_pow] at this
  have hAi_ne : Ai ≠ 0 := by
    intro h0
    apply hfi_ne'
    rw [← hAi, h0, zero_mul]
  have hAj_ne : Aj ≠ 0 := by
    intro h0
    have := hfj_ne
    rw [Valuation.map_mul, Valuation.map_pow] at this
    apply this
    rw [← hAj, h0, zero_mul]
  have hai_ne : q.coeff i ≠ 0 := by
    intro h
    exact hAi_ne (by simp [hAi, h])
  have haj_ne : q.coeff j ≠ 0 := by
    intro h
    exact hAj_ne (by simp [hAj, h])
  have heq : Ai * (v x) ^ i = Aj * (v x) ^ j := by
    have h' := hval_eq
    rw [Valuation.map_mul, Valuation.map_pow, Valuation.map_mul, Valuation.map_pow] at h'
    rwa [← hAi, ← hAj] at h'
  rcases lt_or_gt_of_ne hij with hij_lt | hji_lt
  · -- `i < j`: then `(v x) ^ (j - i)` is the valuation of `(q.coeff i) / (q.coeff j)`.
    refine ⟨j - i, Nat.sub_pos_of_lt hij_lt, q.coeff i / q.coeff j,
      div_ne_zero hai_ne haj_ne, ?_⟩
    have hkey : (v x) ^ (j - i) = Aj⁻¹ * Ai :=
      pow_sub_eq_of_mul_pow_eq hxne hAj_ne heq hij_lt.le
    have hval_div : v (algebraMap k K (q.coeff i / q.coeff j)) = Ai * Aj⁻¹ := by
      rw [map_div₀, Valuation.map_div, ← hAi, ← hAj, div_eq_mul_inv]
    rw [hkey, hval_div, mul_comm]
  · -- `j < i`: symmetrically, `(v x) ^ (i - j)` is the valuation of `(q.coeff j) / (q.coeff i)`.
    refine ⟨i - j, Nat.sub_pos_of_lt hji_lt, q.coeff j / q.coeff i,
      div_ne_zero haj_ne hai_ne, ?_⟩
    have hkey : (v x) ^ (i - j) = Ai⁻¹ * Aj :=
      pow_sub_eq_of_mul_pow_eq hxne hAi_ne heq.symm hji_lt.le
    have hval_div : v (algebraMap k K (q.coeff j / q.coeff i)) = Aj * Ai⁻¹ := by
      rw [map_div₀, Valuation.map_div, ← hAj, ← hAi, div_eq_mul_inv]
    rw [hkey, hval_div, mul_comm]

end Commons.RingTheory.Valuation