import Mathlib
import Submission.NK.NUV2.RouteC.cyclic_cocycle
import Submission.NK.NUV2.RouteC.map_norm_eq_zero

open scoped BigOperators

namespace NK.NUV2.RouteE

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-- `stdC n` at the pair `(i, ofAdd 1)` is `1` exactly when `toAdd i` has value `n - 1`, else `0`
(for `1 < n`). -/
theorem stdC_ofAdd_mul_one {n : ℕ} [NeZero n] (hn : 1 < n) (i : Multiplicative (ZMod n)) :
    NK.NUV2.RouteC.stdC n (i, Multiplicative.ofAdd (1 : ZMod n))
      = if i.toAdd.val = n - 1 then 1 else 0 := by
  haveI : Fact (1 < n) := ⟨hn⟩
  have h1 : (1 : ZMod n).val = 1 := ZMod.val_one n
  have hlt : i.toAdd.val < n := ZMod.val_lt i.toAdd
  simp only [NK.NUV2.RouteC.stdC, toAdd_ofAdd, h1]
  by_cases h : i.toAdd.val = n - 1
  · rw [if_neg (by omega), if_pos h]
  · rw [if_pos (by omega), if_neg h]

/-- **The coefficient sum**: `∑_{i} stdC n (i, ofAdd 1) = 1` in any commutative ring, for
`1 < n`. -/
theorem sum_stdC_ofAdd_mul_one {k : Type} [CommRing k] {n : ℕ} [NeZero n] (hn : 1 < n) :
    (∑ i : Multiplicative (ZMod n),
        ((NK.NUV2.RouteC.stdC n (i, Multiplicative.ofAdd (1 : ZMod n)) : ℕ) : k)) = 1 := by
  classical
  have hterm : ∀ i : Multiplicative (ZMod n),
      ((NK.NUV2.RouteC.stdC n (i, Multiplicative.ofAdd (1 : ZMod n)) : ℕ) : k)
        = if i.toAdd.val = n - 1 then 1 else 0 := by
    intro i
    rw [stdC_ofAdd_mul_one hn i]
    by_cases h : i.toAdd.val = n - 1 <;> simp [h]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_eq_single (Multiplicative.ofAdd ((n - 1 : ℕ) : ZMod n))]
  · have hval : (Multiplicative.ofAdd ((n - 1 : ℕ) : ZMod n)).toAdd.val = n - 1 := by
      rw [toAdd_ofAdd, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [if_pos hval]
  · intro i _ hi
    rw [if_neg]
    exact fun hval => hi (by
      rw [← ofAdd_toAdd i, ← ZMod.natCast_zmod_val i.toAdd, hval])
  · intro h
    exact absurd (Finset.mem_univ _) h


/-- **The downward half of the cyclic periodicity statement in cocycle form.**

If the pointwise product of the standard `2`-cocycle `stdC n` on `Multiplicative (ZMod n)` with
`a : A` is a `2`-coboundary, then `a` lies in the image of the norm map.

The proof sums the identities `d₁₂ b (i, 1) = stdC n (i, 1) • a` over all `i`: the `b (i * 1)`- and
`b i`-terms cancel by the reindexing `i ↦ i * 1` hmm (they are literally equal), leaving
`A.norm.hom (b 1) = (∑_i stdC n (i,1)) • a = a` (the coefficient sum is `1`, since `stdC n (i,1)`
vanishes except at `val i = n - 1`). -/
theorem mem_range_norm_of_d₁₂_eq_stdC_smul {k : Type} [CommRing k] {n : ℕ} [NeZero n]
    (hn : 1 < n) (A : Rep k (Multiplicative (ZMod n))) (a : A)
    (b : Multiplicative (ZMod n) → A)
    (hb : ∀ p : Multiplicative (ZMod n) × Multiplicative (ZMod n),
        (groupCohomology.d₁₂ A).hom b p =
          ((NK.NUV2.RouteC.stdC n p : ℕ) : k) • a) :
    a ∈ LinearMap.range A.norm.hom.toLinearMap := by
  classical
  set q : Multiplicative (ZMod n) := Multiplicative.ofAdd (1 : ZMod n) with hq
  have hL : (∑ i : Multiplicative (ZMod n), (groupCohomology.d₁₂ A).hom b (i, q))
      = A.norm.hom (b q) := by
    have hterm : ∀ i : Multiplicative (ZMod n),
        (groupCohomology.d₁₂ A).hom b (i, q) = A.ρ i (b q) - b (i * q) + b i := by
      intro i
      rw [groupCohomology.d₁₂_hom_apply]
    have hre : (∑ i : Multiplicative (ZMod n), b (i * q)) = ∑ i, b i :=
      Fintype.sum_equiv (Equiv.mulRight q) (fun i => b (i * q)) b (fun i => rfl)
    calc (∑ i : Multiplicative (ZMod n), (groupCohomology.d₁₂ A).hom b (i, q))
        = ∑ i, (A.ρ i (b q) - b (i * q) + b i) := Finset.sum_congr rfl (fun i _ => hterm i)
      _ = (∑ i, A.ρ i (b q)) - (∑ i, b (i * q)) + (∑ i, b i) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (∑ i, A.ρ i (b q)) := by rw [hre, sub_add_cancel]
      _ = A.norm.hom (b q) := (NK.NUV2.RouteC.norm_apply_eq_sum A (b q)).symm
  have hR : (∑ i : Multiplicative (ZMod n),
      ((NK.NUV2.RouteC.stdC n (i, q) : ℕ) : k) • a) = a := by
    rw [← Finset.sum_smul, sum_stdC_ofAdd_mul_one hn, one_smul]
  have hkey : A.norm.hom (b q) = a := by
    rw [← hL, ← hR]
    exact Finset.sum_congr rfl (fun i _ => hb (i, q))
  exact ⟨b q, hkey⟩

end NK.NUV2.RouteE
