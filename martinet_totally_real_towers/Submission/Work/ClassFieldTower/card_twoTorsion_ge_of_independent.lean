import Mathlib

namespace Work.ClassFieldTower

/-- **Elements of order `2` with all nonempty sub-products non-trivial give at least `2 ^ n`
elements of order `2`.**

Hints: `(Fin n → ZMod 2)` has `2 ^ n` elements.  Define the map
`ν : Multiplicative (Fin n → ZMod 2) →* A`, `v ↦ ∏ i, x i ^ (v.toAdd i).val`; it is a
monomorphism: `map_mul'` follows from `ZMod.val_add` and `x ^ 2 = 1` (an exponent may be reduced
modulo `2`: `x ^ (m % 2) = x ^ m`), and injectivity from the hypothesis `hne` (if `ν v = 1` then
the product over the nonempty support of `v` is `1`).  As every `ν v` satisfies `(ν v) ^ 2 = 1`,
`ν` maps into `{y : A // y ^ 2 = 1}` and injectivity gives
`2 ^ n = Nat.card (Fin n → ZMod 2) ≤ Nat.card {y : A // y ^ 2 = 1}`. -/
theorem card_twoTorsion_ge_of_independent (A : Type*) [CommGroup A] [Fintype A] (n : ℕ)
    (x : Fin n → A) (hx : ∀ i, x i ^ 2 = 1)
    (hne : ∀ T : Finset (Fin n), T.Nonempty → (∏ i ∈ T, x i) ≠ 1) :
    2 ^ n ≤ Nat.card {y : A // y ^ 2 = 1} := by
  classical
  -- Every sub-product of the `x i` is `2`-torsion.
  have htwo : ∀ T : Finset (Fin n), (∏ i ∈ T, x i) ^ 2 = 1 := by
    intro T
    rw [← Finset.prod_pow]
    simp [hx]
  -- The injection `T ↦ ∏_{i ∈ T} x i`, from the `2 ^ n` subsets into the `2`-torsion.
  let φ : Finset (Fin n) → {y : A // y ^ 2 = 1} := fun T => ⟨∏ i ∈ T, x i, htwo T⟩
  have hinj : Function.Injective φ := by
    intro T U h
    have hval : ∏ i ∈ T, x i = ∏ i ∈ U, x i := congrArg Subtype.val h
    -- Cancel the common part `T ∩ U` to isolate the symmetric difference.
    have hTU : ∏ i ∈ T \ U, x i = ∏ i ∈ U \ T, x i := by
      refine mul_left_cancel (a := ∏ i ∈ T ∩ U, x i) ?_
      calc (∏ i ∈ T ∩ U, x i) * (∏ i ∈ T \ U, x i)
          = ∏ i ∈ T, x i := Finset.prod_inter_mul_prod_sdiff T U x
        _ = ∏ i ∈ U, x i := hval
        _ = (∏ i ∈ U ∩ T, x i) * (∏ i ∈ U \ T, x i) :=
              (Finset.prod_inter_mul_prod_sdiff U T x).symm
        _ = (∏ i ∈ T ∩ U, x i) * (∏ i ∈ U \ T, x i) := by rw [Finset.inter_comm]
    have hdisj : Disjoint (T \ U) (U \ T) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      rw [Finset.mem_sdiff] at ha hb
      exact ha.2 hb.1
    -- The product over the symmetric difference is trivial.
    have hS : ∏ i ∈ (T \ U) ∪ (U \ T), x i = 1 := by
      rw [Finset.prod_union hdisj, hTU, ← pow_two, ← Finset.prod_pow]
      simp [hx]
    -- ... hence by `hne` the symmetric difference is empty, so `T = U`.
    have hSU : (T \ U) ∪ (U \ T) = ∅ := by
      by_contra hne'
      exact hne _ (Finset.nonempty_iff_ne_empty.mpr hne') hS
    have h1 : T \ U = ∅ := by
      rw [← Finset.subset_empty, ← hSU]
      exact Finset.subset_union_left
    have h2 : U \ T = ∅ := by
      rw [← Finset.subset_empty, ← hSU]
      exact Finset.subset_union_right
    exact Finset.Subset.antisymm (Finset.sdiff_eq_empty_iff_subset.mp h1)
      (Finset.sdiff_eq_empty_iff_subset.mp h2)
  have hcard : 2 ^ n = Fintype.card (Finset (Fin n)) := by
    rw [Fintype.card_finset, Fintype.card_fin]
  rw [hcard, Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_injective φ hinj

end Work.ClassFieldTower
