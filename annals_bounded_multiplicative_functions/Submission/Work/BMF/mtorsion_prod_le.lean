import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset

/-- The number of `m`-th roots of unity in `ZMod (∏ p ∈ s, f p)` is at most the product of the
numbers of `m`-th roots of unity in the factors `ZMod (f p)`, provided the `f p` are non-zero
and pairwise coprime.  This is the Chinese remainder theorem: the natural map
`ZMod (∏ p ∈ s, f p) → ∏ p ∈ s, ZMod (f p)` is an isomorphism of rings, and an element is an
`m`-th root of unity in a product ring if and only if every component is. -/
theorem mtorsion_prod_le (s : Finset ℕ) (f : ℕ → ℕ) (m : ℕ)
    (hf : ∀ p ∈ s, 1 ≤ f p)
    (hcop : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → (f p).Coprime (f q)) :
    Nat.card (rootsOfUnity m (ZMod (∏ p ∈ s, f p))) ≤
      ∏ p ∈ s, Nat.card (rootsOfUnity m (ZMod (f p))) := by
  classical
  -- Reindex `s` by the subtype `↥s`, so that `∏ p ∈ s, f p = ∏ i : ↥s, f i`.
  have hcop' : Pairwise (fun i j : ↥s => Nat.Coprime (f i.1) (f j.1)) := by
    intro i j hij
    exact hcop i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h))
  -- The Chinese remainder theorem as a ring isomorphism.
  let e : ZMod (∏ i : ↥s, f i.1) ≃+* (Π i : ↥s, ZMod (f i.1)) :=
    ZMod.prodEquivPi (fun i : ↥s => f i.1) hcop'
  let ρ : rootsOfUnity m (ZMod (∏ i : ↥s, f i.1)) ≃*
      rootsOfUnity m (Π i : ↥s, ZMod (f i.1)) :=
    MulEquiv.restrictRootsOfUnity e.toMulEquiv m
  -- An `m`-th root of unity in a product ring is a tuple of `m`-th roots of unity.
  let ψ : rootsOfUnity m (Π i : ↥s, ZMod (f i.1)) →
      Π i : ↥s, rootsOfUnity m (ZMod (f i.1)) :=
    fun ζ i => ⟨MulEquiv.piUnits ζ.1 i, by
      have hm : ζ.1 ^ m = 1 := (mem_rootsOfUnity m ζ.1).mp ζ.2
      have h : (MulEquiv.piUnits ζ.1) ^ m = 1 := by
        rw [← map_pow, hm, map_one]
      have := congrFun h i
      simpa [Pi.pow_apply] using this⟩
  have hψinj : Function.Injective ψ := by
    intro ζ ζ' hζ
    apply Subtype.ext
    apply MulEquiv.injective MulEquiv.piUnits
    funext i
    have := congrFun hζ i
    exact congrArg Subtype.val this
  have hφinj : Function.Injective (ψ ∘ ρ) := hψinj.comp ρ.injective
  haveI (j : ↥s) : NeZero (f j.1) := ⟨by have := hf j.1 j.2; omega⟩
  have h1 : Nat.card (rootsOfUnity m (ZMod (∏ i : ↥s, f i.1)))
      ≤ Nat.card (Π i : ↥s, rootsOfUnity m (ZMod (f i.1))) :=
    Nat.card_le_card_of_injective (ψ ∘ ρ) hφinj
  calc
    Nat.card (rootsOfUnity m (ZMod (∏ p ∈ s, f p)))
        = Nat.card (rootsOfUnity m (ZMod (∏ i : ↥s, f i.1))) := by
          rw [← Finset.prod_coe_sort s f]
    _ ≤ Nat.card (Π i : ↥s, rootsOfUnity m (ZMod (f i.1))) := h1
    _ = ∏ i : ↥s, Nat.card (rootsOfUnity m (ZMod (f i.1))) := Nat.card_pi
    _ = ∏ p ∈ s, Nat.card (rootsOfUnity m (ZMod (f p))) :=
          Finset.prod_coe_sort s (fun p => Nat.card (rootsOfUnity m (ZMod (f p))))

end Work.BMF
