import Mathlib

set_option linter.style.haveILetI false

namespace Work.BSW.Cases.K4

/-- If `X ≤ G` is a subgroup of order `3` in a finite group, then the normalizer of `X` has order
at most twice the order of the centralizer of `X`.

Indeed `N_G(X)` acts on `X` by conjugation, giving a homomorphism
`N_G(X) →* MulAut X` with kernel `C_G(X)`, so `|N_G(X)| = |C_G(X)| · |image|`.  The image is a
subgroup of `MulAut X`, and `X` is cyclic of order `3`, so
`|MulAut X| = Nat.totient 3 = 2`.  Hence `|N_G(X)| ≤ 2 · |C_G(X)|`. -/
theorem card_normalizer_le_two_mul_card_centralizer {G : Type} [Group G] [Finite G] (X : Subgroup G)
    (hX3 : Nat.card ↥X = 3) :
    Nat.card ↥(Subgroup.normalizer (X : Set G)) ≤
      2 * Nat.card ↥(Subgroup.centralizer (X : Set G)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  -- `X` has order `3`, hence is cyclic.
  haveI : IsCyclic ↥X := isCyclic_of_card_dvd_prime (p := 3) (by rw [hX3])
  let N : Subgroup G := Subgroup.normalizer (X : Set G)
  let C : Subgroup G := Subgroup.centralizer (X : Set G)
  have hCN : C ≤ N := Subgroup.centralizer_le_normalizer (X : Set G)
  change Nat.card ↥N ≤ 2 * Nat.card ↥C
  -- The conjugation action of `N_G(X)` on `X`; its kernel is `C_G(X)`.
  let f : ↥N →* MulAut ↥X := X.normalizerMonoidHom
  have hker : f.ker = C.subgroupOf N := Subgroup.normalizerMonoidHom_ker X
  have hcardker : Nat.card ↥f.ker = Nat.card ↥C := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv
  haveI : Finite (MulAut ↥X) := inferInstance
  -- `MulAut X` has order `Nat.totient 3 = 2`.
  have haut : Nat.card (MulAut ↥X) = 2 := by
    rw [IsCyclic.card_mulAut, hX3]
    decide
  -- The image of `f` is a subgroup of `MulAut X`, hence has order at most `2`.
  have hrange : Nat.card ↥f.range ≤ 2 := by
    have h1 : Nat.card ↥f.range ≤ Nat.card (MulAut ↥X) :=
      Subgroup.card_le_card_group (G := MulAut ↥X) f.range
    rwa [haut] at h1
  -- `|N| = |ker f| * |range f| = |C| * |range f|`.
  have hmul := Subgroup.card_ker_mul_card_range f
  rw [hcardker] at hmul
  calc Nat.card ↥N = Nat.card ↥C * Nat.card ↥f.range := hmul.symm
    _ ≤ Nat.card ↥C * 2 := Nat.mul_le_mul_left _ hrange
    _ = 2 * Nat.card ↥C := by ring

end Work.BSW.Cases.K4
