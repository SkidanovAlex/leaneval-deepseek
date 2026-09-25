import Mathlib
import Submission.Work.ClassFieldTower.ProTwoDefs

/-!
# A residually-`2` group with bounded finite `2`-quotients is finite

`Work.ClassFieldTower.finite_of_bounded_twoQuotients`:

> A group `G` which is residually a finite `2`-group (`ResiduallyFiniteTwoGroup G`), and every
> one of whose finite `2`-group quotients `G ⧸ N` has `Nat.card (G ⧸ N) ≤ M`, is finite.

This is the "bounded quotients" contrapositive of the pro-`2`-completion formulation: `G` embeds
into its pro-`2` completion, and a pro-`2` group all of whose finite quotients have order at most
`M` is finite (if `N₀` is an open normal subgroup of maximal index and `N₀ ≠ 1`, then intersecting
with an open normal subgroup not containing a given nontrivial element of `N₀` strictly increases
the index, contradiction).

The argument below is the abstract-group transcription of that, needing no completion:

* let `A` be the set of cardinals `Nat.card (G ⧸ N)` realized by normal `N` with `G ⧸ N` a finite
  `2`-group; it is nonempty (`N = ⊤`) and bounded above by `M`, so it has a maximum, attained at
  some `N₀`;
* if `N₀ ≠ ⊥`, pick `g ∈ N₀`, `g ≠ 1`, and (by `ResiduallyFiniteTwoGroup`) a normal `N` with
  `G ⧸ N` a finite `2`-group and `g ∉ N`.  Then `N₀ ⊓ N < N₀`, and the third isomorphism theorem
  (`Subgroup.relIndex_mul_index`) shows `Nat.card (G ⧸ N₀) < Nat.card (G ⧸ (N₀ ⊓ N))`,
  contradicting maximality; the quotient `G ⧸ (N₀ ⊓ N)` is again a finite `2`-group because both
  `G ⧸ N₀` and `G ⧸ N` are;
* hence `N₀ = ⊥` and `G ≅ G ⧸ ⊥` is finite.

The hypothesis that `M` bounds only the *`2`-group* quotients (rather than all finite quotients) is
what makes this statement strictly stronger than
`Commons.GroupTheory.finite_of_bounded_finite_quotients`, which additionally assumes that `G` is
finitely generated and residually finite (but bounds all finite quotients).  Here no finite
generation is needed: residual finiteness in the `2`-group sense suffices.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open scoped Classical

namespace Work.ClassFieldTower

/-- If `K ≤ H` are subgroups of finite index and `K ≠ H`, then `H` has strictly smaller index
than `K`. -/
private lemma index_lt_index_of_lt {G : Type*} [Group G] {H K : Subgroup G}
    (hKH : K ≤ H) (hK : K.index ≠ 0) (hH : H.index ≠ 0) (hne : K ≠ H) :
    H.index < K.index := by
  have hmul : K.relIndex H * H.index = K.index := Subgroup.relIndex_mul_index hKH
  have hr1 : K.relIndex H ≠ 1 := fun h =>
    hne (le_antisymm (Subgroup.relIndex_eq_one.mp h) hKH).symm
  have hr0 : K.relIndex H ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact hK hmul.symm
  have h2 : 2 ≤ K.relIndex H := by omega
  have h3 : H.index < 2 * H.index := by omega
  calc H.index < 2 * H.index := h3
    _ ≤ K.relIndex H * H.index := Nat.mul_le_mul_right _ h2
    _ = K.index := hmul

/-- A group which is an extension of a finite `p`-group by a finite `p`-group is a finite
`p`-group: here, if `G ⧸ N₀` and `G ⧸ N` are `p`-groups then so is `G ⧸ (N₀ ⊓ N)`
(`N₀ ⧸ (N₀ ⊓ N)` is a subgroup of `G ⧸ N` and `G ⧸ (N₀ ⊓ N) ↠ G ⧸ N₀`). -/
private lemma isPGroup_quotient_inf {p : ℕ} {G : Type*} [Group G] {N₀ N : Subgroup G}
    [N₀.Normal] [N.Normal] (h₀ : IsPGroup p (G ⧸ N₀)) (hN : IsPGroup p (G ⧸ N)) :
    IsPGroup p (G ⧸ (N₀ ⊓ N)) := by
  rw [isPGroup_iff_pow_pow_eq_one] at h₀ hN ⊢
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (N₀ ⊓ N) x
  obtain ⟨i, hi⟩ := h₀ (QuotientGroup.mk' N₀ g)
  obtain ⟨k, hk⟩ := hN (QuotientGroup.mk' N g)
  have hi' : g ^ p ^ i ∈ N₀ := by
    have hmk : QuotientGroup.mk' N₀ (g ^ p ^ i) = 1 := by
      rw [map_pow]; exact hi
    exact (QuotientGroup.eq_one_iff (N := N₀) (g ^ p ^ i)).mp hmk
  have hk' : g ^ p ^ k ∈ N := by
    have hmk : QuotientGroup.mk' N (g ^ p ^ k) = 1 := by
      rw [map_pow]; exact hk
    exact (QuotientGroup.eq_one_iff (N := N) (g ^ p ^ k)).mp hmk
  refine ⟨max i k, ?_⟩
  have hpow₀ : g ^ p ^ max i k = (g ^ p ^ i) ^ p ^ (max i k - i) := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' (le_max_left i k)]
  have hpow₁ : g ^ p ^ max i k = (g ^ p ^ k) ^ p ^ (max i k - k) := by
    rw [← pow_mul, ← pow_add, Nat.add_sub_cancel' (le_max_right i k)]
  have hmem : g ^ p ^ max i k ∈ N₀ ⊓ N :=
    ⟨by rw [hpow₀]; exact pow_mem hi' _, by rw [hpow₁]; exact pow_mem hk' _⟩
  rw [← map_pow]
  exact (QuotientGroup.eq_one_iff (N := N₀ ⊓ N) (g ^ p ^ max i k)).mpr hmem

/-- **A residually finite-`2` group whose finite `2`-quotients have bounded order is finite.**

`hres` says every `g ≠ 1` survives in some finite `2`-group quotient; `h` bounds the order of
every such quotient by `M`.  Then `G` itself has at most `M` elements. -/
theorem finite_of_bounded_twoQuotients {G : Type*} [Group G] (hres : ResiduallyFiniteTwoGroup G)
    (M : ℕ) (h : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N) →
      Nat.card (G ⧸ N) ≤ M) : Finite G := by
  classical
  -- The cardinals of the finite `2`-group quotients of `G`.
  let A : Set ℕ := {d | ∃ (N : Subgroup G) (_ : N.Normal), Finite (G ⧸ N) ∧
    IsPGroup 2 (G ⧸ N) ∧ Nat.card (G ⧸ N) = d}
  have hne : A.Nonempty := by
    refine ⟨1, ⊤, inferInstance, ?_, ?_, ?_⟩
    · exact inferInstance
    · exact IsPGroup.of_card (p := 2) (n := 0)
        (by rw [pow_zero, ← Subgroup.index_eq_card, Subgroup.index_top])
    · rw [← Subgroup.index_eq_card, Subgroup.index_top]
  have hbdd : BddAbove A := ⟨M, fun d hd => by
    obtain ⟨N, hN, hfin, hpg, rfl⟩ := hd
    exact h N hfin hpg⟩
  -- A normal subgroup `N₀` whose quotient is a finite `2`-group of maximal order.
  obtain ⟨N₀, hN₀norm, hfin₀, hpg₀, hcard₀⟩ := Nat.sSup_mem hne hbdd
  haveI : N₀.Normal := hN₀norm
  haveI : Finite (G ⧸ N₀) := hfin₀
  have hmax : ∀ (N : Subgroup G) [N.Normal], Finite (G ⧸ N) → IsPGroup 2 (G ⧸ N) →
      Nat.card (G ⧸ N) ≤ Nat.card (G ⧸ N₀) := by
    intro N hN hfin hpg
    have h1 : Nat.card (G ⧸ N) ≤ sSup A := le_csSup hbdd ⟨N, hN, hfin, hpg, rfl⟩
    rwa [← hcard₀] at h1
  by_cases hbot : N₀ = ⊥
  · -- Then `G ≅ G ⧸ ⊥ = G ⧸ N₀` is finite.
    rw [hbot] at hfin₀
    exact (QuotientGroup.quotientBot (G := G)).toEquiv.finite_iff.mp hfin₀
  · -- Otherwise a nontrivial element of `N₀` survives in a further finite `2`-quotient, and
    -- intersecting strictly increases the order, contradicting maximality.
    exfalso
    obtain ⟨g, hgN₀, hg1⟩ : ∃ g ∈ N₀, g ≠ 1 := by
      have hlt : (⊥ : Subgroup G) < N₀ := bot_lt_iff_ne_bot.mpr hbot
      obtain ⟨g, hgN₀, hg⟩ := SetLike.exists_of_lt hlt
      exact ⟨g, hgN₀, by simpa using hg⟩
    obtain ⟨N, hNnorm, hfinN, hpgN, hne1⟩ := hres g hg1
    haveI : N.Normal := hNnorm
    haveI : Finite (G ⧸ N) := hfinN
    have hgN : g ∉ N := fun hg => hne1 ((QuotientGroup.eq_one_iff g).mpr hg)
    haveI hfi₀ : N₀.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    haveI hfiN : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    haveI hfinL : Finite (G ⧸ (N₀ ⊓ N)) := inferInstance
    have hpgL : IsPGroup 2 (G ⧸ (N₀ ⊓ N)) := isPGroup_quotient_inf hpg₀ hpgN
    have hstrict : Nat.card (G ⧸ N₀) < Nat.card (G ⧸ (N₀ ⊓ N)) := by
      rw [← Subgroup.index_eq_card, ← Subgroup.index_eq_card]
      refine index_lt_index_of_lt inf_le_left ?_ ?_ ?_
      · exact Subgroup.index_ne_zero_of_finite
      · exact Subgroup.index_ne_zero_of_finite
      · intro hEq
        exact hgN (inf_eq_left.mp hEq hgN₀)
    have hle := hmax (N₀ ⊓ N) hfinL hpgL
    omega

end Work.ClassFieldTower
