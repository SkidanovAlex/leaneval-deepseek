/-
Area `A7REC` (recognition of `A₇`), file `Basic/card_centralizer_V.lean`.

# `|C_G(V)| = 12`

Let `G` be a finite group satisfying the `A₇` hypotheses (`A7RecCtx G`): `S` is a Sylow
`2`-subgroup isomorphic to the dihedral group of order `8`, `z ∈ S` is its central involution,
`C_G(z) = U ⊔ S` with `|U| = 3` and `U ⊴ C_G(z)`, and `V = O₂(C_G(z))` is a four-group with
`N_G(U) = N_G(V)` of order `72`.

The point of this file is that `V` is *very* small in the following sense: the centralizer of the
four-group `V` is exactly `U × V` (of order `12`).  Nothing about the recognition of `A₇` is used;
the three inputs are

* `z ∈ V` (proved in `Basic/local.lean`, `z_mem_V`), so every element centralizing `V`
  centralizes `z` and hence `C_G(V) ≤ C_G(z)`; with `|C_G(z)| = 24` (`Basic/card_centralizer_z`)
  this gives `|C_G(V)| ∣ 24`;
* `U ≤ C_G(V)` (`Basic/local.lean`, `commute_U_V`) while `U ⊓ V = ⊥`, so `U ⊔ V` has order
  `12` and `12 ∣ |C_G(V)|`;
* the local structure of `D₈`: an abelian subgroup of order `4` of a dihedral group of order `8`
  is self-centralizing (`centralizer_inf_eq_of_isFourGroup_of_dihedral_four` below), so
  `C_G(V) ⊓ S = V` and `|C_G(V)| = 24` is impossible (it would force `S ≤ C_G(V) = C_G(z)`,
  hence `S ≤ V`).

`24` is the only multiple of `12` dividing `24` besides `12`, so `|C_G(V)| = 12`.

For `G = A₇` this is the familiar value `C_{A₇}(V₁) = V₁ × ⟨(4 5 6)⟩` of order `12`, where
`V₁ = {1, (0 1)(2 3), (0 2)(1 3), (0 3)(1 2)}` is the four-group acting on `{0,1,2,3}`.
-/
import Mathlib
import Submission.Work.A7REC.Api
import Submission.Work.A7REC.Assembly

namespace Work.A7REC.Basic

open Subgroup

/-! ## The self-centralizing subgroup of order `4` of a dihedral group of order `8` -/

/-- **An abelian subgroup of order `4` of a non-commutative group of order `8` is
self-centralizing.**

Let `H` be a finite group of order `8` which is not commutative and let `W ≤ H` have `4` elements
and be commutative.  Then `C_H(W) = W`.

Indeed `W ≤ C_H(W)` because `W` is commutative.  For the converse, if `x ∈ C_H(W)` with `x ∉ W`,
then `W` has index `2` in `H` (so it is normal), and `H = W ⊔ ⟨x⟩` (cardinality: `W ⊊ W ⊔ ⟨x⟩`
and `|W ⊔ ⟨x⟩| ∣ |H| = 8`): by `Subgroup.mem_sup_of_normal_left` every element of `H` is a
product of an element of `W` and a power of `x`, and all these commute with each other (`W` is
commutative and `x` centralizes `W`), making `H` commutative — contradiction. -/
theorem centralizer_eq_self_of_abelian_of_card_eight {H : Type*} [Group H] [Finite H]
    (h8 : Nat.card H = 8) (hnonab : ∃ a b : H, a * b ≠ b * a) {W : Subgroup H}
    (hW4 : Nat.card W = 4) (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) :
    Subgroup.centralizer (W : Set H) = W := by
  have hWle : W ≤ Subgroup.centralizer (W : Set H) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hWab x hx y hy).symm
  refine le_antisymm ?_ hWle
  intro x hx
  by_contra hxW
  -- `W` has index `2` in `H`, hence is normal.
  have hidx : W.index = 2 := by
    have h := Subgroup.card_mul_index W
    rw [hW4, h8] at h
    omega
  have hWnorm : W.Normal := Subgroup.normal_of_index_eq_two hidx
  -- `H = W ⊔ ⟨x⟩`, since `W ⊊ W ⊔ ⟨x⟩ ≤ H` and `|H| = 8`
  have hx_sup : x ∈ W ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hne_sub : W ≠ W ⊔ Subgroup.zpowers x := fun h => hxW (h ▸ hx_sup)
  have hcard_gt : 4 < Nat.card ↥(W ⊔ Subgroup.zpowers x) := by
    have hle : (4 : ℕ) ≤ Nat.card ↥(W ⊔ Subgroup.zpowers x) := by
      have h := Subgroup.card_le_of_le (le_sup_left : W ≤ W ⊔ Subgroup.zpowers x)
      rwa [hW4] at h
    have hne : (4 : ℕ) ≠ Nat.card ↥(W ⊔ Subgroup.zpowers x) := by
      intro hc
      exact hne_sub
        (Subgroup.eq_of_le_of_card_ge le_sup_left (le_of_eq (hc.symm.trans hW4.symm)))
    exact lt_of_le_of_ne hle hne
  have hdvd : Nat.card ↥(W ⊔ Subgroup.zpowers x) ∣ 8 := by
    have h := Subgroup.card_subgroup_dvd_card (s := W ⊔ Subgroup.zpowers x)
    rwa [h8] at h
  have hcard8 : Nat.card ↥(W ⊔ Subgroup.zpowers x) = 8 := by
    obtain ⟨m, hm⟩ := hdvd
    have hm1 : m = 1 := by
      have h5 : 5 * m ≤ Nat.card ↥(W ⊔ Subgroup.zpowers x) * m :=
        Nat.mul_le_mul_right m hcard_gt
      rw [← hm] at h5
      have hm_pos : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h | h
        · rw [h, mul_zero] at hm
          omega
        · exact h
      omega
    rw [hm1, mul_one] at hm
    omega
  have hsup : W ⊔ Subgroup.zpowers x = ⊤ :=
    Subgroup.eq_of_le_of_card_ge le_top (le_of_eq (by rw [Subgroup.card_top, h8, hcard8]))
  -- every element of `H` is `w * x ^ k`, and these commute pairwise
  have hcomm : ∀ a b : H, a * b = b * a := by
    letI : W.Normal := hWnorm
    intro a b
    obtain ⟨y₁, hy₁, z₁, hz₁, h₁⟩ := (Subgroup.mem_sup_of_normal_left (s := W)
      (t := Subgroup.zpowers x)).mp (by rw [hsup]; trivial : a ∈ W ⊔ Subgroup.zpowers x)
    obtain ⟨y₂, hy₂, z₂, hz₂, h₂⟩ := (Subgroup.mem_sup_of_normal_left (s := W)
      (t := Subgroup.zpowers x)).mp (by rw [hsup]; trivial : b ∈ W ⊔ Subgroup.zpowers x)
    -- `x` centralizes `W`, so every power of `x` does
    have hxz : ∀ z ∈ Subgroup.zpowers x, ∀ y ∈ W, z * y = y * z := by
      intro z hz y hy
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← hm]
      have hxw : x * y = y * x := (Subgroup.mem_centralizer_iff.mp hx y hy).symm
      exact (Commute.zpow_left ((commute_iff_eq x y).mpr hxw) m).eq
    have hzz : ∀ z ∈ Subgroup.zpowers x, ∀ z' ∈ Subgroup.zpowers x, z * z' = z' * z := by
      intro z hz z' hz'
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hz
      obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hz'
      rw [← hm, ← hl]
      exact (Commute.zpow_zpow_self x m l).eq
    have c₁ : Commute y₁ y₂ := (commute_iff_eq y₁ y₂).mpr (hWab y₁ hy₁ y₂ hy₂)
    have c₂ : Commute z₁ y₂ := (commute_iff_eq z₁ y₂).mpr (hxz z₁ hz₁ y₂ hy₂)
    have c₃ : Commute y₁ z₂ := (commute_iff_eq y₁ z₂).mpr ((hxz z₂ hz₂ y₁ hy₁).symm)
    have c₄ : Commute z₁ z₂ := (commute_iff_eq z₁ z₂).mpr (hzz z₁ hz₁ z₂ hz₂)
    have h11 : Commute (y₁ * z₁) (y₂ * z₂) := (c₁.mul_left c₂).mul_right (c₃.mul_left c₄)
    rw [← h₁, ← h₂]
    exact h11.eq
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab (hcomm a b)

/-- **`C_G(W) ⊓ P = W` for a four-subgroup `W` of a dihedral `P`.**

Let `P ≤ G` be isomorphic to the dihedral group of order `8` and let `W ≤ P` be a four-group
(`|W| = 4`, all elements of order `≤ 2`).  Then the elements of `P` centralizing `W` are exactly
the elements of `W`.

The subgroup `↥P` has order `8` and is not commutative (`exists_not_commute_dihedral_four`), and
`W.subgroupOf P` has order `4` and is commutative (a group of order `4` is); so
`centralizer_eq_self_of_abelian_of_card_eight` computes its centralizer *inside* `↥P`, which is
exactly `C_G(W) ⊓ P` transported along the inclusion. -/
theorem centralizer_inf_eq_of_isFourGroup_of_dihedral_four {G : Type*} [Group G] [Finite G]
    {P : Subgroup G} (hP : Nonempty (↥P ≃* DihedralGroup 4)) {W : Subgroup G} (hW : W ≤ P)
    (hW4 : Nat.card W = 4) (hWsq : ∀ w ∈ W, w ^ 2 = 1) :
    Subgroup.centralizer (W : Set G) ⊓ P = W := by
  obtain ⟨e⟩ := hP
  have h8 : Nat.card ↥P = 8 := by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hnonab : ∃ a b : ↥P, a * b ≠ b * a := exists_not_commute_dihedral_four e
  have hW4' : Nat.card ↥(W.subgroupOf P) = 4 := by
    rw [← hW4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW).toEquiv
  have hWab' : ∀ a ∈ W.subgroupOf P, ∀ b ∈ W.subgroupOf P, a * b = b * a := by
    haveI : IsPGroup 2 ↥(W.subgroupOf P) :=
      IsPGroup.of_card_dvd_pow (p := 2) (n := 2) (by rw [hW4']; norm_num)
    haveI : IsMulCommutative ↥(W.subgroupOf P) :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hW4']; norm_num)
    intro a ha b hb
    have h := isMulCommutative_iff.mp (inferInstance : IsMulCommutative ↥(W.subgroupOf P))
      (⟨a, ha⟩ : ↥(W.subgroupOf P)) (⟨b, hb⟩ : ↥(W.subgroupOf P))
    simpa using congrArg (fun t : ↥(W.subgroupOf P) => (t : ↥P)) h
  have key := centralizer_eq_self_of_abelian_of_card_eight h8 hnonab hW4' hWab'
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    have hmem : (⟨x, hx.2⟩ : ↥P) ∈ Subgroup.centralizer (↑(W.subgroupOf P) : Set ↥P) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hx.1 ((y : ↥P) : G) hy
    rw [key] at hmem
    exact hmem
  · intro x hx
    rw [Subgroup.mem_inf]
    refine ⟨?_, hW hx⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (commute_of_sq_eq_one (by simpa [pow_two] using hWsq x hx)
      (by simpa [pow_two] using hWsq y hy)
      (by simpa [pow_two] using hWsq (x * y) (W.mul_mem hx hy))).symm

/-! ## `|U ⊔ V| = 12` -/

/-- **`|U ⊔ V| = 12`.**  `U` and `V` commute (`commute_U_V`), so in particular `V` normalizes `U`,
while `U ⊓ V = ⊥` because `V ≤ S` and `U ⊓ S = ⊥` (`V_le_S`, `U_inf_S`).  Hence `U ⊔ V` is the
internal direct product of `U ≅ C₃` and `V ≅ C₂ × C₂`: `|U ⊔ V| = 3 · 4 = 12`. -/
theorem card_sup_U_V (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) :
    Nat.card ↥(ctx.U ⊔ ctx.V) = 12 := by
  have hVnorm : ctx.V ≤ Subgroup.normalizer (ctx.U : Set G) := by
    have h2 : ⁅ctx.V, ctx.U⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact commute_U_V G ctx
    have hVC : ctx.V ≤ Subgroup.centralizer (ctx.U : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := ctx.V) (H₂ := ctx.U)).mp h2
    exact le_trans hVC (Subgroup.centralizer_le_normalizer _)
  have hbot : ctx.U ⊓ ctx.V = ⊥ := by
    refine le_bot_iff.mp ?_
    calc ctx.U ⊓ ctx.V ≤ ctx.U ⊓ (ctx.S : Subgroup G) := inf_le_inf_left _ (V_le_S G ctx)
      _ = ⊥ := U_inf_S G ctx
  have hdisj : Disjoint ctx.U ctx.V := disjoint_iff.mpr hbot
  rw [card_sup_mul_card_of_le_normalizer_of_disjoint hVnorm hdisj, ctx.hUcard, ctx.hV4.1]

/-! ## `|C_G(V)| = 12` -/

/-- **`|C_G(V)| = 12`.**

`z ∈ V`, so `C_G(V) ≤ C_G(z)` and `|C_G(V)| ∣ 24`; since `U ⊔ V ≤ C_G(V)` has order `12`, also
`12 ∣ |C_G(V)|`.  The only remaining possibility `|C_G(V)| = 24` is excluded: it would give
`C_G(V) = C_G(z)` (equal orders), hence `S ≤ C_G(V)` as `z` is central in `S`, and then
`S ≤ C_G(V) ⊓ S = V` (the self-centralizing four-subgroup lemma) against `|S| = 8 > 4 = |V|`.
Therefore `|C_G(V)| = 12`. -/
theorem card_centralizer_V (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) :
    Nat.card (Subgroup.centralizer (ctx.V : Set G)) = 12 := by
  -- `z ∈ V`, hence `C_G(V) ≤ C_G(z)`
  have hle : Subgroup.centralizer (ctx.V : Set G) ≤ Subgroup.centralizer ({ctx.z} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact hx ctx.z (z_mem_V G ctx)
  -- `|C_G(V)|` divides `24`
  have hdvd : Nat.card (Subgroup.centralizer (ctx.V : Set G)) ∣ 24 := by
    have h := Subgroup.card_dvd_of_le hle
    rwa [card_centralizer_z G ctx] at h
  -- `U ⊔ V ≤ C_G(V)`, of order `12`
  have hUV_le : ctx.U ⊔ ctx.V ≤ Subgroup.centralizer (ctx.V : Set G) := by
    refine sup_le ?_ ?_
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := ctx.U) (H₂ := ctx.V)).mp
        (commute_U_V G ctx)
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (commute_of_sq_eq_one (by simpa [pow_two] using ctx.hV4.2 x hx)
        (by simpa [pow_two] using ctx.hV4.2 y hy)
        (by simpa [pow_two] using ctx.hV4.2 (x * y) (ctx.V.mul_mem hx hy))).symm
  -- `12` divides `|C_G(V)|`
  have h12 : 12 ∣ Nat.card (Subgroup.centralizer (ctx.V : Set G)) := by
    have h := Subgroup.card_dvd_of_le hUV_le
    rwa [card_sup_U_V G ctx] at h
  have hge : 12 ≤ Nat.card (Subgroup.centralizer (ctx.V : Set G)) := by
    have h := Subgroup.card_le_of_le hUV_le
    rwa [card_sup_U_V G ctx] at h
  -- `|C_G(V)| ∈ {12, 24}`; `24` is impossible
  obtain ⟨k, hk⟩ := h12
  have hle24 : 12 * k ≤ 24 := by
    have h := Nat.le_of_dvd (by norm_num : 0 < 24) hdvd
    rwa [hk] at h
  have hk1 : 1 ≤ k := by omega
  have hk2 : k ≤ 2 := by omega
  interval_cases k
  · omega
  · exfalso
    have hC24 : Nat.card (Subgroup.centralizer (ctx.V : Set G)) = 24 := by omega
    have hCeq : Subgroup.centralizer (ctx.V : Set G) = Subgroup.centralizer ({ctx.z} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [card_centralizer_z G ctx, hC24])
    have hS_le : (ctx.S : Subgroup G) ≤ Subgroup.centralizer (ctx.V : Set G) := by
      rw [hCeq]
      exact S_le_centralizer_z G ctx
    have hS_le_V : (ctx.S : Subgroup G) ≤ ctx.V := by
      have hinf : Subgroup.centralizer (ctx.V : Set G) ⊓ (ctx.S : Subgroup G) = ctx.V :=
        centralizer_inf_eq_of_isFourGroup_of_dihedral_four ctx.hSdih (V_le_S G ctx)
          ctx.hV4.1 ctx.hV4.2
      calc (ctx.S : Subgroup G) ≤ Subgroup.centralizer (ctx.V : Set G) ⊓ (ctx.S : Subgroup G) :=
            le_inf hS_le le_rfl
        _ = ctx.V := hinf
    have hcard := Subgroup.card_le_of_le hS_le_V
    rw [card_S G ctx, ctx.hV4.1] at hcard
    omega

/-- **`C_G(V) = U × V`.**

`U` and `V` commute (`commute_U_V`) and meet trivially (`U ⊓ V = ⊥`), so `U ⊔ V` is the internal
direct product `U × V`, of order `12` (`card_sup_U_V`), and it is contained in `C_G(V)`.  As
`|C_G(V)| = 12` (`card_centralizer_V`), the inclusion is an equality. -/
theorem centralizer_V_eq_sup (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) :
    Subgroup.centralizer (ctx.V : Set G) = ctx.U ⊔ ctx.V := by
  have hUV_le : ctx.U ⊔ ctx.V ≤ Subgroup.centralizer (ctx.V : Set G) := by
    refine sup_le ?_ ?_
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := ctx.U) (H₂ := ctx.V)).mp
        (commute_U_V G ctx)
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (commute_of_sq_eq_one (by simpa [pow_two] using ctx.hV4.2 x hx)
        (by simpa [pow_two] using ctx.hV4.2 y hy)
        (by simpa [pow_two] using ctx.hV4.2 (x * y) (ctx.V.mul_mem hx hy))).symm
  refine (Subgroup.eq_of_le_of_card_ge hUV_le ?_).symm
  exact le_of_eq (by rw [card_centralizer_V G ctx, card_sup_U_V G ctx])

end Work.A7REC.Basic
