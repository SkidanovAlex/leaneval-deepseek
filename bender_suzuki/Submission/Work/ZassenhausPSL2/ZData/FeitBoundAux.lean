import Mathlib
import Submission.Work.ZassenhausPSL2.Defs
import Submission.Work.ZassenhausPSL2.Basic
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.card_twoPoint_dvd
import Submission.Work.ZassenhausTwoGroup.even_card_Q
import Submission.Work.ThreePoints.TwoPointTransitive

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausPSL2.ZData.FeitBoundAux`

The auxiliary lemmas used by the target of `ZData.feit_bound` and by the leaf decomposition
F0–F8 of Feit's count in `Submission/Work/ZassenhausPSL2/Feit/`.  The target of this file is Feit's inequality for the split rank-one (Zassenhaus) data
`(H, Q, t)` with `Q` an abelian `2`-group:

`2 * |twoPoint H t| + 1 ≥ |Q|`, i.e. `|Q| ≤ 2|D| + 1` where `D = H ∩ Hᵗ`.

The lemmas proved below pin down exactly what the target asserts.  They show
that, for the data of `IsSplitRankOne` (with `IsZassenhaus H`), the target is **equivalent** to
the statement that `Q` is elementary abelian (`∀ x ∈ Q, x ^ 2 = 1`):

* `card_twoPoint_dvd` (already in the workspace): `|D| ∣ |Q| - 1`, from the fact that `D` acts
  fixed point freely on `Q#`;
* `even_card_Q` (already in the workspace): `|Q|` is even;
* hence `|Q| - 1 = k |D|`, and `2|D| + 1 ≥ |Q|` says `k ≤ 2`; `k = 2` is impossible since
  `|Q| = 2|D| + 1` would be odd.  So the target says `|Q| = |D| + 1 = |Inv(H)| + 1`
  (`ncard_involutions_H_eq_card_twoPoint`: `D` is transitive and free on `Inv(H)`);
* `involution_mem_Q`: every involution of `H` lies in `Q`,
* `ncard_involutions_Q_eq`: so `|Inv(Q)| = |Inv(H)| = |D|`,
* therefore `|Q| = |D| + 1` holds iff the involutions of `Q` exhaust `Q#`, i.e. iff
  `Q` is elementary abelian.

Consequently the target is *exactly* the abelian case of the classification of Zassenhaus
groups: it is Feit's inequality `2q ≥ m - 1` (Feit 1960, Theorem 1 / Lemma 3.2), whose proof
uses Suzuki's exceptional-character theory for T.I.F.N. subgroups (Feit 1960 §2, Theorem 2;
Brauer–Suzuki–Wall; Isaacs, *Character Theory of Finite Groups*, 7.17–7.20), together with
Zassenhaus' near-field analysis for the case `q ≥ (m-1)/2`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open scoped Pointwise

namespace Work.ZassenhausPSL2.ZData

variable {G : Type} [Group G] [Finite G]
variable {H Q : Subgroup G} {t : G}

/-! ## Elementary helpers -/

/-- Conjugation preserves the order of an element. -/
theorem orderOf_conj_eq_aux {K : Type*} [Group K] (c x : K) :
    orderOf (c * x * c⁻¹) = orderOf x := by
  have h : SemiconjBy c x (c * x * c⁻¹) := by rw [SemiconjBy]; group
  exact (SemiconjBy.orderOf_eq c h).symm

/-- An element of order two lies in every normal subgroup of odd index (Burnside/Cauchy):
otherwise its image in the odd-order quotient has order two. -/
theorem mem_of_orderOf_eq_two_of_odd_index {N : Subgroup G} [N.Normal] (hidx : Odd N.index)
    {x : G} (hx : orderOf x = 2) : x ∈ N := by
  by_contra hxN
  have hdvd : orderOf (QuotientGroup.mk' N x) ∣ 2 := by
    rw [← hx]; exact orderOf_map_dvd (QuotientGroup.mk' N) x
  have hne1 : orderOf (QuotientGroup.mk' N x) ≠ 1 := by
    intro h
    refine hxN ?_
    have hker : x ∈ (QuotientGroup.mk' N).ker := by
      rw [MonoidHom.mem_ker]; exact orderOf_eq_one_iff.mp h
    rwa [QuotientGroup.ker_mk'] at hker
  have htwo : orderOf (QuotientGroup.mk' N x) = 2 :=
    (Nat.dvd_prime Nat.prime_two).mp hdvd |>.resolve_left hne1
  have hdvd2 : 2 ∣ N.index := by
    rw [Subgroup.index_eq_card]
    exact htwo ▸ orderOf_dvd_natCard (QuotientGroup.mk' N x)
  exact Nat.not_even_iff_odd.mpr hidx (even_iff_two_dvd.mpr hdvd2)

/-- `Q` and `Q.subgroupOf K` have the same cardinality when `Q ≤ K`. -/
theorem card_subgroupOf_le {K : Subgroup G} (hKH : Q ≤ K) :
    Nat.card ↥(Q.subgroupOf K) = Nat.card Q :=
  Nat.card_congr
    { toFun := fun x => ⟨((x : ↥K) : G), Subgroup.mem_subgroupOf.mp x.2⟩
      invFun := fun y => ⟨⟨(y : G), hKH y.2⟩, Subgroup.mem_subgroupOf.mpr y.2⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext rfl }

/-! ## Involutions of `H` lie in `Q`, and `|D| = |Inv(H)|` -/

/-- In a split rank-one datum `H = Q ⋊ D` with `D` of odd order, every involution of `H` lies
in `Q` (Peterfalvi I Ch. I §2: `Inv(H) ⊆ Q`). -/
theorem involution_mem_Q (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) {u : G}
    (hu : u ∈ involutions (H : Set G)) : u ∈ Q := by
  simp only [involutions, Set.mem_setOf_eq] at hu
  haveI : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mpr h.normal
  have hcardQ : Nat.card ↥(Q.subgroupOf H) = Nat.card Q := card_subgroupOf_le h.le
  have hcardH : Nat.card H = Nat.card Q * Nat.card (twoPoint H t) :=
    Work.ZassenhausTwoGroup.card_eq_mul_card_twoPoint h
  have hidx : (Q.subgroupOf H).index = Nat.card (twoPoint H t) := by
    have hmul : (Q.subgroupOf H).index * Nat.card ↥(Q.subgroupOf H) = Nat.card H :=
      Subgroup.index_mul_card _
    rw [hcardQ, hcardH] at hmul
    rw [mul_comm (Nat.card Q) (Nat.card (twoPoint H t))] at hmul
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmul
  have hodd : Odd (Q.subgroupOf H).index :=
    hidx ▸ h.stronglyEmbedded.2.2 t h.not_mem
  have hu2 : orderOf (⟨u, hu.1⟩ : ↥H) = 2 := by
    rw [← Subgroup.orderOf_coe (⟨u, hu.1⟩ : ↥H)]
    exact hu.2
  have hmem : (⟨u, hu.1⟩ : ↥H) ∈ Q.subgroupOf H :=
    mem_of_orderOf_eq_two_of_odd_index (G := ↥H) hodd hu2
  exact Subgroup.mem_subgroupOf.mp hmem

/-- `D = twoPoint H t` acts regularly (transitively and freely) on the involutions of `H`; hence
`|D| = |Inv(H)|`.  (Peterfalvi I Ch. I §2 Prop. 2 (b) gives transitivity, the Zassenhaus
hypothesis gives freeness.) -/
theorem ncard_involutions_H_eq_card_twoPoint (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) :
    Nat.card (twoPoint H t) = (involutions (H : Set G)).ncard := by
  classical
  haveI : Fintype ↥H := Fintype.ofFinite _
  -- an involution of `H` exists because `|H|` is even
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2dvd : 2 ∣ Fintype.card ↥H := by
    rw [Fintype.card_eq_nat_card]
    exact even_iff_two_dvd.mp h.stronglyEmbedded.2.1
  obtain ⟨u₀, hu₀⟩ := exists_prime_orderOf_dvd_card (G := ↥H) 2 h2dvd
  have hu₀G : orderOf (u₀ : G) = 2 := by
    rw [Subgroup.orderOf_coe u₀]
    exact hu₀
  have hu₀mem : (u₀ : G) ∈ involutions (H : Set G) := ⟨u₀.2, hu₀G⟩
  have hu₀Q : (u₀ : G) ∈ Q := involution_mem_Q h hz hu₀mem
  have hfpf : Work.ZassenhausTwoGroup.IsFpfOn (twoPoint H t) Q :=
    Work.ZassenhausTwoGroup.CardTwoPoint.isFpfOn_twoPoint_Q h hz
  have hDleH : twoPoint H t ≤ H := inf_le_left
  have hmain : (twoPoint H t : Set G).ncard = (involutions (H : Set G)).ncard := by
    refine Set.ncard_congr (fun d _ => d * (u₀ : G) * d⁻¹) ?_ ?_ ?_
    · intro d hd
      exact ⟨H.mul_mem (H.mul_mem (hDleH hd) u₀.2) (H.inv_mem (hDleH hd)),
        by rw [orderOf_conj_eq_aux]; exact hu₀G⟩
    · intro d₁ d₂ hd₁ hd₂ heq
      by_contra hne
      have hmem : d₂⁻¹ * d₁ ∈ twoPoint H t :=
        (twoPoint H t).mul_mem ((twoPoint H t).inv_mem hd₂) hd₁
      have hne1 : d₂⁻¹ * d₁ ≠ 1 := by
        intro hc
        refine hne ?_
        have h2 := congrArg (fun x => d₂ * x) hc
        simpa [mul_assoc] using h2
      have hconj : (d₂⁻¹ * d₁) * (u₀ : G) * (d₂⁻¹ * d₁)⁻¹ = (u₀ : G) := by
        have h1 : (d₂⁻¹ * d₁) * (u₀ : G) * (d₂⁻¹ * d₁)⁻¹
            = d₂⁻¹ * (d₁ * (u₀ : G) * d₁⁻¹) * d₂ := by group
        rw [h1, heq]
        group
      have h1 := hfpf (d₂⁻¹ * d₁) hmem hne1 (u₀ : G) hu₀Q hconj
      rw [h1, orderOf_one] at hu₀G
      exact absurd hu₀G (by norm_num)
    · intro v hv
      obtain ⟨d, hd, hdconj⟩ :=
        Work.ThreePoints.twoPoint_transitive_on_involutions h.stronglyEmbedded h.invol h.not_mem
          hu₀mem hv
      exact ⟨d, hd, hdconj⟩
  have hnat : Nat.card (twoPoint H t) = (twoPoint H t : Set G).ncard :=
    Nat.card_coe_set_eq (twoPoint H t : Set G)
  rw [hnat]
  exact hmain

/-- The involutions of `Q` are exactly the involutions of `H`: `Inv(Q) = Inv(H)`. -/
theorem ncard_involutions_Q_eq (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) :
    (involutions (Q : Set G)).ncard = (involutions (H : Set G)).ncard := by
  have hset : (involutions (Q : Set G)) = involutions (H : Set G) := by
    ext u
    constructor
    · intro hu
      simp only [involutions, Set.mem_setOf_eq] at hu
      exact ⟨h.le hu.1, hu.2⟩
    · intro hu
      simp only [involutions, Set.mem_setOf_eq] at hu ⊢
      exact ⟨involution_mem_Q h hz hu, hu.2⟩
  rw [hset]

/-- The number of involutions of `Q` is `|D| = |twoPoint H t|`. -/
theorem ncard_involutions_Q_eq_card_twoPoint (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) :
    (involutions (Q : Set G)).ncard = Nat.card (twoPoint H t) := by
  rw [ncard_involutions_Q_eq h hz, ← ncard_involutions_H_eq_card_twoPoint h hz]

/-- The set of involutions of `Q` is contained in `Q ∖ {1}`. -/
theorem involutions_Q_subset (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) :
    (involutions (Q : Set G)) ⊆ (Q : Set G) \ {1} := by
  intro u hu
  simp only [involutions, Set.mem_setOf_eq] at hu
  refine ⟨hu.1, ?_⟩
  intro h1
  rw [Set.mem_singleton_iff] at h1
  exact absurd (h1 ▸ hu.2) (by norm_num)

/-! ## The reduction: the bound is equivalent to `Q` being elementary abelian -/

/-- Pure arithmetic: if `d ∣ n - 1`, `n` is even and `2d + 1 ≥ n` with `d, n > 0`, then
`n = d + 1`.  (`n - 1 = k d` and `k ≤ 2`; `k = 2` gives the odd value `n = 2d + 1`.) -/
theorem arith_card_eq (d n : ℕ) (hd : 0 < d) (hn : 0 < n) (hdiv : d ∣ n - 1)
    (heven : Even n) (hbound : 2 * d + 1 ≥ n) : n = d + 1 := by
  obtain ⟨k, hk⟩ := hdiv
  have hn_eq : n = d * k + 1 := by omega
  have hstep : d * k ≤ 2 * d := by omega
  rw [mul_comm 2 d] at hstep
  have hk_le : k ≤ 2 := Nat.le_of_mul_le_mul_left hstep hd
  have hk_ne0 : k ≠ 0 := by
    intro h0
    have h1 : n = 1 := by rw [hn_eq, h0, mul_zero, zero_add]
    rw [h1] at heven
    exact absurd heven (by norm_num)
  have hk_ne2 : k ≠ 2 := by
    intro h2
    have hn' : n = 2 * d + 1 := by rw [hn_eq, h2, mul_comm d 2]
    have hodd : Odd (2 * d + 1) := ⟨d, rfl⟩
    exact absurd (hn' ▸ heven) (Nat.not_even_iff_odd.mpr hodd)
  have hk1 : k = 1 := by omega
  rw [hn_eq, hk1, mul_one]

/-- Pure arithmetic: `n - 1 = d` (with `n > 0`) gives `2d + 1 ≥ n`. -/
theorem arith_bound_of_card_eq (d n : ℕ) (hn : 0 < n) (h : n - 1 = d) : 2 * d + 1 ≥ n := by
  have : n = d + 1 := by omega
  omega

/-- **The reduction.**  Under `IsSplitRankOne H Q t` and `IsZassenhaus H`, Feit's bound
`2|D| + 1 ≥ |Q|` holds if and only if `Q` is elementary abelian.

The two workspace ingredients are `|D| ∣ |Q| - 1` (freeness of `D` on `Q#`) and `|Q|` even; then
`|Q| - 1 = k|D|` and the bound says `k ≤ 2`, while `k = 2` would force the odd value
`|Q| = 2|D| + 1`.  So the bound says `|Q| = |D| + 1 = |Inv(Q)| + 1`, i.e. that the involutions
of `Q` exhaust `Q#`. -/
theorem feit_bound_iff_elementary (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) :
    (2 * Nat.card (twoPoint H t) + 1 ≥ Nat.card Q) ↔ (∀ x ∈ Q, x ^ 2 = 1) := by
  have hdiv : Nat.card (twoPoint H t) ∣ Nat.card Q - 1 :=
    Work.ZassenhausTwoGroup.card_twoPoint_dvd h hz
  have heven : Even (Nat.card Q) := Work.ZassenhausTwoGroup.even_card_Q h
  have hdpos : 0 < Nat.card (twoPoint H t) := Nat.card_pos
  have hnpos : 0 < Nat.card Q := Nat.card_pos
  have hInvQ : (involutions (Q : Set G)).ncard = Nat.card (twoPoint H t) :=
    ncard_involutions_Q_eq_card_twoPoint h hz
  have hsub : (involutions (Q : Set G)) ⊆ (Q : Set G) \ {1} :=
    involutions_Q_subset h hz
  have hcard_sub : ((Q : Set G) \ {1}).ncard = Nat.card Q - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem (Q.one_mem : (1 : G) ∈ (Q : Set G))]
    have haux : Nat.card Q = (Q : Set G).ncard := Nat.card_coe_set_eq (Q : Set G)
    rw [haux]
  constructor
  · -- the bound forces `|Q| = |D| + 1`, hence `Inv(Q) = Q \ {1}`
    intro hbound
    have hnd : Nat.card Q = Nat.card (twoPoint H t) + 1 :=
      arith_card_eq _ _ hdpos hnpos hdiv heven hbound
    have heq : (involutions (Q : Set G)) = (Q : Set G) \ {1} :=
      Set.eq_of_subset_of_ncard_le hsub (by
        rw [hcard_sub, hnd, hInvQ]
        omega)
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_pow 2
    · have hx' : x ∈ (Q : Set G) \ {1} := ⟨hx, by simpa using hx1⟩
      have hx'' : x ∈ involutions (Q : Set G) := heq ▸ hx'
      simp only [involutions, Set.mem_setOf_eq] at hx''
      rw [← hx''.2]; exact pow_orderOf_eq_one x
  · -- `Q` elementary abelian makes the involutions of `Q` exactly `Q \ {1}`
    intro helem
    have hset : (Q : Set G) \ {1} ⊆ involutions (Q : Set G) := by
      intro u hu
      refine ⟨hu.1, ?_⟩
      have hu1 : u ≠ 1 := by
        intro h1
        exact hu.2 (by rw [Set.mem_singleton_iff]; exact h1)
      have h2 : u ^ 2 = 1 := helem u hu.1
      have hdvd : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hu1
      · exact h1
    have heq : (involutions (Q : Set G)) = (Q : Set G) \ {1} :=
      Set.eq_of_subset_of_ncard_le hsub (Set.ncard_le_ncard hset (Set.toFinite _))
    have hnd : Nat.card Q - 1 = Nat.card (twoPoint H t) := by
      have hc := hcard_sub
      rw [← heq, hInvQ] at hc
      exact hc.symm
    exact arith_bound_of_card_eq _ _ hnpos hnd

/-- The `⟸` half, isolated: if `Q` is elementary abelian then Feit's bound holds. -/
theorem feit_bound_of_elementary (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H)
    (helem : ∀ x ∈ Q, x ^ 2 = 1) :
    2 * Nat.card (twoPoint H t) + 1 ≥ Nat.card Q :=
  (feit_bound_iff_elementary h hz).mpr helem

/-- The `⟹` half, isolated: Feit's bound forces `Q` to be elementary abelian. -/
theorem elementary_of_feit_bound (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H)
    (hbound : 2 * Nat.card (twoPoint H t) + 1 ≥ Nat.card Q) :
    ∀ x ∈ Q, x ^ 2 = 1 :=
  (feit_bound_iff_elementary h hz).mp hbound

end Work.ZassenhausPSL2.ZData
