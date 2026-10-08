import Mathlib
import Submission.Work.ThreePoints.Basic
import Submission.Work.ThreePoints.Omega
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3Sub.OddResidual

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThreePoints.P3Sub.Helpers`

Elementary lemmas used in the proof of Peterfalvi I Ch. II §4 Prop. 3 (a), (b) with a subnormal
`Y`: extraction of a proper normal subgroup from a subnormal chain, and the basic facts about
`O^{2'}` and about the fixed points of a subgroup of `V = C_D(t)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-! ## 1. Subnormal subgroups -/

/-- A subgroup subnormal in `X` is contained in `X`. -/
theorem IsSubnormalIn.le {Y X : Subgroup G} (h : IsSubnormalIn Y X) : Y ≤ X := by
  induction h with
  | refl => exact le_rfl
  | tail _ hbc ih => exact le_trans ih hbc.1

/-- A proper subnormal subgroup of `X` is contained in a proper normal subgroup of `X`
(namely in the second term of a subnormal chain). -/
theorem exists_normal_subgroup_of_subnormal {Y X : Subgroup G} (h : IsSubnormalIn Y X)
    (hne : Y ≠ X) :
    ∃ X₀ : Subgroup G, Y ≤ X₀ ∧ X₀ ≤ X ∧ (X₀.subgroupOf X).Normal ∧ X₀ ≠ X ∧
      IsSubnormalIn Y X₀ := by
  have key : Y ≠ X → ∃ X₀ : Subgroup G, Y ≤ X₀ ∧ X₀ ≤ X ∧ (X₀.subgroupOf X).Normal ∧ X₀ ≠ X ∧
      IsSubnormalIn Y X₀ :=
    Relation.ReflTransGen.head_induction_on h
      (by intro hne'; exact absurd rfl hne')
      (by
        intro a c hac hcX ih hne'
        by_cases hcX' : c = X
        · subst hcX'
          exact ⟨a, le_rfl, hac.1, hac.2, hne', Relation.ReflTransGen.refl⟩
        · obtain ⟨X₀, haX₀, hX₀X, hnorm, hne'', hsub⟩ := ih hcX'
          exact ⟨X₀, le_trans hac.1 haX₀, hX₀X, hnorm, hne'',
            Relation.ReflTransGen.trans
              (Relation.ReflTransGen.tail Relation.ReflTransGen.refl hac) hsub⟩)
  exact key hne

/-! ## 2. Elements of `2`-power order lie in normal subgroups of odd index -/

/-- In a group, an element of `2`-power order lies in every normal subgroup of odd index. -/
theorem mem_of_orderOf_eq_two_pow_of_odd_index {N : Subgroup G} (hN : N.Normal)
    (hodd : Odd N.index) {x : G} {k : ℕ} (hx : orderOf x = 2 ^ k) : x ∈ N := by
  haveI := hN
  have h1 : orderOf (QuotientGroup.mk' N x) ∣ N.index := by
    apply orderOf_dvd_of_pow_eq_one
    exact (QuotientGroup.eq_one_iff (x ^ N.index)).mpr (Subgroup.pow_index_mem N x)
  have h2 : orderOf (QuotientGroup.mk' N x) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← hx, ← map_pow, pow_orderOf_eq_one, map_one]
  have hcop : Nat.Coprime N.index (2 ^ k) := (Nat.coprime_two_right.mpr hodd).pow_right k
  have hcop' : Nat.Coprime (orderOf (QuotientGroup.mk' N x)) N.index :=
    hcop.symm.coprime_dvd_left h2
  have h3 : orderOf (QuotientGroup.mk' N x) = 1 := hcop'.eq_one_of_dvd h1
  exact (QuotientGroup.eq_one_iff x).mp (orderOf_eq_one_iff.mp h3)

/-- An element of `C_G(X)` of `2`-power order lies in `p3F X = O^{2'}(C_G(X))`. -/
theorem mem_p3F_of_two_pow_order {X : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.centralizer (X : Set G)) {k : ℕ} (hord : orderOf x = 2 ^ k) :
    x ∈ p3F X := by
  haveI : Finite ↥(Subgroup.centralizer (X : Set G)) :=
    Finite.of_injective _ (Subgroup.subtype_injective _)
  obtain ⟨hN, hodd, -, -⟩ :=
    oddResidual_basic (G := ↥(Subgroup.centralizer (X : Set G)))
  have hmem : (⟨x, hx⟩ : ↥(Subgroup.centralizer (X : Set G))) ∈
      oddResidual ↥(Subgroup.centralizer (X : Set G)) := by
    refine mem_of_orderOf_eq_two_pow_of_odd_index
      (G := ↥(Subgroup.centralizer (X : Set G))) (k := k) hN hodd ?_
    have hco : orderOf (⟨x, hx⟩ : ↥(Subgroup.centralizer (X : Set G))) = orderOf x :=
      (Subgroup.orderOf_coe ⟨x, hx⟩).symm
    rw [hco]
    exact hord
  exact mem_p3F.mpr ⟨⟨x, hx⟩, hmem, rfl⟩

/-- An involution of `C_G(X)` lies in `p3F X`. -/
theorem mem_p3F_of_involution {X : Subgroup G} {u : G}
    (hu : u ∈ Subgroup.centralizer (X : Set G)) (h2 : orderOf u = 2) : u ∈ p3F X :=
  mem_p3F_of_two_pow_order hu (k := 1) (by rw [h2]; norm_num)

/-- A `2`-subgroup of `C_G(X)` is contained in `O^{2'}(C_G(X))`. -/
theorem mem_p3F_of_isPGroup {X S : Subgroup G} (hS : S ≤ Subgroup.centralizer (X : Set G))
    (h2 : IsPGroup 2 S) : S ≤ p3F X := by
  intro s hs
  have hsub : IsPGroup 2 ↥(Subgroup.zpowers s) := h2.to_le (Subgroup.zpowers_le.mpr hs)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hsub
  refine mem_p3F_of_two_pow_order (hS hs) (k := k) ?_
  rw [← Nat.card_zpowers s]
  exact hk

/-- `p3F X ≤ N_G(X)`. -/
theorem p3F_le_normalizer (X : Subgroup G) :
    p3F X ≤ Subgroup.normalizer (X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff']
  intro n
  have hc : ∀ x ∈ X, x * g = g * x := fun x hx =>
    Subgroup.mem_centralizer_iff.mp (p3F_le_centralizer X hg) x hx
  constructor
  · intro hn
    have h2 : (n * g) * g = (g * n) * g := by
      rw [hc (n * g) hn]; group
    have : n * g = g * n := mul_right_cancel h2
    rw [← this]; exact hn
  · intro hn
    have h2 : g * (n * g) = g * (g * n) := by
      rw [← hc (g * n) hn]; group
    have : n * g = g * n := mul_left_cancel h2
    rw [this]; exact hn

/-! ## 4. The three fixed points of a subgroup of `V = C_D(t)` -/

/-- If `X ≤ C_D(t)` then `X ≤ H` and `X ≤ H^t`. -/
theorem le_of_le_centD {H X : Subgroup G} {t : G} (hX : X ≤ centD H t) :
    X ≤ H ∧ X ≤ conj t H := by
  have h1 : X ≤ twoPoint H t := le_trans hX inf_le_left
  exact ⟨le_trans h1 inf_le_left, le_trans h1 inf_le_right⟩

/-- If `X ≤ C_D(t)` then `X ≤ C_G(t)`. -/
theorem p3sub_centralizer_of_le_centD {H X : Subgroup G} {t : G} (hX : X ≤ centD H t) :
    X ≤ Subgroup.centralizer ({t} : Set G) :=
  le_trans hX inf_le_right

/-- The point `H` of `Ω` is fixed by `X` when `X ≤ C_D(t)`. -/
theorem pt_mem_fixedPts_of_le_centD {H X : Subgroup G} {t : G} (hX : X ≤ centD H t) :
    QuotientGroup.mk (1 : G) ∈ fixedPts H X := by
  rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, conj_one]
  exact (le_of_le_centD hX).1

/-- The point `H^t` of `Ω` is fixed by `X` when `X ≤ C_D(t)`. -/
theorem mk_t_mem_fixedPts_of_le_centD {H X : Subgroup G} {t : G} (hX : X ≤ centD H t) :
    QuotientGroup.mk t ∈ fixedPts H X := by
  rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
  exact (le_of_le_centD hX).2

/-- `V = C_D(t)` fixes at least the three points `H`, `H^t` and the (unique) fixed point of the
involution `t` in `Ω = G ⧸ H`. -/
theorem three_le_ncard_fixedPts_centD {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) : 3 ≤ (fixedPts H (centD H t)).ncard := by
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  set V : Subgroup G := centD H t with hV
  have hVH : V ≤ H := (le_of_le_centD (le_refl V)).1
  have hVt : V ≤ conj t H := (le_of_le_centD (le_refl V)).2
  have hmem1 : ((1 : G) : G ⧸ H) ∈ fixedPts H V := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, conj_one]
    exact hVH
  have hmemt : (t : G ⧸ H) ∈ fixedPts H V := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
    exact hVt
  obtain ⟨ω, hω⟩ := Set.ncard_eq_one.mp (ncard_fixedPts_zpowers hH ht)
  have hmemω : ω ∈ fixedPts H V := by
    rw [mem_fixedPts_iff_le_stabilizer]
    intro v hv
    rw [MulAction.mem_stabilizer_iff]
    have hvC : v ∈ Subgroup.centralizer ({t} : Set G) :=
      p3sub_centralizer_of_le_centD (le_refl V) hv
    have hvt : v * t = t * v := Subgroup.mem_centralizer_singleton_iff.mp hvC
    have htω : t • ω = ω := by
      have hmem : ω ∈ fixedPts H (Subgroup.zpowers t) := by rw [hω]; exact Set.mem_singleton ω
      exact mem_fixedPts.mp hmem t (Subgroup.mem_zpowers t)
    have htvω : t • (v • ω) = v • ω := by rw [← mul_smul, ← hvt, mul_smul, htω]
    have hmem : v • ω ∈ fixedPts H (Subgroup.zpowers t) := by
      rw [mem_fixedPts_iff_le_stabilizer, Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
      exact htvω
    rw [hω] at hmem
    simpa using hmem
  have h1t : ((1 : G) : G ⧸ H) ≠ (t : G ⧸ H) := by
    intro hcon
    rw [QuotientGroup.eq] at hcon
    exact htH (by simpa using hcon)
  have h1notmem : ((1 : G) : G ⧸ H) ∉ fixedPts H (Subgroup.zpowers t) := by
    intro hmem
    have h := mem_fixedPts.mp hmem t (Subgroup.mem_zpowers t)
    have h' : ((1 : G) : G ⧸ H) = (t : G ⧸ H) := by simpa [smul_mk] using h.symm
    exact h1t h'
  have h1ω : ((1 : G) : G ⧸ H) ≠ ω := by
    intro hcon
    have hmem : ω ∈ fixedPts H (Subgroup.zpowers t) := by rw [hω]; exact Set.mem_singleton ω
    rw [← hcon] at hmem
    exact h1notmem hmem
  have htnotmem : (t : G ⧸ H) ∉ fixedPts H (Subgroup.zpowers t) := by
    intro hmem
    have h := mem_fixedPts.mp hmem t (Subgroup.mem_zpowers t)
    have h' : ((1 : G) : G ⧸ H) = (t : G ⧸ H) := by simpa [smul_mk, ht2] using h
    exact h1t h'
  have htω : (t : G ⧸ H) ≠ ω := by
    intro hcon
    have hmem : ω ∈ fixedPts H (Subgroup.zpowers t) := by rw [hω]; exact Set.mem_singleton ω
    rw [← hcon] at hmem
    exact htnotmem hmem
  have hsub : ({((1 : G) : G ⧸ H), (t : G ⧸ H), ω} : Set (G ⧸ H)) ⊆ fixedPts H V := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hmem1
    · exact hmemt
    · exact hmemω
  have hcard : ({((1 : G) : G ⧸ H), (t : G ⧸ H), ω} : Set (G ⧸ H)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [h1t, h1ω]),
      Set.ncard_insert_of_notMem (by simp [htω]), Set.ncard_singleton]
  calc 3 = _ := hcard.symm
    _ ≤ (fixedPts H V).ncard := Set.ncard_le_ncard hsub

/-- For `X ≤ C_D(t)`, `|Ω_X| ≥ 3`. -/
theorem three_le_ncard_fixedPts_of_le_centD {H X : Subgroup G} (hH : IsStronglyEmbedded H)
    {t : G} (ht : orderOf t = 2) (htH : t ∉ H) (hX : X ≤ centD H t) :
    3 ≤ (fixedPts H X).ncard :=
  le_trans (three_le_ncard_fixedPts_centD hH ht htH) (Set.ncard_le_ncard (fixedPts_mono hX))

/-- For `X ≤ C_D(t)`, the involution `t` lies in `p3F X`. -/
theorem t_mem_p3F {H X : Subgroup G} {t : G} (hX : X ≤ centD H t) (ht : orderOf t = 2) :
    t ∈ p3F X := by
  refine mem_p3F_of_involution ?_ ht
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hxt : x ∈ Subgroup.centralizer ({t} : Set G) := p3sub_centralizer_of_le_centD hX hx
  exact Subgroup.mem_centralizer_singleton_iff.mp hxt

/-- A subgroup containing an involution has even order. -/
theorem even_card_of_mem_involution {C : Subgroup G} {u : G} (hu : u ∈ C) (h2 : orderOf u = 2) :
    Even (Nat.card C) := by
  have hdvd : orderOf (⟨u, hu⟩ : ↥C) ∣ Nat.card ↥C := orderOf_dvd_natCard _
  have hco : orderOf (⟨u, hu⟩ : ↥C) = orderOf u := (Subgroup.orderOf_coe ⟨u, hu⟩).symm
  rw [hco, h2] at hdvd
  exact even_iff_two_dvd.mpr hdvd

/-- An even-order subgroup contains an element of order `2` (Cauchy for `p = 2`). -/
theorem exists_orderOf_two_of_even_card {C : Subgroup G} (h : Even (Nat.card C)) :
    ∃ u ∈ C, orderOf u = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp h)
  refine ⟨(u : G), u.2, ?_⟩
  rw [show orderOf ((u : G)) = orderOf u from Subgroup.orderOf_coe u]
  exact hu

end Work.ThreePoints
