import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.sec1_lemma3_struct_commute
import Submission.Work.ThmF.Bender.DTransitiveInv
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThreePoints.P3NeBot.map_subtype_twoPoint_subgroupOf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

/-- If the involutions of a subgroup `S` commute pairwise, then `{1} ∪ Inv(S)` is a subgroup of
`G` with carrier exactly that set: it is an elementary abelian 2-subgroup. -/
theorem aux_exists_subgroup_insert_involutions {G : Type} [Group G] {S : Subgroup G}
    (hc : ∀ u ∈ Submission.Blueprint.involutions (S : Set G),
      ∀ v ∈ Submission.Blueprint.involutions (S : Set G), u * v = v * u) :
    ∃ Q : Subgroup G,
      (Q : Set G) = insert 1 (Submission.Blueprint.involutions (S : Set G)) ∧
      (∀ x ∈ Q, x * x = 1) ∧ (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) := by
  classical
  have hsq : ∀ u ∈ Submission.Blueprint.involutions (S : Set G), u * u = 1 := by
    intro u hu
    have h := pow_orderOf_eq_one u
    rw [hu.2, pow_two] at h
    exact h
  have hmul : ∀ {x y : G}, x ∈ insert 1 (Submission.Blueprint.involutions (S : Set G)) →
      y ∈ insert 1 (Submission.Blueprint.involutions (S : Set G)) →
      x * y ∈ insert 1 (Submission.Blueprint.involutions (S : Set G)) := by
    intro x y hx hy
    rcases hx with rfl | hx
    · simpa using hy
    rcases hy with rfl | hy
    · rw [mul_one]; exact Or.inr hx
    have hxy : x * y = y * x := hc x hx y hy
    have h2 : (x * y) * (x * y) = 1 := by
      calc (x * y) * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [← hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [hsq x hx, hsq y hy, one_mul]
    by_cases h1 : x * y = 1
    · rw [h1]; exact Or.inl rfl
    · exact Or.inr ⟨S.mul_mem hx.1 hy.1, orderOf_eq_prime (by rwa [pow_two]) h1⟩
  have hinv : ∀ {x : G}, x ∈ insert 1 (Submission.Blueprint.involutions (S : Set G)) →
      x⁻¹ ∈ insert 1 (Submission.Blueprint.involutions (S : Set G)) := by
    intro x hx
    rcases hx with rfl | hx
    · simp
    · have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
      rw [hxinv]; exact Or.inr hx
  refine ⟨{ carrier := insert 1 (Submission.Blueprint.involutions (S : Set G)),
            mul_mem' := hmul,
            one_mem' := Or.inl rfl,
            inv_mem' := hinv }, rfl, ?_, ?_⟩
  · intro x hx
    rcases hx with rfl | hx
    · simp
    · exact hsq x hx
  · intro x hx y hy
    rcases hx with rfl | hx
    · simp
    rcases hy with rfl | hy
    · simp
    · exact hc x hx y hy

/-- Peterfalvi I Ch. II §4 Prop. 1 (b) at `F = N_G(X)`, `g = 1`: for `1 ≠ X ≤ V = C_D(t)`,
`H ⊓ N_G(X)` is strongly embedded in `N_G(X)`. -/
theorem aux_isStronglyEmbedded_inf_normalizer (hC4 : Submission.Blueprint.ChIIFourProp)
    {G : Type} [Group G] [Finite G] (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX : X ≠ ⊥)
    (hXV : X ≤ Submission.Blueprint.centD H t) :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded
      ((H ⊓ Subgroup.normalizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))) := by
  have hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard :=
    Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_of_le_centD hH ht htH hXV
  have hInv : Submission.Blueprint.involutions
      (Subgroup.centralizer (X : Set G) : Set G) ⊆ (Subgroup.normalizer (X : Set G) : Set G) :=
    fun y hy => Subgroup.centralizer_le_normalizer (X : Set G) hy.1
  have hXH : X ≤ Submission.Blueprint.conj (1 : G) H := by
    rw [Work.DoubleTransitivity.conj_one]
    intro y hy
    exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hXV hy)).1).1
  have h := (hC4 G hS H hH t ht htH).1 X (Subgroup.normalizer (X : Set G)) hX3 hInv le_rfl 1 hXH
  rw [Work.DoubleTransitivity.conj_one] at h
  have hh := congrArg (fun S : Subgroup G => S.subgroupOf (Subgroup.normalizer (X : Set G)))
      (inf_comm H (Subgroup.normalizer (X : Set G)))
  rw [hh]
  exact h

/-- Transport of `|J(D,t)| = |Inv(H)|` (Peterfalvi I Ch. I §2 Prop. 1 (c)) to a subgroup `M`:
if `H ⊓ M` is strongly embedded in `M`, then `Kset D t ∩ M` and the involutions of `H ⊓ M`
have the same cardinality. -/
theorem aux_ncard_Kset_inter {G : Type} [Group G] [Finite G]
    {H M : Subgroup G} {t : G} (htM : t ∈ M) (ht : orderOf t = 2) (htH : t ∉ H)
    (hse : LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((H ⊓ M).subgroupOf M)) :
    (Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t ∩ (M : Set G)).ncard =
      (Submission.Blueprint.involutions ((H ⊓ M : Subgroup G) : Set G)).ncard := by
  classical
  have ht'2 : orderOf (⟨t, htM⟩ : ↥M) = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have ht'H : (⟨t, htM⟩ : ↥M) ∉ (H ⊓ M).subgroupOf M :=
    fun h => htH (Subgroup.mem_subgroupOf.mp h).1
  have hcard := Work.ThmF.Bender.cardKsetEqInv (G := ↥M) hse ht'2 ht'H
  have hH'eq : (H ⊓ M).subgroupOf M = H.subgroupOf M := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
  have htp : (Submission.Blueprint.twoPoint ((H ⊓ M).subgroupOf M) (⟨t, htM⟩ : ↥M)).map
        (Subgroup.subtype M) = M ⊓ Submission.Blueprint.twoPoint H t := by
    rw [hH'eq]
    exact Work.ThreePoints.P3NeBot.map_subtype_twoPoint_subgroupOf (F := M) (H := H)
      (⟨t, htM⟩ : ↥M)
  have himgK : (Work.ThmF.Kset ((H ⊓ M).subgroupOf M) (⟨t, htM⟩ : ↥M)).image (Subgroup.subtype M)
      = Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t ∩ (M : Set G) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Work.ThmF.mem_Kset_iff] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have hx1M : (x : G) ∈ M ⊓ Submission.Blueprint.twoPoint H t := by
        have hmem : (x : G) ∈ (Submission.Blueprint.twoPoint ((H ⊓ M).subgroupOf M)
            (⟨t, htM⟩ : ↥M)).map (Subgroup.subtype M) := ⟨x, hx1, rfl⟩
        rwa [htp] at hmem
      have hx2' : t * (x : G) * t⁻¹ = (x : G)⁻¹ := by
        have := congrArg (Subgroup.subtype M) hx2
        simpa using this
      exact ⟨⟨hx1M.2, hx2'⟩, x.2⟩
    · rintro ⟨hy1, hy2⟩
      refine ⟨⟨y, hy2⟩, ?_, rfl⟩
      rw [Work.ThmF.mem_Kset_iff]
      refine ⟨?_, ?_⟩
      · have hmem : (y : G) ∈ (Submission.Blueprint.twoPoint ((H ⊓ M).subgroupOf M)
            (⟨t, htM⟩ : ↥M)).map (Subgroup.subtype M) := by
          rw [htp]; exact ⟨hy2, hy1.1⟩
        obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hmem
        have hz' : z = (⟨y, hy2⟩ : ↥M) := Subtype.ext hzy
        rw [hz'] at hz
        exact hz
      · apply Subtype.coe_injective
        show t * y * t⁻¹ = y⁻¹
        exact hy1.2
  have himgI : (Submission.Blueprint.involutions ((H ⊓ M).subgroupOf M : Set ↥M)).image
        (Subgroup.subtype M) =
      Submission.Blueprint.involutions ((H ⊓ M : Subgroup G) : Set G) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨Subgroup.mem_subgroupOf.mp hx.1, ?_⟩
      have hx2' : orderOf ((x : G)) = 2 := by rw [Subgroup.orderOf_coe]; exact hx.2
      exact hx2'
    · rintro ⟨hy1, hy2⟩
      refine ⟨⟨y, hy1.2⟩, ⟨?_, ?_⟩, rfl⟩
      · exact Subgroup.mem_subgroupOf.mpr hy1
      · rw [Subgroup.orderOf_mk]; exact hy2
  have hK := Set.InjOn.ncard_image ((Subgroup.subtype_injective M).injOn
    (s := Work.ThmF.Kset ((H ⊓ M).subgroupOf M) (⟨t, htM⟩ : ↥M)))
  rw [himgK] at hK
  have hI := Set.InjOn.ncard_image ((Subgroup.subtype_injective M).injOn
    (s := Submission.Blueprint.involutions ((H ⊓ M).subgroupOf M : Set ↥M)))
  rw [himgI] at hI
  rw [hK, hcard, ← hI]

/-- Peterfalvi I Ch. I §2 Prop. 2 (b) transported to `M`: `Kset D t ∩ M` acts regularly by
conjugation on the involutions of `H ⊓ M` (given the cardinality input). -/
theorem aux_regular_of_cardKset {G : Type} [Group G] [Finite G]
    {H M : Subgroup G} {t : G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    (ht : orderOf t = 2) (htH : t ∉ H)
    (hcard : (Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t ∩
        (M : Set G)).ncard =
      (Submission.Blueprint.involutions ((H ⊓ M : Subgroup G) : Set G)).ncard) :
    ∀ a ∈ Submission.Blueprint.involutions ((H ⊓ M : Subgroup G) : Set G), a ≠ 1 →
      ∀ b ∈ Submission.Blueprint.involutions ((H ⊓ M : Subgroup G) : Set G), b ≠ 1 →
      ∃! k : G, k ∈ Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t ∩
        (M : Set G) ∧ k * a * k⁻¹ = b := by
  intro a ha _ b hb _
  have haH : a ∈ H := ha.1.1
  have ha2 : orderOf a = 2 := ha.2
  have hmem : ∀ k ∈ Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t ∩
      (M : Set G),
      k * a * k⁻¹ ∈ Submission.Blueprint.involutions ((H ⊓ M : Subgroup G) : Set G) := by
    intro k hk
    have hkH : k ∈ H := hk.1.1.1
    have hkM : k ∈ M := hk.2
    refine ⟨(H ⊓ M).mul_mem ((H ⊓ M).mul_mem ⟨hkH, hkM⟩ ha.1) ((H ⊓ M).inv_mem ⟨hkH, hkM⟩), ?_⟩
    rw [Work.ThmF.Bender.orderOf_conj_eq k a, ha2]
  have hinj : Set.InjOn (fun k => k * a * k⁻¹)
      (Work.NormalComplement.Kset (Submission.Blueprint.twoPoint H t) t ∩ (M : Set G)) :=
    (Work.ThmF.Bender.Kset_conj_injective hH ht htH haH ha2).mono Set.inter_subset_left
  have himg_sub : (fun k => k * a * k⁻¹) '' (Work.NormalComplement.Kset
        (Submission.Blueprint.twoPoint H t) t ∩ (M : Set G)) ⊆
      Submission.Blueprint.involutions ((H ⊓ M : Subgroup G) : Set G) :=
    fun y hy => by
      obtain ⟨k, hk, rfl⟩ := hy
      exact hmem k hk
  have heq : (fun k => k * a * k⁻¹) '' (Work.NormalComplement.Kset
        (Submission.Blueprint.twoPoint H t) t ∩ (M : Set G)) =
      Submission.Blueprint.involutions ((H ⊓ M : Subgroup G) : Set G) :=
    Set.eq_of_subset_of_ncard_le himg_sub
      (le_of_eq ((Set.InjOn.ncard_image hinj).trans hcard).symm)
  have hb' : b ∈ (fun k => k * a * k⁻¹) '' (Work.NormalComplement.Kset
      (Submission.Blueprint.twoPoint H t) t ∩ (M : Set G)) := by
    rw [heq]; exact hb
  obtain ⟨k, hk, hkb⟩ := hb'
  exact ⟨k, ⟨hk, hkb⟩, fun y hy => hinj hy.1 hk (hy.2.trans hkb.symm)⟩

/-- **Peterfalvi I Ch. III §1 Lemma 3, structural part (p. 175).** For `1 ≠ X ≤ V = C_D(t)` with
`N_K(X) ≠ 1`, the group `Q = {1} ∪ Inv(N_H(X))` is an elementary abelian 2-subgroup and
`K₁ = N_K(X) = C_K(X)` is a cyclic subgroup acting regularly on `Q#`. -/
theorem sec4_lm3_kapp_structure (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hMod : Submission.Blueprint.ModelFactsProp)
    {G : Type} [Group G] [Finite G] (hS : Submission.Blueprint.Situation G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX : X ≠ ⊥)
    (hXV : X ≤ Submission.Blueprint.centD H t)
    (hNK : ∃ k ∈ Work.NormalComplement.Design.NK H t X, k ≠ 1) :
    ∃ Q K₁ : Subgroup G,
      (Q : Set G) = insert 1 (Submission.Blueprint.involutions
        ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G)) ∧
      (K₁ : Set G) = Work.NormalComplement.Design.NK H t X ∧
      Work.NormalComplement.Design.NK H t X = Work.NormalComplement.Design.CK H t X ∧
      IsCyclic ↥K₁ ∧
      (∀ x ∈ Q, x * x = 1) ∧
      (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) ∧
      (∀ a ∈ Q, a ≠ 1 → ∀ b ∈ Q, b ≠ 1 →
        ∃! k : G, k ∈ K₁ ∧ k * a * k⁻¹ = b) ∧
      Q ≠ ⊥ := by
  classical
  have htM : t ∈ Subgroup.normalizer (X : Set G) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' := hXV hy
    rw [Subgroup.mem_inf] at hy'
    exact Subgroup.mem_centralizer_singleton_iff.mp hy'.2
  have hse : LeanEval.GroupTheory.Defs.IsStronglyEmbedded
      ((H ⊓ Subgroup.normalizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))) :=
    aux_isStronglyEmbedded_inf_normalizer hC4 hS hH ht htH hX hXV
  have hcard := aux_ncard_Kset_inter (H := H) (M := Subgroup.normalizer (X : Set G)) htM ht htH hse
  have hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t,
      k ≠ 1 ∧ k ∈ Subgroup.normalizer (X : Set G) := by
    obtain ⟨k, hk, hk1⟩ := hNK
    exact ⟨k, hk.1, hk1, hk.2⟩
  have hP3 := (hC4 G hS H hH t ht htH).2.2.2.1
  obtain ⟨K₁, hK1car, hK1cent, hK1cyc⟩ := (hP3 X hX hXV hNX).2.2.2
  have hNKeqCK : Design.NK H t X = Design.CK H t X := by
    ext y
    constructor
    · intro hy
      refine ⟨hy.1, hK1cent ?_⟩
      change y ∈ (K₁ : Set G)
      rw [hK1car]
      exact hy
    · intro hy
      exact ⟨hy.1, Subgroup.centralizer_le_normalizer (X : Set G) hy.2⟩
  obtain ⟨Q, hQcar, hQsq, hQcomm⟩ := aux_exists_subgroup_insert_involutions
    (S := H ⊓ Subgroup.normalizer (X : Set G))
    (fun u hu v hv => sec1_lemma3_struct_commute hC4 hMod hS hH ht htH hX hXV hNK u hu v hv)
  have hQne : Q ≠ ⊥ := by
    obtain ⟨u, huH', hu2⟩ := Work.ThmF.Bender.exists_involution_mem_of_isStronglyEmbedded hse
    intro hbot
    have huQ : (u : G) ∈ Q := by
      change (u : G) ∈ (Q : Set G)
      rw [hQcar]
      refine Or.inr ⟨Subgroup.mem_subgroupOf.mp huH', ?_⟩
      have hu2' : orderOf ((u : G)) = 2 := by rw [Subgroup.orderOf_coe]; exact hu2
      exact hu2'
    rw [hbot] at huQ
    have h1 : (u : G) = 1 := Subgroup.mem_bot.mp huQ
    have h2 : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu2
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hreg : ∀ a ∈ Q, a ≠ 1 → ∀ b ∈ Q, b ≠ 1 →
      ∃! k : G, k ∈ K₁ ∧ k * a * k⁻¹ = b := by
    intro a ha ha1 b hb hb1
    have haI : a ∈ Submission.Blueprint.involutions
        ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) := by
      have ha' : a ∈ (Q : Set G) := ha
      rw [hQcar] at ha'
      rcases ha' with rfl | ha'
      · exact absurd rfl ha1
      · exact ha'
    have hbI : b ∈ Submission.Blueprint.involutions
        ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) := by
      have hb' : b ∈ (Q : Set G) := hb
      rw [hQcar] at hb'
      rcases hb' with rfl | hb'
      · exact absurd rfl hb1
      · exact hb'
    obtain ⟨k, hk, huniq⟩ := aux_regular_of_cardKset (H := H)
      (M := Subgroup.normalizer (X : Set G)) hH ht htH hcard a haI ha1 b hbI hb1
    refine ⟨k, ⟨?_, hk.2⟩, ?_⟩
    · change k ∈ (K₁ : Set G)
      rw [hK1car]
      exact hk.1
    · intro y hy
      have hy' : y ∈ (K₁ : Set G) := hy.1
      rw [hK1car] at hy'
      exact huniq y ⟨hy', hy.2⟩
  exact ⟨Q, K₁, hQcar, hK1car, hNKeqCK, hK1cyc, hQsq, hQcomm, hreg, hQne⟩

end Work.NormalComplement
