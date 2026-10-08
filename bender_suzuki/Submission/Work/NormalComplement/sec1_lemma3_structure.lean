import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.NormalComplement.prop2b_conj_into_centD
import Submission.Work.NormalComplement.section3_prop2
import Submission.Work.NormalComplement.appI_five_d_corrected
import Submission.Work.NormalComplement.appI_four
import Submission.Work.NormalComplement.bender_prelim
import Submission.Work.ThreePoints.P3Sub.Helpers
import Submission.Work.ThreePoints.P3NeBot.map_subtype_twoPoint_subgroupOf
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.NormalComplement.involutions_commute_of_hC4

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement


/-! ## Elementary helpers -/

theorem orderOf_eq_two_of_mul_self_eq_one {G : Type*} [Group G] {x : G} (h : x * x = 1)
    (hx : x ≠ 1) : orderOf x = 2 := by
  have h2 : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
  · exact absurd (orderOf_eq_one_iff.mp h1) hx
  · exact h1

theorem ncard_involutions_subgroupOf {G : Type*} [Group G] {F H : Subgroup G} :
    (Submission.Blueprint.involutions ((H.subgroupOf F) : Set ↥F)).ncard =
      (Submission.Blueprint.involutions ((H ⊓ F : Subgroup G) : Set G)).ncard := by
  classical
  refine Set.ncard_congr (f := fun x _ => (x : G)) ?_ ?_ ?_
  · rintro x ⟨hx1, hx2⟩
    have hmem : (x : G) ∈ (H ⊓ F : Subgroup G) :=
      ⟨Subgroup.mem_subgroupOf.mp hx1, x.2⟩
    exact ⟨hmem, (Subgroup.orderOf_coe x).trans hx2⟩
  · intro x y _ _ hxy
    exact Subtype.ext hxy
  · rintro b ⟨hb1, hb2⟩
    obtain ⟨hbH, hbF⟩ := Subgroup.mem_inf.mp hb1
    have hmem : (⟨b, hbF⟩ : ↥F) ∈ (H.subgroupOf F : Set ↥F) := Subgroup.mem_subgroupOf.mpr hbH
    exact ⟨⟨b, hbF⟩, ⟨hmem, (Subgroup.orderOf_coe (⟨b, hbF⟩ : ↥F)).symm.trans hb2⟩, rfl⟩

theorem ncard_Kset_subgroupOf {G : Type} [Group G] {F H : Subgroup G} {t : G} (htF : t ∈ F) :
    (Work.ThmF.Kset (H.subgroupOf F) ⟨t, htF⟩).ncard =
      ((Work.ThmF.Kset H t) ∩ (F : Set G)).ncard := by
  classical
  have hmap := Work.ThreePoints.P3NeBot.map_subtype_twoPoint_subgroupOf (F := F) (H := H) ⟨t, htF⟩
  refine Set.ncard_congr (f := fun x _ => (x : G)) ?_ ?_ ?_
  · rintro x ⟨hx1, hx2⟩
    have hx2' : t * (x : G) * t⁻¹ = ((x : G))⁻¹ := by
      have h := congrArg (fun y : ↥F => (y : G)) hx2
      simpa using h
    have hmem : (x : G) ∈ (Submission.Blueprint.twoPoint (H.subgroupOf F) ⟨t, htF⟩).map F.subtype :=
      ⟨x, hx1, rfl⟩
    rw [hmap] at hmem
    exact ⟨⟨(Subgroup.mem_inf.mp hmem).2, hx2'⟩, x.2⟩
  · intro x y _ _ hxy
    exact Subtype.ext hxy
  · rintro b ⟨hb, hbF⟩
    obtain ⟨hbmem, hbconj⟩ := Work.ThmF.mem_Kset_iff.mp hb
    refine ⟨⟨b, hbF⟩, ⟨?_, ?_⟩, rfl⟩
    · have hm : b ∈ (Submission.Blueprint.twoPoint (H.subgroupOf F) ⟨t, htF⟩).map F.subtype := by
        rw [hmap]
        exact ⟨hbF, hbmem⟩
      obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.mp hm
      have hyy : y = (⟨b, hbF⟩ : ↥F) := Subtype.ext hyb
      rwa [hyy] at hy
    · apply Subtype.ext
      simpa using hbconj

/-- If an abelian subgroup `K ≤ G` acts transitively by conjugation on a set `S` containing
`x₀`, and `y` commutes with `K`, then the conjugation action of `y` on `S` is the action of some
`k₀ ∈ K`. -/
theorem exists_conj_eq_of_commute_regular {G : Type*} [Group G] {K : Subgroup G} {S : Set G}
    {y x₀ : G} (hx₀ : x₀ ∈ S) (hyS : ∀ x ∈ S, y * x * y⁻¹ ∈ S)
    (htrans : ∀ x ∈ S, ∃ k ∈ K, k * x₀ * k⁻¹ = x)
    (habel : ∀ k ∈ K, ∀ k' ∈ K, k * k' = k' * k)
    (hcomm : ∀ k ∈ K, y * k = k * y) :
    ∃ k₀ ∈ K, ∀ x ∈ S, y * x * y⁻¹ = k₀ * x * k₀⁻¹ := by
  obtain ⟨k₀, hk₀K, hk₀⟩ := htrans (y * x₀ * y⁻¹) (hyS x₀ hx₀)
  refine ⟨k₀, hk₀K, fun x hx => ?_⟩
  obtain ⟨k, hkK, hk⟩ := htrans x hx
  have hyk : y * k * y⁻¹ = k := by rw [hcomm k hkK]; group
  have hyki : y * k⁻¹ * y⁻¹ = k⁻¹ := by rw [hcomm k⁻¹ (K.inv_mem hkK)]; group
  calc y * x * y⁻¹ = y * (k * x₀ * k⁻¹) * y⁻¹ := by rw [hk]
    _ = (y * k * y⁻¹) * (y * x₀ * y⁻¹) * (y * k⁻¹ * y⁻¹) := by group
    _ = k * (k₀ * x₀ * k₀⁻¹) * k⁻¹ := by rw [hyk, hyki, hk₀]
    _ = (k * k₀) * x₀ * (k * k₀)⁻¹ := by group
    _ = (k₀ * k) * x₀ * (k₀ * k)⁻¹ := by rw [habel k hkK k₀ hk₀K]
    _ = k₀ * (k * x₀ * k⁻¹) * k₀⁻¹ := by group
    _ = k₀ * x * k₀⁻¹ := by rw [hk]

/-- An element of `Kset D t ∩ V` is trivial: it is inverted by `t` and centralised by `t`, and
`D = H ∩ H^t` has odd order. -/
theorem eq_one_of_mem_Kset_and_centD {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G}
    (hH : IsStronglyEmbedded H) (htH : t ∉ H) {y : G}
    (hy : y ∈ invertedBy (twoPoint H t) t) (hyV : y ∈ centD H t) : y = 1 := by
  have hDodd : Odd (Nat.card (twoPoint H t)) := hH.2.2 t htH
  have hyinv : t * y * t⁻¹ = y⁻¹ := hy.2
  have hyfix : t * y * t⁻¹ = y := by
    have h := (Work.ThreePoints.mem_centD.mp hyV).2.2
    calc t * y * t⁻¹ = y * t * t⁻¹ := by rw [h]
      _ = y := by group
  have hsq : y * y = 1 := by
    have hthis : y = y⁻¹ := by rw [← hyinv, hyfix]
    nth_rewrite 2 [hthis]
    exact mul_inv_cancel y
  have hdvd : orderOf y ∣ Nat.card (twoPoint H t) := Subgroup.orderOf_dvd_natCard _ hy.1
  have h2dvd : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
  have hone : orderOf y = 1 := by
    have := Nat.dvd_gcd h2dvd hdvd
    rw [Nat.coprime_two_left.mpr hDodd] at this
    exact Nat.dvd_one.mp this
  exact orderOf_eq_one_iff.mp hone

/-- If `K ≤ H` is a subgroup of `H` with `|K| = |Inv H|` acting freely on `Inv H` by
conjugation, then it acts transitively on `Inv H`.  (Variant of
`Work.NormalComplement.Kset_transitive_on_involutions` with the hypothesis `K ⊆ H` instead of
`K = Kset`.) -/
theorem transitive_conj_on_involutions {G : Type} [Group G] [Finite G] {H K : Subgroup G}
    (hKH : (K : Set G) ⊆ (H : Set G))
    (hcard : (K : Set G).ncard = (Submission.Blueprint.involutions (H : Set G)).ncard)
    (hfree : ∀ k ∈ K, k ≠ 1 → ∀ u ∈ Submission.Blueprint.involutions (H : Set G),
      k * u * k⁻¹ ≠ u) :
    ∀ u ∈ Submission.Blueprint.involutions (H : Set G),
      ∀ v ∈ Submission.Blueprint.involutions (H : Set G), ∃ k ∈ K, k * u * k⁻¹ = v := by
  intro u hu v hv
  have hinj : Set.InjOn (fun x => x * u * x⁻¹) (K : Set G) := by
    intro x hx y hy hxy
    change x * u * x⁻¹ = y * u * y⁻¹ at hxy
    have hxy' : (y⁻¹ * x) * u * (y⁻¹ * x)⁻¹ = u := by
      rw [show (y⁻¹ * x) * u * (y⁻¹ * x)⁻¹ = y⁻¹ * (x * u * x⁻¹) * y from by group, hxy]
      group
    have hmem : y⁻¹ * x ∈ K := K.mul_mem (K.inv_mem hy) hx
    have h1 : y⁻¹ * x = 1 := by
      by_contra hne
      exact hfree (y⁻¹ * x) hmem hne u hu hxy'
    calc x = y * (y⁻¹ * x) := by group
      _ = y := by rw [h1, mul_one]
  have himg : (fun x => x * u * x⁻¹) '' (K : Set G) ⊆ Submission.Blueprint.involutions (H : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨H.mul_mem (H.mul_mem (hKH hx) hu.1) (H.inv_mem (hKH hx)), ?_⟩
    show orderOf (x * u * x⁻¹) = 2
    rw [show x * u * x⁻¹ = MulAut.conj x u by rw [MulAut.conj_apply], MulEquiv.orderOf_eq, hu.2]
  have hcardimg : ((fun x => x * u * x⁻¹) '' (K : Set G)).ncard
      = (Submission.Blueprint.involutions (H : Set G)).ncard := by
    rw [Set.InjOn.ncard_image hinj, hcard]
  have heq := Set.eq_of_subset_of_ncard_le himg (le_of_eq hcardimg.symm)
  have hv' : v ∈ (fun x => x * u * x⁻¹) '' (K : Set G) := by rw [heq]; exact hv
  obtain ⟨k, hk, hkv⟩ := hv'
  exact ⟨k, hk, hkv⟩

/-- **Peterfalvi I Ch. III §1 Lemma 3, structural input** (p.175): for `1 ≠ X ≤ V` with
`N_K(X) ≠ 1`, `Q = {1} ∪ Inv(N_H(X))` is an elementary abelian 2-subgroup normalised by `N_H(X)`,
`K₁ = N_K(X) = C_K(X)` is a cyclic subgroup acting regularly on `Inv(N_H(X))`, and
`C_{N_V(X)}(K₁) = N_V(X) ∩ C(Q)`.  Route (Ch. II §4 Prop. 3 (b),(c),(d) inside `N_G(X)`, using
`ChIIFourProp` and `ModelFactsProp`) in `_design/Sec3.lean`. -/
theorem sec1_lemma3_structure (hFT : Submission.Blueprint.FeitThompsonProp)
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
      (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) ∧
      H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (Q : Set G) ∧
      (∀ u ∈ Q, u ≠ 1 → ∀ v ∈ Q, v ≠ 1 → ∃! k : G, k ∈ K₁ ∧ k * u * k⁻¹ = v) ∧
      Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G) ⊓
          Subgroup.centralizer (K₁ : Set G) =
        Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G) ⊓
          Subgroup.centralizer (Q : Set G) := by
  classical
  obtain ⟨hP1b, hP2a, hP2c, hP3, hP4a, hP4b⟩ := hC4 G hS H hH t ht htH
  -- ## 0. basics
  have hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard :=
    Work.ThreePoints.three_le_ncard_fixedPts_of_le_centD hH ht htH hXV
  have hXH : X ≤ H := (Work.ThreePoints.le_of_le_centD hXV).1
  have htC : t ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Work.ThreePoints.mem_centD.mp (hXV hx)).2.2
  have htN : t ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer (X : Set G) htC
  have hDodd : Odd (Nat.card ↥(Submission.Blueprint.twoPoint H t)) := hH.2.2 t htH
  -- ## 1. the P3 hypothesis and `K₁`
  have hP3hyp : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t,
      k ≠ 1 ∧ k ∈ Subgroup.normalizer (X : Set G) := by
    obtain ⟨k, hk, hk1⟩ := hNK
    exact ⟨k, hk.1, hk1, hk.2⟩
  have hP3' := hP3 X hX hXV hP3hyp
  obtain ⟨K₁, hK₁set, hK₁C, hK₁cyc⟩ := hP3'.2.2.2
  have hK₁Kset : ∀ k ∈ (K₁ : Set G),
      k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t :=
    fun k hk => (hK₁set ▸ hk).1
  have hK₁Y : ∀ k ∈ (K₁ : Set G), k ∈ Subgroup.normalizer (X : Set G) :=
    fun k hk => (hK₁set ▸ hk).2
  have hK₁leD : (K₁ : Set G) ⊆ (Submission.Blueprint.twoPoint H t : Set G) :=
    fun k hk => (hK₁Kset k hk).1
  have hK₁leH1 : (K₁ : Set G) ⊆ (((H ⊓ Subgroup.normalizer (X : Set G)) : Subgroup G) : Set G) :=
    fun k hk => Subgroup.mem_inf.mpr ⟨(hK₁leD hk).1, hK₁Y k hk⟩
  have hK₁H : ∀ k ∈ (K₁ : Set G), k ∈ H := fun k hk => (hK₁leD hk).1
  -- `N_H(X)` is strongly embedded in `N_G(X)`
  have hseH1 : IsStronglyEmbedded ((H ⊓ Subgroup.normalizer (X : Set G)).subgroupOf (Subgroup.normalizer (X : Set G))) := by
    have h := hP1b X (Subgroup.normalizer (X : Set G)) hX3
      (fun u hu => Subgroup.centralizer_le_normalizer (X : Set G) hu.1) le_rfl 1
      (by rw [Work.Models.conj_one]; exact hXH)
    rw [Work.Models.conj_one] at h
    rwa [inf_comm] at h
  -- ## 2. `|K₁| = |Inv N_H(X)|`
  have hcardK₁ : (K₁ : Set G).ncard =
      (Submission.Blueprint.involutions (((H ⊓ Subgroup.normalizer (X : Set G)) : Subgroup G) : Set G)).ncard := by
    have ht' : orderOf (⟨t, htN⟩ : ↥(Subgroup.normalizer (X : Set G))) = 2 :=
      (Subgroup.orderOf_coe (⟨t, htN⟩ : ↥(Subgroup.normalizer (X : Set G)))).symm.trans ht
    have htH' : (⟨t, htN⟩ : ↥(Subgroup.normalizer (X : Set G))) ∉
        ((H ⊓ Subgroup.normalizer (X : Set G))).subgroupOf (Subgroup.normalizer (X : Set G)) := by
      intro hmem
      exact htH (Subgroup.mem_subgroupOf.mp hmem).1
    have hc := Work.ThmF.Bender.cardKsetEqInv
      (H := (H ⊓ Subgroup.normalizer (X : Set G)).subgroupOf
        (Subgroup.normalizer (X : Set G)))
      (t := (⟨t, htN⟩ : ↥(Subgroup.normalizer (X : Set G)))) hseH1 ht' htH'
    rw [Subgroup.inf_subgroupOf_right H (Subgroup.normalizer (X : Set G))] at hc
    rw [ncard_Kset_subgroupOf (F := Subgroup.normalizer (X : Set G)) (H := H) htN] at hc
    rw [ncard_involutions_subgroupOf (F := Subgroup.normalizer (X : Set G)) (H := H)] at hc
    rw [← hc]
    exact (congrArg Set.ncard hK₁set.symm).symm
  -- ## 3. commutativity of the involutions of `N_H(X)`
  have hcommInv : ∀ u ∈ Submission.Blueprint.involutions (((H ⊓ Subgroup.normalizer (X : Set G)) : Subgroup G) : Set G),
      ∀ v ∈ Submission.Blueprint.involutions (((H ⊓ Subgroup.normalizer (X : Set G)) : Subgroup G) : Set G), u * v = v * u :=
    involutions_commute_of_hC4 hC4 hMod hS hH ht htH hX hXV hP3hyp
  -- ## 4. a free action of `K₁` on `Inv N_H(X)`
  have hfree : ∀ k ∈ (K₁ : Set G), k ≠ 1 →
      ∀ u ∈ Submission.Blueprint.involutions (((H ⊓ Subgroup.normalizer (X : Set G)) : Subgroup G) : Set G), k * u * k⁻¹ ≠ u := by
    intro k hk hk1 u hu
    exact Work.NormalComplement.no_involution_fixed_of_mem_Kset hH ht htH
      (hK₁Kset k hk) hk1 (hP2c k (hK₁Kset k hk) hk1) hDodd (Subgroup.mem_inf.mp hu.1).1 hu.2
  -- ## 5. the subgroup `Q = {1} ∪ Inv N_H(X)`
  let Q : Subgroup G :=
    { carrier := Set.insert 1 (Submission.Blueprint.involutions (((H ⊓ Subgroup.normalizer (X : Set G)) : Subgroup G) : Set G))
      one_mem' := Set.mem_insert 1 _
      mul_mem' := by
        intro a b ha hb
        rcases Set.mem_insert_iff.mp ha with rfl | ha'
        · rwa [one_mul]
        rcases Set.mem_insert_iff.mp hb with rfl | hb'
        · rwa [mul_one]
        obtain ⟨ha1, ha2⟩ := Work.ThreePoints.mem_involutions.mp ha'
        obtain ⟨hb1, hb2⟩ := Work.ThreePoints.mem_involutions.mp hb'
        have haa : a * a = 1 := by rw [← pow_two, ← ha2]; exact pow_orderOf_eq_one a
        have hbb : b * b = 1 := by rw [← pow_two, ← hb2]; exact pow_orderOf_eq_one b
        have hc' : a * b = b * a := hcommInv a ha' b hb'
        by_cases hab : a * b = 1
        · rw [hab]; exact Set.mem_insert 1 _
        · refine Set.mem_insert_of_mem 1 (Work.ThreePoints.mem_involutions.mpr
            ⟨(H ⊓ Subgroup.normalizer (X : Set G)).mul_mem ha1 hb1, ?_⟩)
          refine orderOf_eq_two_of_mul_self_eq_one ?_ hab
          calc (a * b) * (a * b) = a * (b * a) * b := by group
            _ = a * (a * b) * b := by rw [← hc']
            _ = (a * a) * (b * b) := by group
            _ = 1 := by rw [haa, hbb, one_mul]
      inv_mem' := by
        intro a ha
        rcases Set.mem_insert_iff.mp ha with rfl | ha'
        · rw [inv_one]; exact Set.mem_insert 1 _
        · obtain ⟨ha1, ha2⟩ := Work.ThreePoints.mem_involutions.mp ha'
          have haa : a * a = 1 := by rw [← pow_two, ← ha2]; exact pow_orderOf_eq_one a
          have hainv : a⁻¹ = a := by
            have h : a = a⁻¹ := by
              calc a = (a * a) * a⁻¹ := by group
                _ = a⁻¹ := by rw [haa, one_mul]
            exact h.symm
          rw [hainv]; exact Set.mem_insert_of_mem 1 ha' }
  have hQmem : ∀ u : G, u ∈ Q ↔ u = 1 ∨ u ∈ Submission.Blueprint.involutions
      (((H ⊓ Subgroup.normalizer (X : Set G)) : Subgroup G) : Set G) := fun u => Set.mem_insert_iff
  have hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
    intro x hx y hy
    rcases Set.mem_insert_iff.mp hx with rfl | hx'
    · rw [one_mul, mul_one]
    rcases Set.mem_insert_iff.mp hy with rfl | hy'
    · rw [mul_one, one_mul]
    exact hcommInv x hx' y hy'
  have hQconj : ∀ h ∈ ((H ⊓ Subgroup.normalizer (X : Set G)) : Subgroup G), ∀ q ∈ (Q : Set G),
      h * q * h⁻¹ ∈ (Q : Set G) := by
    intro h hh q hq
    rcases Set.mem_insert_iff.mp hq with rfl | hq'
    · rw [mul_one, mul_inv_cancel]; exact Set.mem_insert 1 _
    · obtain ⟨hq1, hq2⟩ := Work.ThreePoints.mem_involutions.mp hq'
      refine Set.mem_insert_of_mem 1 (Work.ThreePoints.mem_involutions.mpr ⟨?_, ?_⟩)
      · exact (H ⊓ Subgroup.normalizer (X : Set G)).mul_mem ((H ⊓ Subgroup.normalizer (X : Set G)).mul_mem hh hq1) ((H ⊓ Subgroup.normalizer (X : Set G)).inv_mem hh)
      · rw [show h * q * h⁻¹ = MulAut.conj h q by rw [MulAut.conj_apply],
          MulEquiv.orderOf_eq, hq2]
  have hQnorm : (H ⊓ Subgroup.normalizer (X : Set G)) ≤ Subgroup.normalizer (Q : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro q
    exact ⟨hQconj h hh q, fun hq => by
      have hstep := hQconj h⁻¹ ((H ⊓ Subgroup.normalizer (X : Set G)).inv_mem hh) (h * q * h⁻¹) hq
      rwa [show h⁻¹ * (h * q * h⁻¹) * (h⁻¹)⁻¹ = q by group] at hstep⟩
  -- ## 6. an involution in `N_H(X)`
  obtain ⟨u₀, hu₀⟩ : (Submission.Blueprint.involutions
      ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G)).Nonempty := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have heven : Even (Nat.card ↥((H ⊓ Subgroup.normalizer (X : Set G)).subgroupOf
        (Subgroup.normalizer (X : Set G)))) := hseH1.2.1
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
    refine ⟨(y : ↥(Subgroup.normalizer (X : Set G))), ?_⟩
    refine Work.ThreePoints.mem_involutions.mpr ⟨?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mp y.2
    · exact (Subgroup.orderOf_coe (y : ↥(Subgroup.normalizer (X : Set G)))).trans
        ((Subgroup.orderOf_coe y).trans hy)
  have hu₀Q : u₀ ∈ (Q : Set G) := Set.mem_insert_of_mem 1 hu₀
  have hQ_eq_inv : ∀ u ∈ (Q : Set G), u ≠ 1 → u ∈
      Submission.Blueprint.involutions (((H ⊓ Subgroup.normalizer (X : Set G)) : Subgroup G) : Set G) := by
    intro u hu hu1
    rcases Set.mem_insert_iff.mp hu with rfl | h
    · exact absurd rfl hu1
    · exact h
  -- ## 7. the regular action
  have hregular : ∀ u ∈ (Q : Set G), u ≠ 1 → ∀ v ∈ (Q : Set G), v ≠ 1 →
      ∃! k : G, k ∈ (K₁ : Set G) ∧ k * u * k⁻¹ = v := by
    intro u huQ hu1 v hvQ hv1
    have hu : u ∈ Submission.Blueprint.involutions (((H ⊓ Subgroup.normalizer (X : Set G)) : Subgroup G) : Set G) :=
      hQ_eq_inv u huQ hu1
    have hv : v ∈ Submission.Blueprint.involutions (((H ⊓ Subgroup.normalizer (X : Set G)) : Subgroup G) : Set G) :=
      hQ_eq_inv v hvQ hv1
    obtain ⟨k, hkK₁, hk⟩ :=
      transitive_conj_on_involutions hK₁leH1 hcardK₁ hfree u hu v hv
    refine ⟨k, ⟨hkK₁, hk⟩, ?_⟩
    intro k' hk'
    obtain ⟨hk'K₁, hk'⟩ := hk'
    have h1 : (k'⁻¹ * k) * u * (k'⁻¹ * k)⁻¹ = u := by
      rw [show (k'⁻¹ * k) * u * (k'⁻¹ * k)⁻¹ = k'⁻¹ * (k * u * k⁻¹) * k' from by group,
        hk, ← hk']
      group
    have h2 : k'⁻¹ * k = 1 := by
      by_contra hne
      exact hfree (k'⁻¹ * k) (K₁.mul_mem (K₁.inv_mem hk'K₁) hkK₁) hne u hu h1
    calc k' = k' * 1 := (mul_one k').symm
      _ = k' * (k'⁻¹ * k) := by rw [h2]
      _ = k := by group
  -- ## 8. the centraliser identity
  have hK0leV : ∀ z : G, z ∈ Subgroup.centralizer (Q : Set G) →
      z ∈ Submission.Blueprint.twoPoint H t → z ∈ Subgroup.normalizer (X : Set G) →
      z ∈ Submission.Blueprint.centD H t := by
    intro z hzC hzD hzN
    obtain ⟨u, hu, hVeq⟩ := hP2a
    have huCX : u ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hwV : w ∈ Submission.Blueprint.centD H t := hXV hw
      rw [hVeq] at hwV
      have hwCu : w ∈ Subgroup.centralizer ({u} : Set G) := hwV.2
      exact ((Subgroup.mem_centralizer_iff.mp hwCu) u (Set.mem_singleton u)).symm
    have huN : u ∈ Subgroup.normalizer (X : Set G) :=
      Subgroup.centralizer_le_normalizer (X : Set G) huCX
    have huH1 : u ∈ Submission.Blueprint.involutions (((H ⊓ Subgroup.normalizer (X : Set G)) : Subgroup G) : Set G) :=
      Work.ThreePoints.mem_involutions.mpr ⟨Subgroup.mem_inf.mpr ⟨hu.1, huN⟩, hu.2⟩
    have hzu : u * z = z * u :=
      (Subgroup.mem_centralizer_iff.mp hzC) u (Set.mem_insert_of_mem 1 huH1)
    rw [hVeq]
    refine ⟨hzD, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun h hv => by
      rw [Set.mem_singleton_iff.mp hv]
      exact hzu)
  have hcent : Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G) ⊓
        Subgroup.centralizer (K₁ : Set G) =
      Submission.Blueprint.centD H t ⊓ Subgroup.normalizer (X : Set G) ⊓
        Subgroup.centralizer (Q : Set G) := by
    apply le_antisymm
    · -- `C_{V ∩ N}(K₁) ≤ C_{V ∩ N}(Q)`
      intro x hx
      obtain ⟨hxVN, hxCK₁⟩ := hx
      have hxV : x ∈ Submission.Blueprint.centD H t := (Subgroup.mem_inf.mp hxVN).1
      have hxN : x ∈ Subgroup.normalizer (X : Set G) := (Subgroup.mem_inf.mp hxVN).2
      have hxH1 : x ∈ (H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) :=
        Subgroup.mem_inf.mpr ⟨(Work.ThreePoints.mem_centD.mp hxV).1, hxN⟩
      have hxpres : ∀ u ∈ Submission.Blueprint.involutions
            ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G),
          x * u * x⁻¹ ∈ Submission.Blueprint.involutions
            ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) := by
        intro u hu
        obtain ⟨hu1, hu2⟩ := Work.ThreePoints.mem_involutions.mp hu
        refine Work.ThreePoints.mem_involutions.mpr ⟨?_, ?_⟩
        · exact (H ⊓ Subgroup.normalizer (X : Set G)).mul_mem
            ((H ⊓ Subgroup.normalizer (X : Set G)).mul_mem hxH1 hu1)
            ((H ⊓ Subgroup.normalizer (X : Set G)).inv_mem hxH1)
        · rw [show x * u * x⁻¹ = MulAut.conj x u by rw [MulAut.conj_apply],
            MulEquiv.orderOf_eq, hu2]
      have habel : ∀ k ∈ (K₁ : Set G), ∀ k' ∈ (K₁ : Set G), k * k' = k' * k := by
        haveI := hK₁cyc
        have hc' := (isMulCommutative_iff (M := ↥K₁)).mp
          (IsCyclic.isMulCommutative (α := ↥K₁))
        intro k hk k' hk'
        exact congrArg Subtype.val (hc' (⟨k, hk⟩ : ↥K₁) ⟨k', hk'⟩)
      obtain ⟨k₀, hk₀K₁, hk₀⟩ := exists_conj_eq_of_commute_regular (K := K₁)
        (S := Submission.Blueprint.involutions
          ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G)) (y := x) (x₀ := u₀)
        hu₀ hxpres
        (fun z hz => transitive_conj_on_involutions hK₁leH1 hcardK₁ hfree u₀ hu₀ z hz)
        habel (fun k hk => ((Subgroup.mem_centralizer_iff.mp hxCK₁) k hk).symm)
      have hzCQ : k₀⁻¹ * x ∈ Subgroup.centralizer (Q : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        rcases Set.mem_insert_iff.mp hq with rfl | hq'
        · rw [one_mul, mul_one]
        · have h := hk₀ q hq'
          have hfix : (k₀⁻¹ * x) * q * (k₀⁻¹ * x)⁻¹ = q := by
            calc (k₀⁻¹ * x) * q * (k₀⁻¹ * x)⁻¹ = k₀⁻¹ * (x * q * x⁻¹) * k₀ := by group
              _ = k₀⁻¹ * (k₀ * q * k₀⁻¹) * k₀ := by rw [h]
              _ = q := by group
          have h2 : (k₀⁻¹ * x) * q = q * (k₀⁻¹ * x) := by
            calc (k₀⁻¹ * x) * q
                = ((k₀⁻¹ * x) * q * (k₀⁻¹ * x)⁻¹) * (k₀⁻¹ * x) := by group
              _ = q * (k₀⁻¹ * x) := by rw [hfix]
          exact h2.symm
      have hzD : k₀⁻¹ * x ∈ Submission.Blueprint.twoPoint H t :=
        (Submission.Blueprint.twoPoint H t).mul_mem
          ((Submission.Blueprint.twoPoint H t).inv_mem (hK₁leD hk₀K₁))
          ((Subgroup.mem_inf.mp hxV).1)
      have hzN : k₀⁻¹ * x ∈ Subgroup.normalizer (X : Set G) :=
        (Subgroup.normalizer (X : Set G)).mul_mem
          ((Subgroup.normalizer (X : Set G)).inv_mem (hK₁Y k₀ hk₀K₁)) hxN
      have hzV : k₀⁻¹ * x ∈ Submission.Blueprint.centD H t := hK0leV _ hzCQ hzD hzN
      have hk₀V : k₀ ∈ Submission.Blueprint.centD H t := by
        have hzV' : (k₀⁻¹ * x)⁻¹ ∈ Submission.Blueprint.centD H t :=
          (Submission.Blueprint.centD H t).inv_mem hzV
        have : k₀ = x * (k₀⁻¹ * x)⁻¹ := by group
        rw [this]
        exact (Submission.Blueprint.centD H t).mul_mem hxV hzV'
      have hk₀1 : k₀ = 1 := eq_one_of_mem_Kset_and_centD hH htH (hK₁Kset k₀ hk₀K₁) hk₀V
      have hCQ : x ∈ Subgroup.centralizer (Q : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        rcases Set.mem_insert_iff.mp hq with rfl | hq'
        · rw [one_mul, mul_one]
        · have h := hk₀ q hq'
          have h' : x * q * x⁻¹ = q := by simpa [hk₀1] using h
          have h2 : x * q = q * x := by
            calc x * q = (x * q * x⁻¹) * x := by group
              _ = q * x := by rw [h']
          exact h2.symm
      exact ⟨hxVN, hCQ⟩
    · -- `C_{V ∩ N}(Q) ≤ C_{V ∩ N}(K₁)`
      intro x hx
      obtain ⟨hxVN, hxCQ⟩ := hx
      have hxV : x ∈ Submission.Blueprint.centD H t := (Subgroup.mem_inf.mp hxVN).1
      have hxN : x ∈ Subgroup.normalizer (X : Set G) := (Subgroup.mem_inf.mp hxVN).2
      have hxfix : t * x * t⁻¹ = x := by
        have h := (Work.ThreePoints.mem_centD.mp hxV).2.2
        calc t * x * t⁻¹ = x * t * t⁻¹ := by rw [h]
          _ = x := by group
      have hxCQ' : ∀ u ∈ Submission.Blueprint.involutions
            ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G),
          x * u * x⁻¹ = u := by
        intro u hu
        have h := (Subgroup.mem_centralizer_iff.mp hxCQ) u (Set.mem_insert_of_mem 1 hu)
        calc x * u * x⁻¹ = u * x * x⁻¹ := by rw [← h]
          _ = u := by group
      have hCK : x ∈ Subgroup.centralizer (K₁ : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have hkKset := hK₁Kset k hk
        have hkH1 : k ∈ (H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) := hK₁leH1 hk
        have hkD : k ∈ Submission.Blueprint.twoPoint H t := hK₁leD hk
        have hxVN' : x ∈ Submission.Blueprint.twoPoint H t := (Subgroup.mem_inf.mp hxV).1
        have hxkD : x * k * x⁻¹ ∈ Submission.Blueprint.twoPoint H t :=
          (Submission.Blueprint.twoPoint H t).mul_mem
            ((Submission.Blueprint.twoPoint H t).mul_mem hxVN' hkD)
            ((Submission.Blueprint.twoPoint H t).inv_mem hxVN')
        have hxkN : x * k * x⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
          (Subgroup.normalizer (X : Set G)).mul_mem
            ((Subgroup.normalizer (X : Set G)).mul_mem hxN (hK₁Y k hk))
            ((Subgroup.normalizer (X : Set G)).inv_mem hxN)
        have hxkinv : t * (x * k * x⁻¹) * t⁻¹ = (x * k * x⁻¹)⁻¹ := by
          rw [show t * (x * k * x⁻¹) * t⁻¹
              = (t * x * t⁻¹) * (t * k * t⁻¹) * (t * x * t⁻¹)⁻¹ from by group,
            hxfix, hkKset.2]
          group
        have hconjK : x * k * x⁻¹ ∈ (K₁ : Set G) := by
          rw [hK₁set]
          exact ⟨⟨hxkD, hxkinv⟩, hxkN⟩
        have hku₀ : k * u₀ * k⁻¹ ∈ Submission.Blueprint.involutions
            ((H ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) :=
          Work.ThreePoints.mem_involutions.mpr
            ⟨(H ⊓ Subgroup.normalizer (X : Set G)).mul_mem
              ((H ⊓ Subgroup.normalizer (X : Set G)).mul_mem hkH1 hu₀.1)
              ((H ⊓ Subgroup.normalizer (X : Set G)).inv_mem hkH1), by
              rw [show k * u₀ * k⁻¹ = MulAut.conj k u₀ by rw [MulAut.conj_apply],
                MulEquiv.orderOf_eq, hu₀.2]⟩
        have hact : (x * k * x⁻¹) * u₀ * (x * k * x⁻¹)⁻¹ = k * u₀ * k⁻¹ := by
          have hxu := hxCQ' u₀ hu₀
          have hxu' : x⁻¹ * u₀ * x = u₀ := by
            calc x⁻¹ * u₀ * x = x⁻¹ * (x * u₀ * x⁻¹) * x := by rw [hxu]
              _ = u₀ := by group
          have hxku : x * (k * u₀ * k⁻¹) * x⁻¹ = k * u₀ * k⁻¹ := hxCQ' _ hku₀
          calc (x * k * x⁻¹) * u₀ * (x * k * x⁻¹)⁻¹
              = x * k * (x⁻¹ * u₀ * x) * k⁻¹ * x⁻¹ := by group
            _ = x * k * u₀ * k⁻¹ * x⁻¹ := by rw [hxu']
            _ = x * (k * u₀ * k⁻¹) * x⁻¹ := by group
            _ = k * u₀ * k⁻¹ := hxku
        have hcancel : (k⁻¹ * (x * k * x⁻¹)) * u₀ * (k⁻¹ * (x * k * x⁻¹))⁻¹ = u₀ := by
          rw [show k⁻¹ * (x * k * x⁻¹) * u₀ * (k⁻¹ * (x * k * x⁻¹))⁻¹
              = k⁻¹ * ((x * k * x⁻¹) * u₀ * (x * k * x⁻¹)⁻¹) * k from by group,
            hact]
          group
        have h1 : k⁻¹ * (x * k * x⁻¹) = 1 := by
          by_contra hne
          exact hfree _ (K₁.mul_mem (K₁.inv_mem hk) hconjK) hne u₀ hu₀ hcancel
        have h3 : x * k * x⁻¹ = k := by
          have hh := congrArg (fun z => k * z) h1
          rw [mul_one] at hh
          rwa [show k * (k⁻¹ * (x * k * x⁻¹)) = x * k * x⁻¹ from by group] at hh
        have h4 : x * k = k * x := by
          have hh : (x * k * x⁻¹) * x = k * x := congrArg (fun z => z * x) h3
          rwa [show (x * k * x⁻¹) * x = x * k from by group] at hh
        exact h4.symm
      exact ⟨hxVN, hCK⟩
  have hNKCK : Work.NormalComplement.Design.NK H t X = Work.NormalComplement.Design.CK H t X := by
    apply Set.Subset.antisymm
    · intro y hy
      have hyK : y ∈ (K₁ : Set G) := hK₁set.symm ▸ hy
      exact ⟨hy.1, hK₁C hyK⟩
    · intro y hy
      exact ⟨hy.1, Subgroup.centralizer_le_normalizer (X : Set G) hy.2⟩
  exact ⟨Q, K₁, rfl, hK₁set, hNKCK, hK₁cyc, hQab, hQnorm, hregular, hcent⟩


end Work.NormalComplement
