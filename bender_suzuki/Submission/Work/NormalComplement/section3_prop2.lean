import Mathlib
import Submission.Work.NormalComplement.Sections
import Submission.Work.NormalComplement.Prelim
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Basic
import Submission.Work.ThreePoints.hasFourGroupIn_of_odd_index
import Submission.Work.ThmF.Bender.Basic
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThmF.Bender.cardInvGeTwo

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option maxHeartbeats 1600000

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

variable {G : Type} [Group G] [Finite G]

/-! ## Elementary group theory helpers -/

/-- `K = Kset D t`, the set of elements inverted by `t`, is abelian: conjugation by the
involution `t` is an automorphism acting as inversion. -/
theorem Kset_abelian {H : Subgroup G} {t : G} (ht : orderOf t = 2) {K : Subgroup G}
    (hK : (K : Set G) = Kset (twoPoint H t) t) :
    ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
  intro x hx y hy
  have key : ∀ z ∈ K, t * z * t⁻¹ = z⁻¹ := by
    intro z hz
    have hz' : z ∈ Kset (twoPoint H t) t := by rw [← hK]; exact hz
    exact hz'.2
  have hinv : (x * y)⁻¹ = x⁻¹ * y⁻¹ := by
    calc (x * y)⁻¹ = t * (x * y) * t⁻¹ := (key _ (K.mul_mem hx hy)).symm
      _ = (t * x * t⁻¹) * (t * y * t⁻¹) := by group
      _ = x⁻¹ * y⁻¹ := by rw [key x hx, key y hy]
  calc x * y = ((x * y)⁻¹)⁻¹ := by rw [inv_inv]
    _ = (x⁻¹ * y⁻¹)⁻¹ := by rw [hinv]
    _ = y * x := by rw [mul_inv_rev, inv_inv, inv_inv]

/-- `|K| = |Inv H|` for `K = Kset D t` (Ch. I §2 Prop. 2). -/
theorem Kset_ncard {H : Subgroup G} {t : G} (hH : IsStronglyEmbedded H)
    (ht : orderOf t = 2) (htH : t ∉ H) {K : Subgroup G}
    (hK : (K : Set G) = Kset (twoPoint H t) t) :
    (K : Set G).ncard = (involutions (H : Set G)).ncard := by
  rw [hK]
  exact Work.ThmF.Bender.cardKsetEqInv hH ht htH

/-- The index of `W` in `H` is odd when `H = W ⊔ D`, `W ⊴ H` and `D` has odd order. -/
theorem odd_index_of_le_normalizer_of_sup_eq {W D H : Subgroup G}
    (hW : W ≤ H) (hWD : W ⊔ D = H) (hDH : D ≤ H)
    (hHn : H ≤ Subgroup.normalizer (W : Set G)) (hD : Odd (Nat.card D)) :
    Odd ((W.subgroupOf H).index) := by
  haveI : (W.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hW).mpr hHn
  have hsup : (W.subgroupOf H) ⊔ (D.subgroupOf H) = (⊤ : Subgroup ↥H) := by
    rw [← Subgroup.subgroupOf_sup hW hDH, hWD, Subgroup.subgroupOf_self]
  have heq : (W.subgroupOf H).index = (W ⊓ D).relIndex D := by
    calc (W.subgroupOf H).index
        = (W.subgroupOf H).relIndex (⊤ : Subgroup ↥H) := (Subgroup.relIndex_top_right _).symm
      _ = (W.subgroupOf H).relIndex ((W.subgroupOf H) ⊔ (D.subgroupOf H)) := by rw [hsup]
      _ = (W.subgroupOf H).relIndex (D.subgroupOf H) := Subgroup.relIndex_sup_left _ _
      _ = ((W.subgroupOf H) ⊓ (D.subgroupOf H)).relIndex (D.subgroupOf H) :=
            (Subgroup.inf_relIndex_right _ _).symm
      _ = ((W ⊓ D).subgroupOf H).relIndex (D.subgroupOf H) := by
            rw [show (W ⊓ D).subgroupOf H = W.subgroupOf H ⊓ D.subgroupOf H from by
              ext x; simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]]
      _ = (W ⊓ D).relIndex D := Subgroup.relIndex_subgroupOf hDH
  rw [heq]
  exact Work.ThreePoints.Odd.of_dvd (Subgroup.relIndex_dvd_card _ _) hD

/-- Every involution of `H` lies in `W` when `W ⊴ H` has odd index. -/
theorem involution_mem_of_odd_index {W H : Subgroup G} (hW : W ≤ H)
    (hHn : H ≤ Subgroup.normalizer (W : Set G)) (hidx : Odd ((W.subgroupOf H).index))
    {u : G} (huH : u ∈ H) (hu2 : orderOf u = 2) : u ∈ W := by
  haveI : (W.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hW).mpr hHn
  set x : ↥H := ⟨u, huH⟩ with hx
  have hxo : orderOf x = 2 := by rw [hx, Subgroup.orderOf_mk, hu2]
  have hx2 : x ^ 2 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  obtain ⟨k, hk⟩ := hidx
  have hmem : x ^ (W.subgroupOf H).index ∈ W.subgroupOf H := Subgroup.pow_index_mem _ x
  have hxp : x ^ (W.subgroupOf H).index = x := by
    rw [hk]
    have : x ^ (2 * k) = 1 := by rw [pow_mul, hx2]; simp
    rw [pow_succ, this, one_mul]
  rw [hxp] at hmem
  have := Subgroup.mem_subgroupOf.mp hmem
  simpa [hx] using this

/-- `H` contains a four-group when `G` does and `H` is strongly embedded. -/
theorem hasFourGroupIn_of_stronglyEmbedded {H : Subgroup G} (hH : IsStronglyEmbedded H)
    (hfour : HasFourGroup G) : Work.Reductions.HasFourGroupIn H := by
  obtain ⟨a, b, ha2, hb2, hne, hcomm⟩ := hfour
  obtain ⟨g, hga⟩ := Work.ThreePoints.exists_conj_mem hH ha2
  have hK : IsStronglyEmbedded (conj g H) := Work.ThreePoints.conj_stronglyEmbedded hH g
  have hC : Subgroup.centralizer ({a} : Set G) ≤ conj g H :=
    Work.ThreePoints.IsStronglyEmbedded.centralizer_le hK hga (by rw [ha2])
  have hbC : b ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]; exact hcomm.symm
  have hgb : b ∈ conj g H := hC hbC
  have haH : g⁻¹ * a * g ∈ H := (Work.ThreePoints.mem_conj_iff).mp hga
  have hbH : g⁻¹ * b * g ∈ H := (Work.ThreePoints.mem_conj_iff).mp hgb
  refine ⟨g⁻¹ * a * g, g⁻¹ * b * g, haH, hbH, ?_, ?_, ?_, ?_⟩
  · rw [show g⁻¹ * a * g = MulAut.conj g⁻¹ a by rw [MulAut.conj_apply]; group,
      MulEquiv.orderOf_eq, ha2]
  · rw [show g⁻¹ * b * g = MulAut.conj g⁻¹ b by rw [MulAut.conj_apply]; group,
      MulEquiv.orderOf_eq, hb2]
  · intro h; exact hne (by have := congrArg (fun z => g * z * g⁻¹) h; simpa [mul_assoc] using this)
  · calc g⁻¹ * a * g * (g⁻¹ * b * g) = g⁻¹ * (a * b) * g := by group
      _ = g⁻¹ * (b * a) * g := by rw [hcomm]
      _ = g⁻¹ * b * g * (g⁻¹ * a * g) := by group

/-- Every involution of `H` lies in `W`. -/
theorem involutions_subset_of_sup_eq {W D H : Subgroup G} (hW : W ≤ H) (hWD : W ⊔ D = H)
    (hDH : D ≤ H) (hHn : H ≤ Subgroup.normalizer (W : Set G)) (hDodd : Odd (Nat.card D)) :
    involutions (H : Set G) ⊆ (W : Set G) :=
  fun _ hu => involution_mem_of_odd_index hW hHn
    (odd_index_of_le_normalizer_of_sup_eq hW hWD hDH hHn hDodd) hu.1 hu.2

/-- `W` has a four-group when `H` does and `W ⊴ H` has odd index. -/
theorem hasFourGroup_subgroupOf {W D H : Subgroup G} (hHss : IsStronglyEmbedded H)
    (hfour : HasFourGroup G) (hW : W ≤ H) (hWD : W ⊔ D = H) (hDH : D ≤ H)
    (hHn : H ≤ Subgroup.normalizer (W : Set G)) (hDodd : Odd (Nat.card D)) :
    HasFourGroup ↥W := by
  have hsub := involutions_subset_of_sup_eq hW hWD hDH hHn hDodd
  obtain ⟨a, b, haH, hbH, ha2, hb2, hne, hcomm⟩ :=
    hasFourGroupIn_of_stronglyEmbedded hHss hfour
  exact Work.Reductions.HasFourGroupIn.to_subgroup
    ⟨a, b, hsub ⟨haH, ha2⟩, hsub ⟨hbH, hb2⟩, ha2, hb2, hne, hcomm⟩

/-! ## Fixed points of `k ∈ K#` -/

/-- For `k ∈ K#` the fixed points in `Ω = G ⧸ H` are exactly the two points `H` and `H^t`. -/
theorem fixedPts_eq_pair {H : Subgroup G} {t : G} (hH : IsStronglyEmbedded H)
    (ht : orderOf t = 2) (htH : t ∉ H) {k : G} (hk : k ∈ Kset (twoPoint H t) t) (hk1 : k ≠ 1)
    (hcard : (fixedPts H (Subgroup.zpowers k)).ncard = 2) :
    fixedPts H (Subgroup.zpowers k) = {((1 : G) : G ⧸ H), (t : G ⧸ H)} := by
  have hkD : k ∈ twoPoint H t := hk.1
  have hkH : k ∈ H := hkD.1
  have hkHt : k ∈ conj t H := hkD.2
  have hzpH : Subgroup.zpowers k ≤ H := Subgroup.zpowers_le.mpr hkH
  have hzpHt : Subgroup.zpowers k ≤ conj t H := Subgroup.zpowers_le.mpr hkHt
  have hmem1 : ((1 : G) : G ⧸ H) ∈ fixedPts H (Subgroup.zpowers k) := by
    rw [Work.ThreePoints.mem_fixedPts]
    intro x hx
    rw [Work.ThreePoints.smul_mk, mul_one, QuotientGroup.eq]
    simpa using H.inv_mem (hzpH hx)
  have hmemt : (t : G ⧸ H) ∈ fixedPts H (Subgroup.zpowers k) := by
    rw [Work.ThreePoints.mem_fixedPts]
    intro x hx
    rw [Work.ThreePoints.smul_mk, QuotientGroup.eq]
    rw [show (x * t)⁻¹ * t = t⁻¹ * x⁻¹ * t from by group]
    have := H.inv_mem ((Work.ThreePoints.mem_conj_iff).mp (hzpHt hx))
    rwa [show (t⁻¹ * x * t)⁻¹ = t⁻¹ * x⁻¹ * t from by group] at this
  have hne : ((1 : G) : G ⧸ H) ≠ (t : G ⧸ H) := by
    intro h
    exact htH (by rw [QuotientGroup.eq] at h; simpa using h)
  have hsub : ({((1 : G) : G ⧸ H), (t : G ⧸ H)} : Set (G ⧸ H)) ⊆
      fixedPts H (Subgroup.zpowers k) := by
    intro ω hω
    rcases Set.mem_insert_iff.mp hω with rfl | hω
    · exact hmem1
    · rw [Set.mem_singleton_iff] at hω; rw [hω]; exact hmemt
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hcard, Set.ncard_pair hne])).symm

/-- If `x ∈ H` commutes with `k ∈ K#`, then `x ∈ D = H ∩ H^t`. -/
theorem mem_twoPoint_of_commute_of_mem_Kset {H : Subgroup G} {t : G} (hH : IsStronglyEmbedded H)
    (ht : orderOf t = 2) (htH : t ∉ H) {k : G} (hk : k ∈ Kset (twoPoint H t) t) (hk1 : k ≠ 1)
    (hcard : (fixedPts H (Subgroup.zpowers k)).ncard = 2)
    {x : G} (hxH : x ∈ H) (hcomm : x * k = k * x) : x ∈ twoPoint H t := by
  have hconjk : x⁻¹ * k * x = k := by
    calc x⁻¹ * k * x = x⁻¹ * (k * x) := by group
      _ = x⁻¹ * (x * k) := by rw [← hcomm]
      _ = k := by group
  have hconjn : ∀ n : ℤ, x⁻¹ * k ^ n * x = k ^ n := by
    intro n
    have h := conj_zpow (i := n) (a := x⁻¹) (b := k)
    rw [inv_inv] at h
    rw [← h, hconjk]
  have hswap : ∀ n : ℤ, k ^ n * x = x * k ^ n := fun n =>
    calc k ^ n * x = x * (x⁻¹ * k ^ n * x) := by group
      _ = x * k ^ n := by rw [hconjn n]
  have hperm : ∀ ω ∈ fixedPts H (Subgroup.zpowers k),
      x • ω ∈ fixedPts H (Subgroup.zpowers k) := by
    intro ω hω
    rw [Work.ThreePoints.mem_fixedPts] at hω
    rw [Work.ThreePoints.mem_fixedPts]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    calc k ^ n • (x • ω) = (k ^ n * x) • ω := (mul_smul _ _ _).symm
      _ = (x * k ^ n) • ω := by rw [hswap n]
      _ = x • (k ^ n • ω) := mul_smul _ _ _
      _ = x • ω := by rw [hω (k^n) (Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩)]
  have hpair := fixedPts_eq_pair hH ht htH hk hk1 hcard
  have hne : ((1 : G) : G ⧸ H) ≠ (t : G ⧸ H) := by
    intro h; exact htH (by rw [QuotientGroup.eq] at h; simpa using h)
  have hx1 : x • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
    rw [Work.ThreePoints.smul_mk, mul_one, QuotientGroup.eq]
    simpa using H.inv_mem hxH
  have hx_t_mem : x • (t : G ⧸ H) ∈ fixedPts H (Subgroup.zpowers k) :=
    hperm _ (by rw [hpair]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hx_t_eq : x • (t : G ⧸ H) = (t : G ⧸ H) := by
    rw [hpair] at hx_t_mem
    rcases Set.mem_insert_iff.mp hx_t_mem with h | h
    · exfalso
      have h2 : x • (t : G ⧸ H) = x • ((1 : G) : G ⧸ H) := by rw [h, hx1]
      exact hne (MulAction.injective x h2.symm)
    · rwa [Set.mem_singleton_iff] at h
  rw [Work.ThreePoints.mem_twoPoint]
  refine ⟨hxH, ?_⟩
  have h := hx_t_eq
  rw [Work.ThreePoints.smul_mk, QuotientGroup.eq] at h
  rw [show (x * t)⁻¹ * t = t⁻¹ * x⁻¹ * t from by group] at h
  rw [show t⁻¹ * x * t = (t⁻¹ * x⁻¹ * t)⁻¹ from by group]
  exact H.inv_mem h

/-- No element `k ∈ K#` fixes an involution of `H`. -/
theorem no_involution_fixed_of_mem_Kset {H : Subgroup G} {t : G} (hH : IsStronglyEmbedded H)
    (ht : orderOf t = 2) (htH : t ∉ H) {k : G} (hk : k ∈ Kset (twoPoint H t) t) (hk1 : k ≠ 1)
    (hcard : (fixedPts H (Subgroup.zpowers k)).ncard = 2)
    (hDodd : Odd (Nat.card (twoPoint H t)))
    {u : G} (huH : u ∈ H) (hu2 : orderOf u = 2) : k * u * k⁻¹ ≠ u := by
  intro hku
  have hcomm : k * u = u * k := by
    calc k * u = (k * u * k⁻¹) * k := by group
      _ = u * k := by rw [hku]
  have huD : u ∈ twoPoint H t :=
    mem_twoPoint_of_commute_of_mem_Kset hH ht htH hk hk1 hcard huH hcomm.symm
  have hdvd : 2 ∣ Nat.card (twoPoint H t) := by
    rw [← hu2]; exact Subgroup.orderOf_dvd_natCard (twoPoint H t) huD
  exact (Nat.not_odd_iff_even.mpr (even_iff_two_dvd.mpr hdvd)) hDodd

/-! ## `K` acts regularly on `Inv(H)` -/

/-- `K` acts transitively on the involutions of `H`. -/
theorem Kset_transitive_on_involutions {H : Subgroup G} {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {K : Subgroup G} (hK : (K : Set G) = Kset (twoPoint H t) t)
    (hcard : (K : Set G).ncard = (involutions (H : Set G)).ncard)
    (hfree : ∀ k ∈ K, k ≠ 1 → ∀ u ∈ involutions (H:Set G), k * u * k⁻¹ ≠ u) :
    ∀ u ∈ involutions (H:Set G), ∀ v ∈ involutions (H:Set G), ∃ k ∈ K, k * u * k⁻¹ = v := by
  have hKH : (K:Set G) ⊆ (H:Set G) := by
    intro k hk
    have hk' : k ∈ Kset (twoPoint H t) t := by rw [← hK]; exact hk
    exact (hk'.1).1
  intro u hu v hv
  have hinj : Set.InjOn (fun x => x * u * x⁻¹) (K:Set G) := by
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
  have himg : (fun x => x * u * x⁻¹) '' (K:Set G) ⊆ involutions (H:Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨H.mul_mem (H.mul_mem (hKH hx) hu.1) (H.inv_mem (hKH hx)), ?_⟩
    show orderOf (x * u * x⁻¹) = 2
    rw [show x * u * x⁻¹ = MulAut.conj x u by rw [MulAut.conj_apply], MulEquiv.orderOf_eq, hu.2]
  have hcardimg : ((fun x => x * u * x⁻¹) '' (K:Set G)).ncard = (involutions (H:Set G)).ncard := by
    rw [Set.InjOn.ncard_image hinj, hcard]
  have heq := Set.eq_of_subset_of_ncard_le himg (le_of_eq hcardimg.symm)
  have hv' : v ∈ (fun x => x * u * x⁻¹) '' (K:Set G) := by rw [heq]; exact hv
  obtain ⟨k, hk, hkv⟩ := hv'
  exact ⟨k, hk, hkv⟩

/-- The fixed points of the whole of `K` (a subgroup) are `H` and `H^t`. -/
theorem fixedPts_K_eq_pair {H : Subgroup G} {t : G} {K : Subgroup G}
    (hKH : (K : Set G) ⊆ (H : Set G)) (hKHt : (K : Set G) ⊆ (conj t H : Set G))
    (hk : ∃ k ∈ K, k ≠ 1)
    (hfixed : ∀ k ∈ K, k ≠ 1 → fixedPts H (Subgroup.zpowers k)
      = {((1 : G) : G ⧸ H), (t : G ⧸ H)}) :
    fixedPts H K = {((1 : G) : G ⧸ H), (t : G ⧸ H)} := by
  obtain ⟨k₀, hk₀K, hk₀1⟩ := hk
  have hle : fixedPts H K ⊆ fixedPts H (Subgroup.zpowers k₀) :=
    Work.ThreePoints.fixedPts_mono (Subgroup.zpowers_le.mpr hk₀K)
  rw [hfixed k₀ hk₀K hk₀1] at hle
  have hsup : ({((1 : G) : G ⧸ H), (t : G ⧸ H)} : Set (G ⧸ H)) ⊆ fixedPts H K := by
    intro ω hω
    rw [Work.ThreePoints.mem_fixedPts]
    intro x hx
    rcases Set.mem_insert_iff.mp hω with rfl | hω
    · rw [Work.ThreePoints.smul_mk, mul_one, QuotientGroup.eq]
      simpa using H.inv_mem (hKH hx)
    · rw [Set.mem_singleton_iff] at hω; rw [hω]
      rw [Work.ThreePoints.smul_mk, QuotientGroup.eq]
      rw [show (x * t)⁻¹ * t = t⁻¹ * x⁻¹ * t from by group]
      exact (Work.ThreePoints.mem_conj_iff).mp ((conj t H).inv_mem (hKHt hx))
  exact Set.Subset.antisymm hle hsup

/-- `N_W(K) ≤ D = H ∩ H^t`. -/
theorem normalizer_in_W_le_twoPoint {H : Subgroup G} {t : G} (hH : IsStronglyEmbedded H)
    (ht : orderOf t = 2) (htH : t ∉ H) {W K : Subgroup G} (hWH : W ≤ H)
    (hKH : (K : Set G) ⊆ (H : Set G)) (hKHt : (K : Set G) ⊆ (conj t H : Set G))
    (hk : ∃ k ∈ K, k ≠ 1)
    (hfixed : ∀ k ∈ K, k ≠ 1 → fixedPts H (Subgroup.zpowers k)
      = {((1 : G) : G ⧸ H), (t : G ⧸ H)}) :
    W ⊓ Subgroup.normalizer (K : Set G) ≤ twoPoint H t := by
  intro w hw
  obtain ⟨hwW, hwN⟩ := hw
  have hpair := fixedPts_K_eq_pair hKH hKHt hk hfixed
  have hperm : ∀ ω ∈ fixedPts H K, w • ω ∈ fixedPts H K := by
    intro ω hω
    rw [Work.ThreePoints.mem_fixedPts] at hω ⊢
    intro x hx
    have hwx : w⁻¹ * x * w ∈ K := by
      have h := (Subgroup.mem_normalizer_iff.mp hwN) (w⁻¹ * x * w)
      rw [h]
      have : w * (w⁻¹ * x * w) * w⁻¹ = x := by group
      rw [this]; exact hx
    calc x • (w • ω) = (x * w) • ω := (mul_smul _ _ _).symm
      _ = (w * (w⁻¹ * x * w)) • ω := by rw [show x * w = w * (w⁻¹ * x * w) by group]
      _ = w • ((w⁻¹ * x * w) • ω) := mul_smul _ _ _
      _ = w • ω := by rw [hω _ hwx]
  have hw1 : w • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
    rw [Work.ThreePoints.smul_mk, mul_one, QuotientGroup.eq]
    simpa using H.inv_mem (hWH hwW)
  have hne : ((1 : G) : G ⧸ H) ≠ (t : G ⧸ H) := by
    intro h; exact htH (by rw [QuotientGroup.eq] at h; simpa using h)
  have hmem : w • (t : G ⧸ H) ∈ fixedPts H K :=
    hperm _ (by rw [hpair]; exact Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hwt : w • (t : G ⧸ H) = (t : G ⧸ H) := by
    rw [hpair] at hmem
    rcases Set.mem_insert_iff.mp hmem with h | h
    · exfalso
      have h2 : w • (t : G ⧸ H) = w • ((1 : G) : G ⧸ H) := by rw [h, hw1]
      exact hne (MulAction.injective w h2.symm)
    · rwa [Set.mem_singleton_iff] at h
  exact ⟨hWH hwW, by
    change w ∈ conj t H
    rw [Work.ThreePoints.mem_conj_iff]
    have h := hwt
    rw [Work.ThreePoints.smul_mk, QuotientGroup.eq] at h
    rw [show (w * t)⁻¹ * t = t⁻¹ * w⁻¹ * t from by group] at h
    rw [show t⁻¹ * w * t = (t⁻¹ * w⁻¹ * t)⁻¹ from by group]
    exact H.inv_mem h⟩

/-- `C_W(k) = K` for `k ∈ K#`. -/
theorem centralizer_in_W_eq_K {H : Subgroup G} {t : G} {W K : Subgroup G}
    (hKabel : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x)
    (hEnorm : W ⊓ twoPoint H t ≤ Subgroup.normalizer (K : Set G))
    (hKsup : K ⊔ (W ⊓ centD H t) = W ⊓ twoPoint H t)
    (hKfpf : ∀ k ∈ K, k ≠ 1 → ∀ v ∈ W ⊓ centD H t, v ≠ 1 → v * k * v⁻¹ ≠ k)
    (hCltD : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k}:Set G) ⊓ W ≤ twoPoint H t) :
    ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k}:Set G) ⊓ W = K := by
  intro k hk hk1
  apply le_antisymm
  · intro x hx
    obtain ⟨hxcent, hxW⟩ := hx
    have hxk : x * k = k * x := Subgroup.mem_centralizer_singleton_iff.mp hxcent
    have hxD : x ∈ twoPoint H t := hCltD k hk hk1 ⟨hxcent, hxW⟩
    have hxWD : x ∈ W ⊓ twoPoint H t := ⟨hxW, hxD⟩
    have hC0norm : W ⊓ centD H t ≤ Subgroup.normalizer (K : Set G) :=
      le_trans (le_inf inf_le_left (inf_le_right.trans inf_le_left)) hEnorm
    obtain ⟨k₁, hk₁, c, hc, hkc⟩ : ∃ k₁ ∈ K, ∃ c ∈ W ⊓ centD H t, k₁ * c = x := by
      have h2 : x ∈ K ⊔ (W ⊓ centD H t) := by rw [hKsup]; exact hxWD
      have h2set : x ∈ ((K ⊔ (W ⊓ centD H t) : Subgroup G) : Set G) := h2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left K (W ⊓ centD H t) hC0norm] at h2set
      rwa [Set.mem_mul] at h2set
    have h2 : c * k = k * c := by
      have h3 : (k₁ * c) * k = k * (k₁ * c) := by rw [hkc]; exact hxk
      have hconj : k₁⁻¹ * k * k₁ = k := by
        calc k₁⁻¹ * k * k₁ = k₁⁻¹ * (k * k₁) := by group
          _ = k₁⁻¹ * (k₁ * k) := by rw [← hKabel k₁ hk₁ k hk]
          _ = k := by group
      calc c * k = k₁⁻¹ * ((k₁ * c) * k) := by group
        _ = k₁⁻¹ * (k * (k₁ * c)) := by rw [h3]
        _ = (k₁⁻¹ * k * k₁) * c := by group
        _ = k * c := by rw [hconj]
    have hck : c * k * c⁻¹ = k := by rw [h2]; group
    by_cases hc1 : c = 1
    · rw [← hkc, hc1, mul_one]; exact hk₁
    · exact absurd hck (hKfpf k hk hk1 c hc hc1)
  · intro x hx
    refine ⟨?_, ?_⟩
    · change x ∈ Subgroup.centralizer ({k} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]; exact hKabel x hx k hk
    · change x ∈ W
      have : K ≤ W ⊓ twoPoint H t := by rw [← hKsup]; exact le_sup_left
      exact (this hx).1

/-! ## Applying Appendix VI -/

/-- The involutions of `H` as a type. -/
abbrev InvSub (H : Subgroup G) : Type := {u : G // u ∈ involutions (H : Set G)}

/-- The conjugation action of `W` on the involutions of `H`. -/
@[instance_reducible] def invAct {H W : Subgroup G} (hWH : W ≤ H) :
    MulAction ↥W (InvSub H) where
  smul w i := ⟨(w : G) * (i : G) * (w : G)⁻¹, by
    have hi : (i : G) ∈ H ∧ orderOf (i : G) = 2 := Work.ThreePoints.mem_involutions.mp i.2
    refine Work.ThreePoints.mem_involutions.mpr ⟨?_, ?_⟩
    · exact H.mul_mem (H.mul_mem (hWH w.2) hi.1) (H.inv_mem (hWH w.2))
    · rw [show (w : G) * (i : G) * (w : G)⁻¹ = MulAut.conj (w : G) (i : G) by
        rw [MulAut.conj_apply]]
      rw [MulEquiv.orderOf_eq, hi.2]⟩
  one_smul i := Subtype.ext (by
    show ((1 : ↥W) : G) * (i : G) * ((1 : ↥W) : G)⁻¹ = (i : G)
    rw [Subgroup.coe_one]; group)
  mul_smul w₁ w₂ i := Subtype.ext (by
    show (((w₁ * w₂ : ↥W)) : G) * (i : G) * (((w₁ * w₂ : ↥W)) : G)⁻¹
      = (w₁ : G) * ((w₂ : G) * (i : G) * (w₂ : G)⁻¹) * (w₁ : G)⁻¹
    rw [Subgroup.coe_mul]; group)

/-- A `2`-transitive action maps any ordered pair of distinct points to any other. -/
theorem exists_smul_eq_pair_of_two_transitive {M α : Type} [Group M] [MulAction M α]
    (h : MulAction.IsMultiplyPretransitive M α 2) {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ g : M, g • a = c ∧ g • b = d := by
  let e₁ : Fin 2 ↪ α := ⟨![a, b], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  let e₂ : Fin 2 ↪ α := ⟨![c, d], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  obtain ⟨g, hg⟩ := h.exists_smul_eq e₁ e₂
  refine ⟨g, ?_, ?_⟩
  · have hh := congrArg (fun f : Fin 2 ↪ α => f 0) hg
    change g • (e₁ 0) = e₂ 0 at hh
    rwa [show e₁ 0 = a from rfl, show e₂ 0 = c from rfl] at hh
  · have hh := congrArg (fun f : Fin 2 ↪ α => f 1) hg
    change g • (e₁ 1) = e₂ 1 at hh
    rwa [show e₁ 1 = b from rfl, show e₂ 1 = d from rfl] at hh

/-- **Appendix VI input.**  `W = C_W(Inv H)·N_W(K)`. -/
theorem W_le_centralizer_sup_normalizer {H : Subgroup G} {t : G} (hH : IsStronglyEmbedded H)
    (ht : orderOf t = 2) (htH : t ∉ H) (hfour : HasFourGroup G)
    {W K : Subgroup G} (hWH : W ≤ H) (hKW : K ≤ W)
    (hWD : W ⊔ twoPoint H t = H) (hDodd : Odd (Nat.card (twoPoint H t)))
    (hHn : H ≤ Subgroup.normalizer (W : Set G))
    (hcard : (K : Set G).ncard = (involutions (H : Set G)).ncard)
    (htrans : ∀ u ∈ involutions (H:Set G), ∀ v ∈ involutions (H:Set G), ∃ k ∈ K, k * u * k⁻¹ = v)
    (hfree : ∀ k ∈ K, k ≠ 1 → ∀ u ∈ involutions (H:Set G), k * u * k⁻¹ ≠ u)
    (hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k}:Set G) ⊓ W = K)
    (hHer : HeringProp) (hVI : AppVIProp) :
    W ≤ (W ⊓ Subgroup.centralizer (involutions (H:Set G))) ⊔
          (W ⊓ Subgroup.normalizer (K:Set G)) := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  letI : MulAction ↥W (InvSub H) := invAct hWH
  let K' : Subgroup ↥W := K.subgroupOf W
  have hK'mem : ∀ x : ↥W, x ∈ K' ↔ (x : G) ∈ K := fun x => Subgroup.mem_subgroupOf
  have hI0 : 1 < Fintype.card (InvSub H) := by
    have h2 : 2 ≤ (involutions (H:Set G)).ncard := Work.ThmF.Bender.cardInvGeTwo hH hfour
    obtain ⟨u, hu, v, hv, huv⟩ :=
      (Set.one_lt_ncard (s := involutions (H : Set G)) (Set.toFinite _)).mp (by omega)
    exact Fintype.one_lt_card_iff.mpr ⟨⟨u, hu⟩, ⟨v, hv⟩, fun h => huv (Subtype.ext_iff.mp h)⟩
  have hreg0 : ∀ i j : InvSub H, ∃! k : K', (k : ↥W) • i = j := by
    intro i j
    obtain ⟨k0, hk0K, hk0eq⟩ := htrans (i : G) i.2 (j : G) j.2
    refine ⟨⟨⟨k0, hKW hk0K⟩, hk0K⟩, ?_, ?_⟩
    · apply Subtype.ext
      show k0 * (i : G) * k0⁻¹ = (j : G)
      exact hk0eq
    · intro y hy
      have hyG : ((y : ↥W) : G) * (i : G) * (((y : ↥W) : G))⁻¹ = (j : G) := by
        have h := congrArg (fun z : InvSub H => (z : G)) hy
        change ((y : ↥W) : G) * (i : G) * (((y : ↥W) : G))⁻¹ = (j : G) at h
        exact h
      have hyK : ((y : ↥W) : G) ∈ K := (hK'mem y).mp y.2
      have hconj : (k0⁻¹ * ((y : ↥W) : G)) * (i : G) * (k0⁻¹ * ((y : ↥W) : G))⁻¹ = (i : G) := by
        calc (k0⁻¹ * ((y : ↥W) : G)) * (i : G) * (k0⁻¹ * ((y : ↥W) : G))⁻¹
            = k0⁻¹ * (((y : ↥W) : G) * (i : G) * (((y : ↥W) : G))⁻¹) * k0 := by group
          _ = k0⁻¹ * (j : G) * k0 := by rw [hyG]
          _ = k0⁻¹ * (k0 * (i : G) * k0⁻¹) * k0 := by rw [← hk0eq]
          _ = (i : G) := by group
      have hmem : k0⁻¹ * ((y : ↥W) : G) ∈ K := K.mul_mem (K.inv_mem hk0K) hyK
      have h1 : k0⁻¹ * ((y : ↥W) : G) = 1 := by
        by_contra hne
        exact hfree _ hmem hne (i : G) i.2 hconj
      apply Subtype.ext
      apply Subtype.ext
      calc ((y : ↥W) : G) = k0 * (k0⁻¹ * ((y : ↥W) : G)) := by group
        _ = k0 * 1 := by rw [h1]
        _ = k0 := mul_one k0
  have hcent' : ∀ k ∈ K', k ≠ 1 → Subgroup.centralizer ({k} : Set ↥W) = K' := by
    intro k hk hk1
    have hkG : (k : G) ∈ K := (hK'mem k).mp hk
    have hkG1 : (k : G) ≠ 1 := fun h => hk1 (Subtype.ext (by simpa using h))
    have hchar : ∀ x : ↥W, (x : G) ∈ K ↔
        (x : G) ∈ Subgroup.centralizer ({(k : G)} : Set G) ⊓ W := by
      intro x
      rw [← hcent (k : G) hkG hkG1]
    apply le_antisymm
    · intro x hx
      have hxc : x * k = k * x := Subgroup.mem_centralizer_singleton_iff.mp hx
      have hxG : (x : G) * (k : G) = (k : G) * (x : G) := by
        have h2 := congrArg (fun z : ↥W => (z : G)) hxc
        change (x : G) * (k : G) = (k : G) * (x : G) at h2
        exact h2
      exact (hK'mem x).mpr ((hchar x).mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hxG, x.2⟩)
    · intro x hx
      have hxK : (x : G) ∈ K := (hK'mem x).mp hx
      have hxG : (x : G) * (k : G) = (k : G) * (x : G) :=
        Subgroup.mem_centralizer_singleton_iff.mp ((hchar x).mp hxK).1
      change x ∈ Subgroup.centralizer ({k} : Set ↥W)
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      change (x : G) * (k : G) = (k : G) * (x : G)
      exact hxG
  have hI : 1 < Fintype.card (ULift (InvSub H)) := by rwa [Fintype.card_ulift]
  have hreg : ∀ i j : ULift (InvSub H), ∃! k : K', (k : ↥W) • i = j := by
    intro i j
    obtain ⟨i'⟩ := i
    obtain ⟨j'⟩ := j
    obtain ⟨k, hk, huniq⟩ := hreg0 i' j'
    refine ⟨k, ?_, ?_⟩
    · show (k : ↥W) • (ULift.up i') = ULift.up j'
      rw [show (k : ↥W) • (ULift.up i') = ULift.up ((k : ↥W) • i') from rfl, hk]
    · intro y hy
      apply huniq
      have hh := congrArg ULift.down hy
      change (y : ↥W) • i' = j' at hh
      exact hh
  have hmain := hVI (W := ↥W) (I := ULift (InvSub H)) K' hI hreg hcent'
  rcases hmain with hdt | hgen
  · exfalso
    have hfW : HasFourGroup ↥W :=
      hasFourGroup_subgroupOf hH hfour hWH hWD inf_le_left hHn hDodd
    refine hHer ↥W ?_ ?_ hfW
    · have hsub := involutions_subset_of_sup_eq hWH hWD inf_le_left hHn hDodd
      have h2 : 2 ≤ (involutions (H:Set G)).ncard := Work.ThmF.Bender.cardInvGeTwo hH hfour
      obtain ⟨u, hu, -, -, -⟩ :=
        (Set.one_lt_ncard (s := involutions (H : Set G)) (Set.toFinite _)).mp (by omega)
      have huW : u ∈ W := hsub hu
      have hu2 : orderOf u = 2 := (Work.ThreePoints.mem_involutions.mp hu).2
      have := Subgroup.orderOf_dvd_natCard W huW
      rw [hu2] at this
      exact even_iff_two_dvd.mpr this
    · intro a b c d ha2 hb2 hc2 hd2 hab hcd
      -- transfer the double transitivity back from `ULift`
      have hdt0 : MulAction.IsMultiplyPretransitive ↥W (InvSub H) 2 := by
        refine ⟨fun f₁ f₂ => ?_⟩
        let f₁' : Fin 2 ↪ ULift (InvSub H) :=
          ⟨fun i => ULift.up (f₁ i), fun i j h => f₁.injective (ULift.up_inj.mp h)⟩
        let f₂' : Fin 2 ↪ ULift (InvSub H) :=
          ⟨fun i => ULift.up (f₂ i), fun i j h => f₂.injective (ULift.up_inj.mp h)⟩
        obtain ⟨g, hg⟩ := hdt.exists_smul_eq f₁' f₂'
        refine ⟨g, ?_⟩
        apply Function.Embedding.ext
        intro i
        have hh := congrArg (fun f : Fin 2 ↪ ULift (InvSub H) => ULift.down (f i)) hg
        change (g : ↥W) • (f₁ i) = f₂ i at hh
        exact hh
      let memI : ∀ x : ↥W, orderOf x = 2 → InvSub H := fun x hx =>
        ⟨(x : G), Work.ThreePoints.mem_involutions.mpr
          ⟨hWH x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩⟩
      have hAB : memI a ha2 ≠ memI b hb2 := fun h => hab (Subtype.ext (by
        have hh := congrArg (fun z : InvSub H => (z : G)) h
        change (a : G) = (b : G) at hh
        exact hh))
      have hCD : memI c hc2 ≠ memI d hd2 := fun h => hcd (Subtype.ext (by
        have hh := congrArg (fun z : InvSub H => (z : G)) h
        change (c : G) = (d : G) at hh
        exact hh))
      obtain ⟨g, hgA, hgB⟩ := exists_smul_eq_pair_of_two_transitive hdt0 hAB hCD
      refine ⟨g, ?_, ?_⟩
      · apply Subtype.ext
        have h0 := congrArg (fun z : InvSub H => (z : G)) hgA
        change (g : G) * (a : G) * (g : G)⁻¹ = (c : G) at h0
        simpa using h0
      · apply Subtype.ext
        have h0 := congrArg (fun z : InvSub H => (z : G)) hgB
        change (g : G) * (b : G) * (g : G)⁻¹ = (d : G) at h0
        simpa using h0
  · intro w hw
    have hset : (↑(⊤ : Subgroup ↥W) : Set ↥W) =
        (((MulAction.toPermHom ↥W (ULift (InvSub H))).ker : Set ↥W) *
          (Subgroup.normalizer (K' : Set ↥W) : Set ↥W)) := by
      rw [← hgen]
      exact Subgroup.normal_mul (MulAction.toPermHom ↥W (ULift (InvSub H))).ker
        (Subgroup.normalizer (K' : Set ↥W))
    have hwmem : (⟨w, hw⟩ : ↥W) ∈
        (((MulAction.toPermHom ↥W (ULift (InvSub H))).ker : Set ↥W) *
          (Subgroup.normalizer (K' : Set ↥W) : Set ↥W)) := by
      rw [← hset]; exact Subgroup.mem_top _
    obtain ⟨c, hc, n, hn, hcn⟩ := Set.mem_mul.mp hwmem
    have hcG : (c : G) ∈ W ⊓ Subgroup.centralizer (involutions (H:Set G)) := by
      refine ⟨c.2, ?_⟩
      change (c : G) ∈ Subgroup.centralizer (involutions (H:Set G))
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hfix : (c : ↥W) • (ULift.up (⟨y, hy⟩ : InvSub H)) = ULift.up (⟨y, hy⟩ : InvSub H) := by
        have h : (MulAction.toPermHom ↥W (ULift (InvSub H))) c = 1 := hc
        have h2 : ((MulAction.toPermHom ↥W (ULift (InvSub H))) c) (ULift.up (⟨y, hy⟩ : InvSub H))
            = ULift.up (⟨y, hy⟩ : InvSub H) := by rw [h]; rfl
        simpa using h2
      have hh := congrArg ULift.down hfix
      change (c : ↥W) • (⟨y, hy⟩ : InvSub H) = (⟨y, hy⟩ : InvSub H) at hh
      have h2 := congrArg (fun z : InvSub H => (z : G)) hh
      change (c : G) * y * (c : G)⁻¹ = y at h2
      calc y * (c : G) = ((c : G) * y * (c : G)⁻¹) * (c : G) := by rw [h2]
        _ = (c : G) * y := by group
    have hnG : (n : G) ∈ W ⊓ Subgroup.normalizer (K : Set G) := by
      refine ⟨n.2, ?_⟩
      change (n : G) ∈ Subgroup.normalizer (K : Set G)
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have hh' : (⟨h, hKW hh⟩ : ↥W) ∈ K' := (hK'mem ⟨h, hKW hh⟩).mpr hh
        have h2 := (Subgroup.mem_normalizer_iff.mp hn) (⟨h, hKW hh⟩ : ↥W)
        have h3 : (n * ⟨h, hKW hh⟩ * n⁻¹ : ↥W) ∈ K' := h2.mp hh'
        have h4 := (hK'mem (n * ⟨h, hKW hh⟩ * n⁻¹)).mp h3
        simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h4
      · intro hh
        have hninv : (n⁻¹ : ↥W) ∈ Subgroup.normalizer (K' : Set ↥W) :=
          (Subgroup.normalizer (K' : Set ↥W)).inv_mem hn
        have hhn : (⟨(n : G) * h * (n : G)⁻¹, hKW hh⟩ : ↥W) ∈ K' :=
          (hK'mem ⟨(n : G) * h * (n : G)⁻¹, hKW hh⟩).mpr hh
        have h2 := (Subgroup.mem_normalizer_iff.mp hninv) (⟨(n : G) * h * (n : G)⁻¹, hKW hh⟩ : ↥W)
        have h3 : (n⁻¹ * ⟨(n : G) * h * (n : G)⁻¹, hKW hh⟩ * n⁻¹⁻¹ : ↥W) ∈ K' := h2.mp hhn
        have h4 := (hK'mem (n⁻¹ * ⟨(n : G) * h * (n : G)⁻¹, hKW hh⟩ * n⁻¹⁻¹)).mp h3
        have h5 : (((n⁻¹ * ⟨(n : G) * h * (n : G)⁻¹, hKW hh⟩ * n⁻¹⁻¹ : ↥W)) : G) = h := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]; group
        rwa [h5] at h4
    have hcw : (c : G) * (n : G) = w := by
      have hh := congrArg (fun z : ↥W => (z : G)) hcn
      simpa using hh
    rw [← hcw]
    exact Subgroup.mul_mem_sup hcG hnG

/-- **Peterfalvi I Ch. III §3 Prop. 2** (p.178).  With `H` strongly embedded, `t ∉ H` an involution,
`D = H ∩ H^t`, `V = C_D(t)`, `K = J(D,t)`, `W ⊴ H` with `H = W·D`, and `E = W ∩ D`: if `E`, acting
on `Inv(H)` by conjugation, is a Frobenius group with kernel `K` and complement `E ∩ V` (the
conclusion of §3 Prop. 1), then `D` has a normal complement in `H`.

Route (pp. 178–179).  The elements `≠ 1` of `K` fix no involution of `H`, and `|E| = |K|·|V ∩ E|`
since `K ⊆ E` (§2 Lemma 1); so `K` is the Frobenius kernel of `E` and acts regularly on `Inv H`
(Ch. I §2 Prop. 2 = `BenderPrelimProp`).  Since `t` inverts the elements of `K`, `K` is abelian.
For `k ∈ K#` the fixed points of `k` in `Ω = G ⧸ H` are exactly `H` and `H^t` (Ch. II §4 Prop. 2(c)
= `ChIIFourProp`), so `C_W(k) ⊆ C_H(k) ⊆ D`, whence `C_W(k) = C_E(k) = K`.  `App. VI` gives
`W = C_W(Inv H)·N_W(K)` or `W` 2-transitive on `Inv H`; since `Inv H ⊆ W ⊇` a four-group of `G`
(`Situation G`), `W` has 2-rank `≥ 2`, so Hering's theorem (`HeringProp`) excludes double
transitivity.  Finally `N_W(K) ⊆ D` because `W ≤ H` and `K` fixes exactly `H, H^t`; hence
`H = W·D = C_H(Inv H)·D`, and the Corollary of §2 Prop. 1 (`Section2CorollaryProp`) concludes. -/
theorem section3_prop2 (hVI : Work.NormalComplement.AppVIProp)
    (hHer : Submission.Blueprint.HeringProp)
    (hS2c : Work.NormalComplement.Section2CorollaryProp)
    (hBP : Work.NormalComplement.BenderPrelimProp)
    (hC4 : Submission.Blueprint.ChIIFourProp) : Work.NormalComplement.Section3Prop2 := by
  intro G _ _ hSit H hH t ht htH W hWH hHn hWD hFrob
  obtain ⟨K, hKset, hKnorm, hKinf, hKsup, hKfpf⟩ := hFrob
  have hDleH : twoPoint H t ≤ H := inf_le_left
  have hDodd : Odd (Nat.card (twoPoint H t)) := hH.2.2 t htH
  have hfour : HasFourGroup G := hSit.1.1
  have hcardK : (K : Set G).ncard = (involutions (H : Set G)).ncard :=
    Kset_ncard hH ht htH hKset
  have hKabel : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := Kset_abelian ht hKset
  have hC4' := hC4 G hSit H hH t ht htH
  have hP2c : ∀ x ∈ Kset (twoPoint H t) t, x ≠ 1 →
      (fixedPts H (Subgroup.zpowers x)).ncard = 2 := hC4'.2.2.1
  have hKsetmem : ∀ k ∈ K, k ∈ Kset (twoPoint H t) t := fun k hk => by rw [← hKset]; exact hk
  have hfixed : ∀ k ∈ K, k ≠ 1 → fixedPts H (Subgroup.zpowers k)
      = {((1 : G) : G ⧸ H), (t : G ⧸ H)} :=
    fun k hk hk1 => fixedPts_eq_pair hH ht htH (hKsetmem k hk) hk1 (hP2c k (hKsetmem k hk) hk1)
  have hfree : ∀ k ∈ K, k ≠ 1 → ∀ u ∈ involutions (H:Set G), k * u * k⁻¹ ≠ u := by
    intro k hk hk1 u hu
    exact no_involution_fixed_of_mem_Kset hH ht htH (hKsetmem k hk) hk1
      (hP2c k (hKsetmem k hk) hk1) hDodd hu.1 hu.2
  have htrans : ∀ u ∈ involutions (H:Set G), ∀ v ∈ involutions (H:Set G),
      ∃ k ∈ K, k * u * k⁻¹ = v :=
    Kset_transitive_on_involutions ht htH hKset hcardK hfree
  have hKD : (K : Set G) ⊆ (twoPoint H t : Set G) := fun k hk => (hKsetmem k hk).1
  have hKH : (K : Set G) ⊆ (H : Set G) := fun k hk => (hKD hk).1
  have hKHt : (K : Set G) ⊆ (conj t H : Set G) := fun k hk => (hKD hk).2
  have hKW : K ≤ W := by
    have h1 : K ≤ K ⊔ (W ⊓ centD H t) := le_sup_left
    rw [hKsup] at h1
    exact le_trans h1 inf_le_left
  have hKne : ∃ k ∈ K, k ≠ 1 := by
    by_contra h
    push_neg at h
    have h2 : 2 ≤ (K : Set G).ncard := by
      rw [hcardK]; exact Work.ThmF.Bender.cardInvGeTwo hH hfour
    have hle : (K : Set G).ncard ≤ ({1} : Set G).ncard :=
      Set.ncard_le_ncard (fun x hx => by simpa using h x hx)
    rw [Set.ncard_singleton] at hle
    omega
  have hEnorm : W ⊓ twoPoint H t ≤ Subgroup.normalizer (K : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh; exact hKnorm w hw h hh
    · intro hh
      have hw' : w⁻¹ ∈ W ⊓ twoPoint H t := ⟨W.inv_mem hw.1, (twoPoint H t).inv_mem hw.2⟩
      have h2 := hKnorm w⁻¹ hw' (w * h * w⁻¹) hh
      rwa [show w⁻¹ * (w * h * w⁻¹) * (w⁻¹)⁻¹ = h from by group] at h2
  have hCltD : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k}:Set G) ⊓ W ≤ twoPoint H t := by
    intro k hk hk1 x hx
    obtain ⟨hxc, hxW⟩ := hx
    have hxk : x * k = k * x := Subgroup.mem_centralizer_singleton_iff.mp hxc
    exact mem_twoPoint_of_commute_of_mem_Kset hH ht htH (hKsetmem k hk) hk1
      (hP2c k (hKsetmem k hk) hk1) (hWH hxW) hxk
  have hcent : ∀ k ∈ K, k ≠ 1 → Subgroup.centralizer ({k}:Set G) ⊓ W = K :=
    centralizer_in_W_eq_K hKabel hEnorm hKsup hKfpf hCltD
  have hNleD : W ⊓ Subgroup.normalizer (K : Set G) ≤ twoPoint H t :=
    normalizer_in_W_le_twoPoint hH ht htH hWH hKH hKHt hKne hfixed
  have hBl : W ≤ (W ⊓ Subgroup.centralizer (involutions (H:Set G))) ⊔
      (W ⊓ Subgroup.normalizer (K:Set G)) :=
    W_le_centralizer_sup_normalizer hH ht htH hfour hWH hKW hWD hDodd hHn hcardK htrans hfree
      hcent hHer hVI
  have hHCsupD : (H ⊓ Subgroup.centralizer (involutions (H:Set G))) ⊔ twoPoint H t = H := by
    apply le_antisymm
    · exact sup_le inf_le_left hDleH
    · calc H = W ⊔ twoPoint H t := hWD.symm
        _ ≤ (H ⊓ Subgroup.centralizer (involutions (H:Set G))) ⊔ twoPoint H t := by
            refine sup_le ?_ le_sup_right
            refine le_trans hBl (sup_le_sup ?_ hNleD)
            exact le_inf (le_trans inf_le_left hWH) inf_le_right
  exact hS2c G hSit H hH t ht htH hHCsupD

end Work.NormalComplement
