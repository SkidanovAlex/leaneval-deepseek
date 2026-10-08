import Mathlib
import Submission.Work.NormalComplement.Design.Extra
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3Sub.prop3b_support
import Submission.Work.ThreePoints.P3Sub.p3pkg_of_subnormal
import Submission.Work.ThreePoints.P3NeBot.app3_1
import Submission.Work.ThreePoints.P3NeBot.Basic
import Submission.Work.ThreePoints.P3NeBot.maximal_of_twoTransitive
import Submission.Work.ThreePoints.sec4_prop3_cd_ne_bot
import Submission.Work.NormalComplement.p2a_invol_unique
import Submission.Work.NormalComplement.involutions_eq_of_odd_index
import Submission.Work.NormalComplement.card_sup_mul_card_inf
import Submission.Work.ThreePoints.ThmC.odd_ncard_of_unique_fixed
import Submission.Work.BrauerSuzuki.Main
import Submission.Work.Models.models
import Submission.Work.DoubleTransitivity.Sec7.ThmA
import Submission.Work.ThmF.ChV12.glaubermanZJ_free

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open Classical
open scoped Pointwise
open LeanEval.GroupTheory.Defs

namespace Work.NormalComplement

/-! ## Auxiliary group-theoretic lemmas used by `p2a_appIII_data` -/

/-- If `S ≤ L` is normal in `L` of odd index and `S` has a unique involution, then `L` has a
unique involution. -/
private lemma inv_eq_one_of_normal_odd_index {G : Type} [Group G] [Finite G]
    {L S : Subgroup G} (hSL : S ≤ L) (hSn : (S.subgroupOf L).Normal)
    (hindex : Odd (S.subgroupOf L).index)
    (hS : {x : G | x ∈ S ∧ orderOf x = 2}.ncard = 1) :
    {x : G | x ∈ L ∧ orderOf x = 2}.ncard = 1 := by
  haveI : (S.subgroupOf L).Normal := hSn
  have hset : {x : G | x ∈ L ∧ orderOf x = 2} = {x : G | x ∈ S ∧ orderOf x = 2} := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨hxL, hx2⟩ := hx
      refine ⟨?_, hx2⟩
      have hx2' : orderOf (⟨x, hxL⟩ : ↥L) = 2 := by
        rw [← Subgroup.orderOf_coe (⟨x, hxL⟩ : ↥L)]; exact hx2
      exact Subgroup.mem_subgroupOf.mp (mem_of_orderOf_eq_two_of_odd_index hindex hx2')
    · intro x hx; exact ⟨hSL hx.1, hx.2⟩
  rw [hset, hS]

/-- A homomorphism with odd-order kernel does not change the number of involutions: if `L` has a
unique involution then so does `L.map f`. -/
private lemma inv_map_eq_one_of_odd_ker {X Y : Type} [Group X] [Finite X] [Group Y]
    (f : X →* Y) (hodd : Odd (Nat.card f.ker)) {L : Subgroup X}
    (hL : {x : X | x ∈ L ∧ orderOf x = 2}.ncard = 1) :
    {y : Y | y ∈ (L.map f : Subgroup Y) ∧ orderOf y = 2}.ncard = 1 := by
  obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp hL
  have hzmem : z ∈ {x : X | x ∈ L ∧ orderOf x = 2} := by rw [hz]; exact rfl
  obtain ⟨hzL, hz2⟩ := hzmem
  have hzker : z ∉ f.ker := by
    intro h
    have hdvd : orderOf z ∣ Nat.card f.ker := Subgroup.orderOf_dvd_natCard f.ker h
    rw [hz2] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hfz2 : orderOf (f z) = 2 := by
    have hdvd : orderOf (f z) ∣ 2 := by rw [← hz2]; exact orderOf_map_dvd f z
    rcases Nat.prime_two.eq_one_or_self_of_dvd (orderOf (f z)) hdvd with h | h
    · exact absurd (hzker (MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp h))) (by simp)
    · exact h
  rw [Set.ncard_eq_one]
  refine ⟨f z, ?_⟩
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hyL, hy2⟩
    obtain ⟨x, hxL, hxy⟩ := Subgroup.mem_map.mp hyL
    have hy2' : orderOf (f x) = 2 := by rw [hxy]; exact hy2
    rw [← hxy]
    have hfx2 : (f x) ^ 2 = 1 := by rw [← hy2']; exact pow_orderOf_eq_one (f x)
    have hx2ker : x ^ 2 ∈ f.ker := by rw [MonoidHom.mem_ker, map_pow]; exact hfx2
    have hx2dvd : orderOf (x ^ 2) ∣ Nat.card f.ker :=
      Subgroup.orderOf_dvd_natCard f.ker hx2ker
    have hxk2 : (x ^ Nat.card f.ker) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact (orderOf_dvd_iff_pow_eq_one).mp hx2dvd
    have hfxk : f (x ^ Nat.card f.ker) = f x := by
      rw [map_pow]
      obtain ⟨m, hm⟩ := hodd
      rw [hm, pow_succ, pow_mul, hfx2, one_pow, one_mul]
    have hxkne : x ^ Nat.card f.ker ≠ 1 := by
      intro h1
      have : f x = 1 := by rw [← hfxk, h1, map_one]
      rw [this] at hy2'
      simp at hy2'
    have hxkord : orderOf (x ^ Nat.card f.ker) = 2 := by
      have hdvd : orderOf (x ^ Nat.card f.ker) ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]; exact hxk2
      rcases Nat.prime_two.eq_one_or_self_of_dvd (orderOf (x ^ Nat.card f.ker)) hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hxkne
      · exact h
    have hxkeq : x ^ Nat.card f.ker = z := by
      have : x ^ Nat.card f.ker ∈ ({z} : Set X) := by
        rw [← hz]; exact ⟨L.pow_mem hxL _, hxkord⟩
      simpa using this
    rw [← hfxk, hxkeq]
  · rintro rfl
    exact ⟨Subgroup.mem_map.mpr ⟨z, hzL, rfl⟩, hfz2⟩

/-- If a finite group acts on a set of odd cardinality with all point stabilisers containing a
unique involution, then it has no four-group. -/
private theorem not_hasFourGroup_of_odd_card_stab_unique {X : Type} [Group X] [Finite X]
    {α : Type} [MulAction X α] [Finite α]
    (hodd : Odd (Nat.card α))
    (hstab : ∀ z : α,
      {x : X | x ∈ (MulAction.stabilizer X z : Subgroup X) ∧ orderOf x = 2}.ncard = 1) :
    ¬ ∃ a b : X, orderOf a = 2 ∧ orderOf b = 2 ∧ a ≠ b ∧ a * b = b * a := by
  rintro ⟨a, b, ha2, hb2, hab, hcomm⟩
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have hbb : b * b = 1 := by rw [← pow_two, ← hb2, pow_orderOf_eq_one]
  have hinv_a : Function.Involutive (fun z : α => a • z) := by
    intro z
    show a • (a • z) = z
    rw [← mul_smul, haa, one_smul]
  have hinv_b : Function.Involutive (fun z : α => b • z) := by
    intro z
    show b • (b • z) = z
    rw [← mul_smul, hbb, one_smul]
  set Fb : Set α := {z | b • z = z} with hFb
  set T : Set α := {z | b • z ≠ z} with hT
  have hFb_map : ∀ z ∈ Fb, a • z ∈ Fb := by
    intro z hz
    simp only [hFb, Set.mem_ofPred_eq] at hz ⊢
    rw [← mul_smul, ← hcomm, mul_smul, hz]
  have hFb_fix : ∀ z ∈ Fb, a • z ≠ z := by
    intro z hz hcon
    simp only [hFb, Set.mem_ofPred_eq] at hz
    have haz : a ∈ MulAction.stabilizer X z := MulAction.mem_stabilizer_iff.mpr hcon
    have hbz : b ∈ MulAction.stabilizer X z := MulAction.mem_stabilizer_iff.mpr hz
    have h2 : 2 ≤ {x : X | x ∈ (MulAction.stabilizer X z : Subgroup X) ∧ orderOf x = 2}.ncard := by
      have hsub : ({a, b} : Set X) ⊆
          {x : X | x ∈ (MulAction.stabilizer X z : Subgroup X) ∧ orderOf x = 2} := by
        intro y hy
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
        rcases hy with rfl | rfl
        · exact ⟨haz, ha2⟩
        · exact ⟨hbz, hb2⟩
      calc 2 = ({a, b} : Set X).ncard := (Set.ncard_pair hab).symm
        _ ≤ _ := Set.ncard_le_ncard hsub
    rw [hstab z] at h2; omega
  have heven_Fb : Even Fb.ncard :=
    Work.ThreePoints.ThmC.even_ncard_of_fpf_involutive (fun z => a • z) hinv_a hFb_map hFb_fix
  have hT_map : ∀ z ∈ T, b • z ∈ T := by
    intro z hz
    simp only [hT, Set.mem_ofPred_eq] at hz ⊢
    intro hcon
    have hbz : b • (b • z) = z := by rw [← mul_smul, hbb, one_smul]
    rw [hbz] at hcon
    exact hz hcon.symm
  have hT_fix : ∀ z ∈ T, b • z ≠ z := by
    intro z hz; simpa only [hT, Set.mem_ofPred_eq] using hz
  have heven_T : Even T.ncard :=
    Work.ThreePoints.ThmC.even_ncard_of_fpf_involutive (fun z => b • z) hinv_b hT_map hT_fix
  have hcard : Nat.card α = Fb.ncard + T.ncard := by
    have hunion : Fb ∪ T = Set.univ := by
      ext z
      simp only [Set.mem_union, hFb, hT, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      by_cases h : b • z = z
      · exact Or.inl h
      · exact Or.inr h
    have hdisj : Disjoint Fb T := by
      rw [Set.disjoint_left]
      intro z hz1 hz2
      simp only [hFb, Set.mem_ofPred_eq] at hz1
      simp only [hT, Set.mem_ofPred_eq] at hz2
      exact hz2 hz1
    have h := Set.ncard_union_eq hdisj (Set.toFinite Fb) (Set.toFinite T)
    rw [hunion, Set.ncard_univ] at h
    exact h
  have heven : Even (Nat.card α) := by
    rw [hcard]; exact heven_Fb.add heven_T
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- `MulAut.conj g` applied through the monoid-hom coercion (definitional but syntactically
different from `MulAut.conj_apply`). -/
private lemma conjHom_apply {F : Type} [Group F] (g h : F) :
    (↑(MulAut.conj g) : F →* F) h = g * h * g⁻¹ := MulAut.conj_apply g h

theorem p2a_appIII_data (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC : Submission.Blueprint.ThmCProp) (hIII : Work.NormalComplement.AppIIIProp)
    {G : Type} [Group G] [Finite G] {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ}
    {P A : Subgroup G} {r : ℕ} (h : Work.NormalComplement.Design.Setup5 G H t W p P A r)
    {S : Subgroup G} (hSpg : IsPGroup 2 S)
    (hSle : S ≤ Work.ThreePoints.p3F (Submission.Blueprint.centD H t) ⊓ H)
    (hSnorm : H ⊓ Subgroup.normalizer (Submission.Blueprint.centD H t : Set G) ≤
      Subgroup.normalizer (S : Set G))
    (hSD : S ⊓ Submission.Blueprint.twoPoint H t = ⊥)
    (hSsup : S ⊔ (Submission.Blueprint.twoPoint H t ⊓
      Subgroup.normalizer (Submission.Blueprint.centD H t : Set G)) =
      H ⊓ Subgroup.normalizer (Submission.Blueprint.centD H t : Set G))
    (hSidx : ¬ 2 ∣ (S.subgroupOf (Work.ThreePoints.p3F (Submission.Blueprint.centD H t) ⊓ H)).index)
    (huniqS : (Submission.Blueprint.involutions (S : Set G)).ncard = 1)
    (hcardS : (Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t)).ncard =
      (S : Set G).ncard + 1) :
    ∃ (f m : ℕ) (Z : Subgroup G), f.Prime ∧
      (Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t)).ncard = f ^ m ∧
      Z ≤ Submission.Blueprint.twoPoint H t ∧
      Work.ThreePoints.p3F (Submission.Blueprint.centD H t) ≤
        Subgroup.normalizer (Z : Set G) ∧
      ∀ u : G, u ∈ H → orderOf u = 2 →
        u ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) →
        (u * t) ^ f ∈ Z := by
  classical
  have ht : orderOf t = 2 := h.invol
  have htH : t ∉ H := h.notMem
  have hHse : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H := h.se
  have hSit : Submission.Blueprint.Situation G := h.sit
  have hBrSz : Submission.Blueprint.BrauerSuzukiProp := Work.BrauerSuzuki.brauerSuzuki
  have hZJ : Submission.Blueprint.GlaubermanZJProp := Work.ThmF.ChV12.glaubermanZJ_free
  have hThmA : Submission.Blueprint.ThmAProp := Work.DoubleTransitivity.Sec7.ThmA hFT hZJ hBrSz
  have hMod : Submission.Blueprint.ModelFactsProp := Work.Models.models hFT
  set F : Subgroup G := Work.ThreePoints.p3F (Submission.Blueprint.centD H t) with hFdef
  set Ω : Set (G ⧸ H) := Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t) with hΩdef
  set Lg : Subgroup ↥F := (F ⊓ H).subgroupOf F with hLgdef
  -- ### Ch. II §4 Prop. 3 at `X = V`
  have hVne : Submission.Blueprint.centD H t ≠ ⊥ := by
    intro hb; exact h.A_ne (le_bot_iff.mp (hb ▸ h.A_le))
  have hSubA : Submission.Blueprint.IsSubnormalIn A (Submission.Blueprint.centD H t) := by
    refine Relation.ReflTransGen.single ⟨h.A_le, ?_⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer h.A_le).mpr h.A_normal
  have hNX_A : Work.ThreePoints.HasNonTrivialNK H t A := by
    have hp2 : 2 ≤ p := h.prime.two_le
    have hcard : 3 ≤ (Work.NormalComplement.Design.CK H t A).ncard := by
      rw [h.A_CK]
      have h4 : 4 ≤ 2 ^ p := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp2
      omega
    obtain ⟨k, hk, hk1⟩ : ∃ k ∈ Work.NormalComplement.Design.CK H t A, k ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      have hsub : Work.NormalComplement.Design.CK H t A ⊆ ({1} : Set G) := fun x hx => by
        simpa using hcon x hx
      have h1 : (Work.NormalComplement.Design.CK H t A).ncard ≤ 1 := by
        calc (Work.NormalComplement.Design.CK H t A).ncard ≤ ({1} : Set G).ncard :=
              Set.ncard_le_ncard hsub (Set.finite_singleton 1)
          _ = 1 := Set.ncard_singleton 1
      omega
    have hkK : k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t := by
      have hkk := hk.1
      simpa [Work.NormalComplement.Design.CK, Work.ThmF.Kset] using hkk
    exact ⟨k, hkK, hk1, Subgroup.centralizer_le_normalizer _ hk.2⟩
  have hPkg : Work.ThreePoints.P3Pkg H t (Submission.Blueprint.centD H t) :=
    Work.ThreePoints.p3pkg hFT hC hThmA hZJ hBrSz hMod hSit hHse ht htH
      (Submission.Blueprint.centD H t) le_rfl ⟨A, h.A_ne, hSubA, hNX_A⟩
  obtain ⟨hP3ab, hNg2t⟩ := hPkg
  obtain ⟨hNGeq, hP3abS⟩ := hP3ab
  have hSharp : ∀ c ∈ Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t),
      c ≠ (QuotientGroup.mk (1 : G) : G ⧸ H) →
      ∃! q : ↥S, (q : G) • (QuotientGroup.mk t : G ⧸ H) = c :=
    Work.ThreePoints.P3Sub.sharpTrans_of_P3Ab_aux (H := H) (X₀ := Submission.Blueprint.centD H t)
      ht htH le_rfl hNg2t hSle hSnorm hSD hSsup
  -- ### `t ∈ F`, `F` preserves `Ω`
  have hFleN : F ≤ Subgroup.normalizer (Submission.Blueprint.centD H t : Set G) :=
    (Work.ThreePoints.p3F_le_centralizer _).trans (Subgroup.centralizer_le_normalizer _)
  have htCent : t ∈ Subgroup.centralizer (Submission.Blueprint.centD H t : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : x ∈ Subgroup.centralizer ({t} : Set G) := (Subgroup.mem_inf.mp hx).2
    rw [Subgroup.mem_centralizer_singleton_iff] at hx'
    exact hx'
  have htF : t ∈ F := by
    rw [hFdef, Work.ThreePoints.mem_p3F]
    refine ⟨⟨t, htCent⟩, ?_, rfl⟩
    exact Work.ThreePoints.involution_mem_oddResidual (by
      apply Subtype.ext
      show t * t = 1
      rw [← pow_two, ← ht, pow_orderOf_eq_one])
  have hpres : ∀ f ∈ F, ∀ c ∈ Ω, f • c ∈ Ω := by
    intro f hf c hc
    rw [hΩdef] at hc ⊢
    exact Work.ThreePoints.smul_mem_fixedPts_of_mem_normalizer (hFleN hf) hc
  have haΩ : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ Ω := by
    rw [hΩdef, Work.ThreePoints.mem_fixedPts_iff_le_stabilizer, Work.ThreePoints.stabilizer_mk,
      Work.DoubleTransitivity.conj_one]
    exact inf_le_left.trans inf_le_left
  -- ### `F` is transitive on `Ω`
  have horbit : MulAction.orbit (↥F) (QuotientGroup.mk (1 : G) : G ⧸ H) = Ω := by
    apply Set.Subset.antisymm
    · intro c hc
      rw [MulAction.mem_orbit_iff] at hc
      obtain ⟨f, hfc⟩ := hc
      rw [← hfc]
      exact hpres f f.2 _ haΩ
    · intro c hc
      rw [hΩdef] at hc
      refine MulAction.mem_orbit_iff.mpr ?_
      by_cases hca : c = (QuotientGroup.mk (1 : G) : G ⧸ H)
      · exact ⟨1, by rw [one_smul, hca]⟩
      · obtain ⟨q, hq, -⟩ := hSharp c hc hca
        refine ⟨⟨(q : G) * t, F.mul_mem (Subgroup.mem_inf.mp (hSle q.2)).1 htF⟩, ?_⟩
        rw [Subgroup.smul_def, mul_smul]
        have ht1 : t • (QuotientGroup.mk (1 : G) : G ⧸ H) = (QuotientGroup.mk t : G ⧸ H) := by
          rw [Work.DoubleTransitivity.smul_mk, mul_one]
        rw [ht1]; exact hq
  have hstabF : MulAction.stabilizer (↥F) (QuotientGroup.mk (1 : G) : G ⧸ H) = Lg := by
    ext x
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    have hcoe : x • (QuotientGroup.mk (1 : G) : G ⧸ H) = (((x : ↥F) : G) : G ⧸ H) := by
      rw [Subgroup.smul_def, Work.DoubleTransitivity.smul_mk, mul_one]
    rw [hcoe, QuotientGroup.eq]
    constructor
    · intro h
      exact ⟨x.2, (Subgroup.inv_mem_iff H).mp (by simpa using h)⟩
    · rintro ⟨-, hxH⟩
      simpa using (Subgroup.inv_mem_iff H).mpr hxH
  have hcardΩ : Ω.ncard = Lg.index := by
    have h1 : Nat.card ↥(MulAction.orbit (↥F) (QuotientGroup.mk (1 : G) : G ⧸ H))
        = Nat.card (↥F ⧸ Lg) := by
      rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (↥F)
        (QuotientGroup.mk (1 : G) : G ⧸ H)), hstabF]
    rw [← Subgroup.index_eq_card Lg] at h1
    rw [horbit, Nat.card_coe_set_eq] at h1
    exact h1
  have hSge2 : 2 ≤ (S : Set G).ncard := by
    have h3 : 3 ≤ Ω.ncard := by
      rw [hΩdef]; exact Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_centD hHse ht htH
    omega
  have hSeven : Even (S : Set G).ncard := by
    have hc : (S : Set G).ncard = Nat.card ↥S := (Nat.card_coe_set_eq (S : Set G)).symm
    rw [hc]
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hSpg
    rw [hk]
    rcases k with _ | k
    · exfalso
      rw [hc, hk] at hSge2
      simp at hSge2
    · rw [pow_succ']; exact even_two_mul (2 ^ k)
  have hOddΩ : Odd Ω.ncard := by
    obtain ⟨m, hm⟩ := hSeven
    rw [hcardS, hm]
    exact ⟨m, by ring⟩
  have hOddα : Odd (Nat.card (↥F ⧸ Lg)) := by
    rw [← Subgroup.index_eq_card Lg, ← hcardΩ]; exact hOddΩ
  -- ### `F ⊓ H` is maximal in `F`
  have hNGeq' : Subgroup.normalizer (Submission.Blueprint.centD H t : Set G) =
      F ⊔ Submission.Blueprint.centD H t := by
    rw [hNGeq, inf_eq_left.mpr Subgroup.le_normalizer, ← hFdef]
  have hdecomp : ∀ y ∈ Subgroup.normalizer (Submission.Blueprint.centD H t : Set G),
      ∃ f ∈ F, ∃ v ∈ Submission.Blueprint.centD H t, f * v = y := by
    intro y hy
    have hVleN : Submission.Blueprint.centD H t ≤
        Subgroup.normalizer (Submission.Blueprint.centD H t : Set G) := Subgroup.le_normalizer
    have hVnorm : ((Submission.Blueprint.centD H t).subgroupOf
        (Subgroup.normalizer (Submission.Blueprint.centD H t : Set G))).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVleN).mpr (le_refl _)
    have hsupN : (F.subgroupOf (Subgroup.normalizer (Submission.Blueprint.centD H t : Set G))) ⊔
        ((Submission.Blueprint.centD H t).subgroupOf
          (Subgroup.normalizer (Submission.Blueprint.centD H t : Set G))) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hFleN hVleN, hNGeq']
      exact Subgroup.subgroupOf_eq_top.mpr le_rfl
    have hy' : (⟨y, hy⟩ : ↥(Subgroup.normalizer (Submission.Blueprint.centD H t : Set G))) ∈
        (F.subgroupOf _) ⊔ ((Submission.Blueprint.centD H t).subgroupOf _) := by
      rw [hsupN]; exact Subgroup.mem_top _
    haveI := hVnorm
    obtain ⟨a, ha, b, hb, hab⟩ :=
      (Subgroup.mem_sup_of_normal_right (s := F.subgroupOf _)
        (t := (Submission.Blueprint.centD H t).subgroupOf _)).mp hy'
    refine ⟨(a : G), Subgroup.mem_subgroupOf.mp ha, (b : G), Subgroup.mem_subgroupOf.mp hb, ?_⟩
    have h1 := congrArg (fun z : ↥(Subgroup.normalizer
      (Submission.Blueprint.centD H t : Set G)) => (z : G)) hab
    rw [Subgroup.coe_mul] at h1
    exact h1
  have hmaxG : ∀ M : Subgroup G, F ⊓ H ≤ M → M ≤ F → M = F ⊓ H ∨ M = F := by
    intro M hLM hMF
    by_cases hMH : M ≤ H
    · exact Or.inl (le_antisymm (le_inf hMF hMH) hLM)
    · right
      rw [SetLike.le_def] at hMH
      push_neg at hMH
      obtain ⟨m, hmM, hmH⟩ := hMH
      have hmF : m ∈ F := hMF hmM
      refine le_antisymm hMF (fun f hfF => ?_)
      by_cases hfH : f ∈ H
      · exact hLM (Subgroup.mem_inf.mpr ⟨hfF, hfH⟩)
      · have haS : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈
            Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t) := by
          rw [← hΩdef]; exact haΩ
        have hmaS : m • (QuotientGroup.mk (1 : G) : G ⧸ H) ∈
            Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t) := by
          rw [← hΩdef]; exact hpres m hmF _ haΩ
        have hfaS : f • (QuotientGroup.mk (1 : G) : G ⧸ H) ∈
            Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t) := by
          rw [← hΩdef]; exact hpres f hfF _ haΩ
        have hmemH : ∀ x : G, x • (QuotientGroup.mk (1 : G) : G ⧸ H) =
            (QuotientGroup.mk (1 : G) : G ⧸ H) → x ∈ H := by
          intro x hx
          have : x ∈ MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) :=
            MulAction.mem_stabilizer_iff.mpr hx
          rwa [Work.ThreePoints.stabilizer_mk, Work.DoubleTransitivity.conj_one] at this
        have hma_ne : m • (QuotientGroup.mk (1 : G) : G ⧸ H) ≠
            (QuotientGroup.mk (1 : G) : G ⧸ H) := fun hc => hmH (hmemH m hc)
        have hfa_ne : f • (QuotientGroup.mk (1 : G) : G ⧸ H) ≠
            (QuotientGroup.mk (1 : G) : G ⧸ H) := fun hc => hfH (hmemH f hc)
        obtain ⟨g, hgN, hga, hgm⟩ := hNg2t _ haS _ hmaS hma_ne.symm _ haS _ hfaS hfa_ne.symm
        obtain ⟨f₁, hf₁F, v, hvV, hgv⟩ := hdecomp g hgN
        have hva : v • (QuotientGroup.mk (1 : G) : G ⧸ H) =
            (QuotientGroup.mk (1 : G) : G ⧸ H) := by
          have hvH : v ∈ H := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hvV).1).1
          have : v ∈ MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) := by
            rw [Work.ThreePoints.stabilizer_mk, Work.DoubleTransitivity.conj_one]; exact hvH
          exact MulAction.mem_stabilizer_iff.mp this
        have hvm : v • (m • (QuotientGroup.mk (1 : G) : G ⧸ H)) =
            m • (QuotientGroup.mk (1 : G) : G ⧸ H) :=
          MulAction.mem_stabilizer_iff.mp
            ((Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mp hmaS) hvV)
        have hf₁a : f₁ • (QuotientGroup.mk (1 : G) : G ⧸ H) =
            (QuotientGroup.mk (1 : G) : G ⧸ H) := by
          have h1 : (f₁ * v) • (QuotientGroup.mk (1 : G) : G ⧸ H) =
              (QuotientGroup.mk (1 : G) : G ⧸ H) := by rw [hgv]; exact hga
          rwa [mul_smul, hva] at h1
        have hf₁M : f₁ ∈ M := hLM (Subgroup.mem_inf.mpr ⟨hf₁F, hmemH f₁ hf₁a⟩)
        have hstab : (f₁ * m)⁻¹ * f ∈ H := by
          have h1 : (f₁ * v) • (m • (QuotientGroup.mk (1 : G) : G ⧸ H)) =
              f • (QuotientGroup.mk (1 : G) : G ⧸ H) := by rw [hgv]; exact hgm
          rw [mul_smul, hvm] at h1
          have h2 : ((f₁ * m)⁻¹ * f) • (QuotientGroup.mk (1 : G) : G ⧸ H) =
              (QuotientGroup.mk (1 : G) : G ⧸ H) := by
            rw [mul_smul, ← h1, ← mul_smul f₁ m (QuotientGroup.mk (1 : G) : G ⧸ H),
              inv_smul_smul]
          exact hmemH _ h2
        have hkey : (f₁ * m)⁻¹ * f ∈ M := by
          apply hLM
          refine Subgroup.mem_inf.mpr ⟨?_, hstab⟩
          have hfeq : (f₁ * m)⁻¹ * f = m⁻¹ * f₁⁻¹ * f := by group
          rw [hfeq]
          exact F.mul_mem (F.mul_mem (F.inv_mem hmF) (F.inv_mem hf₁F)) hfF
        have hff : f = (f₁ * m) * ((f₁ * m)⁻¹ * f) := by group
        rw [hff]; exact M.mul_mem (M.mul_mem hf₁M hmM) hkey
  have hmax' : ∀ M : Subgroup ↥F, Lg ≤ M → M = Lg ∨ M = ⊤ := by
    intro M hM
    have hle : F ⊓ H ≤ M.map (Subgroup.subtype F) := by
      intro x hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩, hM (by rw [hLgdef, Subgroup.mem_subgroupOf]; exact hx), rfl⟩
    rcases hmaxG (M.map (Subgroup.subtype F)) hle (Subgroup.map_subtype_le M) with hcase | hcase
    · left
      refine le_antisymm ?_ hM
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      have h1 : (x : G) ∈ M.map (Subgroup.subtype F) := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      rwa [hcase] at h1
    · right
      refine le_antisymm le_top fun x _ => ?_
      have h1 : (x : G) ∈ M.map (Subgroup.subtype F) := by rw [hcase]; exact x.2
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h1
      rwa [Subtype.ext hyx] at hy
  -- ### `Lg` is strongly embedded in `↥F`; `Lg` and its conjugates have a unique involution
  have hLgSE : LeanEval.GroupTheory.Defs.IsStronglyEmbedded Lg := by
    rw [hLgdef]
    exact Work.ThreePoints.stronglyEmbedded_p3F_inf_H hFT hC hBrSz hSit hHse ht htH le_rfl
  have hTle : F ⊓ H ≤ H ⊓ Subgroup.normalizer (Submission.Blueprint.centD H t : Set G) :=
    le_inf inf_le_right (inf_le_left.trans hFleN)
  have hSn : (S.subgroupOf (F ⊓ H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSle).mpr (hTle.trans hSnorm)
  have hSidxOdd : Odd (S.subgroupOf (F ⊓ H)).index :=
    Nat.not_even_iff_odd.mp (fun h => hSidx (even_iff_two_dvd.mp h))
  have hLHi : {x : G | x ∈ F ⊓ H ∧ orderOf x = 2}.ncard = 1 :=
    inv_eq_one_of_normal_odd_index hSle hSn hSidxOdd (by
      simpa [Submission.Blueprint.involutions] using huniqS)
  have hLgi : {y : ↥F | y ∈ Lg ∧ orderOf y = 2}.ncard = 1 := by
    rw [← hLHi]
    refine Set.ncard_congr (fun y _ => ((y : ↥F) : G)) ?_ ?_ ?_
    · rintro y ⟨hy, hyo⟩
      refine ⟨Subgroup.mem_subgroupOf.mp (by rwa [hLgdef] at hy), ?_⟩
      rw [Subgroup.orderOf_coe y]; exact hyo
    · rintro y1 _ y2 _ heq; exact Subtype.ext heq
    · rintro x ⟨hx, hxo⟩
      refine ⟨⟨x, (Subgroup.mem_inf.mp hx).1⟩, ⟨?_, ?_⟩, rfl⟩
      · rw [hLgdef]; exact Subgroup.mem_subgroupOf.mpr hx
      · rw [← Subgroup.orderOf_coe (⟨x, (Subgroup.mem_inf.mp hx).1⟩ : ↥F)]; exact hxo
  have hconjInvol : ∀ x : ↥F,
      {y : ↥F | y ∈ Lg.map (MulAut.conj x).toMonoidHom ∧ orderOf y = 2}.ncard = 1 := by
    intro x
    obtain ⟨z0, hz0⟩ := Set.ncard_eq_one.mp hLgi
    have hz0mem : z0 ∈ {y : ↥F | y ∈ Lg ∧ orderOf y = 2} := by rw [hz0]; exact rfl
    obtain ⟨hz0L, hz0o⟩ := hz0mem
    rw [Set.ncard_eq_one]
    refine ⟨x * z0 * x⁻¹, ?_⟩
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hy, hyo⟩
      obtain ⟨z, hzL, hzy⟩ := Subgroup.mem_map.mp hy
      have hzo : orderOf z = 2 := by
        have h3 : orderOf ((MulAut.conj x) z) = 2 := by
          rw [show (MulAut.conj x) z = y from hzy]; exact hyo
        rwa [MulEquiv.orderOf_eq (MulAut.conj x) z] at h3
      have hzeq : z = z0 := by
        have hh : z ∈ ({z0} : Set ↥F) := by rw [← hz0]; exact ⟨hzL, hzo⟩
        simpa using hh
      rw [← hzy, hzeq]
      show (MulAut.conj x) z0 = x * z0 * x⁻¹
      rw [MulAut.conj_apply]
    · intro h
      rw [h]
      refine ⟨Subgroup.mem_map.mpr ⟨z0, hz0L, ?_⟩, ?_⟩
      · change (MulAut.conj x) z0 = x * z0 * x⁻¹
        rw [MulAut.conj_apply]
      · rw [show x * z0 * x⁻¹ = (MulAut.conj x) z0 from (MulAut.conj_apply x z0).symm,
          MulEquiv.orderOf_eq (MulAut.conj x) z0]
        exact hz0o
  -- ### the kernel `Zg`
  set Zg : Subgroup ↥F := Lg.normalCore with hZgdef
  have hZgn : Zg.Normal := by rw [hZgdef]; exact Subgroup.normalCore_normal Lg
  haveI := hZgn
  have hZgL : Zg ≤ Lg := by rw [hZgdef]; exact Subgroup.normalCore_le Lg
  haveI hZgLfact : Fact (Zg ≤ Lg) := ⟨hZgL⟩
  have hZg_fixes : ∀ zg ∈ Zg, ∀ ω ∈ Ω, (zg : G) • ω = ω := by
    intro zg hzg ω hω
    have hωorb : ω ∈ MulAction.orbit (↥F) (QuotientGroup.mk (1 : G) : G ⧸ H) := by
      rw [horbit]; exact hω
    rw [MulAction.mem_orbit_iff] at hωorb
    obtain ⟨f, hfω⟩ := hωorb
    have hfsta : f⁻¹ * zg * f ∈ Zg := by simpa using hZgn.conj_mem zg hzg f⁻¹
    have hxf : f⁻¹ * zg * f ∈
        MulAction.stabilizer (↥F) (QuotientGroup.mk (1 : G) : G ⧸ H) := by
      rw [hstabF]; exact hZgL hfsta
    have hfixa : (f⁻¹ * zg * f : ↥F) • (QuotientGroup.mk (1 : G) : G ⧸ H) =
        (QuotientGroup.mk (1 : G) : G ⧸ H) := MulAction.mem_stabilizer_iff.mp hxf
    rw [← hfω]
    show (zg : ↥F) • ((f : ↥F) • (QuotientGroup.mk (1 : G) : G ⧸ H)) =
      (f : ↥F) • (QuotientGroup.mk (1 : G) : G ⧸ H)
    rw [← mul_smul, show (zg : ↥F) * f = f * (f⁻¹ * zg * f) from by group, mul_smul, hfixa]
  have hmktΩ : (QuotientGroup.mk t : G ⧸ H) ∈ Ω := by
    rw [hΩdef]; exact Work.ThreePoints.mk_t_mem_fixedPts_of_le_centD le_rfl
  have hmktΩ' : (QuotientGroup.mk t : G ⧸ H) ∈
      Submission.Blueprint.fixedPts H (Submission.Blueprint.centD H t) := by
    rw [← hΩdef]; exact hmktΩ
  have hZgOdd : Odd (Nat.card ↥Zg) := by
    rw [← Nat.not_even_iff_odd]
    intro hev
    obtain ⟨z, hz2⟩ := exists_prime_orderOf_dvd_card' (G := ↥Zg) 2 (even_iff_two_dvd.mp hev)
    have hzZg : (z : ↥F) ∈ Zg := z.2
    have hzo2 : orderOf (z : ↥F) = 2 := (Subgroup.orderOf_coe z).trans hz2
    have hzL : (z : ↥F) ∈ Lg := hZgL hzZg
    have hzFH : ((z : ↥F) : G) ∈ F ⊓ H := Subgroup.mem_subgroupOf.mp hzL
    have hzo2G : orderOf (((z : ↥F) : G)) = 2 :=
      (Subgroup.orderOf_coe (z : ↥F)).trans hzo2
    have hzS : ((z : ↥F) : G) ∈ S := by
      haveI : (S.subgroupOf (F ⊓ H)).Normal := hSn
      have hx2 : orderOf (⟨((z : ↥F) : G), hzFH⟩ : ↥(F ⊓ H)) = 2 :=
        (Subgroup.orderOf_coe (⟨((z : ↥F) : G), hzFH⟩ : ↥(F ⊓ H))).symm.trans hzo2G
      exact Subgroup.mem_subgroupOf.mp (mem_of_orderOf_eq_two_of_odd_index hSidxOdd hx2)
    have hzfix : ((z : ↥F) : G) • (QuotientGroup.mk t : G ⧸ H) =
        (QuotientGroup.mk t : G ⧸ H) := hZg_fixes _ hzZg _ hmktΩ
    have hmktne : (QuotientGroup.mk t : G ⧸ H) ≠ (QuotientGroup.mk (1 : G) : G ⧸ H) :=
      (Work.ThreePoints.P3Sub.mk_one_ne_mk_t htH).symm
    obtain ⟨q, hq, huniq⟩ := hSharp (QuotientGroup.mk t) hmktΩ' hmktne
    have hq1 : (⟨((z : ↥F) : G), hzS⟩ : ↥S) • (QuotientGroup.mk t : G ⧸ H) =
        (QuotientGroup.mk t : G ⧸ H) := hzfix
    have h1fix : (1 : ↥S) • (QuotientGroup.mk t : G ⧸ H) =
        (QuotientGroup.mk t : G ⧸ H) := one_smul _ _
    have hqeq : (1 : ↥S) = q := huniq 1 h1fix
    have hzeq1 : (⟨((z : ↥F) : G), hzS⟩ : ↥S) = 1 := by
      rw [huniq _ hq1, ← hqeq]
    have hz1 : (z : ↥F) = 1 := by
      apply Subtype.ext
      have h2 := congrArg (fun s : ↥S => (s : G)) hzeq1
      simpa using h2
    rw [hz1] at hzo2
    simp at hzo2
  -- ### `Z ≤ D` and `F ≤ N_G(Z)`
  have hZ_le_D : Zg.map F.subtype ≤ Submission.Blueprint.twoPoint H t := by
    intro z hz
    obtain ⟨zg, hzg, rfl⟩ := Subgroup.mem_map.mp hz
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_subgroupOf.mp (hZgL hzg)).2, ?_⟩
    have hfix : (zg : G) • (QuotientGroup.mk t : G ⧸ H) = (QuotientGroup.mk t : G ⧸ H) :=
      hZg_fixes zg hzg _ hmktΩ
    rw [← Work.ThreePoints.stabilizer_mk H t]
    exact MulAction.mem_stabilizer_iff.mpr hfix
  have hF_le_NZ : F ≤ Subgroup.normalizer (Zg.map F.subtype : Set G) := by
    intro f hf
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨hg, hhg, rfl⟩ := Subgroup.mem_map.mp hh
      refine Subgroup.mem_map.mpr ⟨⟨f, hf⟩ * hg * ⟨f, hf⟩⁻¹,
        hZgn.conj_mem hg hhg ⟨f, hf⟩, ?_⟩
      rfl
    · intro hh
      obtain ⟨hg, hhg, hhgz⟩ := Subgroup.mem_map.mp hh
      have hconj2 : ⟨f, hf⟩⁻¹ * hg * ⟨f, hf⟩ ∈ Zg := by
        have h := hZgn.conj_mem hg hhg ⟨f, hf⟩⁻¹
        rwa [inv_inv] at h
      refine Subgroup.mem_map.mpr ⟨⟨f, hf⟩⁻¹ * hg * ⟨f, hf⟩, hconj2, ?_⟩
      change f⁻¹ * F.subtype hg * f = h
      rw [hhgz]; group
  -- ### point stabilisers of the `F ⧸ Zg`-action on `F ⧸ Lg`
  have hsmulF : ∀ (x y : ↥F), x • (QuotientGroup.mk y : ↥F ⧸ Lg) =
      (QuotientGroup.mk (x * y) : ↥F ⧸ Lg) := fun x y => rfl
  have hstabFbar : ∀ y : ↥F,
      MulAction.stabilizer (↥F ⧸ Zg) (QuotientGroup.mk y : ↥F ⧸ Lg)
      = (Lg.map (MulAut.conj y)).map (QuotientGroup.mk' Zg) := by
    intro y
    ext w
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_map]
    constructor
    · intro hw
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective Zg w
      refine ⟨u, ?_, rfl⟩
      rw [Subgroup.mem_map]
      have h1 : (QuotientGroup.mk (u * y) : ↥F ⧸ Lg) = QuotientGroup.mk y := by
        have h2 := hw
        rw [Work.ThreePoints.P3NeBot.quotient_smul_mk' Zg Lg u (QuotientGroup.mk y)] at h2
        exact h2
      rw [QuotientGroup.eq] at h1
      refine ⟨y⁻¹ * u * y, ?_, by rw [conjHom_apply]; group⟩
      have h1' : y⁻¹ * u⁻¹ * y ∈ Lg := by
        have h3 := h1
        rwa [show (u * y)⁻¹ * y = y⁻¹ * u⁻¹ * y from by group] at h3
      have h2 : (y⁻¹ * u⁻¹ * y)⁻¹ ∈ Lg := Lg.inv_mem h1'
      rwa [show (y⁻¹ * u⁻¹ * y)⁻¹ = y⁻¹ * u * y from by group] at h2
    · rintro ⟨u, hu, rfl⟩
      rw [Work.ThreePoints.P3NeBot.quotient_smul_mk', hsmulF]
      obtain ⟨z', hz'L, hz'u⟩ := Subgroup.mem_map.mp hu
      have huy : u * y = y * z' := by
        rw [← hz'u, conjHom_apply]; group
      rw [huy, QuotientGroup.eq]
      simpa using Lg.inv_mem hz'L
  have hconj1 : Lg.map (MulAut.conj (1 : ↥F)) = Lg := by
    apply le_antisymm
    · rintro y ⟨z, hz, rfl⟩
      rw [conjHom_apply, one_mul, inv_one, mul_one]; exact hz
    · intro z hz
      exact Subgroup.mem_map.mpr ⟨z, hz, by rw [conjHom_apply, one_mul, inv_one, mul_one]⟩
  have hstabBase : MulAction.stabilizer (↥F ⧸ Zg) (QuotientGroup.mk (1 : ↥F) : ↥F ⧸ Lg)
      = Lg.map (QuotientGroup.mk' Zg) := by
    rw [hstabFbar 1, hconj1]
  have hstabAll : ∀ z : ↥F ⧸ Lg,
      {y : ↥F ⧸ Zg | y ∈ MulAction.stabilizer (↥F ⧸ Zg) z ∧ orderOf y = 2}.ncard = 1 := by
    intro z
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective z
    rw [← hy, hstabFbar y]
    exact inv_map_eq_one_of_odd_ker (QuotientGroup.mk' Zg)
      (by rw [QuotientGroup.ker_mk']; exact hZgOdd) (hconjInvol y)
  have hrank : ¬ Submission.Blueprint.HasFourGroup (↥F ⧸ Zg) :=
    not_hasFourGroup_of_odd_card_stab_unique hOddα hstabAll
  -- ### the App. III hypotheses on `↥F ⧸ Zg` acting on `↥F ⧸ Lg`
  have htrans : MulAction.IsPretransitive (↥F ⧸ Zg) (↥F ⧸ Lg) := by
    refine ⟨fun c d => ?_⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective d
    refine ⟨QuotientGroup.mk' Zg (z * y⁻¹), ?_⟩
    rw [Work.ThreePoints.P3NeBot.quotient_smul_mk', hsmulF]
    show (QuotientGroup.mk ((z * y⁻¹) * y) : ↥F ⧸ Lg) = QuotientGroup.mk z
    rw [show (z * y⁻¹) * y = z from by group]
  have hfaith : ∀ g : ↥F ⧸ Zg, (∀ c : ↥F ⧸ Lg, g • c = c) → g = 1 := by
    intro g hg
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Zg g
    have hmem : a⁻¹ ∈ Zg := by
      intro c
      have h1 := hg ((a⁻¹ * c⁻¹ : ↥F) : ↥F ⧸ Lg)
      rw [Work.ThreePoints.P3NeBot.quotient_smul_mk', hsmulF, QuotientGroup.eq] at h1
      have h2 : (a * (a⁻¹ * c⁻¹))⁻¹ * (a⁻¹ * c⁻¹) = c * a⁻¹ * c⁻¹ := by group
      rwa [h2] at h1
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff a).mpr (by simpa using Zg.inv_mem hmem)
  have hSE : LeanEval.GroupTheory.Defs.IsStronglyEmbedded
      (MulAction.stabilizer (↥F ⧸ Zg) (QuotientGroup.mk (1 : ↥F) : ↥F ⧸ Lg)) := by
    rw [hstabBase]
    exact Work.ThreePoints.isStronglyEmbedded_map_quotient Zg hZgOdd hZgL hLgSE
  have hcoatom : IsCoatom (MulAction.stabilizer (↥F ⧸ Zg) (QuotientGroup.mk (1 : ↥F) : ↥F ⧸ Lg)) := by
    rw [hstabBase, isCoatom_iff_ge_of_le]
    constructor
    · intro hcon
      have h1 : Subgroup.comap (QuotientGroup.mk' Zg)
          (Lg.map (QuotientGroup.mk' Zg)) = Lg :=
        Subgroup.comap_map_eq_self (by rw [QuotientGroup.ker_mk']; exact hZgL)
      rw [hcon, Subgroup.comap_top] at h1
      exact Work.ThreePoints.IsStronglyEmbedded.ne_top hLgSE h1.symm
    · intro b' hb' hle
      have hle' : Lg ≤ Subgroup.comap (QuotientGroup.mk' Zg) b' := by
        intro y hy
        rw [Subgroup.mem_comap]
        exact hle (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
      rcases hmax' (Subgroup.comap (QuotientGroup.mk' Zg) b') hle' with hcase | hcase
      · intro y hy
        obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective Zg y
        rw [← hz]
        refine Subgroup.mem_map.mpr ⟨z, ?_, rfl⟩
        have h3 : z ∈ Subgroup.comap (QuotientGroup.mk' Zg) b' := by
          rw [Subgroup.mem_comap, hz]; exact hy
        rwa [hcase] at h3
      · exfalso
        apply hb'
        refine le_antisymm le_top (fun y _ => ?_)
        obtain ⟨z, hz⟩ := QuotientGroup.mk'_surjective Zg y
        have h3 : z ∈ Subgroup.comap (QuotientGroup.mk' Zg) b' := by
          rw [hcase]; exact Subgroup.mem_top z
        rw [Subgroup.mem_comap] at h3
        rwa [hz] at h3
  -- ### App. III gives `f` and `Q`
  obtain ⟨f, Q, hfp, hQn, hQne, hQab, hQexp, hQinf, hQsup, huniq, h4, hoddInv, h5⟩ :=
    hIII (↥F ⧸ Zg) (↥F ⧸ Lg) (QuotientGroup.mk (1 : ↥F) : ↥F ⧸ Lg) htrans hfaith hrank hSE hcoatom
  haveI hQnI : Q.Normal := hQn
  haveI hfpI : Fact (Nat.Prime f) := ⟨hfp⟩
  -- ### `|Ω| = f ^ m`
  have hStabNQ : MulAction.stabilizer (↥F ⧸ Zg) (QuotientGroup.mk (1 : ↥F) : ↥F ⧸ Lg) ≤
      Subgroup.normalizer (Q : Set (↥F ⧸ Zg)) := by
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro h
    exact ⟨fun hh => hQn.conj_mem h hh x, fun hh => by
      have h3 := hQn.conj_mem (x * h * x⁻¹) hh x⁻¹
      rwa [show x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h from by group] at h3⟩
  have hQcard : Nat.card ↥Q =
      (MulAction.stabilizer (↥F ⧸ Zg) (QuotientGroup.mk (1 : ↥F) : ↥F ⧸ Lg)).index := by
    have h1 := Work.NormalComplement.card_sup_mul_card_inf hStabNQ
    rw [hQsup, hQinf, Subgroup.card_top, Subgroup.card_bot, mul_one] at h1
    have h2 : Nat.card (↥F ⧸ Zg) =
        (MulAction.stabilizer (↥F ⧸ Zg) (QuotientGroup.mk (1 : ↥F) : ↥F ⧸ Lg)).index *
          Nat.card ↥(MulAction.stabilizer (↥F ⧸ Zg) (QuotientGroup.mk (1 : ↥F) : ↥F ⧸ Lg)) :=
      (Subgroup.index_mul_card
        (MulAction.stabilizer (↥F ⧸ Zg)
          (QuotientGroup.mk (1 : ↥F) : ↥F ⧸ Lg))).symm
    rw [h2] at h1
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).symm
  have hstabIdx : (MulAction.stabilizer (↥F ⧸ Zg) (QuotientGroup.mk (1 : ↥F) : ↥F ⧸ Lg)).index =
      Lg.index := by
    rw [hstabBase, Subgroup.index_map, QuotientGroup.ker_mk', sup_eq_left.mpr hZgL,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective Zg), Subgroup.index_top, mul_one]
  have hQp : IsPGroup f ↥Q := by
    intro g
    refine ⟨1, ?_⟩
    have h : (g : ↥F ⧸ Zg) ^ f = 1 := hQexp g.1 g.2
    have h' : g ^ f = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h)
    simpa using h'
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hQp
  have hΩf : Ω.ncard = f ^ m := by
    rw [hcardΩ, ← hstabIdx, ← hQcard, hm]
  -- ### the final clause: `(u t)^f ∈ Z`
  refine ⟨f, m, Zg.map F.subtype, hfp, hΩf, hZ_le_D, hF_le_NZ, ?_⟩
  intro u huH hu2 huC
  have huF : u ∈ F := by
    rw [hFdef, Work.ThreePoints.mem_p3F]
    refine ⟨⟨u, huC⟩, ?_, rfl⟩
    exact Work.ThreePoints.involution_mem_oddResidual (by
      apply Subtype.ext
      show u * u = 1
      rw [← pow_two, ← hu2, pow_orderOf_eq_one])
  set ub : ↥F := ⟨u, huF⟩ with hub
  set tb : ↥F := ⟨t, htF⟩ with htb
  have hub_ord : orderOf ub = 2 := by
    rw [← Subgroup.orderOf_coe ub]; simpa [hub] using hu2
  have htb_ord : orderOf tb = 2 := by
    rw [← Subgroup.orderOf_coe tb]; simpa [htb] using ht
  have hub2 : orderOf (QuotientGroup.mk' Zg ub) = 2 := by
    have hdvd : orderOf (QuotientGroup.mk' Zg ub) ∣ 2 := by
      rw [← hub_ord]; exact orderOf_map_dvd (QuotientGroup.mk' Zg) ub
    rcases Nat.prime_two.eq_one_or_self_of_dvd (orderOf (QuotientGroup.mk' Zg ub)) hdvd with h | h
    · exfalso
      have hmem : ub ∈ Zg := (QuotientGroup.eq_one_iff ub).mp (orderOf_eq_one_iff.mp h)
      have hd : orderOf ub ∣ Nat.card ↥Zg := Subgroup.orderOf_dvd_natCard Zg hmem
      rw [hub_ord] at hd
      exact (Nat.not_even_iff_odd.mpr hZgOdd) (even_iff_two_dvd.mpr hd)
    · exact h
  have htb2 : orderOf (QuotientGroup.mk' Zg tb) = 2 := by
    have hdvd : orderOf (QuotientGroup.mk' Zg tb) ∣ 2 := by
      rw [← htb_ord]; exact orderOf_map_dvd (QuotientGroup.mk' Zg) tb
    rcases Nat.prime_two.eq_one_or_self_of_dvd (orderOf (QuotientGroup.mk' Zg tb)) hdvd with h | h
    · exfalso
      have hmem : tb ∈ Zg := (QuotientGroup.eq_one_iff tb).mp (orderOf_eq_one_iff.mp h)
      have hd : orderOf tb ∣ Nat.card ↥Zg := Subgroup.orderOf_dvd_natCard Zg hmem
      rw [htb_ord] at hd
      exact (Nat.not_even_iff_odd.mpr hZgOdd) (even_iff_two_dvd.mpr hd)
    · exact h
  have hubLg : ub ∈ Lg := by rw [hLgdef, Subgroup.mem_subgroupOf]; exact ⟨huF, huH⟩
  have htbLg : tb ∉ Lg := by
    intro h
    have h' : ((tb : ↥F) : G) ∈ F ⊓ H := by
      rw [hLgdef] at h; exact Subgroup.mem_subgroupOf.mp h
    exact htH (by simpa [htb] using h'.2)
  have hne : QuotientGroup.mk' Zg ub ≠ QuotientGroup.mk' Zg tb := by
    intro hcon
    have hcon' : (↑ub : ↥F ⧸ Zg) = ↑tb := by simpa [QuotientGroup.mk'_apply] using hcon
    have hmem : ub⁻¹ * tb ∈ Zg := (QuotientGroup.eq).mp hcon'
    have : tb ∈ Lg := by
      have h2 : ub * (ub⁻¹ * tb) ∈ Lg := Lg.mul_mem hubLg (hZgL hmem)
      rwa [mul_inv_cancel_left] at h2
    exact htbLg this
  obtain ⟨hQmem, hQord⟩ := h4 (QuotientGroup.mk' Zg ub) (QuotientGroup.mk' Zg tb) hub2 htb2 hne
  have hmul : QuotientGroup.mk' Zg ub * QuotientGroup.mk' Zg tb = QuotientGroup.mk' Zg (ub * tb) :=
    (map_mul (QuotientGroup.mk' Zg) ub tb).symm
  have hpow : (QuotientGroup.mk' Zg (ub * tb)) ^ f = 1 := by
    rw [← hmul, ← hQord, pow_orderOf_eq_one]
  have hpowZg : (ub * tb) ^ f ∈ Zg := by
    have h' : QuotientGroup.mk' Zg ((ub * tb) ^ f) = 1 := by rw [map_pow]; exact hpow
    exact (QuotientGroup.eq_one_iff ((ub * tb) ^ f)).mp h'
  refine Subgroup.mem_map.mpr ⟨(ub * tb) ^ f, hpowZg, ?_⟩
  have hcoe : ((ub * tb : ↥F) : G) = u * t := by
    rw [Subgroup.coe_mul, hub, htb]
  rw [← hcoe, map_pow]
  congr 1
end Work.NormalComplement
