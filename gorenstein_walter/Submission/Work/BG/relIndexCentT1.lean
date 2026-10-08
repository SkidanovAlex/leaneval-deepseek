import Mathlib
import Submission.Work.GLUE.Defs
import Submission.Work.BG.ThmABCDefs
import Submission.Work.BG.splitglue.Split
import Submission.Work.BG.fourGroup_centralizer_in_sylow
import Submission.Work.BG.isFourGroup_closure_pair
import Submission.Work.BG.S_le_H
import Submission.Work.BG.nCases
import Submission.Work.GLUE.PiCoreApi
import Submission.Work.GLUE.InBridge
import Submission.Work.BG.cardCentralizerInfSylowT1
import Submission.Work.BG.twoDvdN
import Submission.Work.BG.relIndexEqCardDiv
import Submission.Work.BG.relIndexSupDecomposition

set_option linter.style.haveILetI false

namespace Work.BG

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## Auxiliary lemmas (elementary, used only here)

`O(K)` transported into the ambient group is normal in `K`, and an element of a join `A ⊔ B`
with `A ◁ (A ⊔ B)` splits as a product. -/

omit [Finite G] in
private theorem subgroupOf_oddCoreIn_eq (K : Subgroup G) :
    (Work.GW2.oddCoreIn K).subgroupOf K = Work.GW2.oddCore ↥K := by
  have hinj : Function.Injective (fun L : Subgroup ↥K => L.map K.subtype) :=
    Subgroup.map_injective (f := K.subtype) Subtype.val_injective
  apply hinj
  calc ((Work.GW2.oddCoreIn K).subgroupOf K).map K.subtype
      = Work.GW2.oddCoreIn K ⊓ K := Subgroup.subgroupOf_map_subtype _ _
    _ = Work.GW2.oddCoreIn K := inf_eq_left.mpr (Subgroup.map_subtype_le (Work.GW2.oddCore ↥K))
    _ = (Work.GW2.oddCore ↥K).map K.subtype := rfl

omit [Finite G] in
private theorem subgroupOf_oddCoreIn_normal (K : Subgroup G) :
    ((Work.GW2.oddCoreIn K).subgroupOf K).Normal := by
  rw [subgroupOf_oddCoreIn_eq K]
  infer_instance

omit [Finite G] in
private theorem mem_sup_decomposition_aux {A B K : Subgroup G} (hBK : B ≤ K)
    (hAnorm : (A.subgroupOf K).Normal) (hsup : A ⊔ B = K) :
    ∀ x ∈ K, ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  intro x hx
  have hAK : A ≤ K := by rw [← hsup]; exact le_sup_left
  have hsup' : A.subgroupOf K ⊔ B.subgroupOf K = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAK hBK, hsup, Subgroup.subgroupOf_self]
  have hmem : (⟨x, hx⟩ : ↥K) ∈ A.subgroupOf K ⊔ B.subgroupOf K := by
    rw [hsup']; trivial
  haveI : (A.subgroupOf K).Normal := hAnorm
  obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  refine ⟨(a : G), ha, (b : G), hb, ?_⟩
  have := congrArg (fun z : ↥K => (z : G)) hab
  simpa using this

/-- **Bender–Glauberman 1981 notation**: `k₁ = |H : C_H(t₁)| = (1/2)|S₀|·|U : B₁|`, i.e.
`(C_G(t₁)).relIndex H = (D.n / 2) * D.B1.relIndex D.U` for the Bender–Glauberman data `D`
(`H = C_G(t)`, `U = O(H)`, `B₁ = U ⊓ C_G(t₁)`, `|S₀| = D.n`).

Route. `t` is central in `S` (`Work.BG.S_le_H`), so `S ≤ H = C_G(t)`; the centralizer splitting
`Work.GW2.CentralizerSplitProp` (proved as `Work.BG.SplitGlue.centralizerSplitProp`) gives
`H = U ⊔ S`, hence (`U` odd, `S` a 2-group) `U ⊓ S = ⊥` and `|H| = |U| * |S| = |U| * 2 * D.n`
(`|S| = 2 * D.n` from `D.dih` and `DihedralGroup.nat_card`).

Writing an element `c ∈ C_H(t₁)` as `c = u * s` with `u ∈ U`, `s ∈ S` (unique since `U ⊓ S = ⊥`)
and conjugating by the involution `t₁` gives `(t₁ * u * t₁) * (t₁ * s * t₁) = u * s`; comparing the
`U`- and `S`-parts forces `s * t₁ * s⁻¹ * t₁ ∈ U ⊓ S = ⊥`, i.e. `s ∈ C_S(t₁)`, and then
`u ∈ C_U(t₁) = B₁`.  So `C_H(t₁) = B₁ ⊔ C_S(t₁)` with `B₁ ⊓ C_S(t₁) = ⊥` (odd versus 2-group) and
`|C_H(t₁)| = |B₁| * |C_S(t₁)|`.

Finally `C_S(t₁) = ⟨t, t₁⟩` is the Klein four-group of `S`: `t` is central in `S`, so
`C_S(t₁) = C_G(⟨t,t₁⟩) ⊓ S`, and a four-subgroup of a dihedral Sylow is self-centralizing
(`Work.BG.fourGroup_centralizer_in_sylow`, applied to the four-group
`Work.BG.isFourGroup_closure_pair` of `t` and `t₁`); hence `|C_S(t₁)| = 4` and
`k₁ = |H| / |C_H(t₁)| = (|U| * 2 * D.n) / (4 * |B₁|) = (D.n / 2) * (D.B1.relIndex D.U)`. -/
theorem relIndexCentT1 {G : Type} [Group G] [Finite G] (D : Work.GW2.BGData G) :
    (Subgroup.centralizer ({D.t1} : Set G)).relIndex D.H
      = (D.n / 2) * D.B1.relIndex D.U := by
  have hSH : (D.S : Subgroup G) ≤ D.H := S_le_H D
  have hUH : D.U ≤ D.H := Subgroup.map_subtype_le _
  have hUnormSub : (D.U.subgroupOf D.H).Normal := subgroupOf_oddCoreIn_normal D.H
  have hHnormU : D.H ≤ Subgroup.normalizer (D.U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mp hUnormSub
  have hSnU : (D.S : Subgroup G) ≤ Subgroup.normalizer (D.U : Set G) := hSH.trans hHnormU
  have hUpi : Subgroup.IsPiSubgroup ({q : ℕ | q ≠ 2}) D.U := by
    rw [show D.U = Work.GW2.oddCoreIn D.H from rfl, Work.GW2.oddCoreIn_eq_opiCoreInG]
    exact OddOrder.GroupTheory.isPiSubgroup_opiCoreInG _ _
  have hUSbot : D.U ⊓ (D.S : Subgroup G) = ⊥ :=
    OddOrder.GroupTheory.inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl hUpi
      (Subgroup.isPiSubgroup_of_isPGroup_of_mem D.S.isPGroup' (by simp))
  have hcentr : ∀ x ∈ (D.S : Subgroup G), x * D.t = D.t * x := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (hSH hx) D.t (Set.mem_singleton D.t)).symm
  have hUS : D.U ⊔ (D.S : Subgroup G) = D.H :=
    Work.BG.SplitGlue.centralizerSplitProp G D.S D.n D.two_le D.dih D.t (D.S0_le D.t_mem)
      D.t_order hcentr
  -- `C_S(t₁)` has order `4` (the Klein four-group `⟨t, t₁⟩` of `S`)
  have hCS4 : Nat.card ↥(Subgroup.centralizer ({D.t1} : Set G) ⊓ (D.S : Subgroup G)) = 4 :=
    cardCentralizerInfSylowT1 D
  -- **Step 1**: `C_G(t₁) ∩ H = B₁ ⊔ (C_G(t₁) ∩ S)`, by comparing the `U`- and `S`-parts
  have hCeq : Subgroup.centralizer ({D.t1} : Set G) ⊓ D.H
      = D.B1 ⊔ (Subgroup.centralizer ({D.t1} : Set G) ⊓ (D.S : Subgroup G)) := by
    refine le_antisymm ?_ ?_
    · intro c hc
      obtain ⟨hcC, hcH⟩ := Subgroup.mem_inf.mp hc
      obtain ⟨u, hu, s, hs, hus⟩ := mem_sup_decomposition_aux hSH hUnormSub hUS c hcH
      have ht1sq : D.t1 * D.t1 = 1 := by
        simpa [pow_two] using ((orderOf_eq_prime_iff (p := 2)).mp D.t1_order).1
      have ht1inv : D.t1⁻¹ = D.t1 := inv_eq_of_mul_eq_one_right ht1sq
      have hcComm : D.t1 * c = c * D.t1 :=
        (Subgroup.mem_centralizer_singleton_iff.mp hcC).symm
      have hconjU : D.t1 * u * D.t1⁻¹ ∈ D.U :=
        (Subgroup.le_normalizer_iff.mp hSnU) D.t1 D.t1_mem u hu
      have hconjS : D.t1 * s * D.t1⁻¹ ∈ (D.S : Subgroup G) :=
        (D.S : Subgroup G).mul_mem ((D.S : Subgroup G).mul_mem D.t1_mem hs)
          ((D.S : Subgroup G).inv_mem D.t1_mem)
      have hconj_c : D.t1 * c * D.t1⁻¹ = c := by
        rw [ht1inv, hcComm, mul_assoc, ht1sq, mul_one]
      have hprod : (D.t1 * u * D.t1⁻¹) * (D.t1 * s * D.t1⁻¹) = u * s := by
        rw [show (D.t1 * u * D.t1⁻¹) * (D.t1 * s * D.t1⁻¹) = D.t1 * (u * s) * D.t1⁻¹ by
          group, hus]
        exact hconj_c
      have hpair : ((⟨D.t1 * u * D.t1⁻¹, hconjU⟩ : ↥D.U),
            (⟨D.t1 * s * D.t1⁻¹, hconjS⟩ : ↥(D.S : Subgroup G)))
          = ((⟨u, hu⟩ : ↥D.U), (⟨s, hs⟩ : ↥(D.S : Subgroup G))) :=
        Subgroup.mul_injective_of_disjoint (H₁ := D.U) (H₂ := (D.S : Subgroup G))
          (disjoint_iff.mpr hUSbot) hprod
      have hu_eq : D.t1 * u * D.t1⁻¹ = u :=
        congrArg (fun z : ↥D.U => (z : G)) (congrArg Prod.fst hpair)
      have hs_eq : D.t1 * s * D.t1⁻¹ = s :=
        congrArg (fun z : ↥(D.S : Subgroup G) => (z : G)) (congrArg Prod.snd hpair)
      have huB1 : u ∈ D.B1 := by
        refine Subgroup.mem_inf.mpr ⟨hu, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h := congrArg (fun z => D.t1 * z) hu_eq
        have h' : u * D.t1⁻¹ = D.t1 * u := by
          rw [show D.t1 * (D.t1 * u * D.t1⁻¹) = (D.t1 * D.t1) * (u * D.t1⁻¹) by group,
            ht1sq, one_mul] at h
          exact h
        rw [ht1inv] at h'
        exact h'
      have hsCS : s ∈ Subgroup.centralizer ({D.t1} : Set G) ⊓ (D.S : Subgroup G) := by
        refine Subgroup.mem_inf.mpr ⟨?_, hs⟩
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h := congrArg (fun z => D.t1 * z) hs_eq
        have h' : s * D.t1⁻¹ = D.t1 * s := by
          rw [show D.t1 * (D.t1 * s * D.t1⁻¹) = (D.t1 * D.t1) * (s * D.t1⁻¹) by group,
            ht1sq, one_mul] at h
          exact h
        rw [ht1inv] at h'
        exact h'
      rw [← hus]
      exact Subgroup.mul_mem_sup huB1 hsCS
    · refine sup_le ?_ ?_
      · exact le_inf inf_le_right (le_trans inf_le_left hUH)
      · exact le_inf inf_le_left (le_trans inf_le_right hSH)
  have hCU : Subgroup.centralizer ({D.t1} : Set G) ⊓ D.H ⊓ D.U = D.B1 := by
    rw [inf_assoc, inf_eq_right.mpr hUH, inf_comm]
  have hCS' : Subgroup.centralizer ({D.t1} : Set G) ⊓ D.H ⊓ (D.S : Subgroup G)
      = Subgroup.centralizer ({D.t1} : Set G) ⊓ (D.S : Subgroup G) := by
    rw [inf_assoc, inf_eq_right.mpr hSH]
  have hC' : Subgroup.centralizer ({D.t1} : Set G) ⊓ D.H
      = (Subgroup.centralizer ({D.t1} : Set G) ⊓ D.H ⊓ D.U) ⊔
        (Subgroup.centralizer ({D.t1} : Set G) ⊓ D.H ⊓ (D.S : Subgroup G)) := by
    rw [hCU, hCS', hCeq]
  have hCA : Subgroup.centralizer ({D.t1} : Set G) ⊓ D.H ⊓ (D.S : Subgroup G)
      ≤ Subgroup.normalizer
        (Subgroup.centralizer ({D.t1} : Set G) ⊓ D.H ⊓ D.U : Subgroup G) := by
    rw [hCU, hCS']
    rw [Subgroup.le_normalizer_iff]
    intro y hy x hx
    obtain ⟨hyC, hyS⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨hxU, hxC⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.le_normalizer_iff.mp hSnU) y hyS x hxU,
       (Subgroup.centralizer ({D.t1} : Set G)).mul_mem
         ((Subgroup.centralizer ({D.t1} : Set G)).mul_mem hyC hxC)
         ((Subgroup.centralizer ({D.t1} : Set G)).inv_mem hyC)⟩
  have hCinf : Subgroup.centralizer ({D.t1} : Set G) ⊓ D.H ⊓ D.U ⊓
      (Subgroup.centralizer ({D.t1} : Set G) ⊓ D.H ⊓ (D.S : Subgroup G)) = ⊥ := by
    rw [hCU, hCS']
    refine le_bot_iff.mp ?_
    calc D.B1 ⊓ (Subgroup.centralizer ({D.t1} : Set G) ⊓ (D.S : Subgroup G))
        ≤ D.U ⊓ (D.S : Subgroup G) := inf_le_inf inf_le_left inf_le_right
      _ = ⊥ := hUSbot
  -- **Step 2**: the index formula for a join, applied to `A = U`, `B = S`, `C = C_G(t₁) ∩ H`
  have hkey := relIndexSupDecomposition (A := D.U) (B := (D.S : Subgroup G))
    (C := Subgroup.centralizer ({D.t1} : Set G) ⊓ D.H) hSnU hUSbot hC' hCA hCinf
  rw [hUS, Subgroup.inf_relIndex_right, hCU, hCS'] at hkey
  have hS_card : Nat.card ↥(D.S : Subgroup G) = 2 * D.n := by
    obtain ⟨e⟩ := D.dih
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  -- **Step 3**: `|S : C_S(t₁)| = 2 * D.n / 4 = D.n / 2`
  have hrelCS : (Subgroup.centralizer ({D.t1} : Set G) ⊓ (D.S : Subgroup G)).relIndex
      (D.S : Subgroup G) = D.n / 2 := by
    rw [relIndexEqCardDiv]
    have h1 : Nat.card ↥((Subgroup.centralizer ({D.t1} : Set G) ⊓ (D.S : Subgroup G)) ⊓
        (D.S : Subgroup G)) = 4 := by
      rw [inf_eq_left.mpr inf_le_right]
      exact hCS4
    rw [h1, hS_card]
    obtain ⟨m, hm⟩ := twoDvdN D
    rw [hm]
    have h2 : (2 : ℕ) * (2 * m) = 4 * m := by ring
    rw [h2, Nat.mul_div_right m (by norm_num : (0:ℕ) < 4),
      Nat.mul_div_right m (by norm_num : (0:ℕ) < 2)]
  rw [hkey, hrelCS, mul_comm]

end Work.BG
