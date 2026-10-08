import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.dihOrCycSylow_subgroup
import Submission.Work.CORE2A.fourGroup_in_quasisimple
import Submission.Work.CORE2A.inf_centralizer_eq_center_map
import Submission.Work.CORE2A.odd_card_centralizer_of_four_subgroup
import Submission.Work.CORE2A.card_PGL2_eq_two_mul_card_PSL2
import Submission.Work.CORE2A.oneInvClassIn_top_iff
import Submission.Work.CORE2A.mem_of_sq_eq_one_of_mem_sup_centralizer
import Submission.Work.CORE2A.not_mem_map_of_card_eq_two_mul
import Submission.Work.CORE2A.card_sup_sylow_eq_two_mul_of_index
import Submission.Work.CORE2A.centralizer_map_quotient_eq_bot
import Submission.Work.CORE2A.oneInvClassIn_top_of_index_odd
import Submission.Work.DSTR.dihOrCycHered
import Submission.Work.DSTR.dihedralSubgroup
import Submission.Work.DSTR.dihedralQuotient
import Submission.Work.DSTR.twoRank
import Submission.Work.DSTR.quasisimpleSylow
import Submission.Work.DSTR.layerOneInvClass
import Submission.Work.DSTR.l19

namespace Work.CORE2A

open scoped MatrixGroups
open Subgroup








/-! ## Elementary helpers for the final construction -/

/-- A `2`-subgroup of a finite group whose subgroup `M` has odd index lies in `M`. -/
private theorem isPGroup_le_of_odd_index {Q : Type*} [Group Q] [Finite Q] {P M : Subgroup Q}
    [M.Normal] (hP : IsPGroup 2 P) (hModd : Odd M.index) : P ≤ M := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : (QuotientGroup.mk' M).ker = M := QuotientGroup.ker_mk' M
  rw [← hker, ← Subgroup.map_eq_bot_iff]
  have hPim : IsPGroup 2 (P.map (QuotientGroup.mk' M)) := hP.map _
  obtain ⟨n, hn⟩ := hPim.exists_card_eq
  have hdvd : Nat.card ↥(P.map (QuotientGroup.mk' M)) ∣ M.index := by
    rw [Subgroup.index_eq_card]
    exact Subgroup.card_subgroup_dvd_card _
  rw [hn] at hdvd
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd] at hModd
  have hn0 : n = 0 := by
    by_contra hn0
    exact hModd (dvd_trans (dvd_pow_self 2 hn0) hdvd)
  exact Subgroup.eq_bot_of_card_eq (P.map (QuotientGroup.mk' M)) (by rw [hn, hn0, pow_zero])

/-- If `L ≤ N ≤ M` with `N ≠ L` and `|M| = 2|L|`, then `N = M`. -/
private theorem eq_of_le_of_ne_of_card_eq_two_mul {G : Type*} [Group G] [Finite G]
    {L M N : Subgroup G} (hLN : L ≤ N) (hNM : N ≤ M) (hne : N ≠ L)
    (hcard : Nat.card ↥M = 2 * Nat.card ↥L) : N = M := by
  have hLpos : 0 < Nat.card ↥L := Nat.card_pos
  have h1 : Nat.card ↥L ∣ Nat.card ↥N := by
    have h := Subgroup.card_subgroup_dvd_card (L.subgroupOf N)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLN).toEquiv] at h
  have h2 : Nat.card ↥N ∣ Nat.card ↥M := by
    have h := Subgroup.card_subgroup_dvd_card (N.subgroupOf M)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv] at h
  obtain ⟨d, hd⟩ := h1
  have hdvd : d ∣ 2 := by
    have h3 : Nat.card ↥L * d ∣ Nat.card ↥M := by rw [← hd]; exact h2
    rw [hcard, Nat.mul_comm 2 (Nat.card ↥L)] at h3
    exact (Nat.mul_dvd_mul_iff_left hLpos).mp h3
  have hNne : Nat.card ↥N ≠ Nat.card ↥L := fun h =>
    hne (Subgroup.eq_of_le_of_card_ge (H := L) (K := N) hLN (le_of_eq h)).symm
  have hd2 : d = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with hd1 | hd1
    · exact absurd (by rw [hd, hd1, mul_one] : Nat.card ↥N = Nat.card ↥L) hNne
    · exact hd1
  have hcard_eq : Nat.card ↥N = Nat.card ↥M := by rw [hd, hd2, hcard, Nat.mul_comm]
  exact Subgroup.eq_of_le_of_card_ge hNM (le_of_eq hcard_eq.symm)

/-- The centre of a subgroup, transported along an injective homomorphism. -/
private theorem map_center_map_subtype {K H : Type*} [Group K] [Group H]
    (f : K →* H) (hf : Function.Injective f) (E : Subgroup K) :
    (Subgroup.center ↥(E.map f)).map ((E.map f).subtype) =
      ((Subgroup.center ↥E).map E.subtype).map f := by
  have hcomp : ((E.map f).subtype).comp
      (Subgroup.equivMapOfInjective E f hf).toMonoidHom = f.comp E.subtype := by
    ext x
    rfl
  have hcenter : Subgroup.center ↥(E.map f) =
      (Subgroup.center ↥E).map (Subgroup.equivMapOfInjective E f hf).toMonoidHom :=
    (Subgroup.map_center_eq (Subgroup.equivMapOfInjective E f hf)).symm
  have h1 : (Subgroup.center ↥(E.map f)).map ((E.map f).subtype) =
      ((Subgroup.center ↥E).map (Subgroup.equivMapOfInjective E f hf).toMonoidHom).map
        ((E.map f).subtype) := by rw [hcenter]
  rw [h1, Subgroup.map_map, hcomp, ← Subgroup.map_map]

/-- Membership of a coerced element in a subgroup pushed forward along `K.subtype`. -/
private theorem mem_map_subtype_iff {G : Type*} [Group G] (K : Subgroup G) (Z : Subgroup ↥K)
    (x : ↥K) : (x : G) ∈ Z.map K.subtype ↔ x ∈ Z := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, hzx⟩
    rwa [Subtype.coe_injective hzx] at hz
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem Thm26bPGL (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop) (hlay : Work.GW2.LayerShapeProp) (h2r : Work.GW2.TwoRankProp) (hone : Work.GW2.LayerOneInvClassProp) (hAutL2 : Work.GW2.AutL2Prop) (hAutA7 : Work.GW2.AutA7Prop) : Work.GW2.Thm26bPGLProp := by
  intro G _instG _instF hFT hbc B hne
  classical
  haveI hSimp : IsSimpleGroup G := hbc.simple
  -- ================= Part 1: the group `K = Ĥ` and its layer `E` =================
  have hKne : B.Hhat ≠ ⊤ := B.Hhat_coatom.ne_top
  have hKlt : Nat.card ↥B.Hhat < Nat.card G := by
    have hdvd : Nat.card ↥B.Hhat ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
    have hle : Nat.card ↥B.Hhat ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos hdvd
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (Subgroup.eq_top_of_card_eq B.Hhat h) hKne
  have hsyK : Work.GW2.DihOrCycSylow ↥B.Hhat := dihOrCycSylow_subgroup hbc.sylow B.Hhat
  have hDG : Work.GW2.IsDGroup ↥B.Hhat := hbc.ih ↥B.Hhat hKlt hsyK
  have hlayer_ne : Work.GW2.layer ↥B.Hhat ≠ ⊥ := by
    intro hbot
    apply hne
    show (Work.GW2.layer ↥B.Hhat).map B.Hhat.subtype = ⊥
    rw [hbot, Subgroup.map_bot]
  obtain ⟨E, hEnorm, hEquasi⟩ :
      ∃ E : Subgroup ↥B.Hhat, E.Normal ∧ Work.GW2.IsQuasisimple E := by
    by_contra hcon
    have hempty : {E : Subgroup ↥B.Hhat | E.Normal ∧ Work.GW2.IsQuasisimple E} = ∅ := by
      ext E
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, h2⟩
      exact hcon ⟨E, h1, h2⟩
    have : Work.GW2.layer ↥B.Hhat = ⊥ := by
      show sSup {E : Subgroup ↥B.Hhat | E.Normal ∧ Work.GW2.IsQuasisimple E} = ⊥
      rw [hempty, sSup_empty]
    exact hlayer_ne this
  obtain ⟨hlayer_eq, hZodd, hEZ⟩ := T.lay ↥B.Hhat hFT hsyK hDG E hEnorm hEquasi
  -- ================= Part 2: the centralizer `C` and the quotient `K ⧸ C` =================
  haveI hEnormI : E.Normal := hEnorm
  -- the centralizer of `E` in `K`
  let C : Subgroup ↥B.Hhat := Subgroup.centralizer (E : Set ↥B.Hhat)
  haveI hCnormal : C.Normal := Subgroup.normal_centralizer (H := E)
  have hinfC : E ⊓ C = (Subgroup.center ↥E).map E.subtype := inf_centralizer_eq_center_map E
  -- `Z(E)` inside `K`
  let Z : Subgroup ↥B.Hhat := (Subgroup.center ↥E).map E.subtype
  have hZle : Z ≤ E := by
    change (Subgroup.center ↥E).map E.subtype ≤ E
    rw [← hinfC]
    exact inf_le_left
  have hZoddK : Odd (Nat.card Z) := by
    rw [show Z = (Subgroup.center ↥E).map E.subtype from rfl,
      Subgroup.card_map_of_injective E.subtype_injective]
    exact hZodd
  -- a four-group in `E`, and oddness of `C`
  obtain ⟨V, hVle, hV4⟩ := fourGroup_in_quasisimple E hEnorm hEquasi hsyK
  have hCodd : Odd (Nat.card C) :=
    odd_card_centralizer_of_four_subgroup E hZodd h2r hsyK ⟨V, hVle, hV4⟩
  -- the image `L` of `E` in `K ⧸ C`
  let L : Subgroup (↥B.Hhat ⧸ C) := E.map (QuotientGroup.mk' C)
  have hLnormal : L.Normal := by
    change (E.map (QuotientGroup.mk' C)).Normal
    exact hEnorm.map _ (QuotientGroup.mk'_surjective C)
  -- `L ≃* E ⧸ Z(E)`
  have hLisoZ : Nonempty (↥L ≃* (↥E ⧸ Subgroup.center ↥E)) := by
    refine ⟨?_⟩
    let φE : ↥E →* (↥B.Hhat ⧸ C) := (QuotientGroup.mk' C).comp E.subtype
    have hker : φE.ker = C.subgroupOf E := by
      ext x
      show ((QuotientGroup.mk' C) (x : ↥B.Hhat) = 1) ↔ ((x : ↥B.Hhat) ∈ C)
      exact QuotientGroup.eq_one_iff _
    have hrange : φE.range = L := by
      rw [MonoidHom.range_eq_map]
      ext q
      constructor
      · rintro ⟨x, -, rfl⟩
        exact ⟨(x : ↥B.Hhat), x.2, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨⟨y, hy⟩, trivial, rfl⟩
    have hCsub : C.subgroupOf E = Subgroup.center ↥E := by
      apply Subgroup.map_injective E.subtype_injective
      rw [Subgroup.subgroupOf_map_subtype, inf_comm, hinfC]
    have hkerZ : φE.ker = Subgroup.center ↥E := hker.trans hCsub
    have e1 : (↥E ⧸ φE.ker) ≃* ↥L :=
      (QuotientGroup.quotientKerEquivRange φE).trans (MulEquiv.subgroupCongr hrange)
    have e2 : (↥E ⧸ Subgroup.center ↥E) ≃* (↥E ⧸ φE.ker) :=
      QuotientGroup.quotientMulEquivOfEq hkerZ.symm
    exact (e2.trans e1).symm
  -- the centralizer of `L` in `K ⧸ C` is trivial
  have hLcent : Subgroup.centralizer (L : Set (↥B.Hhat ⧸ C)) = ⊥ :=
    centralizer_map_quotient_eq_bot E C rfl hEquasi.1 hFT hCodd
  -- `DihOrCycSylow` for the quotient
  have hhered : Work.GW2.DihOrCycHeredProp :=
    Work.DSTR.dihOrCycHered Work.DSTR.dihedralSubgroup Work.DSTR.dihedralQuotient
  have hsyQ : Work.GW2.DihOrCycSylow (↥B.Hhat ⧸ C) := (hhered ↥B.Hhat hsyK).2 C
  -- every involution of `K` is conjugate in `E` to every other one
  have hE1 : Work.GW2.C3OneInvClassIn E := hone ↥B.Hhat hFT hsyK E hEnorm hEquasi
  -- the contradiction from an odd index `[K ⧸ C : L]`
  have hcontra : Odd L.index → False := by
    intro hidx
    have hone' : Work.GW2.OneInvClassIn (⊤ : Subgroup ↥B.Hhat) :=
      oneInvClassIn_top_of_index_odd E C rfl hZodd hCodd hidx hE1
    exact h21 G hFT hbc B ((oneInvClassIn_top_iff B.Hhat).mp hone')
  -- ================= Part 3: the case analysis =================
  obtain ⟨eLZ⟩ := hLisoZ
  rcases hEZ with hA7 | hL2
  · -- `E ⧸ Z(E) ≅ A₇`: the index is odd, contradiction
    obtain ⟨eA7⟩ := hA7
    have hLtop : L = ⊤ := hAutA7 (↥B.Hhat ⧸ C) L hLnormal ⟨eLZ.trans eA7⟩ hLcent hsyQ
    exact False.elim (hcontra (by rw [hLtop, Subgroup.index_top]; exact odd_one))
  · obtain ⟨p, k, hpprime, hpodd, hge, hPSLiso⟩ := hL2
    haveI : Fact p.Prime := hpprime
    obtain ⟨ePSL⟩ := hPSLiso
    -- `L ≅ PSL(2, q)`
    have hLisoPSL : Nonempty (↥L ≃* PSL(2, GaloisField p k)) := ⟨eLZ.trans ePSL⟩
    have hcardL : Nat.card ↥L = Nat.card (PSL(2, GaloisField p k)) :=
      Nat.card_congr (eLZ.trans ePSL).toEquiv
    obtain ⟨M, hMn, hLM, hModd, hMPGL⟩ :=
      hAutL2 (↥B.Hhat ⧸ C) L p k hpodd hge hLnormal hLisoPSL hLcent hsyQ
    rcases hMPGL with hMPSL | hMPGL'
    · -- `M ≅ PSL(2, q)`: then `M = L`, so `[K ⧸ C : L]` is odd
      obtain ⟨eM⟩ := hMPSL
      have hcardM : Nat.card ↥M = Nat.card (PSL(2, GaloisField p k)) :=
        Nat.card_congr eM.toEquiv
      have hML : M = L := (Subgroup.eq_of_le_of_card_ge hLM
        (le_of_eq (hcardM.trans hcardL.symm))).symm
      exact False.elim (hcontra (hML ▸ hModd))
    · -- the good case: `M ≅ PGL(2, q)`
      obtain ⟨eM⟩ := hMPGL'
      have hcardM : Nat.card ↥M = Nat.card (PGL(2, GaloisField p k)) :=
        Nat.card_congr eM.toEquiv
      have hk : k ≠ 0 := by
        rintro rfl
        simp at hge
      have hcardML : Nat.card ↥M = 2 * Nat.card ↥L := by
        rw [hcardM, hcardL, card_PGL2_eq_two_mul_card_PSL2 hpodd hk]
      -- the subgroup `P = S ∩ K` of `K`
      have hSle : (B.S : Subgroup G) ≤ B.Hhat := bSetup_S_le_Hhat B
      let P : Subgroup ↥B.Hhat := (B.S : Subgroup G).subgroupOf B.Hhat
      have hPmap : P.map B.Hhat.subtype = (B.S : Subgroup G) := by
        change ((B.S : Subgroup G).subgroupOf B.Hhat).map B.Hhat.subtype = (B.S : Subgroup G)
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hSle]
      have hPpgroup : IsPGroup 2 P :=
        (B.S).isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hSle).symm
      have hPindex : Odd P.index := by
        have hSodd : ¬ 2 ∣ (B.S : Subgroup G).index := (B.S).not_dvd_index
        have h1 : (B.S : Subgroup G).index = P.index * B.Hhat.index := by
          have h := Subgroup.index_map_subtype P
          rwa [hPmap] at h
        rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
        intro h2
        exact hSodd (h1 ▸ dvd_mul_of_dvd_left h2 _)
      -- `M ≠ ⊥`
      have hMne : M ≠ ⊥ := by
        intro hbot
        have h1 : Nat.card ↥M = 1 := by rw [hbot]; exact Subgroup.card_bot
        rw [hcardML] at h1
        have h2 : 1 ≤ Nat.card ↥L := Nat.card_pos
        omega
      -- `P` is not contained in `E` (equivalently, the image of `P` is not inside `L`)
      have hPbar_notle : ¬ P.map (QuotientGroup.mk' C) ≤ L := fun hle =>
        not_mem_map_of_card_eq_two_mul C hCodd P hPpgroup hPindex (M := M) (L := L)
          hMne hcardML hLM fun x hx => hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
      have hPnotleE : ¬ P ≤ E := fun hPE => hPbar_notle (Subgroup.map_mono hPE)
      -- the index of `E ⊔ C` in `K`
      have hCmap : C.map (QuotientGroup.mk' C) = ⊥ := by
        rw [eq_bot_iff]
        rintro y ⟨c, hc, rfl⟩
        exact (QuotientGroup.eq_one_iff c).mpr hc
      have hL_sup : L = (E ⊔ C).map (QuotientGroup.mk' C) := by
        change E.map (QuotientGroup.mk' C) = (E ⊔ C).map (QuotientGroup.mk' C)
        rw [Subgroup.map_sup, hCmap, sup_bot_eq]
      have hNidx : (E ⊔ C).index = L.index := by
        rw [hL_sup, Subgroup.index_map, QuotientGroup.ker_mk',
          sup_eq_left.mpr le_sup_right,
          MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective C),
          Subgroup.index_top, mul_one]
      have hrelLM : L.relIndex M = 2 := by
        have h := Subgroup.relIndex_mul_card (H := L) (K := M)
        rw [inf_eq_left.mpr hLM, hcardML] at h
        exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
      have hidxN : (E ⊔ C).index = 2 * M.index := by
        rw [hNidx, ← Subgroup.relIndex_mul_index hLM, hrelLM]
      -- the group `DK = P ⊔ E`
      let DK : Subgroup ↥B.Hhat := P ⊔ E
      have hDKcard : Nat.card ↥DK = 2 * Nat.card ↥E :=
        card_sup_sylow_eq_two_mul_of_index E C P hEnormI hCnormal hCodd hPpgroup hPindex
          M.index hModd hidxN hPnotleE
      -- the map `DK → K ⧸ C`
      let ψ : ↥DK →* (↥B.Hhat ⧸ C) := (QuotientGroup.mk' C).comp DK.subtype
      have hPbar_le_M : P.map (QuotientGroup.mk' C) ≤ M := by
        haveI : M.Normal := hMn
        exact isPGroup_le_of_odd_index (hP := hPpgroup.map _) hModd
      have hMuniv : P.map (QuotientGroup.mk' C) ⊔ L = M := by
        have hle : P.map (QuotientGroup.mk' C) ⊔ L ≤ M := sup_le hPbar_le_M hLM
        have hne : P.map (QuotientGroup.mk' C) ⊔ L ≠ L := fun heq =>
          hPbar_notle (heq ▸ le_sup_left)
        exact eq_of_le_of_ne_of_card_eq_two_mul le_sup_right hle hne hcardML
      have hψrange : ψ.range = M := by
        have e1 : ψ.range = DK.map (QuotientGroup.mk' C) := by
          rw [MonoidHom.range_eq_map]
          show (⊤ : Subgroup ↥DK).map ψ = DK.map (QuotientGroup.mk' C)
          rw [show ψ = (QuotientGroup.mk' C).comp DK.subtype from rfl, ← Subgroup.map_map,
            ← MonoidHom.range_eq_map, Subgroup.range_subtype]
        rw [e1, show DK = P ⊔ E from rfl, Subgroup.map_sup]
        exact hMuniv
      let ψM : ↥DK →* ↥M :=
        ψ.codRestrict M fun x => by
          have h : ψ x ∈ ψ.range := MonoidHom.mem_range.mpr ⟨x, rfl⟩
          rwa [hψrange] at h
      let φK : ↥DK →* PGL(2, GaloisField p k) := eM.toMonoidHom.comp ψM
      -- transport to the subgroup of `G` generated by `B.S` and `layerIn B.Hhat`
      let D_G : Subgroup G := (B.S : Subgroup G) ⊔ Work.GW2.layerIn B.Hhat
      have hDle : D_G ≤ B.Hhat :=
        sup_le hSle (by
          change (Work.GW2.layer ↥B.Hhat).map B.Hhat.subtype ≤ B.Hhat
          exact Subgroup.map_subtype_le _)
      have hDKmap : DK.map B.Hhat.subtype = D_G := by
        rw [show DK = P ⊔ E from rfl, Subgroup.map_sup, hPmap]
        congr 1
        change E.map B.Hhat.subtype = (Work.GW2.layer ↥B.Hhat).map B.Hhat.subtype
        rw [hlayer_eq]
      -- the inclusion `↥D_G →* ↥DK`
      let inc : ↥D_G →* ↥B.Hhat := Subgroup.inclusion hDle
      have hDKmem : ∀ y : ↥D_G, inc y ∈ DK := by
        intro y
        have hy : (y : G) ∈ DK.map B.Hhat.subtype := by rw [hDKmap]; exact y.2
        obtain ⟨d, hd, hdy⟩ := Subgroup.mem_map.mp hy
        have h1 : inc y = d := Subtype.ext hdy.symm
        rwa [h1]
      let ι : ↥D_G →* ↥DK := inc.codRestrict DK hDKmem
      let φ : ↥D_G →* PGL(2, GaloisField p k) := (eM.toMonoidHom).comp (ψM.comp ι)
      -- `Z(E)` transported to `G`
      have hZleC : Z ≤ C := by
        intro z hz
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨e, he⟩)
      have hZge : Z ≤ DK ⊓ C := fun z hz =>
        ⟨le_trans hZle (le_sup_right : E ≤ P ⊔ E) hz, hZleC hz⟩
      -- `|E| = |L| * |Z|`
      have hEcard : Nat.card ↥E = Nat.card ↥L * Nat.card ↥Z := by
        have h1 : (Subgroup.center ↥E).index * Nat.card (Subgroup.center ↥E) =
            Nat.card ↥E := Subgroup.index_mul_card _
        have h2 : (Subgroup.center ↥E).index = Nat.card ↥L := by
          rw [Subgroup.index_eq_card]
          exact (Nat.card_congr eLZ.toEquiv).symm
        have h3 : Nat.card (Subgroup.center ↥E) = Nat.card ↥Z := by
          change Nat.card (Subgroup.center ↥E) =
            Nat.card ↥((Subgroup.center ↥E).map E.subtype)
          rw [Subgroup.card_map_of_injective E.subtype_injective]
        rw [h2, h3] at h1
        exact h1.symm
      -- the map `ψ` and its kernel
      have hψker : ψ.ker = C.subgroupOf DK := by
        ext d
        rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
        show ((QuotientGroup.mk' C) (d : ↥B.Hhat) = 1) ↔ ((d : ↥B.Hhat) ∈ C)
        exact QuotientGroup.eq_one_iff _
      -- `|DK ⊓ C| = |Z|`
      have hcardker : Nat.card ↥(DK ⊓ C) = Nat.card ↥Z := by
        have h1 : Nat.card ↥(ψ.ker) * Nat.card ↥(ψ.range) = Nat.card ↥DK :=
          Subgroup.card_ker_mul_card_range ψ
        have h2 : Nat.card ↥(ψ.ker) = Nat.card ↥(DK ⊓ C) := by
          have h3 : C.subgroupOf DK = (DK ⊓ C).subgroupOf DK := by
            ext d
            simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
            exact ⟨fun h => ⟨d.2, h⟩, fun h => h.2⟩
          rw [hψker, h3]
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
        rw [h2, hψrange, hDKcard, hcardML, hEcard] at h1
        have h4 : Nat.card ↥(DK ⊓ C) * (2 * Nat.card ↥L) = Nat.card ↥Z * (2 * Nat.card ↥L) := by
          rw [h1]
          ring
        exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (by norm_num) Nat.card_pos) h4
      have hDCK : DK ⊓ C = Z :=
        (Subgroup.eq_of_le_of_card_ge hZge (le_of_eq hcardker)).symm
      have hDCK_mem : ∀ x : ↥B.Hhat, x ∈ DK → (x ∈ C ↔ x ∈ Z) := fun x hx => by
        constructor
        · intro hxC
          rw [← hDCK]
          exact ⟨hx, hxC⟩
        · intro hxZ
          rw [← hDCK] at hxZ
          exact hxZ.2
      -- `Z(E)` transported to `G`
      have hZG : (Z.map B.Hhat.subtype) =
          (Subgroup.center ↥(Work.GW2.layerIn B.Hhat)).map (Work.GW2.layerIn B.Hhat).subtype := by
        have h := map_center_map_subtype B.Hhat.subtype B.Hhat.subtype_injective E
        rw [show E.map B.Hhat.subtype = Work.GW2.layerIn B.Hhat from by
          change E.map B.Hhat.subtype = (Work.GW2.layer ↥B.Hhat).map B.Hhat.subtype
          rw [hlayer_eq]] at h
        exact h.symm
      -- the kernel of `φ` is `Z(E)`
      have hkerφ : φ.ker = (Z.map B.Hhat.subtype).subgroupOf D_G := by
        ext y
        show (eM (ψM (ι y)) = 1) ↔ ((y : G) ∈ Z.map B.Hhat.subtype)
        rw [MulEquiv.map_eq_one_iff]
        have h1 : (ψM (ι y) = 1) ↔ (((ι y : ↥DK) : ↥B.Hhat) : G) ∈ Z.map B.Hhat.subtype := by
          rw [mem_map_subtype_iff B.Hhat Z ((ι y : ↥DK) : ↥B.Hhat),
            ← hDCK_mem ((ι y : ↥DK) : ↥B.Hhat) (ι y).2]
          constructor
          · intro h
            exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)
          · intro hC
            exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr hC)
        rw [h1]
        rfl
      -- surjectivity
      have hφsurj : Function.Surjective φ := by
        intro w
        obtain ⟨x, hx⟩ := eM.surjective w
        obtain ⟨d, hd⟩ : ∃ d : ↥DK, ψ d = (x : ↥B.Hhat ⧸ C) := by
          have hmem : (x : ↥B.Hhat ⧸ C) ∈ ψ.range := by
            rw [hψrange]
            exact x.2
          exact MonoidHom.mem_range.mp hmem
        have hd' : ∃ y : ↥D_G, ι y = d := by
          refine ⟨⟨(d : G), ?_⟩, ?_⟩
          · rw [← hDKmap]
            exact Subgroup.mem_map.mpr ⟨d, d.2, rfl⟩
          · rfl
        obtain ⟨y, hy⟩ := hd'
        refine ⟨y, ?_⟩
        have h1 : (ψM (ι y) : ↥M) = x := by
          rw [hy]
          exact Subtype.ext hd
        show eM (ψM (ι y)) = w
        rw [h1]
        exact hx
      refine ⟨p, k, hpprime, hpodd, hge, φ, hφsurj, ?_⟩
      rw [hkerφ, hZG]

end Work.CORE2A
