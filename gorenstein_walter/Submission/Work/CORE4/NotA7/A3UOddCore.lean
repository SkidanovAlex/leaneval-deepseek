import Mathlib
import Submission.Work.CORE4.NotA7Defs
import Submission.Work.CORE4.A7Split
import Submission.Work.CORE4.NineRyAux.OddMemU
import Submission.Work.CORE4.fittingIn_eq_self_of_isPGroup
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.API

namespace Work.CORE4.NotA7

open Work.GW2 Subgroup

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-! ## Auxiliary group theory

The two lemmas below are the general group-theoretic ingredients of `A3UOddCore`.

* `le_oddCoreIn_of_normal_of_odd_aux` is the *maximality* of `O_{2'}(M)` read in the ambient
  group: a normal subgroup of `M` of odd order lies in `Work.GW2.oddCoreIn M`.
* `odd_normal_le_centralizer_of_quasisimple_aux` is the step `[O(M), E(M)] = 1`: it is
  `Work.BMAX.nilpotent_normal_le_centralizer_of_quasisimple` with *nilpotency of `N`* replaced by
  *oddness of `N`* (and *evenness of the central quotient of `E`* used instead of the final
  "`E ≤ N` nilpotent" contradiction): if `E ◁ X` is quasisimple with `E/Z(E)` of even order and
  `N ◁ X` has odd order, then `N ≤ C_X(E)`.

  Indeed `M := ⁅E,N⁆ ≤ E ⊓ N` is normal in `X` and in `E`; its image in the simple group
  `E/Z(E)` is `⊥` or `⊤`.  If it is `⊥`, then `M ≤ Z(E)`, so `⁅M,E⁆ = 1` and the three subgroups
  lemma together with `E = ⁅E,E⁆` gives `⁅E,N⁆ = 1`.  If it is `⊤`, then `E/Z(E)` is a quotient
  of `M ≤ N` of odd order (via `Subgroup.card_map_dvd`), hence has odd order — contradicting the
  evenness of `|E/Z(E)|`. -/

/-- **Maximality of `O_{2'}(M)`.** A subgroup `X ≤ M` that is normal in `M` and of odd order lies
in `Work.GW2.oddCoreIn M`. -/
theorem le_oddCoreIn_of_normal_of_odd_aux {G : Type} [Group G] [Finite G] {X M : Subgroup G}
    (hXM : X ≤ M) (hn : (X.subgroupOf M).Normal) (hodd : Odd (Nat.card X)) :
    X ≤ Work.GW2.oddCoreIn M := by
  have hcard : Nat.card (X.subgroupOf M) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv
  have hodd' : Odd (Nat.card (X.subgroupOf M)) := hcard.symm ▸ hodd
  have hle : X.subgroupOf M ≤ Work.GW2.oddCore ↥M :=
    (Subgroup.normal_le_normalCore (N := X.subgroupOf M) (hN := hn)
      (H := sSup {N : Subgroup ↥M | N.Normal ∧ Odd (Nat.card N)})).mpr
      (le_sSup ⟨hn, hodd'⟩)
  rw [← Subgroup.map_subgroupOf_eq_of_le hXM]
  simpa [Work.GW2.oddCoreIn] using Subgroup.map_mono (f := M.subtype) hle

/-- **An odd-order normal subgroup commutes with a quasisimple subgroup whose central quotient
has even order.**  `E ◁ X` quasisimple (`⁅E,E⁆ = E` and `E/Z(E)` simple) with `|E/Z(E)|` even,
`N ◁ X` of odd order ⟹ `N ≤ C_X(E)`. -/
theorem odd_normal_le_centralizer_of_quasisimple_aux {X : Type*} [Group X]
    {E N : Subgroup X} (hEn : E.Normal) (hEE : ⁅E, E⁆ = E)
    (hEsimp : IsSimpleGroup (↥E ⧸ Subgroup.center ↥E))
    (hEeven : Even (Nat.card (↥E ⧸ Subgroup.center ↥E)))
    (hNn : N.Normal) (hNodd : Odd (Nat.card ↥N)) :
    N ≤ Subgroup.centralizer (E : Set X) := by
  haveI := hEn
  haveI := hNn
  set M : Subgroup X := ⁅E, N⁆ with hMdef
  have hME : M ≤ E := Subgroup.commutator_le_left E N
  have hMN : M ≤ N := Subgroup.commutator_le_right E N
  have hMnor : M.Normal := Subgroup.commutator_normal E N
  haveI := hMnor
  set Z : Subgroup ↥E := Subgroup.center ↥E with hZdef
  set ME : Subgroup ↥E := M.subgroupOf E with hMEdef
  have hMEnor : ME.Normal := hMnor.subgroupOf E
  haveI := hMEnor
  have hmapnor : (ME.map (QuotientGroup.mk' Z)).Normal :=
    Subgroup.Normal.map hMEnor _ (QuotientGroup.mk'_surjective Z)
  haveI := hmapnor
  rcases hEsimp.eq_bot_or_eq_top_of_normal (ME.map (QuotientGroup.mk' Z)) with hbot | htop
  · -- `M` centralises `E`, and the three subgroups lemma kills `⁅E,N⁆`
    have hMEleZ : ME ≤ Z := by
      have h := (Subgroup.map_eq_bot_iff ME).mp hbot
      rwa [QuotientGroup.ker_mk' Z] at h
    have hMcent : M ≤ Subgroup.centralizer (E : Set X) := by
      intro m hm
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have hmE : m ∈ E := hME hm
      have hz : (⟨m, hmE⟩ : ↥E) ∈ ME := hm
      have hzu : (⟨m, hmE⟩ : ↥E) ∈ Z := hMEleZ hz
      have hcomm : (⟨e, he⟩ : ↥E) * ⟨m, hmE⟩ = ⟨m, hmE⟩ * ⟨e, he⟩ :=
        Subgroup.mem_center_iff.mp hzu (⟨e, he⟩ : ↥E)
      exact congrArg Subtype.val hcomm
    have hMEbot : ⁅M, E⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hMcent
    have h2 : ⁅⁅N, E⁆, E⁆ = ⊥ := by
      rw [Subgroup.commutator_comm N E]
      exact hMEbot
    have h3 : ⁅⁅E, E⁆, N⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate hMEbot h2
    have hMbot : ⁅E, N⁆ = ⊥ := by
      rw [hEE] at h3
      exact h3
    exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hMbot)
  · -- `E/Z(E)` is a quotient of the odd-order group `M ≤ N`, but has even order
    exfalso
    have hdvd : Nat.card (↥E ⧸ Z) ∣ Nat.card ↥N := by
      have h1 : Nat.card (↥E ⧸ Z) = Nat.card ↥(ME.map (QuotientGroup.mk' Z)) := by
        rw [htop]
        exact (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
      rw [h1]
      refine (Subgroup.card_map_dvd ME (QuotientGroup.mk' Z)).trans ?_
      have h2 : Nat.card ↥ME = Nat.card ↥M := by
        rw [hMEdef]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hME).toEquiv
      rw [h2]
      exact Subgroup.card_dvd_of_le hMN
    exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hNodd hdvd)) hEeven

/-- **C10.A3' part 3** (Bender 1981, §4, p. 226: "Then `O(M) = B = F`"):
`O(M) = F`.

Hypotheses: `Hyp9 G B C`, `IsA7Case C.D` (`E(M)/Z(E) ≅ A₇`), `A7Facts1` (`|F| = 3`),
`A7Facts2` (`S ≤ E(M)`, `|S| = 8`) and `IsPGroup 3 B.U` (so that `F(U) = U`, whence `B₀ = F`).

Route.
* `F ⊴ M` (`N_G(F) = M`, `Case2Pre.N_F`) and `|F| = 3` is odd, so `F ≤ oddCoreIn D.M`; the
  equality reduces to `oddCoreIn D.M ≤ F`.
* The important step is `[O(M), E] = 1` where `E = layerIn D.M`.  `O(M)` is normal in `M` and
  odd, `E ⊴ M` is quasisimple (`Work.CORE4.LayerCtx6`) and `E/Z(E) ≅ A₇` has even order.
  Then `⁅O(M), E⁆ ≤ O(M) ⊓ E ⊴ E`, and `O(M) ⊓ E` is odd (being contained in `O(M)`), so its
  image in the simple group `E/Z(E)` is `⊥` or `⊤`; the second alternative would make `E` a
  quotient of an odd group of order ≥ 2520, impossible because `A₇` has even order.  Hence
  `⁅O(M), E⁆ ≤ Z(E)`, and since `E` is perfect (`IsQuasisimple`) the three-subgroup identity
  gives `⁅E, O(M)⁆ = ⁅E', O(M)⁆ ≤ ⁅E,E,O(M)⁆ ≤ ⁅⁅E,O(M)⁆,E⁆ = ⊥`.
  This is the argument of `Work.BMAX.nilpotent_normal_le_centralizer_of_quasisimple` with the
  parity of `E` replacing nilpotency of the normal subgroup (its final contradiction "`E ≤ N`
  nilpotent" becomes: `E ≤ O(M)` is odd while `|E| = |A₇| · |Z(E)|` is even).
* Consequently `O(M) ≤ C(E) ≤ C(t) = B.H` (because `t ∈ E`) and `O(M) ≤ C(s)` (because `s ∈ E`).
* Every `x ∈ oddCoreIn D.M` has odd order and lies in `B.H = B.U ⊔ S` (`Work.CORE4.A7Split`), and
  `S` is a `2`-group, so `x ∈ B.U` (`Work.CORE4.NineRyAux.OddMemU`).
* Hence `O(M) ≤ B.U ⊓ D.M ⊓ C({s}) = D.B0` (`D.B0_def`) and then `O(M) ≤ D.F`, because
  `D.F = D.B0 ⊓ F(U) = D.B0 ⊓ U = D.B0` for the `3`-group `U`
  (`Work.CORE4.fittingIn_eq_self_of_isPGroup`). -/
theorem A3UOddCore (I : Work.GW2.C4Inputs) : ∀ (G : Type) [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
    Work.GW2.Hyp9 G B C → Work.GW2.IsA7Case C.D → Work.GW2.A7Facts1 C.D →
      Work.GW2.A7Facts2 B C.D → IsPGroup 3 B.U → Work.GW2.oddCoreIn C.D.M = C.D.F := by
  intro G _ _ B C h9 hA7 h1 h2 hU3
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨hbc, -⟩ := h9
  -- `E = E(M)` is quasisimple
  have hDih : Work.GW2.DihOrCycSylow ↥C.D.M := Work.CORE4.DihOrCycSub hbc.sylow C.D.M
  obtain ⟨hEquasi, -, -⟩ := Work.CORE4.LayerCtx6 I hbc C hDih
  -- elementary containments
  have hOle : Work.GW2.oddCoreIn C.D.M ≤ C.D.M := by
    rw [Work.GW2.oddCoreIn]
    exact Subgroup.map_subtype_le _
  have hElayer : Work.GW2.layerIn C.D.M ≤ C.D.M := by
    rw [Work.GW2.layerIn]
    exact Subgroup.map_subtype_le _
  have hOodd : Odd (Nat.card ↥(Work.GW2.oddCoreIn C.D.M)) := by
    have h : Nat.card ↥(Work.GW2.oddCoreIn C.D.M) = Nat.card ↥(Work.GW2.oddCore ↥C.D.M) := by
      rw [Work.GW2.oddCoreIn]
      exact Subgroup.card_map_of_injective C.D.M.subtype_injective
    rw [h]
    exact Work.CORE4.oddCore_odd ↥C.D.M
  -- the crucial step `[O(M), E(M)] = 1`
  have hOcent : Work.GW2.oddCoreIn C.D.M ≤
      Subgroup.centralizer ((Work.GW2.layerIn C.D.M : Subgroup G) : Set G) := by
    set E' : Subgroup ↥C.D.M := (Work.GW2.layerIn C.D.M).subgroupOf C.D.M with hE'def
    set N' : Subgroup ↥C.D.M := (Work.GW2.oddCoreIn C.D.M).subgroupOf C.D.M with hN'def
    have hE'eq : E' = Work.GW2.layer ↥C.D.M := by
      rw [hE'def, Work.GW2.layerIn, Subgroup.subgroupOf]
      exact Subgroup.comap_map_eq_self_of_injective C.D.M.subtype_injective _
    have hN'eq : N' = Work.GW2.oddCore ↥C.D.M := by
      rw [hN'def, Work.GW2.oddCoreIn, Subgroup.subgroupOf]
      exact Subgroup.comap_map_eq_self_of_injective C.D.M.subtype_injective _
    have hE'n : E'.Normal := by
      rw [hE'eq, Work.GW2.layer]
      exact Subgroup.sSup_normal _ (fun _ hH => hH.1)
    have hN'n : N'.Normal := by
      rw [hN'eq]
      exact Work.GW2.oddCore_normal ↥C.D.M
    have hN'odd : Odd (Nat.card ↥N') := by
      rw [hN'eq]
      exact Work.CORE4.oddCore_odd ↥C.D.M
    have hEE' : ⁅E', E'⁆ = E' := by
      refine Subgroup.map_injective (f := C.D.M.subtype) C.D.M.subtype_injective ?_
      rw [Subgroup.map_commutator]
      have hmap : E'.map C.D.M.subtype = Work.GW2.layerIn C.D.M := by
        rw [hE'def]
        exact Subgroup.map_subgroupOf_eq_of_le hElayer
      rw [hmap]
      exact hEquasi.1
    -- transport of `E' ≃* E(M)` and of the quotient data
    have hiso : ↥E' ≃* ↥(Work.GW2.layerIn C.D.M) := Subgroup.subgroupOfEquivOfLe hElayer
    have hcen : (Subgroup.center ↥E').map (hiso : ↥E' →* ↥(Work.GW2.layerIn C.D.M)) =
        Subgroup.center ↥(Work.GW2.layerIn C.D.M) := Work.CORE4.map_center_mulEquiv hiso
    have hEsimp : IsSimpleGroup (↥E' ⧸ Subgroup.center ↥E') := by
      haveI : IsSimpleGroup (↥(Work.GW2.layerIn C.D.M) ⧸
          Subgroup.center ↥(Work.GW2.layerIn C.D.M)) := hEquasi.2
      exact Work.CORE4.isSimpleGroup_of_mulEquiv
        (QuotientGroup.congr (Subgroup.center ↥E')
          (Subgroup.center ↥(Work.GW2.layerIn C.D.M)) hiso hcen).symm
    have h2520 : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    have hEeven : Even (Nat.card (↥E' ⧸ Subgroup.center ↥E')) := by
      obtain ⟨φ⟩ := hA7
      have hq : Nat.card (↥E' ⧸ Subgroup.center ↥E') =
          Nat.card ↥(alternatingGroup (Fin 7)) :=
        Nat.card_congr ((QuotientGroup.congr (Subgroup.center ↥E')
          (Subgroup.center ↥(Work.GW2.layerIn C.D.M)) hiso hcen).trans φ).toEquiv
      rw [hq, h2520]
      norm_num
    have hcent : N' ≤ Subgroup.centralizer (E' : Set ↥C.D.M) :=
      odd_normal_le_centralizer_of_quasisimple_aux hE'n hEE' hEsimp hEeven hN'n hN'odd
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxM : x ∈ C.D.M := hOle hx
    have hyM : y ∈ C.D.M := hElayer hy
    have hxN' : (⟨x, hxM⟩ : ↥C.D.M) ∈ N' := by
      rw [hN'def]
      exact Subgroup.mem_subgroupOf.mpr hx
    have hyE' : (⟨y, hyM⟩ : ↥C.D.M) ∈ E' := by
      rw [hE'def]
      exact Subgroup.mem_subgroupOf.mpr hy
    have hcomm := Subgroup.mem_centralizer_iff.mp (hcent hxN') (⟨y, hyM⟩ : ↥C.D.M) hyE'
    exact congrArg Subtype.val hcomm
  -- `x ∈ O(M)` has odd order, lies in `C(E) ≤ B.H = U ⊔ S`, hence in `U`
  have hO_le_H : Work.GW2.oddCoreIn C.D.M ≤ B.H :=
    le_trans hOcent (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr C.D.t_mem))
  have hO_le_Cs : Work.GW2.oddCoreIn C.D.M ≤ Subgroup.centralizer ({C.D.s} : Set G) :=
    le_trans hOcent (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr (Work.GW2.Case2Data.s_mem_layer B C.D)))
  have hHsplit : B.H = B.U ⊔ (B.S : Subgroup G) := Work.CORE4.A7Split I hbc h2
  -- `F = B₀` for the `3`-group `U`
  have hF_eq_B0 : C.D.F = C.D.B0 := by
    rw [C.D.F_def, Work.CORE4.fittingIn_eq_self_of_isPGroup (p := 3) hU3,
      inf_eq_left.mpr (le_trans (Work.GW2.Case2Data.B0_le B C.D) inf_le_left)]
  have hFM : C.D.F ≤ C.D.M :=
    le_trans (Work.GW2.Case2Data.F_le_B0 B C.D)
      (le_trans (Work.GW2.Case2Data.B0_le B C.D) inf_le_right)
  have hFodd : Odd (Nat.card ↥C.D.F) := by
    rw [h1.2.1]
    norm_num
  refine le_antisymm ?_ ?_
  · -- `O(M) ≤ F`
    intro x hx
    have hxM : x ∈ C.D.M := hOle hx
    have hxH : x ∈ B.H := hO_le_H hx
    have hxodd : Odd (orderOf x) :=
      Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard _ hx)
    have hxU : x ∈ B.U := Work.CORE4.NineRyAux.OddMemU B hHsplit hxH hxodd
    have hxs : x ∈ Subgroup.centralizer ({C.D.s} : Set G) := hO_le_Cs hx
    have hxB0 : x ∈ C.D.B0 := by
      rw [C.D.B0_def]
      exact ⟨⟨hxU, hxM⟩, hxs⟩
    simpa [hF_eq_B0] using hxB0
  · -- `F ≤ O(M)`
    refine le_oddCoreIn_of_normal_of_odd_aux hFM ?_ hFodd
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hFM).mpr ?_
    exact le_of_eq (Work.GW2.Case2Pre.N_F B C.D C.pre).symm

end Work.CORE4.NotA7
