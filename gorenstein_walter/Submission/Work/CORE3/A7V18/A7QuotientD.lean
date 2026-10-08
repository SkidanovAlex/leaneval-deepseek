import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1aFrattini
import Submission.Work.CORE3.Case1aAbelian
import Submission.Work.CORE3.MDataAux
import Submission.Work.CORE3.A7V18.P0ne
import Submission.Work.CORE3.A7V18.V2LayerMne
import Submission.Work.CORE3.A7V18.V2InLayer
import Submission.Work.CORE3.A7V18.LayerMapOddCoreIso
import Submission.Work.CORE3.A7V18.MapQuotientCenterIso
import Submission.Work.CORE3.A7V18.Prelim
import Submission.Work.CORE3.A7V18.NoA7SectionOfPSL2
import Submission.Work.CORE3.A7V18.le_of_inverts_of_odd
import Submission.Work.DSTR.layerShape
import Submission.Work.DSTR.layerShapeAux.isQuasisimple_inf_oddCore_le_center
import Submission.Work.ASM.oddCore_odd
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.dihOrCycSylow_subgroup

open scoped MatrixGroups

namespace Work.CORE3.A7V18

open Subgroup Work.GW2

/-! ## Elementary transport of four-group structure -/

/-- The image of a four-group under an injective homomorphism is a four-group. -/
theorem isFourGroup_map_of_injective' {G H : Type*} [Group G] [Group H]
    {V : Subgroup G} (hV : Work.GW2.IsFourGroup V) (f : G →* H) (hf : Function.Injective f) :
    Work.GW2.IsFourGroup (V.map f) := by
  refine ⟨?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hf]; exact hV.1
  · intro v hv
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
    rw [← map_pow, hV.2 u hu, map_one]

/-- `V ≤ K` and `V` a four-group imply `V.subgroupOf K` is a four-group. -/
theorem isFourGroup_subgroupOf_of_le' {G : Type*} [Group G] {V K : Subgroup G}
    (hV : Work.GW2.IsFourGroup V) (h : V ≤ K) : Work.GW2.IsFourGroup (V.subgroupOf K) := by
  refine ⟨?_, ?_⟩
  · have hcard := Subgroup.card_map_of_injective
      (K := V.subgroupOf K) (f := K.subtype) K.subtype_injective
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left h] at hcard
    rw [← hcard]; exact hV.1
  · intro v hv
    rw [Subgroup.mem_subgroupOf] at hv
    exact Subtype.ext (by simpa using hV.2 (v : G) hv)

/-- If four-groups are self-centralizing in `M` and `e : ↥L ≃* M`, then every element of `L`
centralizing a four-group `W ≤ L` lies in `W`. -/
theorem mem_of_mem_centralizer_of_iso' {Q M : Type*} [Group Q] [Group M]
    (L : Subgroup Q) (e : ↥L ≃* M) (W : Subgroup Q) (hWL : W ≤ L)
    (hW4 : Work.GW2.IsFourGroup W)
    (hfour : ∀ V : Subgroup M, Work.GW2.IsFourGroup V → Subgroup.centralizer (V : Set M) = V)
    {x : Q} (hxL : x ∈ L) (hxc : x ∈ Subgroup.centralizer (W : Set Q)) : x ∈ W := by
  have hV4 : Work.GW2.IsFourGroup (W.subgroupOf L) := isFourGroup_subgroupOf_of_le' hW4 hWL
  have hV4' : Work.GW2.IsFourGroup ((W.subgroupOf L).map e.toMonoidHom) :=
    isFourGroup_map_of_injective' hV4 e.toMonoidHom e.injective
  have hc := hfour ((W.subgroupOf L).map e.toMonoidHom) hV4'
  have hex_c : e ⟨x, hxL⟩ ∈
      Subgroup.centralizer (((W.subgroupOf L).map e.toMonoidHom : Subgroup M) : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
    have hwW : ((w : ↥L) : Q) ∈ W := by
      rw [Subgroup.mem_subgroupOf] at hw; exact hw
    have hxcomm : ((w : ↥L) : Q) * x = x * ((w : ↥L) : Q) :=
      Subgroup.mem_centralizer_iff.mp hxc _ hwW
    have hmul : w * (⟨x, hxL⟩ : ↥L) = (⟨x, hxL⟩ : ↥L) * w := by
      apply Subtype.ext
      show ((w : ↥L) : Q) * x = x * ((w : ↥L) : Q)
      exact hxcomm
    calc e w * e ⟨x, hxL⟩ = e (w * ⟨x, hxL⟩) := (map_mul e.toMonoidHom w _).symm
      _ = e ((⟨x, hxL⟩ : ↥L) * w) := by rw [hmul]
      _ = e ⟨x, hxL⟩ * e w := map_mul e.toMonoidHom _ _
  rw [hc] at hex_c
  obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp hex_c
  have hthis : w = (⟨x, hxL⟩ : ↥L) := e.injective hwx
  have hxw : x = ((w : ↥L) : Q) := by rw [hthis]
  rw [hxw]
  rw [Subgroup.mem_subgroupOf] at hw
  exact hw

/-- An odd-order subgroup of a group `Q` contained in `L ≃* PSL(2,q)` (or `PGL(2,q)`) and in the
centralizer of a four-group `W ≤ L` is trivial: four-groups are self-centralizing there, so
`A ≤ C_L(W) = W`, and `W` has exponent `2`. -/
theorem oddSubCentralizerFourL2_local {Q : Type} [Group Q] [Finite Q]
    (L : Subgroup Q) (p k : ℕ) [Fact p.Prime] (hpodd : Odd p) (h5 : 5 ≤ p ^ k)
    (hLiso : Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) ∨
             Nonempty (L ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k)))
    (l2four : Work.GW2.L2FourGroupProp)
    (A W : Subgroup Q) (hWL : W ≤ L) (hW4 : Work.GW2.IsFourGroup W) (hAL : A ≤ L)
    (hAodd : Odd (Nat.card A)) (hAc : A ≤ Subgroup.centralizer (W : Set Q)) :
    A = ⊥ := by
  have hALW : A ≤ W := by
    intro x hx
    rcases hLiso with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact mem_of_mem_centralizer_of_iso' L e W hWL hW4
        (fun V hV => (l2four p k hpodd h5).1 V hV) (hAL hx) (hAc hx)
    · exact mem_of_mem_centralizer_of_iso' L e W hWL hW4
        (fun V hV => (l2four p k hpodd h5).2 V hV) (hAL hx) (hAc hx)
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hxW : x ∈ W := hALW hx
  have hx2 : x * x = 1 := by
    have h := hW4.2 x hxW
    rwa [pow_two] at h
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
  have h2 : Odd (orderOf x) := Odd.of_dvd_nat hAodd (Subgroup.orderOf_dvd_natCard A hx)
  have h3 : orderOf x = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at h2; exact absurd h2 (by decide)
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h3)

/-! ## The `DShape` analysis of a normal quasisimple subgroup -/

/-- If `X` is a D-group (`DShape (X / O(X))`), `E ◁ X` is quasisimple with `E ≰ O(X)`, and the
`L₂(q)` clause of `DShape` is impossible for the ambient group (hypothesis `hkey`), then
`E / Z(E) ≅ A₇`. -/
theorem a7_of_dshape {X : Type} [Group X] [Finite X]
    (hFT : Work.GW2.FeitThompsonProp)
    (hD : Work.GW2.DShape (X ⧸ Work.GW2.oddCore X))
    (hkey : ∀ (L : Subgroup (X ⧸ Work.GW2.oddCore X)) (hLn : L.Normal) (hLodd : Odd L.index)
      (p k : ℕ) [Fact p.Prime] (hpodd : Odd p) (h5 : 5 ≤ p ^ k),
      (Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) ∨
        Nonempty (L ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k))) → False)
    {E : Subgroup X} (hEn : E.Normal) (hEq : Work.GW2.IsQuasisimple E)
    (hne : ¬ E ≤ Work.GW2.oddCore X) :
    Nonempty (↥E ⧸ Subgroup.center ↥E ≃* alternatingGroup (Fin 7)) := by
  classical
  haveI hOn : (Work.GW2.oddCore X).Normal := Work.GW2.oddCore_normal X
  have hcen : (E ⊓ Work.GW2.oddCore X).subgroupOf E ≤ Subgroup.center ↥E :=
    inf_oddCore_subgroupOf_le_center hFT hEq
  obtain ⟨hĒn, hĒq, hĒne, ⟨eĒ⟩⟩ :=
    MapQuotientCenterIso E (Work.GW2.oddCore X) hEn hEq hcen hne
  rcases hD with hpg | ⟨V, hVn, hV4, hVc⟩ | ⟨⟨e7⟩⟩ |
    ⟨L, hLn, hLodd, p, k, hp, hpodd, h5, hLiso⟩
  · exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent (X ⧸ Work.GW2.oddCore X) := hpg.isNilpotent
    haveI hnt : Nontrivial
        ↥(E.map (QuotientGroup.mk' (Work.GW2.oddCore X))) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hĒne
    haveI hperf : Group.IsPerfect
        ↥(E.map (QuotientGroup.mk' (Work.GW2.oddCore X))) :=
      Subgroup.isPerfect_iff.mpr hĒq.1
    exact Group.IsPerfect.not_isSolvable ↥(E.map (QuotientGroup.mk' (Work.GW2.oddCore X)))
      (inferInstance : Group.IsSolvable ↥(E.map (QuotientGroup.mk' (Work.GW2.oddCore X))))
  · exfalso
    haveI hsolQ : Group.IsSolvable (X ⧸ Work.GW2.oddCore X) :=
      Work.DSTR.isSolvable_of_normal_fourGroup_selfCentralizing V hVn hV4 hVc
    haveI hnt : Nontrivial
        ↥(E.map (QuotientGroup.mk' (Work.GW2.oddCore X))) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hĒne
    haveI hperf : Group.IsPerfect
        ↥(E.map (QuotientGroup.mk' (Work.GW2.oddCore X))) :=
      Subgroup.isPerfect_iff.mpr hĒq.1
    exact Group.IsPerfect.not_isSolvable ↥(E.map (QuotientGroup.mk' (Work.GW2.oddCore X)))
      (inferInstance : Group.IsSolvable ↥(E.map (QuotientGroup.mk' (Work.GW2.oddCore X))))
  · haveI hA7simple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (α := Fin 7) (by rw [Nat.card_eq_fintype_card]; norm_num)
    haveI : IsSimpleGroup (X ⧸ Work.GW2.oddCore X) := MulEquiv.isSimpleGroup e7
    have hĒtop : E.map (QuotientGroup.mk' (Work.GW2.oddCore X)) = ⊤ := by
      rcases Subgroup.Normal.eq_bot_or_eq_top
        (E.map (QuotientGroup.mk' (Work.GW2.oddCore X))) with h | h
      · exact absurd h hĒne
      · exact h
    have hZQ : Subgroup.center (X ⧸ Work.GW2.oddCore X) = ⊥ := by
      have h1 : (Subgroup.center (X ⧸ Work.GW2.oddCore X)).map e7.toMonoidHom =
          Subgroup.center (alternatingGroup (Fin 7)) := Subgroup.map_center_eq e7
      rw [alternatingGroup.center_eq_bot (α := Fin 7)
        (by rw [Nat.card_eq_fintype_card]; norm_num)] at h1
      have h2 : Subgroup.center (X ⧸ Work.GW2.oddCore X) ≤ e7.toMonoidHom.ker :=
        (Subgroup.map_eq_bot_iff _).mp h1
      have h3 : e7.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr e7.injective
      rw [h3] at h2
      exact le_bot_iff.mp h2
    have eĒQ : ↥(E.map (QuotientGroup.mk' (Work.GW2.oddCore X))) ≃*
        (X ⧸ Work.GW2.oddCore X) :=
      (MulEquiv.subgroupCongr hĒtop).trans Subgroup.topEquiv
    have eC : (↥(E.map (QuotientGroup.mk' (Work.GW2.oddCore X))) ⧸
        Subgroup.center ↥(E.map (QuotientGroup.mk' (Work.GW2.oddCore X)))) ≃*
        ((X ⧸ Work.GW2.oddCore X) ⧸ Subgroup.center (X ⧸ Work.GW2.oddCore X)) :=
      QuotientGroup.congr _ _ eĒQ (Subgroup.map_center_eq eĒQ)
    have eQ7 : ((X ⧸ Work.GW2.oddCore X) ⧸ Subgroup.center (X ⧸ Work.GW2.oddCore X)) ≃*
        alternatingGroup (Fin 7) :=
      (QuotientGroup.quotientMulEquivOfEq hZQ).trans (QuotientGroup.quotientBot.trans e7)
    exact ⟨eĒ.trans (eC.trans eQ7)⟩
  · exfalso
    haveI : Fact p.Prime := hp
    exact hkey L hLn hLodd p k hpodd h5 hLiso

theorem A7QuotientD (I : Work.CORE3.Case1Inputs) (hFr : Work.GW2.Case1aFrattiniProp)
    (hAb : Work.GW2.Case1aAbelianProp) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case1 B → B.Hhat = B.H → ∀ D : Work.GW2.Case1aData B, ∀ P2 M : Subgroup G,
        P2 ≤ B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) → IsPGroup D.p P2 →
        ¬ D.p ∣ P2.relIndex (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) →
        IsCoatom M → Subgroup.normalizer (P2 : Set G) ≤ M →
        (Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G) ≠ ⊥ →
        (Subgroup.zpowers B.t ⊔ Subgroup.zpowers D.t2 : Subgroup G) ≤ Work.GW2.layerIn M →
        Nonempty ((↥(Work.GW2.layerIn M) ⧸ Subgroup.center ↥(Work.GW2.layerIn M)) ≃*
          alternatingGroup (Fin 7)) := by
  intro G _instG _finG hFT hBc B hCase hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM hP0 hV2
  classical
  haveI hpprime : Fact D.p.Prime := ⟨D.hp⟩
  -- `S ≤ M`, and membership of the relevant elements
  have hSleM : (B.S : Subgroup G) ≤ M := S_le_M B hP2le hNM
  have htM : B.t ∈ M := hSleM (B.S0_le B.t_mem)
  have ht1S : D.t1 ∈ (B.S : Subgroup G) := D.t1_mem
  have ht1M : D.t1 ∈ M := hSleM ht1S
  have ht2M : D.t2 ∈ M := hSleM D.t2_mem
  have ht : B.t ∈ Work.GW2.layerIn M :=
    hV2 (Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t))
  have ht2 : D.t2 ∈ Work.GW2.layerIn M :=
    hV2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t2))
  -- the layer of `M` is nontrivial
  have hEne : Work.GW2.layer ↥M ≠ ⊥ := by
    intro hbot
    have hb : Work.GW2.layerIn M = ⊥ := by
      rw [Work.GW2.layerIn, hbot, Subgroup.map_bot]
    rw [hb] at ht
    exact Work.CORE2A.bSetup_t_ne_one B (Subgroup.mem_bot.mp ht)
  obtain ⟨hEq, hOddZ⟩ := Work.CORE3.mdata_layer_quasisimple I hBc B hMcoat hEne
  have hEn : (Work.GW2.layer ↥M).Normal := Work.CORE3.mdata_layer_normal M
  have hne : ¬ Work.GW2.layer ↥M ≤ Work.GW2.oddCore ↥M :=
    Work.DSTR.not_le_oddCore_of_isQuasisimple hFT hEq
  -- `M` is a D-group
  have hcard_lt : Nat.card ↥M < Nat.card G := Subgroup.card_lt_card_of_ne_top hMcoat.ne_top
  have hDih : Work.GW2.DihOrCycSylow ↥M := Work.CORE2A.dihOrCycSylow_subgroup hBc.sylow M
  have hD : Work.GW2.DShape (↥M ⧸ Work.GW2.oddCore ↥M) := hBc.ih ↥M hcard_lt hDih
  -- the local killing of the `L₂(q)` clause
  have hkey : ∀ (L : Subgroup (↥M ⧸ Work.GW2.oddCore ↥M)) (hLn : L.Normal)
      (hLodd : Odd L.index) (p k : ℕ) [Fact p.Prime] (hpodd : Odd p) (h5 : 5 ≤ p ^ k),
      (Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)) ∨
        Nonempty (L ≃* Matrix.ProjGenLinGroup (Fin 2) (GaloisField p k))) → False := by
    intro L hLn hLodd p k hpp hpodd h5 hLiso
    haveI : L.Normal := hLn
    haveI : Fact p.Prime := hpp
    let O : Subgroup ↥M := Work.GW2.oddCore ↥M
    let E' : Subgroup ↥M := Work.GW2.layer ↥M
    have hOodd : Odd (Nat.card ↥O) := Work.ASM.oddCore_odd ↥M
    have hE'q : Work.GW2.IsQuasisimple E' := hEq
    have hE'n : E'.Normal := hEn
    have hcen : (E' ⊓ O).subgroupOf E' ≤ Subgroup.center ↥E' :=
      inf_oddCore_subgroupOf_le_center hFT hEq
    have hne' : ¬ E' ≤ O := hne
    obtain ⟨hĒn, hĒq, hĒne, _⟩ := MapQuotientCenterIso E' O hE'n hE'q hcen hne'
    have hEL : E'.map (QuotientGroup.mk' O) ≤ L :=
      le_of_odd_index_of_perfect hFT L hLn hLodd (E'.map (QuotientGroup.mk' O)) hĒq.1
    -- elements of `E' = layer ↥M`
    have htE : (⟨B.t, htM⟩ : ↥M) ∈ E' := by
      have h1 : B.t ∈ (Work.GW2.layer ↥M).map M.subtype := ht
      obtain ⟨e, he, heq⟩ := Subgroup.mem_map.mp h1
      have h2 : e = ⟨B.t, htM⟩ := Subtype.ext heq
      rwa [h2] at he
    have ht2E : (⟨D.t2, ht2M⟩ : ↥M) ∈ E' := by
      have h1 : D.t2 ∈ (Work.GW2.layer ↥M).map M.subtype := ht2
      obtain ⟨e, he, heq⟩ := Subgroup.mem_map.mp h1
      have h2 : e = ⟨D.t2, ht2M⟩ := Subtype.ext heq
      rwa [h2] at he
    -- `P₀ ≤ E(M)` and `P := P₀ ≤ ↥M`
    have hP0leLayer : (Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G) ≤ Work.GW2.layerIn M :=
      le_of_inverts_of_odd (le_normalizer_layerIn M) inf_le_right ht2
        (fun x hx => D.inv x hx.1) (odd_card_pCoreIn_inf B D)
    set P : Subgroup ↥M := (Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G).subgroupOf M with hPdef
    have hPE : P ≤ E' := by
      intro x hx
      rw [hPdef, Subgroup.mem_subgroupOf] at hx
      have hxL : (x : G) ∈ Work.GW2.layerIn M := hP0leLayer hx
      have h1 : (x : G) ∈ (Work.GW2.layer ↥M).map M.subtype := hxL
      obtain ⟨e, he, heq⟩ := Subgroup.mem_map.mp h1
      have h2 : e = x := Subtype.ext heq
      rwa [h2] at he
    have hPne : P ≠ ⊥ := by
      intro h
      apply hP0
      have h1 : P.map M.subtype = ⊥ := by rw [h, Subgroup.map_bot]
      rw [hPdef, Subgroup.subgroupOf_map_subtype] at h1
      rwa [inf_of_le_left inf_le_right] at h1
    -- the two involutions and the four-group they generate
    set u : ↥M ⧸ O := QuotientGroup.mk' O ⟨B.t, htM⟩ with hudef
    set v : ↥M ⧸ O := QuotientGroup.mk' O ⟨D.t1, ht1M⟩ with hvdef
    have hBsq : (⟨B.t, htM⟩ : ↥M) * ⟨B.t, htM⟩ = 1 :=
      Subtype.ext (by rw [← pow_two, ← B.t_order]; exact pow_orderOf_eq_one B.t)
    have ht1sq : (⟨D.t1, ht1M⟩ : ↥M) * ⟨D.t1, ht1M⟩ = 1 :=
      Subtype.ext (by rw [← pow_two, ← D.t1_order]; exact pow_orderOf_eq_one D.t1)
    have hcommM : (⟨B.t, htM⟩ : ↥M) * ⟨D.t1, ht1M⟩ = ⟨D.t1, ht1M⟩ * ⟨B.t, htM⟩ := by
      apply Subtype.ext
      show B.t * D.t1 = D.t1 * B.t
      exact Subgroup.mem_centralizer_iff.mp (Work.CORE2A.bSetup_S_le_H B ht1S) B.t
        (Set.mem_singleton B.t)
    have hu2 : u ^ 2 = 1 := by
      rw [pow_two, hudef, ← map_mul, hBsq, map_one]
    have hv2 : v ^ 2 = 1 := by
      rw [pow_two, hvdef, ← map_mul, ht1sq, map_one]
    have huvc : u * v = v * u := by
      rw [hudef, hvdef, ← map_mul, ← map_mul, hcommM]
    have htv_sq : ((⟨B.t, htM⟩ : ↥M) * ⟨D.t1, ht1M⟩) ^ 2 = 1 := by
      have e : (⟨B.t, htM⟩ : ↥M) * ⟨D.t1, ht1M⟩ * (⟨B.t, htM⟩ * ⟨D.t1, ht1M⟩)
          = (⟨B.t, htM⟩ * (⟨D.t1, ht1M⟩ * ⟨B.t, htM⟩)) * ⟨D.t1, ht1M⟩ := by group
      rw [pow_two, e, ← hcommM]
      rw [show (⟨B.t, htM⟩ : ↥M) * (⟨B.t, htM⟩ * ⟨D.t1, ht1M⟩) * ⟨D.t1, ht1M⟩
          = (⟨B.t, htM⟩ * ⟨B.t, htM⟩) * (⟨D.t1, ht1M⟩ * ⟨D.t1, ht1M⟩) from by group]
      rw [hBsq, ht1sq, mul_one]
    have htv_ne : (⟨B.t, htM⟩ : ↥M) * ⟨D.t1, ht1M⟩ ≠ 1 := by
      intro h
      apply D.t1_nmem
      have h1 : B.t * D.t1 = 1 := congrArg (fun x : ↥M => (x : G)) h
      have h2 : D.t1 = B.t := by
        calc D.t1 = (B.t * B.t) * D.t1 := by
              rw [show B.t * B.t = 1 from Subtype.ext_iff.mp hBsq, one_mul]
          _ = B.t * (B.t * D.t1) := by rw [mul_assoc]
          _ = B.t * 1 := by rw [h1]
          _ = B.t := mul_one B.t
      rw [h2]; exact B.t_mem
    have notMemO : ∀ x : ↥M, orderOf x = 2 → x ∉ O := by
      intro x hx hxO
      have hdvd : orderOf x ∣ Nat.card ↥O := Subgroup.orderOf_dvd_natCard O hxO
      rw [hx] at hdvd
      exact (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr hdvd)
    have hu1 : u ≠ 1 := by
      intro h
      rw [hudef] at h
      exact notMemO ⟨B.t, htM⟩ (by rw [Subgroup.orderOf_mk, B.t_order])
        ((QuotientGroup.eq_one_iff (⟨B.t, htM⟩ : ↥M)).mp h)
    have hv1 : v ≠ 1 := by
      intro h
      rw [hvdef] at h
      exact notMemO ⟨D.t1, ht1M⟩ (by rw [Subgroup.orderOf_mk, D.t1_order])
        ((QuotientGroup.eq_one_iff (⟨D.t1, ht1M⟩ : ↥M)).mp h)
    have huvne : u ≠ v := by
      intro h
      have h1 : (⟨B.t, htM⟩ : ↥M) * ⟨D.t1, ht1M⟩ ∈ O := by
        apply (QuotientGroup.eq_one_iff _).mp
        rw [← QuotientGroup.mk'_apply, map_mul, ← hudef, ← hvdef, h, ← pow_two, hv2]
      exact notMemO _ (orderOf_eq_prime htv_sq htv_ne) h1
    have hW4 : Work.GW2.IsFourGroup
        (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup (↥M ⧸ O)) :=
      Work.CORE3.MData.isFourGroup_zpowers_sup hu2 hv2 huvc hu1 hv1 huvne
    -- `v ∈ L` because `L` has odd index
    have hvL : v ∈ L := by
      have hord : orderOf (QuotientGroup.mk' L v) ∣ 2 :=
        orderOf_dvd_of_pow_eq_one (by rw [pow_two, ← map_mul, ← pow_two, hv2, map_one])
      have hdvd : orderOf (QuotientGroup.mk' L v) ∣
          Nat.card ↥(⊤ : Subgroup ((↥M ⧸ O) ⧸ L)) :=
        Subgroup.orderOf_dvd_natCard ⊤ (Subgroup.mem_top _)
      have htopcard : Nat.card ↥(⊤ : Subgroup ((↥M ⧸ O) ⧸ L)) = L.index := by
        rw [Nat.card_congr (Subgroup.topEquiv).toEquiv, ← Subgroup.index_eq_card]
      have hoddord : Odd (orderOf (QuotientGroup.mk' L v)) := by
        rw [htopcard] at hdvd; exact Odd.of_dvd_nat hLodd hdvd
      have hone : orderOf (QuotientGroup.mk' L v) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hord with h | h
        · exact h
        · rw [h] at hoddord; exact absurd hoddord (by decide)
      have h1 : QuotientGroup.mk' L v = 1 := orderOf_eq_one_iff.mp hone
      rw [QuotientGroup.mk'_apply] at h1
      exact (QuotientGroup.eq_one_iff v).mp h1
    have huL : u ∈ L := hEL (Subgroup.mem_map_of_mem _ htE)
    have hWL : (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup (↥M ⧸ O)) ≤ L :=
      sup_le (Subgroup.zpowers_le.mpr huL) (Subgroup.zpowers_le.mpr hvL)
    -- `A = P·O/O`
    set A : Subgroup (↥M ⧸ O) := P.map (QuotientGroup.mk' O) with hAdef
    have hAL : A ≤ L := (Subgroup.map_mono hPE).trans hEL
    have hPcard : Nat.card ↥P =
        Nat.card ↥(Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G) := by
      have hmap : P.map M.subtype = (Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G) := by
        rw [hPdef, Subgroup.subgroupOf_map_subtype]
        exact inf_of_le_left inf_le_right
      have h := Subgroup.card_map_of_injective (K := P) (f := M.subtype) M.subtype_injective
      rw [hmap] at h
      exact h.symm
    have hPodd : Odd (Nat.card ↥P) := by
      rw [hPcard]; exact odd_card_pCoreIn_inf B D
    have hAodd : Odd (Nat.card ↥A) := by
      rw [hAdef]
      exact Odd.of_dvd_nat hPodd (Subgroup.card_map_dvd P (QuotientGroup.mk' O))
    -- involutions centralize `P`
    have ht_cen_P : ∀ q ∈ P, (⟨B.t, htM⟩ : ↥M) * q = q * ⟨B.t, htM⟩ := by
      intro q hq
      apply Subtype.ext
      show B.t * (q : G) = (q : G) * B.t
      have hqG : (q : G) ∈ (Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G) := by
        rw [hPdef, Subgroup.mem_subgroupOf] at hq; exact hq
      have hqH : (q : G) ∈ B.H :=
        (le_trans (Work.CORE3.pCoreIn_le_self D.p B.U) (Work.CORE3.oddCoreIn_le_self B.H))
          hqG.1
      exact Subgroup.mem_centralizer_iff.mp hqH B.t (Set.mem_singleton B.t)
    have ht1_cen_P : ∀ q ∈ P, (⟨D.t1, ht1M⟩ : ↥M) * q = q * ⟨D.t1, ht1M⟩ := by
      intro q hq
      apply Subtype.ext
      show D.t1 * (q : G) = (q : G) * D.t1
      have hqG : (q : G) ∈ (Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G) := by
        rw [hPdef, Subgroup.mem_subgroupOf] at hq; exact hq
      exact Subgroup.mem_centralizer_iff.mp (D.cent hqG.1) D.t1 (Set.mem_singleton D.t1)
    have hu_cen_A : u ∈ Subgroup.centralizer (A : Set (↥M ⧸ O)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [hAdef] at hx
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
      rw [hudef, ← map_mul, ← map_mul, ht_cen_P q hq]
    have hv_cen_A : v ∈ Subgroup.centralizer (A : Set (↥M ⧸ O)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rw [hAdef] at hx
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hx
      rw [hvdef, ← map_mul, ← map_mul, ht1_cen_P q hq]
    have hAc : A ≤ Subgroup.centralizer
        ((Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup (↥M ⧸ O)) : Set (↥M ⧸ O)) := by
      rw [Subgroup.le_centralizer_iff]
      apply sup_le
      · rw [Subgroup.zpowers_le]; exact hu_cen_A
      · rw [Subgroup.zpowers_le]; exact hv_cen_A
    have hAbot : A = ⊥ :=
      oddSubCentralizerFourL2_local L p k hpodd h5 hLiso I.T.l2four A
        (Subgroup.zpowers u ⊔ Subgroup.zpowers v : Subgroup (↥M ⧸ O))
        hWL hW4 hAL hAodd hAc
    -- `A = ⊥` forces `P = ⊥`
    exfalso
    have hPO : P ≤ O := by
      have h : P.map (QuotientGroup.mk' O) = ⊥ := hAbot
      rw [Subgroup.map_eq_bot_iff] at h
      intro x hx
      have h1 : QuotientGroup.mk' O x = 1 := MonoidHom.mem_ker.mp (h hx)
      rw [QuotientGroup.mk'_apply] at h1
      exact (QuotientGroup.eq_one_iff x).mp h1
    apply hPne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxE' : x ∈ E' := hPE hx
    have hxO : x ∈ O := hPO hx
    have hxZmap : x ∈ (Subgroup.center ↥E').map E'.subtype :=
      Work.DSTR.layerShapeAux.isQuasisimple_inf_oddCore_le_center hFT hEq
        (Subgroup.mem_inf.mpr ⟨hxE', hxO⟩)
    obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp hxZmap
    have hcx' : c = ⟨x, hxE'⟩ := Subtype.ext hcx
    have hxZ : (⟨x, hxE'⟩ : ↥E') ∈ Subgroup.center ↥E' := hcx' ▸ hc
    have hscen : (⟨D.t2, ht2M⟩ : ↥M) * x * (⟨D.t2, ht2M⟩ : ↥M)⁻¹ = x := by
      have hcommE : (⟨D.t2, ht2M⟩ : ↥M) * x = x * (⟨D.t2, ht2M⟩ : ↥M) :=
        congrArg (fun z : ↥E' => (z : ↥M))
          ((Subgroup.mem_center_iff.mp hxZ) (⟨⟨D.t2, ht2M⟩, ht2E⟩ : ↥E'))
      rw [hcommE, mul_assoc, mul_inv_cancel, mul_one]
    have hsinv : (⟨D.t2, ht2M⟩ : ↥M) * x * (⟨D.t2, ht2M⟩ : ↥M)⁻¹ = x⁻¹ := by
      apply Subtype.ext
      show D.t2 * (x : G) * D.t2⁻¹ = (x : G)⁻¹
      have hxP0 : (x : G) ∈ (Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G) := by
        rw [hPdef, Subgroup.mem_subgroupOf] at hx; exact hx
      exact D.inv (x : G) hxP0.1
    have hxinv : x = x⁻¹ := by rw [← hsinv, hscen]
    have hxsq : x * x = 1 := by
      nth_rewrite 2 [hxinv]
      exact mul_inv_cancel x
    have hxord : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rwa [pow_two])
    have hxodd : Odd (orderOf x) := Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard O hxO)
    have hxone : orderOf x = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hxord with h | h
      · exact h
      · rw [h] at hxodd; exact absurd hxodd (by decide)
    exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hxone)
  -- assembly
  obtain ⟨eA⟩ := a7_of_dshape hFT hD hkey hEn hEq hne
  obtain ⟨_, _, _, ⟨eL⟩⟩ := LayerMapOddCoreIso M hFT hEn hEq
  obtain ⟨_, _, _, ⟨eM⟩⟩ := MapQuotientCenterIso (Work.GW2.layer ↥M) (Work.GW2.oddCore ↥M)
    hEn hEq (inf_oddCore_subgroupOf_le_center hFT hEq) hne
  exact ⟨eL.trans (eM.symm.trans eA)⟩

end Work.CORE3.A7V18
