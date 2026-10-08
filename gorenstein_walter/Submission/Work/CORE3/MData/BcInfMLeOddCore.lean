import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.MDataAux
import Submission.Work.CORE3.MData.A7SylowCentralizerIsPGroup
import Submission.Work.CORE3.MData.OddCentralizerLayerAux
import Submission.Work.CORE2A.centralizer_map_quotient_eq_bot
import Submission.Work.CORE2A.dihOrCycSylow_subgroup
import Submission.Work.CORE2A.inf_centralizer_eq_center_map
import Submission.Work.CORE2A.le_oddCoreIn_of_normal_of_odd
import Submission.Work.DSTR.dihOrCycHered
import Submission.Work.DSTR.dihedralSubgroup
import Submission.Work.DSTR.dihedralQuotient
import Submission.Work.DSTR.map_centralizer_eq_bot_and_equiv

/-!
# CORE3 (`MData`): `B ∩ M ≤ O(M)` in the subcase `Ĥ = H`

Deliverable `Work.CORE3.MData.BcInfMLeOddCore` (Bender 1981, §3, p. 223, the display
`B ∩ M = O(M)` for `B = C_U(S)`).

## Strategy

`X := B ∩ M = (B.U ⊓ C_G(B.S)) ⊓ M` is an odd-order subgroup of `M` centralizing `B.S`, and
`B.S ≤ M` is a Sylow 2-subgroup of `M` (a Sylow 2-subgroup of `G` contained in `M`).
The whole content is

> an odd-order subgroup of `M` centralizing a Sylow 2-subgroup of `M` lies in `O(M)`.

Let `E := layer ↥M = E(M)` be the layer of the D-group `M`, quasisimple with odd centre and
`E/Z(E) ≅ A₇` (the §3 subcase).  Put `C := C_M(E)` and `Q := M/C`; the image `L` of `E` in `Q` is
normal with **trivial centralizer** (`Work.CORE2A.centralizer_map_quotient_eq_bot`, using that `C`
is odd), and `L ≅ E/Z(E) ≅ A₇` (`Work.DSTR.map_centralizer_eq_bot_and_equiv`).  Bender's
`AutA7Prop` then forces `L = Q`, so `Q ≅ A₇`.  The image `S̄` of a Sylow 2-subgroup of `M` in `Q`
is a Sylow 2-subgroup of `A₇`, and the centralizer of a Sylow 2-subgroup of `A₇` is a 2-group, so
an odd subgroup of `C_Q(S̄)` is trivial.  Hence `X` maps into `C_M(E)`, i.e.
`X ≤ C_M(E) ≤ O(M)` (the latter because `C_M(E)` is normal of odd order).
-/

open Subgroup

namespace Work.CORE3.MData

/-! ## Generic auxiliary isomorphisms -/

/-- **The quotient by the centre is compatible with `Subgroup.map` along an injective
homomorphism.**  `E/Z(E) ≅ (E.map f)/Z(E.map f)`. -/
theorem QuotientCenterMapIso {G N : Type} [Group G] [Group N] (f : G →* N)
    (hf : Function.Injective f) (E : Subgroup G) :
    Nonempty ((↥E ⧸ Subgroup.center ↥E) ≃*
      (↥(Subgroup.map f E) ⧸ Subgroup.center ↥(Subgroup.map f E))) := by
  let e : ↥E ≃* ↥(Subgroup.map f E) := Subgroup.equivMapOfInjective E f hf
  let g : ↥E →* (↥(Subgroup.map f E) ⧸ Subgroup.center ↥(Subgroup.map f E)) :=
    (QuotientGroup.mk' (Subgroup.center ↥(Subgroup.map f E))).comp e.toMonoidHom
  have hker : g.ker = Subgroup.center ↥E := by
    ext x
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk' (Subgroup.center ↥(Subgroup.map f E))) (e x) = 1 ↔
      x ∈ Subgroup.center ↥E
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff,
      Subgroup.mem_center_iff]
    constructor
    · intro h y
      have h' : e (y * x) = e (x * y) := by
        rw [map_mul, map_mul]
        exact h (e y)
      exact e.injective h'
    · intro h y
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp y.2
      have hy : y = e ⟨z, hz⟩ := by
        apply Subtype.ext
        show (y : N) = f z
        rw [hzy]
      rw [hy]
      show e ⟨z, hz⟩ * e x = e x * e ⟨z, hz⟩
      rw [← map_mul, ← map_mul, h ⟨z, hz⟩]
  have hg : Function.Surjective g :=
    (QuotientGroup.mk'_surjective _).comp e.surjective
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)⟩

/-- **The image of a perfect normal subgroup `E` in `K ⧸ C_K(E)` is `E/Z(E)`.**
The natural map `↥E →* K ⧸ C_K(E)` has kernel `Z(E)` and image `E` (mod `C_K(E)`). -/
theorem ImageQuotientCentralizerIso {K : Type} [Group K] [Finite K] (E : Subgroup K)
    (hEn : E.Normal) (hperf : ⁅E, E⁆ = E) :
    Nonempty ((Subgroup.map (QuotientGroup.mk' (Subgroup.centralizer (E : Set K))) E) ≃*
      (↥E ⧸ Subgroup.center ↥E)) := by
  haveI : E.Normal := hEn
  let C : Subgroup K := Subgroup.centralizer (E : Set K)
  haveI : C.Normal := inferInstance
  let g : ↥E →* (K ⧸ C) := (QuotientGroup.mk' C).comp E.subtype
  have hker : g.ker = Subgroup.center ↥E := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    show (QuotientGroup.mk' C) (x : K) = 1 ↔ ∀ y : ↥E, y * x = x * y
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    have hinf : C ⊓ E = (Subgroup.center ↥E).map E.subtype := by
      rw [inf_comm]; exact Work.CORE2A.inf_centralizer_eq_center_map E
    constructor
    · intro hx y
      have hx' : (↑x : K) ∈ C ⊓ E := ⟨hx, x.2⟩
      rw [hinf] at hx'
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx'
      have hxz : z = x := E.subtype_injective hzx
      subst hxz
      exact Subgroup.mem_center_iff.mp hz y
    · intro hx
      have hx' : (↑x : K) ∈ (Subgroup.center ↥E).map E.subtype :=
        Subgroup.mem_map.mpr ⟨x, Subgroup.mem_center_iff.mpr hx, rfl⟩
      exact (hinf ▸ hx').1
  have hrange : g.range = Subgroup.map (QuotientGroup.mk' C) E := by
    refine Subgroup.ext fun q => ?_
    rw [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : K), x.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange g).trans (MulEquiv.subgroupCongr hrange))).symm⟩

/-! ## Odd subgroups centralizing a Sylow 2-subgroup of `A₇` are trivial -/

/-- **Odd subgroups centralizing a Sylow 2-subgroup of `A₇` are trivial.** -/
theorem odd_subgroup_centralizer_sylow_a7 (h7 : Work.GW2.A7ModelProp) {Q : Type} [Group Q]
    [Finite Q] (hiso : Nonempty (Q ≃* alternatingGroup (Fin 7))) (S : Sylow 2 Q) :
    ∀ X : Subgroup Q, X ≤ Subgroup.centralizer ((S : Subgroup Q) : Set Q) →
      Odd (Nat.card X) → X = ⊥ := by
  intro X hX hodd
  obtain ⟨e⟩ := hiso
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 (alternatingGroup (Fin 7)) :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective S
  have hS'map : (S' : Subgroup (alternatingGroup (Fin 7))) =
      (S : Subgroup Q).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective S
  have hS' : ((S' : Subgroup (alternatingGroup (Fin 7))) : Set (alternatingGroup (Fin 7))) =
      e.toMonoidHom '' ((S : Subgroup Q) : Set Q) := by
    rw [hS'map, Subgroup.coe_map]
  have hX' : Subgroup.map e.toMonoidHom X ≤
      Subgroup.centralizer ((S' : Subgroup (alternatingGroup (Fin 7))) : Set _) := by
    have h1 : Subgroup.map e.toMonoidHom X ≤
        Subgroup.centralizer (e.toMonoidHom '' ((S : Subgroup Q) : Set Q)) :=
      (Subgroup.map_mono hX).trans (Subgroup.map_centralizer_le_centralizer_image _ _)
    rw [← hS'] at h1
    exact h1
  have hpg : IsPGroup 2 ↥(Subgroup.map e.toMonoidHom X) :=
    (A7SylowCentralizerIsPGroup h7 S').to_le hX'
  have hcard : Nat.card ↥(Subgroup.map e.toMonoidHom X) = Nat.card ↥X :=
    Subgroup.card_map_of_injective e.injective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
  have h2k : Nat.card ↥X = 2 ^ k := by rw [← hcard, hk]
  have hodd' : Odd (2 ^ k) := by rw [← h2k]; exact hodd
  have hk0 : k = 0 := by
    by_contra hkne
    exact Nat.not_even_iff_odd.mpr hodd' (even_iff_two_dvd.mpr (dvd_pow_self 2 hkne))
  subst hk0
  rw [pow_zero] at h2k
  exact Subgroup.card_eq_one.mp h2k

/-! ## The main theorem -/

theorem BcInfMLeOddCore (I : Work.CORE3.Case1Inputs) (hSetup : Work.GW2.Case1aSetupProp)
    (hFr : Work.GW2.Case1aFrattiniProp) (hAb : Work.GW2.Case1aAbelianProp)
    (hA7 : Work.GW2.Case1aA7Prop) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case1 B → B.Hhat = B.H → ∀ D : Work.GW2.Case1aData B,
      ∀ P2 M : Subgroup G,
      P2 ≤ B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) → IsPGroup D.p P2 →
      ¬ D.p ∣ P2.relIndex (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) →
      IsCoatom M → Subgroup.normalizer (P2 : Set G) ≤ M →
      (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) ⊓ M ≤ Work.GW2.oddCoreIn M := by
  intro G _instG _finG hFT hCtx B hCase hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  classical
  haveI : IsSimpleGroup G := hCtx.simple
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- ## Step 1: the `A₇`-data of the §3 `M`-analysis
  obtain ⟨hSleM, hV2le, hEiso, hScard, _hP0card⟩ :=
    hA7 G hFT hCtx B hCase hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  -- ## Step 2: the layer of `M` is quasisimple with odd centre
  have ht_mem : B.t ∈ Work.GW2.layerIn M :=
    hV2le (Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t))
  have hlayerIn_ne : Work.GW2.layerIn M ≠ ⊥ := fun hbot =>
    Work.CORE2A.bSetup_t_ne_one B (Subgroup.mem_bot.mp (hbot ▸ ht_mem))
  have hlayer_ne : Work.GW2.layer ↥M ≠ ⊥ := fun hbot =>
    hlayerIn_ne (by rw [Work.GW2.layerIn, hbot, Subgroup.map_bot])
  obtain ⟨hEq, hZodd⟩ := Work.CORE3.mdata_layer_quasisimple I hCtx B hMcoat hlayer_ne
  have hEn : (Work.GW2.layer ↥M).Normal := Work.CORE3.mdata_layer_normal M
  -- ## Step 3: `B.S` is a Sylow 2-subgroup of `M`, and `|M|₂ = 8`
  let SM : Sylow 2 ↥M := Sylow.subtype B.S hSleM
  have hSMcoe : (SM : Subgroup ↥M) = ((B.S : Subgroup G)).subgroupOf M :=
    Sylow.coe_subtype B.S hSleM
  have hSMcard : Nat.card ↥(SM : Subgroup ↥M) = 8 := by
    rw [hSMcoe]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSleM).toEquiv, hScard]
  have h2M : (Nat.card ↥M).factorization 2 = 3 := by
    have h := Sylow.card_eq_multiplicity SM
    rw [hSMcard] at h
    have h' : 2 ^ ((Nat.card ↥M).factorization 2) = 2 ^ 3 := by rw [← h]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h'
  -- ## Step 4: `E/Z(E) ≅ A₇`
  have hisoE : Nonempty ((↥(Work.GW2.layer ↥M) ⧸ Subgroup.center ↥(Work.GW2.layer ↥M)) ≃*
      alternatingGroup (Fin 7)) := by
    obtain ⟨e⟩ := hEiso
    exact ⟨(QuotientCenterMapIso M.subtype M.subtype_injective (Work.GW2.layer ↥M)).some.trans e⟩
  -- ## Step 5: `C = C_M(E)` is normal of odd order
  have hCodd : Odd (Nat.card ↥(Subgroup.centralizer
      ((Work.GW2.layer ↥M : Subgroup ↥M) : Set ↥M))) :=
    OddCentralizerLayerAux M hEq hZodd h2M hisoE
  set C : Subgroup ↥M := Subgroup.centralizer ((Work.GW2.layer ↥M : Subgroup ↥M) : Set ↥M)
    with hCdef
  haveI : C.Normal := by rw [hCdef]; infer_instance
  -- ## Step 6: in `Q = M/C`, the image `L` of `E` is normal with trivial centralizer
  set L : Subgroup (↥M ⧸ C) := (Work.GW2.layer ↥M).map (QuotientGroup.mk' C) with hLdef
  have hCQ : Subgroup.centralizer (L : Set (↥M ⧸ C)) = ⊥ :=
    Work.CORE2A.centralizer_map_quotient_eq_bot (Work.GW2.layer ↥M) C rfl hEq.1 hFT hCodd
  have hisoL : Nonempty (L ≃* alternatingGroup (Fin 7)) := by
    obtain ⟨e⟩ := hisoE
    exact ⟨(ImageQuotientCentralizerIso (Work.GW2.layer ↥M) hEn hEq.1).some.trans e⟩
  have hLnorm : L.Normal := QuotientGroup.map_normal C (Work.GW2.layer ↥M)
  -- ## Step 7: `Q` is a D-group quotient, so Bender's `AutA7Prop` forces `Q = L ≅ A₇`
  have hdihM : Work.GW2.DihOrCycSylow ↥M := Work.CORE2A.dihOrCycSylow_subgroup hCtx.sylow M
  have hdihQ : Work.GW2.DihOrCycSylow (↥M ⧸ C) :=
    (Work.DSTR.dihOrCycHered Work.DSTR.dihedralSubgroup Work.DSTR.dihedralQuotient
      ↥M hdihM).2 C
  have hLtop : L = ⊤ := I.T.autA7 (↥M ⧸ C) L hLnorm hisoL hCQ hdihQ
  have hisoQ : Nonempty ((↥M ⧸ C) ≃* alternatingGroup (Fin 7)) := by
    obtain ⟨e⟩ := hisoL
    exact ⟨(Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hLtop.symm)).trans e⟩
  -- ## Step 8: the image of a Sylow 2-subgroup of `M` in `Q` is a Sylow 2-subgroup of `Q`
  let Sbar : Sylow 2 (↥M ⧸ C) := Sylow.mapSurjective (QuotientGroup.mk'_surjective C) SM
  have hSbarcoe : (Sbar : Subgroup (↥M ⧸ C)) =
      (SM : Subgroup ↥M).map (QuotientGroup.mk' C) := Sylow.coe_mapSurjective _ SM
  -- ## Step 9: `X = B ∩ M` is odd and centralizes `B.S`
  set Bc : Subgroup G := B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) with hBcdef
  have hBcodd : Odd (Nat.card ↥Bc) := Work.CORE3.MdataB_odd B
  have hXM : Bc ⊓ M ≤ M := inf_le_right
  have hXodd : Odd (Nat.card ↥(Bc ⊓ M)) :=
    Odd.of_dvd_nat hBcodd (Subgroup.card_dvd_of_le inf_le_left)
  set X₁ : Subgroup ↥M := (Bc ⊓ M).subgroupOf M with hX1def
  have hX1card : Nat.card ↥X₁ = Nat.card ↥(Bc ⊓ M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv
  have hX1cen : X₁ ≤ Subgroup.centralizer ((SM : Subgroup ↥M) : Set ↥M) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hxB : (x : G) ∈ Bc ⊓ M := Subgroup.mem_subgroupOf.mp hx
    have hyS : (y : G) ∈ (B.S : Subgroup G) := by
      have hy' : y ∈ (SM : Subgroup ↥M) := hy
      rw [hSMcoe] at hy'
      exact Subgroup.mem_subgroupOf.mp hy'
    exact Subtype.ext (by
      show (y : G) * (x : G) = (x : G) * (y : G)
      exact Subgroup.mem_centralizer_iff.mp hxB.1.2 (y : G) hyS)
  have hX1C : X₁.map (QuotientGroup.mk' C) ≤
      Subgroup.centralizer ((Sbar : Subgroup (↥M ⧸ C)) : Set (↥M ⧸ C)) := by
    have h1 : X₁.map (QuotientGroup.mk' C) ≤
        Subgroup.centralizer ((QuotientGroup.mk' C) '' ((SM : Subgroup ↥M) : Set ↥M)) :=
      (Subgroup.map_mono hX1cen).trans (Subgroup.map_centralizer_le_centralizer_image _ _)
    have h2 : ((QuotientGroup.mk' C) '' ((SM : Subgroup ↥M) : Set ↥M)) =
        ((Sbar : Subgroup (↥M ⧸ C)) : Set (↥M ⧸ C)) := by
      rw [← Subgroup.coe_map, hSbarcoe]
    rwa [h2] at h1
  have hX1odd : Odd (Nat.card ↥(X₁.map (QuotientGroup.mk' C))) := by
    have hX1o : Odd (Nat.card ↥X₁) := by rw [hX1card]; exact hXodd
    exact Odd.of_dvd_nat hX1o (Subgroup.card_map_dvd X₁ (QuotientGroup.mk' C))
  -- ## Step 10: the image of `B ∩ M` in `Q` is trivial
  have hXbar : X₁.map (QuotientGroup.mk' C) = ⊥ :=
    odd_subgroup_centralizer_sylow_a7 I.T.a7 hisoQ Sbar _ hX1C hX1odd
  have hX1le : X₁ ≤ C := by
    have h := (Subgroup.map_eq_bot_iff X₁).mp hXbar
    rwa [QuotientGroup.ker_mk'] at h
  -- ## Step 11: `C ≤ O(M)`, hence `B ∩ M ≤ O(M)`
  have hCle : C ≤ Work.GW2.oddCore ↥M := by
    rw [Work.GW2.oddCore]
    exact Subgroup.normal_le_normalCore.mpr (le_sSup ⟨inferInstance, hCodd⟩)
  have hXle : Bc ⊓ M ≤ (Work.GW2.oddCore ↥M).map M.subtype := by
    have h2 : X₁.map M.subtype ≤ C.map M.subtype := Subgroup.map_mono hX1le
    rw [Subgroup.map_subgroupOf_eq_of_le hXM] at h2
    exact h2.trans (Subgroup.map_mono hCle)
  change Bc ⊓ M ≤ (Work.GW2.oddCore ↥M).map M.subtype
  exact hXle

end Work.CORE3.MData
