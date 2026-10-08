import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.MData.BcInfMLeOddCore
import Submission.Work.CORE3.MData.OddCentralizerLayerAux
import Submission.Work.CORE3.MDataAux
import Submission.Work.CORE2A.centralizer_map_quotient_eq_bot
import Submission.Work.CORE2A.dihOrCycSylow_subgroup

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.CORE3.MData

/-- Bender 1981 §3, p. 223 (the `M`-analysis of the subcase `Ĥ = H`): for a maximal `M`
containing `N_G(P₂)` there is a surjection `M ↠ A₇` whose kernel is the centralizer in `M` of
the layer `E(M) = layer ↥M`, that is `M / C_M(E(M)) ≅ A₇`.

The proof is the one already carried out inside `Work.CORE3.MData.BcInfMLeOddCore`
(its lines 174–220): put `E = layer ↥M`, `C = C_M(E)` (normal of odd order by
`Work.CORE3.MData.OddCentralizerLayerAux`), `Q = M/C`; the image `L ≤ Q` of `E` is normal with
trivial centralizer (`Work.CORE2A.centralizer_map_quotient_eq_bot`) and `L ≅ E/Z(E) ≅ A₇`
(`Work.CORE3.MData.ImageQuotientCentralizerIso` plus the `hA7` component `E(M)/Z ≅ A₇`), and `Q`
has cyclic-or-dihedral Sylow 2-subgroups because it is a quotient of the D-group `M`
(`Work.CORE2A.dihOrCycSylow_subgroup`, `Work.DSTR.dihOrCycHered`).  Bender's `AutA7Prop`,
available as the toolkit field `I.T.autA7`, then gives `L = ⊤`, i.e. `Q ≅ A₇`.  Composing the
quotient map `M → Q` with that isomorphism gives `f`, and `f.ker = C` by construction. -/
theorem LayerSurjA7Surj (I : Work.CORE3.Case1Inputs) (hSetup : Work.GW2.Case1aSetupProp)
    (hFr : Work.GW2.Case1aFrattiniProp) (hAb : Work.GW2.Case1aAbelianProp)
    (hA7 : Work.GW2.Case1aA7Prop) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G, Work.GW2.Case1 B → B.Hhat = B.H →
      ∀ D : Work.GW2.Case1aData B, ∀ P2 M : Subgroup G,
      P2 ≤ B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) → IsPGroup D.p P2 →
      ¬ D.p ∣ P2.relIndex (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) →
      IsCoatom M → Subgroup.normalizer (P2 : Set G) ≤ M →
      ∃ f : ↥M →* alternatingGroup (Fin 7), Function.Surjective f ∧
        f.ker = Subgroup.centralizer (((Work.GW2.layer ↥M : Subgroup ↥M)) : Set ↥M) := by
  intro G _instG _finG hFT hCtx B hCase hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  classical
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
  -- ## Step 3: `|M|₂ = 2³`
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
  -- ## Assembly: compose the quotient map `M → M/C` with `M/C ≅ A₇`
  obtain ⟨e⟩ := hisoQ
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' C), ?_, ?_⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective C)
  · rw [MonoidHom.ker_comp_of_injective (QuotientGroup.mk' C) e.toMonoidHom e.injective,
      QuotientGroup.ker_mk']

end Work.CORE3.MData
