import Mathlib
import Submission.NK.NUV2.LC.RouteB.cyclicClassColimAltDefs
import Submission.NK.NUV2.LC.RouteB.DictionaryDeps
import Submission.NK.NUV2.LC.RouteB.RouteBSetup
import Submission.NK.NUV2.LC.RouteB.locUnits_kummerLevel_eq_zero_of_locLevel_eq_zero
import Submission.NK.NUV2.LC.RouteB.survivalSetup
import Submission.NK.NUV2.LC.RouteB.unitsLevelMapTower_unitsTransport
import Submission.NK.NUV2.LC.RouteB.decompRestrict_bij
import Submission.NK.BrauerHasse.exists_heightOneSpectrum_eq_comap
import Submission.NK.ReconstructField.ncard_primesOver_levelPrimeMapGen
import Submission.NK.GlobalCFT.Galois.globalCFT_place_smul_liesOver

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

namespace NK.NUV2.LC.RouteB

open CategoryTheory

/-- The "easy" direction of the local invariant formula, needed for the localisation dictionary of
`NK.NUV2.LC.RouteB.cyclicClassColimAlt`: if the localisation at the place `A` of the
cyclic-algebra class `X b = muToH2 (Y b)` vanishes, then `b` is a local norm at the prime `v` of `F`
below `A`.

The avatar is *given by the hypotheses*: `γ` is the units avatar with the visible level-`E`
representative `(unitsTransport ⟨E⟩).symm (cycClassOf g hg b)` (the explicit-cocycle cyclic class of
the global element `b`), and `Y` is its `μ_p`-avatar (`kummerColim (Y b) = γ b`).  No
`Classical.choice` of a transport occurs, so the class is a concrete term and the proved local
criterion applies to it.

The sibling file `Submission/Work/NUV2/LC/RouteB/loc_eq_zero_imp_mem_localNormPreimage.lean` states
the same result in the `γ`/`Y`-parametrised form, but its module does **not** build: it refers to
the identifier `NK.NUV2.ABHN.levelCompare`, which exists nowhere in its (clash-free) import
closure.  The levelwise comparison of `NK.HassePrinciple.MuLevelH2 p V L` with
`NK.BrauerHasse.LevelH2 p V L` that is actually available, namely
`Submission/Work/NUV2/ABHN/muColimEquivH2ProfiniteOfIsPrimitiveRoot.lean`, is called
`NK.NUV2.ABHN.levelCompareRoot`, and its naturality for the transition maps is
`NK.NUV2.ABHN.levelCompare_muLevelMap` (stated for `levelCompareRoot`).  The proof below is the
argument of that sibling file, carried out here with the correct identifiers, so that the result is
available without editing another agent's module.

Route (as implemented below).

* `X b = muToH2 (Y b)` is represented at some finite level `L₁`; enlarge it to `L = L₁ ⊔ ⟨E⟩` so
  that both the `μ_p`-class and the level-`⟨E⟩` units class are visible there.
* `NK.NUV2.ABHN.muToH2_ofLevel` and `NK.BrauerHasse.H2Profinite.loc_ofLevel_apply` rewrite the
  vanishing of `loc` as the vanishing of the *level* local restriction of
  `levelCompareRoot p hζ ⊤ L xL`, and `NK.HassePrinciple.LocalH2.ofLevel_eq_zero_iff` inflates it
  to a level `M ⊇ L` (`NK.BrauerHasse.levelMap_locLevel_apply` and
  `NK.NUV2.ABHN.levelCompare_muLevelMap` handle the transition of the comparison with the level
  maps).
* The Kummer image of `xM` is the inflation of the level-`⟨E⟩` units class `cls'` (this is exactly
  `NK.HassePrinciple.kummerColim_ofLevel` + `hY` + `hγ`), so after `NK.BrauerTwist.LevelSystem.ofLevel_eq_iff`
  there is a common level `N ⊇ M, ⟨E⟩` on which the two units classes agree
  (`NK.HassePrinciple.kummerLevel_naturality`).
* `NK.NUV2.LC.RouteB.locUnits_kummerLevel_eq_zero_of_locLevel_eq_zero` — the *proved* Kummer
  square converting the vanishing of the local `μ_p` restriction at level `N` into the vanishing of
  `locUnits` of the Kummer image at the prime `qN` of `↥N` cut out by `A`
  (`NK.BrauerHasse.exists_heightOneSpectrum_eq_comap`) — gives the vanishing at level `N`, and
  `NK.NUV2.LC.RouteB.locUnits_eq_zero_iff_unitsLevelMapTower` transports it down to the
  level-`⟨E⟩` explicit cocycle class `cycClassOf g hg b`.
* Finally the *proved* local criterion for the explicit-cocycle class,
  `NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite`, gives
  `localImageAt (ofFinite v) b ∈ localNormSubgroup (ofFinite v)`, and
  `NK.CFTLib.mem_localNormPreimage` (`Iff.rfl`) finishes.

The extra hypotheses `hodd` and `hdeg` of the statement are not used by this direction; `hcyc` is
used only to supply the `IsCyclic` instance.  All imports are clash-free: in particular neither
`Submission/Work/NUV2/ABHN/h2Twist_muColim_equiv.lean` nor
`Submission/Work/NUV2/ABHN/muLevelCompareOfIsPrimitiveRoot.lean` (or any module importing them,
e.g. `Submission/Work/NUV2/LC/RouteB/ccmResAux.lean`) occurs in the import closure. (ofFinite v)` by construction of the latter as a supremum, `NK.CFTLib.mem_localNormPreimage`
finishes. -/
theorem cyclicClassMap_loc_eq_zero_imp_mem_localNormPreimage_c
    (p : ℕ) (hp : p.Prime) (hodd : p ≠ 2) [NeZero p]
    (F : Type) [Field F] [NumberField F] (F' : Type) [Field F'] [Algebra F F']
    [IsSepClosure F F'] (ζ : F) (hζ : IsPrimitiveRoot ζ p)
    (E : IntermediateField F F') [FiniteDimensional F E] [IsGalois F E] [NumberField ↥E]
    (hdeg : Module.finrank F E = p) (hcyc : IsCyclic (↥E ≃ₐ[F] ↥E))
    (g : ↥E ≃ₐ[F] ↥E) (hg : ∀ σ : ↥E ≃ₐ[F] ↥E, σ ∈ Subgroup.zpowers g)
    (γ : Fˣ → NK.HassePrinciple.H2Units (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)))
    (Y : Fˣ → NK.HassePrinciple.MuColim (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)))
    (hγ : ∀ b : Fˣ, NK.HassePrinciple.H2Units.ofLevel (K := F) (K' := F')
      (⊤ : Subgroup Gal(F'/F)) (⟨E⟩ : FiniteGaloisIntermediateField F F')
      ((NK.NUV2.LC.unitsTransport (K := F) (K' := F')
        (⟨E⟩ : FiniteGaloisIntermediateField F F')).symm
        (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := F) (F := ↥E) g hg b)) = γ b)
    (hY : ∀ b : Fˣ, NK.HassePrinciple.kummerColim (K := F) (K' := F') p
      (⊤ : Subgroup Gal(F'/F)) (Y b) = γ b)
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (A : NK.BrauerHasse.OverFinitePrime F F')
    (hA : A.1.comap (algebraMap F F') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime F v)
    (b : Fˣ) :
    NK.BrauerHasse.H2Profinite.loc p ⊤
        (NK.NUV2.ABHN.muToH2 (K := F) (K' := F') p hζ (Y b)) A = 0 →
      b ∈ NK.CFTLib.localNormPreimage (K := F) (L := ↥E)
        (NK.GlobalCFT.Place.ofFinite v) := by
  intro hb
  haveI hcycI : IsCyclic (↥E ≃ₐ[F] ↥E) := hcyc
  -- the level `L₀ = ⟨E⟩` and the class `cls'`
  let L₀ : FiniteGaloisIntermediateField F F' := ⟨E⟩
  let cls' : NK.HassePrinciple.UnitsLevelH2 (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)) L₀ :=
    (NK.NUV2.LC.unitsTransport (K := F) (K' := F') L₀).symm
      (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := F) (F := ↥E) g hg b)
  have hcls' : (NK.NUV2.LC.unitsTransport (K := F) (K' := F') L₀) cls'
      = NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := F) (F := ↥E) g hg b :=
    Equiv.apply_symm_apply _ _
  have hγb : NK.HassePrinciple.H2Units.ofLevel (K := F) (K' := F')
      (⊤ : Subgroup Gal(F'/F)) L₀ cls' = γ b := hγ b
  -- a level at which `Y b` is represented, above `L₀`
  obtain ⟨L₁, x₁, hx₁⟩ := NK.BrauerTwist.LevelSystem.ofLevel_surjective
    (S := NK.HassePrinciple.muLevelSystem (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F))) (Y b)
  let L : FiniteGaloisIntermediateField F F' := L₁ ⊔ L₀
  let xL : NK.HassePrinciple.MuLevelH2 (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)) L :=
    (NK.HassePrinciple.muLevelMap (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F))
      (le_sup_left : L₁ ≤ L₁ ⊔ L₀)).hom x₁
  have hxL : (NK.HassePrinciple.muLevelSystem (K := F) (K' := F') p
      (⊤ : Subgroup Gal(F'/F))).ofLevel L xL = Y b :=
    (NK.BrauerTwist.LevelSystem.ofLevel_map
      (S := NK.HassePrinciple.muLevelSystem (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)))
      (le_sup_left : L₁ ≤ L₁ ⊔ L₀) x₁).trans hx₁
  -- unfold the hypothesis
  have hloc : NK.BrauerHasse.LocalH2.ofLevel (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)) A.1 L
      (NK.BrauerHasse.locLevel (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)) A.1 L
        ((NK.NUV2.ABHN.levelCompareRoot (K := F) (K' := F') p hζ (⊤ : Subgroup Gal(F'/F)) L) xL)) = 0 := by
    have h1 : NK.BrauerHasse.H2Profinite.loc (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F))
        (NK.BrauerHasse.H2Profinite.ofLevel (K := F) (K' := F') L
          ((NK.NUV2.ABHN.levelCompareRoot (K := F) (K' := F') p hζ (⊤ : Subgroup Gal(F'/F)) L) xL)) A = 0 := by
      rw [← NK.NUV2.ABHN.muToH2_ofLevel (K := F) (K' := F') p hζ L xL, hxL]
      exact hb
    rwa [NK.BrauerHasse.H2Profinite.loc_ofLevel_apply] at h1
  obtain ⟨M, hLM, hM⟩ := (NK.HassePrinciple.LocalH2.ofLevel_eq_zero_iff (K := F) (K' := F')
    A.1 L _).mp hloc
  -- the fine vanishing at level `M`
  set xM : NK.HassePrinciple.MuLevelH2 (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)) M :=
    (NK.HassePrinciple.muLevelMap (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)) hLM).hom xL
  have hM' : NK.BrauerHasse.locLevel (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)) A.1 M
      ((NK.NUV2.ABHN.levelCompareRoot (K := F) (K' := F') p hζ (⊤ : Subgroup Gal(F'/F)) M) xM) = 0 := by
    rw [show (NK.NUV2.ABHN.levelCompareRoot (K := F) (K' := F') p hζ (⊤ : Subgroup Gal(F'/F)) M) xM
        = (NK.BrauerHasse.levelMap (K := F) (K' := F') p (U := ⊤) hLM)
          ((NK.NUV2.ABHN.levelCompareRoot (K := F) (K' := F') p hζ (⊤ : Subgroup Gal(F'/F)) L) xL)
        from NK.NUV2.ABHN.levelCompare_muLevelMap (K := F) (K' := F') p hζ (⊤ : Subgroup Gal(F'/F)) hLM xL]
    rw [NK.BrauerHasse.levelMap_locLevel_apply]
    exact hM
  -- the avatar level
  have hava : NK.HassePrinciple.H2Units.ofLevel (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)) M
        ((NK.HassePrinciple.kummerLevel (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)) M).hom xM)
      = NK.HassePrinciple.H2Units.ofLevel (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)) L₀ cls' := by
    rw [← NK.HassePrinciple.kummerColim_ofLevel (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)) M xM]
    have hofM : NK.HassePrinciple.MuColim.ofLevel (K := F) (K' := F') p
        (⊤ : Subgroup Gal(F'/F)) M xM = Y b := by
      show (NK.HassePrinciple.muLevelSystem (K := F) (K' := F') p
        (⊤ : Subgroup Gal(F'/F))).ofLevel M xM = Y b
      rw [show xM = (NK.HassePrinciple.muLevelSystem (K := F) (K' := F') p
          (⊤ : Subgroup Gal(F'/F))).map hLM xL from rfl]
      exact (NK.BrauerTwist.LevelSystem.ofLevel_map
        (S := NK.HassePrinciple.muLevelSystem (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)))
        hLM xL).trans hxL
    rw [hofM, hY b, ← hγb]
  obtain ⟨N, hMN, hL₀N, havatars⟩ := (NK.BrauerTwist.LevelSystem.ofLevel_eq_iff
    (S := NK.HassePrinciple.unitsLevelSystem (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F)))
    ((NK.HassePrinciple.kummerLevel (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)) M).hom xM)
    cls').mp hava
  have havaU : (NK.HassePrinciple.unitsLevelMap (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F))
        ((FiniteGaloisIntermediateField.le_iff M N).mp hMN)).hom
        ((NK.HassePrinciple.kummerLevel (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)) M).hom xM)
      = (NK.HassePrinciple.unitsLevelMap (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F))
        ((FiniteGaloisIntermediateField.le_iff L₀ N).mp hL₀N)).hom cls' := havatars
  set xN : NK.HassePrinciple.MuLevelH2 (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)) N :=
    (NK.HassePrinciple.muLevelMap (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)) hMN).hom xM
  have hN' : NK.BrauerHasse.locLevel (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)) A.1 N
      ((NK.NUV2.ABHN.levelCompareRoot (K := F) (K' := F') p hζ (⊤ : Subgroup Gal(F'/F)) N) xN) = 0 := by
    rw [show (NK.NUV2.ABHN.levelCompareRoot (K := F) (K' := F') p hζ (⊤ : Subgroup Gal(F'/F)) N) xN
        = (NK.BrauerHasse.levelMap (K := F) (K' := F') p (U := ⊤) hMN)
          ((NK.NUV2.ABHN.levelCompareRoot (K := F) (K' := F') p hζ (⊤ : Subgroup Gal(F'/F)) M) xM)
        from NK.NUV2.ABHN.levelCompare_muLevelMap (K := F) (K' := F') p hζ (⊤ : Subgroup Gal(F'/F)) hMN xM]
    rw [NK.BrauerHasse.levelMap_locLevel_apply]
    rw [hM']
    exact map_zero (ConcreteCategory.hom (NK.BrauerHasse.localLevelMap (K := F) (K' := F')
      p (⊤ : Subgroup Gal(F'/F)) A.1 hMN))
  -- the units avatar identity at `N`
  have hkumN : (NK.HassePrinciple.kummerLevel (K := F) (K' := F') p
        (⊤ : Subgroup Gal(F'/F)) N).hom xN
      = (NK.HassePrinciple.unitsLevelMap (K := F) (K' := F') (⊤ : Subgroup Gal(F'/F))
          ((FiniteGaloisIntermediateField.le_iff M N).mp hMN)).hom
          ((NK.HassePrinciple.kummerLevel (K := F) (K' := F') p
            (⊤ : Subgroup Gal(F'/F)) M).hom xM) := by
    have hnat := congrArg (fun (k : NK.HassePrinciple.MuLevelH2 (K := F) (K' := F') p
        (⊤ : Subgroup Gal(F'/F)) M ⟶ NK.HassePrinciple.UnitsLevelH2 (K := F) (K' := F')
        (⊤ : Subgroup Gal(F'/F)) N) => k.hom xM)
      (NK.HassePrinciple.kummerLevel_naturality (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F))
        ((FiniteGaloisIntermediateField.le_iff M N).mp hMN))
    simp only [ModuleCat.comp_apply] at hnat
    exact hnat.symm
  -- the prime `qN` of `↥N` below `A`
  have hneN : A.1.comap (algebraMap ↥(N : IntermediateField F F') F') ≠ ⊤ := by
    intro h
    have hcomp : A.1.comap (algebraMap F F')
        = (A.1.comap (algebraMap ↥(N : IntermediateField F F') F')).comap
          (algebraMap F ↥(N : IntermediateField F F')) :=
      (congrArg (fun (φ : F →+* F') => A.1.comap φ)
        (IsScalarTower.algebraMap_eq F ↥(N : IntermediateField F F') F')).trans
      (ValuationSubring.comap_comap (A := A.1) (g := algebraMap ↥(N : IntermediateField F F') F')
        (algebraMap F ↥(N : IntermediateField F F'))).symm
    exact A.2 (hcomp.trans (by rw [h]; ext x; simp [ValuationSubring.mem_comap]))
  obtain ⟨qN, hqN⟩ := NK.BrauerHasse.exists_heightOneSpectrum_eq_comap
    (K := ↥(N : IntermediateField F F')) (K' := F') A.1 hneN
  -- apply the imported crux
  have hmain := NK.NUV2.LC.RouteB.locUnits_kummerLevel_eq_zero_of_locLevel_eq_zero
    (K := F) (K' := F') p hp ζ hζ N xN A qN hqN hN'
  rw [show (NK.NUV2.LC.RouteB.unitsTransportK (K := F) (K' := F') N)
        ((NK.HassePrinciple.kummerLevel (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)) N).hom xN)
      = (NK.NUV2.LC.unitsTransport (K := F) (K' := F') N)
        ((NK.HassePrinciple.kummerLevel (K := F) (K' := F') p (⊤ : Subgroup Gal(F'/F)) N).hom xN)
      from rfl] at hmain
  rw [hkumN, havaU] at hmain
  -- the prime `q₀` of `↥E` below `A`
  have hneL₀ : A.1.comap (algebraMap ↥(L₀ : IntermediateField F F') F') ≠ ⊤ := by
    intro h
    have hcomp : A.1.comap (algebraMap F F')
        = (A.1.comap (algebraMap ↥(L₀ : IntermediateField F F') F')).comap
          (algebraMap F ↥(L₀ : IntermediateField F F')) :=
      (congrArg (fun (φ : F →+* F') => A.1.comap φ)
        (IsScalarTower.algebraMap_eq F ↥(L₀ : IntermediateField F F') F')).trans
      (ValuationSubring.comap_comap (A := A.1) (g := algebraMap ↥(L₀ : IntermediateField F F') F')
        (algebraMap F ↥(L₀ : IntermediateField F F'))).symm
    exact A.2 (hcomp.trans (by rw [h]; ext x; simp [ValuationSubring.mem_comap]))
  obtain ⟨q₀, hq₀⟩ := NK.BrauerHasse.exists_heightOneSpectrum_eq_comap
    (K := ↥(L₀ : IntermediateField F F')) (K' := F') A.1 hneL₀
  -- the tower instances
  letI : Algebra ↥(L₀ : IntermediateField F F') ↥(N : IntermediateField F F') :=
    (IntermediateField.inclusion ((FiniteGaloisIntermediateField.le_iff L₀ N).mp hL₀N)).toAlgebra
  haveI hST : IsScalarTower F ↥(L₀ : IntermediateField F F') ↥(N : IntermediateField F F') :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      ext
      exact (IntermediateField.coe_inclusion _ (algebraMap F ↥(L₀ : IntermediateField F F') x)).symm)
  -- the `IsScalarTower` into `F'`
  haveI hST2 : IsScalarTower ↥(L₀ : IntermediateField F F') ↥(N : IntermediateField F F') F' := by
    refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
    exact (IntermediateField.coe_inclusion ((FiniteGaloisIntermediateField.le_iff L₀ N).mp hL₀N) x).symm
  -- the `LiesOver` at the ideal and place level
  have hIdeal : qN.asIdeal.LiesOver q₀.asIdeal :=
    NK.ReconstructField.liesOver_of_comap_eq_valRing (K := ↥(L₀ : IntermediateField F F'))
      (L := ↥(N : IntermediateField F F')) (K' := F') q₀ qN A.1 hqN hq₀
  have hLiesOver : (NK.GlobalCFT.Place.ofFinite qN).LiesOver (NK.GlobalCFT.Place.ofFinite q₀) :=
    (NK.GlobalCFT.Galois.globalCFT_liesOver_ofFinite_iff qN q₀).mpr hIdeal
  -- the level-N statement in terms of the tower level map
  have hmain' : (NK.HassePrinciple.locUnits F ↥(N : IntermediateField F F')
      (NK.GlobalCFT.Place.ofFinite qN)).hom
      ((NK.NUV2.LC.unitsLevelMapTower (F := F) (L := ↥(L₀ : IntermediateField F F'))
        (M := ↥(N : IntermediateField F F')))
        (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := F) (F := ↥E) g hg b)) = 0 := by
    rw [← hcls']
    rw [NK.NUV2.LC.RouteB.unitsLevelMapTower_unitsTransport (F := F) L₀ N hL₀N
      (fun x => rfl) cls']
    exact hmain
  have hind : (NK.HassePrinciple.locUnits F ↥(L₀ : IntermediateField F F')
      (NK.GlobalCFT.Place.ofFinite q₀)).hom
      (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := F) (F := ↥E) g hg b) = 0 :=
    (NK.NUV2.LC.RouteB.locUnits_eq_zero_iff_unitsLevelMapTower (F := F)
      (L := ↥(L₀ : IntermediateField F F')) (M := ↥(N : IntermediateField F F'))
      (NK.CFTLib.IdeleHasse.Descent.cycClassOf (K := F) (F := ↥E) g hg b) hLiesOver).mpr hmain'
  -- the local norm criterion
  have hlies : q₀.asIdeal.LiesOver v.asIdeal :=
    NK.ReconstructField.liesOver_of_comap_eq_valRing (K := F) (L := ↥E) (K' := F')
      v q₀ A.1 hq₀ hA
  have hcrit : NK.CFTLib.IdeleHasse.localImageAt (K := F)
        (NK.GlobalCFT.Place.ofFinite v) b
      ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := F) (L := ↥E)
        (NK.GlobalCFT.Place.ofFinite v) :=
    (NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite
      (K := F) (F := ↥E) g hg v q₀ hlies b).mp hind
  have hbridge : NK.CFTLib.IdeleHasse.localImageAt (K := F)
      (NK.GlobalCFT.Place.ofFinite v) b
      = NK.CFTLib.localImageHom (K := F) (NK.GlobalCFT.Place.ofFinite v) b := rfl
  rw [hbridge] at hcrit
  exact (NK.CFTLib.mem_localNormPreimage (K := F) (L := ↥E)
    (v := NK.GlobalCFT.Place.ofFinite v) (x := b)).mpr hcrit

end NK.NUV2.LC.RouteB
