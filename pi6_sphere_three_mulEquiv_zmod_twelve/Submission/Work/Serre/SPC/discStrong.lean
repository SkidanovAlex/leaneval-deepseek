import Mathlib
import Submission.Work.Serre.SPC.cubeStrong
import Submission.Work.Serre.SPC.discDefs

set_option synthInstance.maxHeartbeats 400000


set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.SPC

noncomputable section

/-- **Strong form of `(P_D)` for the model cell.**  For a Serre fibration `p : E → B`, a map
`τ : D^{n+2} → B` and a fibre which is homologically `φ`-connected over every point of the model
cell, the map of pairs `(τ^*E, τ^*E|_{S^{n+1}}) → (D^{n+2}, S^{n+1})` induced by the fibration is an
isomorphism on homology in degrees `< (n+2) + φ` and surjective in degree `(n+2) + φ`. -/
theorem discPairStrong (n : ℕ) :
    ∀ (E : Type) [TopologicalSpace E] (B : Type) [TopologicalSpace B] (p : C(E, B))
      (hp : Work.StemsB.IsSerreFibration p) (τ : C(Work.RatHurewicz.cellDisk n, B)) (φ : ℕ),
      (∀ y : Work.RatHurewicz.cellDisk n, ∀ j : ℕ, 0 < j → j < φ →
        IsZero ((Work.Cohomology.singularChains ℤ
          (TopCat.of (Work.StemsB.fibre p (τ y)))).homology j)) →
      (∀ y : Work.RatHurewicz.cellDisk n,
        IsIso (TopCat.singularHomology₀ε
          (TopCat.of (Work.StemsB.fibre p (τ y))) (ModuleCat.of ℤ ℤ))) →
      (∀ i : ℕ, i < (n + 2) + φ →
        IsIso (HomologicalComplex.homologyMap (Work.Serre.discPairMap n p τ) i)) ∧
      Function.Surjective
        (HomologicalComplex.homologyMap (Work.Serre.discPairMap n p τ) ((n + 2) + φ)).hom := by
  intro E _ B _ p hp τ φ hfib h0
  obtain ⟨hcubeIso, hcubeSurj⟩ :=
    cubePairStrong (n + 2) E B p hp (tauC n τ) φ
      (fun y j hj hjφ => hfib (cHomeo n y) j hj hjφ)
      (fun y => h0 (cHomeo n y))
  let A₁ : Set (Work.StemsB.Pullback p (tauC n τ)) :=
    Work.Serre.pbPre p (tauC n τ) (Work.Serre.cubeBdryS (n + 2))
  let B₁ : Set (Work.StemsB.Pullback p τ) :=
    Work.Serre.discPre n p τ (Work.Serre.cellSphereSet n)
  let Bs : Set (Work.Stems.Cubical.IC (n + 2)) := Work.Serre.cubeBdryS (n + 2)
  let Bd : Set (Work.RatHurewicz.cellDisk n) := Work.Serre.cellSphereSet n
  let P : TopCat := TopCat.of (Work.StemsB.Pullback p (tauC n τ))
  let Q : TopCat := TopCat.of (Work.StemsB.Pullback p τ)
  let X : TopCat := TopCat.of (Work.Stems.Cubical.IC (n + 2))
  let Y : TopCat := TopCat.of (Work.RatHurewicz.cellDisk n)
  let Φm : P ⟶ Q := Work.StemsB.sphHomeoHom (pbH n p τ)
  let hcb : ∀ x ∈ A₁, Φm x ∈ B₁ := fun x hx => (pbH_mem n p τ x).mp hx
  let hcb' : ∀ y ∈ B₁, Work.StemsB.sphHomeoHom (X := Q) (Y := P) (pbH n p τ).symm y ∈ A₁ :=
    fun y hy => (pbH_mem n p τ ((pbH n p τ).symm y)).mpr (by
      rw [Homeomorph.apply_symm_apply]; exact hy)
  let Φb : TopCat.of A₁ ⟶ TopCat.of B₁ := Work.StemsB.pairRestrict Φm A₁ B₁ hcb
  let wΦ : Work.Cohomology.subtypeIncl P A₁ ≫ Φm
      = Φb ≫ Work.Cohomology.subtypeIncl Q B₁ :=
    Work.StemsB.pairRestrict_comp_subtypeIncl Φm A₁ B₁ hcb
  let Gm : Q ⟶ Y := TopCat.ofHom (Work.StemsB.pullbackSnd p τ)
  let Gb : TopCat.of B₁ ⟶ TopCat.of Bd := TopCat.ofHom (Work.Serre.discPairMapRel n p τ)
  let wG : Work.Cohomology.subtypeIncl Q B₁ ≫ Gm
      = Gb ≫ Work.Cohomology.subtypeIncl Y Bd := by ext x; rfl
  let Fm : P ⟶ X := TopCat.ofHom (Work.StemsB.pullbackSnd p (tauC n τ))
  let Fb : TopCat.of A₁ ⟶ TopCat.of Bs :=
    TopCat.ofHom (Work.Serre.cubePairMapRel (n + 2) p (tauC n τ))
  let wF : Work.Cohomology.subtypeIncl P A₁ ≫ Fm
      = Fb ≫ Work.Cohomology.subtypeIncl X Bs := by ext x; rfl
  let Em : X ⟶ Y := Work.StemsB.sphHomeoHom (cHomeo n)
  let heb : ∀ x ∈ Bs, Em x ∈ Bd := fun x hx => (cHomeo_mem_bdry n x).mp hx
  let heb' : ∀ y ∈ Bd, Work.StemsB.sphHomeoHom (X := Y) (Y := X) (cHomeo n).symm y ∈ Bs :=
    fun y hy => (cHomeo_mem_bdry n ((cHomeo n).symm y)).mpr (by
      rw [Homeomorph.apply_symm_apply]; exact hy)
  let Eb : TopCat.of Bs ⟶ TopCat.of Bd := Work.StemsB.pairRestrict Em Bs Bd heb
  let wE : Work.Cohomology.subtypeIncl X Bs ≫ Em
      = Eb ≫ Work.Cohomology.subtypeIncl Y Bd :=
    Work.StemsB.pairRestrict_comp_subtypeIncl Em Bs Bd heb
  have hD : Work.Serre.discPairMap n p τ
      = Work.Cohomology.relChainsMapOf Q Y B₁ Bd Gm Gb wG := rfl
  have hC : Work.Serre.cubePairMap (n + 2) p (tauC n τ)
      = Work.Cohomology.relChainsMapOf P X A₁ Bs Fm Fb wF := rfl
  have hsquare : Φm ≫ Gm = Fm ≫ Em := by
    apply TopCat.hom_ext
    ext x
    rfl
  have hsquareB : Φb ≫ Gb = Fb ≫ Eb := by
    apply TopCat.hom_ext
    ext x
    rfl
  have w₁ : Work.Cohomology.subtypeIncl P A₁ ≫ (Φm ≫ Gm)
      = (Φb ≫ Gb) ≫ Work.Cohomology.subtypeIncl Y Bd := by ext x; rfl
  have w₂ : Work.Cohomology.subtypeIncl P A₁ ≫ (Fm ≫ Em)
      = (Fb ≫ Eb) ≫ Work.Cohomology.subtypeIncl Y Bd := by ext x; rfl
  have h1 := Work.Cohomology.relChainsMapOf_comp A₁ B₁ Bd Φm Φb wΦ Gm Gb wG w₁
  have h2 := Work.Cohomology.relChainsMapOf_comp A₁ Bs Bd Fm Fb wF Em Eb wE w₂
  have hm := relChainsMapOf_congr' A₁ Bd hsquare hsquareB w₁ w₂
  have hrel : Work.Cohomology.relChainsMapOf P Q A₁ B₁ Φm Φb wΦ
        ≫ Work.Cohomology.relChainsMapOf Q Y B₁ Bd Gm Gb wG
      = Work.Cohomology.relChainsMapOf P X A₁ Bs Fm Fb wF
        ≫ Work.Cohomology.relChainsMapOf X Y Bs Bd Em Eb wE :=
    h1.trans (hm.trans h2.symm)
  -- the two vertical maps are isomorphisms of relative chain complexes
  haveI hΦI : IsIso (Work.Cohomology.relChainsMapOf P Q A₁ B₁ Φm Φb wΦ) :=
    isIso_relChainsMapOf_homeo' (X := P) (Y := Q) (pbH n p τ) A₁ B₁ hcb hcb'
  haveI hEI : IsIso (Work.Cohomology.relChainsMapOf X Y Bs Bd Em Eb wE) :=
    isIso_relChainsMapOf_homeo' (X := X) (Y := Y) (cHomeo n) Bs Bd heb heb'
  constructor
  · intro i hi
    have hF : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf P X A₁ Bs Fm Fb wF) i) := by
      rw [← hC]
      exact hcubeIso i hi
    rw [hD]
    have hsq_i := congrArg (fun φ => HomologicalComplex.homologyMap φ i) hrel
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq_i
    haveI : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf P Q A₁ B₁ Φm Φb wΦ) i) := inferInstance
    haveI : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X Y Bs Bd Em Eb wE) i) := inferInstance
    exact (isIso_iff_of_comm_square _ _ _ _ hsq_i).mpr hF
  · have hF : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf P X A₁ Bs Fm Fb wF) ((n + 2) + φ))) := by
      rw [← hC]
      exact hcubeSurj
    rw [hD]
    have hsq_i := congrArg (fun ψ => HomologicalComplex.homologyMap ψ ((n + 2) + φ)) hrel
    rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hsq_i
    haveI : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf P Q A₁ B₁ Φm Φb wΦ) ((n + 2) + φ)) := inferInstance
    haveI : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMapOf X Y Bs Bd Em Eb wE) ((n + 2) + φ)) := inferInstance
    exact (surjective_iff_of_comm_square _ _ _ _ hsq_i).mpr hF

end

end Work.Serre.SPC
