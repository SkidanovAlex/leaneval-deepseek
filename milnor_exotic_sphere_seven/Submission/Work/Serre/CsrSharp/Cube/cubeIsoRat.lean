import Mathlib
import Submission.Work.Serre.CsrSharp.Defs
import Submission.Work.Serre.cubePairDefs
import Submission.Work.Serre.cubeRelIso
import Submission.Work.Serre.cubeAmbient_isZero
import Submission.Work.Serre.cubeBdry_isZero
import Submission.Work.Serre.serreE2d
import Submission.Work.Serre.csrExcisionRat
import Submission.Work.Serre.csrPairFunctoriality
import Submission.Work.Serre.Csr.Base
import Submission.Work.StemsB.RelChainsR
import Submission.Work.StemsB.RatBaseNaturality

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The rational per-cube computation `(P_D)` over `ℚ`

This file proves `Work.Serre.CsrSharp.CubeIsoRat`, the rational-coefficient analogue of
`Work.Serre.cubeRelIso` (`Submission/Work/Serre/cubeRelIso.lean`): for a Serre fibration
`p : E → B`, a map `τ : I^D → B` and fibres which are rationally acyclic in degrees `0 < j < φ`
and rationally connected, the cube pair map `Work.Serre.CsrSharp.cubePairRat D p τ` is an
isomorphism on rational homology in degrees `< D + φ` and surjective in degree `D + φ`.

The proof mirrors the integral proof `cubeRelIso` verbatim, with every integral auxiliary replaced
by its `ℚ`-version:

* `Work.Serre.serreE2dRat` — `H_{k+D}(τ^*E, τ^*E|_{∂I^D};ℚ) ≅ H_k(F;ℚ)` (base change of `serreE2d`);
* `Work.Serre.Csr.cubeBdry_isZeroRat` / `cubeAmbient_isZeroRat` — the two vanishing statements,
  transferred from `ℤ` to `ℚ` by the flat base change `Work.Serre.Csr.isZero_relChainsR_rat_of_isZero_int`;
* `Work.Serre.Csr.cubeBdry_top_isoRat` — `H_D(I^D, ∂I^D;ℚ) ≅ ℚ`;
* `Work.Serre.Csr.cubeSectionMapRat` and its splitting property — giving surjectivity of the pair
  map in every degree;
* `Work.Serre.Csr.isIso_of_epi_of_ratIso` — a surjection between one-dimensional `ℚ`-vector spaces
  is an isomorphism, which upgrades the splitting in the top degree to an isomorphism.

The section of the projection over the cube is `Work.Serre.exists_section_cubePullback`, which is
coefficient-free, and the nonemptiness of the fibre is extracted from the degree-zero hypothesis by
`Work.Serre.Csr.nonempty_of_nonempty_homologyZeroIso`.
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace Work.Serre.CsrSharp.Cube

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## The `ℚ`-version of the E2(d) computation -/

/-- **Serre's relative cube computation over `ℚ`.**  For a Serre fibration `p : E → B`, a map
`τ : I^D → B` and a point `d₀` of the cube, the relative rational homology of the pullback over the
cube pair `(I^D, ∂I^D)` in degree `k + D` is the rational homology of the fibre over `τ d₀` in
degree `k`.  This is the base change along `ℤ → ℚ` of `Work.Serre.serreE2d`. -/
theorem serreE2dRat (D : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (τ : C(Work.Stems.Cubical.IC D, B))
    (d₀ : Work.Stems.Cubical.IC D) (k : ℕ) :
    Nonempty (((Work.StemsB.relChainsR ℚ (TopCat.of (Work.StemsB.Pullback p τ))
        (Work.Serre.pbPre p τ (Work.Serre.cubeBdryS D))).homology (k + D)) ≅
      ((Work.Cohomology.singularChains ℚ (TopCat.of (Work.StemsB.fibre p (τ d₀)))).homology k)) := by
  obtain ⟨e⟩ := Work.Serre.serreE2d E B p D hp τ d₀ k
  obtain ⟨h1⟩ := Work.Serre.Csr.relChainsRHomologyIsoRat
    (TopCat.of (Work.StemsB.Pullback p τ)) (Work.Serre.pbPre p τ (Work.Serre.cubeBdryS D)) (k + D)
  obtain ⟨h2⟩ := Work.Serre.Csr.absHomologyIsoRat
    (TopCat.of (Work.StemsB.fibre p (τ d₀))) k
  exact ⟨h1 ≪≫ Functor.mapIso Work.StemsB.IntRatF e ≪≫ h2.symm⟩

/-! ## The two vanishing statements over `ℚ` -/

/-- The relative rational homology of the cube pair `(I^D, ∂I^D)` vanishes away from degree `D`. -/
theorem cubeBdry_isZeroRat (D m : ℕ) (hm : m ≠ D) :
    IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of (Work.Stems.Cubical.IC D))
      (Work.Serre.cubeBdryS D)).homology m) :=
  Work.Serre.Csr.isZero_relChainsR_rat_of_isZero_int
    (TopCat.of (Work.Stems.Cubical.IC D)) (Work.Serre.cubeBdryS D) m
    (Work.Serre.cubeBdry_isZero D m hm)

/-- The relative rational homology of the pullback cube pair vanishes below the top degree. -/
theorem cubeAmbient_isZeroRat (D : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (τ : C(Work.Stems.Cubical.IC D, B))
    (m : ℕ) (hm : m < D) :
    IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of (Work.StemsB.Pullback p τ))
      (Work.Serre.pbPre p τ (Work.Serre.cubeBdryS D))).homology m) :=
  Work.Serre.Csr.isZero_relChainsR_rat_of_isZero_int
    (TopCat.of (Work.StemsB.Pullback p τ)) (Work.Serre.pbPre p τ (Work.Serre.cubeBdryS D)) m
    (Work.Serre.cubeAmbient_isZero D E B p hp τ m hm)

/-- The top relative rational homology of the cube pair is `ℚ`. -/
theorem cubeBdry_top_isoRat (D : ℕ) :
    Nonempty ((Work.StemsB.relChainsR ℚ (TopCat.of (Work.Stems.Cubical.IC D))
      (Work.Serre.cubeBdryS D)).homology D ≅ ModuleCat.of ℚ ℚ) :=
  Work.Serre.Csr.relChainsR_homology_iso_ratUnit
    (TopCat.of (Work.Stems.Cubical.IC D)) (Work.Serre.cubeBdryS D) D
    (Work.Serre.cubeBdry_top_iso D)

/-! ## The section map on relative chains, over `ℚ` -/

/-- The map of relative rational chains induced by a section of the projection `τ^*E → I^D`. -/
def cubeSectionMapRat (D : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC D, B))
    (s : C(Work.Stems.Cubical.IC D, Work.StemsB.Pullback p τ))
    (hs : (Work.StemsB.pullbackSnd p τ).comp s = ContinuousMap.id _) :
    Work.StemsB.relChainsR ℚ (TopCat.of (Work.Stems.Cubical.IC D)) (Work.Serre.cubeBdryS D) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of (Work.StemsB.Pullback p τ))
        (Work.Serre.pbPre p τ (Work.Serre.cubeBdryS D)) :=
  Work.Serre.relChainsRPairMap (Work.Serre.cubeBdryS D)
    (Work.Serre.pbPre p τ (Work.Serre.cubeBdryS D)) s
    (fun x hx => by
      have hx1 : Work.StemsB.pullbackSnd p τ (s x) = (x : Work.Stems.Cubical.IC D) :=
        congrFun (congrArg DFunLike.coe hs) x
      show Work.StemsB.pullbackSnd p τ (s x) ∈ Work.Serre.cubeBdryS D
      rw [hx1]
      exact hx)

/-- The composite of the section map with the cube pair map is the identity, over `ℚ`. -/
theorem cubeSectionMapRat_comp (D : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (τ : C(Work.Stems.Cubical.IC D, B))
    (s : C(Work.Stems.Cubical.IC D, Work.StemsB.Pullback p τ))
    (hs : (Work.StemsB.pullbackSnd p τ).comp s = ContinuousMap.id _) :
    cubeSectionMapRat D p τ s hs ≫ Work.Serre.CsrSharp.cubePairRat D p τ
      = 𝟙 (Work.StemsB.relChainsR ℚ (TopCat.of (Work.Stems.Cubical.IC D))
          (Work.Serre.cubeBdryS D)) := by
  have hπ1 : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of (Work.Stems.Cubical.IC D))
        (Work.Serre.cubeBdryS D)) ≫ cubeSectionMapRat D p τ s hs
      = Work.Cohomology.chainMap ℚ (TopCat.of (Work.Stems.Cubical.IC D))
          (TopCat.of (Work.StemsB.Pullback p τ)) (TopCat.ofHom s)
        ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of (Work.StemsB.Pullback p τ))
            (Work.Serre.pbPre p τ (Work.Serre.cubeBdryS D))) := by
    unfold cubeSectionMapRat Work.Serre.relChainsRPairMap Work.Serre.csrRelMapOf
    exact Work.Cohomology.cokernel_π_map _ _ _ _ _
  have hπ2 : cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of (Work.StemsB.Pullback p τ))
        (Work.Serre.pbPre p τ (Work.Serre.cubeBdryS D)))
        ≫ Work.Serre.CsrSharp.cubePairRat D p τ
      = Work.Cohomology.chainMap ℚ (TopCat.of (Work.StemsB.Pullback p τ))
          (TopCat.of (Work.Stems.Cubical.IC D)) (TopCat.ofHom (Work.StemsB.pullbackSnd p τ))
        ≫ cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of (Work.Stems.Cubical.IC D))
            (Work.Serre.cubeBdryS D)) := by
    unfold Work.Serre.CsrSharp.cubePairRat Work.Serre.relChainsRPairMap Work.Serre.csrRelMapOf
    exact Work.Cohomology.cokernel_π_map _ _ _ _ _
  apply (cancel_epi (cokernel.π (Work.StemsB.relChainsRIncl ℚ
    (TopCat.of (Work.Stems.Cubical.IC D)) (Work.Serre.cubeBdryS D)))).mp
  show cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of (Work.Stems.Cubical.IC D))
      (Work.Serre.cubeBdryS D))
      ≫ (cubeSectionMapRat D p τ s hs ≫ Work.Serre.CsrSharp.cubePairRat D p τ)
    = cokernel.π (Work.StemsB.relChainsRIncl ℚ (TopCat.of (Work.Stems.Cubical.IC D))
        (Work.Serre.cubeBdryS D)) ≫ 𝟙 _
  rw [← Category.assoc, hπ1, Category.assoc, hπ2, ← Category.assoc,
    ← Work.Cohomology.chainMap_comp_relChains ℚ, ← TopCat.ofHom_comp, hs, TopCat.ofHom_id]
  simp [Work.Cohomology.chainMap]

/-- **Surjectivity of the rational cube pair map in every degree**, from a point of the pullback:
transporting along a section of the projection over the (contractible) cube exhibits the map of
relative chain complexes as a split epimorphism, hence its map on homology as a split epimorphism. -/
theorem cubePairRat_surjective (D : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (τ : C(Work.Stems.Cubical.IC D, B))
    (x₀ : Work.StemsB.Pullback p τ) (n : ℕ) :
    Function.Surjective
      (HomologicalComplex.homologyMap (Work.Serre.CsrSharp.cubePairRat D p τ) n).hom := by
  obtain ⟨s, hs⟩ := Work.Serre.exists_section_cubePullback D p hp τ x₀
  intro y
  refine ⟨(ModuleCat.Hom.hom (HomologicalComplex.homologyMap
    (cubeSectionMapRat D p τ s hs) n)) y, ?_⟩
  have hcomp : HomologicalComplex.homologyMap (cubeSectionMapRat D p τ s hs) n ≫
      HomologicalComplex.homologyMap (Work.Serre.CsrSharp.cubePairRat D p τ) n = 𝟙 _ := by
    rw [← HomologicalComplex.homologyMap_comp (cubeSectionMapRat D p τ s hs)
      (Work.Serre.CsrSharp.cubePairRat D p τ) n, cubeSectionMapRat_comp,
      HomologicalComplex.homologyMap_id]
  have h := congrArg (fun φ => ModuleCat.Hom.hom φ y) hcomp
  simp only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply,
    LinearMap.id_apply] at h
  exact h

/-! ## The main theorem -/

/-- **The rational per-cube computation `(P_D)`.**  For a Serre fibration `p : E → B`, a map
`τ : I^D → B` and fibres which are rationally acyclic in degrees `0 < j < φ` and rationally
connected, `Work.Serre.CsrSharp.cubePairRat D p τ` is an isomorphism on rational homology in
degrees `< D + φ` and surjective in degree `D + φ`. -/
theorem cubePairStrongRat (D : ℕ) {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (τ : C(Work.Stems.Cubical.IC D, B))
    (φ : ℕ)
    (hfib : ∀ y : Work.Stems.Cubical.IC D, ∀ j : ℕ, 0 < j → j < φ →
      IsZero ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre p (τ y)))).homology j))
    (h0 : ∀ y : Work.Stems.Cubical.IC D,
      Nonempty ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre p (τ y)))).homology 0 ≅ ModuleCat.of ℚ ℚ)) :
    (∀ i : ℕ, i < D + φ →
      IsIso (HomologicalComplex.homologyMap (Work.Serre.CsrSharp.cubePairRat D p τ) i)) ∧
    Function.Surjective
      (HomologicalComplex.homologyMap (Work.Serre.CsrSharp.cubePairRat D p τ) (D + φ)).hom := by
  have hne : Nonempty (Work.StemsB.fibre p (τ (fun _ => 0))) :=
    Work.Serre.Csr.nonempty_of_nonempty_homologyZeroIso _ (h0 (fun _ => 0))
  obtain ⟨e₀⟩ := hne
  have hsurjD : Function.Surjective
      (HomologicalComplex.homologyMap (Work.Serre.CsrSharp.cubePairRat D p τ) D).hom :=
    cubePairRat_surjective D p hp τ ⟨(e₀.1, fun _ => 0), e₀.2⟩ D
  refine ⟨fun i hi => ?_, ?_⟩
  · rcases eq_or_ne i D with hD | hne'
    · -- the top degree: the splitting and the two identifications with `ℚ`
      rw [hD]
      obtain ⟨eM⟩ := serreE2dRat D p hp τ (fun _ => 0) 0
      obtain ⟨h0'⟩ := h0 (fun _ => 0)
      have hM : (Work.StemsB.relChainsR ℚ (TopCat.of (Work.StemsB.Pullback p τ))
          (Work.Serre.pbPre p τ (Work.Serre.cubeBdryS D))).homology D ≅ ModuleCat.of ℚ ℚ :=
        (eqToIso (congrArg (fun k => (Work.StemsB.relChainsR ℚ
            (TopCat.of (Work.StemsB.Pullback p τ)) (Work.Serre.pbPre p τ (Work.Serre.cubeBdryS D))).homology k)
          (Nat.zero_add D))).symm ≪≫ eM ≪≫ h0'
      obtain ⟨eN⟩ := cubeBdry_top_isoRat D
      exact Work.Serre.Csr.isIso_of_epi_of_ratIso hM eN _
        ((ModuleCat.epi_iff_surjective _).mpr hsurjD)
    · -- away from the top degree both sides vanish
      have hN : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of (Work.Stems.Cubical.IC D))
        (Work.Serre.cubeBdryS D)).homology i) := cubeBdry_isZeroRat D i hne'
      have hM : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of (Work.StemsB.Pullback p τ))
        (Work.Serre.pbPre p τ (Work.Serre.cubeBdryS D))).homology i) := by
        by_cases hlt : i < D
        · exact cubeAmbient_isZeroRat D p hp τ i hlt
        · have hDle : D ≤ i := Nat.le_of_not_lt hlt
          have hDlt : D < i := lt_of_le_of_ne hDle (Ne.symm hne')
          have hpos : 0 < i - D := Nat.sub_pos_of_lt hDlt
          have hltf : i - D < φ := by omega
          obtain ⟨e⟩ := serreE2dRat D p hp τ (fun _ => 0) (i - D)
          exact IsZero.of_iso (hfib (fun _ => 0) (i - D) hpos hltf)
            ((eqToIso (congrArg (fun k => (Work.StemsB.relChainsR ℚ
                (TopCat.of (Work.StemsB.Pullback p τ)) (Work.Serre.pbPre p τ (Work.Serre.cubeBdryS D))).homology k)
              (Nat.sub_add_cancel hDle))).symm ≪≫ e)
      exact Work.StemsB.isIso_of_isZero_of_isZero hM hN
  · -- surjectivity in degree `D + φ`: either the top degree, or the target vanishes
    rcases Nat.eq_zero_or_pos φ with hφ0 | hφpos
    · subst hφ0
      exact hsurjD
    · have hne'' : D + φ ≠ D := by omega
      have hN : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of (Work.Stems.Cubical.IC D))
        (Work.Serre.cubeBdryS D)).homology (D + φ)) := cubeBdry_isZeroRat D (D + φ) hne''
      have hsub : Subsingleton ((Work.StemsB.relChainsR ℚ (TopCat.of (Work.Stems.Cubical.IC D))
        (Work.Serre.cubeBdryS D)).homology (D + φ)) := ModuleCat.subsingleton_of_isZero hN
      intro y
      exact ⟨0, Subsingleton.elim (α := (Work.StemsB.relChainsR ℚ
        (TopCat.of (Work.Stems.Cubical.IC D)) (Work.Serre.cubeBdryS D)).homology (D + φ))
        _ _⟩

/-- **The rational per-cube computation, in the form of the contract
`Work.Serre.CsrSharp.CubeIsoRat`.**  This is the `ℚ`-coefficient analogue of
`Work.Serre.cubeRelIso`, with the surjectivity clause in the boundary degree. -/
theorem cubeIsoRat : Work.Serre.CsrSharp.CubeIsoRat := by
  intro D E _ B _ p hp τ φ hfib h0
  exact cubePairStrongRat D p hp τ φ hfib h0

end

end Work.Serre.CsrSharp.Cube
