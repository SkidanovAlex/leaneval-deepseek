import Mathlib
import Submission.Work.RatHurewicz.Cofibre.StableRangeDefs
import Submission.Work.Cohomology.HomologyPairSequence
import Submission.Work.RatHurewicz.Cofibre.VContract
import Submission.Work.Serre.rangeWhiteheadInclInt
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.epsilonNaturality
import Submission.Work.Cohomology.euclidean_top_homology_vanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option linter.style.haveILetI false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.RatHurewicz.Cofibre

noncomputable section

variable {E F : Type} [TopologicalSpace E] [TopologicalSpace F]

/-! ## The geometry of the punctured cone

`cofibreV ι = {z | 0 < cofibreHeight ι z}` consists of the cone points of positive height.  When
`F` is nonempty it is contractible (`exists_contraction_cofibreV`); when `F` is empty it is empty.
Both facts are recorded here in the forms needed below. -/

/-- If the fibre `F` is empty then the cofibre is (a quotient of) `E` alone, and hence every point
has height `0`. -/
theorem cofibreHeight_eq_zero_of_isEmpty (ι : C(F, E)) [IsEmpty F] (z : cofibre ι) :
    cofibreHeight ι z = 0 := by
  refine Quotient.inductionOn z ?_
  intro a
  rcases a with e | y
  · exact cofibreHeight_incl ι e
  · exact isEmptyElim y

/-- If the fibre `F` is empty then the punctured cone `cofibreV ι` is empty. -/
theorem isEmpty_cofibreV_of_isEmpty (ι : C(F, E)) [IsEmpty F] : IsEmpty ↥(cofibreV ι) := by
  refine ⟨fun z => ?_⟩
  have hmem : (0 : unitInterval) < cofibreHeight ι z.1 := z.2
  rw [cofibreHeight_eq_zero_of_isEmpty ι z.1] at hmem
  exact absurd hmem (not_lt.mpr le_rfl)

/-- **The punctured cone is contractible** (for nonempty `F`): the contraction of
`exists_contraction_cofibreV` witnesses that the identity of `↥(cofibreV ι)` is nullhomotopic. -/
theorem contractibleSpace_cofibreV (ι : C(F, E)) [Nonempty F] :
    ContractibleSpace (TopCat.of (cofibreV ι)) := by
  obtain ⟨H, h0, b, h1⟩ := Work.RatHurewicz.exists_contraction_cofibreV ι
  refine (contractible_iff_id_nullhomotopic (TopCat.of (cofibreV ι))).mpr ⟨b, ?_⟩
  refine ⟨⟨⟨fun p : unitInterval × ↥(cofibreV ι) => H (p.2, p.1), ?_⟩, ?_, ?_⟩⟩
  · exact H.continuous.comp (continuous_snd.prodMk continuous_fst)
  · intro v
    exact h0 v
  · intro v
    exact h1 v

/-- **The positive-degree homology of the punctured cone vanishes.**  For nonempty `F` this is
`homologyContractible` applied to the contractible `↥(cofibreV ι)`; for empty `F` the space
`↥(cofibreV ι)` is empty and the claim is `isZero_homology_of_isEmpty_aux`. -/
theorem isZero_homology_cofibreV (ι : C(F, E)) (j : ℕ) (hj : 0 < j) :
    IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of (cofibreV ι))).homology j) := by
  by_cases hF : Nonempty F
  · haveI : ContractibleSpace (TopCat.of (cofibreV ι)) := contractibleSpace_cofibreV ι
    exact Work.Cohomology.homologyContractible j hj
  · haveI : IsEmpty F := not_nonempty_iff.mp hF
    haveI : IsEmpty ↥(cofibreV ι) := isEmpty_cofibreV_of_isEmpty ι
    exact Work.Cohomology.isZero_homology_of_isEmpty_aux _ j

/-- **The map `H₀(cofibreV ι) ⟶ H₀(cofibre ι)` is injective.**  It is the degree-`0` part of the
inclusion of the pair, which is the natural augmentation (`epsilonNaturality`); for nonempty `F`
the punctured cone is connected, so its augmentation is an isomorphism and `α₀` is a monomorphism,
and for empty `F` the source is a zero object. -/
theorem mono_h0_inclChains_cofibreV (ι : C(F, E)) :
    Mono (HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of (cofibre ι)) (cofibreV ι)) 0) := by
  by_cases hF : Nonempty F
  · haveI : ContractibleSpace (TopCat.of (cofibreV ι)) := contractibleSpace_cofibreV ι
    haveI : PathConnectedSpace (TopCat.of (cofibreV ι)) := inferInstance
    let α0 := HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of (cofibre ι)) (cofibreV ι)) 0
    let εX := (TopCat.of (cofibre ι)).singularHomology₀ε (ModuleCat.of ℤ ℤ)
    let εA := (TopCat.of (cofibreV ι)).singularHomology₀ε (ModuleCat.of ℤ ℤ)
    haveI : IsIso εA := inferInstance
    have hmonoA : Mono εA := inferInstance
    have hnat := Work.Cohomology.epsilonNaturality (TopCat.of (cofibreV ι))
      (TopCat.of (cofibre ι)) (Work.Cohomology.subtypeIncl (TopCat.of (cofibre ι)) (cofibreV ι))
    haveI : Mono (α0 ≫ εX) := hnat.symm ▸ hmonoA
    exact mono_of_mono α0 εX
  · haveI : IsEmpty F := not_nonempty_iff.mp hF
    haveI : IsEmpty ↥(cofibreV ι) := isEmpty_cofibreV_of_isEmpty ι
    have h0 : IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of (cofibreV ι))).homology 0) :=
      Work.Cohomology.isZero_homology_of_isEmpty_aux _ 0
    exact ⟨fun {Z} g h' _ => h0.eq_of_tgt g h'⟩

/-! ## The middle map of the long exact sequence of the pair `(cofibre ι, cofibreV ι)` -/

/-- **Injectivity**, for `i > 0`: the map `H_i(cofibreV ι) ⟶ H_i(cofibre ι)` vanishes (the source is
a positive-degree homology of a contractible space), so exactness of the pair sequence at
`H_i(cofibre ι)` makes the next map a monomorphism. -/
theorem mono_beta_cofibreV (ι : C(F, E)) (i : ℕ) (hi : 0 < i) :
    Mono (HomologicalComplex.homologyMap (cokernel.π
      (Work.Cohomology.inclChains (TopCat.of (cofibre ι)) (cofibreV ι))) i) := by
  have hf : HomologicalComplex.homologyMap
      (Work.Cohomology.inclChains (TopCat.of (cofibre ι)) (cofibreV ι)) i = 0 :=
    (isZero_homology_cofibreV ι i hi).eq_of_src _ 0
  exact (ShortComplex.exact_iff_mono _ hf).mp
    (Work.Cohomology.hPair_exact₂ (TopCat.of (cofibre ι)) (cofibreV ι) i)

/-- **Surjectivity**, for `i > 0`: for `i ≥ 2` the connecting map
`δ : H_i(cofibre ι, cofibreV ι) ⟶ H_{i-1}(cofibreV ι)` vanishes because its target is a
positive-degree homology of a contractible space, while for `i = 1` it vanishes because
`H₀(cofibreV ι) ⟶ H₀(cofibre ι)` is injective.  Exactness of the pair sequence at
`H_i(cofibre ι, cofibreV ι)` then makes the previous map an epimorphism. -/
theorem epi_beta_cofibreV (ι : C(F, E)) (i : ℕ) (hi : 0 < i) :
    Epi (HomologicalComplex.homologyMap (cokernel.π
      (Work.Cohomology.inclChains (TopCat.of (cofibre ι)) (cofibreV ι))) i) := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  rcases n with _ | n
  · -- `i = 1`: the connecting map into `H₀` of the punctured cone is zero.
    have hδ : Work.Cohomology.hPairδ (TopCat.of (cofibre ι)) (cofibreV ι) 0 = 0 := by
      have hEx := Work.Cohomology.hPair_exact₁ (TopCat.of (cofibre ι)) (cofibreV ι) 0
      rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hEx
      have hker : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Cohomology.inclChains (TopCat.of (cofibre ι)) (cofibreV ι)) 0)).ker = ⊥ := by
        rw [LinearMap.ker_eq_bot]
        exact (ModuleCat.mono_iff_injective _).mp (mono_h0_inclChains_cofibreV ι)
      rw [hker] at hEx
      exact ModuleCat.hom_ext (LinearMap.range_eq_bot.mp hEx)
    exact (ShortComplex.exact_iff_epi _ hδ).mp
      (Work.Cohomology.hPair_exact₃ (TopCat.of (cofibre ι)) (cofibreV ι) 0)
  · -- `i ≥ 2`: the connecting map vanishes because its target has vanishing homology.
    have hδ : Work.Cohomology.hPairδ (TopCat.of (cofibre ι)) (cofibreV ι) (n + 1) = 0 :=
      (isZero_homology_cofibreV ι (n + 1) (by omega)).eq_of_tgt _ 0
    exact (ShortComplex.exact_iff_epi _ hδ).mp
      (Work.Cohomology.hPair_exact₃ (TopCat.of (cofibre ι)) (cofibreV ι) (n + 1))

/-- **The map `H_i(cofibre ι) → H_i(cofibre ι, cofibreV ι)` is an isomorphism for `i > 0`.**

`cofibreV ι = {z : cofibre ι | 0 < cofibreHeight ι z}` is the punctured cone, an open subspace whose
apex has height `1 > 0`; it is contractible
(`Work.RatHurewicz.Cofibre.exists_contraction_cofibreV`, which needs `[Nonempty F]`; for `F = ∅` one
has `cofibreV ι = ∅` and the claim is trivial).  The map is
`cokernel.π (inclChains (cofibre ι) (cofibreV ι))`, the middle morphism of the long exact sequence of
the pair (`Work.Cohomology.hPair_exact₂`, `hPair_exact₃`).

Route.
* `H_j(cofibreV ι) = 0` for `j > 0` and `H_0(cofibreV ι) ≅ ℤ`: from the contraction,
  `↥(cofibreV ι) ≃ PUnit` is a homotopy equivalence and homology is transported by
  `Work.Cohomology.homologyEquiv` (`Work.Cohomology.contractible` also has a ready-made form).
* `mono (cokernel.π …)_i` for `i ≥ 1`: `hPair_exact₂` + `IsZero (H_i(cofibreV ι))`
  (`IsZero.eq_of_src`); `epi (cokernel.π …)_i`: for `i ≥ 2` use `hPair_exact₃` +
  `IsZero (H_{i-1}(cofibreV ι))` (`IsZero.eq_of_tgt`), and for `i = 1` only injectivity of
  `H_0(cofibreV ι) → H_0(cofibre ι)` is needed (the apex is joined to every point), forcing the
  connecting map `hPairδ (cofibre ι) (cofibreV ι) 0` to be zero — the same argument as in
  `Work/Cohomology/diskPairHomologyZero.lean`.
* `IsIso` from `Mono` and `Epi` (`isIso_of_mono_of_epi`). -/
theorem isIso_beta_cofibreV {E F : Type} [TopologicalSpace E] [TopologicalSpace F]
    (ι : C(F, E)) (i : ℕ) (hi : 0 < i) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap (CategoryTheory.Limits.cokernel.π
      (Work.Cohomology.inclChains (TopCat.of (Work.RatHurewicz.cofibre ι))
        (Work.RatHurewicz.cofibreV ι))) i) := by
  haveI := mono_beta_cofibreV ι i hi
  haveI := epi_beta_cofibreV ι i hi
  exact isIso_of_mono_of_epi _

end

end Work.RatHurewicz.Cofibre
