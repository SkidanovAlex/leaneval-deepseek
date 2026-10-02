import Mathlib
import Submission.Work.ThomBordism.valuePmOneV2Defs
import Submission.Work.ThomBordism.localGenDefs
import Submission.Work.ThomBordism.localisation_injective_zeroSection
import Submission.Work.ThomBordism.relCohMap_surjective_of_relCokerMap_surjective
import Submission.Work.Cohomology.relComplex_vanishing_of_homology_free
import Submission.Work.Cohomology.relChainsPairModel
import Submission.Work.Cohomology.pd_triple
import Submission.Work.Cohomology.Endgame.tripleLESSurj
import Submission.Work.Tubular.exists_relKronH_eval_iso
import Submission.Work.ThomBordism.FrameSigns.relKronH_natural
import Submission.Work.Tubular.PuncturedDiscPair.puncturedNormalPair_vanishing
import Submission.Work.ThomBordism.tubeRelChains_tubeInvPunct_nonzero
import Submission.Work.ThomBordism.tubeRelChains_tubePtSet_iso
import Submission.Work.ThomBordism.tubePtSet_relChains_free
import Submission.Work.ThomBordism.tubeRelChains_iso_puncturedNormalPair
import Submission.Work.ThomBordism.tubeRelChains_tubePtSet_free_seven_plus_k

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

namespace Work.ThomBordism

noncomputable section

open CategoryTheory

open Work.ThomBordism.PontryaginThom (EmbeddingData)

variable {V : Work.ThomBordism.Man8} {k : ℕ} {ε : ℝ}

/-!
# The localisation of the tube pair at a point of the zero section is an isomorphism

The target is the bijectivity of the map of relative cohomology groups

`H^{8+k}(C.U, C.U∖{E.e x}; ℤ) ⟶ H^{8+k}(C.U, C.U∖e(V); ℤ)`

induced by the identity.  The proof implemented here has two halves, both reduced to a single group
(the relative homology of the pair `(C.U∖{E.e x}, C.U∖e(V))`), which is compared with the model
pair `(ν∖x₀, ν∖0)` of the normal bundle:

* **injectivity** through the relative Kronecker pairing: `⟨f α, z⟩ = ⟨α, h z⟩` for the homology
  localisation `h`; `h` is injective because the relative homology *above the top* of the pair
  `(tubePtSet, tubeInvPunct)` vanishes (the model vanishing of
  `Work.Tubular.PuncturedDiscPair.puncturedNormalPair_vanishing` transported to the tube), and the
  pairing is an isomorphism on the pair `(C.U, tubePtSet)`.
* **surjectivity** through the long exact sequence of the triple: the third term
  `H^{8+k}(tubePtSet, tubeInvPunct)` vanishes as soon as the relative homology of the tube pair
  vanishes in degree `8+k` and its degree-`7+k` part is free (universal coefficients,
  `Work.Cohomology.relComplex_vanishing_of_homology_free`); then the exactness of the triple
  sequence makes `f` onto.
-/

/-! ## The case `k = 0`

For `k = 0` there is no closed embedding of a closed `8`-manifold into `ℝ⁸` at all: the normal
bundle is trivial, so the open tube is all of `e(V)`, which is at once open, closed and nonempty,
hence all of `ℝ⁸` — impossible since `ℝ⁸` is not compact.  The target statement is therefore
vacuous in that case; the lemma below makes this explicit. -/

/-- **No closed embedding of a compact `8`-manifold into `ℝ⁸` admits a tube chart.** -/
theorem false_of_embeddingData_eight [ConnectedSpace V.pt] (E : EmbeddingData V 8)
    (C : Work.Tubular.TubeChart E ε) : False := by
  have hvec : ∀ p : Work.Tubular.NormalTotal E, (p : V.pt × Work.Tubular.Euc 8).2 = 0 := by
    intro p
    have hfr : Module.finrank ℝ ↥(Work.Tubular.normalSpace E p.1.1) = 0 := by
      have h := Work.Tubular.finrank_normalSpace E p.1.1
      simpa using h
    have hbot : Work.Tubular.normalSpace E p.1.1 = ⊥ :=
      (Submodule.finrank_eq_zero).mp hfr
    have hmem : (p : V.pt × Work.Tubular.Euc 8).2 ∈ Work.Tubular.normalSpace E p.1.1 := p.2
    rw [hbot] at hmem
    simpa using hmem
  have hnorm : ∀ p : Work.Tubular.NormalTotal E, Work.Tubular.normalNorm E p = 0 := by
    intro p
    simp [Work.Tubular.normalNorm, hvec p]
  have hrange : Work.Tubular.openTubeSet E ε = Set.range E.e := by
    rw [Work.Tubular.openTubeSet]
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p.1.1, ?_⟩
      rw [Work.Tubular.tubeMap, hvec p, add_zero]
    · rintro ⟨x, rfl⟩
      refine ⟨Work.Tubular.zeroSectionNormal (k := 0) E x, ?_, ?_⟩
      · show Work.Tubular.normalNorm E (Work.Tubular.zeroSectionNormal (k := 0) E x) < ε
        rw [hnorm]; exact C.eps_pos
      · rw [Work.Tubular.tubeMap, Work.Tubular.zeroSectionNormal_apply]
        simp
  have hopen : IsOpen (Set.range E.e) := hrange ▸ C.isOpen_openTube
  have hclosed : IsClosed (Set.range E.e) := E.closedEmbedding.isClosed_range
  have hne : (Set.range E.e).Nonempty :=
    ⟨E.e (Classical.choice (inferInstance : Nonempty V.pt)), _, rfl⟩
  have huniv : Set.range E.e = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ hne
  have hcomp : IsCompact (Set.univ : Set (Work.Tubular.Euc 8)) := by
    rw [← huniv]
    exact isCompact_range E.smooth.continuous
  exact not_compactSpace_iff.mpr (inferInstance : NoncompactSpace (Work.Tubular.Euc 8))
    (isCompact_univ_iff.mp hcomp)

/-! ## The two bridges between the models of the relative cohomology of a pair

The first map of the cohomology triple `A ⊆ A' ⊆ X` is the inclusion of complexes
`C^*(X,A') ⊆ C^*(X,A)`, which is the pullback along the identity map of pairs. -/

/-- The inclusion of the relative cochain complexes is the pullback along the identity map of
pairs `(X,A) → (X,A')`. -/
theorem relCohMap_id_eq_relInclSet {X : TopCat} (A A' : Set X) (h : A ⊆ A') (n : ℕ) :
    Work.Thom.relCohMap (ContinuousMap.id X) A A' h ℤ n
      = HomologicalComplex.homologyMap (Work.Cohomology.Endgame.relInclSet X A A' h) n := by
  have hmap : Work.Cohomology.Endgame.relInclSet X A A' h
      = Work.Cohomology.relComplexMap ℤ A A' (TopCat.ofHom (ContinuousMap.id X)) h := by
    apply HomologicalComplex.hom_ext
    intro m
    rw [Work.Cohomology.Endgame.relInclSet_f, Work.Cohomology.relComplexMap_f]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [ModuleCat.hom_ofHom]
    rw [Work.Cohomology.Endgame.relInclSetHom_val]
    exact (Work.Cohomology.pd_us_relComplexMap_id_coe (X := X) (A := A) (B := A')
      (fun x hx => by simpa using h hx) m x).symm
  rw [hmap]


/-! ## The two halves of the localisation

Both halves are stated for the "relCokerMap model" of the homology localisation
`h : H_{8+k}(C.U, tubeInvPunct) → H_{8+k}(C.U, tubePtSet)`, i.e. the homology map of
`relCokerMap (TopCat.of ↥C.U) tubeInvPunct tubePtSet`. -/

/-- **The homology localisation is injective** when the relative homology of the pair
`(tubePtSet, tubeInvPunct)` vanishes in degree `8+k`.

This is the exactness of the long exact sequence of the triple `A ⊆ A' ⊆ X` at `H_{8+k}(X,A)`: the
composite `H_{8+k}(A',A) → H_{8+k}(X,A) → H_{8+k}(X,A')` is zero and the source vanishes. -/
theorem relCokerMap_homologyMap_injective_of_vanishing [ConnectedSpace V.pt] {k : ℕ}
    (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hzero : CategoryTheory.Limits.IsZero ((CategoryTheory.Limits.cokernel
      (Work.Cohomology.inclChainsSub (TopCat.of ↥C.U) (tubeInvPunct E C) (tubePtSet E C x)
        (tubePtSet_subset E C x))).homology (8 + k))) :
    Function.Injective ((HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap
      (TopCat.of ↥C.U) (tubeInvPunct E C) (tubePtSet E C x) (tubePtSet_subset E C x))
      (8 + k)).hom) := by
  classical
  have hsub : tubeInvPunct E C ⊆ tubePtSet E C x := tubePtSet_subset E C x
  have hS := Work.Cohomology.relChains_triple_shortExact (TopCat.of ↥C.U) (tubeInvPunct E C)
    (tubePtSet E C x) hsub
  -- the exactness of the triple long exact sequence at the middle term
  have hex := ShortComplex.Exact.moduleCat_range_eq_ker (hS.homology_exact₂ (8 + k))
  have hex' : LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.tripleShort (TopCat.of ↥C.U) (tubeInvPunct E C) (tubePtSet E C x)
        hsub).f (8 + k)))
      = LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.tripleShort (TopCat.of ↥C.U) (tubeInvPunct E C) (tubePtSet E C x)
        hsub).g (8 + k))) := hex
  -- the first map is zero, its source vanishing
  have hf0m : HomologicalComplex.homologyMap (Work.Cohomology.tripleShort (TopCat.of ↥C.U)
      (tubeInvPunct E C) (tubePtSet E C x) hsub).f (8 + k) = 0 :=
    CategoryTheory.Limits.IsZero.eq_zero_of_src hzero _
  have hf0 : ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.tripleShort (TopCat.of ↥C.U) (tubeInvPunct E C) (tubePtSet E C x)
        hsub).f (8 + k)) = 0 := by
    rw [hf0m]; exact ModuleCat.hom_zero
  rw [hf0, LinearMap.range_zero] at hex'
  have hker : LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.tripleShort (TopCat.of ↥C.U) (tubeInvPunct E C) (tubePtSet E C x)
        hsub).g (8 + k))) = ⊥ := hex'.symm
  have hinj := LinearMap.ker_eq_bot.mp hker
  rw [Work.Cohomology.tripleShort_g (TopCat.of ↥C.U) (tubeInvPunct E C) (tubePtSet E C x)
    hsub] at hinj
  exact hinj

/-- **The cohomological localisation is injective** when the homology localisation is.

The proof is the pairing argument: `⟨f α, z⟩ = ⟨α, h z⟩` (`relKronH_relCokerMap`), the pairing on the
pair `(C.U, tubePtSet)` is an isomorphism (`exists_relKronH_eval_iso`, the relative homology being
degreewise free), `H_{8+k}(C.U, tubePtSet) ≅ ℤ`, and `h z₀ ≠ 0` for some `z₀` (the non-vanishing of
the Thom group).  A functional on `ℤ` vanishing at a non-zero element is zero. -/
theorem relCohMap_injective_of_relCokerMap_injective [ConnectedSpace V.pt] {k : ℕ}
    (hk : 1 ≤ k) (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hi : Function.Injective ((HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap
      (TopCat.of ↥C.U) (tubeInvPunct E C) (tubePtSet E C x) (tubePtSet_subset E C x))
      (8 + k)).hom)) :
    Function.Injective ((Work.Thom.relCohMap (ContinuousMap.id ↥C.U) (tubeInvPunct E C)
      (tubePtSet E C x) (tubePtSet_subset E C x) ℤ (8 + k)).hom) := by
  classical
  have hsub : tubeInvPunct E C ⊆ tubePtSet E C x := tubePtSet_subset E C x
  -- the pairing-isomorphism on the pair `(C.U, tubePtSet)`
  obtain ⟨eB, heB⟩ := Work.Tubular.exists_relKronH_eval_iso (TopCat.of ↥C.U) (tubePtSet E C x)
    (8 + k) (tubePtSet_relChains_free (k := k) E C x)
  -- the identification of `H_{8+k}(C.U, tubePtSet)` with `ℤ`
  obtain ⟨eZ⟩ := tubeRelChains_tubePtSet_iso (k := k) E C x
  let eZl : ↥((Work.Cohomology.relChains (TopCat.of ↥C.U) (tubePtSet E C x)).homology (8 + k))
      ≃ₗ[ℤ] ℤ := eZ.toLinearEquiv
  -- a non-zero class of the Thom group
  obtain ⟨z₀, hz₀⟩ := tubeRelChains_tubeInvPunct_nonzero (k := k) hk E C x
  have hz₀' : z₀ ≠ 0 := hz₀
  have hhz₀ : (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap (TopCat.of ↥C.U)
      (tubeInvPunct E C) (tubePtSet E C x) hsub) (8 + k)).hom z₀ ≠ 0 := by
    intro h0
    exact hz₀ (hi (by rw [h0, map_zero]))
  intro α β hαβ
  -- the paired functional vanishes at `h z₀`
  have hvan : (Work.Tubular.relKronH (TopCat.of ↥C.U) (tubePtSet E C x) (8 + k) (α - β))
      ((HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap (TopCat.of ↥C.U)
        (tubeInvPunct E C) (tubePtSet E C x) hsub) (8 + k)).hom z₀) = 0 := by
    have hnat := Work.ThomBordism.relKronH_relCokerMap (X := TopCat.of ↥C.U) hsub (8 + k)
      (α - β) z₀
    have hleft : (Work.Thom.relCohMap (ContinuousMap.id ↥C.U) (tubeInvPunct E C) (tubePtSet E C x)
        hsub ℤ (8 + k)).hom (α - β) = 0 := by
      rw [map_sub, hαβ, sub_self]
    rw [← hnat, hleft]
    simp
  -- hence the functional `eB (α - β)` vanishes, so `α - β = 0`
  have hψ : eB (α - β) = 0 :=
    Work.ThomBordism.linearMap_eq_zero_of_apply_eq_zero eZl (eB (α - β))
      (by simpa using eZl.injective.ne hhz₀)
      (by
        rw [heB (α - β) ((HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap
          (TopCat.of ↥C.U) (tubeInvPunct E C) (tubePtSet E C x) hsub) (8 + k)).hom z₀)]
        exact hvan)
  have hαβ' : eB α = eB β := by
    have h' := hψ
    rw [map_sub] at h'
    exact sub_eq_zero.mp h'
  exact eB.injective hαβ'

/-- **The cohomological localisation is surjective** when the relative cohomology of the pair
`(tubePtSet, tubeInvPunct)` vanishes in degree `8+k`.

This is the exactness of the long exact sequence of the triple `A ⊆ A' ⊆ X` at `H_{8+k}(X,A')`: the
image of `f` is the kernel of the second map, which is zero because its target vanishes. -/
theorem relCohMap_surjective_of_vanishing [ConnectedSpace V.pt] {k : ℕ}
    (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hzero : Subsingleton (Work.Thom.RelCoh ℤ (8 + k) (TopCat.of ↥(tubePtSet E C x))
      {a : ↥(tubePtSet E C x) | (a : ↥C.U) ∈ tubeInvPunct E C})) :
    Function.Surjective ((Work.Thom.relCohMap (ContinuousMap.id ↥C.U) (tubeInvPunct E C)
      (tubePtSet E C x) (tubePtSet_subset E C x) ℤ (8 + k)).hom) := by
  classical
  have hsub : tubeInvPunct E C ⊆ tubePtSet E C x := tubePtSet_subset E C x
  have hh : ∀ y ∈ Work.Cohomology.Endgame.preA (TopCat.of ↥C.U) (tubeInvPunct E C)
      (tubePtSet E C x),
      (ConcreteCategory.hom (Work.Cohomology.subtypeIncl (TopCat.of ↥C.U)
        (tubePtSet E C x))) y ∈ tubeInvPunct E C := fun y hy => hy
  have hS := Work.Cohomology.Endgame.relCohTriple_shortExact (TopCat.of ↥C.U) (tubeInvPunct E C)
    (tubePtSet E C x) hsub hh
  haveI : Subsingleton ((Work.Cohomology.Endgame.relCohTripleShort (TopCat.of ↥C.U)
      (tubeInvPunct E C) (tubePtSet E C x) hsub hh).X₃.homology (8 + k)) := hzero
  -- the exactness of the triple long exact sequence at the middle term
  have hex := ShortComplex.Exact.moduleCat_range_eq_ker (hS.homology_exact₂ (8 + k))
  have hex' : LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.Endgame.relCohTripleShort (TopCat.of ↥C.U) (tubeInvPunct E C)
        (tubePtSet E C x) hsub hh).f (8 + k)))
      = LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.Endgame.relCohTripleShort (TopCat.of ↥C.U) (tubeInvPunct E C)
        (tubePtSet E C x) hsub hh).g (8 + k))) := hex
  -- the second map is zero, its target vanishing
  have hg0 : ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.Endgame.relCohTripleShort (TopCat.of ↥C.U) (tubeInvPunct E C)
        (tubePtSet E C x) hsub hh).g (8 + k)) = 0 :=
    LinearMap.ext (fun y => Subsingleton.elim _ _)
  rw [hg0, LinearMap.ker_zero] at hex'
  -- the range of the first map is everything; identify it with our localisation
  intro y
  have hy : y ∈ LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.Endgame.relCohTripleShort (TopCat.of ↥C.U) (tubeInvPunct E C)
        (tubePtSet E C x) hsub hh).f (8 + k))) := by
    rw [hex']; exact Submodule.mem_top
  have hy' : y ∈ LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.Endgame.relInclSet (TopCat.of ↥C.U) (tubeInvPunct E C)
        (tubePtSet E C x) hsub) (8 + k))) := hy
  rw [← relCohMap_id_eq_relInclSet (X := TopCat.of ↥C.U) (A := tubeInvPunct E C)
    (A' := tubePtSet E C x) (h := hsub) (n := 8 + k)] at hy'
  exact hy'

/-! ## The assembly -/

/-- **The localisation of the tube pair at a point of the zero section is an isomorphism**, given
the two facts about the relative homology of the pair `(C.U∖{E.e x}, C.U∖e(V))` that are proved in
the sibling files: its vanishing in degree `8+k` (transported from the normal-bundle model) and the
freeness of its degree-`7+k` part. -/
theorem tubePointLocalisationIso_of_inputs {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
    {k : ℕ} (hk : 1 ≤ k) (E : EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt)
    (hvan : CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains (TopCat.of ↥(tubePtSet E C x))
      {a : ↥(tubePtSet E C x) | (a : ↥C.U) ∈ tubeInvPunct E C}).homology (8 + k)))
    (hfree : Module.Free ℤ ↥((Work.Cohomology.relChains (TopCat.of ↥(tubePtSet E C x))
      {a : ↥(tubePtSet E C x) | (a : ↥C.U) ∈ tubeInvPunct E C}).homology (7 + k))) :
    Function.Bijective ((Work.Thom.relCohMap (ContinuousMap.id ↥C.U) (tubeInvPunct E C)
      (tubePtSet E C x) (tubePtSet_subset E C x) ℤ (8 + k)).hom) := by
  classical
  have hsub : tubeInvPunct E C ⊆ tubePtSet E C x := tubePtSet_subset E C x
  -- the vanishing for the "restricted inclusion" model of the pair `(tubePtSet, tubeInvPunct)`
  obtain ⟨e1⟩ := Work.Cohomology.coker_inclChainsSub_homology_iso
    (M := TopCat.of ↥C.U) (A := tubeInvPunct E C) (B := tubePtSet E C x) hsub (8 + k)
  have hzero1 : CategoryTheory.Limits.IsZero ((CategoryTheory.Limits.cokernel
      (Work.Cohomology.inclChainsSub (TopCat.of ↥C.U) (tubeInvPunct E C) (tubePtSet E C x)
        hsub)).homology (8 + k)) :=
    CategoryTheory.Limits.IsZero.of_iso hvan e1
  -- the cohomological vanishing of the pair, by universal coefficients
  have hL1 : Subsingleton (Work.Thom.RelCoh ℤ (8 + k) (TopCat.of ↥(tubePtSet E C x))
      {a : ↥(tubePtSet E C x) | (a : ↥C.U) ∈ tubeInvPunct E C}) := by
    have hvan' : CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains
        (TopCat.of ↥(tubePtSet E C x))
        {a : ↥(tubePtSet E C x) | (a : ↥C.U) ∈ tubeInvPunct E C}).homology (7 + k + 1)) := by
      rw [show 7 + k + 1 = 8 + k from by omega]
      exact hvan
    have h := Work.Cohomology.relComplex_vanishing_of_homology_free
      (X := TopCat.of ↥(tubePtSet E C x))
      {a : ↥(tubePtSet E C x) | (a : ↥C.U) ∈ tubeInvPunct E C} (7 + k) hvan' hfree
    rw [show 7 + k + 1 = 8 + k from by omega] at h
    exact h
  refine ⟨?_, ?_⟩
  · exact Work.ThomBordism.relCohMap_injective_of_relCokerMap_injective (V := V) (k := k) hk E C x
      (Work.ThomBordism.relCokerMap_homologyMap_injective_of_vanishing (V := V) (k := k) E C x
        hzero1)
  · exact Work.ThomBordism.relCohMap_surjective_of_vanishing (V := V) (k := k) E C x hL1

/-! ## The target -/

/-- **The localisation of the tube pair at the point `E.e x` of the zero section is an
isomorphism.** -/
theorem tubePointLocalisationIso {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt] {k : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) (x : V.pt) :
    Function.Bijective ((Work.Thom.relCohMap (ContinuousMap.id ↥C.U)
      (Work.ThomBordism.tubeInvPunct E C) (Work.ThomBordism.tubePtSet E C x)
      (Work.ThomBordism.tubePtSet_subset E C x) ℤ (8 + k)).hom) := by
  by_cases hk : 1 ≤ k
  · -- the two facts about the relative homology of the tube pair that the assembly consumes,
    -- proved in the sibling files
    have hiso : ∀ n : ℕ, Nonempty ((Work.Cohomology.relChains (TopCat.of ↥(tubePtSet E C x))
        {a : ↥(tubePtSet E C x) | (a : ↥C.U) ∈ tubeInvPunct E C}).homology n ≅
        (Work.Cohomology.relChains (TopCat.of (Work.Tubular.PuncturedDiscPair.Punct E x))
          (Work.Tubular.PuncturedDiscPair.PunctRel E x)).homology n) :=
      fun n => Work.ThomBordism.tubeRelChains_iso_puncturedNormalPair (k := k) hk E C x n
    have hfree : Module.Free ℤ ↥((Work.Cohomology.relChains (TopCat.of ↥(tubePtSet E C x))
        {a : ↥(tubePtSet E C x) | (a : ↥C.U) ∈ tubeInvPunct E C}).homology (7 + k)) :=
      Work.ThomBordism.tubeRelChains_tubePtSet_free_seven_plus_k (k := k) hk E C x
    have hvan : CategoryTheory.Limits.IsZero ((Work.Cohomology.relChains
        (TopCat.of ↥(tubePtSet E C x))
        {a : ↥(tubePtSet E C x) | (a : ↥C.U) ∈ tubeInvPunct E C}).homology (8 + k)) :=
      CategoryTheory.Limits.IsZero.of_iso
        (Work.Tubular.PuncturedDiscPair.puncturedNormalPair_vanishing E x) (hiso (8 + k)).some
    exact tubePointLocalisationIso_of_inputs hk E C x hvan hfree
  · obtain rfl : k = 0 := by omega
    exact (false_of_embeddingData_eight E C).elim

end
end Work.ThomBordism
