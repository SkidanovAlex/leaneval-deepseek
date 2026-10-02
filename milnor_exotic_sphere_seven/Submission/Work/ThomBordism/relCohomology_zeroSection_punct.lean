import Mathlib
import Submission.Work.Tubular.LocalDegree
import Submission.Work.Tubular.Defs
import Submission.Work.Tubular.Global
import Submission.Work.Cohomology.Endgame.tripleLESSurj
import Submission.Work.Cohomology.pd_us_f
import Submission.Work.ThomBordism.Mine.Vocab
import Submission.Work.ThomBordism.localisation_injective_zeroSection
import Submission.Work.ThomBordism.relH_localisation_injective_normalTotal
import Submission.Work.ThomBordism.normalTotal_relKronH_kernel_bot
import Submission.Work.ThomBordism.relCohMap_surjective_of_relCokerMap_surjective
import Submission.Work.ThomBordism.normalTotal_locCoh_succ_subsingleton
import Submission.Work.ThomBordism.Mine.discLocHSurjective
import Submission.Work.ThomBordism.Mine.discInclPointSurjective
import Submission.Work.Tubular.chartedSpace_normalDisc_add
import Submission.Work.Tubular.exists_halfOrientationFamily_normalDiscSub

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The top relative cohomology of the punctured zero-section pair vanishes

Target (statement unchanged): for `ν = NormalTotal E` the normal total space of an embedding
`E : V ↪ ℝ^{8+k}` of a connected closed oriented smooth `8`-manifold, `z = 0_x` a zero-section point
and `A` the complement of the zero section inside `ν ∖ {z}`,

  `H^{8+k}(ν∖{z}, A; ℤ) = 0`.

## The proof (all inputs are proved in the tree)

Write `X = ν`, `B = ν∖{z}` and `A = ν∖0` (`= normalNonzero E`), so that `A ⊆ B ⊆ X`, and put
`n = 8+k`.

1. **The cohomological localisation is surjective.**  The triple sequence of `A ⊆ B ⊆ X` has
   `H^{n+1}(X,B) = 0` (`normalTotal_locCoh_succ_subsingleton`), so the third term `H^n(B, B∩A)` of
   the triple — the target — vanishes as soon as the first map
   `resRelH : H^n(X,B) → H^n(X,A)` is surjective (`subsingleton_third_of_surj_first`, the proof of
   which is reproduced here from the tree, together with `relInclSet_eq_relCohMap`).

2. **The homological localisation is surjective** (this is the only geometric input, and it is the
   "local degree is a unit" statement).  It is computed on the *compact* disc bundle
   `D = NormalDiscSub E ε` of `ν`:
   * `Mine.discLocHSurjective` — on `D`, where the zero section is compact and the half-orientation
     family glues, the restriction `H_n(D, D∖Z) → H_n(D, D∖{0_x})` is onto;
   * `Mine.discInclPointSurjective` — the inclusion `D ↪ ν` induces a surjection of the local groups
     at `0_x` (the capping `cap E ε` is a homotopy retraction through maps of the point pair);
   * the naturality square `Work.PTGeometric.HOF.RelHmapOf_resRelH` of the inclusion then upgrades
     the disc-level statement to the ν-level one (this is the `hjRel` step below).
   Surjectivity passes to the cohomological localisation along the *relative Kronecker pairing*:
   its kernel on `H^n(X,A)` is trivial (`normalTotal_relKronH_kernel_bot`), the homology
   localisation is also injective (`relH_localisation_injective_normalTotal`, via the compactness of
   the zero section), and `relCohMap_surjective_of_relCokerMap_surjective` converts
   "(homological localisation bijective) + (pairing non-degenerate)" into the cohomological
   statement.  Because the two tasks above are stated for the *support* spelling of the excluded
   sets (a set and its complement) while the pairing needs the complement spelling, the file carries
   two small transport lemmas (`surjective_relCokerMap_of_eq`, `injective_relCokerMap_of_eq`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.ThomBordism.Mine

noncomputable section

open Work.ThomBordism.PontryaginThom (EmbeddingData)

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- The normal-nonzero locus is contained in the complement of a zero-section point. -/
theorem normalNonzero_subset_compl_singleton (E : EmbeddingData V (8 + k)) (x : V.pt) :
    Work.Tubular.normalNonzero E ⊆
      ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) := by
  intro p hp h
  refine (Work.Tubular.mem_normalNonzero (E := E)).mp hp ?_
  rw [h, Work.Tubular.zeroSectionNormal_apply]
  exact norm_zero

/-- `relCokerMap` does not depend on the proof of the subset inclusion. -/
theorem relCokerMap_congr_h {X : TopCat} {A B : Set X} (h h' : A ⊆ B) :
    Work.Cohomology.relCokerMap X A B h = Work.Cohomology.relCokerMap X A B h' := by
  have e1 := Work.Cohomology.relCokerMap_comp_π X A B h
  have e2 := Work.Cohomology.relCokerMap_comp_π X A B h'
  exact (cancel_epi (CategoryTheory.Limits.cokernel.π (Work.Cohomology.inclChains X A))).mp
    (e1.trans e2.symm)

/-- Transport of the surjectivity of a `relCokerMap`-map along equalities of the two excluded sets. -/
theorem surjective_relCokerMap_of_eq {X : TopCat} {A B C D : Set X} (hAB : A = B) (hCD : C = D)
    (hA : A ⊆ C) (hB : B ⊆ D) (n : ℕ)
    (h : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap X A C hA) n).hom) :
    Function.Surjective (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap X B D hB) n).hom := by
  subst hAB
  subst hCD
  rwa [relCokerMap_congr_h hA hB] at h

/-- The same for injectivity. -/
theorem injective_relCokerMap_of_eq {X : TopCat} {A B C D : Set X} (hAB : A = B) (hCD : C = D)
    (hA : A ⊆ C) (hB : B ⊆ D) (n : ℕ)
    (h : Function.Injective (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap X A C hA) n).hom) :
    Function.Injective (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap X B D hB) n).hom := by
  subst hAB
  subst hCD
  rwa [relCokerMap_congr_h hA hB] at h

/-- Transport of a surjectivity statement along an equality of degrees. -/
theorem surjective_homologyMap_of_deg {C D : CochainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D)
    {a b : ℕ} (hab : a = b)
    (h : Function.Surjective (HomologicalComplex.homologyMap φ a).hom) :
    Function.Surjective (HomologicalComplex.homologyMap φ b).hom := by
  subst hab
  exact h

/-- Transport of an injectivity statement along an equality of degrees. -/
theorem injective_homologyMap_of_deg {C D : CochainComplex (ModuleCat ℤ) ℕ} (φ : C ⟶ D)
    {a b : ℕ} (hab : a = b)
    (h : Function.Injective (HomologicalComplex.homologyMap φ a).hom) :
    Function.Injective (HomologicalComplex.homologyMap φ b).hom := by
  subst hab
  exact h

theorem subsingleton_third_of_surj_first {X : TopCat} {A A' : Set X} (h : A ⊆ A')
    (hh : ∀ x ∈ Work.Cohomology.Endgame.preA X A A',
      (ConcreteCategory.hom (Work.Cohomology.subtypeIncl X A')) x ∈ A) (n : ℕ)
    (hsurj : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.Endgame.relCohTripleShort X A A' h hh).f n)))
    (hzero : Subsingleton (Work.Cohomology.relCohomology ℤ X A' (n+1))) :
    Subsingleton ((Work.Cohomology.Endgame.relCohTripleShort X A A' h hh).X₃.homology n) := by
  classical
  have hS : (Work.Cohomology.Endgame.relCohTripleShort X A A' h hh).ShortExact :=
    Work.Cohomology.Endgame.relCohTriple_shortExact X A A' h hh
  have hex := hS.homology_exact₂ n
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hex
  have hfrange : LinearMap.range (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.Endgame.relCohTripleShort X A A' h hh).f n)) = ⊤ :=
    LinearMap.range_eq_top.mpr hsurj
  have hker : LinearMap.ker (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.Endgame.relCohTripleShort X A A' h hh).g n)) = ⊤ := by
    rw [← hex, hfrange]
  have hg : ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.Endgame.relCohTripleShort X A A' h hh).g n) = 0 :=
    LinearMap.ker_eq_top.mp hker
  have hsurjg : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.Endgame.relCohTripleShort X A A' h hh).g n)) := by
    have h3 := Work.Cohomology.Endgame.tripleLESSurj_aux X A A' h hh n hzero
    have hEq : (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
        (Work.Cohomology.Endgame.relCohTripleShort X A A' h hh).g n))
        = (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
          (Work.Cohomology.relComplexMap ℤ (Work.Cohomology.Endgame.preA X A A') A
            (Work.Cohomology.subtypeIncl X A') hh) n)) := rfl
    rw [hEq]
    exact h3
  refine ⟨fun y z => ?_⟩
  have hy : y = 0 := by
    obtain ⟨x, hx⟩ := hsurjg y
    rw [← hx, hg]
    rfl
  have hz : z = 0 := by
    obtain ⟨x, hx⟩ := hsurjg z
    rw [← hx, hg]
    rfl
  rw [hy, hz]

theorem relInclSet_eq_relCohMap {X : TopCat} (A A' : Set X) (h : A ⊆ A') (n : ℕ) :
    HomologicalComplex.homologyMap (Work.Cohomology.Endgame.relInclSet X A A' h) n
      = Work.Thom.relCohMap (ContinuousMap.id X) A A' h ℤ n := by
  have hmap : Work.Cohomology.Endgame.relInclSet X A A' h
      = Work.Cohomology.relComplexMap ℤ A A' (𝟙 X) (fun x hx => by simpa using h hx) := by
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
  rw [hmap, Work.Thom.relCohMap]
  congr 1

end

end Mine

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Work.ThomBordism.PontryaginThom (EmbeddingData)

/-! ## The assembly -/

/-- **The punctured zero section pair has vanishing top relative cohomology.** -/
theorem relCohomology_zeroSection_punct {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
    {k : ℕ} (hk : 1 ≤ k) (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (x : V.pt) :
    Subsingleton (Work.Cohomology.relCohomology ℤ
      (TopCat.of ↥({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}))
      ((Subtype.val : ↥({p : Work.Tubular.NormalTotal E |
        p ≠ Work.Tubular.zeroSectionNormal E x}) → Work.Tubular.NormalTotal E) ⁻¹'
        Work.Tubular.normalNonzero E)
      (8 + k)) := by
  classical
  haveI : NeZero k := ⟨by omega⟩
  obtain ⟨ε, hε, ⟨C⟩⟩ := Work.Tubular.hasTubularNeighbourhood E
  obtain ⟨R⟩ := Work.Tubular.DiscManifold.exists_halfModelReindex k
  have hsub := Mine.normalNonzero_subset_compl_singleton (E := E) x
  have hzsub : ({Work.Tubular.zeroSectionNormal E x} : Set (Work.Tubular.NormalTotal E))
      ⊆ Set.range (Work.Tubular.zeroSectionNormal E) :=
    Set.singleton_subset_iff.mpr (Set.mem_range_self (f := Work.Tubular.zeroSectionNormal E) x)
  have hDsub : ({Mine.zeroSecDisc (E := E) C.eps_pos x} : Set (Work.Tubular.NormalDiscSub E ε))
      ⊆ Mine.zeroSecSet (E := E) C.eps_pos :=
    Set.singleton_subset_iff.mpr (Mine.mem_zeroSecSet (E := E) C.eps_pos x)
  have hP1 := Mine.discLocHSurjective (V := V) (k := k) E C R x
  have hT2 := Mine.discInclPointSurjective (V := V) (k := k) E C x
  have hsquare := Work.PTGeometric.HOF.RelHmapOf_resRelH (n := 7 + k + 1)
    (Mine.discIncl E ε) hDsub hzsub (Mine.discIncl_not_mem_zeroSec E C) (Mine.discIncl_not_mem_point E C x)
  -- the ν-side localisation is surjective
  have hjRel : Function.Surjective (Work.Orient.resRelH (TopCat.of (Work.Tubular.NormalTotal E))
      (7 + k + 1) hzsub) := by
    intro y
    obtain ⟨y', hy'⟩ := hT2 y
    obtain ⟨z', hz'⟩ := hP1 y'
    refine ⟨(Work.PTGeometric.HOF.RelHmapOf (7 + k + 1) (Mine.discIncl E ε)
      (Mine.zeroSecSet (E := E) C.eps_pos)
      (Set.range (Work.Tubular.zeroSectionNormal E)) (Mine.discIncl_not_mem_zeroSec E C)) z', ?_⟩
    have h := LinearMap.congr_fun hsquare z'
    simp only [LinearMap.comp_apply] at h
    rw [← h, hz', hy']
  -- the spelling and degree transport
  have hjRel' : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap (TopCat.of (Work.Tubular.NormalTotal E))
        (Set.range (Work.Tubular.zeroSectionNormal E))ᶜ
        (({Work.Tubular.zeroSectionNormal E x} : Set (Work.Tubular.NormalTotal E))ᶜ)
        (Set.compl_subset_compl.mpr hzsub)) (7 + k + 1)).hom := by
    have h1 : (Work.Orient.resRelH (TopCat.of (Work.Tubular.NormalTotal E))
        (7 + k + 1) hzsub)
        = (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap
            (TopCat.of (Work.Tubular.NormalTotal E))
            (Set.range (Work.Tubular.zeroSectionNormal E))ᶜ
            (({Work.Tubular.zeroSectionNormal E x} : Set (Work.Tubular.NormalTotal E))ᶜ)
            (Set.compl_subset_compl.mpr hzsub)) (7 + k + 1)).hom := rfl
    rw [h1] at hjRel
    exact hjRel
  have hcompl : (({Work.Tubular.zeroSectionNormal E x} : Set (Work.Tubular.NormalTotal E))ᶜ)
      = ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) := by
    ext p
    simp
  have key7 : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) hsub)
      (7 + k + 1)).hom :=
    Mine.surjective_relCokerMap_of_eq (Work.ThomBordism.compl_range_zeroSectionNormal E) hcompl
      (Set.compl_subset_compl.mpr hzsub) hsub (7 + k + 1) hjRel'
  have key : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) hsub)
      (8 + k)).hom := by
    rw [show 7 + k + 1 = 8 + k from by omega] at key7
    exact key7
  -- the injectivity of the same map, in the same spelling
  have hji : Function.Injective (HomologicalComplex.homologyMap
      (Work.Cohomology.relCokerMap (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) hsub)
      (8 + k)).hom := by
    have hinj := Work.ThomBordism.relH_localisation_injective_normalTotal (V := V) (k := k) hk E x
    rw [Work.ThomBordism.RelHmap] at hinj
    exact Mine.injective_relCokerMap_of_eq (Work.ThomBordism.compl_range_zeroSectionNormal E) hcompl
      (Set.compl_subset_compl.mpr hzsub) hsub (8 + k) hinj
  have hker := Work.ThomBordism.normalTotal_relKronH_kernel_bot (V := V) hk E
  have hsurj := Work.ThomBordism.relCohMap_surjective_of_relCokerMap_surjective hsub (8 + k)
    key hji hker
  -- the triple sequence
  have hf : (Work.Cohomology.Endgame.relCohTripleShort (TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)
      ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) hsub
      (Work.Cohomology.Endgame.hsubA _ _ _)).f
      = Work.Cohomology.Endgame.relInclSet (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) hsub := rfl
  have hsurj' : Function.Surjective (ModuleCat.Hom.hom (HomologicalComplex.homologyMap
      (Work.Cohomology.Endgame.relCohTripleShort (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) hsub
        (Work.Cohomology.Endgame.hsubA _ _ _)).f (8 + k))) := by
    rw [hf, Mine.relInclSet_eq_relCohMap (X := TopCat.of (Work.Tubular.NormalTotal E))
      (Work.Tubular.normalNonzero E)
      ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) hsub (8 + k)]
    exact hsurj
  have hX3 := Mine.subsingleton_third_of_surj_first hsub (Work.Cohomology.Endgame.hsubA _ _ _)
    (8 + k) hsurj' (Work.ThomBordism.normalTotal_locCoh_succ_subsingleton (V := V) hk E x)
  -- identify `X₃.homology` with the target group
  have hX3eq : (Work.Cohomology.Endgame.relCohTripleShort (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) hsub
        (Work.Cohomology.Endgame.hsubA _ _ _)).X₃.homology (8 + k)
      = (Work.Cohomology.relComplex ℤ
          (TopCat.of ↥({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}))
          ((Subtype.val : ↥({p : Work.Tubular.NormalTotal E |
            p ≠ Work.Tubular.zeroSectionNormal E x}) → Work.Tubular.NormalTotal E) ⁻¹'
            Work.Tubular.normalNonzero E)).homology (8 + k) := by
    rw [show (Work.Cohomology.Endgame.relCohTripleShort (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)
        ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}) hsub
        (Work.Cohomology.Endgame.hsubA _ _ _)).X₃
      = Work.Cohomology.relComplex ℤ
          (TopCat.of ↥({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x}))
          (Work.Cohomology.Endgame.preA (TopCat.of (Work.Tubular.NormalTotal E))
            (Work.Tubular.normalNonzero E)
            ({p : Work.Tubular.NormalTotal E | p ≠ Work.Tubular.zeroSectionNormal E x})) from rfl]
  rw [hX3eq] at hX3
  exact hX3

end

end ThomBordism

end Work
