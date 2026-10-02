import Mathlib
import Submission.Work.Transgression.MVDefs
import Submission.Work.Transgression.H4Vanishing
import Submission.Work.Cohomology.MVCohomology

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The Mayer–Vietoris assembly of the transgression

`Work.Transgression.PuncturedCohCard a b` says that `H⁴` of the punctured total space `E ∖ 0` of
`clutchBundle a b` has `|a + b|` elements.  This module carries out the assembly from the
Mayer–Vietoris sequence of the cover `E ∖ 0 = pU ∪ pV` (with overlap `pW`), given the geometric
inputs on the two pieces and on the overlap:

* `surjective_HMap_rhoU`, `surjective_HMap_rhoV` — the two retractions `rhoU`, `rhoV` are onto on
  `H³` (they admit sections, hence so do their pullbacks);
* `bijective_HMap_rhoW` — `rhoW` is a homotopy equivalence, so `rhoW^*` is an isomorphism;
* `rhoU_iotaU`, `rhoV_iotaV` — the compatibility of the retractions with the inclusion of the
  overlap: `rhoU ∘ iotaU = prjB ∘ rhoW` and `rhoV ∘ iotaV = ψ ∘ rhoW`;
* the vanishing of `H⁴` on the two pieces (`Work.Transgression.H4Vanishing`);
* Künneth injectivity for `S³ × S³` (`Work.Transgression.KunnethInjQ2`) and the class of the
  clutching map (`Work.Transgression.PsiClass`).
-/

namespace Work.Transgression

open Work.TangentClasses Work.Thom CategoryTheory Limits

noncomputable section

/-! ## 1. The Mayer–Vietoris reduction to the overlap -/

/-- `H⁴` of each of the two pieces of the cover vanishes, so `H⁴` of the punctured total space is
the cohomology of the overlap modulo the range of the middle map of the Mayer–Vietoris
sequence. -/
theorem card_punctured_eq_card_quot (a b : ℤ)
    (hU4 : Subsingleton ↥(Coh ℤ 4 ↥(pU a b)))
    (hV4 : Subsingleton ↥(Coh ℤ 4 ↥(pV a b))) :
    Nat.card ↥(Coh ℤ 4 ↥(Work.Thom.zeroComplement (Zb a b)))
      = Nat.card (↥(Coh ℤ 3 ↥(pW a b)) ⧸
          LinearMap.range (HomologicalComplex.homologyMap
            (Work.Cohomology.mvCochainG (X := MV.XT a b) (pU a b) (pV a b)) 3).hom) := by
  have hU : IsOpen (pU a b) := isOpen_pU a b
  have hV : IsOpen (pV a b) := isOpen_pV a b
  have hcov : pU a b ∪ pV a b = Set.univ := pU_union_pV a b
  -- the middle term of the Mayer–Vietoris sequence vanishes in degree `4`
  have hZeroU : CategoryTheory.Limits.IsZero
      ((Work.Cohomology.cochainU (X := MV.XT a b) (pU a b) (pV a b)).homology 4) :=
    ModuleCat.isZero_iff_subsingleton.mpr hU4
  have hZeroV : CategoryTheory.Limits.IsZero
      ((Work.Cohomology.cochainV (X := MV.XT a b) (pU a b) (pV a b)).homology 4) :=
    ModuleCat.isZero_iff_subsingleton.mpr hV4
  have hZero : Subsingleton ↥((Work.Cohomology.cochainU (X := MV.XT a b) (pU a b) (pV a b) ⊞
      Work.Cohomology.cochainV (X := MV.XT a b) (pU a b) (pV a b)).homology 4) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (Work.Cohomology.isZero_coh_homology_biprod _ _ 4 hZeroU hZeroV)
  -- hence the first map of the sequence is zero in degree `4`
  haveI := hZero
  have hF0 : (HomologicalComplex.homologyMap
      (Work.Cohomology.mvCochainF (X := MV.XT a b) (pU a b) (pV a b)) 4).hom = 0 := by
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _
  -- so the connecting map is surjective
  have hsurj : Function.Surjective
      (Work.Cohomology.mvCohδ (X := MV.XT a b) (pU a b) (pV a b) 3).hom := by
    have hex := (Work.Cohomology.mvCoh_H_exact₁ (X := MV.XT a b) (pU a b) (pV a b)
      3).moduleCat_range_eq_ker
    have htop : LinearMap.range
        (Work.Cohomology.mvCohδ (X := MV.XT a b) (pU a b) (pV a b) 3).hom = ⊤ := by
      rw [hex, hF0]
      simp
    exact LinearMap.range_eq_top.mp htop
  -- and exactness at the overlap identifies its kernel
  have hker : LinearMap.ker
      (Work.Cohomology.mvCohδ (X := MV.XT a b) (pU a b) (pV a b) 3).hom
      = LinearMap.range (HomologicalComplex.homologyMap
          (Work.Cohomology.mvCochainG (X := MV.XT a b) (pU a b) (pV a b)) 3).hom :=
    ((Work.Cohomology.mvCoh_H_exact₃ (X := MV.XT a b) (pU a b) (pV a b)
      3).moduleCat_range_eq_ker).symm
  -- the identification of `H⁴` of the total space with the homology of the small chains
  obtain ⟨eA⟩ := Work.Cohomology.cohSmallIso (X := MV.XT a b) (pU a b) (pV a b) hU hV hcov 4
  calc Nat.card ↥(Coh ℤ 4 ↥(Work.Thom.zeroComplement (Zb a b)))
      = Nat.card ↥((Work.Cohomology.dualComplex ℤ
          (Work.Cohomology.smallChains (X := MV.XT a b) (pU a b) (pV a b))).homology 4) :=
        Nat.card_congr eA.toLinearEquiv.toEquiv
    _ = Nat.card (↥((Work.Cohomology.cochainUV (X := MV.XT a b) (pU a b) (pV a b)).homology 3) ⧸
          LinearMap.ker (Work.Cohomology.mvCohδ
            (X := MV.XT a b) (pU a b) (pV a b) 3).hom) :=
        Nat.card_congr (LinearMap.quotKerEquivOfSurjective
          (Work.Cohomology.mvCohδ (X := MV.XT a b) (pU a b) (pV a b) 3).hom hsurj).symm.toEquiv
    _ = Nat.card (↥((Work.Cohomology.cochainUV (X := MV.XT a b) (pU a b) (pV a b)).homology 3) ⧸
          LinearMap.range (HomologicalComplex.homologyMap
            (Work.Cohomology.mvCochainG (X := MV.XT a b) (pU a b) (pV a b)) 3).hom) :=
        Nat.card_congr (Submodule.quotEquivOfEq
          (LinearMap.ker (Work.Cohomology.mvCohδ
            (X := MV.XT a b) (pU a b) (pV a b) 3).hom)
          (LinearMap.range (HomologicalComplex.homologyMap
            (Work.Cohomology.mvCochainG (X := MV.XT a b) (pU a b) (pV a b)) 3).hom) hker).toEquiv

/-! ## 2. The range of the middle map of the Mayer–Vietoris sequence -/

section Range

/-- The `U`-component of the Mayer–Vietoris map is (the dual of) `chainInclU`. -/
lemma biprod_inl_comp_mvCochainG (a b : ℤ) :
    (biprod.inl : Work.Cohomology.cochainU (X := MV.XT a b) (pU a b) (pV a b) ⟶
        (Work.Cohomology.cochainU (X := MV.XT a b) (pU a b) (pV a b) ⊞
          Work.Cohomology.cochainV (X := MV.XT a b) (pU a b) (pV a b)))
      ≫ Work.Cohomology.mvCochainG (X := MV.XT a b) (pU a b) (pV a b)
    = Work.Cohomology.dualComplexMap ℤ
        (Work.Cohomology.singularChains ℤ (TopCat.of ↥(pW a b)))
        (Work.Cohomology.singularChains ℤ (TopCat.of ↥(pU a b)))
        (Work.Cohomology.chainInclU (X := MV.XT a b) (pU a b) (pV a b)) := by
  apply HomologicalComplex.hom_ext
  intro k
  exact Work.Cohomology.mvCochainG_inl (X := MV.XT a b) (pU a b) (pV a b) k

/-- The `V`-component of the Mayer–Vietoris map is (the dual of) `chainInclV`. -/
lemma biprod_inr_comp_mvCochainG (a b : ℤ) :
    (biprod.inr : Work.Cohomology.cochainV (X := MV.XT a b) (pU a b) (pV a b) ⟶
        (Work.Cohomology.cochainU (X := MV.XT a b) (pU a b) (pV a b) ⊞
          Work.Cohomology.cochainV (X := MV.XT a b) (pU a b) (pV a b)))
      ≫ Work.Cohomology.mvCochainG (X := MV.XT a b) (pU a b) (pV a b)
    = Work.Cohomology.dualComplexMap ℤ
        (Work.Cohomology.singularChains ℤ (TopCat.of ↥(pW a b)))
        (Work.Cohomology.singularChains ℤ (TopCat.of ↥(pV a b)))
        (Work.Cohomology.chainInclV (X := MV.XT a b) (pU a b) (pV a b)) := by
  apply HomologicalComplex.hom_ext
  intro k
  exact Work.Cohomology.mvCochainG_inr (X := MV.XT a b) (pU a b) (pV a b) k

/-- The `U`-component of the Mayer–Vietoris map on `H³` is the pullback along `iotaU`. -/
lemma homologyMap_mvCochainG_inl (a b : ℤ) :
    HomologicalComplex.homologyMap
        (biprod.inl : Work.Cohomology.cochainU (X := MV.XT a b) (pU a b) (pV a b) ⟶
          (Work.Cohomology.cochainU (X := MV.XT a b) (pU a b) (pV a b) ⊞
            Work.Cohomology.cochainV (X := MV.XT a b) (pU a b) (pV a b))) 3
      ≫ HomologicalComplex.homologyMap
          (Work.Cohomology.mvCochainG (X := MV.XT a b) (pU a b) (pV a b)) 3
    = HMap (MV.iotaU a b) 3 := by
  rw [← HomologicalComplex.homologyMap_comp, biprod_inl_comp_mvCochainG a b,
    Work.Cohomology.chainInclU]
  rfl

/-- The `V`-component of the Mayer–Vietoris map on `H³` is the pullback along `iotaV`. -/
lemma homologyMap_mvCochainG_inr (a b : ℤ) :
    HomologicalComplex.homologyMap
        (biprod.inr : Work.Cohomology.cochainV (X := MV.XT a b) (pU a b) (pV a b) ⟶
          (Work.Cohomology.cochainU (X := MV.XT a b) (pU a b) (pV a b) ⊞
            Work.Cohomology.cochainV (X := MV.XT a b) (pU a b) (pV a b))) 3
      ≫ HomologicalComplex.homologyMap
          (Work.Cohomology.mvCochainG (X := MV.XT a b) (pU a b) (pV a b)) 3
    = HMap (MV.iotaV a b) 3 := by
  rw [← HomologicalComplex.homologyMap_comp, biprod_inr_comp_mvCochainG a b,
    Work.Cohomology.chainInclV]
  rfl

end Range

/-! ## 3. The image of the overlap restriction -/

section Image

/-- The pullback of `gen3` along the clutching map, as a submodule statement. -/
theorem map_psi_top (a b : ℤ) :
    Submodule.map (HMap (psi a b) 3).hom (⊤ : Submodule ℤ ↥(Coh ℤ 3 MV.S3Q)) =
      Submodule.span ℤ ({MV.psiGen a b} : Set ↥(Coh ℤ 3 MV.S3Q2)) := by
  calc Submodule.map (HMap (psi a b) 3).hom (⊤ : Submodule ℤ ↥(Coh ℤ 3 MV.S3Q))
      = Submodule.map (HMap (psi a b) 3).hom
          (Submodule.span ℤ ({MV.gen3} : Set ↥(Coh ℤ 3 MV.S3Q))) := by rw [MV.span_gen3]
    _ = Submodule.span ℤ ((HMap (psi a b) 3).hom '' ({MV.gen3} : Set ↥(Coh ℤ 3 MV.S3Q))) :=
        Submodule.map_span _ _
    _ = Submodule.span ℤ ({MV.psiGen a b} : Set ↥(Coh ℤ 3 MV.S3Q2)) := by
        rw [Set.image_singleton]; rfl

/-- **The image of `H³(pU)` in `H³(pW)`**, transported to `S³ × S³` along `rhoW^*`: it is spanned
by `β` (the pullback of the generator along the second projection). -/
theorem range_iotaU (a b : ℤ)
    (hU3 : Function.Surjective (HMap (rhoU a b) 3).hom)
    (hCU : (HMap (MV.iotaU a b) 3).hom.comp (HMap (rhoU a b) 3).hom
      = (HMap (rhoW a b) 3).hom.comp (HMap (prjB) 3).hom) :
    LinearMap.range (HMap (MV.iotaU a b) 3).hom
      = Submodule.map (HMap (rhoW a b) 3).hom
          (Submodule.span ℤ ({MV.beta} : Set ↥(Coh ℤ 3 MV.S3Q2))) := by
  have h1 : LinearMap.range (HMap (MV.iotaU a b) 3).hom
      = LinearMap.range ((HMap (MV.iotaU a b) 3).hom.comp (HMap (rhoU a b) 3).hom) := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hU3, Submodule.map_top,
      LinearMap.range_eq_map]
  calc LinearMap.range (HMap (MV.iotaU a b) 3).hom
      = LinearMap.range ((HMap (MV.iotaU a b) 3).hom.comp (HMap (rhoU a b) 3).hom) := h1
    _ = LinearMap.range ((HMap (rhoW a b) 3).hom.comp (HMap (prjB) 3).hom) := by rw [hCU]
    _ = Submodule.map (HMap (rhoW a b) 3).hom
          (Submodule.map (HMap (prjB) 3).hom ⊤) := by
        rw [LinearMap.range_comp, LinearMap.range_eq_map]
    _ = Submodule.map (HMap (rhoW a b) 3).hom
          (Submodule.span ℤ ({MV.beta} : Set ↥(Coh ℤ 3 MV.S3Q2))) := by rw [MV.map_prjB_top]

/-- **The image of `H³(pV)` in `H³(pW)`**, transported to `S³ × S³` along `rhoW^*`: it is spanned
by the class of the clutching map `ψ`. -/
theorem range_iotaV (a b : ℤ)
    (hV3 : Function.Surjective (HMap (rhoV a b) 3).hom)
    (hCV : (HMap (MV.iotaV a b) 3).hom.comp (HMap (rhoV a b) 3).hom
      = (HMap (rhoW a b) 3).hom.comp (HMap (psi a b) 3).hom) :
    LinearMap.range (HMap (MV.iotaV a b) 3).hom
      = Submodule.map (HMap (rhoW a b) 3).hom
          (Submodule.span ℤ ({MV.psiGen a b} : Set ↥(Coh ℤ 3 MV.S3Q2))) := by
  have h1 : LinearMap.range (HMap (MV.iotaV a b) 3).hom
      = LinearMap.range ((HMap (MV.iotaV a b) 3).hom.comp (HMap (rhoV a b) 3).hom) := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hV3, Submodule.map_top,
      LinearMap.range_eq_map]
  calc LinearMap.range (HMap (MV.iotaV a b) 3).hom
      = LinearMap.range ((HMap (MV.iotaV a b) 3).hom.comp (HMap (rhoV a b) 3).hom) := h1
    _ = LinearMap.range ((HMap (rhoW a b) 3).hom.comp (HMap (psi a b) 3).hom) := by rw [hCV]
    _ = Submodule.map (HMap (rhoW a b) 3).hom
          (Submodule.map (HMap (psi a b) 3).hom ⊤) := by
        rw [LinearMap.range_comp, LinearMap.range_eq_map]
    _ = Submodule.map (HMap (rhoW a b) 3).hom
          (Submodule.span ℤ ({MV.psiGen a b} : Set ↥(Coh ℤ 3 MV.S3Q2))) := by rw [map_psi_top]

/-- The span of two classes is the supremum of the two spans. -/
theorem span_pair_eq (x y : ↥(Coh ℤ 3 MV.S3Q2)) :
    Submodule.span ℤ ({x, y} : Set ↥(Coh ℤ 3 MV.S3Q2))
      = Submodule.span ℤ {x} ⊔ Submodule.span ℤ {y} := by
  rw [show ({x, y} : Set ↥(Coh ℤ 3 MV.S3Q2)) = {x} ∪ {y} from by
    ext z; simp [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm], Submodule.span_union]

/-- **The range of the middle map of the Mayer–Vietoris sequence**, in the model `S³ × S³`: it is
the image under `rhoW^*` of the span of `β` and the class of the clutching map. -/
theorem range_mvCochainG (a b : ℤ)
    (hU3 : Function.Surjective (HMap (rhoU a b) 3).hom)
    (hV3 : Function.Surjective (HMap (rhoV a b) 3).hom)
    (hCU : (HMap (MV.iotaU a b) 3).hom.comp (HMap (rhoU a b) 3).hom
      = (HMap (rhoW a b) 3).hom.comp (HMap (prjB) 3).hom)
    (hCV : (HMap (MV.iotaV a b) 3).hom.comp (HMap (rhoV a b) 3).hom
      = (HMap (rhoW a b) 3).hom.comp (HMap (psi a b) 3).hom) :
    LinearMap.range (HomologicalComplex.homologyMap
        (Work.Cohomology.mvCochainG (X := MV.XT a b) (pU a b) (pV a b)) 3).hom
      = Submodule.map (HMap (rhoW a b) 3).hom
          (Submodule.span ℤ ({MV.beta, MV.psiGen a b} : Set ↥(Coh ℤ 3 MV.S3Q2))) := by
  -- the two components of the middle map
  have hGinl : (HomologicalComplex.homologyMap
        (Work.Cohomology.mvCochainG (X := MV.XT a b) (pU a b) (pV a b)) 3).hom.comp
        (HomologicalComplex.homologyMap
          (biprod.inl : Work.Cohomology.cochainU (X := MV.XT a b) (pU a b) (pV a b) ⟶
            (Work.Cohomology.cochainU (X := MV.XT a b) (pU a b) (pV a b) ⊞
              Work.Cohomology.cochainV (X := MV.XT a b) (pU a b) (pV a b))) 3).hom
      = (HMap (MV.iotaU a b) 3).hom := by
    have h := congrArg ModuleCat.Hom.hom (homologyMap_mvCochainG_inl a b)
    rw [ModuleCat.hom_comp] at h
    exact h
  have hGinr : (HomologicalComplex.homologyMap
        (Work.Cohomology.mvCochainG (X := MV.XT a b) (pU a b) (pV a b)) 3).hom.comp
        (HomologicalComplex.homologyMap
          (biprod.inr : Work.Cohomology.cochainV (X := MV.XT a b) (pU a b) (pV a b) ⟶
            (Work.Cohomology.cochainU (X := MV.XT a b) (pU a b) (pV a b) ⊞
              Work.Cohomology.cochainV (X := MV.XT a b) (pU a b) (pV a b))) 3).hom
      = (HMap (MV.iotaV a b) 3).hom := by
    have h := congrArg ModuleCat.Hom.hom (homologyMap_mvCochainG_inr a b)
    rw [ModuleCat.hom_comp] at h
    exact h
  -- the splitting of the range
  have hsplit : LinearMap.range (HomologicalComplex.homologyMap
        (Work.Cohomology.mvCochainG (X := MV.XT a b) (pU a b) (pV a b)) 3).hom
      = LinearMap.range (HMap (MV.iotaU a b) 3).hom ⊔
          LinearMap.range (HMap (MV.iotaV a b) 3).hom := by
    have htot := congrArg ModuleCat.Hom.hom
      (Work.Cohomology.coh_homologyMap_total
        (Work.Cohomology.cochainU (X := MV.XT a b) (pU a b) (pV a b))
        (Work.Cohomology.cochainV (X := MV.XT a b) (pU a b) (pV a b)) 3)
    rw [ModuleCat.hom_add, ModuleCat.hom_id, ModuleCat.hom_comp, ModuleCat.hom_comp] at htot
    refine le_antisymm ?_ (sup_le ?_ ?_)
    · rintro x ⟨y, rfl⟩
      have hy := LinearMap.congr_fun htot y
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at hy
      rw [← hy, map_add]
      refine Submodule.add_mem _
        (Submodule.mem_sup_left (show _ ∈ LinearMap.range (HMap (MV.iotaU a b) 3).hom from
          ⟨(HomologicalComplex.homologyMap
              (biprod.fst : (Work.Cohomology.cochainU (X := MV.XT a b) (pU a b) (pV a b) ⊞
                Work.Cohomology.cochainV (X := MV.XT a b) (pU a b) (pV a b)) ⟶
                Work.Cohomology.cochainU (X := MV.XT a b) (pU a b) (pV a b)) 3).hom y,
            by rw [← hGinl]; rfl⟩))
        (Submodule.mem_sup_right (show _ ∈ LinearMap.range (HMap (MV.iotaV a b) 3).hom from
          ⟨(HomologicalComplex.homologyMap
              (biprod.snd : (Work.Cohomology.cochainU (X := MV.XT a b) (pU a b) (pV a b) ⊞
                Work.Cohomology.cochainV (X := MV.XT a b) (pU a b) (pV a b)) ⟶
                Work.Cohomology.cochainV (X := MV.XT a b) (pU a b) (pV a b)) 3).hom y,
            by rw [← hGinr]; rfl⟩))
    · rw [← hGinl]
      rintro x ⟨z, rfl⟩
      exact ⟨(HomologicalComplex.homologyMap
        (biprod.inl : Work.Cohomology.cochainU (X := MV.XT a b) (pU a b) (pV a b) ⟶
          (Work.Cohomology.cochainU (X := MV.XT a b) (pU a b) (pV a b) ⊞
            Work.Cohomology.cochainV (X := MV.XT a b) (pU a b) (pV a b))) 3).hom z, rfl⟩
    · rw [← hGinr]
      rintro x ⟨z, rfl⟩
      exact ⟨(HomologicalComplex.homologyMap
        (biprod.inr : Work.Cohomology.cochainV (X := MV.XT a b) (pU a b) (pV a b) ⟶
          (Work.Cohomology.cochainU (X := MV.XT a b) (pU a b) (pV a b) ⊞
            Work.Cohomology.cochainV (X := MV.XT a b) (pU a b) (pV a b))) 3).hom z, rfl⟩
  calc LinearMap.range (HomologicalComplex.homologyMap
        (Work.Cohomology.mvCochainG (X := MV.XT a b) (pU a b) (pV a b)) 3).hom
      = LinearMap.range (HMap (MV.iotaU a b) 3).hom ⊔
          LinearMap.range (HMap (MV.iotaV a b) 3).hom := hsplit
    _ = Submodule.map (HMap (rhoW a b) 3).hom
          (Submodule.span ℤ ({MV.beta} : Set ↥(Coh ℤ 3 MV.S3Q2))) ⊔
        Submodule.map (HMap (rhoW a b) 3).hom
          (Submodule.span ℤ ({MV.psiGen a b} : Set ↥(Coh ℤ 3 MV.S3Q2))) := by
        rw [range_iotaU a b hU3 hCU, range_iotaV a b hV3 hCV]
    _ = Submodule.map (HMap (rhoW a b) 3).hom
          (Submodule.span ℤ ({MV.beta} : Set ↥(Coh ℤ 3 MV.S3Q2)) ⊔
            Submodule.span ℤ ({MV.psiGen a b} : Set ↥(Coh ℤ 3 MV.S3Q2))) := by
        rw [Submodule.map_sup]
    _ = Submodule.map (HMap (rhoW a b) 3).hom
          (Submodule.span ℤ ({MV.beta, MV.psiGen a b} : Set ↥(Coh ℤ 3 MV.S3Q2))) := by
        rw [span_pair_eq]

end Image

/-! ## 4. The final computation of the quotient -/

section Final

theorem puncturedCohCard_of_inputs (a b : ℤ)
    (hU4 : Subsingleton ↥(Coh ℤ 4 ↥(pU a b)))
    (hV4 : Subsingleton ↥(Coh ℤ 4 ↥(pV a b)))
    (hU3 : Function.Surjective (HMap (rhoU a b) 3).hom)
    (hV3 : Function.Surjective (HMap (rhoV a b) 3).hom)
    (hW3 : Function.Bijective (HMap (rhoW a b) 3).hom)
    (hCU : (HMap (MV.iotaU a b) 3).hom.comp (HMap (rhoU a b) 3).hom
      = (HMap (rhoW a b) 3).hom.comp (HMap (prjB) 3).hom)
    (hCV : (HMap (MV.iotaV a b) 3).hom.comp (HMap (rhoV a b) 3).hom
      = (HMap (rhoW a b) 3).hom.comp (HMap (psi a b) 3).hom)
    (hKunn : ∀ x : ↥(Coh ℤ 3 MV.S3Q2),
      (HMap sectA 3).hom x = 0 → (HMap sectB 3).hom x = 0 → x = 0)
    (hPsi : (HMap (psi a b) 3).hom MV.gen3 = (a + b) • MV.alpha + MV.beta) :
    PuncturedCohCard a b := by
  -- Step 1: the Mayer–Vietoris reduction
  have hcard1 : Nat.card ↥(Coh ℤ 4 ↥(Work.Thom.zeroComplement (Zb a b)))
      = Nat.card (↥((Work.Cohomology.cochainUV (X := MV.XT a b) (pU a b) (pV a b)).homology 3) ⧸
          LinearMap.range (HomologicalComplex.homologyMap
            (Work.Cohomology.mvCochainG (X := MV.XT a b) (pU a b) (pV a b)) 3).hom) :=
    card_punctured_eq_card_quot a b hU4 hV4
  -- Step 2: transfer along `rhoW`
  have hrange := range_mvCochainG a b hU3 hV3 hCU hCV
  let φ : ↥(Coh ℤ 3 MV.S3Q2) ≃ₗ[ℤ] ↥(Coh ℤ 3 ↥(pW a b)) :=
    LinearEquiv.ofBijective (HMap (rhoW a b) 3).hom hW3
  have hcard2 : Nat.card (↥((Work.Cohomology.cochainUV (X := MV.XT a b)
          (pU a b) (pV a b)).homology 3) ⧸
          LinearMap.range (HomologicalComplex.homologyMap
            (Work.Cohomology.mvCochainG (X := MV.XT a b) (pU a b) (pV a b)) 3).hom)
      = Nat.card (↥(Coh ℤ 3 MV.S3Q2) ⧸
          Submodule.span ℤ ({MV.beta, MV.psiGen a b} : Set ↥(Coh ℤ 3 MV.S3Q2))) :=
    Nat.card_congr (Submodule.Quotient.equiv
      (Submodule.span ℤ ({MV.beta, MV.psiGen a b} : Set ↥(Coh ℤ 3 MV.S3Q2)))
      (LinearMap.range (HomologicalComplex.homologyMap
        (Work.Cohomology.mvCochainG (X := MV.XT a b) (pU a b) (pV a b)) 3).hom)
      φ hrange.symm).symm.toEquiv
  -- Step 3: the quotient of `H³(S³ × S³)`
  let S : ↥(Coh ℤ 3 MV.S3Q2) →ₗ[ℤ] ℤ × ℤ :=
    (MV.s3Iso.toLinearMap.comp (HMap sectA 3).hom).prod
      (MV.s3Iso.toLinearMap.comp (HMap sectB 3).hom)
  have hSalpha : S MV.alpha = (1, 0) := by
    have h1 : (HMap sectA 3).hom ((HMap prjA 3).hom MV.gen3) = MV.gen3 :=
      LinearMap.congr_fun MV.sectA_comp_prjA MV.gen3
    have h2 : (HMap sectB 3).hom ((HMap prjA 3).hom MV.gen3) = 0 :=
      LinearMap.congr_fun MV.sectB_prjA_zero MV.gen3
    refine Prod.ext ?_ ?_
    · show MV.s3Iso ((HMap sectA 3).hom ((HMap prjA 3).hom MV.gen3)) = 1
      rw [h1, MV.s3Iso_gen3]
    · show MV.s3Iso ((HMap sectB 3).hom ((HMap prjA 3).hom MV.gen3)) = 0
      rw [h2, map_zero]
  have hSbeta : S MV.beta = (0, 1) := by
    have h1 : (HMap sectA 3).hom ((HMap prjB 3).hom MV.gen3) = 0 :=
      LinearMap.congr_fun MV.sectA_prjB_zero MV.gen3
    have h2 : (HMap sectB 3).hom ((HMap prjB 3).hom MV.gen3) = MV.gen3 :=
      LinearMap.congr_fun MV.sectB_comp_prjB MV.gen3
    refine Prod.ext ?_ ?_
    · show MV.s3Iso ((HMap sectA 3).hom ((HMap prjB 3).hom MV.gen3)) = 0
      rw [h1, map_zero]
    · show MV.s3Iso ((HMap sectB 3).hom ((HMap prjB 3).hom MV.gen3)) = 1
      rw [h2, MV.s3Iso_gen3]
  have hSbij : Function.Bijective S := by
    refine ⟨fun x y hxy => ?_, fun p => ?_⟩
    · have hsub : S (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      have hx1 : (HMap sectA 3).hom (x - y) = 0 := by
        refine MV.s3Iso.injective ?_
        simpa [S] using congrArg Prod.fst hsub
      have hx2 : (HMap sectB 3).hom (x - y) = 0 := by
        refine MV.s3Iso.injective ?_
        simpa [S] using congrArg Prod.snd hsub
      have h0 := hKunn (x - y) hx1 hx2
      exact sub_eq_zero.mp h0
    · obtain ⟨c, d⟩ := p
      refine ⟨c • MV.alpha + d • MV.beta, ?_⟩
      rw [map_add, map_zsmul, map_zsmul, hSalpha, hSbeta]
      ext <;> simp
  let eS : ↥(Coh ℤ 3 MV.S3Q2) ≃ₗ[ℤ] ℤ × ℤ := LinearEquiv.ofBijective S hSbij
  have hK : Submodule.span ℤ ({MV.beta, MV.psiGen a b} : Set ↥(Coh ℤ 3 MV.S3Q2))
      = Submodule.span ℤ ({MV.beta, (a + b) • MV.alpha + MV.beta} :
          Set ↥(Coh ℤ 3 MV.S3Q2)) := by
    simp only [MV.psiGen]
    rw [hPsi]
  have hSadd : S ((a + b) • MV.alpha + MV.beta) = ((a + b), 1) := by
    rw [map_add, map_zsmul, hSalpha, hSbeta]
    ext <;> simp
  have hSK : Submodule.map S (Submodule.span ℤ ({MV.beta, MV.psiGen a b} :
        Set ↥(Coh ℤ 3 MV.S3Q2)))
      = Submodule.span ℤ ({((0 : ℤ), (1 : ℤ)), ((a + b), 1)} : Set (ℤ × ℤ)) := by
    rw [hK, Submodule.map_span]
    have himg : S '' ({MV.beta, (a + b) • MV.alpha + MV.beta} : Set ↥(Coh ℤ 3 MV.S3Q2))
        = ({((0 : ℤ), (1 : ℤ)), ((a + b), 1)} : Set (ℤ × ℤ)) := by
      ext p
      simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases hx with rfl | rfl
        · exact Or.inl hSbeta
        · exact Or.inr hSadd
      · rintro (h | h)
        · exact ⟨MV.beta, Or.inl rfl, hSbeta.trans h.symm⟩
        · exact ⟨(a + b) • MV.alpha + MV.beta, Or.inr rfl, hSadd.trans h.symm⟩
    rw [himg]
  have hcard3 : Nat.card (↥(Coh ℤ 3 MV.S3Q2) ⧸
        Submodule.span ℤ ({MV.beta, MV.psiGen a b} : Set ↥(Coh ℤ 3 MV.S3Q2)))
      = Nat.card ((ℤ × ℤ) ⧸ Submodule.span ℤ
          ({((0 : ℤ), (1 : ℤ)), ((a + b), 1)} : Set (ℤ × ℤ))) :=
    Nat.card_congr (Submodule.Quotient.equiv
      (Submodule.span ℤ ({MV.beta, MV.psiGen a b} : Set ↥(Coh ℤ 3 MV.S3Q2)))
      (Submodule.span ℤ ({((0 : ℤ), (1 : ℤ)), ((a + b), 1)} : Set (ℤ × ℤ)))
      eS hSK).toEquiv
  have hcard4 : Nat.card ((ℤ × ℤ) ⧸ Submodule.span ℤ
        ({((0 : ℤ), (1 : ℤ)), ((a + b), 1)} : Set (ℤ × ℤ))) = (a + b).natAbs := by
    obtain ⟨e⟩ := QuotPairSpan (a + b)
    rw [Nat.card_congr e.toEquiv, Nat.card_zmod]
  rw [PuncturedCohCard]
  exact hcard1.trans (hcard2.trans (hcard3.trans hcard4))

end Final

end

end Work.Transgression
