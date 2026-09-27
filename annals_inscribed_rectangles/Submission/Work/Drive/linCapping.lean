import Mathlib
import Submission.Work.Drive.exists_cappingModel_projectivization
import Submission.Work.Drive.projCharted
import Submission.Work.Drive.projRotSmooth
import Submission.Work.Drive.contMDiffAt_projMk
import Submission.Work.Drive.contMDiffAt_projChartMap
import Submission.Work.Drive.cappingSpaceHomeoProj_rotCapping
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.rotCappingSmooth
import Submission.Work.Drive.contMDiffAt_halfLineProjective_iff_general

/-!
# The linear perturbations of the capping space

The counting lane of `Work.Drive.chainParity` needs, for the genericity of its triple points, the
freedom to move the *projective class* of a capped plane without touching its level: the perturbation

`linCapping A p = ((levelOf p, [A · (class of p)]))`

with `A : Eucl 3 ≃L[ℝ] Eucl 3` a small linear automorphism of `ℝ⁴ = Eucl 3` (the `ℝP³` of the model
`CappingSpace ≃ₜ (0,∞) × ℝP³`).  It commutes with the radial dilation `scaleCapping` and hence with the
radial sweep `clampedSweep`, it preserves the level `levelOf` (so the level design of the sweeps is
untouched), and it is `C^∞`.

This file collects that algebra: `linCapping`, its computation rule on the model
`cappingSpaceHomeoProj`, the level invariance, injectivity, the commutation with `scaleCapping` and
`clampedSweep`, and the smoothness of the projectivised linear map
(`contMDiffAt_projMap`) together with `ContMDiff (linCapping A)`.
-/

namespace Work.Drive

open scoped LinearAlgebra.Projectivization Manifold ContDiff Topology
open Set Filter

noncomputable section

set_option linter.style.haveILetI false


/-- The linear perturbations of the capping space: act on the projective class. -/
def linCapping (A : Eucl 3 ≃L[ℝ] Eucl 3) (p : CappingSpace) : CappingSpace :=
  cappingSpaceHomeoProj.symm ((cappingSpaceHomeoProj p).1,
    Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective (cappingSpaceHomeoProj p).2)

@[simp] lemma cappingSpaceHomeoProj_linCapping (A : Eucl 3 ≃L[ℝ] Eucl 3) (p : CappingSpace) :
    cappingSpaceHomeoProj (linCapping A p)
      = ((cappingSpaceHomeoProj p).1,
         Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective (cappingSpaceHomeoProj p).2) :=
  Homeomorph.apply_symm_apply _ _

@[simp] lemma levelOf_linCapping (A : Eucl 3 ≃L[ℝ] Eucl 3) (p : CappingSpace) :
    levelOf (linCapping A p) = levelOf p := by
  rw [levelOf, levelOf, cappingSpaceHomeoProj_linCapping]

lemma linCapping_injective (A : Eucl 3 ≃L[ℝ] Eucl 3) : Function.Injective (linCapping A) := by
  intro p q h
  have h1 : cappingSpaceHomeoProj (linCapping A p) = cappingSpaceHomeoProj (linCapping A q) := by
    rw [h]
  rw [cappingSpaceHomeoProj_linCapping, cappingSpaceHomeoProj_linCapping] at h1
  have h3 : (cappingSpaceHomeoProj p).1 = (cappingSpaceHomeoProj q).1 := (Prod.mk.inj h1).1
  have h2 : (cappingSpaceHomeoProj p).2 = (cappingSpaceHomeoProj q).2 :=
    Projectivization.map_injective _ A.injective (Prod.mk.inj h1).2
  exact cappingSpaceHomeoProj.injective (Prod.ext h3 h2)

@[simp] lemma levelOf_scaleCapping (a : Pos) (p : CappingSpace) :
    levelOf (scaleCapping a p) = (a : ℝ) * levelOf p := by
  rw [levelOf, levelOf, CapSmooth.cappingSpaceHomeoProj_scaleCapping]

lemma cls_scaleCapping (a : Pos) (p : CappingSpace) :
    (cappingSpaceHomeoProj (scaleCapping a p)).2 = (cappingSpaceHomeoProj p).2 := by
  rw [CapSmooth.cappingSpaceHomeoProj_scaleCapping]

lemma linCapping_scaleCapping (A : Eucl 3 ≃L[ℝ] Eucl 3) (a : Pos) (p : CappingSpace) :
    linCapping A (scaleCapping a p) = scaleCapping a (linCapping A p) := by
  apply cappingSpaceHomeoProj.injective
  rw [cappingSpaceHomeoProj_linCapping]
  refine Prod.ext ?_ ?_
  · refine Subtype.ext ?_
    show levelOf (scaleCapping a p) = levelOf (scaleCapping a (linCapping A p))
    rw [levelOf_scaleCapping, levelOf_scaleCapping, levelOf_linCapping]
  · rw [cls_scaleCapping, cls_scaleCapping, cappingSpaceHomeoProj_linCapping]

lemma clampScale_linCapping (A : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (x : EuclideanSpace ℝ (Fin 3)) :
    clampScale c ψ (fun y => linCapping A (P y)) x = clampScale c ψ P x := by
  rw [clampScale, clampScale, levelOf_linCapping]

theorem clampedSweep_linCapping (A : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (ψ : ℝ → ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) (x : EuclideanSpace ℝ (Fin 3)) :
    linCapping A (clampedSweep c ψ P x)
      = clampedSweep c ψ (fun y => linCapping A (P y)) x := by
  have hcs := clampScale_linCapping A c ψ P x
  simp only [clampedSweep_apply, linCapping_scaleCapping]
  have hpos : (pos (clampScale c ψ P x) (clampScale_pos c ψ P x) : Pos)
      = pos (clampScale c ψ (fun y => linCapping A (P y)) x)
          (clampScale_pos c ψ (fun y => linCapping A (P y)) x) := Subtype.ext hcs.symm
  rw [hpos]


theorem contMDiffAt_projMap (A : Eucl 3 ≃L[ℝ] Eucl 3) (p₀ : Projectivization ℝ (Eucl 3)) :
    @ContMDiffAt ℝ _ (EuclideanSpace ℝ (Fin 3)) _ _ (EuclideanSpace ℝ (Fin 3)) _
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (Projectivization ℝ (Eucl 3)) _ (projCharted 3)
      (EuclideanSpace ℝ (Fin 3)) _ _ (EuclideanSpace ℝ (Fin 3)) _
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (Projectivization ℝ (Eucl 3)) _ (projCharted 3)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective) p₀ := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Eucl 3)) := projCharted 3
  set i : Fin (3 + 1) := Classical.choose (exists_mem_projChartSource p₀) with hi
  have hpi : p₀ ∈ projChartSource i := Classical.choose_spec (exists_mem_projChartSource p₀)
  set j : Fin (3 + 1) := Classical.choose (exists_mem_projChartSource
    (Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective p₀)) with hj
  have hpj : Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective p₀ ∈ projChartSource j :=
    Classical.choose_spec (exists_mem_projChartSource
      (Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective p₀))
  -- the lift
  have hVne : ∀ x : EuclideanSpace ℝ (Fin 3),
      (A : Eucl 3 →ₗ[ℝ] Eucl 3) (projSection i x) ≠ 0 :=
    fun x h => projSection_ne_zero i x (A.map_eq_zero_iff.mp h)
  have hVs : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (Eucl 3)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => (A : Eucl 3 →ₗ[ℝ] Eucl 3) (projSection i x)) (projChartMap i p₀) := by
    rw [contMDiffAt_iff_contDiffAt]
    have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : Eucl 3 => (A : Eucl 3 →ₗ[ℝ] Eucl 3) x) :=
      (A : Eucl 3 →L[ℝ] Eucl 3).contDiff
    exact hA.contDiffAt.comp _ (contDiff_projSection 3 i).contDiffAt
  have hmk := contMDiffAt_projMk (n := 3) (k := 3)
    (fun x => (A : Eucl 3 →ₗ[ℝ] Eucl 3) (projSection i x)) hVne (projChartMap i p₀) hVs
  have hinner : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) (𝓡 3)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective (projChartInv i x))
      (projChartMap i p₀) := by
    have hfun : (fun x : EuclideanSpace ℝ (Fin 3) =>
          Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective (projChartInv i x))
        = fun x => Projectivization.mk ℝ ((A : Eucl 3 →ₗ[ℝ] Eucl 3) (projSection i x))
            (hVne x) := by
      funext x
      rw [projChartInv, Projectivization.map_mk]
    rw [hfun]
    exact hmk
  have hpj' : Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective
      (projChartInv i (projChartMap i p₀)) ∈ projChartSource j := by
    rw [projChartInv_projChartMap hpi]
    exact hpj
  have hchart : ContMDiffAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) (𝓡 3)
      ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => projChartMap j
        (Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective (projChartInv i x)))
      (projChartMap i p₀) :=
    (contMDiffAt_projChartMap 3 j _ hpj').comp (projChartMap i p₀) hinner
  have hchart' : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => projChartMap j
        (Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective (projChartInv i x)))
      (projChartMap i p₀) := hchart.contDiffAt
  -- the extended charts
  have tgt : (↑(extChartAt (𝓡 3)
        (Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective p₀)) :
        Projectivization ℝ (Eucl 3) → EuclideanSpace ℝ (Fin 3)) = projChartMap j := by
    rw [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp]
    rw [show (chartAt (EuclideanSpace ℝ (Fin 3))
      (Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective p₀)) = projChart j from rfl]
    rfl
  have src : (↑(extChartAt (𝓡 3) p₀).symm :
        EuclideanSpace ℝ (Fin 3) → Projectivization ℝ (Eucl 3)) = projChartInv i := by
    funext x
    rw [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq]
    rw [show (chartAt (EuclideanSpace ℝ (Fin 3)) p₀) = projChart i from rfl]
    rfl
  have hpt : (↑(extChartAt (𝓡 3) p₀) : Projectivization ℝ (Eucl 3) →
        EuclideanSpace ℝ (Fin 3)) p₀ = projChartMap i p₀ := by
    rw [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp]
    rw [show (chartAt (EuclideanSpace ℝ (Fin 3)) p₀) = projChart i from rfl]
    rfl
  have hG : (↑(extChartAt (𝓡 3)
        (Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective p₀)) ∘
        (Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective) ∘
          ↑(extChartAt (𝓡 3) p₀).symm)
      = (fun q : EuclideanSpace ℝ (Fin 3) => projChartMap j
          (Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective (projChartInv i q))) := by
    funext q
    rw [Function.comp_apply, Function.comp_apply, src, tgt]
  rw [contMDiffAt_iff]
  refine ⟨?_, ?_⟩
  · have hΨ : ContinuousAt (fun p : Projectivization ℝ (Eucl 3) => projChartMap i p) p₀ :=
      (contMDiffAt_projChartMap 3 i p₀ hpi).continuousAt
    have hcont : ContinuousAt (fun p : Projectivization ℝ (Eucl 3) =>
        Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective
          (projChartInv i (projChartMap i p))) p₀ :=
      hinner.continuousAt.comp (f := fun p : Projectivization ℝ (Eucl 3) => projChartMap i p)
        (x := p₀) hΨ
    refine hcont.congr ?_
    filter_upwards [(isOpen_projChartSource i).mem_nhds hpi] with p hp
    rw [projChartInv_projChartMap hp]
  · rw [show Set.range (↑(modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))) = Set.univ from by
        simp only [modelWithCornersSelf_coe, Set.range_id],
      contDiffWithinAt_univ, hG, hpt]
    exact hchart'




/-! ## The rotation of the perturbations

The perturbation `linCapping A` commutes with the rotation `rotCapping t` up to the conjugation of `A`
by the diagonal rotation `diagRot t` of `ℂ² ≅ ℝ⁴`.  This is what makes the *generic* perturbations of
the counting lane rotation invariant (the group element conjugated by an isometry stays as small).
-/

section Rotation

/-- `c₁` is additive, in the form used below (the workspace's two public copies of this fact cannot be
imported simultaneously). -/
lemma linCapping_c₁_add (v w : Eucl 3) : c₁ (v + w) = c₁ v + c₁ w := by
  rw [← confProjVecOf_c₁CLM_apply, ← confProjVecOf_c₁CLM_apply, ← confProjVecOf_c₁CLM_apply, map_add]

/-- `c₂` is additive. -/
lemma linCapping_c₂_add (v w : Eucl 3) : c₂ (v + w) = c₂ v + c₂ w := by
  rw [← confProjVecOf_c₂CLM_apply, ← confProjVecOf_c₂CLM_apply, ← confProjVecOf_c₂CLM_apply, map_add]

/-- The dictionary `ofComplex` is additive. -/
lemma ofComplex_add (z z' w w' : ℂ) :
    ofComplex (z + w) (z' + w') = ofComplex z z' + ofComplex w w' := by
  conv_lhs => rw [← ofComplex_c₁_c₂ (ofComplex (z + w) (z' + w'))]
  conv_rhs => rw [← ofComplex_c₁_c₂ (ofComplex z z' + ofComplex w w')]
  refine ofComplex_congr ?_ ?_
  · rw [c₁_ofComplex, linCapping_c₁_add, c₁_ofComplex, c₁_ofComplex]
  · rw [c₂_ofComplex, linCapping_c₂_add, c₂_ofComplex, c₂_ofComplex]

/-- The diagonal rotation is additive. -/
lemma diagRot_add' (t : ℝ) (x y : Eucl 3) : diagRot t (x + y) = diagRot t x + diagRot t y := by
  simp only [diagRot]
  rw [linCapping_c₁_add, linCapping_c₂_add, mul_add, mul_add, ofComplex_add]

/-- **The diagonal rotation of `ℂ² ≅ ℝ⁴` as a linear equivalence.** -/
def diagRotLin (t : ℝ) : Eucl 3 ≃ₗ[ℝ] Eucl 3 where
  toFun := diagRot t
  invFun := diagRot (-t)
  left_inv := fun x => by rw [diagRot_add, neg_add_cancel, diagRot_zero]
  right_inv := fun x => by rw [diagRot_add, add_neg_cancel, diagRot_zero]
  map_add' := diagRot_add' t
  map_smul' := diagRot_smul t

/-- **The diagonal rotation of `ℂ² ≅ ℝ⁴` as a continuous linear equivalence** (finite dimension). -/
def diagRotL (t : ℝ) : Eucl 3 ≃L[ℝ] Eucl 3 := (diagRotLin t).toContinuousLinearEquiv

@[simp] lemma diagRotL_apply (t : ℝ) (x : Eucl 3) : diagRotL t x = diagRot t x := rfl

/-- **The projectivisation of the diagonal rotation is the rotation `projRot t` of `ℝP³`.** -/
lemma projMap_diagRotL (t : ℝ) :
    Projectivization.map (diagRotL t : Eucl 3 →ₗ[ℝ] Eucl 3) (diagRotL t).injective
      = projRot t := by
  funext p
  rw [← Projectivization.mk_rep p]
  rw [Projectivization.map_mk, projRot_mk]
  rfl

/-- **The announced computation rule of the conjugated perturbation**: conjugating `A` by the diagonal
rotation is composing it with the rotation. -/
lemma diagRotConj_apply (t : ℝ) (A : Eucl 3 ≃L[ℝ] Eucl 3) (x : Eucl 3) :
    ((diagRotL t * A * (diagRotL t)⁻¹ : Eucl 3 ≃L[ℝ] Eucl 3)) x
      = diagRot t (A ((diagRotL t)⁻¹ x)) := by
  rw [show (diagRotL t * A * (diagRotL t)⁻¹ : Eucl 3 ≃L[ℝ] Eucl 3)
      = ((diagRotL t)⁻¹).trans (A.trans (diagRotL t)) from rfl]
  rw [ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.trans_apply]
  rfl

/-- **Functoriality of the projectivised perturbation.** -/
lemma projMap_mul_comp (e e' : Eucl 3 ≃L[ℝ] Eucl 3) :
    Projectivization.map (e : Eucl 3 →ₗ[ℝ] Eucl 3) e.injective
        ∘ Projectivization.map (e' : Eucl 3 →ₗ[ℝ] Eucl 3) e'.injective
      = Projectivization.map ((e * e' : Eucl 3 ≃L[ℝ] Eucl 3) : Eucl 3 →ₗ[ℝ] Eucl 3)
          (e * e').injective := by
  rw [show Projectivization.map (e : Eucl 3 →ₗ[ℝ] Eucl 3) e.injective
        ∘ Projectivization.map (e' : Eucl 3 →ₗ[ℝ] Eucl 3) e'.injective
      = Projectivization.map
          (((e : Eucl 3 →ₗ[ℝ] Eucl 3)).comp (e' : Eucl 3 →ₗ[ℝ] Eucl 3)) _ from
      (Projectivization.map_comp (e' : Eucl 3 →ₗ[ℝ] Eucl 3) e'.injective
        (e : Eucl 3 →ₗ[ℝ] Eucl 3) e.injective).symm]
  congr 1

/-- **Functoriality of the projectivised perturbation**, applied form. -/
lemma projMap_mul (e e' : Eucl 3 ≃L[ℝ] Eucl 3) (c : Projectivization ℝ (Eucl 3)) :
    Projectivization.map (e : Eucl 3 →ₗ[ℝ] Eucl 3) e.injective
        (Projectivization.map (e' : Eucl 3 →ₗ[ℝ] Eucl 3) e'.injective c)
      = Projectivization.map ((e * e' : Eucl 3 ≃L[ℝ] Eucl 3) : Eucl 3 →ₗ[ℝ] Eucl 3)
          (e * e').injective c :=
  congrFun (projMap_mul_comp e e') c

/-- **The key identity on the projective class**: the rotation of the perturbed class is the
perturbed rotation for the conjugated linear part. -/
lemma projMap_conj (t : ℝ) (A : Eucl 3 ≃L[ℝ] Eucl 3) (c : Projectivization ℝ (Eucl 3)) :
    Projectivization.map (diagRotL t : Eucl 3 →ₗ[ℝ] Eucl 3) (diagRotL t).injective
        (Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective c)
      = Projectivization.map
          ((diagRotL t * A * (diagRotL t)⁻¹ : Eucl 3 ≃L[ℝ] Eucl 3) : Eucl 3 →ₗ[ℝ] Eucl 3)
          (diagRotL t * A * (diagRotL t)⁻¹ : Eucl 3 ≃L[ℝ] Eucl 3).injective
          (Projectivization.map (diagRotL t : Eucl 3 →ₗ[ℝ] Eucl 3) (diagRotL t).injective c) := by
  rw [projMap_mul (diagRotL t) A c, projMap_mul (diagRotL t * A * (diagRotL t)⁻¹) (diagRotL t) c]
  exact congrArg (fun e : Eucl 3 ≃L[ℝ] Eucl 3 =>
    Projectivization.map (e : Eucl 3 →ₗ[ℝ] Eucl 3) e.injective c) (by group)

/-- **The transparent coordinates of the LHS** of `rotCapping_linCapping`. -/
lemma cappingSpaceHomeoProj_rotCapping_linCapping (t : ℝ) (A : Eucl 3 ≃L[ℝ] Eucl 3)
    (p : CappingSpace) :
    cappingSpaceHomeoProj (rotCapping ((t : ℝ) : UnitAddCircle) (linCapping A p))
      = ((cappingSpaceHomeoProj p).1,
          projRot t (Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective
            (cappingSpaceHomeoProj p).2)) := by
  rw [cappingSpaceHomeoProj_rotCapping, cappingSpaceHomeoProj_linCapping]

/-- **The transparent coordinates of the RHS** of `rotCapping_linCapping`. -/
lemma cappingSpaceHomeoProj_linCapping_rotCapping (t : ℝ) (A : Eucl 3 ≃L[ℝ] Eucl 3)
    (p : CappingSpace) :
    cappingSpaceHomeoProj
        (linCapping (diagRotL t * A * (diagRotL t)⁻¹)
          (rotCapping ((t : ℝ) : UnitAddCircle) p))
      = ((cappingSpaceHomeoProj p).1,
          Projectivization.map
            ((diagRotL t * A * (diagRotL t)⁻¹ : Eucl 3 ≃L[ℝ] Eucl 3) : Eucl 3 →ₗ[ℝ] Eucl 3)
            (diagRotL t * A * (diagRotL t)⁻¹ : Eucl 3 ≃L[ℝ] Eucl 3).injective
            (projRot t (cappingSpaceHomeoProj p).2)) := by
  rw [cappingSpaceHomeoProj_linCapping, cappingSpaceHomeoProj_rotCapping]

/-- **The perturbations commute with the rotation up to conjugation of the linear part.** -/
theorem rotCapping_linCapping (t : ℝ) (A : Eucl 3 ≃L[ℝ] Eucl 3) :
    rotCapping ((t : ℝ) : UnitAddCircle) ∘ linCapping A
      = linCapping (diagRotL t * A * (diagRotL t)⁻¹)
          ∘ rotCapping ((t : ℝ) : UnitAddCircle) := by
  funext p
  simp only [Function.comp_apply]
  apply cappingSpaceHomeoProj.injective
  rw [cappingSpaceHomeoProj_rotCapping_linCapping, cappingSpaceHomeoProj_linCapping_rotCapping]
  refine Prod.ext rfl ?_
  rw [← projMap_diagRotL t]
  exact projMap_conj t A (cappingSpaceHomeoProj p).2

end Rotation

/-! ## Smoothness of the perturbations -/

section Smooth

set_option linter.style.haveILetI false

/-- **The perturbations are smooth.** -/
theorem contMDiffAt_linCapping (A : Eucl 3 ≃L[ℝ] Eucl 3) (p₀ : CappingSpace) :
    (letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) CappingSpace := cappingCharted
     ContMDiffAt (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (linCapping A) p₀) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) CappingSpace := cappingCharted
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) (ℙ ℝ (Eucl 3)) := projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) (Set.Ioi (0 : ℝ) × ℙ ℝ (Eucl 3)) :=
    halfLineProjectiveCharted
  have hG₀ : ContMDiffAt (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : CappingSpace => cappingSpaceHomeoProj p) p₀ :=
    contMDiffAt_cappingSpaceHomeoProj_charted p₀
  obtain ⟨hrad₀, hproj₀⟩ := (contMDiffAt_halfLineProjective_iff_general (𝓡 4)
    (fun p : CappingSpace => cappingSpaceHomeoProj p) p₀).mp hG₀
  have hG : ContMDiffAt (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : CappingSpace => cappingSpaceHomeoProj (linCapping A p)) p₀ := by
    refine (contMDiffAt_halfLineProjective_iff_general (𝓡 4)
      (fun p : CappingSpace => cappingSpaceHomeoProj (linCapping A p)) p₀).mpr ⟨?_, ?_⟩
    · have hfun : (fun p : CappingSpace =>
            expHomeo.symm ((cappingSpaceHomeoProj (linCapping A p)).1))
          = fun p : CappingSpace => expHomeo.symm ((cappingSpaceHomeoProj p).1) := by
        funext p
        rw [cappingSpaceHomeoProj_linCapping]
      rw [hfun]
      exact hrad₀
    · have hfun : (fun p : CappingSpace => (cappingSpaceHomeoProj (linCapping A p)).2)
          = fun p : CappingSpace => Projectivization.map (A : Eucl 3 →ₗ[ℝ] Eucl 3) A.injective
              (cappingSpaceHomeoProj p).2 := by
        funext p
        rw [cappingSpaceHomeoProj_linCapping]
      rw [hfun]
      exact (contMDiffAt_projMap A (cappingSpaceHomeoProj p₀).2).comp p₀ hproj₀
  exact (chartedStructure_contMDiffWithinAt
    (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    (I' := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    (M := Set.Ioi (0 : ℝ) × ℙ ℝ (Eucl 3)) (M' := CappingSpace)
    (e := cappingSpaceHomeoProj.symm) (Z := CappingSpace) (f := linCapping A) univ p₀).mpr
    (by simpa only [contMDiffWithinAt_univ, Homeomorph.symm_symm] using hG)

/-- **The perturbation `linCapping A` is `C^∞`.** -/
theorem contMDiff_linCapping (A : Eucl 3 ≃L[ℝ] Eucl 3) :
    (letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) CappingSpace := cappingCharted
     ContMDiff (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (linCapping A)) := by
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4)) CappingSpace := cappingCharted
  intro p
  exact contMDiffAt_linCapping A p

end Smooth

end

end Work.Drive
