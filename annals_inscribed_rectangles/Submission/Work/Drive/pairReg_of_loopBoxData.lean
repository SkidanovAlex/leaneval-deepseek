import Mathlib
import Submission.Work.Drive.boxThreeDefs
import Submission.Work.Drive.refTripleClause
import Submission.Work.Drive.mfderiv_cls_surjective
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.clampedSweepLevel
import Submission.Work.Drive.pairRegBricks
import Submission.Work.Drive.boxRegDefs
import Submission.Work.Drive.shadowContinuous
import Submission.Work.Drive.contMDiffAt_halfLineProjective_iff_general
import Submission.Work.Drive.rotCappingSmooth
import Submission.Work.Drive.chartedStructure_contMDiffWithinAt_source

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted Work.Drive.t2Space_cappingSpace Work.Drive.projCharted
local instance : IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) Work.Drive.Ctop (Projectivization ℝ (Work.Drive.Eucl 3)) := Work.Drive.isManifold_projCharted 3
local instance instLineBL' : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0:ℝ)) :=
  Homeomorph.chartedSpace Work.Drive.expHomeo
local instance instHalfLineBL' : ChartedSpace (EuclideanSpace ℝ (Fin 4))
    (Set.Ioi (0:ℝ) × Projectivization ℝ (Work.Drive.Eucl 3)) := Work.Drive.halfLineProjectiveCharted
local instance instProdHalfLineBL' : ChartedSpace
    (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 3))
    (Set.Ioi (0:ℝ) × Projectivization ℝ (Work.Drive.Eucl 3)) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0:ℝ))
    (EuclideanSpace ℝ (Fin 3)) (Projectivization ℝ (Work.Drive.Eucl 3))

/-! ## Elementary bricks -/

/-- `mk2CLM` is onto. -/
lemma mk2CLM_surjective' :
    Function.Surjective (mk2CLM : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2)) := by
  intro y
  refine ⟨WithLp.toLp 2 (![y.ofLp 0, y.ofLp 1, (0 : ℝ)] : Fin 3 → ℝ), ?_⟩
  rw [mk2CLM_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact mk2_eta y

/-- The manifold derivative of the coordinate projection `mk2CLM`. -/
lemma mfderiv_mk2CLM' (x : EuclideanSpace ℝ (Fin 3)) :
    mfderiv (𝓡 3) (𝓡 2) (mk2CLM : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2)) x
      = mk2CLM :=
  (hasMFDerivAt_iff_hasFDerivAt.mpr (ContinuousLinearMap.hasFDerivAt mk2CLM)).mfderiv

/-- The coordinates of `radVec y t` are those of `y`, so `mk2` of them is `y`. -/
lemma mk2_radVec_eta' (y : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    mk2 ((radVec y t).ofLp 0) ((radVec y t).ofLp 1) = y := by
  rw [radVec_apply_zero, radVec_apply_one, mk2_eta]

/-- The radial vector over a point of the square, with parameter in `(0,1)`, lies in the box. -/
lemma radVec_mem_unitBox' {y : EuclideanSpace ℝ (Fin 2)} (hy : y ∈ Submission.Drive.unitBox 1)
    {t : ℝ} (ht : t ∈ Set.Ioo (0:ℝ) 1) : radVec y t ∈ Submission.Drive.unitBox 2 := by
  intro i
  fin_cases i
  · simpa using hy 0
  · simpa using hy 1
  · simpa using ⟨le_of_lt ht.1, le_of_lt ht.2⟩

/-! ## The smoothness of the class map and of the shadow -/

/-- The class projection of the capping space is smooth. -/
theorem contMDiffAt_cls' (p : Work.Drive.CappingSpace) :
    ContMDiffAt (𝓡 4) (𝓡 3) Work.Drive.Ctop
      (Work.Drive.cls : Work.Drive.CappingSpace → Projectivization ℝ (Work.Drive.Eucl 3)) p := by
  have hG := Work.Drive.contMDiffAt_cappingSpaceHomeoProj_charted p
  exact ((Work.Drive.contMDiffAt_halfLineProjective_iff_general (𝓡 4)
    (fun p : Work.Drive.CappingSpace => Work.Drive.cappingSpaceHomeoProj p) p).mp hG).2

/-- The shadow map is smooth. -/
theorem contMDiffAt_shadow' (c : ℝ) (hc : 0 < c) (p : Work.Drive.CappingSpace) :
    ContMDiffAt (𝓡 4) (𝓡 4) Work.Drive.Ctop (Work.Drive.shadow c hc) p := by
  have hkey : (fun y : Work.Drive.CappingSpace => Work.Drive.cappingSpaceHomeoProj
        (Work.Drive.shadow c hc y))
      = fun y => ((⟨c, hc⟩ : Set.Ioi (0:ℝ)), (Work.Drive.cappingSpaceHomeoProj y).2) := by
    funext y
    rw [Work.Drive.shadow, Work.Drive.CapSmooth.cappingSpaceHomeoProj_scaleCapping]
    exact Prod.ext (Subtype.ext (div_mul_cancel₀ c (ne_of_gt (Work.Drive.levelOf_pos y)))) rfl
  have hsm : ContMDiffAt (𝓡 4) (𝓡 4) Work.Drive.Ctop
      (fun y : Work.Drive.CappingSpace => ((⟨c, hc⟩ : Set.Ioi (0:ℝ)),
        (Work.Drive.cappingSpaceHomeoProj y).2)) p := by
    refine (Work.Drive.contMDiffAt_halfLineProjective_iff_general (𝓡 4) _ p).mpr ⟨?_, ?_⟩
    · have hc0 : ContMDiffAt (𝓡 4) (𝓡 1) Work.Drive.Ctop
          (fun _ : Work.Drive.CappingSpace => Work.Drive.expHomeo.symm ⟨c, hc⟩) p :=
        contMDiffAt_const
      simpa only [Prod.fst] using hc0
    · exact contMDiffAt_cls' p
  have hiff := Work.Drive.chartedStructure_contMDiffWithinAt
    (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    (E' := EuclideanSpace ℝ (Fin 4)) (H' := EuclideanSpace ℝ (Fin 4)) (𝓡 4)
    (M := Set.Ioi (0:ℝ) × Projectivization ℝ (Work.Drive.Eucl 3))
    (M' := Work.Drive.CappingSpace) (n := Work.Drive.Ctop)
    Work.Drive.cappingSpaceHomeoProj.symm (Work.Drive.shadow c hc)
    (Set.univ : Set Work.Drive.CappingSpace) p
  rw [← hkey] at hsm
  exact contMDiffWithinAt_univ.mp (hiff.mpr (contMDiffWithinAt_univ.mpr hsm))

/-! ## The main theorem -/

/-- **The pair regularity of two plane presentations, from a loop-versus-sweep meet regularity**
(row 3 of the project lead's `NOTES_LEAD_hodd_blockT6.md` §3, and the `hpair` input of
`Work.Drive.hasClassLinearization_of_endData`).

If the shadow of `A` on the level `lam` meets the clamped sweep of `P` (truncation level `c₂ < lam`,
cutoff `ψ`, and `lam` strictly below the plane levels of `P`) transversally at every meet in the box
(`Work.Drive.LoopBoxData`), then the two class maps `planeClassMap A` and `planeClassMap P` have
*spanning* ranges at every common value with both parameters in the closed unit square
(`Work.Drive.BoxPairReg`).

(The hypothesis `∀ y, lam < levelOf (P y)` is what makes the sweep reach the level `lam`: without it
`hbox` can be vacuous while `BoxPairReg` fails.  Verified by two reviewers of the previous draft, with
the constant-map counterexample.)

Proof (the *chart-free* route, as planned in the original docstring):

1. given `y, y' ∈ unitBox 1` with `planeClassMap A y = planeClassMap P y'`, take the unique
   `t ∈ Ioo 0 1` with `levelOf (clampedSweep c₂ ψ P (radVec y' t)) = lam`
   (`Work.Drive.existsUnique_levelOf_clampedSweep_eq`, with `c₂ < lam < levelOf (P y')`);
2. `shadow lam hlam (A y) = clampedSweep c₂ ψ P (radVec y' t)`: both have level `lam`
   (`levelOf_shadow`, and the choice of `t`) and the same class (`cls_shadow` and
   `cls_clampedSweep` + `mk2 (radVec y' t 0) (radVec y' t 1) = y'`), and `CappingSpace ≃ (0,∞) × ℝP³`
   is injective (`cappingSpaceHomeoProj.injective`);
3. `hbox.1` at this meet gives
   `range (mfderiv (shadow lam hlam ∘ A) y) ⊔ range (mfderiv (clampedSweep c₂ ψ P) (radVec y' t)) = ⊤`
   in the `4`-dimensional capping tangent space;
4. writing `f := mfderiv (𝓡 4) (𝓡 3) cls (shadow lam hlam (A y))` (`Work.Drive.mfderiv_cls_surjective`
   for its surjectivity), the chain rule and `LinearMap.range_comp` express the two class-derivative
   ranges as the images under `f` of the two capping ranges, so that their join is
   `f '' ⊤ = ⊤`.  The extra brick used here is the smoothness of the shadow
   (`Work.Drive.contMDiffAt_shadow'`, from `Work.Drive.continuous_shadow`,
   `CapSmooth.contMDiffAt_scaleCapping` and the smoothness of `levelOf`), which makes the chain rule
   applicable to `shadow lam hlam ∘ A`.  The meet hypothesis enters only through the *sweep's*
   derivative; the vanishing of that derivative when the cutoff is not differentiable at the meet
   parameter is handled by a case split (`mfderiv_zero_of_not_mdifferentiableAt`). -/
theorem pairReg_of_loopBoxData
    (A P : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (hA : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Work.Drive.Ctop A)
    (hP : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Work.Drive.Ctop P)
    (c₂ : ℝ) (hc₂ : 0 < c₂) (lam : ℝ) (hlam : 0 < lam) (hcl : c₂ < lam)
    (ψ : ℝ → ℝ) (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψcont : ContinuousOn ψ (Set.Icc 0 1)) (hψanti : StrictAntiOn ψ (Set.Icc 0 1))
    (hlevlam : ∀ y : EuclideanSpace ℝ (Fin 2), lam < Work.Drive.levelOf (P y))
    (hbox : Work.Drive.LoopBoxData (fun u => Work.Drive.shadow lam hlam (A u))
      (Work.Drive.clampedSweep c₂ ψ P)) :
    Work.Drive.BoxPairReg (Work.Drive.planeClassMap A) (Work.Drive.planeClassMap P) := by
  intro y y' hy hy' hval
  -- names for the shadow map and the sweep
  set S : EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace :=
    fun u => Work.Drive.shadow lam hlam (A u) with hSdef
  set D : EuclideanSpace ℝ (Fin 3) → Work.Drive.CappingSpace :=
    Work.Drive.clampedSweep c₂ ψ P with hDdef
  -- Step 1: the unique interior parameter of the sweep at the level `lam`
  obtain ⟨t, ht, _⟩ := Work.Drive.existsUnique_levelOf_clampedSweep_eq (L := lam) hc₂ hψ0 hψ1
    hψcont hψanti (P := P) (y := y') hcl (hlevlam y')
  obtain ⟨htIoo, htlev⟩ := ht
  set X : EuclideanSpace ℝ (Fin 3) := Work.Drive.radVec y' t with hXdef
  -- Step 2: the two presentations meet at the point of the sweep
  have hz : D X = S y := by
    refine (Homeomorph.injective Work.Drive.cappingSpaceHomeoProj) ?_
    refine Prod.ext ?_ ?_
    · refine Subtype.ext ?_
      show Work.Drive.levelOf (D X) = Work.Drive.levelOf (S y)
      rw [hDdef, hSdef, htlev, Work.Drive.levelOf_shadow]
    · show (Work.Drive.cappingSpaceHomeoProj (D X)).2
        = (Work.Drive.cappingSpaceHomeoProj (S y)).2
      rw [hDdef, hXdef, Work.Drive.cls_clampedSweep]
      have h2 : Work.Drive.mk2 ((Work.Drive.radVec y' t).ofLp 0)
          ((Work.Drive.radVec y' t).ofLp 1) = y' := mk2_radVec_eta' y' t
      rw [h2, hSdef]
      exact ((hval.symm) : (Work.Drive.cappingSpaceHomeoProj (P y')).2
        = (Work.Drive.cappingSpaceHomeoProj (A y)).2).trans
        (Work.Drive.cls_shadow lam hlam (A y)).symm
  -- Step 3: the box membership and the meet spanning
  have hXbox : X ∈ Submission.Drive.unitBox 2 := by
    rw [hXdef]
    exact radVec_mem_unitBox' hy' htIoo
  have hmeet : S y = D X := hz.symm
  have hspan : (mfderiv (𝓡 2) (𝓡 4) S y).toLinearMap.range ⊔
      (mfderiv (𝓡 3) (𝓡 4) D X).toLinearMap.range = ⊤ :=
    hbox.1 y X (by rw [hSdef, hDdef]; exact hmeet) hy hXbox
  -- the class derivative and its surjectivity, at the common point
  have hfsurj : Function.Surjective (mfderiv (𝓡 4) (𝓡 3) Work.Drive.cls (S y)) := by
    have h := Work.Drive.mfderiv_cls_surjective (S y)
    rwa [hSdef] at h
  -- Step 4: the derivative of the `A`-side
  have hSDiff : ContMDiff (𝓡 2) (𝓡 4) Work.Drive.Ctop S := by
    rw [hSdef]
    have hg : ContMDiff (𝓡 4) (𝓡 4) Work.Drive.Ctop (Work.Drive.shadow lam hlam) :=
      fun p => contMDiffAt_shadow' lam hlam p
    simpa only [Function.comp_def] using hg.comp hA
  have hfunA : Work.Drive.planeClassMap A = Work.Drive.cls ∘ S := by
    funext u
    rw [Function.comp_apply, Work.Drive.planeClassMap, Work.Drive.cls_apply, hSdef,
      Work.Drive.cls_shadow]
  have hAchain : mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap A) y
      = (mfderiv (𝓡 4) (𝓡 3) Work.Drive.cls (S y)) ∘L
        (mfderiv (𝓡 2) (𝓡 4) S y) := by
    have hchain := mfderiv_comp (I := 𝓡 2) (I' := 𝓡 4) (I'' := 𝓡 3) (x := y) (f := S)
      (g := Work.Drive.cls)
      ((contMDiffAt_cls' (S y)).mdifferentiableAt (by simp))
      ((hSDiff.contMDiffAt).mdifferentiableAt (by simp))
    rw [← hchain, hfunA]
  have hAeq : (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap A) y).toLinearMap.range
      = Submodule.map (mfderiv (𝓡 4) (𝓡 3) Work.Drive.cls (S y)).toLinearMap
          (mfderiv (𝓡 2) (𝓡 4) S y).toLinearMap.range := by
    have h := congrArg (fun (L : TangentSpace (𝓡 2) y →L[ℝ]
        TangentSpace (𝓡 3) (Work.Drive.cls (S y))) => L.toLinearMap.range) hAchain
    rw [h]
    exact LinearMap.range_comp _ _
  -- Step 5: the derivative of the `P`-side
  have hfunP : (fun w : EuclideanSpace ℝ (Fin 3) => Work.Drive.planeClassMap P (mk2CLM w))
      = Work.Drive.cls ∘ D := by
    funext w
    rw [Function.comp_apply, Work.Drive.planeClassMap, Work.Drive.cls_apply, mk2CLM_apply, hDdef,
      Work.Drive.cls_clampedSweep]
  have hmkpt : mk2CLM X = y' := by
    rw [mk2CLM_apply, hXdef, radVec_apply_zero, radVec_apply_one, mk2_eta]
  -- the class of the common point, in the two notations
  have hzcls : Work.Drive.cls (D X) = Work.Drive.cls (S y) := by
    rw [hz]
  by_cases hDdiff : MDifferentiableAt (𝓡 3) (𝓡 4) D X
  · -- both chain rules
    have hmkdiff : MDifferentiableAt (𝓡 3) (𝓡 2)
        (mk2CLM : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2)) X :=
      (ContinuousLinearMap.hasFDerivAt mk2CLM).differentiableAt.mdifferentiableAt
    have hPdiff : MDifferentiableAt (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap P) (mk2CLM X) := by
      have h1 : MDifferentiableAt (𝓡 2) (𝓡 4) P (mk2CLM X) :=
        (hP.contMDiffAt).mdifferentiableAt (by simp)
      have h2 : MDifferentiableAt (𝓡 4) (𝓡 3) Work.Drive.cls (P (mk2CLM X)) :=
        (contMDiffAt_cls' (P (mk2CLM X))).mdifferentiableAt (by simp)
      exact h2.comp (mk2CLM X) h1
    have hchainMk : mfderiv (𝓡 3) (𝓡 3)
        (fun w : EuclideanSpace ℝ (Fin 3) => Work.Drive.planeClassMap P (mk2CLM w)) X
        = (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap P) y') ∘L
          (mk2CLM : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2)) := by
      have h := mfderiv_comp (I := 𝓡 3) (I' := 𝓡 2) (I'' := 𝓡 3) (x := X)
        (f := (mk2CLM : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 2)))
        (g := Work.Drive.planeClassMap P) hPdiff hmkdiff
      rw [hmkpt, mfderiv_mk2CLM'] at h
      exact h
    have hchainSweep : mfderiv (𝓡 3) (𝓡 3) (Work.Drive.cls ∘ D) X
        = (mfderiv (𝓡 4) (𝓡 3) Work.Drive.cls (S y)) ∘L
          (mfderiv (𝓡 3) (𝓡 4) D X) := by
      have h := mfderiv_comp (I := 𝓡 3) (I' := 𝓡 4) (I'' := 𝓡 3) (x := X) (f := D)
        (g := Work.Drive.cls)
        ((contMDiffAt_cls' (D X)).mdifferentiableAt (by simp)) hDdiff
      rw [hz] at h
      exact h
    have hPchain : mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap P) y' ∘L mk2CLM
        = (mfderiv (𝓡 4) (𝓡 3) Work.Drive.cls (S y)) ∘L
          (mfderiv (𝓡 3) (𝓡 4) D X) := by
      rw [← hchainMk, hfunP, hchainSweep]
    -- the range identity
    let mk2L : TangentSpace (𝓡 3) X →ₗ[ℝ] TangentSpace (𝓡 2) y' :=
      (mk2CLM : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2)).toLinearMap
    have hmk2Lsurj : Function.Surjective ⇑mk2L := mk2CLM_surjective'
    have hstep1 : (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap P) y').toLinearMap.range
        = ((mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap P) y').toLinearMap.comp mk2L).range := by
      rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr hmk2Lsurj, Submodule.map_top]
    have hstep2 : ((mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap P) y').toLinearMap.comp
            mk2L).range
        = (((mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap P) y') ∘L
            (mk2CLM : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2))).toLinearMap).range :=
      rfl
    have hstep3 : (((mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap P) y') ∘L
            (mk2CLM : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 2))).toLinearMap).range
        = (((mfderiv (𝓡 4) (𝓡 3) Work.Drive.cls (S y)) ∘L
            (mfderiv (𝓡 3) (𝓡 4) D X)).toLinearMap).range :=
      congrArg (fun (L : TangentSpace (𝓡 3) X →L[ℝ] TangentSpace (𝓡 3)
          (Work.Drive.cls (S y))) => L.toLinearMap.range) hPchain
    have hPeq : (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap P) y').toLinearMap.range
        = Submodule.map (mfderiv (𝓡 4) (𝓡 3) Work.Drive.cls (S y)).toLinearMap
            (mfderiv (𝓡 3) (𝓡 4) D X).toLinearMap.range :=
      hstep1.trans (hstep2.trans (hstep3.trans (LinearMap.range_comp _ _)))
    -- assemble
    rw [hAeq, hPeq]
    have h2 : Submodule.map (mfderiv (𝓡 4) (𝓡 3) Work.Drive.cls (S y)).toLinearMap
          (mfderiv (𝓡 2) (𝓡 4) S y).toLinearMap.range ⊔
        Submodule.map (mfderiv (𝓡 4) (𝓡 3) Work.Drive.cls (S y)).toLinearMap
          (mfderiv (𝓡 3) (𝓡 4) D X).toLinearMap.range
        = Submodule.map (mfderiv (𝓡 4) (𝓡 3) Work.Drive.cls (S y)).toLinearMap
            ((mfderiv (𝓡 2) (𝓡 4) S y).toLinearMap.range ⊔
              (mfderiv (𝓡 3) (𝓡 4) D X).toLinearMap.range) :=
      (Submodule.map_sup _ _ _).symm
    rw [h2, hspan, Submodule.map_top, LinearMap.range_eq_top.mpr hfsurj]
  · -- the sweep is not differentiable: its derivative vanishes, so the shadow alone spans
    have h0 : (mfderiv (𝓡 3) (𝓡 4) D X).toLinearMap = 0 := by
      rw [mfderiv_zero_of_not_mdifferentiableAt hDdiff]
      rfl
    have hp2 : (mfderiv (𝓡 3) (𝓡 4) D X).toLinearMap.range = ⊥ := by
      rw [h0, LinearMap.range_zero]
    have hp1 : (mfderiv (𝓡 2) (𝓡 4) S y).toLinearMap.range = ⊤ := by
      have h := hspan
      rw [hp2] at h
      simpa using h
    have hAtop : (mfderiv (𝓡 2) (𝓡 3) (Work.Drive.planeClassMap A) y).toLinearMap.range = ⊤ := by
      rw [hAeq, hp1, Submodule.map_top, LinearMap.range_eq_top.mpr hfsurj]
    rw [hAtop]
    exact top_sup_eq _

end

end Work.Drive
