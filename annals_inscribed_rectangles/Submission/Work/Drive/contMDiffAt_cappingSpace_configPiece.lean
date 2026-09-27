import Mathlib
import Submission.Work.Drive.cappingCharted
import Submission.Work.Drive.lensToProj_confTorus
import Submission.Work.Drive.contMDiffAt_projMk
import Submission.Work.Drive.contMDiffAt_halfLineProjective_iff

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-! ## Auxiliary computations for the configuration piece of the capping space

The statement `Work.Drive.contMDiffAt_cappingSpace_configPiece` is proved by unwinding the
transparent smooth structure `Work.Drive.cappingCharted` of the capping space.  This section
collects the elementary computations that this unwinding needs:

* `Work.Drive.logEucl` and `Work.Drive.expHomeo_symm_apply`: the inverse of the homeomorphism
  `expHomeo : ℝ¹ ≃ₜ (0,∞)` is `Real.log` followed by the linear identification `ℝ ≅ ℝ¹`;
* `Work.Drive.cappingSpaceHomeoProj_confPiece`: the value of the homeomorphism
  `CappingSpace ≃ₜ (0,∞) × ℝP³` on a configuration piece point, obtained from the explicit
  description of `Work.Drive.Φ`;
* `Work.Drive.lensToProj_confPiece`: the sphere lift of a configuration torus point;
* `Work.Drive.contDiffAt_ofComplex` and `Work.Drive.contDiffAt_confProjVecOf`: smoothness of the
  sphere lift `confProjVecOf (u ·) (d ·)`;
* `Work.Drive.contMDiffAt_expHomeo_symm`: the first coordinate is smooth because `Real.log ∘ r`
  is. -/

/-- The linear map `ℝ → ℝ¹` inverse to the linear part of `expHomeo`: the identification of `ℝ`
with the `1`-dimensional Euclidean space used for the radial coordinate of the capping space. -/
def logEucl : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (((EuclideanSpace.equiv (Fin 1) ℝ).symm : (Fin 1 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 1)).comp
    ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm : ℝ →L[ℝ] (Fin 1 → ℝ)))

/-- **The inverse of `expHomeo`**: on `(0,∞)` it is `Real.log` followed by the linear
identification `ℝ ≅ ℝ¹` of `Work.Drive.logEucl`. -/
theorem expHomeo_symm_apply (y : Set.Ioi (0:ℝ)) :
    expHomeo.symm y = logEucl (Real.log (y : ℝ)) := by
  have h : Real.log (y : ℝ) = Real.expOrderIso.symm y := Real.log_of_pos y.2
  rw [h]
  rfl

/-- **The value of `cappingSpaceHomeoProj` on a configuration piece point.**  Since
`Work.Drive.Φ` sends `(r, z, η)` to `(r, [z, η])` (`Work.Drive.toProdConfig`), the value of
`cappingSpaceHomeoProj = Φ` followed by the slice identification `LensSpace ≃ₜ ℝP³` is
`(r, lensToProj [z, η])`. -/
lemma cappingSpaceHomeoProj_confPiece (r : ℝ) (d : ℂ) (η : UnitAddCircle) (hr : 0 < r)
    (hd : ‖d‖ ≤ 1) :
    cappingSpaceHomeoProj
        (Quotient.mk'' (Sum.inl (⟨(r, d, η), hr, hd⟩ : ConfigPiece)) : CappingSpace)
      = (⟨r, hr⟩, lensToProj (Quotient.mk'' (Sum.inr
          ((⟨d, mem_closedBall_of_norm_le_one hd⟩ : Metric.closedBall (0:ℂ) 1), η) :
            CapTorus ⊕ ConfTorus) : LensSpace)) := rfl

/-- **The sphere lift of a configuration torus point**: `lensToProj` of the class of
`(d, η) ∈ D² × S¹` with a chosen square root `u` of `circleOf η` is the projectivisation of the
unit vector `Work.Drive.confProjVecOf u d`. -/
lemma lensToProj_confPiece (d : ℂ) (hd : ‖d‖ ≤ 1) (u : ℂ) (hu : ‖u‖ = 1) :
    lensToProj (Quotient.mk'' (Sum.inr
        ((⟨d, mem_closedBall_of_norm_le_one hd⟩ : Metric.closedBall (0:ℂ) 1),
          circOf (u ^ 2) (by rw [norm_pow, hu]; norm_num)) :
            CapTorus ⊕ ConfTorus) : LensSpace)
      = Projectivization.mk ℝ (confProjVecOf u d) (confProjVecOf_ne_zero hu hd) := by
  have hc : u ^ 2 = circleOf (circOf (u ^ 2) (by rw [norm_pow, hu]; norm_num)) :=
    (circleOf_circOf (u ^ 2) (by rw [norm_pow, hu]; norm_num)).symm
  refine (lensToProj_confTorus (d := (⟨d, mem_closedBall_of_norm_le_one hd⟩ :
        Metric.closedBall (0:ℂ) 1))
      (η := circOf (u ^ 2) (by rw [norm_pow, hu]; norm_num)) hc).trans ?_
  exact projectivizationMk_congr ℝ (Eucl 3)

/-- **Smoothness of the complex-coordinate embedding `ofComplex`.**  The map
`(z, z') ↦ ofComplex z z'` is the ℝ-linear identification of `ℂ²` with `ℝ⁴ = Eucl 3`, so
composing smooth complex-valued maps with it is smooth. -/
lemma contDiffAt_ofComplex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : E → ℂ} {x : E} {n : WithTop ℕ∞}
    (ha : ContDiffAt ℝ n a x) (hb : ContDiffAt ℝ n b x) :
    ContDiffAt ℝ n (fun w => ofComplex (a w) (b w)) x := by
  rw [contDiffAt_piLp]
  intro i
  fin_cases i
  · simp only [ofComplex, WithLp.ofLp_toLp]
    exact (Complex.reCLM.contDiff.contDiffAt).comp x ha
  · simp only [ofComplex, WithLp.ofLp_toLp]
    exact (Complex.imCLM.contDiff.contDiffAt).comp x ha
  · simp only [ofComplex, WithLp.ofLp_toLp]
    exact (Complex.reCLM.contDiff.contDiffAt).comp x hb
  · simp only [ofComplex, WithLp.ofLp_toLp]
    exact (Complex.imCLM.contDiff.contDiffAt).comp x hb

/-- **Smoothness of the sphere lift `confProjVecOf (u ·) (d ·)`.**  The vector
`confProjVecOf u d = (u · √(1 - ‖d‖²/2), ū · d/√2)` is smooth in `(u, d)` as long as `‖d x‖ ≤ 1`,
the only point to note being that `‖d ·‖ ^ 2 = Complex.normSq (d ·)` is a *polynomial* in the real
and imaginary parts of `d` (the norm itself is not smooth at `0`). -/
lemma contDiffAt_confProjVecOf {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u d : E → ℂ} {x : E} {n : WithTop ℕ∞} (hu : ContDiffAt ℝ n u x) (hd : ContDiffAt ℝ n d x)
    (hd1 : ‖d x‖ ≤ 1) :
    ContDiffAt ℝ n (fun w => confProjVecOf (u w) (d w)) x := by
  have hre : ContDiffAt ℝ n (fun w => (d w).re) x :=
    (Complex.reCLM.contDiff.contDiffAt).comp x hd
  have him : ContDiffAt ℝ n (fun w => (d w).im) x :=
    (Complex.imCLM.contDiff.contDiffAt).comp x hd
  have hnorm2 : ContDiffAt ℝ n (fun w => ‖d w‖ ^ 2) x := by
    have h := (hre.mul hre).add (him.mul him)
    have hfun : (fun w => ‖d w‖ ^ 2)
        = fun w => (d w).re * (d w).re + (d w).im * (d w).im := by
      funext w
      rw [Complex.sq_norm, Complex.normSq_apply]
    rw [hfun]
    exact h
  have hinner : ContDiffAt ℝ n (fun w => 1 - ‖d w‖ ^ 2 / 2) x :=
    contDiffAt_const.sub (hnorm2.div_const 2)
  have hpos : (1 - ‖d x‖ ^ 2 / 2) ≠ 0 := by
    have := norm_nonneg (d x)
    nlinarith
  have hsqrt : ContDiffAt ℝ n (fun w => Real.sqrt (1 - ‖d w‖ ^ 2 / 2)) x :=
    (Real.contDiffAt_sqrt hpos).comp x hinner
  have h1 : ContDiffAt ℝ n
      (fun w => u w * ((Real.sqrt (1 - ‖d w‖ ^ 2 / 2) : ℝ) : ℂ)) x :=
    hu.mul ((Complex.ofRealCLM.contDiff.contDiffAt).comp x hsqrt)
  have hstar : ContDiffAt ℝ n (fun w => star (u w)) x :=
    (Complex.conjCLE.contDiff.contDiffAt).comp x hu
  have h2 : ContDiffAt ℝ n
      (fun w => star (u w) * d w / ((Real.sqrt 2 : ℝ) : ℂ)) x :=
    (hstar.mul hd).div_const _
  have := contDiffAt_ofComplex h1 h2
  simpa only [confProjVecOf] using this

/-- **Smoothness of the first (radial) coordinate.**  For a smooth positive `r`, the map
`w ↦ expHomeo.symm ⟨r w, ·⟩` into `ℝ¹` is `C^∞`: this is smoothness of `Real.log ∘ r`, through
`Work.Drive.expHomeo_symm_apply`. -/
lemma contMDiffAt_expHomeo_symm {k : ℕ} {r : EuclideanSpace ℝ (Fin k) → ℝ}
    (hr : ∀ w, 0 < r w) (x₀ : EuclideanSpace ℝ (Fin k))
    (hrs : ContMDiffAt (𝓡 k) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) r x₀) :
    ContMDiffAt (𝓡 k) (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => expHomeo.symm ⟨r w, hr w⟩) x₀ := by
  have hfun : (fun w => expHomeo.symm ⟨r w, hr w⟩) = fun w => logEucl (Real.log (r w)) := by
    funext w
    exact expHomeo_symm_apply ⟨r w, hr w⟩
  rw [hfun, contMDiffAt_iff_contDiffAt]
  exact (logEucl.contDiff.contDiffAt).comp x₀
    ((Real.contDiffAt_log.mpr (ne_of_gt (hr x₀))).comp x₀ hrs.contDiffAt)

end

open Manifold in
open scoped Manifold ContDiff in
/-- **Smoothness of a configuration-piece map into the capping space, from a smooth sphere lift.**
For a map `w ↦ (r w, d w, η w)` into the configuration solid torus, where `r > 0`, `d` lies in the
closed unit disk and `η = circOf (u w ^ 2)` for a smooth **non-vanishing** `u` — i.e. `u` is a smooth
*halving* of the `S¹`-coordinate `η` (`u w ^ 2 = circleOf (η w)`) — the class in
`Work.Drive.CappingSpace` is `C^∞` at `x₀` for the transparent smooth structure
`Work.Drive.cappingCharted` of `Submission/Work/Drive/cappingCharted.lean`.

The point of the statement is that the halving `u` has to be *carried as data*: `lensToProj` on the
configuration torus is `lensToProj ⟦inr (d, η)⟧ = mk ℝ (confProjVecOf u d) ⋯` for `u ^ 2 = circleOf η`
(`Work.Drive.lensToProj_confTorus`), the square root cannot be computed continuously from `η`, and
`mk ℝ (confProjVecOf (u·) (d·))` is smooth exactly because `u` and `d` are
(`Work.Drive.contMDiffAt_projMk`, using `‖u w‖ = 1` for non-vanishing).

Route: `Work.Drive.chartedStructure_contMDiffWithinAt` reduces smoothness into
`(CappingSpace, cappingCharted)` to smoothness of the composite with
`Work.Drive.cappingSpaceHomeoProj`, whose configuration-piece value is
`(⟨r w, ⋯⟩, lensToProj ⟦inr (d w, η w)⟧)` (`Φ` sends a configuration point to `(r, ⟦inr ⋯⟧)` by
`Work.Drive.toProdConfig`, and `Work.Drive.lensToProj_confTorus` applies because
`circleOf (circOf (u w ^ 2)) = u w ^ 2`); the second component is then
`mk ℝ (confProjVecOf (u w) (d w)) ⋯`, smooth by `Work.Drive.contMDiffAt_projMk`, and the first is
smooth in `(0,∞)` because `r` is smooth and positive (the structure on `(0,∞)` is the transport
along `Real.expHomeo`, so this is smoothness of `Real.log ∘ r`).  The product and the model change
(`Work.Drive.contMDiffWithinAt_chartedSpaceChangeModel`) finish. -/
theorem contMDiffAt_cappingSpace_configPiece {k : ℕ}
    (r : EuclideanSpace ℝ (Fin k) → ℝ) (d : EuclideanSpace ℝ (Fin k) → ℂ)
    (u : EuclideanSpace ℝ (Fin k) → ℂ) (x₀ : EuclideanSpace ℝ (Fin k))
    (hr : ∀ w, 0 < r w) (hd : ∀ w, ‖d w‖ ≤ 1) (hu : ∀ w, ‖u w‖ = 1)
    (hrs : ContMDiffAt (𝓡 k) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) r x₀)
    (hds : ContMDiffAt (𝓡 k) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) d x₀)
    (hus : ContMDiffAt (𝓡 k) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) u x₀) :
    letI := Work.Drive.cappingCharted
    ContMDiffAt (𝓡 k) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => (Quotient.mk'' (Sum.inl (⟨(r w, d w, Work.Drive.circOf (u w ^ 2)
        (by rw [norm_pow, hu w]; norm_num)), hr w, hd w⟩ : Work.Drive.ConfigPiece) :
          Work.Drive.ConfigPiece ⊕ Work.Drive.CapPiece) : Work.Drive.CappingSpace)) x₀ := by
  -- the transparent structures entering the definition of `halfLineProjectiveCharted`
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0:ℝ)) :=
    Homeomorph.chartedSpace expHomeo
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    halfLineProjectiveCharted
  -- the map of the statement
  let F : EuclideanSpace ℝ (Fin k) → CappingSpace := fun w =>
    (Quotient.mk'' (Sum.inl (⟨(r w, d w, circOf (u w ^ 2)
      (by rw [norm_pow, hu w]; norm_num)), hr w, hd w⟩ : ConfigPiece) :
        ConfigPiece ⊕ CapPiece) : CappingSpace)
  -- its composite with the homeomorphism onto `(0,∞) × ℝP³`
  let g : EuclideanSpace ℝ (Fin k) →
      Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)) :=
    fun w => cappingSpaceHomeoProj (F w)
  -- the explicit value of `cappingSpaceHomeoProj` on the configuration piece
  have hgconf : ∀ w, cappingSpaceHomeoProj (F w) = (⟨r w, hr w⟩,
      lensToProj (Quotient.mk'' (Sum.inr
        ((⟨d w, mem_closedBall_of_norm_le_one (hd w)⟩ : Metric.closedBall (0:ℂ) 1),
          circOf (u w ^ 2) (by rw [norm_pow, hu w]; norm_num)) :
            CapTorus ⊕ ConfTorus) : LensSpace)) := fun w =>
    cappingSpaceHomeoProj_confPiece (r w) (d w)
      (circOf (u w ^ 2) (by rw [norm_pow, hu w]; norm_num)) (hr w) (hd w)
  -- step 1: transport along `cappingSpaceHomeoProj`
  have hchart : (letI := Work.Drive.cappingCharted
        ContMDiffAt (𝓡 k) 𝓘(ℝ, EuclideanSpace ℝ (Fin 4)) ((⊤ : ℕ∞) : WithTop ℕ∞) F x₀) ↔
      ContMDiffAt (𝓡 k) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) g x₀ := by
    have hiff := chartedStructure_contMDiffWithinAt
      (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      (E' := EuclideanSpace ℝ (Fin k)) (H' := EuclideanSpace ℝ (Fin k))
      (𝓡 k)
      (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
      (M' := CappingSpace) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
      cappingSpaceHomeoProj.symm F Set.univ x₀
    exact hiff
  -- step 2: split the two components of `(0,∞) × ℝP³`
  have hfirst : ContMDiffAt (𝓡 k) (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => expHomeo.symm (g w).1) x₀ := by
    have hg1 : ∀ w, (g w).1 = (⟨r w, hr w⟩ : Set.Ioi (0:ℝ)) := fun w =>
      congrArg Prod.fst (hgconf w)
    have hcomp : (fun w => expHomeo.symm (g w).1)
        = fun w => expHomeo.symm ⟨r w, hr w⟩ := by
      funext w
      rw [hg1 w]
    rw [hcomp]
    exact contMDiffAt_expHomeo_symm hr x₀ hrs
  have hsecond : ContMDiffAt (𝓡 k) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun w => (g w).2) x₀ := by
    have hg2 : ∀ w, (g w).2 = Projectivization.mk ℝ (confProjVecOf (u w) (d w))
        (confProjVecOf_ne_zero (hu w) (hd w)) := fun w =>
      (congrArg Prod.snd (hgconf w)).trans (lensToProj_confPiece (d w) (hd w) (u w) (hu w))
    have hcomp : (fun w => (g w).2)
        = fun w => Projectivization.mk ℝ (confProjVecOf (u w) (d w))
            (confProjVecOf_ne_zero (hu w) (hd w)) := funext hg2
    rw [hcomp]
    exact contMDiffAt_projMk (fun w => confProjVecOf (u w) (d w))
      (fun w => confProjVecOf_ne_zero (hu w) (hd w)) x₀
      (contMDiffAt_iff_contDiffAt.mpr (contDiffAt_confProjVecOf
        (E := EuclideanSpace ℝ (Fin k)) (u := u) (d := d) (x := x₀)
        hus.contDiffAt hds.contDiffAt (hd x₀)))
  have hhl := contMDiffAt_halfLineProjective_iff g x₀
  have hgoal := hhl.mpr ⟨hfirst, hsecond⟩
  exact hchart.mpr hgoal

end Work.Drive
