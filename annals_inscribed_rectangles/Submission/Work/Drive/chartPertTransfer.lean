import Mathlib
import Submission.Work.Drive.chartPertData
import Submission.Work.Drive.linearPlaneChart
import Submission.Work.Drive.referenceClassCount
import Submission.Work.Drive.CapSmooth.sweepChainSmooth

/-!
# Transfer of the data of a chart along the perturbation `chartPert`

`Work.Drive.chartPert τ : CappingSpace → CappingSpace` acts, in the transparent coordinates
`cappingSpaceHomeoProj`, as `(level ↦ levelScale τ level, class ↦ classMap τ class)`.  This file
collects the elementary transfer lemmas of that action that a perturbed chart statement consumes:
the level of a perturbed point, the monotonicity/injectivity of `levelScale`, the injectivity of the
action, the transport of the projective plane `projLine (linSub φ)` under `classMap τ`, and the
transport of the functional `linFun`.

They are the interface of the lead's item (ii) (`odd_coreSideCountPt_reference_chartPert`): the
reference factor `(F1)` of `hn2` is transported along `chartPert` verbatim, with the level scaled and
the functional `φ` replaced by `φ.trans (classEquiv τ)`.
-/

namespace Work.Drive

open scoped Manifold ContDiff LinearAlgebra.Projectivization

noncomputable section

open Work.Drive.CapSmooth

/-! ## The level -/

/-- The value of `expHomeo : ℝ¹ ≃ₜ (0,∞)` is `Real.exp` of the (single) coordinate. -/
theorem expHomeo_apply (x : EuclideanSpace ℝ (Fin 1)) :
    ((expHomeo x : Set.Ioi (0 : ℝ)) : ℝ) = Real.exp (x 0) := by
  simp [expHomeo, Real.coe_expOrderIso_apply]

/-- The inverse of `expHomeo`, read as the coordinate projection of `ℝ¹`. -/
theorem euclLog_apply (x : EuclideanSpace ℝ (Fin 1)) : euclLog x = x 0 := by
  simp [euclLog, EuclideanSpace.equiv, ContinuousLinearEquiv.coe_coe]

/-- **The value of the perturbed level**: `levelScale τ r = exp (log r + τ 0)`. -/
theorem levelScale_apply (t : Eucl 3) (r : Set.Ioi (0 : ℝ)) :
    ((levelScale t r : Set.Ioi (0 : ℝ)) : ℝ) = Real.exp (Real.log (r : ℝ) + t 0) := by
  rw [levelScale, expHomeo_apply]
  have h1 : ((expHomeo.symm r + t 0 • (e1 : EuclideanSpace ℝ (Fin 1))) 0)
      = (expHomeo.symm r) 0 + t 0 := by
    simp [e1, PiLp.add_apply, PiLp.smul_apply]
  rw [h1]
  have h2 : (expHomeo.symm r) 0 = Real.log (r : ℝ) := by
    rw [expHomeo_symm_apply, ← euclLog_apply]
    exact euclLog_logEucl _
  rw [h2]

/-- The perturbed level is monotone in the level. -/
theorem levelScale_le_iff (t : Eucl 3) (r r' : Set.Ioi (0 : ℝ)) :
    ((levelScale t r : Set.Ioi (0 : ℝ)) : ℝ) ≤ ((levelScale t r' : Set.Ioi (0 : ℝ)) : ℝ)
      ↔ (r : ℝ) ≤ (r' : ℝ) := by
  rw [levelScale_apply, levelScale_apply, Real.exp_le_exp]
  constructor
  · intro h
    exact (Real.log_le_log_iff r.2 r'.2).mp (by linarith)
  · intro h
    have := (Real.log_le_log_iff r.2 r'.2).mpr h
    linarith

/-- The perturbed level is *strictly* monotone in the level. -/
theorem levelScale_lt_iff (t : Eucl 3) (r r' : Set.Ioi (0 : ℝ)) :
    ((levelScale t r : Set.Ioi (0 : ℝ)) : ℝ) < ((levelScale t r' : Set.Ioi (0 : ℝ)) : ℝ)
      ↔ (r : ℝ) < (r' : ℝ) := by
  rw [levelScale_apply, levelScale_apply, Real.exp_lt_exp]
  constructor
  · intro h
    exact (Real.log_lt_log_iff r.2 r'.2).mp (by linarith)
  · intro h
    have := (Real.log_lt_log_iff r.2 r'.2).mpr h
    linarith

/-- The perturbed level is injective. -/
theorem levelScale_injective (t : Eucl 3) : Function.Injective (levelScale t) := by
  intro r r' h
  have hh : ((levelScale t r : Set.Ioi (0 : ℝ)) : ℝ)
      = ((levelScale t r' : Set.Ioi (0 : ℝ)) : ℝ) := by rw [h]
  refine Subtype.ext (le_antisymm ?_ ?_)
  · exact (levelScale_le_iff t r r').mp (le_of_eq hh)
  · exact (levelScale_le_iff t r' r).mp (le_of_eq hh.symm)

/-- **The level of a perturbed point.** -/
theorem levelOf_chartPert (t : Eucl 3) (p : CappingSpace) :
    levelOf (chartPert t p)
      = ((levelScale t ⟨levelOf p, levelOf_pos p⟩ : Set.Ioi (0 : ℝ)) : ℝ) := by
  rw [levelOf, cappingSpaceHomeoProj_chartPert, coordFam]
  rfl

/-! ## The injectivity of the action -/

/-- The class action `classMap τ` is injective. -/
theorem classMap_injective (t : Eucl 3) : Function.Injective (classMap t) :=
  Projectivization.map_injective _ (classEquiv t).injective

/-- The coordinate action `coordFam τ` is injective. -/
theorem coordFam_injective (t : Eucl 3) : Function.Injective (coordFam t) := by
  intro x y h
  have h1 : levelScale t x.1 = levelScale t y.1 := by
    have := congrArg Prod.fst h
    simpa [coordFam] using this
  have h2 : classMap t x.2 = classMap t y.2 := by
    have := congrArg Prod.snd h
    simpa [coordFam] using this
  exact Prod.ext (levelScale_injective t h1) (classMap_injective t h2)

/-- **The chart perturbation `chartPert τ` is injective.** -/
theorem chartPert_injective (t : Eucl 3) : Function.Injective (chartPert t) := by
  intro p q h
  have h' : coordFam t (cappingSpaceHomeoProj p) = coordFam t (cappingSpaceHomeoProj q) := by
    have := congrArg cappingSpaceHomeoProj h
    rwa [cappingSpaceHomeoProj_chartPert, cappingSpaceHomeoProj_chartPert] at this
  exact cappingSpaceHomeoProj.injective (coordFam_injective t h')

/-! ## The transport of the plane, the functional and the class of the core loop -/

/-- **The functional of a perturbed linear plane is the same functional**: this is the identity that
makes the transport of `(F1)` along `chartPert` a pure transport. -/
theorem linFun_trans_classEquiv (φ : Eucl 3 ≃L[ℝ] Eucl 3) (τ v : Eucl 3) :
    linFun (φ.trans (classEquiv τ)) (classEquiv τ v) = linFun φ v := by
  rw [linFun_apply, linFun_apply]
  have h : (φ.trans (classEquiv τ)).symm (classEquiv τ v) = φ.symm v := by
    refine (φ.trans (classEquiv τ)).injective ?_
    rw [ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply]
  rw [h]

/-- **The projective plane of a perturbed linear plane is the `classMap τ`-image of the original
one**, in membership form: this is the transport of the class data of a perturbed chart. -/
theorem mem_projLine_classMap_iff (φ : Eucl 3 ≃L[ℝ] Eucl 3) (τ : Eucl 3)
    (p : Projectivization ℝ (Eucl 3)) :
    classMap τ p ∈ projLine (linSub (φ.trans (classEquiv τ))) ↔ p ∈ projLine (linSub φ) := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [classMap_mk, mk_mem_projLine_iff _ (classEquiv_ne_zero hv),
      mk_mem_projLine_iff _ hv, linFun_trans_classEquiv]

/-- **The class of the core loop of a perturbed chart is the `classMap τ`-image of the class of the
core loop of the chart.** -/
theorem class_coreLoop_chartPert (τ : Eucl 3) (Q : ℂ → CappingSpace) (t : ℝ) :
    (cappingSpaceHomeoProj (coreLoop (chartPert τ ∘ Q) t)).2
      = classMap τ ((cappingSpaceHomeoProj (coreLoop Q t)).2) := by
  simp only [coreLoop_eq, Function.comp_apply, cappingSpaceHomeoProj_chartPert, coordFam_snd]

end

end Work.Drive
