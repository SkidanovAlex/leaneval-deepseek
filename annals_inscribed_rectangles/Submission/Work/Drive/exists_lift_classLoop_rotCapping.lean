import Mathlib
import Submission.Work.Drive.planeChartDefs
import Submission.Work.Drive.sideCountDefs
import Submission.Work.Drive.cappedPlaneFamily
import Submission.Work.Drive.seamEssentiality
import Submission.Work.Drive.exists_nonvanishing_lift_projCharted
import Submission.Work.Drive.cappingSpaceHomeoProj_rotCapping
import Submission.Work.Drive.projRot
import Submission.Work.Drive.classImageGraphData
import Submission.Work.Drive.rotSweepEquivariance

/-!
# A smooth nonvanishing lift of the class loop of the rotated plane chart

`Work.Drive.coreLoop Q t = Q (exp (i pi t))` is the *core loop* of a disk presentation `Q : ℂ →
CappingSpace` of a plane: its parameter interval `[0,1]` closes up (`coreLoop Q 1 = coreLoop Q 0`,
because of the chart's seam clause `Q (-z) = Q z`), and it is the generator of the plane's `H₁`.
Reading it in the model `Y = (0,∞) × ℝP³` (`Work.Drive.cappingSpaceHomeoProj`) gives a loop in `ℝP³`,
whose **essentiality** is that no *nonvanishing continuous* lift of it to `ℝ⁴` closes up:

> `V 1 = κ • V 0` with `κ < 0`.

This file produces, for the **rotated** chart `z ↦ rotCapping u (Q z)` and every angle `u : UnitAddCircle`,
a lift `V : ℝ → ℝ⁴` of that class loop which is

* `C^∞` and nowhere vanishing on **all** of `ℝ` (not merely on the parameter interval), and
* closed up with a *negative* factor.

**The witness.**  The seam lift `Work.Drive.seamLift γ : ℝ → ℝ⁴` (`seamEssentiality.lean`) is the sphere
lift of the class of the seam chord of `γ` at the angular parameter `θ`, and it satisfies
`seamLift γ (θ + π) = - seamLift γ θ` (`seamLift_add_pi`) and
`[seamLift γ θ] = class of Q at exp θ` (`cls_seamLift`).  Since `coreLoopArg t = exp (i π t)`, the map

> `θ ↦ seamLift γ (π t)`

is the desired lift of the *base* chart's class loop — with the sign closed up by `κ = -1`, the cleanest
possible essentiality — and the rotation is applied to it by the diagonal rotation
`Work.Drive.diagRot u` of `ℂ² = ℝ⁴`, whose projectivisation is `Work.Drive.projRot u`
(`projRot_mk`, `cappingSpaceHomeoProj_rotCapping`).  The rotation is linear, so it preserves both the
nonvanishing and the sign `V 1 = - V 0`.

The only new ingredient is the smoothness of `θ ↦ seamLift γ θ` (only its *continuity* was recorded in
the workspace): the seam parameters `seamParam θ = (θ + π/2, θ - π/2)` stay at distance `π`, hence
`stripHalf`/`stripData` are smooth there (`contDiffAt_stripHalf`, `contMDiffAt_stripData_snd`, the
hypothesis `stripA ≠ 0` being met by `stripA_ne_zero`), and the sphere lift `confProjVecOf` is smooth
along them (`contDiffAt_confProjVecOf'`).

This is the input of `Work.Drive.exists_lift_classLoop_rotCapping`'s consumer in
`F1_GENERICITY_RESOLUTION.md` (the reference factor `(F1)` of `hn2`).
-/

namespace Work.Drive

/-- **The seam lift is `C^∞` in its parameter.**

`seamLift γ θ = confProjVecOf (stripHalf γ (seamParam θ)) ((stripData γ (seamParam θ)).2.1)` is a
composite of the smooth affine map `θ ↦ seamParam θ`, the two smooth strip coordinate functions
(smooth at the seam parameters because the two chord endpoints differ by `π`, so they are distinct, and
because `stripA γ ≠ 0` by `stripA_ne_zero`) and the smooth sphere lift `confProjVecOf` (smooth where its
second argument has norm `< √2`, which holds since `‖(stripData γ w).2.1‖ ≤ 1`).  Only the *continuity*
of the seam lift was recorded in the workspace (`continuous_seamLift`); this is the stronger form. -/
private lemma contDiff_seamLift {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun θ : ℝ => seamLift γ θ) := by
  rw [contDiff_iff_contDiffAt]
  intro θ
  -- the seam parameters depend smoothly on `θ`
  have hsp : ContDiffAt ℝ Ctop (seamParam) θ := by
    have h : (fun θ : ℝ => WithLp.toLp 2 (![θ + Real.pi / 2, θ - Real.pi / 2] : Fin 2 → ℝ))
        = seamParam := rfl
    rw [← h, contDiffAt_piLp (p := 2) (E := fun _ : Fin 2 => ℝ)]
    intro i
    fin_cases i
    · show ContDiffAt ℝ Ctop (fun θ : ℝ => θ + Real.pi / 2) θ
      exact (contDiff_id.add contDiff_const).contDiffAt
    · show ContDiffAt ℝ Ctop (fun θ : ℝ => θ - Real.pi / 2) θ
      exact (contDiff_id.sub contDiff_const).contDiffAt
  -- the two strip coordinates at the seam parameters
  have hU : ContDiffAt ℝ Ctop (fun θ : ℝ => stripHalf γ (seamParam θ)) θ :=
    (contDiffAt_stripHalf hγ (seamParam_exp_ne θ)).comp θ hsp
  have hD : ContDiffAt ℝ Ctop (fun θ : ℝ => (stripData γ (seamParam θ)).2.1) θ :=
    (contMDiffAt_iff_contDiffAt.mp
      (contMDiffAt_stripData_snd hγ (stripA_ne_zero hγne (seamParam θ)))).comp θ hsp
  -- the sphere lift is smooth there: its second argument lies in the unit disk
  have hne : 1 - ‖(stripData γ (seamParam θ)).2.1‖ ^ 2 / 2 ≠ 0 := by
    have h1 : ‖(stripData γ (seamParam θ)).2.1‖ ≤ 1 := by
      simpa only [stripData] using
        confOf_snd_norm_le_one (Submission.Configuration.muOrd γ
          (Circle.exp ((seamParam θ) 0), Circle.exp ((seamParam θ) 1)))
    intro h0
    nlinarith [norm_nonneg ((stripData γ (seamParam θ)).2.1), h1]
  show ContDiffAt ℝ Ctop (fun θ => confProjVecOf (stripHalf γ (seamParam θ))
    ((stripData γ (seamParam θ)).2.1)) θ
  exact contDiffAt_confProjVecOf' hU hD hne

/-- **A `C^∞`, nowhere vanishing lift of the class loop of the rotated plane chart, closed up with
negative factor.**

For a smooth embedded plane curve `γ` avoiding the origin, a plane chart `Q` of `γ` and an angle
`u : UnitAddCircle`, there is a `C^∞` nowhere vanishing `V : ℝ → ℝ⁴` whose projective class is the class
of the core loop of the rotated chart `z ↦ rotCapping u (Q z)` on `[0,1]`, and whose endpoints satisfy
`V 1 = κ • V 0` with `κ < 0` — the essentiality of the class loop.

The witness is `V t = diagRot u (seamLift γ (π t))`: the seam lift has the right class (`cls_seamLift`),
is `C^∞` (`contDiff_seamLift`) and nonzero (`seamLift_ne_zero`), and `seamLift γ (θ + π) = - seamLift γ θ`
gives `V 1 = - V 0` (the diagonal rotation is linear).  The rotation acts on the class by `projRot u`
(`projRot_mk`) and on the capping space by the `ℝP³` coordinate alone
(`cappingSpaceHomeoProj_rotCapping`). -/
theorem exists_lift_classLoop_rotCapping {γ : Circle → ℝ × ℝ}
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → Work.Drive.CappingSpace} (hQ : Work.Drive.IsPlaneChart γ hγne Q)
    (u : UnitAddCircle) :
    ∃ V : ℝ → EuclideanSpace ℝ (Fin 4), ∃ hVne : ∀ t : ℝ, V t ≠ 0,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 1,
        Projectivization.mk ℝ (V t) (hVne t)
          = (Work.Drive.cappingSpaceHomeoProj
              (Work.Drive.coreLoop (fun z => Work.Drive.rotCapping u (Q z)) t)).2) ∧
      ∃ κ : ℝ, κ < 0 ∧ V 1 = κ • V 0 := by
  have hseam : ContDiff ℝ Ctop (fun θ : ℝ => seamLift γ θ) := contDiff_seamLift hγ hγne
  -- choose a real representative of the rotation angle
  obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective u
  have ht' : ((t : ℝ) : UnitAddCircle) = u := ht
  rw [← ht']
  refine ⟨fun s => diagRot t (seamLift γ (Real.pi * s)), ?_, ?_, ?_, -1, by norm_num, ?_⟩
  · -- nowhere vanishing
    intro s
    exact diagRot_ne_zero t (seamLift_ne_zero hγ _)
  · -- smoothness of the witness
    have hinner : ContDiff ℝ Ctop (fun s : ℝ => (t, seamLift γ (Real.pi * s))) := by
      refine (contDiff_prod_iff _).mpr ⟨?_, ?_⟩
      · simpa [Function.comp_def] using (contDiff_const (c := t) : ContDiff ℝ Ctop (fun _ : ℝ => t))
      · simpa [Function.comp_def] using hseam.comp (contDiff_const.mul contDiff_id)
    simpa [Function.comp_def] using contDiff_diagRot.comp hinner
  · -- the class of the witness is the class of the rotated loop
    intro s hs
    have hseamcls : Projectivization.mk ℝ (seamLift γ (Real.pi * s))
        (seamLift_ne_zero hγ (Real.pi * s))
        = (cappingSpaceHomeoProj
            (Q (Complex.exp (↑Real.pi * (↑s : ℂ) * Complex.I)))).2 := by
      have h := cls_seamLift hγ hγne hQ (Real.pi * s)
      rw [show ((Circle.exp (Real.pi * s) : Circle) : ℂ)
          = Complex.exp (↑Real.pi * (↑s : ℂ) * Complex.I) from by
        rw [Circle.coe_exp]; congr 1; push_cast; ring] at h
      exact h
    have hcp : (cappingSpaceHomeoProj
        (rotCapping ((t : ℝ) : UnitAddCircle)
          (Q (Complex.exp (↑Real.pi * (↑s : ℂ) * Complex.I))))).2
        = projRot t
            ((cappingSpaceHomeoProj (Q (Complex.exp (↑Real.pi * (↑s : ℂ) * Complex.I)))).2) := by
      simpa using congrArg Prod.snd (cappingSpaceHomeoProj_rotCapping t
        (Q (Complex.exp (↑Real.pi * (↑s : ℂ) * Complex.I))))
    show Projectivization.mk ℝ (diagRot t (seamLift γ (Real.pi * s))) _
        = (cappingSpaceHomeoProj
            (coreLoop (fun z => rotCapping ((t : ℝ) : UnitAddCircle) (Q z)) s)).2
    rw [show coreLoop (fun z => rotCapping ((t : ℝ) : UnitAddCircle) (Q z)) s
        = rotCapping ((t : ℝ) : UnitAddCircle)
            (Q (Complex.exp (↑Real.pi * (↑s : ℂ) * Complex.I))) from rfl]
    rw [hcp]
    exact (projRot_mk t (seamLift γ (Real.pi * s))
      (seamLift_ne_zero hγ (Real.pi * s))).symm.trans (congrArg (projRot t) hseamcls)
  · -- the negative closure of the witness
    have hneg : diagRot t (-(seamLift γ 0)) = -diagRot t (seamLift γ 0) := by
      rw [← neg_one_smul ℝ (seamLift γ 0), diagRot_smul, neg_one_smul]
    show diagRot t (seamLift γ (Real.pi * 1)) = (-1 : ℝ) • diagRot t (seamLift γ (Real.pi * 0))
    rw [show Real.pi * 1 = 0 + Real.pi by ring, show Real.pi * 0 = 0 by ring,
      seamLift_add_pi, hneg, neg_one_smul]

end Work.Drive
