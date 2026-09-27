import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.meetBoxEngine
import Submission.Work.Drive.geometricLocality
import Submission.Work.Drive.eventually_ncard_meetBox_eq_fam
import Submission.Work.Drive.chartIsSmooth
import Submission.Work.Drive.sweepPertSurj_of_chartPert
import Submission.Work.Drive.sideGerm_parity_local
import Submission.Work.Drive.parityFamDefs

/-!
# The count of a good configuration is locally constant (the brick behind `sideGerm`)

At a `GoodPair` the box count `coreSideCount` is the mod-`2` pairing of the loop with the sweep's
image, so it is locally constant in the deformation — in particular its parity is.  This file proves
that statement in the two-parameter form the germ route consumes:

> `Work.Drive.CntAt Ξ Q c w (A + τ) = CntAt Ξ Q c w A` in parity, for `τ` in a *ball* around `0` of the
> configuration space `𝔼^m × 𝔼^m` (the loop's chart perturbation and the sweep's chart perturbation
> are independent).

## The proof

The engine `Work.Drive.eventually_ncard_meetBox_eq_manifold`
(`Submission/Work/Drive/sideGerm_parity_local.lean`) gives the local constancy of the *number* of
parameter meets of a loop against a `3`-chain in the `4`-manifold `CappingSpace` for a family moving
with a parameter in a finite-dimensional space, provided

* the two curve families are jointly `C^∞` in the parameter and the curve parameter (`hL`, `hD`),
* the base meet set of the configuration `A` is finite, interior in the box, and transverse.

The base data is exactly the `GoodPair` clause of `Work.Drive.GoodAt Ξ Q c w A`; the smoothness of the
loop family is `Work.Drive.parityLoopFam_contMDiff`, and the smoothness of the sweep family is the one
new ingredient proved here (`Work.Drive.contMDiff_parityChainFam`).

For the sweep, the point is the *factorisation*

> `clampedSweep c ψ P x = dil c (ψ (x 2)) (P (x 0, x 1))`,  `dil c a q = scaleCapping (pos (exp (a (log c - log (levelOf q))))) q`

(`Work.Drive.clampedSweep_eq_dil`, definitional): the sweep is the *power dilation* `dil c (1 - x 2)`
applied to the plane's point at `(x 0, x 1)`.  Both factors are then smooth jointly in the
configuration parameter and the box parameter: the point is a composite of `Ξ`, `Q` and the disk
parametrisation of the rotated plane, and the joint smoothness of `dil`
(`Work.Drive.contMDiffAt_dil_uncurry`) is read off in the transparent coordinates
`(0,∞) × ℝP³` of the capping space, where the dilation is
`(a, q) ↦ (exp (a (log c - log (levelOf q))) * levelOf q, class q)` — smooth because `log ∘ levelOf` is
(`Work.Drive.contMDiffAt_logLevelOf`) and the arithmetic operations are.
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 1000000

noncomputable section

/-! ## 1. The clamped sweep as a power dilation, and the joint smoothness of the dilation -/

/-- **The radial sweep is the power dilation of its plane point**: definitionally,
`clampedSweep c ψ P x = dil c (ψ (x 2)) (P (x 0, x 1))`. -/
lemma clampedSweep_eq_dil (c : ℝ) (ψ : ℝ → ℝ) (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (x : EuclideanSpace ℝ (Fin 3)) :
    clampedSweep c ψ P x = dil c (ψ (x 2)) (P (mk2 (x 0) (x 1))) := rfl

/-- **The power dilation is `C^∞` jointly in the exponent and the point.**  The point here is that the
statement is *joint*: the level coordinate of `dil c a q` is
`a (log c - log (levelOf q)) + log (levelOf q)`, smooth in `(a, q)` because `log ∘ levelOf` is
(`Work.Drive.contMDiffAt_logLevelOf`), and the class coordinate does not move. -/
theorem contMDiffAt_dil_uncurry (c a₀ : ℝ) (q₀ : CappingSpace) :
    ContMDiffAt ((𝓘(ℝ,ℝ)).prod (𝓡 4)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℝ × CappingSpace => dil c z.1 z.2) (a₀, q₀) := by
  have hsnd : ContMDiffAt ((𝓘(ℝ,ℝ)).prod (𝓡 4)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℝ × CappingSpace => z.2) (a₀, q₀) := contMDiffAt_snd
  rw [← contMDiffWithinAt_univ]
  refine (chartedStructure_contMDiffWithinAt (I := 𝓡 4) (I' := (𝓘(ℝ,ℝ)).prod (𝓡 4))
    (M := Set.Ioi (0:ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
    (M' := CappingSpace) (e := cappingSpaceHomeoProj.symm) (Z := ℝ × CappingSpace)
    (f := fun z : ℝ × CappingSpace => dil c z.1 z.2) Set.univ (a₀, q₀)).mpr ?_
  rw [contMDiffWithinAt_univ]
  refine (contMDiffAt_halfLineProjective_iff_general ((𝓘(ℝ,ℝ)).prod (𝓡 4))
    (fun z : ℝ × CappingSpace => cappingSpaceHomeoProj (dil c z.1 z.2)) (a₀, q₀)).mpr ⟨?_, ?_⟩
  · -- the level coordinate, in the exponential chart, is `a (log c - log l) + log l`
    have hfun : (fun z : ℝ × CappingSpace =>
        expHomeo.symm ((cappingSpaceHomeoProj (dil c z.1 z.2)).1))
        = fun z : ℝ × CappingSpace =>
            logEucl (z.1 * (Real.log c - Real.log (levelOf z.2)) + Real.log (levelOf z.2)) := by
      funext z
      rw [expHomeo_symm_apply]
      show logEucl (Real.log (levelOf (dil c z.1 z.2))) = _
      rw [dil_level, Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt (levelOf_pos z.2)),
        Real.log_exp]
    rw [hfun]
    have hlog : ContMDiffAt ((𝓘(ℝ,ℝ)).prod (𝓡 4)) 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : ℝ × CappingSpace => Real.log (levelOf z.2)) (a₀, q₀) :=
      (contMDiffAt_logLevelOf q₀).comp (f := fun z : ℝ × CappingSpace => z.2) (a₀, q₀) hsnd
    have hg : ContMDiffAt ((𝓘(ℝ,ℝ)).prod (𝓡 4)) 𝓘(ℝ,ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : ℝ × CappingSpace =>
          z.1 * (Real.log c - Real.log (levelOf z.2)) + Real.log (levelOf z.2)) (a₀, q₀) :=
      ((contMDiffAt_fst.mul (contMDiffAt_const.sub hlog)).add hlog)
    exact (logEucl.contMDiff.contMDiffAt (x := a₀ * (Real.log c - Real.log (levelOf q₀))
      + Real.log (levelOf q₀))).comp (a₀, q₀) hg
  · -- the class coordinate does not depend on the exponent
    have hfun : (fun z : ℝ × CappingSpace => (cappingSpaceHomeoProj (dil c z.1 z.2)).2)
        = fun z : ℝ × CappingSpace => (cappingSpaceHomeoProj z.2).2 := by
      funext z; rw [dil, cls_scaleCapping]
    rw [hfun]
    exact (contMDiffAt_classProj q₀).comp (f := fun z : ℝ × CappingSpace => z.2) (a₀, q₀) hsnd

/-- The pointwise form above, as a global statement. -/
theorem contMDiff_dil_uncurry (c : ℝ) :
    ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 4)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℝ × CappingSpace => dil c z.1 z.2) :=
  fun z => contMDiffAt_dil_uncurry c z.1 z.2

/-! ## 2. Joint smoothness of the sweep family -/

/-- **The sweep family of the germ count is jointly `C^∞`** in the configuration parameter
(independent perturbations of the loop's and the sweep's chart, of which only the second is used here)
and the chain parameter.

Proof: `clampedSweep c (1 - ·) P x = dil c (1 - x 2) (P (x 0, x 1))`
(`Work.Drive.clampedSweep_eq_dil`), the plane point `P (x 0, x 1) = rotPresentation (Ξ (A.2 + u.2) ∘ Q) w (x 0, x 1)`
is smooth by composing `Ξ`, `Q` and the disk parametrisation, and `dil` is smooth jointly by
`Work.Drive.contMDiff_dil_uncurry`. -/
theorem contMDiff_parityChainFam {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle)
    (hΞ : ChartPert Q m Ξ) (hQ : IsChartData Q)
    (A : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    ContMDiff
      (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) × EuclideanSpace ℝ (Fin 3)))
      (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
          × EuclideanSpace ℝ (Fin 3) => parityChainFam Ξ Q c w A q.1 q.2) := by
  -- the plane point of the rotated perturbed chart
  have hG : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
        × EuclideanSpace ℝ (Fin 3))) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
          × EuclideanSpace ℝ (Fin 3) =>
        rotPresentation (pertChart Ξ Q (A.2 + q.1.2)) w (mk2 (q.2 0) (q.2 1))) := by
    have hQpart : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
          × EuclideanSpace ℝ (Fin 3))) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
            × EuclideanSpace ℝ (Fin 3) => diskPlane Q (mk2 (q.2 0) (q.2 1))) := by
      refine (contMDiff_diskPlane hQ.1).comp ?_
      have hmk : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
            × EuclideanSpace ℝ (Fin 3) => mk2CLM q.2) := by fun_prop
      refine contMDiff_iff_contDiff.mpr ?_
      simpa [mk2CLM_apply] using hmk
    have hfst : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
          × EuclideanSpace ℝ (Fin 3))) (𝓡 m) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
            × EuclideanSpace ℝ (Fin 3) => A.2 + q.1.2) :=
      contMDiff_iff_contDiff.mpr (by fun_prop)
    have hpair := hfst.prodMk hQpart
    have hmain := hΞ.2.1.comp hpair
    have hrot := (contMDiff_rotCappingAngle w).comp hmain
    refine hrot.congr (fun q => ?_)
    simp only [Function.comp_def, rotPresentation, diskPlane, pertChart]
  -- the exponent and the plane point, paired
  have hφ : ContMDiff (𝓘(ℝ, (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
        × EuclideanSpace ℝ (Fin 3))) (𝓘(ℝ,ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
          × EuclideanSpace ℝ (Fin 3) => 1 - q.2 2) :=
    contMDiff_iff_contDiff.mpr (by fun_prop)
  have hcomp := (contMDiff_dil_uncurry c).comp (hφ.prodMk hG)
  refine hcomp.congr (fun q => ?_)
  simp only [Function.comp_def, parityChainFam, clampedSweep_eq_dil]

/-! ## 3. The main theorem -/

/-- **The count is locally constant in parity at a good configuration.**  For every `GoodAt`
configuration `A` there is a ball around `0` in the two-parameter perturbation space on which the
parity of the count `CntAt Ξ Q c w` is constant. -/
theorem sideGerm_count_localconst {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace) (c : ℝ) (hΞ : Work.Drive.ChartPert Q m Ξ)
    (hQ : Work.Drive.IsChartData Q)
    (w : UnitAddCircle) (A : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (hA : Work.Drive.GoodAt Ξ Q c w A) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ τ₁ τ₂ : EuclideanSpace ℝ (Fin m),
      ‖τ₁‖ < ρ → ‖τ₂‖ < ρ →
        Odd (Work.Drive.CntAt Ξ Q c w (A.1 + τ₁, A.2 + τ₂)) = Odd (Work.Drive.CntAt Ξ Q c w A) := by
  classical
  -- the base data of the good configuration, read at the base parameter `A + 0` of the family
  have hA0 : GoodAt Ξ Q c w (A + 0) := by simpa using hA
  obtain ⟨-, -, hfin0, hint0, htrans0⟩ := hA0
  have hfin : (meetBox (parityLoopFam Ξ Q A 0) (parityChainFam Ξ Q c w A 0)).Finite := hfin0
  have hint : ∀ p ∈ meetBox (parityLoopFam Ξ Q A 0) (parityChainFam Ξ Q c w A 0),
      p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ i : Fin 3, p.2 i ∈ Set.Ioo (0 : ℝ) 1 := hint0
  have htrans : ∀ p ∈ meetBox (parityLoopFam Ξ Q A 0) (parityChainFam Ξ Q c w A 0),
      LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (parityLoopFam Ξ Q A 0) p.1).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (parityChainFam Ξ Q c w A 0) p.2).toLinearMap = ⊤ :=
    htrans0
  -- the local constancy of the *number* of meets, from the engine
  have hEv := eventually_ncard_meetBox_eq_manifold
    (P := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (parityLoopFam Ξ Q A) (parityChainFam Ξ Q c w A)
    (parityLoopFam_contMDiff Ξ Q hΞ hQ A) (contMDiff_parityChainFam Ξ Q c w hΞ hQ A)
    hfin hint htrans
  obtain ⟨η, hη, hsub⟩ := Metric.mem_nhds_iff.mp hEv
  refine ⟨η, hη, fun τ₁ τ₂ hτ₁ hτ₂ => ?_⟩
  -- the two independent perturbations are the point `(τ₁, τ₂)` of the parameter space
  have hnorm : ‖((τ₁, τ₂) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))‖ < η := by
    rw [Prod.norm_def]
    exact max_lt hτ₁ hτ₂
  have hEq := hsub (by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hnorm)
  -- identify the two ends with the counts of the statement
  have hleft : CntAt Ξ Q c w (A.1 + τ₁, A.2 + τ₂)
      = (meetBox (parityLoopFam Ξ Q A (τ₁, τ₂))
          (parityChainFam Ξ Q c w A (τ₁, τ₂))).ncard :=
    CntAt_eq_ncard_meetBox Ξ Q c w A (τ₁, τ₂)
  have hright : CntAt Ξ Q c w A
      = (meetBox (parityLoopFam Ξ Q A 0) (parityChainFam Ξ Q c w A 0)).ncard := by
    simpa using CntAt_eq_ncard_meetBox Ξ Q c w A 0
  rw [hleft, hright]
  exact congrArg Odd hEq

end

end Work.Drive
