import Mathlib
import Submission.Work.Drive.diskPlaneInjectivity
import Submission.Work.Drive.clampedSweep_injOn_unitBox
import Submission.Work.Drive.chartPertTransfer

namespace Work.Drive

open Manifold Set
open scoped Manifold ContDiff Topology
attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

/-! ## The interior form of the injectivity of the clamped radial sweep

`Work.Drive.clampedSweep_injOn_unitBox` proves the injectivity of the clamped radial sweep
`clampedSweep c ψ P` on the **closed** parameter box `[0,1]³` from two hypotheses on the *closed*
square `[0,1]²`: the class-injectivity of the presentation `P` and the avoidance of the truncation
level `c`.  For a plane chart the first hypothesis holds only on the **interior** of the square (the
disk presentation `diskPlane` identifies the antipodal boundary points of the square — that is the
seam of the box), so the statement below restricts both hypotheses, and the conclusion, to the strict
interior.  The proof is the same three-step argument (classes agree; the radial coordinates then
force `ψ (x 2) = ψ (x' 2)`; `ψ` injective), with every use of the two hypotheses checked to take
interior arguments. -/

/-- **Injectivity of the clamped radial sweep on the interior of the box**, from the two hypotheses
restricted to the interior square.  (`{x | ∀ i, x i ∈ Ioo 0 1}` is the strict interior of
`Submission.Drive.unitBox 2`, and likewise in dimension `1`.) -/
theorem clampedSweep_injOn_interiorBox {c : ℝ} (hc : 0 < c) {ψ : ℝ → ℝ}
    (hψ : Set.InjOn ψ (Set.Icc (0 : ℝ) 1))
    {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hcls : ∀ y, (∀ i, y i ∈ Set.Ioo (0 : ℝ) 1) →
      ∀ y', (∀ i, y' i ∈ Set.Ioo (0 : ℝ) 1) →
        (cappingSpaceHomeoProj (P y)).2 = (cappingSpaceHomeoProj (P y')).2 → y = y')
    (hlev : ∀ y, (∀ i, y i ∈ Set.Ioo (0 : ℝ) 1) → levelOf (P y) ≠ c) :
    Set.InjOn (clampedSweep c ψ P)
      {x : EuclideanSpace ℝ (Fin 3) | ∀ i, x i ∈ Set.Ioo (0 : ℝ) 1} := by
  intro x hx x' hx' heq
  -- ## Step 1: the two plane points have the same projective class, hence coincide
  have hy : ∀ i, (mk2 (x 0) (x 1)) i ∈ Set.Ioo (0 : ℝ) 1 := by
    intro i; fin_cases i
    · simpa using hx 0
    · simpa using hx 1
  have hy' : ∀ i, (mk2 (x' 0) (x' 1)) i ∈ Set.Ioo (0 : ℝ) 1 := by
    intro i; fin_cases i
    · simpa using hx' 0
    · simpa using hx' 1
  have hclass : (cappingSpaceHomeoProj (P (mk2 (x 0) (x 1)))).2
      = (cappingSpaceHomeoProj (P (mk2 (x' 0) (x' 1)))).2 := by
    rw [← cappingSpaceHomeoProj_clampedSweep_snd c ψ P x, heq,
      cappingSpaceHomeoProj_clampedSweep_snd c ψ P x']
  have hyy : mk2 (x 0) (x 1) = mk2 (x' 0) (x' 1) := hcls _ hy _ hy' hclass
  have hx0 : x 0 = x' 0 := by
    have h := congrArg (fun u : EuclideanSpace ℝ (Fin 2) => u 0) hyy
    simpa using h
  have hx1 : x 1 = x' 1 := by
    have h := congrArg (fun u : EuclideanSpace ℝ (Fin 2) => u 1) hyy
    simpa using h
  -- ## Step 2: the scale factors agree, whence `ψ (x 2) = ψ (x' 2)` and `x 2 = x' 2`
  have hlog : Real.log c - Real.log (levelOf (P (mk2 (x' 0) (x' 1)))) ≠ 0 := by
    intro h0
    have h1 : Real.log c = Real.log (levelOf (P (mk2 (x' 0) (x' 1)))) := sub_eq_zero.mp h0
    have h2 : c = levelOf (P (mk2 (x' 0) (x' 1))) :=
      Real.log_injOn_pos (Set.mem_Ioi.mpr hc) (Set.mem_Ioi.mpr (levelOf_pos _)) h1
    exact hlev _ hy' h2.symm
  have hscale : clampScale c ψ P x = clampScale c ψ P x' := by
    have h := congrArg levelOf heq
    rw [levelOf_clampedSweep, levelOf_clampedSweep, hyy] at h
    exact mul_right_cancel₀ (ne_of_gt (levelOf_pos (P (mk2 (x' 0) (x' 1))))) h
  have hψeq : ψ (x 2) = ψ (x' 2) := by
    have h := hscale
    rw [clampScale, clampScale, hyy] at h
    exact mul_right_cancel₀ hlog (Real.exp_injective h)
  have hx2 : x 2 = x' 2 :=
    hψ ⟨(hx 2).1.le, (hx 2).2.le⟩ ⟨(hx' 2).1.le, (hx' 2).2.le⟩ hψeq
  -- ## Step 3: conclude
  rw [WithLp.ext_iff]
  funext i
  fin_cases i
  · exact hx0
  · exact hx1
  · exact hx2

/-! ## The perturbed linear reference plane

`Q z = chartPert τ (linPlaneChart φ lam hlam z)` is the linear reference plane of the level `lam`,
presented by the disk model of `ℝP²` and then displaced by the chart perturbation `chartPert τ`.  Its
two structural facts (used below) are that all its points have the *same* level `exp (log lam + τ 0)`
(the perturbation scales the level `lam` by `exp (τ 0)`), and that its class-injectivity off the seam
is that of `linPlaneChart`, transported along the injective `chartPert τ`. -/

/-- **The level of the perturbed linear plane chart**: the *constant* `exp (log lam + τ 0)`. -/
private lemma levelOf_chartPert_linPlaneChart (φ : Eucl 3 ≃L[ℝ] Eucl 3) (τ : Eucl 3) (lam : ℝ)
    (hlam : 0 < lam) (z : ℂ) :
    levelOf (chartPert τ (linPlaneChart φ lam hlam z)) = Real.exp (Real.log lam + τ 0) := by
  rw [levelOf_chartPert, levelScale_apply]
  have h : levelOf (linPlaneChart φ lam hlam z) = lam := level_linPlaneChart φ lam hlam z
  simp only [h]

/-- **The level of the perturbed linear reference plane**, read through the disk presentation. -/
private lemma levelOf_diskPlane_chartPert (φ : Eucl 3 ≃L[ℝ] Eucl 3) (τ : Eucl 3) (lam : ℝ)
    (hlam : 0 < lam) (y : EuclideanSpace ℝ (Fin 2)) :
    levelOf (diskPlane (fun z : ℂ => chartPert τ (linPlaneChart φ lam hlam z)) y)
      = Real.exp (Real.log lam + τ 0) := by
  rw [diskPlane_apply]
  exact levelOf_chartPert_linPlaneChart φ τ lam hlam _

/-- **The class of the perturbed linear reference plane** is the `classMap τ`-image of the class of
the linear plane chart at the corresponding disk point. -/
private lemma cls_diskPlane_chartPert (φ : Eucl 3 ≃L[ℝ] Eucl 3) (τ : Eucl 3) (lam : ℝ)
    (hlam : 0 < lam) (y : EuclideanSpace ℝ (Fin 2)) :
    (cappingSpaceHomeoProj
        (diskPlane (fun z : ℂ => chartPert τ (linPlaneChart φ lam hlam z)) y)).2
      = classMap τ ((cappingSpaceHomeoProj (linPlaneChart φ lam hlam (sqDisk (foldBox y)))).2) := by
  rw [diskPlane_apply, cappingSpaceHomeoProj_chartPert, coordFam_snd]

/-- **The level estimate**: for `τ` of norm `< log 2` the perturbed level `exp (log lam + τ 0)` stays
above `c₂`.  Indeed `exp (log lam + τ 0) = lam * exp (τ 0) ≥ lam * exp (-‖τ‖) > lam * (1/2)`, because
`‖τ‖ < log 2` gives `exp (-‖τ‖) > exp (-log 2) = 1/2`. -/
private lemma exp_log_add_gt {lam c₂ : ℝ} (hlam : 0 < lam) (hc₂lam : c₂ < lam / 2)
    {τ : Eucl 3} (hτ : ‖τ‖ < Real.log 2) : c₂ < Real.exp (Real.log lam + τ 0) := by
  have hτle : -‖τ‖ ≤ τ 0 := by
    have h := PiLp.norm_apply_le τ (0 : Fin 4)
    rw [Real.norm_eq_abs] at h
    linarith [neg_abs_le (τ 0)]
  have hexp : (1 : ℝ) / 2 < Real.exp (τ 0) := by
    have h1 : Real.exp (-‖τ‖) ≤ Real.exp (τ 0) := Real.exp_le_exp.mpr hτle
    have h2 : (1 : ℝ) / 2 < Real.exp (-‖τ‖) := by
      have h3 : -Real.log 2 < -‖τ‖ := by linarith
      calc (1 : ℝ) / 2 = Real.exp (-Real.log 2) := by
            rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]; norm_num
        _ < Real.exp (-‖τ‖) := Real.exp_lt_exp.mpr h3
    linarith
  rw [Real.exp_add, Real.exp_log hlam]
  nlinarith [Real.exp_pos (τ 0)]

/-- **The interior injectivity of the swept cone over a perturbed linear reference plane.**  (The
closed-box form is FALSE: `diskPlane` identifies the antipodal boundary points of the square, so the
sweep is 2-to-1 on the seam of the box; every meet of the design lies in the strict interior, where
there is no seam.)  On the interior of the parameter box the three ingredients of the sweep's
injectivity hold: `diskPlane (chartPert τ ∘ linPlaneChart φ lam)` is injective on the (open) square
(`Work.Drive.diskPlane_injOn_interior_of_seamInjOn` fed by `Work.Drive.linPlaneChart_eq_iff` through the
injective `chartPert τ`), its level is the *constant* `exp (log lam + τ 0) > lam/2 > c₂`, and
`t ↦ 1 - t` is injective.  The proof is the interior variant of `Work.Drive.clampedSweep_injOn_unitBox`
(whose existing form asks the two hypotheses on the whole closed box; inline the same argument with the
hypotheses restricted to the interior). -/
theorem mixedSweep_injOn {φ : Eucl 3 ≃L[ℝ] Eucl 3} {lam c₂ : ℝ} (hlam : 0 < lam)
    (hc₂ : 0 < c₂) (hc₂lam : c₂ < lam / 2) {τ : Eucl 3} (hτ : ‖τ‖ < Real.log 2) :
    Set.InjOn (Work.Drive.clampedSweep c₂ (fun t => 1 - t)
      (Work.Drive.diskPlane (fun z : ℂ =>
        Work.Drive.chartPert τ (Work.Drive.linPlaneChart φ lam hlam z))))
      {x : EuclideanSpace ℝ (Fin 3) | ∀ i, x i ∈ Set.Ioo (0 : ℝ) 1} := by
  have hest : c₂ < Real.exp (Real.log lam + τ 0) := exp_log_add_gt hlam hc₂lam hτ
  refine clampedSweep_injOn_interiorBox (c := c₂) (ψ := fun t => 1 - t)
    (P := diskPlane (fun z : ℂ => chartPert τ (linPlaneChart φ lam hlam z))) hc₂ ?_ ?_ ?_
  · intro a ha b _ h
    linarith
  · -- the class-injectivity on the interior square, off the seam
    intro y hy y' hy' hcl
    have hQ : ∀ z z' : ℂ, ‖z‖ ≤ 1 → ‖z'‖ ≤ 1 →
        chartPert τ (linPlaneChart φ lam hlam z) = chartPert τ (linPlaneChart φ lam hlam z') →
        z = z' ∨ (‖z‖ = 1 ∧ z' = -z) := by
      intro z z' hz hz' h
      have h' : linPlaneChart φ lam hlam z = linPlaneChart φ lam hlam z' :=
        chartPert_injective τ h
      rcases (linPlaneChart_eq_iff φ lam hlam hz hz').mp h' with hzz | ⟨h1, -, h3⟩
      · exact Or.inl hzz
      · exact Or.inr ⟨h1, h3⟩
    have hlvl : levelOf (diskPlane (fun z : ℂ => chartPert τ (linPlaneChart φ lam hlam z)) y)
        = levelOf (diskPlane (fun z : ℂ => chartPert τ (linPlaneChart φ lam hlam z)) y') := by
      rw [levelOf_diskPlane_chartPert φ τ lam hlam y, levelOf_diskPlane_chartPert φ τ lam hlam y']
    have hpt : diskPlane (fun z : ℂ => chartPert τ (linPlaneChart φ lam hlam z)) y
        = diskPlane (fun z : ℂ => chartPert τ (linPlaneChart φ lam hlam z)) y' :=
      cappingSpaceHomeoProj.injective (Prod.ext (Subtype.ext hlvl) hcl)
    exact diskPlane_injOn_interior_of_seamInjOn
      (fun z : ℂ => chartPert τ (linPlaneChart φ lam hlam z)) hQ hy hy' hpt
  · -- the level of the presentation is the constant `exp (log lam + τ 0) ≠ c₂`
    intro y _
    rw [levelOf_diskPlane_chartPert φ τ lam hlam y]
    exact ne_of_gt hest

end Work.Drive
