import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Submission.Work.Elliptic.PsiStar_ode
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false

/-! ## Auxiliary material for `Phi_derivs` -/

namespace Aux

/-- The open neighbourhood of the closed quadrant on which `SmoothNbhd` gives smoothness. -/
def PhiU : Set (ℝ × ℝ) := Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π/2 + 1)

theorem isOpen_U : IsOpen PhiU := isOpen_Ioi.prod isOpen_Ioo

theorem mem_U {z θ : ℝ} : (z, θ) ∈ PhiU ↔ -1 < z ∧ -1 < θ ∧ θ < π/2 + 1 := by
  simp [PhiU, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]

/-- The slice `x ↦ w x θ` of a function differentiable on `ℝ × ℝ` is differentiable. -/
theorem differentiableAt_slice {w : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry w) (z, θ)) :
    DifferentiableAt ℝ (fun x => w x θ) z := by
  have hfd : HasFDerivAt (Function.uncurry w) (fderiv ℝ (Function.uncurry w) (z, θ)) (z, θ) :=
    h.hasFDerivAt
  have hcurve : HasFDerivAt (fun x : ℝ => (x, θ)) (ContinuousLinearMap.inl ℝ ℝ ℝ) z :=
    hasFDerivAt_prodMk_left z θ
  exact (hfd.comp z hcurve).differentiableAt

theorem hasDerivAt_slice {w : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : DifferentiableAt ℝ (Function.uncurry w) (z, θ)) :
    HasDerivAt (fun x => w x θ) (Work.Spaces.pz w z θ) z :=
  (differentiableAt_slice h).hasDerivAt

/-- Differentiation under the integral sign over the angular interval `Iθ`: if the integrand and
its `z`-derivative are jointly continuous on `[z-ε,z+ε] × Iθ` and the `z`-derivative exists
pointwise there, then the integral is differentiable at `z`. -/
theorem hasDerivAt_integral_theta_backup {F F' : ℝ → ℝ → ℝ} {z ε : ℝ} (hε : 0 < ε)
    (hF : ContinuousOn (fun p : ℝ × ℝ => F p.1 p.2)
      (Set.Icc (z - ε) (z + ε) ×ˢ Work.Spaces.Iθ))
    (hF' : ContinuousOn (fun p : ℝ × ℝ => F' p.1 p.2)
      (Set.Icc (z - ε) (z + ε) ×ˢ Work.Spaces.Iθ))
    (hd : ∀ x ∈ Set.Icc (z - ε) (z + ε), ∀ θ ∈ Work.Spaces.Iθ,
      HasDerivAt (fun x' => F x' θ) (F' x θ) x) :
    HasDerivAt (fun x => ∫ θ in Work.Spaces.Iθ, F x θ)
      (∫ θ in Work.Spaces.Iθ, F' z θ) z := by
  set s : Set ℝ := Set.Icc (z - ε) (z + ε) with hs_def
  have hzs : z ∈ s := ⟨by linarith, by linarith⟩
  have hsmem : s ∈ 𝓝 z := Icc_mem_nhds (by linarith) (by linarith)
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_Icc.prod isCompact_Icc) hF'
  have hFslice : ∀ x ∈ s, ContinuousOn (fun θ => F x θ) Work.Spaces.Iθ := by
    intro x hx
    exact hF.comp ((continuous_const.prodMk continuous_id).continuousOn)
      (fun θ hθ => ⟨hx, hθ⟩)
  have hF'slice : ∀ x ∈ s, ContinuousOn (fun θ => F' x θ) Work.Spaces.Iθ := by
    intro x hx
    exact hF'.comp ((continuous_const.prodMk continuous_id).continuousOn)
      (fun θ hθ => ⟨hx, hθ⟩)
  have hFmeas : ∀ᶠ x in 𝓝 z, AEStronglyMeasurable (F x) (volume.restrict Work.Spaces.Iθ) := by
    filter_upwards [hsmem] with x hx
    exact (hFslice x hx).aestronglyMeasurable measurableSet_Icc
  have hFint : Integrable (F z) (volume.restrict Work.Spaces.Iθ) :=
    ContinuousOn.integrableOn_compact isCompact_Icc (hFslice z hzs)
  have hF'meas : AEStronglyMeasurable (F' z) (volume.restrict Work.Spaces.Iθ) :=
    (hF'slice z hzs).aestronglyMeasurable measurableSet_Icc
  have hIθmeas : MeasurableSet Work.Spaces.Iθ :=
    show MeasurableSet (Set.Icc (0 : ℝ) (π/2)) from measurableSet_Icc
  have hbdd : ∀ᵐ a ∂(volume.restrict Work.Spaces.Iθ), ∀ x ∈ s, ‖F' x a‖ ≤ C := by
    filter_upwards [MeasureTheory.ae_restrict_mem hIθmeas] with a ha x hx
    exact hC (x, a) ⟨hx, ha⟩
  have hbint : Integrable (fun _ : ℝ => C) (volume.restrict Work.Spaces.Iθ) :=
    ContinuousOn.integrableOn_compact isCompact_Icc continuousOn_const
  have hderiv : ∀ᵐ a ∂(volume.restrict Work.Spaces.Iθ), ∀ x ∈ s,
      HasDerivAt (fun x' => F x' a) (F' x a) x := by
    filter_upwards [MeasureTheory.ae_restrict_mem hIθmeas] with a ha x hx
    exact hd x hx a ha
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict Work.Spaces.Iθ)
      (F := F) (F' := F') (x₀ := z) (s := s) (bound := fun _ => C)
      hsmem hFmeas hFint hF'meas hbdd hbint hderiv).2

/-- `Work.Spaces.pz v` is smooth on the open neighbourhood `PhiU` of the closed quadrant, whenever
`v` is smooth there. -/
theorem contDiffOn_pz_backup {v : ℝ → ℝ → ℝ} (hs : Work.Spaces.SmoothNbhd v) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => Work.Spaces.pz v p.1 p.2) PhiU := by
  have hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry v) PhiU := hs.of_le le_top
  have hdiff : DifferentiableOn ℝ (Function.uncurry v) PhiU :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_U).1 hG).1
  have hGf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry v) p) PhiU :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_U).1 hG).2
  have hZ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry v) p) ((1 : ℝ), (0 : ℝ))) PhiU :=
    hGf.clm_apply contDiffOn_const
  refine hZ.congr fun p hp => ?_
  have hd : HasFDerivAt (Function.uncurry v) (fderiv ℝ (Function.uncurry v) p) p :=
    (hdiff.differentiableAt (isOpen_U.mem_nhds hp)).hasFDerivAt
  have hcurve : HasFDerivAt (fun x : ℝ => (x, p.2)) (ContinuousLinearMap.inl ℝ ℝ ℝ) p.1 :=
    hasFDerivAt_prodMk_left p.1 p.2
  have hder := (hd.comp p.1 hcurve).hasDerivAt
  have hval : deriv (fun x => (Function.uncurry v) (x, p.2)) p.1
      = (fderiv ℝ (Function.uncurry v) p) ((1 : ℝ), (0 : ℝ)) := by
    rw [show (fun x => (Function.uncurry v) (x, p.2))
        = Function.uncurry v ∘ fun x : ℝ => (x, p.2) from by funext x; rfl]
    rw [hder.deriv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  show deriv (fun x => (Function.uncurry v) (x, p.2)) p.1
      = (fderiv ℝ (Function.uncurry v) p) ((1 : ℝ), (0 : ℝ))
  exact hval

end Aux

/-- The second `z`-derivative of a smooth function is smooth on `Aux.PhiU`. -/
theorem contDiffOn_pzIter_two {v : ℝ → ℝ → ℝ} (hs : Work.Spaces.SmoothNbhd v) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 v p.1 p.2) Aux.PhiU := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => Work.Spaces.pz v p.1 p.2) Aux.PhiU := Aux.contDiffOn_pz_backup hs
  have hd1 : DifferentiableOn ℝ (fun q : ℝ × ℝ => Work.Spaces.pz v q.1 q.2) Aux.PhiU :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen Aux.isOpen_U).1 h1).1
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => fderiv ℝ (fun q : ℝ × ℝ => Work.Spaces.pz v q.1 q.2) p) Aux.PhiU :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen Aux.isOpen_U).1 h1).2
  have h3 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × ℝ => (fderiv ℝ (fun q : ℝ × ℝ => Work.Spaces.pz v q.1 q.2) p)
        ((1 : ℝ), (0 : ℝ))) Aux.PhiU :=
    h2.clm_apply contDiffOn_const
  refine h3.congr fun p hp => ?_
  have hd : HasFDerivAt (fun q : ℝ × ℝ => Work.Spaces.pz v q.1 q.2)
      (fderiv ℝ (fun q : ℝ × ℝ => Work.Spaces.pz v q.1 q.2) p) p :=
    (hd1.differentiableAt (Aux.isOpen_U.mem_nhds hp)).hasFDerivAt
  have hcurve : HasFDerivAt (fun x : ℝ => (x, p.2)) (ContinuousLinearMap.inl ℝ ℝ ℝ) p.1 :=
    hasFDerivAt_prodMk_left p.1 p.2
  have hder := (hd.comp p.1 hcurve).hasDerivAt
  have hval : deriv (fun x => Work.Spaces.pz v x p.2) p.1
      = (fderiv ℝ (fun q : ℝ × ℝ => Work.Spaces.pz v q.1 q.2) p) ((1 : ℝ), (0 : ℝ)) := by
    rw [show (fun x => Work.Spaces.pz v x p.2)
        = (fun q : ℝ × ℝ => Work.Spaces.pz v q.1 q.2) ∘ fun x : ℝ => (x, p.2) from by
          funext x; rfl]
    rw [hder.deriv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  exact hval

/-- The first two `z`-derivatives of the angular `L²`-mass `Φ z = ∫_θ (v z θ)² dθ` of a
`SmoothNbhd` function, obtained by differentiating under the integral sign. -/
theorem Phi_derivs (v : ℝ → ℝ → ℝ) (hs : Work.Spaces.SmoothNbhd v) :
    (∀ z ∈ Set.Ioi (-1 : ℝ), HasDerivAt (fun z' => ∫ θ in Work.Spaces.Iθ, (v z' θ) ^ 2)
      (2 * (∫ θ in Work.Spaces.Iθ, v z θ * Work.Spaces.pz v z θ)) z) ∧
    (∀ z ∈ Set.Ioi (-1 : ℝ),
      HasDerivAt (fun z' => 2 * (∫ θ in Work.Spaces.Iθ, v z' θ * Work.Spaces.pz v z' θ))
        (2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz v z θ) ^ 2)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 v z θ * v z θ)) z) := by
  have hvc : ContinuousOn (Function.uncurry v)
      (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1) (π/2 + 1)) := hs.continuousOn
  have hpzc : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz v p.1 p.2)
      (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1) (π/2 + 1)) := (Aux.contDiffOn_pz_backup hs).continuousOn
  have hpz2c : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 v p.1 p.2)
      (Set.Ioi (-1 : ℝ) ×ˢ Set.Ioo (-1) (π/2 + 1)) := (contDiffOn_pzIter_two hs).continuousOn
  constructor
  · intro z hz
    have hz1 : (-1 : ℝ) < z := hz
    have hε : 0 < (z + 1) / 2 := by linarith
    have hzs : z ∈ Set.Icc (z - (z + 1) / 2) (z + (z + 1) / 2) := ⟨by linarith, by linarith⟩
    have hsU : Set.Icc (z - (z + 1) / 2) (z + (z + 1) / 2) ×ˢ Work.Spaces.Iθ ⊆ Aux.PhiU := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := hp
      rw [Aux.mem_U]
      simp only [Set.mem_Icc] at hp1
      simp only [Work.Spaces.Iθ, Set.mem_Icc] at hp2
      exact ⟨by linarith [hp1.1], by linarith [hp2.1], by linarith [hp2.2]⟩
    have hF : ContinuousOn (fun p : ℝ × ℝ => (v p.1 p.2) ^ 2)
        (Set.Icc (z - (z + 1) / 2) (z + (z + 1) / 2) ×ˢ Work.Spaces.Iθ) :=
      (hvc.mono hsU).pow 2
    have hF' : ContinuousOn (fun p : ℝ × ℝ => 2 * (v p.1 p.2 * Work.Spaces.pz v p.1 p.2))
        (Set.Icc (z - (z + 1) / 2) (z + (z + 1) / 2) ×ˢ Work.Spaces.Iθ) :=
      ((hvc.mono hsU).mul (hpzc.mono hsU)).const_mul 2
    have hd : ∀ x ∈ Set.Icc (z - (z + 1) / 2) (z + (z + 1) / 2), ∀ θ ∈ Work.Spaces.Iθ,
        HasDerivAt (fun x' => (v x' θ) ^ 2) (2 * (v x θ * Work.Spaces.pz v x θ)) x := by
      intro x hx θ hθ
      have hmem : (x, θ) ∈ Aux.PhiU := hsU ⟨hx, hθ⟩
      have hdiff : DifferentiableAt ℝ (Function.uncurry v) (x, θ) :=
        (hs.contDiffAt (Aux.isOpen_U.mem_nhds hmem)).differentiableAt (by decide)
      have h1 : HasDerivAt (fun x' => v x' θ) (Work.Spaces.pz v x θ) x :=
        Aux.hasDerivAt_slice hdiff
      have h2 := h1.pow 2
      convert h2 using 1
      ring
    have key := Aux.hasDerivAt_integral_theta_backup (F := fun x θ => (v x θ) ^ 2)
      (F' := fun x θ => 2 * (v x θ * Work.Spaces.pz v x θ)) hε hF hF' hd
    rwa [MeasureTheory.integral_const_mul] at key
  · intro z hz
    have hz1 : (-1 : ℝ) < z := hz
    have hε : 0 < (z + 1) / 2 := by linarith
    have hzs : z ∈ Set.Icc (z - (z + 1) / 2) (z + (z + 1) / 2) := ⟨by linarith, by linarith⟩
    have hsU : Set.Icc (z - (z + 1) / 2) (z + (z + 1) / 2) ×ˢ Work.Spaces.Iθ ⊆ Aux.PhiU := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := hp
      rw [Aux.mem_U]
      simp only [Set.mem_Icc] at hp1
      simp only [Work.Spaces.Iθ, Set.mem_Icc] at hp2
      exact ⟨by linarith [hp1.1], by linarith [hp2.1], by linarith [hp2.2]⟩
    have hF : ContinuousOn (fun p : ℝ × ℝ => 2 * (v p.1 p.2 * Work.Spaces.pz v p.1 p.2))
        (Set.Icc (z - (z + 1) / 2) (z + (z + 1) / 2) ×ˢ Work.Spaces.Iθ) :=
      ((hvc.mono hsU).mul (hpzc.mono hsU)).const_mul 2
    have hF' : ContinuousOn (fun p : ℝ × ℝ => 2 * ((Work.Spaces.pz v p.1 p.2) ^ 2
        + Work.Spaces.pzIter 2 v p.1 p.2 * v p.1 p.2))
        (Set.Icc (z - (z + 1) / 2) (z + (z + 1) / 2) ×ˢ Work.Spaces.Iθ) :=
      (((hpzc.mono hsU).pow 2).add ((hpz2c.mono hsU).mul (hvc.mono hsU))).const_mul 2
    have hd : ∀ x ∈ Set.Icc (z - (z + 1) / 2) (z + (z + 1) / 2), ∀ θ ∈ Work.Spaces.Iθ,
        HasDerivAt (fun x' => 2 * (v x' θ * Work.Spaces.pz v x' θ))
          (2 * ((Work.Spaces.pz v x θ) ^ 2 + Work.Spaces.pzIter 2 v x θ * v x θ)) x := by
      intro x hx θ hθ
      have hmem : (x, θ) ∈ Aux.PhiU := hsU ⟨hx, hθ⟩
      have hdiff : DifferentiableAt ℝ (Function.uncurry v) (x, θ) :=
        (hs.contDiffAt (Aux.isOpen_U.mem_nhds hmem)).differentiableAt (by decide)
      have hdiff2 : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pz v)) (x, θ) :=
        (((Aux.contDiffOn_pz_backup hs).differentiableOn (by decide)).differentiableAt
          (Aux.isOpen_U.mem_nhds hmem))
      have h1 : HasDerivAt (fun x' => v x' θ) (Work.Spaces.pz v x θ) x :=
        Aux.hasDerivAt_slice hdiff
      have h2 : HasDerivAt (fun x' => Work.Spaces.pz v x' θ) (Work.Spaces.pzIter 2 v x θ) x :=
        Aux.hasDerivAt_slice hdiff2
      have h3 := (h1.mul h2).const_mul 2
      convert h3 using 1
      ring
    have key := Aux.hasDerivAt_integral_theta_backup
      (F := fun x θ => 2 * (v x θ * Work.Spaces.pz v x θ))
      (F' := fun x θ => 2 * ((Work.Spaces.pz v x θ) ^ 2
        + Work.Spaces.pzIter 2 v x θ * v x θ)) hε hF hF' hd
    have hfun : (fun x => ∫ θ in Work.Spaces.Iθ, 2 * (v x θ * Work.Spaces.pz v x θ))
        = fun x => 2 * (∫ θ in Work.Spaces.Iθ, v x θ * Work.Spaces.pz v x θ) := by
      funext x
      rw [MeasureTheory.integral_const_mul]
    rw [hfun] at key
    have hslice : ContinuousOn (fun θ => Work.Spaces.pz v z θ) Work.Spaces.Iθ :=
      (hpzc.mono hsU).comp (continuous_const.prodMk continuous_id).continuousOn
        (fun θ hθ => ⟨hzs, hθ⟩)
    have hslice2 : ContinuousOn (fun θ => Work.Spaces.pzIter 2 v z θ) Work.Spaces.Iθ :=
      (hpz2c.mono hsU).comp (continuous_const.prodMk continuous_id).continuousOn
        (fun θ hθ => ⟨hzs, hθ⟩)
    have hslicev : ContinuousOn (fun θ => v z θ) Work.Spaces.Iθ :=
      (hvc.mono hsU).comp (continuous_const.prodMk continuous_id).continuousOn
        (fun θ hθ => ⟨hzs, hθ⟩)
    have hA : Integrable (fun θ => (Work.Spaces.pz v z θ) ^ 2)
        (volume.restrict Work.Spaces.Iθ) :=
      ContinuousOn.integrableOn_compact isCompact_Icc (hslice.pow 2)
    have hB : Integrable (fun θ => Work.Spaces.pzIter 2 v z θ * v z θ)
        (volume.restrict Work.Spaces.Iθ) :=
      ContinuousOn.integrableOn_compact isCompact_Icc (hslice2.mul hslicev)
    have hval : (∫ θ in Work.Spaces.Iθ, 2 * ((Work.Spaces.pz v z θ) ^ 2
          + Work.Spaces.pzIter 2 v z θ * v z θ))
        = 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz v z θ) ^ 2)
          + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.pzIter 2 v z θ * v z θ) := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hA hB]
      ring
    rw [hval] at key
    exact key

end Work.FTS.EllipticEst
