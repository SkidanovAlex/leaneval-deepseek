/-
Interior regularity of `bslOp α` (weight `(5+α)/α`): the localized strip vocabulary.

This file contains the elementary facts about the strip model of `Strip.lean` / `VT/Defs.lean`
needed by the local Sobolev-regularity argument: the coordinate identification
`coords : ℝ × ℝ → E2` (measurable, measure preserving), the weight identity
`wt α (coords s θ) = α e^{(5+2α)s} cos θ`, the integrability of `χ · Vc` and `χ · Gc` on
compactly supported cut-offs (a change-of-variables argument reducing to
`LocallyIntegrableOn (uncurry Ψ) Q0`), and the smoothness of `χ · Gc` when `F` is `C^∞` on the
open quadrant.
-/
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.EllipticEst.InteriorRegularity.VT.Defs
import Submission.Work.EllipticEst.InteriorRegularity.contDiff_mul_of_tsupport_subset

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Work.EllipticEst.InteriorRegularity.VT

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The coordinate map `(s,θ) ↦ coords s θ` -/

theorem continuous_coords : Continuous (fun p : ℝ × ℝ => coords p.1 p.2) := by
  have h : (fun p : ℝ × ℝ => coords p.1 p.2) =
      fun p : ℝ × ℝ => p.1 • e0 + p.2 • e1 := by
    funext p
    ext i
    fin_cases i <;> simp [coords, e0, e1]
  rw [h]
  exact (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)

theorem coords_zero (s θ : ℝ) : (coords s θ) 0 = s := by simp [coords]

theorem coords_one (s θ : ℝ) : (coords s θ) 1 = θ := by simp [coords]

theorem coords_injective : Function.Injective (fun p : ℝ × ℝ => coords p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h' : coords a b = coords c d := h
  have h0 : (coords a b) 0 = (coords c d) 0 := congrArg (fun v : E2 => v 0) h'
  have h1 : (coords a b) 1 = (coords c d) 1 := congrArg (fun v : E2 => v 1) h'
  rw [coords_zero, coords_zero] at h0
  rw [coords_one, coords_one] at h1
  exact Prod.ext h0 h1

theorem measurable_coords_fst : Measurable fun x : E2 => x 0 :=
  (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2)).measurable

theorem measurable_coords_snd : Measurable fun x : E2 => x 1 :=
  (PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (1 : Fin 2)).measurable

theorem coords_measurableEmbedding :
    MeasurableEmbedding (fun p : ℝ × ℝ => coords p.1 p.2) := by
  refine ⟨coords_injective, continuous_coords.measurable, ?_⟩
  intro s hs
  have hg : Measurable fun x : E2 => (x 0, x 1) :=
    measurable_coords_fst.prodMk measurable_coords_snd
  have h1 : (fun p : ℝ × ℝ => coords p.1 p.2) '' s = (fun x : E2 => (x 0, x 1)) ⁻¹' s := by
    ext y
    constructor
    · rintro ⟨p, hp, rfl⟩
      show ((coords p.1 p.2) 0, (coords p.1 p.2) 1) ∈ s
      rw [coords_zero, coords_one]
      exact hp
    · intro hy
      refine ⟨(y 0, y 1), hy, ?_⟩
      ext i
      fin_cases i <;> simp [coords]
  rw [h1]
  exact hg hs

theorem coords_measurePreserving :
    MeasurePreserving (fun p : ℝ × ℝ => coords p.1 p.2) volume volume := by
  have h1 : MeasurePreserving ((MeasurableEquiv.finTwoArrow (α := ℝ)).symm)
      (volume : Measure (ℝ × ℝ)) (volume : Measure (Fin 2 → ℝ)) :=
    (volume_preserving_finTwoArrow ℝ).symm
  have h2 : MeasurePreserving (WithLp.toLp 2 : (Fin 2 → ℝ) → E2)
      (volume : Measure (Fin 2 → ℝ)) (volume : Measure E2) :=
    PiLp.volume_preserving_toLp (Fin 2)
  have h3 := h2.comp h1
  convert h3 using 2
  ext i
  fin_cases i <;> simp [coords, MeasurableEquiv.finTwoArrow_symm_apply]

/-! ## The strip -/

theorem continuous_coord_one : Continuous fun x : E2 => x 1 :=
  PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (1 : Fin 2)

theorem isOpen_stripE : IsOpen stripE :=
  isOpen_Ioo.preimage continuous_coord_one

theorem mem_stripE {x : E2} : x ∈ stripE ↔ 0 < x 1 ∧ x 1 < Real.pi / 2 := Iff.rfl

theorem wt_coords {α : ℝ} (hα : α ≠ 0) (s θ : ℝ) :
    wt α (coords s θ) = α * Real.exp ((5 + 2 * α) * s) * Real.cos θ := by
  simp only [wt, coords_zero, coords_one]
  rw [Real.rpow_def_of_pos (Real.exp_pos (α * s)), Real.log_exp]
  rw [show α * s * ((5 + 2 * α) / α) = (5 + 2 * α) * s by field_simp]

/-- On `α ≠ 0` the weight `wt α` is the explicitly exponential function
`α * exp ((5+2α) s) * cos θ`. -/
theorem wt_eq_exp {α : ℝ} (hα : α ≠ 0) :
    wt α = fun x : E2 => α * Real.exp ((5 + 2 * α) * x 0) * Real.cos (x 1) := by
  funext x
  rw [wt, Real.rpow_def_of_pos (Real.exp_pos (α * x 0)), Real.log_exp]
  rw [show α * x 0 * ((5 + 2 * α) / α) = (5 + 2 * α) * x 0 by field_simp]

theorem wt_contDiff {α : ℝ} (hα : α ≠ 0) (n : ℕ) : ContDiff ℝ n (wt α) := by
  rw [wt_eq_exp hα]
  fun_prop

theorem wt_ne_zero {α : ℝ} (hα : 0 < α) {x : E2} (hx : x ∈ stripE) : wt α x ≠ 0 := by
  rw [wt]
  have h1 : 0 < Real.exp (α * x 0) ^ ((5 + 2 * α) / α) :=
    Real.rpow_pos_of_pos (Real.exp_pos _) _
  have h2 : 0 < Real.cos (x 1) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩
  positivity

/-! ## The un-indicated pull-backs -/

@[simp] theorem Ws_apply (α : ℝ) (Ψ : ℝ → ℝ → ℝ) (x : E2) :
    Ws α Ψ x = ((wt α x * Ψ (Real.exp (α * x 0)) (x 1) : ℝ) : ℂ) := rfl

@[simp] theorem Gs_apply (α : ℝ) (F : ℝ → ℝ → ℝ) (x : E2) :
    Gs α F x = ((wt α x * F (Real.exp (α * x 0)) (x 1) : ℝ) : ℂ) := rfl

theorem Vc_of_mem {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {x : E2} (hx : x ∈ stripE) :
    Vc α Ψ x = Ws α Ψ x := Set.indicator_of_mem hx _

theorem Vc_of_notMem {α : ℝ} {Ψ : ℝ → ℝ → ℝ} {x : E2} (hx : x ∉ stripE) :
    Vc α Ψ x = 0 := Set.indicator_of_notMem hx _

theorem Gc_of_mem {α : ℝ} {F : ℝ → ℝ → ℝ} {x : E2} (hx : x ∈ stripE) :
    Gc α F x = Gs α F x := Set.indicator_of_mem hx _

theorem Gc_of_notMem {α : ℝ} {F : ℝ → ℝ → ℝ} {x : E2} (hx : x ∉ stripE) :
    Gc α F x = 0 := Set.indicator_of_notMem hx _

theorem cplx_indicator (s : Set E2) (g : E2 → ℝ) :
    cplx (s.indicator g) = s.indicator (fun x => ((g x : ℝ) : ℂ)) := by
  funext x
  by_cases hx : x ∈ s <;> simp [cplx, Set.indicator_of_mem, Set.indicator_of_notMem, hx]

theorem Vc_eq_cplx_Vfun (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : Vc α Ψ = cplx (Vfun α Ψ) := by
  funext x
  simp only [Vc, Vfun, Ws, cplx]
  by_cases hx : x ∈ stripE <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]

theorem Gc_eq_cplx_Gfun (α : ℝ) (F : ℝ → ℝ → ℝ) : Gc α F = cplx (Gfun α F) := by
  funext x
  simp only [Gc, Gfun, Gs, cplx]
  by_cases hx : x ∈ stripE <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]

/-! ## The scaled bump `cfun` -/

@[simp] theorem cfun_apply (x₀ : E2) (ρ : ℝ) (hρ : 0 < ρ) (x : E2) :
    cfun x₀ ρ hρ x = (((cdb x₀ ρ hρ) x : ℝ) : ℂ) := rfl

theorem cfun_contDiff (x₀ : E2) (ρ : ℝ) (hρ : 0 < ρ) : ∀ n : ℕ, ContDiff ℝ n (cfun x₀ ρ hρ) := by
  intro n
  change ContDiff ℝ n (fun x : E2 => (((cdb x₀ ρ hρ) x : ℝ) : ℂ))
  exact Complex.ofRealCLM.contDiff.comp ((cdb x₀ ρ hρ).contDiff (n := (n : ℕ∞)))

theorem cfun_support (x₀ : E2) (ρ : ℝ) (hρ : 0 < ρ) :
    Function.support (cfun x₀ ρ hρ) = Metric.ball x₀ (2 * ρ) := by
  have h1 : Function.support (cfun x₀ ρ hρ) = Function.support (↑(cdb x₀ ρ hρ) : E2 → ℝ) := by
    ext x
    simp [Function.mem_support, cfun_apply, Complex.ofReal_eq_zero]
  rw [h1, ContDiffBump.support_eq]
  rfl

theorem cfun_tsupport (x₀ : E2) (ρ : ℝ) (hρ : 0 < ρ) :
    tsupport (cfun x₀ ρ hρ) = Metric.closedBall x₀ (2 * ρ) := by
  rw [tsupport, cfun_support]
  exact closure_ball x₀ (ne_of_gt (by linarith : (0 : ℝ) < 2 * ρ))

theorem cfun_one {x₀ x : E2} {ρ : ℝ} (hρ : 0 < ρ) (hx : x ∈ Metric.closedBall x₀ ρ) :
    cfun x₀ ρ hρ x = 1 := by
  rw [cfun_apply, ContDiffBump.one_of_mem_closedBall]
  · simp
  · rwa [cdb]

theorem cfun_norm_le (x₀ : E2) (ρ : ℝ) (hρ : 0 < ρ) (x : E2) :
    ‖cfun x₀ ρ hρ x‖ ≤ 1 := by
  rw [cfun_apply, Complex.norm_real,
    Real.norm_of_nonneg ((cdb x₀ ρ hρ).nonneg)]
  exact (cdb x₀ ρ hρ).le_one

theorem cfun_hasCompactSupport (x₀ : E2) (ρ : ℝ) (hρ : 0 < ρ) :
    HasCompactSupport (cfun x₀ ρ hρ) := by
  simpa [HasCompactSupport, cfun_tsupport x₀ ρ hρ] using isCompact_closedBall x₀ (2 * ρ)

end Work.EllipticEst.InteriorRegularity.VT
