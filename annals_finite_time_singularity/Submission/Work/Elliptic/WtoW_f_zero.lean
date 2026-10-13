/-
Copyright: work module for the Elgindi finite-time singularity project.

# `f` itself obeys the `𝒲⁴,∞`-estimate of the angular derivative

Elgindi, *Finite-time singularity formation for `C^{1,α}` solutions to the
incompressible Euler equations on `ℝ³`*, Annals of Math. **194** (2021),
Lemma `WtoW` (tex 1255).  This file isolates the "endpoint" version of the
estimate: if `f` vanishes on the two angular boundaries `θ = 0`, `θ = π/2` and
`∂_θ f ∈ 𝒲^{4,∞}`, then every `z`-derivative `∂_z^c f`, `c ≤ 4`, is controlled
by `|∂_θ f|_{𝒲^{4,∞}} · sin(2θ)`.

The mechanism is the one used throughout §H2: the angular vanishing turns the
bound for `∂_θ f` into a bound for `f` itself by the mean value theorem applied
on the two-sided angular interval, and the two endpoint bounds
`|∂_z^c f(z,θ)| ≤ |∂_z^c ∂_θ f|_∞ · θ` and `≤ |∂_z^c ∂_θ f|_∞ · (π/2 - θ)`
combine with `min θ (π/2 - θ) ≤ (π/4) sin(2θ)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Elliptic.WtoWAux
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.Spaces.BoxBounds
import Submission.Work.Spaces.SmoothCompact_Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Elliptic

set_option autoImplicit false

/-- The main estimate: for `f` smooth on a neighbourhood of the closed quadrant,
vanishing on the angular boundaries, with `∂_θ f ∈ 𝒲^{4,∞}`, the `z`-derivatives
`∂_z^c f` (`c ≤ 4`) are bounded by `(π/4)·|∂_θ f|_{𝒲^{4,∞}}·sin(2θ)`. -/
theorem WtoW_f_zero : ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    Work.Spaces.SmoothNbhd f → Work.Spaces.VanishTheta f →
    Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f) →
    ∀ (c : ℕ), c ≤ 4 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      |(z + 1) ^ c * Work.Spaces.pzIter c f z θ|
        ≤ K * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) * Real.sin (2 * θ) := by
  refine ⟨Real.pi / 4, by positivity, ?_⟩
  intro α f hα hα1 hsm hv hmem c hc z hz θ hθ
  let M : ℝ := Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
  have hMnn : 0 ≤ M := by
    show 0 ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
    rw [Work.Spaces.WlInf]
    exact add_nonneg (Work.Spaces.wlZSum_nonneg α 4 (Work.Spaces.pth f) hmem)
      (Work.Spaces.wlThSum_nonneg α 4 (Work.Spaces.pth f) hmem)
  -- `∂_θ ∂_z^d f = ∂_z^d ∂_θ f` on the neighbourhood of the quadrant
  have hcomm : ∀ d : ℕ, EqOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.pzIter d f)))
      (Function.uncurry (Work.Spaces.pzIter d (Work.Spaces.pth f))) Work.Spaces.nbhU := by
    intro d
    induction d with
    | zero => intro y hy; rfl
    | succ n ih =>
        intro y hy
        obtain ⟨a, b⟩ := y
        have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pzIter n f)) (a, b) :=
          (ContDiffOn.contDiffAt (Work.Spaces.smoothNbhd_pzIter hsm n)
            (Work.Spaces.isOpen_nbhU.mem_nhds hy)).of_le (by norm_num)
        show Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pzIter n f)) a b
          = Work.Spaces.pz (Work.Spaces.pzIter n (Work.Spaces.pth f)) a b
        rw [← Work.Spaces.pz_pth_comm hcd]
        exact Work.Spaces.pz_congr ih hy
  -- the angular slice `s ↦ ∂_z^c f (z,s)` is differentiable on the closed quadrant
  have hslice : ∀ s ∈ Work.Spaces.Iθ,
      DifferentiableAt ℝ (fun s' => Work.Spaces.pzIter c f z s') s := by
    intro s hs
    have hy : (z, s) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU hz hs
    have hF : DifferentiableAt ℝ (Function.uncurry (Work.Spaces.pzIter c f)) (z, s) :=
      (ContDiffOn.contDiffAt (Work.Spaces.smoothNbhd_pzIter hsm c)
        (Work.Spaces.isOpen_nbhU.mem_nhds hy)).differentiableAt (by norm_num)
    exact Work.Spaces.differentiableAt_curry_right hF
  -- the weighted slice whose mean value we control
  let φ : ℝ → ℝ := fun s => (z + 1) ^ c * Work.Spaces.pzIter c f z s
  have hφ0 : φ 0 = 0 := by
    show (z + 1) ^ c * Work.Spaces.pzIter c f z 0 = 0
    rw [Work.Spaces.pzIter_apply_zero_of f hv.1 c z, mul_zero]
  have hφpi : φ (π / 2) = 0 := by
    show (z + 1) ^ c * Work.Spaces.pzIter c f z (π / 2) = 0
    rw [Work.Spaces.pzIter_apply_pi_half_of f hv.2 c z, mul_zero]
  have hdiff : ∀ s ∈ Set.Icc (0 : ℝ) (π / 2), DifferentiableAt ℝ φ s := by
    intro s hs
    exact (hslice s hs).const_mul ((z + 1) ^ c)
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) (π / 2), ‖deriv φ s‖ ≤ M := by
    intro s hs
    have hderiv : deriv φ s
        = (z + 1) ^ c * Work.Spaces.pzIter c (Work.Spaces.pth f) z s := by
      show deriv (fun s' => (z + 1) ^ c * Work.Spaces.pzIter c f z s') s = _
      rw [deriv_const_mul _ (hslice s hs)]
      rw [show deriv (fun s' => Work.Spaces.pzIter c f z s') s
            = Work.Spaces.pzIter c (Work.Spaces.pth f) z s
          from hcomm c (Work.Spaces.mem_nbhU hz hs)]
    rw [hderiv, Real.norm_eq_abs]
    exact Work.Spaces.WlInf_z_bound α 4 (Work.Spaces.pth f) hmem c hc z s hz hs
  have hconv : Convex ℝ (Set.Icc (0 : ℝ) (π / 2)) := convex_Icc _ _
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨le_refl _, by linarith [Real.pi_pos]⟩
  have hpi : (π / 2) ∈ Set.Icc (0 : ℝ) (π / 2) := ⟨by linarith [Real.pi_pos], le_refl _⟩
  have h1 : ‖φ θ - φ 0‖ ≤ M * ‖θ - 0‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound hconv h0 hθ
  have h2 : ‖φ θ - φ (π / 2)‖ ≤ M * ‖θ - π / 2‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbound hconv hpi hθ
  have hb1 : |φ θ| ≤ M * θ := by
    have h := h1
    rw [hφ0] at h
    have hL : ‖φ θ - 0‖ = |φ θ| := by simp [Real.norm_eq_abs]
    have hR : ‖θ - 0‖ = θ := by rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hθ.1]
    rwa [hL, hR] at h
  have hb2 : |φ θ| ≤ M * (π / 2 - θ) := by
    have h := h2
    rw [hφpi] at h
    have hL : ‖φ θ - 0‖ = |φ θ| := by simp [Real.norm_eq_abs]
    have hR : ‖θ - π / 2‖ = π / 2 - θ := by
      rw [Real.norm_eq_abs, abs_of_nonpos (by linarith [hθ.2])]; ring
    rwa [hL, hR] at h
  have hmin : |φ θ| ≤ M * min θ (π / 2 - θ) := by
    rcases le_total θ (π / 2 - θ) with h | h
    · rw [min_eq_left h]; exact hb1
    · rw [min_eq_right h]; exact hb2
  have hfin : |φ θ| ≤ M * (Real.pi / 4 * Real.sin (2 * θ)) :=
    calc |φ θ| ≤ M * min θ (π / 2 - θ) := hmin
      _ ≤ M * (Real.pi / 4 * Real.sin (2 * θ)) :=
          mul_le_mul_of_nonneg_left (WtoW_sin2_min_bound hθ) hMnn
  show |(z + 1) ^ c * Work.Spaces.pzIter c f z θ| ≤ Real.pi / 4 * M * Real.sin (2 * θ)
  calc |(z + 1) ^ c * Work.Spaces.pzIter c f z θ| = |φ θ| := rfl
    _ ≤ M * (Real.pi / 4 * Real.sin (2 * θ)) := hfin
    _ = Real.pi / 4 * M * Real.sin (2 * θ) := by ring

end Work.Elliptic
