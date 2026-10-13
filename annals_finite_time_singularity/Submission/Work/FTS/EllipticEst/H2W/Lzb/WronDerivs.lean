import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.H2W.LzeroSolSpan
import Submission.Work.FTS.EllipticEst.LzeroSingContDiffOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real Topology
open Filter

namespace Work.FTS.EllipticEst.H2W.Lzb

/-! ## Elementary derivative facts used below -/

/-- A `C²` function on the open interval `(0, π/2)` is differentiable at each of its points. -/
private theorem hasDerivAt_of_contDiffOn_two {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) : HasDerivAt f (deriv f θ) θ := by
  have hs : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  exact ((hf.contDiffAt hs).differentiableAt (by norm_num)).hasDerivAt

/-- A `C²` function on `(0, π/2)` has a differentiable derivative there. -/
private theorem hasDerivAt_deriv_of_contDiffOn_two {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2))) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    HasDerivAt (deriv f) (deriv (deriv f) θ) θ := by
  have hs : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have h2 : ContDiffAt ℝ 1 (deriv f) θ := (hf.contDiffAt hs).derivWithin (by norm_num)
  exact (h2.differentiableAt (by norm_num)).hasDerivAt

/-- **The derivative of a Wronskian.**  If `u`, `y` are twice differentiable at `θ` (in the
sense that `u`, `y` and their derivatives are differentiable there), then
`wron u y = u y' - u' y` has derivative `u y'' - u'' y` at `θ`. -/
private theorem wron_hasDerivAt {u y : ℝ → ℝ} {θ : ℝ}
    (hu1 : HasDerivAt u (deriv u θ) θ)
    (hu2 : HasDerivAt (deriv u) (deriv (deriv u) θ) θ)
    (hy1 : HasDerivAt y (deriv y θ) θ)
    (hy2 : HasDerivAt (deriv y) (deriv (deriv y) θ) θ) :
    HasDerivAt (Work.FTS.EllipticEst.H2W.wron u y)
      (u θ * deriv (deriv y) θ - deriv (deriv u) θ * y θ) θ := by
  have h := (hu1.mul hy2).sub (hu2.mul hy1)
  exact h.congr_deriv (by ring)

/-- The product rule for `θ ↦ tan θ * f θ` at a point where `cos θ ≠ 0`. -/
private theorem deriv_tan_mul {f : ℝ → ℝ} {θ : ℝ} (hc : Real.cos θ ≠ 0)
    (hf : HasDerivAt f (deriv f θ) θ) :
    deriv (fun t : ℝ => Real.tan t * f t) θ
      = deriv Real.tan θ * f θ + Real.tan θ * deriv f θ := by
  have h := ((Real.hasDerivAt_tan hc).mul hf).deriv
  rw [Real.deriv_tan]
  exact h

private theorem sin_two_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.sin (2 * s)) (2 * Real.cos (2 * t)) t := by
  have h2 : HasDerivAt (fun s : ℝ => (2 : ℝ) * s) 2 t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul (2 : ℝ)
  exact ((Real.hasDerivAt_sin (2 * t)).comp t h2).congr_deriv (by ring)

private theorem cos_two_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => 2 * Real.cos (2 * s)) (-4 * Real.sin (2 * t)) t := by
  have h2 : HasDerivAt (fun s : ℝ => (2 : ℝ) * s) 2 t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul (2 : ℝ)
  have hc : HasDerivAt (fun s : ℝ => Real.cos (2 * s)) (-2 * Real.sin (2 * t)) t :=
    ((Real.hasDerivAt_cos (2 * t)).comp t h2).congr_deriv (by ring)
  exact (hc.const_mul 2).congr_deriv (by ring)

private theorem deriv_sin_two :
    deriv (fun s : ℝ => Real.sin (2 * s)) = fun s => 2 * Real.cos (2 * s) :=
  funext fun s => (sin_two_hasDerivAt s).deriv

/-- `y₁ = sin 2θ` solves `Lzero1 y₁ = 0` on `(0, π/2)`. -/
private theorem Lzero1_sin_two {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.FTS.EllipticEst.Lzero1 (fun t : ℝ => Real.sin (2 * t)) θ = 0 := by
  have hc : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
  have hddy : deriv (deriv (fun s : ℝ => Real.sin (2 * s))) θ = -4 * Real.sin (2 * θ) := by
    rw [deriv_sin_two]
    exact (cos_two_hasDerivAt θ).deriv
  have htvy : deriv (fun s : ℝ => Real.tan s * Real.sin (2 * s)) θ
      = deriv Real.tan θ * Real.sin (2 * θ) + Real.tan θ * (2 * Real.cos (2 * θ)) := by
    have h := ((Real.hasDerivAt_tan hc).mul (sin_two_hasDerivAt θ)).deriv
    rw [Real.deriv_tan]
    exact h
  rw [Work.FTS.EllipticEst.Lzero1, hddy, htvy]
  rw [Real.deriv_tan, Real.tan_eq_sin_div_cos, Real.sin_two_mul, Real.cos_two_mul]
  field_simp
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The equation `Lzero1 u = g` in the solved form `u'' = (tan · u)' - 6u - g` (with
`g = Lzero1 u`). -/
private theorem deriv_deriv_of_Lzero1 {u : ℝ → ℝ} {θ : ℝ} :
    deriv (deriv u) θ
      = deriv (fun t : ℝ => Real.tan t * u t) θ - 6 * u θ
        - Work.FTS.EllipticEst.Lzero1 u θ := by
  have h : Work.FTS.EllipticEst.Lzero1 u θ
      = -(deriv (deriv u) θ) + deriv (fun t : ℝ => Real.tan t * u t) θ - 6 * u θ := rfl
  linarith

/-- The derivatives of the two Wronskians attached to a solution of `Lzero1 u = g` on `(0, π/2)`.
With `y₁ = sin 2θ` and `y₂ = LzeroSing` both solving `Lzero1 y = 0`, and `g = Lzero1 u`, the
standard identity `wron(u, y)' = u y'' - u'' y` together with the two equations in the form
`u'' = deriv (tan · u) - 6u - g`, `y'' = deriv (tan · y) - 6y` gives
`wron(u,y₂)' = tan θ · wron(u,y₂) + g y₂` and `wron(y₁,u)' = tan θ · wron(y₁,u) - g y₁`
(the `tan'` terms cancel).  Here `wron f g θ = f θ * deriv g θ - deriv f θ * g θ`
(`Work.FTS.EllipticEst.H2W.wron`), the equations used are `Lzero1` unfolded and
`Work.FTS.EllipticEst.LzeroSingODE`, and differentiability follows from
`ContDiffOn ℝ 2 u` and `Work.FTS.EllipticEst.LzeroSingContDiffOn`. -/
theorem WronDerivs {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2))) :
    (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        HasDerivAt (Work.FTS.EllipticEst.H2W.wron u Work.FTS.EllipticEst.LzeroSing)
          (Real.tan θ * Work.FTS.EllipticEst.H2W.wron u Work.FTS.EllipticEst.LzeroSing θ
            + Work.FTS.EllipticEst.Lzero1 u θ * Work.FTS.EllipticEst.LzeroSing θ) θ)
      ∧ (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        HasDerivAt
          (Work.FTS.EllipticEst.H2W.wron (fun t : ℝ => Real.sin (2 * t)) u)
          (Real.tan θ * Work.FTS.EllipticEst.H2W.wron (fun t : ℝ => Real.sin (2 * t)) u θ
            - Work.FTS.EllipticEst.Lzero1 u θ * Real.sin (2 * θ)) θ) := by
  constructor
  · intro θ hθ
    have hc : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
    have hu1 := hasDerivAt_of_contDiffOn_two hu hθ
    have hu2 := hasDerivAt_deriv_of_contDiffOn_two hu hθ
    have hy1 := hasDerivAt_of_contDiffOn_two (LzeroSingContDiffOn 2) hθ
    have hy2 := hasDerivAt_deriv_of_contDiffOn_two (LzeroSingContDiffOn 2) hθ
    have hmain := wron_hasDerivAt hu1 hu2 hy1 hy2
    -- `LzeroSing` solves `Lzero1 y = 0`, in solved form
    have hyode : deriv (deriv Work.FTS.EllipticEst.LzeroSing) θ
        = deriv (fun t : ℝ => Real.tan t * Work.FTS.EllipticEst.LzeroSing t) θ
          - 6 * Work.FTS.EllipticEst.LzeroSing θ := by
      have h := LzeroSingODE θ hθ
      linarith
    have huode := deriv_deriv_of_Lzero1 (u := u) (θ := θ)
    have hutv := deriv_tan_mul hc hu1
    have hytv := deriv_tan_mul hc hy1
    refine hmain.congr_deriv ?_
    rw [hyode, huode, hutv, hytv]
    simp only [Work.FTS.EllipticEst.H2W.wron]
    ring
  · intro θ hθ
    have hc : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)
    have hddy : deriv (deriv (fun s : ℝ => Real.sin (2 * s))) θ = -4 * Real.sin (2 * θ) := by
      rw [deriv_sin_two]
      exact (cos_two_hasDerivAt θ).deriv
    have hu1 := hasDerivAt_of_contDiffOn_two hu hθ
    have hu2 := hasDerivAt_deriv_of_contDiffOn_two hu hθ
    have hy1 : HasDerivAt (fun t : ℝ => Real.sin (2 * t))
        (deriv (fun t : ℝ => Real.sin (2 * t)) θ) θ :=
      (sin_two_hasDerivAt θ).congr_deriv (sin_two_hasDerivAt θ).deriv.symm
    have hy2 : HasDerivAt (deriv (fun t : ℝ => Real.sin (2 * t)))
        (deriv (deriv (fun t : ℝ => Real.sin (2 * t))) θ) θ := by
      simpa only [deriv_sin_two] using (cos_two_hasDerivAt θ).congr_deriv hddy.symm
    have hmain := wron_hasDerivAt hy1 hy2 hu1 hu2
    -- `y₁ = sin 2θ` solves `Lzero1 y₁ = 0`, in solved form
    have hyode : deriv (deriv (fun t : ℝ => Real.sin (2 * t))) θ
        = deriv (fun t : ℝ => Real.tan t * Real.sin (2 * t)) θ - 6 * Real.sin (2 * θ) := by
      have h0 : Work.FTS.EllipticEst.Lzero1 (fun t : ℝ => Real.sin (2 * t)) θ = 0 :=
        Lzero1_sin_two hθ
      have h : Work.FTS.EllipticEst.Lzero1 (fun t : ℝ => Real.sin (2 * t)) θ
          = -(deriv (deriv (fun t : ℝ => Real.sin (2 * t))) θ)
            + deriv (fun t : ℝ => Real.tan t * Real.sin (2 * t)) θ - 6 * Real.sin (2 * θ) := rfl
      linarith
    have huode := deriv_deriv_of_Lzero1 (u := u) (θ := θ)
    have hutv := deriv_tan_mul hc hu1
    have hytv := deriv_tan_mul hc hy1
    refine hmain.congr_deriv ?_
    rw [hyode, huode, hutv, hytv]
    simp only [Work.FTS.EllipticEst.H2W.wron]
    ring

end Work.FTS.EllipticEst.H2W.Lzb
