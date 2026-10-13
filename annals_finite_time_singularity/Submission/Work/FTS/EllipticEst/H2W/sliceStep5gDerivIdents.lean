import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology
open Filter Set

/-! ## The `tan`-form of the slice operator `L₀`

`Lzero1 u = -u'' + (tan θ · u)' - 6u`.  On the open interval `(0, π/2)` the derivative
`(tan θ · u)'` expands by the Leibniz rule, `(tan θ)' = 1 + tan²θ`, and
`(1 + tan²θ) - 6 = tan²θ - 5`:

  `Lzero1 u = -u'' + tan θ · u' + (tan²θ - 5) u`,

which is the first identity of `sliceStep5gDerivIdents`.  Differentiating once more with

  `(tan θ · u)'' = tan θ · u'' + 2(1 + tan²θ) u' + 2 tan θ (1 + tan²θ) u`

(this is `deriv_deriv_tan_mul` below) gives the second identity:

  `g' = -u''' + tan θ · u'' + (2tan²θ - 4) u' + (2tan θ + 2tan³θ) u`.

The two auxiliary lemmas `deriv_tan_mul`, `deriv_deriv_tan_mul` are exactly the two
derivatives of `θ ↦ tan θ · u θ` on `(0, π/2)`.
-/

/-- `(tan θ)' = 1 + tan²θ` (at a point where `cos θ ≠ 0`). -/
private lemma one_div_cos_sq {θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    1 / Real.cos θ ^ 2 = 1 + Real.tan θ ^ 2 := by
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  rw [Real.cos_sq_add_sin_sq]

/-- `cos θ ≠ 0` for `θ ∈ (0, π/2)`. -/
private lemma cos_ne_zero_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.cos θ ≠ 0 :=
  (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩).ne'

/-- `tan` is differentiable at any point where `cos` does not vanish. -/
private lemma differentiableAt_tan {θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    DifferentiableAt ℝ Real.tan θ :=
  ((Real.contDiffAt_tan (n := 1)).mpr hcos).differentiableAt (by norm_num)

/-- The first derivative of `θ ↦ tan θ · u θ` on `(0, π/2)`. -/
private lemma deriv_tan_mul (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun s => Real.tan s * u s) θ
      = (1 + Real.tan θ ^ 2) * u θ + Real.tan θ * deriv u θ := by
  have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hcos : Real.cos θ ≠ 0 := cos_ne_zero_of_mem_Ioo hθ
  have hu1 : HasDerivAt u (deriv u θ) θ :=
    ((hu.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
  rw [show (fun s => Real.tan s * u s) = Real.tan * u from rfl,
    deriv_mul (differentiableAt_tan hcos) hu1.differentiableAt, Real.deriv_tan]
  rw [show 1 / Real.cos θ ^ 2 = 1 + Real.tan θ ^ 2 from one_div_cos_sq hcos]

/-- The second derivative of `θ ↦ tan θ · u θ` on `(0, π/2)`. -/
private lemma deriv_deriv_tan_mul (u : ℝ → ℝ)
    (hu : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)))
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun t => deriv (fun s => Real.tan s * u s) t) θ
      = Real.tan θ * deriv (deriv u) θ + 2 * (1 + Real.tan θ ^ 2) * deriv u θ
        + 2 * Real.tan θ * (1 + Real.tan θ ^ 2) * u θ := by
  have hmem : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hcos : Real.cos θ ≠ 0 := cos_ne_zero_of_mem_Ioo hθ
  have hu1 : HasDerivAt u (deriv u θ) θ :=
    ((hu.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
  have hdu : ContDiffOn ℝ 1 (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    hu.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  have hu2 : HasDerivAt (deriv u) (deriv (deriv u) θ) θ :=
    ((hdu.contDiffAt hmem).differentiableAt (by norm_num)).hasDerivAt
  have hdt : DifferentiableAt ℝ Real.tan θ := differentiableAt_tan hcos
  -- the first derivative is, near `θ`, the explicit function of `u`, `u'`
  have hev : deriv (fun s => Real.tan s * u s) =ᶠ[𝓝 θ]
      (fun t => (1 + Real.tan t ^ 2) * u t + Real.tan t * deriv u t) := by
    filter_upwards [hmem] with t ht
    exact deriv_tan_mul u (hu.of_le (by norm_num)) ht
  have hdtpow : DifferentiableAt ℝ (fun t => Real.tan t ^ 2) θ := hdt.pow 2
  have hcst : DifferentiableAt ℝ (fun _ : ℝ => (1 : ℝ)) θ := differentiableAt_const (1 : ℝ)
  -- the derivative of `1 + tan²`
  have hA : deriv (fun t => 1 + Real.tan t ^ 2) θ
      = 2 * Real.tan θ * (1 + Real.tan θ ^ 2) := by
    rw [show (fun t => 1 + Real.tan t ^ 2)
          = (fun _ : ℝ => (1 : ℝ)) + (fun t => Real.tan t ^ 2) from rfl,
      deriv_add hcst hdtpow, deriv_const, zero_add]
    rw [show (fun t => Real.tan t ^ 2) = Real.tan ^ 2 from rfl, deriv_pow hdt 2,
      Real.deriv_tan]
    rw [show 1 / Real.cos θ ^ 2 = 1 + Real.tan θ ^ 2 from one_div_cos_sq hcos]
    ring
  have h1diff : DifferentiableAt ℝ (fun t => 1 + Real.tan t ^ 2) θ := hcst.add hdtpow
  have hf : DifferentiableAt ℝ (fun t => (1 + Real.tan t ^ 2) * u t) θ :=
    h1diff.mul hu1.differentiableAt
  have hg : DifferentiableAt ℝ (fun t => Real.tan t * deriv u t) θ :=
    hdt.mul hu2.differentiableAt
  rw [hev.deriv_eq,
    show (fun t => (1 + Real.tan t ^ 2) * u t + Real.tan t * deriv u t)
        = (fun t => (1 + Real.tan t ^ 2) * u t) + fun t => Real.tan t * deriv u t from rfl,
    deriv_add hf hg]
  rw [show (fun t => (1 + Real.tan t ^ 2) * u t)
        = (fun t => 1 + Real.tan t ^ 2) * u from rfl,
    deriv_mul h1diff hu1.differentiableAt, hA]
  rw [show (fun t => Real.tan t * deriv u t) = Real.tan * deriv u from rfl,
    deriv_mul hdt hu2.differentiableAt, Real.deriv_tan]
  rw [show 1 / Real.cos θ ^ 2 = 1 + Real.tan θ ^ 2 from one_div_cos_sq hcos]
  ring

theorem sliceStep5gDerivIdents (u g : ℝ → ℝ)
    (hu : ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)))
    (hode : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) :
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      g θ = -(deriv (deriv u) θ) + Real.tan θ * deriv u θ
        + (Real.tan θ ^ 2 - 5) * u θ) ∧
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv g θ = -(deriv (deriv (deriv u)) θ) + Real.tan θ * deriv (deriv u) θ
        + (2 * Real.tan θ ^ 2 - 4) * deriv u θ
        + (2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ) := by
  have hu1 : ContDiffOn ℝ 1 u (Set.Ioo 0 (Real.pi / 2)) := hu.of_le (by norm_num)
  have hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) := hu.of_le (by norm_num)
  have hu3 : ContDiffOn ℝ 3 u (Set.Ioo 0 (Real.pi / 2)) := hu.of_le (by norm_num)
  constructor
  · intro θ hθ
    have hder := deriv_tan_mul u hu1 hθ
    calc g θ = Work.FTS.EllipticEst.Lzero1 u θ := (hode θ hθ).symm
      _ = -(deriv (deriv u) θ) + deriv (fun s => Real.tan s * u s) θ - 6 * u θ := by
            simp only [Work.FTS.EllipticEst.Lzero1]
      _ = -(deriv (deriv u) θ)
            + ((1 + Real.tan θ ^ 2) * u θ + Real.tan θ * deriv u θ) - 6 * u θ := by
            rw [hder]
      _ = -(deriv (deriv u) θ) + Real.tan θ * deriv u θ
            + (Real.tan θ ^ 2 - 5) * u θ := by ring
  · intro θ hθ
    have hg := Work.FTS.EllipticEst.remov.slice_gprime_ident u g hu3 hode θ hθ
    have hder2 := deriv_deriv_tan_mul u hu2 hθ
    calc deriv g θ
        = - deriv (deriv (deriv u)) θ
          + deriv (fun t => deriv (fun s => Real.tan s * u s) t) θ - 6 * deriv u θ := hg
      _ = - deriv (deriv (deriv u)) θ
          + (Real.tan θ * deriv (deriv u) θ + 2 * (1 + Real.tan θ ^ 2) * deriv u θ
              + 2 * Real.tan θ * (1 + Real.tan θ ^ 2) * u θ) - 6 * deriv u θ := by
            rw [hder2]
      _ = -(deriv (deriv (deriv u)) θ) + Real.tan θ * deriv (deriv u) θ
          + (2 * Real.tan θ ^ 2 - 4) * deriv u θ
          + (2 * Real.tan θ ^ 3 + 2 * Real.tan θ) * u θ := by ring

end Work.FTS.EllipticEst.H2W
