import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Elliptic.rigidity_tail
import Submission.Work.Elliptic.euler_first_integral_algebra

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

open Set Filter
open scoped Topology

/-- **Rigidity of the homogeneous radial Euler profile.**

If `g : ℝ → ℝ` is `C²` on `(0,∞)`, solves the Euler-type equation
`α²z² g'' + α(5+α)z g' = 0` there, decays to `0` at `+∞`, and satisfies
`z² g z → 0` as `z → 0⁺`, and if `0 < α < 5/2`, then `g ≡ 0` on `(0,∞)`.

Indeed the first integral `z^c g'` (`c = 1 + 5/α`) is constant, whence
`g' z = κ z^{-c}` and so `g z = A z^{-5/α} + B` on `(0,∞)`; the two decay
conditions force `A = B = 0` (the exponent condition `α < 5/2` is exactly what
makes `z^{2-5/α} → +∞` as `z → 0⁺`). -/
lemma rigidity_ode (α : ℝ) (hα : 0 < α) (hα2 : α < 5 / 2) (g : ℝ → ℝ)
    (hg : ContDiffOn ℝ 2 g (Set.Ioi 0))
    (hode : ∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv g z') z + α * (5 + α) * z * deriv g z = 0)
    (hdec : Filter.Tendsto g Filter.atTop (nhds 0))
    (h0 : Filter.Tendsto (fun z => z ^ 2 * g z) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), g z = 0 := by
  have hαne : α ≠ 0 := ne_of_gt hα
  -- the exponent `c = 1 + 5/α` of the first integral
  set c : ℝ := 1 + 5 / α with hcdef
  have hc5 : α * c = 5 + α := by rw [hcdef]; field_simp; ring
  have hec : -c = -(5 / α) - 1 := by rw [hcdef]; ring
  -- differentiability of `g` and of `deriv g` on `(0,∞)`
  have hgd : DifferentiableOn ℝ g (Set.Ioi 0) := hg.differentiableOn (by norm_num)
  have hg_at : ∀ z ∈ Set.Ioi (0:ℝ), HasDerivAt g (deriv g z) z := fun z hz =>
    (hgd.differentiableAt (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  have hdc : ContDiffOn ℝ 1 (deriv g) (Set.Ioi 0) :=
    hg.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hv : ∀ z ∈ Set.Ioi (0:ℝ), HasDerivAt (deriv g) (deriv (deriv g) z) z := by
    intro z hz
    exact ((hdc.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hz)).hasDerivAt
  -- **First integral**: `F z = z^c g' z` has zero derivative on `(0,∞)`.
  have hF : ∀ z ∈ Set.Ioi (0:ℝ), HasDerivAt (fun w => w ^ c * deriv g w) 0 z := by
    intro z hz
    have hzp : 0 < z := hz
    have hzne : z ≠ 0 := ne_of_gt hzp
    have h1 : HasDerivAt (fun w : ℝ => w ^ c) (c * z ^ (c - 1)) z :=
      Real.hasDerivAt_rpow_const (Or.inl hzne)
    have h2 : HasDerivAt (deriv g) (deriv (deriv g) z) z := hv z hz
    have h3 := h1.mul h2
    -- the ODE divided by `α z`
    have hzw : α * z * deriv (deriv g) z + (5 + α) * deriv g z = 0 := by
      have hz0 := hode z hz
      have hfac : α * z * (α * z * deriv (deriv g) z + (5 + α) * deriv g z) = 0 := by
        have e : α * z * (α * z * deriv (deriv g) z + (5 + α) * deriv g z)
            = α ^ 2 * z ^ 2 * deriv (deriv g) z + α * (5 + α) * z * deriv g z := by
          ring
        rw [e]; exact hz0
      exact (mul_eq_zero.mp hfac).resolve_left (mul_ne_zero hαne hzne)
    have hval : c * z ^ (c - 1) * deriv g z + z ^ c * deriv (deriv g) z = 0 :=
      euler_first_integral_algebra α c z (deriv g z) (deriv (deriv g) z) hzp hαne hc5 hzw
    rw [hval] at h3
    exact h3
  have hFconst : ∀ z ∈ Set.Ioi (0:ℝ), z ^ c * deriv g z = deriv g 1 := by
    intro z hz
    have h := IsOpen.is_const_of_deriv_eq_zero (𝕜 := ℝ) isOpen_Ioi isPreconnected_Ioi
      (fun w hw => (hF w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hF w hw).deriv) hz (by norm_num : (1:ℝ) ∈ Set.Ioi 0)
    simpa using h
  -- **Solving the first-order equation**: `g' z = κ z^{-c}`.
  have hv_eq : ∀ z ∈ Set.Ioi (0:ℝ), deriv g z = deriv g 1 * z ^ (-c) := by
    intro z hz
    have hzp : 0 < z := hz
    have h := hFconst z hz
    have hzcp : z ^ c ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hzp c)
    have key : deriv g z * z ^ c = deriv g 1 := by rw [mul_comm]; exact h
    have key2 : deriv g z = deriv g 1 / z ^ c := (eq_div_iff hzcp).mpr key
    rw [key2, div_eq_mul_inv, ← Real.rpow_neg hzp.le c]
  set κ : ℝ := deriv g 1 with hκdef
  have hv_eq' : ∀ z ∈ Set.Ioi (0:ℝ), deriv g z = κ * z ^ (-c) := by
    intro z hz; rw [hv_eq z hz, hκdef]
  -- **Second integral**: `D z = g z + (κ α/5) z^{-5/α}` has zero derivative.
  have hD : ∀ z ∈ Set.Ioi (0:ℝ),
      HasDerivAt (fun w => g w + (κ * α / 5) * w ^ (-(5 / α))) 0 z := by
    intro z hz
    have hzp : 0 < z := hz
    have hzne : z ≠ 0 := ne_of_gt hzp
    have hga : HasDerivAt g (deriv g z) z := hg_at z hz
    have hr : HasDerivAt (fun w : ℝ => w ^ (-(5 / α))) ((-(5 / α)) * z ^ (-(5 / α) - 1)) z :=
      Real.hasDerivAt_rpow_const (Or.inl hzne)
    have h := hga.add (hr.const_mul (κ * α / 5))
    have hval : deriv g z + (κ * α / 5) * ((-(5 / α)) * z ^ (-(5 / α) - 1)) = 0 := by
      rw [hv_eq' z hz, hec]
      have hcoef : κ + (κ * α / 5) * (-(5 / α)) = 0 := by field_simp; ring
      calc κ * z ^ (-(5 / α) - 1) + (κ * α / 5) * ((-(5 / α)) * z ^ (-(5 / α) - 1))
          = z ^ (-(5 / α) - 1) * (κ + (κ * α / 5) * (-(5 / α))) := by ring
        _ = 0 := by rw [hcoef, mul_zero]
    rw [hval] at h
    exact h
  have hDconst : ∀ z ∈ Set.Ioi (0:ℝ),
      (g z + (κ * α / 5) * z ^ (-(5 / α))) = (g 1 + (κ * α / 5) * 1 ^ (-(5 / α))) := by
    intro z hz
    exact IsOpen.is_const_of_deriv_eq_zero (𝕜 := ℝ) isOpen_Ioi isPreconnected_Ioi
      (fun w hw => (hD w hw).differentiableAt.differentiableWithinAt)
      (fun w hw => (hD w hw).deriv) hz (by norm_num)
  -- **The explicit form** `g z = A z^{-5/α} + B` on `(0,∞)`.
  have hform0 : ∀ z ∈ Set.Ioi (0:ℝ),
      g z = -(κ * α / 5) * z ^ (-(5 / α)) + (g 1 + κ * α / 5) := by
    intro z hz
    have h := hDconst z hz
    rw [Real.one_rpow, mul_one] at h
    linarith
  -- **The two decay conditions kill both constants.**
  obtain ⟨hA, hB⟩ :=
    rigidity_tail α hα hα2 (-(κ * α / 5)) (g 1 + κ * α / 5) g hform0 hdec h0
  intro z hz
  rw [hform0 z hz, hA, hB]
  ring

end Work.Elliptic
