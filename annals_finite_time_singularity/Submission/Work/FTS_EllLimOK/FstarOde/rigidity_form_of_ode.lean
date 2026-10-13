/-
Copyright: work module for the Elgindi finite-time singularity project.

# Rigidity of the Euler ODE for the angular moment

At a fixed angle, the elliptic equation of Elgindi's construction reduces to the Euler
(equidimensional) ordinary differential equation

  `α² z² g''(z) + α (5 + α) z g'(z) = 0`     (`z > 0`)

for the angular moment `g = F_*δ` of a box-regular solution of the linearised operator.
This file records that the *only* `C²` solutions of this equation on `(0, ∞)` are the
combinations

  `g z = A z^{-5/α} + B`,

i.e. the solution space of the indicial equation `α r (α r + 5) = 0` is spanned by the
two characteristic exponents `r = 0` and `r = -5/α` (distinct, since `α > 0`).  This is
what makes the modulated self-similar ansatz rigid: a vanishing angular moment forces the
corresponding datum to vanish identically.

The proof is the standard one for an equidimensional equation.  Multiplying the equation
by `z^{(5+α)/α - 1}` exhibits it as the vanishing of a derivative,

  `(z^{(5+α)/α} g')' = z^{5/α} (z g'' + ((5+α)/α) g') = 0`,

so `z ↦ z^{(5+α)/α} g'(z)` is constant on the connected set `(0, ∞)`; writing the constant
as `c` gives `g'(z) = c z^{-(5+α)/α}`, and the antiderivative of the right-hand side is an
affine combination of the two characteristic powers, whence
`z ↦ g z - A z^{-5/α}` is again constant on `(0, ∞)`.

No completeness or integrability of `g` is needed: the hypothesis is differentiability
together with the equation on the *open* half-line, which is exactly the data supplied by
`Fstar_ode_of_bslOp_zero`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.FstarOde

open scoped Real

/-- A function on `(0, ∞)` that is differentiable there with identically vanishing
derivative is constant.  (The open half-line `(0, ∞)` is open, connected and convex.) -/
private lemma exists_const_of_deriv_eq_zero {f : ℝ → ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ioi 0))
    (hf' : ∀ z ∈ Set.Ioi (0 : ℝ), deriv f z = 0) :
    ∃ c : ℝ, ∀ z ∈ Set.Ioi (0 : ℝ), f z = c :=
  isOpen_Ioi.exists_is_const_of_deriv_eq_zero isPreconnected_Ioi hf hf'

theorem rigidity_form_of_ode (α : ℝ) (hα : 0 < α) {g : ℝ → ℝ}
    (hg1 : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt g (deriv g z) z)
    (hg2 : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (deriv g) (deriv (deriv g) z) z)
    (hode : ∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (deriv g) z + α * (5 + α) * z * deriv g z = 0) :
    ∃ A B : ℝ, ∀ z ∈ Set.Ioi (0 : ℝ), g z = A * z ^ (-(5 / α)) + B := by
  have hαne : α ≠ 0 := ne_of_gt hα
  set p : ℝ := (5 + α) / α with hp
  have hpα : α * p = 5 + α := by
    rw [hp]; field_simp
  -- ## Step 1: `z ↦ g'(z) z^p` is constant on `(0, ∞)`
  have hφdiff : DifferentiableOn ℝ (deriv g * fun z : ℝ => z ^ p) (Set.Ioi (0 : ℝ)) := by
    intro z hz
    have h2 : HasDerivAt (fun z : ℝ => z ^ p) (p * z ^ (p - 1)) z :=
      Real.hasDerivAt_rpow_const (x := z) (p := p) (Or.inl (ne_of_gt hz))
    exact ((hg2 z hz).differentiableAt.mul h2.differentiableAt).differentiableWithinAt
  have hφderiv : ∀ z ∈ Set.Ioi (0 : ℝ), deriv (deriv g * fun z : ℝ => z ^ p) z = 0 := by
    intro z hz
    have h2 : HasDerivAt (fun z : ℝ => z ^ p) (p * z ^ (p - 1)) z :=
      Real.hasDerivAt_rpow_const (x := z) (p := p) (Or.inl (ne_of_gt hz))
    have hd : HasDerivAt (deriv g * fun z : ℝ => z ^ p)
        (deriv (deriv g) z * z ^ p + deriv g z * (p * z ^ (p - 1))) z :=
      (hg2 z hz).mul h2
    rw [hd.deriv]
    -- the ODE, rewritten as `α z g'' + (5 + α) g' = 0`
    have hcore : α * z * deriv (deriv g) z + (5 + α) * deriv g z = 0 := by
      have h : (α * z) * (α * z * deriv (deriv g) z + (5 + α) * deriv g z) = 0 := by
        have heq : (α * z) * (α * z * deriv (deriv g) z + (5 + α) * deriv g z)
            = α ^ 2 * z ^ 2 * deriv (deriv g) z + α * (5 + α) * z * deriv g z := by
          ring
        rw [heq, hode z hz]
      exact (mul_eq_zero.mp h).resolve_left (ne_of_gt (mul_pos hα hz))
    -- `z^p = z^(p-1) z`
    have hzp : z ^ p = z ^ (p - 1) * z := by
      have h := Real.rpow_add hz (p - 1) 1
      rw [Real.rpow_one] at h
      rwa [sub_add_cancel] at h
    have key1 : α * (deriv (deriv g) z * z ^ p + deriv g z * (p * z ^ (p - 1)))
        = z ^ (p - 1) * (α * z * deriv (deriv g) z + (α * p) * deriv g z) := by
      rw [hzp]; ring
    have key : α * (deriv (deriv g) z * z ^ p + deriv g z * (p * z ^ (p - 1)))
        = z ^ (p - 1) * (α * z * deriv (deriv g) z + (5 + α) * deriv g z) := by
      rw [key1, hpα]
    have hzero : α * (deriv (deriv g) z * z ^ p + deriv g z * (p * z ^ (p - 1))) = 0 := by
      rw [key, hcore, mul_zero]
    exact (mul_eq_zero.mp hzero).resolve_left hαne
  obtain ⟨c, hc⟩ := exists_const_of_deriv_eq_zero hφdiff hφderiv
  -- `c` is the value of `z ↦ g'(z) z^p`, whence `g'(z) = c z^{-p}`
  have hc' : ∀ z ∈ Set.Ioi (0 : ℝ), deriv g z * z ^ p = c := by
    intro z hz
    simpa only [Pi.mul_apply] using hc z hz
  -- ## Step 2: `z ↦ g z - A z^{-5/α}` is constant on `(0, ∞)`, with `A := -c α / 5`
  set A : ℝ := -(c * α) / 5 with hAdef
  have hAr : A * (-(5 / α)) = c := by
    rw [hAdef]; field_simp
  have hrp : -(5 / α) - 1 = -p := by
    rw [hp]; field_simp; ring
  have hHderiv : ∀ z ∈ Set.Ioi (0 : ℝ),
      deriv (g - fun z : ℝ => A * z ^ (-(5 / α))) z = 0 := by
    intro z hz
    have h2 : HasDerivAt (fun z : ℝ => z ^ (-(5 / α))) ((-(5 / α)) * z ^ (-(5 / α) - 1)) z :=
      Real.hasDerivAt_rpow_const (x := z) (p := -(5 / α)) (Or.inl (ne_of_gt hz))
    have hd : HasDerivAt (g - fun z : ℝ => A * z ^ (-(5 / α)))
        (deriv g z - A * ((-(5 / α)) * z ^ (-(5 / α) - 1))) z :=
      (hg1 z hz).sub (h2.const_mul A)
    rw [hd.deriv]
    have hgz : deriv g z = c * z ^ (-p) := by
      have hzpow_ne : z ^ p ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hz p)
      have hcz : c * z ^ (-p) = c / z ^ p := by
        rw [Real.rpow_neg hz.le p, div_eq_mul_inv]
      rw [hcz, eq_div_iff hzpow_ne]
      exact hc' z hz
    rw [hgz, hrp]
    have : A * ((-(5 / α)) * z ^ (-p)) = (A * (-(5 / α))) * z ^ (-p) := by ring
    rw [this, hAr]
    ring
  have hHdiff : DifferentiableOn ℝ (g - fun z : ℝ => A * z ^ (-(5 / α))) (Set.Ioi (0 : ℝ)) := by
    intro z hz
    have h2 : HasDerivAt (fun z : ℝ => z ^ (-(5 / α))) ((-(5 / α)) * z ^ (-(5 / α) - 1)) z :=
      Real.hasDerivAt_rpow_const (x := z) (p := -(5 / α)) (Or.inl (ne_of_gt hz))
    have h1 : DifferentiableAt ℝ g z := (hg1 z hz).differentiableAt
    have h3 : DifferentiableAt ℝ (fun z : ℝ => A * z ^ (-(5 / α))) z :=
      (h2.const_mul A).differentiableAt
    exact (h1.sub h3).differentiableWithinAt
  obtain ⟨B, hB⟩ := exists_const_of_deriv_eq_zero hHdiff hHderiv
  refine ⟨A, B, fun z hz => ?_⟩
  have hBz : g z - A * z ^ (-(5 / α)) = B := by
    simpa only [Pi.sub_apply] using hB z hz
  linarith

end Work.FTS_EllLimOK.FstarOde
