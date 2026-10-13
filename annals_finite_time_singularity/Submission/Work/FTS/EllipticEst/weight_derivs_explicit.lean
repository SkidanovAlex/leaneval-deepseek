import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst

/-- Derivative of `w ↦ (1 + w) ^ n` at a point `z`, obtained by composing
`hasDerivAt_pow` with the affine map `w ↦ 1 + w`. -/
private lemma hasDerivAt_one_add_pow (n : ℕ) (z : ℝ) :
    HasDerivAt (fun w : ℝ => (1 + w) ^ n) (n * (1 + z) ^ (n - 1)) z := by
  have h := (hasDerivAt_pow n (1 + z)).comp z
    ((hasDerivAt_const (x := z) 1).add (hasDerivAt_id z))
  simpa [Function.comp_def] using h

/-- Derivative of `w ↦ w - 1` at a point `z`. -/
private lemma hasDerivAt_sub_one (z : ℝ) : HasDerivAt (fun w : ℝ => w - 1) 1 z := by
  have h := (hasDerivAt_id z).sub (hasDerivAt_const z 1)
  convert h using 1
  · ext w; simp
  · ring

/-- **Explicit derivatives of the rational building blocks of the radial weights.**  All for `z ≠ 0`, with the obvious derivative of each quotient:
`(1+z)^4/z^2` (i.e. `z²w²`) has derivative `2(z-1)(1+z)^3/z^3`, whose derivative is `(1+z)^2(2z²-4z+6)/z^4`;
`(1+z)^4/z^3` (i.e. `z w²`) has derivative `(z-3)(1+z)^3/z^4`;
`(1+z)^4/z^4` (i.e. `w²`) has derivative `-4(1+z)^3/z^5`, whose derivative is `4(1+z)^2(2z+5)/z^6`.
These are the `HasDerivAt` forms of the `deriv` identities of `Work.FTS.EllipticEst.weight_algebra_fts`, proved directly from `HasDerivAt.div`, `HasDerivAt.pow`, `HasDerivAt.add` and `ring`. -/
theorem weight_derivs_explicit :
    (∀ z : ℝ, z ≠ 0 →
      HasDerivAt (fun z : ℝ => (1 + z) ^ 4 / z ^ 2) (2 * (z - 1) * (1 + z) ^ 3 / z ^ 3) z) ∧
    (∀ z : ℝ, z ≠ 0 →
      HasDerivAt (fun z : ℝ => 2 * (z - 1) * (1 + z) ^ 3 / z ^ 3)
        ((1 + z) ^ 2 * (2 * z ^ 2 - 4 * z + 6) / z ^ 4) z) ∧
    (∀ z : ℝ, z ≠ 0 →
      HasDerivAt (fun z : ℝ => (1 + z) ^ 4 / z ^ 3) ((z - 3) * (1 + z) ^ 3 / z ^ 4) z) ∧
    (∀ z : ℝ, z ≠ 0 →
      HasDerivAt (fun z : ℝ => (1 + z) ^ 4 / z ^ 4) (-4 * (1 + z) ^ 3 / z ^ 5) z) ∧
    (∀ z : ℝ, z ≠ 0 →
      HasDerivAt (fun z : ℝ => -4 * (1 + z) ^ 3 / z ^ 5)
        (4 * (1 + z) ^ 2 * (2 * z + 5) / z ^ 6) z) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `(1+z)^4 / z^2`
    intro z hz
    have hnum := hasDerivAt_one_add_pow 4 z
    have hden : HasDerivAt (fun w : ℝ => w ^ 2) (2 * z) z := by
      simpa using hasDerivAt_pow 2 z
    have hd := hnum.div hden (pow_ne_zero 2 hz)
    convert hd using 1
    field_simp
    ring
  · -- `2(z-1)(1+z)^3 / z^3`
    intro z hz
    have hb := hasDerivAt_one_add_pow 3 z
    have ha := hasDerivAt_sub_one z
    have hnum : HasDerivAt (fun w : ℝ => 2 * (w - 1) * (1 + w) ^ 3)
        ((0 * (z - 1) + 2 * 1) * (1 + z) ^ 3 + (2 * (z - 1)) * (3 * (1 + z) ^ 2)) z :=
      ((hasDerivAt_const z (2 : ℝ)).mul ha).mul hb
    have hden : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ 2) z := by
      simpa using hasDerivAt_pow 3 z
    have hd := hnum.div hden (pow_ne_zero 3 hz)
    convert hd using 1
    field_simp
    ring
  · -- `(1+z)^4 / z^3`
    intro z hz
    have hnum := hasDerivAt_one_add_pow 4 z
    have hden : HasDerivAt (fun w : ℝ => w ^ 3) (3 * z ^ 2) z := by
      simpa using hasDerivAt_pow 3 z
    have hd := hnum.div hden (pow_ne_zero 3 hz)
    convert hd using 1
    field_simp
    ring
  · -- `(1+z)^4 / z^4`
    intro z hz
    have hnum := hasDerivAt_one_add_pow 4 z
    have hden : HasDerivAt (fun w : ℝ => w ^ 4) (4 * z ^ 3) z := by
      simpa using hasDerivAt_pow 4 z
    have hd := hnum.div hden (pow_ne_zero 4 hz)
    convert hd using 1
    field_simp
    ring
  · -- `-4(1+z)^3 / z^5`
    intro z hz
    have hb := hasDerivAt_one_add_pow 3 z
    have hnum : HasDerivAt (fun w : ℝ => -4 * (1 + w) ^ 3)
        (0 * (1 + z) ^ 3 + (-4) * (3 * (1 + z) ^ 2)) z :=
      (hasDerivAt_const z (-4 : ℝ)).mul hb
    have hden : HasDerivAt (fun w : ℝ => w ^ 5) (5 * z ^ 4) z := by
      simpa using hasDerivAt_pow 5 z
    have hd := hnum.div hden (pow_ne_zero 5 hz)
    convert hd using 1
    field_simp
    ring

end Work.FTS.EllipticEst
