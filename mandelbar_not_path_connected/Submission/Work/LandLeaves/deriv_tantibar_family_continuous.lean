import Mathlib
import Submission.Work.Landing.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Function
open LeanEval.ComplexAnalysis (Tantibar)

/-! ## Auxiliary facts for `deriv_tantibar_family_continuous`

The tricorn iterate `(T_f)^[2k]` of `T_f z = z̄² + f` is the `k`-th iterate of the holomorphic
quartic `Tsq f z = (z² + f̄)² + f`.  We compute the derivative of the iterates through the
"skew product with derivative" map `R (f, z, d) = (f, Tsq f z, deriv (Tsq f) z * d)`.
-/

/-- The derivative of the holomorphic second iterate `Tsq c z = (z² + c̄)² + c` at `w`,
computed by the chain/product rules. -/
theorem dtb_deriv_tsq (c w : ℂ) :
    deriv (Work.Landing.Tsq c) w = 4 * w * (w ^ 2 + star c) := by
  have key : deriv (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c) w = 4 * w * (w ^ 2 + star c) := by
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_pow (by fun_prop) 2]
    rw [deriv_fun_add (by fun_prop) (by fun_prop)]
    rw [deriv_fun_pow (by fun_prop) 2]
    simp
    ring
  exact key

/-- `Tsq c` is (complex) differentiable everywhere. -/
theorem dtb_differentiable_tsq (c : ℂ) : Differentiable ℂ (Work.Landing.Tsq c) := by
  unfold Work.Landing.Tsq
  fun_prop

/-- All iterates of `Tsq c` are differentiable everywhere. -/
theorem dtb_differentiable_tsq_iterate (c : ℂ) (n : ℕ) :
    Differentiable ℂ ((Work.Landing.Tsq c)^[n]) :=
  (dtb_differentiable_tsq c).iterate n

/-- Even iterates of the antiholomorphic `T̄_c` are the iterates of the holomorphic
`Tsq c`: `(T_c)^[2n] = (Tsq c)^[n]`. -/
theorem dtb_tantibar_iterate_even (c : ℂ) (n : ℕ) :
    (Tantibar c)^[2 * n] = (Work.Landing.Tsq c)^[n] := by
  have h2 : (Tantibar c)^[2] = Work.Landing.Tsq c := by
    funext z
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    simp only [Work.Landing.Tsq, LeanEval.ComplexAnalysis.Tantibar, map_add, map_pow,
      starRingEnd_apply, star_star]
  rw [Function.iterate_mul (f := Tantibar c) 2 n, h2]

/-- The "skew product with derivative" map on `(f, z, d)`:
`R (f, z, d) = (f, Tsq f z, deriv (Tsq f) z * d)`, with the derivative made explicit as the
polynomial `4 * z * (z² + f̄)`. -/
def dtbSkew (p : ℂ × ℂ × ℂ) : ℂ × ℂ × ℂ :=
  (p.1, Work.Landing.Tsq p.1 p.2.1, 4 * p.2.1 * (p.2.1 ^ 2 + star p.1) * p.2.2)

/-- The key induction: the `n`-th iterate of the skew product, started from the derivative `1`,
returns the `n`-th iterate of `Tsq f` together with its derivative (chain rule). -/
theorem dtb_skew_iterate (c z : ℂ) (n : ℕ) :
    dtbSkew^[n] (c, z, 1) =
      (c, (Work.Landing.Tsq c)^[n] z, deriv ((Work.Landing.Tsq c)^[n]) z) := by
  induction n with
  | zero => simp [Function.iterate_zero, deriv_id]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    have hw : (Work.Landing.Tsq c)^[n + 1] z =
        Work.Landing.Tsq c ((Work.Landing.Tsq c)^[n] z) := by
      rw [Function.iterate_succ_apply']
    have hd : deriv ((Work.Landing.Tsq c)^[n + 1]) z =
        4 * ((Work.Landing.Tsq c)^[n] z) * (((Work.Landing.Tsq c)^[n] z)^2 + star c)
          * deriv ((Work.Landing.Tsq c)^[n]) z := by
      rw [Function.iterate_succ']
      rw [deriv_comp z (dtb_differentiable_tsq c).differentiableAt
            (dtb_differentiable_tsq_iterate c n).differentiableAt]
      rw [dtb_deriv_tsq]
    rw [hw, hd]
    rfl

/-- The skew product with derivative is continuous. -/
theorem dtb_continuous_skew : Continuous dtbSkew := by
  unfold dtbSkew
  simp only [Work.Landing.Tsq]
  fun_prop

/-- The `z`-derivative of the `2k`-th iterate of the tricorn map depends jointly continuously on
the parameter `f` and the point `z`:

  `(f, z) ↦ deriv (fun w => (T_f)^[2*k] w) z`  is continuous on `ℂ × ℂ`.

Note `(T_f)^[2k] = (Tsq f)^[k]` where `Tsq f z = (z^2 + star f)^2 + f` is the holomorphic second
iterate, and `Tsq f` is a polynomial in `z` (with coefficients polynomial in `f, star f`), so
this function is a polynomial in `f, star f, z`.

Proof sketch: the "skew product with derivative" map
`R : ℂ × ℂ × ℂ → ℂ × ℂ × ℂ`, `R (f,z,d) = (f, (z^2+star f)^2 + f, 4*z*d*(z^2+star f))`,
is continuous (`fun_prop`), and one shows by induction on `n` that
`R^[n] (f,z,1) = (f, (Tsq f)^[n] z, deriv (fun w => (Tsq f)^[n] w) z)` (the third component is the
chain rule: `deriv (Tsq f) w = 4*w*(w^2+star f)`). Composing with the third projection gives
continuity of `(f,z) ↦ deriv (fun w => (Tsq f)^[k] w) z`, which is the stated function since
`(Tsq f)^[k] = (T_f)^[2k]`. -/
theorem deriv_tantibar_family_continuous (k : ℕ) :
    Continuous (fun p : ℂ × ℂ => deriv (fun z : ℂ => (LeanEval.ComplexAnalysis.Tantibar p.1)^[2 * k] z) p.2) := by
  have h1 : Continuous (fun p : ℂ × ℂ => dtbSkew^[k] (p.1, p.2, (1 : ℂ))) :=
    (dtb_continuous_skew.iterate k).comp (by fun_prop)
  have h2 : Continuous (fun p : ℂ × ℂ => (dtbSkew^[k] (p.1, p.2, (1 : ℂ))).2.2) := h1.snd.snd
  have h3 : Continuous (fun p : ℂ × ℂ => deriv ((Work.Landing.Tsq p.1)^[k]) p.2) :=
    h2.congr (fun p => by rw [dtb_skew_iterate])
  refine h3.congr ?_
  intro p
  rw [dtb_tantibar_iterate_even p.1 k]

end Work.LandLeaves
