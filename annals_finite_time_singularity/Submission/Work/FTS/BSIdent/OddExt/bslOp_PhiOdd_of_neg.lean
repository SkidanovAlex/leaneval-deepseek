import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.BSIdent.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `bslOp` of the odd extension in `θ`, at `θ < 0`

For `θ < 0` the odd extension `PhiOdd Φ` is in its reflected branch, `PhiOdd Φ z' θ' τ =
-Φ z' (-θ') τ`, and the elliptic operator `bslOp p` is *odd* under that reflection:

`bslOp p (PhiOdd Φ · · τ) z θ = -(bslOp p (Φ · · τ) z (-θ))`.

The whole content is that the reflection `θ' ↦ -θ'` turns each `θ`-derivative into the
corresponding derivative at `-θ` with the sign dictated by parity — `deriv_comp_neg`,
`deriv (fun t => f (-t)) x = -deriv f (-x)`, which holds *unconditionally* because `deriv` is a
total function.  Consequently

* `pz`, `pzIter 2`, `Ψ` itself and `-6Ψ` are all *odd* (the reflection fixes `z`),
* `pthIter 2` is odd (`∂_θ` of an odd slice is even, `∂_θθ` is odd again),
* `tan θ · Ψ` is *even*, so `∂_θ(tan θ · Ψ)` is odd,

and `bslOp` is built out of these; see `bslOp_of_odd_slice` below for the general statement.
Because `deriv` is total, no differentiability hypothesis is needed for the identity itself (the
hypothesis `hΦ` of the target statement is then unused).

Everything here is a pure `deriv` bookkeeping computation: the only tools are
`Filter.EventuallyEq.deriv_eq` (to replace a slice by its reflection on a neighbourhood) and
`deriv_comp_neg`.
-/

namespace Work.FTS.BSIdent.OddExt

open Set

/-- If two functions agree on the open half-line `θ < 0`, then so do their derivatives, at
every point of that half-line.  (Used to transfer a *pointwise* slice identity into an identity
of derivatives: the set `Iio 0` is open, hence a neighbourhood of each of its points.) -/
private theorem deriv_eq_of_eqOn_Iio {f g : ℝ → ℝ} (h : Set.EqOn f g (Set.Iio 0)) {x : ℝ}
    (hx : x < 0) : deriv f x = deriv g x :=
  (Set.EqOn.eventuallyEq_of_mem h (isOpen_Iio.mem_nhds hx)).deriv_eq

/-- **The reflection principle for `bslOp`.**  If `Ψ` is the odd reflection in `θ` of `Φs` on
the open half-line `θ' < 0`, i.e. `Ψ z θ' = -Φs z (-θ')` for all `z` and all `θ' < 0`, then for
every `θ < 0`

`bslOp p Ψ z θ = -(bslOp p Φs z (-θ))`.

No regularity hypotheses: `deriv` is total and `deriv_comp_neg` is unconditional. -/
theorem bslOp_of_odd_slice {p : ℝ} {Ψ Φs : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hrel : ∀ z' θ', θ' < 0 → Ψ z' θ' = -Φs z' (-θ')) (hθ : θ < 0) :
    Work.Elliptic.bslOp p Ψ z θ = -(Work.Elliptic.bslOp p Φs z (-θ)) := by
  -- the values
  have h1 : Ψ z θ = -Φs z (-θ) := hrel z θ hθ
  -- `∂_z` is odd (the reflection acts on the second variable only)
  have h2 : Work.Spaces.pz Ψ z θ = -(Work.Spaces.pz Φs z (-θ)) := by
    have hfun : (fun ζ => Ψ ζ θ) = fun ζ => -(Φs ζ (-θ)) := funext fun ζ => hrel ζ θ hθ
    simp only [Work.Spaces.pz]
    rw [hfun]
    simp
  -- `∂_z∂_z` is odd for the same reason
  have h3 : Work.Spaces.pzIter 2 Ψ z θ = -(Work.Spaces.pzIter 2 Φs z (-θ)) := by
    have hpzf : (fun ζ => Work.Spaces.pz Ψ ζ θ) = fun ζ => -(Work.Spaces.pz Φs ζ (-θ)) := by
      funext ζ
      have hfun : (fun ζ' => Ψ ζ' θ) = fun ζ' => -(Φs ζ' (-θ)) := funext fun ζ' => hrel ζ' θ hθ
      simp only [Work.Spaces.pz]
      rw [hfun]
      simp
    calc Work.Spaces.pzIter 2 Ψ z θ = deriv (fun ζ => Work.Spaces.pz Ψ ζ θ) z := rfl
      _ = deriv (fun ζ => -(Work.Spaces.pz Φs ζ (-θ))) z := by rw [hpzf]
      _ = -deriv (fun ζ => Work.Spaces.pz Φs ζ (-θ)) z := by simp
      _ = -(Work.Spaces.pzIter 2 Φs z (-θ)) := rfl
  -- `∂_θθ` is odd: the reflected slice is `s ↦ -(Φs z (-s))`, whose derivative at `s` is the
  -- derivative of the slice of `Φs` at `-s`, so one more differentiation flips the sign
  have h4 : Work.Spaces.pthIter 2 Ψ z θ = -(Work.Spaces.pthIter 2 Φs z (-θ)) := by
    have hE1 : Set.EqOn (fun t => deriv (fun u => Ψ z u) t)
        (fun t => deriv (fun u => -(Φs z (-u))) t) (Set.Iio 0) :=
      fun t ht => deriv_eq_of_eqOn_Iio (fun u hu => hrel z u hu) ht
    have step1 : deriv (fun t => deriv (fun u => Ψ z u) t) θ
        = deriv (fun t => deriv (fun u => -(Φs z (-u))) t) θ :=
      deriv_eq_of_eqOn_Iio hE1 hθ
    have hpt : ∀ t, deriv (fun u => -(Φs z (-u))) t = deriv (fun u => Φs z u) (-t) := by
      intro t
      simpa using deriv_comp_neg (fun u => -(Φs z u)) t
    calc Work.Spaces.pthIter 2 Ψ z θ
        = deriv (fun t => deriv (fun u => Ψ z u) t) θ := rfl
      _ = deriv (fun t => deriv (fun u => -(Φs z (-u))) t) θ := step1
      _ = deriv (fun t => deriv (fun u => Φs z u) (-t)) θ := by simp only [hpt]
      _ = -deriv (fun t => deriv (fun u => Φs z u) t) (-θ) := deriv_comp_neg _ θ
      _ = -(Work.Spaces.pthIter 2 Φs z (-θ)) := rfl
  -- `θ' ↦ tan θ' · Ψ z θ'` is *even* (`tan` is odd and the slice is odd), hence its derivative
  -- is odd
  have h5 : Work.Spaces.pth (fun z' θ' => Real.tan θ' * Ψ z' θ') z θ
      = -(Work.Spaces.pth (fun z' θ' => Real.tan θ' * Φs z' θ') z (-θ)) := by
    have hEqT : Set.EqOn (fun t => Real.tan t * Ψ z t) (fun t => Real.tan (-t) * Φs z (-t))
        (Set.Iio 0) := by
      intro t ht
      show Real.tan t * Ψ z t = Real.tan (-t) * Φs z (-t)
      rw [hrel z t ht, Real.tan_neg]
      ring
    calc Work.Spaces.pth (fun z' θ' => Real.tan θ' * Ψ z' θ') z θ
        = deriv (fun t => Real.tan t * Ψ z t) θ := rfl
      _ = deriv (fun t => Real.tan (-t) * Φs z (-t)) θ := deriv_eq_of_eqOn_Iio hEqT hθ
      _ = -deriv (fun t => Real.tan t * Φs z t) (-θ) :=
            deriv_comp_neg (fun t => Real.tan t * Φs z t) θ
      _ = -(Work.Spaces.pth (fun z' θ' => Real.tan θ' * Φs z' θ') z (-θ)) := rfl
  simp only [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero, h1, h2, h3, h4, h5]
  ring

set_option linter.unusedVariables false in
/-- **`bslOp` of the odd extension at `θ < 0`.**  The reflected branch of `PhiOdd` is
`θ' ↦ -Φ z (-θ') τ` on all of `θ' < 0`, so `bslOp_of_odd_slice` applies verbatim. -/
theorem bslOp_PhiOdd_of_neg {p : ℝ} {Φ : Work.FTS.BSIdent.Fam} {z θ τ : ℝ} (hθ : θ < 0)
    (hΦ : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Φ q.1 q.2 τ) (z, -θ)) :
    Work.Elliptic.bslOp p (fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ) z θ
      = -(Work.Elliptic.bslOp p (fun z' θ' => Φ z' θ' τ) z (-θ)) := by
  refine bslOp_of_odd_slice (Ψ := fun z' θ' => Work.FTS.BSIdent.PhiOdd Φ z' θ' τ)
    (Φs := fun z' θ' => Φ z' θ' τ) ?_ hθ
  intro z' θ' hθ'
  exact Work.FTS.BSIdent.PhiOdd_of_neg (not_le.mpr hθ')

end Work.FTS.BSIdent.OddExt
