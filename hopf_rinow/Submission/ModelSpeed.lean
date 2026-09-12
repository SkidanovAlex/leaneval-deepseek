import Submission.Model
import Submission.ModelCore
import Mathlib

/-!
# Speed is constant along model-space geodesics

Task: prove the final theorem `speed_const` below (fill in its proof).

## Setting (from `Submission.Model` and `Submission.ModelCore`)

`Bilin E := E →L[ℝ] (E →L[ℝ] ℝ)`; a smooth family `g : E → Bilin E` plays the role
of the metric tensor (assumed symmetric: `hsym`), with every `g x` invertible.
The geodesic equation for a curve `c : ℝ → E` with velocity `v : ℝ → E` is

    HasDerivAt c (v t) t        and
    HasDerivAt v (accel (g (c t)) (fderiv ℝ g (c t)) (v t)) t

with `accel gx T v = (ContinuousLinearMap.inverse gx) (rhsCovector T v)`; i.e.
`g (c t) (v' , ·) = rhsCovector (fderiv ℝ g (c t)) (v t)` where
`rhsCovector T v w = ½ ((T w) v) v − ((T v) v) w` (covector-valued, applied to `w`).

## Goal

The metric speed `sp t := ((g (c t)) (v t)) (v t)` is constant: its derivative is 0.

## Mathematical computation (pointwise, at fixed `t`)

Let `T := fderiv ℝ g (c t)`, `A := g (c t)`, `u := v t`, `u' := accel A T u`.
We have `A (u') = rhsCovector T u` as covectors (because `u' = (inverse A)(rhsCovector T u)`),
so, writing `T u (u) (u) := (((T u) u) u)` (i.e. `((fderiv ℝ g (c t)) (v t)) (v t)` applied to `v t`),
and using symmetry `(A a) b = (A b) a`:

  d/dt [A (v t) (v t)]   (chain + product rules; v' = u')
    = (((fderiv ℝ g (c t)) (v t)) (v t)) (v t)          -- term from d/dt of g(c t)
      + (g (c t)) (accel A T u) (v t)                    -- cross term 1
      + (g (c t)) (v t) (accel A T u)                    -- cross term 2
    = T(u)(u)(u) + 2 · (A u') u
    = T(u)(u)(u) + 2 · (rhsCovector T u) u
    = T(u)(u)(u) + 2 · (½ T(u)(u)(u) − T(u)(u)(u))
    = 0

The point is that the two terms `(T w)(v)(v)`-style cancel exactly.  (Derive the
identity `(A u') u = ½ T(u)(u)(u) − T(u)(u)(u)` from the definition of `accel`/`rhsCovector`
and the fact `inverse A` is a true inverse of `A`; you may need to prove that
`(ContinuousLinearMap.inverse A) (rhsCovector T u)` maps to a vector `w` with `A w = rhsCovector T u`
— or use `ContinuousLinearMap.apply_inverse` if it exists — otherwise prove it by applying both
sides to basis-free arguments: `((A ((inverse A) φ)) x) y = (A ((inverse A) φ) x) y = ...`; in finite
dimension `inverse A` satisfies `A ∘L (inverse A) = 1` on the whole dual, see
`ContinuousLinearMap.inverse` documentation and `IsInvertible`).

## API hints (all verified to exist in this Mathlib snapshot)

* `HasFDerivAt.comp_hasDerivAt.{u,v,w} {𝕜} ... {f : 𝕜 → F} {f' : F} (x : 𝕜) {l : F → E}
    {l' : F →L[𝕜] E} (hl : HasFDerivAt l l' (f x)) (hf : HasDerivAt f f' x) :
    HasDerivAt (l ∘ f) (l' f') x`
  — IMPORTANT: `f` and `f'` are implicit and precede `x`; supply them by name if needed:
  `HasFDerivAt.comp_hasDerivAt (f := c) (f' := v) t hgfd hcv`.
* `hg.contDiffAt.differentiableAt (by norm_num : (1:ℕ∞ω) ≠ 0) |>.hasFDerivAt` builds the
  `HasFDerivAt g (fderiv ℝ g (c t)) (c t)` from `hg : ContDiff ℝ 3 g`.
* `HasDerivAt.hasFDerivAt` converts to the `toSpanSingleton ℝ d` form:
  `HasFDerivAt f (ContinuousLinearMap.toSpanSingleton ℝ d) t`.
* `HasFDerivAt.clm_apply (hc : HasFDerivAt c c' x) (hu : HasFDerivAt u u' x) :
    HasFDerivAt (fun y => (c y) (u y)) (c x ∘SL u' + c'.flip (u x)) x`
  (all in `Mathlib/Analysis/Calculus/Deriv/Comp.lean` resp. `FDeriv/CompCLM.lean`).
* Simplification lemmas: `ContinuousLinearMap.toSpanSingleton_apply`, `flip_apply`,
  `ContinuousLinearMap.comp_apply`, `ContinuousLinearMap.add_apply`.
* `hsym : ∀ x u w, (g x) u w = (g x) w u` lets you swap the two cross terms.
* `HasDerivAt.clm_apply` (in `Mathlib/Analysis/Calculus/Deriv/Mul.lean`):
    `HasDerivAt (fun y => (c y) (u y)) (c' (u x) + c x u') x` for `c : 𝕜 → F →L[𝕜] G`,
  which is the product rule used twice below.
* `ContinuousLinearMap.IsInvertible.self_apply_inverse (hA : A.IsInvertible) y :
    A (A.inverse y) = y` (i.e. `A ((ContinuousLinearMap.inverse A) y) = y`).

## Structure of the proof (suggested)

1. Prove an auxiliary lemma: for `A : Bilin E` invertible and any covector `φ : E →L ℝ`,
   `(A ((ContinuousLinearMap.inverse A) φ)) u w = φ u * (1 : ℝ)`-style identity —
   i.e. `A ((inverse A) φ) = φ` (as functions of `u,w`: `((A ((inverse A) φ)) u) w = φ u * ...`? no:
   `((A ((inverse A) φ)) u) w = (φ u) * 1` is wrong: actually `(A ((inverse A) φ)) u` is a covector,
   and `((A ((inverse A) φ)) u) w = φ u * 1` is false; the correct identity is
   `A ((inverse A) φ) = φ`, i.e. for all u,w: `((A ((inverse A) φ)) u) w = φ u * ?` no:
   `A w0` with `w0 := (inverse A) φ` satisfies: for all u: `(A w0) u = φ u` as covectors, i.e.
   `((A w0) u) w = (φ u) w * 1 = φ u * ?` — just aim for: `∀ u w, ((A ((inverse A) φ)) u) w = φ u * 1`?? No:
   simply prove `∀ u : E, (A ((inverse A) φ)) u = φ u` (equality of covectors; then specialize at `u = v t`).
   You may need the definition of `ContinuousLinearMap.inverse`; check whether the library
   provides `ContinuousLinearMap.apply_inverse` or similar, else use
   `(ContinuousLinearMap.inverse A).isInverse`-type facts or prove from
   `IsInvertible` API: see `ContinuousLinearMap.IsInvertible` and `inverse` in
   `Mathlib/Analysis/Normed/Operator/BoundedLinearMaps.lean`.

2. Assemble the pointwise derivative as in the computation above, using the two chain-rule
   steps: (i) `d/dt (g ∘ c) = (fderiv ℝ g (c t)) (v t)`, (ii) product rule for
   `s ↦ (g (c s)) (v s)` (a map `ℝ → E →L[ℝ] ℝ`), (iii) product rule again for
   `s ↦ ((g (c s)) (v s)) (v s)`.

3. `have hc1 : ContinuousAt c t := hcv.continuousAt` etc. as needed.

You may add any number of helper lemmas above `speed_const`.  Do NOT change the statement of
`speed_const`.  No `axiom` or unproved placeholder may remain.
-/

open ContinuousLinearMap
open scoped ContDiff
open Set

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section

/-- Pointwise value of the Euler–Lagrange right-hand covector:
`(rhsCovector T u) w = ½ ((T w) u) u − ((T u) u) w`. -/
lemma rhsCovector_apply (T : E →L[ℝ] Bilin E) (u w : E) :
    (rhsCovector T u) w = (1 / 2 : ℝ) * (((T w) u) u) - (((T u) u) w) := by
  simp [rhsCovector, evalAtV]

/-- The scalar contribution of the two cross terms of `d/dt [A (v t) (v t)]` at a geodesic
is exactly `0`: with `A u' = rhsCovector T u` (the Euler–Lagrange equation) and the
symmetry of `A`,
`((T u) u) u + (A u') u + (A u) u' = 0`. -/
lemma speed_cross_terms (A : Bilin E) (T : E →L[ℝ] Bilin E) (u u' : E)
    (hsym : (A u) u' = (A u') u)
    (hODE : A u' = rhsCovector T u) :
    ((T u) u) u + (A u') u + (A u) u' = 0 := by
  rw [hODE]
  rw [rhsCovector_apply]
  rw [hsym]
  rw [hODE]
  rw [rhsCovector_apply]
  ring

/-- The metric speed is constant along a solution of the (second order) geodesic equation. -/
theorem speed_const (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u w, (g x) u w = (g x) w u)
    {c v : ℝ → E} {ε : ℝ} (hε : 0 < ε)
    (hc : ∀ t ∈ Ioo (-ε) ε, HasDerivAt c (v t) t)
    (hv : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt v (accel (g (c t)) (fderiv ℝ g (c t)) (v t)) t) :
    ∀ t ∈ Ioo (-ε) ε, HasDerivAt (fun s : ℝ => (g (c s)) (v s) (v s)) 0 t := by
  intro t ht
  -- pointwise setup
  let A : Bilin E := g (c t)
  let T : E →L[ℝ] Bilin E := fderiv ℝ g (c t)
  let u : E := v t
  let u' : E := accel A T u
  -- (1) derivative of the metric family along the curve: d/dt (g ∘ c) = (fderiv ℝ g (c t)) (v t)
  have hgfd : HasFDerivAt g (fderiv ℝ g (c t)) (c t) := by
    exact (hg.contDiffAt.differentiableAt (by norm_num : (3 : ℕ∞ω) ≠ 0)).hasFDerivAt
  have hgc : HasDerivAt (fun s : ℝ => g (c s)) (T u) t := by
    have h1 : HasDerivAt (g ∘ c) ((fderiv ℝ g (c t)) (v t)) t :=
      HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := E) (E := Bilin E)
        (f := c) (f' := v t) t hgfd (hc t ht)
    convert h1 using 1
    funext s; rfl
  -- (2) derivative of the velocity is given by the equation
  have hv' : HasDerivAt v u' t := by
    simpa [A, T, u, u', accel] using hv t ht
  -- (3) product rule for the covector s ↦ (g (c s)) (v s)
  have hφ : HasDerivAt (fun s : ℝ => (g (c s)) (v s)) ((T u) u + A u') t := by
    simpa using (HasDerivAt.clm_apply (𝕜 := ℝ) (F := E) (G := E →L[ℝ] ℝ)
      (c := fun s : ℝ => g (c s)) (c' := T u) (u := v) (u' := u') hgc hv')
  -- (4) product rule again for s ↦ ((g (c s)) (v s)) (v s)
  have hF : HasDerivAt (fun s : ℝ => ((g (c s)) (v s)) (v s))
      (((T u) u + A u') u + (A u) u') t := by
    simpa using (HasDerivAt.clm_apply (𝕜 := ℝ) (F := E) (G := ℝ)
      (c := fun s : ℝ => (g (c s)) (v s)) (c' := ((T u) u + A u')) (u := v) (u' := u')
      hφ hv')
  -- (5) Euler–Lagrange: A u' = rhsCovector T u (u' is obtained by applying the inverse metric)
  have hAinv : A.IsInvertible := by simpa [A] using hinv (c t)
  have hODE : A u' = rhsCovector T u := by
    calc
      A u' = A ((ContinuousLinearMap.inverse A) (rhsCovector T u)) := by simp [u', accel]
      _ = rhsCovector T u :=
        ContinuousLinearMap.IsInvertible.self_apply_inverse hAinv (rhsCovector T u)
  -- (6) symmetry of the metric
  have hsym' : (A u) u' = (A u') u := by simpa [A] using hsym (c t) u u'
  -- (7) the computed derivative is zero
  have hzero : ((T u) u) u + (A u') u + (A u) u' = 0 :=
    speed_cross_terms A T u u' hsym' hODE
  simpa [add_apply, hzero] using hF

end

end Submission.Model
