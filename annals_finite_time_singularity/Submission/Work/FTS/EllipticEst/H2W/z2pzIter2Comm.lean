import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Have
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.pz_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# `z²∂_z²` commutes with the iterated `D_z = z∂_z`

The identity `z²∂_z² = D_z² − D_z` shows that `z²∂_z²` is a polynomial in `D_z = z∂_z`,
hence commutes with every power of `D_z`:

`z²·pzIter 2 (DzIter j f) = DzIter j (z²·pzIter 2 f)`   (pointwise, when the iterates
are differentiable at the point under consideration).

This is the observation `(op)` of `Submission/Work/FTS/EllipticEst/H2W/NOTES_mixedA.md`: it
identifies the pure (radial) part of the `ℋ²`-norm of `z²∂_z²Ψ` and hence turns
`H2W/mixedA` into a statement about the three *mixed* slots of `A = z²∂_z²Ψ`.

The statement holds for a *fixed* angle `θ` at *every* `z ∈ ℝ` (also `z ≤ 0`; at `z = 0`
both sides vanish), the only input being that each iterate `∂_z^i f(·,θ)` is differentiable
at every point (hypothesis `h1`; `h2` is its own `i+1` case — `deriv (fun z'' => pzIter i f
z'' θ) = fun z'' => pzIter (i+1) f z'' θ` definitionally — and is therefore redundant).
Under `h1` the angle slice `z ↦ f z θ` is `C^∞`, which is all the proof needs: the
`C^∞`-slices of the iterates `D_z^j f` are differentiable, so the pointwise operator
identity `z²∂_z² = D_z² − D_z` holds at every point and the induction on `j` goes through.

The file is deliberately self-contained: its whole import closure is verified (the pointwise
operator identity is reproved here under the local name `zsq_pzIter2_slice_eq` rather than
imported from `H2W/mixedA`).
-/

namespace Work.FTS.EllipticEst.H2W

open scoped Real Topology ContDiff
open Set Filter

set_option autoImplicit false

/-! ## The angle slice is `C^∞` -/

/-- If every iterated `z`-derivative of the `θ`-slice of `f` is differentiable at every
point, then that slice is `C^∞`. -/
theorem contDiff_slice_of_pzIter (f : ℝ → ℝ → ℝ) (θ : ℝ)
    (h1 : ∀ (i : ℕ) (z : ℝ), DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter i f z' θ) z) :
    ContDiff ℝ ∞ (fun z => f z θ) := by
  refine contDiff_of_differentiable_iteratedDeriv (n := ⊤) fun m _ => ?_
  intro z
  have heq : (fun z' => Work.Spaces.pzIter m f z' θ)
      = iteratedDeriv m (fun z' => f z' θ) :=
    funext fun z' => Work.Spaces.pzIter_eq_iteratedDeriv m f z' θ
  simpa only [← heq] using h1 m z

/-- The `z`-slices of all the iterates `D_z^j f` of a function whose `z`-slice is `C^∞` are
themselves `C^∞`. -/
theorem contDiff_DzIter_slice (f : ℝ → ℝ → ℝ) (θ : ℝ)
    (h : ContDiff ℝ ∞ (fun z => f z θ)) :
    ∀ j : ℕ, ContDiff ℝ ∞ (fun z => Work.Spaces.DzIter j f z θ) := by
  intro j
  induction j with
  | zero => simpa using h
  | succ n ih =>
    have hd : ContDiff ℝ ∞ (deriv (fun z => Work.Spaces.DzIter n f z θ)) := by
      simpa using ContDiff.iterate_deriv (𝕜 := ℝ) 1 ih
    have hmul : ContDiff ℝ ∞
        (fun z => z * deriv (fun z' => Work.Spaces.DzIter n f z' θ) z) :=
      (contDiff_id (𝕜 := ℝ)).mul hd
    have hfun : (fun z => Work.Spaces.DzIter (n + 1) f z θ)
        = fun z => z * deriv (fun z' => Work.Spaces.DzIter n f z' θ) z := rfl
    rwa [hfun]

/-! ## The pointwise operator identity `z²∂_z² = D_z² − D_z` -/

/-- The one-variable form of the operator identity: for a function `g` of one variable which
is twice differentiable at `z`, `z² g''(z) = z·(z·g')'(z) − z·g'(z)`. -/
private theorem zsq_mul_deriv_deriv (g : ℝ → ℝ) (z : ℝ)
    (h1 : DifferentiableAt ℝ g z) (h2 : DifferentiableAt ℝ (deriv g) z) :
    z ^ 2 * deriv (deriv g) z
      = z * deriv (fun z' => z' * deriv g z') z - z * deriv g z := by
  have h : deriv (fun z' => z' * deriv g z') z = deriv (id * deriv g) z := rfl
  rw [h, deriv_mul differentiableAt_id h2]
  simp only [deriv_id, id_eq, one_mul]
  ring

/-- **The pointwise identity `z²∂_z² g = D_z² g − D_z g`** for data differentiable at the
point under consideration. -/
private theorem zsq_pzIter2_slice_eq (g : ℝ → ℝ → ℝ) (z θ : ℝ)
    (h1 : DifferentiableAt ℝ (fun z' => g z' θ) z)
    (h2 : DifferentiableAt ℝ (fun z' => deriv (fun z'' => g z'' θ) z') z) :
    z ^ 2 * Work.Spaces.pzIter 2 g z θ
      = Work.Spaces.DzIter 2 g z θ - Work.Spaces.DzIter 1 g z θ := by
  have h := zsq_mul_deriv_deriv (fun z' => g z' θ) z h1 h2
  simpa only [Work.Spaces.DzIter, Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero,
    Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.Dz, Work.Spaces.pz] using h

/-- The iterates compose: `D_z^{a+b} = D_z^a D_z^b`. -/
private theorem DzIter_add' (a b : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter (a + b) g = Work.Spaces.DzIter a (Work.Spaces.DzIter b g) := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_add, Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]

/-! ## The commutation -/

theorem z2pzIter2Comm (f : ℝ → ℝ → ℝ) (θ : ℝ)
    (h1 : ∀ (i : ℕ) (z : ℝ), DifferentiableAt ℝ (fun z' => Work.Spaces.pzIter i f z' θ) z)
    (h2 : ∀ (i : ℕ) (z : ℝ),
      DifferentiableAt ℝ (fun z' => deriv (fun z'' => Work.Spaces.pzIter i f z'' θ) z') z) :
    ∀ (j : ℕ) (z : ℝ),
      z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter j f) z θ
        = Work.Spaces.DzIter j (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z θ := by
  have hcd : ContDiff ℝ ∞ (fun z => f z θ) := contDiff_slice_of_pzIter f θ h1
  have hDz : ∀ j : ℕ, ContDiff ℝ ∞ (fun z => Work.Spaces.DzIter j f z θ) :=
    contDiff_DzIter_slice f θ hcd
  -- the slices of the iterates and of their derivatives are differentiable everywhere
  have hdiff0 : ∀ (j : ℕ) (z : ℝ),
      DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter j f z' θ) z :=
    fun j z => (hDz j).differentiable (by simp) z
  have hdiff' : ∀ (j : ℕ) (z : ℝ),
      DifferentiableAt ℝ
        (fun z' => deriv (fun z'' => Work.Spaces.DzIter j f z'' θ) z') z := by
    intro j z
    have h1j : ContDiff ℝ ∞ (deriv (fun z => Work.Spaces.DzIter j f z θ)) := by
      simpa using ContDiff.iterate_deriv (𝕜 := ℝ) 1 (hDz j)
    exact h1j.differentiable (by simp) z
  -- the pointwise operator identity `z²∂_z² (D_z^j f) = D_z^{j+2} f − D_z^{j+1} f`
  have hP : ∀ (m : ℕ) (z : ℝ),
      z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter m f) z θ
        = Work.Spaces.DzIter (m + 2) f z θ - Work.Spaces.DzIter (m + 1) f z θ := by
    intro m z
    have h := zsq_pzIter2_slice_eq (Work.Spaces.DzIter m f) z θ (hdiff0 m z) (hdiff' m z)
    have e1 : Work.Spaces.DzIter 2 (Work.Spaces.DzIter m f)
        = Work.Spaces.DzIter (m + 2) f := by
      rw [← DzIter_add' 2 m]
      congr 1
      omega
    have e2 : Work.Spaces.DzIter 1 (Work.Spaces.DzIter m f)
        = Work.Spaces.DzIter (m + 1) f := by
      rw [← DzIter_add' 1 m]
      congr 1
      omega
    rw [h, e1, e2]
  intro j
  induction j with
  | zero => intro z; rfl
  | succ n ih =>
    intro z
    -- the two `z`-slices involved agree everywhere, hence so do their derivatives
    have hA : (fun z' => Work.Spaces.DzIter n
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z' θ)
        =ᶠ[𝓝 z] (fun z' => z' ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter n f) z' θ) := by
      filter_upwards with z'
      exact (ih z').symm
    have hB : (fun z' => z' ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter n f) z' θ)
        =ᶠ[𝓝 z] (fun z' => Work.Spaces.DzIter (n + 2) f z' θ
            - Work.Spaces.DzIter (n + 1) f z' θ) := by
      filter_upwards with z'
      exact hP n z'
    have hC : deriv (fun z' => Work.Spaces.DzIter (n + 2) f z' θ
          - Work.Spaces.DzIter (n + 1) f z' θ) z
        = deriv (fun z' => Work.Spaces.DzIter (n + 2) f z' θ) z
          - deriv (fun z' => Work.Spaces.DzIter (n + 1) f z' θ) z :=
      deriv_sub (hdiff0 (n + 2) z) (hdiff0 (n + 1) z)
    have hchain : deriv (fun z' => Work.Spaces.DzIter n
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z' θ) z
        = deriv (fun z' => Work.Spaces.DzIter (n + 2) f z' θ) z
          - deriv (fun z' => Work.Spaces.DzIter (n + 1) f z' θ) z :=
      (Filter.EventuallyEq.deriv_eq hA).trans ((Filter.EventuallyEq.deriv_eq hB).trans hC)
    have hfirst : Work.Spaces.DzIter (n + 3) f z θ - Work.Spaces.DzIter (n + 2) f z θ
        = z * (deriv (fun z' => Work.Spaces.DzIter (n + 2) f z' θ) z
            - deriv (fun z' => Work.Spaces.DzIter (n + 1) f z' θ) z) := by
      have h3 : Work.Spaces.DzIter (n + 3) f z θ
          = z * deriv (fun z' => Work.Spaces.DzIter (n + 2) f z' θ) z := by
        rw [show n + 3 = (n + 2) + 1 from by omega]
        rfl
      have h2 : Work.Spaces.DzIter (n + 2) f z θ
          = z * deriv (fun z' => Work.Spaces.DzIter (n + 1) f z' θ) z := by
        rw [show n + 2 = (n + 1) + 1 from by omega]
        rfl
      rw [h3, h2, mul_sub]
    calc z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter (n + 1) f) z θ
        = Work.Spaces.DzIter (n + 3) f z θ - Work.Spaces.DzIter (n + 2) f z θ := hP (n + 1) z
      _ = z * (deriv (fun z' => Work.Spaces.DzIter (n + 2) f z' θ) z
            - deriv (fun z' => Work.Spaces.DzIter (n + 1) f z' θ) z) := hfirst
      _ = z * deriv (fun z' => Work.Spaces.DzIter n
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z' θ) z := by rw [hchain]
      _ = Work.Spaces.DzIter (n + 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 f z θ) z θ := rfl

end Work.FTS.EllipticEst.H2W
