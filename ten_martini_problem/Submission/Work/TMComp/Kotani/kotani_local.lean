import Mathlib
import Submission.Work.TMComp.Kotani.Objects
import Submission.Work.TMComp.Kotani.mfun_props
import Submission.Work.TMComp.Kotani.two_ell
import Submission.Work.TMComp.Kotani.Psi_bounds
import Submission.Work.TMComp.Kotani.cayley_defect
import Submission.Work.TMComp.Kotani.GlueDefs
import Submission.Work.TMComp.RedC8.ae_jump_of_lyap_eq_zero
import Submission.Work.TMComp.RedC8.exists_local_continuation_of_ae_jump

/-!
# C8: the local Kotani continuation (`kotani_local`)

`kotani_local` is the local core of AJ Theorem 2.2: if the Lyapunov exponent vanishes on the
open interval `(a,b)`, then for every `E₀` in that interval and every phase `x` the section
`E ↦ mfun α lam E x` continues analytically across `E₀`, the continuation below the axis being
the reflection `1/conj (mfun (conj ·) (α - x))`, and it is `ℍ`-valued on the continuation ball.

## Proof (assembly)

The proof reduces the local statement to two facts already established in this workspace:

1. **The a.e. jump estimate.**  `Work.TMComp.RedC8.ae_jump_of_lyap_eq_zero` shows that under
   `hL : ∀ E ∈ Ioo a b, lyap α lam E = 0`, for a.e. phase `y` the jump
   `cayley (Psi (E+iε) y) - cayley (Psi (E-iε) y)` is small in `L¹` over a closed subinterval
   `[a',b'] ⊂ (a,b)` along a sequence `ε_j ↓ 0` (`Psi` is `ℍ`-valued, so `cayley ∘ Psi` is
   bounded by `1`, and `cayley` is the Cayley transform).
2. **Reconstruction / local continuation.**
   `Work.TMComp.RedC8.exists_local_continuation_of_ae_jump` turns that a.e. condition into, for
   every `E₀ ∈ (a',b')` and every phase `x`, an analytic function on a ball around `E₀` agreeing
   with `mfun α lam · x` above the axis, with `1/star (mfun α lam (star ·) (α - x))` below, and
   with positive imaginary part.  The proof uses `rectangle_extension` (holomorphic continuation
   across `ℝ` from boundedness plus `L¹`-small jumps), the closedness of the set of good phases
   and its invariance under the dense group `ℤ + αℤ` (`hα`).

The file then applies these two facts to a subinterval `[a',b'] = [(a+E₀)/2, (E₀+b)/2]` with
`a < a' < E₀ < b' < b`, giving the asserted `f` for the given `(E₀, x)`.

## Supporting contribution of this file's author

`Submission/Work/TMComp/Kotani/cayley_defect.lean` (fully proved) supplies the Schwarz–Pick
bound on the jump that the route needs in place of its original estimate (K3):
`norm (cayley X - cayley Y) ≤ 2√(δ/(δ+4))` for `δ = delta X Y`, and its (K2)-form
`norm (cayley X - cayley Y)² ≤ (im B · δ/‖B‖²) · im B`, `B = X - conj Y`
(`norm_cayley_sub_le`, `norm_cayley_sub_sq_le_K`, `cayley_Psi_jump_le`).
-/

namespace Work.TMComp.Kotani

theorem kotani_local (α lam a b : ℝ) (hα : Irrational α) (h0 : 0 ≤ lam)
    (hab : a < b) (hL : ∀ E ∈ Set.Ioo a b, Work.TMContract.lyap α lam (E : ℂ) = 0)
    (E₀ : ℝ) (hE₀ : E₀ ∈ Set.Ioo a b) (x : ℝ) :
    ∃ f : ℂ → ℂ,
      AnalyticAt ℂ f (E₀ : ℂ) ∧
      (∀ᶠ E in nhds (E₀ : ℂ), 0 < E.im → f E = Work.TMComp.Kotani.mfun α lam E x) ∧
      (∀ᶠ E in nhds (E₀ : ℂ), E.im < 0 →
        f E = 1 / star (Work.TMComp.Kotani.mfun α lam (star E) (α - x))) ∧
      (∀ᶠ E in nhds (E₀ : ℂ), 0 < (f E).im) := by
  -- Pick a closed subinterval `[a',b'] ⊂ (a,b)` containing `E₀` in its interior.
  have ha' : a < (a + E₀) / 2 := by linarith [hE₀.1]
  have hb' : (E₀ + b) / 2 < b := by linarith [hE₀.2]
  have ha'b' : (a + E₀) / 2 < (E₀ + b) / 2 := by linarith [hE₀.1, hE₀.2]
  have hE₀' : E₀ ∈ Set.Ioo ((a + E₀) / 2) ((E₀ + b) / 2) := ⟨by linarith, by linarith⟩
  -- Under `hL` the jump of `cayley ∘ Psi` is `L¹`-small along a sequence, for a.e. phase.
  have hae := Work.TMComp.RedC8.ae_jump_of_lyap_eq_zero α lam a b ((a + E₀) / 2) ((E₀ + b) / 2)
    hab ha' hb' ha'b' hL
  -- The reconstruction then gives the local continuation for every phase.
  exact Work.TMComp.RedC8.exists_local_continuation_of_ae_jump α lam ((a + E₀) / 2) ((E₀ + b) / 2)
    hα ha'b' hae E₀ hE₀' x

end Work.TMComp.Kotani
