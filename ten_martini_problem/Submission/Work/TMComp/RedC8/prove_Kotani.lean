import Mathlib
import Submission.Work.TMComp.RedC8.ae_jump_of_lyap_eq_zero
import Submission.Work.TMComp.RedC8.exists_local_continuation_of_ae_jump
import Submission.Work.TMComp.Kotani.Assembly
import Submission.Work.TMComp.Kotani.kotani_core_of_local

/-!
# `RedC8`: an independent assembly of C8 (`P_Kotani`)

This file closes the `RedC8` fork of the Kotani continuation.  It is *independent of*
`Submission/Work/TMComp/Kotani/kotani_local.lean` (the component's own file, still `by sorry`):
the local continuation is obtained from the a.e.-phase jump decay
(`RedC8.ae_jump_of_lyap_eq_zero`, whose input `L ≡ 0` on `(a,b)` is used only through the
quantitative bound `RedC8.ell_le_mul_of_lyap_eq_zero_compact`) via the reconstruction
(`RedC8.rectangle_extension` + `LocCantor.extOn_of_cayley`, wrapped as
`RedC8.exists_local_continuation_of_ae_jump`).

The two Kotani glue theorems (`kotani_core_of_local`, `prove_Kotani_of_core`) are from the
component's own directory and are sorry-free.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.RedC8

/-- **The local continuation at every point of `(a,b)`**, in the exact form consumed by
`Kotani.kotani_core_of_local` and `Kotani.uniform_ext`: for every `E₀ ∈ (a,b)` and every phase
`x` the section `E ↦ mfun α lam E x` continues analytically across `E₀`, the continuation below
the axis being `1/conj (mfun (conj ·) (α - x))`, with positive imaginary part.

The interval `(a,b)` is cut down to a compact subinterval `(a',b') ∋ E₀` so that the a.e.-phase
jump decay (which needs the uniform bound `ℓ(E+iε) ≤ C ε` on a *compact* set of energies) applies. -/
theorem local_continuation (α lam a b : ℝ) (hα : Irrational α) (hab : a < b)
    (hL : ∀ E ∈ Set.Ioo a b, Work.TMContract.lyap α lam (E : ℂ) = 0) :
    ∀ E₀ ∈ Set.Ioo a b, ∀ x : ℝ, ∃ f : ℂ → ℂ,
      AnalyticAt ℂ f (E₀ : ℂ) ∧
      (∀ᶠ E in nhds (E₀ : ℂ), 0 < E.im → f E = Work.TMComp.Kotani.mfun α lam E x) ∧
      (∀ᶠ E in nhds (E₀ : ℂ), E.im < 0 →
        f E = 1 / star (Work.TMComp.Kotani.mfun α lam (star E) (α - x))) ∧
      (∀ᶠ E in nhds (E₀ : ℂ), 0 < (f E).im) := by
  intro E₀ hE₀ x
  obtain ⟨haE, hEb⟩ := hE₀
  set a' : ℝ := (a + E₀) / 2 with ha'def
  set b' : ℝ := (E₀ + b) / 2 with hb'def
  have ha' : a < a' := by rw [ha'def]; linarith
  have hb' : b' < b := by rw [hb'def]; linarith
  have ha'b' : a' < b' := by rw [ha'def, hb'def]; linarith
  have hE₀' : E₀ ∈ Set.Ioo a' b' := ⟨by rw [ha'def]; linarith, by rw [hb'def]; linarith⟩
  exact exists_local_continuation_of_ae_jump α lam a' b' hα ha'b'
    (ae_jump_of_lyap_eq_zero α lam a b a' b' hab ha' hb' ha'b' hL) E₀ hE₀' x

/-- **C8 (`P_Kotani`) from the `RedC8` fork.**  The frozen component statement, assembled from
`Kotani.prove_Kotani_of_core` and `Kotani.kotani_core_of_local` applied to the local
continuation proved above. -/
theorem prove_Kotani : Work.TMContract.P_Kotani :=
  Work.TMComp.Kotani.prove_Kotani_of_core fun α lam a b hα h0 hab hL =>
    Work.TMComp.Kotani.kotani_core_of_local α lam a b hα h0 hab hL
      (local_continuation α lam a b hα hab hL)

end Work.TMComp.RedC8
