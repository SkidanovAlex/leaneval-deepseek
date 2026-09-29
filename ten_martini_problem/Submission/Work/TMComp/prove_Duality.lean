import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.Duality.Defs
import Submission.Work.TMComp.Duality.Basic
import Submission.Work.TMComp.Duality.PhaseIndep
import Submission.Work.TMComp.Duality.Twist
import Submission.Work.TMComp.Duality.spectrum_amoOp_subset_suspA
import Submission.Work.TMComp.Duality.spectrum_suspA_subset_amoOp

/-!
# Component C3: Aubry duality `Σ_λ = λ Σ_{1/λ}`

Proof of `Work.TMContract.P_Duality` (Avila--Jitomirskaya, *The Ten Martini Problem*, §1.1).

Writing `suspA α λ` for the suspension of the almost Mathieu cocycle on `ℓ²(ℤ × ℤ)`
(`Defs.lean`), the argument is:

* `σ(suspA α λ) = Σ_λ = σ(amoOp α λ 0)` for irrational `α`
  (`spectrum_amoOp_subset_suspA` + `spectrum_suspA_subset_amoOp`; the second uses the
  phase-independence `amoOp_spectrum_phase` and the Fourier twist/Parseval identity,
  the first uses `fs_approx` and "block vectors" concentrating the phase at `0`);
* the Aubry twist `U` is unitary and `U ∘ suspA α λ = λ · suspA α λ⁻¹ ∘ U`, whence
  `σ(suspA α λ) = λ • σ(suspA α λ⁻¹)` (`Twist.lean`).

The two together give `E ∈ Σ_λ ↔ E/λ ∈ Σ_{1/λ}`.
-/

open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp

theorem prove_Duality : Work.TMContract.P_Duality := by
  intro α lam hα hlam E
  rw [Work.TMComp.Duality.mem_amoSpec_iff α lam E,
    Work.TMComp.Duality.mem_amoSpec_iff α lam⁻¹ (E / lam)]
  constructor
  · intro hE
    have h1 : (E : ℂ) ∈ spectrum ℂ (Work.TMComp.Duality.suspA α lam) :=
      Work.TMComp.Duality.spectrum_amoOp_subset_suspA α lam hE
    have h2 : ((E / lam : ℝ) : ℂ) ∈ spectrum ℂ (Work.TMComp.Duality.suspA α lam⁻¹) :=
      (Work.TMComp.Duality.mem_spectrum_suspA_iff α lam hlam E).mp h1
    exact Work.TMComp.Duality.spectrum_suspA_subset_amoOp α lam⁻¹ hα h2
  · intro hE
    have h1 : ((E / lam : ℝ) : ℂ) ∈ spectrum ℂ (Work.TMComp.Duality.suspA α lam⁻¹) :=
      Work.TMComp.Duality.spectrum_amoOp_subset_suspA α lam⁻¹ hE
    have h2 : (E : ℂ) ∈ spectrum ℂ (Work.TMComp.Duality.suspA α lam) :=
      (Work.TMComp.Duality.mem_spectrum_suspA_iff α lam hlam E).mpr h1
    exact Work.TMComp.Duality.spectrum_suspA_subset_amoOp α lam hα h2

end Work.TMComp
