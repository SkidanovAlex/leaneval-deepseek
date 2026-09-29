import Mathlib
import Submission.Work.TMComp.LocCantor.Bloch
import Submission.Work.TMComp.LocCantor.bloch_identity
import Submission.Work.TMComp.LocCantor.det_blochMat_const
import Submission.Work.TMComp.LocCantor.det_blochReal_eq
import Submission.Work.TMComp.LocCantor.normConj_spec
import Submission.Work.TMComp.LocCantor.normConj_analytic
import Submission.Work.TMComp.LocCantor.blochReal_analytic
import Submission.Work.TMComp.LocCantor.Reducible

/-!
# The Bloch reduction (AJ §5, `P_LocCantor` step)

A verbatim copy of the theorem `Work.TMComp.bloch_reduction` of
`Submission/Work/TMComp/prove_LocCantor.lean`, with the imports narrowed so that the file does
not depend on the `sorry`-stubbed C7/C8 stubs `prove_BJ` / `prove_Reducibility`.

A decaying generalised eigenvector `u` of the almost Mathieu operator at phase `θ` and coupling
`λ` (with irrational `α`, `λ ≠ 0`, phase not resonant) produces, for the *dual* coupling `λ⁻¹`,
membership of `E·λ⁻¹` in the reducible set `RedSet α λ⁻¹` together with the rotation-number
identity `ids α λ⁻¹ (E·λ⁻¹) = 1 + 2(εθ) + 2kα - 2j` of AJ (5.12).
-/

open scoped BigOperators
open MeasureTheory Filter Topology Set

noncomputable section

namespace Work.LocCantor

open Work.TMContract
open Work.TMComp
open Work.TMComp.LocCantor

-- File: Submission/Work/LocCantor/bloch_reduction.lean
-- Module: Submission.Work.LocCantor.bloch_reduction
-- Namespace: Work.LocCantor
-- Aim: a verbatim copy of the theorem `Work.TMComp.bloch_reduction` of
-- Submission/Work/TMComp/prove_LocCantor.lean (lines 37-110), which you may copy verbatim,
-- BUT with imports narrowed: your file must NOT import Submission.Work.TMComp.prove_LocCantor
-- (nor prove_Reducibility), because those pull in the `sorry`-stubbed C7 stub `prove_BJ`.
-- Importing the `LocCantor` submodules listed in `depends_on` is enough (they are exactly the
-- modules `prove_LocCantor.lean` uses for this proof, and they are `sorry`-free; verify with
-- `python3 _stat_red.py Submission.Work.LocCantor.bloch_reduction`).
theorem bloch_reduction
    (hconv : ∀ (α lam E : ℝ) (B : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (φ : ℝ → ℝ) (k : ℤ),
      Work.TMContract.HasDegree B k → (∀ x, B (x + 1) = B x) → (∀ x, (B x).det = 1) →
      Continuous φ → (∀ x, φ (x + 1) = φ x) →
      (∀ x, B (x + α) * Work.TMContract.tmR lam E x = Work.TMContract.rot (φ x) * B x) →
      ∃ j : ℤ, Work.TMContract.rotLift α lam E
        = 2 * (∫ x in (0 : ℝ)..1, φ x) - 2 * (k : ℝ) * α + 2 * (j : ℝ))
    {α θ lam E : ℝ} {u : ℤ → ℂ}
    (hα : Irrational α) (hlam : lam ≠ 0) (hnt : u ≠ 0) (hdec : Work.TMContract.ExpDecay u)
    (hrec : ∀ n : ℤ, Work.TMContract.amoAct α lam θ u n = (E : ℂ) * u n)
    (hθ : ∀ k l : ℤ, 2 * θ ≠ (k : ℝ) * α + (l : ℝ))
    (hAn : AnalyticOnNhd ℝ (Work.TMComp.fourier u) Set.univ)
    (hperp : ∀ x, Work.TMComp.fourier u (x + 1) = Work.TMComp.fourier u x)
    (hdetne : ∀ (c : ℝ), (∀ x, (Work.TMComp.blochMat α θ u x).det = (c : ℂ) * Complex.I) → c ≠ 0) :
    ∃ (k j : ℤ) (ε : ℝ), (ε = 1 ∨ ε = -1) ∧ (E * lam⁻¹) ∈ Work.TMContract.RedSet α lam⁻¹ ∧
      Work.TMContract.ids α lam⁻¹ (E * lam⁻¹)
        = 1 + 2 * (ε * θ) + 2 * (k : ℝ) * α - 2 * (j : ℝ) := by
  have hident0 := bloch_identity hdec hrec
  have hident : ∀ x : ℝ,
      (((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ)) * fourier u x
        + (lam : ℂ) * Complex.exp (2 * Real.pi * θ * Complex.I) * fourier u (x + α)
        + (lam : ℂ) * Complex.exp (-(2 * Real.pi * θ * Complex.I)) * fourier u (x - α)
      = (E : ℂ) * fourier u x := by
    intro x
    have h := hident0 x
    have h2 : Complex.exp (2 * ↑Real.pi * ↑x * Complex.I)
        + Complex.exp (-(2 * ↑Real.pi * ↑x * Complex.I)) = ((2 * Real.cos (2 * Real.pi * x) : ℝ) : ℂ) := by
      rw [show (2 : ℂ) * ↑Real.pi * ↑x = ↑(2 * Real.pi * x) by push_cast; ring]
      exact exp_add_exp_neg_cos (2 * Real.pi * x)
    rw [add_comm (Complex.exp (-(2 * ↑Real.pi * ↑x * Complex.I))), h2] at h
    exact h
  have hcont : Continuous (fourier u) := continuousOn_univ.mp hAn.continuousOn
  obtain ⟨c, hc⟩ := det_blochMat_const hα hlam hcont hperp hident
  have hcne : c ≠ 0 := hdetne c hc
  obtain ⟨d, hd, hcd, hdetd⟩ := det_blochReal_eq hcne hc
  set σ : ℝ := if 0 < d then 1 else -1 with hσdef
  have hσ : σ = 1 ∨ σ = -1 := by
    by_cases h : 0 < d <;> simp [hσdef, h]
  have hσd : σ * d = |d| := by
    rcases hσ with h1 | h1
    · have hpos : 0 < d := by
        by_contra hcon
        have : σ = -1 := by simp [hσdef, not_lt.mp hcon]
        rw [this] at h1; norm_num at h1
      rw [h1, one_mul, abs_of_pos hpos]
    · have hneg : d < 0 := by
        by_contra hcon
        have hdpos : 0 ≤ d := not_lt.mp hcon
        have : σ = 1 := by simp [hσdef, lt_of_le_of_ne hdpos (Ne.symm hd)]
        rw [this] at h1; norm_num at h1
      rw [h1, neg_mul, one_mul, abs_of_neg hneg]
  obtain ⟨hBdet, hBrelx⟩ := normConj_spec hσ (blochReal_rel hident hlam) hdetd hd hσd
  have hbra := blochReal_analytic (α := α) (θ := θ) (u := u) hAn hperp
  obtain ⟨hBan, hBper⟩ := normConj_analytic (A := blochReal α θ u) (σ := σ) hd hbra.1 hdetd hbra.2
  obtain ⟨k, j, hred, hids⟩ :=
    reducible_of_conjugacy hconv (normConj (blochReal α θ u) σ) σ hσ hBan hBper hBdet hBrelx
  exact ⟨k, j, σ, hσ, hred, hids⟩

end Work.LocCantor
