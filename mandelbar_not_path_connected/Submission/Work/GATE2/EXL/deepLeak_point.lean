import Mathlib
import Submission.Work.GATE2.Access
import Submission.Work.GATE2.Inputs
import Submission.Work.PARIMPL.leak_shift_int

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.EXL

/-- **A deep real leak point.**  The only hypotheses used are: the exists-it-anywhere leak
`hleak₀`, the far-left tails in the two near sides (`htailP0`, `hballQ` + `hΨsmall`), and the
far-left potential bound `hpot`.  The leak propagates to *every* integer translate along the real
axis (`Work.PARIMPL.leak_shift_int`, from the equivariance `Ψ (w+1) = F (Ψ w)` and the total
invariance of the filled Julia set under `T_c`); choosing the translate far enough to the left
makes all the far-left hypotheses apply simultaneously. -/
theorem deepLeak_point {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa) (Q : Work.EL.CoPair d.hN)
    (hleak₀ : ∃ x : ℝ, fl.Ψ ((x : ℝ) : ℂ) ∉ Work.EL.K c)
    (htailP0 : ∃ R : ℝ, ∀ x : ℝ, x < -R → fl.Ψ ((x : ℝ) : ℂ) ∈ Work.EL.pairSideNear nest.P0)
    (hballQ : ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball d.z₁ ρ ⊆ Work.EL.pairSideNear Q)
    (hΨsmall : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ w : ℂ, w.re < -R → ‖fl.Ψ w - d.z₁‖ < ε)
    {N g : ℝ} (hg : 0 < g)
    (hpot : ∃ R : ℝ, ∀ w : ℂ, w.re < -R → Work.EL.pot d.hN (fl.Ψ w) < g) :
    ∃ x₀ : ℝ, x₀ < -N ∧ fl.Ψ ((x₀ : ℝ) : ℂ) ∉ Work.EL.K c ∧
      fl.Ψ ((x₀ : ℝ) : ℂ) ∈ Work.EL.pairSideNear nest.P0 ∧
      fl.Ψ ((x₀ : ℝ) : ℂ) ∈ Work.EL.pairSideNear Q ∧
      Work.EL.pot d.hN (fl.Ψ ((x₀ : ℝ) : ℂ)) < g := by
  obtain ⟨x, hxleak⟩ := hleak₀
  obtain ⟨ρ, hρpos, hρsub⟩ := hballQ
  obtain ⟨RQ, hRQ⟩ := hΨsmall ρ hρpos
  obtain ⟨RP0, hP0⟩ := htailP0
  obtain ⟨Rpot, hpot'⟩ := hpot
  set M : ℝ := max (max N RP0) (max RQ Rpot) with hMdef
  have hMN : N ≤ M := by rw [hMdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hMP0 : RP0 ≤ M := by rw [hMdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hMQ : RQ ≤ M := by rw [hMdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hMpot : Rpot ≤ M := by rw [hMdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (n : ℝ) < -M - x := exists_int_lt _
  refine ⟨x + (n : ℝ), by linarith, ?_, ?_, ?_, ?_⟩
  · exact Work.PARIMPL.leak_shift_int fl.Ψ_shift hxleak n
  · exact hP0 (x + (n : ℝ)) (by linarith)
  · apply hρsub
    rw [Metric.mem_ball]
    have h := hRQ (((x + (n : ℝ) : ℝ)) : ℂ) (by simp only [Complex.ofReal_re]; linarith)
    simpa [dist_eq_norm] using h
  · exact hpot' (((x + (n : ℝ) : ℝ)) : ℂ) (by simp only [Complex.ofReal_re]; linarith)

end Work.GATE2.EXL
