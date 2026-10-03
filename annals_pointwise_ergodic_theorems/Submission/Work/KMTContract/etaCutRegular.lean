import Mathlib
import Submission.Work.KMTContract.Defs

namespace Work.KMTContract

/-- The rescaled Littlewood–Paley cutoff `η_{≤k}(θ) = η(θ / 2^k)` attached to the KMT cutoff
`kmtEta` is smooth, it is by definition `θ ↦ kmtEta (θ / 2^k)`, and it vanishes as soon as
`|θ| ≥ 2^k`.  (The last two clauses are the reason `ηCut` is the "cutoff at scale `2^k`": the
support of `η` is contained in `[-1,1]`.) -/
theorem etaCutRegular (k : ℤ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) ∧
    (∀ θ : ℝ, Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k θ
      = Work.KMTContract.kmtEta (θ / (2:ℝ)^k)) ∧
    (∀ θ : ℝ, (2:ℝ)^k ≤ |θ| → Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k θ = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · -- smoothness: `η` is smooth, `kmtEta` is its complexification, and `θ ↦ θ/2^k` is smooth
    have h1 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun θ : ℝ => θ / (2:ℝ)^k) :=
      ContDiff.div_const contDiff_id _
    have h3 : ContDiff ℝ (↑(⊤ : ℕ∞)) (kmtBump : ℝ → ℝ) :=
      ContDiffBump.contDiff kmtBump (n := ⊤)
    have h2 : ContDiff ℝ (↑(⊤ : ℕ∞)) (Complex.ofRealCLM : ℝ → ℂ) :=
      Complex.ofRealCLM.contDiff
    exact h2.comp (h3.comp h1)
  · intro θ
    rfl
  · intro θ hθ
    have hpos : (0:ℝ) < (2:ℝ)^k := zpow_pos (by norm_num) k
    refine kmtEta_zero ?_
    rw [abs_div, abs_of_pos hpos, one_le_div hpos]
    exact hθ

end Work.KMTContract
