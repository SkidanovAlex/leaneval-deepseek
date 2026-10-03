import Mathlib
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.Setup

namespace Work.Pert

open MandelDim Complex Set

/-- A legal level of `w` in `Dphi` immediately gives a level for `GoodP`: the seed value is
`τ (F^[n] ζ)`, and `hτF`/`hτD` put its partial orbit in `Df`. -/
theorem goodP_of_mem_Dphi {f : ℂ → ℂ} {Df : Set ℂ} {F τ Φ : ℂ → ℂ} {Q : Set ℂ} {w : ℂ}
    (hinj : Set.InjOn Φ Q) (hab : ∀ z ∈ Q, F z ∈ Q → Φ (F z) = Φ z + 1)
    (hτF : ∀ z ∈ Q, τ (F z) = f (τ z)) (hτD : ∀ z ∈ Q, τ z ∈ Df)
    (hw : w ∈ Dphi F Φ Q) : GoodP f Df τ Φ Q w := by
  obtain ⟨n, ζ, hζQ, hΦζ, hwalk⟩ := hw
  have hex : ∃ y ∈ Q, Φ y = w - (n : ℂ) := ⟨ζ, hζQ, hΦζ⟩
  have hseed : seedP τ Φ Q (w - (n : ℂ)) = τ ζ := by
    simp only [seedP]
    rw [invOn_eq hinj hex hζQ hΦζ]
  refine ⟨n, ⟨ζ, hζQ, hΦζ⟩, ?_⟩
  have hiter : ∀ j : ℕ, j ≤ n → f^[j] (τ ζ) = τ (F^[j] ζ) := by
    intro j hj
    induction j with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega)]
      exact (hτF (F^[k] ζ) (hwalk k (by omega))).symm
  intro j hj
  rw [hseed, hiter j (by omega)]
  exact hτD (F^[j] ζ) (hwalk j (by omega))

end Work.Pert
