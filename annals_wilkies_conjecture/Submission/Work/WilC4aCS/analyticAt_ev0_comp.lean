import Mathlib
import Submission.Work.WilC4aCS.Defs

namespace Work.WilC4aCS

open WilkiesDesign.E

/-- Reindex the componentwise hypothesis `hf` for the index type `Fin D ⊕ Fin 0`: the left
components are the original ones, the right components are (vacuously) constant zero. -/
private lemma analyticAt_ev0_comp_aux {n D : ℕ} (f : (Fin n → ℝ) → (Fin D → ℝ))
    (hf : ∀ i, AnalyticAt ℝ (fun x => f x i) 0) :
    ∀ i : Fin D ⊕ Fin 0,
      AnalyticAt ℝ (fun x => Sum.elim (f x) (fun _ : Fin 0 => (0 : ℝ)) i) 0 := by
  rintro (j | j)
  · exact hf j
  · exact Fin.elim0 j

theorem analyticAt_ev0_comp {n D : ℕ} (f : (Fin n → ℝ) → (Fin D → ℝ))
    (p : WilkiesDesign.E.EAPoly D 0) (hf : ∀ i, AnalyticAt ℝ (fun x => f x i) 0) :
    AnalyticAt ℝ (fun x => Work.WilC4aCS.ev0 (f x) p) 0 := by
  have h := AnalyticAt.aeval_mvPolynomial (𝕜 := ℝ) (z := (0 : Fin n → ℝ))
    (A := ℝ) (B := ℝ) (σ := Fin D ⊕ Fin 0)
    (f := fun x => Sum.elim (f x) (fun _ : Fin 0 => (0 : ℝ))) (p := p)
    (analyticAt_ev0_comp_aux f hf)
  simpa [Work.WilC4aCS.ev0] using h

end Work.WilC4aCS
