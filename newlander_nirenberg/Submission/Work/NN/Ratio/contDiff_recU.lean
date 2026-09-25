import Mathlib
import Submission.Work.NN.Ratio.Defs

namespace Work.NN.Ratio

open scoped NNReal ENNReal ContDiff
open Set

theorem contDiff_recU {n : ℕ} (G : Work.NN.Ratio.Geom n) {k : ℕ}
    {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiff ℝ (k + 1) (f j)) :
    ContDiff ℝ (k + 1) (fun z => G.recU f z) := by
  have hrb : G.b < G.r := by
    have hb0 : 0 < G.b := lt_trans G.ha G.hab
    linarith [G.hr]
  have htransform : ∀ (j : Fin n) (g : (Fin n → ℂ) → ℂ), ContDiff ℝ (k + 1) g →
      (∀ y : Fin n → ℂ, G.b ≤ ‖y j‖ → g y = 0) →
      ContDiff ℝ (k + 1) (Work.CR.Flat.Cauchy.dbarTransform G.r j g) :=
    fun j g hg hsupp => Work.CR.Flat.Cauchy.contDiff_dbarTransform hrb j (k + 1) hg hsupp
  have hsm : ∀ m : ℕ, ∀ j : Fin n, ContDiff ℝ (k + 1) (G.recF f m j) := by
    intro m
    induction m with
    | zero => intro j; exact hf j
    | succ m ih =>
      intro j
      rcases Nat.lt_or_ge m n with h | h
      · rw [Geom.recF_succ_of_lt (G := G) h]
        exact htransform ⟨m, h⟩ (fun y => G.cutFbar ⟨m, h⟩ y * G.recF f m j y)
          (((Geom.contDiff_cutFbar (G := G) ⟨m, h⟩).of_le (le_infty (k + 1))).mul (ih j))
          (fun y hy => by rw [Geom.cutFbar_eq_zero_of_ge (G := G) hy, zero_mul])
      · have hrec : G.recF f (m + 1) = G.recF f m := by
          rw [Geom.recF_succ (G := G)]
          exact dite_eq_right (not_lt.mpr h)
        rw [hrec]
        exact ih j
  have hmain : ∀ j : Fin n, ContDiff ℝ (k + 1)
      (fun z => Work.CR.Flat.Cauchy.dbarTransform G.r j
        (fun y => G.cutF j y * G.recF f (j : ℕ) j y) z) := by
    intro j
    exact htransform j (fun y => G.cutF j y * G.recF f (j : ℕ) j y)
      (((Geom.contDiff_cutF (G := G) j).of_le (le_infty (k + 1))).mul (hsm (j : ℕ) j))
      (fun y hy => by rw [Geom.cutF_eq_zero (G := G) hy, zero_mul])
  have hgoal : (fun z => G.recU f z)
      = fun z => ∑ j : Fin n, Work.CR.Flat.Cauchy.dbarTransform G.r j
          (fun y => G.cutF j y * G.recF f (j : ℕ) j y) z := rfl
  rw [hgoal]
  exact ContDiff.sum (fun j _ => hmain j)

end Work.NN.Ratio
