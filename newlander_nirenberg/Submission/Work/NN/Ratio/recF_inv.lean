import Mathlib
import Submission.Work.NN.Ratio.Defs

namespace Work.NN.Ratio

open scoped ContDiff

/-- **Invariants of the telescoping recursion.**

At every stage `s ≤ n` of the recursion `G.recF f`:

* the data are still `C^{k+1}`;
* for every already processed direction `l < s` the data are `∂̄_l`-holomorphic on the
  region `‖z l‖ < G.a` on which the cutoff is identically `1`;
* for every pair of not yet processed directions `i, l ≥ s` the data are still closed.

These are the three properties the construction of `G.recU` needs. -/
theorem recF_inv {n : ℕ} {k : ℕ} (G : Work.NN.Ratio.Geom n)
    {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiff ℝ (k + 1) (f j)) (hcl : Work.CR.Flat.IsClosedForm f) :
    ∀ s : ℕ, s ≤ n →
      (∀ j, ContDiff ℝ (k + 1) (G.recF f s j)) ∧
      (∀ l : Fin n, (l : ℕ) < s → ∀ j z, ‖z l‖ < G.a →
        Work.CR.Flat.dbarCoord l (G.recF f s j) z = 0) ∧
      (∀ i l : Fin n, s ≤ (i : ℕ) → s ≤ (l : ℕ) → ∀ z,
        Work.CR.Flat.dbarCoord l (G.recF f s i) z = Work.CR.Flat.dbarCoord i (G.recF f s l) z) := by
  intro s
  induction s with
  | zero =>
      intro _
      refine ⟨hf, ?_, ?_⟩
      · intro l hl; exact absurd hl (Nat.not_lt_zero _)
      · intro i l _ _ z; exact (hcl l i z).symm
  | succ s ihs =>
      intro hs
      obtain ⟨ih1, ih2, ih3⟩ := ihs (by omega)
      by_cases hlt : s < n
      · set j : Fin n := ⟨s, hlt⟩ with hj
        have hjs : (j : ℕ) = s := rfl
        have hrec : G.recF f (s + 1) = G.stepData j (G.recF f s) := by
          exact Geom.recF_succ_of_lt (G := G) hlt
        have hC1 : ∀ i : Fin n, ContDiff ℝ 1 (fun y => G.cutFbar j y * G.recF f s i y) := fun i =>
          (((Geom.contDiff_cutFbar (G := G) j).of_le (le_infty _)).mul (ih1 i)).of_le
            (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero k))
        refine ⟨?_, ?_, ?_⟩
        · -- smoothness at the next stage
          intro i
          rw [hrec]
          simp only [Geom.stepData]
          exact Work.CR.Flat.Cauchy.contDiff_dbarTransform (ρ := G.r) (b := G.b)
            (by linarith [G.hr, G.hab, G.ha]) j (k + 1)
            (((Geom.contDiff_cutFbar (G := G) j).of_le (le_infty _)).mul (ih1 i))
            (fun y hy => by rw [Geom.cutFbar_eq_zero_of_ge (G := G) hy, zero_mul])
        · -- holomorphy in the processed directions
          intro l hl i z hz
          rw [hrec]
          simp only [Geom.stepData]
          rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hlt' | heq
          · -- `l` was already processed before
            have hne : l ≠ j := by
              intro hlj; rw [hlj, hjs] at hlt'; exact absurd hlt' (by omega)
            rw [Work.CR.Flat.Cauchy.dbarTransform_dbarCoord (ρ := G.r) j l (hC1 i) z]
            rw [Work.CR.Flat.Cauchy.dbarTransform_eq_zero_of_fiber]
            intro y hy
            rw [Geom.dbarCoord_cutFbar_mul (G := G) hne
              ((ih1 i).differentiable (by simp)).differentiableAt]
            have hyl : ‖y l‖ < G.a := by rw [hy l hne]; exact hz
            rw [ih2 l hlt' i y hyl, mul_zero]
          · -- `l = j` is the new direction
            have hlj : l = j := by ext; rw [hjs]; exact heq
            subst hlj
            rw [Work.CR.Flat.Cauchy.dbarTransform_dbarCoord (ρ := G.r) j j (hC1 i) z]
            have hz' : ‖z j‖ < G.r / 2 := by linarith [hz, G.hab, G.hr]
            rw [Work.CR.Flat.Cauchy.dbarTransform_dbarCoord_self (ρ := G.r) G.hr0 j (hC1 i)
              (fun y hy => by
                rw [Geom.cutFbar_eq_zero_of_ge (G := G)
                  (show G.b ≤ ‖y j‖ from by linarith [G.hr, hy]), zero_mul])
              hz']
            rw [Geom.cutFbar_eq_zero_of_le (G := G) (le_of_lt hz), zero_mul]
        · -- closedness is preserved on the unprocessed directions
          intro i l hi hl z
          rw [hrec]
          simp only [Geom.stepData]
          have hine : i ≠ j := by
            intro hij; rw [hij, hjs] at hi; exact absurd hi (by omega)
          have hlne : l ≠ j := by
            intro hlj; rw [hlj, hjs] at hl; exact absurd hl (by omega)
          have hfun : (fun y => Work.CR.Flat.dbarCoord l
                (fun y' => G.cutFbar j y' * G.recF f s i y') y)
              = fun y => Work.CR.Flat.dbarCoord i
                (fun y' => G.cutFbar j y' * G.recF f s l y') y := by
            funext y
            rw [Geom.dbarCoord_cutFbar_mul (G := G) hlne
                ((ih1 i).differentiable (by simp)).differentiableAt,
              Geom.dbarCoord_cutFbar_mul (G := G) hine
                ((ih1 l).differentiable (by simp)).differentiableAt,
              ih3 i l (by omega) (by omega) y]
          rw [Work.CR.Flat.Cauchy.dbarTransform_dbarCoord (ρ := G.r) j l (hC1 i) z,
            Work.CR.Flat.Cauchy.dbarTransform_dbarCoord (ρ := G.r) j i (hC1 l) z, hfun]
      · -- all coordinates have been processed: nothing changes any more
        have hrec : G.recF f (s + 1) = G.recF f s := by
          rw [Geom.recF_succ (G := G) (f := f)]; simp [hlt]
        have hsn : n ≤ s := not_lt.mp hlt
        rw [hrec]
        refine ⟨ih1, ?_, ?_⟩
        · intro l hl i z hz
          exact ih2 l (by omega) i z hz
        · intro i l hi hl z
          exact ih3 i l (by omega) (by omega) z

end Work.NN.Ratio
