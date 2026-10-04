import Mathlib
import Submission.Work.Diff.STE.flat.coeffDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

theorem coeffA_smooth_periodic {n : ℕ} {T : ℝ}
    (u : ℝ → Work.Diff.STE.Flat.Torus n)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => u p.1 p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ))
    (huper : ∀ t ∈ Set.Ico (0:ℝ) T, Work.Diff.STE.Periodic1 (u t))
    (lam : ℝ) (hlam : 0 < lam)
    (hell : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x : Fin n → ℝ, ∀ ξ : Fin n → ℝ,
      lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j,
        Work.Diff.STE.Flat.reMat (u t x) i j * ξ i * ξ j) :
    (∀ c d : Fin n, ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × (Fin n → ℝ) => Work.Diff.STE.flat.coeffA u p.1 p.2 c d)
        (Set.Ico (0:ℝ) T ×ˢ Set.univ)) ∧
      (∀ t ∈ Set.Ico (0:ℝ) T, Work.Diff.STE.Periodic1 (Work.Diff.STE.flat.coeffA u t)) := by
  -- The entries of `reMat (u t x)` are jointly smooth on `Ico 0 T × univ`.
  have hmat : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => Work.Diff.STE.Flat.reMat (u p.1 p.2) i j)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) :=
    fun i j => contDiffOn_reMat_entry hu i j
  -- The uniform ellipticity hypothesis forces `det ≠ 0` everywhere on the strip.
  have hdet : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x,
      (Work.Diff.STE.Flat.reMat (u t x)).det ≠ 0 :=
    fun t ht x => det_ne_zero_of_quadratic hlam (hell t ht x)
  -- Hence the entries of the inverse matrix are jointly smooth.
  have hinv : ∀ c d, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => ((Work.Diff.STE.Flat.reMat (u p.1 p.2))⁻¹) c d)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) :=
    fun c d => contDiffOn_matrixInv_entry hmat hdet c d
  refine ⟨fun c d => ?_, fun t ht => ?_⟩
  · -- `coeffA u t x c d = ((reMat (u t x))⁻¹ c d + (reMat (u t x))⁻¹ d c) / 2`
    have hfun : (fun p : ℝ × (Fin n → ℝ) => Work.Diff.STE.flat.coeffA u p.1 p.2 c d)
        = fun p : ℝ × (Fin n → ℝ) =>
            (((Work.Diff.STE.Flat.reMat (u p.1 p.2))⁻¹) c d
              + ((Work.Diff.STE.Flat.reMat (u p.1 p.2))⁻¹) d c) / 2 := by
      funext p
      exact coeffA_apply u p.1 p.2 c d
    rw [hfun]
    exact ((hinv c d).add (hinv d c)).div_const 2
  · -- periodicity: transport `Periodic1 (u t)` through `reMat` and the matrix inverse
    intro i x
    have hperRe : Work.Diff.STE.Periodic1
        (fun y : Fin n → ℝ => Work.Diff.STE.Flat.reMat (u t y)) :=
      fun j y => by
        show Work.Diff.STE.Flat.reMat (u t (y + Pi.single j 1)) = Work.Diff.STE.Flat.reMat (u t y)
        rw [huper t ht j y]
    ext c d
    have hcd := Periodic1.matrixInv_entry hperRe c d i x
    have hdc := Periodic1.matrixInv_entry hperRe d c i x
    simp only [] at hcd hdc
    simp only [coeffA_apply]
    rw [hcd, hdc]

end Work.Diff.STE.flat
