import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Complex.BigOperators
import Submission.Work.BoseB4.ModeFock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PotCubicLowBandAux

/-- The real frame bound `∑_k ⟪f k, w⟫² ≤ C ‖w‖²` for real vectors `w` (where the pairing is
`Work.BoseB4.gram`), with all the `f k` orthogonal to the `0`-th coordinate, extends to complex
vectors `u : Fin m → ℂ`, with the `0`-th coordinate dropped from the right-hand side.

Writing `u l = (u l).re + (u l).im · I`, the sum `∑_l (f k l : ℂ) · u l` splits into its real and
imaginary parts, and `‖z‖² = z.re² + z.im²`; since `f k 0 = 0`, both real vectors
`l ↦ if l = 0 then 0 else (u l).re` and `l ↦ if l = 0 then 0 else (u l).im` pair with `f k` exactly
as the (unmodified) real and imaginary parts of `u` do, so the real frame bound applies to each. -/
theorem frame_complex {m : ℕ} [NeZero m] {ι : Type*} [Fintype ι]
    (f : ι → Fin m → ℝ) (C : ℝ)
    (hframe : ∀ w : Fin m → ℝ,
      ∑ k : ι, (Work.BoseB4.gram (f k) w) ^ 2 ≤ C * ∑ l : Fin m, (w l) ^ 2)
    (h0 : ∀ k : ι, f k 0 = 0) (u : Fin m → ℂ) :
    ∑ k : ι, ‖∑ l : Fin m, (((f k) l : ℝ) : ℂ) * u l‖ ^ 2
      ≤ C * ∑ l ∈ (Finset.univ.erase (0 : Fin m)), ‖u l‖ ^ 2 := by
  set A : Fin m → ℝ := fun l => if l = 0 then 0 else (u l).re with hA
  set B : Fin m → ℝ := fun l => if l = 0 then 0 else (u l).im with hB
  have hkey : ∀ k : ι, ‖∑ l : Fin m, (((f k) l : ℝ) : ℂ) * u l‖ ^ 2
      = (Work.BoseB4.gram (f k) A) ^ 2 + (Work.BoseB4.gram (f k) B) ^ 2 := by
    intro k
    have hre : (∑ l : Fin m, (((f k) l : ℝ) : ℂ) * u l).re = Work.BoseB4.gram (f k) A := by
      rw [Complex.re_sum, Work.BoseB4.gram]
      apply Finset.sum_congr rfl
      intro l _
      by_cases hl : l = 0
      · subst hl; simp [hA, h0 k]
      · simp [hA, hl, Complex.mul_re]
    have him : (∑ l : Fin m, (((f k) l : ℝ) : ℂ) * u l).im = Work.BoseB4.gram (f k) B := by
      rw [Complex.im_sum, Work.BoseB4.gram]
      apply Finset.sum_congr rfl
      intro l _
      by_cases hl : l = 0
      · subst hl; simp [hB, h0 k]
      · simp [hB, hl, Complex.mul_im]
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  have hA0 : A 0 = 0 := by simp [hA]
  have hB0 : B 0 = 0 := by simp [hB]
  have hAsum : ∑ l : Fin m, (A l) ^ 2
      = ∑ l ∈ Finset.univ.erase (0 : Fin m), ((u l).re) ^ 2 := by
    rw [← Finset.sum_erase_add Finset.univ (fun l : Fin m => (A l) ^ 2) (Finset.mem_univ 0)]
    have hA02 : (A 0) ^ 2 = 0 := by rw [hA0]; norm_num
    rw [hA02, add_zero]
    apply Finset.sum_congr rfl
    intro l hl
    have hl0 : l ≠ 0 := (Finset.mem_erase.mp hl).1
    simp only [hA]
    rw [if_neg hl0]
  have hBsum : ∑ l : Fin m, (B l) ^ 2
      = ∑ l ∈ Finset.univ.erase (0 : Fin m), ((u l).im) ^ 2 := by
    rw [← Finset.sum_erase_add Finset.univ (fun l : Fin m => (B l) ^ 2) (Finset.mem_univ 0)]
    have hB02 : (B 0) ^ 2 = 0 := by rw [hB0]; norm_num
    rw [hB02, add_zero]
    apply Finset.sum_congr rfl
    intro l hl
    have hl0 : l ≠ 0 := (Finset.mem_erase.mp hl).1
    simp only [hB]
    rw [if_neg hl0]
  have hnorm : ∑ l ∈ Finset.univ.erase (0 : Fin m), ‖u l‖ ^ 2
      = (∑ l ∈ Finset.univ.erase (0 : Fin m), ((u l).re) ^ 2)
        + ∑ l ∈ Finset.univ.erase (0 : Fin m), ((u l).im) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro l _
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  calc ∑ k : ι, ‖∑ l : Fin m, (((f k) l : ℝ) : ℂ) * u l‖ ^ 2
      = ∑ k : ι, ((Work.BoseB4.gram (f k) A) ^ 2 + (Work.BoseB4.gram (f k) B) ^ 2) :=
        Finset.sum_congr rfl (fun k _ => hkey k)
    _ = (∑ k : ι, (Work.BoseB4.gram (f k) A) ^ 2)
          + ∑ k : ι, (Work.BoseB4.gram (f k) B) ^ 2 := Finset.sum_add_distrib
    _ ≤ C * (∑ l : Fin m, (A l) ^ 2) + C * ∑ l : Fin m, (B l) ^ 2 :=
        add_le_add (hframe A) (hframe B)
    _ = C * ∑ l ∈ (Finset.univ.erase (0 : Fin m)), ‖u l‖ ^ 2 := by
        rw [hAsum, hBsum, hnorm]; ring

end Work.BoseBoxFock.PotCubicLowBandAux
