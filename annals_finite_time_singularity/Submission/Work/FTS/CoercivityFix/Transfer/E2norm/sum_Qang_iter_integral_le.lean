import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.Pieces

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS.CoercivityFix.Transfer.E2norm

/-- The half-line `[0,∞)` and the open half-line `(0,∞)` agree almost everywhere for the
Lebesgue measure of `ℝ`.  (Reproved here so that this module does not depend on a `private`
helper of `E2norm.Pieces`.) -/
private theorem Iz_ae_eq_Ioi' : Work.Spaces.Iz =ᵐ[volume] Set.Ioi (0 : ℝ) :=
  (MeasureTheory.Ioi_ae_eq_Ici (a := 0)).symm

theorem sum_Qang_iter_integral_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {n : ℕ} (hn : n ≤ 3)
    {f : ℝ → ℝ → ℝ} (hf : Work.FTS.Nonlin.CoerAdm α f) {j : ℕ} (hj : j ≤ n) :
    (∑ b ∈ Finset.range (j + 1), ∫ z in Set.Ioi (0 : ℝ),
        (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ((j : ℝ) + 1) * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkSq α n f) := by
  have hterm : ∀ b ∈ Finset.range (j + 1),
      (∫ z in Set.Ioi (0 : ℝ),
          (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n f := by
    intro b hb
    have hbj : j - b ≤ n := by
      have hle : b ≤ j := by
        simpa only [Finset.mem_range, Nat.lt_succ_iff] using hb
      omega
    have hq := (qang_sq_w_sq_le α hα hα1 hn hf (j - b) hbj).2
    rwa [MeasureTheory.setIntegral_congr_set Iz_ae_eq_Ioi'] at hq
  calc (∑ b ∈ Finset.range (j + 1), ∫ z in Set.Ioi (0 : ℝ),
          (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ∑ _b ∈ Finset.range (j + 1),
          (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n f :=
        Finset.sum_le_sum hterm
    _ = (Finset.range (j + 1)).card •
          ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n f) :=
        Finset.sum_const _
    _ = ((j : ℝ) + 1) * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkSq α n f) := by
        rw [Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

end Work.FTS.CoercivityFix.Transfer.E2norm
