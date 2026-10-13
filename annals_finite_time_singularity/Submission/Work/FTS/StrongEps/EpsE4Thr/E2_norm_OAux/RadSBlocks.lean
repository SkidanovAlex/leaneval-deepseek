import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2_norm_OAux.RadSMaj

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E2O

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The block sums of the majorant -/

/-- The `L₁₂`-slot sum at level `n`. -/
noncomputable def LSlotSum (n : ℕ) (f : Fn) : ℝ → ℝ := fun z =>
  ∑ i ∈ Finset.range (n + 1),
    (Work.Elliptic.DzdIter i (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2

/-- The angular-moment slot sum at level `n`. -/
noncomputable def QSlotSum (n : ℕ) (f : Fn) : ℝ → ℝ := fun z =>
  ∑ i ∈ Finset.range (n + 1), (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2

/-- The `ampB`-slot sum at level `n`. -/
noncomputable def BSlotSum (n : ℕ) (α : ℝ) : ℝ → ℝ := fun z =>
  ∑ i ∈ Finset.range (n + 1),
    (Work.Elliptic.DzdIter (i + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
      * (Work.Spaces.w z) ^ 2

/-- The projector constant of the third block of the majorant. -/
noncomputable def SConst (α : ℝ) (f : Fn) : ℝ :=
  (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2

/-- The sum of the squared binomial coefficients is at most `4^j`. -/
private theorem sum_choose_sq_le (j : ℕ) :
    (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) ≤ 4 ^ j := by
  have hsum : (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ)) = (2 : ℝ) ^ j := by
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
  have hcb : ∀ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ≤ (2 : ℝ) ^ j := by
    intro b hb
    have h1 := Finset.single_le_sum (f := fun i : ℕ => ((j.choose i : ℕ) : ℝ))
      (fun i _ => Nat.cast_nonneg _) hb
    rwa [hsum] at h1
  calc (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2)
      ≤ ∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) * (2 : ℝ) ^ j := by
        refine Finset.sum_le_sum fun b hb => ?_
        rw [sq]
        exact mul_le_mul_of_nonneg_left (hcb b hb) (Nat.cast_nonneg _)
    _ = (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ)) * (2 : ℝ) ^ j := by
        rw [Finset.sum_mul]
    _ = 4 ^ j := by
        rw [hsum, ← mul_pow]
        norm_num

/-- The block sums are nonnegative. -/
theorem LSlotSum_nonneg (n : ℕ) (f : Fn) (z : ℝ) : 0 ≤ LSlotSum n f z := by
  simp only [LSlotSum]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem QSlotSum_nonneg (n : ℕ) (f : Fn) (z : ℝ) : 0 ≤ QSlotSum n f z := by
  simp only [QSlotSum]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem BSlotSum_nonneg (n : ℕ) (α : ℝ) (z : ℝ) : 0 ≤ BSlotSum n α z := by
  simp only [BSlotSum]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

theorem SConst_nonneg (α : ℝ) (f : Fn) : 0 ≤ SConst α f := by
  rw [SConst]; exact sq_nonneg _

/-! ## The per-`j` bound of the majorant -/

/-- **Each summand of the majorant is dominated by the three block sums.** -/
theorem SmajA_le_blocks (α : ℝ) {f : Fn} {n : ℕ} (hn : n ≤ 3) {KA : ℝ} (hKA2 : 0 ≤ KA ^ 2)
    {j : ℕ} (hj : j ≤ n) {z : ℝ} :
    Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA α f j KA z
      ≤ 771 * (KA ^ 2 * LSlotSum n f z + KA ^ 2 * QSlotSum n f z
          + SConst α f * BSlotSum n α z) := by
  have hj3 : j ≤ 3 := by omega
  have hAj : (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) ≤ 64 := by
    calc (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) ≤ 4 ^ j := sum_choose_sq_le j
      _ ≤ 4 ^ 3 := pow_le_pow_right₀ (by norm_num) hj3
      _ = 64 := by norm_num
  have hS1 : (∑ b ∈ Finset.range (j + 1),
        (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ ((j : ℝ) + 1) * LSlotSum n f z := by
    have hb : ∀ b ∈ Finset.range (j + 1),
        (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
          * (Work.Spaces.w z) ^ 2 ≤ LSlotSum n f z := by
      intro b hb
      have hbj : j - b ≤ n := by have := Finset.mem_range.mp hb; omega
      have hmem : (j - b) ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
      simp only [LSlotSum]
      exact Finset.single_le_sum (f := fun i => (Work.Elliptic.DzdIter i
          (Work.Coercivity.L12f f) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hmem
    calc (∑ b ∈ Finset.range (j + 1),
          (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _b ∈ Finset.range (j + 1), LSlotSum n f z := Finset.sum_le_sum hb
      _ = ((j : ℝ) + 1) * LSlotSum n f z := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hS2 : (∑ b ∈ Finset.range (j + 1),
        (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ((j : ℝ) + 1) * QSlotSum n f z := by
    have hb : ∀ b ∈ Finset.range (j + 1),
        (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ QSlotSum n f z := by
      intro b hb
      have hbj : j - b ≤ n := by have := Finset.mem_range.mp hb; omega
      have hmem : (j - b) ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
      simp only [QSlotSum]
      exact Finset.single_le_sum (f := fun i => (Work.Elliptic.Qang f i z) ^ 2
          * (Work.Spaces.w z) ^ 2)
        (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hmem
    calc (∑ b ∈ Finset.range (j + 1),
          (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _b ∈ Finset.range (j + 1), QSlotSum n f z := Finset.sum_le_sum hb
      _ = ((j : ℝ) + 1) * QSlotSum n f z := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  have hS3 : (Work.Elliptic.DzdIter (j + 1)
        (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ BSlotSum n α z := by
    have hmem : j ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    simp only [BSlotSum]
    exact Finset.single_le_sum (f := fun i => (Work.Elliptic.DzdIter (i + 1)
        (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hmem
  have hS1nn : 0 ≤ (∑ b ∈ Finset.range (j + 1),
      (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) :=
    Finset.sum_nonneg fun b _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hS2nn : 0 ≤ (∑ b ∈ Finset.range (j + 1),
      (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2) :=
    Finset.sum_nonneg fun b _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have e1 : (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2
        * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
              * (Work.Spaces.w z) ^ 2)
      ≤ 256 * (KA ^ 2 * LSlotSum n f z) := by
    have h1 : (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2
        ≤ 64 * KA ^ 2 := mul_le_mul_of_nonneg_right hAj hKA2
    have hj4 : ((j : ℝ) + 1) ≤ 4 := by
      have : (j : ℝ) ≤ 3 := by exact_mod_cast hj3
      linarith
    calc (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
                * (Work.Spaces.w z) ^ 2)
        ≤ (64 * KA ^ 2) * (((j : ℝ) + 1) * LSlotSum n f z) :=
          mul_le_mul h1 hS1 hS1nn (by positivity)
      _ ≤ (64 * KA ^ 2) * (4 * LSlotSum n f z) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hj4 (LSlotSum_nonneg n f z)
      _ = 256 * (KA ^ 2 * LSlotSum n f z) := by ring
  have e2 : (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2
        * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 256 * (KA ^ 2 * QSlotSum n f z) := by
    have h1 : (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2
        ≤ 64 * KA ^ 2 := mul_le_mul_of_nonneg_right hAj hKA2
    have hj4 : ((j : ℝ) + 1) ≤ 4 := by
      have : (j : ℝ) ≤ 3 := by exact_mod_cast hj3
      linarith
    calc (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2
          * (∑ b ∈ Finset.range (j + 1),
              (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ (64 * KA ^ 2) * (((j : ℝ) + 1) * QSlotSum n f z) :=
          mul_le_mul h1 hS2 hS2nn (by positivity)
      _ ≤ (64 * KA ^ 2) * (4 * QSlotSum n f z) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hj4 (QSlotSum_nonneg n f z)
      _ = 256 * (KA ^ 2 * QSlotSum n f z) := by ring
  have e3 : SConst α f * ((Work.Elliptic.DzdIter (j + 1)
          (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ 64 * (SConst α f * BSlotSum n α z) := by
    have h1 : SConst α f * ((Work.Elliptic.DzdIter (j + 1)
          (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ SConst α f * BSlotSum n α z := mul_le_mul_of_nonneg_left hS3 (SConst_nonneg α f)
    have hnn : 0 ≤ SConst α f * BSlotSum n α z :=
      mul_nonneg (SConst_nonneg α f) (BSlotSum_nonneg n α z)
    linarith [h1, hnn]
  have hLnn : 0 ≤ LSlotSum n f z := LSlotSum_nonneg n f z
  have hQnn : 0 ≤ QSlotSum n f z := QSlotSum_nonneg n f z
  have hBnn : 0 ≤ BSlotSum n α z := BSlotSum_nonneg n α z
  have hD2nn : 0 ≤ SConst α f := SConst_nonneg α f
  rw [Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA]
  have hgoal : 3 * ((∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2
        * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.DzdIter (j - b) (Work.Coercivity.L12f f) z) ^ 2
              * (Work.Spaces.w z) ^ 2)
      + (∑ b ∈ Finset.range (j + 1), ((j.choose b : ℕ) : ℝ) ^ 2) * KA ^ 2
        * (∑ b ∈ Finset.range (j + 1),
            (Work.Elliptic.Qang f (j - b) z) ^ 2 * (Work.Spaces.w z) ^ 2)
      + SConst α f * ((Work.Elliptic.DzdIter (j + 1)
          (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2 * (Work.Spaces.w z) ^ 2))
      ≤ 771 * (KA ^ 2 * LSlotSum n f z + KA ^ 2 * QSlotSum n f z
          + SConst α f * BSlotSum n α z) := by
    have hX : 0 ≤ KA ^ 2 * LSlotSum n f z := mul_nonneg hKA2 hLnn
    have hY : 0 ≤ KA ^ 2 * QSlotSum n f z := mul_nonneg hKA2 hQnn
    have hZ : 0 ≤ SConst α f * BSlotSum n α z := mul_nonneg hD2nn hBnn
    nlinarith [e1, e2, e3, hX, hY, hZ]
  exact hgoal

/-! ## The sum-level pointwise bound -/

/-- **The level-`n` slot sum of `radS` is dominated by the three block sums.** -/
theorem radS_sum_le (α : ℝ) {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {n : ℕ} (hn : n ≤ 3)
    (hO : Work.FTS.EllipticEst.SmoothOpen f) (hmem5 : Work.Spaces.HkMem α 5 f)
    (hl12 : Work.Construction.L12 f 0 = 0) {KA : ℝ} (hKAnn : 0 ≤ KA)
    (hKbd : ∀ b ≤ 4, ∀ z ∈ IoiA,
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ KA) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ 3084 * (KA ^ 2 * LSlotSum n f z + KA ^ 2 * QSlotSum n f z
            + SConst α f * BSlotSum n α z) := by
  have hKA2 : 0 ≤ KA ^ 2 := sq_nonneg KA
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => ?_)
  have hw0 : Work.Spaces.w (0 : ℝ) = 0 := by
    simp only [Work.Spaces.w]; norm_num
  have hL0 : LSlotSum n f 0 = 0 := by
    simp only [LSlotSum, hw0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      Finset.sum_const_zero]
  have hQ0 : QSlotSum n f 0 = 0 := by
    simp only [QSlotSum, hw0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      Finset.sum_const_zero]
  have hB0 : BSlotSum n α 0 = 0 := by
    simp only [BSlotSum, hw0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero,
      Finset.sum_const_zero]
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    rw [hL0, hQ0, hB0]
    simp only [hw0, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, Finset.sum_const_zero,
      mul_assoc, mul_zero, add_zero, le_refl]
  · have h1 : (∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ ∑ j ∈ Finset.range (n + 1),
            Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA α f j KA z :=
      Finset.sum_le_sum (fun j hj =>
        radS_sq_le_SmajA_O α hα hα1 hO hmem5 hl12
          (by have := Finset.mem_range.mp hj; omega) hKAnn hKbd z hzpos)
    have h2 : (∑ j ∈ Finset.range (n + 1),
            Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA α f j KA z)
        ≤ 3084 * (KA ^ 2 * LSlotSum n f z + KA ^ 2 * QSlotSum n f z
            + SConst α f * BSlotSum n α z) := by
      have hsum : (∑ j ∈ Finset.range (n + 1),
              Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA α f j KA z)
          ≤ ∑ _j ∈ Finset.range (n + 1), 771 * (KA ^ 2 * LSlotSum n f z
              + KA ^ 2 * QSlotSum n f z + SConst α f * BSlotSum n α z) :=
        Finset.sum_le_sum (fun j hj =>
          SmajA_le_blocks α hn hKA2 (by have := Finset.mem_range.mp hj; omega))
      have hconst : (∑ _j ∈ Finset.range (n + 1), 771 * (KA ^ 2 * LSlotSum n f z
            + KA ^ 2 * QSlotSum n f z + SConst α f * BSlotSum n α z))
          = ((n : ℝ) + 1) * (771 * (KA ^ 2 * LSlotSum n f z
              + KA ^ 2 * QSlotSum n f z + SConst α f * BSlotSum n α z)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring
      have hn4 : ((n : ℝ) + 1) ≤ 4 := by
        have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
        linarith
      have hYnn : 0 ≤ 771 * (KA ^ 2 * LSlotSum n f z + KA ^ 2 * QSlotSum n f z
          + SConst α f * BSlotSum n α z) := by
        have h1 : 0 ≤ KA ^ 2 * LSlotSum n f z := mul_nonneg hKA2 (LSlotSum_nonneg n f z)
        have h2 : 0 ≤ KA ^ 2 * QSlotSum n f z := mul_nonneg hKA2 (QSlotSum_nonneg n f z)
        have h3 : 0 ≤ SConst α f * BSlotSum n α z :=
          mul_nonneg (SConst_nonneg α f) (BSlotSum_nonneg n α z)
        linarith
      calc (∑ j ∈ Finset.range (n + 1),
              Work.FTS.CoercivityFix.Transfer.E2pkg.SmajA α f j KA z)
          ≤ ∑ _j ∈ Finset.range (n + 1), 771 * (KA ^ 2 * LSlotSum n f z
              + KA ^ 2 * QSlotSum n f z + SConst α f * BSlotSum n α z) := hsum
        _ = ((n : ℝ) + 1) * (771 * (KA ^ 2 * LSlotSum n f z
              + KA ^ 2 * QSlotSum n f z + SConst α f * BSlotSum n α z)) := hconst
        _ ≤ 4 * (771 * (KA ^ 2 * LSlotSum n f z
              + KA ^ 2 * QSlotSum n f z + SConst α f * BSlotSum n α z)) :=
            mul_le_mul_of_nonneg_right hn4 hYnn
        _ = 3084 * (KA ^ 2 * LSlotSum n f z + KA ^ 2 * QSlotSum n f z
              + SConst α f * BSlotSum n α z) := by ring
    linarith [h1, h2]

end Work.FTS.StrongEps.EpsE4Thr.E2O
