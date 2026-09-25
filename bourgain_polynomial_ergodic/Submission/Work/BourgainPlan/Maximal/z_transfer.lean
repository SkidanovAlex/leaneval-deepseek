import Mathlib
import Submission.Work.BourgainPlan.Maximal.z_defs
import Submission.Work.BourgainPlan.Maximal.foundations

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

namespace Work.BourgainPlan.Maximal

open Submission.BourgainPlan (discAvg NonnegOnNat)

/-! ## The measure-theoretic transfer `ℕ → ℤ` -/

/-- **Transfer of `ℓᵖ`-integrals from `ℕ` to `ℤ`.**  For every `f : ℕ → ℝ≥0∞`,
`∫⁻_ℕ f = ∫⁻_ℤ 1_{m ≥ 0} · f(m.toNat)`. -/
lemma lintegral_count_nat_int (f : ℕ → ℝ≥0∞) :
    ∫⁻ n : ℕ, f n ∂Measure.count
      = ∫⁻ m : ℤ, (if 0 ≤ m then f m.toNat else 0) ∂Measure.count := by
  rw [MeasureTheory.lintegral_count, MeasureTheory.lintegral_count]
  set F : ℤ → ℝ≥0∞ := fun m => if 0 ≤ m then f m.toNat else 0 with hF
  have hsupp : Function.support F ⊆ {m : ℤ | 0 ≤ m} := by
    intro m hm
    rw [Set.mem_ofPred_eq]
    by_contra h
    simp [hF, h] at hm
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  let e : ℕ ≃ {m : ℤ | 0 ≤ m} :=
    { toFun := fun n => ⟨(n : ℤ), by simp⟩
      invFun := fun m => m.1.toNat
      left_inv := by intro n; simp [Int.toNat_natCast]
      right_inv := by
        intro m
        simp only [Subtype.ext_iff]
        exact Int.toNat_of_nonneg m.2 }
  rw [← Equiv.tsum_eq e (fun x : {m : ℤ | 0 ≤ m} => F x.val)]
  apply tsum_congr
  intro n
  simp [F, e]

/-! ## The `ℤ`-extension of a function on `ℕ` -/

/-- The extension of `g : ℕ → ℝ` to `ℤ`, zero on the negative integers. -/
noncomputable def liftZ (g : ℕ → ℝ) : ℤ → ℝ := fun m => if 0 ≤ m then g m.toNat else 0

lemma liftZ_of_nonneg (g : ℕ → ℝ) {m : ℤ} (h : 0 ≤ m) : liftZ g m = g m.toNat := by
  simp [liftZ, h]

lemma liftZ_of_neg (g : ℕ → ℝ) {m : ℤ} (h : ¬ 0 ≤ m) : liftZ g m = 0 := by
  simp [liftZ, h]

/-- **The `ℤ`-average of the extension is the `ℕ`-average.** -/
lemma discAvgZ_liftZ (P : Polynomial ℤ) (N : ℕ) (g : ℕ → ℝ) (n : ℕ) :
    discAvgZ P N (liftZ g) (n : ℤ) = discAvg P N g n := by
  rw [discAvg_eq_sum]
  unfold discAvgZ liftZ
  congr 1

/-- **The `ℤ`-maximal function of the extension is the `ℕ`-maximal function.** -/
lemma maxFZ_liftZ (P : Polynomial ℤ) (g : ℕ → ℝ) (n : ℕ) :
    maxFZ P (liftZ g) (n : ℤ) = ⨆ N : ℕ, ‖discAvg P N g n‖ₑ := by
  unfold maxFZ
  apply iSup_congr
  intro N
  rw [discAvgZ_liftZ]

/-- The extension of a finitely supported function is finitely supported. -/
lemma liftZ_support (g : ℕ → ℝ) (s : Finset ℕ) (hs : ∀ n, n ∉ s → g n = 0) :
    ∃ s' : Finset ℤ, ∀ m, m ∉ s' → liftZ g m = 0 := by
  refine ⟨s.image (fun n : ℕ => (n : ℤ)), ?_⟩
  intro m hm
  by_cases h : 0 ≤ m
  · rw [liftZ_of_nonneg _ h]
    exact hs m.toNat fun hmem => hm (Finset.mem_image.mpr ⟨m.toNat, hmem, Int.toNat_of_nonneg h⟩)
  · exact liftZ_of_neg _ h

/-- **The `ℓᵖ`-norm of the extension is the `ℓᵖ`-norm of `g`.** -/
lemma liftZ_norm_lintegral (g : ℕ → ℝ) {p : ℝ} (hp : 0 < p) :
    ∫⁻ m : ℤ, ‖liftZ g m‖ₑ ^ p ∂Measure.count
      = ∫⁻ n : ℕ, ‖g n‖ₑ ^ p ∂Measure.count := by
  rw [lintegral_count_nat_int (fun n => ‖g n‖ₑ ^ p)]
  apply MeasureTheory.lintegral_congr
  intro m
  by_cases h : 0 ≤ m
  · rw [if_pos h, liftZ_of_nonneg _ h]
  · rw [if_neg h, liftZ_of_neg _ h, enorm_zero, ENNReal.zero_rpow_of_pos hp]

/-- **The `ℤ`-form of the maximal inequality implies the `ℕ`-form.**
If Bourgain's discrete maximal inequality holds for functions on `ℤ` and the `ℤ`-maximal
function `maxFZ`, then `Submission.BourgainPlan.MaximalStatement` holds.

Route: given a finitely supported `g : ℕ → ℝ`, extend it to `G : ℤ → ℝ` by `G m = g m.toNat` for
`m ≥ 0` and `G m = 0` for `m < 0`.  For `n : ℕ` the `ℤ`-average of `G` at `m = (n : ℤ)` is exactly
`(N)⁻¹ ∑_{i<N} g (n + P i)`, which is `discAvg P N g n` by `discAvg_eq_sum`; moreover `G` is
finitely supported.  Hence `sup_N ‖discAvg P N g n‖ₑ = maxFZ P G (n : ℤ)`, and the `ℓᵖ(ℕ)`-integral
is bounded by the `ℓᵖ(ℤ)`-integral, while `∫⁻_ℤ ‖G‖ₑ^p = ∫⁻_ℕ ‖g‖ₑ^p`. -/
theorem z_transfer (hZ : Work.BourgainPlan.Maximal.MaximalStatementZ) :
    Submission.BourgainPlan.MaximalStatement := by
  intro P hP p hp
  obtain ⟨C, hC, hbound⟩ := hZ P hP p hp
  refine ⟨C, hC, ?_⟩
  intro g hg
  obtain ⟨s, hs⟩ := hg
  obtain ⟨s', hs'⟩ := liftZ_support g s hs
  have hp0 : (0 : ℝ) < p := by linarith
  have hG := hbound (liftZ g) ⟨s', hs'⟩
  have h1 : ∫⁻ n : ℕ, (⨆ N : ℕ, ‖discAvg P N g n‖ₑ) ^ p ∂Measure.count
      = ∫⁻ m : ℤ, (if 0 ≤ m then (⨆ N : ℕ, ‖discAvg P N g m.toNat‖ₑ) ^ p else 0)
          ∂Measure.count :=
    lintegral_count_nat_int (fun n => (⨆ N : ℕ, ‖discAvg P N g n‖ₑ) ^ p)
  have h2 : ∫⁻ m : ℤ, (if 0 ≤ m then (⨆ N : ℕ, ‖discAvg P N g m.toNat‖ₑ) ^ p else 0)
        ∂Measure.count
      ≤ ∫⁻ m : ℤ, (maxFZ P (liftZ g) m) ^ p ∂Measure.count := by
    apply MeasureTheory.lintegral_mono
    intro m
    dsimp only
    by_cases hm : 0 ≤ m
    · rw [if_pos hm]
      have heq : (⨆ N : ℕ, ‖discAvg P N g m.toNat‖ₑ) = maxFZ P (liftZ g) m := by
        rw [← maxFZ_liftZ P g m.toNat, Int.toNat_of_nonneg hm]
      rw [heq]
    · rw [if_neg hm]
      positivity
  rw [h1]
  refine le_trans h2 ?_
  refine le_trans hG ?_
  exact le_of_eq (by rw [liftZ_norm_lintegral g hp0])

end Work.BourgainPlan.Maximal
