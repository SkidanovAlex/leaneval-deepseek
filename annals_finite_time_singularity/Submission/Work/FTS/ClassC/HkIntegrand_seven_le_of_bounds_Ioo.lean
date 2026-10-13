import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.ClassC.PureVanishingReduction
import Submission.Work.FTS.ClassC.VanishFamilyDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassC

theorem HkIntegrand_seven_le_of_bounds_Ioo {α : ℝ} (hα : 0 < α)
    (hγ : Work.Spaces.gam α ≤ 3 / 2) {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) {G : ℝ → ℝ → ℝ}
    (hGnn : ∀ z : ℝ, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ G z θ)
    (h0 : ∀ j : ℕ, j ≤ 7 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ ≤ 4 * G z θ)
    (h1 : ∀ j r : ℕ, 1 ≤ r → r + j ≤ 7 → ∀ z : ℝ, 0 < z →
      ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) → Work.FTS.ClassC.vig α f r j z θ ≤ 4 * G z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.HkIntegrand α 7 f z θ
      ≤ (32 + 32 * Work.FTS.ClassC.vanSum α hα hγ f hsm 7) * G z θ := by
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hG : 0 ≤ G z θ := hGnn z θ hθ
  refine le_trans (HkIntegrand_le_pure_vanishing hα hγ hsm 7 z θ hzI hθI) ?_
  -- the pure radial slots: eight terms, each `≤ 4 G`
  have hbase : (∑ j ∈ Finset.range 8,
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ) ≤ 32 * G z θ := by
    calc ∑ j ∈ Finset.range 8, Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ
        ≤ ∑ j ∈ Finset.range 8, 4 * G z θ :=
          Finset.sum_le_sum fun j hj =>
            h0 j (by have h := Finset.mem_range.mp hj; omega) z hz θ hθ
      _ = 32 * G z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  -- the mixed slots: `vanC`-weighted `vig` sums, each bounded by `32 G`
  have hmixed : (∑ j ∈ Finset.range 8, ∑ i ∈ Finset.Icc 1 (7 - j),
        (if h : 1 ≤ i then vanC α hα hγ f hsm i j h else 0)
          * ∑ r ∈ Finset.Icc 1 i, vig α f r j z θ)
      ≤ 32 * vanSum α hα hγ f hsm 7 * G z θ := by
    have key : ∀ j ∈ Finset.range 8, ∀ i ∈ Finset.Icc 1 (7 - j),
        (if h : 1 ≤ i then vanC α hα hγ f hsm i j h else 0)
          * ∑ r ∈ Finset.Icc 1 i, vig α f r j z θ
        ≤ (if h : 1 ≤ i then vanC α hα hγ f hsm i j h else 0) * (32 * G z θ) := by
      intro j hj i hi
      by_cases hi1 : 1 ≤ i
      · rw [dif_pos hi1]
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (vanC_pos α hα hγ f hsm i j hi1))
        have hile : i ≤ 7 := by
          have h2 : i ≤ 7 - j := (Finset.mem_Icc.mp hi).2
          omega
        have hcard : (Finset.Icc 1 i).card = i := by
          rw [Nat.card_Icc]; exact Nat.add_sub_cancel i 1
        calc ∑ r ∈ Finset.Icc 1 i, vig α f r j z θ
            ≤ ∑ r ∈ Finset.Icc 1 i, 4 * G z θ :=
              Finset.sum_le_sum fun r hr => by
                have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
                have hr2 : r ≤ i := (Finset.mem_Icc.mp hr).2
                have h2 : i ≤ 7 - j := (Finset.mem_Icc.mp hi).2
                exact h1 j r hr1 (by omega) z hz θ hθ
          _ = (i : ℝ) * (4 * G z θ) := by
              rw [Finset.sum_const, hcard, nsmul_eq_mul]
          _ ≤ 32 * G z θ := by
              have hileR : (i : ℝ) ≤ 7 := by exact_mod_cast hile
              nlinarith [hG, hileR]
      · rw [dif_neg hi1]
        simp
    calc _ ≤ ∑ j ∈ Finset.range 8, ∑ i ∈ Finset.Icc 1 (7 - j),
          (if h : 1 ≤ i then vanC α hα hγ f hsm i j h else 0) * (32 * G z θ) :=
          Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun i hi => key j hj i hi
      _ = vanSum α hα hγ f hsm 7 * (32 * G z θ) := by
          rw [(by simp only [Finset.sum_mul] :
              (∑ j ∈ Finset.range 8, ∑ i ∈ Finset.Icc 1 (7 - j),
                (if h : 1 ≤ i then vanC α hα hγ f hsm i j h else 0)) * (32 * G z θ)
              = ∑ j ∈ Finset.range 8, ∑ i ∈ Finset.Icc 1 (7 - j),
                (if h : 1 ≤ i then vanC α hα hγ f hsm i j h else 0) * (32 * G z θ)).symm]
          rfl
      _ = 32 * vanSum α hα hγ f hsm 7 * G z θ := by ring
  refine le_trans (add_le_add hbase hmixed) ?_
  exact le_of_eq (by ring)

end Work.FTS.ClassC
