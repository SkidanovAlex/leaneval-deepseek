import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Honesty.VanGridK
import Submission.Work.FTS.ClassC.PureVanishingReduction

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem HkIntegrand_K_le_of_bounds {α : ℝ} (hα : 0 < α)
    (hγ : Work.Spaces.gam α ≤ 3 / 2) {K : ℕ} {f : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) {G : ℝ → ℝ → ℝ}
    (hGnn : ∀ z : ℝ, ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ G z θ)
    (h0 : ∀ j : ℕ, j ≤ K → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ ≤ 4 * G z θ)
    (h1 : ∀ j r : ℕ, 1 ≤ r → r + j ≤ K → ∀ z : ℝ, 0 < z →
      ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
        Work.FTS.ClassC.vig α f r j z θ ≤ 4 * G z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.HkIntegrand α K f z θ
      ≤ (4 * ((K : ℝ) + 1) + 4 * (K : ℝ) * Work.FTS.ClassC.vanSum α hα hγ f hsm K) * G z θ := by
  classical
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hGz : 0 ≤ G z θ := hGnn z θ hθ
  -- the pointwise slot reduction: pure radial level-`0` slots + `vanC`-weighted vanishing slots
  have hkey := Work.FTS.ClassC.HkIntegrand_le_pure_vanishing hα hγ hsm K z θ hzI hθI
  -- the pure part: `K + 1` slots, each `≤ 4G`
  have hpure : (∑ j ∈ Finset.range (K + 1),
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ)
      ≤ 4 * ((K : ℝ) + 1) * G z θ := by
    calc (∑ j ∈ Finset.range (K + 1),
            Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ)
        ≤ ∑ j ∈ Finset.range (K + 1), 4 * G z θ := by
          refine Finset.sum_le_sum fun j hj => ?_
          exact h0 j (by have := Finset.mem_range.mp hj; omega) z hz θ hθ
      _ = 4 * ((K : ℝ) + 1) * G z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
  -- the mixed part: each slot carries a factor `vanC ≥ 0` and an inner sum of at most `i ≤ K`
  -- vanishing-weight slots, each `≤ 4G`
  have hmix : (∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.Icc 1 (K - j),
        (if h : 1 ≤ i then Work.FTS.ClassC.vanC α hα hγ f hsm i j h else 0)
          * ∑ r ∈ Finset.Icc 1 i, Work.FTS.ClassC.vig α f r j z θ)
      ≤ 4 * (K : ℝ) * Work.FTS.ClassC.vanSum α hα hγ f hsm K * G z θ := by
    have hinner : ∀ j ∈ Finset.range (K + 1), ∀ i ∈ Finset.Icc 1 (K - j),
        ∑ r ∈ Finset.Icc 1 i, Work.FTS.ClassC.vig α f r j z θ ≤ 4 * (K : ℝ) * G z θ := by
      intro j hj i hi
      have hile : i ≤ K - j := (Finset.mem_Icc.mp hi).2
      have hiK : i ≤ K := by omega
      calc ∑ r ∈ Finset.Icc 1 i, Work.FTS.ClassC.vig α f r j z θ
          ≤ ∑ r ∈ Finset.Icc 1 i, 4 * G z θ := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
            have hrl : r ≤ i := (Finset.mem_Icc.mp hr).2
            exact h1 j r hr1 (by omega) z hz θ hθ
        _ = ((Finset.Icc 1 i).card : ℝ) * (4 * G z θ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ 4 * (K : ℝ) * G z θ := by
            have hcard : (Finset.Icc 1 i).card ≤ K := by
              have hsub : Finset.Icc 1 i ⊆ Finset.Icc 1 K := by
                intro x hx
                exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hx).1,
                  le_trans (Finset.mem_Icc.mp hx).2 hiK⟩
              calc (Finset.Icc 1 i).card ≤ (Finset.Icc 1 K).card := Finset.card_le_card hsub
                _ = K := by rw [Nat.card_Icc]; omega
            have hcardR : ((Finset.Icc 1 i).card : ℝ) ≤ (K : ℝ) := by exact_mod_cast hcard
            have h4 : 0 ≤ 4 * G z θ := by linarith
            calc ((Finset.Icc 1 i).card : ℝ) * (4 * G z θ)
                ≤ (K : ℝ) * (4 * G z θ) := mul_le_mul_of_nonneg_right hcardR h4
              _ = 4 * (K : ℝ) * G z θ := by ring
    have hmul : ∀ j ∈ Finset.range (K + 1), ∀ i ∈ Finset.Icc 1 (K - j),
        (if h : 1 ≤ i then Work.FTS.ClassC.vanC α hα hγ f hsm i j h else 0)
          * (∑ r ∈ Finset.Icc 1 i, Work.FTS.ClassC.vig α f r j z θ)
        ≤ (if h : 1 ≤ i then Work.FTS.ClassC.vanC α hα hγ f hsm i j h else 0)
          * (4 * (K : ℝ) * G z θ) := by
      intro j hj i hi
      have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
      have hpos : 0 ≤ (if h : 1 ≤ i then Work.FTS.ClassC.vanC α hα hγ f hsm i j h else 0) := by
        rw [dite_eq_left hi1]
        exact le_of_lt (Work.FTS.ClassC.vanC_pos α hα hγ f hsm i j hi1)
      exact mul_le_mul_of_nonneg_left (hinner j hj i hi) hpos
    calc (∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.Icc 1 (K - j),
          (if h : 1 ≤ i then Work.FTS.ClassC.vanC α hα hγ f hsm i j h else 0)
            * ∑ r ∈ Finset.Icc 1 i, Work.FTS.ClassC.vig α f r j z θ)
        ≤ ∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.Icc 1 (K - j),
            (if h : 1 ≤ i then Work.FTS.ClassC.vanC α hα hγ f hsm i j h else 0)
              * (4 * (K : ℝ) * G z θ) :=
          Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun i hi => hmul j hj i hi
      _ = (∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.Icc 1 (K - j),
            (if h : 1 ≤ i then Work.FTS.ClassC.vanC α hα hγ f hsm i j h else 0))
              * (4 * (K : ℝ) * G z θ) := by
          simp only [← Finset.sum_mul]
      _ = 4 * (K : ℝ) * Work.FTS.ClassC.vanSum α hα hγ f hsm K * G z θ := by
          simp only [Work.FTS.ClassC.vanSum]
          ring
  have hfin : Work.Spaces.HkIntegrand α K f z θ
      ≤ 4 * ((K : ℝ) + 1) * G z θ
        + 4 * (K : ℝ) * Work.FTS.ClassC.vanSum α hα hγ f hsm K * G z θ := by
    linarith
  calc Work.Spaces.HkIntegrand α K f z θ
      ≤ 4 * ((K : ℝ) + 1) * G z θ
        + 4 * (K : ℝ) * Work.FTS.ClassC.vanSum α hα hγ f hsm K * G z θ := hfin
    _ = (4 * ((K : ℝ) + 1) + 4 * (K : ℝ) * Work.FTS.ClassC.vanSum α hα hγ f hsm K) * G z θ := by
        ring

end Work.FTS.PhiStar.Honesty
