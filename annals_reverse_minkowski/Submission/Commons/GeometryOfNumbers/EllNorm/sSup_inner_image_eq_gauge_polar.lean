import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Gauge
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped Pointwise
open Set

namespace Commons.GeometryOfNumbers.EllNorm

theorem sSup_inner_image_eq_gauge_polar {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (K : Set E) (hKsymm : ∀ x ∈ K, -x ∈ K) (hKbdd : Bornology.IsBounded K) (x : E) :
    sSup ((fun y : E => inner ℝ y x) '' K)
      = gauge {z : E | ∀ y ∈ K, inner ℝ z y ≤ 1} x := by
  set P : Set E := {z : E | ∀ y ∈ K, inner ℝ z y ≤ 1} with hPdef
  set S : Set ℝ := (fun y : E => inner ℝ y x) '' K with hSdef
  simp only [gauge_def, Set.mem_Ioi]
  by_cases hKne : K.Nonempty
  · have hSne : S.Nonempty := hKne.image (fun y : E => inner ℝ y x)
    -- S is bounded above
    have hBdd : BddAbove S := by
      obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : E)).mp hKbdd
      refine ⟨R * ‖x‖, ?_⟩
      rintro c ⟨y, hy, rfl⟩
      calc inner ℝ y x ≤ ‖inner ℝ y x‖ := le_abs_self _
        _ ≤ ‖y‖ * ‖x‖ := norm_inner_le_norm y x
        _ ≤ R * ‖x‖ := by
            have hyR : ‖y‖ ≤ R := by
              have := hR hy
              rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at this
            exact mul_le_mul_of_nonneg_right hyR (norm_nonneg x)
    -- S is symmetric, hence its supremum is nonnegative
    have hSsymm : ∀ c ∈ S, -c ∈ S := by
      rintro c ⟨y, hy, rfl⟩
      exact ⟨-y, hKsymm y hy, inner_neg_left y x⟩
    have h0le : 0 ≤ sSup S := by
      obtain ⟨c, hc⟩ := hSne
      have h1 : c ≤ sSup S := le_csSup hBdd hc
      have h2 : -c ≤ sSup S := le_csSup hBdd (hSsymm c hc)
      linarith
    -- `x ∈ r • P` for `r > 0` is equivalent to `∀ y ∈ K, ⟪x, y⟫ ≤ r`
    have hTU : {r : ℝ | 0 < r ∧ x ∈ r • P}
        = {r : ℝ | 0 < r ∧ ∀ y ∈ K, inner ℝ x y ≤ r} := by
      ext r
      constructor
      · rintro ⟨hr, hxr⟩
        refine ⟨hr, fun y hy => ?_⟩
        have hmem : r⁻¹ • x ∈ P := (mem_smul_set_iff_inv_smul_mem₀ hr.ne' P x).mp hxr
        rw [hPdef] at hmem
        have h1 : inner ℝ (r⁻¹ • x) y ≤ 1 := hmem y hy
        rw [real_inner_smul_left] at h1
        rw [inv_mul_le_iff₀ hr] at h1
        simpa using h1
      · rintro ⟨hr, h⟩
        refine ⟨hr, ?_⟩
        rw [mem_smul_set_iff_inv_smul_mem₀ hr.ne' P x, hPdef]
        intro y hy
        rw [real_inner_smul_left]
        rw [inv_mul_le_iff₀ hr]
        simpa using h y hy
    rw [hTU]
    apply le_antisymm
    · -- sSup S ≤ sInf U
      apply le_csInf
      · refine ⟨|sSup S| + 1, by positivity, fun y hy => ?_⟩
        have hmem : inner ℝ x y ∈ S := ⟨y, hy, by rw [real_inner_comm]⟩
        have := le_csSup hBdd hmem
        have := le_abs_self (sSup S)
        linarith
      · intro b hb
        exact csSup_le hSne (fun c hc => by
          obtain ⟨y, hy, rfl⟩ := hc
          show inner ℝ y x ≤ b
          rw [real_inner_comm]
          exact hb.2 y hy)
    · -- sInf U ≤ sSup S
      apply le_of_forall_pos_le_add
      intro ε hε
      have hbddU : BddBelow {r : ℝ | 0 < r ∧ ∀ y ∈ K, inner ℝ x y ≤ r} :=
        ⟨0, fun b hb => hb.1.le⟩
      have hmemU : sSup S + ε ∈ {r : ℝ | 0 < r ∧ ∀ y ∈ K, inner ℝ x y ≤ r} := by
        refine ⟨by linarith, fun y hy => ?_⟩
        have hmem : inner ℝ x y ∈ S := ⟨y, hy, by rw [real_inner_comm]⟩
        have := le_csSup hBdd hmem
        linarith
      exact csInf_le hbddU hmemU
  · -- K = ∅
    have hKeq : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    have hSempty : S = ∅ := by rw [hSdef, hKeq, image_empty]
    have hPuniv : P = univ := by
      rw [hPdef, hKeq]; ext z; simp
    have hTeq : {r : ℝ | 0 < r ∧ x ∈ r • P} = Set.Ioi 0 := by
      ext r
      constructor
      · rintro ⟨hr, _⟩; exact hr
      · intro hr
        refine ⟨hr, ?_⟩
        rw [hPuniv, Set.mem_smul_set]
        exact ⟨r⁻¹ • x, trivial, smul_inv_smul₀ hr.ne' x⟩
    rw [hSempty, Real.sSup_empty, hTeq, csInf_Ioi]

end Commons.GeometryOfNumbers.EllNorm