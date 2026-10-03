import Mathlib
import Submission.Work.Analysis.Concentration.Basic

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `L^s` concentration bound from the weak-type concentration bound

`FiberWeakType P Q d C` says that the level sets of the fibre counting function
`h(y) = polyFiberCard P Q y = #{x ∈ ℤ/Qℤ : P x = y}` decay like
`#{y : h(y) ≥ t} ≤ C t^{-α} Q`, `α = d/(d-1)` (Appendix C, Corollary `cor:1`).
`FiberLpBound P Q s C'` says `∑_y h(y)^s ≤ C'^s Q`, i.e. `‖h‖_{L^s} ≤ C' Q^{1/s}`.

Here we prove the layer-cake (Cavalieri) implication `FiberWeakType ⟹ FiberLpBound`
for `1 ≤ s < d/(d-1)`, with the explicit constant `fiberWeakTypeConstant d s C` of
`Basic.lean`.  The argument is the standard one: writing the integral of `t ↦ t^{s-1}`
over `[0, h(y)]` and exchanging the order of summation and integration gives

  `∑_y h(y)^s = s ∫_0^Q t^{s-1} #{y : h(y) > t} dt`,

and one estimates the distribution function by `Q` below `T = max 1 C^{1/α}` and by
`C t^{-α} Q` above it.
-/

set_option autoImplicit false

namespace Work.Analysis.Concentration

open Polynomial Finset MeasureTheory

noncomputable section

/-- The explicit weak-type constant unfolds to the displayed expression, with
`α = d/(d-1)` and `T = max 1 C^{1/α}`. -/
lemma fiberWeakTypeConstant_eq (d s C : ℝ) :
    fiberWeakTypeConstant d s C
      = (s * (max 1 (C ^ (1 / (d / (d - 1))))) ^ s
          + s * C * (max 1 (C ^ (1 / (d / (d - 1))))) ^ (s - d / (d - 1))
            / (d / (d - 1) - s)) ^ (1 / s) := rfl

theorem fiberLpBound_of_fiberWeakType {P : Polynomial ℤ} {Q : ℕ} [NeZero Q] {d s C : ℝ}
    (hd : 1 < d) (hC : 0 ≤ C) (h : FiberWeakType P Q d C)
    (hs1 : 1 ≤ s) (hs2 : s < d / (d - 1)) :
    FiberLpBound P Q s (fiberWeakTypeConstant d s C) := by
  classical
  set α : ℝ := d / (d - 1) with hα
  set T : ℝ := max 1 (C ^ (1 / α)) with hT
  have hd1 : 0 < d - 1 := by linarith
  have hα0 : 0 < α := by rw [hα]; positivity
  have hα1 : 1 < α := by
    rw [hα]; exact (one_lt_div hd1).mpr (by linarith)
  have hs0 : 0 < s := by linarith
  have hsα : 0 < α - s := by linarith
  have hT1 : 1 ≤ T := by rw [hT]; exact le_max_left _ _
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT1
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hcard : ((Finset.univ : Finset (ZMod Q)).card : ℝ) = Q := by
    rw [Finset.card_univ, ZMod.card]
  have hfib_le : ∀ y : ZMod Q, (polyFiberCard P Q y : ℝ) ≤ Q := by
    intro y
    have hle : polyFiberCard P Q y ≤ Q := by
      rw [polyFiberCard]
      calc (Finset.univ.filter (fun x : ZMod Q => polyEvalZMod P Q x = y)).card
          ≤ (Finset.univ : Finset (ZMod Q)).card := Finset.card_filter_le _ _
        _ = Q := by rw [Finset.card_univ, ZMod.card]
    exact_mod_cast hle
  -- the value of the constant, raised to the power `s`
  have hconst : (fiberWeakTypeConstant d s C) ^ s
      = s * T ^ s + s * C * T ^ (s - α) / (α - s) := by
    have hX0 : 0 ≤ s * T ^ s + s * C * T ^ (s - α) / (α - s) := by
      have h1 : 0 < T ^ s := Real.rpow_pos_of_pos hT0 s
      have h2 : 0 < T ^ (s - α) := Real.rpow_pos_of_pos hT0 _
      have h3 : 0 ≤ s * C * T ^ (s - α) / (α - s) := by positivity
      have h4 : 0 ≤ s * T ^ s := by positivity
      linarith
    rw [fiberWeakTypeConstant]
    simp only [← hα, ← hT]
    rw [← Real.rpow_mul hX0, one_div, inv_mul_cancel₀ (ne_of_gt hs0), Real.rpow_one]
  unfold FiberLpBound
  rw [hconst]
  by_cases hQT : Q ≤ T
  · -- Case 1: `Q ≤ T`; every fibre has size at most `T`
    have hterm : ∀ y : ZMod Q, (polyFiberCard P Q y : ℝ) ^ s ≤ T ^ s := fun y =>
      Real.rpow_le_rpow (by positivity) (le_trans (hfib_le y) hQT) (le_of_lt hs0)
    have hsum1 : ∑ y : ZMod Q, (polyFiberCard P Q y : ℝ) ^ s ≤ Q * T ^ s := by
      calc ∑ y : ZMod Q, (polyFiberCard P Q y : ℝ) ^ s
          ≤ ∑ _y : ZMod Q, T ^ s := Finset.sum_le_sum (fun y _ => hterm y)
        _ = ((Finset.univ : Finset (ZMod Q)).card : ℝ) * T ^ s := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ = Q * T ^ s := by rw [hcard]
    refine hsum1.trans ?_
    have hTs : 0 ≤ T ^ s := Real.rpow_nonneg hT0.le s
    have hnum : 0 ≤ s * C * T ^ (s - α) / (α - s) := by
      have h2 : 0 < T ^ (s - α) := Real.rpow_pos_of_pos hT0 _
      have h3 : 0 ≤ s * C * T ^ (s - α) := by positivity
      exact div_nonneg h3 (le_of_lt hsα)
    have hTs_le : T ^ s ≤ s * T ^ s := by nlinarith [hTs, hs1]
    calc Q * T ^ s ≤ Q * (s * T ^ s) := mul_le_mul_of_nonneg_left hTs_le hQpos.le
      _ ≤ Q * (s * T ^ s + s * C * T ^ (s - α) / (α - s)) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hnum) hQpos.le
      _ = (s * T ^ s + s * C * T ^ (s - α) / (α - s)) * Q := by ring
  · -- Case 2: `T < Q`; layer cake with an explicit exchange of sum and integral
    have hTQ : T < Q := lt_of_not_ge hQT
    set g : ZMod Q → ℝ → ℝ :=
      fun y t => t ^ (s - 1) * (if t < (polyFiberCard P Q y : ℝ) then 1 else 0) with hg
    have hgint : ∀ y : ZMod Q, IntervalIntegrable (g y) volume (0 : ℝ) (Q : ℝ) := by
      intro y
      have hh0 : (0 : ℝ) ≤ (polyFiberCard P Q y : ℝ) := by positivity
      have hhQ : (polyFiberCard P Q y : ℝ) ≤ Q := hfib_le y
      have hA : IntervalIntegrable (g y) volume (0 : ℝ) (polyFiberCard P Q y : ℝ) := by
        refine (intervalIntegral.intervalIntegrable_rpow (μ := volume) (r := s - 1)
          (Or.inl (by linarith))).congr_uIoo ?_
        intro t ht
        rw [Set.uIoo_of_le hh0] at ht
        simp only [hg, if_pos ht.2, mul_one]
      have hB : IntervalIntegrable (g y) volume (polyFiberCard P Q y : ℝ) (Q : ℝ) := by
        refine (intervalIntegrable_const (c := (0 : ℝ)) (μ := volume)
          (a := (polyFiberCard P Q y : ℝ)) (b := (Q : ℝ))).congr_uIoo ?_
        intro t ht
        rw [Set.uIoo_of_le hhQ] at ht
        simp only [hg, if_neg (not_lt.mpr (le_of_lt ht.1)), mul_zero]
      exact hA.trans hB
    have hsum : ∀ t : ℝ, (∑ y : ZMod Q, g y t)
        = t ^ (s - 1) *
            ((Finset.univ.filter (fun y : ZMod Q => t < (polyFiberCard P Q y : ℝ))).card : ℝ) := by
      intro t
      rw [hg]
      simp only []
      rw [← Finset.mul_sum, Finset.sum_boole]
    have hper : ∀ y : ZMod Q, (polyFiberCard P Q y : ℝ) ^ s
        = s * ∫ t in (0 : ℝ)..(Q : ℝ), g y t := by
      intro y
      have hh0 : (0 : ℝ) ≤ (polyFiberCard P Q y : ℝ) := by positivity
      have hhQ : (polyFiberCard P Q y : ℝ) ≤ Q := hfib_le y
      have hA : IntervalIntegrable (g y) volume (0 : ℝ) (polyFiberCard P Q y : ℝ) :=
        (hgint y).mono_set (by
          rw [Set.uIcc_of_le hh0, Set.uIcc_of_le hQpos.le]
          exact Set.Icc_subset_Icc le_rfl hhQ)
      have hB : IntervalIntegrable (g y) volume (polyFiberCard P Q y : ℝ) (Q : ℝ) :=
        (hgint y).mono_set (by
          rw [Set.uIcc_of_le hhQ, Set.uIcc_of_le hQpos.le]
          exact Set.Icc_subset_Icc hh0 le_rfl)
      have hsplit := intervalIntegral.integral_add_adjacent_intervals hA hB
      have h1 : ∫ t in (0 : ℝ)..(polyFiberCard P Q y : ℝ), g y t
          = (polyFiberCard P Q y : ℝ) ^ s / s := by
        have hc : ∫ t in (0 : ℝ)..(polyFiberCard P Q y : ℝ), g y t
            = ∫ t in (0 : ℝ)..(polyFiberCard P Q y : ℝ), t ^ (s - 1) := by
          refine intervalIntegral.integral_congr_Ioo_of_le hh0 ?_
          intro t ht
          simp only [hg, if_pos ht.2, mul_one]
        rw [hc, integral_rpow (Or.inl (by linarith : (-1 : ℝ) < s - 1))]
        rw [show s - 1 + 1 = s by ring, Real.zero_rpow (ne_of_gt hs0), sub_zero]
      have h2 : ∫ t in (polyFiberCard P Q y : ℝ)..(Q : ℝ), g y t = 0 := by
        have hc : ∫ t in (polyFiberCard P Q y : ℝ)..(Q : ℝ), g y t
            = ∫ t in (polyFiberCard P Q y : ℝ)..(Q : ℝ), (0 : ℝ) := by
          refine intervalIntegral.integral_congr_Ioo_of_le hhQ ?_
          intro t ht
          simp only [hg, if_neg (not_lt.mpr (le_of_lt ht.1)), mul_zero]
        rw [hc, intervalIntegral.integral_zero]
      rw [← hsplit, h1, h2, add_zero, mul_div_cancel₀ _ (ne_of_gt hs0)]
    have hsumint : IntervalIntegrable (fun t : ℝ => ∑ y : ZMod Q, g y t) volume (0 : ℝ) (Q : ℝ) := by
      have h0 : IntervalIntegrable (∑ y : ZMod Q, g y) volume (0 : ℝ) (Q : ℝ) :=
        IntervalIntegrable.sum (Finset.univ : Finset (ZMod Q)) (fun y _ => hgint y)
      have heq : (∑ y : ZMod Q, g y) = (fun t : ℝ => ∑ y : ZMod Q, g y t) := by
        funext t
        rw [Finset.sum_apply]
      rwa [heq] at h0
    have hi1 : IntervalIntegrable (fun t : ℝ => ∑ y : ZMod Q, g y t) volume (0 : ℝ) T :=
      hsumint.mono_set (by
        rw [Set.uIcc_of_le (le_of_lt hT0), Set.uIcc_of_le hQpos.le]
        exact Set.Icc_subset_Icc le_rfl hTQ.le)
    have hi2 : IntervalIntegrable (fun t : ℝ => ∑ y : ZMod Q, g y t) volume T (Q : ℝ) :=
      hsumint.mono_set (by
        rw [Set.uIcc_of_le hTQ.le, Set.uIcc_of_le hQpos.le]
        exact Set.Icc_subset_Icc hT0.le le_rfl)
    have hint1 : ∫ t in (0 : ℝ)..T, (∑ y : ZMod Q, g y t) ≤ Q * T ^ s / s := by
      have hle : ∫ t in (0 : ℝ)..T, (∑ y : ZMod Q, g y t)
          ≤ ∫ t in (0 : ℝ)..T, Q * t ^ (s - 1) := by
        refine intervalIntegral.integral_mono_on (le_of_lt hT0) hi1 ?_ ?_
        · exact (intervalIntegral.intervalIntegrable_rpow (μ := volume) (r := s - 1)
            (Or.inl (by linarith))).const_mul Q
        · intro t ht
          rw [hsum t]
          have hN : ((Finset.univ.filter
              (fun y : ZMod Q => t < (polyFiberCard P Q y : ℝ))).card : ℝ) ≤ Q := by
            calc ((Finset.univ.filter
                  (fun y : ZMod Q => t < (polyFiberCard P Q y : ℝ))).card : ℝ)
                ≤ ((Finset.univ : Finset (ZMod Q)).card : ℝ) := by
                  exact_mod_cast Finset.card_filter_le _ _
              _ = Q := hcard
          calc t ^ (s - 1) * ((Finset.univ.filter
                (fun y : ZMod Q => t < (polyFiberCard P Q y : ℝ))).card : ℝ)
              ≤ t ^ (s - 1) * Q := mul_le_mul_of_nonneg_left hN (Real.rpow_nonneg ht.1 (s - 1))
            _ = Q * t ^ (s - 1) := by ring
      refine hle.trans (le_of_eq ?_)
      rw [intervalIntegral.integral_const_mul,
        integral_rpow (Or.inl (by linarith : (-1 : ℝ) < s - 1))]
      rw [show s - 1 + 1 = s by ring, Real.zero_rpow (ne_of_gt hs0), sub_zero]
      ring
    have hint2 : ∫ t in T..(Q : ℝ), (∑ y : ZMod Q, g y t)
        ≤ C * Q * (T ^ (s - α) / (α - s)) := by
      have hQ0 : (0 : ℝ) ∉ Set.uIcc T Q := by
        rw [Set.uIcc_of_le hTQ.le]
        exact fun hc => absurd hc.1 (not_le.mpr hT0)
      have hne : s - 1 - α ≠ -1 := by
        intro he
        exact (ne_of_gt hsα) (by linarith)
      have hi : IntervalIntegrable (fun t : ℝ => C * Q * (t ^ (s - 1) * t ^ (-α)))
          volume T (Q : ℝ) := by
        refine ((intervalIntegral.intervalIntegrable_rpow (μ := volume) (r := s - 1)
          (Or.inl (by linarith))).mul_continuousOn ?_).const_mul (C * Q)
        exact continuousOn_id.rpow_const (fun t ht => Or.inl (by
          rw [Set.uIcc_of_le hTQ.le] at ht
          exact ne_of_gt (lt_of_lt_of_le hT0 ht.1)))
      have hle : ∫ t in T..(Q : ℝ), (∑ y : ZMod Q, g y t)
          ≤ ∫ t in T..(Q : ℝ), C * Q * (t ^ (s - 1) * t ^ (-α)) := by
        refine intervalIntegral.integral_mono_on hTQ.le hi2 hi ?_
        intro t ht
        rw [hsum t]
        have ht0 : 0 < t := lt_of_lt_of_le hT0 ht.1
        have hN : ((Finset.univ.filter
            (fun y : ZMod Q => t < (polyFiberCard P Q y : ℝ))).card : ℝ)
            ≤ C * t ^ (-α) * Q := by
          have hwt := h t ht0
          rw [← hα] at hwt
          have hmono : (Finset.univ.filter
              (fun y : ZMod Q => t < (polyFiberCard P Q y : ℝ))).card
              ≤ (Finset.univ.filter (fun y : ZMod Q => t ≤ (polyFiberCard P Q y : ℝ))).card :=
            Finset.card_le_card (fun y hy => by
              simp only [Finset.mem_filter] at hy ⊢
              exact ⟨hy.1, le_of_lt hy.2⟩)
          calc ((Finset.univ.filter
                (fun y : ZMod Q => t < (polyFiberCard P Q y : ℝ))).card : ℝ)
              ≤ ((Finset.univ.filter
                  (fun y : ZMod Q => t ≤ (polyFiberCard P Q y : ℝ))).card : ℝ) := by
                exact_mod_cast hmono
            _ ≤ C * t ^ (-α) * Q := hwt
        calc t ^ (s - 1) * ((Finset.univ.filter
              (fun y : ZMod Q => t < (polyFiberCard P Q y : ℝ))).card : ℝ)
            ≤ t ^ (s - 1) * (C * t ^ (-α) * Q) :=
              mul_le_mul_of_nonneg_left hN (Real.rpow_nonneg ht0.le _)
          _ = C * Q * (t ^ (s - 1) * t ^ (-α)) := by ring
      refine hle.trans ?_
      have hB : ∫ t in T..(Q : ℝ), C * Q * (t ^ (s - 1) * t ^ (-α))
          = ∫ t in T..(Q : ℝ), C * Q * t ^ (s - 1 - α) := by
        refine intervalIntegral.integral_congr_Ioo_of_le hTQ.le ?_
        intro t ht
        simp only []
        rw [← Real.rpow_add (lt_trans hT0 ht.1) (s - 1) (-α)]
        ring_nf
      rw [hB, intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨hne, hQ0⟩)]
      rw [show s - 1 - α + 1 = s - α by ring]
      have hflip : (Q ^ (s - α) - T ^ (s - α)) / (s - α)
          = (T ^ (s - α) - Q ^ (s - α)) / (α - s) := by
        rw [div_eq_div_iff (by linarith : s - α ≠ 0) (ne_of_gt hsα)]
        ring
      rw [hflip]
      have hle' : (T ^ (s - α) - Q ^ (s - α)) / (α - s) ≤ T ^ (s - α) / (α - s) := by
        rw [div_le_div_iff_of_pos_right hsα]
        linarith [Real.rpow_nonneg hQpos.le (s - α)]
      exact mul_le_mul_of_nonneg_left hle' (by positivity)
    have hmain : s * ∫ t in (0 : ℝ)..(Q : ℝ), (∑ y : ZMod Q, g y t)
        ≤ (s * T ^ s + s * C * T ^ (s - α) / (α - s)) * Q := by
      have hsplit2 := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
      rw [← hsplit2]
      calc s * ((∫ t in (0 : ℝ)..T, (∑ y : ZMod Q, g y t))
            + ∫ t in T..(Q : ℝ), (∑ y : ZMod Q, g y t))
          ≤ s * (Q * T ^ s / s + C * Q * (T ^ (s - α) / (α - s))) :=
            mul_le_mul_of_nonneg_left (add_le_add hint1 hint2) (le_of_lt hs0)
        _ ≤ (s * T ^ s + s * C * T ^ (s - α) / (α - s)) * Q := by
            have hsne : s ≠ 0 := ne_of_gt hs0
            have hfac : s * (Q * T ^ s / s + C * Q * (T ^ (s - α) / (α - s)))
                = Q * T ^ s + s * C * Q * T ^ (s - α) / (α - s) := by
              rw [mul_add, mul_div_cancel₀ _ hsne]
              ring
            rw [hfac]
            have hTs : 0 ≤ T ^ s := Real.rpow_nonneg hT0.le s
            have hTs_le : T ^ s ≤ s * T ^ s := by nlinarith [hTs, hs1]
            have h1 : Q * T ^ s ≤ (s * T ^ s) * Q := by
              rw [mul_comm (Q : ℝ) (T ^ s)]
              exact mul_le_mul_of_nonneg_right hTs_le hQpos.le
            have h2 : s * C * Q * T ^ (s - α) / (α - s)
                ≤ (s * C * T ^ (s - α) / (α - s)) * Q := by
              have he : (s * C * T ^ (s - α) / (α - s)) * Q
                  = s * C * Q * T ^ (s - α) / (α - s) := by ring
              rw [he]
            calc Q * T ^ s + s * C * Q * T ^ (s - α) / (α - s)
                ≤ (s * T ^ s) * Q + (s * C * T ^ (s - α) / (α - s)) * Q :=
                  add_le_add h1 h2
              _ = (s * T ^ s + s * C * T ^ (s - α) / (α - s)) * Q := by ring
    calc ∑ y : ZMod Q, (polyFiberCard P Q y : ℝ) ^ s
        = ∑ y : ZMod Q, s * ∫ t in (0 : ℝ)..(Q : ℝ), g y t :=
          Finset.sum_congr rfl (fun y _ => hper y)
      _ = s * ∑ y : ZMod Q, ∫ t in (0 : ℝ)..(Q : ℝ), g y t := (Finset.mul_sum _ _ _).symm
      _ = s * ∫ t in (0 : ℝ)..(Q : ℝ), ∑ y : ZMod Q, g y t := by
            rw [intervalIntegral.integral_finsetSum (fun y _ => hgint y)]
      _ ≤ (s * T ^ s + s * C * T ^ (s - α) / (α - s)) * Q := hmain

end

end Work.Analysis.Concentration
