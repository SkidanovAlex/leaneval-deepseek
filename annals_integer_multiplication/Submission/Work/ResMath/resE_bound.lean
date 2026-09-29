import Mathlib
import Submission.Work.ResMath.resE_row
import Submission.Work.ResMath.resE_tail

/-!
# The operator-norm bound `‖E‖ ≤ 2.000008 · e^{-π α² θ/2}` (paper Lemma 4.6)

`Work.ResMath.norm_Emat_mulVec_le`: for `0 < s < t`, `0 < α` and `x := α²(t/s - 1) ≥ 1`,

`‖Emat s t α · u‖ ≤ 2.000008 · exp (-π x / 2) · ‖u‖`

for the sup norms on `Fin s → ℂ`.  This is the analytic content of Lemma 4.6 of Harvey–van der
Hoeven, *Integer multiplication in time* `O(n log n)`: the row series of `Emat` is dominated by
`2 ∑_{m ≥ 1} e^{-2πx(m - 1/2)²} = 2 e^{-πx/2}(1 + O(e^{-4πx}))`.
-/

set_option maxHeartbeats 800000

namespace Work.ResMath

open HvdH

/-- The "killed" Gaussian weight family `n ↦ (n = 0 ? 0 : e^{-2πx(|n|-1/2)²})` is summable. -/
lemma summable_killed_gauss (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℤ =>
      if n = 0 then 0 else Real.exp (-(2 * Real.pi * x) * (|(n : ℝ)| - 1 / 2) ^ 2)) := by
  have h1 : Summable (fun n : ℤ => Real.exp (-(2 * Real.pi * x / 4) * (n : ℝ) ^ 2)) := by
    have h := summable_exp_neg_affine_sq (2 * Real.pi * x / 4) 0 (by positivity) (Nat.one_pos)
    refine h.congr (fun n => ?_)
    congr 1
    push_cast
    ring
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) h1
  · by_cases hn : n = 0 <;> simp only [hn, ↓reduceIte] <;> positivity
  · by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, ↓reduceIte]
      apply Real.exp_le_exp.mpr
      have habs : (1 : ℝ) ≤ |(n : ℝ)| := by
        have h2 : (1 : ℤ) ≤ |n| := by
          have : 0 < |n| := abs_pos.mpr hn
          omega
        have h3 : ((1 : ℤ) : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast h2
        simpa only [Int.cast_abs, Int.cast_one] using h3
      have hsq : (|(n : ℝ)|) ^ 2 = (n : ℝ) ^ 2 := sq_abs _
      have hpoly : (n : ℝ) ^ 2 ≤ 4 * (|(n : ℝ)| - 1 / 2) ^ 2 := by
        nlinarith [hsq, habs]
      have hstep := mul_le_mul_of_nonneg_left hpoly
        (by positivity : (0 : ℝ) ≤ 2 * Real.pi * x / 4)
      nlinarith [hstep]

/-- The "killed" `phi` family is summable. -/
lemma summable_killed_phi (s t α : ℕ) (hs : 0 < s) (hst : s < t) (hα : 0 < α)
    (u : Fin s → ℂ) (ℓ : Fin s) :
    Summable (fun n : ℤ => if n = (ℓ : ℤ) then (0 : ℂ) else phi s t α hs ℓ u n) := by
  have hφ := summable_phi s t α hs hst hα u ℓ
  refine Summable.of_norm_bounded hφ.norm (fun n => ?_)
  by_cases hn : n = (ℓ : ℤ) <;> simp [hn]

/-- **Lemma 4.6** (operator norm form): for `0 < s < t`, `0 < α` and `α²(t/s-1) ≥ 1`,
`‖Emat s t α · u‖ ≤ 2.000008 · e^{-π α² (t/s-1)/2} · ‖u‖`. -/
theorem norm_Emat_mulVec_le (s t α : ℕ) (hs : 0 < s) (hst : s < t) (hα : 0 < α)
    (hx : 1 ≤ (α : ℝ) ^ 2 * ((t : ℝ) / s - 1)) (u : Fin s → ℂ) :
    ‖(HvdH.Emat s t α).mulVec u‖ ≤
      2.000008 * Real.exp (-(Real.pi * ((α : ℝ) ^ 2 * ((t : ℝ) / s - 1)) / 2)) * ‖u‖ := by
  haveI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  have hx0 : 0 < (α : ℝ) ^ 2 * ((t : ℝ) / s - 1) := by linarith
  rw [pi_norm_le_iff_of_nonempty]
  intro ℓ
  have hφ := summable_phi s t α hs hst hα u ℓ
  have hkφ := summable_killed_phi s t α hs hst hα u ℓ
  have hrow := Nmat_mulVec_eq_tsum s t α hs hst hα u ℓ
  have hE : (HvdH.Emat s t α).mulVec u ℓ =
      ∑' n : ℤ, (if n = (ℓ : ℤ) then (0 : ℂ) else phi s t α hs ℓ u n) := by
    have hsub : (HvdH.Emat s t α).mulVec u ℓ = (HvdH.Nmat s t α).mulVec u ℓ - u ℓ := by
      simp only [HvdH.Emat, Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply]
    rw [hsub, hrow, ← phi_self s t α hs ℓ u]
    rw [hφ.tsum_eq_add_tsum_ite (ℓ : ℤ)]
    abel
  rw [hE]
  calc ‖∑' n : ℤ, (if n = (ℓ : ℤ) then (0 : ℂ) else phi s t α hs ℓ u n)‖
      ≤ ∑' n : ℤ, ‖(if n = (ℓ : ℤ) then (0 : ℂ) else phi s t α hs ℓ u n)‖ :=
        norm_tsum_le_tsum_norm hkφ.norm
    _ = ∑' n : ℤ, ‖(if n = 0 then (0 : ℂ) else phi s t α hs ℓ u (n + (ℓ : ℤ)))‖ := by
        rw [← Equiv.tsum_eq (Equiv.addRight (ℓ : ℤ))
          (fun m : ℤ => ‖(if m = (ℓ : ℤ) then (0 : ℂ) else phi s t α hs ℓ u m)‖)]
        exact tsum_congr (fun n => by
          have h1 : n + (ℓ : ℤ) = (ℓ : ℤ) ↔ n = 0 := by omega
          simp only [Equiv.coe_addRight, h1])
    _ ≤ ∑' n : ℤ,
          (if n = 0 then 0 else Real.exp (-(2 * Real.pi * ((α : ℝ) ^ 2 * ((t : ℝ) / s - 1))) *
            (|(n : ℝ)| - 1 / 2) ^ 2)) * ‖u‖ := by
        have hsum2 : Summable (fun n : ℤ =>
            ‖(if n = 0 then (0 : ℂ) else phi s t α hs ℓ u (n + (ℓ : ℤ)))‖) := by
          have h3 : Summable (fun n : ℤ =>
              ‖(if n + (ℓ : ℤ) = (ℓ : ℤ) then (0 : ℂ)
                else phi s t α hs ℓ u (n + (ℓ : ℤ)))‖) :=
            (Equiv.summable_iff (Equiv.addRight (ℓ : ℤ))
              (f := fun m : ℤ => ‖(if m = (ℓ : ℤ) then (0 : ℂ)
                else phi s t α hs ℓ u m)‖)).mpr hkφ.norm
          refine h3.congr (fun n => ?_)
          have h1 : n + (ℓ : ℤ) = (ℓ : ℤ) ↔ n = 0 := by omega
          simp only [h1]
        refine hsum2.tsum_le_tsum (fun n => ?_)
          ((summable_killed_gauss ((α : ℝ) ^ 2 * ((t : ℝ) / s - 1)) hx0).mul_right ‖u‖)
        by_cases hn : n = 0
        · simp [hn]
        · simp only [hn, ↓reduceIte]
          have hnn : n + (ℓ : ℤ) ≠ (ℓ : ℤ) := by omega
          have hb := norm_phi_le s t α hs hst hα ℓ u (n + (ℓ : ℤ)) hnn
          have hcast : (((n + (ℓ : ℤ) : ℤ) : ℝ) - (ℓ : ℝ)) = (n : ℝ) := by push_cast; ring
          rw [hcast] at hb
          refine le_trans hb (le_of_eq ?_)
          rw [neg_mul]
    _ = (∑' n : ℤ, (if n = 0 then 0 else Real.exp (-(2 * Real.pi * ((α : ℝ) ^ 2 * ((t : ℝ) / s - 1))) *
            (|(n : ℝ)| - 1 / 2) ^ 2))) * ‖u‖ := by
        have hm : (∑' n : ℤ, (if n = 0 then 0 else Real.exp (-(2 * Real.pi *
              ((α : ℝ) ^ 2 * ((t : ℝ) / s - 1))) * (|(n : ℝ)| - 1 / 2) ^ 2)) * ‖u‖)
            = (∑' n : ℤ, (if n = 0 then 0 else Real.exp (-(2 * Real.pi *
              ((α : ℝ) ^ 2 * ((t : ℝ) / s - 1))) * (|(n : ℝ)| - 1 / 2) ^ 2))) * ‖u‖ :=
          Summable.tsum_mul_right _ (summable_killed_gauss _ hx0)
        rw [← hm]
    _ ≤ (2.000008 * Real.exp (-(Real.pi * ((α : ℝ) ^ 2 * ((t : ℝ) / s - 1)) / 2))) * ‖u‖ :=
        mul_le_mul_of_nonneg_right
          (killedGaussTail_le ((α : ℝ) ^ 2 * ((t : ℝ) / s - 1)) hx) (norm_nonneg u)

end Work.ResMath
