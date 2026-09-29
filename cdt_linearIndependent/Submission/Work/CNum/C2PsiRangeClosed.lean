import Mathlib
import Submission.Work.CNum.C2_setup
import Submission.Work.CNum.C2Psi_deriv_neg

/-!
# `Work.CNum.C2PsiRangeClosed`

`C2Psi t = t - π/2 + arcsin (cos t / C)`, where `C = C2C = cos(α/2)`, `α = alpR`.

On the closed interval `[α/2, π - α/2]` the function `C2Psi` takes its values in
`[-α/2, α/2]`:

* `C2Psi` is strictly antitone on the closed interval `[α/2, π - α/2]`: it is
  continuous there and `deriv C2Psi t < 0` on the interior (lemma
  `Work.CNum.C2Psi_deriv_neg`);
* the endpoint values are `C2Psi (α/2) = α/2` and `C2Psi (π - α/2) = -α/2`
  (because `cos (α/2) / C = 1` and `cos (π - α/2) / C = -1`).

Hence for `α ≤ θ ≤ 2π - α`, i.e. `θ/2 ∈ [α/2, π - α/2]`, we get
`-α/2 ≤ C2Psi (θ/2) ≤ α/2`.
-/

namespace Work.CNum

noncomputable section

open Real

private lemma Psi_end_left : C2Psi (alpR / 2) = alpR / 2 := by
  rw [C2Psi, cos_half_alpR, div_self C2C_ne_zero, Real.arcsin_one]
  ring

private lemma Psi_end_right : C2Psi (Real.pi - alpR / 2) = -(alpR / 2) := by
  have h1 : Real.cos (Real.pi - alpR / 2) / C2C = -1 := by
    rw [Real.cos_pi_sub, cos_half_alpR, neg_div, div_self C2C_ne_zero]
  rw [C2Psi, h1, Real.arcsin_neg_one]
  ring

private lemma Psi_strictAntiOn_Icc :
    StrictAntiOn C2Psi (Set.Icc (alpR / 2) (Real.pi - alpR / 2)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
  · apply Continuous.continuousOn
    unfold C2Psi
    continuity
  · intro x hx
    rw [interior_Icc] at hx
    exact C2Psi_deriv_neg hx

theorem C2PsiRangeClosed {θ : ℝ} (h1 : Work.CNum.alpR ≤ θ)
    (h2 : θ ≤ 2 * Real.pi - Work.CNum.alpR) :
    -(Work.CNum.alpR / 2) ≤ Work.CNum.C2Psi (θ / 2) ∧
      Work.CNum.C2Psi (θ / 2) ≤ Work.CNum.alpR / 2 := by
  have hab : alpR / 2 ≤ Real.pi - alpR / 2 := by linarith [alpR_lt_pi]
  have hmem : θ / 2 ∈ Set.Icc (alpR / 2) (Real.pi - alpR / 2) :=
    ⟨by linarith, by linarith⟩
  constructor
  · rcases eq_or_lt_of_le hmem.2 with h | h
    · rw [h, Psi_end_right]
    · have := Psi_strictAntiOn_Icc hmem (Set.right_mem_Icc.mpr hab) h
      rw [Psi_end_right] at this
      exact this.le
  · rcases eq_or_lt_of_le hmem.1 with h | h
    · rw [← h, Psi_end_left]
    · have := Psi_strictAntiOn_Icc (Set.left_mem_Icc.mpr hab) hmem h
      rw [Psi_end_left] at this
      exact this.le

end

end Work.CNum
