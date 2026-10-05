import Mathlib
import Submission.Work.RPCore.Chain.C4Defs
import Submission.Work.RPCore.Chain.ChainDefs

/-!
# `Work.RPCore.Chain`: the linear projections feeding the chain action

The chain action

`chainAction n W q P = ∑_j ⟨P_j, q_{j+1} - q_j⟩ - ∑_j W j (q_j, Peff n P j)`

evaluates the `j`-th generating function at the point of `PS` whose coordinates are the `j`-th
position `z.1 j` and the `j`-th momentum `Peff n z.2 j`.  This file records that this assignment

* `projPS n j : ChainSp n →L[ℝ] PS`, `projPS n j z = (z.1 j, Peff n z.2 j)`,

is a **continuous linear map of operator norm `≤ 1`**, and it introduces the `j`-th summand

* `stepFun n N δ W j z = if midBlock N (j:ℕ) then 0 else W j (projPS n j z)`

of the perturbation `chainAction n W - chainAction n (refGF N δ)` (`chainAction_sub_refGF`).

The two lemmas `norm_projPS_le` and `opNorm_projPS_le_one` are what makes the derivative of the
perturbation bounded by the *same* constant that bounds each `W j`.
-/

namespace Work.RPCore.Chain

open Work.RPV

noncomputable section

/-- The continuous linear map `ChainSp n → PS`, `z ↦ (z.1 j, Peff n z.2 j)`, i.e. the pair of
arguments at which the `j`-th generating function of the chain is evaluated. -/
def projPS (n : ℕ) (j : Fin (n + 1)) : ChainSp n →L[ℝ] PS :=
  (((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.fst ℝ (Fin (n + 1) → ℝ × ℝ) (Fin n → ℝ × ℝ))).prod
    (if h : (j : ℕ) < n then
      (ContinuousLinearMap.proj (⟨(j : ℕ), h⟩ : Fin n)).comp
        (ContinuousLinearMap.snd ℝ (Fin (n + 1) → ℝ × ℝ) (Fin n → ℝ × ℝ))
     else 0))

@[simp] theorem projPS_apply (n : ℕ) (j : Fin (n + 1)) (z : ChainSp n) :
    projPS n j z = (z.1 j, Peff n z.2 j) := by
  unfold projPS Peff ContinuousLinearMap.proj
  by_cases h : (j : ℕ) < n <;> simp [h]

/-- `projPS` does not increase the norm. -/
theorem norm_projPS_le (n : ℕ) (j : Fin (n + 1)) (z : ChainSp n) :
    ‖projPS n j z‖ ≤ ‖z‖ := by
  rw [projPS_apply]
  have h1 : ‖((z.1 j, Peff n z.2 j) : PS)‖ = max ‖z.1 j‖ ‖Peff n z.2 j‖ := Prod.norm_def _
  rw [h1]
  refine max_le (le_trans (norm_le_pi_norm z.1 j) (norm_fst_le z)) ?_
  rw [Peff]; split
  · exact le_trans (norm_le_pi_norm z.2 _) (norm_snd_le z)
  · simp

/-- Consequently the operator norm of `projPS` is at most `1`. -/
theorem opNorm_projPS_le_one (n : ℕ) (j : Fin (n + 1)) : ‖projPS n j‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun z => by
    rw [one_mul]; exact norm_projPS_le n j z)

/-- The `j`-th summand of the perturbation `chainAction n W - chainAction n (refGF N δ)`: on the
middle block (the rotation steps) it vanishes, off it it is `W j` evaluated at the `j`-th pair of
chain variables. -/
def stepFun (n N : ℕ) (δ : ℝ) (W : Fin (n + 1) → PS → ℝ) (j : Fin (n + 1))
    (z : ChainSp n) : ℝ :=
  if midBlock N (j : ℕ) then 0 else W j (projPS n j z)

theorem stepFun_of_mid {n N : ℕ} {δ : ℝ} {W : Fin (n + 1) → PS → ℝ} {j : Fin (n + 1)}
    (h : midBlock N (j : ℕ)) (z : ChainSp n) : stepFun n N δ W j z = 0 := by
  unfold stepFun; rw [if_pos h]

theorem stepFun_of_not_mid {n N : ℕ} {δ : ℝ} {W : Fin (n + 1) → PS → ℝ} {j : Fin (n + 1)}
    (h : ¬ midBlock N (j : ℕ)) (z : ChainSp n) : stepFun n N δ W j z = W j (projPS n j z) := by
  unfold stepFun; rw [if_neg h]

theorem stepFun_eq_zero {n N : ℕ} {δ : ℝ} {W : Fin (n + 1) → PS → ℝ} {j : Fin (n + 1)}
    (h : midBlock N (j : ℕ)) : stepFun n N δ W j = fun _ : ChainSp n => (0 : ℝ) := by
  funext z; exact stepFun_of_mid h z

theorem stepFun_eq_pullback {n N : ℕ} {δ : ℝ} {W : Fin (n + 1) → PS → ℝ} {j : Fin (n + 1)}
    (h : ¬ midBlock N (j : ℕ)) : stepFun n N δ W j = fun z => W j (projPS n j z) := by
  funext z; exact stepFun_of_not_mid h z

/-- Every summand of the perturbation is `C³` as soon as `W j` is. -/
theorem contDiff_stepFun {n N : ℕ} {δ : ℝ} {W : Fin (n + 1) → PS → ℝ} {j : Fin (n + 1)}
    (hWc : ContDiff ℝ 3 (W j)) : ContDiff ℝ 3 (stepFun n N δ W j) := by
  by_cases hm : midBlock N (j : ℕ)
  · rw [stepFun_eq_zero hm]; exact contDiff_const
  · rw [stepFun_eq_pullback hm]
    exact hWc.comp (projPS n j).contDiff

end

end Work.RPCore.Chain
