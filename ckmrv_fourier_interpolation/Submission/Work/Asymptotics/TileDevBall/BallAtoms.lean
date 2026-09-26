/-
# The atom bounds on the tile ball

The `ζ`-atoms (functions of the second variable only) and the `τ`-atoms (functions of `w` at
`τ = n +ᵥ w`, `n = ±1`) in the `BBdd` calculus of `TileDevBall/BallShape.lean`.

The `ζ`-atoms live on `{Im ζ ≥ 3}` (where `E₂, E₄, E₆, …` are bounded and `Δ`, `E₂ − 1` are
`O(e^{-2π Im ζ})`), the `τ`-atoms are transported from the `E`-region bounds of
`EtailE/Atoms.lean` and `Asymptotics/tile_Bdd_atoms.lean`.
-/
import Mathlib
import Submission.Work.Asymptotics.TileDevBall.BallShape
import Submission.Work.Asymptotics.tile_Bdd_atoms

set_option maxHeartbeats 1000000

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics.TileDevBall

open Work.Kernels

/-! ## The `ζ`-atoms -/

lemma zE2 : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => E2Fun ζ) := by
  obtain ⟨C, hC, hb⟩ := E2Fun_bound
  refine ⟨C, 0, hC, le_rfl, fun w ζ hw => ?_⟩
  have h1 := hb ζ (by linarith [hw.him])
  simpa using h1

lemma zE4 : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => E4Fun ζ) := by
  obtain ⟨C, hC, hb⟩ := E4Fun_bound
  refine ⟨C, 0, hC, le_rfl, fun w ζ hw => ?_⟩
  have h1 := hb ζ (by linarith [hw.him])
  simpa using h1

lemma zE6 : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => E6Fun ζ) := by
  obtain ⟨C, hC, hb⟩ := E6Fun_bound
  refine ⟨C, 0, hC, le_rfl, fun w ζ hw => ?_⟩
  have h1 := hb ζ (by linarith [hw.him])
  simpa using h1

lemma zE8 : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => E8Fun ζ) := by
  have h : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => E4Fun ζ * E4Fun ζ) := by
    simpa using BBdd.mul zE4 zE4
  refine BBdd.congr ?_ h
  funext w ζ
  rw [E8Fun, pow_two]

lemma zE10 : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => E10Fun ζ) := by
  have h : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => E4Fun ζ * E6Fun ζ) := by
    simpa using BBdd.mul zE4 zE6
  refine BBdd.congr ?_ h
  funext w ζ
  rw [E10Fun]

lemma zE14 : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => E14Fun ζ) := by
  have h : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => (E4Fun ζ * E4Fun ζ) * E6Fun ζ) := by
    have h1 : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => E4Fun ζ * E4Fun ζ) := by
      simpa using BBdd.mul zE4 zE4
    simpa using BBdd.mul h1 zE6
  refine BBdd.congr ?_ h
  funext w ζ
  rw [E14Fun]; ring

lemma zE2sub1 : BBdd 0 (-(2 * Real.pi)) (fun (_ : ℍ) (ζ : ℍ) => E2Fun ζ - 1) := by
  obtain ⟨C, hC, hb⟩ := E2Fun_two_term
  refine ⟨C + 24, 0, by positivity, le_rfl, fun w ζ hw => ?_⟩
  have him1 : (1:ℝ) ≤ ζ.im := by linarith [hw.him]
  have h1 := hb ζ him1
  have hq := norm_qParamFun ζ
  have he1 : Real.exp (-(2 * Real.pi * ζ.im)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [Real.pi_pos, hw.im_pos]
  have hq1 : ‖qParamFun ζ‖ ≤ 1 := by rw [hq]; exact he1
  have hsq : ‖qParamFun ζ‖ ^ 2 ≤ ‖qParamFun ζ‖ := by
    nlinarith [hq1, norm_nonneg (qParamFun ζ)]
  have hsplit : E2Fun ζ - 1 = (E2Fun ζ - 1 + 24 * qParamFun ζ) - 24 * qParamFun ζ := by ring
  have h24 : ‖(24 : ℂ) * qParamFun ζ‖ = 24 * ‖qParamFun ζ‖ := by
    rw [norm_mul]; norm_num
  have h2 : ‖E2Fun ζ - 1‖ ≤ (C + 24) * ‖qParamFun ζ‖ := by
    rw [hsplit]
    refine le_trans (norm_sub_le _ _) ?_
    rw [h24]
    nlinarith [h1, hsq, hC.le, norm_nonneg (qParamFun ζ)]
  have h3 : (C + 24) * ‖qParamFun ζ‖ ≤ (C + 24) * Real.exp ((-(2 * Real.pi)) * ζ.im) := by
    rw [hq]
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by positivity)
    ring_nf
  simpa using le_trans h2 h3

lemma zDelta : BBdd 0 (-(2 * Real.pi)) (fun (_ : ℍ) (ζ : ℍ) => DeltaFun ζ) := by
  obtain ⟨C, hC, hb⟩ := DeltaFun_upper
  refine ⟨C, 0, hC, le_rfl, fun w ζ hw => ?_⟩
  have h1 := hb ζ (by linarith [hw.him])
  rw [norm_qParamFun] at h1
  have h2 : Real.exp (-(2 * Real.pi * ζ.im)) = Real.exp ((-(2 * Real.pi)) * ζ.im) := by
    congr 1; ring
  rw [h2] at h1
  simpa using h1

lemma zcoe : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => (ζ : ℂ)) := by
  refine ⟨49 / 20, 1, by norm_num, by norm_num, fun w ζ hw => ?_⟩
  simpa using hw.norm_le_scaled

lemma znorm_pi : ‖(Real.pi : ℂ)‖ = Real.pi := EtailE.norm_pi

lemma zE2S : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => E2S ζ) := by
  obtain ⟨C, hC, hb⟩ := E2Fun_bound
  refine ⟨C + 1, 0, by positivity, le_rfl, fun w ζ hw => ?_⟩
  show ‖E2S ζ‖ ≤ (C + 1) * scale w ^ (0:ℝ) * Real.exp (0 * (ModularGroup.S • w).im)
      * Real.exp (0 * ζ.im)
  rw [TildeFacts.E2S_eq]
  have h1 := hb ζ (by linarith [hw.him])
  have hz : (3:ℝ) ≤ ‖(ζ : ℂ)‖ := le_trans hw.him (Work.Kernels.im_le_coe_norm ζ)
  have hzpos : 0 < ‖(ζ : ℂ)‖ := lt_of_lt_of_le (by norm_num) hz
  have h2 : ‖6 * Complex.I / ((Real.pi : ℂ) * (ζ : ℂ))‖ ≤ 1 := by
    rw [norm_div, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, znorm_pi]
    rw [div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three, hz]
  have h3 : ‖E2Fun ζ - 6 * Complex.I / ((Real.pi : ℂ) * (ζ : ℂ))‖ ≤ C + 1 := by
    refine le_trans (norm_sub_le _ _) ?_
    linarith
  simpa using h3

lemma zphit1 : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => phitVec ζ 1) := by
  have h : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => (ζ : ℂ) ^ 2 * E2S ζ) := by
    have h1 : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => (ζ : ℂ) * ((ζ : ℂ) * E2S ζ)) := by
      simpa using BBdd.mul zcoe (BBdd.mul zcoe zE2S)
    have h2 : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => (ζ : ℂ) ^ 2 * E2S ζ) := by
      simpa [pow_two, mul_assoc] using h1
    exact h2
  refine BBdd.congr ?_ h
  funext w ζ
  simp [phitVec]

lemma zphit2 : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => phitVec ζ 2) := by
  have h : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => (ζ : ℂ) ^ 2 * (E2S ζ * E2S ζ)) := by
    have h1 := BBdd.mul zcoe (BBdd.mul zcoe (BBdd.mul zE2S zE2S))
    have h2 : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) =>
        (ζ : ℂ) * ((ζ : ℂ) * (E2S ζ * E2S ζ))) := by
      simpa using h1
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h2
  refine BBdd.congr ?_ h
  funext w ζ
  simp [phitVec, mul_assoc, pow_two]


lemma zE4sq : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => E4Fun ζ ^ 2) := by
  have h : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => E4Fun ζ * E4Fun ζ) := by
    simpa using BBdd.mul zE4 zE4
  refine BBdd.congr ?_ h
  funext w ζ
  rw [pow_two]

lemma zE4cube : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => E4Fun ζ ^ 3) := by
  have h : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => E4Fun ζ * E4Fun ζ * E4Fun ζ) := by
    simpa using BBdd.mul (BBdd.mul zE4 zE4) zE4
  refine BBdd.congr ?_ h
  funext w ζ
  ring

lemma zcoe_sq : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => (ζ : ℂ) ^ 2) := by
  have h : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => (ζ : ℂ) * (ζ : ℂ)) := by
    simpa using BBdd.mul zcoe zcoe
  refine BBdd.congr ?_ h
  funext w ζ
  ring

/-- `E₂ ζ - 1` is `O(e^{-2π Im ζ})`; reduced to the plain shape. -/
lemma zE2sub1Bdd : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => E2Fun ζ - 1) :=
  zE2sub1.reduce (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

/-- `Δ ζ` is `O(e^{-2π Im ζ})`; reduced to the plain shape. -/
lemma zDeltaBdd : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => DeltaFun ζ) :=
  zDelta.reduce (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

/-! ## The `τ`-atoms -/

section Tau

lemma tE2 (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w : ℍ) (_ : ℍ) => E2Fun ((n:ℝ)+ᵥw)) :=
  BBdd.of_bdd (Work.Asymptotics.Bdd.vadd_E2 n hn)

lemma tE4 (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w : ℍ) (_ : ℍ) => E4Fun ((n:ℝ)+ᵥw)) :=
  BBdd.of_bdd (Work.Asymptotics.Bdd.vadd_E4 n hn)

lemma tE6 (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w : ℍ) (_ : ℍ) => E6Fun ((n:ℝ)+ᵥw)) :=
  BBdd.of_bdd (Work.Asymptotics.Bdd.vadd_E6 n hn)

lemma tE8 (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w : ℍ) (_ : ℍ) => E8Fun ((n:ℝ)+ᵥw)) :=
  BBdd.of_bdd (Work.Asymptotics.Bdd.vadd_E8 n hn)

lemma tE10 (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w : ℍ) (_ : ℍ) => E10Fun ((n:ℝ)+ᵥw)) :=
  BBdd.of_bdd (Work.Asymptotics.Bdd.vadd_E10 n hn)

lemma tE14 (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w : ℍ) (_ : ℍ) => E14Fun ((n:ℝ)+ᵥw)) :=
  BBdd.of_bdd (Work.Asymptotics.Bdd.vadd_E14 n hn)

lemma tDelta (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w : ℍ) (_ : ℍ) => DeltaFun ((n:ℝ)+ᵥw)) :=
  BBdd.of_bdd (Work.Asymptotics.Bdd.vadd_Delta n hn)

lemma tcoe (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w : ℍ) (_ : ℍ) => (((n:ℝ)+ᵥw : ℍ) : ℂ)) :=
  BBdd.of_bdd (Work.Asymptotics.Bdd.vadd n hn)

lemma tphi0 (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w : ℍ) (_ : ℍ) => phi0 ((n:ℝ)+ᵥw)) := by
  have h := BBdd.of_bdd (Work.Asymptotics.Bdd.vadd_phi1 n hn)
  refine BBdd.congr ?_ h
  funext w ζ
  rfl

lemma tphi2 (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w : ℍ) (_ : ℍ) => phi2 ((n:ℝ)+ᵥw)) := by
  have h := BBdd.of_bdd (Work.Asymptotics.Bdd.vadd_phi2 n hn)
  refine BBdd.congr ?_ h
  funext w ζ
  rfl

lemma tj (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd (2 * Real.pi) 0 (fun (w : ℍ) (_ : ℍ) => jInvariantFun ((n:ℝ)+ᵥw)) := by
  obtain ⟨C, N, hC, hN, hb⟩ := EtailE.E_bdd_j
  refine ⟨C, N, hC, hN, fun w ζ hw => ?_⟩
  simp only []
  rw [Work.Asymptotics.Tile.vadd_int_eq_self jInvariantFun
    (fun τ => KernelFacts.jInvariantFun_vadd_one τ) n hn w]
  have h1 := hb w hw.hw
  simpa using h1

lemma tinvDelta (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd (2 * Real.pi) 0 (fun (w : ℍ) (_ : ℍ) => (DeltaFun ((n:ℝ)+ᵥw))⁻¹) := by
  obtain ⟨C, N, hC, hN, hb⟩ := EtailE.E_bdd_invDelta
  refine ⟨C, N, hC, hN, fun w ζ hw => ?_⟩
  simp only []
  rw [Work.Asymptotics.Tile.vadd_int_eq_self DeltaFun
    (fun τ => KernelFacts.DeltaFun_vadd_one τ) n hn w]
  have h1 := hb w hw.hw
  simpa using h1

lemma tE14divDelta (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd (2 * Real.pi) 0 (fun (w : ℍ) (ζ : ℍ) =>
      E14Fun ((n:ℝ)+ᵥw) / DeltaFun ((n:ℝ)+ᵥw)) := by
  have h' : BBdd (2 * Real.pi) 0 (fun (w : ℍ) (ζ : ℍ) =>
      E14Fun ((n:ℝ)+ᵥw) * (DeltaFun ((n:ℝ)+ᵥw))⁻¹) := by
    simpa using BBdd.mul (tE14 n hn) (tinvDelta n hn)
  refine BBdd.congr ?_ h'
  funext w ζ
  rw [div_eq_mul_inv]

/-- `Δ ζ · j (n +ᵥ w)`: the product of the two exponential atoms, in the plain shape. -/
lemma deltaJmulBdd (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) => DeltaFun ζ * jInvariantFun ((n:ℝ)+ᵥw)) := by
  have h : BBdd (2 * Real.pi) (-(2 * Real.pi))
      (fun (w : ℍ) (ζ : ℍ) => DeltaFun ζ * jInvariantFun ((n:ℝ)+ᵥw)) := by
    simpa using BBdd.mul zDelta (tj n hn)
  exact h.reduce (by nlinarith [Real.pi_pos]) (by linarith [Real.pi_pos])

end Tau

end Work.Asymptotics.TileDevBall
