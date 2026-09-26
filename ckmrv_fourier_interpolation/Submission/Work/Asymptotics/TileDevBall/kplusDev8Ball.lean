/-
# The cleared deviation bound for `K_+^{(8)}` on the cusp-`±1` tile ball

The target `Work.Asymptotics.TileDevBall.kplusDev8Ball` bounds

  `‖Sh τ ζ · (K_+^{(8)}(τ,ζ) - 𝒢_+^{(8)}(τ,ζ))‖ ≤ C (scale w)^N`

on the ball `‖ζ - S • w‖ ≤ 29/20`, `3 ≤ Im ζ`, `w ∈ E = KEpsilon`, `τ = n +ᵥ w`, `n = ±1`.

The mathematical content is the *cancellation of the pole* of `K_+^{(8)}` at `j τ = j ζ`: the
prefactor `Sh τ ζ = E₄(ζ)³ - Δ(ζ)j(τ) = -Δ(ζ)(j τ - j ζ)` removes exactly the denominator of the
cusp-expansion remainder, and the algebra of `Compact.KPlus8_sub_Gplus8_decomp` then expresses
`Sh · (K_+ - 𝒢_+)` as a finite combination of atoms, all of which are polynomially bounded in
`scale w` on the ball (`Δ(ζ)` and `E₂(ζ) - 1` are exponentially small, `j(τ)` and `Δ(τ)⁻¹` are
`O(e^{2π Im (S • w)})`, and `Im ζ ≥ Im (S • w) - 29/20` on the ball, which is exactly what makes
the `τ`-side and `ζ`-side exponential factors cancel).
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.Compact.kplus8_tail_core
import Submission.Work.Asymptotics.Compact.kminus_tail_core
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.EtailE.Shapes
import Submission.Work.Asymptotics.EBase
import Submission.Work.Asymptotics.EtailE.Atoms
import Submission.Work.Asymptotics.tile_Bdd_atoms
import Submission.Work.Asymptotics.TileDevBall.BallShape
import Submission.Work.Asymptotics.TileDevBall.BallAtoms

set_option maxHeartbeats 2000000

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

namespace Work.Asymptotics.TileDevBall

open Work.Kernels
open Work.Asymptotics.Compact

/-! ## Elementary helpers -/

/-- Monotonicity of `C · X^N` in both `C` and `N`, for `X ≥ 1`. -/
lemma le_mul_rpow_mono {C C' N N' X : ℝ} (hX : 1 ≤ X) (hC : C ≤ C') (hN : N ≤ N')
    (hC0 : 0 ≤ C) : C * X ^ N ≤ C' * X ^ N' := by
  have h1 : C * X ^ N ≤ C' * X ^ N := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (by linarith) N)
  have h2 : C' * X ^ N ≤ C' * X ^ N' :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hX hN) (le_trans hC0 hC)
  exact le_trans h1 h2

lemma rpow_mono_scale {w : ℍ} {N M : ℝ} (hN : N ≤ M) : (scale w) ^ N ≤ (scale w) ^ M :=
  Real.rpow_le_rpow_of_exponent_le (Work.Kernels.one_le_scale w) hN

/-- The constant right-hand side of a `BBdd 0 0` bound is nonnegative on the ball. -/
lemma ball_nonneg {C N : ℝ} (hC : 0 ≤ C) (w ζ : ℍ) :
    (0:ℝ) ≤ C * (scale w) ^ N * Real.exp (0 * (ModularGroup.S • w).im) * Real.exp (0 * ζ.im) :=
  mul_nonneg (mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos w)) N))
    (Real.exp_pos _).le) (Real.exp_pos _).le

/-! ## The `Sh` identity and the cancellation of the pole -/

/-- `Sh τ ζ = -Δ(ζ)(j τ - j ζ)`. -/
lemma Sh_eq' (τ ζ : ℍ) : Sh τ ζ = -DeltaFun ζ * (jInvariantFun τ - jInvariantFun ζ) := by
  rw [Sh, ← ClassicalFacts.DeltaFun_mul_jInvariantFun ζ]
  ring

/-- The closed form of `Sh τ ζ · Φ₂(τ,ζ)` (valid for `j τ ≠ j ζ`). -/
def DivCorr (τ ζ : ℍ) : ℂ :=
  DeltaFun ζ * (phi2 τ * (E14Fun τ / DeltaFun τ) * (ζ : ℂ) ^ 2)

/-- The closed form of `Sh τ ζ · Φ₃(τ,ζ)` (valid for `j τ ≠ j ζ`). -/
def NumCorr (τ ζ : ℍ) : ℂ :=
  (τ : ℂ) * E6Fun τ * phitVec ζ 2 * (E8Fun ζ - E4Fun ζ ^ 3 + DeltaFun ζ * jInvariantFun τ)
    - 2 * phi0 τ * E4Fun τ * phitVec ζ 1
      * (E10Fun ζ - E4Fun ζ ^ 3 + DeltaFun ζ * jInvariantFun τ)

/-- The cancellation in the `Φ₂` piece. -/
lemma Sh_mul_PhiDiv' (τ ζ : ℍ) (hJ : jInvariantFun τ ≠ jInvariantFun ζ) :
    Sh τ ζ * PhiDiv τ ζ = -DivCorr τ ζ := by
  have hJ' : E4Fun τ ^ 3 / DeltaFun τ - E4Fun ζ ^ 3 / DeltaFun ζ ≠ 0 := by
    have h := sub_ne_zero.mpr hJ
    simpa only [jInvariantFun] using h
  have hDτ : DeltaFun τ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero τ
  have hD : DeltaFun τ * (E4Fun τ ^ 3 / DeltaFun τ - E4Fun ζ ^ 3 / DeltaFun ζ) ≠ 0 :=
    mul_ne_zero hDτ hJ'
  refine mul_right_cancel₀ hD ?_
  rw [Sh_eq' τ ζ, PhiDiv_eq]
  unfold DivCorr
  field_simp

/-- The cancellation in the `Φ₃` piece. -/
lemma Sh_mul_PhiCorr' (τ ζ : ℍ) (hJ : jInvariantFun τ ≠ jInvariantFun ζ) :
    Sh τ ζ * PhiCorr τ ζ = -NumCorr τ ζ := by
  have hJ' : E4Fun τ ^ 3 / DeltaFun τ - E4Fun ζ ^ 3 / DeltaFun ζ ≠ 0 := by
    have h := sub_ne_zero.mpr hJ
    simpa only [jInvariantFun] using h
  have hDz : DeltaFun ζ ≠ 0 := ClassicalFacts.DeltaFun_ne_zero ζ
  have hD : DeltaFun ζ * (E4Fun τ ^ 3 / DeltaFun τ - E4Fun ζ ^ 3 / DeltaFun ζ) ≠ 0 :=
    mul_ne_zero hDz hJ'
  refine mul_right_cancel₀ hD ?_
  rw [Sh_eq' τ ζ]
  unfold PhiCorr NumCorr
  field_simp

/-! ## The pieces of the decomposition, in the ball calculus -/

/-- `Sh (n +ᵥ w) ζ` is polynomially bounded on the ball. -/
lemma shBdd (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) => Sh ((n:ℝ)+ᵥw) ζ) := by
  have h3 : BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) =>
      E4Fun ζ ^ 3 - DeltaFun ζ * jInvariantFun ((n:ℝ)+ᵥw)) := by
    simpa using (zE4cube.sub (deltaJmulBdd n hn))
  refine BBdd.congr ?_ h3
  funext w ζ
  rw [Sh]

/-- The bracket `Φ_L(ζ) = -(ζ²(1+E₂(ζ))) + 12iζ/π` is polynomially bounded on the ball. -/
lemma phiLBdd : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => PhiL ζ) := by
  have hA : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => (ζ : ℂ) ^ 2 * (1 + E2Fun ζ)) := by
    have h2 : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => (1 : ℂ) + E2Fun ζ) := by
      simpa using (BBdd.const (1 : ℂ)).add zE2
    simpa using BBdd.mul zcoe_sq h2
  have hB : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => 12 * Complex.I * (ζ : ℂ) / (Real.pi : ℂ)) := by
    have h1 : BBdd 0 0 (fun (_ : ℍ) (ζ : ℍ) => (12 * Complex.I / (Real.pi : ℂ)) * (ζ : ℂ)) :=
      BBdd.const_mul _ zcoe
    refine BBdd.congr ?_ h1
    funext w ζ
    first | rfl | ring | ring_nf
  have h : BBdd (max 0 0) (max 0 0) (fun (_ : ℍ) (ζ : ℍ) => -((ζ : ℂ) ^ 2 * (1 + E2Fun ζ))
      + 12 * Complex.I * (ζ : ℂ) / (Real.pi : ℂ)) := hA.neg.add hB
  refine BBdd.congr ?_ (by simpa using h)
  funext w ζ
  rw [PhiL]

/-- The `Φ₁` piece of `Sh · (K₊ - 𝒢₊)`. -/
lemma shPhiMainBdd (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) => Sh ((n:ℝ)+ᵥw) ζ * PhiMain ((n:ℝ)+ᵥw) ζ) := by
  have hA : BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) =>
      (((n:ℝ)+ᵥw : ℍ) : ℂ) * E6Fun ((n:ℝ)+ᵥw) * PhiL ζ) := by
    simpa using BBdd.mul (BBdd.mul (tcoe n hn) (tE6 n hn)) phiLBdd
  have hB : BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) =>
      2 * phi0 ((n:ℝ)+ᵥw) * E4Fun ((n:ℝ)+ᵥw) * (ζ : ℂ) ^ 2) := by
    have h1 : BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) => (2 : ℂ) * phi0 ((n:ℝ)+ᵥw)) := by
      simpa using BBdd.const_mul (2 : ℂ) (tphi0 n hn)
    simpa [mul_assoc] using BBdd.mul (BBdd.mul h1 (tE4 n hn)) zcoe_sq
  have hBr : BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) =>
      (((n:ℝ)+ᵥw : ℍ) : ℂ) * E6Fun ((n:ℝ)+ᵥw) * PhiL ζ
        + 2 * phi0 ((n:ℝ)+ᵥw) * E4Fun ((n:ℝ)+ᵥw) * (ζ : ℂ) ^ 2) := by
    simpa using hA.add hB
  have h := BBdd.mul (BBdd.mul (shBdd n hn) zE2sub1Bdd) hBr
  refine BBdd.congr ?_ (by simpa using h)
  funext w ζ
  rw [PhiMain_eq, mul_assoc]
  first | rfl | ring | ring_nf

/-- The `Φ₂` piece of `Sh · (K₊ - 𝒢₊)`. -/
lemma shPhiDivBdd (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) => Sh ((n:ℝ)+ᵥw) ζ * PhiDiv ((n:ℝ)+ᵥw) ζ) := by
  have hdiv : BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) => DivCorr ((n:ℝ)+ᵥw) ζ) := by
    have h1 : BBdd (2 * Real.pi) (-(2 * Real.pi)) (fun (w : ℍ) (ζ : ℍ) =>
        DeltaFun ζ * (E14Fun ((n:ℝ)+ᵥw) / DeltaFun ((n:ℝ)+ᵥw))) := by
      simpa using BBdd.mul zDelta (tE14divDelta ℓ n hn)
    have h4 : BBdd (2 * Real.pi) (-(2 * Real.pi)) (fun (w : ℍ) (ζ : ℍ) =>
        DeltaFun ζ * (E14Fun ((n:ℝ)+ᵥw) / DeltaFun ((n:ℝ)+ᵥw))
          * (phi2 ((n:ℝ)+ᵥw) * (ζ : ℂ) ^ 2)) := by
      simpa using BBdd.mul h1 (BBdd.mul (tphi2 n hn) zcoe_sq)
    have h5 : BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) =>
        DeltaFun ζ * (phi2 ((n:ℝ)+ᵥw) * (E14Fun ((n:ℝ)+ᵥw) / DeltaFun ((n:ℝ)+ᵥw))
          * (ζ : ℂ) ^ 2)) := by
      refine BBdd.congr ?_ (h4.reduce (by nlinarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
      funext w ζ
      ring
    exact h5
  obtain ⟨C, N, hC, hN, hb⟩ := BBdd.exists_bound_zero hdiv
  refine ⟨max C 1, N, by positivity, hN, fun w ζ hw => ?_⟩
  simp only [zero_mul, Real.exp_zero, mul_one]
  by_cases hJ : jInvariantFun ((n:ℝ)+ᵥw) = jInvariantFun ζ
  · have hz : PhiDiv ((n:ℝ)+ᵥw) ζ = 0 := by
      rw [PhiDiv, hJ, sub_self, mul_zero, div_zero]
    rw [hz, mul_zero, norm_zero]
    exact mul_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_right C 1)))
      (Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos w)) N)
  · rw [Sh_mul_PhiDiv' _ _ hJ, norm_neg]
    exact le_trans (hb w ζ hw)
      (le_mul_rpow_mono hw.one_le_scale (le_max_left C 1) le_rfl (le_of_lt hC))

/-- The two `Φ₃` brackets are polynomially bounded on the ball. -/
lemma phiCorrBracketsBdd (n : ℤ) (hn : n = 1 ∨ n = -1) :
    (BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) =>
        E8Fun ζ - E4Fun ζ ^ 3 + DeltaFun ζ * jInvariantFun ((n:ℝ)+ᵥw))) ∧
    (BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) =>
        E10Fun ζ - E4Fun ζ ^ 3 + DeltaFun ζ * jInvariantFun ((n:ℝ)+ᵥw))) :=
  ⟨by simpa using (zE8.sub zE4cube).add (deltaJmulBdd n hn),
   by simpa using (zE10.sub zE4cube).add (deltaJmulBdd n hn)⟩

/-- The `Φ₃` piece of `Sh · (K₊ - 𝒢₊)`. -/
lemma shPhiCorrBdd (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) => Sh ((n:ℝ)+ᵥw) ζ * PhiCorr ((n:ℝ)+ᵥw) ζ) := by
  obtain ⟨hB8, hB10⟩ := phiCorrBracketsBdd n hn
  have hA : BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) =>
      (((n:ℝ)+ᵥw : ℍ) : ℂ) * E6Fun ((n:ℝ)+ᵥw) * phitVec ζ 2
        * (E8Fun ζ - E4Fun ζ ^ 3 + DeltaFun ζ * jInvariantFun ((n:ℝ)+ᵥw))) := by
    simpa [mul_assoc] using BBdd.mul (BBdd.mul (BBdd.mul (tcoe n hn) (tE6 n hn)) zphit2) hB8
  have hB : BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) =>
      2 * phi0 ((n:ℝ)+ᵥw) * E4Fun ((n:ℝ)+ᵥw) * phitVec ζ 1
        * (E10Fun ζ - E4Fun ζ ^ 3 + DeltaFun ζ * jInvariantFun ((n:ℝ)+ᵥw))) := by
    have h1 : BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) => (2 : ℂ) * phi0 ((n:ℝ)+ᵥw)) := by
      simpa using BBdd.const_mul (2 : ℂ) (tphi0 n hn)
    simpa [mul_assoc] using BBdd.mul (BBdd.mul (BBdd.mul h1 (tE4 n hn)) zphit1) hB10
  have hnum : BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) => NumCorr ((n:ℝ)+ᵥw) ζ) := by
    refine BBdd.congr ?_ (by simpa using hA.sub hB)
    funext w ζ
    rw [NumCorr]
    first | rfl | ring | ring_nf
  obtain ⟨C, N, hC, hN, hb⟩ := BBdd.exists_bound_zero hnum
  refine ⟨max C 1, N, by positivity, hN, fun w ζ hw => ?_⟩
  simp only [zero_mul, Real.exp_zero, mul_one]
  by_cases hJ : jInvariantFun ((n:ℝ)+ᵥw) = jInvariantFun ζ
  · have hz : PhiCorr ((n:ℝ)+ᵥw) ζ = 0 := by
      unfold PhiCorr
      rw [hJ, sub_self, mul_zero, div_zero]
    rw [hz, mul_zero, norm_zero]
    exact mul_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_right C 1)))
      (Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos w)) N)
  · rw [Sh_mul_PhiCorr' _ _ hJ, norm_neg]
    exact le_trans (hb w ζ hw)
      (le_mul_rpow_mono hw.one_le_scale (le_max_left C 1) le_rfl (le_of_lt hC))

/-! ## The deviation bound -/

/-- `Sh (n +ᵥ w) ζ · (K₊^{(8)}(n +ᵥ w, ζ) - 𝒢₊^{(8)}(n +ᵥ w, ζ))` is polynomially bounded. -/
lemma devBBdd (ℓ : LogLambdaData) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    BBdd 0 0 (fun (w : ℍ) (ζ : ℍ) => Sh ((n:ℝ)+ᵥw) ζ
      * (KPlus 8 ((n:ℝ)+ᵥw) ζ - Gplus 8 ((n:ℝ)+ᵥw) ζ)) := by
  have hgen : ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧ ∀ (w ζ : ℍ), Ball w ζ →
      jInvariantFun ((n:ℝ)+ᵥw) ≠ jInvariantFun ζ →
      ‖Sh ((n:ℝ)+ᵥw) ζ * (KPlus 8 ((n:ℝ)+ᵥw) ζ - Gplus 8 ((n:ℝ)+ᵥw) ζ)‖
        ≤ C * (scale w) ^ N := by
    obtain ⟨C1, N1, hC1, hN1, hb1⟩ := BBdd.exists_bound_zero (shPhiMainBdd n hn)
    obtain ⟨C2, N2, hC2, hN2, hb2⟩ := BBdd.exists_bound_zero (shPhiDivBdd ℓ n hn)
    obtain ⟨C3, N3, hC3, hN3, hb3⟩ := BBdd.exists_bound_zero (shPhiCorrBdd n hn)
    refine ⟨‖tailC⁻¹‖ * (C1 + C2 + C3) + 1, max (max N1 N2) N3, by positivity,
      le_trans hN1 (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
    intro w ζ hw hJ
    have hX : (1:ℝ) ≤ scale w := hw.one_le_scale
    have hN1' : N1 ≤ max (max N1 N2) N3 := le_trans (le_max_left _ _) (le_max_left _ _)
    have hN2' : N2 ≤ max (max N1 N2) N3 := le_trans (le_max_right _ _) (le_max_left _ _)
    have hN3' : N3 ≤ max (max N1 N2) N3 := le_max_right _ _
    have e1 : ‖Sh ((n:ℝ)+ᵥw) ζ * PhiMain ((n:ℝ)+ᵥw) ζ‖
        ≤ C1 * (scale w) ^ (max (max N1 N2) N3) :=
      le_trans (hb1 w ζ hw) (mul_le_mul_of_nonneg_left (rpow_mono_scale hN1') hC1.le)
    have e2 : ‖Sh ((n:ℝ)+ᵥw) ζ * PhiDiv ((n:ℝ)+ᵥw) ζ‖
        ≤ C2 * (scale w) ^ (max (max N1 N2) N3) :=
      le_trans (hb2 w ζ hw) (mul_le_mul_of_nonneg_left (rpow_mono_scale hN2') hC2.le)
    have e3 : ‖Sh ((n:ℝ)+ᵥw) ζ * PhiCorr ((n:ℝ)+ᵥw) ζ‖
        ≤ C3 * (scale w) ^ (max (max N1 N2) N3) :=
      le_trans (hb3 w ζ hw) (mul_le_mul_of_nonneg_left (rpow_mono_scale hN3') hC3.le)
    have hsum : ‖Sh ((n:ℝ)+ᵥw) ζ * PhiMain ((n:ℝ)+ᵥw) ζ
          + Sh ((n:ℝ)+ᵥw) ζ * PhiDiv ((n:ℝ)+ᵥw) ζ
          + Sh ((n:ℝ)+ᵥw) ζ * PhiCorr ((n:ℝ)+ᵥw) ζ‖
        ≤ (C1 + C2 + C3) * (scale w) ^ (max (max N1 N2) N3) := by
      have htri1 : ‖Sh ((n:ℝ)+ᵥw) ζ * PhiMain ((n:ℝ)+ᵥw) ζ
              + Sh ((n:ℝ)+ᵥw) ζ * PhiDiv ((n:ℝ)+ᵥw) ζ
              + Sh ((n:ℝ)+ᵥw) ζ * PhiCorr ((n:ℝ)+ᵥw) ζ‖
          ≤ ‖Sh ((n:ℝ)+ᵥw) ζ * PhiMain ((n:ℝ)+ᵥw) ζ
                + Sh ((n:ℝ)+ᵥw) ζ * PhiDiv ((n:ℝ)+ᵥw) ζ‖
            + ‖Sh ((n:ℝ)+ᵥw) ζ * PhiCorr ((n:ℝ)+ᵥw) ζ‖ := norm_add_le _ _
      have htri2 : ‖Sh ((n:ℝ)+ᵥw) ζ * PhiMain ((n:ℝ)+ᵥw) ζ
                + Sh ((n:ℝ)+ᵥw) ζ * PhiDiv ((n:ℝ)+ᵥw) ζ‖
          ≤ ‖Sh ((n:ℝ)+ᵥw) ζ * PhiMain ((n:ℝ)+ᵥw) ζ‖
            + ‖Sh ((n:ℝ)+ᵥw) ζ * PhiDiv ((n:ℝ)+ᵥw) ζ‖ := norm_add_le _ _
      have hgoal : C1 * (scale w) ^ (max (max N1 N2) N3)
              + C2 * (scale w) ^ (max (max N1 N2) N3)
              + C3 * (scale w) ^ (max (max N1 N2) N3)
          = (C1 + C2 + C3) * (scale w) ^ (max (max N1 N2) N3) := by ring
      linarith [htri1, htri2, e1, e2, e3, hgoal]
    have hgp : Gplus 8 ((n:ℝ)+ᵥw) ζ = Gplus8 ((n:ℝ)+ᵥw) ζ := by
      rw [Gplus]; exact if_pos rfl
    have hdec := KPlus8_sub_Gplus8_decomp ((n:ℝ)+ᵥw) ζ hJ
    have hrew : Sh ((n:ℝ)+ᵥw) ζ
          * (tailC⁻¹ * (PhiMain ((n:ℝ)+ᵥw) ζ + PhiDiv ((n:ℝ)+ᵥw) ζ
              + PhiCorr ((n:ℝ)+ᵥw) ζ))
        = tailC⁻¹ * (Sh ((n:ℝ)+ᵥw) ζ * PhiMain ((n:ℝ)+ᵥw) ζ
            + Sh ((n:ℝ)+ᵥw) ζ * PhiDiv ((n:ℝ)+ᵥw) ζ
            + Sh ((n:ℝ)+ᵥw) ζ * PhiCorr ((n:ℝ)+ᵥw) ζ) := by ring
    rw [hgp, hdec, hrew, norm_mul]
    have h1 : ‖tailC⁻¹‖ * ‖Sh ((n:ℝ)+ᵥw) ζ * PhiMain ((n:ℝ)+ᵥw) ζ
            + Sh ((n:ℝ)+ᵥw) ζ * PhiDiv ((n:ℝ)+ᵥw) ζ
            + Sh ((n:ℝ)+ᵥw) ζ * PhiCorr ((n:ℝ)+ᵥw) ζ‖
        ≤ ‖tailC⁻¹‖ * ((C1 + C2 + C3) * (scale w) ^ (max (max N1 N2) N3)) :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    have h2 : ‖tailC⁻¹‖ * ((C1 + C2 + C3) * (scale w) ^ (max (max N1 N2) N3))
        ≤ (‖tailC⁻¹‖ * (C1 + C2 + C3) + 1) * (scale w) ^ (max (max N1 N2) N3) := by
      have hX1 : (1:ℝ) ≤ (scale w) ^ (max (max N1 N2) N3) :=
        Real.one_le_rpow hX (le_trans hN1 hN1')
      have hT0 : (0:ℝ) ≤ ‖tailC⁻¹‖ * (C1 + C2 + C3) := by positivity
      nlinarith [hT0, hX1, mul_nonneg hT0 (le_trans zero_le_one hX1)]
    linarith [h1, h2]
  obtain ⟨C, N, hC, hN, hb⟩ := hgen
  refine ⟨max C 1, N, by positivity, hN, fun w ζ hw => ?_⟩
  simp only [zero_mul, Real.exp_zero, mul_one]
  by_cases hJ : jInvariantFun ((n:ℝ)+ᵥw) = jInvariantFun ζ
  · have hSh0 : Sh ((n:ℝ)+ᵥw) ζ = 0 := by
      rw [Sh_eq' ((n:ℝ)+ᵥw) ζ, hJ, sub_self, mul_zero]
    rw [hSh0, zero_mul, norm_zero]
    exact mul_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one (le_max_right C 1)))
      (Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos w)) N)
  · exact le_trans (hb w ζ hw hJ)
      (le_mul_rpow_mono hw.one_le_scale (le_max_left C 1) le_rfl (le_of_lt hC))

set_option autoImplicit false in
theorem kplusDev8Ball (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → ∀ (n : ℤ), (n = 1 ∨ n = -1) →
        ∀ ζ : UpperHalfPlane, ‖(ζ : ℂ) - (((ModularGroup.S • w : UpperHalfPlane)) : ℂ)‖ ≤ 29 / 20 →
          3 ≤ ζ.im →
          ‖Work.Asymptotics.Compact.Sh ((n : ℝ) +ᵥ w) ζ
            * (Work.Kernels.KPlus 8 ((n : ℝ) +ᵥ w) ζ
                - Work.Asymptotics.Compact.Gplus 8 ((n : ℝ) +ᵥ w) ζ)‖
          ≤ C * (Work.Kernels.scale w) ^ N := by
  obtain ⟨C1, N1, hC1, hN1, h1⟩ := BBdd.exists_bound_zero (devBBdd ℓ 1 (Or.inl rfl))
  obtain ⟨C2, N2, hC2, hN2, h2⟩ := BBdd.exists_bound_zero (devBBdd ℓ (-1) (Or.inr rfl))
  refine ⟨max C1 C2 + 1, max N1 N2, by positivity, le_max_of_le_left hN1, ?_⟩
  intro w hw n hn ζ hball him
  have hB : Ball w ζ := ⟨hw, hball, him⟩
  rcases hn with h | h
  · subst h
    exact le_trans (h1 w ζ hB)
      (le_mul_rpow_mono hB.one_le_scale (by linarith [le_max_left C1 C2]) (le_max_left N1 N2)
        (le_of_lt hC1))
  · subst h
    exact le_trans (h2 w ζ hB)
      (le_mul_rpow_mono hB.one_le_scale (by linarith [le_max_right C1 C2]) (le_max_right N1 N2)
        (le_of_lt hC2))

end Work.Asymptotics.TileDevBall
