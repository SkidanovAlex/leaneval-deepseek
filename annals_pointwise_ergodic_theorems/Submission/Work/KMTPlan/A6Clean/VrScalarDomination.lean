/-
# Step 2 (vector-valued): the `ℓ²(ZMod Q)`-valued `V^R` datum is dominated by the scalar `V^R`'s

**Brick of step 2 of the `(lin-1)`/`(lin-2)` proof** (see
`NOTES_MdlWindowLift_CORRECTED_BAND.md` §6).  Step 2 in its *scalar* form is the proved
`Work.KMTAreas.A7Hi.vrsdIntegralLeSamples`:

  `∫⁻ x, (V^r (n ↦ 𝓕⁻(W n) x))^p ≤ C(r,p) · Σ'_m (V^r (n ↦ 𝓕⁻(W n) m))^p`

for amplitudes `W n` supported in `Icc (-1/4) (1/4)`.  The datum of the `(lin-1)`/`(lin-2)` clauses
is instead `ℓ²(ZMod Q)`-valued, i.e. `VrLiftDataP`.  This file provides the comparison that makes
the scalar estimate applicable:

  `VrLiftDataP 2 Q u ≤ 2 · (Q⁻¹ Σ_θ (V^2 (n ↦ u n θ))²)^{1/2}`,

i.e. (after squaring, `VrLiftDataP_two_sq_le`) the *squared* `ℓ²(ZMod Q)`-valued datum is
dominated by the average over `θ` of the squared *scalar* variational norms — with the `Q⁻¹`
normalisation of `zmodProb Q` and **no cardinality loss**.

Ingredients (all elementary, no analysis):
* `(eLpNorm f 2 (zmodProb Q))² = Q⁻¹ Σ_θ ‖f θ‖ₑ²` (`eLpNorm_zmodProb_two_sq`);
* the sup part: `‖u n θ‖ₑ ≤ V^2 (n ↦ u n θ)` (`Work.KMTAreas.A7.enorm_apply_le_variationalNorm`);
* the variation part: every monotone `Fin (J+1)`-chain sum of squared increments is
  `≤ (V^2 (n ↦ u n θ))²` (`Work.KMTPlan.A6Clean.chain_sum_sq_le_variationalNorm`,
  `VrChainSumLe.lean`).

The *reverse* comparison (needed to bound the lattice side below, before applying `hfib`) is the
sup-over-chains interchange `⨆_P Σ_θ f_θ(P) = Σ_θ ⨆_P f_θ(P)` (directedness of the chains under
refinement); it is not in this file.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlAdelicProb
import Submission.Work.KMTPlan.A6Clean.VrChainSumLe
import Submission.Port.Aesm

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.KMTPlan.A6Clean

open MeasureTheory Finset
open scoped BigOperators ENNReal NNReal

/-- **The squared `L²(zmodProb Q)`-norm of a function on `ZMod Q`** is the normalised sum of the
squared norms. -/
theorem eLpNorm_zmodProb_two_sq {Q : ℕ} [NeZero Q] (f : ZMod Q → ℂ) :
    (eLpNorm f 2 (Work.KMTPlan.A6.zmodProb Q)) ^ (2 : ℕ)
      = (Q : ENNReal)⁻¹ * ∑ θ : ZMod Q, ‖f θ‖ₑ ^ (2 : ℕ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ⊤)]
  rw [show ((2 : ENNReal).toReal) = (2 : ℝ) by norm_num,
    show (1 / (2 : ℝ)) = ((1 / 2 : ℝ)) by norm_num]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
    show ((1 / 2 : ℝ) * ((2 : ℕ) : ℝ)) = 1 from by norm_num, ENNReal.rpow_one,
    Work.KMTPlan.A6.zmodProb, MeasureTheory.lintegral_smul_measure, MeasureTheory.lintegral_count,
    tsum_fintype, smul_eq_mul]
  congr 1
  exact Finset.sum_congr rfl fun θ _ => ENNReal.rpow_natCast _ 2

/-- **The sup part of `VrLiftDataP` is dominated by the scalar variational norms.** -/
theorem eLpNorm_le_sum_variationalNorm {Q : ℕ} [NeZero Q] (u : ℕ → ZMod Q → ℂ) (n : ℕ) :
    eLpNorm (u n) 2 (Work.KMTPlan.A6.zmodProb Q)
      ≤ ((Q : ENNReal)⁻¹ * ∑ θ : ZMod Q,
          (PointwiseErgodicTheorems.variationalNorm 2 (fun k => u k θ)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
  set Y : ENNReal := (Q : ENNReal)⁻¹ * ∑ θ : ZMod Q,
    (PointwiseErgodicTheorems.variationalNorm 2 (fun k => u k θ)) ^ (2 : ℕ) with hY
  have h1 : (eLpNorm (u n) 2 (Work.KMTPlan.A6.zmodProb Q)) ^ (2 : ℕ) ≤ Y := by
    rw [eLpNorm_zmodProb_two_sq, hY]
    refine mul_le_mul' le_rfl ?_
    refine Finset.sum_le_sum fun θ _ => ?_
    have h2 := Work.KMTAreas.A7.enorm_apply_le_variationalNorm (r := 2) (fun k => u k θ) n
    calc ‖u n θ‖ₑ ^ (2 : ℕ) = ‖u n θ‖ₑ * ‖u n θ‖ₑ := by rw [pow_two]
      _ ≤ (PointwiseErgodicTheorems.variationalNorm 2 (fun k => u k θ))
            * (PointwiseErgodicTheorems.variationalNorm 2 (fun k => u k θ)) :=
          mul_le_mul' h2 h2
      _ = (PointwiseErgodicTheorems.variationalNorm 2 (fun k => u k θ)) ^ (2 : ℕ) := by
          rw [pow_two]
  calc eLpNorm (u n) 2 (Work.KMTPlan.A6.zmodProb Q)
      = ((eLpNorm (u n) 2 (Work.KMTPlan.A6.zmodProb Q)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ Y ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h1 (by norm_num)

/-- **The variation part of `VrLiftDataP` is dominated by the scalar variational norms.** -/
theorem rpow_sum_eLpNorm_le_sum_variationalNorm {Q : ℕ} [NeZero Q] (u : ℕ → ZMod Q → ℂ)
    (J : ℕ) (k : Fin (J + 1) → ℕ) (hk : Monotone k) :
    (∑ i : Fin J, (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2
        (Work.KMTPlan.A6.zmodProb Q)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ)
      ≤ ((Q : ENNReal)⁻¹ * ∑ θ : ZMod Q,
          (PointwiseErgodicTheorems.variationalNorm 2 (fun n => u n θ)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
  set Y : ENNReal := (Q : ENNReal)⁻¹ * ∑ θ : ZMod Q,
    (PointwiseErgodicTheorems.variationalNorm 2 (fun n => u n θ)) ^ (2 : ℕ) with hY
  have h1 : (∑ i : Fin J, (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2
      (Work.KMTPlan.A6.zmodProb Q)) ^ (2 : ℕ)) ≤ Y := by
    rw [hY]
    calc (∑ i : Fin J, (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2
          (Work.KMTPlan.A6.zmodProb Q)) ^ (2 : ℕ))
        = ∑ i : Fin J, (Q : ENNReal)⁻¹ * ∑ θ : ZMod Q,
            ‖u (k i.succ) θ - u (k i.castSucc) θ‖ₑ ^ (2 : ℕ) :=
          Finset.sum_congr rfl fun i _ => eLpNorm_zmodProb_two_sq _
      _ = (Q : ENNReal)⁻¹ * ∑ i : Fin J, ∑ θ : ZMod Q,
            ‖u (k i.succ) θ - u (k i.castSucc) θ‖ₑ ^ (2 : ℕ) := by
          rw [Finset.mul_sum]
      _ = (Q : ENNReal)⁻¹ * ∑ θ : ZMod Q, ∑ i : Fin J,
            ‖u (k i.succ) θ - u (k i.castSucc) θ‖ₑ ^ (2 : ℕ) := by
          rw [Finset.sum_comm]
      _ ≤ (Q : ENNReal)⁻¹ * ∑ θ : ZMod Q,
            (PointwiseErgodicTheorems.variationalNorm 2 (fun n => u n θ)) ^ (2 : ℕ) := by
          refine mul_le_mul' le_rfl ?_
          refine Finset.sum_le_sum fun θ _ => ?_
          exact chain_sum_sq_le_variationalNorm k hk (fun n => u n θ)
  exact ENNReal.rpow_le_rpow h1 (by norm_num)

/-- **Step 2, vector-valued, pointwise.**  The `ℓ²(ZMod Q)`-valued `V^2` datum is at most twice the
normalised `ℓ²`-norm of the scalar `V^2`'s. -/
theorem VrLiftDataP_two_le {Q : ℕ} [NeZero Q] (u : ℕ → ZMod Q → ℂ) :
    Work.KMTPlan.A6.VrLiftDataP (2 : ℝ) Q u
      ≤ 2 * ((Q : ENNReal)⁻¹ * ∑ θ : ZMod Q,
          (PointwiseErgodicTheorems.variationalNorm 2 (fun n => u n θ)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
  set Y : ENNReal := (Q : ENNReal)⁻¹ * ∑ θ : ZMod Q,
    (PointwiseErgodicTheorems.variationalNorm 2 (fun n => u n θ)) ^ (2 : ℕ) with hY
  have hP1 : (⨆ n : ℕ, eLpNorm (u n) 2 (Work.KMTPlan.A6.zmodProb Q)) ≤ Y ^ (1 / 2 : ℝ) :=
    iSup_le fun n => eLpNorm_le_sum_variationalNorm u n
  have hP2 : (⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
      ENNReal.rpow (∑ i : Fin J, ENNReal.rpow (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2
          (Work.KMTPlan.A6.zmodProb Q)) 2) (1 / 2)) ≤ Y ^ (1 / 2 : ℝ) := by
    refine iSup_le fun J => iSup_le fun k => iSup_le fun hk => ?_
    have hsum : (∑ i : Fin J, ENNReal.rpow (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2
        (Work.KMTPlan.A6.zmodProb Q)) 2)
        = ∑ i : Fin J, (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2
            (Work.KMTPlan.A6.zmodProb Q)) ^ (2 : ℕ) :=
      Finset.sum_congr rfl fun i _ => ENNReal.rpow_natCast _ 2
    rw [hsum]
    exact rpow_sum_eLpNorm_le_sum_variationalNorm u J k hk
  calc Work.KMTPlan.A6.VrLiftDataP (2 : ℝ) Q u
      = (⨆ n : ℕ, eLpNorm (u n) 2 (Work.KMTPlan.A6.zmodProb Q))
        + (⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
            ENNReal.rpow (∑ i : Fin J, ENNReal.rpow (eLpNorm (u (k i.succ) - u (k i.castSucc)) 2
                (Work.KMTPlan.A6.zmodProb Q)) 2) (1 / 2)) := rfl
    _ ≤ Y ^ (1 / 2 : ℝ) + Y ^ (1 / 2 : ℝ) := add_le_add hP1 hP2
    _ = 2 * Y ^ (1 / 2 : ℝ) := by rw [two_mul]

/-- **Step 2, vector-valued (squared form).** -/
theorem VrLiftDataP_two_sq_le {Q : ℕ} [NeZero Q] (u : ℕ → ZMod Q → ℂ) :
    (Work.KMTPlan.A6.VrLiftDataP (2 : ℝ) Q u) ^ (2 : ℕ)
      ≤ 4 * ((Q : ENNReal)⁻¹ * ∑ θ : ZMod Q,
          (PointwiseErgodicTheorems.variationalNorm 2 (fun n => u n θ)) ^ (2 : ℕ)) := by
  set Y : ENNReal := (Q : ENNReal)⁻¹ * ∑ θ : ZMod Q,
    (PointwiseErgodicTheorems.variationalNorm 2 (fun n => u n θ)) ^ (2 : ℕ) with hY
  have h := VrLiftDataP_two_le u
  have hs : Y ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ) = Y := by
    rw [← pow_two, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      show ((1 / 2 : ℝ) * ((2 : ℕ) : ℝ)) = 1 from by norm_num, ENNReal.rpow_one]
  calc (Work.KMTPlan.A6.VrLiftDataP (2 : ℝ) Q u) ^ (2 : ℕ)
      = Work.KMTPlan.A6.VrLiftDataP (2 : ℝ) Q u * Work.KMTPlan.A6.VrLiftDataP (2 : ℝ) Q u := by
        rw [pow_two]
    _ ≤ (2 * Y ^ (1 / 2 : ℝ)) * (2 * Y ^ (1 / 2 : ℝ)) := mul_le_mul' h h
    _ = 4 * Y := by rw [show (2 : ENNReal) * Y ^ (1 / 2 : ℝ) * (2 * Y ^ (1 / 2 : ℝ))
          = 2 * 2 * (Y ^ (1 / 2 : ℝ) * Y ^ (1 / 2 : ℝ)) by ring, hs]; norm_num

end Work.KMTPlan.A6Clean
