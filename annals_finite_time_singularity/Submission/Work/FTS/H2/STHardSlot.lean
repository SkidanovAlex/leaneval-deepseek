/-
Copyright: work module for the Elgindi finite-time singularity project.

# The per-slot bound of the "hard" part of `SpecialTransport`

Combining the angular integration by parts of `STIbp.ibp_partial` with the pointwise bounds
`|f| ≤ K·sin(2θ)`, `|∂_θf| ≤ 3K`, `|v| ≤ C·sin(2θ)` gives, for a single `g`-slot
`(v, q)` of the hard part of the `SpecialTransport` pairing,

  `|∫_θ sin(2θ)^{-q}·f·∂_θv·v| ≤ (qK + 3K/2)·∫_θ sin(2θ)^{-q}·v²`.

The two exponent facts used throughout (both *before* any `ring`, per the handoff):

* `sin(2θ)^{-q-1}·sin(2θ) = sin(2θ)^{-q}`  (`rpow_neg_sub_one_mul`);
* `sin(2θ)^{-q}·sin(2θ)³ = sin(2θ)^{3-q}`   (`rpow_neg_mul_cube`).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.STIbp

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The two exponent identities -/

theorem rpow_neg_sub_one_mul (q : ℝ) {s : ℝ} (hs : 0 < s) :
    s ^ (-q - 1) * s = s ^ (-q) := by
  have h2 : s ^ (-q) = s ^ (-q - 1) * s ^ (1 : ℝ) := by
    rw [← Real.rpow_add hs]; ring_nf
  rw [h2, Real.rpow_one]

theorem rpow_neg_mul_cube (q : ℝ) {s : ℝ} (hs : 0 < s) :
    s ^ (-q) * s ^ 3 = s ^ (3 - q) := by
  rw [← Real.rpow_natCast s 3, ← Real.rpow_add hs]
  ring_nf

/-! ## The pointwise bound on the coefficient produced by the integration by parts -/

theorem hard_slot_coef {q K : ℝ} (hq0 : 0 < q) (hK : 0 ≤ K) {f : ℝ → ℝ → ℝ} {z : ℝ}
    (hf1 : ∀ θ ∈ Spaces.Iθ, |f z θ| ≤ K * Real.sin (2 * θ))
    (hf2 : ∀ θ ∈ Spaces.Iθ, |Spaces.pth f z θ| ≤ 3 * K) :
    ∀ θ ∈ Spaces.Iθ, |q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ
        - (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Spaces.pth f z θ|
      ≤ (q * K + 3 * K / 2) * (Real.sin (2 * θ)) ^ (-q) := by
  intro θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  rcases eq_or_lt_of_le hs0 with hs | hs
  · rw [← hs]
    rw [Real.zero_rpow (x := -q - 1) (by linarith), Real.zero_rpow (x := -q) (by linarith)]
    simp
  · have hcos : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one (2 * θ)
    have h1 : |q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ|
        ≤ q * K * (Real.sin (2 * θ)) ^ (-q) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0 _),
        abs_of_pos hq0]
      calc q * |Real.cos (2 * θ)| * (Real.sin (2 * θ)) ^ (-q - 1) * |f z θ|
          ≤ q * 1 * (Real.sin (2 * θ)) ^ (-q - 1) * (K * Real.sin (2 * θ)) := by
            gcongr
            · exact hf1 θ hθ
        _ = q * (K * ((Real.sin (2 * θ)) ^ (-q - 1) * Real.sin (2 * θ))) := by ring
        _ = q * (K * (Real.sin (2 * θ)) ^ (-q)) := by rw [rpow_neg_sub_one_mul q hs]
        _ = q * K * (Real.sin (2 * θ)) ^ (-q) := by ring
    have h2 : |(1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Spaces.pth f z θ|
        ≤ (3 * K / 2) * (Real.sin (2 * θ)) ^ (-q) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
        abs_of_nonneg (Real.rpow_nonneg hs0 _)]
      calc (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * |Spaces.pth f z θ|
          ≤ (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * (3 * K) := by
            gcongr
            · exact hf2 θ hθ
        _ = (3 * K / 2) * (Real.sin (2 * θ)) ^ (-q) := by ring
    calc |q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ
          - (1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Spaces.pth f z θ|
        ≤ |q * Real.cos (2 * θ) * (Real.sin (2 * θ)) ^ (-q - 1) * f z θ|
          + |(1 / 2) * (Real.sin (2 * θ)) ^ (-q) * Spaces.pth f z θ| :=
          abs_sub_le_abs_add _ _
      _ ≤ q * K * (Real.sin (2 * θ)) ^ (-q) + (3 * K / 2) * (Real.sin (2 * θ)) ^ (-q) :=
          add_le_add h1 h2
      _ = (q * K + 3 * K / 2) * (Real.sin (2 * θ)) ^ (-q) := by ring

/-! ## The boundary vanishing -/

theorem hard_slot_van {q K C : ℝ} (hq0 : 0 < q) (hq3 : q < 3) (hK : 0 ≤ K) (hC : 0 ≤ C)
    {f v : ℝ → ℝ → ℝ} {z : ℝ}
    (hf1 : ∀ θ ∈ Spaces.Iθ, |f z θ| ≤ K * Real.sin (2 * θ))
    (hv1 : ∀ θ ∈ Spaces.Iθ, |v z θ| ≤ C * Real.sin (2 * θ)) :
    ∀ θ ∈ Spaces.Iθ, |(Real.sin (2 * θ)) ^ (-q) * f z θ * (v z θ) ^ 2| ≤
      K * C ^ 2 * (Real.sin (2 * θ)) ^ (3 - q) := by
  intro θ hθ
  have hs0 : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  rcases eq_or_lt_of_le hs0 with hs | hs
  · rw [← hs]
    rw [Real.zero_rpow (x := -q) (by linarith), Real.zero_rpow (x := 3 - q) (by linarith)]
    simp
  · have h1 : |(Real.sin (2 * θ)) ^ (-q)| = (Real.sin (2 * θ)) ^ (-q) :=
      abs_of_nonneg (Real.rpow_nonneg hs0 _)
    have h2 : |(v z θ) ^ 2| = |v z θ| ^ 2 := by rw [abs_sq, sq_abs]
    rw [abs_mul, abs_mul, h1, h2]
    calc (Real.sin (2 * θ)) ^ (-q) * |f z θ| * |v z θ| ^ 2
        ≤ (Real.sin (2 * θ)) ^ (-q) * (K * Real.sin (2 * θ))
            * (C * Real.sin (2 * θ)) ^ 2 := by
          gcongr
          · exact hf1 θ hθ
          · exact hv1 θ hθ
      _ = K * C ^ 2 * ((Real.sin (2 * θ)) ^ (-q) * Real.sin (2 * θ) ^ 3) := by ring
      _ = K * C ^ 2 * (Real.sin (2 * θ)) ^ (3 - q) := by
          rw [rpow_neg_mul_cube q hs]

end Work.FTS.H2
