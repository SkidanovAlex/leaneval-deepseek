import Mathlib
import Submission.Work.TMC16Core.Defs

open scoped ENNReal
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMC16Core.Op

/-- Reindexing `n ↦ n + k` preserves `ℓ²(ℤ)`: the shift is a bijection of the index
set, hence the square-summability of `‖·‖ ^ 2` is unchanged. -/
lemma memℓp_shift (f : EllTwo) (k : ℤ) : Memℓp (fun n : ℤ => f (n + k)) 2 := by
  have hf : Summable (fun n : ℤ => ‖f n‖ ^ ((2 : ℝ≥0∞).toReal)) :=
    (lp.memℓp f).summable (by norm_num)
  apply memℓp_gen
  have h := (Equiv.summable_iff (Equiv.addRight k)).2 hf
  simpa only [Function.comp_def, Equiv.coe_addRight] using h

theorem diagShift_spec (c : ℤ → ℂ) (k : ℤ) (K : ℝ) (hK : ∀ n, ‖c n‖ ≤ K) :
    ∃ T : LeanEval.Analysis.TenMartini.EllTwo →L[ℂ] LeanEval.Analysis.TenMartini.EllTwo,
      (∀ f n, T f n = c n * f (n + k)) ∧ ‖T‖ ≤ K := by
  have hK0 : 0 ≤ K := le_trans (norm_nonneg _) (hK 0)
  -- Membership of the image sequence in `ℓ²`.
  have hmem : ∀ f : EllTwo, Memℓp (fun n : ℤ => c n * f (n + k)) 2 := by
    intro f
    have hKshift : Memℓp (fun n : ℤ => K * ‖f (n + k)‖) 2 :=
      (memℓp_shift f k).norm.const_mul K
    refine Memℓp.mono hKshift (fun n => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hK n) (norm_nonneg _)
  -- The underlying linear map.
  let L : EllTwo →ₗ[ℂ] EllTwo :=
    { toFun := fun f => ⟨fun n => c n * f (n + k), hmem f⟩
      map_add' := fun f g => by
        apply lp.ext; funext n; simp only [lp.coeFn_add, Pi.add_apply, mul_add]
      map_smul' := fun a f => by
        apply lp.ext; funext n
        simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  -- The operator norm bound `‖L‖ ≤ K`, via the `ℓ²` norm written as a sum of squares.
  have hbound : ∀ f : EllTwo, ‖L f‖ ≤ K * ‖f‖ := by
    intro f
    have hs : Summable (fun n : ℤ => ‖f (n + k)‖ ^ ((2 : ℝ≥0∞).toReal)) :=
      (memℓp_shift f k).summable (by norm_num)
    have hshiftnorm :
        ∑' n : ℤ, ‖f (n + k)‖ ^ ((2 : ℝ≥0∞).toReal) = ‖f‖ ^ ((2 : ℝ≥0∞).toReal) := by
      rw [show (∑' n : ℤ, ‖f (n + k)‖ ^ ((2 : ℝ≥0∞).toReal))
            = ∑' n : ℤ, ‖f n‖ ^ ((2 : ℝ≥0∞).toReal) from by
            simpa only [Equiv.coe_addRight] using
              (Equiv.tsum_eq (Equiv.addRight k) (fun i : ℤ => ‖f i‖ ^ ((2 : ℝ≥0∞).toReal)))]
      exact (lp.norm_rpow_eq_tsum (by norm_num) f).symm
    rw [show L f = ⟨fun n => c n * f (n + k), hmem f⟩ from rfl]
    have hpt : ∀ n : ℤ, ‖c n * f (n + k)‖ ^ ((2 : ℝ≥0∞).toReal)
        ≤ K ^ ((2 : ℝ≥0∞).toReal) * ‖f (n + k)‖ ^ ((2 : ℝ≥0∞).toReal) := by
      intro n
      have hle : ‖c n * f (n + k)‖ ≤ K * ‖f (n + k)‖ := by
        rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hK n) (norm_nonneg _)
      calc ‖c n * f (n + k)‖ ^ ((2 : ℝ≥0∞).toReal)
          ≤ (K * ‖f (n + k)‖) ^ ((2 : ℝ≥0∞).toReal) :=
            Real.rpow_le_rpow (by positivity) hle (by norm_num)
        _ = K ^ ((2 : ℝ≥0∞).toReal) * ‖f (n + k)‖ ^ ((2 : ℝ≥0∞).toReal) :=
            Real.mul_rpow hK0 (norm_nonneg _)
    have hS2 : Summable
        (fun n : ℤ => K ^ ((2 : ℝ≥0∞).toReal) * ‖f (n + k)‖ ^ ((2 : ℝ≥0∞).toReal)) :=
      hs.mul_left _
    have hS1 : Summable (fun n : ℤ => ‖c n * f (n + k)‖ ^ ((2 : ℝ≥0∞).toReal)) :=
      Summable.of_nonneg_of_le (fun n => by positivity) hpt hS2
    have hmain : ∑' n : ℤ, ‖c n * f (n + k)‖ ^ ((2 : ℝ≥0∞).toReal)
        ≤ (K * ‖f‖) ^ ((2 : ℝ≥0∞).toReal) := by
      calc ∑' n : ℤ, ‖c n * f (n + k)‖ ^ ((2 : ℝ≥0∞).toReal)
          ≤ ∑' n : ℤ, K ^ ((2 : ℝ≥0∞).toReal) * ‖f (n + k)‖ ^ ((2 : ℝ≥0∞).toReal) :=
            Summable.tsum_le_tsum hpt hS1 hS2
        _ = K ^ ((2 : ℝ≥0∞).toReal) * ∑' n : ℤ, ‖f (n + k)‖ ^ ((2 : ℝ≥0∞).toReal) :=
            tsum_mul_left
        _ = K ^ ((2 : ℝ≥0∞).toReal) * ‖f‖ ^ ((2 : ℝ≥0∞).toReal) := by rw [hshiftnorm]
        _ = (K * ‖f‖) ^ ((2 : ℝ≥0∞).toReal) := (Real.mul_rpow hK0 (norm_nonneg f)).symm
    exact lp.norm_le_of_tsum_le (by norm_num) (mul_nonneg hK0 (norm_nonneg _)) hmain
  refine ⟨L.mkContinuous K hbound, ?_, ?_⟩
  · intro f n
    rw [LinearMap.mkContinuous_apply]
    rfl
  · exact LinearMap.mkContinuous_norm_le L hK0 hbound

end Work.TMC16Core.Op
