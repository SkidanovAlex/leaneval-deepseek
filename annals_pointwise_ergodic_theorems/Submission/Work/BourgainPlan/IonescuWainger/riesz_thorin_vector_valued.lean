import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.vector_valued_lp_interpolation
import Submission.Work.BourgainPlan.IonescuWainger.riesz_thorin_vec_core
import Submission.Work.BourgainPlan.IonescuWainger.mLp_dual_witness
import Submission.Work.BourgainPlan.IonescuWainger.normalize_lp

open scoped BigOperators

set_option maxHeartbeats 4000000

namespace Work.BourgainPlan.IonescuWainger

/-- **Riesz–Thorin (complex interpolation) for a linear operator between `ℓ^p` spaces, with
values in a finite-dimensional Hilbert space `ℂ^ι` (square-summable norm), including the `L^∞`
endpoint.**  For finite types `α, β, ι`, a `ℂ`-linear `T : (α → ℂ) → (β → ι → ℂ)`, and `2 ≤ p`:
if `T` is bounded with norm `≤ A` from `ℓ²(α)` to `L²(β; ℓ²(ι))`, and with norm `≤ B` from
`ℓ^∞(α)` to `L^∞(β; ℓ²(ι))` (sup of the `ℓ²`-norms — the `L^∞` of the vector-valued function),
then it is bounded on `ℓ^p` with norm `≤ A ^ (2 / p) * B ^ (1 - 2 / p)`.

This is the vector-valued version of `Commons.Analysis.Integral.riesz_thorin_finite` (on disk; its
proof is the template: the interpolation vector `φ ↦ ‖φ a‖ ^ (t z) • ph (φ a)` becomes
`φ ↦ ‖φ b‖₂ ^ (t z) • (‖φ b‖₂)⁻¹ • φ b`, element-wise in `ι`, so each `b`-component stays analytic
in `z` and its `ℓ²`-norm is `‖φ b‖ ^ (Re (t z))`; the three-lines tool is
`Commons.Analysis.Complex.hadamard_three_lines`).  The `L^∞` endpoint is the one the scalar
`riesz_thorin_finite` cannot state (its exponents are reals), but no limiting argument is needed:
the endpoint hypothesis is *by definition* the sup-norm of the target, and the Hadamard three-lines
result only ever evaluates the endpoint hypotheses.

Consequences: this is exactly the "interpolation" step of Tao's `ortho-apply`(ii)
(arXiv:2008.05066) and of the `(L²(ℓ²), L^∞(ℓ²)) ⟹ L^p(ℓ²)` step of `vector_valued_lp_interpolation`
— but in the *operator* form (different source and target types), which is what is needed when the
`L^p` sum and the `ℓ²` index live on different sets. -/
theorem riesz_thorin_vector_valued {α β ι : Type*} [Fintype α] [Fintype β] [Fintype ι]
    {p : ℝ} (hp : 2 ≤ p) :
    ∀ (T : (α → ℂ) →ₗ[ℂ] (β → ι → ℂ)) (A B : ℝ), 0 ≤ A → 0 ≤ B →
      (∀ f : α → ℂ, (∑ b, ∑ i, ‖T f b i‖ ^ 2) ^ ((1 : ℝ) / 2)
        ≤ A * (∑ a, ‖f a‖ ^ 2) ^ ((1 : ℝ) / 2)) →
      (∀ f : α → ℂ, (⨆ b, (∑ i, ‖T f b i‖ ^ 2) ^ ((1 : ℝ) / 2))
        ≤ B * (⨆ a, ‖f a‖)) →
      ∀ f : α → ℂ, (∑ b, (∑ i, ‖T f b i‖ ^ 2) ^ (p / 2)) ^ (1 / p)
        ≤ A ^ (2 / p) * B ^ (1 - 2 / p) * (∑ a, ‖f a‖ ^ p) ^ (1 / p) := by
  intro T A B hA hB hT0 hT1 f
  have hp0 : 0 < p := by linarith
  -- the `L^∞`-hypothesis, rewritten with the fibre `ℓ²`-norm `n2`
  have hT1n : ∀ g : α → ℂ, (⨆ b, n2 (T g b)) ≤ B * (⨆ a, ‖g a‖) := fun g => by
    simpa only [n2_eq_rpow] using hT1 g
  rcases lt_or_eq_of_le hp with hpgt | hpeq
  · -- `2 < p`
    have h1p : 1 < p := by linarith
    have h2p : (0 : ℝ) < 2 / p := div_pos (by norm_num) hp0
    have h12p : (1 : ℝ) - 2 / p ≠ 0 := by
      have h := (div_lt_one hp0).mpr hpgt
      exact ne_of_gt (by linarith)
    rcases eq_or_lt_of_le hA with hA0 | hApos
    · -- `A = 0`: then `T = 0`
      have hzero : ∀ b i, T f b i = 0 := by
        have h1 : (∑ b, ∑ i, ‖T f b i‖ ^ 2) ^ ((1 : ℝ) / 2) ≤ 0 := by
          have h := hT0 f
          rw [← hA0, zero_mul] at h
          exact h
        have hnn : 0 ≤ ∑ b, ∑ i, ‖T f b i‖ ^ 2 :=
          Finset.sum_nonneg fun b _ => Finset.sum_nonneg fun i _ => sq_nonneg _
        have h2 : (∑ b, ∑ i, ‖T f b i‖ ^ 2) = 0 := by
          have h3 : Real.sqrt (∑ b, ∑ i, ‖T f b i‖ ^ 2) = 0 := by
            rw [Real.sqrt_eq_rpow]
            exact le_antisymm h1 (Real.rpow_nonneg hnn _)
          calc ∑ b, ∑ i, ‖T f b i‖ ^ 2 = (Real.sqrt (∑ b, ∑ i, ‖T f b i‖ ^ 2)) ^ 2 :=
                (Real.sq_sqrt hnn).symm
            _ = 0 := by rw [h3]; ring
        have hb : ∀ b, ∑ i, ‖T f b i‖ ^ 2 = 0 := fun b =>
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun b _ => Finset.sum_nonneg fun i _ => sq_nonneg _)).mp h2 b (Finset.mem_univ b)
        intro b i
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => sq_nonneg _)).mp (hb b) i (Finset.mem_univ i)))
      rw [lp_vector_zero hp0 (T f) hzero, ← hA0,
        Real.zero_rpow (div_ne_zero (by norm_num) (ne_of_gt hp0)), zero_mul, zero_mul]
    rcases eq_or_lt_of_le hB with hB0 | hBpos
    · -- `B = 0`: then `T = 0`
      have hzero : ∀ b i, T f b i = 0 := by
        have hfib : ∀ b, (∑ i, ‖T f b i‖ ^ 2) ^ ((1 : ℝ) / 2) = 0 := by
          intro b
          have hle : (∑ i, ‖T f b i‖ ^ 2) ^ ((1 : ℝ) / 2)
              ≤ (⨆ b, (∑ i, ‖T f b i‖ ^ 2) ^ ((1 : ℝ) / 2)) :=
            le_ciSup (f := fun b => (∑ i, ‖T f b i‖ ^ 2) ^ ((1 : ℝ) / 2))
              (Set.finite_range _).bddAbove b
          have h0 : (⨆ b, (∑ i, ‖T f b i‖ ^ 2) ^ ((1 : ℝ) / 2)) ≤ 0 := by
            have h := hT1 f
            rw [← hB0, zero_mul] at h
            exact h
          exact le_antisymm (le_trans hle h0)
            (Real.rpow_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) _)
        intro b i
        have hsq : (∑ i, ‖T f b i‖ ^ 2) = 0 := by
          calc ∑ i, ‖T f b i‖ ^ 2 = (Real.sqrt (∑ i, ‖T f b i‖ ^ 2)) ^ 2 :=
                (Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)).symm
            _ = 0 := by rw [Real.sqrt_eq_rpow, hfib b]; ring
        exact norm_eq_zero.mp (sq_eq_zero_iff.mp ((Finset.sum_eq_zero_iff_of_nonneg
          (fun i _ => sq_nonneg _)).mp hsq i (Finset.mem_univ i)))
      rw [lp_vector_zero hp0 (T f) hzero, ← hB0, Real.zero_rpow h12p, mul_zero, zero_mul]
    by_cases hf0 : (∑ a, ‖f a‖ ^ p) = 0
    · -- `f = 0`
      have hL : (∑ b, (∑ i, ‖T f b i‖ ^ 2) ^ (p / 2)) ^ (1 / p) = 0 := by
        have hfzero : f = 0 := by
          funext a
          have hle : ‖f a‖ ^ p ≤ ∑ a, ‖f a‖ ^ p :=
            Finset.single_le_sum (fun a _ => Real.rpow_nonneg (norm_nonneg _) p) (Finset.mem_univ a)
          have hz : ‖f a‖ ^ p = 0 := by
            rw [hf0] at hle
            exact le_antisymm hle (Real.rpow_nonneg (norm_nonneg _) p)
          by_contra hc
          exact absurd hz (ne_of_gt (Real.rpow_pos_of_pos (norm_pos_iff.mpr hc) p))
        refine lp_vector_zero hp0 (T f) fun b i => ?_
        rw [hfzero, map_zero]
        rfl
      rw [hL]
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _))
        (Real.rpow_nonneg (Finset.sum_nonneg fun a _ => Real.rpow_nonneg (norm_nonneg _) p) _)
    · -- main case
      have hfpos : 0 < ∑ a, ‖f a‖ ^ p :=
        lt_of_le_of_ne (Finset.sum_nonneg fun a _ => Real.rpow_nonneg (norm_nonneg _) p)
          (Ne.symm hf0)
      set S : ℝ := (∑ a, ‖f a‖ ^ p) ^ (1 / p) with hS
      have hSpos : 0 < S := Real.rpow_pos_of_pos hfpos _
      have hSne : ((S : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hSpos)
      set f' : α → ℂ := fun a => (((S : ℝ)) : ℂ)⁻¹ * f a with hf'def
      have hf'norm : (∑ a, ‖f' a‖ ^ p) = 1 := by
        rw [hf'def, hS]
        exact normalize_lp hp0 f hfpos
      have hff : ((S : ℝ) : ℂ) • f' = f := by
        funext a
        simp only [hf'def, Pi.smul_apply, smul_eq_mul]
        rw [← mul_assoc, mul_inv_cancel₀ hSne, one_mul]
      have hscale : T f = ((S : ℝ) : ℂ) • T f' := by
        rw [← hff, map_smul]
      have hmain : mLp (T f') p ≤ A ^ (2 / p) * B ^ (1 - 2 / p) := by
        by_cases hTf' : T f' = 0
        · rw [hTf']
          have hzero : mLp (0 : β → ι → ℂ) p = 0 := by
            rw [mLp]
            have hsum : (∑ b, (n2 ((0 : β → ι → ℂ) b)) ^ p) = 0 := by
              refine Finset.sum_eq_zero fun b _ => ?_
              rw [Pi.zero_apply, n2_zero, Real.zero_rpow (ne_of_gt hp0)]
            rw [hsum, Real.zero_rpow (div_ne_zero one_ne_zero (ne_of_gt hp0))]
          rw [hzero]
          exact mul_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _)
        · obtain ⟨g, hg1, hg2⟩ := mLp_dual_witness h1p (T f')
          exact le_trans hg2 (riesz_thorin_vec_core T hpgt hApos hBpos hT0 hT1n f' g
            (le_of_eq hf'norm) hg1)
      calc (∑ b, (∑ i, ‖T f b i‖ ^ 2) ^ (p / 2)) ^ (1 / p)
          = mLp (T f) p := (mLp_eq_goal (T f) p).symm
        _ = mLp (((S : ℝ) : ℂ) • T f') p := by rw [hscale]
        _ = S * mLp (T f') p := by
            rw [mLp_smul _ _ hp0, Complex.norm_def, Complex.normSq_ofReal,
              Real.sqrt_mul_self hSpos.le]
        _ ≤ S * (A ^ (2 / p) * B ^ (1 - 2 / p)) := mul_le_mul_of_nonneg_left hmain hSpos.le
        _ = A ^ (2 / p) * B ^ (1 - 2 / p) * (∑ a, ‖f a‖ ^ p) ^ (1 / p) := by
            rw [hS]; ring
  · -- `p = 2`
    rw [← hpeq]
    have hL : ∀ b : β, (∑ i, ‖T f b i‖ ^ 2) ^ ((2 : ℝ) / 2) = ∑ i, ‖T f b i‖ ^ 2 := fun b => by
      rw [show ((2 : ℝ) / 2) = 1 by norm_num, Real.rpow_one]
    have hR : (∑ a, ‖f a‖ ^ (2 : ℝ)) = ∑ a, ‖f a‖ ^ 2 :=
      Finset.sum_congr rfl fun a _ => rpow_two_eq_sq (‖f a‖)
    have hA2 : A ^ ((2 : ℝ) / 2) = A := by
      rw [show ((2 : ℝ) / 2) = 1 by norm_num, Real.rpow_one]
    have hB2 : B ^ (1 - (2 : ℝ) / 2) = 1 := by
      rw [show 1 - (2 : ℝ) / 2 = 0 by norm_num, Real.rpow_zero]
    simp only [hL, hR, hA2, hB2, one_mul, mul_one]
    exact hT0 f


end Work.BourgainPlan.IonescuWainger
