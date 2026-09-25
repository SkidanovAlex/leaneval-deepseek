import Mathlib
import Submission.Work.BourgainPlan.Maximal.mstFreezeDefs
import Submission.Work.BourgainPlan.Maximal.eLpNorm_two_opMul_le
import Submission.Work.BourgainPlan.Maximal.level_l2_mst_small_n

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal
open Work.BourgainPlan.IonescuWainger

set_option maxHeartbeats 1000000

noncomputable section

/-- The `e`-norm of a complex number is the `ofReal` of its norm. -/
lemma enorm_eq_ofReal_norm (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ENNReal.ofReal_eq_coe_nnreal (norm_nonneg z)]
  congr 1

/-- **Triangle inequality for a finite sum of single multipliers with bounded symbols.**  If the
symbols `Φ β` are all bounded by `b ≥ 0` almost everywhere, then
`eLpNorm (Σ β∈E, (G β) • Op_{Φ β} f) 2 ≤ ofReal((Σ β∈E ‖G β‖) * b) · eLpNorm f 2`. -/
private lemma eLpNorm_sum_arcs_le {ι : Type*} [DecidableEq ι] (E : Finset ι) (G : ι → ℂ)
    (Φ : ι → MeasureTheory.Lp ℂ ⊤ mstHaar) (f : ℤ → ℂ) (hf : Memℓp f 2) {b : ℝ} (hb : 0 ≤ b)
    (hsym : ∀ β ∈ E, ∀ᵐ ξ ∂mstHaar, ‖(Φ β : mstCirc → ℂ) ξ‖ ≤ b) :
    MeasureTheory.eLpNorm (∑ β ∈ E, (G β) • opMul (Φ β) f hf) (ENNReal.ofReal 2)
        MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((∑ β ∈ E, ‖G β‖) * b)
        * MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
  calc
    MeasureTheory.eLpNorm (∑ β ∈ E, (G β) • opMul (Φ β) f hf) (ENNReal.ofReal 2)
        MeasureTheory.Measure.count
      ≤ ∑ β ∈ E, MeasureTheory.eLpNorm ((G β) • opMul (Φ β) f hf) (ENNReal.ofReal 2)
          MeasureTheory.Measure.count :=
        MeasureTheory.eLpNorm_sum_le (by norm_num)
    _ = ∑ β ∈ E, ‖G β‖ₑ * MeasureTheory.eLpNorm (opMul (Φ β) f hf) (ENNReal.ofReal 2)
          MeasureTheory.Measure.count := by
        refine Finset.sum_congr rfl (fun β _ => ?_)
        rw [MeasureTheory.eLpNorm_const_smul]
    _ ≤ ∑ β ∈ E, ‖G β‖ₑ * (ENNReal.ofReal b
          * MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count) := by
        refine Finset.sum_le_sum (fun β hβ => mul_le_mul_right ?_ _)
        exact eLpNorm_two_opMul_le hf hb (hsym β hβ)
    _ = ∑ β ∈ E, ENNReal.ofReal (‖G β‖ * b)
          * MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
        refine Finset.sum_congr rfl (fun β _ => ?_)
        rw [enorm_eq_ofReal_norm, ← mul_assoc, ← ENNReal.ofReal_mul (norm_nonneg (G β))]
    _ = (∑ β ∈ E, ENNReal.ofReal (‖G β‖ * b))
          * MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
        rw [Finset.sum_mul]
    _ = ENNReal.ofReal (∑ β ∈ E, ‖G β‖ * b)
          * MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun β _ => mul_nonneg (norm_nonneg (G β)) hb)]
    _ = ENNReal.ofReal ((∑ β ∈ E, ‖G β‖) * b)
          * MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count := by
        rw [← Finset.sum_mul E (fun β => ‖G β‖) b]

/-- **The per-`n` `ℓ²` bound for the freezing difference.**  If, for a given scale `n`, the freezing difference `D n` is the sum over the arcs `β ∈ mstLvl l s` of the single multipliers with symbol `mstFreezeSymFun … β` weighted by `G β` (the hypothesis `hident`, supplied by `mstFreeze_diff_eq`), and if all these symbols are bounded by `b ≥ 0` (`hsym`), then
`∫⁻_x ‖D n x‖ₑ² ∂count ≤ ofReal((Σ_{β∈E}‖G β‖ · b)²) · ∫⁻_m ‖f m‖ₑ² ∂count`.
Route: rewrite `D n x` as `(∑ β ∈ E, (G β) • (fun x => opMul (mstFreezeSymLp … β) f hf x)) x`, then `eLpNorm_sum_le` (`eLpNorm (fun x => ∑ β∈E, …) (ofReal 2) count ≤ ∑ β∈E, eLpNorm (…)`; measurability of each summand is free for `Measure.count` on `ℤ`), `eLpNorm_const_smul` (giving `‖G β‖ₑ · …`), the symbol bound `eLpNorm_two_opMul_le` (`Work.BourgainPlan.Maximal.eLpNorm_two_opMul_le`, with the a.e. bound on the class `mstFreezeSymLp` supplied by `hsym` + `mstFreezeSymLp_coeFn`), and finally pass from `eLpNorm`-squares to `lintegral`s with `eLpNorm_two_sq` (`Work.BourgainPlan.Maximal.eLpNorm_two_sq`, in `level_l2_mst_small_n.lean`) together with `ENNReal.ofReal_mul`/`ENNReal.ofReal_sum_of_nonneg`. -/
theorem mstFreeze_per_n_sq (P : Polynomial ℤ) (l d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (hη : Continuous η)
    (s n u : ℕ) (G : Work.BourgainPlan.IonescuWainger.Circle → ℂ) (f : ℤ → ℂ) (hf : Memℓp f 2)
    (hB : ∀ n : ℕ, MeasureTheory.Lp ℂ ⊤ Work.BourgainPlan.Maximal.mstHaar)
    {b : ℝ} (hb : 0 ≤ b)
    (hsym : ∀ (β ξ : Work.BourgainPlan.IonescuWainger.Circle),
      ‖Work.BourgainPlan.Maximal.mstFreezeSymFun P d χ η s n u β ξ‖ ≤ b)
    (hident : ∀ x : ℤ,
      Work.BourgainPlan.IonescuWainger.opMul (hB n)
          (Work.BourgainPlan.Maximal.mstModSeq G (Work.BourgainPlan.Maximal.mstLvl l s) f x)
          (Work.BourgainPlan.Maximal.memℒp_mstModSeq hf x) (x + (u : ℤ))
        - Work.BourgainPlan.IonescuWainger.opMul (hB n)
          (Work.BourgainPlan.Maximal.mstModSeq G (Work.BourgainPlan.Maximal.mstLvl l s) f x)
          (Work.BourgainPlan.Maximal.memℒp_mstModSeq hf x) x
        = Finset.sum (Work.BourgainPlan.Maximal.mstLvl l s) (fun β =>
            G β * Work.BourgainPlan.IonescuWainger.opMul
              (Work.BourgainPlan.Maximal.mstFreezeSymLp P d χ η hη s n u β) f hf x)) :
    MeasureTheory.lintegral MeasureTheory.Measure.count (fun x : ℤ =>
        ‖Work.BourgainPlan.IonescuWainger.opMul (hB n)
            (Work.BourgainPlan.Maximal.mstModSeq G (Work.BourgainPlan.Maximal.mstLvl l s) f x)
            (Work.BourgainPlan.Maximal.memℒp_mstModSeq hf x) (x + (u : ℤ))
          - Work.BourgainPlan.IonescuWainger.opMul (hB n)
            (Work.BourgainPlan.Maximal.mstModSeq G (Work.BourgainPlan.Maximal.mstLvl l s) f x)
            (Work.BourgainPlan.Maximal.memℒp_mstModSeq hf x) x‖ₑ ^ (2 : ℝ))
      ≤ ENNReal.ofReal
          ((Finset.sum (Work.BourgainPlan.Maximal.mstLvl l s) (fun β => ‖G β‖) * b) ^ 2)
        * MeasureTheory.lintegral MeasureTheory.Measure.count (fun m : ℤ => ‖f m‖ₑ ^ (2 : ℝ)) := by
  classical
  -- (1) the freezing difference really is the frozen sum
  have hpt : ∀ x : ℤ,
      (∑ β ∈ mstLvl l s, (G β) • opMul (mstFreezeSymLp P d χ η hη s n u β) f hf) x
        = opMul (hB n) (mstModSeq G (mstLvl l s) f x) (memℒp_mstModSeq hf x) (x + (u : ℤ))
          - opMul (hB n) (mstModSeq G (mstLvl l s) f x) (memℒp_mstModSeq hf x) x := by
    intro x
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (hident x).symm
  -- (2) the symbols `mstFreezeSymLp … β` are a.e. bounded by `b`
  have hsym' : ∀ β ∈ mstLvl l s, ∀ᵐ ξ ∂mstHaar,
      ‖(mstFreezeSymLp P d χ η hη s n u β : mstCirc → ℂ) ξ‖ ≤ b := by
    intro β _
    filter_upwards [mstFreezeSymLp_coeFn P d χ η hη s n u β] with ξ hξ
    rw [hξ]
    exact hsym β ξ
  -- (3) the `eLpNorm` bound for the frozen sum
  have hsum_lp : MeasureTheory.eLpNorm
        (∑ β ∈ mstLvl l s, (G β) • opMul (mstFreezeSymLp P d χ η hη s n u β) f hf)
        (ENNReal.ofReal 2) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((∑ β ∈ mstLvl l s, ‖G β‖) * b)
        * MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count :=
    eLpNorm_sum_arcs_le (mstLvl l s) G
      (fun β => mstFreezeSymLp P d χ η hη s n u β) f hf hb hsym'
  -- (4) square the `eLpNorm` bound and convert squares to `lintegral`s
  have hmain : (MeasureTheory.eLpNorm
        (∑ β ∈ mstLvl l s, (G β) • opMul (mstFreezeSymLp P d χ η hη s n u β) f hf)
        (ENNReal.ofReal 2) MeasureTheory.Measure.count) ^ 2
      ≤ ENNReal.ofReal (((∑ β ∈ mstLvl l s, ‖G β‖) * b) ^ 2)
        * ∫⁻ m : ℤ, ‖f m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
    calc
      (MeasureTheory.eLpNorm
          (∑ β ∈ mstLvl l s, (G β) • opMul (mstFreezeSymLp P d χ η hη s n u β) f hf)
          (ENNReal.ofReal 2) MeasureTheory.Measure.count) ^ 2
        ≤ (ENNReal.ofReal ((∑ β ∈ mstLvl l s, ‖G β‖) * b)
            * MeasureTheory.eLpNorm f (ENNReal.ofReal 2) MeasureTheory.Measure.count) ^ 2 :=
          pow_le_pow_left₀ (by positivity) hsum_lp 2
      _ = ENNReal.ofReal (((∑ β ∈ mstLvl l s, ‖G β‖) * b) ^ 2)
            * ∫⁻ m : ℤ, ‖f m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := by
          rw [mul_pow, ← ENNReal.ofReal_pow (mul_nonneg (Finset.sum_nonneg
              (fun β _ => norm_nonneg (G β))) hb), eLpNorm_two_sq f]
  -- (5) assemble
  calc
    MeasureTheory.lintegral MeasureTheory.Measure.count (fun x : ℤ =>
        ‖opMul (hB n) (mstModSeq G (mstLvl l s) f x) (memℒp_mstModSeq hf x) (x + (u : ℤ))
          - opMul (hB n) (mstModSeq G (mstLvl l s) f x) (memℒp_mstModSeq hf x) x‖ₑ ^ (2 : ℝ))
      = MeasureTheory.lintegral MeasureTheory.Measure.count (fun x : ℤ =>
          ‖(∑ β ∈ mstLvl l s, (G β) • opMul (mstFreezeSymLp P d χ η hη s n u β) f hf) x‖ₑ
            ^ (2 : ℝ)) := by
        refine MeasureTheory.lintegral_congr (fun x => ?_)
        rw [hpt x]
    _ = (MeasureTheory.eLpNorm
          (∑ β ∈ mstLvl l s, (G β) • opMul (mstFreezeSymLp P d χ η hη s n u β) f hf)
          (ENNReal.ofReal 2) MeasureTheory.Measure.count) ^ 2 :=
        (eLpNorm_two_sq (∑ β ∈ mstLvl l s,
          (G β) • opMul (mstFreezeSymLp P d χ η hη s n u β) f hf)).symm
    _ ≤ ENNReal.ofReal (((∑ β ∈ mstLvl l s, ‖G β‖) * b) ^ 2)
          * ∫⁻ m : ℤ, ‖f m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count := hmain

end

end Work.BourgainPlan.Maximal
