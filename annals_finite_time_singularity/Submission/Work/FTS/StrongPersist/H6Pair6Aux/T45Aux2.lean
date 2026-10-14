import Mathlib.Algebra.Order.Chebyshev
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T45Aux
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.slotCS_z
import Submission.Work.FTS.StrongPersist.H6Rows.N0pair6Aux.radialMul6Cont
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-!
# `T45Aux2` — the `z`-weighted jet sum and the angular Cauchy–Schwarz

The binomial-weighted sum of the `L₁₂`-jets, its `w²`-weighted `L¹` bound (`SW_bound`), and
the square-root form of the Cauchy–Schwarz inequality on `Iθ` with nonnegativity only a.e.
-/

/-! ## The `z`-weighted sum of the `L₁₂`-jets -/

/-- The integrability of a finite sum of integrable functions. -/
theorem integrable_finset_sum_loc {ι : Type*} (s : Finset ι) {μ : Measure ℝ}
    {f : ι → ℝ → ℝ} (h : ∀ i ∈ s, Integrable (f i) μ) :
    Integrable (fun a => ∑ i ∈ s, f i a) μ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert b s hb ih =>
    have hstep : (fun a => ∑ i ∈ insert b s, f i a) = (fun a => f b a + ∑ i ∈ s, f i a) := by
      funext x; rw [Finset.sum_insert hb]
    rw [hstep]
    exact (h b (Finset.mem_insert_self b s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The a.e.-strong-measurability of a finite sum of a.e.-strongly-measurable functions. -/
theorem aesm_finset_sum_loc {ι : Type*} (s : Finset ι) {μ : Measure ℝ}
    {f : ι → ℝ → ℝ} (h : ∀ i ∈ s, AEStronglyMeasurable (f i) μ) :
    AEStronglyMeasurable (fun a => ∑ i ∈ s, f i a) μ := by
  classical
  induction s using Finset.induction with
  | empty => simpa using aestronglyMeasurable_const (b := (0 : ℝ)) (μ := μ)
  | insert b s hb ih =>
    have hstep : (fun a => ∑ i ∈ insert b s, f i a) = (fun a => f b a + ∑ i ∈ s, f i a) := by
      funext x; rw [Finset.sum_insert hb]
    rw [hstep]
    exact (h b (Finset.mem_insert_self b s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- The measures restricted to `(0,∞)` and to `Iz = [0,∞)` agree. -/
theorem restrict_Ioi_eq_restrict_Iz :
    volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict Work.Spaces.Iz := by
  rw [Work.Spaces.Iz]
  exact MeasureTheory.Measure.restrict_congr_set
    (MeasureTheory.Ioi_ae_eq_Ici (μ := volume) (a := 0))

/-- The radial weight is measurable. -/
theorem measurable_w : Measurable Work.Spaces.w := by
  have heq : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 * (z ^ 2)⁻¹ := by
    funext z; rw [Work.Spaces.w, div_eq_mul_inv]
  rw [heq]
  exact ((measurable_const.add measurable_id).pow_const 2).mul
    ((measurable_id.pow_const 2).inv)

/-- **The weighted `z`-sum of the `L₁₂`-jets.**  If each `(X k)² w²` has `Iz`-integral
at most `CL·|f|²_{ℋ⁶}`, then the full binomial-weighted sum, squared and against `w²`, is
dominated by a universal multiple of `CL·|f|²_{ℋ⁶}`. -/
theorem SW_bound {α : ℝ} {f : ℝ → ℝ → ℝ} {CL : ℝ} (hCL0 : 0 ≤ CL) {b : ℕ} (hb : b ≤ 6)
    {X : ℕ → ℝ → ℝ}
    (hXint : ∀ k : ℕ, k ≤ 6 → MeasureTheory.IntegrableOn
      (fun z => (X k z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz)
    (hXbd : ∀ k : ℕ, k ≤ 6 →
      (∫ z in Work.Spaces.Iz, (X k z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ CL * Work.Spaces.HkSq α 6 f)
    (hXaesm : ∀ k : ℕ, k ≤ 6 → AEStronglyMeasurable (X k)
      (volume.restrict Work.Spaces.Iz)) :
    MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 *
          (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) * |X k z|) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) * |X k z|) ^ 2)
        ≤ 10000000 * CL * Work.Spaces.HkSq α 6 f := by
  have hHk0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hc : ∀ k : ℕ, (b.choose k : ℝ) ^ 2 ≤ 4096 := by
    intro k
    have h1 : b.choose k ≤ 2 ^ b := Nat.choose_le_two_pow b k
    have h2 : 2 ^ b ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : b.choose k ≤ 64 := le_trans h1 h2
    have h4 : (b.choose k : ℝ) ≤ 64 := by exact_mod_cast h3
    nlinarith [show (0 : ℝ) ≤ (b.choose k : ℝ) by positivity]
  have hb1 : ((b + 1 : ℕ) : ℝ) ≤ 7 := by exact_mod_cast (by omega : b + 1 ≤ 7)
  have hC1 : ∀ k : ℕ, ((b + 1 : ℕ) : ℝ) * (b.choose k : ℝ) ^ 2 ≤ 28672 := by
    intro k
    calc ((b + 1 : ℕ) : ℝ) * (b.choose k : ℝ) ^ 2 ≤ 7 * 4096 :=
          mul_le_mul hb1 (hc k) (sq_nonneg _) (by norm_num)
      _ = 28672 := by norm_num
  have hpt : ∀ z : ℝ, (Work.Spaces.w z) ^ 2 *
        (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) * |X k z|) ^ 2
      ≤ 28672 * ∑ k ∈ Finset.range (b + 1), (X k z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
    intro z
    have hcs : (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) * |X k z|) ^ 2
        ≤ ((b + 1 : ℕ) : ℝ) *
          ∑ k ∈ Finset.range (b + 1), ((b.choose k : ℝ) * |X k z|) ^ 2 := by
      have h : (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) * |X k z|) ^ 2
          ≤ (((Finset.range (b + 1)).card : ℕ) : ℝ) *
            ∑ k ∈ Finset.range (b + 1), ((b.choose k : ℝ) * |X k z|) ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      simpa using h
    have hstep1 : (Work.Spaces.w z) ^ 2 *
          (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) * |X k z|) ^ 2
        ≤ (Work.Spaces.w z) ^ 2 *
          (((b + 1 : ℕ) : ℝ) *
            ∑ k ∈ Finset.range (b + 1), ((b.choose k : ℝ) * |X k z|) ^ 2) :=
      mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    refine hstep1.trans ?_
    have hEq : (Work.Spaces.w z) ^ 2 *
          (((b + 1 : ℕ) : ℝ) *
            ∑ k ∈ Finset.range (b + 1), ((b.choose k : ℝ) * |X k z|) ^ 2)
        = ∑ k ∈ Finset.range (b + 1), (Work.Spaces.w z) ^ 2 *
            (((b + 1 : ℕ) : ℝ) * ((b.choose k : ℝ) * |X k z|) ^ 2) := by
      rw [Finset.mul_sum, Finset.mul_sum]
    rw [hEq]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have h2 : ((b.choose k : ℝ) * |X k z|) ^ 2 = (b.choose k : ℝ) ^ 2 * (X k z) ^ 2 := by
      rw [mul_pow, sq_abs]
    rw [h2]
    have h1 : ((b + 1 : ℕ) : ℝ) * (b.choose k : ℝ) ^ 2 ≤ 28672 := hC1 k
    have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hx2 : 0 ≤ (X k z) ^ 2 := sq_nonneg _
    calc (Work.Spaces.w z) ^ 2 *
          (((b + 1 : ℕ) : ℝ) * ((b.choose k : ℝ) ^ 2 * (X k z) ^ 2))
        = (((b + 1 : ℕ) : ℝ) * (b.choose k : ℝ) ^ 2) *
            ((Work.Spaces.w z) ^ 2 * (X k z) ^ 2) := by ring
      _ ≤ 28672 * ((Work.Spaces.w z) ^ 2 * (X k z) ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg hw2 hx2)
      _ = 28672 * ((X k z) ^ 2 * (Work.Spaces.w z) ^ 2) := by ring
  have hIntSum : Integrable (fun z => ∑ k ∈ Finset.range (b + 1),
      (X k z) ^ 2 * (Work.Spaces.w z) ^ 2) (volume.restrict Work.Spaces.Iz) :=
    integrable_finset_sum_loc _ (fun k hk => hXint k (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) (by omega)))
  have hDom : Integrable (fun z => 28672 * ∑ k ∈ Finset.range (b + 1),
      (X k z) ^ 2 * (Work.Spaces.w z) ^ 2) (volume.restrict Work.Spaces.Iz) :=
    hIntSum.const_mul _
  have hAESM : AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 *
      (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) * |X k z|) ^ 2)
      (volume.restrict Work.Spaces.Iz) := by
    have hw : AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2)
        (volume.restrict Work.Spaces.Iz) :=
      (measurable_w.pow_const 2).aestronglyMeasurable
    have hsum : AEStronglyMeasurable
        (fun z => ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) * |X k z|)
        (volume.restrict Work.Spaces.Iz) :=
      aesm_finset_sum_loc _ (fun k hk =>
        (((hXaesm k (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) (by omega))).norm).congr
          (Filter.Eventually.of_forall fun z => Real.norm_eq_abs (X k z))).const_mul _)
    have hSW : AEStronglyMeasurable
        (fun z => (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) * |X k z|) ^ 2)
        (volume.restrict Work.Spaces.Iz) :=
      (hsum.mul hsum).congr (Filter.Eventually.of_forall fun z => by
        simp only [Pi.mul_apply, pow_two])
    exact (hw.mul hSW).congr (Filter.Eventually.of_forall fun z => by
      simp only [Pi.mul_apply])
  refine ⟨Integrable.mono' hDom hAESM (Filter.Eventually.of_forall fun z => ?_), ?_⟩
  · rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hpt z
  · have h1 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        (∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ) * |X k z|) ^ 2)
        ≤ ∫ z in Work.Spaces.Iz, 28672 * ∑ k ∈ Finset.range (b + 1),
            (X k z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _))
        hDom (Filter.Eventually.of_forall fun z => hpt z)
    refine h1.trans ?_
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_finsetSum _ (fun k hk => hXint k (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) (by omega)))]
    have h2 : (∑ k ∈ Finset.range (b + 1),
        ∫ z in Work.Spaces.Iz, (X k z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _k ∈ Finset.range (b + 1), CL * Work.Spaces.HkSq α 6 f :=
      Finset.sum_le_sum fun k hk => hXbd k (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) (by omega))
    have h3 : (∑ _k ∈ Finset.range (b + 1), CL * Work.Spaces.HkSq α 6 f)
        = ((b + 1 : ℕ) : ℝ) * (CL * Work.Spaces.HkSq α 6 f) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [h3] at h2
    refine (mul_le_mul_of_nonneg_left h2 (by norm_num : (0:ℝ) ≤ 28672)).trans ?_
    have h4 : 28672 * (((b + 1 : ℕ) : ℝ) * (CL * Work.Spaces.HkSq α 6 f))
        ≤ 10000000 * CL * Work.Spaces.HkSq α 6 f := by
      have h5 : 28672 * ((b + 1 : ℕ) : ℝ) ≤ 10000000 := by
        nlinarith [hb1]
      calc 28672 * (((b + 1 : ℕ) : ℝ) * (CL * Work.Spaces.HkSq α 6 f))
          = (28672 * ((b + 1 : ℕ) : ℝ)) * (CL * Work.Spaces.HkSq α 6 f) := by ring
        _ ≤ 10000000 * (CL * Work.Spaces.HkSq α 6 f) :=
            mul_le_mul_of_nonneg_right h5 (mul_nonneg hCL0 hHk0)
        _ = 10000000 * CL * Work.Spaces.HkSq α 6 f := by ring
    exact h4

/-! ## Cauchy–Schwarz in square-root form on the angular interval -/

/-- Cauchy–Schwarz in the square-root form, with the nonnegativity hypotheses only a.e. -/
theorem cs_sqrt_le_ae_Iθ {A B : ℝ → ℝ}
    (hA : MeasureTheory.IntegrableOn A Work.Spaces.Iθ)
    (hB : MeasureTheory.IntegrableOn B Work.Spaces.Iθ)
    (hAnn : ∀ᵐ x ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ A x)
    (hBnn : ∀ᵐ x ∂(volume.restrict Work.Spaces.Iθ), 0 ≤ B x) :
    (∫ x in Work.Spaces.Iθ, Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt (∫ x in Work.Spaces.Iθ, A x) * Real.sqrt (∫ x in Work.Spaces.Iθ, B x) := by
  have hAsm : AEStronglyMeasurable (fun x => Real.sqrt (A x))
      (volume.restrict Work.Spaces.Iθ) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have hBsm : AEStronglyMeasurable (fun x => Real.sqrt (B x))
      (volume.restrict Work.Spaces.Iθ) :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hB.aestronglyMeasurable
  have hAsq : Integrable (fun x => Real.sqrt (A x) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    hA.congr (hAnn.mono fun x hx => (Real.sq_sqrt hx).symm)
  have hBsq : Integrable (fun x => Real.sqrt (B x) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    hB.congr (hBnn.mono fun x hx => (Real.sq_sqrt hx).symm)
  have hAlp : MemLp (fun x => Real.sqrt (A x)) 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq hAsm).mpr hAsq
  have hBlp : MemLp (fun x => Real.sqrt (B x)) 2 (volume.restrict Work.Spaces.Iθ) :=
    (memLp_two_iff_integrable_sq hBsm).mpr hBsq
  have hcs := Work.Spaces.cs_integral hAlp hBlp
  have e1 : (∫ x in Work.Spaces.Iθ, Real.sqrt (A x) ^ 2) = ∫ x in Work.Spaces.Iθ, A x :=
    MeasureTheory.integral_congr_ae (hAnn.mono fun x hx => Real.sq_sqrt hx)
  have e2 : (∫ x in Work.Spaces.Iθ, Real.sqrt (B x) ^ 2) = ∫ x in Work.Spaces.Iθ, B x :=
    MeasureTheory.integral_congr_ae (hBnn.mono fun x hx => Real.sq_sqrt hx)
  rw [e1, e2] at hcs
  calc (∫ x in Work.Spaces.Iθ, Real.sqrt (A x) * Real.sqrt (B x))
      ≤ Real.sqrt ((∫ x in Work.Spaces.Iθ, A x) * (∫ x in Work.Spaces.Iθ, B x)) :=
        Real.le_sqrt_of_sq_le hcs
    _ = Real.sqrt (∫ x in Work.Spaces.Iθ, A x) * Real.sqrt (∫ x in Work.Spaces.Iθ, B x) :=
        Real.sqrt_mul (MeasureTheory.integral_nonneg_of_ae hAnn) _


end Work.FTS.StrongPersist.H6Pair6Aux
