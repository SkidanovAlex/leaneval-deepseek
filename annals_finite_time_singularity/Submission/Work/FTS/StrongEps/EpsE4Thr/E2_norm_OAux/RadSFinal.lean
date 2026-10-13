import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongEps.EpsE4Thr.E2_norm_OAux.RadSBlocks
import Submission.Work.FTS.StrongEps.EpsE4Thr.E1Open.Qang_sq_w_sq_le_HkSq_O
import Submission.Work.FTS.StrongEps.EpsE4Thr.E1Open.L12f_slot_le_O
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.radS_DzdIter_le
import Submission.Work.FTS.CoercivityFix.Transfer.E2norm.ampB_DzdIter_sq_w_sq_le
import Submission.Work.H2.T1Q.PwBdQ
import Submission.Work.Spaces.c_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E2O

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- **The level-`n` weighted slot sum of `radS α f`**, in the open class.

For a datum `f` which is `C^∞` on the open quadrant, honest in `ℋ⁵` and whose zero mode
vanishes, the sum of the weighted squares of the `D_z`-iterates of `radS α f` up to order
`n ≤ 3` is integrable and bounded by a multiple of `|f|²_{ℋⁿ} + |D_θ f|²_{ℋⁿ}`, uniformly in
`α ∈ (0,1]`, `n ≤ 3` and `f`.

The single input on the projector zero mode `C₀ = L₁₂(Transport f)(0)` is the hypothesis
`hC0`. -/
theorem radS_slotSum_le_O
    (hC0 : ∃ K : ℝ, 0 ≤ K ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 5 f →
      Work.Construction.L12 f 0 = 0 →
      (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
        ≤ K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (n : ℕ), n ≤ 3 → ∀ f : Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 5 f →
      Work.Construction.L12 f 0 = 0 →
      MeasureTheory.IntegrableOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
          (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ C * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
  obtain ⟨KA, hKAnn, hKAbd⟩ :=
    Work.FTS.CoercivityFix.Transfer.E2norm.ampA_dzdIter_bound_uniform
  obtain ⟨KB, hKBnn, hKB⟩ :=
    Work.FTS.CoercivityFix.Transfer.E2norm.ampB_DzdIter_sq_w_sq_le
  obtain ⟨K, hKnn, hKbound⟩ := hC0
  obtain ⟨CL, hCLpos, hCL⟩ := Work.FTS.StrongEps.EpsE4Thr.E1Open.L12f_slot_le_O_of
    (CQ := ∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
    (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
    (fun β m g hβ hβ1 hO hmem i hi =>
      Work.FTS.StrongEps.EpsE4Thr.E1Open.Qang_sq_w_sq_le_HkSq_O m β g hβ hβ1 hO hmem i hi)
  refine ⟨3084 * (KA ^ 2 * CL + 4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
      + 400 * KB * K) + 1, by positivity, ?_⟩
  intro α hα hα1 n hn f hO hmem5 hl12
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hO 4 (by norm_num) hmem5
  have hmemn : Work.Spaces.HkMem α n f :=
    Work.FTS.OpenPkg.HkMem_mono_open hO n (by omega) hmem5
  -- the angular-moment slot bounds at level `n`
  have hQ : ∀ i ≤ n, MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n f :=
    fun i hi =>
      Work.FTS.StrongEps.EpsE4Thr.E1Open.Qang_sq_w_sq_le_HkSq_O n α f hα hα1 hO hmemn i hi
  -- the `L₁₂` slot-sum bound at level `n`
  have hL := hCL α ⟨hα, hα1⟩ f hO hmem4 hl12 n hn
  -- the `ampB` slot bounds
  have hB : ∀ j ∈ Finset.range (n + 1), MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.Elliptic.DzdIter (j + 1)
        (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz :=
    fun j hj => (hKB α hα hα1 (j + 1) (by have := Finset.mem_range.mp hj; omega)).1
  have hBb : ∀ j ∈ Finset.range (n + 1),
      (∫ z in Work.Spaces.Iz, (Work.Elliptic.DzdIter (j + 1)
        (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) ≤ KB :=
    fun j hj => (hKB α hα hα1 (j + 1) (by have := Finset.mem_range.mp hj; omega)).2
  -- the `α`-uniform Kato bound on the `ampA`-iterates
  have hKbd : ∀ b ≤ 4, ∀ z ∈ IoiA,
      |Work.Elliptic.DzdIter b (Work.FTS.CoercivityFix.Transfer.ampA α) z| ≤ KA :=
    fun b hb z hz => hKAbd α hα hα1 b hb z hz
  -- the projector zero-mode bound at level `n`
  have hKC : (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
      ≤ K * Work.Spaces.HkSq α n (Work.Spaces.Dth f) := hKbound α hα hα1 n hn f hO hmem5 hl12
  have hKA2 : 0 ≤ KA ^ 2 := sq_nonneg KA
  -- integrability of the three block sums
  have hLSumInt : MeasureTheory.IntegrableOn (LSlotSum n f) Work.Spaces.Iz := hL.1
  have hQSumInt : MeasureTheory.IntegrableOn (QSlotSum n f) Work.Spaces.Iz := by
    change MeasureTheory.IntegrableOn (fun z : ℝ => ∑ i ∈ Finset.range (n + 1),
      (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz
    exact MeasureTheory.integrable_finsetSum _
      (fun i hi => (hQ i (by have := Finset.mem_range.mp hi; omega)).1)
  have hBSumInt : MeasureTheory.IntegrableOn (BSlotSum n α) Work.Spaces.Iz := by
    change MeasureTheory.IntegrableOn (fun z : ℝ => ∑ i ∈ Finset.range (n + 1),
      (Work.Elliptic.DzdIter (i + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz
    exact MeasureTheory.integrable_finsetSum _ (fun i hi => hB i hi)
  -- integrals of the three block sums
  have hIL : (∫ z in Work.Spaces.Iz, LSlotSum n f z) ≤ CL * Work.Spaces.HkSq α n f := hL.2
  have hIQ : (∫ z in Work.Spaces.Iz, QSlotSum n f z)
      ≤ 4 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n f) := by
    change (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range (n + 1),
        (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2) ≤ _
    rw [MeasureTheory.integral_finsetSum _
      (fun i hi => (hQ i (by have := Finset.mem_range.mp hi; omega)).1)]
    have h1 : (∑ i ∈ Finset.range (n + 1), ∫ z in Work.Spaces.Iz,
          (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _i ∈ Finset.range (n + 1),
            (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n f :=
      Finset.sum_le_sum (fun i hi => (hQ i (by have := Finset.mem_range.mp hi; omega)).2)
    have h2 : (∑ _i ∈ Finset.range (n + 1),
          (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n f)
        = ((n : ℝ) + 1) * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α n f) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    have h3 : ((n : ℝ) + 1) ≤ 4 := by
      have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
      linarith
    have h4 : 0 ≤ (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        * Work.Spaces.HkSq α n f :=
      mul_nonneg (MeasureTheory.integral_nonneg fun θ => sq_nonneg _)
        (Work.Spaces.HkSq_nonneg α n f)
    calc (∑ i ∈ Finset.range (n + 1), ∫ z in Work.Spaces.Iz,
          (Work.Elliptic.Qang f i z) ^ 2 * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _i ∈ Finset.range (n + 1),
            (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) * Work.Spaces.HkSq α n f := h1
      _ = ((n : ℝ) + 1) * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α n f) := h2
      _ ≤ 4 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α n f) := mul_le_mul_of_nonneg_right h3 h4
  have hIB : (∫ z in Work.Spaces.Iz, BSlotSum n α z) ≤ 4 * KB := by
    change (∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter (i + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
          * (Work.Spaces.w z) ^ 2) ≤ _
    rw [MeasureTheory.integral_finsetSum _ (fun i hi => hB i hi)]
    have h1 : (∑ i ∈ Finset.range (n + 1), ∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter (i + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
            * (Work.Spaces.w z) ^ 2) ≤ ∑ _i ∈ Finset.range (n + 1), KB :=
      Finset.sum_le_sum (fun i hi => hBb i hi)
    have h2 : (∑ _i ∈ Finset.range (n + 1), KB) = ((n : ℝ) + 1) * KB := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      push_cast
      ring
    have h3 : ((n : ℝ) + 1) ≤ 4 := by
      have : (n : ℝ) ≤ 3 := by exact_mod_cast hn
      linarith
    calc (∑ i ∈ Finset.range (n + 1), ∫ z in Work.Spaces.Iz,
          (Work.Elliptic.DzdIter (i + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
            * (Work.Spaces.w z) ^ 2)
        ≤ ∑ _i ∈ Finset.range (n + 1), KB := h1
      _ = ((n : ℝ) + 1) * KB := h2
      _ ≤ 4 * KB := mul_le_mul_of_nonneg_right h3 hKBnn
  -- ## the pointwise bound
  have hpt := radS_sum_le (n := n) α hα hα1 hn hO hmem5 hl12 hKAnn hKbd
  -- ## integrability of the slot sum
  have hRHSInt : MeasureTheory.IntegrableOn (fun z : ℝ =>
      3084 * (KA ^ 2 * LSlotSum n f z + KA ^ 2 * QSlotSum n f z
        + SConst α f * BSlotSum n α z)) Work.Spaces.Iz :=
    (((hLSumInt.const_mul (KA ^ 2)).add (hQSumInt.const_mul (KA ^ 2))).add
      (hBSumInt.const_mul (SConst α f))).const_mul 3084
  have haesm : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    have hA : ContDiffOn ℝ 4 (Work.Coercivity.L12f f) IoiA :=
      contDiffOn_four_L12f α hα hα1 hO hmem5
    have hsmR : ContDiffOn ℝ 3 (Work.FTS.CoercivityFix.Transfer.radS α f) IoiA :=
      Work.FTS.CoercivityFix.Transfer.AuxE2.radS_contDiffOn_three α hα hα1 hA
    have hcont : ContinuousOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2) IoiA := by
      refine continuousOn_finsetSum _ (fun j hj => ?_)
      have hj3 : j ≤ 3 := by have := Finset.mem_range.mp hj; omega
      have hj1 : ContinuousOn (fun z : ℝ =>
          Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) IoiA := by
        rw [Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter]
        exact Work.FTS.CoercivityFix.Transfer.E1Parts.continuousOn_Zop_iter_of_contDiffOn
          (b := j) (n := 0) (hu := hsmR.of_le (Nat.cast_le.mpr hj3))
      have hw2 : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) IoiA := by
        have hfun : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
        rw [hfun]
        exact (ContinuousOn.div ((continuousOn_const.add continuousOn_id).pow 2)
          (continuousOn_id.pow 2) (fun z hz => pow_ne_zero 2 (ne_of_gt hz))).pow 2
      exact (hj1.pow 2).mul hw2
    exact Work.H2.T1Q.aesm_Iz_of_continuousOn hcont
  have hint : MeasureTheory.IntegrableOn (fun z : ℝ => ∑ j ∈ Finset.range (n + 1),
      (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
        * (Work.Spaces.w z) ^ 2) Work.Spaces.Iz := by
    refine Integrable.mono' hRHSInt haesm ?_
    filter_upwards [hpt] with z hz
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact hz
  refine ⟨hint, ?_⟩
  -- ## the integral bound
  have hmono : (∫ z in Work.Spaces.Iz, ∑ j ∈ Finset.range (n + 1),
        (Work.Elliptic.DzdIter j (Work.FTS.CoercivityFix.Transfer.radS α f) z) ^ 2
          * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Work.Spaces.Iz,
          3084 * (KA ^ 2 * LSlotSum n f z + KA ^ 2 * QSlotSum n f z
            + SConst α f * BSlotSum n α z) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => Finset.sum_nonneg fun j _ =>
        mul_nonneg (sq_nonneg _) (sq_nonneg _)) hRHSInt ?_
    filter_upwards [hpt] with z hz
    exact hz
  refine le_trans hmono ?_
  have hlin : (∫ z in Work.Spaces.Iz,
        3084 * (KA ^ 2 * LSlotSum n f z + KA ^ 2 * QSlotSum n f z
          + SConst α f * BSlotSum n α z))
      = 3084 * (KA ^ 2 * (∫ z in Work.Spaces.Iz, LSlotSum n f z)
          + KA ^ 2 * (∫ z in Work.Spaces.Iz, QSlotSum n f z)
          + SConst α f * (∫ z in Work.Spaces.Iz, BSlotSum n α z)) := by
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [MeasureTheory.integral_add
      (f := fun x : ℝ => KA ^ 2 * LSlotSum n f x + KA ^ 2 * QSlotSum n f x)
      (g := fun x : ℝ => SConst α f * BSlotSum n α x)
      ((hLSumInt.const_mul (KA ^ 2)).add (hQSumInt.const_mul (KA ^ 2)))
      (hBSumInt.const_mul (SConst α f))]
    rw [MeasureTheory.integral_add (f := fun x : ℝ => KA ^ 2 * LSlotSum n f x)
      (g := fun x : ℝ => KA ^ 2 * QSlotSum n f x) (hLSumInt.const_mul (KA ^ 2))
      (hQSumInt.const_mul (KA ^ 2)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
  rw [hlin]
  -- ## the final arithmetic
  have hHnn : 0 ≤ Work.Spaces.HkSq α n f := Work.Spaces.HkSq_nonneg α n f
  have hH'nn : 0 ≤ Work.Spaces.HkSq α n (Work.Spaces.Dth f) := Work.Spaces.HkSq_nonneg α n _
  have hSle : SConst α f ≤ 100 * (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    rw [SConst]
    have hc := (Work.Spaces.c_bounds α hα hα1).1
    have hcpos : 0 < Work.Spaces.c α := by linarith
    have hcsq : (1 : ℝ) / 100 ≤ (Work.Spaces.c α) ^ 2 := by nlinarith [hc, hcpos]
    have hinv : ((Work.Spaces.c α) ^ 2)⁻¹ ≤ 100 := by
      rw [inv_eq_one_div, div_le_iff₀ (pow_pos hcpos 2)]
      nlinarith [hcsq]
    calc (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 / Work.Spaces.c α) ^ 2
        = (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2
            * ((Work.Spaces.c α) ^ 2)⁻¹ := by rw [div_pow, div_eq_mul_inv]
      _ ≤ (Work.Coercivity.L12f (Work.Coercivity.Transport f) 0) ^ 2 * 100 :=
          mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
      _ ≤ (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) * 100 :=
          mul_le_mul_of_nonneg_right hKC (by norm_num)
      _ = 100 * (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by ring
  have hIBSnn : 0 ≤ (∫ z in Work.Spaces.Iz, BSlotSum n α z) := by
    change 0 ≤ ∫ z in Work.Spaces.Iz, ∑ i ∈ Finset.range (n + 1),
      (Work.Elliptic.DzdIter (i + 1) (Work.FTS.CoercivityFix.Transfer.ampB α) z) ^ 2
        * (Work.Spaces.w z) ^ 2
    exact MeasureTheory.integral_nonneg fun z => Finset.sum_nonneg fun i _ =>
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hT1 : KA ^ 2 * (∫ z in Work.Spaces.Iz, LSlotSum n f z)
      ≤ KA ^ 2 * (CL * Work.Spaces.HkSq α n f) :=
    mul_le_mul_of_nonneg_left hIL hKA2
  have hT2 : KA ^ 2 * (∫ z in Work.Spaces.Iz, QSlotSum n f z)
      ≤ KA ^ 2 * (4 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkSq α n f)) := mul_le_mul_of_nonneg_left hIQ hKA2
  have hT3 : SConst α f * (∫ z in Work.Spaces.Iz, BSlotSum n α z)
      ≤ 100 * (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) * (4 * KB) :=
    mul_le_mul hSle hIB hIBSnn (by positivity)
  have hYnn : 0 ≤ Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f) := by
    linarith
  -- the three blocks, each bounded by the target
  have hE1 : 3084 * (KA ^ 2 * (CL * Work.Spaces.HkSq α n f))
      ≤ (3084 * (KA ^ 2 * CL)) * (Work.Spaces.HkSq α n f
          + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have hX : (0 : ℝ) ≤ 3084 * (KA ^ 2 * CL) :=
      mul_nonneg (by norm_num) (mul_nonneg hKA2 hCLpos.le)
    have h := mul_le_mul_of_nonneg_left (show Work.Spaces.HkSq α n f
        ≤ Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f) by linarith) hX
    calc 3084 * (KA ^ 2 * (CL * Work.Spaces.HkSq α n f))
        = (3084 * (KA ^ 2 * CL)) * Work.Spaces.HkSq α n f := by ring
      _ ≤ (3084 * (KA ^ 2 * CL)) * (Work.Spaces.HkSq α n f
            + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := h
  have hE2 : 3084 * (KA ^ 2 * (4 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          * Work.Spaces.HkSq α n f)))
      ≤ (3084 * (4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)))
          * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have hX : 0 ≤ 4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) := by positivity
    have h := mul_le_mul_of_nonneg_left (show Work.Spaces.HkSq α n f
        ≤ Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f) by linarith) hX
    calc 3084 * (KA ^ 2 * (4 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α n f)))
        = 3084 * ((4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2))
            * Work.Spaces.HkSq α n f) := by ring
      _ ≤ 3084 * ((4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2))
            * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
          mul_le_mul_of_nonneg_left h (by norm_num)
      _ = _ := by ring
  have hE3 : 3084 * (100 * (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) * (4 * KB))
      ≤ (3084 * (400 * KB * K)) * (Work.Spaces.HkSq α n f
          + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have hX : 0 ≤ 400 * KB * K := by positivity
    have h := mul_le_mul_of_nonneg_left (show Work.Spaces.HkSq α n (Work.Spaces.Dth f)
        ≤ Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f) by linarith) hX
    calc 3084 * (100 * (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) * (4 * KB))
        = 3084 * ((400 * KB * K) * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by ring
      _ ≤ 3084 * ((400 * KB * K) * (Work.Spaces.HkSq α n f
            + Work.Spaces.HkSq α n (Work.Spaces.Dth f))) :=
          mul_le_mul_of_nonneg_left h (by norm_num)
      _ = (3084 * (400 * KB * K)) * (Work.Spaces.HkSq α n f
            + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by ring
  have hcomb : (3084 * (KA ^ 2 * CL)) * (Work.Spaces.HkSq α n f
          + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
        + (3084 * (4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)))
          * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
        + (3084 * (400 * KB * K)) * (Work.Spaces.HkSq α n f
          + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
      = 3084 * (KA ^ 2 * CL + 4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          + 400 * KB * K) * (Work.Spaces.HkSq α n f
            + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by ring
  have hmain : 3084 * (KA ^ 2 * (∫ z in Work.Spaces.Iz, LSlotSum n f z)
        + KA ^ 2 * (∫ z in Work.Spaces.Iz, QSlotSum n f z)
        + SConst α f * (∫ z in Work.Spaces.Iz, BSlotSum n α z))
      ≤ 3084 * (KA ^ 2 * (CL * Work.Spaces.HkSq α n f)
        + KA ^ 2 * (4 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α n f))
        + 100 * (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) * (4 * KB)) := by
    have h1 : KA ^ 2 * (∫ z in Work.Spaces.Iz, LSlotSum n f z)
          + KA ^ 2 * (∫ z in Work.Spaces.Iz, QSlotSum n f z)
          + SConst α f * (∫ z in Work.Spaces.Iz, BSlotSum n α z)
        ≤ KA ^ 2 * (CL * Work.Spaces.HkSq α n f)
          + KA ^ 2 * (4 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
              * Work.Spaces.HkSq α n f))
          + 100 * (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) * (4 * KB) := by
      linarith [hT1, hT2, hT3]
    exact mul_le_mul_of_nonneg_left h1 (by norm_num)
  have hsplit : 3084 * (KA ^ 2 * (CL * Work.Spaces.HkSq α n f)
        + KA ^ 2 * (4 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α n f))
        + 100 * (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) * (4 * KB))
      = 3084 * (KA ^ 2 * (CL * Work.Spaces.HkSq α n f))
        + 3084 * (KA ^ 2 * (4 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α n f)))
        + 3084 * (100 * (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) * (4 * KB)) := by ring
  have hbig : 3084 * (KA ^ 2 * (CL * Work.Spaces.HkSq α n f))
        + 3084 * (KA ^ 2 * (4 * ((∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
            * Work.Spaces.HkSq α n f)))
        + 3084 * (100 * (K * Work.Spaces.HkSq α n (Work.Spaces.Dth f)) * (4 * KB))
      ≤ 3084 * (KA ^ 2 * CL + 4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          + 400 * KB * K) * (Work.Spaces.HkSq α n f
            + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    linarith [hE1, hE2, hE3, hcomb]
  have hTgt : 3084 * (KA ^ 2 * CL + 4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
        + 400 * KB * K) * (Work.Spaces.HkSq α n f + Work.Spaces.HkSq α n (Work.Spaces.Dth f))
      ≤ (3084 * (KA ^ 2 * CL + 4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2)
          + 400 * KB * K) + 1) * (Work.Spaces.HkSq α n f
            + Work.Spaces.HkSq α n (Work.Spaces.Dth f)) := by
    have h1 : 3084 * (KA ^ 2 * CL
          + 4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 400 * KB * K)
        ≤ 3084 * (KA ^ 2 * CL
          + 4 * KA ^ 2 * (∫ θ in Work.Spaces.Iθ, Work.Elliptic.Ktheta θ ^ 2) + 400 * KB * K)
          + 1 := by linarith
    exact mul_le_mul_of_nonneg_right h1 hYnn
  linarith [hmain, hsplit, hbig, hTgt]

end Work.FTS.StrongEps.EpsE4Thr.E2O
