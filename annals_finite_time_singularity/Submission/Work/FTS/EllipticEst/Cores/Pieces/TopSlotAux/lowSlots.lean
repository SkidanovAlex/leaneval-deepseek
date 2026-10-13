import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.TT.ESW.low_order_le
import Submission.Work.FTS.EllipticEst.remov.high_slice_chain_slots
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.EllipticEst.remov.smoothOpen_slices_weak
import Submission.Work.FTS.EllipticEst.mul_w_sin_rpow_sq
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `lowSlots`: the three low angular slots of the elliptic `ℋ^k` estimate

The target is the low-order angular part of Elgindi's `ℋ^k` elliptic estimate: for a datum
`EllWeakPos α k F Ψ` of the weak class with `k ≥ 3` and under the single level-`(k-1)` norm bound

  `α²|z²∂_z²Ψ|_{ℋ^{k-1}} + |∂_θθΨ|_{ℋ^{k-1}} ≤ D |F|_{ℋ^k}`,

the three slots `∫∫ w²(∂_θθΨ)²σ`, `∫∫ w²(∂_θΨ)²` and `∫∫ w²Ψ²` (the `η`-term and the two
`L²`-bounded slots of `TopSlotRhsDom`) are bounded by `C·|F|²_{ℋ^k}`, with `C` depending on `D`
and `k` only.

The proof has two parts.

* The `η`-slot `∫∫ w²(∂_θθΨ)² σ` is a single summand of the `ℋ^{k-1}`-integrand of
  `∂_θθΨ` (the `i = 0` slot, `σ = sin(2θ)^{-η}`), so it is at most
  `HkSq α (k-1) (∂_θθΨ) ≤ D²·HkSq α k F` — the second inequality being the square of the
  hypothesis (via `HkSq_eq_HkNorm_sq`).  The level-`(k-1)` honesty of `∂_θθΨ` is
  `HkMem_descend_open` applied to `EllWeakPos.memB`.

* The two `L²`-slots are handled *slicewise* by the proved all-order slice bound
  `TT.ESW.low_order_le`:  for `z > 0` the slice `u = Ψ z ·` is `C²` on `(0,π/2)` with vanishing
  angular moment, right endpoint limit `0` and `∫(u'')²σ < ∞`, and the first-order slice bound
  `∫(u')² + ∫u² ≤ 20∫(u'')²σ` holds (`TT.ESW.slice_low_order`).  Integrating the resulting
  pointwise (in `z`) bounds `∫(∂_θΨ)² ≤ 20∫(∂_θθΨ)²σ` and `∫Ψ² ≤ 20∫(∂_θθΨ)²σ` against `w²`
  needs only the honest integrability of `z ↦ w(z)²∫(∂_θθΨ)²σ`, which is the
  `i = 0`-slot of `HkMem α k (∂_θθΨ)` (`TT.ESW.integrable_w_sq_thetaEnergy`); the two
  `L²`-integrands themselves need not be integrable thanks to `integral_mono_of_nonneg`.

Constants are existential, so all losses are absorbed into `C = 41 D² + 1`.
-/

namespace Work.FTS.EllipticEst.Cores.Pieces.TopSlotAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

/-- **The `i = 0` slot of the `ℋ^k`-integrand dominates the `η`-weighted square of the centre.**
For `f` with honest `ℋ^k`-integrand and `z ∈ Iz`,
`w(z)²·∫_θ (f z θ)² σ(θ) ≤ ∫_θ HkIntegrand α k f z θ`.  This is the per-`z` comparison behind
`Work.Spaces.L2Sq_DzIter_le_HkSq` at `i = 0`. -/
private theorem slot_le_HkIntegrand {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hmem : Work.Spaces.HkMem α k g) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    (Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ := by
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono_of_nonneg ?_ (hmem.1 z hz) ?_
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _)
        (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.Honest.sEta_nonneg hθ))
  · refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo fun θ hθ => ?_
    have h1 := Work.Spaces.sq_le_HkIntegrand_z α k g z θ 0 (Nat.zero_le k)
    simp only [Work.Spaces.DzIter_zero] at h1
    have h2 := Work.FTS.EllipticEst.mul_w_sin_rpow_sq (g z θ) (Work.Spaces.w z)
      (show θ ∈ Work.Spaces.Iθ from ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    simp only [Work.FTS.EllipticEst.sEta] at h1 ⊢
    calc (Work.Spaces.w z) ^ 2 * ((g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) := by ring
      _ = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
          h2.symm
      _ ≤ Work.Spaces.HkIntegrand α k g z θ := h1

/-- **The slicewise low-order bound of `TT.ESW`, in the form used below.**  For a datum of the
weak class and `z > 0`,

  `∫_θ (∂_θΨ)² + ∫_θ Ψ² ≤ 20 ∫_θ (∂_θθΨ)² σ`.

The two integrals on the left are split with `integral_add`, which needs their honest
integrability — supplied by the boundedness of the slice and of its derivative on `(0,π/2)`
(`Honest.SliceBddSqSigma`) and the finiteness of the angular measure. -/
private theorem low_slot_perZ {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
        + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
      ≤ 20 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) := by
  obtain ⟨hsm2, hB2, hint, hmom, hval⟩ :=
    Work.FTS.EllipticEst.TT.ESW.slice_class_facts hwk hz
  have hπ : Filter.Tendsto (fun θ => Ψ z θ)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
    Work.FTS.EllipticEst.TT.ESW.slice_tendsto_pi_half hwk hz
  have hslice := Work.FTS.EllipticEst.TT.ESW.slice_low_order hsm2 hπ hval hint hmom hB2
  -- ## the two low-order slices are honestly integrable
  obtain ⟨C, _hCpos, hC⟩ := Work.FTS.EllipticEst.Honest.SliceBddSqSigma hsm2 hB2
  have hvol : (MeasureTheory.volume : Measure ℝ) Work.Spaces.Iθ < ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
  have hYint : MeasureTheory.IntegrableOn (fun θ => (deriv (fun t => Ψ z t) θ) ^ 2)
      Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.of_bound hvol
      ((measurable_deriv (fun t => Ψ z t)).aestronglyMeasurable.pow 2) (C ^ 2) ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo fun θ hθ => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc (deriv (fun t => Ψ z t) θ) ^ 2 = |deriv (fun t => Ψ z t) θ| ^ 2 := by rw [sq_abs]
      _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hC θ hθ).1 2
  have hS : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
  have hZint : MeasureTheory.IntegrableOn (fun θ => (Ψ z θ) ^ 2) Work.Spaces.Iθ := by
    refine MeasureTheory.IntegrableOn.of_bound hvol
      ((Work.FTS.EllipticEst.remov.ws_aesm_slice hS hz).pow 2) (C ^ 2) ?_
    refine Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo fun θ hθ => ?_
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    calc (Ψ z θ) ^ 2 = |Ψ z θ| ^ 2 := by rw [sq_abs]
      _ ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hC θ hθ).2 2
  -- ## transport `slice_low_order` to the `pthIter`-vocabulary and split the sum
  have hEq2 : (∫ θ in Work.Spaces.Iθ, (deriv (fun t => deriv (fun s => Ψ z s) t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  rw [hEq2] at hslice
  have hsplit : (∫ θ in Work.Spaces.Iθ, (deriv (fun t => Ψ z t) θ) ^ 2 + (Ψ z θ) ^ 2)
      = (∫ θ in Work.Spaces.Iθ, (deriv (fun t => Ψ z t) θ) ^ 2)
        + (∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2) :=
    MeasureTheory.integral_add hYint hZint
  rw [hsplit] at hslice
  have hEq1 : (∫ θ in Work.Spaces.Iθ, (deriv (fun t => Ψ z t) θ) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2 :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => by
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  rw [hEq1] at hslice
  exact hslice

/-- **The pointwise-in-`z` bound integrated against `w²`.**  If `v z ≤ 20 X z` for `z > 0`, with
`v` nonnegative and `X z = ∫_θ (∂_θθΨ)²σ`, then `∫_z w²·v ≤ 20∫_z w²·X`; this uses only the
honest integrability of `z ↦ w²·X` and `integral_mono_of_nonneg`, so no integrability of
`z ↦ w²·v` is needed. -/
private theorem zIntegral_le_of_perZ {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (v : ℝ → ℝ)
    (hv : ∀ z, 0 < z → v z ≤ 20 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
    (hvnn : ∀ z, 0 ≤ v z) :
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * v z)
      ≤ 20 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) := by
  have hmaj : MeasureTheory.Integrable
      (fun z => 20 * ((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (Work.FTS.EllipticEst.TT.ESW.integrable_w_sq_thetaEnergy hwk).const_mul 20
  have hpt : ∀ z ∈ Work.Spaces.Iz,
      (Work.Spaces.w z) ^ 2 * v z ≤ 20 * ((Work.Spaces.w z) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)) := by
    intro z hz
    have hz' : (0 : ℝ) ≤ z := hz
    rcases eq_or_lt_of_le hz' with h0 | hz0
    · subst h0
      simp [Work.Spaces.w]
    · calc (Work.Spaces.w z) ^ 2 * v z
          ≤ (Work.Spaces.w z) ^ 2 * (20 * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
            mul_le_mul_of_nonneg_left (hv z hz0) (sq_nonneg _)
        _ = 20 * ((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) := by ring
  have hmain := MeasureTheory.integral_mono_of_nonneg
    (f := fun z => (Work.Spaces.w z) ^ 2 * v z)
    (g := fun z => 20 * ((Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)))
    (Filter.Eventually.of_forall fun z => mul_nonneg (sq_nonneg _) (hvnn z))
    hmaj
    ((MeasureTheory.ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall hpt))
  rwa [MeasureTheory.integral_const_mul] at hmain

theorem lowSlots (D : ℝ) (hD : 0 < D) : ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
        ≤ D * Work.Spaces.HkNorm α k F →
      ((∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
              ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)
            + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
              ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
            + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
              ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
        ≤ C * Work.Spaces.HkSq α k F := by
  intro k hk
  refine ⟨41 * D ^ 2 + 1, by positivity, ?_⟩
  intro α F Ψ hα hα4 hwk h1
  -- ## the `η`-slot, a single summand of the level-`(k-1)` integrand of `∂_θθΨ`
  have hT1 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)
      ≤ Work.Spaces.HkSq α (k - 1) (Work.Spaces.pthIter 2 Ψ) := by
    have hsm2 : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 Ψ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
        (Work.FTS.EllipticEst.remov.smoothOpen_slices_weak hwk 0).2.2.2
    have hmemB2 : Work.Spaces.HkMem α (k - 1) (Work.Spaces.pthIter 2 Ψ) :=
      Work.FTS.EllipticEst.TT.HkMem_descend_open (by omega) hsm2 hwk.memB
    rw [Work.Spaces.HkSq]
    refine MeasureTheory.integral_mono_ae
      (Work.FTS.EllipticEst.TT.ESW.integrable_w_sq_thetaEnergy hwk) hmemB2.2 ?_
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mpr
      (Filter.Eventually.of_forall ?_)
    intro z hz
    exact slot_le_HkIntegrand hmemB2 hz
  have hBsq : Work.Spaces.HkSq α (k - 1) (Work.Spaces.pthIter 2 Ψ)
      ≤ D ^ 2 * Work.Spaces.HkSq α k F := by
    have hBnorm : Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
        ≤ D * Work.Spaces.HkNorm α k F := by
      have h0 : 0 ≤ α ^ 2 * Work.Spaces.HkNorm α (k - 1)
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
        mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg α (k - 1) _)
      linarith
    exact Work.FTS.EllipticEst.remov.HkSq_le_of_HkNorm_le hD.le hBnorm
  have hA : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) ≤ D ^ 2 * Work.Spaces.HkSq α k F :=
    le_trans hT1 hBsq
  -- ## the two low-order slots, slicewise
  have hT2 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
      ≤ 20 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) :=
    zIntegral_le_of_perZ hwk (fun z => ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
      (fun z hz => by
        have h := low_slot_perZ hwk hz
        have hZnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2 :=
          integral_nonneg fun θ => sq_nonneg _
        linarith)
      (fun _ => integral_nonneg fun θ => sq_nonneg _)
  have hT3 : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
        ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
      ≤ 20 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) :=
    zIntegral_le_of_perZ hwk (fun z => ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2)
      (fun z hz => by
        have h := low_slot_perZ hwk hz
        have hYnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2 :=
          integral_nonneg fun θ => sq_nonneg _
        linarith)
      (fun _ => integral_nonneg fun θ => sq_nonneg _)
  -- ## the arithmetic
  have hFnn : 0 ≤ Work.Spaces.HkSq α k F := Work.Spaces.HkSq_nonneg α k F
  have hsum : ((∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
              ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)
            + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
              ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
            + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
              ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      ≤ (41 * D ^ 2) * Work.Spaces.HkSq α k F := by
    linarith [hA, hT2, hT3]
  calc ((∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
              ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 Ψ z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)
            + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
              ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 1 Ψ z θ) ^ 2)
            + (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
              ∫ θ in Work.Spaces.Iθ, (Ψ z θ) ^ 2))
      ≤ (41 * D ^ 2) * Work.Spaces.HkSq α k F := hsum
    _ ≤ (41 * D ^ 2 + 1) * Work.Spaces.HkSq α k F := by
        nlinarith [hFnn]

end Work.FTS.EllipticEst.Cores.Pieces.TopSlotAux
