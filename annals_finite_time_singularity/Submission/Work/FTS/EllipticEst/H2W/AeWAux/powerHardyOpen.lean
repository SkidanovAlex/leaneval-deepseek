import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The sharp power-weight Hardy inequality on the open interval `(0,a)`

For `a > 0` and `0 ≤ η < 1`, every `f` of class `C¹` on `(0,a)` with
`∫_0^a f² t^{-(2+η)} < ∞` and `∫_0^a (f')² t^{-η} < ∞` satisfies

  `∫_0^a f² t^{-(2+η)} ≤ 4/(1+η)² ∫_0^a (f')² t^{-η}`,

with the classical sharp constant `4/(1+η)²` (saturated in the limit by `t ↦ t^s`,
`s ↘ (1+η)/2`).

**No boundary condition at `0` is needed.**  The finiteness of `∫ f² t^{-(2+η)}` alone forces
`liminf_{t→0⁺} f(t)² t^{-(1+η)} = 0` (otherwise `f² t^{-(2+η)} ≥ λ/t` on a neighbourhood of `0`,
and `t ↦ 1/t` is not integrable on `(0,δ)`), which is exactly what is needed to pass the boundary
term of the completion of squares `0 ≤ (f' - ((1+η)/2) f/t)² t^{-η}` to the limit.

The proof of `powerHardyOpen_interval` below is the standard open-interval argument: integrate
the completion of squares over `[ε, a']`, apply the fundamental theorem of calculus to
`t ↦ f(t)² t^{-(1+η)}`, discard the two favourable boundary terms, and let the left endpoint tend
to `0` along a sequence on which `f(t)² t^{-(1+η)} → 0`.
-/

namespace Work.FTS.EllipticEst.H2W.AeWAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

private theorem powerHardyOpen_interval {a η : ℝ} (ha : 0 < a) (hη0 : 0 ≤ η) (hη1 : η < 1) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 a))
    (hInt2 : IntegrableOn (fun t => (f t) ^ 2 * t ^ (-(2 + η))) (Set.Ioo 0 a))
    (hInt1 : IntegrableOn (fun t => (deriv f t) ^ 2 * t ^ (-η)) (Set.Ioo 0 a)) :
    (∫ t in (0 : ℝ)..a, (f t) ^ 2 * t ^ (-(2 + η)))
      ≤ 4 / (1 + η) ^ 2 * ∫ t in (0 : ℝ)..a, (deriv f t) ^ 2 * t ^ (-η) := by
  have h1η : (0 : ℝ) < 1 + η := by linarith
  set G : ℝ → ℝ := fun t => (f t) ^ 2 * t ^ (-(1 + η)) with hG
  set Φ : ℝ → ℝ := fun t => 2 * (f t * deriv f t * t ^ (-(1 + η)))
      - (1 + η) * ((f t) ^ 2 * t ^ (-(2 + η))) with hΦ
  -- ### derivative data
  have hfd : ∀ x ∈ Set.Ioo (0 : ℝ) a, HasDerivAt f (deriv f x) x := by
    intro x hx
    exact ((hf.contDiffAt (isOpen_Ioo.mem_nhds hx)).differentiableAt one_ne_zero).hasDerivAt
  have hGderiv : ∀ x ∈ Set.Ioo (0 : ℝ) a, HasDerivAt G (Φ x) x := by
    intro x hx
    have hd := hfd x hx
    have h1 : HasDerivAt (fun t : ℝ => (f t) ^ 2) (2 * (f x) ^ 1 * deriv f x) x := hd.pow 2
    have h2 : HasDerivAt (fun t : ℝ => t ^ (-(1 + η))) (-(1 + η) * x ^ (-(1 + η) - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx.1))
    have h3 := h1.mul h2
    rw [show -(1 + η) - 1 = -(2 + η) by ring] at h3
    rw [hG, hΦ]
    refine h3.congr_deriv ?_
    ring
  -- ### pointwise completion of squares
  have hpt : ∀ t ∈ Set.Ioo (0 : ℝ) a,
      (1 + η) ^ 2 / 4 * ((f t) ^ 2 * t ^ (-(2 + η)))
        ≤ (deriv f t) ^ 2 * t ^ (-η) + (-(1 + η) / 2) * Φ t := by
    intro t ht
    simp only [hΦ]
    have hid1 : t ^ 2 * t ^ (-(2 + η)) = t ^ (-η) := by
      rw [← Real.rpow_two t, ← Real.rpow_add ht.1]; congr 1; ring
    have hid2 : t * t ^ (-(1 + η)) = t ^ (-η) := by
      have h := Real.rpow_add ht.1 (1 : ℝ) (-(1 + η))
      rw [show (1 : ℝ) + (-(1 + η)) = -η by ring] at h
      rw [Real.rpow_one] at h
      exact h.symm
    have h2 : (f t / t) ^ 2 * t ^ 2 = f t ^ 2 := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 (ne_of_gt ht.1))]
    have hx1 : f t ^ 2 * t ^ (-(2 + η)) = (f t / t) ^ 2 * t ^ (-η) := by
      calc f t ^ 2 * t ^ (-(2 + η)) = ((f t / t) ^ 2 * t ^ 2) * t ^ (-(2 + η)) := by rw [h2]
        _ = (f t / t) ^ 2 * (t ^ 2 * t ^ (-(2 + η))) := by ring
        _ = (f t / t) ^ 2 * t ^ (-η) := by rw [hid1]
    have hx2 : f t * deriv f t * t ^ (-(1 + η)) = (f t / t) * deriv f t * t ^ (-η) := by
      have h3 : (f t / t) * t = f t := div_mul_cancel₀ (f t) (ne_of_gt ht.1)
      calc f t * deriv f t * t ^ (-(1 + η))
          = ((f t / t) * t) * deriv f t * t ^ (-(1 + η)) := by rw [h3]
        _ = (f t / t) * deriv f t * (t * t ^ (-(1 + η))) := by ring
        _ = (f t / t) * deriv f t * t ^ (-η) := by rw [hid2]
    rw [hx1, hx2]
    nlinarith [mul_nonneg (Real.rpow_nonneg ht.1.le (-η))
      (sq_nonneg (deriv f t - (1 + η) / 2 * (f t / t)))]
  -- ### Step 1: the per-`ε` inequality
  have step1 : ∀ ε a' : ℝ, 0 < ε → ε < a' → a' < a →
      (1 + η) ^ 2 / 4 * (∫ t in ε..a', (f t) ^ 2 * t ^ (-(2 + η)))
        ≤ (∫ t in ε..a', (deriv f t) ^ 2 * t ^ (-η)) + (1 + η) / 2 * G ε := by
    intro ε a' hε hεa' ha'a
    have hle : ε ≤ a' := le_of_lt hεa'
    have hsub : Set.Icc ε a' ⊆ Set.Ioo (0 : ℝ) a := fun x hx =>
      ⟨lt_of_lt_of_le hε hx.1, lt_of_le_of_lt hx.2 ha'a⟩
    have hfcont : ContinuousOn f (Set.Icc ε a') := hf.continuousOn.mono hsub
    have hdcont : ContinuousOn (deriv f) (Set.Icc ε a') :=
      (hf.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hsub
    have hpow2 : ContinuousOn (fun t : ℝ => t ^ (-(2 + η))) (Set.Icc ε a') :=
      continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le hε hx.1))
    have hpow1 : ContinuousOn (fun t : ℝ => t ^ (-(1 + η))) (Set.Icc ε a') :=
      continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le hε hx.1))
    have hpow0 : ContinuousOn (fun t : ℝ => t ^ (-η)) (Set.Icc ε a') :=
      continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le hε hx.1))
    have hFcont : ContinuousOn (fun t : ℝ => (f t) ^ 2 * t ^ (-(2 + η))) (Set.Icc ε a') :=
      (hfcont.pow 2).mul hpow2
    have hDercont : ContinuousOn (fun t : ℝ => (deriv f t) ^ 2 * t ^ (-η)) (Set.Icc ε a') :=
      (hdcont.pow 2).mul hpow0
    have hΦcont : ContinuousOn Φ (Set.Icc ε a') := by
      rw [hΦ]
      exact (((hfcont.mul hdcont).mul hpow1).const_mul 2).sub (hFcont.const_mul (1 + η))
    have hintL : IntervalIntegrable
        (fun t : ℝ => (1 + η) ^ 2 / 4 * ((f t) ^ 2 * t ^ (-(2 + η)))) volume ε a' :=
      ContinuousOn.intervalIntegrable_of_Icc hle (hFcont.const_mul _)
    have hintR : IntervalIntegrable
        (fun t : ℝ => (deriv f t) ^ 2 * t ^ (-η) + (-(1 + η) / 2) * Φ t) volume ε a' :=
      (ContinuousOn.intervalIntegrable_of_Icc hle hDercont).add
        (ContinuousOn.intervalIntegrable_of_Icc hle (hΦcont.const_mul _))
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hle hintL hintR
      (fun t ht => hpt t ⟨lt_trans hε ht.1, lt_trans ht.2 ha'a⟩)
    rw [intervalIntegral.integral_const_mul] at hmono
    rw [intervalIntegral.integral_add (ContinuousOn.intervalIntegrable_of_Icc hle hDercont)
      (ContinuousOn.intervalIntegrable_of_Icc hle (hΦcont.const_mul _)),
      intervalIntegral.integral_const_mul] at hmono
    have hFTC : (∫ t in ε..a', Φ t) = G a' - G ε := by
      refine intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hle ?_ ?_ ?_
      · rw [hG]; exact (hfcont.pow 2).mul hpow1
      · intro x hx
        exact hGderiv x ⟨lt_trans hε hx.1, lt_trans hx.2 ha'a⟩
      · exact ContinuousOn.intervalIntegrable_of_Icc hle hΦcont
    rw [hFTC] at hmono
    have hGa' : 0 ≤ G a' := mul_nonneg (sq_nonneg _)
      (Real.rpow_nonneg (le_of_lt (lt_trans hε hεa')) _)
    have hexp : -(1 + η) / 2 * (G a' - G ε) = (1 + η) / 2 * G ε - (1 + η) / 2 * G a' := by ring
    rw [hexp] at hmono
    have hdrop : 0 ≤ (1 + η) / 2 * G a' := mul_nonneg (by linarith) hGa'
    linarith [hmono, hdrop]
  -- ### Step 2: the boundary term at `0` can be made small
  have claim : ∀ lam : ℝ, 0 < lam → ∀ δ : ℝ, 0 < δ → δ ≤ a →
      ∃ ε ∈ Set.Ioo (0 : ℝ) δ, G ε < lam := by
    intro lam hlam δ hδ hδa
    by_contra hcon
    push_neg at hcon
    have hI : IntegrableOn (fun t : ℝ => (f t) ^ 2 * t ^ (-(2 + η)) / lam) (Set.Ioo 0 δ) :=
      (hInt2.mono_set (Set.Ioo_subset_Ioo le_rfl hδa)).div_const lam
    have hmeas : AEStronglyMeasurable (fun t : ℝ => t ^ (-1 : ℝ))
        (volume.restrict (Set.Ioo 0 δ)) :=
      ContinuousOn.aestronglyMeasurable
        (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx.1)) measurableSet_Ioo
    have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioo 0 δ)),
        ‖t ^ (-1 : ℝ)‖ ≤ (f t) ^ 2 * t ^ (-(2 + η)) / lam := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have htpos : 0 < t := ht.1
      have h1 : lam ≤ G t := hcon t ht
      have hrw : t ^ (-(2 + η)) = t ^ (-(1 + η)) * t ^ (-1 : ℝ) := by
        rw [← Real.rpow_add htpos]; congr 1; ring
      have hinv : (0 : ℝ) < t ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one]; exact inv_pos.mpr htpos
      have h2 : lam * t ^ (-1 : ℝ) ≤ ((f t) ^ 2 * t ^ (-(1 + η))) * t ^ (-1 : ℝ) :=
        mul_le_mul_of_nonneg_right h1 hinv.le
      rw [Real.norm_of_nonneg (Real.rpow_nonneg htpos.le _), hrw, le_div_iff₀ hlam]
      linarith [h2]
    have hint : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Set.Ioo 0 δ) := hI.mono' hmeas hbound
    have hnot : ¬ IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Set.Ioo 0 δ) := by
      rw [intervalIntegral.integrableOn_Ioo_rpow_iff hδ]
      norm_num
    exact hnot hint
  -- ### Step 3: the sequence, the truncated upper endpoints, and the limits
  have hseq : ∀ n : ℕ, ∃ ε : ℝ, ε ∈ Set.Ioo (0 : ℝ) (min (a / 2) (1 / ((n : ℝ) + 1)))
      ∧ G ε < 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < min (a / 2) (1 / ((n : ℝ) + 1)) :=
      lt_min (by linarith) (by positivity)
    exact claim (1 / ((n : ℝ) + 1)) (by positivity) _ hpos
      (le_trans (min_le_left _ _) (by linarith))
  choose ε hε using hseq
  have hεpos : ∀ n, 0 < ε n := fun n => (hε n).1.1
  have hεhalf : ∀ n, ε n < a / 2 := fun n =>
    lt_of_lt_of_le (hε n).1.2 (min_le_left _ _)
  have hGsmall : ∀ n, G (ε n) < 1 / ((n : ℝ) + 1) := fun n => (hε n).2
  have han_pos : ∀ n : ℕ, (0 : ℝ) < a - a / ((n : ℝ) + 2) := by
    intro n
    have hb : ((n : ℝ) + 2) ≠ 0 := by positivity
    have h : a - a / ((n : ℝ) + 2) = a * ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
      field_simp; ring
    rw [h]; positivity
  have han_lt : ∀ n : ℕ, a - a / ((n : ℝ) + 2) < a := by
    intro n
    have h : (0 : ℝ) < a / ((n : ℝ) + 2) := by positivity
    linarith
  have hεan : ∀ n : ℕ, ε n < a - a / ((n : ℝ) + 2) := by
    intro n
    have h2 : (2 : ℝ) ≤ (n : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have h3 : a / ((n : ℝ) + 2) ≤ a / 2 := by
      have h4 : 1 / ((n : ℝ) + 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
      calc a / ((n : ℝ) + 2) = a * (1 / ((n : ℝ) + 2)) := by ring
        _ ≤ a * (1 / 2) := mul_le_mul_of_nonneg_left h4 ha.le
        _ = a / 2 := by ring
    linarith [hεhalf n, h3]
  -- the two primitives are continuous on `[0,a]`
  have hFint : IntervalIntegrable (fun t : ℝ => (f t) ^ 2 * t ^ (-(2 + η))) volume 0 a := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le]
    exact hInt2.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hDint : IntervalIntegrable (fun t : ℝ => (deriv f t) ^ 2 * t ^ (-η)) volume 0 a := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le]
    exact hInt1.congr_set_ae MeasureTheory.Ioo_ae_eq_Ioc.symm
  have hFprim : ContinuousOn (fun b : ℝ => ∫ t in (0 : ℝ)..b, (f t) ^ 2 * t ^ (-(2 + η)))
      (Set.Icc 0 a) := by
    rw [← Set.uIcc_of_le ha.le]
    exact intervalIntegral.continuousOn_primitive_interval' hFint left_mem_uIcc
  have hDprim : ContinuousOn (fun b : ℝ => ∫ t in (0 : ℝ)..b, (deriv f t) ^ 2 * t ^ (-η))
      (Set.Icc 0 a) := by
    rw [← Set.uIcc_of_le ha.le]
    exact intervalIntegral.continuousOn_primitive_interval' hDint left_mem_uIcc
  -- limits of the truncated integrals
  have hsmall : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsmall2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) hsmall
    exact one_div_le_one_div_of_le (by positivity) (by push_cast; linarith)
  have han_tend : Tendsto (fun n : ℕ => a - a / ((n : ℝ) + 2)) atTop (𝓝 a) := by
    have h : Tendsto (fun n : ℕ => a / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h2 := hsmall2.const_mul a
      simpa [div_eq_mul_inv, mul_comm] using h2
    simpa using tendsto_const_nhds.sub h
  have han_within : Tendsto (fun n : ℕ => a - a / ((n : ℝ) + 2)) atTop (𝓝[Set.Icc 0 a] a) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨han_tend, ?_⟩
    filter_upwards with n
    exact ⟨(han_pos n).le, (han_lt n).le⟩
  have heps_within : Tendsto (fun n : ℕ => ε n) atTop (𝓝[Set.Icc 0 a] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · refine squeeze_zero (fun n => (hεpos n).le) (fun n => ?_) hsmall
      exact le_of_lt (lt_of_lt_of_le (hε n).1.2 (min_le_right _ _))
    · filter_upwards with n
      exact ⟨(hεpos n).le, (hεhalf n).le.trans (by linarith)⟩
  have hFlim_n : Tendsto (fun n : ℕ => ∫ t in (0 : ℝ)..(a - a / ((n : ℝ) + 2)),
      (f t) ^ 2 * t ^ (-(2 + η))) atTop (𝓝 (∫ t in (0 : ℝ)..a, (f t) ^ 2 * t ^ (-(2 + η)))) :=
    (hFprim.continuousWithinAt (by exact ⟨ha.le, le_rfl⟩)).tendsto.comp han_within
  have hFlim_eps : Tendsto (fun n : ℕ => ∫ t in (0 : ℝ)..(ε n),
      (f t) ^ 2 * t ^ (-(2 + η))) atTop (𝓝 (∫ t in (0 : ℝ)..(0 : ℝ),
        (f t) ^ 2 * t ^ (-(2 + η)))) :=
    (hFprim.continuousWithinAt (by exact ⟨le_rfl, ha.le⟩)).tendsto.comp heps_within
  have hDlim_n : Tendsto (fun n : ℕ => ∫ t in (0 : ℝ)..(a - a / ((n : ℝ) + 2)),
      (deriv f t) ^ 2 * t ^ (-η)) atTop (𝓝 (∫ t in (0 : ℝ)..a, (deriv f t) ^ 2 * t ^ (-η))) :=
    (hDprim.continuousWithinAt (by exact ⟨ha.le, le_rfl⟩)).tendsto.comp han_within
  have hDlim_eps : Tendsto (fun n : ℕ => ∫ t in (0 : ℝ)..(ε n),
      (deriv f t) ^ 2 * t ^ (-η)) atTop (𝓝 (∫ t in (0 : ℝ)..(0 : ℝ),
        (deriv f t) ^ 2 * t ^ (-η))) :=
    (hDprim.continuousWithinAt (by exact ⟨le_rfl, ha.le⟩)).tendsto.comp heps_within
  -- the per-`n` bound
  have hFsplit : ∀ n : ℕ, (∫ t in (ε n)..(a - a / ((n : ℝ) + 2)),
      (f t) ^ 2 * t ^ (-(2 + η)))
      = (∫ t in (0 : ℝ)..(a - a / ((n : ℝ) + 2)), (f t) ^ 2 * t ^ (-(2 + η)))
        - (∫ t in (0 : ℝ)..(ε n), (f t) ^ 2 * t ^ (-(2 + η))) := by
    intro n
    have h1 : IntervalIntegrable (fun t : ℝ => (f t) ^ 2 * t ^ (-(2 + η))) volume 0 (ε n) := by
      refine hFint.mono_set ?_
      rw [Set.uIcc_of_le (hεpos n).le, Set.uIcc_of_le ha.le]
      exact Set.Icc_subset_Icc le_rfl (by linarith [hεhalf n])
    have h2 : IntervalIntegrable (fun t : ℝ => (f t) ^ 2 * t ^ (-(2 + η))) volume (ε n)
        (a - a / ((n : ℝ) + 2)) :=
      (ContinuousOn.intervalIntegrable_of_Icc (le_of_lt (hεan n)) (by
        have hsub : Set.Icc (ε n) (a - a / ((n : ℝ) + 2)) ⊆ Set.Ioo (0 : ℝ) a := fun x hx =>
          ⟨lt_of_lt_of_le (hεpos n) hx.1, lt_of_le_of_lt hx.2 (han_lt n)⟩
        exact ((hf.continuousOn.mono hsub).pow 2).mul
          (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (hsub hx).1))))
    have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
    linarith [hadd]
  have hDsplit : ∀ n : ℕ, (∫ t in (ε n)..(a - a / ((n : ℝ) + 2)),
      (deriv f t) ^ 2 * t ^ (-η))
      = (∫ t in (0 : ℝ)..(a - a / ((n : ℝ) + 2)), (deriv f t) ^ 2 * t ^ (-η))
        - (∫ t in (0 : ℝ)..(ε n), (deriv f t) ^ 2 * t ^ (-η)) := by
    intro n
    have h1 : IntervalIntegrable (fun t : ℝ => (deriv f t) ^ 2 * t ^ (-η)) volume 0 (ε n) := by
      refine hDint.mono_set ?_
      rw [Set.uIcc_of_le (hεpos n).le, Set.uIcc_of_le ha.le]
      exact Set.Icc_subset_Icc le_rfl (by linarith [hεhalf n])
    have h2 : IntervalIntegrable (fun t : ℝ => (deriv f t) ^ 2 * t ^ (-η)) volume (ε n)
        (a - a / ((n : ℝ) + 2)) := by
      have hsub : Set.Icc (ε n) (a - a / ((n : ℝ) + 2)) ⊆ Set.Ioo (0 : ℝ) a := fun x hx =>
        ⟨lt_of_lt_of_le (hεpos n) hx.1, lt_of_le_of_lt hx.2 (han_lt n)⟩
      exact ContinuousOn.intervalIntegrable_of_Icc (le_of_lt (hεan n))
        (((hf.continuousOn_deriv_of_isOpen isOpen_Ioo le_rfl).mono hsub).pow 2 |>.mul
          (continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt (hsub hx).1)))
    have hadd := intervalIntegral.integral_add_adjacent_intervals h1 h2
    linarith [hadd]
  have hev : ∀ᶠ n : ℕ in atTop,
      (1 + η) ^ 2 / 4 * (∫ t in (ε n)..(a - a / ((n : ℝ) + 2)), (f t) ^ 2 * t ^ (-(2 + η)))
        ≤ (∫ t in (ε n)..(a - a / ((n : ℝ) + 2)), (deriv f t) ^ 2 * t ^ (-η))
          + (1 + η) / 2 * (1 / ((n : ℝ) + 1)) := by
    filter_upwards with n
    have h1 := step1 (ε n) (a - a / ((n : ℝ) + 2)) (hεpos n) (hεan n) (han_lt n)
    have h2 : (1 + η) / 2 * G (ε n) < (1 + η) / 2 * (1 / ((n : ℝ) + 1)) :=
      mul_lt_mul_of_pos_left (hGsmall n) (by linarith)
    linarith [h1, h2]
  -- assemble the limits
  have hzF : (∫ t in (0 : ℝ)..(0 : ℝ), (f t) ^ 2 * t ^ (-(2 + η))) = 0 := by simp
  have hzD : (∫ t in (0 : ℝ)..(0 : ℝ), (deriv f t) ^ 2 * t ^ (-η)) = 0 := by simp
  have hinner : Tendsto (fun n : ℕ => ∫ t in (ε n)..(a - a / ((n : ℝ) + 2)),
      (f t) ^ 2 * t ^ (-(2 + η))) atTop
      (𝓝 (∫ t in (0 : ℝ)..a, (f t) ^ 2 * t ^ (-(2 + η)))) := by
    have hbase : Tendsto (fun n : ℕ => (∫ t in (0 : ℝ)..(a - a / ((n : ℝ) + 2)),
        (f t) ^ 2 * t ^ (-(2 + η))) - (∫ t in (0 : ℝ)..(ε n),
        (f t) ^ 2 * t ^ (-(2 + η)))) atTop
        (𝓝 (∫ t in (0 : ℝ)..a, (f t) ^ 2 * t ^ (-(2 + η)))) := by
      have h := hFlim_n.sub hFlim_eps
      rw [hzF, sub_zero] at h
      exact h
    refine hbase.congr' ?_
    filter_upwards with n
    exact (hFsplit n).symm
  have hinnerD : Tendsto (fun n : ℕ => ∫ t in (ε n)..(a - a / ((n : ℝ) + 2)),
      (deriv f t) ^ 2 * t ^ (-η)) atTop
      (𝓝 (∫ t in (0 : ℝ)..a, (deriv f t) ^ 2 * t ^ (-η))) := by
    have hbase : Tendsto (fun n : ℕ => (∫ t in (0 : ℝ)..(a - a / ((n : ℝ) + 2)),
        (deriv f t) ^ 2 * t ^ (-η)) - (∫ t in (0 : ℝ)..(ε n),
        (deriv f t) ^ 2 * t ^ (-η))) atTop
        (𝓝 (∫ t in (0 : ℝ)..a, (deriv f t) ^ 2 * t ^ (-η))) := by
      have h := hDlim_n.sub hDlim_eps
      rw [hzD, sub_zero] at h
      exact h
    refine hbase.congr' ?_
    filter_upwards with n
    exact (hDsplit n).symm
  have hLHSlim : Tendsto (fun n : ℕ => (1 + η) ^ 2 / 4 * (∫ t in (ε n)..(a - a / ((n : ℝ) + 2)),
      (f t) ^ 2 * t ^ (-(2 + η)))) atTop
      (𝓝 ((1 + η) ^ 2 / 4 * (∫ t in (0 : ℝ)..a, (f t) ^ 2 * t ^ (-(2 + η))))) :=
    hinner.const_mul _
  have hRHSlim : Tendsto (fun n : ℕ => (∫ t in (ε n)..(a - a / ((n : ℝ) + 2)),
      (deriv f t) ^ 2 * t ^ (-η)) + (1 + η) / 2 * (1 / ((n : ℝ) + 1))) atTop
      (𝓝 ((∫ t in (0 : ℝ)..a, (deriv f t) ^ 2 * t ^ (-η)) + (1 + η) / 2 * 0)) :=
    hinnerD.add (hsmall.const_mul _)
  have hkey : (1 + η) ^ 2 / 4 * (∫ t in (0 : ℝ)..a, (f t) ^ 2 * t ^ (-(2 + η)))
      ≤ ∫ t in (0 : ℝ)..a, (deriv f t) ^ 2 * t ^ (-η) := by
    have h := le_of_tendsto_of_tendsto hLHSlim hRHSlim hev
    simpa using h
  have hstep : (4 / (1 + η) ^ 2)
      * ((1 + η) ^ 2 / 4 * (∫ t in (0 : ℝ)..a, (f t) ^ 2 * t ^ (-(2 + η))))
      = ∫ t in (0 : ℝ)..a, (f t) ^ 2 * t ^ (-(2 + η)) := by
    field_simp
  calc (∫ t in (0 : ℝ)..a, (f t) ^ 2 * t ^ (-(2 + η)))
      = (4 / (1 + η) ^ 2)
          * ((1 + η) ^ 2 / 4 * (∫ t in (0 : ℝ)..a, (f t) ^ 2 * t ^ (-(2 + η)))) := hstep.symm
    _ ≤ (4 / (1 + η) ^ 2) * (∫ t in (0 : ℝ)..a, (deriv f t) ^ 2 * t ^ (-η)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)

/-- **The sharp power-weight Hardy inequality on the open interval `(0,a)`.**

For `a > 0`, `0 ≤ η < 1` and `f` of class `C¹` on `(0,a)` with both weighted energies finite,

  `∫_0^a f(t)² t^{-(2+η)} dt ≤ 4/(1+η)² ∫_0^a (f'(t))² t^{-η} dt`.

The constant `4/(1+η)²` is the classical sharp constant, saturated in the limit by
`t ↦ t^s`, `s ↘ (1+η)/2`.  No boundary condition at `0` is required: the finiteness of
`∫ f² t^{-(2+η)}` forces `liminf_{t→0⁺} f(t)² t^{-(1+η)} = 0`. -/
theorem powerHardyOpen {a η : ℝ} (ha : 0 < a) (hη0 : 0 ≤ η) (hη1 : η < 1) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 1 f (Set.Ioo 0 a))
    (hInt2 : MeasureTheory.IntegrableOn (fun t : ℝ => (f t) ^ 2 * t ^ (-(2 + η))) (Set.Ioo 0 a))
    (hInt1 : MeasureTheory.IntegrableOn (fun t : ℝ => (deriv f t) ^ 2 * t ^ (-η)) (Set.Ioo 0 a)) :
    (∫ t in Set.Ioo 0 a, (f t) ^ 2 * t ^ (-(2 + η)))
      ≤ 4 / (1 + η) ^ 2 * ∫ t in Set.Ioo 0 a, (deriv f t) ^ 2 * t ^ (-η) := by
  have e1 : (∫ t in Set.Ioo 0 a, (f t) ^ 2 * t ^ (-(2 + η)))
      = ∫ t in (0 : ℝ)..a, (f t) ^ 2 * t ^ (-(2 + η)) := by
    rw [intervalIntegral.integral_of_le ha.le]
    exact setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Ioc
  have e2 : (∫ t in Set.Ioo 0 a, (deriv f t) ^ 2 * t ^ (-η))
      = ∫ t in (0 : ℝ)..a, (deriv f t) ^ 2 * t ^ (-η) := by
    rw [intervalIntegral.integral_of_le ha.le]
    exact setIntegral_congr_set MeasureTheory.Ioo_ae_eq_Ioc
  rw [e1, e2]
  exact powerHardyOpen_interval ha hη0 hη1 hf hInt2 hInt1

end Work.FTS.EllipticEst.H2W.AeWAux
