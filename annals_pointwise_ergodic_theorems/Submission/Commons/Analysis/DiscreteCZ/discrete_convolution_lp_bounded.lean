import Mathlib
import Submission.Commons.Analysis.DiscreteCZ.discrete_convolution_weak_type_one
import Submission.Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_integrable_explicit
import Submission.Commons.Analysis.InfiniteSum.tendsto_sum_Icc_tsum
import Submission.Port.Aesm

open MeasureTheory Filter
open scoped ENNReal BigOperators

namespace Commons.Analysis.DiscreteCZ

noncomputable section

set_option autoImplicit false

/-- For a summable family indexed by `ℤ` with values in a seminormed additive commutative group,
the partial sums over the symmetric intervals `[-N,N]` converge to the full `tsum`. -/
theorem tendsto_sum_Icc_tsum_int {E : Type*} [SeminormedAddCommGroup E]
    (c : ℤ → E) (hc : Summable c) :
    Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), c m)
      Filter.atTop (nhds (∑' m, c m)) :=
  hc.hasSum.comp Commons.Analysis.InfiniteSum.tendsto_finset_Icc_int_atTop

/-- Fatou's lemma for `eLpNorm` on `ℤ` with the counting measure. -/
theorem eLpNorm_le_liminf_of_enorm_le_liminf {E : Type*} [SeminormedAddCommGroup E]
    {q : ℝ} (hq : 0 < q) {u : ℕ → ℤ → E} {U : ℤ → E}
    (h : ∀ x : ℤ, ‖U x‖ₑ ≤ Filter.liminf (fun n => ‖u n x‖ₑ) Filter.atTop) :
    eLpNorm U (ENNReal.ofReal q) (Measure.count : Measure ℤ)
      ≤ Filter.liminf (fun n => eLpNorm (u n) (ENNReal.ofReal q)
          (Measure.count : Measure ℤ)) Filter.atTop := by
  have hqne : (ENNReal.ofReal q) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hq
  have hqtop : (ENNReal.ofReal q) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hU : eLpNorm U (ENNReal.ofReal q) (Measure.count : Measure ℤ)
      = (∫⁻ x : ℤ, ‖U x‖ₑ ^ q ∂(Measure.count : Measure ℤ)) ^ (1/q) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hqne hqtop, ENNReal.toReal_ofReal hq.le]
  have hu : ∀ n, eLpNorm (u n) (ENNReal.ofReal q) (Measure.count : Measure ℤ)
      = (∫⁻ x : ℤ, ‖u n x‖ₑ ^ q ∂(Measure.count : Measure ℤ)) ^ (1/q) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hqne hqtop, ENNReal.toReal_ofReal hq.le]
  rw [hU]
  simp_rw [hu]
  have hliminf_rpow :
      (Filter.liminf (fun n => ∫⁻ x : ℤ, ‖u n x‖ₑ ^ q ∂(Measure.count : Measure ℤ))
          Filter.atTop) ^ (1/q)
      = Filter.liminf (fun n => (∫⁻ x : ℤ, ‖u n x‖ₑ ^ q
          ∂(Measure.count : Measure ℤ)) ^ (1/q)) Filter.atTop :=
    (ENNReal.orderIsoRpow (1/q) (by positivity)).liminf_apply
  rw [← hliminf_rpow]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  have hpt : ∀ x : ℤ, ‖U x‖ₑ ^ q ≤ Filter.liminf (fun n => ‖u n x‖ₑ ^ q) Filter.atTop := by
    intro x
    have hx : Filter.liminf (fun n => ‖u n x‖ₑ) Filter.atTop ^ q
        = Filter.liminf (fun n => ‖u n x‖ₑ ^ q) Filter.atTop :=
      (ENNReal.orderIsoRpow q hq).liminf_apply
    rw [← hx]
    exact ENNReal.rpow_le_rpow (h x) hq.le
  refine le_trans (lintegral_mono hpt) ?_
  refine lintegral_liminf_le' ?_
  intro n
  exact (measurable_of_countable (fun x : ℤ => ‖u n x‖ₑ ^ q)).aemeasurable


/-- Auxiliary `rpow` identity used to normalise the Marcinkiewicz constant. -/
theorem rpow_marcinkiewicz_const {A0 A2 p : ℝ} (hA0 : 0 < A0) (hA2 : 0 < A2) :
    (A0 / A2 ^ 2) ^ (1 / p - 1) * A0 ^ (1 / p) = A0 ^ (2 / p - 1) * A2 ^ (2 - 2 / p) := by
  have hA2sq : (0 : ℝ) < A2 ^ 2 := by positivity
  rw [Real.div_rpow hA0.le hA2sq.le]
  rw [div_eq_mul_inv, ← Real.rpow_neg hA2sq.le (1 / p - 1)]
  rw [show (A2 ^ 2) ^ (-(1 / p - 1)) = A2 ^ (2 - 2 / p) from by
    rw [show A2 ^ 2 = A2 ^ (2 : ℝ) from by rw [Real.rpow_ofNat]]
    rw [← Real.rpow_mul hA2.le 2 (-(1 / p - 1))]
    congr 1; ring]
  rw [show A0 ^ (1 / p - 1) * A2 ^ (2 - 2 / p) * A0 ^ (1 / p)
        = A0 ^ (2 / p - 1) * A2 ^ (2 - 2 / p) from by
    rw [mul_comm (A0 ^ (1 / p - 1)) (A2 ^ (2 - 2 / p)), mul_assoc,
      ← Real.rpow_add hA0 (1 / p - 1) (1 / p),
      mul_comm (A2 ^ (2 - 2 / p)) (A0 ^ (1 / p - 1 + 1 / p))]
    congr 1; ring]

/-- **The discrete Calderón--Zygmund `ℓᵖ` bound on `ℤ`.**  Under the same size, Hörmander and
`ℓ²`-boundedness hypotheses as `Commons.Analysis.DiscreteCZ.discrete_convolution_weak_type_one`
(`K` bounded by `Bk`, `∑_{2|y| ≤ |x|} ‖K (x - y) - K x‖ ≤ Ak`, `‖T‖_{ℓ²→ℓ²} ≤ A2`), the
convolution operator `T f x = ∑'_y K (x - y) • f y` is bounded on `ℓᵖ(ℤ; H)` for `1 < p < 2`,
with constant controlled by the Marcinkiewicz expression
`C (24 A2² + 4 Ak + 100)^{2/p - 1} A2^{2 - 2/p}`.  The proof interpolates the weak-type `(1,1)`
bound with the strong `(2,2)` bound; in the standard interpolation argument the level sets of `f`
are split into `f·1_{‖f‖ > α} ∈ ℓ¹` (which is summable because `∑ ‖f‖ ≤ α^{1-p} ∑ ‖f‖^p`) and
`f·1_{‖f‖ ≤ α} ∈ ℓ²` (because `∑ ‖f‖² ≤ α^{2-p} ∑ ‖f‖^p`), so that only the summable-input
hypotheses are needed.  The case `p > 2` follows by duality. -/
theorem discrete_convolution_lp_bounded {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] {p : ℝ} (hp : 1 < p) (hp2 : p < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℤ → ℂ) (A2 Ak Bk : ℝ), 0 < A2 → 0 ≤ Ak →
      (∀ z : ℤ, ‖K z‖ ≤ Bk) →
      (∀ y : ℤ, y ≠ 0 → ∫⁻ x in {x : ℤ | 2 * y.natAbs ≤ x.natAbs},
          ‖K (x - y) - K x‖ₑ ∂MeasureTheory.Measure.count ≤ ENNReal.ofReal Ak) →
      (∀ f : ℤ → H, Summable f →
        MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, K (x - y) • f y) 2
            MeasureTheory.Measure.count
          ≤ ENNReal.ofReal A2
            * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) →
      ∀ f : ℤ → H, Summable (fun n : ℤ => ‖f n‖ ^ p) →
        MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, K (x - y) • f y) (ENNReal.ofReal p)
            MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * (24 * A2 ^ 2 + 4 * Ak + 100) ^ (2 / p - 1)
              * A2 ^ (2 - 2 / p))
            * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  classical
  set M : ℝ := 12 * 2 ^ (p - 1) / (p - 1) + 16 / (2 - p) with hMdef
  have hp1' : 0 < p - 1 := by linarith
  have hp2' : 0 < 2 - p := by linarith
  have hMpos : 0 < M := by
    rw [hMdef]
    have h1 : 0 < (2:ℝ) ^ (p - 1) := Real.rpow_pos_of_pos (by norm_num) (p - 1)
    have h2 : 0 < 12 * (2:ℝ) ^ (p - 1) / (p - 1) :=
      div_pos (mul_pos (by norm_num) h1) hp1'
    have h3 : 0 < 16 / (2 - p) := div_pos (by norm_num) hp2'
    linarith
  refine ⟨M ^ (1 / p), Real.rpow_pos_of_pos hMpos _, ?_⟩
  intro K A2 Ak Bk hA2 hAk hKbdd hker hstrong f hf
  set A0 : ℝ := 24 * A2 ^ 2 + 4 * Ak + 100 with hA0def
  have hA0pos : 0 < A0 := by rw [hA0def]; positivity
  let T : (ℤ → H) → (ℤ → H) := fun g => fun x => ∑' y : ℤ, K (x - y) • g y
  -- Small pieces
  have hweak1 : ∀ (g : ℤ → H) (lam : ℝ), Integrable g (Measure.count : Measure ℤ) → 0 < lam →
      Measure.count {x : ℤ | lam < ‖T g x‖}
        ≤ ENNReal.ofReal (A0 / lam) * eLpNorm g 1 (Measure.count : Measure ℤ) := by
    intro g lam hg hlam
    have hgsum : Summable g := Summable.of_norm (integrable_count_iff.mp hg)
    have h := discrete_convolution_weak_type_one (H := H) K A2 Ak Bk hA2 hAk hKbdd hker hstrong
      g hgsum lam hlam
    rw [hA0def]
    simpa only [T] using h
  have hstrong1 : ∀ g : ℤ → H, Integrable g (Measure.count : Measure ℤ) →
      eLpNorm (T g) 2 (Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal A2 * eLpNorm g 2 (Measure.count : Measure ℤ) := by
    intro g hg
    have hgsum : Summable g := Summable.of_norm (integrable_count_iff.mp hg)
    have h := hstrong g hgsum
    simpa only [T] using h
  have hsumm_smul : ∀ (u : ℤ → H) (x : ℤ), Summable (fun y : ℤ => ‖u y‖) →
      Summable (fun y : ℤ => K (x - y) • u y) := by
    intro u x hu
    refine Summable.of_norm_bounded (hu.mul_left Bk) (fun y => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hKbdd (x - y)) (norm_nonneg _)
  have hadd : ∀ f g : ℤ → H, Integrable f (Measure.count : Measure ℤ) →
      Integrable g (Measure.count : Measure ℤ) → T (f + g) = T f + T g := by
    intro f g hf hg
    funext x
    have hfs : Summable (fun y : ℤ => K (x - y) • f y) :=
      hsumm_smul f x (integrable_count_iff.mp hf)
    have hgs : Summable (fun y : ℤ => K (x - y) • g y) :=
      hsumm_smul g x (integrable_count_iff.mp hg)
    show (∑' y : ℤ, K (x - y) • (f y + g y))
        = (∑' y : ℤ, K (x - y) • f y) + (∑' y : ℤ, K (x - y) • g y)
    rw [show (∑' y : ℤ, K (x - y) • (f y + g y))
          = ∑' y : ℤ, (K (x - y) • f y + K (x - y) • g y) from
        tsum_congr (fun y => smul_add _ _ _)]
    exact Summable.tsum_add hfs hgs
  -- The ℓ¹ bound with the optimised (factorised) constant, via rescaling.
  have hℓ1 : ∀ g : ℤ → H, Integrable g (Measure.count : Measure ℤ) →
      eLpNorm (T g) (ENNReal.ofReal p) (Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal (M ^ (1 / p) * A0 ^ (2 / p - 1) * A2 ^ (2 - 2 / p))
          * eLpNorm g (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
    intro g hg
    set α : ℝ := A0 / A2 ^ 2 with hαdef
    have hαpos : 0 < α := by rw [hαdef]; positivity
    have hαA2 : α * A2 ^ 2 = A0 := by
      rw [hαdef]
      exact div_mul_cancel₀ A0 (pow_ne_zero 2 hA2.ne')
    have hαA0pos : 0 < α * A0 := mul_pos hαpos hA0pos
    letI : MeasurableSpace H := borel H
    let Tc : (ℤ → H) → (ℤ → H) := fun g => (α : ℂ) • (T g)
    have hTc_add : ∀ f g : ℤ → H, Integrable f (Measure.count : Measure ℤ) →
        Integrable g (Measure.count : Measure ℤ) → Tc (f + g) = Tc f + Tc g := by
      intro f g hf hg
      show (α : ℂ) • (T (f + g)) = (α : ℂ) • T f + (α : ℂ) • T g
      rw [hadd f g hf hg, smul_add]
    have hTc_weak : ∀ (f : ℤ → H) (lam : ℝ), Integrable f (Measure.count : Measure ℤ) →
        0 < lam → Measure.count {x : ℤ | lam < ‖Tc f x‖}
          ≤ ENNReal.ofReal (α * A0 / lam) * eLpNorm f 1 (Measure.count : Measure ℤ) := by
      intro f lam hf' hlam
      have hset : {x : ℤ | lam < ‖Tc f x‖} = {x : ℤ | lam / α < ‖T f x‖} := by
        ext x
        show lam < ‖(α : ℂ) • T f x‖ ↔ lam / α < ‖T f x‖
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hαpos,
          div_lt_iff₀ hαpos, mul_comm]
      rw [hset]
      have h1 := hweak1 f (lam / α) hf' (div_pos hlam hαpos)
      refine h1.trans ?_
      refine mul_le_mul_left ?_ _
      apply ENNReal.ofReal_le_ofReal
      rw [div_div_eq_mul_div]
      exact le_of_eq (by ring)
    have hTc_strong : ∀ f : ℤ → H, Integrable f (Measure.count : Measure ℤ) →
        eLpNorm (Tc f) 2 (Measure.count : Measure ℤ)
          ≤ ENNReal.ofReal (α * A2) * eLpNorm f 2 (Measure.count : Measure ℤ) := by
      intro f hf'
      show eLpNorm ((α : ℂ) • (T f)) 2 (Measure.count : Measure ℤ) ≤ _
      rw [eLpNorm_const_smul, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hαpos, ENNReal.ofReal_mul hαpos.le, mul_assoc]
      gcongr
      exact hstrong1 f hf'
    have hbnd := Commons.Analysis.MeasureTheory.marcinkiewicz_weak_one_strong_two_integrable_explicit
      (α := ℤ) (β := ℤ) (E := H) (μ := Measure.count) (ν := Measure.count)
      Tc hTc_add hαA0pos (mul_pos hαpos hA2) hTc_weak hTc_strong hp hp2 g hg
    rw [show Tc g = (α : ℂ) • (T g) from rfl, eLpNorm_const_smul, ← ofReal_norm,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hαpos] at hbnd
    -- normalise the constant
    have hα1 : α⁻¹ * α ^ (1 / p) = α ^ (1 / p - 1) := by
      have hαm1 : α ^ (-(1 : ℝ)) = α⁻¹ := by rw [Real.rpow_neg hαpos.le, Real.rpow_one]
      rw [← hαm1, ← Real.rpow_add hαpos (-(1 : ℝ)) (1 / p)]
      congr 1; ring
    have hαinvB : α⁻¹ * (12 * (α * A0) * 2 ^ (p - 1) / (p - 1)
          + 16 * (α * A2) ^ 2 / (2 - p)) ^ (1 / p)
        = M ^ (1 / p) * A0 ^ (2 / p - 1) * A2 ^ (2 - 2 / p) := by
      have hbr : 12 * (α * A0) * 2 ^ (p - 1) / (p - 1) + 16 * (α * A2) ^ 2 / (2 - p)
          = M * (α * A0) := by
        have h1 : (α * A2) ^ 2 = α * (α * A2 ^ 2) := by ring
        rw [h1, hαA2, hMdef]
        ring
      rw [hbr, Real.mul_rpow hMpos.le hαA0pos.le, Real.mul_rpow hαpos.le hA0pos.le]
      calc α⁻¹ * (M ^ (1 / p) * (α ^ (1 / p) * A0 ^ (1 / p)))
          = M ^ (1 / p) * ((α⁻¹ * α ^ (1 / p)) * A0 ^ (1 / p)) := by ring
        _ = M ^ (1 / p) * (α ^ (1 / p - 1) * A0 ^ (1 / p)) := by rw [hα1]
        _ = M ^ (1 / p) * (A0 ^ (2 / p - 1) * A2 ^ (2 - 2 / p)) := by
              rw [hαdef, rpow_marcinkiewicz_const hA0pos hA2]
        _ = M ^ (1 / p) * A0 ^ (2 / p - 1) * A2 ^ (2 - 2 / p) := by ring
    have hB : (12 * (α * A0) * 2 ^ (p - 1) / (p - 1) + 16 * (α * A2) ^ 2 / (2 - p)) ^ (1 / p)
        = α * (M ^ (1 / p) * A0 ^ (2 / p - 1) * A2 ^ (2 - 2 / p)) := by
      have hαmul : α * (α⁻¹ * (12 * (α * A0) * 2 ^ (p - 1) / (p - 1)
            + 16 * (α * A2) ^ 2 / (2 - p)) ^ (1 / p))
          = (12 * (α * A0) * 2 ^ (p - 1) / (p - 1)
            + 16 * (α * A2) ^ 2 / (2 - p)) ^ (1 / p) := by
        rw [← mul_assoc, mul_inv_cancel₀ hαpos.ne', one_mul]
      rw [hαmul.symm, hαinvB]
    rw [hB, ENNReal.ofReal_mul hαpos.le, mul_assoc] at hbnd
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_ne_zero_iff.mpr hαpos)
      ENNReal.ofReal_ne_top).mp hbnd
  -- Extend from ℓ¹ to ℓᵖ by Fatou along truncations.
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  by_cases hfin : eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ) = ⊤
  · rw [hfin, ENNReal.mul_top]
    · exact le_top
    · exact ENNReal.ofReal_ne_zero_iff.mpr (by
        have : 0 < M ^ (1 / p) * A0 ^ (2 / p - 1) * A2 ^ (2 - 2 / p) :=
          mul_pos (mul_pos (Real.rpow_pos_of_pos hMpos _) (Real.rpow_pos_of_pos hA0pos _))
            (Real.rpow_pos_of_pos hA2 _)
        linarith)
  · have hflt : eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ) < ⊤ :=
      lt_top_iff_ne_top.mpr hfin
    let fN : ℕ → ℤ → H := fun N n => if n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) then f n else 0
    have hfN_int : ∀ N, Integrable (fN N) (Measure.count : Measure ℤ) := by
      intro N
      rw [integrable_count_iff]
      refine summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ)) (N : ℤ)) (fun n hn => ?_)
      simp only [fN]; rw [if_neg hn, norm_zero]
    have hpartial : ∀ N x, T (fN N) x
        = ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), K (x - m) • f m := by
      intro N x
      show (∑' y : ℤ, K (x - y) • fN N y) = _
      rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) (N : ℤ))
        (f := fun y : ℤ => K (x - y) • fN N y) (fun y hy => by
          simp only [fN]; rw [if_neg hy, smul_zero])]
      exact Finset.sum_congr rfl (fun m hm => by simp only [fN]; rw [if_pos hm])
    have hpoint : ∀ x : ℤ, ‖T f x‖ₑ ≤ Filter.liminf (fun N => ‖T (fN N) x‖ₑ) Filter.atTop := by
      intro x
      by_cases hx : Summable (fun y : ℤ => K (x - y) • f y)
      · have hconv : Filter.Tendsto (fun N => T (fN N) x) Filter.atTop (nhds (T f x)) := by
          have h1 := tendsto_sum_Icc_tsum_int (fun y : ℤ => K (x - y) • f y) hx
          rw [show (∑' m : ℤ, K (x - m) • f m) = T f x from rfl] at h1
          exact h1.congr (fun N => (hpartial N x).symm)
        have h4 : Filter.Tendsto (fun N => ‖T (fN N) x‖ₑ) Filter.atTop (nhds ‖T f x‖ₑ) :=
          (continuous_enorm.tendsto (T f x)).comp hconv
        rw [h4.liminf_eq]
      · have h0 : T f x = 0 := tsum_eq_zero_of_not_summable hx
        rw [h0, enorm_zero]
        exact bot_le
    have hboundN : ∀ N, eLpNorm (T (fN N)) (ENNReal.ofReal p) (Measure.count : Measure ℤ)
        ≤ ENNReal.ofReal (M ^ (1 / p) * A0 ^ (2 / p - 1) * A2 ^ (2 - 2 / p))
          * eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
      intro N
      refine (hℓ1 (fN N) (hfN_int N)).trans ?_
      gcongr
      refine eLpNorm_mono (hf := by pw_aesm) (fun n => ?_)
      simp only [fN]
      by_cases hn : n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)
      · rw [if_pos hn]
      · rw [if_neg hn, norm_zero]; positivity
    refine (eLpNorm_le_liminf_of_enorm_le_liminf (E := H) hp0 hpoint).trans ?_
    refine Filter.liminf_le_of_le (by isBoundedDefault) ?_
    intro b hb
    obtain ⟨N, hN⟩ := hb.exists
    exact le_trans hN (hboundN N)

end

end Commons.Analysis.DiscreteCZ
