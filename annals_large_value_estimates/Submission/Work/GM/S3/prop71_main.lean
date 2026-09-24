import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.Iterm_eq_integral
import Submission.Work.GM.S3.osc_integral_decay
import Submission.Work.GM.S3.prop71_defs
import Submission.Work.GM.S3.prop71_inner_uniform
import Submission.Work.GM.S3.prop71_inner_support
import Submission.Work.GM.S3.prop71_inner_decay
import Submission.Work.GM.S3.prop71_inner_tail
import Submission.Work.GM.S3.prop71_pbox_measure
import Submission.Work.GM.S3.prop71_box_integral_bound
import Submission.Work.GM.S3.prop71_card_bound
import Submission.Work.GM.S3.prop71_tail_arith
import Submission.Work.GM.S3.prop71_final_arith
import Submission.Work.GM.S3.prop71_rhs_domination

/-!
# GM Proposition 7.1: the key cancellation inside the `I_m` integrals

This file proves `Work.GM.S3.prop71_main`, the main estimate of GM Prop 7.1.

* `Iterm_eq_vint`: the change of variables `v₁ = u₁/u₃`, `v₂ = u₂/u₃` in the integral
  representation `Iterm_eq_integral` of `Iterm` (GM (7.3)), turning the triple integral into
  `N³ ∫_v R(v₁)R(v₂/v₁)R(1/v₂) · innerInt(v) dv` (`innerInt` is the oscillatory `u₃`-integral).
* `norm_Iterm_le`: `‖Iterm‖ ≤ N³ ∫_v ‖Rprod v‖ ‖innerInt v‖`.
* `prop71_main`: the estimate itself, assembled from `prop71_box_integral_bound` (split of the
  `v`-integral into the stationary set `|m₁v₁+m₂v₂+m₃| ≤ (M N)^η/N` and its complement),
  `prop71_inner_uniform` (`≪ 1` on the stationary set), `prop71_inner_decay` /
  `prop71_inner_tail` (`O((N|phas|)^{-j})` off it), `prop71_tail_arith` (choosing
  `j ≈ 133/(6η)` makes the error `O(N^{-20})`), `prop71_card_bound` (`|W| ≤ 2 M N`) and
  `prop71_final_arith` (the final bookkeeping).
-/

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators
open Submission.GM (Rfun Separated Iterm hhat hfun)
open Submission.LargeValues

theorem measurable_bumpW : Measurable bumpW := bumpW_contDiff.continuous.measurable

theorem mem_Icc_of_w2C_ne_zero {x : ℝ} (h : w2C x ≠ 0) : x ∈ Set.Icc (1 : ℝ) 2 := by
  rw [w2C_eq] at h
  have hb : bumpW x ≠ 0 := by
    intro hb'
    exact h (by rw [hb']; norm_num)
  exact bumpW_spec.2.2.1 x hb

theorem norm_IFun_le (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) (u : ℝ × ℝ × ℝ) :
    ‖IFun N W m u‖ ≤ Cw ^ 6 * (W.card : ℝ) ^ 3 := by
  have hA : ‖(((Real.fourierChar (-((N : ℝ) * ((m.1 : ℝ) * u.1 + (m.2.1 : ℝ) * u.2.1 +
      (m.2.2 : ℝ) * u.2.2))) : Circle)) : ℂ)‖ = 1 := Circle.norm_coe _
  have hB : ‖w2C u.1‖ ≤ Cw ^ 2 := norm_w2C_le u.1
  have hC : ‖w2C u.2.1‖ ≤ Cw ^ 2 := norm_w2C_le u.2.1
  have hD : ‖w2C u.2.2‖ ≤ Cw ^ 2 := norm_w2C_le u.2.2
  have hE : ‖Rfun W (u.1 / u.2.2)‖ ≤ (W.card : ℝ) := Rfun_norm_le_card W _
  have hF : ‖Rfun W (u.2.1 / u.1)‖ ≤ (W.card : ℝ) := Rfun_norm_le_card W _
  have hG : ‖Rfun W (u.2.2 / u.2.1)‖ ≤ (W.card : ℝ) := Rfun_norm_le_card W _
  have hEq : ‖IFun N W m u‖ =
      ‖(((Real.fourierChar (-((N : ℝ) * ((m.1 : ℝ) * u.1 + (m.2.1 : ℝ) * u.2.1 +
        (m.2.2 : ℝ) * u.2.2))) : Circle)) : ℂ)‖ * (‖w2C u.1‖ * ‖w2C u.2.1‖ * ‖w2C u.2.2‖) *
        ‖Rfun W (u.1 / u.2.2)‖ * ‖Rfun W (u.2.1 / u.1)‖ * ‖Rfun W (u.2.2 / u.2.1)‖ := by
    simp only [IFun, norm_mul]
  rw [hEq]
  have key : (1 : ℝ) * (Cw ^ 2 * Cw ^ 2 * Cw ^ 2) * (W.card : ℝ) * (W.card : ℝ) * (W.card : ℝ) =
      Cw ^ 6 * (W.card : ℝ) ^ 3 := by ring
  rw [← key]
  gcongr <;> first | rw [hA] | exact hB | exact hC | exact hD | exact hE | exact hF | exact hG

theorem measurable_IFun (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) : Measurable (IFun N W m) := by
  have hR : Measurable (Rfun W) := Rfun_measurable W
  have hbw : Measurable bumpW := measurable_bumpW
  unfold IFun w2C
  fun_prop

theorem meas_Gterm (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) :
    Measurable (fun p : (ℝ × ℝ) × ℝ => Gterm N W m p.1 p.2) := by
  have hR : Measurable (Rfun W) := Rfun_measurable W
  have hbw : Measurable bumpW := measurable_bumpW
  unfold Gterm Rprod w2v w2C phas
  fun_prop


lemma mem_Icc_half_two_of_mul_mem {x y : ℝ} (hxy : x * y ∈ Set.Icc (1 : ℝ) 2)
    (hy : y ∈ Set.Icc (1 : ℝ) 2) : x ∈ Set.Icc (1 / 2 : ℝ) 2 := by
  obtain ⟨h1, h2⟩ := hxy
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · by_contra h
    rw [not_le] at h
    nlinarith
  · nlinarith

theorem integrable_prodAssoc_IFun (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) :
    Integrable (fun p : (ℝ × ℝ) × ℝ => IFun N W m (MeasurableEquiv.prodAssoc p))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  refine integrable_of_measurable_bounded_support
    (K := (Set.Icc (1 : ℝ) 2 ×ˢ Set.Icc (1 : ℝ) 2) ×ˢ Set.Icc (1 : ℝ) 2)
    ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc)
    ((measurable_IFun N W m).comp MeasurableEquiv.prodAssoc.measurable) ?_ (C := Cw ^ 6 * (W.card : ℝ) ^ 3) ?_
  · intro p hp
    rw [Function.mem_support] at hp
    rw [Set.mem_prod, Set.mem_prod]
    have hz : w2C p.1.1 * w2C p.1.2 * w2C p.2 ≠ 0 := by
      intro h
      apply hp
      rw [show MeasurableEquiv.prodAssoc p = (p.1.1, (p.1.2, p.2)) from rfl]
      simp only [IFun]
      rw [h]
      ring
    obtain ⟨h12, h3⟩ := mul_ne_zero_iff.mp hz
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h12
    exact ⟨⟨mem_Icc_of_w2C_ne_zero h1, mem_Icc_of_w2C_ne_zero h2⟩, mem_Icc_of_w2C_ne_zero h3⟩
  · intro p
    exact norm_IFun_le N W m _

theorem norm_Gterm_le (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) (w : ℝ × ℝ) (u : ℝ) :
    ‖Gterm N W m w u‖ ≤ (W.card : ℝ) ^ 3 * (4 * Cw ^ 6) := by
  have hR : ‖Rprod W w‖ ≤ (W.card : ℝ) ^ 3 := norm_Rprod_le W w
  have hw : ‖w2v w u‖ ≤ 4 * Cw ^ 6 := norm_w2v_le w u
  have he : ‖Complex.exp (-(2 * Real.pi * Complex.I * ((N : ℝ) * phas m w) * u))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have hcard : 0 ≤ (W.card : ℝ) ^ 3 := by positivity
  simp only [Gterm]
  rw [norm_mul, norm_mul, he, one_mul]
  exact mul_le_mul hR hw (norm_nonneg _) hcard

theorem integrable_Gterm (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) :
    Integrable (fun p : (ℝ × ℝ) × ℝ => Gterm N W m p.1 p.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  refine integrable_of_measurable_bounded_support
    (K := (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (1 / 2 : ℝ) 2) ×ˢ Set.Icc (1 : ℝ) 2)
    ((isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc) (meas_Gterm N W m) ?_
    (C := (W.card : ℝ) ^ 3 * (4 * Cw ^ 6)) ?_
  · intro p hp
    rw [Function.mem_support] at hp
    rw [Set.mem_prod, Set.mem_prod]
    have hz : w2v p.1 p.2 ≠ 0 := by
      intro h
      apply hp
      simp only [Gterm]
      rw [h]
      ring
    have hzv : w2v p.1 p.2 =
        (p.2 : ℂ) ^ 2 * w2C p.2 * w2C (p.1.1 * p.2) * w2C (p.1.2 * p.2) := rfl
    rw [hzv] at hz
    obtain ⟨h23, h4⟩ := mul_ne_zero_iff.mp hz
    obtain ⟨h12, h3⟩ := mul_ne_zero_iff.mp h23
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp h12
    have hy : p.2 ∈ Set.Icc (1 : ℝ) 2 := mem_Icc_of_w2C_ne_zero h2
    have hx1 : p.1.1 * p.2 ∈ Set.Icc (1 : ℝ) 2 := mem_Icc_of_w2C_ne_zero h3
    have hx2 : p.1.2 * p.2 ∈ Set.Icc (1 : ℝ) 2 := mem_Icc_of_w2C_ne_zero h4
    refine ⟨⟨mem_Icc_half_two_of_mul_mem hx1 hy, mem_Icc_half_two_of_mul_mem hx2 hy⟩, hy⟩
  · intro p
    exact norm_Gterm_le N W m _ _

theorem ae_ne_zero_real : ∀ᵐ x : ℝ, x ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  apply MeasureTheory.measure_mono_null (t := {0})
  · intro x hx; simpa using hx
  · simp

theorem smul_IFun (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) (w : ℝ × ℝ) {u : ℝ} (hu : u ≠ 0) :
    (u ^ 2) • (IFun N W m (MeasurableEquiv.prodAssoc (u • w, u))) = Gterm N W m w u := by
  have h1 : (u * w.1) / u = w.1 := mul_div_cancel_left₀ w.1 hu
  have h2 : (u * w.2) / (u * w.1) = w.2 / w.1 := by
    by_cases hw : w.1 = 0
    · simp [hw]
    · field_simp
  have h3 : u / (u * w.2) = 1 / w.2 := by
    by_cases hw : w.2 = 0
    · simp [hw]
    · field_simp
  rw [show MeasurableEquiv.prodAssoc (u • w, u) = (u * w.1, (u * w.2, u)) from rfl]
  simp only [IFun, Gterm, Rprod, w2v, phas]
  rw [h1, h2, h3, Real.fourierChar_apply]
  have harg : ((2 * Real.pi * (-((N : ℝ) * ((m.1 : ℝ) * (u * w.1) + (m.2.1 : ℝ) * (u * w.2) +
        (m.2.2 : ℝ) * u))) : ℝ) : ℂ) * Complex.I
      = -(2 * Real.pi * Complex.I * ((N : ℝ) * ((m.1 : ℝ) * w.1 + (m.2.1 : ℝ) * w.2 +
        (m.2.2 : ℝ)) * u)) := by
    push_cast
    ring
  rw [harg, Complex.real_smul]
  have hw1 : w2C (w.1 * u) = w2C (u * w.1) := by rw [mul_comm w.1 u]
  have hw2 : w2C (w.2 * u) = w2C (u * w.2) := by rw [mul_comm w.2 u]
  rw [hw1, hw2]
  push_cast
  ring

theorem Iterm_eq_vint (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) :
    Iterm N W m = (N : ℂ) ^ 3 * ∫ v : ℝ × ℝ, Rprod W v * innerInt N m v := by
  have hI : Iterm N W m = (N : ℂ) ^ 3 * ∫ u : ℝ × ℝ × ℝ, IFun N W m u := by
    rw [Iterm_eq_integral]
    rfl
  rw [hI]
  congr 1
  have hAint := integrable_prodAssoc_IFun N W m
  have hGint := integrable_Gterm N W m
  have h1 : (∫ u : ℝ × ℝ × ℝ, IFun N W m u)
      = ∫ p : (ℝ × ℝ) × ℝ, IFun N W m (MeasurableEquiv.prodAssoc p) :=
    ((MeasureTheory.volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ) (γ₁ := ℝ)).integral_comp
      MeasurableEquiv.prodAssoc.measurableEmbedding (IFun N W m)).symm
  have h2 : (∫ p : (ℝ × ℝ) × ℝ, IFun N W m (MeasurableEquiv.prodAssoc p))
      = ∫ u₃ : ℝ, ∫ w : ℝ × ℝ, IFun N W m (MeasurableEquiv.prodAssoc (w, u₃)) :=
    MeasureTheory.integral_prod_symm _ hAint
  have h3 : (∫ u₃ : ℝ, ∫ w : ℝ × ℝ, IFun N W m (MeasurableEquiv.prodAssoc (w, u₃)))
      = ∫ u₃ : ℝ, ∫ w : ℝ × ℝ, Gterm N W m w u₃ := by
    apply integral_congr_ae
    filter_upwards [ae_ne_zero_real] with u₃ hu₃
    have hsq : u₃ ^ 2 ≠ 0 := pow_ne_zero 2 hu₃
    have hHaar : (∫ x : ℝ × ℝ, IFun N W m (MeasurableEquiv.prodAssoc (x, u₃)))
        = (u₃ ^ 2) • ∫ x : ℝ × ℝ, IFun N W m (MeasurableEquiv.prodAssoc (u₃ • x, u₃)) := by
      have h := MeasureTheory.Measure.integral_comp_smul
        (μ := (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)))
        (fun x : ℝ × ℝ => IFun N W m (MeasurableEquiv.prodAssoc (x, u₃))) u₃
      rw [show Module.finrank ℝ (ℝ × ℝ) = 2 from by simp [Module.finrank_prod]] at h
      rw [show |(u₃ ^ 2)⁻¹| = (u₃ ^ 2)⁻¹ from abs_of_nonneg (inv_nonneg.mpr (sq_nonneg u₃))] at h
      rw [h, smul_smul, mul_inv_cancel₀ hsq, one_smul]
    rw [hHaar, ← MeasureTheory.integral_smul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with w
    exact smul_IFun N W m w hu₃
  have h4 : (∫ u₃ : ℝ, ∫ w : ℝ × ℝ, Gterm N W m w u₃)
      = ∫ p : (ℝ × ℝ) × ℝ, Gterm N W m p.1 p.2 :=
    (MeasureTheory.integral_prod_symm _ hGint).symm
  have h5 : (∫ p : (ℝ × ℝ) × ℝ, Gterm N W m p.1 p.2)
      = ∫ w : ℝ × ℝ, Rprod W w * innerInt N m w := by
    have key : (∫ p : (ℝ × ℝ) × ℝ, Gterm N W m p.1 p.2)
        = ∫ w : ℝ × ℝ, ∫ u : ℝ, Gterm N W m w u :=
      MeasureTheory.integral_prod _ hGint
    rw [key]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with w
    exact integral_Gterm N W m w
  rw [h1, h2, h3, h4, h5]



/-- `‖Iterm‖` is bounded by the `v`-integral `∫_v ‖R(v₁)R(v₂/v₁)R(1/v₂)‖ ‖innerInt(v)‖`. -/
theorem norm_Iterm_le (N : ℕ) (W : Finset ℝ) (m : ℤ × ℤ × ℤ) :
    ‖Iterm N W m‖ ≤ (N : ℝ) ^ 3 * ∫ v : ℝ × ℝ, ‖Rprod W v‖ * ‖innerInt N m v‖ := by
  rw [Iterm_eq_vint, norm_mul, norm_pow]
  have hnormN : ‖((N : ℕ) : ℂ)‖ = (N : ℝ) := by simp
  rw [hnormN]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  apply MeasureTheory.integral_congr_ae
  filter_upwards with v
  rw [norm_mul]

/-- **GM Proposition 7.1, main estimate.** For every `ε, η > 0` there are `C > 0`, `N₀` such that for `N ≥ N₀`, every `W ⊆ [0, M N]` that is
`(M N)^ε`-separated, and every `m : ℤ × ℤ × ℤ`,

`‖Iterm N W m‖ ≤ C * N³ * ∫_{v ∈ [1/2,2]²} 1_{|m₁v₁+m₂v₂+m₃| ≤ (M N)^η / N} * ‖R(v₁) R(v₂/v₁) R(1/v₂)‖
                 + C * N^{-20}`,

with `R = Rfun`.  (Paper: `|I_m| ≪ N³ ∫_{|m₁v₁+m₂v₂+m₃| ⪅ 1/N, v₁≍v₂≍1}|R(v₁)R(v₂/v₁)R(1/v₂)| +
O(T^{-200})`; the `⪅ 1/N` is spelled out as `(M N)^η/N` for arbitrary `η > 0`.) -/
theorem prop71_main :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
    ∀ m : ℤ × ℤ × ℤ,
      ‖Submission.GM.Iterm N W m‖ ≤ C * (N : ℝ) ^ 3 *
        ∫ v in (Set.Icc (1/2 : ℝ) 2 ×ˢ Set.Icc (1/2 : ℝ) 2),
          (if |(m.1 : ℝ) * v.1 + (m.2.1 : ℝ) * v.2 + (m.2.2 : ℝ)| ≤
              (Submission.LargeValues.M N) ^ η / (N : ℝ)
            then ‖Submission.GM.Rfun W v.1 * Submission.GM.Rfun W (v.2 / v.1) *
              Submission.GM.Rfun W (1 / v.2)‖ else 0)
        + C * (N : ℝ) ^ (-20 : ℤ) := by
  intro ε η hε hη
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (133 : ℝ) / 6 ≤ (j : ℝ) * η := by
    obtain ⟨j, hj⟩ := exists_nat_ge (133 / (6 * η))
    refine ⟨j, ?_⟩
    have h3 : 133 / (6 * η) * η = 133 / 6 := by field_simp
    have h2 : 133 / (6 * η) * η ≤ (j : ℝ) * η :=
      mul_le_mul_of_nonneg_right hj (le_of_lt hη)
    rwa [h3] at h2
  obtain ⟨K, hKpos, hin⟩ := prop71_inner_uniform
  obtain ⟨Cj, hCjpos, hdec⟩ := prop71_inner_decay j
  obtain ⟨Ctail, hCtailpos, hCtailspec⟩ := prop71_tail_arith η hη j hj
  refine ⟨max (max K ((9 / 4) * Cj * Ctail)) 1, ?_, 1, ?_⟩
  · have h1 : K ≤ max (max K ((9 / 4) * Cj * Ctail)) 1 :=
      le_trans (le_max_left _ _) (le_max_left _ _)
    linarith
  intro N hN W hW hsep m
  have hsep1 : ∀ t ∈ W, ∀ s ∈ W, t ≠ s → 1 ≤ |t - s| := by
    intro t ht s hs hts
    refine le_trans ?_ (hsep t ht s hs hts)
    have := Real.one_le_rpow (Submission.LargeValues.M_ge_one hN) (le_of_lt hε)
    simpa using this
  have hcard : (W.card : ℝ) ≤ 2 * Submission.LargeValues.M N :=
    prop71_card_bound N hN W hW hsep1
  have hmain : (0 : ℝ) ≤
      ∫ v in pbox, (if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
        then ‖Rprod W v‖ else 0) := by
    rw [← MeasureTheory.integral_indicator measurableSet_pbox]
    apply MeasureTheory.integral_nonneg
    intro v
    by_cases hv : v ∈ pbox
    · rw [Set.indicator_of_mem hv]
      split <;> positivity
    · rw [Set.indicator_of_notMem hv]
      norm_num
  have hbox := prop71_box_integral_bound K Cj hKpos hCjpos j hin hdec N hN η hη W m
  have hfin := prop71_final_arith η hη j hj K Cj Ctail (le_of_lt hKpos) (le_of_lt hCjpos)
    (le_of_lt hCtailpos) hCtailspec N hN W hcard
    (∫ v in pbox, (if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
      then ‖Rprod W v‖ else 0))
    (∫ v : ℝ × ℝ, ‖Rprod W v‖ * ‖innerInt N m v‖) hmain hbox
  have hC'le : max K ((9 / 4) * Cj * Ctail) ≤ max (max K ((9 / 4) * Cj * Ctail)) 1 :=
    le_max_left _ _
  have hzpow : (0 : ℝ) ≤ (N : ℝ) ^ (-20 : ℤ) := zpow_nonneg (by positivity) _
  have hfinC : (N : ℝ) ^ 3 * (∫ v : ℝ × ℝ, ‖Rprod W v‖ * ‖innerInt N m v‖) ≤
      (max (max K ((9 / 4) * Cj * Ctail)) 1) *
        ((N : ℝ) ^ 3 * (∫ v in pbox, (if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
          then ‖Rprod W v‖ else 0))) +
      (max (max K ((9 / 4) * Cj * Ctail)) 1) * (N : ℝ) ^ (-20 : ℤ) :=
    le_trans hfin (add_le_add (mul_le_mul_of_nonneg_right hC'le (by positivity))
      (mul_le_mul_of_nonneg_right hC'le hzpow))
  have hdom := prop71_rhs_domination N hN η hη (max (max K ((9 / 4) * Cj * Ctail)) 1)
    (le_max_right _ _) W m
  refine le_trans (norm_Iterm_le N W m) (le_trans ?_ hdom)
  simpa only [pbox, Rprod, phas, mul_assoc] using hfinC

end Work.GM.S3
