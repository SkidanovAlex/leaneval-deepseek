import Mathlib
import Submission.Work.GM.S3.Base
import Submission.Work.GM.S3.Defs
import Submission.Work.GM.S3.prop71_defs
import Submission.Work.GM.S3.prop71_main
import Submission.Work.GM.S3.window_defs
import Submission.Work.GM.S3.prop72_core
import Submission.Work.GM.S3.pdom_defs
import Submission.Work.GM.S3.box_integral_bound_of_set

/-!
# Sharpened GM Proposition 7.1: the `v`-integral may be restricted to the true domain

`Work.GM.S3.prop71_main` proves GM Prop 7.1 with the `v`-integral taken over `pbox = [1/2,2]²`.
The `u₃`-weight `w2v v u = u²w(u)²w(v₁u)²w(v₂u)²` of `Work.GM.S3.prop71_defs` is non-zero only
when `u, v₁u, v₂u ∈ [1,2]` (the support of `bumpW`), which forces `v ∈ [1/2,2]²` *and*
`v₂/v₁ = (v₂u)/(v₁u) ∈ [1/2,2]`.  Hence `innerInt N m v` vanishes off

    pdom = pbox ∩ {v | v₂/v₁ ∈ [1/2,2]}

(`Work.GM.S3.innerInt_eq_zero_of_not_mem_pdom`, in `Submission.Work.GM.S3.pdom_defs`), and the
whole proof of `prop71_main` can be re-run with `pbox` replaced by `pdom`:

* `Work.GM.S3.box_integral_bound_of_set` is the box-integral bound for a general measurable
  `S ⊆ pbox` off which `innerInt` vanishes;
* `rhs_domination_of_set` moves the `+ C N^{-20}` term into the integral body (as the statement's
  binder does), using `vol(pdom) ≥ 1` (`Work.GM.S3.pdom_volume_ge_one`);
* `Work.GM.S3.prop71_final_arith` and `Work.GM.S3.prop71_card_bound` are the unchanged arithmetic.

-/

namespace Work.GM.S3

open Complex Finset MeasureTheory
open scoped BigOperators
open Submission.GM (Rfun Separated Iterm hhat hfun)

theorem rhs_domination_of_set (N : ℕ) (hN : 1 ≤ N) (η : ℝ) (hη : 0 < η) (C : ℝ) (hC : 1 ≤ C)
    (W : Finset ℝ) (m : ℤ × ℤ × ℤ) (S : Set (ℝ × ℝ)) (hSmeas : MeasurableSet S)
    (hSne : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) S ≠ ⊤)
    (hvol : 1 ≤ ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) S).toReal) :
    C * (N : ℝ) ^ 3 * (∫ v in S, (if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
        then ‖Rprod W v‖ else 0)) + C * (N : ℝ) ^ (-20 : ℤ)
    ≤ C * (N : ℝ) ^ 3 * (∫ v in S,
        ((if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
          then ‖Rprod W v‖ else 0) + C * (N : ℝ) ^ (-20 : ℤ))) := by
  have _ := hSmeas
  have _ := hη
  have hphas_meas : Measurable (fun v : ℝ × ℝ => phas m v) := by unfold phas; fun_prop
  have hmeas : Measurable (fun v : ℝ × ℝ =>
      (if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ) then ‖Rprod W v‖ else 0)) := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_le (continuous_abs.measurable.comp hphas_meas) measurable_const
    · exact (Rprod_measurable W).norm
  set V : ℝ := ((MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) S).toReal with hVdef
  have hconst_int :
      Integrable (fun _ : ℝ × ℝ => (W.card : ℝ) ^ 3) (MeasureTheory.volume.restrict S) :=
    MeasureTheory.integrableOn_const hSne
  have hbound : ∀ v : ℝ × ℝ, ‖(if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
      then ‖Rprod W v‖ else 0)‖ ≤ (W.card : ℝ) ^ 3 := by
    intro v
    split_ifs with h
    · simpa using norm_Rprod_le W v
    · simp
  have hint_g : Integrable (fun v : ℝ × ℝ =>
      (if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
        then ‖Rprod W v‖ else 0)) (MeasureTheory.volume.restrict S) :=
    hconst_int.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hint_c : Integrable (fun _ : ℝ × ℝ => C * (N : ℝ) ^ (-20 : ℤ))
      (MeasureTheory.volume.restrict S) :=
    MeasureTheory.integrableOn_const hSne
  have hsplit : ∫ v in S, ((if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
        then ‖Rprod W v‖ else 0) + C * (N : ℝ) ^ (-20 : ℤ))
      = (∫ v in S, (if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
        then ‖Rprod W v‖ else 0)) + (C * (N : ℝ) ^ (-20 : ℤ)) * V := by
    rw [MeasureTheory.integral_add hint_g hint_c]
    congr 1
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, ← hVdef, smul_eq_mul]
    ring
  rw [hsplit]
  have hV1 : 1 ≤ V := by rw [hVdef]; exact hvol
  have hc : 0 ≤ C * (N : ℝ) ^ (-20 : ℤ) :=
    mul_nonneg (by linarith) (zpow_nonneg (by positivity) _)
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hC3 : (1 : ℝ) ≤ C * (N : ℝ) ^ 3 := by
    have hN3 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ hN1
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ C * (N : ℝ) ^ 3 := mul_le_mul hC hN3 zero_le_one (by linarith)
  have hCV : 1 ≤ C * (N : ℝ) ^ 3 * V := by
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ C * (N : ℝ) ^ 3 * V := mul_le_mul hC3 hV1 zero_le_one (by linarith)
  have hstep : C * (N : ℝ) ^ (-20 : ℤ) ≤ (C * (N : ℝ) ^ 3) *
      (C * (N : ℝ) ^ (-20 : ℤ) * V) := by
    have h := mul_le_mul_of_nonneg_left hCV hc
    calc C * (N : ℝ) ^ (-20 : ℤ) = C * (N : ℝ) ^ (-20 : ℤ) * 1 := by ring
      _ ≤ C * (N : ℝ) ^ (-20 : ℤ) * (C * (N : ℝ) ^ 3 * V) := h
      _ = (C * (N : ℝ) ^ 3) * (C * (N : ℝ) ^ (-20 : ℤ) * V) := by ring
  have hexp : C * (N : ℝ) ^ 3 * ((∫ v in S, (if |phas m v| ≤
        (Submission.LargeValues.M N) ^ η / (N : ℝ) then ‖Rprod W v‖ else 0)) +
        C * (N : ℝ) ^ (-20 : ℤ) * V)
      = C * (N : ℝ) ^ 3 * (∫ v in S, (if |phas m v| ≤
        (Submission.LargeValues.M N) ^ η / (N : ℝ) then ‖Rprod W v‖ else 0)) +
        (C * (N : ℝ) ^ 3) * (C * (N : ℝ) ^ (-20 : ℤ) * V) := by ring
  rw [hexp]
  linarith [hstep]

/-- **Sharpened GM Prop 7.1.** `Work.GM.S3.prop71_main` bounds `‖Iterm N W m‖` by `N³` times the
`v`-integral of `1_{|phas m v| ≤ (MN)^η/N}‖Rprod v‖` over `pbox = [1/2,2]²`.  But the true `u₃`-weight
`w2v v u = u²w(u)²w(v₁u)²w(v₂u)²` vanishes unless `u, v₁u, v₂u ∈ [1,2]`, hence unless
`v₂/v₁ = (v₂u)/(v₁u) ∈ [1/2,2]`.  Therefore the `v`-integral can be restricted to the *true domain*
`{v : v₂/v₁ ∈ [1/2,2]}` (the corner triangles of `pbox` carry weight zero), and the constant and `N₀`
are unchanged.  This is the same proof as `prop71_main` with `prop71_inner_support` strengthened to
`innerInt N m v = 0` for `v ∉ pbox ∨ v₂/v₁ ∉ [1/2,2]`. -/
theorem prop71_domain :
    ∀ ε η : ℝ, 0 < ε → 0 < η → ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    ∀ W : Finset ℝ, (∀ t ∈ W, t ∈ Set.Icc 0 (Submission.LargeValues.M N)) →
      Submission.GM.Separated W ((Submission.LargeValues.M N) ^ ε) →
    ∀ m : ℤ × ℤ × ℤ,
      ‖Submission.GM.Iterm N W m‖ ≤ C * (N : ℝ) ^ 3 *
        ∫ v in (Work.GM.S3.pbox ∩ {v : ℝ × ℝ | v.2 / v.1 ∈ Set.Icc (1 / 2 : ℝ) 2}),
          (if |Work.GM.S3.phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
            then ‖Work.GM.S3.Rprod W v‖ else 0)
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
  have hmain : (0 : ℝ) ≤ ∫ v in pdom, (if |phas m v| ≤
      (Submission.LargeValues.M N) ^ η / (N : ℝ) then ‖Rprod W v‖ else 0) := by
    rw [← MeasureTheory.integral_indicator measurableSet_pdom]
    apply MeasureTheory.integral_nonneg
    intro v
    by_cases hv : v ∈ pdom
    · rw [Set.indicator_of_mem hv]; split <;> positivity
    · rw [Set.indicator_of_notMem hv]; norm_num
  have hbox := box_integral_bound_of_set K Cj hKpos hCjpos j hin hdec pdom measurableSet_pdom
    pdom_subset_pbox (fun N m v hv => innerInt_eq_zero_of_not_mem_pdom hv) N hN η hη W m
  have hfin := prop71_final_arith η hη j hj K Cj Ctail (le_of_lt hKpos) (le_of_lt hCjpos)
    (le_of_lt hCtailpos) hCtailspec N hN W hcard
    (∫ v in pdom, (if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
      then ‖Rprod W v‖ else 0))
    (∫ v : ℝ × ℝ, ‖Rprod W v‖ * ‖innerInt N m v‖) hmain hbox
  have hCle : max K ((9 / 4) * Cj * Ctail) ≤ max (max K ((9 / 4) * Cj * Ctail)) 1 :=
    le_max_left _ _
  have hfinC : (N : ℝ) ^ 3 * (∫ v : ℝ × ℝ, ‖Rprod W v‖ * ‖innerInt N m v‖) ≤
      max (max K ((9 / 4) * Cj * Ctail)) 1 *
        ((N : ℝ) ^ 3 * (∫ v in pdom, (if |phas m v| ≤
          (Submission.LargeValues.M N) ^ η / (N : ℝ) then ‖Rprod W v‖ else 0))) +
      max (max K ((9 / 4) * Cj * Ctail)) 1 * (N : ℝ) ^ (-20 : ℤ) := by
    refine le_trans hfin ?_
    have h3 : (0 : ℝ) ≤ (N : ℝ) ^ 3 * (∫ v in pdom, (if |phas m v| ≤
        (Submission.LargeValues.M N) ^ η / (N : ℝ) then ‖Rprod W v‖ else 0)) :=
      mul_nonneg (by positivity) hmain
    have h4 : (0 : ℝ) ≤ (N : ℝ) ^ (-20 : ℤ) := zpow_nonneg (by positivity) _
    have h5 := add_le_add (mul_le_mul_of_nonneg_right hCle h3) (mul_le_mul_of_nonneg_right hCle h4)
    linarith [h5]
  have hSne : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)) pdom ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (MeasureTheory.measure_mono pdom_subset_pbox)
      prop71_box_isCompact_pbox.measure_lt_top)
  have hdom := rhs_domination_of_set N hN η hη (max (max K ((9 / 4) * Cj * Ctail)) 1)
    (le_max_right _ _) W m pdom measurableSet_pdom hSne pdom_volume_ge_one
  refine le_trans (norm_Iterm_le N W m) (le_trans hfinC ?_)
  simpa only [pdom, mul_assoc] using hdom

end Work.GM.S3
