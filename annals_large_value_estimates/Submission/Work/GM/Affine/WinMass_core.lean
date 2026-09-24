import Mathlib
import Submission.Work.GM.Affine.fine_setup
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.region_II_vocab
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.WinMass_basic
import Submission.Work.GM.Affine.WinMass_window
import Submission.Work.GM.Affine.winmass_sampling
import Submission.Work.GM.Affine.Gfun_sq_ge_coherence
import Submission.Work.GM.Affine.supf_le_T_mul_integral
import Submission.Work.GM.Affine.WinMass_crux_tail_uniform
import Submission.Work.GM.Affine.WinMass_fejer_defs
import Submission.Work.GM.Affine.winMass_le_fejer
import Submission.Work.GM.Affine.fejerK_basic
import Submission.Work.GM.Affine.near_correlation_le_Gfun
import Submission.Work.GM.Affine.far_tail_le
import Submission.Work.GM.Affine.smoothed_L2_le
import Submission.Work.GM.Affine.WinMass_core_of_fejer_route
import Submission.Work.GM.Affine.Hprof_sq_integral_le

/-!
# `Work.GM.Affine.WinMass_core`

The target lemma of GM §9 region II:

`WinMass f M₂ M₃ ≤ C' T^δ (M₂ (∫f²)^{1/2} (∫Gfun²)^{1/2} + M₂² M₃ ∫f²)`.

## Route

Everything is proved here from the single analytic input `hprof_dilate_sq_eps`, the `M₂^ε`-lossy
dilate inequality for the profile `Hprof f M₂ u = Σ_{m₂∈R2 M₂} f(u/m₂)`:

`∀ ε > 0, ∃ C > 0, ∀ M₂ ≥ 1, ∀ f: ∫ (Hprof f M₂)² ≤ C M₂^ε (M₂²∫f² + M₂³(∫f²)^{1/2}∫f)`.

(Without the `M₂^ε` loss the inequality is FALSE — needle-comb counterexamples make the left side
grow like `log M₂` while the right side stays bounded; see
`NOTES_hprof_dilate_sq_min_FALSE.md`. The loss is harmless here because `M₂ ≤ Mbig ≤ T⁴`.)

* `hprof_core_bound_eps`: dilate inequality + coherence
  (`Gfun_sq_ge_coherence`: `c₁ M₂⁶ (∫f)² ≤ ∫ (Gfun C₀ T M₂ f)²`) give the *profile bound*
  `∫ (Hprof f M₂)² ≤ C T^δ (√(∫f²) √(∫Gfun²) + M₂²∫f²)`; the `M₂^{δ/4}` factor of the dilate
  inequality is absorbed by `T^δ` via `M₂ ≤ T⁴`.
* `winmass_core_of_core`: the sampling bound (`winmass_sampling`) and the elementary window bound
  (`WinMass_window_le`) give `WinMass ≤ C min(M₂,M₃) ∫ (Hprof f M₂)²` for `M₃ ≥ 1`, and the
  two terms of the profile bound are distributed over `min ≤ M₂` and `min ≤ M₃`.
* the degenerate range `M₂ < 1`: `R2 M₂ ⊆ {1}`, so `Hprof f M₂ ≤ f` and the second target term
  `M₂²M₃∫f²` dominates.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.GM.Affine

noncomputable section

/-- The right-hand side factor of the target: `M₂ √(∫f²) √(∫Gfun²) + M₂² M₃ ∫f²`. -/
def winmassQ (C₀ T M₂ M₃ : ℝ) (f : ℝ → ℝ) : ℝ :=
  M₂ * Real.sqrt (∫ u, (f u) ^ 2) * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)
    + M₂ ^ 2 * M₃ * (∫ u, (f u) ^ 2)

lemma winmassQ_nonneg {C₀ T M₂ M₃ : ℝ} {f : ℝ → ℝ} (hM₂ : 0 ≤ M₂) (hM₃ : 0 ≤ M₃)
    (hfnn : ∀ u, 0 ≤ f u) : 0 ≤ winmassQ C₀ T M₂ M₃ f := by
  unfold winmassQ
  have hA : (0:ℝ) ≤ Real.sqrt (∫ u, (f u) ^ 2) := Real.sqrt_nonneg _
  have hB : (0:ℝ) ≤ Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) := Real.sqrt_nonneg _
  have hX : (0:ℝ) ≤ (∫ u, (f u) ^ 2) := integral_nonneg (fun u => sq_nonneg _)
  linarith [mul_nonneg (mul_nonneg hM₂ hA) hB, mul_nonneg (mul_nonneg (sq_nonneg M₂) hM₃) hX]

/-! ## Elementary facts about the ranges and the profile -/

lemma winmass_hcs_of_suppHyp {C₀ : ℝ} {f : ℝ → ℝ} (h : SuppHyp C₀ f) :
    HasCompactSupport f := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1 / C₀) C₀) isCompact_Icc ?_
  intro u hu
  rw [Function.mem_support] at hu
  exact h u hu

/-- For `M₂ < 1` the range `R2 M₂` is contained in `{1}`. -/
lemma winmass_R2_subset_singleton {M₂ : ℝ} (hM₂ : M₂ < 1) : R2 M₂ ⊆ ({(1:ℤ)} : Finset ℤ) := by
  intro m hm
  rw [Finset.mem_singleton]
  obtain ⟨hmI, _⟩ := Finset.mem_filter.mp hm
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hmI
  have h2' : (m : ℝ) ≤ 2 * M₂ := le_trans (by exact_mod_cast h2) (Int.floor_le _)
  have h3 : (m : ℝ) < 2 := by linarith
  have h4 : m < (2:ℤ) := by exact_mod_cast h3
  omega

/-- For `M₂ < 1` the profile is pointwise dominated by `f`. -/
lemma winmass_Hprof_le_self {M₂ : ℝ} (hM₂ : M₂ < 1) {f : ℝ → ℝ} (hfnn : ∀ u, 0 ≤ f u)
    (u : ℝ) : Hprof f M₂ u ≤ f u := by
  unfold Hprof
  calc (∑ m₂ ∈ R2 M₂, f (u / (m₂ : ℝ)))
      ≤ ∑ m₂ ∈ ({(1:ℤ)} : Finset ℤ), f (u / (m₂ : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (winmass_R2_subset_singleton hM₂)
          (fun m _ _ => hfnn _)
    _ = f u := by simp

/-- For `M₂ < 1/2` the range `R2 M₂` is empty. -/
lemma winmass_R2_eq_empty {M₂ : ℝ} (hM₂ : M₂ < 1/2) : R2 M₂ = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr (fun m hm => ?_)
  have hm1 : m = 1 := by
    have h := winmass_R2_subset_singleton (by linarith : M₂ < 1) hm
    simpa using h
  rw [hm1] at hm
  obtain ⟨hmI, _⟩ := Finset.mem_filter.mp hm
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hmI
  have h2' : (1:ℝ) ≤ ((⌊2 * M₂⌋ : ℤ) : ℝ) := by
    have : ((1:ℤ) : ℝ) ≤ ((⌊2 * M₂⌋ : ℤ) : ℝ) := by exact_mod_cast h2
    simpa using this
  have h3 : ((⌊2 * M₂⌋ : ℤ) : ℝ) ≤ 2 * M₂ := Int.floor_le _
  linarith

/-! ## The support Cauchy--Schwarz bound

For `f ≥ 0` continuous with `SuppHyp C₀ f` the whole mass is carried by `[1/C₀, C₀]`, so
`(∫ f)² ≤ C₀ ∫ f²`.  This is the elementary input that lets the `(∫ f)²`-term of the dilate
shape be absorbed into `√(∫f²)·√(∫Gfun²)` via the coherence bound. -/
lemma sq_integral_le_C0_mul_sq_integral {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {f : ℝ → ℝ}
    (hf : Continuous f) (hfnn : ∀ u, 0 ≤ f u) (hSupp : SuppHyp C₀ f) :
    (∫ u, f u) ^ 2 ≤ C₀ * ∫ u, (f u) ^ 2 := by
  have hzero : ∀ u, u ∉ Set.Icc (1/C₀) C₀ → f u = 0 := by
    intro u hu; by_contra h; exact hu (hSupp u h)
  have hset : ∫ u in Set.Icc (1/C₀) C₀, f u = ∫ u, f u :=
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  have hcs : HasCompactSupport f := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1/C₀) C₀) isCompact_Icc ?_
    intro u hu
    rw [Function.mem_support] at hu
    by_contra h; exact hu (hzero u h)
  have hvolnn : (0:ℝ) ≤ C₀ - 1/C₀ := by
    rw [sub_nonneg, div_le_iff₀ (by linarith : (0:ℝ) < C₀)]; nlinarith
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (1/C₀) C₀)) := by
    rw [MeasureTheory.isFiniteMeasure_restrict, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have hmemf : MemLp f (ENNReal.ofReal 2) (volume.restrict (Set.Icc (1/C₀) C₀)) :=
    (Continuous.memLp_of_hasCompactSupport hf hcs).restrict _
  have hmemg : MemLp (fun _ : ℝ => (1:ℝ)) (ENNReal.ofReal 2)
      (volume.restrict (Set.Icc (1/C₀) C₀)) :=
    MeasureTheory.memLp_const (1:ℝ)
  have hholder : ∫ a in Set.Icc (1/C₀) C₀, f a ≤
      (∫ a in Set.Icc (1/C₀) C₀, (f a) ^ (2:ℝ)) ^ (1/(2:ℝ)) *
        (∫ a in Set.Icc (1/C₀) C₀, (1:ℝ) ^ (2:ℝ)) ^ (1/(2:ℝ)) := by
    have h := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := volume.restrict (Set.Icc (1/C₀) C₀))
      (p := 2) (q := 2) Real.HolderConjugate.two_two (f := f) (g := fun _ : ℝ => (1:ℝ))
      (Filter.Eventually.of_forall (fun a => hfnn a))
      (Filter.Eventually.of_forall (fun a => zero_le_one)) hmemf hmemg
    simpa using h
  have hvol : (∫ a in Set.Icc (1/C₀) C₀, (1:ℝ) ^ (2:ℝ)) = C₀ - 1/C₀ := by
    rw [show (∫ a in Set.Icc (1/C₀) C₀, (1:ℝ) ^ (2:ℝ))
          = ∫ a in Set.Icc (1/C₀) C₀, (1:ℝ) by
      refine setIntegral_congr_fun measurableSet_Icc (fun a _ => ?_); norm_num]
    rw [setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal hvolnn]
    ring
  have hf2 : (∫ a in Set.Icc (1/C₀) C₀, (f a) ^ (2:ℝ))
      = ∫ a in Set.Icc (1/C₀) C₀, (f a) ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Icc (fun a _ => ?_); rw [Real.rpow_two]
  have hf2cs : HasCompactSupport (fun u => (f u)^2) := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1/C₀) C₀) isCompact_Icc ?_
    intro u hu
    rw [Function.mem_support] at hu
    by_contra h
    exact hu (by rw [hzero u h]; norm_num)
  have hf2int : Integrable (fun u => (f u)^2) := (hf.pow 2).integrable_of_hasCompactSupport hf2cs
  have hle : ∫ a in Set.Icc (1/C₀) C₀, (f a) ^ 2 ≤ ∫ u, (f u) ^ 2 :=
    MeasureTheory.setIntegral_le_integral hf2int
      (Filter.Eventually.of_forall (fun u => sq_nonneg _))
  have hnn2 : (0:ℝ) ≤ ∫ a in Set.Icc (1/C₀) C₀, (f a) ^ 2 := integral_nonneg (fun a => sq_nonneg _)
  have hA : (0:ℝ) ≤ ∫ u, (f u)^2 := integral_nonneg (fun u => sq_nonneg _)
  have hs1 : ((∫ a in Set.Icc (1/C₀) C₀, (f a) ^ 2) ^ (1/(2:ℝ)))^(2:ℕ)
      = (∫ a in Set.Icc (1/C₀) C₀, (f a) ^ 2) := by
    rw [← Real.sqrt_eq_rpow]; exact Real.sq_sqrt hnn2
  have hs2 : ((C₀ - 1/C₀) ^ (1/(2:ℝ)))^(2:ℕ) = (C₀ - 1/C₀) := by
    rw [← Real.sqrt_eq_rpow]; exact Real.sq_sqrt hvolnn
  have key : (∫ a in Set.Icc (1/C₀) C₀, f a) ^ 2
      ≤ (∫ a in Set.Icc (1/C₀) C₀, (f a) ^ 2) * (C₀ - 1/C₀) := by
    have h2 := hholder
    rw [hf2, hvol] at h2
    have hnn : (0:ℝ) ≤ ∫ a in Set.Icc (1/C₀) C₀, f a := integral_nonneg (fun a => hfnn a)
    have hsq := sq_le_sq' (by linarith [h2]) h2
    rw [mul_pow, hs1, hs2] at hsq
    exact hsq
  have hpos : 0 < 1/C₀ := by positivity
  have h1 : (∫ a in Set.Icc (1/C₀) C₀, (f a) ^ 2) * (C₀ - 1/C₀) ≤ (∫ u, (f u)^2) * C₀ :=
    mul_le_mul hle (by linarith) hvolnn hA
  rw [← hset]
  linarith [key, h1]

/-- **The effective-width (admissibility) bound.**  From the sharp admissibility
`supf f ≤ C T^{1+δ}∫f` one gets `∫f² ≤ supf f · ∫f ≤ C T^{1+δ}(∫f)²`, i.e. the "coherence
width" `w = (∫f)²/∫f²` is at least `T^{-1-δ}`. -/
theorem sq_integral_le_T_mul_sq_integral {C₀ : ℝ} (hC₀ : 1 ≤ C₀) (c : ℕ → ℝ → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, 1 ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∫ u, (f u) ^ 2 ≤ C * T ^ (1 + δ) * (∫ u, f u) ^ 2 := by
  obtain ⟨C₁, hC₁pos, hsup⟩ := supf_le_T_mul_integral hC₀ c δ hδ
  refine ⟨max C₁ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro T hT f hf hfnn hSupp Λ hΛ hdec hcompat
  have hsup' := hsup T hT f hf hfnn hSupp Λ hΛ hdec hcompat
  have hcs : HasCompactSupport f := winmass_hcs_of_suppHyp hSupp
  have hU : (0:ℝ) ≤ ∫ u, f u := integral_nonneg hfnn
  have hUnn : (0:ℝ) ≤ supf f := le_trans (hfnn (1/C₀)) (le_supf hf hcs (1/C₀))
  have hcs2 : HasCompactSupport (fun u => f u * f u) := by
    refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (1/C₀) C₀)
      isCompact_Icc ?_
    intro u hu
    rw [Function.mem_support] at hu
    by_contra h
    exact hu (by rw [by_contra (fun h' => h (hSupp u h'))]; ring)
  have hInt1 : Integrable (fun u => f u * f u) :=
    (hf.mul hf).integrable_of_hasCompactSupport hcs2
  have hInt2 : Integrable (fun u => supf f * f u) :=
    Integrable.const_mul (hf.integrable_of_hasCompactSupport hcs) (supf f)
  have hle : ∫ u, (f u) ^ 2 ≤ ∫ u, supf f * f u := by
    have hp : (fun u => (f u)^2) = fun u => f u * f u := by funext u; ring
    rw [hp]
    refine integral_mono hInt1 hInt2 (fun u => ?_)
    nlinarith [hfnn u, le_supf hf hcs u]
  calc ∫ u, (f u) ^ 2 ≤ ∫ u, supf f * f u := hle
    _ = supf f * ∫ u, f u := integral_const_mul (supf f) f
    _ ≤ (C₁ * T ^ (1 + δ) * ∫ u, f u) * ∫ u, f u :=
        mul_le_mul_of_nonneg_right hsup' hU
    _ ≤ max C₁ 1 * T ^ (1 + δ) * (∫ u, f u) ^ 2 := by
        have hTnn : (0:ℝ) ≤ T ^ (1+δ) := Real.rpow_nonneg (le_trans zero_le_one hT) _
        have hU' : (0:ℝ) ≤ (∫ u, f u) * (∫ u, f u) := mul_nonneg hU hU
        have h1 : C₁ * T^(1+δ) ≤ max C₁ 1 * T^(1+δ) :=
          mul_le_mul_of_nonneg_right (le_max_left (C₁:ℝ) 1) hTnn
        have h2 : (C₁ * T^(1+δ)) * ((∫ u, f u) * (∫ u, f u))
            ≤ (max C₁ 1 * T^(1+δ)) * ((∫ u, f u) * (∫ u, f u)) :=
          mul_le_mul_of_nonneg_right h1 hU'
        calc (C₁ * T ^ (1 + δ) * ∫ u, f u) * ∫ u, f u
            = C₁ * T^(1+δ) * (∫ u, f u) * (∫ u, f u) := by ring
          _ ≤ max C₁ 1 * T^(1+δ) * (∫ u, f u) * (∫ u, f u) := by
              have hh := h2
              ring_nf at hh ⊢
              exact hh
          _ = max C₁ 1 * T ^ (1 + δ) * (∫ u, f u) ^ 2 := by ring

/-! ## The core profile bound (dilate inequality + coherence) -/

/-- **The core profile bound.** From the `M₂^ε`-lossy dilate inequality and the coherence lower
bound for `Gfun`, the profile is controlled by `T^δ (√(∫f²) √(∫Gfun²) + M₂² ∫f²)`: the factor
`M₂^{δ/4}` of the dilate inequality is absorbed by `T^δ` through `M₂ ≤ T⁴`. -/
theorem hprof_core_bound_eps {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {δ : ℝ} (hδ : 0 < δ)
    (hdil : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ {M₂ : ℝ}, 1 ≤ M₂ → ∀ {f : ℝ → ℝ}, Continuous f → (∀ u, 0 ≤ f u) →
        SuppHyp C₀ f →
        (∫ u, (∑ m₂ ∈ R2 M₂, f (u / (m₂ : ℝ))) ^ 2) ≤
          C * M₂ ^ ε * (M₂ ^ 2 * (∫ u, (f u) ^ 2) +
            M₂ ^ 3 * (∫ u, (f u) ^ 2) ^ (1 / 2 : ℝ) * (∫ u, f u))) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T M₂ : ℝ}, 1 ≤ T → 1 ≤ M₂ → M₂ ≤ T ^ 4 → ∀ {f : ℝ → ℝ}, Continuous f →
        (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        (∫ u, (∑ m₂ ∈ R2 M₂, f (u / (m₂ : ℝ))) ^ 2) ≤
          C * T ^ δ * (Real.sqrt (∫ u, (f u) ^ 2) * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)
            + M₂ ^ 2 * (∫ u, (f u) ^ 2)) := by
  obtain ⟨C₂, hC₂pos, hdil'⟩ := hdil (δ / 4) (by positivity)
  obtain ⟨c₁, hc₁pos, hcoher⟩ := Gfun_sq_ge_coherence hC₀
  refine ⟨C₂ * max 1 (1 / Real.sqrt c₁) + 1, by positivity, ?_⟩
  intro T M₂ hT hM₂ hM₂T f hf hfnn hSupp
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hpow : M₂ ^ (δ / 4) ≤ T ^ δ := by
    have h1 : M₂ ^ (δ / 4) ≤ (T ^ 4) ^ (δ / 4) :=
      Real.rpow_le_rpow (by linarith : (0:ℝ) ≤ M₂) hM₂T (by positivity)
    have h2 : (T ^ 4) ^ (δ / 4) = T ^ δ := by
      rw [← Real.rpow_natCast T 4, ← Real.rpow_mul hTpos.le]
      congr 1
      ring
    linarith [h1, h2.le]
  have hUnn : 0 ≤ M₂ ^ (δ / 4) := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ M₂) _
  have hVnn : 0 ≤ T ^ δ := Real.rpow_nonneg hTpos.le _
  have hXnn : 0 ≤ (∫ u, (f u) ^ 2) := integral_nonneg (fun u => sq_nonneg _)
  have hAnn : 0 ≤ (∫ u, f u) := integral_nonneg hfnn
  have hSX : 0 ≤ Real.sqrt (∫ u, (f u) ^ 2) := Real.sqrt_nonneg _
  have hSG : 0 ≤ Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) := Real.sqrt_nonneg _
  have hmax1 : (1:ℝ) ≤ max 1 (1 / Real.sqrt c₁) := le_max_left _ _
  have hmax2 : (1 / Real.sqrt c₁) ≤ max 1 (1 / Real.sqrt c₁) := le_max_right _ _
  have hmaxnn : 0 ≤ max 1 (1 / Real.sqrt c₁) := le_trans zero_le_one hmax1
  have hd := hdil' hM₂ hf hfnn hSupp
  rw [show (∫ u, (f u) ^ 2) ^ (1 / 2 : ℝ) = Real.sqrt (∫ u, (f u) ^ 2)
        from (Real.sqrt_eq_rpow _).symm] at hd
  have hcoh := hcoher hT hM₂ hf hfnn hSupp
  have hc₁sqrt : 0 < Real.sqrt c₁ := Real.sqrt_pos.mpr hc₁pos
  have hsqeq : Real.sqrt (c₁ * M₂ ^ 6 * (∫ u, f u) ^ 2)
      = Real.sqrt c₁ * (M₂ ^ 3 * ∫ u, f u) := by
    rw [show c₁ * M₂ ^ 6 * (∫ u, f u) ^ 2 = c₁ * (M₂ ^ 3 * ∫ u, f u) ^ 2 from by ring]
    rw [Real.sqrt_mul hc₁pos.le, Real.sqrt_sq (by positivity)]
  have hle : Real.sqrt c₁ * (M₂ ^ 3 * ∫ u, f u)
      ≤ Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) := by
    rw [← hsqeq]; exact Real.sqrt_le_sqrt hcoh
  have hMI : M₂ ^ 3 * (∫ u, f u)
      ≤ Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) / Real.sqrt c₁ := by
    rw [le_div_iff₀ hc₁sqrt]
    calc (M₂ ^ 3 * (∫ u, f u)) * Real.sqrt c₁ = Real.sqrt c₁ * (M₂ ^ 3 * (∫ u, f u)) := by ring
      _ ≤ Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) := hle
  have hkey : M₂ ^ 3 * Real.sqrt (∫ u, (f u) ^ 2) * (∫ u, f u)
      ≤ (Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) / Real.sqrt c₁)
        * Real.sqrt (∫ u, (f u) ^ 2) := by
    rw [show M₂ ^ 3 * Real.sqrt (∫ u, (f u) ^ 2) * (∫ u, f u)
        = (M₂ ^ 3 * (∫ u, f u)) * Real.sqrt (∫ u, (f u) ^ 2) from by ring]
    exact mul_le_mul_of_nonneg_right hMI hSX
  have hstep : (∫ u, (∑ m₂ ∈ R2 M₂, f (u / (m₂ : ℝ))) ^ 2)
      ≤ C₂ * M₂ ^ (δ / 4) * (max 1 (1 / Real.sqrt c₁)
          * (M₂ ^ 2 * (∫ u, (f u) ^ 2) + Real.sqrt (∫ u, (f u) ^ 2)
            * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2))) := by
    refine hd.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC₂pos.le hUnn)
    have h1 : (Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) / Real.sqrt c₁)
          * Real.sqrt (∫ u, (f u) ^ 2)
        ≤ max 1 (1 / Real.sqrt c₁)
          * (Real.sqrt (∫ u, (f u) ^ 2) * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)) := by
      rw [show (Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) / Real.sqrt c₁)
            * Real.sqrt (∫ u, (f u) ^ 2)
          = (1 / Real.sqrt c₁)
            * (Real.sqrt (∫ u, (f u) ^ 2) * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)) from by ring]
      exact mul_le_mul_of_nonneg_right hmax2 (mul_nonneg hSX hSG)
    have h2 : M₂ ^ 2 * (∫ u, (f u) ^ 2) + M₂ ^ 3 * Real.sqrt (∫ u, (f u) ^ 2) * (∫ u, f u)
        ≤ M₂ ^ 2 * (∫ u, (f u) ^ 2)
          + (Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) / Real.sqrt c₁)
            * Real.sqrt (∫ u, (f u) ^ 2) := by linarith [hkey]
    have h3 : M₂ ^ 2 * (∫ u, (f u) ^ 2)
          + (Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) / Real.sqrt c₁)
            * Real.sqrt (∫ u, (f u) ^ 2)
        ≤ max 1 (1 / Real.sqrt c₁)
          * (M₂ ^ 2 * (∫ u, (f u) ^ 2)
            + Real.sqrt (∫ u, (f u) ^ 2) * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)) := by
      have h4 : M₂ ^ 2 * (∫ u, (f u) ^ 2)
          ≤ max 1 (1 / Real.sqrt c₁) * (M₂ ^ 2 * (∫ u, (f u) ^ 2)) := by
        have h := mul_le_mul_of_nonneg_right hmax1 (mul_nonneg (sq_nonneg M₂) hXnn)
        linarith [h]
      rw [mul_add]
      linarith [h1, h4]
    linarith [h2, h3]
  have hstep2 : C₂ * M₂ ^ (δ / 4) * (max 1 (1 / Real.sqrt c₁)
        * (M₂ ^ 2 * (∫ u, (f u) ^ 2) + Real.sqrt (∫ u, (f u) ^ 2)
          * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)))
      ≤ C₂ * T ^ δ * (max 1 (1 / Real.sqrt c₁)
        * (M₂ ^ 2 * (∫ u, (f u) ^ 2) + Real.sqrt (∫ u, (f u) ^ 2)
          * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2))) := by
    refine mul_le_mul_of_nonneg_right ?_
      (mul_nonneg hmaxnn (add_nonneg (mul_nonneg (sq_nonneg M₂) hXnn) (mul_nonneg hSX hSG)))
    exact mul_le_mul_of_nonneg_left hpow hC₂pos.le
  have hstep3 : C₂ * T ^ δ * (max 1 (1 / Real.sqrt c₁)
        * (M₂ ^ 2 * (∫ u, (f u) ^ 2) + Real.sqrt (∫ u, (f u) ^ 2)
          * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)))
      ≤ (C₂ * max 1 (1 / Real.sqrt c₁) + 1) * T ^ δ
        * (Real.sqrt (∫ u, (f u) ^ 2) * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)
          + M₂ ^ 2 * (∫ u, (f u) ^ 2)) := by
    have he : C₂ * T ^ δ * (max 1 (1 / Real.sqrt c₁)
          * (M₂ ^ 2 * (∫ u, (f u) ^ 2) + Real.sqrt (∫ u, (f u) ^ 2)
            * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)))
        = C₂ * max 1 (1 / Real.sqrt c₁) * T ^ δ
          * (Real.sqrt (∫ u, (f u) ^ 2) * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)
            + M₂ ^ 2 * (∫ u, (f u) ^ 2)) := by ring
    rw [he]
    have hnn : 0 ≤ T ^ δ * (Real.sqrt (∫ u, (f u) ^ 2) * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)
        + M₂ ^ 2 * (∫ u, (f u) ^ 2)) :=
      mul_nonneg hVnn (add_nonneg (mul_nonneg hSX hSG) (mul_nonneg (sq_nonneg M₂) hXnn))
    nlinarith [hnn]
  exact hstep.trans (hstep2.trans hstep3)

/-! ## Arithmetic for the assembly -/

/-- The sampling branch: `M₂ ≤ M₃`. -/
lemma arith_sampling {Cs Cc M₂ M₃ SX SG X : ℝ} (hCs : 0 ≤ Cs) (hCc : 0 ≤ Cc)
    (hM₂ : 1 ≤ M₂) (hle : M₂ ≤ M₃) (hSX : 0 ≤ SX) (hSG : 0 ≤ SG) (hX : 0 ≤ X) :
    Cs * (1 + M₂) * (Cc * (SX * SG + M₂ ^ 2 * X)) ≤
      (2 * Cs * Cc) * (M₂ * SX * SG + M₂ ^ 2 * M₃ * X) := by
  have hP : 0 ≤ SX * SG := mul_nonneg hSX hSG
  have hmul : M₂ * SX * SG = M₂ * (SX * SG) := by ring
  rw [hmul]
  have h1 : (1 + M₂) ≤ 2 * M₂ := by linarith
  have h2 : (1 + M₂) * M₂ ^ 2 ≤ 2 * M₂ ^ 2 * M₃ := by
    have h3 : (1 + M₂) * M₂ ^ 2 ≤ (2 * M₂) * M₂ ^ 2 :=
      mul_le_mul_of_nonneg_right h1 (sq_nonneg M₂)
    have h5 : M₂ ^ 3 ≤ M₂ ^ 2 * M₃ := by
      calc M₂ ^ 3 = M₂ ^ 2 * M₂ := by ring
        _ ≤ M₂ ^ 2 * M₃ := mul_le_mul_of_nonneg_left hle (sq_nonneg M₂)
    nlinarith [h3, h5]
  have he : Cs * (1 + M₂) * (Cc * (SX * SG + M₂ ^ 2 * X))
      = Cs * Cc * ((1 + M₂) * (SX * SG) + ((1 + M₂) * M₂ ^ 2) * X) := by ring
  rw [he]
  have hA : (1 + M₂) * (SX * SG) ≤ (2 * M₂) * (SX * SG) := mul_le_mul_of_nonneg_right h1 hP
  have hB : ((1 + M₂) * M₂ ^ 2) * X ≤ (2 * M₂ ^ 2 * M₃) * X :=
    mul_le_mul_of_nonneg_right h2 hX
  calc Cs * Cc * ((1 + M₂) * (SX * SG) + ((1 + M₂) * M₂ ^ 2) * X)
      ≤ Cs * Cc * ((2 * M₂) * (SX * SG) + (2 * M₂ ^ 2 * M₃) * X) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) (mul_nonneg hCs hCc)
    _ = (2 * Cs * Cc) * (M₂ * (SX * SG) + M₂ ^ 2 * M₃ * X) := by ring

/-- The window branch: `M₃ < M₂`. -/
lemma arith_window {Cc M₂ M₃ SX SG X : ℝ} (hCc : 0 ≤ Cc) (hM₂ : 1 ≤ M₂) (hM₃ : 1 ≤ M₃)
    (hlt : M₃ < M₂) (hSX : 0 ≤ SX) (hSG : 0 ≤ SG) (hX : 0 ≤ X) :
    (M₃ + 4) * (Cc * (SX * SG + M₂ ^ 2 * X)) ≤
      (5 * Cc) * (M₂ * SX * SG + M₂ ^ 2 * M₃ * X) := by
  have hP : 0 ≤ SX * SG := mul_nonneg hSX hSG
  have hmul : M₂ * SX * SG = M₂ * (SX * SG) := by ring
  rw [hmul]
  have h34 : M₃ + 4 ≤ 5 * M₃ := by linarith
  have h35 : M₃ + 4 ≤ 5 * M₂ := by linarith
  have he : (M₃ + 4) * (Cc * (SX * SG + M₂ ^ 2 * X))
      = Cc * ((M₃ + 4) * (SX * SG) + ((M₃ + 4) * M₂ ^ 2) * X) := by ring
  rw [he]
  have hA : (M₃ + 4) * (SX * SG) ≤ (5 * M₂) * (SX * SG) := mul_le_mul_of_nonneg_right h35 hP
  have hB : ((M₃ + 4) * M₂ ^ 2) * X ≤ ((5 * M₃) * M₂ ^ 2) * X :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h34 (sq_nonneg M₂)) hX
  calc Cc * ((M₃ + 4) * (SX * SG) + ((M₃ + 4) * M₂ ^ 2) * X)
      ≤ Cc * ((5 * M₂) * (SX * SG) + ((5 * M₃) * M₂ ^ 2) * X) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) hCc
    _ = (5 * Cc) * (M₂ * (SX * SG) + M₂ ^ 2 * M₃ * X) := by ring

/-! ## The assembly -/

/-- **Assembly.** The target follows from the band-limited sampling bound `winmass_sampling`,
the elementary window bound `WinMass_window_le`, and the profile bound returned by `hcore`. -/
theorem winmass_core_of_core {C₀ T₀ C₃ : ℝ} (hC₀ : 1 ≤ C₀) (hT₀ : 1 ≤ T₀) (hC₃ : 1 ≤ C₃)
    (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hcore : ∃ C : ℝ, 0 < C ∧
      ∀ {T M₂ : ℝ}, 1 ≤ T → 1 ≤ M₂ → M₂ ≤ T ^ 4 → ∀ {f : ℝ → ℝ}, Continuous f →
        (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        (∫ u, (∑ m₂ ∈ R2 M₂, f (u / (m₂ : ℝ))) ^ 2) ≤
          C * T ^ δ * (Real.sqrt (∫ u, (f u) ^ 2) * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)
            + M₂ ^ 2 * (∫ u, (f u) ^ 2))) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ Mbig M₂ M₃ : ℝ,
        1 ≤ Mbig → Mbig ≤ T ^ 4 → 1 ≤ M₃ → M₃ ≤ C₃ * Mbig → 0 < M₂ → M₂ ≤ Mbig →
        WinMass f M₂ M₃ ≤
          C' * T ^ δ * (M₂ * (∫ u, (f u) ^ 2) ^ (1/2:ℝ) *
              (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) +
            M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2) := by
  obtain ⟨Cs, hCspos, hsamp⟩ := winmass_sampling hC₀
  obtain ⟨Cc, hCcpos, hcore'⟩ := hcore
  refine ⟨max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20, by positivity, ?_⟩
  intro T hTT₀ f hf hfnn hSupp Λ hΛ hdecay hΛbd Mbig M₂ M₃
    hMbig hMbigT hM₃ hM₃M hM₂pos hM₂Mbig
  have hT1 : (1:ℝ) ≤ T := le_trans hT₀ hTT₀
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hTδ1 : (1:ℝ) ≤ T ^ δ := Real.one_le_rpow hT1 hδ.le
  have hTδnn : (0:ℝ) ≤ T ^ δ := le_trans zero_le_one hTδ1
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  have hcs : HasCompactSupport f := winmass_hcs_of_suppHyp hSupp
  rw [show (∫ u, (f u) ^ 2) ^ (1/2:ℝ) = Real.sqrt (∫ u, (f u) ^ 2)
        from (Real.sqrt_eq_rpow _).symm,
      show (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ)
        = Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) from (Real.sqrt_eq_rpow _).symm]
  set B : ℝ := ∫ u, (f u) ^ 2 with hB
  set SX : ℝ := Real.sqrt (∫ u, (f u) ^ 2) with hSXdef
  set SG : ℝ := Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) with hSGdef
  set Q : ℝ := M₂ * SX * SG + M₂ ^ 2 * M₃ * B with hQ
  have hBnn : 0 ≤ B := by rw [hB]; exact integral_nonneg (fun u => sq_nonneg _)
  have hSXnn : 0 ≤ SX := by rw [hSXdef]; exact Real.sqrt_nonneg _
  have hSGnn : 0 ≤ SG := by rw [hSGdef]; exact Real.sqrt_nonneg _
  have hPnn : 0 ≤ SX * SG := mul_nonneg hSXnn hSGnn
  have hQnn : 0 ≤ Q := by
    rw [hQ]
    exact add_nonneg (mul_nonneg (mul_nonneg hM₂pos.le hSXnn) hSGnn)
      (mul_nonneg (mul_nonneg (sq_nonneg M₂) hM₃pos.le) hBnn)
  have hM₂T : M₂ ≤ T ^ 4 := le_trans hM₂Mbig hMbigT
  have hconst : (2 * Cs * Cc) ≤ max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 := by
    have h1 : (2 * Cs) ≤ max (2 * Cs) 5 + 1 := by linarith [le_max_left (2 * Cs) (5:ℝ)]
    have h3 : 2 * Cs * Cc ≤ (max (2 * Cs) 5 + 1) * (Cc + 1) := by
      calc 2 * Cs * Cc ≤ (max (2 * Cs) 5 + 1) * Cc := mul_le_mul_of_nonneg_right h1 hCcpos.le
        _ ≤ (max (2 * Cs) 5 + 1) * (Cc + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact le_trans h3 (le_max_left _ _)
  have hconst5 : (5 * Cc) ≤ max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 := by
    have h1 : (5:ℝ) ≤ max (2 * Cs) 5 + 1 := by linarith [le_max_right (2 * Cs) (5:ℝ)]
    have h3 : 5 * Cc ≤ (max (2 * Cs) 5 + 1) * (Cc + 1) := by
      calc 5 * Cc ≤ (max (2 * Cs) 5 + 1) * Cc := mul_le_mul_of_nonneg_right h1 hCcpos.le
        _ ≤ (max (2 * Cs) 5 + 1) * (Cc + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact le_trans h3 (le_max_left _ _)
  have hconst20 : (20:ℝ) ≤ max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 := le_max_right _ _
  have hmain : WinMass f M₂ M₃ ≤ max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 * T ^ δ * Q := by
    by_cases hM₂1 : 1 ≤ M₂
    · have hcor := hcore' hT1 hM₂1 hM₂T hf hfnn hSupp
      rw [← hSXdef, ← hSGdef, ← hB] at hcor
      by_cases hle : M₂ ≤ M₃
      · have hs := hsamp M₂ M₃ hM₂pos hM₃pos f hf hcs hSupp
        have h1 : WinMass f M₂ M₃ ≤ Cs * (1 + M₂) * (Cc * T ^ δ * (SX * SG + M₂ ^ 2 * B)) :=
          le_trans hs (mul_le_mul_of_nonneg_left hcor (by positivity))
        have h2 := arith_sampling (Cs := Cs) (Cc := Cc) (M₂ := M₂) (M₃ := M₃)
          (SX := SX) (SG := SG) (X := B) hCspos.le hCcpos.le hM₂1 hle hSXnn hSGnn hBnn
        have key : Cs * (1 + M₂) * (Cc * T ^ δ * (SX * SG + M₂ ^ 2 * B))
            = Cs * (1 + M₂) * (Cc * (SX * SG + M₂ ^ 2 * B)) * T ^ δ := by ring
        calc WinMass f M₂ M₃ ≤ Cs * (1 + M₂) * (Cc * T ^ δ * (SX * SG + M₂ ^ 2 * B)) := h1
          _ = Cs * (1 + M₂) * (Cc * (SX * SG + M₂ ^ 2 * B)) * T ^ δ := key
          _ ≤ (2 * Cs * Cc) * (M₂ * SX * SG + M₂ ^ 2 * M₃ * B) * T ^ δ :=
              mul_le_mul_of_nonneg_right h2 hTδnn
          _ = (2 * Cs * Cc) * (Q * T ^ δ) := by rw [hQ]; ring
          _ ≤ max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 * (Q * T ^ δ) :=
              mul_le_mul_of_nonneg_right hconst (mul_nonneg hQnn hTδnn)
          _ = max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 * T ^ δ * Q := by ring
      · push_neg at hle
        have hw := WinMass_window_le hC₀ hM₂pos hM₃pos hf hcs hSupp
        have hw' : WinMass f M₂ M₃
            ≤ (M₃ + 4) * (∫ u, (∑ m₂ ∈ R2 M₂, f (u / (m₂ : ℝ))) ^ 2) := hw
        have h1 : WinMass f M₂ M₃ ≤ (M₃ + 4) * (Cc * T ^ δ * (SX * SG + M₂ ^ 2 * B)) :=
          le_trans hw' (mul_le_mul_of_nonneg_left hcor (by linarith))
        have h2 := arith_window (Cc := Cc) (M₂ := M₂) (M₃ := M₃)
          (SX := SX) (SG := SG) (X := B) hCcpos.le hM₂1 hM₃ hle hSXnn hSGnn hBnn
        have key : (M₃ + 4) * (Cc * T ^ δ * (SX * SG + M₂ ^ 2 * B))
            = (M₃ + 4) * (Cc * (SX * SG + M₂ ^ 2 * B)) * T ^ δ := by ring
        calc WinMass f M₂ M₃ ≤ (M₃ + 4) * (Cc * T ^ δ * (SX * SG + M₂ ^ 2 * B)) := h1
          _ = (M₃ + 4) * (Cc * (SX * SG + M₂ ^ 2 * B)) * T ^ δ := key
          _ ≤ (5 * Cc) * (M₂ * SX * SG + M₂ ^ 2 * M₃ * B) * T ^ δ :=
              mul_le_mul_of_nonneg_right h2 hTδnn
          _ = (5 * Cc) * (Q * T ^ δ) := by rw [hQ]; ring
          _ ≤ max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 * (Q * T ^ δ) :=
              mul_le_mul_of_nonneg_right hconst5 (mul_nonneg hQnn hTδnn)
          _ = max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 * T ^ δ * Q := by ring
    · push_neg at hM₂1
      have hw := WinMass_window_le hC₀ hM₂pos hM₃pos hf hcs hSupp
      by_cases hhalf : M₂ < 1/2
      · have hR2 : R2 M₂ = ∅ := winmass_R2_eq_empty hhalf
        have hHz : ∀ u, Hprof f M₂ u = 0 := by intro u; simp [Hprof, hR2]
        have hzero : (∫ u, (Hprof f M₂ u) ^ 2) = 0 := by
          have : (fun u => (Hprof f M₂ u) ^ 2) = fun _ => (0:ℝ) :=
            funext (fun u => by rw [hHz u]; norm_num)
          rw [this]; simp
        have hle0 : WinMass f M₂ M₃ ≤ 0 := by
          calc WinMass f M₂ M₃ ≤ (M₃ + 4) * (∫ u, (Hprof f M₂ u) ^ 2) := hw
            _ = 0 := by rw [hzero, mul_zero]
        exact le_trans hle0 (mul_nonneg (by positivity) hQnn)
      · push_neg at hhalf
        have h20 : (M₃ + 4) ≤ 20 * (M₂ ^ 2 * M₃) := by
          have hM₂2 : (1:ℝ)/4 ≤ M₂ ^ 2 := by nlinarith [hhalf, hM₂pos]
          nlinarith [hM₃, hM₂2]
        have hHle : (∫ u, (Hprof f M₂ u) ^ 2) ≤ B := by
          rw [hB]
          have hf2int : Integrable (fun u : ℝ => (f u) ^ 2) := by
            have h2cs : HasCompactSupport (fun u : ℝ => (f u) ^ 2) := by
              refine HasCompactSupport.of_support_subset_isCompact hcs ?_
              intro u hu
              rw [Function.mem_support] at hu
              refine subset_closure (Function.mem_support.mpr ?_)
              intro h0
              exact hu (by rw [h0]; norm_num)
            exact (hf.pow 2).integrable_of_hasCompactSupport h2cs
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun u => sq_nonneg _)) hf2int
            (Filter.Eventually.of_forall (fun u => ?_))
          have h1 : 0 ≤ Hprof f M₂ u := by
            unfold Hprof
            exact Finset.sum_nonneg (fun m _ => hfnn _)
          have h2 : Hprof f M₂ u ≤ f u := winmass_Hprof_le_self hM₂1 hfnn u
          exact pow_le_pow_left₀ h1 h2 2
        have hQle : M₂ ^ 2 * M₃ * B ≤ Q := by
          rw [hQ]
          linarith [mul_nonneg (mul_nonneg hM₂pos.le hSXnn) hSGnn]
        have hstep0 : WinMass f M₂ M₃ ≤ 20 * (M₂ ^ 2 * M₃ * B) := by
          calc WinMass f M₂ M₃ ≤ (M₃ + 4) * (∫ u, (Hprof f M₂ u) ^ 2) := hw
            _ ≤ (M₃ + 4) * B := mul_le_mul_of_nonneg_left hHle (by linarith)
            _ ≤ 20 * (M₂ ^ 2 * M₃ * B) := by
                have h := mul_le_mul_of_nonneg_right h20 hBnn
                linarith [h]
        calc WinMass f M₂ M₃ ≤ 20 * (M₂ ^ 2 * M₃ * B) := hstep0
          _ ≤ 20 * Q := by nlinarith [hQle]
          _ ≤ max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 * (Q * T ^ δ) := by
              have h1 : 20 * Q ≤ max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 * Q :=
                mul_le_mul_of_nonneg_right hconst20 hQnn
              have h3 : max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 * Q
                  ≤ max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 * (Q * T ^ δ) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                nlinarith [hQnn, hTδ1]
              exact le_trans h1 h3
          _ = max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 * T ^ δ * Q := by ring
  exact hmain

theorem winmass_core_of_core_decay {C₀ T₀ C₃ : ℝ} (hC₀ : 1 ≤ C₀) (hT₀ : 1 ≤ T₀) (hC₃ : 1 ≤ C₃)
    (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hcore : ∃ C : ℝ, 0 < C ∧
      ∀ (T : ℝ), 1 ≤ T → ∀ (f : ℝ → ℝ), Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ M₂ : ℝ, 1 ≤ M₂ → M₂ ≤ T ^ 4 →
        (∫ u, (∑ m₂ ∈ R2 M₂, f (u / (m₂ : ℝ))) ^ 2) ≤
          C * T ^ δ * (Real.sqrt (∫ u, (f u) ^ 2) * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)
            + M₂ ^ 2 * (∫ u, (f u) ^ 2))) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ Mbig M₂ M₃ : ℝ,
        1 ≤ Mbig → Mbig ≤ T ^ 4 → 1 ≤ M₃ → M₃ ≤ C₃ * Mbig → 0 < M₂ → M₂ ≤ Mbig →
        WinMass f M₂ M₃ ≤
          C' * T ^ δ * (M₂ * (∫ u, (f u) ^ 2) ^ (1/2:ℝ) *
              (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) +
            M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2) := by
  obtain ⟨Cs, hCspos, hsamp⟩ := winmass_sampling hC₀
  obtain ⟨Cc, hCcpos, hcore'⟩ := hcore
  refine ⟨max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20, by positivity, ?_⟩
  intro T hTT₀ f hf hfnn hSupp Λ hΛ hdecay hΛbd Mbig M₂ M₃
    hMbig hMbigT hM₃ hM₃M hM₂pos hM₂Mbig
  have hT1 : (1:ℝ) ≤ T := le_trans hT₀ hTT₀
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hTδ1 : (1:ℝ) ≤ T ^ δ := Real.one_le_rpow hT1 hδ.le
  have hTδnn : (0:ℝ) ≤ T ^ δ := le_trans zero_le_one hTδ1
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  have hcs : HasCompactSupport f := winmass_hcs_of_suppHyp hSupp
  rw [show (∫ u, (f u) ^ 2) ^ (1/2:ℝ) = Real.sqrt (∫ u, (f u) ^ 2)
        from (Real.sqrt_eq_rpow _).symm,
      show (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ)
        = Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) from (Real.sqrt_eq_rpow _).symm]
  set B : ℝ := ∫ u, (f u) ^ 2 with hB
  set SX : ℝ := Real.sqrt (∫ u, (f u) ^ 2) with hSXdef
  set SG : ℝ := Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) with hSGdef
  set Q : ℝ := M₂ * SX * SG + M₂ ^ 2 * M₃ * B with hQ
  have hBnn : 0 ≤ B := by rw [hB]; exact integral_nonneg (fun u => sq_nonneg _)
  have hSXnn : 0 ≤ SX := by rw [hSXdef]; exact Real.sqrt_nonneg _
  have hSGnn : 0 ≤ SG := by rw [hSGdef]; exact Real.sqrt_nonneg _
  have hPnn : 0 ≤ SX * SG := mul_nonneg hSXnn hSGnn
  have hQnn : 0 ≤ Q := by
    rw [hQ]
    exact add_nonneg (mul_nonneg (mul_nonneg hM₂pos.le hSXnn) hSGnn)
      (mul_nonneg (mul_nonneg (sq_nonneg M₂) hM₃pos.le) hBnn)
  have hM₂T : M₂ ≤ T ^ 4 := le_trans hM₂Mbig hMbigT
  have hconst : (2 * Cs * Cc) ≤ max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 := by
    have h1 : (2 * Cs) ≤ max (2 * Cs) 5 + 1 := by linarith [le_max_left (2 * Cs) (5:ℝ)]
    have h3 : 2 * Cs * Cc ≤ (max (2 * Cs) 5 + 1) * (Cc + 1) := by
      calc 2 * Cs * Cc ≤ (max (2 * Cs) 5 + 1) * Cc := mul_le_mul_of_nonneg_right h1 hCcpos.le
        _ ≤ (max (2 * Cs) 5 + 1) * (Cc + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact le_trans h3 (le_max_left _ _)
  have hconst5 : (5 * Cc) ≤ max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 := by
    have h1 : (5:ℝ) ≤ max (2 * Cs) 5 + 1 := by linarith [le_max_right (2 * Cs) (5:ℝ)]
    have h3 : 5 * Cc ≤ (max (2 * Cs) 5 + 1) * (Cc + 1) := by
      calc 5 * Cc ≤ (max (2 * Cs) 5 + 1) * Cc := mul_le_mul_of_nonneg_right h1 hCcpos.le
        _ ≤ (max (2 * Cs) 5 + 1) * (Cc + 1) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact le_trans h3 (le_max_left _ _)
  have hconst20 : (20:ℝ) ≤ max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 := le_max_right _ _
  have hmain : WinMass f M₂ M₃ ≤ max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 * T ^ δ * Q := by
    by_cases hM₂1 : 1 ≤ M₂
    · have hcor : (∫ u, (∑ m₂ ∈ R2 M₂, f (u / (m₂ : ℝ))) ^ 2)
          ≤ Cc * T ^ δ * (SX * SG + M₂ ^ 2 * B) :=
        hcore' T hT1 f hf hfnn hSupp Λ hΛ hdecay hΛbd M₂ hM₂1 hM₂T
      by_cases hle : M₂ ≤ M₃
      · have hs := hsamp M₂ M₃ hM₂pos hM₃pos f hf hcs hSupp
        have h1 : WinMass f M₂ M₃ ≤ Cs * (1 + M₂) * (Cc * T ^ δ * (SX * SG + M₂ ^ 2 * B)) :=
          le_trans hs (mul_le_mul_of_nonneg_left hcor (by positivity))
        have h2 := arith_sampling (Cs := Cs) (Cc := Cc) (M₂ := M₂) (M₃ := M₃)
          (SX := SX) (SG := SG) (X := B) hCspos.le hCcpos.le hM₂1 hle hSXnn hSGnn hBnn
        have key : Cs * (1 + M₂) * (Cc * T ^ δ * (SX * SG + M₂ ^ 2 * B))
            = Cs * (1 + M₂) * (Cc * (SX * SG + M₂ ^ 2 * B)) * T ^ δ := by ring
        calc WinMass f M₂ M₃ ≤ Cs * (1 + M₂) * (Cc * T ^ δ * (SX * SG + M₂ ^ 2 * B)) := h1
          _ = Cs * (1 + M₂) * (Cc * (SX * SG + M₂ ^ 2 * B)) * T ^ δ := key
          _ ≤ (2 * Cs * Cc) * (M₂ * SX * SG + M₂ ^ 2 * M₃ * B) * T ^ δ :=
              mul_le_mul_of_nonneg_right h2 hTδnn
          _ = (2 * Cs * Cc) * (Q * T ^ δ) := by rw [hQ]; ring
          _ ≤ max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 * (Q * T ^ δ) :=
              mul_le_mul_of_nonneg_right hconst (mul_nonneg hQnn hTδnn)
          _ = max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 * T ^ δ * Q := by ring
      · push_neg at hle
        have hw := WinMass_window_le hC₀ hM₂pos hM₃pos hf hcs hSupp
        have hw' : WinMass f M₂ M₃
            ≤ (M₃ + 4) * (∫ u, (∑ m₂ ∈ R2 M₂, f (u / (m₂ : ℝ))) ^ 2) := hw
        have h1 : WinMass f M₂ M₃ ≤ (M₃ + 4) * (Cc * T ^ δ * (SX * SG + M₂ ^ 2 * B)) :=
          le_trans hw' (mul_le_mul_of_nonneg_left hcor (by linarith))
        have h2 := arith_window (Cc := Cc) (M₂ := M₂) (M₃ := M₃)
          (SX := SX) (SG := SG) (X := B) hCcpos.le hM₂1 hM₃ hle hSXnn hSGnn hBnn
        have key : (M₃ + 4) * (Cc * T ^ δ * (SX * SG + M₂ ^ 2 * B))
            = (M₃ + 4) * (Cc * (SX * SG + M₂ ^ 2 * B)) * T ^ δ := by ring
        calc WinMass f M₂ M₃ ≤ (M₃ + 4) * (Cc * T ^ δ * (SX * SG + M₂ ^ 2 * B)) := h1
          _ = (M₃ + 4) * (Cc * (SX * SG + M₂ ^ 2 * B)) * T ^ δ := key
          _ ≤ (5 * Cc) * (M₂ * SX * SG + M₂ ^ 2 * M₃ * B) * T ^ δ :=
              mul_le_mul_of_nonneg_right h2 hTδnn
          _ = (5 * Cc) * (Q * T ^ δ) := by rw [hQ]; ring
          _ ≤ max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 * (Q * T ^ δ) :=
              mul_le_mul_of_nonneg_right hconst5 (mul_nonneg hQnn hTδnn)
          _ = max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 * T ^ δ * Q := by ring
    · push_neg at hM₂1
      have hw := WinMass_window_le hC₀ hM₂pos hM₃pos hf hcs hSupp
      by_cases hhalf : M₂ < 1/2
      · have hR2 : R2 M₂ = ∅ := winmass_R2_eq_empty hhalf
        have hHz : ∀ u, Hprof f M₂ u = 0 := by intro u; simp [Hprof, hR2]
        have hzero : (∫ u, (Hprof f M₂ u) ^ 2) = 0 := by
          have : (fun u => (Hprof f M₂ u) ^ 2) = fun _ => (0:ℝ) :=
            funext (fun u => by rw [hHz u]; norm_num)
          rw [this]; simp
        have hle0 : WinMass f M₂ M₃ ≤ 0 := by
          calc WinMass f M₂ M₃ ≤ (M₃ + 4) * (∫ u, (Hprof f M₂ u) ^ 2) := hw
            _ = 0 := by rw [hzero, mul_zero]
        exact le_trans hle0 (mul_nonneg (by positivity) hQnn)
      · push_neg at hhalf
        have h20 : (M₃ + 4) ≤ 20 * (M₂ ^ 2 * M₃) := by
          have hM₂2 : (1:ℝ)/4 ≤ M₂ ^ 2 := by nlinarith [hhalf, hM₂pos]
          nlinarith [hM₃, hM₂2]
        have hHle : (∫ u, (Hprof f M₂ u) ^ 2) ≤ B := by
          rw [hB]
          have hf2int : Integrable (fun u : ℝ => (f u) ^ 2) := by
            have h2cs : HasCompactSupport (fun u : ℝ => (f u) ^ 2) := by
              refine HasCompactSupport.of_support_subset_isCompact hcs ?_
              intro u hu
              rw [Function.mem_support] at hu
              refine subset_closure (Function.mem_support.mpr ?_)
              intro h0
              exact hu (by rw [h0]; norm_num)
            exact (hf.pow 2).integrable_of_hasCompactSupport h2cs
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun u => sq_nonneg _)) hf2int
            (Filter.Eventually.of_forall (fun u => ?_))
          have h1 : 0 ≤ Hprof f M₂ u := by
            unfold Hprof
            exact Finset.sum_nonneg (fun m _ => hfnn _)
          have h2 : Hprof f M₂ u ≤ f u := winmass_Hprof_le_self hM₂1 hfnn u
          exact pow_le_pow_left₀ h1 h2 2
        have hQle : M₂ ^ 2 * M₃ * B ≤ Q := by
          rw [hQ]
          linarith [mul_nonneg (mul_nonneg hM₂pos.le hSXnn) hSGnn]
        have hstep0 : WinMass f M₂ M₃ ≤ 20 * (M₂ ^ 2 * M₃ * B) := by
          calc WinMass f M₂ M₃ ≤ (M₃ + 4) * (∫ u, (Hprof f M₂ u) ^ 2) := hw
            _ ≤ (M₃ + 4) * B := mul_le_mul_of_nonneg_left hHle (by linarith)
            _ ≤ 20 * (M₂ ^ 2 * M₃ * B) := by
                have h := mul_le_mul_of_nonneg_right h20 hBnn
                linarith [h]
        calc WinMass f M₂ M₃ ≤ 20 * (M₂ ^ 2 * M₃ * B) := hstep0
          _ ≤ 20 * Q := by nlinarith [hQle]
          _ ≤ max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 * (Q * T ^ δ) := by
              have h1 : 20 * Q ≤ max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 * Q :=
                mul_le_mul_of_nonneg_right hconst20 hQnn
              have h3 : max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 * Q
                  ≤ max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 * (Q * T ^ δ) := by
                refine mul_le_mul_of_nonneg_left ?_ (by positivity)
                nlinarith [hQnn, hTδ1]
              exact le_trans h1 h3
          _ = max ((max (2 * Cs) 5 + 1) * (Cc + 1)) 20 * T ^ δ * Q := by ring
  exact hmain


/-! ## The `M₃`-uniform crux/tail route to the target -/

/-- Degenerate range `M₂ < 1`: the window mass is dominated by `M₂² M₃ ∫f²`. -/
lemma winmass_le_small_M₂ {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {M₂ M₃ : ℝ} (hM₂ : 0 < M₂) (hM₃ : 1 ≤ M₃)
    {f : ℝ → ℝ} (hf : Continuous f) (hfnn : ∀ u, 0 ≤ f u) (hcs : HasCompactSupport f)
    (hSupp : SuppHyp C₀ f) (hM₂1 : M₂ < 1) :
    WinMass f M₂ M₃ ≤ 20 * M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2 := by
  have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
  have hw := WinMass_window_le hC₀ hM₂ hM₃pos hf hcs hSupp
  have hAnn : (0 : ℝ) ≤ ∫ u, (f u) ^ 2 := integral_nonneg (fun u => sq_nonneg _)
  by_cases hhalf : M₂ < 1 / 2
  · have hR2 : R2 M₂ = ∅ := winmass_R2_eq_empty hhalf
    have hHz : ∀ u, Hprof f M₂ u = 0 := by intro u; simp [Hprof, hR2]
    have hzero : (∫ u, (Hprof f M₂ u) ^ 2) = 0 := by
      have hfun : (fun u => (Hprof f M₂ u) ^ 2) = fun _ => (0 : ℝ) :=
        funext (fun u => by rw [hHz u]; norm_num)
      rw [hfun]; simp
    have hle0 : WinMass f M₂ M₃ ≤ 0 := by
      calc WinMass f M₂ M₃ ≤ (M₃ + 4) * (∫ u, (Hprof f M₂ u) ^ 2) := hw
        _ = 0 := by rw [hzero, mul_zero]
    exact le_trans hle0 (by positivity)
  · push_neg at hhalf
    have h20 : (M₃ + 4) ≤ 20 * (M₂ ^ 2 * M₃) := by
      have hM₂2 : (1 : ℝ) / 4 ≤ M₂ ^ 2 := by nlinarith [hhalf, hM₂]
      nlinarith [hM₃, hM₂2]
    have hHle : (∫ u, (Hprof f M₂ u) ^ 2) ≤ ∫ u, (f u) ^ 2 := by
      have hf2int : Integrable (fun u : ℝ => (f u) ^ 2) := by
        have h2cs : HasCompactSupport (fun u : ℝ => (f u) ^ 2) := by
          refine HasCompactSupport.of_support_subset_isCompact hcs ?_
          intro u hu
          rw [Function.mem_support] at hu
          refine subset_closure (Function.mem_support.mpr ?_)
          intro h0
          exact hu (by rw [h0]; norm_num)
        exact (hf.pow 2).integrable_of_hasCompactSupport h2cs
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun u => sq_nonneg _)) hf2int
        (Filter.Eventually.of_forall (fun u => ?_))
      have h1 : 0 ≤ Hprof f M₂ u := Finset.sum_nonneg (fun m _ => hfnn _)
      have h2 : Hprof f M₂ u ≤ f u := winmass_Hprof_le_self hM₂1 hfnn u
      exact pow_le_pow_left₀ h1 h2 2
    calc WinMass f M₂ M₃ ≤ (M₃ + 4) * (∫ u, (Hprof f M₂ u) ^ 2) := hw
      _ ≤ (M₃ + 4) * ∫ u, (f u) ^ 2 := mul_le_mul_of_nonneg_left hHle (by linarith)
      _ ≤ 20 * (M₂ ^ 2 * M₃) * ∫ u, (f u) ^ 2 :=
          mul_le_mul_of_nonneg_right h20 hAnn
      _ = 20 * M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2 := by ring

/-- **Conditional assembly.**  The `M₃`-uniform crux/tail bound (the conclusion of
`Work.GM.Affine.WinMass_crux_tail_uniform`) implies the target `WinMass_core`: the near-`ℓ`
part is the crux `Work.GM.Affine.window_spike_crux`, the far-`ℓ` part is
`Work.GM.Affine.window_far_tail`, and `M₂ < 1` is the elementary `winmass_le_small_M₂`. -/
theorem WinMass_core_of_uniform_bound {C₀ T₀ C₃ : ℝ} (hC₀ : 1 ≤ C₀) (hT₀ : 1 ≤ T₀)
    (hC₃ : 1 ≤ C₃) (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hU : ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, 1 ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ M₂ M₃ : ℝ, 1 ≤ M₂ → M₂ ≤ T ^ 4 → 1 ≤ M₃ →
          WinMass f M₂ M₃ ≤ C * T ^ δ * M₂ * Real.sqrt (∫ u, (f u) ^ 2) *
            Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ Mbig M₂ M₃ : ℝ,
        1 ≤ Mbig → Mbig ≤ T ^ 4 → 1 ≤ M₃ → M₃ ≤ C₃ * Mbig → 0 < M₂ → M₂ ≤ Mbig →
        WinMass f M₂ M₃ ≤
          C' * T ^ δ * (M₂ * (∫ u, (f u) ^ 2) ^ (1/2:ℝ) *
              (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) +
            M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2) := by
  obtain ⟨C₁, hC₁pos, hU'⟩ := hU
  refine ⟨max C₁ 20, lt_max_of_lt_left hC₁pos, ?_⟩
  intro T hTT₀ f hf hfnn hSupp Λ hΛ hdec hΛbd Mbig M₂ M₃ hMbig hMbigT hM₃ hM₃M hM₂pos hM₂Mbig
  have hT1 : (1 : ℝ) ≤ T := le_trans hT₀ hTT₀
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT1
  have hTδ1 : (1 : ℝ) ≤ T ^ δ := Real.one_le_rpow hT1 hδ.le
  have hTδnn : (0 : ℝ) ≤ T ^ δ := le_trans zero_le_one hTδ1
  have hcs : HasCompactSupport f := winmass_hcs_of_suppHyp hSupp
  have hAnn : (0 : ℝ) ≤ ∫ u, (f u) ^ 2 := integral_nonneg (fun u => sq_nonneg _)
  have hJnn : (0 : ℝ) ≤ ∫ u, (Gfun C₀ T M₂ f u) ^ 2 :=
    integral_nonneg (fun u => sq_nonneg _)
  have hM₂T4 : M₂ ≤ T ^ 4 := le_trans hM₂Mbig hMbigT
  have hsx : (0 : ℝ) ≤ Real.sqrt (∫ u, (f u) ^ 2) := Real.sqrt_nonneg _
  have hsg : (0 : ℝ) ≤ Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) := Real.sqrt_nonneg _
  have hSnn : (0 : ℝ) ≤ M₂ * Real.sqrt (∫ u, (f u) ^ 2)
      * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) := by positivity
  have hVnn : (0 : ℝ) ≤ M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2 := by
    have hM₃pos : (0 : ℝ) < M₃ := lt_of_lt_of_le zero_lt_one hM₃
    positivity
  have hCn : (0 : ℝ) ≤ max C₁ 20 := le_of_lt (lt_max_of_lt_left hC₁pos)
  rw [show (∫ u, (f u) ^ 2) ^ (1/2:ℝ) = Real.sqrt (∫ u, (f u) ^ 2)
        from (Real.sqrt_eq_rpow _).symm,
      show (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ)
        = Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) from (Real.sqrt_eq_rpow _).symm]
  by_cases hM₂1 : 1 ≤ M₂
  · have h := hU' T hT1 f hf hfnn hSupp Λ hΛ hdec hΛbd M₂ M₃ hM₂1 hM₂T4 hM₃
    have hstep1 : WinMass f M₂ M₃ ≤ max C₁ 20 * T ^ δ *
        (M₂ * Real.sqrt (∫ u, (f u) ^ 2) * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)) := by
      calc WinMass f M₂ M₃ ≤ C₁ * T ^ δ * M₂ * Real.sqrt (∫ u, (f u) ^ 2)
              * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2) := h
        _ = (C₁ * T ^ δ) * (M₂ * Real.sqrt (∫ u, (f u) ^ 2)
              * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)) := by ring
        _ ≤ (max C₁ 20 * T ^ δ) * (M₂ * Real.sqrt (∫ u, (f u) ^ 2)
              * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left C₁ 20) hTδnn) hSnn
        _ = max C₁ 20 * T ^ δ *
              (M₂ * Real.sqrt (∫ u, (f u) ^ 2) * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)) := by
            ring
    calc WinMass f M₂ M₃ ≤ max C₁ 20 * T ^ δ *
          (M₂ * Real.sqrt (∫ u, (f u) ^ 2) * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)) := hstep1
      _ ≤ max C₁ 20 * T ^ δ *
            (M₂ * Real.sqrt (∫ u, (f u) ^ 2) * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)
              + M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hVnn) (by positivity)
  · push_neg at hM₂1
    have hsmall := winmass_le_small_M₂ hC₀ hM₂pos hM₃ hf hfnn hcs hSupp hM₂1
    have hstep1 : WinMass f M₂ M₃ ≤ max C₁ 20 * (M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2) := by
      calc WinMass f M₂ M₃ ≤ 20 * M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2 := hsmall
        _ = 20 * (M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2) := by ring
        _ ≤ max C₁ 20 * (M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2) :=
            mul_le_mul_of_nonneg_right (le_max_right C₁ 20) hVnn
    calc WinMass f M₂ M₃ ≤ max C₁ 20 * (M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2) := hstep1
      _ ≤ max C₁ 20 * T ^ δ * (M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2) := by
          have h1 : max C₁ 20 * (M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2)
              = max C₁ 20 * 1 * (M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2) := by ring
          rw [h1]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hTδ1 hCn) hVnn
      _ ≤ max C₁ 20 * T ^ δ *
            (M₂ * Real.sqrt (∫ u, (f u) ^ 2) * Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)
              + M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2) := by
          have h1 : (0 : ℝ) ≤ max C₁ 20 * T ^ δ := by positivity
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hSnn) h1


/-- **The target from the two analytic inputs of GM §9.**  With the crux
(`Work.GM.Affine.window_spike_crux`, the near-`ℓ` window sum) and the tail
(`Work.GM.Affine.window_far_tail`, the far-`ℓ` window sum) as hypotheses, the target
`WinMass_core` follows: `WinMass_crux_tail_uniform` assembles the two into the `M₃`-uniform
bound, and `WinMass_core_of_uniform_bound` adds the `M₂ < 1` range. -/
theorem WinMass_core_of_crux_tail {C₀ T₀ C₃ : ℝ} (hC₀ : 1 ≤ C₀) (hT₀ : 1 ≤ T₀)
    (hC₃ : 1 ≤ C₃) (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hcrux : ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, 1 ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ M₂ M₃ K : ℝ, 1 ≤ M₂ → 1 ≤ M₃ → 8 ≤ K →
          (∑' ℓ : ℤ, (psi1 1 ((M₂ * (ℓ : ℝ)) / (K * T)) : ℝ) *
              ∫ τ in Set.Icc (-2 : ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2)
            ≤ C * T ^ δ * K * M₂ * (∫ u, f u * Gfun C₀ T M₂ f u))
    (htail : ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, 1 ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ M₂ M₃ K : ℝ, 1 ≤ M₂ → 1 ≤ M₃ → M₂ ≤ T ^ 4 → 8 ≤ K →
        ∀ s : Finset ℤ, (∀ ℓ ∈ s, K * T / M₂ < |(ℓ : ℝ)|) →
          (∑ ℓ ∈ s, ∫ τ in Set.Icc (-2 : ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2)
            ≤ C * T ^ δ * M₂ * Real.sqrt (∫ u, (f u) ^ 2) *
                Real.sqrt (∫ u, (Gfun C₀ T M₂ f u) ^ 2)) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ Mbig M₂ M₃ : ℝ,
        1 ≤ Mbig → Mbig ≤ T ^ 4 → 1 ≤ M₃ → M₃ ≤ C₃ * Mbig → 0 < M₂ → M₂ ≤ Mbig →
        WinMass f M₂ M₃ ≤
          C' * T ^ δ * (M₂ * (∫ u, (f u) ^ 2) ^ (1/2:ℝ) *
              (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) +
            M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2) :=
  WinMass_core_of_uniform_bound hC₀ hT₀ hC₃ c δ hδ
    (WinMass_crux_tail_uniform hC₀ c δ hδ hcrux htail)


/-- The crude (L1) bound `WinMass f M₂ M₃ ≤ 40 max(M₂,1)³ M₃ ∫f²`, proved locally from
`WinMass_window_le` and `Hprof_sq_integral_le` (the module `winMass_crude` cannot be imported
here: it re-declares the global name `hasCompactSupport_of_suppHyp`). -/
private lemma winmass_crude_local {C₀ : ℝ} (hC₀ : 1 ≤ C₀) {M₂ M₃ : ℝ} (hM₃ : 1 ≤ M₃)
    {f : ℝ → ℝ} (hf : Continuous f) (hfnn : ∀ u, 0 ≤ f u) (hSupp : SuppHyp C₀ f) :
    WinMass f M₂ M₃ ≤ 40 * (max M₂ 1) ^ 3 * M₃ * ∫ u, (f u) ^ 2 := by
  by_cases hM₂ : 0 < M₂
  · have hM₃pos : 0 < M₃ := lt_of_lt_of_le zero_lt_one hM₃
    have hcs : HasCompactSupport f := winmass_hcs_of_suppHyp hSupp
    have hw := WinMass_window_le hC₀ hM₂ hM₃pos hf hcs hSupp
    have hP := Hprof_sq_integral_le hC₀ hM₂ hf hfnn hSupp
    have hAnn : (0 : ℝ) ≤ ∫ u, (f u) ^ 2 := integral_nonneg (fun u => sq_nonneg _)
    have hM₃4 : M₃ + 4 ≤ 5 * M₃ := by linarith
    calc WinMass f M₂ M₃ ≤ (M₃ + 4) * ∫ u, (Hprof f M₂ u) ^ 2 := hw
      _ ≤ (M₃ + 4) * (8 * (max M₂ 1) ^ 3 * ∫ u, (f u) ^ 2) :=
          mul_le_mul_of_nonneg_left hP (by linarith)
      _ ≤ 5 * M₃ * (8 * (max M₂ 1) ^ 3 * ∫ u, (f u) ^ 2) :=
          mul_le_mul_of_nonneg_right hM₃4 (by positivity)
      _ = 40 * (max M₂ 1) ^ 3 * M₃ * ∫ u, (f u) ^ 2 := by ring
  · push_neg at hM₂
    have hR2 : R2 M₂ = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr (fun m hm => ?_)
      obtain ⟨hmI, _⟩ := Finset.mem_filter.mp hm
      have h1 : (1 : ℤ) ≤ m := (Finset.mem_Icc.mp hmI).1
      have h2 : m ≤ ⌊2 * M₂⌋ := (Finset.mem_Icc.mp hmI).2
      have h3 : ⌊2 * M₂⌋ ≤ 0 := Int.floor_nonpos (by linarith)
      omega
    have hHf : ∀ (ℓ : ℤ) (τ : ℝ), Hfun f M₂ M₃ ℓ τ = 0 := by
      intro ℓ τ
      simp only [Hfun, hR2, Finset.sum_empty]
    have hzero : WinMass f M₂ M₃ = 0 := by
      simp only [WinMass]
      have hfun : (fun ℓ : ℤ => ∫ τ in Set.Icc (-2 : ℝ) 2, ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2)
          = fun _ => (0 : ℝ) := by
        funext ℓ
        have h2 : (fun τ : ℝ => ‖Hfun f M₂ M₃ ℓ τ‖ ^ 2) = fun _ => (0 : ℝ) :=
          funext (fun τ => by rw [hHf ℓ τ]; norm_num)
        rw [h2]; simp
      rw [hfun]; simp
    rw [hzero]
    positivity

/-- **The target lemma.** -/
theorem WinMass_core {C₀ T₀ C₃ : ℝ} (hC₀ : 1 ≤ C₀) (hT₀ : 1 ≤ T₀)
    (hC₃ : 1 ≤ C₃) (c : ℕ → ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ T : ℝ, T₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ Mbig M₂ M₃ : ℝ,
        1 ≤ Mbig → Mbig ≤ T ^ 4 → 1 ≤ M₃ → M₃ ≤ C₃ * Mbig → 0 < M₂ → M₂ ≤ Mbig →
        WinMass f M₂ M₃ ≤
          C' * T ^ δ * (M₂ * (∫ u, (f u) ^ 2) ^ (1/2:ℝ) *
              (∫ u, (Gfun C₀ T M₂ f u) ^ 2) ^ (1/2:ℝ) +
            M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2) := by
  -- The Fejer/Fourier route of `WINMASS_ROUTE.md`: the target only asks for
  -- `sqrt(∫f²) · sqrt(∫Gfun²)`, so both factors are smoothed and the proof finishes with
  -- `‖f~‖₂ ≤ ‖f‖₂`.  The near part is the Fejer majorant plus the near correlation bound, the
  -- far part is the decay tail, and the bounded cases (`M₂ < 1`, or `T`/`M₂` bounded) are the
  -- elementary crude bounds.  The six inputs are ascribed explicitly to pin `C₀`.
  have hF' : ∃ C : ℝ, 0 < C ∧
      ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        ∀ M₂ : ℝ, 0 ≤ M₂ → ∀ M₃ : ℝ, 1 ≤ M₃ →
          WinMass f M₂ M₃ ≤ C * ∫ x : ℝ, ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x :=
    winMass_le_fejer hC₀
  have hN' : ∃ C : ℝ, 0 < C ∧
      ∀ K T M₂ : ℝ, 1 ≤ T → 8 ≤ K → 2 * C₀ ≤ M₂ → 2 * C₀ ≤ T →
        ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
          ∀ M₃ : ℝ, 1 ≤ M₃ →
            (∫ x in Set.Icc (-(K * T / M₂)) (K * T / M₂),
                ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x)
              ≤ C * K ^ 2 * M₂ *
                  ∫ u : ℝ, smoothed psiSmooth T f u * Gfun C₀ T M₂ f u :=
    near_correlation_le_Gfun hC₀
  have hTl' : ∃ C : ℝ, 0 < C ∧
      ∀ T : ℝ, 1 ≤ T → 2 * C₀ ≤ T → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) →
        SuppHyp C₀ f →
        ∀ Λ : ℝ, 0 < Λ →
        (∀ (j : ℕ) (ε : ℝ), 0 < ε → ∀ ξ : ℝ, ξ ≠ 0 →
          ‖Fhat f ξ‖ ≤ c j ε * T ^ ε * (T / |ξ|) ^ j * Λ) →
        Λ ≤ 16 * c 2 1 * T ^ 3 * ∫ u, f u →
        ∀ M₂ : ℝ, 1 ≤ M₂ → M₂ ≤ T ^ 4 → ∀ M₃ : ℝ, 1 ≤ M₃ →
          (∫ x in {x : ℝ | T ^ (δ / 2) * T / M₂ < |x|},
              ‖Bsum f M₂ x‖ ^ 2 * fejerK M₃ x)
            ≤ C * M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2 :=
    far_tail_le hC₀ c δ hδ
  have hL2' : ∀ T : ℝ, 0 < T → ∀ f : ℝ → ℝ, Continuous f → HasCompactSupport f →
      (∫ u, (smoothed psiSmooth T f u) ^ 2) ≤ ∫ u, (f u) ^ 2 :=
    fun T hT f hf hcs => smoothed_L2_le hT hf hcs
  have hCr' : ∃ C : ℝ, 0 < C ∧
      ∀ M₂ M₃ : ℝ, 1 ≤ M₃ → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) → SuppHyp C₀ f →
        WinMass f M₂ M₃ ≤ C * (max M₂ 1) ^ 3 * M₃ * ∫ u, (f u) ^ 2 :=
    ⟨40, by norm_num,
      fun M₂ M₃ hM₃ f hf hfnn hSupp => winmass_crude_local hC₀ hM₃ hf hfnn hSupp⟩
  have hSm' : ∀ M₂ M₃ : ℝ, 0 < M₂ → 1 ≤ M₃ → ∀ f : ℝ → ℝ, Continuous f → (∀ u, 0 ≤ f u) →
      HasCompactSupport f → SuppHyp C₀ f → M₂ < 1 →
        WinMass f M₂ M₃ ≤ 20 * M₂ ^ 2 * M₃ * ∫ u, (f u) ^ 2 :=
    fun M₂ M₃ hM₂ hM₃ f hf hfnn hcs hSupp hM₂1 =>
      winmass_le_small_M₂ hC₀ hM₂ hM₃ hf hfnn hcs hSupp hM₂1
  exact WinMass_core_of_fejer_route hC₀ hT₀ hC₃ c δ hδ hF' hN' hTl' hL2' hCr' hSm'


end

end Work.GM.Affine
