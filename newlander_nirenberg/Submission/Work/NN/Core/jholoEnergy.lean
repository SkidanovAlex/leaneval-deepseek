import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.jholo_dbar_pointwise
import Submission.Work.NN.Core.weighted_energy_le
import Submission.Work.NN.Core.exists_contDiff_bump_of_isCompact_subset
import Submission.Work.NN.Core.jholoFrame_pre

/-!
# The weighted energy estimate for a `J`-holomorphic function

Let `J = Jstd + A` be a small perturbation of the standard complex structure on `ℂⁿ`
(the coefficients of `A` are Hölder of exponent `α ∈ (0,1)` with norm at most `ε`,
and `J² = -1`), and let `g` be `J`-holomorphic on the polydisc `polydisc 0 ρ`.
Then for every smooth compactly supported `φ ≥ 0` with `tsupport φ ⊆ polydisc 0 ρ`,

`∫_{polydisc 0 ρ} φ² ∑_j (‖∂_j g‖² + ‖∂̄_j g‖²) ≤ C ∫_{polydisc 0 ρ} ‖Dφ‖² ‖g‖²`,

with `C` independent of `g` and `φ` (and of `A`, `ε ≤ ε₀`).

The proof combines
* the pointwise smallness of the standard `∂̄`-energy of a `J`-holomorphic function
  (`Work.NN.Core.jholo_dbar_pointwise`), and
* the weighted energy estimate `Work.NN.Core.weighted_energy_le` for compactly supported
  `C¹` functions whose `∂̄`-energy is small relative to their full energy,

applied to `η = φ` and a cutoff multiple `H = χ·g` of `g`, the cutoff `χ` being `1` near
`tsupport φ` (so that `H` is globally `C¹` with compact support) and of sup-norm at most `1`.
-/

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set MeasureTheory Filter

namespace Work.NN.Core

/-! ## Auxiliary lemmas -/

/-- The flat `∂`-derivative depends only on the germ of the function. -/
lemma dCoord_congr_eventuallyEq {n : ℕ} {f g : Cn n → ℂ} {z : Cn n}
    (h : f =ᶠ[𝓝 z] g) (j : Fin n) :
    Work.CR.Flat.dCoord j f z = Work.CR.Flat.dCoord j g z := by
  simp only [Work.CR.Flat.dCoord]
  rw [h.fderiv_eq]

/-- The flat `∂̄`-derivative depends only on the germ of the function. -/
lemma dbarCoord_congr_eventuallyEq {n : ℕ} {f g : Cn n → ℂ} {z : Cn n}
    (h : f =ᶠ[𝓝 z] g) (j : Fin n) :
    Work.CR.Flat.dbarCoord j f z = Work.CR.Flat.dbarCoord j g z := by
  simp only [Work.CR.Flat.dbarCoord]
  rw [h.fderiv_eq]

/-- The topological support of a real function and of its complexification agree. -/
lemma tsupport_ofReal_eq {n : ℕ} (φ : Cn n → ℝ) :
    tsupport (fun z : Cn n => (φ z : ℂ)) = tsupport φ := by
  have h : Function.support (fun z : Cn n => (φ z : ℂ)) = Function.support φ := by
    ext z
    simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
  rw [tsupport, tsupport, h]

/-- A function vanishes in a neighbourhood of a point outside its topological support. -/
lemma tsupport_compl_eventuallyEq_zero {n : ℕ} {f : Cn n → ℝ} {z : Cn n}
    (hz : z ∉ tsupport f) : f =ᶠ[𝓝 z] 0 := by
  have hopen : (tsupport f)ᶜ ∈ 𝓝 z := (isClosed_tsupport f).isOpen_compl.mem_nhds hz
  filter_upwards [hopen] with y hy
  by_contra h
  exact hy (subset_tsupport f (Function.mem_support.mpr h))

/-- Complexifying a real function does not increase the norm of its Fréchet derivative. -/
lemma norm_fderiv_ofReal_le {n : ℕ} {f : Cn n → ℝ} {z : Cn n}
    (hf : DifferentiableAt ℝ f z) :
    ‖fderiv ℝ (fun w : Cn n => (f w : ℂ)) z‖ ≤ ‖fderiv ℝ f z‖ := by
  have h : (fun w : Cn n => (f w : ℂ)) = Complex.ofRealCLM ∘ f := by
    ext w; simp [Complex.ofRealCLM_apply]
  rw [h, fderiv_comp]
  · rw [ContinuousLinearMap.fderiv]
    calc ‖(Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp (fderiv ℝ f z)‖
        ≤ ‖(Complex.ofRealCLM : ℝ →L[ℝ] ℂ)‖ * ‖fderiv ℝ f z‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ = ‖fderiv ℝ f z‖ := by rw [Complex.ofRealCLM_norm, one_mul]
  · exact (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).differentiableAt
  · exact hf

/-- A smooth `ℂ`-valued bump on `ℂⁿ`, of sup-norm at most `1`, equal to `1` on an open
neighbourhood `V` of a given compact set `K ⊆ U`, with support inside the open set `U`. -/
lemma exists_contDiff_bump_le_one {n : ℕ} {K U : Set (Cn n)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ (χ : Cn n → ℂ) (V : Set (Cn n)), ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ U ∧ IsOpen V ∧ K ⊆ V ∧ (∀ y ∈ V, χ y = 1) ∧ (∀ z, ‖χ z‖ ≤ 1) := by
  obtain ⟨R, _hRpos, hRle⟩ := hK.isBounded.exists_pos_norm_le
  have hball : K ⊆ Metric.ball (0 : Cn n) (R + 1) := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt (hRle x hx) (lt_add_one R)
  have hU' : IsOpen (U ∩ Metric.ball (0 : Cn n) (R + 1)) := hU.inter Metric.isOpen_ball
  have hKU' : K ⊆ U ∩ Metric.ball (0 : Cn n) (R + 1) := fun x hx => ⟨hKU hx, hball hx⟩
  obtain ⟨V₀, hV₀o, hKV₀, hclV₀⟩ := hK.exists_isOpen_closure_subset (hU'.mem_nhdsSet.mpr hKU')
  have hclV₀U : closure V₀ ⊆ U := hclV₀.trans inter_subset_left
  have hclV₀cpt : IsCompact (closure V₀) :=
    IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Cn n) (R + 1)) isClosed_closure
      (hclV₀.trans (inter_subset_right.trans Metric.ball_subset_closedBall))
  obtain ⟨V, hVo, hKV, hclV⟩ := hK.exists_isOpen_closure_subset (hV₀o.mem_nhdsSet.mpr hKV₀)
  obtain ⟨f, hfdiff, hfrange, hfsupp, hfone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hV₀o isClosed_closure hclV
  refine ⟨fun y => (f y : ℂ), V, ?_, ?_, ?_, hVo, hKV, ?_, ?_⟩
  · have h := Complex.ofRealCLM.contDiff.comp hfdiff
    simpa [Function.comp_def] using h
  · change IsCompact (tsupport (fun y : Cn n => (f y : ℂ)))
    rw [tsupport_ofReal_eq, tsupport, hfsupp]
    exact hclV₀cpt
  · rw [tsupport_ofReal_eq, tsupport, hfsupp]
    exact hclV₀U
  · intro y hy
    have h1 : f y = 1 := (hfone y).mp (subset_closure hy)
    simp [h1]
  · intro y
    have h1 : (0 : ℝ) ≤ f y := (hfrange (Set.mem_range_self y)).1
    have h2 : f y ≤ 1 := (hfrange (Set.mem_range_self y)).2
    rw [Complex.norm_of_nonneg h1]
    exact h2

/-! ## The weighted energy estimate -/

theorem jholoEnergy {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {ρ : Fin n → ℝ} (hρ0 : ∀ j, 0 < ρ j) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ {A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n},
        (∀ m : ℕ, ContDiff ℝ m A) → ∀ {ε : ℝ}, 0 ≤ ε → ε ≤ ε₀ →
        (∀ i j : Fin n, Work.CR.Flat.holderNorm 1 α (fun z => A z (Pi.single i 1) j)
          (Work.CR.Flat.polydisc 0 ρ) ≤ ENNReal.ofReal ε) →
        (∀ z v : Work.NN.Core.Cn n,
          (Work.NN.Core.JstdCn n + A) z ((Work.NN.Core.JstdCn n + A) z v) = -v) →
        ∀ g : Work.NN.Core.Cn n → ℂ,
          ContDiffOn ℝ 1 g (Work.CR.Flat.polydisc 0 ρ) →
          (∀ j, ∀ z ∈ Work.CR.Flat.polydisc 0 ρ,
            Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) g z (Pi.single j 1) = 0) →
          ∀ φ : Work.NN.Core.Cn n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
            tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρ → (∀ z, 0 ≤ φ z) →
            ∫ z in Work.CR.Flat.polydisc 0 ρ,
                (φ z)^2 * (∑ j, (‖Work.CR.Flat.dCoord j g z‖^2
                  + ‖Work.CR.Flat.dbarCoord j g z‖^2))
              ≤ C * ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * ‖g z‖^2 := by
  classical
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsqrt10 : 0 < Real.sqrt 10 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨min 1 (1 / ((n : ℝ) * Real.sqrt 10)),
    lt_min zero_lt_one (div_pos one_pos (mul_pos hnR hsqrt10)),
    24 * (n : ℝ), by positivity, ?_⟩
  intro A hA ε hε0 hεε0 hsmall hJ g hg hdbar φ hφsm hφcs hts hφ0
  have hU : IsOpen (Work.CR.Flat.polydisc 0 ρ) := Work.CR.Flat.isOpen_polydisc 0 ρ
  have hφ1 : ContDiff ℝ 1 φ := hφsm.of_le (by simp)
  -- smallness constant
  have hεle : ε ≤ 1 / ((n : ℝ) * Real.sqrt 10) := le_trans hεε0 (min_le_right _ _)
  have hεb : ((n : ℝ) * ε) ^ 2 ≤ 1 / 10 := by
    have hmul : (n : ℝ) * ε ≤ (n : ℝ) * (1 / ((n : ℝ) * Real.sqrt 10)) :=
      mul_le_mul_of_nonneg_left hεle (le_of_lt hnR)
    have hval : (n : ℝ) * (1 / ((n : ℝ) * Real.sqrt 10)) = 1 / Real.sqrt 10 := by
      field_simp
    rw [hval] at hmul
    have h2 : (1 / Real.sqrt 10) ^ 2 = 1 / 10 := by
      rw [div_pow, one_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
    exact le_trans (pow_le_pow_left₀ (mul_nonneg (le_of_lt hnR) hε0) hmul 2) (le_of_eq h2)
  -- the complexification of `φ`
  set eta : Cn n → ℂ := fun z => (φ z : ℂ) with heta
  have hηC1 : ContDiff ℝ 1 eta := by
    rw [heta]
    exact Complex.ofRealCLM.contDiff.comp hφ1
  have hηcs : HasCompactSupport eta := by
    rw [heta]
    show IsCompact (tsupport (fun z : Cn n => (φ z : ℂ)))
    rw [tsupport_ofReal_eq]
    exact hφcs
  have hts' : tsupport eta ⊆ Work.CR.Flat.polydisc 0 ρ := by
    rw [heta, tsupport_ofReal_eq]
    exact hts
  -- cutoff
  obtain ⟨χ, V, hχsm, hχcs, hχts, hVopen, hKV, hχ1, hχle⟩ :=
    exists_contDiff_bump_le_one (K := tsupport eta) hηcs hU hts'
  have hχC1 : ContDiff ℝ 1 χ := hχsm.of_le (by simp)
  set H : Cn n → ℂ := fun z => g z * χ z with hHdef
  have hHC1 : ContDiff ℝ 1 H := by
    rw [hHdef]
    exact JFPre.jf_contDiff_one_mul_of_contDiffOn hU hg hχC1 hχts
  have hHcs : HasCompactSupport H := by
    rw [hHdef]
    exact hχcs.mul_left
  have hH_eq : ∀ z ∈ tsupport eta, H =ᶠ[𝓝 z] g := by
    intro z hz
    filter_upwards [hVopen.mem_nhds (hKV hz)] with y hy
    show g y * χ y = g y
    rw [hχ1 y hy, mul_one]
  -- pointwise smallness of the `(0,1)`-energy of `H`
  have hsmallH : ∀ z ∈ tsupport eta,
      ∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2
        ≤ ((n : ℝ) * ε) ^ 2 * ∑ j : Fin n,
            (‖Work.CR.Flat.dCoord j H z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2) := by
    intro z hz
    have hzpol : z ∈ Work.CR.Flat.polydisc 0 ρ := hts' hz
    have hHeq := hH_eq z hz
    have hpoint := jholo_dbar_pointwise (α := α) (ε := ε) hn hε0 (ρ := ρ) hsmall
      (h := g) hdbar hzpol
    have e1 : ∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2
        = ∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j g z‖ ^ 2 :=
      Finset.sum_congr rfl (fun j _ => by rw [dbarCoord_congr_eventuallyEq hHeq j])
    have e2 : ∑ j : Fin n,
          (‖Work.CR.Flat.dCoord j H z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2)
        = ∑ j : Fin n,
          (‖Work.CR.Flat.dCoord j g z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j g z‖ ^ 2) :=
      Finset.sum_congr rfl (fun j _ => by
        rw [dCoord_congr_eventuallyEq hHeq j, dbarCoord_congr_eventuallyEq hHeq j])
    calc ∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2
        = ∑ j : Fin n, ‖Work.CR.Flat.dbarCoord j g z‖ ^ 2 := e1
      _ ≤ (n : ℝ) ^ 2 * ε ^ 2 * ∑ j : Fin n,
            (‖Work.CR.Flat.dCoord j g z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j g z‖ ^ 2) := hpoint
      _ = ((n : ℝ) * ε) ^ 2 * ∑ j : Fin n,
            (‖Work.CR.Flat.dCoord j g z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j g z‖ ^ 2) := by ring
      _ = ((n : ℝ) * ε) ^ 2 * ∑ j : Fin n,
            (‖Work.CR.Flat.dCoord j H z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2) := by
          rw [e2]
  -- the weighted energy estimate
  have hWE := weighted_energy_le (η := eta) (H := H) hηC1 hHC1 hηcs hHcs
    (mul_nonneg (le_of_lt hnR) hε0) hεb hsmallH
  -- pointwise bound of the energy of `eta` by `‖Dφ‖²`
  have hF_le : ∀ z : Cn n, (∑ j : Fin n, (‖Work.CR.Flat.dCoord j eta z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j eta z‖ ^ 2)) ≤ 2 * (n : ℝ) * ‖fderiv ℝ φ z‖ ^ 2 := by
    intro z
    have hfd : ‖fderiv ℝ eta z‖ ≤ ‖fderiv ℝ φ z‖ := by
      rw [heta]
      exact norm_fderiv_ofReal_le (hφ1.differentiable_one z)
    calc (∑ j : Fin n, (‖Work.CR.Flat.dCoord j eta z‖ ^ 2
            + ‖Work.CR.Flat.dbarCoord j eta z‖ ^ 2))
        ≤ ∑ _j : Fin n, (‖fderiv ℝ φ z‖ ^ 2 + ‖fderiv ℝ φ z‖ ^ 2) :=
          Finset.sum_le_sum (fun j _ => by
            have h1 : ‖Work.CR.Flat.dCoord j eta z‖ ≤ ‖fderiv ℝ φ z‖ :=
              le_trans (norm_dCoord_le j eta z) hfd
            have h2 : ‖Work.CR.Flat.dbarCoord j eta z‖ ≤ ‖fderiv ℝ φ z‖ :=
              le_trans (norm_dbarCoord_le j eta z) hfd
            exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) h1 2)
              (pow_le_pow_left₀ (norm_nonneg _) h2 2))
      _ = 2 * (n : ℝ) * ‖fderiv ℝ φ z‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  -- step: bound the right hand side of `hWE` by the energy of `φ`
  have hstep2 : ∫ z, ‖H z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j eta z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j eta z‖ ^ 2))
      ≤ 2 * (n : ℝ) * ∫ z, ‖H z‖ ^ 2 * ‖fderiv ℝ φ z‖ ^ 2 := by
    have hsupp : Function.support (fun z : Cn n => ‖H z‖ ^ 2
        * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j eta z‖ ^ 2
            + ‖Work.CR.Flat.dbarCoord j eta z‖ ^ 2))) ⊆ tsupport H := by
      intro z hz
      refine subset_closure ?_
      intro hH0
      exact (Function.mem_support.mp hz) (by simp [hH0])
    have hsupp' : Function.support (fun z : Cn n => ‖H z‖ ^ 2
        * (2 * (n : ℝ) * ‖fderiv ℝ φ z‖ ^ 2)) ⊆ tsupport H := by
      intro z hz
      refine subset_closure ?_
      intro hH0
      exact (Function.mem_support.mp hz) (by simp [hH0])
    have hmono : ∫ z, ‖H z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j eta z‖ ^ 2
          + ‖Work.CR.Flat.dbarCoord j eta z‖ ^ 2))
        ≤ ∫ z, ‖H z‖ ^ 2 * (2 * (n : ℝ) * ‖fderiv ℝ φ z‖ ^ 2) := by
      refine integral_mono ?_ ?_ (fun z => mul_le_mul_of_nonneg_left (hF_le z) (sq_nonneg _))
      · refine Continuous.integrable_of_hasCompactSupport ?_ (hHcs.mono' hsupp)
        exact (hHC1.continuous.norm.pow 2).mul (continuous_finsetSum _
          (fun j _ => ((continuous_dCoord j hηC1).norm.pow 2).add
            ((continuous_dbarCoord j hηC1).norm.pow 2)))
      · refine Continuous.integrable_of_hasCompactSupport ?_ (hHcs.mono' hsupp')
        exact (hHC1.continuous.norm.pow 2).mul
          (continuous_const.mul ((hφ1.continuous_fderiv (by norm_num)).norm.pow 2))
    calc ∫ z, ‖H z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j eta z‖ ^ 2
          + ‖Work.CR.Flat.dbarCoord j eta z‖ ^ 2))
        ≤ ∫ z, ‖H z‖ ^ 2 * (2 * (n : ℝ) * ‖fderiv ℝ φ z‖ ^ 2) := hmono
      _ = 2 * (n : ℝ) * ∫ z, ‖H z‖ ^ 2 * ‖fderiv ℝ φ z‖ ^ 2 := by
          rw [← MeasureTheory.integral_const_mul]
          refine integral_congr_ae (Eventually.of_forall (fun z => ?_))
          ring
  -- the change of variables between `(φ z)^2` and `‖eta z‖²`, and between `H` and `g`
  have hpt1 : ∀ z : Cn n, (φ z) ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j g z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j g z‖ ^ 2))
      = ‖eta z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j H z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2)) := by
    intro z
    by_cases hz : φ z = 0
    · have h1 : ‖eta z‖ ^ 2 = 0 := by
        rw [show eta z = (φ z : ℂ) by rw [heta]]
        rw [hz]
        simp
      rw [h1, hz]
      simp
    · have hzm : z ∈ tsupport eta :=
        subset_closure (Function.mem_support.mpr (by
          simpa only [heta, Function.mem_support, ne_eq, Complex.ofReal_eq_zero] using hz))
      have hHeq := hH_eq z hzm
      have hnorm : ‖eta z‖ ^ 2 = (φ z) ^ 2 := by
        rw [show eta z = (φ z : ℂ) by rw [heta]]
        rw [Complex.norm_of_nonneg (hφ0 z)]
      rw [hnorm]
      congr 1
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [dCoord_congr_eventuallyEq hHeq j, dbarCoord_congr_eventuallyEq hHeq j]
  have hcongr1 : ∫ z, (φ z) ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j g z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j g z‖ ^ 2))
      = ∫ z, ‖eta z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j H z‖ ^ 2
        + ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2)) :=
    integral_congr_ae (Eventually.of_forall hpt1)
  have hpt3 : ∀ z : Cn n, ‖H z‖ ^ 2 * ‖fderiv ℝ φ z‖ ^ 2
      = ‖g z‖ ^ 2 * ‖fderiv ℝ φ z‖ ^ 2 := by
    intro z
    by_cases hz : z ∈ tsupport φ
    · have hzm : z ∈ tsupport eta := by rw [heta, tsupport_ofReal_eq]; exact hz
      have hHz : H z = g z := by
        show g z * χ z = g z
        rw [hχ1 z (hKV hzm), mul_one]
      rw [hHz]
    · have h0 : φ =ᶠ[𝓝 z] 0 := tsupport_compl_eventuallyEq_zero hz
      have hf0 : fderiv ℝ φ z = 0 := by
        rw [Filter.EventuallyEq.fderiv_eq h0]
        simp
      rw [hf0]
      simp
  have hcongr3 : ∫ z, ‖H z‖ ^ 2 * ‖fderiv ℝ φ z‖ ^ 2
      = ∫ z, ‖g z‖ ^ 2 * ‖fderiv ℝ φ z‖ ^ 2 :=
    integral_congr_ae (Eventually.of_forall hpt3)
  -- the two set integrals over the polydisc are the integrals over `ℂⁿ`
  have hsetL : ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z) ^ 2 * (∑ j : Fin n,
        (‖Work.CR.Flat.dCoord j g z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j g z‖ ^ 2))
      = ∫ z, (φ z) ^ 2 * (∑ j : Fin n,
        (‖Work.CR.Flat.dCoord j g z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j g z‖ ^ 2)) :=
    MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      have hzφ : φ z = 0 := by
        by_contra h
        exact hz (hts (subset_closure (Function.mem_support.mpr h)))
      simp [hzφ])
  have hsetR : ∫ z, ‖g z‖ ^ 2 * ‖fderiv ℝ φ z‖ ^ 2
      = ∫ z in Work.CR.Flat.polydisc 0 ρ, ‖g z‖ ^ 2 * ‖fderiv ℝ φ z‖ ^ 2 :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      have h0 : φ =ᶠ[𝓝 z] 0 :=
        tsupport_compl_eventuallyEq_zero (fun h => hz (hts h))
      have hf0 : fderiv ℝ φ z = 0 := by
        rw [Filter.EventuallyEq.fderiv_eq h0]
        simp
      simp [hf0])).symm
  calc ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z) ^ 2 * (∑ j : Fin n,
        (‖Work.CR.Flat.dCoord j g z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j g z‖ ^ 2))
      = ∫ z, (φ z) ^ 2 * (∑ j : Fin n,
          (‖Work.CR.Flat.dCoord j g z‖ ^ 2 + ‖Work.CR.Flat.dbarCoord j g z‖ ^ 2)) := hsetL
    _ = ∫ z, ‖eta z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j H z‖ ^ 2
          + ‖Work.CR.Flat.dbarCoord j H z‖ ^ 2)) := hcongr1
    _ ≤ 12 * ∫ z, ‖H z‖ ^ 2 * (∑ j : Fin n, (‖Work.CR.Flat.dCoord j eta z‖ ^ 2
          + ‖Work.CR.Flat.dbarCoord j eta z‖ ^ 2)) := hWE
    _ ≤ 12 * (2 * (n : ℝ) * ∫ z, ‖H z‖ ^ 2 * ‖fderiv ℝ φ z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hstep2 (by norm_num)
    _ = 24 * (n : ℝ) * ∫ z, ‖H z‖ ^ 2 * ‖fderiv ℝ φ z‖ ^ 2 := by ring
    _ = 24 * (n : ℝ) * ∫ z, ‖g z‖ ^ 2 * ‖fderiv ℝ φ z‖ ^ 2 := by rw [hcongr3]
    _ = 24 * (n : ℝ) * ∫ z in Work.CR.Flat.polydisc 0 ρ,
          ‖g z‖ ^ 2 * ‖fderiv ℝ φ z‖ ^ 2 := by rw [hsetR]
    _ = 24 * (n : ℝ) * ∫ z in Work.CR.Flat.polydisc 0 ρ,
          ‖fderiv ℝ φ z‖ ^ 2 * ‖g z‖ ^ 2 := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall (fun z => ?_))
        ring

end Work.NN.Core
