import Mathlib
import Submission.Work.NN.Core.czB_L2_defs
import Submission.Work.NN.Core.bmPotential_dCoord_eq
import Submission.Work.NN.Core.exists_contDiff_uniform_approx
import Submission.Work.NN.Core.czbL2_smooth_aux
import Submission.Work.NN.Core.tendsto_dCoord_bmPotential
import Submission.Work.NN.Core.tendsto_lintegral_data

namespace Work.NN.Core

open Work.CR.Flat.Cauchy
open MeasureTheory Set Filter
open scoped NNReal ENNReal ContDiff Topology

/-- **From `C^∞_c` data to `C¹_c` data in the `L²` bound for `∂ bmPotential`.**  If the `L²` bound
`∫⁻ Σ_k ofReal ‖∂_k (bmPotential h)‖² ≤ ofReal(C²) · ∫⁻ Σ_j ofReal ‖h_j‖²` holds for every
smooth (`ContDiff ℝ ∞`, i.e. `C^∞`, NOT the analytic level `⊤`/`∞` of `WithTop ℕ∞`) compactly
supported family `h`, then it holds for every `C¹` compactly supported family `h`.

Note this is the CORRECTED statement: the previous version used `ContDiff ℝ ⊤`, which in this
Mathlib is the *analytic* level; an analytic function with compact support on `ℂⁿ` vanishes, so the
hypothesis was vacuous and the conclusion false.  Use `ContDiff ℝ ∞` (the smooth level).

Route (mollification + Fatou).  Let `h` be `C¹` with compact support and let `h^(m) = h ⋆ ρ_m` be a
mollification sequence (`contDiffBump`/`mollifier`, or `Work.NN.Core.exists_contDiff_uniform_approx`
with `ε = 1/(m+1)` applied componentwise), so that each `h^(m)` is `C^∞`, has compact support
contained in a fixed ball, converges to `h` uniformly together with its first derivatives, and
`∫⁻ Σ_j ofReal ‖h^(m)_j‖² → ∫⁻ Σ_j ofReal ‖h_j‖²` (dominated convergence; the supports stay in a
fixed ball so the `L²`-norms converge, and `ofReal_integral_eq_lintegral_ofReal` converts the
real integrals).  The hypothesis gives the bound for each `m`.
For the left-hand side, `∂_k (bmPotential h^(m)) z = Σ_l ∫ x, bmKernel l x * ∂_k (h^(m)_l) (z+x)`
by `Work.NN.Core.bmPotential_dCoord_eq`, which tends pointwise to `∂_k (bmPotential h) z`
(dominated convergence: `‖bmKernel l x‖ ≤ ‖x‖^{1-2n}` is locally integrable, the data are
supported in a fixed ball, and the first derivatives converge uniformly).  Then Fatou for the lower
integral (`MeasureTheory.lintegral_liminf_le`, applied to the nonnegative measurable functions
`z ↦ Σ_k ofReal ‖∂_k (bmPotential h^(m)) z‖²`) gives
`∫⁻ Σ_k ofReal ‖∂_k (bmPotential h) z‖² ≤ liminf_m ∫⁻ Σ_k ofReal ‖∂_k (bmPotential h^(m)) z‖²`;
combining with the hypothesis for each `m` and the convergence of the right-hand sides
(`ENNReal.ofReal_mul`, `ofReal (C^2)` nonnegative) gives the claim. -/
theorem czbL2_bound_of_smooth {n : ℕ} (hn : 0 < n) {C : ℝ}
    (hsmooth : ∀ h : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ ∞ (h j)) →
      (∀ j, HasCompactSupport (h j)) →
      ∫⁻ z : Fin n → ℂ, (∑ k : Fin n, ENNReal.ofReal
          ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2)
        ≤ ENNReal.ofReal (C ^ 2) *
          ∫⁻ z : Fin n → ℂ, (∑ j : Fin n, ENNReal.ofReal ‖h j z‖ ^ 2)) :
    ∀ h : Fin n → (Fin n → ℂ) → ℂ, (∀ j, ContDiff ℝ 1 (h j)) →
      (∀ j, HasCompactSupport (h j)) →
      ∫⁻ z : Fin n → ℂ, (∑ k : Fin n, ENNReal.ofReal
          ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2)
        ≤ ENNReal.ofReal (C ^ 2) *
          ∫⁻ z : Fin n → ℂ, (∑ j : Fin n, ENNReal.ofReal ‖h j z‖ ^ 2)
:= by
  intro h hh hcs
  -- a common ball outside which all components of `h` vanish
  have hkeyρ : ∀ j : Fin n, ∃ r : ℝ, 0 ≤ r ∧ ∀ w : Fin n → ℂ, r ≤ ‖w‖ → h j w = 0 :=
    fun j => exists_norm_le_of_hasCompactSupport (hcs j)
  set ρ : ℝ := ∑ j : Fin n, Classical.choose (hkeyρ j) with hρdef
  have hρnn : 0 ≤ ρ := by
    rw [hρdef]
    exact Finset.sum_nonneg (s := Finset.univ) fun j _ => (Classical.choose_spec (hkeyρ j)).1
  have hh0 : ∀ j w, ρ ≤ ‖w‖ → h j w = 0 := by
    intro j w hw
    refine (Classical.choose_spec (hkeyρ j)).2 w (le_trans ?_ hw)
    calc Classical.choose (hkeyρ j) ≤ ∑ i : Fin n, Classical.choose (hkeyρ i) :=
          Finset.single_le_sum (fun i _ => (Classical.choose_spec (hkeyρ i)).1)
            (Finset.mem_univ j)
      _ = ρ := hρdef.symm
  -- smooth approximants with support in the closed ball of radius `ρ + 1`
  have hkeyH : ∀ m : ℕ, ∀ j : Fin n, ∃ ψ : (Fin n → ℂ) → ℂ,
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ (∀ z, ρ + 1 ≤ ‖z‖ → ψ z = 0) ∧
      (∀ z, ‖ψ z - h j z‖ ≤ 1 / (m + 1)) ∧
      (∀ z, ‖fderiv ℝ ψ z - fderiv ℝ (h j) z‖ ≤ 1 / (m + 1)) :=
    fun m j => exists_contDiff_uniform_approx (φ := h j) (hh j) hρnn (hh0 j)
      (ε := 1 / (m + 1)) (by positivity)
  set H : ℕ → Fin n → (Fin n → ℂ) → ℂ := fun m j => Classical.choose (hkeyH m j) with hHdef
  have hHcd : ∀ m j, ContDiff ℝ ∞ (H m j) := fun m j => by
    simpa only [hHdef] using (Classical.choose_spec (hkeyH m j)).1
  have hHcs : ∀ m j, HasCompactSupport (H m j) := fun m j => by
    simpa only [hHdef] using (Classical.choose_spec (hkeyH m j)).2.1
  have hHsupp : ∀ m j w, ρ + 1 ≤ ‖w‖ → H m j w = 0 := fun m j => by
    simpa only [hHdef] using (Classical.choose_spec (hkeyH m j)).2.2.1
  have hHval : ∀ m j w, ‖H m j w - h j w‖ ≤ 1 / (m + 1) := fun m j => by
    simpa only [hHdef] using (Classical.choose_spec (hkeyH m j)).2.2.2.1
  have hHder : ∀ m j w, ‖fderiv ℝ (H m j) w - fderiv ℝ (h j) w‖ ≤ 1 / (m + 1) := fun m j => by
    simpa only [hHdef] using (Classical.choose_spec (hkeyH m j)).2.2.2.2
  have hε0 : Filter.Tendsto (fun m : ℕ => (1 : ℝ) / (m + 1)) Filter.atTop (nhds 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hεnn : ∀ m : ℕ, 0 ≤ (1 : ℝ) / (m + 1) := fun m => by positivity
  -- pointwise convergence of `dCoord k (bmPotential (H m))`
  have hLtend : ∀ k : Fin n, ∀ z, Filter.Tendsto
      (fun m => Work.CR.Flat.dCoord k (bmPotential (H m)) z) Filter.atTop
      (nhds (Work.CR.Flat.dCoord k (bmPotential h) z)) := by
    intro k
    refine tendsto_dCoord_bmPotential hn k (show (0 : ℝ) ≤ ρ + 1 by linarith)
      (fun m j => (hHcd m j).of_le (by norm_num)) hh hHcs hcs
      (fun m j w hw => hHsupp m j w hw)
      (fun j w hw => hh0 j w (le_trans (by linarith) hw)) hε0 hεnn (fun m j w => ?_)
    calc ‖Work.CR.Flat.dCoord k (H m j) w - Work.CR.Flat.dCoord k (h j) w‖
        ≤ ‖fderiv ℝ (H m j) w - fderiv ℝ (h j) w‖ := norm_dCoord_sub_le k _ _ _
      _ ≤ 1 / (m + 1) := hHder m j w
  -- uniform bounds on the data
  have hkeyM : ∀ j : Fin n, ∃ M : ℝ, 0 ≤ M ∧ ∀ w, ‖h j w‖ ≤ M := fun j => by
    obtain ⟨M, hM⟩ := (hh j).continuous.bounded_above_of_compact_support (hcs j)
    exact ⟨max M 0, le_max_right _ _, fun w => le_trans (hM w) (le_max_left _ _)⟩
  set B : ℝ := (∑ j : Fin n, Classical.choose (hkeyM j)) + 1 with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have h := Finset.sum_nonneg (s := Finset.univ) fun j _ => (Classical.choose_spec (hkeyM j)).1
    linarith
  have hHB : ∀ m j w, ‖H m j w‖ ≤ B := by
    intro m j w
    have hsum : Classical.choose (hkeyM j) ≤ ∑ i : Fin n, Classical.choose (hkeyM i) :=
      Finset.single_le_sum (fun i _ => (Classical.choose_spec (hkeyM i)).1) (Finset.mem_univ j)
    have h1 : ‖H m j w‖ ≤ ‖h j w‖ + ‖H m j w - h j w‖ := by
      have he : H m j w = h j w + (H m j w - h j w) := by ring
      conv_lhs => rw [he]
      exact norm_add_le _ _
    have h2 : ‖h j w‖ ≤ Classical.choose (hkeyM j) := (Classical.choose_spec (hkeyM j)).2 w
    have h3 : ‖H m j w - h j w‖ ≤ 1 / (m + 1) := hHval m j w
    have h4 : (1 : ℝ) / (m + 1) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < (m + 1))]
      push_cast; linarith
    rw [hBdef]; linarith
  have hconvH : ∀ j w, Filter.Tendsto (fun m => H m j w) Filter.atTop (nhds (h j w)) := by
    intro j w
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    exact squeeze_zero (fun m => norm_nonneg _) (fun m => hHval m j w) hε0
  -- convergence of the right-hand sides
  have hRtend := tendsto_lintegral_data (F := H) (f := h) (ρ := ρ + 1) (B := B)
    (by linarith) hB0 (fun m j => (hHcd m j).continuous.measurable)
    (fun m j w hw => hHsupp m j w hw) (fun m j w => hHB m j w) hconvH
  -- measurability for Fatou
  have hFm : ∀ m, Measurable (fun z : Fin n → ℂ =>
      ∑ k : Fin n, ENNReal.ofReal ‖Work.CR.Flat.dCoord k (bmPotential (H m)) z‖ ^ 2) := by
    intro m
    have hu : ContDiff ℝ 1 (bmPotential (H m)) :=
      contDiff_one_bmPotential hn (fun j => (hHcd m j).of_le (by norm_num)) (fun j => hHcs m j)
    have hcont : ∀ k : Fin n, Continuous (fun z : Fin n → ℂ =>
        ENNReal.ofReal ‖Work.CR.Flat.dCoord k (bmPotential (H m)) z‖ ^ 2) := by
      intro k
      have h1 : (fun z : Fin n → ℂ =>
            ENNReal.ofReal ‖Work.CR.Flat.dCoord k (bmPotential (H m)) z‖ ^ 2)
          = fun z => ENNReal.ofReal (‖Work.CR.Flat.dCoord k (bmPotential (H m)) z‖ ^ 2) := by
        funext z; rw [ENNReal.ofReal_pow (norm_nonneg _)]
      rw [h1]
      exact ENNReal.continuous_ofReal.comp ((czbL2smooth_continuous_dCoord hu k).norm.pow 2)
    exact (continuous_finsetSum _ fun k _ => hcont k).measurable
  -- pointwise convergence of the integrands
  have hpc : ∀ z, Filter.Tendsto
      (fun m => ∑ k : Fin n, ENNReal.ofReal ‖Work.CR.Flat.dCoord k (bmPotential (H m)) z‖ ^ 2)
      Filter.atTop
      (nhds (∑ k : Fin n, ENNReal.ofReal ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2)) := by
    intro z
    refine tendsto_finsetSum _ fun k _ => ?_
    have hc : Continuous (fun x : ℂ => ENNReal.ofReal ‖x‖ ^ 2) := by
      have h1 : (fun x : ℂ => ENNReal.ofReal ‖x‖ ^ 2) = fun x => ENNReal.ofReal (‖x‖ ^ 2) := by
        funext x; rw [ENNReal.ofReal_pow (norm_nonneg x)]
      rw [h1]
      exact ENNReal.continuous_ofReal.comp (continuous_norm.pow 2)
    exact (hc.tendsto (Work.CR.Flat.dCoord k (bmPotential h) z)).comp (hLtend k z)
  -- Fatou
  have hFatou : (∫⁻ z : Fin n → ℂ, (∑ k : Fin n, ENNReal.ofReal
        ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2))
      ≤ Filter.liminf (fun m => ∫⁻ z : Fin n → ℂ, ∑ k : Fin n, ENNReal.ofReal
          ‖Work.CR.Flat.dCoord k (bmPotential (H m)) z‖ ^ 2) Filter.atTop := by
    have hF := MeasureTheory.lintegral_liminf_le (μ := volume) (u := Filter.atTop)
      (f := fun m (z : Fin n → ℂ) => ∑ k : Fin n, ENNReal.ofReal
          ‖Work.CR.Flat.dCoord k (bmPotential (H m)) z‖ ^ 2) hFm
    have hcongr : (fun z : Fin n → ℂ => Filter.liminf (fun m => ∑ k : Fin n, ENNReal.ofReal
          ‖Work.CR.Flat.dCoord k (bmPotential (H m)) z‖ ^ 2) Filter.atTop)
        = fun z : Fin n → ℂ => ∑ k : Fin n, ENNReal.ofReal
          ‖Work.CR.Flat.dCoord k (bmPotential h) z‖ ^ 2 := funext fun z => (hpc z).liminf_eq
    rw [hcongr] at hF
    exact hF
  have hbound : ∀ m, (∫⁻ z : Fin n → ℂ, ∑ k : Fin n, ENNReal.ofReal
        ‖Work.CR.Flat.dCoord k (bmPotential (H m)) z‖ ^ 2)
      ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ z : Fin n → ℂ,
          ∑ j : Fin n, ENNReal.ofReal ‖H m j z‖ ^ 2 :=
    fun m => hsmooth (H m) (hHcd m) (hHcs m)
  have hliminf : Filter.liminf (fun m => ∫⁻ z : Fin n → ℂ, ∑ k : Fin n, ENNReal.ofReal
        ‖Work.CR.Flat.dCoord k (bmPotential (H m)) z‖ ^ 2) Filter.atTop
      ≤ ENNReal.ofReal (C ^ 2) * ∫⁻ z : Fin n → ℂ,
          ∑ j : Fin n, ENNReal.ofReal ‖h j z‖ ^ 2 := by
    have hle := Filter.liminf_le_liminf (f := Filter.atTop)
      (u := fun m => ENNReal.ofReal (C ^ 2) * ∫⁻ z : Fin n → ℂ,
          ∑ j : Fin n, ENNReal.ofReal ‖H m j z‖ ^ 2)
      (v := fun m => ∫⁻ z : Fin n → ℂ, ∑ k : Fin n, ENNReal.ofReal
          ‖Work.CR.Flat.dCoord k (bmPotential (H m)) z‖ ^ 2)
      (Filter.Eventually.of_forall hbound)
    have ht : Filter.Tendsto (fun m => ENNReal.ofReal (C ^ 2) * ∫⁻ z : Fin n → ℂ,
          ∑ j : Fin n, ENNReal.ofReal ‖H m j z‖ ^ 2) Filter.atTop
        (nhds (ENNReal.ofReal (C ^ 2) * ∫⁻ z : Fin n → ℂ,
          ∑ j : Fin n, ENNReal.ofReal ‖h j z‖ ^ 2)) :=
      ((ENNReal.continuous_const_mul (a := ENNReal.ofReal (C ^ 2))
        ENNReal.ofReal_ne_top).tendsto _).comp hRtend
    exact hle.trans (le_of_eq ht.liminf_eq)
  exact hFatou.trans hliminf

end Work.NN.Core
