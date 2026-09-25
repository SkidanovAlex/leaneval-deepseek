import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.gagliardoNirenbergGeomMean
import Submission.Work.NN.Core.Lev.nnGradBoundPoint
import Submission.Work.NN.Core.ofReal_integral_normSq_le_eLpNorm_sq
import Submission.Work.NN.Core.contDiff_one_mul_of_support

/-!
# Moser's boost for the power Caccioppoli inequality (uniform constant)

This file proves `Work.NN.Core.Lev.nnMoserBoost`: from the integer-level power Caccioppoli
inequality

`∫_{polydisc 0 ρ} φ² Σ_j (|∂_j u^k|² + |∂̄_j u^k|²) ≤ C₀ ∫_{polydisc 0 ρ} |∇φ|² (|u|²)^k`

one obtains, with a constant `C` depending only on `n` and `C₀`, for all polydiscs
`r ⊂⊂ s ⊂⊂ ρ` and all cutoffs `χ` which are `1` on the closed polydisc of multiradius `r`,
supported in the polydisc of multiradius `s` and satisfy `‖∇χ‖ ≤ L`:

`‖u‖_{L^{2k(2n)'}(r)} ≤ (C(1+L))^{1/(2k)} ‖u‖_{L^{2k}(s)}`.

The mathematical content is the geometric-mean Gagliardo–Nirenberg inequality applied to
`W = χ · u^k`, together with the Caccioppoli inequality (which bounds `‖∇W‖_{L²}`) and the
pointwise bound `‖∇v‖² ≤ 8n Σ_j (|∂_j v|² + |∂̄_j v|²)`.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal ContDiff Topology

namespace Work.NN.Core.Lev

/-! ## Elementary measure-theoretic helpers -/

/-- A nonnegative `ℝ≥0∞`-valued function vanishing off `s` has the same Lebesgue integral as its
restriction to `s`. -/
private lemma lintegral_eq_lintegral_restrict {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) {f : α → ENNReal} (hf : ∀ z, z ∉ s → f z = 0) :
    ∫⁻ z, f z ∂μ = ∫⁻ z, f z ∂(μ.restrict s) := by
  rw [← MeasureTheory.lintegral_indicator hs f]
  exact MeasureTheory.lintegral_congr fun z => by
    by_cases hz : z ∈ s
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, hf z hz]

/-- The set integral over a `ℝ≥0∞`-valued function vanishing off `s ⊆ t` is unchanged when
replacing the ambient set `t` by `s`. -/
private lemma setLIntegral_eq_of_zero_off {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s t : Set α} (ht : MeasurableSet t) (hs : MeasurableSet s) (hst : s ⊆ t)
    {f : α → ENNReal} (hf : ∀ z, z ∉ s → f z = 0) :
    ∫⁻ z in t, f z ∂μ = ∫⁻ z in s, f z ∂μ := by
  rw [← MeasureTheory.lintegral_indicator ht f, ← MeasureTheory.lintegral_indicator hs f]
  exact MeasureTheory.lintegral_congr fun z => by
    by_cases hz : z ∈ s
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (hst hz)]
    · rw [Set.indicator_of_notMem hz]
      by_cases hzt : z ∈ t
      · rw [Set.indicator_of_mem hzt, hf z hz]
      · rw [Set.indicator_of_notMem hzt]

/-- The `ℝ≥0∞`-valued square of the extended norm of a vector is the `ofReal` of the square of
its norm. -/
private lemma enorm_sq_eq_ofReal {E : Type*} [SeminormedAddCommGroup E] (x : E) :
    ‖x‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖x‖ ^ 2) := by
  rw [enorm_eq_nnnorm]
  rw [show (↑‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from (ENNReal.ofReal_coe_nnreal (p := ‖x‖₊)).symm]
  rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]

/-- `x ^ (2 : ℝ) = x ^ 2` for `x : ℝ≥0∞`. -/
private lemma ENNReal_rpow_two (x : ENNReal) : x ^ (2:ℝ) = x ^ 2 := ENNReal.rpow_natCast x 2

/-- `fderiv` vanishes off the topological support. -/
private lemma fderiv_eq_zero_of_notMem_tsupport {n : ℕ} {χ : Work.NN.Core.Cn n → ℝ}
    {z : Work.NN.Core.Cn n} (hzt : z ∉ tsupport χ) : fderiv ℝ χ z = 0 := by
  have hU : (tsupport χ)ᶜ ∈ 𝓝 z := (isClosed_tsupport χ).isOpen_compl.mem_nhds hzt
  have hev : χ =ᶠ[𝓝 z] 0 := by
    filter_upwards [hU] with y hy
    by_contra hne
    exact hy (subset_closure (Function.mem_support.mpr hne))
  have h := hev.fderiv_eq (𝕜 := ℝ); rw [h]; simp

/-- The norm of `fderiv` of a real-valued function composed with the inclusion `ℝ → ℂ`. -/
private lemma norm_fderiv_ofReal_le {n : ℕ} {χ : Work.NN.Core.Cn n → ℝ}
    (hχd : ContDiff ℝ (⊤ : ℕ∞) χ) (z : Work.NN.Core.Cn n) :
    ‖fderiv ℝ (fun w => (χ w : ℂ)) z‖ ≤ ‖fderiv ℝ χ z‖ := by
  have hχ1 : ContDiff ℝ 1 χ := hχd.of_le (by simp)
  rw [show fderiv ℝ (fun w => (χ w : ℂ)) z = Complex.ofRealCLM.comp (fderiv ℝ χ z) from
    (Complex.ofRealCLM.hasFDerivAt.comp z
      (hχ1.differentiable (by norm_num) |>.differentiableAt.hasFDerivAt)).fderiv]
  have h := ContinuousLinearMap.opNorm_comp_le Complex.ofRealCLM (fderiv ℝ χ z)
  rwa [Complex.ofRealCLM_norm, one_mul] at h

/-- **Pointwise bound of `‖d(χ · v)‖` by the two pieces of the Leibniz rule.** -/
private lemma fderiv_mul_le {n : ℕ} {ρ s : Fin n → ℝ} (hsρ : ∀ j, s j < ρ j)
    {v : Work.NN.Core.Cn n → ℂ} {χ : Work.NN.Core.Cn n → ℝ} {W : Work.NN.Core.Cn n → ℂ}
    (hv : ContDiffOn ℝ 1 v (Work.CR.Flat.polydisc 0 ρ))
    (hχd : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hW : W = fun z => (χ z : ℂ) * v z)
    (hχsupp : tsupport χ ⊆ Work.CR.Flat.polydisc 0 s)
    (hχnn : ∀ z, 0 ≤ χ z)
    (z : Work.NN.Core.Cn n) :
    ‖fderiv ℝ W z‖ ≤ χ z * ‖fderiv ℝ v z‖ + ‖v z‖ * ‖fderiv ℝ χ z‖ := by
  have hχc_diff : DifferentiableAt ℝ (fun w => (χ w : ℂ)) z :=
    ((Complex.ofRealCLM.contDiff.comp hχd).differentiable (by simp)).differentiableAt
  have hnorm_χc : ‖fderiv ℝ (fun w => (χ w : ℂ)) z‖ ≤ ‖fderiv ℝ χ z‖ :=
    norm_fderiv_ofReal_le hχd z
  by_cases hz : z ∈ Work.CR.Flat.polydisc 0 s
  · have hzρ : z ∈ Work.CR.Flat.polydisc 0 ρ :=
      Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hsρ j)) hz
    have hvz : DifferentiableAt ℝ v z :=
      (hv.contDiffAt ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds hzρ)).differentiableAt
        (by norm_num)
    have hfx : fderiv ℝ W z
        = (χ z : ℂ) • fderiv ℝ v z + v z • fderiv ℝ (fun w => (χ w : ℂ)) z := by
      rw [hW]; exact fderiv_mul hχc_diff hvz
    rw [hfx]
    calc ‖(χ z : ℂ) • fderiv ℝ v z + v z • fderiv ℝ (fun w => (χ w : ℂ)) z‖
        ≤ ‖(χ z : ℂ) • fderiv ℝ v z‖ + ‖v z • fderiv ℝ (fun w => (χ w : ℂ)) z‖ :=
          norm_add_le _ _
      _ = ‖(χ z : ℂ)‖ * ‖fderiv ℝ v z‖ + ‖v z‖ * ‖fderiv ℝ (fun w => (χ w : ℂ)) z‖ := by
          rw [norm_smul, norm_smul]
      _ ≤ χ z * ‖fderiv ℝ v z‖ + ‖v z‖ * ‖fderiv ℝ χ z‖ := by
          have h1 : ‖(χ z : ℂ)‖ = χ z := by
            rw [show ‖(χ z : ℂ)‖ = ‖χ z‖ from by simp, Real.norm_of_nonneg (hχnn z)]
          rw [h1]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hnorm_χc (norm_nonneg _))
  · have hzt : z ∉ tsupport χ := fun h => hz (hχsupp h)
    have hev : χ =ᶠ[𝓝 z] 0 := by
      filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds hzt] with y hy
      by_contra hne
      exact hy (subset_closure (Function.mem_support.mpr hne))
    have hχz : χ z = 0 := hev.self_of_nhds
    have hfχ : fderiv ℝ χ z = 0 := by
      have h := hev.fderiv_eq (𝕜 := ℝ); rw [h]; simp
    have hfW : fderiv ℝ W z = 0 := by
      have hW_ev : W =ᶠ[𝓝 z] 0 := by
        filter_upwards [hev] with y hy
        rw [hW]; simp [hy]
      have h := hW_ev.fderiv_eq (𝕜 := ℝ); rw [h]; simp
    rw [hfW, hfχ, hχz]; simp

/-- Continuity of `z ↦ χ(z)² Σ_j (|∂_j v|² + |∂̄_j v|²)` (the integrand of the Caccioppoli
left hand side). -/
private lemma continuous_energyIntegrand {n : ℕ} {ρ s : Fin n → ℝ} {v : Work.NN.Core.Cn n → ℂ}
    {χ : Work.NN.Core.Cn n → ℝ}
    (hv : ContDiffOn ℝ 1 v (Work.CR.Flat.polydisc 0 ρ)) (hsρ : ∀ j, s j < ρ j)
    (hχd : ContDiff ℝ (⊤ : ℕ∞) χ) (hχsupp : tsupport χ ⊆ Work.CR.Flat.polydisc 0 s) :
    Continuous (fun z => (χ z)^2 *
      ∑ j : Fin n, (‖Work.CR.Flat.dCoord j v z‖^2 + ‖Work.CR.Flat.dbarCoord j v z‖^2)) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ Work.CR.Flat.polydisc 0 s
  · have hzρ : z ∈ Work.CR.Flat.polydisc 0 ρ :=
      Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hsρ j)) hz
    have hv_at : ContinuousAt (fun w => fderiv ℝ v w) z :=
      (hv.contDiffAt ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds hzρ)).continuousAt_fderiv
        (by norm_num)
    have hχ_at : ContinuousAt χ z := hχd.continuous.continuousAt
    have hsum : ContinuousAt (fun w => ∑ j : Fin n,
        (‖Work.CR.Flat.dCoord j v w‖^2 + ‖Work.CR.Flat.dbarCoord j v w‖^2)) z := by
      simp only [Work.CR.Flat.dCoord, Work.CR.Flat.dbarCoord]
      fun_prop
    exact hχ_at.pow 2 |>.mul hsum
  · have hzt : z ∉ tsupport χ := fun h => hz (hχsupp h)
    have hev : (fun w => (χ w)^2 * ∑ j : Fin n,
        (‖Work.CR.Flat.dCoord j v w‖^2 + ‖Work.CR.Flat.dbarCoord j v w‖^2)) =ᶠ[𝓝 z] 0 := by
      have hU : (tsupport χ)ᶜ ∈ 𝓝 z := (isClosed_tsupport χ).isOpen_compl.mem_nhds hzt
      filter_upwards [hU] with y hy
      have hy0 : χ y = 0 := by
        by_contra hne
        exact hy (subset_closure (Function.mem_support.mpr hne))
      rw [hy0]; simp
    exact ContinuousAt.congr_of_eventuallyEq continuousAt_const hev

/-- Continuity of `z ↦ ‖∇χ(z)‖² (‖u(z)‖²)^k` (the integrand of the Caccioppoli right hand
side). -/
private lemma continuous_rhsIntegrand {n : ℕ} {ρ s : Fin n → ℝ} {u : Work.NN.Core.Cn n → ℂ}
    {χ : Work.NN.Core.Cn n → ℝ}
    (hu : ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ)) (hsρ : ∀ j, s j < ρ j)
    (hχd : ContDiff ℝ (⊤ : ℕ∞) χ) (hχsupp : tsupport χ ⊆ Work.CR.Flat.polydisc 0 s) (k : ℕ) :
    Continuous (fun z => ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k) := by
  have hχ1 : ContDiff ℝ 1 χ := hχd.of_le (by simp)
  have hχfd : Continuous (fun w => fderiv ℝ χ w) := hχ1.continuous_fderiv (by norm_num)
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ Work.CR.Flat.polydisc 0 s
  · have hzρ : z ∈ Work.CR.Flat.polydisc 0 ρ :=
      Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hsρ j)) hz
    have hu_at : ContinuousAt u z :=
      (hu.contDiffAt ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds hzρ)).continuousAt
    exact ((hχfd.continuousAt.norm.pow 2)).mul ((hu_at.norm.pow 2).pow k)
  · have hzt : z ∉ tsupport χ := fun h => hz (hχsupp h)
    have hev : (fun w => ‖fderiv ℝ χ w‖^2 * (‖u w‖^2)^k) =ᶠ[𝓝 z] 0 := by
      have hU : (tsupport χ)ᶜ ∈ 𝓝 z := (isClosed_tsupport χ).isOpen_compl.mem_nhds hzt
      filter_upwards [hU] with y hy
      have hy0 : fderiv ℝ χ y = 0 := fderiv_eq_zero_of_notMem_tsupport hy
      rw [hy0]; simp
    exact ContinuousAt.congr_of_eventuallyEq continuousAt_const hev

/-- Compact support of the energy integrand. -/
private lemma hasCompactSupport_energyIntegrand {n : ℕ} {v : Work.NN.Core.Cn n → ℂ}
    {χ : Work.NN.Core.Cn n → ℝ} (hχcs : HasCompactSupport χ) :
    HasCompactSupport (fun z => (χ z)^2 *
      ∑ j : Fin n, (‖Work.CR.Flat.dCoord j v z‖^2 + ‖Work.CR.Flat.dbarCoord j v z‖^2)) := by
  refine hχcs.mono (f' := fun z => (χ z)^2 *
      ∑ j : Fin n, (‖Work.CR.Flat.dCoord j v z‖^2 + ‖Work.CR.Flat.dbarCoord j v z‖^2)) ?_
  intro z hz
  simp only [Function.mem_support] at hz ⊢
  intro hχz
  exact hz (by simp [hχz])

/-- Compact support of the right hand side integrand. -/
private lemma hasCompactSupport_rhsIntegrand {n : ℕ} {u : Work.NN.Core.Cn n → ℂ}
    {χ : Work.NN.Core.Cn n → ℝ} (hχcs : HasCompactSupport χ) (k : ℕ) :
    HasCompactSupport (fun z => ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k) := by
  refine hχcs.mono' (f' := fun z => ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k) ?_
  intro z hz
  simp only [Function.mem_support] at hz
  have h1 : fderiv ℝ χ z ≠ 0 := by
    intro h0; exact hz (by rw [h0]; simp)
  have h2 : z ∈ tsupport (fun w => fderiv ℝ χ w) :=
    subset_closure (Function.mem_support.mpr h1)
  have hsupp : Function.support (fun w => fderiv ℝ χ w) ⊆ tsupport χ :=
    fun w hw => by_contra (fun hwt => hw (fderiv_eq_zero_of_notMem_tsupport hwt))
  have h3 : z ∈ closure (tsupport χ) := closure_mono hsupp h2
  rwa [(isClosed_tsupport χ).closure_eq] at h3

/-! ## The main `L²` bound for `∇(χ · u^k)` -/

private lemma fderiv_eLpNorm_bound {n : ℕ} {C₀ L Cg : ℝ} (hC₀ : 0 ≤ C₀) (hL0 : 0 ≤ L)
    (hCg0 : 0 ≤ Cg)
    (hCg : ∀ (v : Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n),
      ‖fderiv ℝ v z‖^2 ≤ Cg * ∑ j : Fin n,
        (‖Work.CR.Flat.dCoord j v z‖^2 + ‖Work.CR.Flat.dbarCoord j v z‖^2))
    {ρ s : Fin n → ℝ} {u : Work.NN.Core.Cn n → ℂ} {χ : Work.NN.Core.Cn n → ℝ} {k : ℕ}
    (hu : ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ))
    (hsρ : ∀ j, s j < ρ j)
    (hχcd : ContDiff ℝ (⊤ : ℕ∞) χ) (hχcs : HasCompactSupport χ)
    (hχsupp : tsupport χ ⊆ Work.CR.Flat.polydisc 0 s) (hχnn : ∀ z, 0 ≤ χ z)
    (hHk : ∫ z in Work.CR.Flat.polydisc 0 ρ, (χ z)^2 *
              (∑ j, (‖Work.CR.Flat.dCoord j (fun w => (u w)^k) z‖^2
                   + ‖Work.CR.Flat.dbarCoord j (fun w => (u w)^k) z‖^2))
            ≤ C₀ * ∫ z in Work.CR.Flat.polydisc 0 ρ,
                ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k)
    (hL : ∀ z, ‖fderiv ℝ χ z‖ ≤ L) :
    MeasureTheory.eLpNorm (fderiv ℝ (fun z => (χ z : ℂ) * (u z)^k)) 2 MeasureTheory.volume
      ≤ ENNReal.ofReal (Real.sqrt (2 * (Cg * C₀ + 1)) * L) *
        MeasureTheory.eLpNorm (fun z => (u z)^k) 2
          (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) := by
  classical
  let v : Work.NN.Core.Cn n → ℂ := fun z => (u z)^k
  let W : Work.NN.Core.Cn n → ℂ := fun z => (χ z : ℂ) * v z
  let S : Set (Work.NN.Core.Cn n) := Work.CR.Flat.polydisc 0 s
  let R : Set (Work.NN.Core.Cn n) := Work.CR.Flat.polydisc 0 ρ
  change MeasureTheory.eLpNorm (fderiv ℝ W) 2 MeasureTheory.volume
      ≤ ENNReal.ofReal (Real.sqrt (2 * (Cg * C₀ + 1)) * L) *
        MeasureTheory.eLpNorm v 2 (MeasureTheory.volume.restrict S)
  let A' : Work.NN.Core.Cn n → ENNReal := fun z => ENNReal.ofReal ((χ z)^2 * ‖fderiv ℝ v z‖^2)
  let B' : Work.NN.Core.Cn n → ENNReal :=
    fun z => ENNReal.ofReal (‖v z‖^2 * ‖fderiv ℝ χ z‖^2)
  let C' : Work.NN.Core.Cn n → ENNReal := fun z => ENNReal.ofReal ((χ z)^2 *
      ∑ j : Fin n, (‖Work.CR.Flat.dCoord j v z‖^2 + ‖Work.CR.Flat.dbarCoord j v z‖^2))
  let D' : Work.NN.Core.Cn n → ENNReal :=
    fun z => ENNReal.ofReal (‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k)
  have hvCD : ContDiffOn ℝ 1 v R := hu.pow k
  have hSmeas : MeasurableSet S := (Work.CR.Flat.isOpen_polydisc 0 s).measurableSet
  have hRmeas : MeasurableSet R := (Work.CR.Flat.isOpen_polydisc 0 ρ).measurableSet
  have hSR : S ⊆ R := Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hsρ j))
  have hχr : ∀ z, (∃ j, s j ≤ ‖z j‖) → χ z = 0 := by
    intro z hz
    have hzS : z ∉ S := by
      intro h
      obtain ⟨j, hj⟩ := hz
      have h1 : ‖z j‖ < s j := by simpa using h j
      exact absurd h1 (not_lt.mpr hj)
    by_contra hne
    exact hzS (hχsupp (subset_closure (Function.mem_support.mpr hne)))
  have hχzero_off : ∀ z, z ∉ S → χ z = 0 := by
    intro z hz
    by_contra hne
    exact hz (hχsupp (subset_closure (Function.mem_support.mpr hne)))
  have hWcd : ContDiff ℝ 1 W :=
    Work.NN.Core.contDiff_one_mul_of_support (ρ := ρ) (r := s) hχcd hχr hsρ hvCD
  have hWcs : HasCompactSupport W := by
    have h1 : HasCompactSupport (fun z : Work.NN.Core.Cn n => (χ z : ℂ)) :=
      hχcs.comp_left (g := Complex.ofRealCLM) (by simp)
    exact h1.mul_right (f' := v)
  -- integrability of the two Caccioppoli integrands
  have hG1c : Continuous (fun z => (χ z)^2 * ∑ j : Fin n,
      (‖Work.CR.Flat.dCoord j v z‖^2 + ‖Work.CR.Flat.dbarCoord j v z‖^2)) :=
    continuous_energyIntegrand hvCD hsρ hχcd hχsupp
  have hG1cs : HasCompactSupport (fun z => (χ z)^2 * ∑ j : Fin n,
      (‖Work.CR.Flat.dCoord j v z‖^2 + ‖Work.CR.Flat.dbarCoord j v z‖^2)) :=
    hasCompactSupport_energyIntegrand hχcs
  have hG1int : Integrable (fun z => (χ z)^2 * ∑ j : Fin n,
      (‖Work.CR.Flat.dCoord j v z‖^2 + ‖Work.CR.Flat.dbarCoord j v z‖^2))
      (MeasureTheory.volume.restrict R) :=
    (hG1c.integrable_of_hasCompactSupport hG1cs).restrict
  have hG2c : Continuous (fun z => ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k) :=
    continuous_rhsIntegrand hu hsρ hχcd hχsupp k
  have hG2cs : HasCompactSupport (fun z => ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k) :=
    hasCompactSupport_rhsIntegrand hχcs k
  have hG2int : Integrable (fun z => ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k)
      (MeasureTheory.volume.restrict R) :=
    (hG2c.integrable_of_hasCompactSupport hG2cs).restrict
  have hG1nn : ∀ z, 0 ≤ (χ z)^2 * ∑ j : Fin n,
      (‖Work.CR.Flat.dCoord j v z‖^2 + ‖Work.CR.Flat.dbarCoord j v z‖^2) :=
    fun z => mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => by positivity)
  have hG2nn : ∀ z, 0 ≤ ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k := fun z => by positivity
  -- the Caccioppoli hypothesis in `ℝ≥0∞` form
  have hHk' : ∫⁻ z in R, C' z ≤ ENNReal.ofReal C₀ * ∫⁻ z in R, D' z := by
    have h1 : ∫⁻ z in R, C' z = ENNReal.ofReal (∫ z in R, (χ z)^2 * ∑ j : Fin n,
        (‖Work.CR.Flat.dCoord j v z‖^2 + ‖Work.CR.Flat.dbarCoord j v z‖^2)) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hG1int
        (Filter.Eventually.of_forall hG1nn)).symm
    have h2 : ∫⁻ z in R, D' z
        = ENNReal.ofReal (∫ z in R, ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k) :=
      (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hG2int
        (Filter.Eventually.of_forall hG2nn)).symm
    calc ∫⁻ z in R, C' z = ENNReal.ofReal (∫ z in R, (χ z)^2 * ∑ j : Fin n,
          (‖Work.CR.Flat.dCoord j v z‖^2 + ‖Work.CR.Flat.dbarCoord j v z‖^2)) := h1
      _ ≤ ENNReal.ofReal (C₀ * ∫ z in R, ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k) :=
          ENNReal.ofReal_le_ofReal hHk
      _ = ENNReal.ofReal C₀ * ENNReal.ofReal (∫ z in R, ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k) :=
          ENNReal.ofReal_mul hC₀
      _ = ENNReal.ofReal C₀ * ∫⁻ z in R, D' z := by rw [h2]
  -- vanishing off `S` of the four integrands
  have hA'zero : ∀ z, z ∉ S → A' z = 0 := by
    intro z hz
    simp only [A']
    rw [hχzero_off z hz]
    simp
  have hB'zero : ∀ z, z ∉ S → B' z = 0 := by
    intro z hz
    have hzt : z ∉ tsupport χ := fun h => hz (hχsupp h)
    simp only [B']
    rw [fderiv_eq_zero_of_notMem_tsupport hzt]
    simp
  have hC'zero : ∀ z, z ∉ S → C' z = 0 := by
    intro z hz
    simp only [C']
    rw [hχzero_off z hz]
    simp
  have hD'zero : ∀ z, z ∉ S → D' z = 0 := by
    intro z hz
    have hzt : z ∉ tsupport χ := fun h => hz (hχsupp h)
    simp only [D']
    rw [fderiv_eq_zero_of_notMem_tsupport hzt]
    simp
  -- pointwise bound
  have hpt : ∀ z, ENNReal.ofReal (‖fderiv ℝ W z‖^2) ≤ 2 * A' z + 2 * B' z := by
    intro z
    have hle := fderiv_mul_le hsρ hvCD hχcd rfl hχsupp hχnn z
    have h1 : ‖fderiv ℝ W z‖^2 ≤ 2 * ((χ z)^2 * ‖fderiv ℝ v z‖^2)
        + 2 * (‖v z‖^2 * ‖fderiv ℝ χ z‖^2) := by
      have h2 := pow_le_pow_left₀ (norm_nonneg (fderiv ℝ W z)) hle 2
      nlinarith [sq_nonneg (χ z * ‖fderiv ℝ v z‖ - ‖v z‖ * ‖fderiv ℝ χ z‖)]
    calc ENNReal.ofReal (‖fderiv ℝ W z‖^2)
        ≤ ENNReal.ofReal (2 * ((χ z)^2 * ‖fderiv ℝ v z‖^2)
            + 2 * (‖v z‖^2 * ‖fderiv ℝ χ z‖^2)) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (2 * ((χ z)^2 * ‖fderiv ℝ v z‖^2))
            + ENNReal.ofReal (2 * (‖v z‖^2 * ‖fderiv ℝ χ z‖^2)) :=
          ENNReal.ofReal_add (by positivity) (by positivity)
      _ = 2 * A' z + 2 * B' z := by
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
              ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  -- continuity of `A'` on `S`, giving a.e. measurability of `2 * A'`
  have hA'cont : ContinuousOn A' S := by
    intro z hz
    have hzR : z ∈ R := hSR hz
    have hv_at : ContinuousAt (fun w => fderiv ℝ v w) z :=
      (hvCD.contDiffAt ((Work.CR.Flat.isOpen_polydisc 0 ρ).mem_nhds hzR)).continuousAt_fderiv
        (by norm_num)
    have hreal : ContinuousAt (fun w => (χ w)^2 * ‖fderiv ℝ v w‖^2) z :=
      ((hχcd.continuous.continuousAt).pow 2).mul ((hv_at.norm).pow 2)
    exact (ENNReal.continuous_ofReal.continuousWithinAt).comp hreal.continuousWithinAt
      (fun y _ => Set.mem_univ _)
  have hA'meas : AEMeasurable (fun z => 2 * A' z) (MeasureTheory.volume.restrict S) :=
    (hA'cont.aemeasurable (μ := MeasureTheory.volume) hSmeas).const_mul 2
  -- the elementary estimates
  have hA'le : ∫⁻ z in S, A' z ≤ ENNReal.ofReal Cg * ∫⁻ z in S, C' z := by
    rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal Cg) (fun z => C' z)
      ENNReal.ofReal_ne_top]
    refine MeasureTheory.lintegral_mono fun z => ?_
    have hχs : 0 ≤ (χ z)^2 := sq_nonneg _
    have h1 : (χ z)^2 * ‖fderiv ℝ v z‖^2 ≤ Cg * ((χ z)^2 * ∑ j : Fin n,
        (‖Work.CR.Flat.dCoord j v z‖^2 + ‖Work.CR.Flat.dbarCoord j v z‖^2)) := by
      have h2 := mul_le_mul_of_nonneg_left (hCg v z) hχs
      nlinarith [h2]
    calc A' z = ENNReal.ofReal ((χ z)^2 * ‖fderiv ℝ v z‖^2) := rfl
      _ ≤ ENNReal.ofReal (Cg * ((χ z)^2 * ∑ j : Fin n,
            (‖Work.CR.Flat.dCoord j v z‖^2 + ‖Work.CR.Flat.dbarCoord j v z‖^2))) :=
          ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal Cg * C' z := ENNReal.ofReal_mul hCg0
  have hB'le : ∫⁻ z in S, B' z ≤ ENNReal.ofReal (L^2) * ∫⁻ z in S, ‖v z‖ₑ ^ (2:ℝ) := by
    rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (L^2))
      (fun z => ‖v z‖ₑ ^ (2:ℝ)) ENNReal.ofReal_ne_top]
    refine MeasureTheory.lintegral_mono fun z => ?_
    have h3 : ‖fderiv ℝ χ z‖^2 ≤ L^2 := pow_le_pow_left₀ (norm_nonneg _) (hL z) 2
    have h1 : ‖v z‖^2 * ‖fderiv ℝ χ z‖^2 ≤ L^2 * ‖v z‖^2 :=
      (mul_le_mul_of_nonneg_left h3 (by positivity)).trans (le_of_eq (by ring))
    calc B' z = ENNReal.ofReal (‖v z‖^2 * ‖fderiv ℝ χ z‖^2) := rfl
      _ ≤ ENNReal.ofReal (L^2 * ‖v z‖^2) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (L^2) * ENNReal.ofReal (‖v z‖^2) := ENNReal.ofReal_mul (sq_nonneg L)
      _ = ENNReal.ofReal (L^2) * ‖v z‖ₑ ^ (2:ℝ) := by rw [← enorm_sq_eq_ofReal (v z)]
  have hC'' : ∫⁻ z in S, C' z ≤ ENNReal.ofReal C₀ * ∫⁻ z in S, D' z := by
    rw [← setLIntegral_eq_of_zero_off (μ := MeasureTheory.volume) hRmeas hSmeas hSR
        (f := C') hC'zero,
      ← setLIntegral_eq_of_zero_off (μ := MeasureTheory.volume) hRmeas hSmeas hSR
        (f := D') hD'zero]
    exact hHk'
  have hD'le : ∫⁻ z in S, D' z ≤ ENNReal.ofReal (L^2) * ∫⁻ z in S, ‖v z‖ₑ ^ (2:ℝ) := by
    rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (L^2))
      (fun z => ‖v z‖ₑ ^ (2:ℝ)) ENNReal.ofReal_ne_top]
    refine MeasureTheory.lintegral_mono fun z => ?_
    have h3 : ‖fderiv ℝ χ z‖^2 ≤ L^2 := pow_le_pow_left₀ (norm_nonneg _) (hL z) 2
    have h2 : 0 ≤ (‖u z‖^2)^k := by positivity
    have h1 : ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k ≤ L^2 * (‖u z‖^2)^k :=
      mul_le_mul_of_nonneg_right h3 h2
    have hnormv : ‖v z‖ₑ ^ (2:ℝ) = ENNReal.ofReal ((‖u z‖^2)^k) := by
      rw [enorm_sq_eq_ofReal]
      congr 1
      show ‖(u z)^k‖^2 = (‖u z‖^2)^k
      rw [norm_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
    calc D' z = ENNReal.ofReal (‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k) := rfl
      _ ≤ ENNReal.ofReal (L^2 * (‖u z‖^2)^k) := ENNReal.ofReal_le_ofReal h1
      _ = ENNReal.ofReal (L^2) * ENNReal.ofReal ((‖u z‖^2)^k) := ENNReal.ofReal_mul (sq_nonneg L)
      _ = ENNReal.ofReal (L^2) * ‖v z‖ₑ ^ (2:ℝ) := by rw [← hnormv]
  -- the `L²` identity for `v`
  have hBeq : (MeasureTheory.eLpNorm v 2 (MeasureTheory.volume.restrict S)) ^ (2:ℝ)
      = ∫⁻ z in S, ‖v z‖ₑ ^ (2:ℝ) := by
    have hm : AEStronglyMeasurable v (MeasureTheory.volume.restrict S) :=
      ((hvCD.mono hSR).continuousOn).aestronglyMeasurable hSmeas
    have h := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
      (μ := MeasureTheory.volume.restrict S) (f := v) (p := (2:NNReal)) (by norm_num) hm
    simpa using h
  -- the `L²` identity for `∇W`
  have hXeq : (MeasureTheory.eLpNorm (fderiv ℝ W) 2 MeasureTheory.volume) ^ (2:ℝ)
      = ∫⁻ z, ‖fderiv ℝ W z‖ₑ ^ (2:ℝ) := by
    have hm : AEStronglyMeasurable (fderiv ℝ W) MeasureTheory.volume :=
      (hWcd.continuous_fderiv (by norm_num)).aestronglyMeasurable
    have h := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
      (μ := MeasureTheory.volume) (f := fderiv ℝ W) (p := (2:NNReal)) (by norm_num) hm
    simpa using h
  have hvan : ∀ z, z ∉ S → 2 * A' z + 2 * B' z = 0 := by
    intro z hz
    rw [hA'zero z hz, hB'zero z hz]; simp
  -- the squared estimate
  have hchain : (MeasureTheory.eLpNorm (fderiv ℝ W) 2 MeasureTheory.volume) ^ (2:ℝ)
      ≤ (ENNReal.ofReal (Real.sqrt (2 * (Cg * C₀ + 1)) * L)
          * MeasureTheory.eLpNorm v 2 (MeasureTheory.volume.restrict S)) ^ (2:ℝ) := by
    have hZeq : (ENNReal.ofReal (Real.sqrt (2 * (Cg * C₀ + 1)) * L)
          * MeasureTheory.eLpNorm v 2 (MeasureTheory.volume.restrict S)) ^ (2:ℝ)
        = ENNReal.ofReal (2 * (Cg * C₀ + 1) * L^2) * ∫⁻ z in S, ‖v z‖ₑ ^ (2:ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0:ℝ) ≤ 2), hBeq]
      congr 1
      congr 1
      rw [Real.rpow_two, mul_pow, Real.sq_sqrt (by positivity)]
    rw [hXeq, hZeq]
    calc ∫⁻ z, ‖fderiv ℝ W z‖ₑ ^ (2:ℝ)
        ≤ ∫⁻ z, (2 * A' z + 2 * B' z) := by
          refine MeasureTheory.lintegral_mono fun z => ?_
          rw [enorm_sq_eq_ofReal]
          exact hpt z
      _ = ∫⁻ z in S, (2 * A' z + 2 * B' z) :=
          lintegral_eq_lintegral_restrict hSmeas hvan
      _ = (2 * ∫⁻ z in S, A' z) + (2 * ∫⁻ z in S, B' z) := by
          rw [MeasureTheory.lintegral_add_left' hA'meas (fun z => 2 * B' z),
              MeasureTheory.lintegral_const_mul' 2 A' (by norm_num),
              MeasureTheory.lintegral_const_mul' 2 B' (by norm_num)]
      _ ≤ (2 * (ENNReal.ofReal Cg * ∫⁻ z in S, C' z))
            + (2 * (ENNReal.ofReal (L^2) * ∫⁻ z in S, ‖v z‖ₑ ^ (2:ℝ))) :=
          add_le_add (mul_le_mul_of_nonneg_left hA'le (by norm_num : (0:ENNReal) ≤ 2))
            (mul_le_mul_of_nonneg_left hB'le (by norm_num : (0:ENNReal) ≤ 2))
      _ ≤ (2 * (ENNReal.ofReal Cg * (ENNReal.ofReal C₀ * ∫⁻ z in S, D' z)))
            + (2 * (ENNReal.ofReal (L^2) * ∫⁻ z in S, ‖v z‖ₑ ^ (2:ℝ))) :=
          add_le_add
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hC'' (by positivity : (0:ENNReal) ≤ ENNReal.ofReal Cg))
              (by norm_num : (0:ENNReal) ≤ 2))
            le_rfl
      _ ≤ (2 * (ENNReal.ofReal Cg * (ENNReal.ofReal C₀
              * (ENNReal.ofReal (L^2) * ∫⁻ z in S, ‖v z‖ₑ ^ (2:ℝ)))))
            + (2 * (ENNReal.ofReal (L^2) * ∫⁻ z in S, ‖v z‖ₑ ^ (2:ℝ))) :=
          add_le_add
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hD'le (by positivity : (0:ENNReal) ≤ ENNReal.ofReal C₀))
                (by positivity : (0:ENNReal) ≤ ENNReal.ofReal Cg))
              (by norm_num : (0:ENNReal) ≤ 2))
            le_rfl
      _ = ENNReal.ofReal (2 * (Cg * C₀ + 1) * L^2) * ∫⁻ z in S, ‖v z‖ₑ ^ (2:ℝ) := by
          have hCgL : ENNReal.ofReal (Cg * C₀ + 1)
              = ENNReal.ofReal Cg * ENNReal.ofReal C₀ + 1 := by
            rw [ENNReal.ofReal_add (mul_nonneg hCg0 hC₀) (by norm_num),
                ENNReal.ofReal_mul hCg0, ENNReal.ofReal_one]
          have hLL : ENNReal.ofReal (2 * (Cg * C₀ + 1) * L^2)
              = 2 * (ENNReal.ofReal Cg * ENNReal.ofReal C₀ + 1) * ENNReal.ofReal (L^2) := by
            rw [show (2:ℝ) * (Cg * C₀ + 1) * L^2 = (2 * (Cg * C₀ + 1)) * L^2 by ring,
                ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * (Cg * C₀ + 1)),
                ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat, hCgL]
          rw [hLL]; ring
  -- square roots
  have h1 : MeasureTheory.eLpNorm (fderiv ℝ W) 2 MeasureTheory.volume
      = ((MeasureTheory.eLpNorm (fderiv ℝ W) 2 MeasureTheory.volume) ^ (2:ℝ)) ^ (1/2:ℝ) := by
    rw [← ENNReal.rpow_mul,
        show (2:ℝ) * (1/2) = 1 by norm_num, ENNReal.rpow_one]
  rw [h1]
  refine le_trans (ENNReal.rpow_le_rpow hchain (by norm_num : (0:ℝ) ≤ 1/2)) ?_
  rw [← ENNReal.rpow_mul, show (2:ℝ) * (1/2) = 1 by norm_num, ENNReal.rpow_one]

/-! ## The single Moser step -/

theorem nnMoserStep {n : ℕ} (hn : 0 < n) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∃ Kb : ℝ, 0 < Kb ∧
      ∀ {ρ : Fin n → ℝ} {u : Work.NN.Core.Cn n → ℂ},
      ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ) → ∀ {k : ℕ}, 1 ≤ k →
      ∀ {r s : Fin n → ℝ}, (∀ j, r j < s j) → (∀ j, s j < ρ j) →
      ∀ {χ : Work.NN.Core.Cn n → ℝ}, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
        tsupport χ ⊆ Work.CR.Flat.polydisc 0 s → (∀ z, 0 ≤ χ z) → (∀ z, χ z ≤ 1) →
        (∀ z, (∀ j, ‖z j‖ ≤ r j) → χ z = 1) →
        (∫ z in Work.CR.Flat.polydisc 0 ρ, (χ z)^2 *
            (∑ j, (‖Work.CR.Flat.dCoord j (fun w => (u w)^k) z‖^2
                 + ‖Work.CR.Flat.dbarCoord j (fun w => (u w)^k) z‖^2))
          ≤ C₀ * ∫ z in Work.CR.Flat.polydisc 0 ρ,
              ‖fderiv ℝ χ z‖^2 * (‖u z‖^2)^k) →
        ∀ {L : ℝ}, 0 ≤ L → (∀ z, ‖fderiv ℝ χ z‖ ≤ L) →
        MeasureTheory.eLpNorm (fun z => (u z)^k)
            ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal))
            (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
          ≤ ENNReal.ofReal (Real.sqrt (Kb * L)) *
            MeasureTheory.eLpNorm (fun z => (u z)^k) 2
              (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) := by
  obtain ⟨CGN, hCGN0, hGN⟩ := Work.NN.Core.gagliardoNirenbergGeomMean hn
  obtain ⟨Cg, hCg0, hCg⟩ := nnGradBoundPoint hn
  refine ⟨CGN * Real.sqrt (2 * (Cg * C₀ + 1)), by positivity, ?_⟩
  intro ρ u hu k hk r s hrs hsρ χ hχcd hχcs hχsupp hχnn hχle1 hχ1 hHk L hL0 hL
  let v : Work.NN.Core.Cn n → ℂ := fun z => (u z)^k
  let W : Work.NN.Core.Cn n → ℂ := fun z => (χ z : ℂ) * v z
  let A₂ : ENNReal := MeasureTheory.eLpNorm v 2
    (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s))
  change MeasureTheory.eLpNorm v ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal))
        (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
      ≤ ENNReal.ofReal (Real.sqrt ((CGN * Real.sqrt (2 * (Cg * C₀ + 1))) * L)) * A₂
  have hχzero_off : ∀ z, (∃ j, s j ≤ ‖z j‖) → χ z = 0 := by
    intro z hz
    by_contra hne
    obtain ⟨j, hj⟩ := hz
    have hmem : z ∈ tsupport χ := subset_closure (Function.mem_support.mpr hne)
    have hlt : ‖z j‖ < s j := by
      simpa using (Work.CR.Flat.mem_polydisc.mp (hχsupp hmem)) j
    exact absurd hlt (not_lt.mpr hj)
  have hχzero : ∀ z, z ∉ Work.CR.Flat.polydisc 0 s → χ z = 0 := by
    intro z hz
    refine hχzero_off z ?_
    by_contra hcon
    simp only [not_exists, not_le] at hcon
    exact hz fun j => by simpa using hcon j
  have hWcd : ContDiff ℝ 1 W :=
    Work.NN.Core.contDiff_one_mul_of_support (ρ := ρ) (r := s) hχcd hχzero_off hsρ (hu.pow k)
  have hWcs : HasCompactSupport W := by
    have h1 : HasCompactSupport (fun z : Work.NN.Core.Cn n => (χ z : ℂ)) :=
      hχcs.comp_left (g := Complex.ofRealCLM) (by simp)
    exact h1.mul_right (f' := v)
  -- the `L²` bound for `∇W`
  have hY : MeasureTheory.eLpNorm (fderiv ℝ W) 2 MeasureTheory.volume
      ≤ ENNReal.ofReal (Real.sqrt (2 * (Cg * C₀ + 1)) * L) * A₂ :=
    fderiv_eLpNorm_bound hC₀ hL0 hCg0.le hCg hu hsρ hχcd hχcs hχsupp hχnn hHk hL
  -- `‖W‖_{L²} ≤ A₂`
  have hW2 : MeasureTheory.eLpNorm W 2 MeasureTheory.volume ≤ A₂ := by
    have hWmeas : AEStronglyMeasurable W MeasureTheory.volume :=
      hWcd.continuous.aestronglyMeasurable
    have hsuppW : Function.support W ⊆ Work.CR.Flat.polydisc 0 s := by
      intro z hz
      by_contra hzS
      exact hz (by simp only [W, hχzero z hzS, Complex.ofReal_zero, zero_mul])
    rw [← MeasureTheory.eLpNorm_restrict_eq_of_support_subset hWmeas hsuppW]
    refine MeasureTheory.eLpNorm_mono (hWmeas.mono_measure MeasureTheory.Measure.restrict_le_self) ?_
    intro z
    have h3 : ‖(χ z : ℂ)‖ = χ z := by
      rw [show ‖(χ z : ℂ)‖ = ‖χ z‖ from by simp, Real.norm_of_nonneg (hχnn z)]
    rw [show W z = (χ z : ℂ) * v z from rfl, norm_mul, h3]
    calc χ z * ‖v z‖ ≤ 1 * ‖v z‖ := mul_le_mul_of_nonneg_right (hχle1 z) (norm_nonneg _)
      _ = ‖v z‖ := one_mul _
  -- `‖u^k‖_{L^{2(2n)'}(r)} ≤ ‖W‖_{L^{2(2n)'}}`
  have hleq : MeasureTheory.eLpNorm v ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal))
        (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
      ≤ MeasureTheory.eLpNorm W ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal))
        MeasureTheory.volume := by
    have hae : v =ᵐ[MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)] W := by
      filter_upwards [MeasureTheory.ae_restrict_mem
        (Work.CR.Flat.isOpen_polydisc 0 r).measurableSet] with z hz
      have hz1 : (∀ j, ‖z j‖ ≤ r j) := fun j => le_of_lt (by simpa using hz j)
      show v z = W z
      simp only [W]
      rw [hχ1 z hz1]
      simp
    calc MeasureTheory.eLpNorm v ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal))
            (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
        = MeasureTheory.eLpNorm W ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal))
            (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)) :=
          MeasureTheory.eLpNorm_congr_ae hae
      _ ≤ MeasureTheory.eLpNorm W ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal))
            MeasureTheory.volume :=
          MeasureTheory.eLpNorm_mono_measure W MeasureTheory.Measure.restrict_le_self
  -- combine with Gagliardo–Nirenberg
  have hGNv' : (MeasureTheory.eLpNorm W ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal))
        MeasureTheory.volume)^(2:ℝ)
      ≤ ENNReal.ofReal CGN * (MeasureTheory.eLpNorm W 2 MeasureTheory.volume)
        * (MeasureTheory.eLpNorm (fderiv ℝ W) 2 MeasureTheory.volume) := by
    have h := hGN W hWcd hWcs
    rw [ENNReal_rpow_two]
    exact h
  have hkey : (MeasureTheory.eLpNorm v ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal))
        (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)))^(2:ℝ)
      ≤ (ENNReal.ofReal (Real.sqrt ((CGN * Real.sqrt (2 * (Cg * C₀ + 1))) * L)) * A₂)^(2:ℝ) := by
    have hZeq : (ENNReal.ofReal (Real.sqrt ((CGN * Real.sqrt (2 * (Cg * C₀ + 1))) * L)) * A₂)^(2:ℝ)
        = ENNReal.ofReal (CGN * (Real.sqrt (2 * (Cg * C₀ + 1)) * L)) * A₂ ^ (2:ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2),
          ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num : (0:ℝ) ≤ 2),
          Real.rpow_two]
      congr 1
      congr 1
      rw [Real.sq_sqrt (by positivity)]
      ring
    calc (MeasureTheory.eLpNorm v ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal))
            (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)))^(2:ℝ)
        ≤ (MeasureTheory.eLpNorm W ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal))
            MeasureTheory.volume)^(2:ℝ) :=
          ENNReal.rpow_le_rpow hleq (by norm_num : (0:ℝ) ≤ 2)
      _ ≤ ENNReal.ofReal CGN * (MeasureTheory.eLpNorm W 2 MeasureTheory.volume)
            * (MeasureTheory.eLpNorm (fderiv ℝ W) 2 MeasureTheory.volume) := hGNv'
      _ ≤ ENNReal.ofReal CGN * A₂ * (ENNReal.ofReal (Real.sqrt (2 * (Cg * C₀ + 1)) * L) * A₂) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hW2 (by positivity)) hY (by positivity)
            (by positivity)
      _ = ENNReal.ofReal (CGN * (Real.sqrt (2 * (Cg * C₀ + 1)) * L)) * A₂ ^ (2:ℝ) := by
          calc ENNReal.ofReal CGN * A₂ * (ENNReal.ofReal (Real.sqrt (2 * (Cg * C₀ + 1)) * L) * A₂)
              = ENNReal.ofReal CGN * ENNReal.ofReal (Real.sqrt (2 * (Cg * C₀ + 1)) * L)
                  * (A₂ * A₂) := by ac_rfl
            _ = ENNReal.ofReal (CGN * (Real.sqrt (2 * (Cg * C₀ + 1)) * L)) * (A₂ * A₂) := by
                rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ CGN)]
            _ = ENNReal.ofReal (CGN * (Real.sqrt (2 * (Cg * C₀ + 1)) * L)) * A₂ ^ (2:ℝ) := by
                rw [ENNReal_rpow_two, pow_two]
      _ = (ENNReal.ofReal (Real.sqrt ((CGN * Real.sqrt (2 * (Cg * C₀ + 1))) * L)) * A₂)^(2:ℝ) :=
          hZeq.symm
  -- take square roots
  have h1 : MeasureTheory.eLpNorm v ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal))
        (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
      = ((MeasureTheory.eLpNorm v ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal))
        (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)))^(2:ℝ))^(1/2:ℝ) := by
    rw [← ENNReal.rpow_mul, show (2:ℝ) * (1/2) = 1 by norm_num, ENNReal.rpow_one]
  rw [h1]
  refine le_trans (ENNReal.rpow_le_rpow hkey (by norm_num : (0:ℝ) ≤ 1/2)) ?_
  rw [← ENNReal.rpow_mul, show (2:ℝ) * (1/2) = 1 by norm_num, ENNReal.rpow_one]

/-! ## From the `u^k` form to the `u` form -/

private lemma eLpNorm_pow_eq' {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    {p : ENNReal} {k : ℕ} (hk : 1 ≤ k) (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun x => f x ^ k) p μ = (eLpNorm f (p * ENNReal.ofReal (k : ℝ)) μ) ^ (k : ℝ) := by
  have hfpow : AEStronglyMeasurable (fun x => f x ^ k) μ := hf.pow k
  have hnorm : AEStronglyMeasurable (fun x => ‖f x‖ ^ (k:ℝ)) μ := by
    have h2 : (fun x => ‖f x‖ ^ (k:ℝ)) = fun x => ‖f x‖ ^ k := by
      funext x; exact Real.rpow_natCast _ _
    rw [h2]; exact (hf.norm.pow k)
  have h1 : eLpNorm (fun x => f x ^ k) p μ = eLpNorm (fun x => ‖f x‖ ^ (k:ℝ)) p μ := by
    refine eLpNorm_congr_norm_ae hfpow hnorm ?_
    filter_upwards with x
    rw [norm_pow, Real.rpow_natCast, Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
  rw [h1, eLpNorm_norm_rpow f hf (by exact_mod_cast (by omega : 0 < k))]

/-- **From the `L^{2k}` bound for `u^k` to the `L^{2k(2n)'}` bound for `u`.** -/
theorem nnMoserBoostAux {n : ℕ} {ρ r s : Fin n → ℝ} {u : Work.NN.Core.Cn n → ℂ}
    (hu : ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ))
    (hrs : ∀ j, r j < s j) (hsρ : ∀ j, s j < ρ j)
    {k : ℕ} (hk : 1 ≤ k) {L : ℝ} (hL0 : 0 ≤ L) {Kb : ℝ} (hKb : 0 < Kb)
    (hstep : MeasureTheory.eLpNorm (fun z => (u z) ^ k)
          ((2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal))
          (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
        ≤ ENNReal.ofReal (Real.sqrt (Kb * L)) *
          MeasureTheory.eLpNorm (fun z => (u z) ^ k) 2
            (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s))) :
      MeasureTheory.eLpNorm u
          (ENNReal.ofReal (2 * ((k : ℝ) * ((NNReal.conjExponent (2 * n) : NNReal) : ℝ))))
          (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
        ≤ ENNReal.ofReal ((Kb + 1) * (1 + L)) ^ (1 / (2 * (k : ℝ))) *
          MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (k : ℝ)))
            (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) := by
  have hkpos : (0:ℝ) < (k:ℝ) := by exact_mod_cast (by omega : 0 < k)
  let qE : ENNReal := (2 : ENNReal) * ((NNReal.conjExponent (2 * n) : NNReal) : ENNReal)
  let pX : ENNReal := ENNReal.ofReal (2 * ((k:ℝ) * ((NNReal.conjExponent (2 * n) : NNReal) : ℝ)))
  let pY : ENNReal := ENNReal.ofReal (2 * (k:ℝ))
  let B₂ : ENNReal := MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (k : ℝ)))
    (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s))
  change MeasureTheory.eLpNorm u pX (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
      ≤ ENNReal.ofReal ((Kb + 1) * (1 + L)) ^ (1 / (2 * (k : ℝ))) * B₂
  have hsub_s : Work.CR.Flat.polydisc 0 s ⊆ Work.CR.Flat.polydisc 0 ρ :=
    Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hsρ j))
  have hsub_r : Work.CR.Flat.polydisc 0 r ⊆ Work.CR.Flat.polydisc 0 s :=
    Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hrs j))
  have hmeas_s : AEStronglyMeasurable u (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) :=
    ((hu.mono hsub_s).continuousOn).aestronglyMeasurable (Work.CR.Flat.isOpen_polydisc 0 s).measurableSet
  have hmeas_r : AEStronglyMeasurable u (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)) :=
    ((hu.mono (hsub_r.trans hsub_s)).continuousOn).aestronglyMeasurable
      (Work.CR.Flat.isOpen_polydisc 0 r).measurableSet
  have hexp : pX = qE * ENNReal.ofReal (k : ℝ) := by
    simp only [pX, qE]
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
        ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (k:ℝ)),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
    ac_rfl
  have hexp2 : pY = (2 : ENNReal) * ENNReal.ofReal (k : ℝ) := by
    simp only [pY]
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have hXp : (MeasureTheory.eLpNorm u pX (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)))^(k:ℝ)
      = MeasureTheory.eLpNorm (fun z => (u z)^k) qE
          (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)) := by
    rw [eLpNorm_pow_eq' hk hmeas_r, ← hexp]
  have hYp : (MeasureTheory.eLpNorm u pY (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)))^(k:ℝ)
      = MeasureTheory.eLpNorm (fun z => (u z)^k) 2
          (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) := by
    rw [eLpNorm_pow_eq' hk hmeas_s, ← hexp2]
  have hstep' : (MeasureTheory.eLpNorm u pX (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)))^(k:ℝ)
      ≤ ENNReal.ofReal (Real.sqrt (Kb * L)) *
        (MeasureTheory.eLpNorm u pY (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)))^(k:ℝ) := by
    rw [hXp, hYp]; exact hstep
  have hX_eq : MeasureTheory.eLpNorm u pX (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
      = ((MeasureTheory.eLpNorm u pX (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)))^(k:ℝ))^(1/(k:ℝ)) := by
    rw [← ENNReal.rpow_mul, show (k:ℝ) * (1/(k:ℝ)) = 1 by field_simp, ENNReal.rpow_one]
  have hfac : (ENNReal.ofReal (Real.sqrt (Kb * L)))^(1/(k:ℝ))
      ≤ (ENNReal.ofReal ((Kb + 1) * (1 + L)))^(1/(2*(k:ℝ))) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by positivity),
        ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have h1 : (Real.sqrt (Kb * L))^(1/(k:ℝ)) = (Kb * L)^(1/(2*(k:ℝ))) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
      congr 1
      field_simp
    rw [h1]
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    nlinarith [hKb, hL0]
  calc MeasureTheory.eLpNorm u pX (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
      = ((MeasureTheory.eLpNorm u pX (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r)))^(k:ℝ))^(1/(k:ℝ)) := hX_eq
    _ ≤ (ENNReal.ofReal (Real.sqrt (Kb * L)) *
          (MeasureTheory.eLpNorm u pY (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)))^(k:ℝ))^(1/(k:ℝ)) :=
        ENNReal.rpow_le_rpow hstep' (by positivity)
    _ = (ENNReal.ofReal (Real.sqrt (Kb * L)))^(1/(k:ℝ)) *
          ((MeasureTheory.eLpNorm u pY (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)))^(k:ℝ))^(1/(k:ℝ)) :=
        ENNReal.mul_rpow_of_nonneg _ _ (by positivity)
    _ = (ENNReal.ofReal (Real.sqrt (Kb * L)))^(1/(k:ℝ)) * B₂ := by
        rw [← ENNReal.rpow_mul, show (k:ℝ) * (1/(k:ℝ)) = 1 by field_simp, ENNReal.rpow_one]
    _ ≤ (ENNReal.ofReal ((Kb + 1) * (1 + L)))^(1/(2*(k:ℝ))) * B₂ :=
        mul_le_mul_left hfac _

/-! ## The boost -/

theorem nnMoserBoost {n : ℕ} (hn : 0 < n) {C₀ : ℝ} (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {ρ : Fin n → ℝ}, (∀ j, 0 < ρ j) → ∀ {u : Work.NN.Core.Cn n → ℂ},
      ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ) →
      (∀ (k : ℕ), 1 ≤ k → ∀ (φ : Work.NN.Core.Cn n → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρ → (∀ z, 0 ≤ φ z) →
        ∫ z in Work.CR.Flat.polydisc 0 ρ, (φ z)^2 *
            (∑ j, (‖Work.CR.Flat.dCoord j (fun w => (u w)^k) z‖^2
                 + ‖Work.CR.Flat.dbarCoord j (fun w => (u w)^k) z‖^2))
          ≤ C₀ * ∫ z in Work.CR.Flat.polydisc 0 ρ,
              ‖fderiv ℝ φ z‖^2 * (‖u z‖^2)^k) →
      ∀ {r s : Fin n → ℝ}, (∀ j, r j < s j) → (∀ j, s j < ρ j) →
      ∀ {χ : Work.NN.Core.Cn n → ℝ}, ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
        tsupport χ ⊆ Work.CR.Flat.polydisc 0 s → (∀ z, 0 ≤ χ z) → (∀ z, χ z ≤ 1) →
        (∀ z, (∀ j, ‖z j‖ ≤ r j) → χ z = 1) →
      ∀ {L : ℝ}, 0 ≤ L → (∀ z, ‖fderiv ℝ χ z‖ ≤ L) →
      ∀ (k : ℕ), 1 ≤ k →
        MeasureTheory.eLpNorm u
            (ENNReal.ofReal (2 * ((k : ℝ) * ((NNReal.conjExponent (2 * n) : NNReal) : ℝ))))
            (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 r))
          ≤ (ENNReal.ofReal (C * (1 + L))) ^ (1 / (2 * (k : ℝ))) *
            MeasureTheory.eLpNorm u (ENNReal.ofReal (2 * (k : ℝ)))
              (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 s)) := by
  obtain ⟨Kb, hKb, hstep⟩ := nnMoserStep hn hC₀.le
  refine ⟨Kb + 1, by linarith, ?_⟩
  intro ρ hρ u hu hH r s hrs hsρ χ hχcd hχcs hχsupp hχnn hχle1 hχ1 L hL0 hL k hk
  have hχsuppρ : tsupport χ ⊆ Work.CR.Flat.polydisc 0 ρ :=
    hχsupp.trans (Work.CR.Flat.polydisc_mono (fun j => le_of_lt (hsρ j)))
  refine nnMoserBoostAux hu hrs hsρ hk hL0 hKb (hstep hu hk hrs hsρ hχcd hχcs hχsupp hχnn
    hχle1 hχ1 (hH k hk χ hχcd hχcs hχsuppρ hχnn) hL0 hL)

end Work.NN.Core.Lev
