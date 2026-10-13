/-
# `Work.FTS.PhiStar.Series.Deleg.psiExpansion` — the `eFam`-expansion of the angular model

Let `ψ` be an angular model (`Work.FTS.PhiStar.AngModel α ψ`: `L₀ψ = Γ̄`, `ψ(0) = ψ(π/2) = 0`,
smooth on `(0,π/2)`, continuous on the closed interval, with the `sinθcos²θ`-moment normalised)
and let

  `b m := cmode m (fun _ θ => ψ θ) 0 = (∫₀^{π/2} ψ(θ) e_m(θ) cos θ dθ)

be the `m`-th modal coefficient of `ψ` in the self-adjoint weight `cos θ dθ`
(`Work.FTS.PhiStar.Series.cmode`), where `e_m = eFam m` is the Dirichlet eigenfamily of `Lzero`
(`eFam m θ = cos θ C^{(3/2)}_{2m+1}(sin θ)`, eigenvalue `lam m = 2m(2m+5)`).

**Claim.**  `∑_m b m · e_m(θ) = ψ(θ)` for every `θ ∈ (0, π/2)`.

**Route.**  The three inputs are the decay of the coefficients and the growth of the
eigenfunctions on the one hand, and the `L²`-completeness of `eFam` on the other:

* `hdecay` (`|b m| ≤ C / (lam m · √(2m+1))` for `m ≥ 1`, the statement of `CmodeDecay`) together
  with `hbound` (`|eFam m θ| ≤ √((2m+2)(2m+3))`, the first conjunct of `AngBounds`) gives the
  pointwise majorant

    `|b m e_m(θ)| ≤ √((2m+2)(2m+3)) / (lam m √(2m+1)) ≤ (5/4) m^{-3/2}`  (`m ≥ 1`),

  a summable sequence, the `m = 0` term being a single constant.  Hence the series converges
  absolutely at every `θ ∈ (0,π/2)`, and by the Weierstrass M-test it converges *uniformly* on
  `(0,π/2)`, so its sum `S` is continuous there.
* `eFam_parseval` + `eFam_pythagoras` (the `L²(Iθ, cos θ dθ)` theory of `ModalSolution`) give
  `∫_{Iθ} (ψ - ∑_{m≤N} b m e_m)² cos θ → 0`.
* Dominated convergence (the partial sums are uniformly bounded by the majorant mass, and `ψ` is
  bounded on the compact `Iθ`) then yields `∫_{Iθ} (ψ - S)² cos θ = 0`, i.e. `ψ = S` almost
  everywhere on `Iθ`, hence on `(0,π/2)`; and since both sides are continuous there, they agree
  *everywhere* on `(0,π/2)` (`MeasureTheory.Measure.eqOn_Ioo_of_ae_eq`).

## What is delegated

The five hypotheses of the private assembly lemma `psiExpansion_aux` are the five auxiliary
lemmas, proved by colleagues in this directory:

* `modeRatioLe` — the elementary ratio estimate (with the generous constant `5/4`);
* `summableModeMajorant` — summability of the majorant `(if m = 0 then K else 0) + A m^{-3/2}`;
* `continuousOnTsumEFam` — the Weierstrass M-test for `∑ b m e_m`;
* `residualTendstoZero` — Parseval minus Pythagoras.

Everything else (the definition of the majorant from the hypotheses, the uniform bound on the
partial sums, the identification of the limit, the dominated-convergence/a.e. step and the final
`eqOn_Ioo_of_ae_eq`) is proved in this file.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Series.eFam_zero_moment
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_orthogonal
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_complete
import Submission.Work.FTS.PhiStar.Gegenbauer.gC_ode
import Submission.Work.EllipticEst.ModalSolution.eFam_expansion_L2
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.PhiStar.Series.Deleg.modeRatioLe
import Submission.Work.FTS.PhiStar.Series.Deleg.summableModeMajorant
import Submission.Work.FTS.PhiStar.Series.Deleg.continuousOnTsumEFam
import Submission.Work.FTS.PhiStar.Series.Deleg.residualTendstoZero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators MeasureTheory
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Deleg

set_option autoImplicit false

private abbrev mcoeff (ψ : ℝ → ℝ) : ℕ → ℝ :=
  fun m => Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0

private abbrev modeMajor (ψ : ℝ → ℝ) (C : ℝ) : ℕ → ℝ :=
  fun m => (if m = 0 then |mcoeff ψ 0| * Real.sqrt 6 else 0)
    + (5 * C / 4) * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹

private abbrev modeSum (ψ : ℝ → ℝ) : ℕ → ℝ → ℝ :=
  fun m θ => mcoeff ψ m * Work.FTS.PhiStar.Gegenbauer.eFam m θ

private abbrev seriesSum (ψ : ℝ → ℝ) : ℝ → ℝ :=
  fun θ => ∑' m : ℕ, modeSum ψ m θ

/-- `0` is negligible. -/
private lemma ae_ne_zero : ∀ᵐ θ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), θ ≠ (0 : ℝ) := by
  rw [MeasureTheory.ae_iff]
  simpa using (MeasureTheory.measure_singleton (0 : ℝ) :
    (MeasureTheory.volume : MeasureTheory.Measure ℝ) ({0} : Set ℝ) = 0)

/-- `π/2` is negligible. -/
private lemma ae_ne_pi_half : ∀ᵐ θ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
    θ ≠ Real.pi / 2 := by
  rw [MeasureTheory.ae_iff]
  simpa using (MeasureTheory.measure_singleton (Real.pi / 2) :
    (MeasureTheory.volume : MeasureTheory.Measure ℝ) ({Real.pi / 2} : Set ℝ) = 0)

/-- A property holding on the open interval holds a.e. on `Iθ`. -/
private lemma ae_mem_Ioo_Iθ :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Set.Ioo 0 (Real.pi / 2) := by
  rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  filter_upwards [ae_ne_zero, ae_ne_pi_half] with θ h0 h1 hIcc
  rw [Set.mem_Icc] at hIcc
  exact ⟨lt_of_le_of_ne hIcc.1 (Ne.symm h0), lt_of_le_of_ne hIcc.2 h1⟩

/-- The `(N+1)`-st partial sum of the angular mode series. -/
private abbrev modePart (b : ℕ → ℝ) : ℕ → ℝ → ℝ :=
  fun N θ => ∑ m ∈ Finset.range (N + 1), b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ

/-- **The `L²`-limit of the partial sums is the pointwise limit, a.e.**  If the partial sums
`∑_{m ≤ N} b m e_m` are bounded by `M` on the open interval, converge pointwise there to `S`,
and `∫ (ψ - ∑_{m ≤ N} b m e_m)² cos θ → 0`, while `ψ` is bounded by `M` on `Iθ` and
`S` is continuous on the open interval, then `S = ψ` a.e. on `(0,π/2)`. -/
private theorem ae_eq_of_residual (b : ℕ → ℝ) (ψ S : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hψbound : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |ψ θ| ≤ M)
    (hPbound : ∀ (N : ℕ) (θ : ℝ), θ ∈ Set.Ioo 0 (Real.pi / 2) → |modePart b N θ| ≤ M)
    (hcontS : ContinuousOn S (Set.Ioo 0 (Real.pi / 2)))
    (hmeas : MeasureTheory.AEStronglyMeasurable ψ (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hconv : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Filter.Tendsto (fun N : ℕ => modePart b N θ) Filter.atTop (nhds (S θ)))
    (hlim : Filter.Tendsto (fun N : ℕ => ∫ θ in Work.Spaces.Iθ,
        (ψ θ - modePart b N θ) ^ 2 * Real.cos θ) Filter.atTop (nhds 0)) :
    S =ᵐ[MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))] ψ := by
  have hcospos : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), 0 < Real.cos θ := fun θ hθ =>
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩
  -- `S` is a.e. strongly measurable on `Iθ` (it is continuous on the open interval)
  have hS_ae : MeasureTheory.AEStronglyMeasurable S
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    obtain ⟨g, hg, hgeq⟩ := hcontS.aestronglyMeasurable measurableSet_Ioo
    refine ⟨g, hg, ?_⟩
    show ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), S θ = g θ
    rw [Work.Spaces.Iθ, MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    have h1 : ∀ᵐ θ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
        θ ∈ Set.Ioo 0 (Real.pi / 2) → S θ = g θ :=
      (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mp hgeq
    filter_upwards [h1, ae_ne_zero, ae_ne_pi_half] with θ hθ1 h0 h1' hIcc
    refine hθ1 ?_
    rw [Set.mem_Icc] at hIcc
    exact ⟨lt_of_le_of_ne hIcc.1 (Ne.symm h0), lt_of_le_of_ne hIcc.2 h1'⟩
  -- continuity of each mode and of the partial sums
  have hcontE : ∀ m : ℕ, Continuous (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
    intro m
    have h := (Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous
    exact Real.continuous_cos.mul (h.comp Real.continuous_sin)
  have hcontP : ∀ N : ℕ, Continuous (fun θ : ℝ => modePart b N θ) := by
    intro N
    refine continuous_finsetSum (Finset.range (N + 1)) (fun m _ => ?_)
    exact continuous_const.mul (hcontE m)
  -- the dominating function is integrable
  have hbdInt : MeasureTheory.Integrable (fun θ : ℝ => (2 * M) ^ 2 * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    ContinuousOn.integrableOn_compact isCompact_Icc
      ((continuous_const.mul Real.continuous_cos).continuousOn)
  -- a.e. strong measurability of the residuals
  have hmeasF : ∀ N : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (ψ θ - modePart b N θ) ^ 2 * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    intro N
    have hq : AEMeasurable (fun θ : ℝ => modePart b N θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      (hcontP N).measurable.aemeasurable
    have hm : AEMeasurable (fun θ : ℝ => (ψ θ - modePart b N θ) ^ 2 * Real.cos θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      ((hmeas.aemeasurable.sub hq).pow_const 2).mul Real.continuous_cos.measurable.aemeasurable
    rwa [aestronglyMeasurable_iff_aemeasurable]
  -- the a.e. domination
  have hbound_ae : ∀ N : ℕ, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ‖(ψ θ - modePart b N θ) ^ 2 * Real.cos θ‖ ≤ (2 * M) ^ 2 * Real.cos θ := by
    intro N
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    have hcos : 0 ≤ Real.cos θ := le_of_lt (hcospos θ hθ)
    have h1 : |ψ θ| ≤ M := hψbound θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have h2 : |modePart b N θ| ≤ M := hPbound N θ hθ
    have h3 : |ψ θ - modePart b N θ| ≤ 2 * M := by
      calc |ψ θ - modePart b N θ| = |ψ θ + -(modePart b N θ)| := by ring_nf
        _ ≤ |ψ θ| + |-(modePart b N θ)| := abs_add_le _ _
        _ = |ψ θ| + |modePart b N θ| := by rw [abs_neg]
        _ ≤ 2 * M := by linarith
    have hsq : (ψ θ - modePart b N θ) ^ 2 ≤ (2 * M) ^ 2 := by
      calc (ψ θ - modePart b N θ) ^ 2 = |ψ θ - modePart b N θ| ^ 2 := (sq_abs _).symm
        _ ≤ (2 * M) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
    calc ‖(ψ θ - modePart b N θ) ^ 2 * Real.cos θ‖
        = |(ψ θ - modePart b N θ) ^ 2 * Real.cos θ| := Real.norm_eq_abs _
      _ = (ψ θ - modePart b N θ) ^ 2 * Real.cos θ := by
            rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hcos)]
      _ ≤ (2 * M) ^ 2 * Real.cos θ := mul_le_mul_of_nonneg_right hsq hcos
  -- the a.e. pointwise convergence
  have hlim_ae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      Filter.Tendsto (fun N : ℕ => (ψ θ - modePart b N θ) ^ 2 * Real.cos θ) Filter.atTop
        (nhds ((ψ θ - S θ) ^ 2 * Real.cos θ)) := by
    filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
    exact (((tendsto_const_nhds.sub (hconv θ hθ)).pow 2).mul tendsto_const_nhds)
  -- dominated convergence
  have hdct := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (F := fun N θ => (ψ θ - modePart b N θ) ^ 2 * Real.cos θ)
    (f := fun θ => (ψ θ - S θ) ^ 2 * Real.cos θ)
    (fun θ => (2 * M) ^ 2 * Real.cos θ) hmeasF hbdInt hbound_ae hlim_ae
  have hint0 : ∫ θ in Work.Spaces.Iθ, (ψ θ - S θ) ^ 2 * Real.cos θ = 0 :=
    tendsto_nhds_unique hdct hlim
  -- integrability of the limit residual
  have hSbound : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |S θ| ≤ M := by
    intro θ hθ
    refine abs_le.mpr ⟨?_, ?_⟩
    · exact ge_of_tendsto (hconv θ hθ)
        (Eventually.of_forall (fun N => (abs_le.mp (hPbound N θ hθ)).1))
    · exact le_of_tendsto (hconv θ hθ)
        (Eventually.of_forall (fun N => (abs_le.mp (hPbound N θ hθ)).2))
  have hf_int : MeasureTheory.Integrable (fun θ : ℝ => (ψ θ - S θ) ^ 2 * Real.cos θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    refine hbdInt.mono' ?_ ?_
    · have hm : AEMeasurable (fun θ : ℝ => (ψ θ - S θ) ^ 2 * Real.cos θ)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        ((hmeas.aemeasurable.sub hS_ae.aemeasurable).pow_const 2).mul
          Real.continuous_cos.measurable.aemeasurable
      rwa [aestronglyMeasurable_iff_aemeasurable]
    · filter_upwards [ae_mem_Ioo_Iθ] with θ hθ
      have hcos : 0 ≤ Real.cos θ := le_of_lt (hcospos θ hθ)
      have h1 : |ψ θ| ≤ M := hψbound θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
      have h2 : |S θ| ≤ M := hSbound θ hθ
      have h3 : |ψ θ - S θ| ≤ 2 * M := by
        calc |ψ θ - S θ| = |ψ θ + -S θ| := by ring_nf
          _ ≤ |ψ θ| + |-S θ| := abs_add_le _ _
          _ = |ψ θ| + |S θ| := by rw [abs_neg]
          _ ≤ 2 * M := by linarith
      have hsq : (ψ θ - S θ) ^ 2 ≤ (2 * M) ^ 2 := by
        calc (ψ θ - S θ) ^ 2 = |ψ θ - S θ| ^ 2 := (sq_abs _).symm
          _ ≤ (2 * M) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h3 2
      calc ‖(ψ θ - S θ) ^ 2 * Real.cos θ‖
          = |(ψ θ - S θ) ^ 2 * Real.cos θ| := Real.norm_eq_abs _
        _ = (ψ θ - S θ) ^ 2 * Real.cos θ := by
              rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hcos)]
        _ ≤ (2 * M) ^ 2 * Real.cos θ := mul_le_mul_of_nonneg_right hsq hcos
  -- the residual vanishes a.e.
  have hnonneg : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      0 ≤ (ψ θ - S θ) ^ 2 * Real.cos θ := by
    filter_upwards [MeasureTheory.ae_restrict_mem (s := Work.Spaces.Iθ) measurableSet_Icc]
      with θ hθ
    exact mul_nonneg (sq_nonneg _)
      (Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)
  have hfae : (fun θ : ℝ => (ψ θ - S θ) ^ 2 * Real.cos θ)
      =ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnonneg hf_int).mp hint0
  have hfae' : (fun θ : ℝ => (ψ θ - S θ) ^ 2 * Real.cos θ)
      =ᵐ[MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))] 0 :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset Ioo_subset_Icc_self hfae
  filter_upwards [hfae', MeasureTheory.ae_restrict_mem measurableSet_Ioo] with θ hθ hmem
  have hc : Real.cos θ ≠ 0 := ne_of_gt (hcospos θ hmem)
  have hsq : (ψ θ - S θ) ^ 2 = 0 := (mul_eq_zero.mp hθ).resolve_right hc
  have hzero : ψ θ - S θ = 0 := sq_eq_zero_iff.mp hsq
  linarith


private theorem psiExpansion_aux (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5)
    (hψ : Work.FTS.PhiStar.AngModel α ψ)
    (hdecay : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.cmode m (fun _ θ => ψ θ) 0|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hbound : ∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)))
    (hModeRatio : ∀ m : ℕ, 1 ≤ m →
      Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
          / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
        ≤ (5 / 4) * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹)
    (hMajorant : ∀ K A : ℝ,
      Summable (fun m : ℕ => (if m = 0 then K else 0) + A * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹))
    (hContTsum : ∀ (b : ℕ → ℝ) (u : ℕ → ℝ), Summable u →
      (∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ u m) →
      ContinuousOn (fun θ : ℝ => ∑' m : ℕ, b m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        (Set.Ioo 0 (Real.pi / 2)))
    (hResidual : ∀ ψ : ℝ → ℝ,
      MeasureTheory.AEStronglyMeasurable ψ (MeasureTheory.volume.restrict Work.Spaces.Iθ) →
      MeasureTheory.IntegrableOn (fun θ => ψ θ ^ 2 * Real.cos θ) Work.Spaces.Iθ →
      Filter.Tendsto (fun N : ℕ => ∫ θ in Work.Spaces.Iθ,
          (ψ θ - ∑ m ∈ Finset.range (N + 1),
            Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) ^ 2 * Real.cos θ)
        Filter.atTop (nhds 0)) :
    ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      (∑' m : ℕ, Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ := by
  obtain ⟨C, hCpos, hCdec⟩ := hdecay
  have hpi4 : (Real.pi / 4) ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  -- summability of the majorant
  have hu : Summable (modeMajor ψ C) :=
    hMajorant (|mcoeff ψ 0| * Real.sqrt 6) (5 * C / 4)
  -- the pointwise majorant
  have hbu : ∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |modeSum ψ m θ| ≤ modeMajor ψ C m := by
    intro m θ hθ
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      have hb0 : |Work.FTS.PhiStar.Gegenbauer.eFam 0 θ| ≤ Real.sqrt 6 := by
        have h := hbound 0 θ hθ
        norm_num at h
        exact h
      calc |modeSum ψ 0 θ|
          = |mcoeff ψ 0| * |Work.FTS.PhiStar.Gegenbauer.eFam 0 θ| := by
            simp only [modeSum, abs_mul]
        _ ≤ |mcoeff ψ 0| * Real.sqrt 6 :=
            mul_le_mul_of_nonneg_left hb0 (abs_nonneg _)
        _ = modeMajor ψ C 0 := by
            simp only [modeMajor]
            simp [Real.zero_rpow (show (3 / 2 : ℝ) ≠ 0 by norm_num)]
    · have hm1 : 1 ≤ m := hmpos
      have hm0' : ¬ (m = 0) := Nat.pos_iff_ne_zero.mp hmpos
      have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hlamp : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
        rw [Work.FTS.PhiStar.Gegenbauer.lam]
        nlinarith
      have hsqrtp : 0 < Real.sqrt (2 * (m : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
      have hden : 0 ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) :=
        div_nonneg hCpos.le (mul_pos hlamp hsqrtp).le
      calc |modeSum ψ m θ|
          = |mcoeff ψ m| * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| := by
            simp only [modeSum, abs_mul]
        _ ≤ (C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
              * Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) :=
            mul_le_mul (hCdec m hm1) (hbound m θ hθ) (abs_nonneg _) hden
        _ = C * (Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))
              / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
            ring
        _ ≤ C * ((5 / 4) * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
            mul_le_mul_of_nonneg_left (hModeRatio m hm1) hCpos.le
        _ = (5 * C / 4) * ((m : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by ring
        _ = modeMajor ψ C m := by
            simp only [modeMajor, if_neg hm0']
            ring
  have hu_nonneg : ∀ m, 0 ≤ modeMajor ψ C m :=
    fun m => le_trans (abs_nonneg _) (hbu m (Real.pi / 4) hpi4)
  -- the partial sums are bounded by the total mass of the majorant
  have hpartial : ∀ N : ℕ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |∑ m ∈ Finset.range (N + 1), modeSum ψ m θ| ≤ ∑' m, modeMajor ψ C m := by
    intro N θ hθ
    calc |∑ m ∈ Finset.range (N + 1), modeSum ψ m θ|
        ≤ ∑ m ∈ Finset.range (N + 1), |modeSum ψ m θ| :=
          Finset.abs_sum_le_sum_abs (fun m => modeSum ψ m θ) (Finset.range (N + 1))
      _ ≤ ∑ m ∈ Finset.range (N + 1), modeMajor ψ C m :=
          Finset.sum_le_sum (fun m _ => hbu m θ hθ)
      _ ≤ ∑' m, modeMajor ψ C m :=
          hu.sum_le_tsum _ (fun m _ => hu_nonneg m)
  -- absolute convergence of the mode series at every interior point
  have hsummable : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Summable (modeSum ψ · θ) := by
    intro θ hθ
    have h1 : Summable (fun m => |modeSum ψ m θ|) :=
      Summable.of_nonneg_of_le (fun m => abs_nonneg _) (fun m => hbu m θ hθ) hu
    exact Summable.of_norm (by simpa only [Real.norm_eq_abs] using h1)
  have hconvN : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, modeSum ψ m θ)
        Filter.atTop (nhds (∑' m, modeSum ψ m θ)) :=
    fun θ hθ => (hsummable θ hθ).hasSum.tendsto_sum_nat
  have hconv : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.range (N + 1), modeSum ψ m θ)
        Filter.atTop (nhds (∑' m, modeSum ψ m θ)) :=
    fun θ hθ => (hconvN θ hθ).comp (tendsto_add_atTop_nat 1)
  have hSbound : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      |∑' m, modeSum ψ m θ| ≤ ∑' m, modeMajor ψ C m := by
    intro θ hθ
    refine abs_le.mpr ⟨?_, ?_⟩
    · exact ge_of_tendsto (hconv θ hθ)
        (Eventually.of_forall (fun N => (abs_le.mp (hpartial N θ hθ)).1))
    · exact le_of_tendsto (hconv θ hθ)
        (Eventually.of_forall (fun N => (abs_le.mp (hpartial N θ hθ)).2))
  -- a bound for ψ on the closed interval, and the common bound M
  obtain ⟨Mψ, hMψ⟩ := isCompact_Icc.exists_bound_of_continuousOn hψ.cont
  have hMψ' : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |ψ θ| ≤ Mψ := by
    intro θ hθ
    simpa only [Real.norm_eq_abs] using hMψ θ hθ
  set M : ℝ := max (∑' m, modeMajor ψ C m) Mψ with hMdef
  have hMnonneg : 0 ≤ M := by
    rw [hMdef]
    exact le_trans (tsum_nonneg hu_nonneg) (le_max_left _ _)
  have hψbound : ∀ θ ∈ Set.Icc 0 (Real.pi / 2), |ψ θ| ≤ M := by
    intro θ hθ
    rw [hMdef]
    exact le_trans (hMψ' θ hθ) (le_max_right _ _)
  have hSboundM : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |seriesSum ψ θ| ≤ M := by
    intro θ hθ
    rw [hMdef]
    simp only [seriesSum]
    exact le_trans (hSbound θ hθ) (le_max_left _ _)
  -- the two inputs of the a.e. step
  have hmeasψ : MeasureTheory.AEStronglyMeasurable ψ
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    hψ.cont.aestronglyMeasurable measurableSet_Icc
  have hzψ : MeasureTheory.IntegrableOn (fun θ => ψ θ ^ 2 * Real.cos θ) Work.Spaces.Iθ :=
    ContinuousOn.integrableOn_compact isCompact_Icc
      ((hψ.cont.pow 2).mul Real.continuous_cos.continuousOn)
  have hres := hResidual ψ hmeasψ hzψ
  have hconvS : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.range (N + 1),
          mcoeff ψ m * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
        Filter.atTop (nhds (seriesSum ψ θ)) := by
    intro θ hθ
    simpa only [modeSum, seriesSum] using hconv θ hθ
  -- the partial sums are uniformly bounded by `M`
  have hpartialM : ∀ (N : ℕ) (θ : ℝ), θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |∑ m ∈ Finset.range (N + 1), modeSum ψ m θ| ≤ M := by
    intro N θ hθ
    rw [hMdef]
    exact le_trans (hpartial N θ hθ) (le_max_left _ _)
  -- continuity of `S` on the open interval
  have hcontS : ContinuousOn (seriesSum ψ) (Set.Ioo 0 (Real.pi / 2)) :=
    hContTsum (mcoeff ψ) (modeMajor ψ C) hu (fun m θ hθ => hbu m θ hθ)
  -- the `L²`-limit and the pointwise limit agree a.e.
  have hae : seriesSum ψ =ᵐ[MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2))] ψ :=
    ae_eq_of_residual (mcoeff ψ) ψ (seriesSum ψ) M hMnonneg hψbound hpartialM hcontS
      hmeasψ hconvS hres
  have hcontψ : ContinuousOn ψ (Set.Ioo 0 (Real.pi / 2)) :=
    hψ.cont.mono Ioo_subset_Icc_self
  have heq : Set.EqOn (seriesSum ψ) ψ (Set.Ioo 0 (Real.pi / 2)) :=
    MeasureTheory.Measure.eqOn_Ioo_of_ae_eq volume hae hcontS hcontψ
  intro θ h0 h1
  exact heq ⟨h0, h1⟩

/-- **The `eFam`-expansion of the angular model `ψ`.** -/
theorem psiExpansion (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5)
    (hψ : Work.FTS.PhiStar.AngModel α ψ)
    (hdecay : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.cmode m (fun _ θ => ψ θ) 0|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hbound : ∀ m : ℕ, ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ Real.sqrt ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3))) :
    ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      (∑' m : ℕ, Work.FTS.PhiStar.Series.cmode m (fun _ θ' => ψ θ') 0
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ :=
  psiExpansion_aux α ψ hα hα5 hψ hdecay hbound
    (fun m hm => modeRatioLe m hm)
    (fun K A => summableModeMajorant K A)
    (fun b u hu h => continuousOnTsumEFam b u hu h)
    (fun ψ' h1 h2 => residualTendstoZero ψ' h1 h2)

end Work.FTS.PhiStar.Series.Deleg
