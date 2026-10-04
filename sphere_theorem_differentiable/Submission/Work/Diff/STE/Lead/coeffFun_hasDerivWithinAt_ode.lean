import Mathlib
import Submission.Work.Diff.STE.Lead.CoeffRepr

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Differentiating the Fourier coefficient functional along the ODE family

This file proves `Work.Diff.STE.Lead.coeffFun_hasDerivWithinAt_ode`: the Fourier coefficient

  `s ↦ ĉ_μ(s) = fourierCoeff (D.Rper i (u m s) a b) μ = ∫_{cube} e_{-μ}(z) · Rper i (u m s) a b z dz`

of a localised periodised component of a family `s ↦ u m s` of sections is differentiable in `s`
with derivative `ĉ_μ` of the *pointwise* `s`-derivative `vs m t`, provided

* the pointwise derivative exists (`hode`) with the value `vs m t` at every `t ∈ [0,τ₀]`,
* `vs` is *uniformly bounded* in the natural `g₀`-norm sense (`hvsb`), and
* each slice `u m s` is chart-smooth (`hsm`).

The two ingredients are:

* `hasDerivWithinAt_integral_of_dominated_Icc` — differentiation under the integral sign over `Icc`,
  from a dominated-difference-quotient bound and a.e. pointwise one-sided differentiability
  (dominated convergence for the difference quotients);
* `Rper_derivWithin_aux` — the *pointwise* (in the flat variable `z`) version of the assertion: on
  the unit cube the periodisation collapses to the finite sum over `{0,-1}ⁿ`
  (`Work.Diff.STE.Lead.Rper_eq_finset_sum_of_mem_unitCube`), and each summand is
  `(ψ_i √dens_i)(z+m) • (u m ·)(pt i (z+m)) (e i a) (e i b)`, i.e. a constant times the pointwise
  derivative supplied by `hode`.

The dominance comes from the already proved
`Work.Diff.STE.Lead.Rper_norm_sub_le` (Lipschitz bound for `Rper`, with constant
`2^n √Cdens K`, from `hode` + `hvsb` and the uniform density bound
`Work.Diff.STE.B3.dens_bound_sigma`).
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace Work.Diff.STE.Lead

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## Differentiation under the integral sign on `Icc` -/

/-- **Differentiation under the integral sign, dominated convergence form.**  If `s ↦ G s` is a
family of integrable `ℂ`-valued functions for which the difference quotients relative to `G t` are
dominated by the integrable `g`, and the functions `s ↦ G s x` are one-sidedly differentiable at
`t` for a.e. `x`, then `s ↦ ∫ x, G s x ∂μ` is one-sidedly differentiable at `t` with derivative
`∫ x, G' x ∂μ`. -/
theorem hasDerivWithinAt_integral_of_dominated_Icc {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {G : ℝ → X → ℂ} {G' : X → ℂ} {g : X → ℝ} {τ t : ℝ}
    (hg : Integrable g μ) (hGint : Integrable (G t) μ)
    (hmeas : ∀ s ∈ Set.Icc (0 : ℝ) τ, AEStronglyMeasurable (G s) μ)
    (hdiff : ∀ s ∈ Set.Icc (0 : ℝ) τ, ∀ᵐ x ∂μ, ‖G s x - G t x‖ ≤ |s - t| * g x)
    (hder : ∀ᵐ x ∂μ, HasDerivWithinAt (fun s : ℝ => G s x) (G' x) (Set.Icc (0 : ℝ) τ) t) :
    HasDerivWithinAt (fun s : ℝ => ∫ x, G s x ∂μ) (∫ x, G' x ∂μ) (Set.Icc (0 : ℝ) τ) t := by
  have hmem : (Set.Icc (0 : ℝ) τ \ {t}) ∈ 𝓝[Set.Icc (0 : ℝ) τ \ {t}] t := self_mem_nhdsWithin
  -- `G s` is integrable for every `s ∈ Icc 0 τ`, being `G t` plus a difference dominated by `g`.
  have hGs : ∀ s ∈ Set.Icc (0 : ℝ) τ, Integrable (G s) μ := by
    intro s hs
    have h1 : Integrable (fun x => G s x - G t x) μ :=
      Integrable.mono' (hg.const_mul |s - t|)
        ((hmeas s hs).sub hGint.aestronglyMeasurable) (hdiff s hs)
    have h2 : Integrable (fun x => G t x + (G s x - G t x)) μ := hGint.add h1
    simpa using h2
  -- Dominated convergence for the difference quotients on the punctured interval.
  have hDCT : Tendsto (fun s : ℝ => ∫ x, (s - t)⁻¹ • (G s x - G t x) ∂μ)
      (𝓝[(Set.Icc (0 : ℝ) τ) \ {t}] t) (𝓝 (∫ x, G' x ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (bound := g)
      (F := fun s x => (s - t)⁻¹ • (G s x - G t x)) (f := fun x => G' x) ?_ ?_ hg ?_
    · refine Filter.eventually_of_mem hmem fun s hs => ?_
      exact ((hmeas s hs.1).sub hGint.aestronglyMeasurable).const_smul (𝕜 := ℝ) ((s - t)⁻¹)
    · refine Filter.eventually_of_mem hmem fun s hs => (hdiff s hs.1).mono fun x hx => ?_
      have hst : |s - t| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hs.2)
      rw [norm_smul, Real.norm_eq_abs, abs_inv]
      calc |s - t|⁻¹ * ‖G s x - G t x‖ ≤ |s - t|⁻¹ * (|s - t| * g x) :=
            mul_le_mul_of_nonneg_left hx (inv_nonneg.mpr (abs_nonneg _))
        _ = g x := by rw [← mul_assoc, inv_mul_cancel₀ hst, one_mul]
    · filter_upwards [hder] with x hx
      exact hasDerivWithinAt_iff_tendsto_slope.mp hx
  -- On the punctured interval the difference quotient of the integral is the integral of the
  -- difference quotient.
  have hEq : (fun s : ℝ => ∫ x, (s - t)⁻¹ • (G s x - G t x) ∂μ)
      =ᶠ[𝓝[(Set.Icc (0 : ℝ) τ) \ {t}] t] slope (fun s : ℝ => ∫ x, G s x ∂μ) t := by
    refine Filter.eventually_of_mem hmem fun s hs => ?_
    simp only [slope, vsub_eq_sub]
    rw [← integral_sub (hGs s hs.1) hGint,
      ← integral_smul (μ := μ) (c := (s - t)⁻¹) (f := fun x => G s x - G t x)]
  have hTendsto := hDCT.congr' hEq
  rw [hasDerivWithinAt_iff_tendsto_slope]
  exact hTendsto

/-! ## The pointwise (in the flat variable) derivative of the periodisation -/

/-- **Pointwise derivative of the periodised localised component.**  For a fixed point `x` of the
unit cube the periodisation `D.Rper i (·) a b x` is, on the cube, the finite sum over `{0,-1}ⁿ` of
the localised components; each summand is a constant (in `s`) times the matrix coefficient
`s ↦ u m s (pt i w) (e i a) (e i b)`, whose derivative is given by `hode`. -/
theorem Rper_derivWithin_aux
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (τ₀ : ℝ) (u vs : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hode : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ (x : M) (u₀ v : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => u m s x u₀ v) (vs m t x u₀ v) (Set.Icc (0 : ℝ) τ₀) t)
    (m : ℕ) (t : ℝ) (htI : t ∈ Set.Icc (0 : ℝ) τ₀) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) (x : Fin (Module.finrank ℝ E) → ℝ)
    (hx : x ∈ Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E))) :
    HasDerivWithinAt (fun s : ℝ => D.Rper i (u m s) a b x) (D.Rper i (vs m t) a b x)
      (Set.Icc (0 : ℝ) τ₀) t := by
  have hval : D.Rper i (vs m t) a b x
      = ∑ m' ∈ cubeIdx E,
          ((D.R i (vs m t) a b (x + Work.Diff.STE.iVec m') : ℝ) : ℂ) :=
    Rper_eq_finset_sum_of_mem_unitCube D (vs m t) i a b x hx
  have hsum : HasDerivWithinAt
      (∑ m' ∈ cubeIdx E,
        fun s : ℝ => ((D.R i (u m s) a b (x + Work.Diff.STE.iVec m') : ℝ) : ℂ))
      (∑ m' ∈ cubeIdx E,
        ((D.R i (vs m t) a b (x + Work.Diff.STE.iVec m') : ℝ) : ℂ))
      (Set.Icc (0 : ℝ) τ₀) t := by
    refine HasDerivWithinAt.sum (u := cubeIdx E)
      (A := fun m' (s : ℝ) => ((D.R i (u m s) a b (x + Work.Diff.STE.iVec m') : ℝ) : ℂ))
      (A' := fun m' => ((D.R i (vs m t) a b (x + Work.Diff.STE.iVec m') : ℝ) : ℂ)) ?_
    intro m' hm'
    set w : Fin (Module.finrank ℝ E) → ℝ := x + Work.Diff.STE.iVec m' with hw
    have hbase : HasDerivWithinAt
        (fun s : ℝ => ((u m s (D.pt i w) (D.e i a (D.pt i w)) (D.e i b (D.pt i w)) : ℝ) : ℂ))
        ((vs m t (D.pt i w) (D.e i a (D.pt i w)) (D.e i b (D.pt i w)) : ℝ) : ℂ)
        (Set.Icc (0 : ℝ) τ₀) t :=
      (hode m t htI (D.pt i w) (D.e i a (D.pt i w)) (D.e i b (D.pt i w))).ofReal_comp
    have hfun : (fun s : ℝ => ((D.R i (u m s) a b w : ℝ) : ℂ))
        = fun s : ℝ => ((D.psi i w * Real.sqrt (D.dens i w) : ℝ) : ℂ)
            * ((u m s (D.pt i w) (D.e i a (D.pt i w)) (D.e i b (D.pt i w)) : ℝ) : ℂ) := by
      funext s
      simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat]
      push_cast
      ring
    have hval2 : ((D.R i (vs m t) a b w : ℝ) : ℂ)
        = ((D.psi i w * Real.sqrt (D.dens i w) : ℝ) : ℂ)
            * ((vs m t (D.pt i w) (D.e i a (D.pt i w)) (D.e i b (D.pt i w)) : ℝ) : ℂ) := by
      simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat]
      push_cast
      ring
    rw [hfun, hval2]
    exact hbase.const_mul _
  have hfin : (∑ m' ∈ cubeIdx E,
        fun s : ℝ => ((D.R i (u m s) a b (x + Work.Diff.STE.iVec m') : ℝ) : ℂ))
      = fun s : ℝ => ∑ m' ∈ cubeIdx E,
          ((D.R i (u m s) a b (x + Work.Diff.STE.iVec m') : ℝ) : ℂ) := by
    funext s
    exact Finset.sum_apply s (cubeIdx E)
      (fun m' (s : ℝ) => ((D.R i (u m s) a b (x + Work.Diff.STE.iVec m') : ℝ) : ℂ))
  rw [hfin] at hsum
  have hEq_fun : (fun s : ℝ => D.Rper i (u m s) a b x)
      = fun s : ℝ => ∑ m' ∈ cubeIdx E,
          ((D.R i (u m s) a b (x + Work.Diff.STE.iVec m') : ℝ) : ℂ) :=
    funext fun s => Rper_eq_finset_sum_of_mem_unitCube D (u m s) i a b x hx
  rw [hval, hEq_fun]
  exact hsum

/-! ## The target -/

theorem coeffFun_hasDerivWithinAt_ode
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (τ₀ : ℝ) (hτ₀ : 0 < τ₀) (K : ℝ) (hK : 0 ≤ K)
    (u vs : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : ∀ (m : ℕ) (t : ℝ), Work.Diff.STE.D.ChartData (I := I) (M := M) (u m t))
    (hode : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ (x : M) (u₀ v : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => u m s x u₀ v) (vs m t x u₀ v) (Set.Icc (0 : ℝ) τ₀) t)
    (hvsb : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ (x : M) (u₀ v : TangentSpace I x),
      |vs m t x u₀ v| ≤ K * Real.sqrt (g₀.inner x u₀ u₀) * Real.sqrt (g₀.inner x v v)) :
    ∀ (m : ℕ) (t : ℝ), t ∈ Set.Ico (0 : ℝ) τ₀ → ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ),
      HasDerivWithinAt (fun s : ℝ => Work.Diff.STE.fourierCoeff (D.Rper i (u m s) a b) μ)
        (Work.Diff.STE.fourierCoeff (D.Rper i (vs m t) a b) μ) (Set.Icc (0 : ℝ) τ₀) t := by
  intro m t ht i a b μ
  -- The uniform two-sided bound on the volume density: `Work.Diff.STE.B3.dens_bound_sigma`.
  obtain ⟨_c, Cdens, _hcpos, _hCdens, hdens⟩ := Work.Diff.STE.B3.dens_bound_sigma D
  have htI : t ∈ Set.Icc (0 : ℝ) τ₀ := ⟨ht.1, le_of_lt ht.2⟩
  -- `hvsb` turns the pointwise ODE into the `∃R` form consumed by `Rper_norm_sub_le`.
  have hode' : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ (x : M) (u₀ v : TangentSpace I x),
      ∃ R : ℝ, HasDerivWithinAt (fun s : ℝ => u m s x u₀ v) R (Set.Icc (0 : ℝ) τ₀) t ∧
        |R| ≤ K * Real.sqrt (g₀.inner x u₀ u₀) * Real.sqrt (g₀.inner x v v) :=
    fun m t ht x u₀ v => ⟨vs m t x u₀ v, hode m t ht x u₀ v, hvsb m t ht x u₀ v⟩
  have hcube : MeasurableSet (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E))) := by
    rw [Work.Diff.STE.unitCube]
    exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioc)
  have hfinite : IsFiniteMeasure
      (volume.restrict (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)))) := by
    constructor
    rw [MeasureTheory.Measure.restrict_apply_univ, Work.Diff.STE.volume_unitCube]
    exact ENNReal.one_lt_top
  -- Continuity of the periodised components (chart smoothness of every slice).
  have hcont : ∀ s : ℝ, Continuous (D.Rper i (u m s) a b) := fun s =>
    ((Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i (u m s) a b
      (Work.Diff.STE.B3.R_contDiff_of_chartData D (u m s) (hsm m s) i a b)).1).continuous
  have hgc : Continuous (Work.Diff.STE.fourierExp (-μ)) := Work.Diff.STE.continuous_fourierExp (-μ)
  set Kc : ℝ := (2 : ℝ) ^ Module.finrank ℝ E * (Real.sqrt Cdens * K) with hKc
  set G : ℝ → (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
    fun s x => Work.Diff.STE.fourierExp (-μ) x * D.Rper i (u m s) a b x with hG
  set G' : (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
    fun x => Work.Diff.STE.fourierExp (-μ) x * D.Rper i (vs m t) a b x with hG'
  have hg : Integrable (fun _ : Fin (Module.finrank ℝ E) → ℝ => Kc)
      (volume.restrict (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)))) := by
    haveI := hfinite
    exact integrable_const Kc
  have hGint : Integrable (G t)
      (volume.restrict (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous (hgc.mul (hcont t))
  have hmeas : ∀ s ∈ Set.Icc (0 : ℝ) τ₀, AEStronglyMeasurable (G s)
      (volume.restrict (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)))) :=
    fun s _ => (hgc.mul (hcont s)).aestronglyMeasurable
  -- The domination: the Lipschitz bound `Rper_norm_sub_le` for the periodised components.
  have hdiff : ∀ s ∈ Set.Icc (0 : ℝ) τ₀,
      ∀ᵐ x ∂(volume.restrict (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)))),
        ‖G s x - G t x‖ ≤ |s - t| * Kc := by
    intro s hs
    rw [MeasureTheory.ae_restrict_iff' hcube]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have h1 : G s x - G t x = Work.Diff.STE.fourierExp (-μ) x
        * (D.Rper i (u m s) a b x - D.Rper i (u m t) a b x) := by
      simp only [hG]
      ring
    rw [h1, norm_mul, Work.Diff.STE.tpd_norm_fourierExp, one_mul, hKc]
    calc ‖D.Rper i (u m s) a b x - D.Rper i (u m t) a b x‖
        ≤ (2 : ℝ) ^ Module.finrank ℝ E * (Real.sqrt Cdens * K) * |s - t| :=
          Rper_norm_sub_le D K τ₀ hK u hode' Cdens (fun i z hz => (hdens i z hz).2)
            m hs htI i a b x hx
      _ = |s - t| * ((2 : ℝ) ^ Module.finrank ℝ E * (Real.sqrt Cdens * K)) := by ring
  -- The pointwise one-sided derivative of the integrand.
  have hder : ∀ᵐ x ∂(volume.restrict (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)))),
      HasDerivWithinAt (fun s : ℝ => G s x) (G' x) (Set.Icc (0 : ℝ) τ₀) t := by
    rw [MeasureTheory.ae_restrict_iff' hcube]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hbase := Rper_derivWithin_aux D τ₀ u vs hode m t htI i a b x hx
    have h2 := hbase.const_mul (Work.Diff.STE.fourierExp (-μ) x)
    simpa only [hG, hG'] using h2
  have hmain := hasDerivWithinAt_integral_of_dominated_Icc
    (volume.restrict (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E))))
    (G := G) (G' := G') (g := fun _ => Kc) (τ := τ₀) (t := t) hg hGint hmeas hdiff hder
  simp only [Work.Diff.STE.fourierCoeff, hG, hG'] at hmain ⊢
  exact hmain

end Work.Diff.STE.Lead
