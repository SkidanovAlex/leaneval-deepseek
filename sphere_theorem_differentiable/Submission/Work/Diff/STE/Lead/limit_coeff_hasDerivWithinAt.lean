import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Pointwise
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.B3.fourierCoeff_periodization
import Submission.Work.Diff.STE.Lead.hasDerivWithinAt_of_sub_eq_integral
import Submission.Work.Diff.STE.Lead.hasDerivWithinAt_integral_Ico
import Submission.Work.Diff.STE.Lead.CoeffRepr
import Submission.Work.Diff.STE.Lead.fourierCoeff_le_sqrt_BNorm
import Submission.Work.Diff.STE.Lead.R_abs_le
import Submission.Work.Diff.STE.Lead.Rper_norm_le_of_R_abs_le
import Submission.Work.Diff.STE.Lead.tendsto_coeffFun_of_BNorm
import Submission.Work.Diff.STE.Lead.coeffFun_hasDerivWithinAt_ode
import Submission.Work.Diff.STE.Lead.tendsto_interval_integral_coeffFun

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

open MeasureTheory

/-- **A uniform bound on the Fourier coefficients of a pointwise bounded section.**  If `h` is
bounded pointwise by `K√g₀(u,u)√g₀(v,v)` then every coefficient of every periodised localised
component of `h` is bounded by `√Cdens · K`, where `Cdens` bounds the volume densities on the
`σ i`-balls.

Route: `|D.R i h a b w| ≤ √Cdens · K` (`Work.Diff.STE.Lead.R_abs_le`), hence
`‖D.Rper i h a b z‖ ≤ √Cdens · K` (`Work.Diff.STE.Lead.Rper_norm_le_of_R_abs_le`), and the
coefficient is the integral of `fourierExp (-μ) · Rper` over the volume-one unit cube. -/
lemma norm_fourierCoeff_Rper_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (K Cdens : ℝ) (hK : 0 ≤ K) (hCdens : 0 < Cdens)
    (hdens : ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ D.σ i → D.dens i z ≤ Cdens)
    (hbound : ∀ (y : M) (u' v' : TangentSpace I y),
      |h y u' v'| ≤ K * Real.sqrt (g₀.inner y u' u') * Real.sqrt (g₀.inner y v' v')) :
    ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      ‖Work.Diff.STE.fourierCoeff (D.Rper i h a b) μ‖ ≤ Real.sqrt Cdens * K := by
  intro i a b μ
  have hL : 0 ≤ Real.sqrt Cdens * K := mul_nonneg (Real.sqrt_nonneg _) hK
  have hR : ∀ w, |D.R i h a b w| ≤ Real.sqrt Cdens * K :=
    Work.Diff.STE.Lead.R_abs_le D h K Cdens hK hCdens hdens hbound i a b
  have hper : ∀ z, ‖D.Rper i h a b z‖ ≤ Real.sqrt Cdens * K :=
    Work.Diff.STE.Lead.Rper_norm_le_of_R_abs_le D h i a b hL hR
  rw [Work.Diff.STE.fourierCoeff]
  refine le_trans (MeasureTheory.norm_integral_le_lintegral_norm
    (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.fourierExp (-μ) z * D.Rper i h a b z)) ?_
  have hmono : (∫⁻ z, ENNReal.ofReal
        ‖Work.Diff.STE.fourierExp (-μ) z * D.Rper i h a b z‖
        ∂(volume.restrict (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)))))
      ≤ ∫⁻ _z, ENNReal.ofReal (Real.sqrt Cdens * K)
        ∂(volume.restrict (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)))) := by
    refine lintegral_mono fun z => ?_
    rw [ENNReal.ofReal_le_ofReal_iff hL, norm_mul, Work.Diff.STE.tpd_norm_fourierExp, one_mul]
    exact hper z
  have hconst : (∫⁻ _z, ENNReal.ofReal (Real.sqrt Cdens * K)
      ∂(volume.restrict (Work.Diff.STE.unitCube (ι := Fin (Module.finrank ℝ E)))))
      = ENNReal.ofReal (Real.sqrt Cdens * K) := by
    rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Work.Diff.STE.volume_unitCube, mul_one]
  rw [hconst] at hmono
  exact le_trans (ENNReal.toReal_mono ENNReal.ofReal_ne_top hmono)
    (le_of_eq (ENNReal.toReal_ofReal hL))

/-- **The coefficient functions of the limit solve the limit equation (coefficient form).**

`u m` is a sequence of curves of sections whose every matrix coefficient has (within `Icc 0 τ₀`)
derivative `vs m`, with a uniform *pointwise* bound on `vs m`; `u (φ m)` converges to `U` in every
composite norm `BNorm k` on `Ico 0 τ₀`; the Fourier coefficients of `vs (φ m)` converge to those of
`W`; and `σ ↦ ĉ_μ(W σ)` is continuous.  Then `ĉ_μ(U ·)` is differentiable on `Ico 0 τ₀` with
derivative `ĉ_μ(W ·)`.

Route: for each `m`, differentiate `ĉ_μ(u m ·)` under the cube integral (dominated convergence, with
the *pointwise* bound `hvsb` on the derivative, which is available precisely because we are not on
the false `coeffBound` route of `NOTE_coeffFun_lipschitz_FALSE.md`), identify the derivative with
`ĉ_μ(vs m ·)` via `fourierCoeff_periodization`, apply Newton–Leibniz on `Ico 0 τ₀`
(`intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le`, using `hvsmeas` for the interval
integrability of the derivative), let `m → ∞` (dominated convergence in `σ`, using `hcv` and the
uniform bound `hvsb`), and finish with a `HasDerivWithinAt`-version of
`hasDerivWithinAt_of_sub_eq_integral` (or `intervalIntegral.integral_hasDerivWithinAt_right`) using
`hcontW`. -/
theorem limit_coeff_hasDerivWithinAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (τ₀ : ℝ) (hτ₀ : 0 < τ₀) (φ : ℕ → ℕ)
    (u vs : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (U W : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : ∀ (m : ℕ) (t : ℝ), Work.Diff.STE.D.ChartData (I := I) (M := M) (u m t))
    (hsmU : ∀ t : ℝ, Work.Diff.STE.D.ChartData (I := I) (M := M) (U t))
    (hode : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ (x : M) (u₀ v : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => u m s x u₀ v) (vs m t x u₀ v) (Set.Icc (0 : ℝ) τ₀) t)
    (hvsb : ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ₀ →
      ∀ (x : M) (u₀ v : TangentSpace I x),
      |vs m t x u₀ v| ≤ C * Real.sqrt (g₀.inner x u₀ u₀) * Real.sqrt (g₀.inner x v v))
    (hvsmeas : ∀ (m : ℕ) (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ),
      AEMeasurable (fun σ : ℝ => Work.Diff.STE.fourierCoeff (D.Rper i (vs m σ) a b) μ)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) τ₀)))
    (hconv : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) τ₀ → ∀ k : ℕ,
      Filter.Tendsto (fun m : ℕ => D.BNorm k (u (φ m) t - U t)) Filter.atTop (nhds 0))
    (hcv : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) τ₀ → ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ),
      Filter.Tendsto (fun m : ℕ => Work.Diff.STE.fourierCoeff (D.Rper i (vs (φ m) t) a b) μ)
        Filter.atTop (nhds (Work.Diff.STE.fourierCoeff (D.Rper i (W t) a b) μ)))
    (hcontW : ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) τ₀ → ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ),
      ContinuousWithinAt (fun σ : ℝ => Work.Diff.STE.fourierCoeff (D.Rper i (W σ) a b) μ)
        (Set.Ico (0 : ℝ) τ₀) t) :
    ∀ t : ℝ, t ∈ Set.Ico (0 : ℝ) τ₀ → ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ),
      HasDerivWithinAt (fun s : ℝ => Work.Diff.STE.fourierCoeff (D.Rper i (U s) a b) μ)
        (Work.Diff.STE.fourierCoeff (D.Rper i (W t) a b) μ) (Set.Ico (0 : ℝ) τ₀) t := by
  obtain ⟨C, hC0, hvsbC⟩ := hvsb
  obtain ⟨c₀, Cdens, hc₀, hCdens, hdens⟩ := Work.Diff.STE.B3.dens_bound_sigma D
  intro t ht i a b μ
  set κ : ℝ := Real.sqrt Cdens * C with hκ
  have hκ0 : 0 ≤ κ := mul_nonneg (Real.sqrt_nonneg _) hC0
  -- (1) the pointwise `s`-derivative of `s ↦ ĉ_μ(u m s)`
  have hderivPerM : ∀ (m : ℕ) (x : ℝ), x ∈ Set.Ico (0 : ℝ) τ₀ →
      HasDerivWithinAt (fun r : ℝ => Work.Diff.STE.fourierCoeff (D.Rper i (u m r) a b) μ)
        (Work.Diff.STE.fourierCoeff (D.Rper i (vs m x) a b) μ) (Set.Icc (0 : ℝ) τ₀) x := by
    intro m x hx
    exact coeffFun_hasDerivWithinAt_ode D τ₀ hτ₀ C hC0 u vs hsm hode
      hvsbC m x hx i a b μ
  -- (2) the uniform bound on the coefficients of the velocities
  have hbnd : ∀ (m : ℕ) (σ : ℝ), σ ∈ Set.Icc (0 : ℝ) τ₀ →
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (vs m σ) a b) μ‖ ≤ κ := by
    intro m σ hσ
    exact norm_fourierCoeff_Rper_le D (vs m σ) C Cdens hC0 hCdens
      (fun i' z hz => (hdens i' z hz).2)
      (fun y u' v' => hvsbC m σ hσ y u' v') i a b μ
  -- (3) interval integrability of `σ ↦ ĉ_μ(vs m σ)` on `[0,τ₀]`
  have hvolIcc : (volume : Measure ℝ) (Set.Icc (0 : ℝ) τ₀) < ⊤ := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have hIntOn : ∀ (m : ℕ), MeasureTheory.IntegrableOn
      (fun σ : ℝ => Work.Diff.STE.fourierCoeff (D.Rper i (vs m σ) a b) μ)
      (Set.Icc (0 : ℝ) τ₀) volume := by
    intro m
    refine MeasureTheory.IntegrableOn.of_bound hvolIcc
      (hvsmeas m i a b μ).aestronglyMeasurable κ ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun σ hσ => hbnd m σ hσ
  -- (4) Newton–Leibniz for each `m`
  have hNLm : ∀ (m : ℕ) (s : ℝ), s ∈ Set.Ico (0 : ℝ) τ₀ →
      Work.Diff.STE.fourierCoeff (D.Rper i (u m s) a b) μ
        - Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ
      = ∫ σ in t..s, Work.Diff.STE.fourierCoeff (D.Rper i (vs m σ) a b) μ := by
    intro m s hs
    have hsI : s ∈ Set.Icc (0 : ℝ) τ₀ := ⟨hs.1, hs.2.le⟩
    have htI : t ∈ Set.Icc (0 : ℝ) τ₀ := ⟨ht.1, ht.2.le⟩
    have hsub : Set.uIcc t s ⊆ Set.Icc (0 : ℝ) τ₀ := Set.uIcc_subset_Icc htI hsI
    have hcont : ContinuousOn
        (fun r : ℝ => Work.Diff.STE.fourierCoeff (D.Rper i (u m r) a b) μ)
        (Set.uIcc t s) := by
      intro x hx
      have hxIco : x ∈ Set.Ico (0 : ℝ) τ₀ := by
        rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨le_trans (le_min ht.1 hs.1) (le_trans (min_le_left t s) h1),
            lt_of_le_of_lt h2 hs.2⟩
        · exact ⟨le_trans (le_min ht.1 hs.1) (le_trans (min_le_right t s) h1),
            lt_of_le_of_lt h2 ht.2⟩
      exact ((hderivPerM m x hxIco).continuousWithinAt).mono hsub
    have hderiv : ∀ x ∈ Set.Ioo (min t s) (max t s),
        HasDerivWithinAt (fun r : ℝ => Work.Diff.STE.fourierCoeff (D.Rper i (u m r) a b) μ)
          (Work.Diff.STE.fourierCoeff (D.Rper i (vs m x) a b) μ) (Set.Ioi x) x := by
      intro x hx
      have hx0 : 0 < x := lt_of_le_of_lt (le_min ht.1 hs.1) hx.1
      have hxτ : x < τ₀ := lt_trans hx.2 (max_lt ht.2 hs.2)
      have hxIco : x ∈ Set.Ico (0 : ℝ) τ₀ := ⟨le_of_lt hx0, hxτ⟩
      exact ((hderivPerM m x hxIco).hasDerivAt (Icc_mem_nhds hx0 hxτ)).hasDerivWithinAt
    have hint : IntervalIntegrable
        (fun σ : ℝ => Work.Diff.STE.fourierCoeff (D.Rper i (vs m σ) a b) μ) volume t s :=
      ((hIntOn m).mono_set hsub).intervalIntegrable
    exact (intervalIntegral.integral_eq_sub_of_hasDeriv_right hcont hderiv hint).symm
  -- (5) the coefficients of the limit velocities are bounded by `κ`
  have hWbnd : ∀ σ : ℝ, σ ∈ Set.Ico (0 : ℝ) τ₀ →
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (W σ) a b) μ‖ ≤ κ := by
    intro σ hσ
    refine le_of_tendsto' ((continuous_norm.tendsto _).comp (hcv σ hσ i a b μ)) fun m => ?_
    exact hbnd (φ m) σ ⟨hσ.1, hσ.2.le⟩
  -- (6) interval integrability of `σ ↦ ĉ_μ(W σ)` between points of `Ico 0 τ₀`
  have hGint : ∀ {p q : ℝ}, p ∈ Set.Ico (0 : ℝ) τ₀ → q ∈ Set.Ico (0 : ℝ) τ₀ →
      IntervalIntegrable
        (fun σ : ℝ => Work.Diff.STE.fourierCoeff (D.Rper i (W σ) a b) μ) volume p q := by
    intro p q hp hq
    have hpI : p ∈ Set.Icc (0 : ℝ) τ₀ := ⟨hp.1, hp.2.le⟩
    have hqI : q ∈ Set.Icc (0 : ℝ) τ₀ := ⟨hq.1, hq.2.le⟩
    have hsub : Set.uIcc p q ⊆ Set.Ico (0 : ℝ) τ₀ := by
      intro x hx
      rcases Set.mem_uIcc.mp hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨le_trans (le_min hp.1 hq.1) (le_trans (min_le_left p q) h1),
          lt_of_le_of_lt h2 hq.2⟩
      · exact ⟨le_trans (le_min hp.1 hq.1) (le_trans (min_le_right p q) h1),
          lt_of_le_of_lt h2 hp.2⟩
    have hfin : (volume : Measure ℝ) (Set.uIcc p q) < ⊤ :=
      lt_of_le_of_lt (measure_mono (Set.uIcc_subset_Icc hpI hqI)) hvolIcc
    have hcontQQ : ContinuousOn
        (fun σ : ℝ => Work.Diff.STE.fourierCoeff (D.Rper i (W σ) a b) μ) (Set.uIcc p q) :=
      fun x hx => (hcontW x (hsub hx) i a b μ).mono hsub
    have hae : AEStronglyMeasurable
        (fun σ : ℝ => Work.Diff.STE.fourierCoeff (D.Rper i (W σ) a b) μ)
        (volume.restrict (Set.uIcc p q)) :=
      hcontQQ.aestronglyMeasurable measurableSet_uIcc
    refine (MeasureTheory.IntegrableOn.of_bound hfin hae κ ?_).intervalIntegrable
    rw [MeasureTheory.ae_restrict_iff' measurableSet_uIcc]
    exact Filter.Eventually.of_forall fun σ hσ => hWbnd σ (hsub hσ)
  -- (7) coefficient convergence along `φ`
  have hconvCoef : ∀ (r : ℝ), r ∈ Set.Ico (0 : ℝ) τ₀ →
      Filter.Tendsto (fun m : ℕ => Work.Diff.STE.fourierCoeff (D.Rper i (u (φ m) r) a b) μ)
        Filter.atTop (nhds (Work.Diff.STE.fourierCoeff (D.Rper i (U r) a b) μ)) := by
    intro r hr
    exact Work.Diff.STE.Lead.tendsto_coeffFun_of_BNorm D τ₀ (fun m => u (φ m)) U
      (fun m r' => hsm (φ m) r') hsmU hconv r hr i a b μ
  -- (8) the limit of the σ-integrals
  have hlimInt : ∀ (r : ℝ), r ∈ Set.Ico (0 : ℝ) τ₀ →
      Filter.Tendsto (fun m : ℕ => ∫ σ in t..r,
          Work.Diff.STE.fourierCoeff (D.Rper i (vs (φ m) σ) a b) μ)
        Filter.atTop
        (nhds (∫ σ in t..r, Work.Diff.STE.fourierCoeff (D.Rper i (W σ) a b) μ)) := by
    intro r hr
    exact Work.Diff.STE.Lead.tendsto_interval_integral_coeffFun D τ₀ hτ₀ φ vs W i a b μ κ hκ0
      (fun m => hvsmeas m i a b μ) (fun m σ hσ => hbnd m σ hσ)
      (fun σ hσ => hcv σ hσ i a b μ) r t hr ht
  -- (9) the identity `F r - F t = ∫_t^r G` for the limit
  have hlim : ∀ (s : ℝ), s ∈ Set.Ico (0 : ℝ) τ₀ →
      Work.Diff.STE.fourierCoeff (D.Rper i (U s) a b) μ
        - Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ
      = ∫ σ in t..s, Work.Diff.STE.fourierCoeff (D.Rper i (W σ) a b) μ := by
    intro s hs
    refine tendsto_nhds_unique (Filter.Tendsto.congr' (Filter.Eventually.of_forall fun m => ?_)
      ((hconvCoef s hs).sub (hconvCoef t ht))) (hlimInt s hs)
    exact hNLm (φ m) s hs
  -- (10) the final assembly: `F` agrees with the primitive of `G` on `Ico 0 τ₀`
  have hGcont : ContinuousOn (fun σ : ℝ => Work.Diff.STE.fourierCoeff (D.Rper i (W σ) a b) μ)
      (Set.Ico (0 : ℝ) τ₀) := fun σ hσ => hcontW σ hσ i a b μ
  have hA : HasDerivWithinAt
      (fun r : ℝ => ∫ σ in (0 : ℝ)..r, Work.Diff.STE.fourierCoeff (D.Rper i (W σ) a b) μ)
      (Work.Diff.STE.fourierCoeff (D.Rper i (W t) a b) μ)
      (Set.Ico (0 : ℝ) τ₀) t :=
    hasDerivWithinAt_integral_Ico hτ₀ hGcont ht
  have h0Ico : (0 : ℝ) ∈ Set.Ico (0 : ℝ) τ₀ := ⟨le_refl 0, hτ₀⟩
  have hmain : HasDerivWithinAt
      (fun r : ℝ => (∫ σ in (0 : ℝ)..r, Work.Diff.STE.fourierCoeff (D.Rper i (W σ) a b) μ)
        + Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ
        - (∫ σ in (0 : ℝ)..t, Work.Diff.STE.fourierCoeff (D.Rper i (W σ) a b) μ))
      (Work.Diff.STE.fourierCoeff (D.Rper i (W t) a b) μ) (Set.Ico (0 : ℝ) τ₀) t :=
    (hA.add_const _).sub_const _
  refine hmain.congr (fun r hr => ?_) ?_
  · have h1 : Work.Diff.STE.fourierCoeff (D.Rper i (U r) a b) μ
        = Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ
          + ∫ σ in t..r, Work.Diff.STE.fourierCoeff (D.Rper i (W σ) a b) μ := by
      rw [← hlim r hr]
      ring
    have h2 : ∫ σ in t..r, Work.Diff.STE.fourierCoeff (D.Rper i (W σ) a b) μ
        = (∫ σ in (0 : ℝ)..r, Work.Diff.STE.fourierCoeff (D.Rper i (W σ) a b) μ)
          - (∫ σ in (0 : ℝ)..t, Work.Diff.STE.fourierCoeff (D.Rper i (W σ) a b) μ) := by
      rw [← intervalIntegral.integral_add_adjacent_intervals (hGint h0Ico ht) (hGint ht hr)]
      ring
    rw [h1, h2]
    ring
  · ring

end Work.Diff.STE.Lead
