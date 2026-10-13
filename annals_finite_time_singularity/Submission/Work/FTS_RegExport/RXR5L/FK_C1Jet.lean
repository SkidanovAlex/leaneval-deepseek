/-
# `Work.FTS_RegExport.RXR5L.FK_C1Jet` — the `𝔽K`-slot of the R5 class data

The `R5`-assembly `Work.FTS.RegPkgGal.Der.R5Parts_of_pieces_F` consumes, besides the elliptic
slots, the class-1 jet of the **angular moment**

  `𝔽K(F_τ)(z) = ∫_{Iθ} K(θ)·F_τ(z,θ) dθ`,   `K(θ) = 3 sinθ cos²θ`   (`Construction.FK`),

of the fake-time profile `F_τ = Ftau (pExp α) (gS α (tauExt g)) τ = F_* + g̃(τ)`.  This file
supplies that slot from the two hypotheses of the R5 producer, namely the dynamic package
`DynOK'` and the class data `St1Class` of the sanitised family `SG α g = gS α (tauExt g)`:

* the *value/`Jet` half* (`Ftau_C1Jet'`, from `C1JetFstar` for `F_*` and `RXR5L.SG_C1Jet` for the
  perturbation) is `C1Jet`-regular on the horizon, and
* the angular moment of a `C1Jet` family is again `C1Jet` (`c1jet_Kavg` below),

whence `∃ N₁₄ ≥ 0, C1Jet α S N₁₄ (fun z θ τ => 𝔽K(F_τ)(z))`.

## The moment of a `C1Jet` family

`c1jet_Kavg` is the only real work.  Let `h` be a `C1Jet α S N` family (a uniform bound `N` on the
box, a joint `α`-modulus for the metric `|Δz|+|Δθ|+|Δτ|`, and, at every `z > 0`, a genuine
`z`-derivative of every angular slice, bounded by `N`), and

  `G z τ = ∫_{Iθ} h z σ τ K σ dσ`.

* **Bound and modulus.**  `|G| ≤ 3N(π/2)` and
  `|G z τ - G z' τ'| ≤ 3N(π/2)(|z-z'|+|τ-τ'|)^α` — the joint modulus of `h` evaluated at the
  two *equal* angles `σ = σ` — both by
  `norm_integral_le_integral_norm` + `setIntegral_abs_le_of_bound` (`|K| ≤ 3`, `|Iθ| = π/2`),
  with the *difference* of the two moments written as the moment of the difference
  (`integral_sub`, the integrands being bounded on a finite measure space).  The function is
  independent of `θ`, so the third modulus is free.
* **The `z`-derivative.**  The key point is that the pointwise `z`-derivative bound `|∂_z h| ≤ N`
  upgrades, by the mean value theorem, to the *Lipschitz* bound `|h z σ τ - h z' σ τ| ≤ N|z-z'|`
  on every angular slice — so the difference quotients are uniformly bounded by `3N`, and
  Lebesgue's dominated convergence (in its filter form, along the *punctured* filter `𝓝[≠] z`,
  along which the quotient is the slope) gives

    `HasDerivAt (fun z' => G z' τ) (∫_{Iθ} ∂_z h(z,σ,τ)·K σ dσ) z`.

  No measurability of `σ ↦ ∂_z h(z,σ,τ)` is ever needed: the limit is *identified* with the
  integral of the pointwise derivative, and *bounded* by `3N(π/2)` through
  `norm_integral_le_integral_norm` + `setIntegral_abs_le_of_bound` applied to the pointwise
  derivative bound `|∂_z h| ≤ N` — neither of which requires measurability.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Submission.Work.FTS_RegExport.RXR5.Basic
import Submission.Work.FTS_RegExport.RXR5L.SG_C1Jet
import Submission.Work.FTS_RegExport.RXR5.Fstar_C1Jet
import Submission.Work.FTS.RegPkgGal.Der.L12fBasic
import Submission.Work.FTS.RegPkgGal.Der.zderiv_N

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_RegExport.RXR5L

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 Elementary facts about the angular weight `K` and the interval `Iθ` -/

/-- The angular weight `K(θ) = 3 sinθ cos²θ` is continuous. -/
theorem continuous_K : Continuous Work.Spaces.K := by
  rw [show Work.Spaces.K = fun θ : ℝ => 3 * Real.sin θ * Real.cos θ ^ 2 from rfl]
  fun_prop

/-- `|K| ≤ 3` on `Iθ` (from `Der.L12fBasic`). -/
theorem abs_K_le_three' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : |Work.Spaces.K θ| ≤ 3 :=
  Work.FTS.RegPkgGal.Der.abs_K_le_three hθ

/-! ## §2 The angular moment of a `C1Jet` family -/

/-- **The Lipschitz bound in `z` of a `C1Jet`, slice by slice.**  A pointwise `z`-derivative
bounded by `N` upgrades to a Lipschitz bound by the mean value theorem (applied on `Ioi 0`, a
convex set on which the slice is differentiable with `|deriv| ≤ N`). -/
theorem c1jet_z_lipschitz {α S N : ℝ} {h : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.RegPkgGal.C1Jet α S N h) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S)
    {σ : ℝ} (hσ : σ ∈ Work.Spaces.Iθ) {z z' : ℝ} (hz : 0 < z) (hz' : 0 < z') :
    |h z' σ τ - h z σ τ| ≤ N * |z' - z| := by
  have hderiv : ∀ x ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ (fun y => h y σ τ) x := fun x hx =>
    (H.2 τ hτ σ hσ x hx).choose_spec.1.differentiableAt
  have hbd : ∀ x ∈ Set.Ioi (0 : ℝ), ‖deriv (fun y => h y σ τ) x‖ ≤ N := by
    intro x hx
    obtain ⟨d, hd, hdb⟩ := H.2 τ hτ σ hσ x hx
    rw [hd.deriv, Real.norm_eq_abs]
    exact hdb
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun y => h y σ τ)
    hderiv hbd (convex_Ioi (0 : ℝ)) hz hz'
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

/-- **Integrability of the moment integrand.**  A bounded, angularly continuous slice is
integrable against `K` on the finite interval `Iθ`. -/
theorem c1jet_integrable_Kmul {α S N : ℝ} (hα : 0 < α) {h : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.RegPkgGal.C1Jet α S N h) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S)
    {z : ℝ} (hz : 0 ≤ z) :
    MeasureTheory.Integrable (fun σ => h z σ τ * Work.Spaces.K σ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hN : 0 ≤ N := H.1.1
  have hcont : ContinuousOn (fun σ => h z σ τ) Work.Spaces.Iθ :=
    Work.FTS.RegPkgGal.Der.continuousOn_of_holder hN hα
      (fun σ hσ σ' hσ' => H.1.thmod hz hσ hσ' hτ)
  have hmeas : AEStronglyMeasurable (fun σ => h z σ τ * Work.Spaces.K σ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (hcont.mul continuous_K.continuousOn).aestronglyMeasurable_of_isCompact
      isCompact_Icc measurableSet_Icc
  refine MeasureTheory.Integrable.mono' (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (g := fun _ : ℝ => 3 * N) ?_ hmeas ?_
  · exact MeasureTheory.integrableOn_const (μ := MeasureTheory.volume)
      (s := Work.Spaces.Iθ) (C := 3 * N) (ne_of_lt Work.Spaces.volume_Iθ_lt_top)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with σ hσ
    rw [Real.norm_eq_abs, abs_mul]
    calc |h z σ τ| * |Work.Spaces.K σ| ≤ N * 3 :=
          mul_le_mul (H.1.abs_le hz hσ hτ) (abs_K_le_three' hσ) (abs_nonneg _) hN
      _ = 3 * N := by ring

/-- **The crude sup bound of the angular moment.** -/
theorem Kavg_abs_le {N z τ : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (hN : 0 ≤ N)
    (hb : ∀ σ ∈ Work.Spaces.Iθ, |h z σ τ| ≤ N) :
    |∫ σ in Work.Spaces.Iθ, h z σ τ * Work.Spaces.K σ| ≤ 3 * N * (π / 2) := by
  have hmn := Work.FTS.RegPkgGal.Der.setIntegral_abs_le_of_bound (c := 3 * N)
    (f := fun σ => h z σ τ * Work.Spaces.K σ) (fun σ hσ => by
      rw [abs_mul]
      calc |h z σ τ| * |Work.Spaces.K σ| ≤ N * 3 :=
            mul_le_mul (hb σ hσ) (abs_K_le_three' hσ) (abs_nonneg _) hN
        _ = 3 * N := by ring)
  have hnorm := MeasureTheory.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (fun σ => h z σ τ * Work.Spaces.K σ)
  rw [Real.norm_eq_abs] at hnorm
  exact le_trans hnorm hmn

/-- **The moment of the difference is the difference of the moments.** -/
theorem Kavg_sub {α S N : ℝ} (hα : 0 < α) {h : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.RegPkgGal.C1Jet α S N h) {τ τ' : ℝ} (hτ : τ ∈ Set.Icc 0 S)
    (hτ' : τ' ∈ Set.Icc 0 S) {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') :
    (∫ σ in Work.Spaces.Iθ, h z σ τ * Work.Spaces.K σ)
        - (∫ σ in Work.Spaces.Iθ, h z' σ τ' * Work.Spaces.K σ)
      = ∫ σ in Work.Spaces.Iθ, (h z σ τ - h z' σ τ') * Work.Spaces.K σ := by
  rw [← MeasureTheory.integral_sub (c1jet_integrable_Kmul hα H hτ hz) (c1jet_integrable_Kmul hα H hτ' hz')]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun σ _ => by ring)

/-- **The joint `(z,τ)`-modulus of the angular moment.** -/
theorem Kavg_modulus {α S N : ℝ} (hα : 0 < α) {h : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.RegPkgGal.C1Jet α S N h) {z z' τ τ' : ℝ}
    (hz : 0 ≤ z) (hz' : 0 ≤ z') (hτ : τ ∈ Set.Icc 0 S) (hτ' : τ' ∈ Set.Icc 0 S) :
    |(∫ σ in Work.Spaces.Iθ, h z σ τ * Work.Spaces.K σ)
        - (∫ σ in Work.Spaces.Iθ, h z' σ τ' * Work.Spaces.K σ)|
      ≤ 3 * N * (π / 2) * (|z - z'| + |τ - τ'|) ^ α := by
  have hN : 0 ≤ N := H.1.1
  rw [Kavg_sub hα H hτ hτ' hz hz']
  have hnorm := MeasureTheory.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (fun σ => (h z σ τ - h z' σ τ') * Work.Spaces.K σ)
  rw [Real.norm_eq_abs] at hnorm
  have hmn := Work.FTS.RegPkgGal.Der.setIntegral_abs_le_of_bound
    (f := fun σ => (h z σ τ - h z' σ τ') * Work.Spaces.K σ)
    (c := 3 * N * (|z - z'| + |τ - τ'|) ^ α) (fun σ hσ => by
      rw [abs_mul]
      have h1 := H.1.2.2 z z' σ σ τ τ' hz hz' hσ hσ hτ hτ'
      simp only [sub_self, abs_zero, add_zero] at h1
      calc |h z σ τ - h z' σ τ'| * |Work.Spaces.K σ|
          ≤ (N * (|z - z'| + |τ - τ'|) ^ α) * 3 :=
            mul_le_mul h1 (abs_K_le_three' hσ) (abs_nonneg _)
              (mul_nonneg hN (Real.rpow_nonneg (by positivity) α))
        _ = 3 * N * (|z - z'| + |τ - τ'|) ^ α := by ring)
  calc |∫ σ in Work.Spaces.Iθ, (h z σ τ - h z' σ τ') * Work.Spaces.K σ|
      ≤ ∫ σ in Work.Spaces.Iθ, ‖(h z σ τ - h z' σ τ') * Work.Spaces.K σ‖ := hnorm
    _ ≤ 3 * N * (|z - z'| + |τ - τ'|) ^ α * (π / 2) := hmn
    _ = 3 * N * (π / 2) * (|z - z'| + |τ - τ'|) ^ α := by ring

/-- **The `z`-derivative of the angular moment of a `C1Jet` family.**  Dominated convergence
along the punctured filter `𝓝[≠] z`, with the *uniform* (in the parameter) bound `3N` on the
difference quotients supplied by `c1jet_z_lipschitz`. -/
theorem Kavg_hasDerivAt {α S N : ℝ} (hα : 0 < α) {h : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.RegPkgGal.C1Jet α S N h) {τ : ℝ} (hτ : τ ∈ Set.Icc 0 S) {z : ℝ}
    (hz : 0 < z) :
    ∃ d : ℝ, HasDerivAt (fun z' => ∫ σ in Work.Spaces.Iθ, h z' σ τ * Work.Spaces.K σ) d z ∧
      |d| ≤ 3 * N * (π / 2) := by
  have hN : 0 ≤ N := H.1.1
  -- the candidate derivative
  set D : ℝ := ∫ σ in Work.Spaces.Iθ, deriv (fun y => h y σ τ) z * Work.Spaces.K σ with hD
  -- the uniform bound on the difference quotients
  have hquot : ∀ z' σ : ℝ, 0 < z' → z' ≠ z → σ ∈ Work.Spaces.Iθ →
      |(z' - z)⁻¹ * (h z' σ τ * Work.Spaces.K σ - h z σ τ * Work.Spaces.K σ)| ≤ 3 * N := by
    intro z' σ hz' hzne hσ
    have hlip := c1jet_z_lipschitz H hτ hσ hz hz'
    have hkey : h z' σ τ * Work.Spaces.K σ - h z σ τ * Work.Spaces.K σ
        = (h z' σ τ - h z σ τ) * Work.Spaces.K σ := by ring
    rw [hkey, abs_mul, abs_mul, abs_inv]
    calc |z' - z|⁻¹ * (|h z' σ τ - h z σ τ| * |Work.Spaces.K σ|)
        ≤ |z' - z|⁻¹ * ((N * |z' - z|) * 3) := by
          refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (abs_nonneg _))
          exact mul_le_mul hlip (abs_K_le_three' hσ) (abs_nonneg _) (by positivity)
      _ = 3 * N := by
          rw [show |z' - z|⁻¹ * ((N * |z' - z|) * 3) = (|z' - z|⁻¹ * |z' - z|) * (3 * N)
            from by ring, inv_mul_cancel₀ (abs_ne_zero.mpr (sub_ne_zero.mpr hzne)), one_mul]
  -- the dominated convergence step
  have hDCT : Tendsto (fun z' => ∫ σ in Work.Spaces.Iθ,
      (z' - z)⁻¹ * (h z' σ τ * Work.Spaces.K σ - h z σ τ * Work.Spaces.K σ))
      (𝓝[≠] z) (𝓝 D) := by
    have hmain := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ) (l := 𝓝[≠] z)
      (F := fun z' σ => (z' - z)⁻¹ * (h z' σ τ * Work.Spaces.K σ - h z σ τ * Work.Spaces.K σ))
      (f := fun σ => deriv (fun y => h y σ τ) z * Work.Spaces.K σ)
      (bound := fun _ : ℝ => 3 * N) ?_ ?_ ?_ ?_
    · rw [hD]
      exact hmain
    · -- a.e. strong measurability of the difference quotients
      filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds
        (by linarith : z / 2 < z) (by linarith : z < 2 * z))] with z' hz'
      have hz'0 : (0 : ℝ) < z' := lt_trans (by linarith : (0 : ℝ) < z / 2) hz'.1
      have hcont1 : ContinuousOn (fun σ => h z' σ τ) Work.Spaces.Iθ :=
        Work.FTS.RegPkgGal.Der.continuousOn_of_holder hN hα
          (fun σ hσ σ' hσ' => H.1.thmod hz'0.le hσ hσ' hτ)
      have hcont2 : ContinuousOn (fun σ => h z σ τ) Work.Spaces.Iθ :=
        Work.FTS.RegPkgGal.Der.continuousOn_of_holder hN hα
          (fun σ hσ σ' hσ' => H.1.thmod hz.le hσ hσ' hτ)
      have hcont : ContinuousOn (fun σ => h z' σ τ * Work.Spaces.K σ
          - h z σ τ * Work.Spaces.K σ) Work.Spaces.Iθ :=
        (hcont1.mul continuous_K.continuousOn).sub (hcont2.mul continuous_K.continuousOn)
      exact (hcont.const_mul ((z' - z)⁻¹)).aestronglyMeasurable_of_isCompact
        isCompact_Icc measurableSet_Icc
    · -- the uniform bound on the quotients
      filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds
        (by linarith : z / 2 < z) (by linarith : z < 2 * z)), self_mem_nhdsWithin] with z' hz' hzne
      have hz'0 : (0 : ℝ) < z' := lt_trans (by linarith : (0 : ℝ) < z / 2) hz'.1
      have hzne' : z' ≠ z := by simpa using hzne
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with σ hσ
      rw [Real.norm_eq_abs]
      exact hquot z' σ hz'0 hzne' hσ
    · -- the dominating function is integrable
      exact MeasureTheory.integrableOn_const (μ := MeasureTheory.volume)
        (s := Work.Spaces.Iθ) (C := 3 * N) (ne_of_lt Work.Spaces.volume_Iθ_lt_top)
    · -- pointwise convergence of the quotients to the pointwise derivative
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with σ hσ
      obtain ⟨d, hd, _hdb⟩ := H.2 τ hτ σ hσ z hz
      have h1 : Tendsto (slope (fun y => h y σ τ) z) (𝓝[≠] z) (𝓝 d) := hd.tendsto_slope
      have h2 : Tendsto (fun z' => slope (fun y => h y σ τ) z z' * Work.Spaces.K σ)
          (𝓝[≠] z) (𝓝 (d * Work.Spaces.K σ)) := h1.mul_const _
      have h3 : Tendsto (fun z' => (z' - z)⁻¹ * (h z' σ τ - h z σ τ) * Work.Spaces.K σ)
          (𝓝[≠] z) (𝓝 (d * Work.Spaces.K σ)) :=
        Filter.Tendsto.congr' (Filter.Eventually.of_forall
          (fun z' => by simp only [slope, vsub_eq_sub, smul_eq_mul])) h2
      have h4 : Tendsto (fun z' => (z' - z)⁻¹
          * (h z' σ τ * Work.Spaces.K σ - h z σ τ * Work.Spaces.K σ))
          (𝓝[≠] z) (𝓝 (d * Work.Spaces.K σ)) :=
        Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun z' => by ring)) h3
      rw [hd.deriv]
      exact h4
  -- identify the two expressions of the difference quotients
  have hcongr : (fun z' => (z' - z)⁻¹ * ((∫ σ in Work.Spaces.Iθ, h z' σ τ * Work.Spaces.K σ)
        - (∫ σ in Work.Spaces.Iθ, h z σ τ * Work.Spaces.K σ)))
      =ᶠ[𝓝[≠] z] (fun z' => ∫ σ in Work.Spaces.Iθ,
        (z' - z)⁻¹ * (h z' σ τ * Work.Spaces.K σ - h z σ τ * Work.Spaces.K σ)) := by
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds
      (by linarith : z / 2 < z) (by linarith : z < 2 * z))] with z' hz'
    have hz'0 : (0 : ℝ) < z' := lt_trans (by linarith : (0 : ℝ) < z / 2) hz'.1
    rw [MeasureTheory.integral_const_mul,
      MeasureTheory.integral_sub (c1jet_integrable_Kmul hα H hτ hz'0.le)
        (c1jet_integrable_Kmul hα H hτ hz.le)]
  have hslope : Tendsto (slope (fun z' => ∫ σ in Work.Spaces.Iθ, h z' σ τ * Work.Spaces.K σ) z)
      (𝓝[≠] z) (𝓝 D) :=
    Filter.Tendsto.congr' (hcongr.symm.trans (Filter.Eventually.of_forall
      (fun z' => by simp only [slope, vsub_eq_sub, smul_eq_mul]))) hDCT
  refine ⟨D, hasDerivAt_iff_tendsto_slope.mpr hslope, ?_⟩
  -- bound on the derivative
  rw [hD]
  have hnorm := MeasureTheory.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
    (fun σ => deriv (fun y => h y σ τ) z * Work.Spaces.K σ)
  rw [Real.norm_eq_abs] at hnorm
  refine le_trans hnorm (Work.FTS.RegPkgGal.Der.setIntegral_abs_le_of_bound
    (f := fun σ => deriv (fun y => h y σ τ) z * Work.Spaces.K σ) (c := 3 * N)
    (fun σ hσ => by
      rw [abs_mul]
      obtain ⟨d, hd, hdb⟩ := H.2 τ hτ σ hσ z hz
      rw [hd.deriv]
      calc |d| * |Work.Spaces.K σ| ≤ N * 3 :=
            mul_le_mul hdb (abs_K_le_three' hσ) (abs_nonneg _) hN
        _ = 3 * N := by ring))

/-- **The angular moment of a `C1Jet` family is a `C1Jet`.** -/
theorem c1jet_Kavg {α S N : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {h : ℝ → ℝ → ℝ → ℝ} (H : Work.FTS.RegPkgGal.C1Jet α S N h) :
    ∃ N' : ℝ, 0 ≤ N' ∧ Work.FTS.RegPkgGal.C1Jet α S N'
      (fun z θ τ => ∫ σ in Work.Spaces.Iθ, h z σ τ * Work.Spaces.K σ) := by
  have hN : 0 ≤ N := H.1.1
  have hpi1 : (0 : ℝ) < π / 2 := by linarith [Real.pi_pos]
  refine ⟨6 * N, by linarith, ⟨by linarith, ?_, ?_⟩, ?_⟩
  · -- the sup bound
    intro z θ τ hz hθ hτ
    refine le_trans (Kavg_abs_le hN (fun σ hσ => H.1.abs_le hz hσ hτ)) ?_
    nlinarith [Real.pi_lt_four, hN]
  · -- the joint modulus
    intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    refine le_trans (Kavg_modulus hα H hz hz' hτ hτ') ?_
    have hbase : 0 ≤ |z - z'| + |τ - τ'| := by positivity
    have hle : |z - z'| + |τ - τ'| ≤ |z - z'| + |θ - θ'| + |τ - τ'| := by
      have := abs_nonneg (θ - θ')
      linarith
    have h2 : (|z - z'| + |τ - τ'|) ^ α ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow hbase hle hα.le
    have h3 : 0 ≤ (|z - z'| + |τ - τ'|) ^ α := Real.rpow_nonneg hbase α
    have hNL : N * (|z - z'| + |τ - τ'|) ^ α ≤ N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      mul_le_mul_of_nonneg_left h2 hN
    have hpi : 3 * (π / 2) ≤ 6 := by linarith [Real.pi_lt_four]
    calc 3 * N * (π / 2) * (|z - z'| + |τ - τ'|) ^ α
        = 3 * (π / 2) * (N * (|z - z'| + |τ - τ'|) ^ α) := by ring
      _ ≤ 6 * (N * (|z - z'| + |τ - τ'|) ^ α) :=
          mul_le_mul_of_nonneg_right hpi (mul_nonneg hN h3)
      _ ≤ 6 * (N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α) :=
          mul_le_mul_of_nonneg_left hNL (by norm_num)
      _ = 6 * N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by ring
  · -- the `z`-derivative
    intro τ hτ θ hθ z hz
    obtain ⟨d, hd, hdb⟩ := Kavg_hasDerivAt hα H hτ hz
    refine ⟨d, hd, ?_⟩
    have hpi2 : (π : ℝ) / 2 ≤ 2 := by linarith [Real.pi_lt_four]
    nlinarith [hN, hpi1, hpi2, hdb]

/-! ## §3 The `C1Jet`-slot of the full profile -/

/-- **`F_τ = F_* + g̃(τ)` is a `C1Jet`** from the class data of the sanitised family (the
`hO1`-free version of `RXR5L.Ftau_C1Jet`). -/
theorem Ftau_C1Jet' {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))) :
    ∃ N₄ : ℝ, 0 ≤ N₄ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₄
        (fun z θ τ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ z θ) := by
  obtain ⟨N₁, hN₁0, hN₁⟩ := SG_C1Jet (S := S) hα hα13 hOK hS hSt1
  have hF : Work.FTS.RegPkgGal.C1Jet α S (100 + 20 * Work.FTS.Regularity.pExp α)
      (fun z θ (_ : ℝ) => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) :=
    Work.FTS.RegPkgGal.Der.C1JetFstar (S := S) hα hα13
  have hsum : Work.FTS.RegPkgGal.C1Jet α S
      ((100 + 20 * Work.FTS.Regularity.pExp α) + N₁)
      (fun z θ τ =>
        Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
          + Work.FTS_RegExport.RXR5.SG α g z θ τ) :=
    Work.FTS.RegPkgGal.C1Jet.add hF hN₁
  exact ⟨(100 + 20 * Work.FTS.Regularity.pExp α) + N₁,
    by have hp := Work.FTS.Regularity.pExp_pos hα; linarith, hsum⟩

/-! ## §4 The target -/

theorem FK_C1Jet {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g))) :
    ∃ N₁₄ : ℝ, 0 ≤ N₁₄ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₁₄
        (fun z θ τ => Work.Construction.FK (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ) z) := by
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨N₄, hN₄0, hC1⟩ := Ftau_C1Jet' hα hα13 hOK hS hSt1
  obtain ⟨N', hN'0, hKavg⟩ := c1jet_Kavg (S := S) hα hα1 hC1
  refine ⟨N', hN'0, Work.FTS.RegPkgGal.C1Jet.congr hKavg (fun z θ τ _ _ _ => ?_)⟩
  simp only [Work.Construction.FK, Work.Construction.Ftau]

end Work.FTS_RegExport.RXR5L
