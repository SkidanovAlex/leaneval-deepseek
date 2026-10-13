/-
# `n4norm_exists` — inhabitation of the `N4Norm` interface

The structure `Work.FTS.Nonlin.N4Norm` (`Submission/Work/FTS/Nonlinear/Interface.lean`)
collects the norm-level facts needed by the §8 estimates of Elgindi's paper.  This file
discharges **every** field of it, with a single universal constant
`Ci = 1 + Σ|C_i|` (the sum of the constants of the individual field lemmas plus one), for every
`0 < α₂ ≤ 1`.

**History (why three fields carry `SmoothInt` hypotheses).**  The interface revision of 07:02
did not carry the regularity hypotheses that the fields `angmul`, `wang` and `wrad` need — all
three constrain only totalized (`junk`) derivatives, which carry no differentiability
information.  The counterexample for `wrad` is machine-checked in
`Submission/Work/FTS/Nonlinear/n4norm_refuted.lean`
(`Work.FTS.Nonlinear.not_n4norm_exists`), and the one for `angmul` is analysed in
`N4Fields/angmul_field.lean`; `N4Fields/wang_field_refuted.lean` refutes the (stronger,
constant-free) lemma that had been dispatched for `wang`.  The interface was repaired in its
revision of 07:49 by adding the analyticity hypotheses `Work.Spaces.SmoothInt` for the profiles
involved, and this file is proved against that revision.  Details, counterexamples and the
field-by-field status: `NOTES_n4norm_exists.md`.

| field | lemma of this file | backing |
|---|---|---|
| `pos` | — | trivial |
| `prod` | `prod_field` | `Work.FTS.H2.HProdQ` |
| `wprod` | `wprod_field` | `Work.FTS.H2.WProdQ` |
| `wtoh` | `wtoh_field` | `Work.FTS.H2.WtoHQ` |
| `l12H` | `l12H_field` | `Work.FTS.H2.L12HQ` |
| `l12zero` | `l12zero_field` | `Work.FTS.H2.L12ZeroQ` + `constructionL12_eq_ellipticL12` |
| `fkH` | `fkH_field` | `N4Fields.fk_field` |
| `l12diff` | `l12diff_field` | `Work.FM.hasDerivAt_L12` via `L12densIntegrable` (no zero mode) |
| `radialMul` | `radialMul_field` | `RadialProd.radial_prod` |
| `angmul` | `N4Fields.angmul_field_smoothInt` | `HkIntegrand_mul_angular_le` |
| `wang` | `N4Fields.wang_field_smoothInt` | `prodW_interior_bound` + `wlInf_of_pointwise_bounds` |
| `wrad` | `N4Fields.wrad_field_smoothInt` | `wlInf_of_pointwise_bounds` |
| `wmul` | `wmul_field'` | `N4Fields.wmul_field` |
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.Nonlinear.Interface
import Submission.Work.FTS.H2.HProdQ
import Submission.Work.FTS.H2.WProdQ
import Submission.Work.FTS.H2.WtoHQ
import Submission.Work.FTS.H2.L12HQ
import Submission.Work.FTS.H2.L12ZeroQ
import Submission.Work.FTS.Nonlinear.RadialProd.radial_prod
import Submission.Work.FTS.Nonlinear.N4Fields.fk_field
import Submission.Work.FTS.Nonlinear.N4Fields.wmul_field
import Submission.Work.FTS.Nonlinear.N4Fields.angmul_field_smoothInt
import Submission.Work.FTS.Nonlinear.N4Fields.wang_field_smoothInt
import Submission.Work.FTS.Nonlinear.N4Fields.wrad_field_smoothInt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary identity: `(α^{-1/2})² = α^{-1}` -/

theorem rpow_neg_half_sq {α : ℝ} (hα : 0 < α) :
    (α ^ (-(1 / 2 : ℝ))) ^ 2 = α⁻¹ := by
  rw [sq, ← Real.rpow_add hα, show -(1 / 2 : ℝ) + -(1 / 2) = -1 by ring,
    Real.rpow_neg_one]

/-! ## `prod`: `ℋ⁴` is closed under products -/

theorem prod_field {α₂ : ℝ} (hα₂1 : α₂ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
      Work.FTS.Nonlin.RegQ α 4 f → Work.FTS.Nonlin.RegQ α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.H2.HProdQ
  refine ⟨Real.sqrt (10 * C) + 1, by positivity, ?_⟩
  intro α hα f g hf hg
  have hα1 : α ≤ 1 := le_trans hα.2 hα₂1
  obtain ⟨hmem, hsq⟩ := hC α f g hα.1 hα1 hf hg
  refine ⟨hmem, ?_⟩
  have hRnn : 0 ≤ Real.sqrt (10 * C) * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f
      * Work.FTS.Nonlin.Xn α g := by
    have h1 : (0 : ℝ) ≤ Real.sqrt (10 * C) := Real.sqrt_nonneg _
    have h2 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.1.le _
    have h3 : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α f := Real.sqrt_nonneg _
    have h4 : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g := Real.sqrt_nonneg _
    positivity
  have hsq' : Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ)
      ≤ (Real.sqrt (10 * C) * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f
          * Work.FTS.Nonlin.Xn α g) ^ 2 := by
    have hfac : C / (Work.Spaces.gam α - 1) = 10 * C * α⁻¹ := by
      rw [Work.Spaces.gam_sub_one]; field_simp
    have hfnn : 0 ≤ Work.Spaces.HkSq α 4 f := Work.Spaces.HkSq_nonneg α 4 f
    have hgnn : 0 ≤ Work.Spaces.HkSq α 4 g := Work.Spaces.HkSq_nonneg α 4 g
    have hR2 : (Real.sqrt (10 * C) * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f
          * Work.FTS.Nonlin.Xn α g) ^ 2
        = 10 * C * α⁻¹ * Work.Spaces.HkSq α 4 f * Work.Spaces.HkSq α 4 g := by
      have h3 : (Work.FTS.Nonlin.Xn α f) ^ 2 = Work.Spaces.HkSq α 4 f := by
        rw [show Work.FTS.Nonlin.Xn α f = Real.sqrt (Work.Spaces.HkSq α 4 f) from rfl,
          Real.sq_sqrt hfnn]
      have h4 : (Work.FTS.Nonlin.Xn α g) ^ 2 = Work.Spaces.HkSq α 4 g := by
        rw [show Work.FTS.Nonlin.Xn α g = Real.sqrt (Work.Spaces.HkSq α 4 g) from rfl,
          Real.sq_sqrt hgnn]
      calc (Real.sqrt (10 * C) * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f
            * Work.FTS.Nonlin.Xn α g) ^ 2
          = (Real.sqrt (10 * C)) ^ 2 * (α ^ (-(1 / 2 : ℝ))) ^ 2
              * (Work.FTS.Nonlin.Xn α f) ^ 2 * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
        _ = 10 * C * α⁻¹ * Work.Spaces.HkSq α 4 f * Work.Spaces.HkSq α 4 g := by
            rw [h3, h4, rpow_neg_half_sq hα.1, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 10 * C)]
    have hsq2 : Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ)
        ≤ 10 * C * α⁻¹ * Work.Spaces.HkSq α 4 f * Work.Spaces.HkSq α 4 g := by
      rwa [hfac] at hsq
    rw [hR2]
    exact hsq2
  rw [show Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
      = Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ)) from rfl]
  calc Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ))
      ≤ Real.sqrt ((Real.sqrt (10 * C) * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f
          * Work.FTS.Nonlin.Xn α g) ^ 2) := Real.sqrt_le_sqrt hsq'
    _ = Real.sqrt (10 * C) * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f
          * Work.FTS.Nonlin.Xn α g := Real.sqrt_sq hRnn
    _ ≤ (Real.sqrt (10 * C) + 1) * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f
          * Work.FTS.Nonlin.Xn α g := by
        have h1 : (0 : ℝ) ≤ Real.sqrt (10 * C) := Real.sqrt_nonneg _
        have h2 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.1.le _
        have h3 : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α f := Real.sqrt_nonneg _
        have h4 : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g := Real.sqrt_nonneg _
        nlinarith [mul_nonneg (mul_nonneg h2 h3) h4,
          mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4]

/-! ## `wprod`: `𝒲^{4,∞} × ℋ⁴ → ℋ⁴` -/

theorem wprod_field {α₂ : ℝ} (hα₂1 : α₂ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
      Work.FTS.LocData.SmoothQuad f → Work.Spaces.WlInfMem α 4 f →
      Work.FTS.Nonlin.RegQ α 4 g →
      Work.Spaces.HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.H2.WProdQ
  refine ⟨Real.sqrt (10 * C) + 1, by positivity, ?_⟩
  intro α hα f g hf hfm hg
  have hα1 : α ≤ 1 := le_trans hα.2 hα₂1
  obtain ⟨hmem, hsq⟩ := hC α f g hα.1 hα1 hf hfm hg
  refine ⟨hmem, ?_⟩
  have hWnn : 0 ≤ Work.Spaces.WlInf α 4 f := Work.Spaces.WlInf_nonneg α 4 f hfm
  have hRnn : 0 ≤ Real.sqrt (10 * C) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f
      * Work.FTS.Nonlin.Xn α g := by
    have h1 : (0 : ℝ) ≤ Real.sqrt (10 * C) := Real.sqrt_nonneg _
    have h2 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.1.le _
    have h4 : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g := Real.sqrt_nonneg _
    positivity
  have hsq' : Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ)
      ≤ (Real.sqrt (10 * C) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f
          * Work.FTS.Nonlin.Xn α g) ^ 2 := by
    have hfac : C / (Work.Spaces.gam α - 1) = 10 * C * α⁻¹ := by
      rw [Work.Spaces.gam_sub_one]; field_simp
    have hgnn : 0 ≤ Work.Spaces.HkSq α 4 g := Work.Spaces.HkSq_nonneg α 4 g
    have hR2 : (Real.sqrt (10 * C) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f
          * Work.FTS.Nonlin.Xn α g) ^ 2
        = 10 * C * α⁻¹ * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkSq α 4 g := by
      have h4 : (Work.FTS.Nonlin.Xn α g) ^ 2 = Work.Spaces.HkSq α 4 g := by
        rw [show Work.FTS.Nonlin.Xn α g = Real.sqrt (Work.Spaces.HkSq α 4 g) from rfl,
          Real.sq_sqrt hgnn]
      calc (Real.sqrt (10 * C) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f
            * Work.FTS.Nonlin.Xn α g) ^ 2
          = (Real.sqrt (10 * C)) ^ 2 * (α ^ (-(1 / 2 : ℝ))) ^ 2
              * (Work.Spaces.WlInf α 4 f) ^ 2 * (Work.FTS.Nonlin.Xn α g) ^ 2 := by ring
        _ = 10 * C * α⁻¹ * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkSq α 4 g := by
            rw [h4, rpow_neg_half_sq hα.1, Real.sq_sqrt (by positivity : (0:ℝ) ≤ 10 * C)]
    have hsq2 : Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ)
        ≤ 10 * C * α⁻¹ * (Work.Spaces.WlInf α 4 f) ^ 2 * Work.Spaces.HkSq α 4 g := by
      rwa [hfac] at hsq
    rw [hR2]
    exact hsq2
  rw [show Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
      = Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ)) from rfl]
  calc Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ => f z θ * g z θ))
      ≤ Real.sqrt ((Real.sqrt (10 * C) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f
          * Work.FTS.Nonlin.Xn α g) ^ 2) := Real.sqrt_le_sqrt hsq'
    _ = Real.sqrt (10 * C) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f
          * Work.FTS.Nonlin.Xn α g := Real.sqrt_sq hRnn
    _ ≤ (Real.sqrt (10 * C) + 1) * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f
          * Work.FTS.Nonlin.Xn α g := by
        have h1 : (0 : ℝ) ≤ Real.sqrt (10 * C) := Real.sqrt_nonneg _
        have h2 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.1.le _
        have h4 : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g := Real.sqrt_nonneg _
        nlinarith [mul_nonneg (mul_nonneg h2 hWnn) h4,
          mul_nonneg (mul_nonneg (mul_nonneg h1 h2) hWnn) h4]

/-! ## `wtoh`: the weighted `𝒲^{4,∞}`-bound controls `ℋ⁴` -/

theorem wtoh_field {α₂ : ℝ} (hα₂1 : α₂ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn,
      Work.FTS.LocData.SmoothQuad f →
      Work.Spaces.WlInfMem α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) →
      Work.FTS.Nonlin.RegQ α 4 f →
      Work.FTS.Nonlin.Xn α f ≤ C * Work.Spaces.WlInf α 4
        (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.H2.WtoHQ
  exact ⟨C, hCpos, fun α hα f _ hfm hg => hC α f hα.1 (le_trans hα.2 hα₂1) hfm hg⟩

/-! ## `l12H`: `L₁₂` is bounded on `ℋ⁴` -/

theorem l12H_field {α₂ : ℝ} (hα₂1 : α₂ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn,
      Work.FTS.Nonlin.RegQ α 4 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 4 (fun z θ => Work.Construction.L12 g z) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => Work.Construction.L12 g z)
        ≤ C * Work.FTS.Nonlin.Xn α g := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.H2.L12HQ
  exact ⟨C, hCpos, fun α hα g hg h0 => hC α g hα.1 (le_trans hα.2 hα₂1) hg h0⟩

/-! ## `l12zero`: the zero mode of `L₁₂` -/

theorem l12zero_field {α₂ : ℝ} (hα₂1 : α₂ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f : Fn,
      Work.FTS.Nonlin.RegQ α 4 f →
      |Work.Construction.L12 f 0| ≤ C * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.H2.L12ZeroQ
  refine ⟨C, hCpos, ?_⟩
  intro α hα f hf
  have h := hC α f hα.1 (le_trans hα.2 hα₂1) hf
  rw [Work.FTS.H2.constructionL12_eq_ellipticL12 f]
  exact h

/-! ## `fkH`: the radial angular moment `FK g` -/

theorem fkH_field {α₂ : ℝ} (hα₂ : 0 < α₂) (hα₂1 : α₂ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn,
      Work.FTS.Nonlin.RegQ α 4 g → Work.Construction.L12 g 0 = 0 →
      Work.Spaces.HkMem α 4 (fun z _ => Work.Construction.FK g z) ∧
      Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z)
        ≤ C * Work.FTS.Nonlin.Xn α g :=
  Work.FTS.Nonlinear.N4Fields.fk_field hα₂ hα₂1

/-! ## `radialMul`: lossless product with a function of `z` alone -/

theorem radialMul_field {α₂ : ℝ} (hα₂1 : α₂ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ (r : ℝ → ℝ) (g : Fn),
      Work.FTS.LocData.SmoothQuad (fun z _ => r z) → Work.FTS.LocData.SmoothQuad g →
      Work.Spaces.HkMem α 4 (fun z _ => r z) → Work.Spaces.HkMem α 4 g →
      (∀ b : ℕ, b ≤ 4 → Filter.Tendsto (fun z : ℝ => Work.Spaces.DzIter b (fun z _ => r z) z 0)
        Filter.atTop (nhds 0)) →
      (∀ b : ℕ, b ≤ 4 → ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
        Filter.Tendsto (fun z : ℝ => Work.Spaces.DzIter b g z θ) Filter.atTop (nhds 0)) →
      Work.Spaces.HkMem α 4 (fun z θ => r z * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => r z * g z θ)
        ≤ C * Work.FTS.Nonlin.Xn α (fun z _ => r z) * Work.FTS.Nonlin.Xn α g := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.Nonlinear.RadialProd.radial_prod
  exact ⟨C, hCpos, fun α hα r g hr hg hrm hgm hdecr hdecg =>
    hC α hα.1 (le_trans hα.2 hα₂1) r g hr hg hrm hgm hdecr hdecg⟩

/-! ## `wmul`: the `𝒲^{4,∞}`-product rule -/

theorem wmul_field' {α₂ : ℝ} (hα₂ : 0 < α₂) (hα₂1 : α₂ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
      Work.FTS.LocData.SmoothQuad f → Work.FTS.LocData.SmoothQuad g →
      Work.Spaces.WlInfMem α 4 f → Work.Spaces.WlInfMem α 4 g →
      (∀ k : ℕ, k ≤ 4 → ∀ z : ℝ,
        Work.Spaces.pzIter k g z 0 = 0 ∧ Work.Spaces.pzIter k g z (π / 2) = 0) →
      Work.Spaces.WlInfMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.Spaces.WlInf α 4 (fun z θ => f z θ * g z θ)
        ≤ C * Work.Spaces.WlInf α 4 f * Work.Spaces.WlInf α 4 g :=
  Work.FTS.Nonlinear.N4Fields.wmul_field hα₂ hα₂1

/-! ## `l12diff`: differentiability of `z ↦ L₁₂(g)(z)` on `(0,∞)` -/

theorem l12diff_field {α₂ : ℝ} (hα₂1 : α₂ ≤ 1) :
    ∀ α ∈ Set.Ioc 0 α₂, ∀ g : Fn, Work.FTS.LocData.SmoothQuad g →
      Work.Spaces.HkMem α 4 g → ∀ z ∈ Set.Ioi (0 : ℝ),
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z := by
  intro α hα g hsm hmem z hz
  have hα1 : α ≤ 1 := le_trans hα.2 hα₂1
  -- the density is integrable on `(0,∞)` and continuous at `z`
  have hint : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.H2.L12densIntegrable α g hα.1 hα1 hsm hmem
  obtain ⟨hQang_deriv, hQang_cont⟩ := Work.FTS.H2.QangDiff α g hα.1 hα1 hsm hmem
  have hdens_contOn : ContinuousOn (Work.Elliptic.L12dens g) (Set.Ioi (0 : ℝ)) := by
    have hdiv : ContinuousOn (fun z => Work.Elliptic.Qang g 0 z / z) (Set.Ioi (0 : ℝ)) :=
      (hQang_cont 0 (by norm_num)).div continuousOn_id (fun z hz => ne_of_gt hz)
    exact hdiv.congr (fun z _ => Work.Elliptic.L12dens_eq_Qang_div g z)
  have hdens_contAt : ContinuousAt (Work.Elliptic.L12dens g) z :=
    hdens_contOn.continuousAt (isOpen_Ioi.mem_nhds hz)
  -- the primitive `t ↦ ∫_0^t dens` is differentiable at `z`
  have hInt0z : IntervalIntegrable (Work.Elliptic.L12dens g) volume (0 : ℝ) z := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hz.le]
    exact hint.mono_set Set.Ioc_subset_Ioi_self
  have hprim : HasDerivAt (fun t => ∫ s in (0 : ℝ)..t, Work.Elliptic.L12dens g s)
      (Work.Elliptic.L12dens g z) z :=
    intervalIntegral.integral_hasDerivAt_right hInt0z
      (ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi hdens_contOn z hz) hdens_contAt
  -- `L₁₂(g)(t) = (L₁₂(g)(z) + ∫_0^z dens) - ∫_0^t dens` near `z`
  have hev : (fun t => Work.Elliptic.L12 g t) =ᶠ[𝓝 z]
      fun t => (Work.Elliptic.L12 g z + ∫ s in (0 : ℝ)..z, Work.Elliptic.L12dens g s)
        - ∫ s in (0 : ℝ)..t, Work.Elliptic.L12dens g s := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with t ht
    have htpos : 0 < t := ht
    have hzint : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi z) :=
      hint.mono_set (Ioi_subset_Ioi hz.le)
    have htint : MeasureTheory.IntegrableOn (Work.Elliptic.L12dens g) (Set.Ioi t) :=
      hint.mono_set (Ioi_subset_Ioi htpos.le)
    have hmain : (∫ s in Set.Ioi z, Work.Elliptic.L12dens g s)
        - (∫ s in Set.Ioi t, Work.Elliptic.L12dens g s)
        = ∫ s in z..t, Work.Elliptic.L12dens g s := by
      rcases le_total z t with hle | hle
      · exact intervalIntegral.integral_Ioi_sub_Ioi hzint hle
      · have h := intervalIntegral.integral_Ioi_sub_Ioi htint hle
        rw [intervalIntegral.integral_symm (a := t) (b := z)]
        linarith
    have hsplit : (∫ s in z..t, Work.Elliptic.L12dens g s)
        = (∫ s in (0 : ℝ)..t, Work.Elliptic.L12dens g s)
          - ∫ s in (0 : ℝ)..z, Work.Elliptic.L12dens g s := by
      have h0z : IntervalIntegrable (Work.Elliptic.L12dens g) volume (0 : ℝ) z := hInt0z
      have hzt : IntervalIntegrable (Work.Elliptic.L12dens g) volume z t := by
        rw [intervalIntegrable_iff]
        refine hint.mono_set ?_
        intro x hx
        have h1 : min z t < x := by
          rcases le_total z t with h | h
          · rw [uIoc_of_le h] at hx
            exact lt_of_le_of_lt (min_le_left _ _) hx.1
          · rw [uIoc_of_ge h] at hx
            exact lt_of_le_of_lt (min_le_right _ _) hx.1
        exact lt_of_le_of_lt (le_min hz.le htpos.le) h1
      have h := intervalIntegral.integral_add_adjacent_intervals h0z hzt
      linarith
    rw [Work.Elliptic.L12, Work.Elliptic.L12]
    linarith
  have hdiff : DifferentiableAt ℝ
      (fun t => (Work.Elliptic.L12 g z + ∫ s in (0 : ℝ)..z, Work.Elliptic.L12dens g s)
        - ∫ s in (0 : ℝ)..t, Work.Elliptic.L12dens g s) z :=
    (differentiableAt_const _).sub hprim.differentiableAt
  have hEll : DifferentiableAt ℝ (fun t => Work.Elliptic.L12 g t) z :=
    hdiff.congr_of_eventuallyEq hev
  simpa [Work.FTS.H2.constructionL12_eq_ellipticL12 g] using hEll

theorem n4norm_exists {α₂ : ℝ} (hα₂ : 0 < α₂) (hα₂1 : α₂ ≤ 1) :
    ∃ Ci : ℝ, 0 < Ci ∧ Work.FTS.Nonlin.N4Norm Ci α₂ := by
  obtain ⟨C1, hC1pos, hC1⟩ := prod_field hα₂1
  obtain ⟨C2, hC2pos, hC2⟩ := wprod_field hα₂1
  obtain ⟨C3, hC3pos, hC3⟩ := wtoh_field hα₂1
  obtain ⟨C4, hC4pos, hC4⟩ := l12H_field hα₂1
  obtain ⟨C5, hC5pos, hC5⟩ := l12zero_field hα₂1
  obtain ⟨C6, hC6pos, hC6⟩ := fkH_field hα₂ hα₂1
  obtain ⟨C7, hC7pos, hC7⟩ := radialMul_field hα₂1
  obtain ⟨C8, hC8pos, hC8⟩ := wmul_field' hα₂ hα₂1
  obtain ⟨C9, hC9pos, hC9⟩ := Work.FTS.Nonlinear.N4Fields.angmul_field_smoothInt hα₂ hα₂1
  obtain ⟨C10, hC10pos, hC10⟩ := Work.FTS.Nonlinear.N4Fields.wang_field_smoothInt hα₂ hα₂1
  obtain ⟨C11, hC11pos, hC11⟩ := Work.FTS.Nonlinear.N4Fields.wrad_field_smoothInt hα₂ hα₂1
  set Ci : ℝ := 1 + |C1| + |C2| + |C3| + |C4| + |C5| + |C6| + |C7| + |C8| + |C9| + |C10| + |C11|
    with hCidef
  have hCipos : 0 < Ci := by rw [hCidef]; positivity
  have h1 : C1 ≤ Ci := by
    rw [hCidef]
    linarith [le_abs_self C1, abs_nonneg C2, abs_nonneg C3, abs_nonneg C4, abs_nonneg C5,
      abs_nonneg C6, abs_nonneg C7, abs_nonneg C8, abs_nonneg C9, abs_nonneg C10, abs_nonneg C11]
  have h2 : C2 ≤ Ci := by
    rw [hCidef]
    linarith [le_abs_self C2, abs_nonneg C1, abs_nonneg C3, abs_nonneg C4, abs_nonneg C5,
      abs_nonneg C6, abs_nonneg C7, abs_nonneg C8, abs_nonneg C9, abs_nonneg C10, abs_nonneg C11]
  have h3 : C3 ≤ Ci := by
    rw [hCidef]
    linarith [le_abs_self C3, abs_nonneg C1, abs_nonneg C2, abs_nonneg C4, abs_nonneg C5,
      abs_nonneg C6, abs_nonneg C7, abs_nonneg C8, abs_nonneg C9, abs_nonneg C10, abs_nonneg C11]
  have h4 : C4 ≤ Ci := by
    rw [hCidef]
    linarith [le_abs_self C4, abs_nonneg C1, abs_nonneg C2, abs_nonneg C3, abs_nonneg C5,
      abs_nonneg C6, abs_nonneg C7, abs_nonneg C8, abs_nonneg C9, abs_nonneg C10, abs_nonneg C11]
  have h5 : C5 ≤ Ci := by
    rw [hCidef]
    linarith [le_abs_self C5, abs_nonneg C1, abs_nonneg C2, abs_nonneg C3, abs_nonneg C4,
      abs_nonneg C6, abs_nonneg C7, abs_nonneg C8, abs_nonneg C9, abs_nonneg C10, abs_nonneg C11]
  have h6 : C6 ≤ Ci := by
    rw [hCidef]
    linarith [le_abs_self C6, abs_nonneg C1, abs_nonneg C2, abs_nonneg C3, abs_nonneg C4,
      abs_nonneg C5, abs_nonneg C7, abs_nonneg C8, abs_nonneg C9, abs_nonneg C10, abs_nonneg C11]
  have h7 : C7 ≤ Ci := by
    rw [hCidef]
    linarith [le_abs_self C7, abs_nonneg C1, abs_nonneg C2, abs_nonneg C3, abs_nonneg C4,
      abs_nonneg C5, abs_nonneg C6, abs_nonneg C8, abs_nonneg C9, abs_nonneg C10, abs_nonneg C11]
  have h8 : C8 ≤ Ci := by
    rw [hCidef]
    linarith [le_abs_self C8, abs_nonneg C1, abs_nonneg C2, abs_nonneg C3, abs_nonneg C4,
      abs_nonneg C5, abs_nonneg C6, abs_nonneg C7, abs_nonneg C9, abs_nonneg C10, abs_nonneg C11]
  have h9 : C9 ≤ Ci := by
    rw [hCidef]
    linarith [le_abs_self C9, abs_nonneg C1, abs_nonneg C2, abs_nonneg C3, abs_nonneg C4,
      abs_nonneg C5, abs_nonneg C6, abs_nonneg C7, abs_nonneg C8, abs_nonneg C10, abs_nonneg C11]
  have h10 : C10 ≤ Ci := by
    rw [hCidef]
    linarith [le_abs_self C10, abs_nonneg C1, abs_nonneg C2, abs_nonneg C3, abs_nonneg C4,
      abs_nonneg C5, abs_nonneg C6, abs_nonneg C7, abs_nonneg C8, abs_nonneg C9, abs_nonneg C11]
  have h11 : C11 ≤ Ci := by
    rw [hCidef]
    linarith [le_abs_self C11, abs_nonneg C1, abs_nonneg C2, abs_nonneg C3, abs_nonneg C4,
      abs_nonneg C5, abs_nonneg C6, abs_nonneg C7, abs_nonneg C8, abs_nonneg C9, abs_nonneg C10]
  refine ⟨Ci, hCipos, ?_⟩
  refine ⟨⟨hCipos, hα₂⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- prod
    intro α hα f g hf hg
    obtain ⟨hmem, hineq⟩ := hC1 α hα f g hf hg
    refine ⟨hmem, ?_⟩
    have hαh : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.1.le _
    have hXf : 0 ≤ Work.FTS.Nonlin.Xn α f := Real.sqrt_nonneg _
    have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Real.sqrt_nonneg _
    calc Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ C1 * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g := hineq
      _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hαh) hXf) hXg
  · -- wprod
    intro α hα f g hfS hfm hreg
    obtain ⟨hmem, hineq⟩ := hC2 α hα f g hfS hfm hreg
    refine ⟨hmem, ?_⟩
    have hαh : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.1.le _
    have hWf : 0 ≤ Work.Spaces.WlInf α 4 f := Work.Spaces.WlInf_nonneg α 4 f hfm
    have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Real.sqrt_nonneg _
    calc Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ C2 * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g := hineq
      _ ≤ Ci * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 4 f * Work.FTS.Nonlin.Xn α g :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hαh) hWf) hXg
  · -- wtoh
    intro α hα f hfS hfm hreg
    have h := hC3 α hα f hfS hfm hreg
    have hWnn : 0 ≤ Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) :=
      Work.Spaces.WlInf_nonneg α 4 _ hfm
    calc Work.FTS.Nonlin.Xn α f
        ≤ C3 * Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) := h
      _ ≤ Ci * Work.Spaces.WlInf α 4 (fun z θ => (z + 1) ^ 3 / z ^ 2 * f z θ) :=
          mul_le_mul_of_nonneg_right h3 hWnn
  · -- l12H
    intro α hα g hreg h0
    obtain ⟨hmem, hineq⟩ := hC4 α hα g hreg h0
    refine ⟨hmem, ?_⟩
    have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Real.sqrt_nonneg _
    exact le_trans hineq (mul_le_mul_of_nonneg_right h4 hXg)
  · -- l12zero
    intro α hα f hreg
    have h := hC5 α hα f hreg
    have hXf : 0 ≤ Work.FTS.Nonlin.Xn α f := Real.sqrt_nonneg _
    exact le_trans h (mul_le_mul_of_nonneg_right h5 hXf)
  · -- fkH
    intro α hα g hreg h0
    obtain ⟨hmem, hineq⟩ := hC6 α hα g hreg h0
    refine ⟨hmem, ?_⟩
    have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Real.sqrt_nonneg _
    exact le_trans hineq (mul_le_mul_of_nonneg_right h6 hXg)
  · -- l12diff
    intro α hα g hsm hmem z hz
    exact l12diff_field hα₂1 α hα g hsm hmem z hz
  · -- radialMul
    intro α hα r g hrS hgS hrm hgm hdecr hdecg
    obtain ⟨hmem, hineq⟩ := hC7 α hα r g hrS hgS hrm hgm hdecr hdecg
    refine ⟨hmem, ?_⟩
    have hXr : 0 ≤ Work.FTS.Nonlin.Xn α (fun z _ => r z) := Real.sqrt_nonneg _
    have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Real.sqrt_nonneg _
    exact le_trans hineq
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h7 hXr) hXg)
  · -- angmul
    intro α hα a f haSm haB haD hfS hmem
    obtain ⟨hmem', hineq⟩ := hC9 α hα a Ci f hCipos.le haSm haB haD hfS hmem
    refine ⟨hmem', ?_⟩
    have hXf : 0 ≤ Work.FTS.Nonlin.Xn α f := Real.sqrt_nonneg _
    calc Work.FTS.Nonlin.Xn α (fun z θ => a θ * f z θ)
        ≤ C9 * Ci * Work.FTS.Nonlin.Xn α f := hineq
      _ ≤ Ci * Ci * Work.FTS.Nonlin.Xn α f :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h9 hCipos.le) hXf
  · -- wang
    intro α hα a h haSm hhSm haB haD hmem
    obtain ⟨hmem', hineq⟩ := hC10 α hα a Ci h hCipos.le haSm hhSm haB haD hmem
    refine ⟨hmem', ?_⟩
    have hWh : 0 ≤ Work.Spaces.WlInf α 4 h := Work.Spaces.WlInf_nonneg α 4 h hmem
    calc Work.Spaces.WlInf α 4 (fun z θ => a θ * h z θ)
        ≤ C10 * Ci * Work.Spaces.WlInf α 4 h := hineq
      _ ≤ Ci * Ci * Work.Spaces.WlInf α 4 h :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h10 hCipos.le) hWh
  · -- wrad
    intro α hα φ h hφSm hhSm hφm hhm
    obtain ⟨hmem', hineq⟩ := hC11 α hα φ h hφSm hhSm hφm hhm
    refine ⟨hmem', ?_⟩
    have hWφ : 0 ≤ Work.Spaces.WlInf α 4 (fun z _ => φ z) :=
      Work.Spaces.WlInf_nonneg α 4 _ hφm
    have hWh : 0 ≤ Work.Spaces.WlInf α 4 h := Work.Spaces.WlInf_nonneg α 4 h hhm
    exact le_trans hineq
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h11 hWφ) hWh)
  · -- wmul
    intro α hα f g hfS hgS hfm hgm hbdy
    obtain ⟨hmem, hineq⟩ := hC8 α hα f g hfS hgS hfm hgm hbdy
    refine ⟨hmem, ?_⟩
    have hWf : 0 ≤ Work.Spaces.WlInf α 4 f := Work.Spaces.WlInf_nonneg α 4 f hfm
    have hWg : 0 ≤ Work.Spaces.WlInf α 4 g := Work.Spaces.WlInf_nonneg α 4 g hgm
    exact le_trans hineq (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h8 hWf) hWg)

end Work.FTS.Nonlinear
