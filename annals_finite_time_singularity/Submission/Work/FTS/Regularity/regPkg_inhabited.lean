/-
# `Work.FTS.Regularity.regPkg_inhabited` — the interface `RegPkg` is inhabited

The interface `Work.FTS.Regularity.RegPkg` (node N7 of the route) collects the quantitative
regularity data of a self-similar profile `g` (the perturbation `F - F_*` of the modulation) with
which the transfer theorems of the chapter produce the physical regularity of the reconstructed
vorticity and velocity.

This module proves the **inhabitation obligation** of the interface, for the *localised static*
profile of the route: for every `0 < α ≤ 1/3` the package

  `RegPkg α 1 (fun _ => 1) (fun _ => 1) (fun z θ _ => -F_*(z,θ)·(1 - χ(z/4)))`

holds, where `F_* = Work.Construction.Fstar (3α)` is the paper's profile and `χ` the explicit
cut-off `Work.Stability.chi`.  The profile perturbation `g = -F_*·(1 - χ(z/4))` is the *far part*
`zfar 4 F_*` of the profile, so that the full profile `F_* + g = F_*·χ(·/4)` is compactly
supported in `z` — this is the localisation of the route (see `Submission/Work/FTS/LocData`),
and it is what makes the far-field clauses of the challenge statement trivial.

## Why this particular `g`

`g` vanishes identically for `z ≤ 4` (where `χ(z/4) = 1`) and equals `-F_*` for `z ≥ 8` (where
`χ(z/4) = 0`), so

* the structural fields at `z = 0` (`hquad0`, `hquad`) and the quadratic Taylor datum (`htay`)
  are trivial, with `K = 0`;
* the angular vanishing (`hvt`) is the exact vanishing of `Γ(θ) = (sinθcos²θ)^α` at the
  endpoints `θ = 0, π/2`;
* the compact support of the *full* profile (`hsupp`) holds with `L = 8`;
* the `ℋ⁴`-membership (`hH4`) is the far-part membership `zfar 4 F_* ∈ ℋ⁴`: on the compact
  region `z ≤ 4` the perturbation is *locally zero* (so the radial weight `w = (1+z)²/z²` is
  harmless), and for `z ≥ 4` the pointwise `ℋ⁴`-integrand is dominated by the angular majorant
  `angMaj` of the localisation chapter (`hkIntegrandZfarBound`);
* the joint `α`-Hölder data (`hg`, `hpz`) come from the moduli of the profile
  (`gammaFstarModuli`, `pzFstarModuli`) and the moduli of the cut-off (`chiModuli`), through the
  `Jet`-calculus proved below.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.Regularity.chiModuli
import Submission.Work.FTS.Regularity.gammaFstarModuli
import Submission.Work.FTS.Regularity.pzFstarModuli
import Submission.Work.FTS.Regularity.hkIntegrandZfarBound
import Submission.Work.FTS.LocData.Defs
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.LocData.SmoothQuad_locG
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.LocData.angMaj_mem
import Submission.Work.FTS.LocData.HkIntegrand_neg
import Submission.Work.FTS.LocData.HkMem_zfar_Fstar
import Submission.Work.Stability.HkSqZfar
import Submission.Work.Stability.PzFstarAdd
import Submission.Work.FM.Core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

namespace Work.FTS.Regularity

/-! ## The `Jet` interface: closure properties -/

theorem Jet.neg {α S N : ℝ} {h : ℝ → ℝ → ℝ → ℝ} (H : Jet α S N h) :
    Jet α S N (fun z θ τ => -h z θ τ) := by
  refine ⟨H.1, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    simpa using H.2.1 z θ τ hz hθ hτ
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h1 := H.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h2 : |(-h z θ τ) - (-h z' θ' τ')| = |h z θ τ - h z' θ' τ'| := by
      rw [show (-h z θ τ) - (-h z' θ' τ') = -(h z θ τ - h z' θ' τ') by ring, abs_neg]
    rw [h2]
    exact h1

theorem Jet.add {α S N₁ N₂ : ℝ} {a b : ℝ → ℝ → ℝ → ℝ} (Ha : Jet α S N₁ a)
    (Hb : Jet α S N₂ b) :
    Jet α S (N₁ + N₂) (fun z θ τ => a z θ τ + b z θ τ) := by
  refine ⟨add_nonneg Ha.1 Hb.1, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    calc |a z θ τ + b z θ τ| ≤ |a z θ τ| + |b z θ τ| := abs_add_le _ _
      _ ≤ N₁ + N₂ := add_le_add (Ha.2.1 z θ τ hz hθ hτ) (Hb.2.1 z θ τ hz hθ hτ)
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h1 := Ha.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h2 := Hb.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h3 : a z θ τ + b z θ τ - (a z' θ' τ' + b z' θ' τ')
        = (a z θ τ - a z' θ' τ') + (b z θ τ - b z' θ' τ') := by ring
    rw [h3]
    calc |(a z θ τ - a z' θ' τ') + (b z θ τ - b z' θ' τ')|
        ≤ |a z θ τ - a z' θ' τ'| + |b z θ τ - b z' θ' τ'| := abs_add_le _ _
      _ ≤ N₁ * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α
            + N₂ * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := add_le_add h1 h2
      _ = (N₁ + N₂) * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by ring

theorem Jet.mul {α S N₁ N₂ : ℝ} {a b : ℝ → ℝ → ℝ → ℝ} (Ha : Jet α S N₁ a)
    (Hb : Jet α S N₂ b) :
    Jet α S (2 * N₁ * N₂) (fun z θ τ => a z θ τ * b z θ τ) := by
  have hN : 0 ≤ 2 * N₁ * N₂ := by nlinarith [Ha.1, Hb.1]
  refine ⟨hN, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    have h1 := Ha.2.1 z θ τ hz hθ hτ
    have h2 := Hb.2.1 z θ τ hz hθ hτ
    calc |a z θ τ * b z θ τ| = |a z θ τ| * |b z θ τ| := abs_mul _ _
      _ ≤ N₁ * N₂ := mul_le_mul h1 h2 (abs_nonneg _) Ha.1
      _ ≤ 2 * N₁ * N₂ := by nlinarith [Ha.1, Hb.1]
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h1 := Ha.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h2 := Hb.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have hb1 := Ha.2.1 z θ τ hz hθ hτ
    have hb2 := Hb.2.1 z' θ' τ' hz' hθ' hτ'
    have hd : |a z θ τ * b z θ τ - a z' θ' τ' * b z' θ' τ'|
        ≤ |a z θ τ| * |b z θ τ - b z' θ' τ'| + |b z' θ' τ'| * |a z θ τ - a z' θ' τ'| := by
      rw [show a z θ τ * b z θ τ - a z' θ' τ' * b z' θ' τ'
          = a z θ τ * (b z θ τ - b z' θ' τ') + b z' θ' τ' * (a z θ τ - a z' θ' τ') by ring]
      refine le_trans (abs_add_le _ _) (le_of_eq ?_)
      rw [abs_mul, abs_mul]
    refine le_trans hd ?_
    have e1 : |a z θ τ| * |b z θ τ - b z' θ' τ'|
        ≤ N₁ * (N₂ * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α) :=
      mul_le_mul hb1 h2 (abs_nonneg _) Ha.1
    have e2 : |b z' θ' τ'| * |a z θ τ - a z' θ' τ'|
        ≤ N₂ * (N₁ * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α) :=
      mul_le_mul hb2 h1 (abs_nonneg _) Hb.1
    calc |a z θ τ| * |b z θ τ - b z' θ' τ'| + |b z' θ' τ'| * |a z θ τ - a z' θ' τ'|
        ≤ N₁ * (N₂ * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α)
          + N₂ * (N₁ * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α) := add_le_add e1 e2
      _ = 2 * N₁ * N₂ * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by ring

theorem Jet.congr {α S N : ℝ} {a b : ℝ → ℝ → ℝ → ℝ} (Ha : Jet α S N a)
    (h : ∀ z θ τ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → τ ∈ Set.Icc 0 S → a z θ τ = b z θ τ) :
    Jet α S N b := by
  refine ⟨Ha.1, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    rw [← h z θ τ hz hθ hτ]
    exact Ha.2.1 z θ τ hz hθ hτ
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    rw [← h z θ τ hz hθ hτ, ← h z' θ' τ' hz' hθ' hτ']
    exact Ha.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'

theorem Jet.of_bounded_holder {α S N : ℝ} {h : ℝ → ℝ → ℝ} (hN : 0 ≤ N) (hα0 : 0 ≤ α)
    (hb : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |h z θ| ≤ N)
    (hh : ∀ z z' θ θ' : ℝ, 0 ≤ z → 0 ≤ z' → θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ →
      |h z θ - h z' θ'| ≤ N * (|z - z'| + |θ - θ'|) ^ α) :
    Jet α S N (fun z θ _ => h z θ) := by
  refine ⟨hN, fun z θ τ hz hθ hτ => hb z θ hz hθ, ?_⟩
  intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
  refine le_trans (hh z z' θ θ' hz hz' hθ hθ') ?_
  refine mul_le_mul_of_nonneg_left ?_ hN
  refine Real.rpow_le_rpow (by positivity) ?_ hα0
  have h1 : 0 ≤ |θ - θ'| := abs_nonneg _
  have h2 : 0 ≤ |τ - τ'| := abs_nonneg _
  linarith

/-- For `0 ≤ α ≤ 1` and `0 ≤ a ≤ 1`, `0 ≤ b`: `a ≤ (a+b)^α`. -/
theorem le_rpow_add {α a b : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) : a ≤ (a + b) ^ α := by
  rcases eq_or_lt_of_le ha0 with ha | ha
  · rw [← ha]
    exact Real.rpow_nonneg (show (0 : ℝ) ≤ 0 + b by linarith) α
  · rcases le_total (a + b) 1 with h | h
    · have hpos : 0 < a + b := lt_of_lt_of_le ha (le_add_of_nonneg_right hb0)
      have hle := Real.rpow_le_rpow_of_exponent_ge hpos h hα1
      rw [Real.rpow_one] at hle
      linarith
    · have hle := Real.one_le_rpow h hα0
      linarith

/-- A bounded Lipschitz function of `z` alone gives a `Jet` (with constant `2N`). -/
theorem Jet.of_z_lipschitz {α S N : ℝ} {φ : ℝ → ℝ} (hN : 0 ≤ N) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hb : ∀ z : ℝ, |φ z| ≤ N) (hl : ∀ z z' : ℝ, |φ z - φ z'| ≤ N * |z - z'|) :
    Jet α S (2 * N) (fun z θ _ => φ z) := by
  refine ⟨by linarith, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    linarith [hb z]
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have hd0 : (0 : ℝ) ≤ |z - z'| + |θ - θ'| + |τ - τ'| := by positivity
    rcases le_total |z - z'| 1 with hcase | hcase
    · have hle1 : |z - z'| ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by
        have h := le_rpow_add hα0 hα1 (abs_nonneg (z - z')) hcase
          (by positivity : (0 : ℝ) ≤ |θ - θ'| + |τ - τ'|)
        rwa [← add_assoc] at h
      calc |φ z - φ z'| ≤ N * |z - z'| := hl z z'
        _ ≤ N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := mul_le_mul_of_nonneg_left hle1 hN
        _ ≤ 2 * N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by
            have := Real.rpow_nonneg hd0 α
            nlinarith [hN]
    · have hle1 : 1 ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by
        refine Real.one_le_rpow ?_ hα0
        have h1 : 0 ≤ |θ - θ'| := abs_nonneg _
        have h2 : 0 ≤ |τ - τ'| := abs_nonneg _
        linarith
      have h2N : |φ z - φ z'| ≤ 2 * N := by
        have h1 : |φ z| ≤ N := hb z
        have h2 : |φ z'| ≤ N := hb z'
        calc |φ z - φ z'| = |φ z + (-φ z')| := by ring_nf
          _ ≤ |φ z| + |-φ z'| := abs_add_le _ _
          _ = |φ z| + |φ z'| := by rw [abs_neg]
          _ ≤ 2 * N := by linarith
      calc |φ z - φ z'| ≤ 2 * N := h2N
        _ = 2 * N * 1 := by ring
        _ ≤ 2 * N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
            mul_le_mul_of_nonneg_left hle1 (by linarith)

/-! ## Two calculus auxiliaries -/

/-- The derivative of the cut-off factor `z ↦ 1 - χ(z/4)`: `-(1/4)·χ'(z/4)`. -/
theorem deriv_one_sub_chi_div (z : ℝ) :
    deriv (fun z' : ℝ => 1 - Work.Stability.chi (z' / 4)) z
      = -(1 / 4) * deriv Work.Stability.chi (z / 4) := by
  have hchi : ContDiff ℝ (1 : WithTop ℕ∞) Work.Stability.chi :=
    Work.Stability.chi_contDiff.of_le (by simp)
  have hchi_diff : Differentiable ℝ Work.Stability.chi := hchi.differentiable (by simp)
  have h1 : HasDerivAt (fun z' : ℝ => z' / 4) (1 / 4) z := by
    simpa using (hasDerivAt_id z).div_const 4
  have h2 : HasDerivAt Work.Stability.chi (deriv Work.Stability.chi (z / 4)) (z / 4) :=
    hchi_diff.differentiableAt.hasDerivAt
  have h3 : HasDerivAt (Work.Stability.chi ∘ fun z' : ℝ => z' / 4)
      (deriv Work.Stability.chi (z / 4) * (1 / 4)) z := h2.comp z h1
  have h3d : deriv (fun z' : ℝ => Work.Stability.chi (z' / 4)) z
      = deriv Work.Stability.chi (z / 4) * (1 / 4) := by
    simpa only [Function.comp_def] using h3.deriv
  have h4 : HasDerivAt (fun z' : ℝ => 1 - Work.Stability.chi (z' / 4))
      (0 - deriv Work.Stability.chi (z / 4) * (1 / 4)) z :=
    (hasDerivAt_const (x := z) (c := (1 : ℝ))).sub h3
  have h4d : deriv (fun z' : ℝ => 1 - Work.Stability.chi (z' / 4)) z
      = 0 - deriv Work.Stability.chi (z / 4) * (1 / 4) := h4.deriv
  rw [h4d]
  ring

/-- The `z`-derivative of the profile perturbation `-F_*(z,θ)·(1 - χ(z/4))`, by the product
rule: this is the expression whose `Jet`-data give the field `hpz` of the package. -/
theorem pz_slice_eq (α : ℝ) (z θ : ℝ) (hz : 0 ≤ z) :
    Work.Spaces.pz (fun z θ => -Work.Construction.Fstar (3 * α) z θ
        * (1 - Work.Stability.chi (z / 4))) z θ
      = (-(Work.Spaces.pz (Work.Construction.Fstar (3 * α)) z θ))
          * (1 - Work.Stability.chi (z / 4))
        + (-(Work.Construction.Fstar (3 * α) z θ))
          * deriv (fun z' : ℝ => 1 - Work.Stability.chi (z' / 4)) z := by
  have hz1 : -1 < z := by linarith
  have hF : DifferentiableAt ℝ (fun z' => Work.Construction.Fstar (3 * α) z' θ) z :=
    Work.Stability.differentiableAt_Fstar_slice (3 * α) θ z hz1
  have hchi : ContDiff ℝ (1 : WithTop ℕ∞) Work.Stability.chi :=
    Work.Stability.chi_contDiff.of_le (by simp)
  have hchi_diff : Differentiable ℝ Work.Stability.chi := hchi.differentiable (by simp)
  have hdiv : DifferentiableAt ℝ (fun z' : ℝ => z' / 4) z :=
    differentiableAt_id.div_const 4
  have hP : DifferentiableAt ℝ (fun z' : ℝ => 1 - Work.Stability.chi (z' / 4)) z :=
    (differentiableAt_const (c := (1 : ℝ))).sub
      (hchi_diff.differentiableAt.comp z hdiv)
  have h1d : deriv (-(fun z' : ℝ => Work.Construction.Fstar (3 * α) z' θ)) z
      = -(Work.Spaces.pz (Work.Construction.Fstar (3 * α)) z θ) := by
    rw [Work.Spaces.pz]
    exact deriv.neg
  have hmul : deriv (fun z' : ℝ => -Work.Construction.Fstar (3 * α) z' θ
        * (1 - Work.Stability.chi (z' / 4))) z
      = (-(Work.Spaces.pz (Work.Construction.Fstar (3 * α)) z θ))
          * (1 - Work.Stability.chi (z / 4))
        + (-(Work.Construction.Fstar (3 * α) z θ))
          * deriv (fun z' : ℝ => 1 - Work.Stability.chi (z' / 4)) z := by
    rw [show (fun z' : ℝ => -Work.Construction.Fstar (3 * α) z' θ
          * (1 - Work.Stability.chi (z' / 4)))
        = (-(fun z' : ℝ => Work.Construction.Fstar (3 * α) z' θ))
          * (fun z' : ℝ => 1 - Work.Stability.chi (z' / 4)) from rfl]
    rw [deriv_mul hF.neg hP, h1d]
    simp only [Pi.neg_apply]
  rw [Work.Spaces.pz]
  show deriv (fun z' : ℝ => -Work.Construction.Fstar (3 * α) z' θ
      * (1 - Work.Stability.chi (z' / 4))) z
    = (-(Work.Spaces.pz (Work.Construction.Fstar (3 * α)) z θ))
          * (1 - Work.Stability.chi (z / 4))
      + (-(Work.Construction.Fstar (3 * α) z θ))
          * deriv (fun z' : ℝ => 1 - Work.Stability.chi (z' / 4)) z
  exact hmul

/-! ## The pointwise `ℋ⁴`-integrand bound on the whole domain

The delegated bound `hkIntegrandZfarBound` covers `z ≥ 4`; for `z ∈ [0,4)` the perturbation
vanishes on a neighbourhood of `(z,θ)`, so its `ℋ⁴`-integrand vanishes there
(`HkIntegrand_zfar_eq_zero`, and `HkIntegrand_zero_fst` at `z = 0`). -/

theorem hkIntegrandCutProfile_all {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 ≤ z → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Work.Spaces.HkIntegrand (3 * α) 4
        (fun z θ => -Work.Construction.Fstar (3 * α) z θ * (1 - Work.Stability.chi (z / 4))) z θ
        ≤ C * Work.FTS.LocData.angMaj (3 * α) θ / (1 + z) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := hkIntegrandZfarBound hα hα13
  refine ⟨C, hC0, fun z hz θ hθ => ?_⟩
  have hang : 0 ≤ Work.FTS.LocData.angMaj (3 * α) θ := Work.FTS.LocData.angMaj_nonneg hθ
  rcases lt_or_ge z 4 with hz4 | hz4
  · have hzle : Work.Spaces.HkIntegrand (3 * α) 4
        (fun z θ => -Work.Construction.Fstar (3 * α) z θ * (1 - Work.Stability.chi (z / 4))) z θ
        = 0 := by
      rcases eq_or_lt_of_le hz with h0 | h0
      · subst h0
        exact Work.FTS.LocData.HkIntegrand_zero_fst (3 * α) 4 _ θ
      · have hfun : (fun z θ => -Work.Construction.Fstar (3 * α) z θ
            * (1 - Work.Stability.chi (z / 4)))
            = fun z θ => -((Work.Stability.zfar 4 (Work.Construction.Fstar (3 * α))) z θ) := by
          funext z θ
          rw [Work.Stability.zfar_apply]
          ring
        rw [hfun, Work.FTS.LocData.HkIntegrand_neg]
        exact Work.Stability.HkIntegrand_zfar_eq_zero (α := 3 * α) (k := 4)
          (Z := 4) (f := Work.Construction.Fstar (3 * α)) (by norm_num)
          (z := z) (θ := θ) ⟨h0, hz4⟩
    rw [hzle]
    have hnn : 0 ≤ C * Work.FTS.LocData.angMaj (3 * α) θ / (1 + z) ^ 2 := by positivity
    linarith
  · exact hC z hz4 θ hθ

/-! ## The regularity package -/

theorem regPkg_inhabited {α : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    Work.FTS.Regularity.RegPkg α 1 (fun _ => 1) (fun _ => 1)
      (fun z θ _ => -Work.Construction.Fstar (3 * α) z θ * (1 - Work.Stability.chi (z / 4))) := by
  obtain ⟨Cg, hCg0, hFb, hFz0, hFzpi, _hF00, _hGHolder, hFHolder⟩ :=
    gammaFstarModuli hα hα13
  obtain ⟨Cp, hCp0, hpzb, hpzH⟩ := pzFstarModuli hα hα13
  obtain ⟨Cc, hCcpos, _hcbnd, hcd1, _hcd2, hchLip, hcdLip⟩ := chiModuli
  have hMphi0 : 0 ≤ max Cc 1 := le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right _ _)
  have hGN : ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → 0 ≤ Work.FTS.Regularity.Gamma α θ :=
    fun θ hθ => Work.ConstructionInstance.Gamma_nonneg hθ
  have hG1 : ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ → Work.FTS.Regularity.Gamma α θ ≤ 1 :=
    fun θ hθ => Work.ConstructionInstance.Gamma_le_one hα.le hθ
  -- the `Jet` of the reference profile
  have hjetF : Jet α 1 Cg (fun z θ _ => Work.Construction.Fstar (3 * α) z θ) := by
    refine Jet.of_bounded_holder hCg0 hα.le (fun z θ hz hθ => ?_)
      (fun z z' θ θ' hz hz' hθ hθ' => hFHolder z z' θ θ' hz hz' hθ hθ')
    have h1 := hFb z θ hz hθ
    have h2 := hG1 θ hθ
    calc |Work.Construction.Fstar (3 * α) z θ| ≤ Cg * Work.FTS.Regularity.Gamma α θ := h1
      _ ≤ Cg * 1 := mul_le_mul_of_nonneg_left h2 hCg0
      _ = Cg := by ring
  -- the `Jet` of the cut-off factor `z ↦ 1 - χ(z/4)`
  have hjetPh : Jet α 1 (2 * max Cc 1) (fun z θ _ => 1 - Work.Stability.chi (z / 4)) := by
    refine Jet.of_z_lipschitz hMphi0 hα.le (by linarith) (fun z => ?_) (fun z z' => ?_)
    · have h2 := Work.Stability.chi_nonneg (z / 4)
      have h3 := Work.Stability.chi_le_one (z / 4)
      have h4 : |(1 : ℝ) - Work.Stability.chi (z / 4)| = 1 - Work.Stability.chi (z / 4) :=
        abs_of_nonneg (by linarith)
      rw [h4]
      exact le_trans (by linarith) (le_max_right _ _)
    · have h := hchLip (z / 4) (z' / 4)
      have h1 : |(1 - Work.Stability.chi (z / 4)) - (1 - Work.Stability.chi (z' / 4))|
          = |Work.Stability.chi (z / 4) - Work.Stability.chi (z' / 4)| := by
        rw [show (1 - Work.Stability.chi (z / 4)) - (1 - Work.Stability.chi (z' / 4))
            = -(Work.Stability.chi (z / 4) - Work.Stability.chi (z' / 4)) by ring, abs_neg]
      rw [h1]
      have h2 : |z / 4 - z' / 4| = |z - z'| / 4 := by
        rw [show z / 4 - z' / 4 = (z - z') / 4 by ring, abs_div,
          abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      calc |Work.Stability.chi (z / 4) - Work.Stability.chi (z' / 4)|
          ≤ Cc * |z / 4 - z' / 4| := h
        _ = Cc * (|z - z'| / 4) := by rw [h2]
        _ = (Cc / 4) * |z - z'| := by ring
        _ ≤ max Cc 1 * |z - z'| := by
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            linarith [le_max_left Cc 1]
  -- the `Jet` of the derivative of the cut-off factor
  have hjetDPh : Jet α 1 (2 * max Cc 1)
      (fun z θ _ => deriv (fun z' : ℝ => 1 - Work.Stability.chi (z' / 4)) z) := by
    refine Jet.of_z_lipschitz hMphi0 hα.le (by linarith) (fun z => ?_) (fun z z' => ?_)
    · rw [deriv_one_sub_chi_div z, abs_mul, abs_neg]
      have h1 : |((1 : ℝ) / 4)| = 1 / 4 := by norm_num
      rw [h1]
      have h2 := hcd1 (z / 4)
      calc (1 / 4) * |deriv Work.Stability.chi (z / 4)| ≤ (1 / 4) * Cc :=
            mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ ≤ max Cc 1 := by linarith [le_max_left Cc 1]
    · rw [deriv_one_sub_chi_div z, deriv_one_sub_chi_div z']
      have h1 : |-(1 / 4) * deriv Work.Stability.chi (z / 4)
            - (-(1 / 4) * deriv Work.Stability.chi (z' / 4))|
          = (1 / 4) * |deriv Work.Stability.chi (z / 4)
              - deriv Work.Stability.chi (z' / 4)| := by
        rw [show -(1 / 4) * deriv Work.Stability.chi (z / 4)
              - (-(1 / 4) * deriv Work.Stability.chi (z' / 4))
            = -(1 / 4) * (deriv Work.Stability.chi (z / 4)
              - deriv Work.Stability.chi (z' / 4)) by ring, abs_mul, abs_neg]
        norm_num
      rw [h1]
      have h2 := hcdLip (z / 4) (z' / 4)
      have h3 : |z / 4 - z' / 4| = |z - z'| / 4 := by
        rw [show z / 4 - z' / 4 = (z - z') / 4 by ring, abs_div,
          abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      calc (1 / 4) * |deriv Work.Stability.chi (z / 4) - deriv Work.Stability.chi (z' / 4)|
          ≤ (1 / 4) * (Cc * |z / 4 - z' / 4|) := mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ = (1 / 4) * (Cc * (|z - z'| / 4)) := by rw [h3]
        _ = (Cc / 16) * |z - z'| := by ring
        _ ≤ max Cc 1 * |z - z'| := by
            refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
            linarith [le_max_left Cc 1, hCcpos]
  -- the `Jet` of `∂_z F_*`
  have hjetpzF : Jet α 1 Cp (fun z θ _ => Work.Spaces.pz (Work.Construction.Fstar (3 * α)) z θ) :=
    Jet.of_bounded_holder hCp0 hα.le (fun z θ hz hθ => hpzb z θ hz hθ)
      (fun z z' θ θ' hz hz' hθ hθ' => hpzH z z' θ θ' hz hz' hθ hθ')
  -- the `Jet` of the perturbation
  have hjetg : Jet α 1 (2 * Cg * (2 * max Cc 1))
      (fun z θ _ => -Work.Construction.Fstar (3 * α) z θ * (1 - Work.Stability.chi (z / 4))) :=
    Jet.mul (Jet.neg hjetF) hjetPh
  -- the `ℋ⁴`-membership of the (τ-independent) profile perturbation
  have hH4fun : Work.Spaces.HkMem (3 * α) 4
      (fun z θ => -Work.Construction.Fstar (3 * α) z θ * (1 - Work.Stability.chi (z / 4))) := by
    obtain ⟨K, hK0, hKle⟩ := hkIntegrandCutProfile_all hα hα13
    obtain ⟨hAmS, hAmZ⟩ :=
      Work.FTS.LocData.angMaj_majorant_integrable (3 * α) K (by linarith) (by linarith)
    have hsm0 : Work.FTS.LocData.SmoothQuad (fun _ _ : ℝ => (0 : ℝ)) := by
      unfold Work.FTS.LocData.SmoothQuad
      simpa only [Function.uncurry_def] using (contDiffOn_const :
        ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ × ℝ => (0 : ℝ))
          (Set.Ioi (-1) ×ˢ Set.Ioo 0 (π / 2)))
    have hloc := Work.FTS.LocData.SmoothQuad_locG (3 * α) 4 0 (by linarith) (by linarith) hsm0
    have hsm : Work.FTS.LocData.SmoothQuad
        (fun z θ => -Work.Construction.Fstar (3 * α) z θ * (1 - Work.Stability.chi (z / 4))) := by
      unfold Work.FTS.LocData.SmoothQuad at hloc ⊢
      refine hloc.congr (fun p hp => ?_)
      simp only [Function.uncurry_def, Work.FTS.LocData.locG_apply, Work.FTS.LocData.locData_apply]
      ring
    have hcont := Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad (3 * α) 4 _ hsm
    exact Work.FTS.LocData.HkMem_of_majorant (3 * α) 4 hcont
      (M := fun z θ => K * Work.FTS.LocData.angMaj (3 * α) θ / (1 + z) ^ 2) hAmS hAmZ hKle
  refine ⟨hα, hα13, by norm_num, fun τ hτ => by norm_num, fun τ hτ => by norm_num,
    ⟨1, 1, by norm_num, fun τ hτ => ⟨le_rfl, le_rfl⟩⟩,
    ⟨1, 1, by norm_num, fun τ hτ => ⟨le_rfl, le_rfl⟩⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- hAdiff
    intro τ hτ
    rw [deriv_const]
    exact hasDerivAt_const (x := τ) (c := (1 : ℝ))
  · -- hBdiff
    intro τ hτ
    rw [deriv_const]
    exact hasDerivAt_const (x := τ) (c := (1 : ℝ))
  · -- hAd
    exact ⟨0, fun τ hτ => by rw [deriv_const]; norm_num⟩
  · -- hBd
    exact ⟨0, fun τ hτ => by rw [deriv_const]; norm_num⟩
  · -- hAdh
    exact ⟨0, fun τ hτ τ' hτ' => by rw [deriv_const, deriv_const]; simp⟩
  · -- hBdh
    exact ⟨0, fun τ hτ τ' hτ' => by rw [deriv_const, deriv_const]; simp⟩
  · -- hvt
    intro τ hτ
    constructor
    · intro z
      show -Work.Construction.Fstar (3 * α) z 0 * (1 - Work.Stability.chi (z / 4)) = 0
      rw [hFz0 z]
      ring
    · intro z
      show -Work.Construction.Fstar (3 * α) z (Real.pi / 2)
        * (1 - Work.Stability.chi (z / 4)) = 0
      rw [hFzpi z]
      ring
  · -- hquad0
    intro τ hτ θ hθ
    show -Work.Construction.Fstar (3 * α) 0 θ * (1 - Work.Stability.chi (0 / 4)) = 0
    rw [zero_div, Work.Stability.chi_zero]
    ring
  · -- hquad
    intro τ hτ θ hθ
    have hev : (fun z : ℝ => -Work.Construction.Fstar (3 * α) z θ
          * (1 - Work.Stability.chi (z / 4))) =ᶠ[𝓝 (0 : ℝ)] (fun _ => (0 : ℝ)) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with z hz
      rw [Metric.mem_ball, Real.dist_eq] at hz
      have hz1 : |z| < 1 := by simpa using hz
      have h4 : |z / 4| ≤ 1 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4), div_le_one (by norm_num)]
        linarith
      rw [Work.Stability.chi_eq_one h4]
      ring
    show Work.Spaces.pz (fun z θ => -Work.Construction.Fstar (3 * α) z θ
        * (1 - Work.Stability.chi (z / 4))) 0 θ = 0
    rw [Work.Spaces.pz]
    show deriv (fun z' : ℝ => -Work.Construction.Fstar (3 * α) z' θ
        * (1 - Work.Stability.chi (z' / 4))) 0 = 0
    rw [hev.deriv_eq]
    simp
  · -- hg
    exact ⟨2 * Cg * (2 * max Cc 1), hjetg⟩
  · -- hpz
    have hsum : Jet α 1 (2 * Cp * (2 * max Cc 1) + 2 * Cg * (2 * max Cc 1))
        (fun z θ _ => (-(Work.Spaces.pz (Work.Construction.Fstar (3 * α)) z θ))
            * (1 - Work.Stability.chi (z / 4))
          + (-(Work.Construction.Fstar (3 * α) z θ))
            * deriv (fun z' : ℝ => 1 - Work.Stability.chi (z' / 4)) z) :=
      Jet.add (Jet.mul (Jet.neg hjetpzF) hjetPh) (Jet.mul (Jet.neg hjetF) hjetDPh)
    refine ⟨2 * Cp * (2 * max Cc 1) + 2 * Cg * (2 * max Cc 1), ?_⟩
    refine Jet.congr hsum (fun z θ τ hz hθ hτ => ?_)
    show (-(Work.Spaces.pz (Work.Construction.Fstar (3 * α)) z θ))
          * (1 - Work.Stability.chi (z / 4))
        + (-(Work.Construction.Fstar (3 * α) z θ))
          * deriv (fun z' : ℝ => 1 - Work.Stability.chi (z' / 4)) z
      = Work.Spaces.pz (fun z θ => -Work.Construction.Fstar (3 * α) z θ
          * (1 - Work.Stability.chi (z / 4))) z θ
    exact (pz_slice_eq α z θ hz).symm
  · -- hgdoth
    refine ⟨0, le_rfl, ?_, ?_⟩
    · intro z θ τ hz hθ hτ
      have h : deriv (fun _ : ℝ => -Work.Construction.Fstar (3 * α) z θ
          * (1 - Work.Stability.chi (z / 4))) τ = 0 := by rw [deriv_const]
      show |deriv (fun s : ℝ => -Work.Construction.Fstar (3 * α) z θ
          * (1 - Work.Stability.chi (z / 4))) τ| ≤ 0
      rw [h, abs_zero]
    · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
      show |deriv (fun s : ℝ => -Work.Construction.Fstar (3 * α) z θ
            * (1 - Work.Stability.chi (z / 4))) τ
          - deriv (fun s : ℝ => -Work.Construction.Fstar (3 * α) z' θ'
            * (1 - Work.Stability.chi (z' / 4))) τ'| ≤ 0 * _
      rw [deriv_const, deriv_const]
      simp
  · -- hvan
    refine ⟨Cg, hCg0, fun τ hτ z θ hz hθ => ?_⟩
    have h1 : |(-Work.Construction.Fstar (3 * α) z θ) * (1 - Work.Stability.chi (z / 4))|
        = |Work.Construction.Fstar (3 * α) z θ| * |1 - Work.Stability.chi (z / 4)| := by
      rw [abs_mul, abs_neg]
    rw [h1]
    have h2 : |(1 : ℝ) - Work.Stability.chi (z / 4)| ≤ 1 := by
      have ha := Work.Stability.chi_nonneg (z / 4)
      have hb := Work.Stability.chi_le_one (z / 4)
      rw [abs_of_nonneg (by linarith)]
      linarith
    have h3 := hFb z θ hz hθ
    calc |Work.Construction.Fstar (3 * α) z θ| * |1 - Work.Stability.chi (z / 4)|
        ≤ (Cg * Work.FTS.Regularity.Gamma α θ) * 1 :=
          mul_le_mul h3 h2 (abs_nonneg _) (mul_nonneg hCg0 (hGN θ hθ))
      _ = Cg * Work.FTS.Regularity.Gamma α θ := by ring
  · -- htay
    refine ⟨0, le_rfl, fun τ hτ θ hθ => ⟨?_, ?_, ?_⟩⟩
    · intro z hz hz2
      have h4 : |z / 4| ≤ 1 := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ z / 4), div_le_one (by norm_num)]
        linarith
      have hz0 : -Work.Construction.Fstar (3 * α) z θ * (1 - Work.Stability.chi (z / 4)) = 0 := by
        rw [Work.Stability.chi_eq_one h4]
        ring
      rw [hz0, abs_zero]
      simp
    · intro z z' hz hz2 hz' hz2'
      have h4 : |z / 4| ≤ 1 := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ z / 4), div_le_one (by norm_num)]
        linarith
      have h4' : |z' / 4| ≤ 1 := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ z' / 4), div_le_one (by norm_num)]
        linarith
      have hz0 : -Work.Construction.Fstar (3 * α) z θ * (1 - Work.Stability.chi (z / 4)) = 0 := by
        rw [Work.Stability.chi_eq_one h4]
        ring
      have hz0' : -Work.Construction.Fstar (3 * α) z' θ * (1 - Work.Stability.chi (z' / 4)) = 0 := by
        rw [Work.Stability.chi_eq_one h4']
        ring
      rw [hz0, hz0']
      simp
    · intro z hz hz2 θ' hθ'
      have h4 : |z / 4| ≤ 1 := by
        rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ z / 4), div_le_one (by norm_num)]
        linarith
      have hz0 : -Work.Construction.Fstar (3 * α) z θ * (1 - Work.Stability.chi (z / 4)) = 0 := by
        rw [Work.Stability.chi_eq_one h4]
        ring
      have hz0' : -Work.Construction.Fstar (3 * α) z θ' * (1 - Work.Stability.chi (z / 4)) = 0 := by
        rw [Work.Stability.chi_eq_one h4]
        ring
      rw [hz0, hz0']
      simp
  · -- hsupp
    refine ⟨8, by norm_num, fun τ hτ z θ hz => ?_⟩
    have h2 : 2 ≤ |z / 4| := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ z / 4),
        le_div_iff₀ (by norm_num : (0 : ℝ) < 4)]
      linarith
    show Work.Construction.Fstar (3 * α) z θ
        + (-Work.Construction.Fstar (3 * α) z θ * (1 - Work.Stability.chi (z / 4))) = 0
    rw [Work.Stability.chi_eq_zero h2]
    ring
  · -- hH4
    intro τ hτ
    show Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 4
      (fun z θ => -Work.Construction.Fstar (3 * α) z θ * (1 - Work.Stability.chi (z / 4)))
    exact hH4fun
  · -- hcont
    intro θ hθ
    have hF' : ContDiffOn ℝ 1 (fun z : ℝ => Work.Construction.Fstar (3 * α) z θ)
        (Set.Ioi (-1)) := by
      have h1 : ContDiffOn ℝ 1 (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi (-1)) := by
        simp only [Work.FM.Fstar]
        refine ContDiffOn.div (contDiffOn_const.mul contDiff_id.contDiffOn)
          ((contDiffOn_const.add contDiff_id.contDiffOn).pow 2) (fun z hz => ?_)
        have hz' : (0 : ℝ) < 1 + z := by
          rw [Set.mem_Ioi] at hz
          linarith
        exact pow_ne_zero 2 (by positivity)
      have h2 : ContDiffOn ℝ 1 (fun z : ℝ => ((3 * α)
            * (Work.Spaces.Gam (3 * α) θ / Work.Spaces.c (3 * α))) * Work.FM.Fstar z)
          (Set.Ioi (-1)) :=
        contDiffOn_const.mul h1
      simpa only [Work.Construction.Fstar, mul_assoc] using h2
    have hPh : ContDiffOn ℝ 1 (fun z : ℝ => 1 - Work.Stability.chi (z / 4)) (Set.Ioi (-1)) := by
      have hchi : ContDiff ℝ (1 : WithTop ℕ∞) Work.Stability.chi :=
        Work.Stability.chi_contDiff.of_le (by simp)
      have hcomp : ContDiff ℝ (1 : WithTop ℕ∞) (fun z : ℝ => Work.Stability.chi (z / 4)) :=
        hchi.comp (contDiff_id.div_const 4)
      exact contDiffOn_const.sub hcomp.contDiffOn
    have hz : ContDiffOn ℝ 1 (fun z : ℝ => -Work.Construction.Fstar (3 * α) z θ
        * (1 - Work.Stability.chi (z / 4))) (Set.Ioi (-1)) := hF'.neg.mul hPh
    have hpr : ContDiffOn ℝ 1 (fun q : ℝ × ℝ => q.1)
        (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (1 + 1)) := contDiffOn_fst
    have hcomp := hz.comp hpr (fun q hq => hq.1)
    simpa only [Function.comp_def] using hcomp

end Work.FTS.Regularity
