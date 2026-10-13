/-
Copyright: work module for the Elgindi finite-time singularity project.

# Radial integration by parts in the weight `w²` (`D_z = z ∂_z`)

This file proves `Work.EllipticEst.Core.radialPairIBP`, the radial integration by parts
used in the coercivity/elliptic estimates of the paper (Elgindi, Annals 194 (3) 2021).

For `0 < a < b`, `φ` of class `C²` and `ψ` of class `C¹` on `(0,∞)`, both supported in the
compact interval `[a,b] ⊂ (0,∞)`, and with `w(z) = (1+z)²/z²`:

  `∫_0^∞ w² (zφ') (zψ') dz = - ∫_0^∞ w² (z (zφ')' + ((z-3)/(1+z)) (zφ')) ψ dz`.

Both sides are plain integration by parts for the flux
`Φ = w² · (zφ') · z · ψ`: by the fundamental theorem of calculus `∫_a^b Φ' = Φ(b) - Φ(a) = 0`
(here `ψ a = ψ b = 0`) and
`Φ' = w²·(zφ')·(zψ') + (w² (zφ') z)' · ψ`, while the algebraic identity

  `d/dz (w² (zφ') z) = w² · (z (zφ')' + ((z-3)/(1+z)) (zφ'))`

uses only `(w²)'/w² = -4/(z(1+z))`, i.e. the elementary computation
`d/dz (w(z)² z) = w(z)² (z-3)/(1+z)`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core

set_option autoImplicit false
noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Three elementary one-dimensional lemmas -/

/-- A function which vanishes on a neighbourhood of `x` has vanishing derivative there. -/
lemma deriv_eq_zero_of_eventuallyEq_zero {f : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] 0) :
    deriv f x = 0 := by
  have h' := h.deriv_eq
  simpa using h'

/-- For `z > 0`: `d/dz (w(z)² · z) = w(z)² · (z-3)/(1+z)`, where `w(z) = (1+z)²/z²`.
(Indeed `w(z)² z = (1+z)⁴/z³`.) -/
lemma hasDerivAt_w_sq_mul_id {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun y : ℝ => (Work.Spaces.w y) ^ 2 * y)
      ((Work.Spaces.w z) ^ 2 * ((z - 3) / (1 + z))) z := by
  have hA : HasDerivAt (fun y : ℝ => (1 + y) ^ 2 / y ^ 2)
      (2 * (1 + z) / z ^ 2 - 2 * (1 + z) ^ 2 / z ^ 3) z := by
    have hnum : HasDerivAt (fun y : ℝ => (1 + y) ^ 2) (2 * (1 + z)) z := by
      have h := ((hasDerivAt_id z).const_add 1).pow 2
      convert h using 1
      · ext y; simp [Pi.pow_apply]
      · simp
    have hden : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by
      have h := (hasDerivAt_id z).pow 2
      convert h using 1
      · ext y; simp [Pi.pow_apply]
      · simp
    have hdiv := hnum.div hden (by positivity : (z ^ 2) ≠ 0)
    convert hdiv using 1
    field_simp
  have h := (hA.pow 2).mul (hasDerivAt_id z)
  convert h using 1
  · ext y; simp only [Work.Spaces.w, Pi.pow_apply, Pi.mul_apply, id_eq]
  · simp only [Work.Spaces.w, Pi.pow_apply, id_eq]
    norm_num
    have h1 : z ≠ 0 := ne_of_gt hz
    have h2 : (1 : ℝ) + z ≠ 0 := by linarith
    field_simp [h1, h2]
    ring

/-- If `φ` is `C²` on `(0,∞)` then `y ↦ y φ'(y)` is differentiable at every `z > 0`,
with derivative `deriv (fun y => y * deriv φ y) z`. -/
lemma hasDerivAt_id_mul_deriv {φ : ℝ → ℝ} (hφ : ContDiffOn ℝ 2 φ (Set.Ioi (0:ℝ)))
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun y : ℝ => y * deriv φ y) (deriv (fun y : ℝ => y * deriv φ y) z) z := by
  have h1 : ContDiffOn ℝ 1 (deriv φ) (Set.Ioi (0:ℝ)) :=
    hφ.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have h2 : DifferentiableOn ℝ (deriv φ) (Set.Ioi (0:ℝ)) := h1.differentiableOn (by norm_num)
  have h3 : DifferentiableOn ℝ (fun y : ℝ => y * deriv φ y) (Set.Ioi (0:ℝ)) :=
    differentiableOn_id.mul h2
  exact h3.hasDerivAt (isOpen_Ioi.mem_nhds hz)

/-- If `f` vanishes on the part of `[0,∞)` lying outside `[a,b]` (with `0 < a ≤ b`), then
its integral over `[0,∞)` is its integral over the interval `[a,b]`. -/
lemma setIntegral_Ici_eq_intervalIntegral_of_support {f : ℝ → ℝ} {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hf : ∀ z, 0 ≤ z → (z < a ∨ b < z) → f z = 0) :
    (∫ z in Set.Ici (0 : ℝ), f z) = ∫ z in a..b, f z := by
  have h1 : (∫ z in Set.Ici (0 : ℝ), f z) = ∫ z in Set.Icc a b, f z :=
    MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ici
      (fun x hx => le_trans (le_of_lt ha) hx.1)
      (fun x hx => by
        refine hf x hx.1 ?_
        by_contra hcon
        rw [not_or] at hcon
        exact hx.2 ⟨not_lt.mp hcon.1, not_lt.mp hcon.2⟩)
  rw [h1, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]

/-! ## The main lemma -/

theorem radialPairIBP : ∀ {a b : ℝ}, 0 < a → a < b → ∀ φ ψ : ℝ → ℝ,
    ContDiffOn ℝ 2 φ (Set.Ioi (0:ℝ)) → ContDiffOn ℝ 1 ψ (Set.Ioi (0:ℝ)) →
    (∀ z : ℝ, z ∉ Set.Icc a b → φ z = 0) → (∀ z : ℝ, z ∉ Set.Icc a b → ψ z = 0) →
    (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * (z * deriv φ z) * (z * deriv ψ z))
      = - ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (z * deriv (fun y : ℝ => y * deriv φ y) z
              + (z - 3) / (1 + z) * (z * deriv φ z)) * ψ z := by
  intro a b ha hab φ ψ hφ hψ hφs hψs
  have hab' : a ≤ b := hab.le
  -- ## The support of `φ` and `ψ`
  have hmem : ∀ z : ℝ, z ∉ Set.Icc a b ↔ (z < a ∨ b < z) := by
    intro z
    constructor
    · intro h
      rcases lt_or_ge z a with h' | h'
      · exact Or.inl h'
      · refine Or.inr ?_
        by_contra h''
        exact h ⟨h', not_lt.mp h''⟩
    · rintro (h' | h') ⟨h1, h2⟩
      · exact absurd h1 (not_le.mpr h')
      · exact absurd h2 (not_le.mpr h')
  have hφzero : ∀ z : ℝ, z < a ∨ b < z → φ z = 0 := fun z hz => hφs z ((hmem z).mpr hz)
  have hψzero : ∀ z : ℝ, z < a ∨ b < z → ψ z = 0 := fun z hz => hψs z ((hmem z).mpr hz)
  -- ## All the derivatives vanish off `[a,b]`
  have hdφ : ∀ z : ℝ, z < a ∨ b < z → deriv φ z = 0 := by
    intro z hz
    refine deriv_eq_zero_of_eventuallyEq_zero ?_
    rcases hz with hz | hz
    · filter_upwards [isOpen_Iio.mem_nhds hz] with y hy
      exact hφzero y (Or.inl hy)
    · filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      exact hφzero y (Or.inr hy)
  have hdψ : ∀ z : ℝ, z < a ∨ b < z → deriv ψ z = 0 := by
    intro z hz
    refine deriv_eq_zero_of_eventuallyEq_zero ?_
    rcases hz with hz | hz
    · filter_upwards [isOpen_Iio.mem_nhds hz] with y hy
      exact hψzero y (Or.inl hy)
    · filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      exact hψzero y (Or.inr hy)
  have hdg : ∀ z : ℝ, z < a ∨ b < z → deriv (fun y : ℝ => y * deriv φ y) z = 0 := by
    intro z hz
    refine deriv_eq_zero_of_eventuallyEq_zero ?_
    rcases hz with hz | hz
    · filter_upwards [isOpen_Iio.mem_nhds hz] with y hy
      rw [hdφ y (Or.inl hy)]; simp
    · filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
      rw [hdφ y (Or.inr hy)]; simp
  -- ## Regularity consequences used for the fundamental theorem of calculus
  have hsub : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun x hx => lt_of_lt_of_le ha hx.1
  have hderivφ : ContDiffOn ℝ 1 (deriv φ) (Set.Ioi (0 : ℝ)) :=
    hφ.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hg1 : ContDiffOn ℝ 1 (fun y : ℝ => y * deriv φ y) (Set.Ioi (0 : ℝ)) :=
    contDiffOn_id.mul hderivφ
  have hcφ : ContinuousOn (deriv φ) (Set.Icc a b) := hderivφ.continuousOn.mono hsub
  have hcg : ContinuousOn (deriv (fun y : ℝ => y * deriv φ y)) (Set.Icc a b) :=
    (hg1.continuousOn_deriv_of_isOpen isOpen_Ioi (le_refl 1)).mono hsub
  have hcψ : ContinuousOn ψ (Set.Icc a b) := hψ.continuousOn.mono hsub
  have hcψd : ContinuousOn (deriv ψ) (Set.Icc a b) :=
    (hψ.continuousOn_deriv_of_isOpen isOpen_Ioi (le_refl 1)).mono hsub
  have hcw : ContinuousOn Work.Spaces.w (Set.Icc a b) := by
    show ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Icc a b)
    refine ContinuousOn.div (by fun_prop) (by fun_prop) (fun z hz => ?_)
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le ha hz.1))
  -- ## The two integrands and the two functions entering the integration by parts
  set F1 : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * (z * deriv φ z) * (z * deriv ψ z)
    with hF1def
  set F2 : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2
      * (z * deriv (fun y : ℝ => y * deriv φ y) z
          + (z - 3) / (1 + z) * (z * deriv φ z)) * ψ z with hF2def
  set u : ℝ → ℝ := fun y => (Work.Spaces.w y) ^ 2 * y * (y * deriv φ y) with hudef
  set u' : ℝ → ℝ := fun y => (Work.Spaces.w y) ^ 2
      * (y * deriv (fun y : ℝ => y * deriv φ y) y
          + (y - 3) / (1 + y) * (y * deriv φ y)) with hu'def
  -- ## `F1` and `F2` vanish off `[a,b]`
  have hF1supp : ∀ z : ℝ, 0 ≤ z → (z < a ∨ b < z) → F1 z = 0 := by
    intro z _ hz
    simp only [hF1def]
    rcases hz with hz | hz
    · rw [hdφ z (Or.inl hz)]; ring
    · rw [hdφ z (Or.inr hz)]; ring
  have hF2supp : ∀ z : ℝ, 0 ≤ z → (z < a ∨ b < z) → F2 z = 0 := by
    intro z _ hz
    simp only [hF2def]
    rcases hz with hz | hz
    · rw [hdφ z (Or.inl hz), hdg z (Or.inl hz), hψzero z (Or.inl hz)]; ring
    · rw [hdφ z (Or.inr hz), hdg z (Or.inr hz), hψzero z (Or.inr hz)]; ring
  -- ## The derivative of `u`
  have hu_deriv : ∀ x ∈ Set.uIcc a b, HasDerivAt u (u' x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab'] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have h := (hasDerivAt_w_sq_mul_id hx0).mul (hasDerivAt_id_mul_deriv hφ hx0)
    have hfun : u = (fun y : ℝ => (Work.Spaces.w y) ^ 2 * y)
        * (fun y : ℝ => y * deriv φ y) := by
      funext y
      simp only [hudef, Pi.mul_apply]
    have hval : u' x = (Work.Spaces.w x) ^ 2 * ((x - 3) / (1 + x)) * (x * deriv φ x)
        + ((Work.Spaces.w x) ^ 2 * x) * deriv (fun y : ℝ => y * deriv φ y) x := by
      simp only [hu'def]
      ring
    rw [hfun, hval]
    exact h
  -- ## Integrability of the two factors
  have hu'cont : ContinuousOn u' (Set.Icc a b) := by
    rw [hu'def]
    have hbracket : ContinuousOn (fun y : ℝ =>
        y * deriv (fun t : ℝ => t * deriv φ t) y + (y - 3) / (1 + y) * (y * deriv φ y))
        (Set.Icc a b) := by
      refine ContinuousOn.add (continuousOn_id.mul hcg) ?_
      refine ContinuousOn.mul ?_ (continuousOn_id.mul hcφ)
      exact ContinuousOn.div (continuousOn_id.sub continuousOn_const)
        (continuousOn_const.add continuousOn_id) (fun y hy => by
          have : (0 : ℝ) < y := lt_of_lt_of_le ha hy.1
          linarith)
    convert (hcw.pow 2).mul hbracket using 1
  have hu'int : IntervalIntegrable u' volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab' hu'cont
  have hψint : IntervalIntegrable (deriv ψ) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab' hcψd
  have hψ_deriv : ∀ x ∈ Set.uIcc a b, HasDerivAt ψ (deriv ψ x) x := by
    intro x hx
    rw [Set.uIcc_of_le hab'] at hx
    exact (hψ.differentiableOn (by norm_num)).hasDerivAt
      (isOpen_Ioi.mem_nhds (lt_of_lt_of_le ha hx.1))
  have hIBP := intervalIntegral.integral_deriv_mul_eq_sub hu_deriv hψ_deriv hu'int hψint
  -- ## The boundary terms vanish because `ψ a = ψ b = 0`
  have hψa : ψ a = 0 := by
    have hcont : ContinuousAt ψ a := hψ.continuousOn.continuousAt (isOpen_Ioi.mem_nhds ha)
    have h1 : Tendsto ψ (𝓝[<] a) (𝓝 (ψ a)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hev : ψ =ᶠ[𝓝[<] a] 0 := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hψzero z (Or.inl hz)
    have h2 : Tendsto ψ (𝓝[<] a) (𝓝 0) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[<] a) (𝓝 0)).congr' hev.symm
    exact tendsto_nhds_unique h1 h2
  have hψb : ψ b = 0 := by
    have hb0 : 0 < b := lt_of_lt_of_le ha hab'
    have hcont : ContinuousAt ψ b := hψ.continuousOn.continuousAt (isOpen_Ioi.mem_nhds hb0)
    have h1 : Tendsto ψ (𝓝[>] b) (𝓝 (ψ b)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hev : ψ =ᶠ[𝓝[>] b] 0 := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact hψzero z (Or.inr hz)
    have h2 : Tendsto ψ (𝓝[>] b) (𝓝 0) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] b) (𝓝 0)).congr' hev.symm
    exact tendsto_nhds_unique h1 h2
  have hbdy : u b * ψ b - u a * ψ a = 0 := by rw [hψb, hψa]; ring
  rw [hbdy] at hIBP
  -- ## Continuity and integrability of `F1`, `F2`
  have hF1cont : ContinuousOn F1 (Set.Icc a b) := by
    rw [hF1def]
    convert ((hcw.pow 2).mul (continuousOn_id.mul hcφ)).mul
      (continuousOn_id.mul hcψd) using 1
    ext z; simp only [Pi.pow_apply, Pi.mul_apply, id_eq]
  have hF2cont : ContinuousOn F2 (Set.Icc a b) := by
    have hF2eq : F2 = u' * ψ := by
      funext z
      simp only [hF2def, hu'def, Pi.mul_apply]
    rw [hF2eq]
    exact hu'cont.mul hcψ
  have hF1int : IntervalIntegrable F1 volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab' hF1cont
  have hF2int : IntervalIntegrable F2 volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab' hF2cont
  -- ## The two integrands of the fundamental theorem
  have hcongr : (∫ x in a..b, u' x * ψ x + u x * deriv ψ x)
      = ∫ x in a..b, (F2 x + F1 x) := by
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    simp only [hF1def, hF2def, hudef, hu'def]
    ring
  have hzero : (∫ x in a..b, F2 x) + (∫ x in a..b, F1 x) = 0 := by
    rw [← intervalIntegral.integral_add hF2int hF1int, ← hcongr]
    exact hIBP
  have hkey : (∫ x in a..b, F1 x) = - ∫ x in a..b, F2 x := by linarith
  -- ## Replacing the integrals over `[0,∞)` by interval integrals
  have hL : (∫ z in Work.Spaces.Iz, F1 z) = ∫ z in a..b, F1 z :=
    setIntegral_Ici_eq_intervalIntegral_of_support ha hab' hF1supp
  have hR : (∫ z in Work.Spaces.Iz, F2 z) = ∫ z in a..b, F2 z :=
    setIntegral_Ici_eq_intervalIntegral_of_support ha hab' hF2supp
  change (∫ z in Work.Spaces.Iz, F1 z) = - ∫ z in Work.Spaces.Iz, F2 z
  rw [hL, hR]
  exact hkey

end

end Work.EllipticEst.Core
