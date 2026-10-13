/-
# `Work.FTS.ClassCHon.CmpSupp.source_facts`

The basic facts about a source `F` of the elliptic node which is *globally* `C^∞` and supported
in a strip `[a,b]` of the radial variable with `0 < a`:

```
source_facts :  SmoothOpen F ∧ HkMem α 0 F
              ∧ (∀ z > 0, IntegrableOn (θ ↦ F z θ ^ 2 · cos θ) Iθ)
              ∧ (∀ z > 0, IntegrableOn (θ ↦ F z θ ^ 2 · σ θ) Iθ)
              ∧ IntegrableOn (p ↦ F p.1 p.2 ^ 2) Q0
```

where `σ = sEta = sin(2θ)^{-η}` with `η = 99/100` (so `σ` is integrable on `Iθ`), `Iθ = [0,π/2]`
and `Q0 = (0,∞) × (0,π/2)` is the open quadrant.

## Mathematics

Nothing here uses the elliptic structure: a globally `C^∞` function is `C^∞` on the open quadrant
(`hFsm.contDiffOn`), and the compact support in `z` makes every one of the five assertions
elementary.

* **the `ℋ⁰`-membership** (proved below).  At level `0` the `ℋ⁰`-integrand collapses to the single
  square `HkIntegrand α 0 F z θ = (F z θ · w(z) / sin(2θ)^{η/2})²` (`sf_HkIntegrand_zero_eq`); on
  `Iθ` this is `F z θ ^ 2 · w(z)² · σ θ` (`sf_Whz_sq_Iθ`, pure `rpow` algebra on the nonnegative
  base `sin(2θ)`).  The function `F` is bounded on the compact box `[a,b] × Iθ` (global
  continuity), `w(z)² = ((1+z)²/z²)²` is bounded there by `((1+b)²/a²)²` because `z ≥ a > 0`, and
  off the box `F` vanishes.  So the integrand is dominated by the separable majorant
  `srcMajorant a b Mc`, whose `θ`-slices are a constant times the (integrable) weight `σ` and
  whose slice integrals are the indicator of `[a,b]` times a constant, hence integrable on
  `Iz = [0,∞)`.  `Work.FTS.LocData.HkMem_of_majorant` turns this domination into `HkMem α 0 F`
  (it supplies all the Fubini/measurability bookkeeping).
* **the two slice facts and the `Q0`-integrability** are the delivered sibling
  `Work.FTS.ClassCHon.CmpSupp.src_int_facts` (conjuncts 3, 4, 5 of the statement), proved there by
  the compactness of `Iθ` resp. of the support box; they are consumed here rather than re-proved.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.ClassCHon.CmpSupp.src_int_facts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassCHon.CmpSupp

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Elementary facts about the angular weight `σ` -/

/-- `sin (2θ) ≥ 0` on the angular interval `Iθ = [0,π/2]`. -/
theorem sf_sin_two_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Real.sin (2 * θ) :=
  Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

/-- The angular weight `σ θ = sin(2θ)^{-η}` is integrable on `Iθ` (`η = 99/100 < 1`). -/
theorem sf_sEta_integrableOn :
    MeasureTheory.IntegrableOn Work.FTS.EllipticEst.sEta Work.Spaces.Iθ :=
  (Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
    (by norm_num [Work.Spaces.eta]) (by norm_num [Work.Spaces.eta])).1

/-- `(a ^ p) ^ 2 = a ^ (p * 2)` for `a ≥ 0`: the natural-number power on the left is converted
into a real one by `Real.rpow_natCast` before `Real.rpow_mul` is applied. -/
theorem sf_sq_rpow_mul_two {a : ℝ} (ha : 0 ≤ a) (p : ℝ) : (a ^ p) ^ 2 = a ^ (p * 2) := by
  rw [← Real.rpow_natCast (a ^ p) 2]
  exact (Real.rpow_mul ha p 2).symm

/-- **The square of the `i = 0` angular weight on `Iθ`**: `(w(z)/sin(2θ)^{η/2})² = w(z)²·σ(θ)`.
The only use of `θ ∈ Iθ` is the non-negativity of the base `sin(2θ)`; at the endpoints both sides
are `0` by Lean's totalised `rpow` and division. -/
theorem sf_Whz_sq_Iθ {z θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  have ha : 0 ≤ Real.sin (2 * θ) := sf_sin_two_nonneg_Iθ hθ
  have h1 : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg ha (Work.Spaces.eta / 2)]
  rw [h1, mul_pow, sf_sq_rpow_mul_two ha (-(Work.Spaces.eta / 2)),
    show (-(Work.Spaces.eta / 2)) * 2 = -Work.Spaces.eta by ring]
  rfl

/-- **The `ℋ⁰`-integrand collapses to a single square**: at level `k = 0` the mixed double sum of
`HkIntegrand` is empty (`1 ≤ 0` is false) and only the `i = 0` term of the `D_z`-sum survives. -/
theorem sf_HkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand]
  norm_num

/-! ## The separable majorant of the `ℋ⁰`-integrand

`srcMajorant a b Mc` is the constant `Mc` on the strip `[a,b]` (in `z`) times the angular weight
`σ`, and `0` off the strip.  It is the majorant used in `source_facts`: the `ℋ⁰`-integrand of a
source supported in `[a,b]` is below it (with `Mc` the bound of `F z θ ² w(z)²` on the box), its
`θ`-slices are integrable because `σ` is, and its slice integrals are the indicator of `[a,b]`
times a constant, hence integrable on `[0,∞)`. -/

/-- The majorant: `Mc · σ θ` for `z ∈ [a,b]` and `0` otherwise. -/
def srcMajorant (a b Mc : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => (if z ∈ Set.Icc a b then Mc else 0) * Work.FTS.EllipticEst.sEta θ

theorem srcMajorant_apply (a b Mc z θ : ℝ) :
    srcMajorant a b Mc z θ = (if z ∈ Set.Icc a b then Mc else 0) * Work.FTS.EllipticEst.sEta θ :=
  rfl

/-- The `θ`-slices of the majorant are integrable on `Iθ`. -/
theorem srcMajorant_integrable_slice (a b Mc : ℝ) :
    ∀ z ∈ Work.Spaces.Iz,
      MeasureTheory.IntegrableOn (fun θ => srcMajorant a b Mc z θ) Work.Spaces.Iθ := by
  intro z _
  rw [show (fun θ : ℝ => srcMajorant a b Mc z θ)
      = fun θ : ℝ => (if z ∈ Set.Icc a b then Mc else 0) * Work.FTS.EllipticEst.sEta θ
    from funext fun θ => srcMajorant_apply a b Mc z θ]
  by_cases hz : z ∈ Set.Icc a b
  · rw [show (fun θ : ℝ => (if z ∈ Set.Icc a b then Mc else 0) * Work.FTS.EllipticEst.sEta θ)
        = fun θ : ℝ => Mc * Work.FTS.EllipticEst.sEta θ from
      funext fun θ => by rw [ite_eq_left hz]]
    exact sf_sEta_integrableOn.const_mul Mc
  · rw [show (fun θ : ℝ => (if z ∈ Set.Icc a b then Mc else 0) * Work.FTS.EllipticEst.sEta θ)
        = fun _ => (0 : ℝ) from funext fun θ => by rw [ite_eq_right hz, zero_mul]]
    exact integrableOn_zero

/-- The `z`-integral of the majorant is integrable on `Iz`: it is the indicator of the finite
measure interval `[a,b]` times the constant `Mc · ∫_θ σ`. -/
theorem srcMajorant_integrable_z (a b Mc : ℝ) :
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, srcMajorant a b Mc z θ)
      Work.Spaces.Iz := by
  have hfun : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, srcMajorant a b Mc z θ)
      = fun z : ℝ => (if z ∈ Set.Icc a b then Mc else 0)
          * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ) := by
    funext z
    by_cases hz : z ∈ Set.Icc a b
    · rw [show (fun θ : ℝ => srcMajorant a b Mc z θ)
          = fun θ : ℝ => Mc * Work.FTS.EllipticEst.sEta θ from
        funext fun θ => by rw [srcMajorant_apply, ite_eq_left hz]]
      rw [MeasureTheory.integral_const_mul, ite_eq_left hz]
    · rw [show (fun θ : ℝ => srcMajorant a b Mc z θ) = fun _ => (0 : ℝ) from
        funext fun θ => by rw [srcMajorant_apply, ite_eq_right hz, zero_mul]]
      rw [integral_zero, ite_eq_right hz, zero_mul]
  rw [hfun]
  have hind : (fun z : ℝ => (if z ∈ Set.Icc a b then Mc else 0)
        * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ))
      = (Set.Icc a b).indicator
          (fun _ => Mc * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ)) := by
    funext z
    by_cases hz : z ∈ Set.Icc a b
    · rw [ite_eq_left hz, Set.indicator_of_mem hz]
    · rw [ite_eq_right hz, zero_mul, Set.indicator_of_notMem hz]
  rw [hind]
  have hconst : MeasureTheory.IntegrableOn
      (fun _ : ℝ => Mc * (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ))
      (Set.Icc a b) :=
    MeasureTheory.integrableOn_const (C := Mc * (∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.sEta θ)) (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  exact (((MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr hconst)).integrableOn

/-! ## The main theorem -/

theorem source_facts {α : ℝ} (hα : 0 < α) {a b : ℝ} (ha : 0 < a) {F : ℝ → ℝ → ℝ}
    (hFsm : ContDiff ℝ Work.Stability.smoothOrder (Function.uncurry F))
    (hsupp : ∀ z θ : ℝ, z ∉ Set.Icc a b → F z θ = 0) :
    Work.FTS.EllipticEst.SmoothOpen F
    ∧ Work.Spaces.HkMem α 0 F
    ∧ (∀ z ∈ Set.Ioi (0 : ℝ),
        MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Real.cos θ) Work.Spaces.Iθ)
    ∧ (∀ z ∈ Set.Ioi (0 : ℝ),
        MeasureTheory.IntegrableOn (fun θ => (F z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          Work.Spaces.Iθ)
    ∧ MeasureTheory.IntegrableOn (fun p : ℝ × ℝ => (F p.1 p.2) ^ 2)
        Work.FTS.EllipticEst.Q0 := by
  have hcont : Continuous (Function.uncurry F) := hFsm.continuous
  classical
  have hSmooth : Work.FTS.EllipticEst.SmoothOpen F := hFsm.contDiffOn
  -- the source is bounded on the compact box `[a,b] × Iθ`
  have hboxc : IsCompact (Set.Icc a b ×ˢ Work.Spaces.Iθ) :=
    isCompact_Icc.prod (show IsCompact (Set.Icc (0 : ℝ) (Real.pi / 2)) from isCompact_Icc)
  obtain ⟨C, hC⟩ := hboxc.exists_bound_of_continuousOn hcont.continuousOn
  set M : ℝ := max C 0 with hMdef
  have hFbd : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Work.Spaces.Iθ, |F z θ| ≤ M := by
    intro z hz θ hθ
    have h := hC (z, θ) (Set.mem_prod.mpr ⟨hz, hθ⟩)
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  -- the radial weight is bounded on `[a,b]` (`a > 0`)
  have hWbd : ∀ z ∈ Set.Icc a b,
      (Work.Spaces.w z) ^ 2 ≤ ((1 + b) ^ 2 / a ^ 2) ^ 2 := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := hz
    have hnum : (1 + z) ^ 2 ≤ (1 + b) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hden : a ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ (le_of_lt ha) hz1 2
    have h1 : Work.Spaces.w z ≤ (1 + b) ^ 2 / a ^ 2 := by
      rw [Work.Spaces.w]
      exact div_le_div₀ (by positivity) hnum (by positivity) hden
    exact pow_le_pow_left₀ (by rw [Work.Spaces.w]; positivity) h1 2
  obtain ⟨hcos, hsig, hbox⟩ := src_int_facts ha hFsm hsupp
  refine ⟨hSmooth, ?_, hcos, hsig, hbox⟩
  · -- ## membership in `ℋ⁰`, by domination with `srcMajorant`
    set Mc : ℝ := M ^ 2 * ((1 + b) ^ 2 / a ^ 2) ^ 2 with hMcdef
    have hle : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 F z θ ≤ srcMajorant a b Mc z θ := by
      intro z _ θ hθ
      rw [sf_HkIntegrand_zero_eq, mul_pow, sf_Whz_sq_Iθ hθ, srcMajorant_apply]
      have hsEta_nn : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
        Real.rpow_nonneg (sf_sin_two_nonneg_Iθ hθ) _
      by_cases hzab : z ∈ Set.Icc a b
      · rw [ite_eq_left hzab]
        have h1 : (F z θ) ^ 2 ≤ M ^ 2 := by
          have h := pow_le_pow_left₀ (abs_nonneg (F z θ)) (hFbd z hzab θ hθ) 2
          rwa [sq_abs] at h
        have h2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
        have h3 : (Work.Spaces.w z) ^ 2 ≤ ((1 + b) ^ 2 / a ^ 2) ^ 2 := hWbd z hzab
        have h4 : (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ Mc := by
          rw [hMcdef]
          exact mul_le_mul h1 h3 h2 (by positivity)
        calc (F z θ) ^ 2 * ((Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)
            = (F z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ := by ring
          _ ≤ Mc * Work.FTS.EllipticEst.sEta θ :=
              mul_le_mul_of_nonneg_right h4 hsEta_nn
      · rw [ite_eq_right hzab, zero_mul, hsupp z θ hzab]
        simp
    exact Work.FTS.LocData.HkMem_of_majorant α 0
      (hSmooth.continuousOn_HkIntegrand α 0)
      (srcMajorant_integrable_slice a b Mc) (srcMajorant_integrable_z a b Mc) hle

end Work.FTS.ClassCHon.CmpSupp
