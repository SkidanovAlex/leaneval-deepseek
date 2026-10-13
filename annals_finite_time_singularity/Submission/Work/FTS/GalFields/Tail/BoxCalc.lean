/-
# `FTS/GalFields/Tail/BoxCalc` — integrals over the interior boxes `[a,b] × [δ,π/2-δ]`

This module provides the elementary `L¹`/`L²` calculus over a box
`bx a b δ = [a,b] × [δ,π/2-δ]` (with `0 < a` and `0 < δ < π/2-δ`, so that the box is compactly
contained in the open quadrant) which is used by the per-mode bound
(`Tail/perMode_of_slotDom`): the per-slot integration by parts transfers the derivatives of the
first factor onto a compactly supported test function, so that the pairing is dominated by the
`L¹`-integral of the first factor over the box, and that integral is then bounded term by term.

The two functionals are

* `binL1 a b δ f = ∫ p in bx a b δ, |f p.1 p.2|` (the `L¹`-norm over the box),
* `binL2 a b δ f = ∫ p in bx a b δ, (f p.1 p.2)^2` (the squared `L²`-norm over the box).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.Galerkin.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.GalFields.Tail

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- The interior box `[a,b] × [δ,π/2-δ]` of the `(z,θ)`-plane.  For `0 < a` and `0 < δ < π/2-δ`
it is a compact subset of the open quadrant on which all the weights `w`, `sin(2θ)^{-q}` of the
chapter are bounded above and below by positive constants. -/
def bx (a b δ : ℝ) : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc δ (π / 2 - δ)

theorem isCompact_bx (a b δ : ℝ) : IsCompact (bx a b δ) :=
  isCompact_Icc.prod isCompact_Icc

theorem measurableSet_bx (a b δ : ℝ) : MeasurableSet (bx a b δ) :=
  measurableSet_Icc.prod measurableSet_Icc

theorem volume_bx_ne_top (a b δ : ℝ) : volume (bx a b δ) ≠ ⊤ :=
  (isCompact_bx a b δ).measure_lt_top.ne

theorem mem_bx {a b δ z θ : ℝ} : (z, θ) ∈ bx a b δ ↔ z ∈ Set.Icc a b ∧ θ ∈ Set.Icc δ (π / 2 - δ) :=
  Iff.rfl

theorem bx_subset_Q0 {a b δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (hδ2 : δ < π / 2) :
    bx a b δ ⊆ Work.FTS.EllipticEst.Q0 := by
  rintro ⟨z, θ⟩ ⟨hz, hθ⟩
  refine Work.FTS.EllipticEst.mem_Q0.mpr ⟨lt_of_lt_of_le ha hz.1, lt_of_lt_of_le hδ hθ.1, ?_⟩
  exact lt_of_le_of_lt hθ.2 (by linarith)

theorem bx_subset_dom {a b δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) (hδ3 : δ ≤ π / 2) :
    bx a b δ ⊆ Work.Spaces.Iz ×ˢ Work.Spaces.Iθ := by
  rintro ⟨z, θ⟩ ⟨hz, hθ⟩
  refine ⟨?_, ?_⟩
  · simp only [Work.Spaces.Iz, Set.mem_Ici]; linarith [hz.1]
  · simp only [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩

/-- The `L¹`-integral of `f` over the box. -/
def binL1 (a b δ : ℝ) (f : Fn) : ℝ := ∫ p in bx a b δ, |f p.1 p.2|

/-- The squared `L²`-integral of `f` over the box. -/
def binL2 (a b δ : ℝ) (f : Fn) : ℝ := ∫ p in bx a b δ, f p.1 p.2 ^ 2

theorem binL1_nonneg (a b δ : ℝ) (f : Fn) : 0 ≤ binL1 a b δ f :=
  integral_nonneg fun p => abs_nonneg _

theorem binL2_nonneg (a b δ : ℝ) (f : Fn) : 0 ≤ binL2 a b δ f :=
  integral_nonneg fun p => sq_nonneg _

theorem binL1_congr {a b δ : ℝ} {f g : Fn} (h : ∀ z θ, f z θ = g z θ) :
    binL1 a b δ f = binL1 a b δ g := by
  refine MeasureTheory.setIntegral_congr_fun (measurableSet_bx a b δ) ?_
  rintro ⟨z, θ⟩ _
  show |f z θ| = |g z θ|
  rw [h z θ]

theorem binL2_congr {a b δ : ℝ} {f g : Fn} (h : ∀ z θ, f z θ = g z θ) :
    binL2 a b δ f = binL2 a b δ g := by
  refine MeasureTheory.setIntegral_congr_fun (measurableSet_bx a b δ) ?_
  rintro ⟨z, θ⟩ _
  show f z θ ^ 2 = g z θ ^ 2
  rw [h z θ]

/-! ## Integrability of continuous functions on the box -/

theorem integrableOn_bx_of_continuousOn {a b δ : ℝ} {f : Fn}
    (hf : ContinuousOn (Function.uncurry f) (bx a b δ)) :
    IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (bx a b δ) :=
  hf.integrableOn_compact (isCompact_bx a b δ)

/-- Integrability on the box of any continuous function of the two variables. -/
theorem integrableOn_bx_of_continuousOn' {a b δ : ℝ} {g : ℝ × ℝ → ℝ}
    (hg : ContinuousOn g (bx a b δ)) : IntegrableOn g (bx a b δ) :=
  hg.integrableOn_compact (isCompact_bx a b δ)

/-! ## Additivity and scalar rules -/

/-- The `L¹`-integral over the box is subadditive. -/
theorem binL1_add_le {a b δ : ℝ} {f g : Fn}
    (hf : IntegrableOn (fun p : ℝ × ℝ => |f p.1 p.2|) (bx a b δ))
    (hg : IntegrableOn (fun p : ℝ × ℝ => |g p.1 p.2|) (bx a b δ))
    (hfg : IntegrableOn (fun p : ℝ × ℝ => |f p.1 p.2 + g p.1 p.2|) (bx a b δ)) :
    binL1 a b δ (fun z θ => f z θ + g z θ) ≤ binL1 a b δ f + binL1 a b δ g := by
  have hsum : IntegrableOn (fun p : ℝ × ℝ => |f p.1 p.2| + |g p.1 p.2|) (bx a b δ) :=
    hf.add hg
  calc binL1 a b δ (fun z θ => f z θ + g z θ)
      ≤ ∫ p in bx a b δ, (|f p.1 p.2| + |g p.1 p.2|) :=
        MeasureTheory.setIntegral_mono_on hfg hsum (measurableSet_bx a b δ)
          (fun p _ => abs_add_le _ _)
    _ = binL1 a b δ f + binL1 a b δ g := by
        rw [binL1, binL1, MeasureTheory.integral_add hf hg]

/-- The `L¹`-integral over the box of a negative is the same. -/
theorem binL1_neg {a b δ : ℝ} (f : Fn) : binL1 a b δ (fun z θ => -f z θ) = binL1 a b δ f := by
  rw [binL1, binL1]
  refine MeasureTheory.setIntegral_congr_fun (measurableSet_bx a b δ) ?_
  rintro ⟨z, θ⟩ _
  show |(-f z θ)| = |f z θ|
  rw [abs_neg]

/-- The squared `L²`-integral over the box of a scalar multiple. -/
theorem binL2_const_mul {a b δ c : ℝ} {f : Fn} :
    binL2 a b δ (fun z θ => c * f z θ) = c ^ 2 * binL2 a b δ f := by
  rw [binL2, binL2]
  calc ∫ p in bx a b δ, (c * f p.1 p.2) ^ 2
      = ∫ p in bx a b δ, c ^ 2 * f p.1 p.2 ^ 2 :=
        MeasureTheory.setIntegral_congr_fun (measurableSet_bx a b δ)
          (fun p _ => by ring)
    _ = c ^ 2 * ∫ p in bx a b δ, f p.1 p.2 ^ 2 := MeasureTheory.integral_const_mul _ _

/-- The `L¹`-integral over the box of a scalar multiple. -/
theorem binL1_const_mul_le {a b δ c : ℝ} {f : Fn} :
    binL1 a b δ (fun z θ => c * f z θ) ≤ |c| * binL1 a b δ f := by
  have h1 : binL1 a b δ (fun z θ => c * f z θ)
      = ∫ p in bx a b δ, |c| * |f p.1 p.2| := by
    rw [binL1]
    refine MeasureTheory.setIntegral_congr_fun (measurableSet_bx a b δ) ?_
    rintro ⟨z, θ⟩ _
    show |c * f z θ| = |c| * |f z θ|
    rw [abs_mul]
  rw [h1, binL1]
  rw [MeasureTheory.integral_const_mul]

/-- The `L¹`-integral over the box is monotone in the integrand. -/
theorem binL1_mono {a b δ : ℝ} {f g : Fn}
    (hf : IntegrableOn (fun p : ℝ × ℝ => |f p.1 p.2|) (bx a b δ))
    (hg : IntegrableOn (fun p : ℝ × ℝ => |g p.1 p.2|) (bx a b δ))
    (h : ∀ p ∈ bx a b δ, |f p.1 p.2| ≤ |g p.1 p.2|) :
    binL1 a b δ f ≤ binL1 a b δ g :=
  MeasureTheory.setIntegral_mono_on hf hg (measurableSet_bx a b δ) h

/-- `∫_box (g / r) = (∫_box g) / r`. -/
theorem binL1_int_div {a b δ r : ℝ} {g : ℝ × ℝ → ℝ} :
    (∫ p in bx a b δ, g p / r) = (∫ p in bx a b δ, g p) / r :=
  MeasureTheory.integral_div r _

/-- **The box integral as an iterated integral**: for an integrable function on the box, the
(product-measure) box integral equals the iterated `z`-then-`θ` integral over the two intervals.
This is the bridge between `binL1` and the iterated integrals of the slot estimates. -/
theorem iterated_eq_binL1 {a b δ : ℝ} {f : Fn}
    (hf : IntegrableOn (fun p : ℝ × ℝ => |f p.1 p.2|) (bx a b δ)) :
    (∫ z in Set.Icc a b, ∫ θ in Set.Icc δ (π / 2 - δ), |f z θ|) = binL1 a b δ f := by
  have hprod : (volume.restrict (bx a b δ))
      = (volume.restrict (Set.Icc a b)).prod
          (volume.restrict (Set.Icc δ (π / 2 - δ))) := by
    rw [bx]
    exact (MeasureTheory.Measure.prod_restrict _ _).symm
  rw [binL1, hprod]
  rw [MeasureTheory.integral_prod _ (by rwa [← hprod])]

/-- `∫_box 1 = |box|`. -/
theorem binL1_int_one (a b δ : ℝ) :
    (∫ _p in bx a b δ, (1 : ℝ)) = (volume (bx a b δ)).toReal :=
  MeasureTheory.setIntegral_one_eq_measureReal

/-- **The `L¹`-norm over the box is dominated by the `L²`-norm plus the area**: the pointwise
`2|f| ≤ f² + 1`, integrated. -/
theorem binL1_le_binL2_add {a b δ : ℝ} {f : Fn}
    (hf : IntegrableOn (fun p : ℝ × ℝ => |f p.1 p.2|) (bx a b δ))
    (hf2 : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2 ^ 2) (bx a b δ)) :
    binL1 a b δ f ≤ (binL2 a b δ f + (volume (bx a b δ)).toReal) / 2 := by
  have hone : IntegrableOn (fun _ : ℝ × ℝ => (1 : ℝ)) (bx a b δ) :=
    integrableOn_const (volume_bx_ne_top a b δ)
  have hsum : IntegrableOn (fun p : ℝ × ℝ => (f p.1 p.2 ^ 2 + 1) / 2) (bx a b δ) :=
    (hf2.add hone).div_const 2
  have hpt : ∀ p : ℝ × ℝ, |f p.1 p.2| ≤ (f p.1 p.2 ^ 2 + 1) / 2 := by
    intro p
    nlinarith [sq_nonneg (|f p.1 p.2| - 1), abs_nonneg (f p.1 p.2), sq_abs (f p.1 p.2)]
  have hkey : (∫ p in bx a b δ, (f p.1 p.2 ^ 2 + 1) / 2)
      = (binL2 a b δ f + (volume (bx a b δ)).toReal) / 2 := by
    rw [binL1_int_div, MeasureTheory.integral_add hf2 hone, binL1_int_one, binL2]
  calc binL1 a b δ f ≤ ∫ p in bx a b δ, (f p.1 p.2 ^ 2 + 1) / 2 :=
        MeasureTheory.setIntegral_mono_on hf hsum (measurableSet_bx a b δ) (fun p _ => hpt p)
    _ = _ := hkey

/-- **The pairwise AM–GM bound**: `∫_box |f·g| ≤ (∫_box f² + ∫_box g²)/2`. -/
theorem binL1_mul_le {a b δ : ℝ} {f g : Fn}
    (hf : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2 ^ 2) (bx a b δ))
    (hg : IntegrableOn (fun p : ℝ × ℝ => g p.1 p.2 ^ 2) (bx a b δ))
    (hfg : IntegrableOn (fun p : ℝ × ℝ => |f p.1 p.2 * g p.1 p.2|) (bx a b δ)) :
    binL1 a b δ (fun z θ => f z θ * g z θ) ≤ (binL2 a b δ f + binL2 a b δ g) / 2 := by
  have hpt : ∀ p : ℝ × ℝ, |f p.1 p.2 * g p.1 p.2| ≤ (f p.1 p.2 ^ 2 + g p.1 p.2 ^ 2) / 2 := by
    intro p
    have h1 : 2 * (f p.1 p.2 * g p.1 p.2) ≤ f p.1 p.2 ^ 2 + g p.1 p.2 ^ 2 := by
      nlinarith [sq_nonneg (f p.1 p.2 - g p.1 p.2)]
    have h2 : -(f p.1 p.2 ^ 2 + g p.1 p.2 ^ 2) ≤ 2 * (f p.1 p.2 * g p.1 p.2) := by
      nlinarith [sq_nonneg (f p.1 p.2 + g p.1 p.2)]
    rw [abs_le]
    constructor <;> linarith
  have hsum : IntegrableOn
      (fun p : ℝ × ℝ => (f p.1 p.2 ^ 2 + g p.1 p.2 ^ 2) / 2) (bx a b δ) :=
    (hf.add hg).div_const 2
  have hkey : (∫ p in bx a b δ, (f p.1 p.2 ^ 2 + g p.1 p.2 ^ 2) / 2)
      = (binL2 a b δ f + binL2 a b δ g) / 2 := by
    rw [binL1_int_div, MeasureTheory.integral_add hf hg, binL2, binL2]
  calc binL1 a b δ (fun z θ => f z θ * g z θ)
      ≤ ∫ p in bx a b δ, (f p.1 p.2 ^ 2 + g p.1 p.2 ^ 2) / 2 := by
        exact MeasureTheory.setIntegral_mono_on hfg hsum (measurableSet_bx a b δ)
          (fun p _ => hpt p)
    _ = _ := hkey

/-- **The `L²`-integral over the box of a bounded function.** -/
theorem binL2_le_of_bound {a b δ B : ℝ} {f : Fn}
    (hf : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2 ^ 2) (bx a b δ))
    (h : ∀ p ∈ bx a b δ, |f p.1 p.2| ≤ B) :
    binL2 a b δ f ≤ B ^ 2 * (volume (bx a b δ)).toReal := by
  have hone : IntegrableOn (fun _ : ℝ × ℝ => B ^ 2) (bx a b δ) :=
    integrableOn_const (volume_bx_ne_top a b δ)
  calc binL2 a b δ f ≤ ∫ _p in bx a b δ, B ^ 2 := by
        refine MeasureTheory.setIntegral_mono_on hf hone (measurableSet_bx a b δ) ?_
        intro p hp
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (h p hp) 2
    _ = B ^ 2 * (volume (bx a b δ)).toReal := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_comm, MeasureTheory.Measure.real_def]

end Work.FTS.GalFields.Tail
