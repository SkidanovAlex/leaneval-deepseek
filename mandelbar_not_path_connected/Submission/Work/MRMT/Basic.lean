/-
Copyright: Work.MRMT (mandelbar) subproject.
The measurable Riemann mapping theorem / Ahlfors–Bers theory: core definitions.

This file fixes the CONVENTIONS of the whole subproject.  Everything else in
`Submission/Work/MRMT/` imports it, and the consumer (`F`, the height-0 root-arc
parameter) states its theorems in the vocabulary defined here:

* `Work.MRMT.dz`, `Work.MRMT.dzbar`  — Wirtinger derivatives, computed from the real
  Fréchet derivative (junk value `0` where `f` is not real-differentiable);
* `Work.MRMT.beltramiOf g z = dzbar g z / dz g z` — the pointwise complex dilatation;
* `Work.MRMT.IsQCOn g U μ` — `g` is quasiconformal on the open set `U` with complex
  dilatation `μ` (analytic definition, a.e. on `U`);
* `Work.MRMT.Beltrami` — a *measurable* complex dilatation with `‖μ‖ ≤ k < 1` a.e.,
  bundled with its dilatation bound;
* `Work.MRMT.IsDbarDeriv`, `Work.MRMT.IsDzDeriv` — the weak (distributional)
  Wirtinger derivatives, used for Weyl's lemma and the Ahlfors–Bers construction;
* `Work.MRMT.hyperbolicSum` — the Möbius sum `(μ+ν)/(1+μ̄ν)` governing composition.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal

namespace Work.MRMT

/-! ## Wirtinger derivatives and the pointwise complex dilatation -/

/-- Wirtinger derivative `∂g/∂z = ½(Dg(1) - i Dg(i))`, from the real Fréchet derivative.
Junk value `0` where `g` is not real-differentiable. -/
def dz (g : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ g z 1 - Complex.I * fderiv ℝ g z Complex.I) / 2

/-- Wirtinger derivative `∂g/∂z̄ = ½(Dg(1) + i Dg(i))`, from the real Fréchet derivative.
Junk value `0` where `g` is not real-differentiable. -/
def dzbar (g : ℂ → ℂ) (z : ℂ) : ℂ := (fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I) / 2

/-- The pointwise complex dilatation `μ_g = (∂g/∂z̄)/(∂g/∂z)` (junk value `0` where
`∂g/∂z = 0`). -/
def beltramiOf (g : ℂ → ℂ) (z : ℂ) : ℂ := dzbar g z / dz g z

@[simp] theorem dz_zero (z : ℂ) : dz (fun _ : ℂ => (0 : ℂ)) z = 0 := by simp [dz]

@[simp] theorem dzbar_zero (z : ℂ) : dzbar (fun _ : ℂ => (0 : ℂ)) z = 0 := by simp [dzbar]

@[simp] theorem dz_id (z : ℂ) : dz (id : ℂ → ℂ) z = 1 := by simp [dz]

@[simp] theorem dzbar_id (z : ℂ) : dzbar (id : ℂ → ℂ) z = 0 := by simp [dzbar]

@[simp] theorem beltramiOf_id (z : ℂ) : beltramiOf (id : ℂ → ℂ) z = 0 := by
  simp [beltramiOf]

/-! ## Local `L²` and weak (distributional) derivatives -/

/-- `f` is locally square integrable on the set `U`. -/
def MemL2LocOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → IntegrableOn (fun z => ‖f z‖ ^ 2) (K ∩ U) volume

/-- `f` is locally square integrable on `ℂ`. -/
def MemL2Loc (f : ℂ → ℂ) : Prop := MemL2LocOn f Set.univ

/-- Weak (distributional) `∂̄`-derivative: `g = ∂̄ f` tested against smooth compactly
supported functions. -/
def IsDbarDeriv (f g : ℂ → ℂ) : Prop :=
  LocallyIntegrable f volume ∧ LocallyIntegrable g volume ∧
    ∀ φ : 𝓓(⊤, ℂ),
      Integrable (fun z => f z * dzbar (φ : ℂ → ℂ) z) ∧
      Integrable (fun z => g z * φ z) ∧
      ∫ z, f z * dzbar (φ : ℂ → ℂ) z = - ∫ z, g z * φ z

/-- Weak (distributional) `∂`-derivative. -/
def IsDzDeriv (f g : ℂ → ℂ) : Prop :=
  LocallyIntegrable f volume ∧ LocallyIntegrable g volume ∧
    ∀ φ : 𝓓(⊤, ℂ),
      Integrable (fun z => f z * dz (φ : ℂ → ℂ) z) ∧
      Integrable (fun z => g z * φ z) ∧
      ∫ z, f z * dz (φ : ℂ → ℂ) z = - ∫ z, g z * φ z

/-! ## Beltrami coefficients -/

/-- A Beltrami coefficient: a measurable field `μ` with `|μ| ≤ k < 1` almost everywhere,
bundled with a dilatation bound `k`. -/
structure Beltrami where
  /-- The coefficient as a function. -/
  toFun : ℂ → ℂ
  /-- Measurability. -/
  measurable : AEStronglyMeasurable toFun volume
  /-- The dilatation bound `k`. -/
  k : ℝ
  /-- `k ≥ 0`. -/
  k_nonneg : 0 ≤ k
  /-- `k < 1`. -/
  k_lt_one : k < 1
  /-- The a.e. bound. -/
  norm_le : ∀ᵐ z ∂volume, ‖toFun z‖ ≤ k

namespace Beltrami

instance : CoeFun Beltrami (fun _ => ℂ → ℂ) := ⟨Beltrami.toFun⟩

theorem norm_le_ae (μ : Beltrami) : ∀ᵐ z ∂volume, ‖μ z‖ ≤ μ.k := μ.norm_le

theorem norm_lt_one_ae (μ : Beltrami) : ∀ᵐ z ∂volume, ‖μ z‖ < 1 := by
  filter_upwards [μ.norm_le] with z hz
  exact lt_of_le_of_lt hz μ.k_lt_one

/-- The zero Beltrami coefficient. -/
def zero : Beltrami where
  toFun := fun _ => 0
  measurable := aestronglyMeasurable_const
  k := 0
  k_nonneg := le_refl 0
  k_lt_one := zero_lt_one
  norm_le := by simp

@[simp] theorem zero_apply (z : ℂ) : zero z = 0 := rfl

/-- A constant Beltrami coefficient of modulus `< 1`. -/
def const (c : ℂ) (hc : ‖c‖ < 1) : Beltrami where
  toFun := fun _ => c
  measurable := aestronglyMeasurable_const
  k := ‖c‖
  k_nonneg := norm_nonneg c
  k_lt_one := hc
  norm_le := by filter_upwards with z; simp

@[simp] theorem const_apply (c : ℂ) (hc : ‖c‖ < 1) (z : ℂ) : const c hc z = c := rfl

/-- Pointwise product of Beltrami coefficients; dilatation bound the product. -/
def mul (μ ν : Beltrami) : Beltrami where
  toFun := fun z => μ z * ν z
  measurable := μ.measurable.mul ν.measurable
  k := μ.k * ν.k
  k_nonneg := mul_nonneg μ.k_nonneg ν.k_nonneg
  k_lt_one := by
    have h₁ := μ.k_lt_one
    have h₂ := ν.k_lt_one
    have := ν.k_nonneg
    nlinarith
  norm_le := by
    filter_upwards [μ.norm_le, ν.norm_le] with z hz hz'
    calc ‖μ z * ν z‖ = ‖μ z‖ * ‖ν z‖ := norm_mul _ _
      _ ≤ μ.k * ν.k := mul_le_mul hz hz' (norm_nonneg _) μ.k_nonneg

@[simp] theorem mul_apply (μ ν : Beltrami) (z : ℂ) : mul μ ν z = μ z * ν z := rfl

/-- A Beltrami coefficient is in `L^∞`. -/
theorem memLp_top (μ : Beltrami) : MemLp (⇑μ) ⊤ volume := by
  rw [memLp_iff, eLpNorm_exponent_top μ.measurable]
  exact (eLpNormEssSup_le_of_ae_bound μ.norm_le).trans_lt ENNReal.ofReal_lt_top

/-- The essential supremum of `|μ|` is `≤ k`. -/
theorem eLpNormEssSup_le (μ : Beltrami) : eLpNormEssSup (⇑μ) volume ≤ ENNReal.ofReal μ.k :=
  eLpNormEssSup_le_of_ae_bound μ.norm_le

end Beltrami

/-! ## Quasiconformal maps -/

/-- `g` maps `U` homeomorphically onto `g '' U`. -/
def IsHomeomorphOn (g : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ContinuousOn g U ∧ ∃ ginv : ℂ → ℂ, ContinuousOn ginv (g '' U) ∧
    (∀ x ∈ U, ginv (g x) = x) ∧ ∀ y ∈ g '' U, g (ginv y) = y

/-- Weak (distributional) `∂̄`-derivative on an open set `U`: tested against smooth
functions whose support is compactly contained in `U`. -/
def IsDbarDerivOn (f g : ℂ → ℂ) (U : Set ℂ) : Prop :=
  LocallyIntegrableOn f U volume ∧ LocallyIntegrableOn g U volume ∧
    ∀ φ : 𝓓(⊤, ℂ), tsupport (φ : ℂ → ℂ) ⊆ U →
      Integrable (fun z => f z * dzbar (φ : ℂ → ℂ) z) ∧
      Integrable (fun z => g z * φ z) ∧
      ∫ z, f z * dzbar (φ : ℂ → ℂ) z = - ∫ z, g z * φ z

/-- Weak (distributional) `∂`-derivative on an open set `U`. -/
def IsDzDerivOn (f g : ℂ → ℂ) (U : Set ℂ) : Prop :=
  LocallyIntegrableOn f U volume ∧ LocallyIntegrableOn g U volume ∧
    ∀ φ : 𝓓(⊤, ℂ), tsupport (φ : ℂ → ℂ) ⊆ U →
      Integrable (fun z => f z * dz (φ : ℂ → ℂ) z) ∧
      Integrable (fun z => g z * φ z) ∧
      ∫ z, f z * dz (φ : ℂ → ℂ) z = - ∫ z, g z * φ z

/-- `g ∈ W^{1,2}_{loc}(U)`: `g` is locally square integrable on `U`, its weak Wirtinger
derivatives on `U` exist and are locally square integrable, and the pointwise (Fréchet)
Wirtinger derivatives `dz g`, `dzbar g` (junk `0` on the null set of non-differentiability)
agree with them a.e. -/
def HasW12LocOn (g : ℂ → ℂ) (U : Set ℂ) : Prop :=
  MemL2LocOn g U ∧
    ∃ gz gzbar : ℂ → ℂ,
      IsDzDerivOn g gz U ∧ IsDbarDerivOn g gzbar U ∧ MemL2LocOn gz U ∧ MemL2LocOn gzbar U ∧
        gz =ᵐ[volume] dz g ∧ gzbar =ᵐ[volume] dzbar g

/-- `g` is **quasiconformal on the open set `U` with complex dilatation `μ`** (analytic
definition): `g : U → g '' U` is a homeomorphism, `g ∈ W^{1,2}_{loc}(U)`, `∂̄g = μ · ∂g`
a.e. on `U`, and `‖μ‖ ≤ k` a.e. on `U` for some `k < 1`.

The `W^{1,2}_{loc}` clause (`HasW12LocOn`) is *not* redundant: without it the pointwise
a.e. relation `dzbar g = μ dz g` is satisfied vacuously by homeomorphisms that are nowhere
differentiable (where both `dz g` and `dzbar g` take the junk value `0`). -/
def IsQCOn (g : ℂ → ℂ) (U : Set ℂ) (μ : ℂ → ℂ) : Prop :=
  IsOpen U ∧ IsHomeomorphOn g U ∧ HasW12LocOn g U ∧
    (∃ k : ℝ, k < 1 ∧ ∀ᵐ z ∂volume, z ∈ U → ‖μ z‖ ≤ k) ∧
    ∀ᵐ z ∂volume, z ∈ U → dzbar g z = μ z * dz g z

/-- A quasiconformal homeomorphism of the plane: quasiconformal on `ℂ` and surjective
onto `ℂ` (the standard convention, "q.c. homeomorphism of `ℂ` onto `ℂ`").  Surjectivity
is not automatic from `IsQCOn f univ μ`; it is the classical rigidity fact that a q.c.
homeomorphism with bounded dilatation on `ℂ` has image `ℂ`. -/
def IsQuasiconformal (f : ℂ → ℂ) (μ : ℂ → ℂ) : Prop := IsQCOn f Set.univ μ ∧ Function.Surjective f

/-- `f` is conformal in the weak sense: `∂̄ f = 0` distributionally. -/
def IsWeaklyConformal (f : ℂ → ℂ) : Prop := ∃ g : ℂ → ℂ, IsDbarDeriv f g ∧ ∀ᵐ z, g z = 0

/-- `f` fixes infinity in the sense `f(z) - z → 0` at `∞`. -/
def FixesInfinity (f : ℂ → ℂ) : Prop := Tendsto (fun z : ℂ => f z - z) (cocompact ℂ) (𝓝 0)

/-- Normalisation `f(0) = 0, f(1) = 1`. -/
def FixesZeroOne (f : ℂ → ℂ) : Prop := f 0 = 0 ∧ f 1 = 1

/-- The **principal normalisation** `f(z) = z + O(1/z)` at `∞`. -/
def IsPrincipalAtInfinity (f : ℂ → ℂ) : Prop :=
  Asymptotics.IsBigO (cocompact ℂ) (fun z => z * (f z - z)) (fun _ => (1 : ℂ))

/-! ## The hyperbolic sum of complex dilatations -/

/-- The hyperbolic (= Möbius) sum `(μ + ν)/(1 + μ̄ν)` of two complex dilatations.  This is
the operation governing the dilatation of a composite of quasiconformal maps: if `|μ| ≤ k`
and `|ν| ≤ k'` with `k, k' < 1` then `|hyperbolicSum μ ν| ≤ (k+k')/(1+kk')`. -/
def hyperbolicSum (μ ν : ℂ) : ℂ := (μ + ν) / (1 + star μ * ν)

@[simp] theorem hyperbolicSum_zero_left (ν : ℂ) : hyperbolicSum 0 ν = ν := by
  simp [hyperbolicSum]

@[simp] theorem hyperbolicSum_zero_right (μ : ℂ) : hyperbolicSum μ 0 = μ := by
  simp [hyperbolicSum]

end Work.MRMT
