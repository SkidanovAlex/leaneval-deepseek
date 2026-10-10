import Mathlib
import Submission.Work.MotV.PlaceDefs
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.Classification
import Submission.Work.SilvermanReduction.Basic
import Submission.Work.MotV.regularConstAux

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `ℤᵐ⁰`-valued valuation attached to a rational place of `N(E)`

`Work.MotV.ordOfPlace E S hS f` is the order of vanishing of `f ∈ N(E)` at the rational place `S`
of `N(E)/N` (positive = zero of `f`, negative = pole).  This file constructs the associated
`ℤᵐ⁰`-valued valuation

`placeValuation E S hS f = exp (-(ordOfPlace E S hS f))`   (`f ≠ 0`),

which is the form in which the place is consumed by the parent development (the valuation is
needed to state `Work.MotV.FifthPowerValued`, `Work.MotV5.ASUnramified` etc. at a *given* place,
whereas `ordOfPlace` alone only provides the order function).

The construction is *not* a re-derivation of the valuation axioms from `ordOfPlace` (that would
need multiplicativity and the ultrametric inequality of `ordOfPlace`, which are proved in the
sibling work `Work.MotV5.ordOfPlace_api`).  Instead we take the classical adic valuation of the
discrete valuation ring `S`,

`Work.SilvermanReduction.val ↥S N(E)`,

whose valuation axioms are those of a `Valuation` by construction, and identify its value on the
place with `exp (-ordOfPlace ·)`.  The two cases are:

* `f ∈ S`: the value is `exp (-addVal ⟨f, ·⟩)` by
  `Work.MotV5.val_algebraMap_eq_exp_neg_addVal` (the bridge between Mathlib's
  `IsDiscreteValuationRing.addVal` and the adic valuation of the maximal ideal), and
  `ordOfPlace` unfolds to `addVal ⟨f, ·⟩`;
* `f ∉ S`: then `f⁻¹ ∈ S` and the value is the inverse of the value of `f⁻¹`, which reduces to
  the previous case; on the order side `ordOfPlace f = - ordOfPlace f⁻¹` by definition.

The last two components of the main theorem — `v f ≤ 1 ↔ 0 ≤ ordOfPlace f` and
`1 < v f ↔ ordOfPlace f < 0` — are then immediate from `WithZero.exp_le_exp` /
`WithZero.exp_lt_exp` (the `0` of `ℤᵐ⁰` is the "infinite" value, so `v f ≤ 1` means that `f` is
regular at the place).
-/

namespace Work.MotV5

set_option linter.style.haveILetI false
set_option linter.unnecessarySimpa false

open scoped WithZero

noncomputable section

variable {N : Type*} [Field N]

/-! ## §1 A rational place is a fraction ring -/

/-- A rational place `S` of `N(E)/N` generates `N(E)` as a ring of fractions: `IsRatPlace` says
that every element of `N(E)` is a quotient `s₁ / s₂` of two elements of `S` with `s₂ ≠ 0`, which is
exactly the `surj` condition of `IsLocalization`; the other two conditions are automatic because
`N(E)` is a field and `S ↪ N(E)` is injective. -/
theorem isFractionRing_of_isRatPlace (E : WeierstrassCurve N)
    (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S) :
    IsFractionRing ↥S (Work.MotC2.Func E) where
  map_units := by
    intro y
    have hy0 : (y : ↥S) ≠ 0 := fun h => (mem_nonZeroDivisors_iff_ne_zero.mp y.2) h
    have hy1 : ((y : ↥S) : Work.MotC2.Func E) ≠ 0 := fun h => hy0 (Subtype.ext h)
    have hunit : IsUnit (((y : ↥S) : Work.MotC2.Func E)) := isUnit_iff_ne_zero.mpr hy1
    simpa [Subalgebra.algebraMap_apply] using hunit
  surj := by
    intro z
    obtain ⟨s₁, s₂, hs₂, h⟩ := hS.2 z
    refine ⟨(s₁, ⟨s₂, mem_nonZeroDivisors_iff_ne_zero.mpr ?_⟩),
      by simpa [Subalgebra.algebraMap_apply] using h⟩
    intro hs
    exact hs₂ (by rw [hs]; simp)
  exists_of_eq := by
    intro a b h
    refine ⟨1, Subtype.ext ?_⟩
    simpa [Subalgebra.algebraMap_apply] using h

/-! ## §2 The bridge between `addVal` and the adic valuation

Mathlib's `IsDiscreteValuationRing.addVal R : R → ℕ∞` is the multiplicity valuation of a
uniformizer, while `Work.SilvermanReduction.val R K` is the `ℤᵐ⁰`-valued adic valuation of the
maximal ideal `(π)` of `R`, normalized by `val π = exp (-1)`.  The two differ by exponentiation
with a sign: this is the content of Mathlib's `IsDiscreteValuationRing.intValuation_maximalIdeal`
(`intValuation x = (recTopCoe 0 (exp ·) (addVal x))⁻¹`). -/

/-- On the ring `R` itself, the adic valuation of the maximal ideal is
`WithZero.exp (-(addVal R ·))`.  (`hx` is needed only to exclude `x = 0`, where `addVal` takes the
value `⊤` and the `untopD`-normalization would give the wrong sign.) -/
private theorem val_bridge {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (x : R)
    (hx : algebraMap R K x ≠ 0) :
    Work.SilvermanReduction.val R K (algebraMap R K x) =
      WithZero.exp (-(((WithTop.untopD 0 (IsDiscreteValuationRing.addVal R x) : ℕ) : ℤ))) := by
  have hx0 : x ≠ 0 := fun h => hx (by rw [h, map_zero])
  have hne : IsDiscreteValuationRing.addVal R x ≠ ⊤ := by
    intro h
    exact hx0 (IsDiscreteValuationRing.addVal_eq_top_iff.mp h)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  have hgoal : ((WithTop.untopD 0 (IsDiscreteValuationRing.addVal R x) : ℕ) : ℤ) =
      ((ENat.toNat (IsDiscreteValuationRing.addVal R x) : ℕ) : ℤ) := rfl
  rw [hgoal, Work.SilvermanReduction.val,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal, ← hn, ENat.recTopCoe_natCast,
    ENat.toNat_natCast, WithZero.exp_neg, WithZero.exp_eq_coe_ofAdd]

/-! ## §3 The valuation at a rational place -/

/-- **The `ℤᵐ⁰`-valued valuation of `N(E)` at the rational place `S`**: the adic valuation of the
discrete valuation ring `S`, normalized so that a uniformizer has value `exp (-1)` and (as proved
in `placeValuation_apply`) so that `placeValuation E S hS f = exp (-(ordOfPlace E S hS f))` for
`f ≠ 0`. -/
noncomputable def placeValuation (E : WeierstrassCurve N)
    (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S) :
    Valuation (Work.MotC2.Func E) (WithZero (Multiplicative ℤ)) :=
  letI : IsDiscreteValuationRing ↥S := hS.1.choose
  letI : IsFractionRing ↥S (Work.MotC2.Func E) := isFractionRing_of_isRatPlace E S hS
  Work.SilvermanReduction.val ↥S (Work.MotC2.Func E)

/-- **The defining property of `placeValuation`**: on a nonzero element it is
`exp (-(ordOfPlace E S hS ·))`. -/
theorem placeValuation_apply (E : WeierstrassCurve N)
    (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S)
    (f : Work.MotC2.Func E) (hf : f ≠ 0) :
    placeValuation E S hS f = WithZero.exp (-(Work.MotV.ordOfPlace E S hS f)) := by
  classical
  letI : IsDiscreteValuationRing ↥S := hS.1.choose
  haveI hfrac : IsFractionRing ↥S (Work.MotC2.Func E) := isFractionRing_of_isRatPlace E S hS
  change Work.SilvermanReduction.val ↥S (Work.MotC2.Func E) f =
    WithZero.exp (-(Work.MotV.ordOfPlace E S hS f))
  by_cases hfS : f ∈ S
  · -- `f` is regular at the place: the value is `exp (-(addVal ⟨f, hfS⟩))`
    have hunfold : Work.MotV.ordOfPlace E S hS f =
        ((WithTop.untopD 0 ((IsDiscreteValuationRing.addVal ↥S) ⟨f, hfS⟩) : ℕ) : ℤ) := by
      unfold Work.MotV.ordOfPlace
      rw [dite_eq_left hfS]
    have hcoe : (algebraMap ↥S (Work.MotC2.Func E) ⟨f, hfS⟩ : Work.MotC2.Func E) = f := by
      simp [Subalgebra.algebraMap_apply]
    rw [hunfold]
    calc Work.SilvermanReduction.val ↥S (Work.MotC2.Func E) f
        = Work.SilvermanReduction.val ↥S (Work.MotC2.Func E)
            (algebraMap ↥S (Work.MotC2.Func E) ⟨f, hfS⟩) := by rw [hcoe]
      _ = WithZero.exp
            (-(((WithTop.untopD 0 ((IsDiscreteValuationRing.addVal ↥S) ⟨f, hfS⟩) : ℕ) : ℤ))) :=
          val_bridge (R := ↥S) (K := Work.MotC2.Func E) ⟨f, hfS⟩
            (by rw [hcoe]; exact hf)
  · -- `f` has a pole: `f⁻¹ ∈ S` and the value is the inverse of the value of `f⁻¹`
    have hfinv : f⁻¹ ∈ S :=
      (Work.MotC2.mem_or_inv_mem_of_isRatPlace hS f).resolve_left hfS
    let g : ↥S := ⟨f⁻¹, hfinv⟩
    have hunfold : Work.MotV.ordOfPlace E S hS f =
        -(((WithTop.untopD 0 ((IsDiscreteValuationRing.addVal ↥S) g) : ℕ) : ℤ)) := by
      unfold Work.MotV.ordOfPlace
      rw [dite_eq_right hfS]
    have hcoe : (algebraMap ↥S (Work.MotC2.Func E) g : Work.MotC2.Func E) = f⁻¹ := by
      simp [g, Subalgebra.algebraMap_apply]
    have hg0 : (algebraMap ↥S (Work.MotC2.Func E) g : Work.MotC2.Func E) ≠ 0 := by
      rw [hcoe]
      exact inv_ne_zero hf
    have hvinv : Work.SilvermanReduction.val ↥S (Work.MotC2.Func E) f =
        (Work.SilvermanReduction.val ↥S (Work.MotC2.Func E)
          (algebraMap ↥S (Work.MotC2.Func E) g))⁻¹ := by
      have hfeq : f = (algebraMap ↥S (Work.MotC2.Func E) g)⁻¹ := by rw [hcoe, inv_inv]
      rw [hfeq, Valuation.map_inv]
    calc Work.SilvermanReduction.val ↥S (Work.MotC2.Func E) f
        = (Work.SilvermanReduction.val ↥S (Work.MotC2.Func E)
            (algebraMap ↥S (Work.MotC2.Func E) g))⁻¹ := hvinv
      _ = (WithZero.exp
            (-(((WithTop.untopD 0 ((IsDiscreteValuationRing.addVal ↥S) g) : ℕ) : ℤ))))⁻¹ := by
            rw [val_bridge (R := ↥S) (K := Work.MotC2.Func E) g hg0]
      _ = WithZero.exp
            (-(-(((WithTop.untopD 0 ((IsDiscreteValuationRing.addVal ↥S) g) : ℕ) : ℤ)))) :=
            (WithZero.exp_neg
              (-(((WithTop.untopD 0 ((IsDiscreteValuationRing.addVal ↥S) g) : ℕ) : ℤ)))).symm
      _ = WithZero.exp (-(Work.MotV.ordOfPlace E S hS f)) := by rw [hunfold]

/-! ## §4 The main theorem -/

theorem placeVal_valuation {N : Type*} [Field N] (E : WeierstrassCurve N)
    (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S) :
    ∃ v : Valuation (Work.MotC2.Func E) (WithZero (Multiplicative ℤ)),
      Work.MotV.TrivOn N v ∧
      (∀ f : Work.MotC2.Func E, f ≠ 0 →
        v f = WithZero.exp (-(Work.MotV.ordOfPlace E S hS f))) ∧
      (∀ f : Work.MotC2.Func E, f ≠ 0 →
        (v f ≤ 1 ↔ 0 ≤ Work.MotV.ordOfPlace E S hS f)) ∧
      (∀ f : Work.MotC2.Func E, f ≠ 0 →
        (1 < v f ↔ Work.MotV.ordOfPlace E S hS f < 0)) := by
  classical
  refine ⟨placeValuation E S hS, ?_, ?_, ?_, ?_⟩
  · -- triviality on the constants: a nonzero constant is a unit of `S`, hence of order `0`
    intro c hc
    have hc0 : algebraMap N (Work.MotC2.Func E) c ≠ 0 := by
      simpa using (FaithfulSMul.algebraMap_injective N (Work.MotC2.Func E)).ne hc
    have hunit : IsUnit (⟨algebraMap N (Work.MotC2.Func E) c, S.algebraMap_mem c⟩ : ↥S) := by
      refine isUnit_iff_exists_inv.mpr
        ⟨⟨algebraMap N (Work.MotC2.Func E) c⁻¹, S.algebraMap_mem c⁻¹⟩, ?_⟩
      apply Subtype.ext
      show algebraMap N (Work.MotC2.Func E) c * algebraMap N (Work.MotC2.Func E) c⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hc, map_one]
    have hz : Work.MotV.ordOfPlace E S hS (algebraMap N (Work.MotC2.Func E) c) = 0 :=
      (Work.MotV.ordOfPlace_eq_zero_iff hS (S.algebraMap_mem c) hc0).mpr hunit
    rw [placeValuation_apply E S hS _ hc0, hz, neg_zero, WithZero.exp_zero]
  · intro f hf
    exact placeValuation_apply E S hS f hf
  · intro f hf
    rw [placeValuation_apply E S hS f hf, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  · intro f hf
    rw [placeValuation_apply E S hS f hf, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega

end

end Work.MotV5
