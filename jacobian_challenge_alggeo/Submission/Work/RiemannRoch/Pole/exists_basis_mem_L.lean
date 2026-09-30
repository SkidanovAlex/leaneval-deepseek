import Mathlib
import Submission.Work.RiemannRoch.Pole
import Submission.Work.CurveBasics.Order.finiteDimensional_adjoin_functionField
import Submission.Work.CurveBasics.Order.Bridge

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
open scoped IntermediateField.algebraAdjoinAdjoin

universe u

namespace Work.RiemannRoch.Pole

open Work.CurveBasics

noncomputable section

/-- An element of `K(C)` integral over `k[x]` is regular at every place at which `x` is. -/
theorem isIntegral_ordAt_nonneg {k : Type u} [Field k] (C : Curve k) (x y : C.functionField)
    (hy : IsIntegral ↥(Algebra.adjoin k ({x} : Set C.functionField)) y)
    (Q : C.Place) (hQ : 0 ≤ C.ordAt x Q) : 0 ≤ C.ordAt y Q := by
  have hmem : y ∈ (kxInt C x).toSubring := by
    rw [Subalgebra.mem_toSubring]
    exact (mem_integralClosure_iff _ _).mpr hy
  have hle := kxClosure_le_valuationSubring C x Q hQ hmem
  rw [ValuationSubring.mem_toSubring] at hle
  exact (Place.mem_valuationSubring_iff C Q y).mp hle

/-- An element of `K(C)` integral over `k[x]` lies in `L(s • poleDivisor x)` for some `s`. -/
theorem isIntegral_mem_L {k : Type u} [Field k] (C : Curve k) (x : C.functionField)
    (hx : Transcendental k x) {y : C.functionField}
    (hy : IsIntegral ↥(Algebra.adjoin k ({x} : Set C.functionField)) y) :
    ∃ s : ℕ, y ∈ C.L (s • Work.RiemannRoch.Curve.poleDivisor C x) := by
  classical
  by_cases hy0 : y = 0
  · exact ⟨0, by rw [hy0]; exact Submodule.zero_mem _⟩
  set D : C.Div := Work.RiemannRoch.Curve.poleDivisor C x with hD
  set s : ℕ := D.support.sup (fun Q => Int.toNat (-(C.ordAt y Q))) with hs
  have hkey : ∀ Q : C.Place, (s : ℤ) * D Q ≥ -(C.ordAt y Q) := by
    intro Q
    by_cases hd : D Q = 0
    · have hxQ : 0 ≤ C.ordAt x Q := by
        have hh := hd
        rw [hD, Work.RiemannRoch.Curve.poleDivisor_apply] at hh
        have h3 : -(C.ordAt x Q) ≤ 0 := le_trans (le_max_right (0 : ℤ) _) (le_of_eq hh)
        omega
      have hyQ : 0 ≤ C.ordAt y Q := isIntegral_ordAt_nonneg C x y hy Q hxQ
      rw [hd]
      simp only [mul_zero]
      linarith
    · have hmem : Q ∈ D.support := Finsupp.mem_support_iff.mpr hd
      have hd1 : (1 : ℤ) ≤ D Q := by
        have h0 : 0 ≤ D Q := (Work.RiemannRoch.Curve.isEffective_poleDivisor C x) Q
        omega
      have hsup : (Int.toNat (-(C.ordAt y Q)) : ℕ) ≤ s := by
        rw [hs]
        exact Finset.le_sup (f := fun Q => Int.toNat (-(C.ordAt y Q))) hmem
      have hsupZ : ((Int.toNat (-(C.ordAt y Q)) : ℕ) : ℤ) ≤ (s : ℤ) := Nat.cast_le.mpr hsup
      have h1 : -(C.ordAt y Q) ≤ (s : ℤ) :=
        (Int.self_le_toNat (-(C.ordAt y Q))).trans hsupZ
      have h2 : (0 : ℤ) ≤ (s : ℤ) := by exact_mod_cast Nat.zero_le s
      nlinarith [h1, h2, hd1]
  refine ⟨s, ?_⟩
  rw [C.mem_L_iff]
  refine Or.inr ?_
  rw [C.isEffective_div_add_iff]
  intro Q
  have hk := hkey Q
  rw [Finsupp.smul_apply, nsmul_eq_mul]
  linarith

/-- **A `k(x)`-basis of `K(C)` inside a single pole space `L(r • poleDivisor x)`.**

The basis is obtained from an arbitrary `k(x)`-basis by multiplying each vector by a nonzero
element of `k[x]` making it integral over `k[x]`; such elements have poles only at the poles
of `x` (`isIntegral_mem_L`). -/
theorem exists_basis_mem_L {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (x : C.functionField) (hx : Transcendental k x) :
    ∃ r : ℕ, ∃ b : Module.Basis
        (Fin (Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField))
          C.functionField))
        (IntermediateField.adjoin k ({x} : Set C.functionField)) C.functionField,
      ∀ i, (b i : C.functionField) ∈ C.L (r • Work.RiemannRoch.Curve.poleDivisor C x) := by
  classical
  haveI hfd : FiniteDimensional (IntermediateField.adjoin k ({x} : Set C.functionField))
      C.functionField :=
    Work.CurveBasics.Order.finiteDimensional_adjoin_functionField C hx
  haveI hAlg : Algebra.IsAlgebraic (IntermediateField.adjoin k ({x} : Set C.functionField))
      C.functionField := Algebra.IsAlgebraic.of_finite _ _
  let b₀ : Module.Basis
      (Fin (Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField))
        C.functionField))
      (IntermediateField.adjoin k ({x} : Set C.functionField)) C.functionField :=
    Module.finBasis _ _
  have key : ∀ i, ∃ c : ↥(Algebra.adjoin k ({x} : Set C.functionField)),
      c ≠ 0 ∧ IsIntegral ↥(Algebra.adjoin k ({x} : Set C.functionField)) (c • (b₀ i)) := by
    intro i
    haveI : IsFractionRing ↥(Algebra.adjoin k ({x} : Set C.functionField))
        (IntermediateField.adjoin k ({x} : Set C.functionField)) := inferInstance
    have hbL : IsAlgebraic (IntermediateField.adjoin k ({x} : Set C.functionField)) (b₀ i) :=
      Algebra.IsAlgebraic.isAlgebraic (b₀ i)
    have hbK : IsAlgebraic ↥(Algebra.adjoin k ({x} : Set C.functionField)) (b₀ i) :=
      (IsFractionRing.isAlgebraic_iff ↥(Algebra.adjoin k ({x} : Set C.functionField))
        ↥(IntermediateField.adjoin k ({x} : Set C.functionField)) C.functionField).mpr hbL
    exact hbK.exists_integral_multiple
  choose c hc0 hcint using key
  let u : Fin (Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField))
        C.functionField) → (IntermediateField.adjoin k ({x} : Set C.functionField))ˣ :=
    fun i => Units.mk0 (algebraMap ↥(Algebra.adjoin k ({x} : Set C.functionField))
        (IntermediateField.adjoin k ({x} : Set C.functionField)) (c i))
      (fun h => hc0 i ((IsFractionRing.injective _ _) h))
  have hval : ∀ i, ((u i : IntermediateField.adjoin k ({x} : Set C.functionField)))
      = algebraMap ↥(Algebra.adjoin k ({x} : Set C.functionField))
          (IntermediateField.adjoin k ({x} : Set C.functionField)) (c i) :=
    fun i => Units.val_mk0 _
  have hint : ∀ i, IsIntegral ↥(Algebra.adjoin k ({x} : Set C.functionField))
      ((b₀.unitsSMul u i : C.functionField)) := by
    intro i
    have hEq : ((b₀.unitsSMul u i : C.functionField)) = c i • (b₀ i) := by
      rw [Module.Basis.unitsSMul_apply, Units.smul_def, Algebra.smul_def, Algebra.smul_def]
      rw [hval i, IsScalarTower.algebraMap_apply ↥(Algebra.adjoin k ({x} : Set C.functionField))
        ↥(IntermediateField.adjoin k ({x} : Set C.functionField)) C.functionField (c i)]
    rw [hEq]
    exact hcint i
  choose s hs using fun i => isIntegral_mem_L C x hx (hint i)
  refine ⟨Finset.univ.sup s, b₀.unitsSMul u, fun i => ?_⟩
  refine C.L_mono ?_ (hs i)
  rw [Curve.Div.le_iff]
  intro Q
  simp only [Finsupp.smul_apply, nsmul_eq_mul]
  have hsi : s i ≤ Finset.univ.sup s := Finset.le_sup (Finset.mem_univ i)
  have hsiZ : ((s i : ℕ) : ℤ) ≤ ((Finset.univ.sup s : ℕ) : ℤ) := Nat.cast_le.mpr hsi
  have hD0 : (0 : ℤ) ≤ Work.RiemannRoch.Curve.poleDivisor C x Q :=
    (Work.RiemannRoch.Curve.isEffective_poleDivisor C x) Q
  exact mul_le_mul_of_nonneg_right hsiZ hD0

end

end Work.RiemannRoch.Pole
