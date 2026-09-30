/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Divisors, `ℓ`, linear equivalence and `Pic⁰` (area GB)

For a curve `C` over `K` and a field extension `F/K` we write

* `Dv C F` for the group of divisors of `C_F`;
* `Ddeg C F` for the degree;
* `ell C D` for `ℓ(D) = dim_F L(D)`;
* `LinEquiv C D D'` for linear equivalence `D ∼ D'`: there is `h ≠ 0` with `div h = D - D'`;
* `Pic C F` for the divisor class group and `Pic0 C F` for the group of classes of degree
  zero.

`Pic0 C F` is the quotient of the degree-zero divisors by the degree-zero principal
divisors.  Once CB's `deg (div h) = 0` (`Work.CurveBasics.Order.deg_div`) is available this
is the usual `Pic⁰`, and `mk` is the usual class map.

The accompanying files contain the API:
`Submission/Work/GCBasics/LinEquiv.lean`, `…/PicApi.lean` and `…/EllApi.lean`.
-/
import Submission.Work.GCBasics.Basic
import Submission.Work.CurveBasics.Linear
import Submission.Work.CurveBasics.BaseChange
import Submission.Work.CurveBasics.Order.div_inv
import Submission.Work.CurveBasics.Linear.finiteDimensional_L

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.GCBasics

open Work.CurveBasics

noncomputable section

variable {K : Type u} [Field K]

/-- The group of divisors of `C` over a field extension `F/K`. -/
abbrev Dv (C : Curve K) (F : Type u) [Field F] [Algebra K F] : Type u :=
  (Curve.baseChange C F).Div

/-- The degree of a divisor of `C` over `F`, as an additive homomorphism. -/
abbrev Ddeg (C : Curve K) (F : Type u) [Field F] [Algebra K F] : Dv C F →+ ℤ :=
  (Curve.baseChange C F).degHom

/-- The dimension `ℓ(D) = dim_F L(D)` of the Riemann-Roch space, over a field of
definition `F`. -/
def ell (C : Curve K) {F : Type u} [Field F] [Algebra K F] (D : Dv C F) : ℕ :=
  Module.finrank F ((Curve.baseChange C F).L D)

/-- `D` and `D'` are linearly equivalent: `D - D'` is the divisor of a nonzero rational
function. -/
def LinEquiv (C : Curve K) {F : Type u} [Field F] [Algebra K F] (D D' : Dv C F) : Prop :=
  ∃ h : (Curve.baseChange C F).functionField, h ≠ 0 ∧ (Curve.baseChange C F).div h = D - D'

theorem linEquiv_def (C : Curve K) {F : Type u} [Field F] [Algebra K F] (D D' : Dv C F) :
    LinEquiv C D D' ↔ ∃ h : (Curve.baseChange C F).functionField,
      h ≠ 0 ∧ (Curve.baseChange C F).div h = D - D' := Iff.rfl

/-- The subgroup of principal divisors of `C` over `F`: divisors of nonzero rational
functions. -/
def prin (C : Curve K) (F : Type u) [Field F] [Algebra K F] : AddSubgroup (Dv C F) where
  carrier := {D | ∃ h : (Curve.baseChange C F).functionField,
    h ≠ 0 ∧ (Curve.baseChange C F).div h = D}
  zero_mem' := ⟨1, one_ne_zero, by
    rw [show (1 : (Curve.baseChange C F).functionField) = algebraMap F _ 1 from (map_one _).symm,
      Work.CurveBasics.Order.div_algebraMap_eq_zero]⟩
  add_mem' := by
    rintro D E ⟨h, hh, hD⟩ ⟨g, hg, hE⟩
    exact ⟨h * g, mul_ne_zero hh hg, by rw [Curve.div_mul _ hh hg, hD, hE]⟩
  neg_mem' := by
    rintro D ⟨h, hh, hD⟩
    exact ⟨h⁻¹, inv_ne_zero hh, by rw [Work.CurveBasics.Order.div_inv _ hh, hD]⟩

theorem mem_prin {C : Curve K} {F : Type u} [Field F] [Algebra K F] {D : Dv C F} :
    D ∈ prin C F ↔ ∃ h : (Curve.baseChange C F).functionField,
      h ≠ 0 ∧ (Curve.baseChange C F).div h = D := Iff.rfl

theorem mem_prin_iff {C : Curve K} {F : Type u} [Field F] [Algebra K F] {D : Dv C F} :
    D ∈ prin C F ↔ LinEquiv C D 0 := by
  rw [mem_prin, linEquiv_def]
  simp

theorem linEquiv_sub_zero_iff {C : Curve K} {F : Type u} [Field F] [Algebra K F]
    (D D' : Dv C F) : LinEquiv C (D - D') 0 ↔ LinEquiv C D D' := by
  rw [linEquiv_def, linEquiv_def]
  simp

theorem linEquiv_iff_sub_mem {C : Curve K} {F : Type u} [Field F] [Algebra K F]
    {D D' : Dv C F} : LinEquiv C D D' ↔ D - D' ∈ prin C F := by
  rw [mem_prin_iff, linEquiv_sub_zero_iff]

/-- The subgroup of divisors of degree zero. -/
def div0 (C : Curve K) (F : Type u) [Field F] [Algebra K F] : AddSubgroup (Dv C F) where
  carrier := {D | Ddeg C F D = 0}
  zero_mem' := by simp
  add_mem' := by
    rintro D E (hD : Ddeg C F D = 0) (hE : Ddeg C F E = 0)
    change Ddeg C F (D + E) = 0
    rw [map_add, hD, hE, add_zero]
  neg_mem' := by
    rintro D (hD : Ddeg C F D = 0)
    change Ddeg C F (-D) = 0
    rw [map_neg, hD, neg_zero]

/-- The divisor class group of `C_F`. -/
abbrev Pic (C : Curve K) (F : Type u) [Field F] [Algebra K F] : Type u := (Dv C F) ⧸ prin C F

/-- The group of divisor classes of degree zero of `C_F`. -/
abbrev Pic0 (C : Curve K) (F : Type u) [Field F] [Algebra K F] : Type u :=
  (div0 C F) ⧸ (prin C F).comap (div0 C F).subtype

/-- `ℓ` is monotone in the divisor: if `D ≤ D'` then `L(D) ⊆ L(D')`. -/
theorem ell_mono {C : Curve K} {F : Type u} [Field F] [Algebra K F] {D D' : Dv C F}
    (h : D ≤ D') : ell C D ≤ ell C D' := by
  haveI := Work.CurveBasics.Linear.finiteDimensional_L (Curve.baseChange C F) D'
  exact Submodule.finrank_mono (Curve.L_mono (Curve.baseChange C F) (Curve.Div.le_iff.mpr h))

/-- `ℓ` is monotone in the divisor, for the order `Div.le` of area CB. -/
theorem ell_mono' {C : Curve K} {F : Type u} [Field F] [Algebra K F] {D D' : Dv C F}
    (h : Curve.Div.le D D') : ell C D ≤ ell C D' :=
  ell_mono (Curve.Div.le_iff.mp h)

namespace LinEquiv

variable {C : Curve K} {F : Type u} [Field F] [Algebra K F]

/-- Linear equivalence is reflexive. -/
theorem refl (D : Dv C F) : LinEquiv C D D := by
  refine ⟨1, one_ne_zero, ?_⟩
  rw [show (1 : (Curve.baseChange C F).functionField) = algebraMap F _ 1 from (map_one _).symm,
    Work.CurveBasics.Order.div_algebraMap_eq_zero, sub_self]

/-- Linear equivalence is symmetric. -/
theorem symm {D D' : Dv C F} (h : LinEquiv C D D') : LinEquiv C D' D := by
  obtain ⟨g, hg, hdiv⟩ := h
  exact ⟨g⁻¹, inv_ne_zero hg, by rw [Work.CurveBasics.Order.div_inv _ hg, hdiv]; exact neg_sub D D'⟩

/-- Linear equivalence is transitive. -/
theorem trans {D D' D'' : Dv C F} (h : LinEquiv C D D') (h' : LinEquiv C D' D'') :
    LinEquiv C D D'' := by
  obtain ⟨g, hg, hdiv⟩ := h
  obtain ⟨g', hg', hdiv'⟩ := h'
  exact ⟨g * g', mul_ne_zero hg hg', by rw [Curve.div_mul _ hg hg', hdiv, hdiv']; abel⟩

/-- Adding a fixed divisor does not change linear equivalence. -/
theorem add {D D' : Dv C F} (h : LinEquiv C D D') (E : Dv C F) :
    LinEquiv C (D + E) (D' + E) := by
  obtain ⟨g, hg, hdiv⟩ := h
  exact ⟨g, hg, by rw [hdiv]; abel⟩

/-- Negation preserves linear equivalence. -/
theorem neg {D D' : Dv C F} (h : LinEquiv C D D') : LinEquiv C (-D) (-D') := by
  obtain ⟨g, hg, hdiv⟩ := h
  exact ⟨g⁻¹, inv_ne_zero hg, by rw [Work.CurveBasics.Order.div_inv _ hg, hdiv]; abel⟩

/-- Adding a fixed divisor is an equivalence for linear equivalence. -/
theorem add_iff (D D' E : Dv C F) :
    LinEquiv C (D + E) (D' + E) ↔ LinEquiv C D D' := by
  constructor
  · rintro ⟨g, hg, hdiv⟩
    exact ⟨g, hg, by rw [hdiv]; abel⟩
  · exact fun h => h.add E

/-- Subtracting a fixed divisor is an equivalence for linear equivalence. -/
theorem sub_iff (D D' E : Dv C F) :
    LinEquiv C (D - E) (D' - E) ↔ LinEquiv C D D' := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact add_iff D D' (-E)

/-- Linear equivalence is an equivalence relation. -/
theorem isEquivalence (C : Curve K) (F : Type u) [Field F] [Algebra K F] :
    Equivalence (LinEquiv (K := K) C (F := F)) where
  refl D := LinEquiv.refl D
  symm h := h.symm
  trans h h' := h.trans h'

end LinEquiv

namespace Pic

variable {C : Curve K} {F : Type u} [Field F] [Algebra K F]

/-- The class map of divisors of `C_F` into the divisor class group, as an additive
homomorphism. -/
def mkHom (C : Curve K) (F : Type u) [Field F] [Algebra K F] : Dv C F →+ Pic C F :=
  QuotientAddGroup.mk' (prin C F)

/-- The class of a divisor in the divisor class group. -/
def mk (D : Dv C F) : Pic C F := mkHom C F D

theorem mk_add (D D' : Dv C F) : mk (D + D') = mk D + mk D' := map_add _ _ _

theorem mk_zero : mk (0 : Dv C F) = 0 := map_zero _

theorem mk_neg (D : Dv C F) : mk (-D) = -mk D := map_neg _ _

theorem mk_sub (D D' : Dv C F) : mk (D - D') = mk D - mk D' := map_sub _ _ _

theorem mk_eq_iff {D D' : Dv C F} : mk D = mk D' ↔ LinEquiv C D D' := by
  change QuotientAddGroup.mk D = QuotientAddGroup.mk D' ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem, linEquiv_iff_sub_mem]

end Pic

namespace Pic0

variable {C : Curve K} {F : Type u} [Field F] [Algebra K F]

/-- The class map of degree-zero divisors of `C_F` into `Pic⁰`, as an additive
homomorphism. -/
def mkHom (C : Curve K) (F : Type u) [Field F] [Algebra K F] :
    div0 C F →+ Pic0 C F := QuotientAddGroup.mk' _

/-- The class of a divisor of degree zero in `Pic⁰`. -/
def mk (D : Dv C F) (hD : Ddeg C F D = 0) : Pic0 C F := mkHom C F ⟨D, hD⟩

theorem mk_add {D D' : Dv C F} (hD : Ddeg C F D = 0) (hD' : Ddeg C F D' = 0)
    (h : Ddeg C F (D + D') = 0) :
    mk (D + D') h = mk D hD + mk D' hD' := by
  show mkHom C F (⟨D + D', h⟩ : div0 C F) = mkHom C F ⟨D, hD⟩ + mkHom C F ⟨D', hD'⟩
  rw [← map_add]
  congr 1

theorem mk_zero : mk (0 : Dv C F) (by simp) = 0 := by
  show mkHom C F (⟨0, _⟩ : div0 C F) = 0
  rw [← map_zero (mkHom C F)]
  congr 1

theorem mk_neg {D : Dv C F} (hD : Ddeg C F D = 0) (h : Ddeg C F (-D) = 0) :
    mk (-D) h = -mk D hD := by
  show mkHom C F (⟨-D, h⟩ : div0 C F) = -mkHom C F ⟨D, hD⟩
  rw [← map_neg]
  congr 1

theorem mk_sub {D D' : Dv C F} (hD : Ddeg C F D = 0) (hD' : Ddeg C F D' = 0)
    (h : Ddeg C F (D - D') = 0) : mk (D - D') h = mk D hD - mk D' hD' := by
  show mkHom C F (⟨D - D', h⟩ : div0 C F) = mkHom C F ⟨D, hD⟩ - mkHom C F ⟨D', hD'⟩
  rw [← map_sub]
  congr 1

theorem mk_eq_iff {D D' : Dv C F} (hD : Ddeg C F D = 0) (hD' : Ddeg C F D' = 0) :
    mk D hD = mk D' hD' ↔ LinEquiv C D D' := by
  change QuotientAddGroup.mk (⟨D, hD⟩ : div0 C F) = QuotientAddGroup.mk ⟨D', hD'⟩ ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_comap]
  change (D - D') ∈ prin C F ↔ LinEquiv C D D'
  rw [linEquiv_iff_sub_mem]

end Pic0

end

end Work.GCBasics
