import Mathlib
import Submission.Work.MotTDG.Defs
import Submission.Work.MotC2.TransAux.NoRoot
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotTDG

/-!
**TDG-f**: a nonconstant point of a Weierstrass curve over its own function field gives an
`L`-algebra endomorphism of the function field by substitution.

If `U V ∈ L(E)` satisfy the Weierstrass equation of `E` pushed to `L(E)` (`Equation (E.map
(algebraMap L (FunctionField E))) U V`) and `U` is transcendental over `L`, then there is an
`L`-algebra endomorphism `φ` of `L(E)` with `φ x = U` and `φ y = V`.  This is the general form of
`Work.MotC2.phi` (`Submission/Work/MotC2/Translation.lean`), which is the case
`(U, V) = (transX E T, transY E T)`; unlike that one, neither ellipticity nor `DecidableEq L` is
needed.  It is the last ingredient of node TDG-M (`Work.MotTDG.projAut_of_kleinEq_spans`), where
`(U, V) = (v'₁, v'₂)` is the Weierstrass point produced by a net-preserving projectivity `M`.

PROOF ROUTE (mirror `Submission/Work/MotC2/Translation.lean`, lines 87–150, replacing the
translated coordinates by `U, V`):

* `g := Work.MotC2.plugHom E U V hUV : Work.MotC2.Coord E →ₐ[L] Work.MotC2.Func E` is the
  evaluation homomorphism with `g (coordX E) = U`, `g (coordY E) = V`
  (`Work.MotC2.plugHom_coordX`, `Work.MotC2.plugHom_coordY`).
* **Injectivity of `g`.**  Show first that `V ∉ L⟮U⟯`: if `V = aeval U r / aeval U s` with
  `s ≠ 0`, then multiplying the equation by `s ^ 2` and applying `Work.MotC2.TransAux.NoRoot`
  (the pure degree statement `p² + (a₁X+a₃)pq - (X³+a₂X²+a₄X+a₆)q² ≠ 0` for `q ≠ 0`) to the
  injectivity of `aeval U : L[X] → L(E)` (that is `Transcendental`/`transcendental_iff`) gives a
  contradiction; this is exactly the argument of `Work.MotC2.notMem_adjoin_of_equation`, whose
  proof does not use ellipticity.  Now if `g r = 0` with `r ≠ 0`, write
  `r = algebraMap (L[X]) (Coord E) p + algebraMap (L[X]) (Coord E) q * coordY E` using
  `CoordinateRing.exists_smul_basis_eq` and `CoordinateRing.smul`.  If `q = 0` then `p ≠ 0` and
  `aeval U p = 0` contradicts `hU`; if `q ≠ 0` then `aeval U q ≠ 0` (transcendence) and
  `V = -(aeval U p) / (aeval U q) ∈ L⟮U⟯` (`IntermediateField.mem_adjoin_simple_iff`),
  contradiction.
* **Extension.**  `IsFractionRing.liftAlgHom (hg : Function.Injective g)` is an `L`-algebra
  homomorphism `FunctionField E →ₐ[L] FunctionField E` whose composite with the structure map of
  `Coord E` is `g` (`IsFractionRing.coe_liftAlgHom`, `IsFractionRing.lift_algebraMap`).
* **Identification.**  `Work.MotTDG.genX_eq` gives `Work.MotV.genX E = Work.MotC2.genX E`
  (and `genY_eq` likewise), and `Work.MotC2.genX` is `algebraMap (Coord E) (Func E) (coordX E)`,
  so the two required values follow.

The result is `Work.MotTDG.exists_algHom_of_point`; node TDG-M instantiates it.
-/

open Polynomial WeierstrassCurve.Affine
open scoped IntermediateField

noncomputable section

variable {L : Type} [Field L]

/-! ## The equation `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` has no rational root in `L(U)` -/

/-- **`V` is not a rational function of `U`**: if `(U, V)` satisfies the Weierstrass equation
pushed to `L(E)` and `U` is transcendental over `L`, then `V ∉ L⟮U⟯`.  This is
`Work.MotC2.notMem_adjoin_of_equation`, with neither ellipticity nor `DecidableEq L`. -/
lemma notMem_adjoin_of_equation (E : WeierstrassCurve L) {U V : FunctionField E}
    (h : Equation (E.map (algebraMap L (FunctionField E))) U V)
    (hU : Transcendental L U) : V ∉ L⟮U⟯ := by
  intro hmem
  rw [IntermediateField.mem_adjoin_simple_iff] at hmem
  obtain ⟨r, s, hs⟩ := hmem
  have key : ∀ r s : L[X], s ≠ 0 → V ≠ Polynomial.aeval U r / Polynomial.aeval U s := by
    intro r s hs' heq
    have hUinj := transcendental_iff_injective.mp hU
    have hsU : Polynomial.aeval U s ≠ 0 := fun hz => hs' (hUinj (by simpa using hz))
    have hmul : V * Polynomial.aeval U s = Polynomial.aeval U r := by
      rw [heq, div_mul_cancel₀ _ hsU]
    have hrel := h
    rw [equation_iff, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at hrel
    have hRU : Polynomial.aeval U (r ^ 2 + (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃)
        * r * s - (Polynomial.X ^ 3 + Polynomial.C E.a₂ * Polynomial.X ^ 2
          + Polynomial.C E.a₄ * Polynomial.X + Polynomial.C E.a₆) * s ^ 2) = 0 := by
      simp only [map_sub, map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
      rw [← hmul]
      linear_combination (norm := first | refl_ring1 | ring1) (Polynomial.aeval U s ^ 2) * hrel
    have hR0 : r ^ 2 + (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃) * r * s
        - (Polynomial.X ^ 3 + Polynomial.C E.a₂ * Polynomial.X ^ 2 + Polynomial.C E.a₄
            * Polynomial.X + Polynomial.C E.a₆) * s ^ 2 = 0 :=
      hUinj (by simpa using hRU)
    exact Work.MotC2.TransAux.NoRoot E.a₁ E.a₃ E.a₂ E.a₄ E.a₆ r s hs' hR0
  by_cases hs0 : s = 0
  · have hV0 : V = Polynomial.aeval U (0 : L[X]) / Polynomial.aeval U (1 : L[X]) := by
      rw [hs, hs0]
      simp
    exact key 0 1 one_ne_zero hV0
  · exact key r s hs0 hs

/-! ## The evaluation homomorphism at `(U, V)` is injective -/

/-- `plugHom E U V hUV` is `aeval U` on the subalgebra `L[X] ⊆ L(E)`. -/
lemma plugHom_algebraMap (E : WeierstrassCurve L) (U V : FunctionField E)
    (hUV : Equation (E.map (algebraMap L (FunctionField E))) U V) (p : L[X]) :
    Work.MotC2.plugHom E U V hUV (algebraMap (L[X]) (Work.MotC2.Coord E) p)
      = Polynomial.aeval U p := by
  have hcomp : (Work.MotC2.plugHom E U V hUV).comp
        (IsScalarTower.toAlgHom L (L[X]) (Work.MotC2.Coord E)) = Polynomial.aeval U := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
      Work.MotC2.algebraMap_X_eq_coordX, Work.MotC2.plugHom_coordX, Polynomial.aeval_X]
  exact AlgHom.congr_fun hcomp p

/-- A nonzero element of the coordinate ring is not killed by the evaluation at `(U, V)`. -/
lemma plugHom_eq_zero (E : WeierstrassCurve L) (U V : FunctionField E)
    (hUV : Equation (E.map (algebraMap L (FunctionField E))) U V)
    (hU : Transcendental L U) {r : Work.MotC2.Coord E}
    (hr : Work.MotC2.plugHom E U V hUV r = 0) : r = 0 := by
  obtain ⟨p, q, hpq⟩ :=
    WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq (W' := E) r
  have hr' : r = algebraMap (L[X]) (Work.MotC2.Coord E) p
      + algebraMap (L[X]) (Work.MotC2.Coord E) q * Work.MotC2.coordY E := by
    rw [← hpq, WeierstrassCurve.Affine.CoordinateRing.smul,
      WeierstrassCurve.Affine.CoordinateRing.smul, mul_one, AdjoinRoot.mk_C, AdjoinRoot.mk_C,
      ← Work.MotC2.coordY_eq_mk, ← AdjoinRoot.algebraMap_eq]
  have h2 : Polynomial.aeval U p + Polynomial.aeval U q * V = 0 := by
    rw [← hr, hr', map_add, map_mul, plugHom_algebraMap E U V hUV p,
      plugHom_algebraMap E U V hUV q, Work.MotC2.plugHom_coordY]
  by_cases hq : q = 0
  · have hp : p = 0 := by
      refine (transcendental_iff_injective.mp hU) ?_
      simpa [hq] using h2
    rw [hr', hp, hq]
    simp
  · exfalso
    have hV : V ∉ L⟮U⟯ := notMem_adjoin_of_equation E hUV hU
    apply hV
    rw [IntermediateField.mem_adjoin_simple_iff]
    refine ⟨-p, q, ?_⟩
    have hqne : Polynomial.aeval U q ≠ 0 := fun hz =>
      hq ((transcendental_iff_injective.mp hU) (by simpa using hz))
    rw [map_neg, eq_div_iff hqne]
    linear_combination (norm := first | refl_ring1 | ring1) h2

/-- The evaluation homomorphism at a point `(U, V)` with `U` transcendental is injective. -/
lemma plugHom_injective (E : WeierstrassCurve L) (U V : FunctionField E)
    (hUV : Equation (E.map (algebraMap L (FunctionField E))) U V)
    (hU : Transcendental L U) : Function.Injective (Work.MotC2.plugHom E U V hUV) := by
  intro r r' hrr
  have h0 : Work.MotC2.plugHom E U V hUV (r - r') = 0 := by rw [map_sub, hrr, sub_self]
  exact sub_eq_zero.mp (plugHom_eq_zero E U V hUV hU h0)

theorem exists_algHom_of_point {L : Type} [Field L] (E : WeierstrassCurve L)
    (U V : WeierstrassCurve.Affine.FunctionField E)
    (hUV : WeierstrassCurve.Affine.Equation
      (E.map (algebraMap L (WeierstrassCurve.Affine.FunctionField E))) U V)
    (hU : Transcendental L U) :
    ∃ φ : WeierstrassCurve.Affine.FunctionField E →ₐ[L]
        WeierstrassCurve.Affine.FunctionField E,
      φ (Work.MotV.genX E) = U ∧ φ (Work.MotV.genY E) = V := by
  refine ⟨IsFractionRing.liftAlgHom (plugHom_injective E U V hUV hU), ?_, ?_⟩
  · rw [genX_eq E, Work.MotC2.genX, IsFractionRing.coe_liftAlgHom,
      IsFractionRing.lift_algebraMap]
    exact Work.MotC2.plugHom_coordX E U V hUV
  · rw [genY_eq E, Work.MotC2.genY, IsFractionRing.coe_liftAlgHom,
      IsFractionRing.lift_algebraMap]
    exact Work.MotC2.plugHom_coordY E U V hUV

end

end Work.MotTDG
