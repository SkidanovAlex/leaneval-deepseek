import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotTDG.exists_algHom_of_point
import Submission.Work.MotC2.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotTDG

open Polynomial WeierstrassCurve.Affine
open scoped IntermediateField

noncomputable section

variable {K : Type} [Field K]
variable {F : Type} [Field F] [Algebra K F]

/-! ## The equation `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` has no rational root in `K(U)` -/

/-- **`V` is not a rational function of `U`** over an arbitrary field `F ⊇ K`: if `(U, V)` satisfies
the Weierstrass equation of `E` pushed to `F` and `U` is transcendental over `K`, then
`V ∉ K⟮U⟯`.  This is `Work.MotTDG.notMem_adjoin_of_equation` with the ambient field replaced by an
arbitrary `F`; the proof is ambient-field agnostic. -/
lemma notMem_adjoin_of_equation_between (E : WeierstrassCurve K) {U V : F}
    (h : Equation (E.map (algebraMap K F)) U V)
    (hU : Transcendental K U) : V ∉ K⟮U⟯ := by
  intro hmem
  rw [IntermediateField.mem_adjoin_simple_iff] at hmem
  obtain ⟨r, s, hs⟩ := hmem
  have key : ∀ r s : K[X], s ≠ 0 → V ≠ Polynomial.aeval U r / Polynomial.aeval U s := by
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
  · have hV0 : V = Polynomial.aeval U (0 : K[X]) / Polynomial.aeval U (1 : K[X]) := by
      rw [hs, hs0]
      simp
    exact key 0 1 one_ne_zero hV0
  · exact key r s hs0 hs

/-! ## The evaluation homomorphism at `(U, V)` is injective -/

/-- `plugHom E U V hUV` is `aeval U` on the subalgebra `K[X] ⊆ K(E)`, over an arbitrary field. -/
lemma plugHom_algebraMap_between (E : WeierstrassCurve K) (U V : F)
    (hUV : Equation (E.map (algebraMap K F)) U V) (p : K[X]) :
    Work.MotC2.plugHom E U V hUV (algebraMap (K[X]) (Work.MotC2.Coord E) p)
      = Polynomial.aeval U p := by
  have hcomp : (Work.MotC2.plugHom E U V hUV).comp
        (IsScalarTower.toAlgHom K (K[X]) (Work.MotC2.Coord E)) = Polynomial.aeval U := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, IsScalarTower.toAlgHom_apply,
      Work.MotC2.algebraMap_X_eq_coordX, Work.MotC2.plugHom_coordX, Polynomial.aeval_X]
  exact AlgHom.congr_fun hcomp p

/-- A nonzero element of the coordinate ring is not killed by the evaluation at `(U, V)`, for `U`,
`V` in an arbitrary field extension `F ⊇ K`. -/
lemma plugHom_eq_zero_between (E : WeierstrassCurve K) (U V : F)
    (hUV : Equation (E.map (algebraMap K F)) U V)
    (hU : Transcendental K U) {r : Work.MotC2.Coord E}
    (hr : Work.MotC2.plugHom E U V hUV r = 0) : r = 0 := by
  obtain ⟨p, q, hpq⟩ :=
    WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq (W' := E) r
  have hr' : r = algebraMap (K[X]) (Work.MotC2.Coord E) p
      + algebraMap (K[X]) (Work.MotC2.Coord E) q * Work.MotC2.coordY E := by
    rw [← hpq, WeierstrassCurve.Affine.CoordinateRing.smul,
      WeierstrassCurve.Affine.CoordinateRing.smul, mul_one, AdjoinRoot.mk_C, AdjoinRoot.mk_C,
      ← Work.MotC2.coordY_eq_mk, ← AdjoinRoot.algebraMap_eq]
  have h2 : Polynomial.aeval U p + Polynomial.aeval U q * V = 0 := by
    rw [← hr, hr', map_add, map_mul, plugHom_algebraMap_between E U V hUV p,
      plugHom_algebraMap_between E U V hUV q, Work.MotC2.plugHom_coordY]
  by_cases hq : q = 0
  · have hp : p = 0 := by
      refine (transcendental_iff_injective.mp hU) ?_
      simpa [hq] using h2
    rw [hr', hp, hq]
    simp
  · exfalso
    have hV : V ∉ K⟮U⟯ := notMem_adjoin_of_equation_between E hUV hU
    apply hV
    rw [IntermediateField.mem_adjoin_simple_iff]
    refine ⟨-p, q, ?_⟩
    have hqne : Polynomial.aeval U q ≠ 0 := fun hz =>
      hq ((transcendental_iff_injective.mp hU) (by simpa using hz))
    rw [map_neg, eq_div_iff hqne]
    linear_combination (norm := first | refl_ring1 | ring1) h2

/-- The evaluation homomorphism at a point `(U, V)` of `E` over an arbitrary field extension
`F ⊇ K`, with `U` transcendental over `K`, is injective. -/
lemma plugHom_injective_between (E : WeierstrassCurve K) (U V : F)
    (hUV : Equation (E.map (algebraMap K F)) U V)
    (hU : Transcendental K U) : Function.Injective (Work.MotC2.plugHom E U V hUV) := by
  intro r r' hrr
  have h0 : Work.MotC2.plugHom E U V hUV (r - r') = 0 := by rw [map_sub, hrr, sub_self]
  exact sub_eq_zero.mp (plugHom_eq_zero_between E U V hUV hU h0)

end

/-- **TDG-f, two-curve form**: a point of a Weierstrass curve `E` over `K` with coordinates in an
arbitrary field extension `F ⊇ K`, whose `x`-coordinate is transcendental over `K`, gives a
`K`-algebra homomorphism `K(E) →ₐ[K] F` by substitution.  This is
`Work.MotTDG.exists_algHom_of_point` with the ambient field `FunctionField E` replaced by an
arbitrary field `F`: `Work.MotC2.plugHom E U V h` already targets an arbitrary field, and the three
lemmas used in that proof (`notMem_adjoin_of_equation`, `plugHom_eq_zero`, `plugHom_injective`, all
in `Submission/Work/MotTDG/exists_algHom_of_point.lean`) have proofs that are ambient-field
agnostic and only need to be re-stated with `U V : F`,
`hUV : Equation (E.map (algebraMap K F)) U V` and `V ∉ K⟮U⟯` relative to `F`; then
`IsFractionRing.liftAlgHom` (with target `F`) finishes.  Nothing else uses `F = FunctionField E`. -/
theorem exists_algHom_of_point_between (K : Type) [Field K] (E : WeierstrassCurve K)
    (F : Type) [Field F] [Algebra K F] (U V : F)
    (hUV : WeierstrassCurve.Affine.Equation (E.map (algebraMap K F)) U V)
    (hU : Transcendental K U) :
    ∃ φ : WeierstrassCurve.Affine.FunctionField E →ₐ[K] F,
      φ (Work.MotV.genX E) = U ∧ φ (Work.MotV.genY E) = V := by
  refine ⟨IsFractionRing.liftAlgHom (plugHom_injective_between E U V hUV hU), ?_, ?_⟩
  · rw [Work.MotTDG.genX_eq E, Work.MotC2.genX, IsFractionRing.coe_liftAlgHom,
      IsFractionRing.lift_algebraMap]
    exact Work.MotC2.plugHom_coordX E U V hUV
  · rw [Work.MotTDG.genY_eq E, Work.MotC2.genY, IsFractionRing.coe_liftAlgHom,
      IsFractionRing.lift_algebraMap]
    exact Work.MotC2.plugHom_coordY E U V hUV

end Work.MotTDG
