import Mathlib
import Submission.Work.MotC2.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC2

open Polynomial WeierstrassCurve.Affine

variable {L : Type*} [Field L]

/-
GUIDANCE.  Please also DEFINE in this file, with the exact names, `negAlgEquiv (E : WeierstrassCurve L) :
Func E ≃ₐ[L] Func E` (the negation `[-1]` of the function field) together with the API facts
`negAlgEquiv_mul_self` (it squares to `1`), `negAlgEquiv_genX` (it fixes `genX E`),
`negAlgEquiv_genY` (it sends `genY E` to `- genY E - a₁ genX E - a₃`), `negAlgEquiv_infCoordRing`
(its image of `infCoordRing E` is `infCoordRing E`) and `negAlgEquiv_infPlace` (its image of
`infPlace E` is `infPlace E`), so that downstream files can use `Work.MotC2.negAlgEquiv`; the
statement below then follows from those by `Classical.choose`/`exact`.

Route: the substitution `X ↦ X`, `Y ↦ -Y - a₁X - a₃` is an involutive automorphism of `L[X][X]`
preserving `polynomial E` *identically* (expand: the `a₁²X²`, `a₃²` and mixed terms cancel), hence
descends to `Coord E` (`AdjoinRoot.liftAlgHom`, or `AdjoinRoot.algEquivOfEq`); extend to
`Func E = FractionRing (Coord E)` via `IsFractionRing.liftAlgHom` (injective since the source is a
domain, the target a field, and the map is nonzero), and identify the extension with an equivalence
by extensionality on `Coord E` (`IsLocalization.algHom_ext`).
-/

/-! ## The negation `[-1]` of the function field

We build the substitution `X ↦ X`, `Y ↦ -Y - a₁X - a₃` on the affine coordinate ring
`Coord E = L[X,Y]/(W_E)` and descend it along `AdjoinRoot.liftAlgHom`; the resulting involutive
`L`-algebra automorphism extends to the fraction field `Func E = L(E)` by
`IsFractionRing.algEquivOfAlgEquiv`. -/

/-- The linear coefficient `a₁X + a₃` of the Weierstrass polynomial, as an element of `L[X]`. -/
noncomputable def linCoef (E : WeierstrassCurve L) : L[X] :=
  Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃

/-- The cubic coefficient `X³ + a₂X² + a₄X + a₆` of the Weierstrass polynomial. -/
noncomputable def cubCoef (E : WeierstrassCurve L) : L[X] :=
  Polynomial.X^3 + Polynomial.C E.a₂ * Polynomial.X^2 + Polynomial.C E.a₄ * Polynomial.X +
    Polynomial.C E.a₆

/-- The image of the class of `Y` under the negation substitution, in `Coord E`. -/
noncomputable def negSubst (E : WeierstrassCurve L) : Coord E :=
  - AdjoinRoot.root (polynomial E) - algebraMap (L[X]) (Coord E) (linCoef E)

/-! The substitution is a root of the Weierstrass polynomial: expanding
`Y² + (a₁X + a₃)Y - (X³ + a₂X² + a₄X + a₆)` at `Y ↦ -Y - a₁X - a₃` returns the same
polynomial (the `a₁²X²`, `a₃²` and mixed terms cancel). -/
lemma negSubst_eval (E : WeierstrassCurve L) :
    (polynomial E).eval₂ (algebraMap (L[X]) (Coord E)) (negSubst E) = 0 := by
  have key : ∀ y : Coord E,
      Polynomial.eval₂ (algebraMap (L[X]) (Coord E)) y (polynomial E) =
        y^2 + algebraMap (L[X]) (Coord E) (linCoef E) * y -
          algebraMap (L[X]) (Coord E) (cubCoef E) := by
    intro y
    simp only [WeierstrassCurve.Affine.polynomial, linCoef, cubCoef, Polynomial.eval₂_add,
      Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
  have hr : (AdjoinRoot.root (polynomial E))^2 +
      algebraMap (L[X]) (Coord E) (linCoef E) * AdjoinRoot.root (polynomial E) -
      algebraMap (L[X]) (Coord E) (cubCoef E) = 0 := by
    have h := AdjoinRoot.eval₂_root (polynomial E)
    rw [← AdjoinRoot.algebraMap_eq] at h
    rwa [key] at h
  rw [key (negSubst E), negSubst]
  linear_combination (norm := first | refl_ring1 | ring1) hr

/-- The descent of the negation substitution to an `L`-algebra endomorphism of `Coord E`. -/
noncomputable def negCoordHom (E : WeierstrassCurve L) : Coord E →ₐ[L] Coord E :=
  AdjoinRoot.liftAlgHom (polynomial E) (AdjoinRoot.ofAlgHom L (polynomial E)) (negSubst E)
    (by simpa only [AdjoinRoot.toRingHom_ofAlgHom, ← AdjoinRoot.algebraMap_eq]
      using negSubst_eval E)

lemma negCoordHom_of (E : WeierstrassCurve L) (r : L[X]) :
    negCoordHom E (AdjoinRoot.of (polynomial E) r) = AdjoinRoot.of (polynomial E) r := by
  simp [negCoordHom]

lemma negCoordHom_root (E : WeierstrassCurve L) :
    negCoordHom E (AdjoinRoot.root (polynomial E)) = negSubst E := by
  rw [negCoordHom, AdjoinRoot.liftAlgHom_root]

/-- The negation substitution is an involution on `Coord E`. -/
lemma negCoordHom_comp_self (E : WeierstrassCurve L) :
    (negCoordHom E).comp (negCoordHom E) = AlgHom.id L (Coord E) := by
  apply AdjoinRoot.algHom_ext'
  · ext
    simp [negCoordHom]
  · rw [AlgHom.comp_apply, negCoordHom_root]
    simp only [negSubst, AdjoinRoot.algebraMap_eq, map_sub, map_neg, negCoordHom_root,
      negCoordHom_of, AlgHom.id_apply]
    first | refl_ring1 | ring

/-- The negation `[-1]` as an `L`-algebra automorphism of the coordinate ring `Coord E`. -/
noncomputable def negCoordAlgEquiv (E : WeierstrassCurve L) : Coord E ≃ₐ[L] Coord E :=
  AlgEquiv.ofAlgHom (negCoordHom E) (negCoordHom E) (negCoordHom_comp_self E)
    (negCoordHom_comp_self E)

lemma negCoordAlgEquiv_coordX (E : WeierstrassCurve L) :
    negCoordAlgEquiv E (coordX E) = coordX E := by
  rw [negCoordAlgEquiv, AlgEquiv.ofAlgHom_apply, coordX, negCoordHom_of]

lemma negCoordAlgEquiv_coordY (E : WeierstrassCurve L) :
    negCoordAlgEquiv E (coordY E) = - coordY E - algebraMap (L[X]) (Coord E) (linCoef E) := by
  rw [negCoordAlgEquiv, AlgEquiv.ofAlgHom_apply, coordY, negCoordHom_root]
  rfl

lemma negCoordAlgEquiv_mul_self (E : WeierstrassCurve L) :
    negCoordAlgEquiv E * negCoordAlgEquiv E = 1 := by
  ext x
  rw [AlgEquiv.mul_apply, AlgEquiv.one_apply]
  have := AlgHom.congr_fun (negCoordHom_comp_self E) x
  rw [AlgHom.comp_apply, AlgHom.id_apply] at this
  simpa [negCoordAlgEquiv, AlgEquiv.ofAlgHom_apply] using this

/-! ## The negation `[-1]` of the function field -/

/-- The negation `[-1]` as an `L`-algebra automorphism of the function field `Func E = L(E)`,
extending the negation of the coordinate ring. -/
noncomputable def negAlgEquiv (E : WeierstrassCurve L) : Func E ≃ₐ[L] Func E :=
  IsFractionRing.algEquivOfAlgEquiv (negCoordAlgEquiv E)

lemma negAlgEquiv_genX (E : WeierstrassCurve L) : negAlgEquiv E (genX E) = genX E := by
  rw [genX, negAlgEquiv, IsFractionRing.algEquivOfAlgEquiv_algebraMap, negCoordAlgEquiv_coordX]

lemma algebraMap_X_func (E : WeierstrassCurve L) :
    algebraMap (L[X]) (Func E) Polynomial.X = genX E := by
  rw [IsScalarTower.algebraMap_apply L[X] (Coord E) (Func E), algebraMap_X_eq_coordX]
  rfl

lemma algebraMap_linCoef (E : WeierstrassCurve L) :
    algebraMap (L[X]) (Func E) (linCoef E) =
      algebraMap L (Func E) E.a₁ * genX E + algebraMap L (Func E) E.a₃ := by
  simp only [linCoef, map_add, map_mul, Polynomial.C_eq_algebraMap, algebraMap_X_func,
    IsScalarTower.algebraMap_apply L (L[X]) (Func E)]

lemma negAlgEquiv_genY (E : WeierstrassCurve L) :
    negAlgEquiv E (genY E) = - genY E - algebraMap L (Func E) E.a₁ * genX E -
      algebraMap L (Func E) E.a₃ := by
  rw [genY, negAlgEquiv, IsFractionRing.algEquivOfAlgEquiv_algebraMap, negCoordAlgEquiv_coordY]
  rw [map_sub, map_neg, ← IsScalarTower.algebraMap_apply L[X] (Coord E) (Func E) (linCoef E),
    algebraMap_linCoef]
  first | refl_ring1 | ring

/-- The negation squares to the identity. -/
lemma negAlgEquiv_mul_self (E : WeierstrassCurve L) : negAlgEquiv E * negAlgEquiv E = 1 := by
  have hcomp : (negAlgEquiv E).toAlgHom.comp (negAlgEquiv E).toAlgHom = AlgHom.id L (Func E) := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (Coord E))
    apply AlgHom.ext
    intro a
    simp only [AlgHom.comp_apply, AlgHom.id_apply]
    change (negAlgEquiv E) ((negAlgEquiv E) (algebraMap (Coord E) (Func E) a)) =
      algebraMap (Coord E) (Func E) a
    rw [negAlgEquiv, IsFractionRing.algEquivOfAlgEquiv_algebraMap,
      IsFractionRing.algEquivOfAlgEquiv_algebraMap]
    have h2 : negCoordAlgEquiv E (negCoordAlgEquiv E a) = a := by
      have := AlgEquiv.congr_fun (negCoordAlgEquiv_mul_self E) a
      simpa [AlgEquiv.mul_apply, AlgEquiv.one_apply] using this
    rw [h2]
  ext x
  rw [AlgEquiv.mul_apply, AlgEquiv.one_apply]
  exact AlgHom.congr_fun hcomp x

/-! ## The chart at infinity

`infPlace E` is, by the definition in `Defs`, the `L`-subalgebra of `L(E)` generated by the
chart-at-infinity coordinate ring `infCoordRing E = L[1/x, y/x²]` together with the inverses of the
elements of `infCoordRing E` lying outside the maximal ideal `infIdeal E = (1/x, y/x²)`.  The
negation permutes this generating set: it permutes `infCoordRing E` (`map_infCoordRing_eq_of` below)
and preserves membership in `infIdeal E` (`infIdeal_mem_of` below), hence permutes the set of
elements of `infCoordRing E` outside `infIdeal E` (`map_infPlace_eq_of`). -/

/-- The element `-w - a₁u - a₃u²` (the image of the chart coordinate `w = y/x²` under the negation
substitution) lies in the chart-at-infinity coordinate ring `L[u, w]`. -/
lemma neg_image_infW_mem (E : WeierstrassCurve L) :
    - infW E - algebraMap L (Func E) E.a₁ * infU E - algebraMap L (Func E) E.a₃ * (infU E)^2 ∈
      infCoordRing E := by
  have hu : infU E ∈ infCoordRing E := Algebra.subset_adjoin (by simp)
  have hw : infW E ∈ infCoordRing E := Algebra.subset_adjoin (by simp)
  exact sub_mem (sub_mem (neg_mem hw) (mul_mem (Subalgebra.algebraMap_mem _ _) hu))
    (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem hu 2))

/-- The same element `-w - a₁u - a₃u²` lies in the maximal ideal `(1/x, y/x²)` of the chart at
infinity. -/
lemma neg_image_infW_mem_infIdeal (E : WeierstrassCurve L) :
    - infW E - algebraMap L (Func E) E.a₁ * infU E - algebraMap L (Func E) E.a₃ * (infU E)^2 ∈
      infIdeal E := by
  have hu : infU E ∈ infIdeal E := Submodule.subset_span (by simp)
  have hw : infW E ∈ infIdeal E := Submodule.subset_span (by simp)
  have hu2 : (infU E)^2 ∈ infIdeal E := by
    have h := Submodule.smul_mem (infIdeal E)
      (⟨infU E, Algebra.subset_adjoin (by simp)⟩ : infCoordRing E) hu
    simpa [Algebra.smul_def, Subalgebra.algebraMap_apply, pow_two] using h
  have h1 : algebraMap L (Func E) E.a₁ * infU E ∈ infIdeal E := by
    have h := Submodule.smul_mem (infIdeal E)
      (⟨algebraMap L (Func E) E.a₁, Subalgebra.algebraMap_mem _ _⟩ : infCoordRing E) hu
    simpa [Algebra.smul_def, Subalgebra.algebraMap_apply] using h
  have h3 : algebraMap L (Func E) E.a₃ * (infU E)^2 ∈ infIdeal E := by
    have h := Submodule.smul_mem (infIdeal E)
      (⟨algebraMap L (Func E) E.a₃, Subalgebra.algebraMap_mem _ _⟩ : infCoordRing E) hu2
    simpa [Algebra.smul_def, Subalgebra.algebraMap_apply] using h
  exact sub_mem (sub_mem (neg_mem hw) h1) h3

/-- On the chart at infinity `u = 1/x`, `w = y/x²`, the negation acts by
`u ↦ u`, `w ↦ -w - a₁u - a₃u²`; hence it maps `infCoordRing E` into itself. -/
lemma map_infCoordRing_le (E : WeierstrassCurve L) (τ : Func E ≃ₐ[L] Func E)
    (hx : τ (genX E) = genX E)
    (hy : τ (genY E) = - genY E - algebraMap L (Func E) E.a₁ * genX E -
      algebraMap L (Func E) E.a₃) :
    Subalgebra.map τ.toAlgHom (infCoordRing E) ≤ infCoordRing E := by
  have hx' : τ.toAlgHom (genX E) = genX E := hx
  have hy' : τ.toAlgHom (genY E) = - genY E - algebraMap L (Func E) E.a₁ * genX E -
      algebraMap L (Func E) E.a₃ := hy
  have hu : τ.toAlgHom (infU E) = infU E := by
    rw [infU, map_inv₀, hx']
  have hw : τ.toAlgHom (infW E) = - infW E - algebraMap L (Func E) E.a₁ * infU E -
      algebraMap L (Func E) E.a₃ * (infU E)^2 := by
    rw [infW, infU, map_div₀, map_pow, hx', hy']
    field_simp
  rw [infCoordRing, AlgHom.map_adjoin]
  refine Algebra.adjoin_le_iff.mpr ?_
  rintro y ⟨x, hxmem, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxmem
  rcases hxmem with rfl | rfl
  · rw [hu]; exact Algebra.subset_adjoin (by simp)
  · rw [hw]; exact neg_image_infW_mem E

/-- Any `L`-algebra automorphism acting on `genX`, `genY` by the negation formulas maps
`infCoordRing E` onto itself. -/
lemma map_infCoordRing_eq_of (E : WeierstrassCurve L) (τ : Func E ≃ₐ[L] Func E)
    (hx : τ (genX E) = genX E)
    (hy : τ (genY E) = - genY E - algebraMap L (Func E) E.a₁ * genX E -
      algebraMap L (Func E) E.a₃) :
    Subalgebra.map τ.toAlgHom (infCoordRing E) = infCoordRing E := by
  have hxs : τ.symm (genX E) = genX E := by
    have h := congrArg (⇑τ.symm) hx
    simpa using h.symm
  have hys : τ.symm (genY E) = - genY E - algebraMap L (Func E) E.a₁ * genX E -
      algebraMap L (Func E) E.a₃ := by
    have h := congrArg (⇑τ.symm) hy
    simp only [AlgEquiv.symm_apply_apply, map_sub, map_neg, map_mul, hxs, AlgEquiv.commutes] at h
    linear_combination (norm := first | refl_ring1 | ring1) h
  refine le_antisymm (map_infCoordRing_le E τ hx hy) ?_
  intro x hxmem
  refine Subalgebra.mem_map.mpr ⟨τ.symm x, ?_, ?_⟩
  · exact map_infCoordRing_le E τ.symm hxs hys (Subalgebra.mem_map.mpr ⟨x, hxmem, rfl⟩)
  · simpa using AlgEquiv.apply_symm_apply τ x

/-- The negation formula `u ↦ u`, `w ↦ -w - a₁u - a₃u²` on the chart coordinates preserves
membership in the maximal ideal `(u, w)` of the chart at infinity. -/
lemma infIdeal_mem_of (E : WeierstrassCurve L) (τ : Func E ≃ₐ[L] Func E)
    (hring : Subalgebra.map τ.toAlgHom (infCoordRing E) ≤ infCoordRing E)
    (hu : τ.toAlgHom (infU E) = infU E)
    (hw : τ.toAlgHom (infW E) = - infW E - algebraMap L (Func E) E.a₁ * infU E -
      algebraMap L (Func E) E.a₃ * (infU E)^2) :
    ∀ x : Func E, x ∈ infIdeal E → τ.toAlgHom x ∈ infIdeal E := by
  intro x hx
  refine Submodule.span_induction (p := fun x _ => τ.toAlgHom x ∈ infIdeal E) ?_ ?_ ?_ ?_ hx
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · rw [hu]; exact Submodule.subset_span (by simp)
    · rw [hw]; exact neg_image_infW_mem_infIdeal E
  · rw [map_zero]; exact Submodule.zero_mem (infIdeal E)
  · intro a b _ _ ha hb
    rw [map_add]; exact add_mem ha hb
  · intro c a _ ha
    have hc : τ.toAlgHom (c : Func E) ∈ infCoordRing E :=
      hring (Subalgebra.mem_map.mpr ⟨(c : Func E), c.2, rfl⟩)
    have h := Submodule.smul_mem (infIdeal E)
      (⟨τ.toAlgHom (c : Func E), hc⟩ : infCoordRing E) ha
    simpa [map_mul, Algebra.smul_def, Subalgebra.algebraMap_apply] using h

/-- Any `L`-algebra automorphism of `L(E)` acting on the chart coordinates by `u ↦ u` and
`w ↦ -w - a₁u - a₃u²` maps the local ring `infPlace E` of the point at infinity onto itself. -/
lemma map_infPlace_eq_of (E : WeierstrassCurve L) (τ : Func E ≃ₐ[L] Func E)
    (hx : τ (genX E) = genX E)
    (hy : τ (genY E) = - genY E - algebraMap L (Func E) E.a₁ * genX E -
      algebraMap L (Func E) E.a₃) :
    Subalgebra.map τ.toAlgHom (infPlace E) = infPlace E := by
  have hx' : τ.toAlgHom (genX E) = genX E := hx
  have hy' : τ.toAlgHom (genY E) = - genY E - algebraMap L (Func E) E.a₁ * genX E -
      algebraMap L (Func E) E.a₃ := hy
  have hring : Subalgebra.map τ.toAlgHom (infCoordRing E) ≤ infCoordRing E :=
    (map_infCoordRing_eq_of E τ hx hy).le
  have hu : τ.toAlgHom (infU E) = infU E := by rw [infU, map_inv₀, hx']
  have hw : τ.toAlgHom (infW E) = - infW E - algebraMap L (Func E) E.a₁ * infU E -
      algebraMap L (Func E) E.a₃ * (infU E)^2 := by
    rw [infW, infU, map_div₀, map_pow, hx', hy']
    field_simp
  have hxs : τ.symm (genX E) = genX E := by
    have h := congrArg (⇑τ.symm) hx
    simpa using h.symm
  have hys : τ.symm (genY E) = - genY E - algebraMap L (Func E) E.a₁ * genX E -
      algebraMap L (Func E) E.a₃ := by
    have h := congrArg (⇑τ.symm) hy
    simp only [AlgEquiv.symm_apply_apply, map_sub, map_neg, map_mul, hxs, AlgEquiv.commutes] at h
    linear_combination (norm := first | refl_ring1 | ring1) h
  have hxs' : τ.symm.toAlgHom (genX E) = genX E := hxs
  have hys' : τ.symm.toAlgHom (genY E) = - genY E - algebraMap L (Func E) E.a₁ * genX E -
      algebraMap L (Func E) E.a₃ := hys
  have hring' : Subalgebra.map τ.symm.toAlgHom (infCoordRing E) ≤ infCoordRing E :=
    (map_infCoordRing_eq_of E τ.symm hxs hys).le
  have hu' : τ.symm.toAlgHom (infU E) = infU E := by rw [infU, map_inv₀, hxs']
  have hw' : τ.symm.toAlgHom (infW E) = - infW E - algebraMap L (Func E) E.a₁ * infU E -
      algebraMap L (Func E) E.a₃ * (infU E)^2 := by
    rw [infW, infU, map_div₀, map_pow, hxs', hys']
    field_simp
  have hI : ∀ x : Func E, x ∈ infIdeal E → τ.toAlgHom x ∈ infIdeal E :=
    infIdeal_mem_of E τ hring hu hw
  have hI' : ∀ x : Func E, x ∈ infIdeal E → τ.symm.toAlgHom x ∈ infIdeal E :=
    infIdeal_mem_of E τ.symm hring' hu' hw'
  rw [infPlace]
  set U : Set (Func E) := {r : Func E | r ∈ infCoordRing E ∧ r ∉ infIdeal E} with hU
  have hSU : τ.toAlgHom '' U = U := by
    ext r
    constructor
    · rintro ⟨s, ⟨hsS, hsI⟩, rfl⟩
      refine ⟨hring (Subalgebra.mem_map.mpr ⟨s, hsS, rfl⟩), fun h => hsI ?_⟩
      simpa using hI' (τ.toAlgHom s) h
    · rintro ⟨hrS, hrI⟩
      refine ⟨τ.symm r, ⟨hring' (Subalgebra.mem_map.mpr ⟨r, hrS, rfl⟩), fun h => hrI ?_⟩, ?_⟩
      · simpa using hI (τ.symm r) h
      · simp
  have himg : τ.toAlgHom '' ((fun r => r⁻¹) '' U) = (fun r => r⁻¹) '' U := by
    ext y
    constructor
    · rintro ⟨z, ⟨r, hr, rfl⟩, rfl⟩
      refine ⟨τ.toAlgHom r, hSU ▸ ⟨r, hr, rfl⟩, ?_⟩
      rw [map_inv₀]
    · rintro ⟨r, hr, rfl⟩
      refine ⟨(τ.symm r)⁻¹, ⟨τ.symm r, ⟨?_, ?_⟩, rfl⟩, ?_⟩
      · exact hring' (Subalgebra.mem_map.mpr ⟨r, hr.1, rfl⟩)
      · intro h
        exact hr.2 (by simpa using hI (τ.symm r) h)
      · rw [map_inv₀]
        have h2 : τ.toAlgHom (τ.symm r) = r := AlgEquiv.apply_symm_apply τ r
        rw [h2]
  rw [AlgHom.map_adjoin, Set.image_union, ← Subalgebra.coe_map,
    map_infCoordRing_eq_of E τ hx hy, himg]

lemma negAlgEquiv_infCoordRing (E : WeierstrassCurve L) :
    Subalgebra.map (negAlgEquiv E).toAlgHom (infCoordRing E) = infCoordRing E :=
  map_infCoordRing_eq_of E (negAlgEquiv E) (negAlgEquiv_genX E) (negAlgEquiv_genY E)

lemma negAlgEquiv_infPlace (E : WeierstrassCurve L) :
    Subalgebra.map (negAlgEquiv E).toAlgHom (infPlace E) = infPlace E :=
  map_infPlace_eq_of E (negAlgEquiv E) (negAlgEquiv_genX E) (negAlgEquiv_genY E)

/-- **The negation `[-1]` of the Weierstrass function field.**  The substitution
`X ↦ X`, `Y ↦ -Y - a₁X - a₃` defines an involutive `L`-algebra automorphism of `L(E)` fixing the
point at infinity; as a witness of the target statement it also carries the local ring `infPlace E`
onto itself. -/
theorem Negation (L : Type*) [Field L] (E : WeierstrassCurve L) :
    ∃ σ : Work.MotC2.Func E ≃ₐ[L] Work.MotC2.Func E,
      σ * σ = 1 ∧
      σ (Work.MotC2.genX E) = Work.MotC2.genX E ∧
      σ (Work.MotC2.genY E) = - Work.MotC2.genY E -
        algebraMap L (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E -
        algebraMap L (Work.MotC2.Func E) E.a₃ ∧
      Subalgebra.map σ.toAlgHom (Work.MotC2.infPlace E) = Work.MotC2.infPlace E := by
  exact ⟨negAlgEquiv E, negAlgEquiv_mul_self E, negAlgEquiv_genX E, negAlgEquiv_genY E,
    negAlgEquiv_infPlace E⟩

end Work.MotC2
