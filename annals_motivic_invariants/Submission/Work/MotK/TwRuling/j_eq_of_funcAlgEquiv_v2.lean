import Mathlib
import Submission.Work.MotC2.PoleOrder
import Submission.Work.MotC2.PoleCond
import Submission.Work.MotC2.ExistsVariableChange
import Submission.Work.MotC2.VariableChange
import Submission.Work.MotC2.Places
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.Translation
import Submission.Work.MotC2.IsRatPlaceMap
import Submission.Work.MotC2.CoordPreserved
import Submission.Work.MotC2.TransPlace
import Submission.Work.MotC2.SubstCoeffs
import Submission.Work.MotK.TwRuling.IsRatPlaceMap_v2
import Submission.Work.MotK.TwRuling.affRing_map_eq
import Submission.Work.MotK.TwRuling.PoleCond_v2
import Submission.Work.MotK.TwRuling.cross_coeff_three
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

/-!
# `j`-invariants of Weierstrass curves with isomorphic function fields

If two elliptic Weierstrass curves `E`, `E'` over a field `L` have `L`-isomorphic function fields,
then `E.j = E'.j`.

The proof reduces (via the classification of rational places of `L(E')/L`, applied to the image of
the place at infinity of `E` under the isomorphism) to the case where the isomorphism `Ψ` preserves
the point at infinity `O`.  In that case:

* `Ψ` preserves the affine coordinate rings (`affRing_map_eq`) and the pole conditions
  (`PoleCond_v2`), so by `PoleOrder` the images of the coordinates are
  `Ψ x = a + b x'`, `Ψ y = c + d x' + e y'` with `a,b,c,d,e ∈ L`;
* the substitution satisfies the Weierstrass relation of `E` in `L(E')`, whence `e² = b³`
  (`cross_coeff_three`);
* consequently `(x', y')` is a point of the curve `C • E` for `C = ⟨e/b, a, d/b, c⟩`
  (`equation_variableChange`), and since `(x', y')` is also a point of `E'` and
  `1, x', y', x'², x'y'` are linearly independent over `L`, the two curves coincide;
* `variableChange_j` finishes.
-/

namespace Work.MotK.TwRuling

open Polynomial WeierstrassCurve.Affine

set_option maxHeartbeats 1000000

variable {L : Type*} [Field L]

/-- Membership in the affine coordinate ring: `x ∈ L[x,y]` iff it is the image of an element of
the coordinate ring `L[X,Y]/(W_E)`. -/
lemma jv2_mem_affRing_iff (E : WeierstrassCurve L) (x : Work.MotC2.Func E) :
    x ∈ Work.MotC2.affRing E ↔
      ∃ r : Work.MotC2.Coord E, algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) r = x := by
  unfold Work.MotC2.affRing
  set φ : Work.MotC2.Coord E →ₐ[L] Work.MotC2.Func E := Algebra.algHom L _ _ with hφ
  constructor
  · intro hx
    have hle : Algebra.adjoin L (Set.range (algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E))) ≤
        φ.range :=
      Algebra.adjoin_le (by rintro y ⟨r, rfl⟩; exact ⟨r, rfl⟩)
    obtain ⟨r, hr⟩ := (AlgHom.mem_range (φ := φ)).mp (hle hx)
    exact ⟨r, hr⟩
  · rintro ⟨r, rfl⟩
    exact Algebra.subset_adjoin ⟨r, rfl⟩

/-- The coordinate `x = genX E` of the function field is not a constant. -/
lemma jv2_genX_ne_const (E : WeierstrassCurve L) (a : L) :
    Work.MotC2.genX E ≠ algebraMap L (Work.MotC2.Func E) a := by
  intro h
  have h1 : algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) (Work.MotC2.coordX E) =
      algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E)
        (algebraMap L (Work.MotC2.Coord E) a) := by
    rw [← IsScalarTower.algebraMap_apply L (Work.MotC2.Coord E) (Work.MotC2.Func E)]
    exact h
  have h2 : Work.MotC2.coordX E = algebraMap L (Work.MotC2.Coord E) a :=
    IsFractionRing.injective (Work.MotC2.Coord E) (Work.MotC2.Func E) h1
  have h3 : algebraMap (Polynomial L) (Work.MotC2.Coord E) Polynomial.X =
      algebraMap L (Work.MotC2.Coord E) a := by
    rw [Work.MotC2.algebraMap_X_eq_coordX, h2]
  have h3' : algebraMap (Polynomial L) (Work.MotC2.Coord E) (Polynomial.C a) =
      algebraMap L (Work.MotC2.Coord E) a := by
    rw [Polynomial.C_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply L (Polynomial L) (Work.MotC2.Coord E)]
  have h4 : algebraMap (Polynomial L) (Work.MotC2.Coord E) (Polynomial.X - Polynomial.C a) = 0 := by
    rw [map_sub, h3, h3', sub_self]
  have h5 : (Polynomial.X - Polynomial.C a) • (1 : Work.MotC2.Coord E) = 0 := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact h4
  have h6 : Polynomial.X - Polynomial.C a = 0 := by
    have hh := CoordinateRing.smul_basis_eq_zero (W' := E)
      (p := Polynomial.X - Polynomial.C a) (q := 0) (by simpa using h5)
    exact hh.1
  exact Polynomial.X_sub_C_ne_zero a h6

/-- Linear independence of `1, x, y, x², xy` over `L` in the function field `L(E)`. -/
lemma jv2_linear_combo_eq_zero (E : WeierstrassCurve L) (k₁ k₂ k₃ k₄ k₅ : L)
    (h : algebraMap L (Work.MotC2.Func E) k₁ * (Work.MotC2.genX E * Work.MotC2.genY E) +
          algebraMap L (Work.MotC2.Func E) k₂ * (Work.MotC2.genX E) ^ 2 +
          algebraMap L (Work.MotC2.Func E) k₃ * Work.MotC2.genY E +
          algebraMap L (Work.MotC2.Func E) k₄ * Work.MotC2.genX E +
          algebraMap L (Work.MotC2.Func E) k₅ = 0) :
    k₁ = 0 ∧ k₂ = 0 ∧ k₃ = 0 ∧ k₄ = 0 ∧ k₅ = 0 := by
  set P : Polynomial L := Polynomial.C k₅ + Polynomial.C k₄ * Polynomial.X +
    Polynomial.C k₂ * Polynomial.X ^ 2 with hP
  set Q : Polynomial L := Polynomial.C k₃ + Polynomial.C k₁ * Polynomial.X with hQ
  have h2 : Polynomial.aeval (Work.MotC2.genX E) P +
      Polynomial.aeval (Work.MotC2.genX E) Q * Work.MotC2.genY E = 0 := by
    rw [hP, hQ]
    simp only [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X,
      map_pow]
    linear_combination (norm := first | refl_ring1 | ring1) h
  have h3 : algebraMap (Polynomial L) (Work.MotC2.Coord E) P +
      algebraMap (Polynomial L) (Work.MotC2.Coord E) Q * Work.MotC2.coordY E = 0 := by
    apply IsFractionRing.injective (Work.MotC2.Coord E) (Work.MotC2.Func E)
    rw [map_add, map_mul, map_zero]
    rw [← IsScalarTower.algebraMap_apply (Polynomial L) (Work.MotC2.Coord E) (Work.MotC2.Func E) P,
      ← IsScalarTower.algebraMap_apply (Polynomial L) (Work.MotC2.Coord E) (Work.MotC2.Func E) Q]
    have hgenY : algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) (Work.MotC2.coordY E) =
        Work.MotC2.genY E := rfl
    rw [hgenY]
    have hQ2 : algebraMap (Polynomial L) (Work.MotC2.Func E) P =
        Polynomial.aeval (Work.MotC2.genX E) P := Work.MotC2.algebraMap_poly_func E P
    have hQ3 : algebraMap (Polynomial L) (Work.MotC2.Func E) Q =
        Polynomial.aeval (Work.MotC2.genX E) Q := Work.MotC2.algebraMap_poly_func E Q
    rw [hQ2, hQ3]
    exact h2
  have h4 : P • (1 : Work.MotC2.Coord E) + Q • Work.MotC2.coordY E = 0 := by
    rw [Work.MotC2.smul_one_eq E P, Work.MotC2.smul_coordY_eq E Q]
    exact h3
  obtain ⟨hp, hq⟩ := CoordinateRing.smul_basis_eq_zero (W' := E) h4
  have hk₁ : k₁ = 0 := by
    have hh := congrArg (fun p : Polynomial L => p.coeff 1) hq
    rw [hQ] at hh
    simpa [Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C] using hh
  have hk₃ : k₃ = 0 := by
    have hh := congrArg (fun p : Polynomial L => p.coeff 0) hq
    rw [hQ] at hh
    simpa [Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C] using hh
  have hk₅ : k₅ = 0 := by
    have hh := congrArg (fun p : Polynomial L => p.coeff 0) hp
    rw [hP] at hh
    simpa [Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C] using hh
  have hk₄ : k₄ = 0 := by
    have hh := congrArg (fun p : Polynomial L => p.coeff 1) hp
    rw [hP] at hh
    simpa [Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C] using hh
  have hk₂ : k₂ = 0 := by
    have hh := congrArg (fun p : Polynomial L => p.coeff 2) hp
    rw [hP] at hh
    simpa [Polynomial.coeff_add, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_mul_X_pow,
      Polynomial.coeff_C] using hh
  exact ⟨hk₁, hk₂, hk₃, hk₄, hk₅⟩

/-- A Weierstrass curve over `L` is determined by any point of it in `L(E)` with generic
coordinates: two curves for which `(genX E, genY E)` is a solution coincide. -/
theorem jv2_ext_of_equation (E : WeierstrassCurve L) (W₁ W₂ : WeierstrassCurve L)
    (h₁ : Equation (W₁.map (algebraMap L (Work.MotC2.Func E))) (Work.MotC2.genX E)
      (Work.MotC2.genY E))
    (h₂ : Equation (W₂.map (algebraMap L (Work.MotC2.Func E))) (Work.MotC2.genX E)
      (Work.MotC2.genY E)) :
    W₁ = W₂ := by
  rw [equation_iff'] at h₁ h₂
  rw [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h₁ h₂
  have h : algebraMap L (Work.MotC2.Func E) (W₁.a₁ - W₂.a₁) *
        (Work.MotC2.genX E * Work.MotC2.genY E) +
      algebraMap L (Work.MotC2.Func E) (W₂.a₂ - W₁.a₂) * (Work.MotC2.genX E) ^ 2 +
      algebraMap L (Work.MotC2.Func E) (W₁.a₃ - W₂.a₃) * Work.MotC2.genY E +
      algebraMap L (Work.MotC2.Func E) (W₂.a₄ - W₁.a₄) * Work.MotC2.genX E +
      algebraMap L (Work.MotC2.Func E) (W₂.a₆ - W₁.a₆) = 0 := by
    rw [map_sub, map_sub, map_sub, map_sub, map_sub]
    linear_combination (norm := first | refl_ring1 | ring1) h₁ - h₂
  obtain ⟨e1, e2, e3, e4, e5⟩ := jv2_linear_combo_eq_zero E _ _ _ _ _ h
  exact WeierstrassCurve.ext (sub_eq_zero.mp e1)
    (sub_eq_zero.mp (by linear_combination -e2)) (sub_eq_zero.mp e3)
    (sub_eq_zero.mp (by linear_combination -e4)) (sub_eq_zero.mp (by linear_combination -e5))

/-- The defining property of the change of variables `(X,Y) ↦ (u²X + r, u³Y + u²sX + t)`: the
point `(x,y)` lies on `C • W` iff the transformed point lies on `W`. -/
lemma jv2_equation_variableChange (L : Type*) [Field L] (C : WeierstrassCurve.VariableChange L)
    (W : WeierstrassCurve L) (x y : L) :
    Equation (C • W) x y ↔
      Equation W ((C.u : L) ^ 2 * x + C.r)
        ((C.u : L) ^ 3 * y + C.s * (C.u : L) ^ 2 * x + C.t) := by
  have hu : (C.u : L) ≠ 0 := Units.ne_zero C.u
  rw [equation_iff', equation_iff']
  have key : ((C.u : L) ^ 3 * y + C.s * (C.u : L) ^ 2 * x + C.t) ^ 2 +
        W.a₁ * ((C.u : L) ^ 2 * x + C.r) *
          ((C.u : L) ^ 3 * y + C.s * (C.u : L) ^ 2 * x + C.t) +
        W.a₃ * ((C.u : L) ^ 3 * y + C.s * (C.u : L) ^ 2 * x + C.t) -
        (((C.u : L) ^ 2 * x + C.r) ^ 3 + W.a₂ * ((C.u : L) ^ 2 * x + C.r) ^ 2 +
          W.a₄ * ((C.u : L) ^ 2 * x + C.r) + W.a₆)
      = (C.u : L) ^ 6 * (y ^ 2 + (C • W).a₁ * x * y + (C • W).a₃ * y -
          (x ^ 3 + (C • W).a₂ * x ^ 2 + (C • W).a₄ * x + (C • W).a₆)) := by
    rw [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆, Units.val_inv_eq_inv_val]
    field_simp
    first | refl_ring1 | ring
  rw [key]
  constructor
  · intro h; rw [h, mul_zero]
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (pow_ne_zero 6 hu)
    · exact h

/-- **Core case.**  An isomorphism of function fields sending the place at infinity of `E` onto
that of `E'` (hence, in particular, the origin onto the origin) forces equal `j`-invariants. -/
theorem jv2_j_eq_of_placeAtO (L : Type*) [Field L] (E E' : WeierstrassCurve L) [E.IsElliptic]
    [E'.IsElliptic] (Ψ : Work.MotC2.Func E ≃ₐ[L] Work.MotC2.Func E')
    (hΨ : Subalgebra.map Ψ.toAlgHom (Work.MotC2.infPlace E) = Work.MotC2.infPlace E') :
    E.j = E'.j := by
  obtain ⟨hpx, hpy⟩ := PoleCond_v2 L E E' Ψ hΨ
  have hA : Subalgebra.map Ψ.toAlgHom (Work.MotC2.affRing E) = Work.MotC2.affRing E' :=
    affRing_map_eq L E E' Ψ hΨ
  have hxmem : Ψ (Work.MotC2.genX E) ∈ Work.MotC2.affRing E' := by
    rw [← hA]
    exact Subalgebra.mem_map.mpr ⟨Work.MotC2.genX E,
      (jv2_mem_affRing_iff E _).mpr ⟨Work.MotC2.coordX E, rfl⟩, rfl⟩
  have hymem : Ψ (Work.MotC2.genY E) ∈ Work.MotC2.affRing E' := by
    rw [← hA]
    exact Subalgebra.mem_map.mpr ⟨Work.MotC2.genY E,
      (jv2_mem_affRing_iff E _).mpr ⟨Work.MotC2.coordY E, rfl⟩, rfl⟩
  obtain ⟨r₁, hr₁⟩ := (jv2_mem_affRing_iff E' _).mp hxmem
  obtain ⟨r₂, hr₂⟩ := (jv2_mem_affRing_iff E' _).mp hymem
  rw [← hr₁] at hpx
  rw [← hr₂] at hpy
  obtain ⟨a, b, hab⟩ := ((Work.MotC2.PoleOrder L E').1 r₁).mp hpx
  obtain ⟨c, d, e, hcde⟩ := ((Work.MotC2.PoleOrder L E').2 r₂).mp hpy
  have hu : Ψ (Work.MotC2.genX E) = algebraMap L (Work.MotC2.Func E') a +
      algebraMap L (Work.MotC2.Func E') b * Work.MotC2.genX E' := by
    rw [← hr₁]; exact hab
  have hv : Ψ (Work.MotC2.genY E) = algebraMap L (Work.MotC2.Func E') c +
      algebraMap L (Work.MotC2.Func E') d * Work.MotC2.genX E' +
        algebraMap L (Work.MotC2.Func E') e * Work.MotC2.genY E' := by
    rw [← hr₂]; exact hcde
  have hb : b ≠ 0 := by
    intro hb0
    have h3 : Ψ (Work.MotC2.genX E) = algebraMap L (Work.MotC2.Func E') a := by
      rw [hu, hb0, map_zero, zero_mul, add_zero]
    have h4 := congrArg Ψ.symm h3
    simp only [AlgEquiv.symm_apply_apply, AlgEquiv.commutes] at h4
    exact jv2_genX_ne_const E a h4
  have hrel : (algebraMap L (Work.MotC2.Func E') c + algebraMap L (Work.MotC2.Func E') d *
          Work.MotC2.genX E' + algebraMap L (Work.MotC2.Func E') e * Work.MotC2.genY E') ^ 2 +
      algebraMap L (Work.MotC2.Func E') E.a₁ *
          (algebraMap L (Work.MotC2.Func E') a +
            algebraMap L (Work.MotC2.Func E') b * Work.MotC2.genX E') *
          (algebraMap L (Work.MotC2.Func E') c + algebraMap L (Work.MotC2.Func E') d *
              Work.MotC2.genX E' + algebraMap L (Work.MotC2.Func E') e * Work.MotC2.genY E') +
      algebraMap L (Work.MotC2.Func E') E.a₃ *
          (algebraMap L (Work.MotC2.Func E') c + algebraMap L (Work.MotC2.Func E') d *
              Work.MotC2.genX E' + algebraMap L (Work.MotC2.Func E') e * Work.MotC2.genY E') =
      (algebraMap L (Work.MotC2.Func E') a +
          algebraMap L (Work.MotC2.Func E') b * Work.MotC2.genX E') ^ 3 +
        algebraMap L (Work.MotC2.Func E') E.a₂ *
          (algebraMap L (Work.MotC2.Func E') a +
            algebraMap L (Work.MotC2.Func E') b * Work.MotC2.genX E') ^ 2 +
        algebraMap L (Work.MotC2.Func E') E.a₄ *
          (algebraMap L (Work.MotC2.Func E') a +
            algebraMap L (Work.MotC2.Func E') b * Work.MotC2.genX E') +
        algebraMap L (Work.MotC2.Func E') E.a₆ := by
    rw [← hu, ← hv]
    have h := congrArg Ψ (Work.MotC2.genY_sq_relation E)
    simpa only [map_add, map_mul, map_pow, AlgEquiv.commutes, pow_two] using h
  have he2 : e ^ 2 = b ^ 3 := cross_coeff_three L E E' a b c d e hrel
  have he : e ≠ 0 := by
    intro he0
    have h3 : b ^ 3 = 0 := by rw [← he2, he0]; ring
    exact hb ((pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp h3)
  have hdiv2 : (e / b) ^ 2 = b := by
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hb)]
    linear_combination (norm := first | refl_ring1 | ring1) he2
  have hdiv3 : (e / b) ^ 3 = e := by
    rw [div_pow, div_eq_iff (pow_ne_zero 3 hb), show e ^ 3 = e * e ^ 2 from by ring, he2]
  have hdivs : (d / b) * b = d := div_mul_cancel₀ d hb
  let C : WeierstrassCurve.VariableChange L :=
    ⟨Units.mk0 (e / b) (div_ne_zero he hb), a, d / b, c⟩
  have hX : ((C.map (algebraMap L (Work.MotC2.Func E'))).u : Work.MotC2.Func E') ^ 2 *
        Work.MotC2.genX E' +
      (C.map (algebraMap L (Work.MotC2.Func E'))).r = Ψ (Work.MotC2.genX E) := by
    have h1 : ((C.map (algebraMap L (Work.MotC2.Func E'))).u : Work.MotC2.Func E') =
        algebraMap L (Work.MotC2.Func E') (e / b) := by
      rw [WeierstrassCurve.VariableChange.map_u, Units.coe_map]
      rfl
    have h2 : (C.map (algebraMap L (Work.MotC2.Func E'))).r =
        algebraMap L (Work.MotC2.Func E') a := by
      rw [WeierstrassCurve.VariableChange.map_r]
    rw [h1, h2, hu, ← map_pow, hdiv2]
    first | refl_ring1 | ring
  have hY : ((C.map (algebraMap L (Work.MotC2.Func E'))).u : Work.MotC2.Func E') ^ 3 *
        Work.MotC2.genY E' +
      (C.map (algebraMap L (Work.MotC2.Func E'))).s *
        ((C.map (algebraMap L (Work.MotC2.Func E'))).u : Work.MotC2.Func E') ^ 2 *
        Work.MotC2.genX E' +
      (C.map (algebraMap L (Work.MotC2.Func E'))).t = Ψ (Work.MotC2.genY E) := by
    have h1 : ((C.map (algebraMap L (Work.MotC2.Func E'))).u : Work.MotC2.Func E') =
        algebraMap L (Work.MotC2.Func E') (e / b) := by
      rw [WeierstrassCurve.VariableChange.map_u, Units.coe_map]
      rfl
    have h2 : (C.map (algebraMap L (Work.MotC2.Func E'))).s =
        algebraMap L (Work.MotC2.Func E') (d / b) := by
      rw [WeierstrassCurve.VariableChange.map_s]
    have h3 : (C.map (algebraMap L (Work.MotC2.Func E'))).t =
        algebraMap L (Work.MotC2.Func E') c := by
      rw [WeierstrassCurve.VariableChange.map_t]
    rw [h1, h2, h3, hv, ← map_pow, ← map_pow, hdiv3, hdiv2, ← map_mul, hdivs]
    first | refl_ring1 | ring
  have hEeq : Equation (E.map (algebraMap L (Work.MotC2.Func E'))) (Ψ (Work.MotC2.genX E))
      (Ψ (Work.MotC2.genY E)) := by
    rw [equation_iff]
    have h := congrArg Ψ (Work.MotC2.genY_sq_relation E)
    simpa only [map_add, map_mul, map_pow, AlgEquiv.commutes, WeierstrassCurve.map_a₁,
      WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
      WeierstrassCurve.map_a₆] using h
  have hCE : Equation ((C • E).map (algebraMap L (Work.MotC2.Func E'))) (Work.MotC2.genX E')
      (Work.MotC2.genY E') := by
    rw [← WeierstrassCurve.map_variableChange]
    refine (jv2_equation_variableChange (Work.MotC2.Func E')
      (C.map (algebraMap L (Work.MotC2.Func E'))) (E.map (algebraMap L (Work.MotC2.Func E')))
      (Work.MotC2.genX E') (Work.MotC2.genY E')).mpr ?_
    rw [hX, hY]
    exact hEeq
  have hE'eq : Equation (E'.map (algebraMap L (Work.MotC2.Func E'))) (Work.MotC2.genX E')
      (Work.MotC2.genY E') := by
    rw [equation_iff]
    simpa only [WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
      WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] using Work.MotC2.genY_sq_relation E'
  have hEqi : C • E = E' := jv2_ext_of_equation (E := E') (C • E) E' hCE hE'eq
  have h2 : (C • E).j = E'.j := by simp_rw [hEqi]
  calc E.j = (C • E).j := (WeierstrassCurve.variableChange_j E C).symm
    _ = E'.j := h2

theorem j_eq_of_funcAlgEquiv_v2 (L : Type) [Field L] (E E' : WeierstrassCurve L)
    [E.IsElliptic] [E'.IsElliptic]
    (Θ : WeierstrassCurve.Affine.FunctionField E ≃ₐ[L] WeierstrassCurve.Affine.FunctionField E') :
    E.j = E'.j := by
  classical
  have hS : Work.MotC2.IsRatPlace E' (Subalgebra.map Θ.toAlgHom (Work.MotC2.infPlace E)) :=
    IsRatPlaceMap_v2 L E E' Θ (Work.MotC2.infPlace E) (Work.MotC2.isRatPlace_infPlace E)
  rcases Work.MotC2.Classification L E' _ hS with h | ⟨a, b, hns, hEq⟩
  · exact jv2_j_eq_of_placeAtO L E E' Θ h
  · refine jv2_j_eq_of_placeAtO L E E'
      (AlgEquiv.trans Θ (Work.MotC2.transAlgEquiv E' (Point.some a b hns))) ?_
    have hcomp : (AlgEquiv.trans Θ (Work.MotC2.transAlgEquiv E' (Point.some a b hns))).toAlgHom =
        (Work.MotC2.transAlgEquiv E' (Point.some a b hns)).toAlgHom.comp Θ.toAlgHom := rfl
    rw [hcomp, ← Subalgebra.map_map, hEq]
    exact (Work.MotC2.TransPlace L E' a b hns).1

end Work.MotK.TwRuling
