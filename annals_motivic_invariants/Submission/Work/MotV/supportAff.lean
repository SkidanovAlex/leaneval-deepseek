import Mathlib
import Submission.Work.MotV.H1Data
import Submission.Work.MotV.PlaceDefs
import Submission.Work.MotC2.AffPlace
import Submission.Work.MotC2.AffPlaceResidueField
import Submission.Work.MotC2.AffPlaceMaxIdealPrincipal
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The affine support of an element of the coordinate ring

For an elliptic Weierstrass curve `E` over a field `N`, an element `a` of the affine coordinate
ring `N[W]` of `E` is regular at every affine rational point, and if `α = algebraMap a ∈ N(E)`
vanishes at the affine rational point `P = (c, d)` then `c` is a root of the norm
`Algebra.norm (Polynomial N) a`: the norm of `a` from `N[W]` to `N[X]` is the product of the
`Y`-conjugates of `a`, so its value at `X = c` is the product of the values of `a` at the points
of `E` above `X = c`, one of which is `(c, d)`.

## Main results

* `Work.MotV.affEval`: evaluation of the affine coordinate ring at an affine point;
* `Work.MotV.affEval_eq_zero_of_mem_XYIdeal`: vanishing at `P` is membership in the ideal
  `⟨x - c, y - d⟩`;
* `Work.MotV.eval_norm_eq_zero`: the norm of an element of `⟨x - c, y - d⟩` vanishes at `X = c`;
* `Work.MotV.supportAff`: the affine support of `algebraMap a`.

## Tags

elliptic curve, coordinate ring, norm, affine place
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotV

noncomputable section

variable {N : Type*} [Field N]

/-! ## Evaluation at an affine point -/

/-- Evaluation of the affine coordinate ring `N[W]` at the affine point `(c, d)`: the `N`-algebra
homomorphism sending the coordinates `x` and `y` to `c` and `d`. -/
noncomputable def affEval (E : WeierstrassCurve N) (c d : N)
    (h : WeierstrassCurve.Affine.Equation E c d) : MotC2.Coord E →ₐ[N] N :=
  MotC2.plugHom E c d (by simpa [Algebra.algebraMap_self, WeierstrassCurve.map_id] using h)

@[simp]
lemma affEval_coordX (E : WeierstrassCurve N) (c d : N)
    (h : WeierstrassCurve.Affine.Equation E c d) :
    affEval E c d h (MotC2.coordX E) = c := by
  simp [affEval]

@[simp]
lemma affEval_coordY (E : WeierstrassCurve N) (c d : N)
    (h : WeierstrassCurve.Affine.Equation E c d) :
    affEval E c d h (MotC2.coordY E) = d := by
  simp [affEval]

/-- The evaluation is the `N[X]`-algebra map `X ↦ c`: its value on the image of a polynomial is
the evaluation of that polynomial at `c`. -/
lemma affEval_algebraMap (E : WeierstrassCurve N) (c d : N)
    (h : WeierstrassCurve.Affine.Equation E c d) (p : Polynomial N) :
    affEval E c d h (algebraMap (Polynomial N) (MotC2.Coord E) p) = Polynomial.eval c p := by
  have hhom : ((affEval E c d h).toRingHom.comp (algebraMap (Polynomial N) (MotC2.Coord E)))
      = Polynomial.evalRingHom c := by
    refine Polynomial.ringHom_ext ?_ ?_
    · intro x
      rw [RingHom.comp_apply, Polynomial.C_eq_algebraMap,
        ← IsScalarTower.algebraMap_apply N (Polynomial N) (MotC2.Coord E) x]
      have hx : (Polynomial.evalRingHom c) (algebraMap N (Polynomial N) x) = x := by
        rw [← Polynomial.C_eq_algebraMap]; simp
      rw [hx]
      show (affEval E c d h) (algebraMap N (MotC2.Coord E) x) = x
      rw [AlgHom.commutes]; simp
    · rw [RingHom.comp_apply, MotC2.algebraMap_X_eq_coordX]
      have hx : (Polynomial.evalRingHom c) Polynomial.X = c := by simp
      rw [hx]
      simp [affEval]
  exact RingHom.congr_fun hhom p

/-- The evaluation of the coordinate-ring element `p • 1 + q • y` is `p(c) + q(c) · d`. -/
lemma affEval_smul_basis (E : WeierstrassCurve N) (c d : N)
    (h : WeierstrassCurve.Affine.Equation E c d) (p q : Polynomial N) :
    affEval E c d h (p • (1 : MotC2.Coord E) + q • MotC2.coordY E)
      = Polynomial.eval c p + Polynomial.eval c q * d := by
  have h1 : p • (1 : MotC2.Coord E) = algebraMap (Polynomial N) (MotC2.Coord E) p := by
    rw [CoordinateRing.smul, mul_one, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C]
  have h2 : q • (MotC2.coordY E) =
      algebraMap (Polynomial N) (MotC2.Coord E) q * MotC2.coordY E := by
    rw [CoordinateRing.smul, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C]
  rw [h1, h2, map_add, map_mul, affEval_algebraMap, affEval_algebraMap, affEval_coordY]

/-! ## The norm and evaluation -/

/-- The value at `X = c` of the norm of `p • 1 + q • y`, expanded in terms of `p(c)`, `q(c)`. -/
lemma norm_eval_smul_basis (E : WeierstrassCurve N) (c : N) (p q : Polynomial N) :
    Polynomial.eval c (Algebra.norm (Polynomial N)
        (p • (1 : MotC2.Coord E) + q • MotC2.coordY E))
      = (Polynomial.eval c p) ^ 2 - (Polynomial.eval c p) * (Polynomial.eval c q) *
          (E.a₁ * c + E.a₃)
        - (Polynomial.eval c q) ^ 2 * (c ^ 3 + E.a₂ * c ^ 2 + E.a₄ * c + E.a₆) := by
  rw [MotC2.coordY_eq_mk, CoordinateRing.norm_smul_basis]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_C, Polynomial.eval_X]

/-- If `p(c) + q(c)·d = 0` for a point `(c,d)` of `E`, then the norm of `p • 1 + q • y` vanishes
at `X = c`. -/
lemma eval_norm_eq_zero (E : WeierstrassCurve N) (c d : N)
    (hweier : d ^ 2 + E.a₁ * c * d + E.a₃ * d = c ^ 3 + E.a₂ * c ^ 2 + E.a₄ * c + E.a₆)
    (p q : Polynomial N) (hP : Polynomial.eval c p + Polynomial.eval c q * d = 0) :
    Polynomial.eval c (Algebra.norm (Polynomial N)
        (p • (1 : MotC2.Coord E) + q • MotC2.coordY E)) = 0 := by
  rw [norm_eval_smul_basis]
  have hP' : Polynomial.eval c p = - (Polynomial.eval c q * d) := by linear_combination hP
  rw [hP']
  linear_combination (norm := first | refl_ring1 | ring1) (Polynomial.eval c q ^ 2) * hweier

/-! ## Vanishing at a point -/

@[simp]
lemma affEval_XClass (E : WeierstrassCurve N) (c d : N)
    (h : WeierstrassCurve.Affine.Equation E c d) :
    affEval E c d h (CoordinateRing.XClass E c) = 0 := by
  rw [MotC2.XClass_eq_coordX_sub, map_sub, AlgHom.commutes, affEval_coordX]
  simp

@[simp]
lemma affEval_YClass (E : WeierstrassCurve N) (c d : N)
    (h : WeierstrassCurve.Affine.Equation E c d) :
    affEval E c d h (CoordinateRing.YClass E (Polynomial.C d)) = 0 := by
  rw [MotC2.YClass_eq_coordY_sub, map_sub, AlgHom.commutes, affEval_coordY]
  simp

/-- An element of the ideal `⟨x - c, y - d⟩` of the affine coordinate ring evaluates to zero at
`(c, d)`. -/
lemma affEval_eq_zero_of_mem_XYIdeal (E : WeierstrassCurve N) (c d : N)
    (h : WeierstrassCurve.Affine.Equation E c d) (a : CoordinateRing E)
    (ha : a ∈ CoordinateRing.XYIdeal E c (Polynomial.C d)) :
    affEval E c d h a = 0 := by
  rw [CoordinateRing.XYIdeal] at ha
  obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.mp ha
  rw [← hrs, map_add, map_mul, map_mul, affEval_XClass, affEval_YClass]
  first | refl_ring1 | ring

/-- The image in the local ring `affPlaceAt E c d` of an element of the coordinate ring lies in the
maximal ideal if and only if the element lies in `⟨x - c, y - d⟩`. -/
lemma mem_XYIdeal_of_algebraMap_mem_maximalIdeal (E : WeierstrassCurve N) (c d : N)
    [MotC2.IsNonsingularPoint E c d] (a : CoordinateRing E)
    (ha : algebraMap (CoordinateRing E) ↥(MotC2.affPlaceAt E c d) a ∈
        IsLocalRing.maximalIdeal ↥(MotC2.affPlaceAt E c d)) :
    a ∈ CoordinateRing.XYIdeal E c (Polynomial.C d) := by
  have h1 := (IsLocalization.AtPrime.to_map_mem_maximal_iff ↥(MotC2.affPlaceAt E c d)
    (MotC2.affPlaceIdeal E c d) a).mp ha
  simpa [MotC2.affPlaceIdeal] using h1

/-- The maximal ideal of the local ring is the set of elements whose value at `(c, d)` vanishes. -/
lemma algebraMap_mem_maximalIdeal_of_val_mem (E : WeierstrassCurve N) (c d : N)
    [MotC2.IsNonsingularPoint E c d] (a : CoordinateRing E)
    (hmem : algebraMap (CoordinateRing E) (MotC2.Func E) a ∈ MotC2.affPlaceAt E c d)
    (hav : (⟨algebraMap (CoordinateRing E) (MotC2.Func E) a, hmem⟩ :
        ↥(MotC2.affPlaceAt E c d)) ∈
        IsLocalRing.maximalIdeal ↥(MotC2.affPlaceAt E c d)) :
    algebraMap (CoordinateRing E) ↥(MotC2.affPlaceAt E c d) a ∈
        IsLocalRing.maximalIdeal ↥(MotC2.affPlaceAt E c d) := by
  have heq : algebraMap (CoordinateRing E) ↥(MotC2.affPlaceAt E c d) a
      = ⟨algebraMap (CoordinateRing E) (MotC2.Func E) a, hmem⟩ :=
    Subtype.ext (by rw [MotC2.affPlaceAt_algebraMap_val])
  rw [heq]
  exact hav

/-! ## Positivity of the order at a place -/

/-- An element of a rational place whose order is positive is not a unit. -/
lemma not_isUnit_of_ord_pos (E : WeierstrassCurve N) [E.IsElliptic] (H : H1Data N E)
    (S : Subalgebra N (MotC2.Func E)) (hS : MotC2.IsRatPlace E S)
    (f : MotC2.Func E) (hf : f ∈ S) (hpos : 0 < ordOfPlace E S hS f) :
    ¬ IsUnit (⟨f, hf⟩ : ↥S) := by
  intro hu
  obtain ⟨g, hg⟩ := isUnit_iff_exists_inv.mp hu
  have hgval : f * (g : MotC2.Func E) = 1 := by
    have := congrArg (fun z : ↥S => (z : MotC2.Func E)) hg
    simpa using this
  have hf0 : f ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hgval; exact one_ne_zero hgval.symm
  have hg0 : (g : MotC2.Func E) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hgval; exact one_ne_zero hgval.symm
  have h1 : ordOfPlace E S hS (1 : MotC2.Func E) = 0 := by
    have := H.ord_mul S hS 1 1 one_ne_zero one_ne_zero
    rw [one_mul] at this
    linarith
  have hmul := H.ord_mul S hS f (g : MotC2.Func E) hf0 hg0
  rw [hgval] at hmul
  have hgmem : (0 : ℤ) ≤ ordOfPlace E S hS (g : MotC2.Func E) :=
    (H.ord_nonneg S hS _).mpr g.2
  linarith

/-! ## The affine support -/

theorem supportAff {N : Type*} [Field N] (E : WeierstrassCurve N) [E.IsElliptic]
    (H : Work.MotV.H1Data N E) (a : WeierstrassCurve.Affine.CoordinateRing E) (ha : a ≠ 0)
    (c d : N) (h : WeierstrassCurve.Affine.Nonsingular E c d) :
    0 ≤ Work.MotV.ordOfPlace E (Work.MotC2.affPlaceAt E c d) (Work.MotC2.AffPlace N E c d h).1
          (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a) ∧
      (0 < Work.MotV.ordOfPlace E (Work.MotC2.affPlaceAt E c d) (Work.MotC2.AffPlace N E c d h).1
            (algebraMap (WeierstrassCurve.Affine.CoordinateRing E) (Work.MotC2.Func E) a) →
        (Algebra.norm (Polynomial N) a).IsRoot c) := by
  haveI : MotC2.IsNonsingularPoint E c d := ⟨h⟩
  have hmem : algebraMap (CoordinateRing E) (MotC2.Func E) a ∈ MotC2.affPlaceAt E c d :=
    MotC2.algebraMap_mem_affPlaceAt E c d a
  refine ⟨(H.ord_nonneg _ (MotC2.AffPlace N E c d h).1 _).mpr hmem, ?_⟩
  intro hpos
  -- the element is not a unit of the local ring
  have hnu : ¬ IsUnit (⟨algebraMap (CoordinateRing E) (MotC2.Func E) a, hmem⟩ :
      ↥(MotC2.affPlaceAt E c d)) :=
    not_isUnit_of_ord_pos E H _ (MotC2.AffPlace N E c d h).1 _ hmem hpos
  -- hence it lies in the maximal ideal
  have hM : (⟨algebraMap (CoordinateRing E) (MotC2.Func E) a, hmem⟩ :
      ↥(MotC2.affPlaceAt E c d)) ∈
      IsLocalRing.maximalIdeal ↥(MotC2.affPlaceAt E c d) := by
    by_contra hcon
    exact hnu (IsLocalRing.notMem_maximalIdeal.mp hcon)
  -- hence its image in the coordinate ring lies in `⟨x - c, y - d⟩`
  have haI : a ∈ CoordinateRing.XYIdeal E c (Polynomial.C d) :=
    mem_XYIdeal_of_algebraMap_mem_maximalIdeal E c d a
      (algebraMap_mem_maximalIdeal_of_val_mem E c d a hmem hM)
  -- so its evaluation at `(c, d)` vanishes
  have hev : affEval E c d h.1 a = 0 := affEval_eq_zero_of_mem_XYIdeal E c d h.1 a haI
  -- write `a = p • 1 + q • y`
  obtain ⟨p, q, hpq₀⟩ := CoordinateRing.exists_smul_basis_eq (W' := E) a
  have hpq : p • (1 : CoordinateRing E) + q • MotC2.coordY E = a := by
    simpa [MotC2.coordY_eq_mk] using hpq₀
  have hP : Polynomial.eval c p + Polynomial.eval c q * d = 0 := by
    have h := congrArg (affEval E c d h.1) hpq
    rw [affEval_smul_basis, hev] at h
    exact h
  have hweier : d ^ 2 + E.a₁ * c * d + E.a₃ * d = c ^ 3 + E.a₂ * c ^ 2 + E.a₄ * c + E.a₆ :=
    (equation_iff (W := E) c d).mp h.1
  have hzero : Polynomial.eval c (Algebra.norm (Polynomial N) a) = 0 := by
    rw [← hpq]
    exact eval_norm_eq_zero E c d hweier p q hP
  exact hzero

end

end Work.MotV
