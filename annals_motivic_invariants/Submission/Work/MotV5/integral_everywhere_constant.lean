import Mathlib
import Submission.Work.MotC2.AffPlace
import Submission.Work.MotC2.PoleOrder
import Submission.Work.MotC2.InfPlace
import Submission.Work.MotC2.InfPlaceCore
import Submission.Work.MotC2Cls.Setup
import Submission.Work.MotC2Cls.ker_eq_XYIdeal
import Submission.Work.MotV5.denominator_ideal_lift
import Submission.Work.MotV5.maximalIdeal_eval
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Functions of `N(E)` regular at every rational place are constant

Let `E` be an elliptic curve over an algebraically closed field `N`.  If `f ∈ N(E)` lies in every
rational place of `N(E)/N` (i.e. `f` has no pole on `E`), then `f` is a constant.  This is the
statement that the projective curve `E` is complete: the only everywhere regular functions are the
constants.

The proof has two halves.

* **The affine half.**  `f ∈ affPlaceAt E a b` for every nonsingular affine point `(a,b)`
  (`MotC2.AffPlace`).  Each maximal ideal of the affine coordinate ring `C = N[x,y]` is the maximal
  ideal `⟨x - a, y - b⟩` of a nonsingular point (the Nullstellensatz, see
  `Work.MotV5.maximalIdeal_eval` and `maximalIdeal_eq_XYIdeal_of_isMaximal`), so the ideal of
  denominators `I = {s ∈ C | f · s ∈ C}` of `f` is contained in no maximal ideal, hence is `⊤`:
  `f ∈ C = affRing E` (`Work.MotV5.denominator_ideal_lift`).
* **The infinity half.**  If `f ∈ affRing E` and `f ∈ infPlace E`, then `f · (infW E)² ∈ infPlace E`
  (`infW = y/x²` generates the maximal ideal of the local ring at infinity), so `PoleOrder` writes
  `f = a + b · x` with `a b : N`; if `b ≠ 0` this exhibits `x` as an element of `infPlace E`, which
  is impossible (`x ∉ infPlace E`, since `1/x` is a non-unit of `infPlace E`).  Hence `f = a`.

## Tags

elliptic curve, function field, rational place, completeness
-/

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotV5

noncomputable section

/-! ## `x` is not regular at the point at infinity -/

/-- The affine coordinate `x` is not regular at the point at infinity: `u = 1/x` lies in the maximal
ideal of `infPlace E` (it is a multiple of the uniformiser `w = y/x²`, `InfPlaceCore.algebraMap_U_eq_W_mul`
and `InfPlaceCore.maxIdeal_eq_span`), hence is a non-unit, while `x · u = 1` would make it a unit. -/
theorem notMem_infPlace_genX {N : Type*} [Field N] (E : WeierstrassCurve N) :
    Work.MotC2.genX E ∉ Work.MotC2.infPlace E := by
  intro hx
  have hmem : algebraMap (Work.MotC2.infCoordRing E) ↥(Work.MotC2.infPlace E)
      (Work.MotC2.InfPlaceCore.U E) ∈
      IsLocalRing.maximalIdeal ↥(Work.MotC2.infPlace E) := by
    rw [Work.MotC2.InfPlaceCore.maxIdeal_eq_span]
    exact Ideal.mem_span_singleton.mpr ⟨_, Work.MotC2.InfPlaceCore.algebraMap_U_eq_W_mul E⟩
  refine (IsLocalRing.mem_maximalIdeal _).mp hmem ?_
  refine isUnit_iff_exists_inv.mpr ⟨⟨Work.MotC2.genX E, hx⟩, ?_⟩
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, Work.MotC2.infPlace_algebraMap_val, Work.MotC2.InfPlaceCore.coe_U,
    Subalgebra.coe_one]
  exact Work.MotC2.infU_mul_genX E

/-! ## The maximal ideals of the affine coordinate ring -/

/-- Every maximal ideal of the affine coordinate ring `C = N[x,y]` of an elliptic curve over an
algebraically closed field is `⟨x - a, y - b⟩` for a nonsingular affine point `(a,b)`.

Proof.  `Work.MotV5.maximalIdeal_eval` produces an `N`-algebra homomorphism `φ : C →ₐ[N] N` with
`ker φ = m`; its kernel is computed by `Work.MotC2Cls.ker_eq_XYIdeal`, and the point
`(φ x, φ y)` lies on the curve because `φ` respects the Weierstrass relation (`coordY_sq_relation`),
so it is nonsingular by `equation_iff_nonsingular`. -/
theorem maximalIdeal_eq_XYIdeal_of_isMaximal {N : Type*} [Field N] [IsAlgClosed N]
    (E : WeierstrassCurve N) [E.IsElliptic] (m : Ideal (Work.MotC2.Coord E)) (hm : m.IsMaximal) :
    ∃ a b : N, Nonsingular E a b ∧
      m = CoordinateRing.XYIdeal E a (Polynomial.C b) := by
  obtain ⟨φ, hφ⟩ := maximalIdeal_eval E m hm
  have hc : ∀ c : N, φ (algebraMap N (Work.MotC2.Coord E) c) = c := by
    intro c
    rw [AlgHom.commutes]
    exact Algebra.algebraMap_self_apply c
  have hEq : Equation E (φ (Work.MotC2.coordX E)) (φ (Work.MotC2.coordY E)) := by
    rw [equation_iff]
    have h := congrArg (φ : Work.MotC2.Coord E → N) (Work.MotC2.coordY_sq_relation E)
    simp only [map_add, map_mul, map_pow, hc] at h
    linear_combination (norm := first | refl_ring1 | ring1) h
  refine ⟨φ (Work.MotC2.coordX E), φ (Work.MotC2.coordY E),
    equation_iff_nonsingular.mp hEq, ?_⟩
  rw [← hφ]
  exact Work.MotC2Cls.ker_eq_XYIdeal E φ

/-! ## The affine half -/

/-- **A function of `N(E)` which is regular at every affine rational point lies in the affine
coordinate ring `N[x,y]`.**  This is the algebraic form of "the local rings of the affine points
intersect in `N[x,y]`".

The ideal `I = {s : C | f · s ∈ C}` of denominators of `f` is not contained in any maximal ideal of
`C = N[x,y]`: a maximal ideal is `⟨x - a, y - b⟩` for a nonsingular point `(a,b)`
(`maximalIdeal_eq_XYIdeal_of_isMaximal`), and regularity of `f` there
(`MotC2.AffPlace`) supplies a denominator outside it.  Hence `I = ⊤`, i.e. `f ∈ C`. -/
theorem mem_affRing_of_mem_affPlaceAt {N : Type*} [Field N] [IsAlgClosed N]
    (E : WeierstrassCurve N) [E.IsElliptic] (f : Work.MotC2.Func E)
    (hf : ∀ a b : N, Nonsingular E a b → f ∈ Work.MotC2.affPlaceAt E a b) :
    f ∈ Work.MotC2.affRing E := by
  have hden : ∀ m : Ideal (Work.MotC2.Coord E), m.IsMaximal →
      ∃ s r : Work.MotC2.Coord E, s ∉ m ∧
        f * algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) s =
          algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) r := by
    intro m hm
    obtain ⟨a, b, hns, hmab⟩ := maximalIdeal_eq_XYIdeal_of_isMaximal E m hm
    obtain ⟨r, g, hg, heq⟩ := ((Work.MotC2.AffPlace N E a b hns).2 f).mp (hf a b hns)
    exact ⟨g, r, by rwa [← hmab] at hg, heq⟩
  obtain ⟨r, hr⟩ := denominator_ideal_lift (R := Work.MotC2.Coord E) (K := Work.MotC2.Func E) f hden
  rw [Work.MotC2.affRing]
  exact Algebra.subset_adjoin ⟨r, hr.symm⟩

/-! ## The infinity half -/

/-- **A function of the affine coordinate ring which is regular at the point at infinity is a
constant.**  `f ∈ N[x,y]` is `algebraMap r` for some `r : C`; multiplying the hypothesis by `w²`
(`w = y/x²`) and applying `MotC2.PoleOrder` gives `f = a + b·x`, and `b ≠ 0` would force
`x ∈ infPlace E`, contradicting `notMem_infPlace_genX`. -/
theorem eq_algebraMap_of_mem_affRing_infPlace {N : Type*} [Field N] (E : WeierstrassCurve N)
    [E.IsElliptic] (f : Work.MotC2.Func E) (hC : f ∈ Work.MotC2.affRing E)
    (hinf : f ∈ Work.MotC2.infPlace E) :
    ∃ c : N, algebraMap N (Work.MotC2.Func E) c = f := by
  have hle : Work.MotC2.affRing E ≤
      (IsScalarTower.toAlgHom N (Work.MotC2.Coord E) (Work.MotC2.Func E)).range := by
    rw [Work.MotC2.affRing]
    exact Algebra.adjoin_le_iff.mpr (fun x hx => hx)
  obtain ⟨r, hr⟩ :=
    (AlgHom.mem_range (IsScalarTower.toAlgHom N (Work.MotC2.Coord E)
      (Work.MotC2.Func E))).mp (hle hC)
  have hr' : algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) r = f := hr
  have hinf' : algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) r ∈ Work.MotC2.infPlace E := by
    rw [hr']
    exact hinf
  have h2 : algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) r * (Work.MotC2.infW E) ^ 2 ∈
      Work.MotC2.infPlace E :=
    mul_mem hinf' (pow_mem (Work.MotC2.InfPlaceCore.infW_mem_infPlace E) 2)
  obtain ⟨a, b, hab⟩ := ((Work.MotC2.PoleOrder N E).1 r).mp h2
  rcases eq_or_ne b 0 with hb | hb
  · subst hb
    refine ⟨a, ?_⟩
    rw [← hr', hab]
    simp
  · exfalso
    have hb' : algebraMap N (Work.MotC2.Func E) b ≠ 0 := by
      intro h0
      have h1 : algebraMap N (Work.MotC2.Func E) b * algebraMap N (Work.MotC2.Func E) b⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel₀ hb, map_one]
      rw [h0, zero_mul] at h1
      exact one_ne_zero h1.symm
    have hinv : (algebraMap N (Work.MotC2.Func E) b)⁻¹ ∈ Work.MotC2.infPlace E := by
      rw [← map_inv₀ (algebraMap N (Work.MotC2.Func E)) b]
      exact Subalgebra.algebraMap_mem _ b⁻¹
    have hsub : algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) r -
        algebraMap N (Work.MotC2.Func E) a ∈ Work.MotC2.infPlace E :=
      sub_mem hinf' (Subalgebra.algebraMap_mem _ a)
    have hkey : (algebraMap (Work.MotC2.Coord E) (Work.MotC2.Func E) r -
        algebraMap N (Work.MotC2.Func E) a) * (algebraMap N (Work.MotC2.Func E) b)⁻¹ =
        Work.MotC2.genX E := by
      rw [hab, add_sub_cancel_left, mul_comm (algebraMap N (Work.MotC2.Func E) b)
        (Work.MotC2.genX E), mul_inv_cancel_right₀ hb']
    exact notMem_infPlace_genX E (by rw [← hkey]; exact mul_mem hsub hinv)

/-! ## The theorem -/

theorem integral_everywhere_constant {N : Type*} [Field N] [IsAlgClosed N] (E : WeierstrassCurve N)
    [E.IsElliptic] (f : Work.MotC2.Func E)
    (hf : ∀ (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S), f ∈ S) :
    ∃ c : N, algebraMap N (Work.MotC2.Func E) c = f := by
  have hC : f ∈ Work.MotC2.affRing E :=
    mem_affRing_of_mem_affPlaceAt E f
      (fun a b hns => hf _ (Work.MotC2.AffPlace N E a b hns).1)
  have hinf : f ∈ Work.MotC2.infPlace E := hf _ (Work.MotC2.InfPlace N E).1
  exact eq_algebraMap_of_mem_affRing_infPlace E f hC hinf

end

end Work.MotV5
