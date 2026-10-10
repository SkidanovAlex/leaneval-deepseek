import Mathlib
import Submission.Work.MotC2.AffPlace
import Submission.Work.MotC2.DVRMaximal
import Submission.Work.MotC2.InfPlaceCore
import Submission.Work.MotC2.Integral
import Submission.Work.MotC2.affRing_eq_adjoin
import Submission.Work.MotC2Cls.infPlace_le_of_notMem_genX
import Submission.Work.MotC2Cls.ker_eq_XYIdeal
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve.Affine

namespace Work.MotV5

open Work.MotC2

variable {N : Type*} [Field N]

/-! ## Integrality of the affine coordinate ring in a rational place -/

/-- An element of `L(E)` that is integral over a rational place belongs to it: a rational place is
a discrete valuation ring, hence integrally closed. -/
private lemma mem_of_isIntegral {E : WeierstrassCurve N} {S : Subalgebra N (Func E)}
    (hS : IsRatPlace E S) {f : Func E} (hf : IsIntegral S f) : f ∈ S := by
  obtain ⟨⟨hDVR, -⟩, hfrac⟩ := hS
  haveI : IsFractionRing S (Func E) := isFractionRing_of_forall_mul_eq hfrac
  letI : IsDiscreteValuationRing S := hDVR
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := Func E)).mp hf
  rw [← hy]
  exact y.2

/-- `genY E` is integral over any `L`-subalgebra of `L(E)` containing `genX E`. -/
private lemma isIntegral_genY_of_mem {E : WeierstrassCurve N} {S : Subalgebra N (Func E)}
    (hx : genX E ∈ S) : IsIntegral S (genY E) :=
  isIntegral_of_quadratic S
    (algebraMap N (Func E) E.a₁ * genX E + algebraMap N (Func E) E.a₃)
    (-((genX E) ^ 3 + algebraMap N (Func E) E.a₂ * (genX E) ^ 2 +
      algebraMap N (Func E) E.a₄ * genX E + algebraMap N (Func E) E.a₆))
    (add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) hx) (Subalgebra.algebraMap_mem _ _))
    (neg_mem (add_mem (add_mem (add_mem
      (pow_mem hx 3)
      (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem hx 2)))
      (mul_mem (Subalgebra.algebraMap_mem _ _) hx))
      (Subalgebra.algebraMap_mem _ _)))
    (by linear_combination genY_sq_relation E)

/-- The affine coordinate ring `L[x,y] ⊆ L(E)` is generated over `L` by `x` and `y`. -/
private lemma affRing_eq_adjoin_genX_genY (E : WeierstrassCurve N) :
    affRing E = Algebra.adjoin N ({genX E, genY E} : Set (Func E)) := by
  refine le_antisymm ?_ ?_
  · rw [affRing]
    refine Algebra.adjoin_le_iff.mpr ?_
    rintro y ⟨r, rfl⟩
    have hle : Algebra.adjoin N ({coordX E, coordY E} : Set (Coord E)) ≤
        Subalgebra.comap (IsScalarTower.toAlgHom N (Coord E) (Func E))
          (Algebra.adjoin N ({genX E, genY E} : Set (Func E))) := by
      refine Algebra.adjoin_le_iff.mpr ?_
      rintro x (rfl | rfl)
      · exact Algebra.subset_adjoin (Or.inl rfl)
      · exact Algebra.subset_adjoin (Or.inr rfl)
    exact hle (by rw [adjoin_coordX_coordY]; trivial)
  · refine Algebra.adjoin_le_iff.mpr ?_
    rintro y (rfl | rfl)
    · exact Algebra.subset_adjoin ⟨coordX E, rfl⟩
    · exact Algebra.subset_adjoin ⟨coordY E, rfl⟩

/-- If `genX E ∈ S` then the whole affine coordinate ring `L[x,y]` is contained in `S`. -/
private lemma affRing_le_of_genX_mem {E : WeierstrassCurve N} {S : Subalgebra N (Func E)}
    (hS : IsRatPlace E S) (hx : genX E ∈ S) : affRing E ≤ S := by
  have hy : genY E ∈ S := mem_of_isIntegral hS (isIntegral_genY_of_mem hx)
  rw [affRing_eq_adjoin_genX_genY E]
  refine Algebra.adjoin_le_iff.mpr ?_
  intro x hx'
  rcases hx' with rfl | rfl
  · exact hx
  · exact hy

/-- An element of a rational place outside its maximal ideal is a unit, so its inverse (taken in
`L(E)`) still lies in `S`. -/
private lemma inv_mem_of_notMem_maximalIdeal {E : WeierstrassCurve N}
    {S : Subalgebra N (Func E)} [IsLocalRing S] (f : Func E) (hf : f ∈ S)
    (h : (⟨f, hf⟩ : S) ∉ IsLocalRing.maximalIdeal S) : f⁻¹ ∈ S := by
  obtain ⟨u, hu⟩ := IsLocalRing.notMem_maximalIdeal.mp h
  have hcoe : (((u : Sˣ) : S) : Func E) = f := by rw [hu]
  have hval : (((u⁻¹ : Sˣ) : S) : Func E) = f⁻¹ := by
    rw [subalgebra_coe_unit_inv S u, hcoe]
  rw [← hval]
  exact ((u⁻¹ : Sˣ) : S).2

/-! ## The local ring at infinity is a rational place -/

/-- The local ring `infPlace E` of the point at infinity is a rational place of `L(E)/L`.  This is
assembled from the discrete valuation ring instance, the identification of the residue field with
`L`, and the fact that `L(E)` is the fraction field of `infPlace E`, all of which are proved in
`Work.MotC2.InfPlaceCore`. -/
private lemma infPlace_isRatPlace (E : WeierstrassCurve N) :
    IsRatPlace E (infPlace E) :=
  ⟨⟨InfPlaceCore.instIsDiscreteValuationRing E, InfPlaceCore.residue_field E⟩,
    InfPlaceCore.frac_field E⟩

theorem classification_ratPlace {N : Type*} [Field N] (E : WeierstrassCurve N) [E.IsElliptic]
    (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S) :
    S = Work.MotC2.infPlace E ∨
      ∃ a b : N, WeierstrassCurve.Affine.Nonsingular E a b ∧ S = Work.MotC2.affPlaceAt E a b := by
  obtain ⟨⟨hDVR, hres⟩, hfrac⟩ := hS
  letI : IsDiscreteValuationRing S := hDVR
  by_cases hx : genX E ∈ S
  · -- The affine case: `x ∈ S`, so `S` is the local ring of an affine rational point.
    right
    have hle_aff : affRing E ≤ S := affRing_le_of_genX_mem ⟨⟨hDVR, hres⟩, hfrac⟩ hx
    let e : N ≃ₐ[N] (S ⧸ IsLocalRing.maximalIdeal S) :=
      AlgEquiv.ofBijective
        ((Ideal.Quotient.mkₐ N (IsLocalRing.maximalIdeal S)).comp (Algebra.ofId N S)) hres
    let Φ : Coord E →ₐ[N] S :=
      (IsScalarTower.toAlgHom N (Coord E) (Func E)).codRestrict S
        (fun r => hle_aff (Algebra.subset_adjoin ⟨r, rfl⟩))
    let φ : Coord E →ₐ[N] N :=
      e.symm.toAlgHom.comp ((Ideal.Quotient.mkₐ N (IsLocalRing.maximalIdeal S)).comp Φ)
    have hEq : Equation E (φ (coordX E)) (φ (coordY E)) := by
      rw [equation_iff]
      have h := congrArg (φ : Coord E → N) (coordY_sq_relation E)
      have hc : ∀ c : N, φ (algebraMap N (Coord E) c) = c := by
        intro c
        rw [AlgHom.commutes]
        exact Algebra.algebraMap_self_apply c
      simp only [map_add, map_mul, map_pow, hc] at h
      linear_combination (norm := first | refl_ring1 | ring1) h
    have hns : Nonsingular E (φ (coordX E)) (φ (coordY E)) :=
      WeierstrassCurve.Affine.equation_iff_nonsingular.mp hEq
    have hker : RingHom.ker (φ : Coord E →+* N) =
        WeierstrassCurve.Affine.CoordinateRing.XYIdeal E (φ (coordX E))
          (Polynomial.C (φ (coordY E))) :=
      Work.MotC2Cls.ker_eq_XYIdeal E φ
    have hle_place : affPlaceAt E (φ (coordX E)) (φ (coordY E)) ≤ S := by
      rw [affPlaceAt]
      refine Algebra.adjoin_le_iff.mpr ?_
      rintro y (hy | hy)
      · obtain ⟨r, rfl⟩ := hy
        exact hle_aff (Algebra.subset_adjoin ⟨r, rfl⟩)
      · obtain ⟨r, hr, rfl⟩ := hy
        have hne0 : (Φ r) ∉ IsLocalRing.maximalIdeal S := by
          intro hmem
          apply hr
          rw [← hker, RingHom.mem_ker]
          show e.symm (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S) (Φ r)) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr hmem, map_zero]
        have hinv : ((Φ r : S) : Func E)⁻¹ ∈ S :=
          inv_mem_of_notMem_maximalIdeal (S := S) (f := (Φ r : Func E)) (Φ r).2 hne0
        show (algebraMap (Coord E) (Func E) r)⁻¹ ∈ S
        exact hinv
    refine ⟨φ (coordX E), φ (coordY E), hns, ?_⟩
    exact (DVRMaximal N E (affPlaceAt E (φ (coordX E)) (φ (coordY E))) S
      (AffPlace N E (φ (coordX E)) (φ (coordY E)) hns).1 ⟨⟨hDVR, hres⟩, hfrac⟩ hle_place).symm
  · -- The case at infinity: `x ∉ S`, so `S` is the local ring of the point at infinity.
    left
    have hle_inf : infPlace E ≤ S :=
      Work.MotC2Cls.infPlace_le_of_notMem_genX E S ⟨⟨hDVR, hres⟩, hfrac⟩ hx
    exact (DVRMaximal N E (infPlace E) S (infPlace_isRatPlace E) ⟨⟨hDVR, hres⟩, hfrac⟩
      hle_inf).symm

end Work.MotV5
