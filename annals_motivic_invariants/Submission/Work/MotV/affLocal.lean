import Mathlib
import Submission.Work.MotV.PlaceDefs
import Submission.Work.MotV.affLocalCaseNe
import Submission.Work.MotV.affLocalCaseEq
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.MotV

noncomputable section

/-- Reading off `ordOfPlace` from the value of `addVal` on an element of the place. -/
private lemma ordOfPlace_eq_of {N : Type*} [Field N] {E : WeierstrassCurve N}
    {S : Subalgebra N (MotC2.Func E)} (hS : MotC2.IsRatPlace E S)
    {f : MotC2.Func E} (hf : f ∈ S) {n : ℕ}
    (h : @IsDiscreteValuationRing.addVal ↥S _ _ hS.1.choose (⟨f, hf⟩ : ↥S) = (n : ℕ∞)) :
    ordOfPlace E S hS f = n := by
  rw [ordOfPlace, dif_pos hf, h]
  exact congrArg (fun m : ℕ => (m : ℤ)) (WithTop.untopD_coe (0 : ℕ) n)

/-- **Local orders at an affine point of an elliptic curve.**  Let `E` be an elliptic Weierstrass
curve over a field `N` and `(a, b)` a nonsingular affine point.  At the place `S = affPlaceAt E a b`
the local parameter is `x - a` if the `y`-derivative `2y + a₁x + a₃` does not vanish at `(a, b)`
(the tangent line is not vertical), and `y - b` otherwise (vertical tangent):
`x - a` has order `1` in the first case and `2` in the second, `2y + a₁x + a₃` has order `0` in
the first case, `y - b` has order `1` and the `x`-derivative `3x² + 2a₂x + a₄ - a₁y` has order `0`
in the second. -/
theorem affLocal {N : Type*} [Field N] (E : WeierstrassCurve N) [E.IsElliptic]
    (a b : N) (h : WeierstrassCurve.Affine.Nonsingular E a b) :
    ((2 * b + E.a₁ * a + E.a₃ ≠ 0) →
      Work.MotV.ordOfPlace E (Work.MotC2.affPlaceAt E a b)
          (Work.MotC2.AffPlace N E a b h).1
          (Work.MotC2.genX E - algebraMap N (Work.MotC2.Func E) a) = 1 ∧
      Work.MotV.ordOfPlace E (Work.MotC2.affPlaceAt E a b)
          (Work.MotC2.AffPlace N E a b h).1
          (2 * Work.MotC2.genY E + algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genX E +
            algebraMap N (Work.MotC2.Func E) E.a₃) = 0) ∧
    ((2 * b + E.a₁ * a + E.a₃ = 0) →
      Work.MotV.ordOfPlace E (Work.MotC2.affPlaceAt E a b)
          (Work.MotC2.AffPlace N E a b h).1
          (Work.MotC2.genX E - algebraMap N (Work.MotC2.Func E) a) = 2 ∧
      Work.MotV.ordOfPlace E (Work.MotC2.affPlaceAt E a b)
          (Work.MotC2.AffPlace N E a b h).1
          (Work.MotC2.genY E - algebraMap N (Work.MotC2.Func E) b) = 1 ∧
      Work.MotV.ordOfPlace E (Work.MotC2.affPlaceAt E a b)
          (Work.MotC2.AffPlace N E a b h).1
          (3 * (Work.MotC2.genX E) ^ 2 + 2 * algebraMap N (Work.MotC2.Func E) E.a₂ *
              Work.MotC2.genX E + algebraMap N (Work.MotC2.Func E) E.a₄ -
            algebraMap N (Work.MotC2.Func E) E.a₁ * Work.MotC2.genY E) = 0) := by
  set hS : MotC2.IsRatPlace E (MotC2.affPlaceAt E a b) := (MotC2.AffPlace N E a b h).1
  letI : IsDiscreteValuationRing ↥(MotC2.affPlaceAt E a b) := hS.1.choose
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · -- ## The tangent line at `(a, b)` is not vertical: `x - a` is a local parameter
    obtain ⟨hX, hunit⟩ := affLocalCaseNe E a b h hw
    refine ⟨?_, ?_⟩
    · -- `ord (x - a) = 1`
      have key1 : MotC2.genX E - algebraMap N (MotC2.Func E) a =
          algebraMap (MotC2.Coord E) (MotC2.Func E) (CoordinateRing.XClass E a) := by
        simp only [MotC2.genX, Work.MotC2.XClass_eq_coordX_sub, map_sub,
          IsScalarTower.algebraMap_apply N (MotC2.Coord E) (MotC2.Func E)]
      have hmem : MotC2.genX E - algebraMap N (MotC2.Func E) a ∈ MotC2.affPlaceAt E a b := by
        have h0 := MotC2.algebraMap_mem_affPlaceAt E a b (CoordinateRing.XClass E a)
        rwa [← key1] at h0
      have hsub : (⟨MotC2.genX E - algebraMap N (MotC2.Func E) a, hmem⟩ :
            ↥(MotC2.affPlaceAt E a b)) =
          algebraMap (MotC2.Coord E) ↥(MotC2.affPlaceAt E a b) (CoordinateRing.XClass E a) := by
        apply Subtype.ext
        simpa [MotC2.affPlaceAt_algebraMap_val] using key1
      have hadd : IsDiscreteValuationRing.addVal ↥(MotC2.affPlaceAt E a b)
          (algebraMap (MotC2.Coord E) ↥(MotC2.affPlaceAt E a b) (CoordinateRing.XClass E a))
            = (1 : ℕ∞) :=
        IsDiscreteValuationRing.addVal_uniformizer hX
      exact ordOfPlace_eq_of hS hmem (by rw [hsub]; exact hadd)
    · -- `ord (2y + a₁x + a₃) = 0`
      set r2 : MotC2.Coord E := 2 * MotC2.coordY E +
        algebraMap N (MotC2.Coord E) E.a₁ * MotC2.coordX E + algebraMap N (MotC2.Coord E) E.a₃
      have key2 : 2 * MotC2.genY E + algebraMap N (MotC2.Func E) E.a₁ * MotC2.genX E +
            algebraMap N (MotC2.Func E) E.a₃
          = algebraMap (MotC2.Coord E) (MotC2.Func E) r2 := by
        simp only [MotC2.genX, MotC2.genY, r2, map_add, map_mul, map_ofNat,
          IsScalarTower.algebraMap_apply N (MotC2.Coord E) (MotC2.Func E)]
      have hmem : 2 * MotC2.genY E + algebraMap N (MotC2.Func E) E.a₁ * MotC2.genX E +
            algebraMap N (MotC2.Func E) E.a₃ ∈ MotC2.affPlaceAt E a b := by
        have h0 := MotC2.algebraMap_mem_affPlaceAt E a b r2
        rwa [← key2] at h0
      have hsub2 : (⟨2 * MotC2.genY E + algebraMap N (MotC2.Func E) E.a₁ * MotC2.genX E +
            algebraMap N (MotC2.Func E) E.a₃, hmem⟩ : ↥(MotC2.affPlaceAt E a b)) =
          algebraMap (MotC2.Coord E) ↥(MotC2.affPlaceAt E a b) r2 := by
        apply Subtype.ext
        simpa [MotC2.affPlaceAt_algebraMap_val] using key2
      have hr2 : r2 = 2 * CoordinateRing.YClass E (C b) +
          algebraMap N (MotC2.Coord E) E.a₁ * CoordinateRing.XClass E a +
          algebraMap N (MotC2.Coord E) (2 * b + E.a₁ * a + E.a₃) := by
        simp only [r2, Work.MotC2.XClass_eq_coordX_sub, Work.MotC2.YClass_eq_coordY_sub,
          map_add, map_mul, map_ofNat]
        first | refl_ring1 | ring
      have hmap : algebraMap (MotC2.Coord E) ↥(MotC2.affPlaceAt E a b) r2 =
          2 * algebraMap (MotC2.Coord E) ↥(MotC2.affPlaceAt E a b)
                (CoordinateRing.YClass E (C b)) +
            algebraMap N ↥(MotC2.affPlaceAt E a b) E.a₁ *
              algebraMap (MotC2.Coord E) ↥(MotC2.affPlaceAt E a b) (CoordinateRing.XClass E a) +
            algebraMap N ↥(MotC2.affPlaceAt E a b) (2 * b + E.a₁ * a + E.a₃) := by
        rw [hr2]
        simp only [map_add, map_mul, map_ofNat, MotC2.affPlaceAt_algebraMap_algebraMap]
      have hrel : (⟨2 * MotC2.genY E + algebraMap N (MotC2.Func E) E.a₁ * MotC2.genX E +
            algebraMap N (MotC2.Func E) E.a₃, hmem⟩ : ↥(MotC2.affPlaceAt E a b)) =
          2 * algebraMap (MotC2.Coord E) ↥(MotC2.affPlaceAt E a b)
                (CoordinateRing.YClass E (C b)) +
            algebraMap N ↥(MotC2.affPlaceAt E a b) E.a₁ *
              algebraMap (MotC2.Coord E) ↥(MotC2.affPlaceAt E a b) (CoordinateRing.XClass E a) +
            algebraMap N ↥(MotC2.affPlaceAt E a b) (2 * b + E.a₁ * a + E.a₃) := by
        rw [hsub2, hmap]
      have hunit' : IsUnit (⟨2 * MotC2.genY E + algebraMap N (MotC2.Func E) E.a₁ * MotC2.genX E +
            algebraMap N (MotC2.Func E) E.a₃, hmem⟩ : ↥(MotC2.affPlaceAt E a b)) := by
        rw [hrel]; exact hunit
      have hadd : @IsDiscreteValuationRing.addVal ↥(MotC2.affPlaceAt E a b) _ _ hS.1.choose
          (⟨2 * MotC2.genY E + algebraMap N (MotC2.Func E) E.a₁ * MotC2.genX E +
            algebraMap N (MotC2.Func E) E.a₃, hmem⟩ : ↥(MotC2.affPlaceAt E a b))
            = ((0 : ℕ) : ℕ∞) :=
        (@IsDiscreteValuationRing.addVal_eq_zero_iff ↥(MotC2.affPlaceAt E a b) _ _
          hS.1.choose _).mpr hunit'
      exact ordOfPlace_eq_of hS hmem hadd
  · -- ## The tangent line at `(a, b)` is vertical: `y - b` is a local parameter
    obtain ⟨hY, hfac, hunit3⟩ := affLocalCaseEq E a b h hw
    refine ⟨?_, ?_, ?_⟩
    · -- `ord (x - a) = 2`
      have key1 : MotC2.genX E - algebraMap N (MotC2.Func E) a =
          algebraMap (MotC2.Coord E) (MotC2.Func E) (CoordinateRing.XClass E a) := by
        simp only [MotC2.genX, Work.MotC2.XClass_eq_coordX_sub, map_sub,
          IsScalarTower.algebraMap_apply N (MotC2.Coord E) (MotC2.Func E)]
      have hmem : MotC2.genX E - algebraMap N (MotC2.Func E) a ∈ MotC2.affPlaceAt E a b := by
        have h0 := MotC2.algebraMap_mem_affPlaceAt E a b (CoordinateRing.XClass E a)
        rwa [← key1] at h0
      have hsub : (⟨MotC2.genX E - algebraMap N (MotC2.Func E) a, hmem⟩ :
            ↥(MotC2.affPlaceAt E a b)) =
          algebraMap (MotC2.Coord E) ↥(MotC2.affPlaceAt E a b) (CoordinateRing.XClass E a) := by
        apply Subtype.ext
        simpa [MotC2.affPlaceAt_algebraMap_val] using key1
      obtain ⟨u, hu⟩ := hfac
      have hadd : IsDiscreteValuationRing.addVal ↥(MotC2.affPlaceAt E a b)
          (algebraMap (MotC2.Coord E) ↥(MotC2.affPlaceAt E a b) (CoordinateRing.XClass E a))
            = (2 : ℕ∞) :=
        IsDiscreteValuationRing.addVal_def _ u hY 2 hu
      exact ordOfPlace_eq_of hS hmem (by rw [hsub]; exact hadd)
    · -- `ord (y - b) = 1`
      have key : MotC2.genY E - algebraMap N (MotC2.Func E) b =
          algebraMap (MotC2.Coord E) (MotC2.Func E) (CoordinateRing.YClass E (C b)) := by
        simp only [MotC2.genY, Work.MotC2.YClass_eq_coordY_sub, map_sub,
          IsScalarTower.algebraMap_apply N (MotC2.Coord E) (MotC2.Func E)]
      have hmem : MotC2.genY E - algebraMap N (MotC2.Func E) b ∈ MotC2.affPlaceAt E a b := by
        have h0 := MotC2.algebraMap_mem_affPlaceAt E a b (CoordinateRing.YClass E (C b))
        rwa [← key] at h0
      have hsub : (⟨MotC2.genY E - algebraMap N (MotC2.Func E) b, hmem⟩ :
            ↥(MotC2.affPlaceAt E a b)) =
          algebraMap (MotC2.Coord E) ↥(MotC2.affPlaceAt E a b) (CoordinateRing.YClass E (C b)) := by
        apply Subtype.ext
        simpa [MotC2.affPlaceAt_algebraMap_val] using key
      have hadd : IsDiscreteValuationRing.addVal ↥(MotC2.affPlaceAt E a b)
          (algebraMap (MotC2.Coord E) ↥(MotC2.affPlaceAt E a b) (CoordinateRing.YClass E (C b)))
            = (1 : ℕ∞) :=
        IsDiscreteValuationRing.addVal_uniformizer hY
      exact ordOfPlace_eq_of hS hmem (by rw [hsub]; exact hadd)
    · -- `ord (3x² + 2a₂x + a₄ - a₁y) = 0`
      set r4 : MotC2.Coord E := 3 * (MotC2.coordX E) ^ 2 +
        algebraMap N (MotC2.Coord E) (2 * E.a₂) * MotC2.coordX E +
        algebraMap N (MotC2.Coord E) E.a₄ - algebraMap N (MotC2.Coord E) E.a₁ * MotC2.coordY E
      have key4 : 3 * (MotC2.genX E) ^ 2 + 2 * algebraMap N (MotC2.Func E) E.a₂ * MotC2.genX E +
            algebraMap N (MotC2.Func E) E.a₄ - algebraMap N (MotC2.Func E) E.a₁ * MotC2.genY E
          = algebraMap (MotC2.Coord E) (MotC2.Func E) r4 := by
        simp only [MotC2.genX, MotC2.genY, r4, map_sub, map_add, map_mul, map_pow, map_ofNat,
          IsScalarTower.algebraMap_apply N (MotC2.Coord E) (MotC2.Func E)] <;> ring
      have hmem : 3 * (MotC2.genX E) ^ 2 + 2 * algebraMap N (MotC2.Func E) E.a₂ * MotC2.genX E +
            algebraMap N (MotC2.Func E) E.a₄ - algebraMap N (MotC2.Func E) E.a₁ * MotC2.genY E
          ∈ MotC2.affPlaceAt E a b := by
        have h0 := MotC2.algebraMap_mem_affPlaceAt E a b r4
        rwa [← key4] at h0
      have hsub : (⟨3 * (MotC2.genX E) ^ 2 + 2 * algebraMap N (MotC2.Func E) E.a₂ * MotC2.genX E +
            algebraMap N (MotC2.Func E) E.a₄ - algebraMap N (MotC2.Func E) E.a₁ * MotC2.genY E,
            hmem⟩ : ↥(MotC2.affPlaceAt E a b)) =
          algebraMap (MotC2.Coord E) ↥(MotC2.affPlaceAt E a b) r4 := by
        apply Subtype.ext
        simpa [MotC2.affPlaceAt_algebraMap_val] using key4
      have hunit' : IsUnit (⟨3 * (MotC2.genX E) ^ 2 + 2 * algebraMap N (MotC2.Func E) E.a₂ *
            MotC2.genX E + algebraMap N (MotC2.Func E) E.a₄ -
            algebraMap N (MotC2.Func E) E.a₁ * MotC2.genY E, hmem⟩ :
          ↥(MotC2.affPlaceAt E a b)) := by
        rw [hsub]; exact hunit3
      have hadd : @IsDiscreteValuationRing.addVal ↥(MotC2.affPlaceAt E a b) _ _ hS.1.choose
          (⟨3 * (MotC2.genX E) ^ 2 + 2 * algebraMap N (MotC2.Func E) E.a₂ * MotC2.genX E +
            algebraMap N (MotC2.Func E) E.a₄ - algebraMap N (MotC2.Func E) E.a₁ * MotC2.genY E,
            hmem⟩ : ↥(MotC2.affPlaceAt E a b)) = ((0 : ℕ) : ℕ∞) :=
        (@IsDiscreteValuationRing.addVal_eq_zero_iff ↥(MotC2.affPlaceAt E a b) _ _
          hS.1.choose _).mpr hunit'
      exact ordOfPlace_eq_of hS hmem hadd

end

end Work.MotV
