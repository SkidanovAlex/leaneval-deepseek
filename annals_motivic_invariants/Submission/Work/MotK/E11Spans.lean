-- This file is a *copy* of `Submission/Work/MotK/Spans.lean` (whose declarations are renamed with
-- the prefix `e11_` so that the copy can be imported by `Submission/Work/MotK/ExistsKleinData.lean`
-- without an import cycle).  The proofs are unchanged.
import Mathlib
import Submission.Work.MotK.E11Model
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.e11_Spans`

The two nondegeneracy properties of the explicit Klein data `Work.MotK.kleinDataCandidate`
(the `b = 11` Tate normal form, valid whenever `11 ≠ 0` in the base field):

* `κ₀ = 5x² + 55x + 121` does not vanish in the function field of `E₁₁` over any field
  extension `L/𝕜`;
* the basis `1, x, y, x², xy` of `L(5·O)` is a `𝕜`-linear combination of the Klein linear forms
  `κ₀, …, κ₄`, i.e. the explicit `5 × 5` matrix `kleinCoordInt` is invertible.

The first is proved by descending to the coordinate ring `L[E₁₁]`, which is free on `1, Y`
over `L[X]` (`WeierstrassCurve.Affine.CoordinateRing.basis`); hence a polynomial in `X` alone
vanishes in the function field only if it vanishes in `L[X]`.  For `5x² + 55x + 121` this is
impossible because its constant coefficient is `11² ≠ 0`.

The second is the integral matrix identity `adj · coordInt = 1331 · 1` (`1331 = 11³`), which
becomes invertibility of `coordInt` over `𝕜` as soon as `11 ≠ 0`.
-/

namespace Work.MotK

open WeierstrassCurve WeierstrassCurve.Affine

noncomputable section

/-! ## §1 The coordinate matrix of the candidate -/

/-- The `coord` field of `kleinDataCandidate` is the integral matrix `kleinCoordInt`, cast. -/
lemma e11_candidate_coord_eq (𝕜 : Type) [Field 𝕜] :
    (kleinDataCandidate 𝕜).coord = fun i j => (kleinCoordInt i j : 𝕜) := rfl

/-! ## §2 The integral inverse of `kleinCoordInt` -/

/-- `11³` times the inverse of the matrix `kleinCoordInt` (whose determinant is `11⁵`). -/
def e11_adjInt : Fin 5 → Fin 5 → ℤ :=
  !![ -14, -5, -15, -15, -5;
      88, 66, 77, 77, 66;
      363, 363, 242, 363, 242;
      -363, -605, -484, -484, -605;
      -1331, -2662, -1331, -2662, -2662]

/-- The matrix identity `e11_adjInt · kleinCoordInt = 11³ · 1` over `ℤ`. -/
lemma e11_adjInt_mul (m j : Fin 5) :
    ∑ i : Fin 5, e11_adjInt m i * kleinCoordInt i j = 1331 * (if m = j then 1 else 0) := by
  fin_cases m <;> fin_cases j <;>
  · rw [Fin.sum_univ_five]
    norm_num [e11_adjInt, kleinCoordInt]

/-- The inverse of the Klein coordinate matrix over any field with `11 ≠ 0`. -/
def e11_eCand (𝕜 : Type) [Field 𝕜] : Fin 5 → Fin 5 → 𝕜 :=
  fun m i => ((e11_adjInt m i : ℤ) : 𝕜) * ((1331 : 𝕜))⁻¹

/-- `e11_eCand` is a right inverse of the coordinate matrix over `𝕜` (`11 ≠ 0`). -/
lemma e11_eCand_mul (𝕜 : Type) [Field 𝕜] (h11 : (11 : 𝕜) ≠ 0) (m j : Fin 5) :
    ∑ i : Fin 5, e11_eCand 𝕜 m i * ((kleinCoordInt i j : ℤ) : 𝕜) = if m = j then 1 else 0 := by
  have h1331 : (1331 : 𝕜) ≠ 0 := by
    have h : (1331 : 𝕜) = 11 * (11 * 11) := by norm_num
    rw [h]; exact mul_ne_zero h11 (mul_ne_zero h11 h11)
  have hZ := e11_adjInt_mul m j
  have hcast : ((∑ i : Fin 5, e11_adjInt m i * kleinCoordInt i j : ℤ) : 𝕜)
      = ((1331 * (if m = j then 1 else 0) : ℤ) : 𝕜) := by rw [hZ]
  push_cast at hcast
  simp only [e11_eCand]
  rw [show (∑ i : Fin 5, ((e11_adjInt m i : ℤ) : 𝕜) * ((1331 : 𝕜))⁻¹ * ((kleinCoordInt i j : ℤ) : 𝕜))
      = (∑ i : Fin 5, ((e11_adjInt m i : ℤ) : 𝕜) * ((kleinCoordInt i j : ℤ) : 𝕜)) *
          ((1331 : 𝕜))⁻¹ from by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => by ring)]
  rw [hcast]
  split_ifs with h
  · simp only [mul_one]; exact mul_inv_cancel₀ h1331
  · simp

/-! ## §3 A polynomial in `X` does not vanish in the function field -/

/-- In the function field of any Weierstrass curve over a field `L`, the class of a nonzero
polynomial in the `x`-coordinate is nonzero: the coordinate ring is free over `L[X]` on `1, Y`
and embeds in its fraction field. -/
lemma e11_algebraMap_polynomial_ne_zero (L : Type) [Field L] (W : WeierstrassCurve L)
    (P : Polynomial L) (hP : P ≠ 0) :
    algebraMap (Polynomial L) (Affine.FunctionField W) P ≠ 0 := by
  intro h
  have h1 : algebraMap (CoordinateRing W) (Affine.FunctionField W)
      (algebraMap (Polynomial L) (CoordinateRing W) P) = 0 := by
    rw [← IsScalarTower.algebraMap_apply (Polynomial L) (CoordinateRing W)
      (Affine.FunctionField W)]
    exact h
  have h2 : algebraMap (Polynomial L) (CoordinateRing W) P = 0 :=
    IsFractionRing.injective (CoordinateRing W) (Affine.FunctionField W) (by rw [h1, map_zero])
  have h3 : P • (1 : CoordinateRing W) = 0 := by
    rw [← h2, CoordinateRing.smul]; simp
  have h4 : P • (1 : CoordinateRing W) + (0 : Polynomial L) •
      (CoordinateRing.mk W Polynomial.X) = 0 := by
    rw [h3]; simp
  exact hP (CoordinateRing.smul_basis_eq_zero h4).1

/-! ## §4 Nonvanishing of `κ₀` -/

/-- `κ₀` of the candidate, as the image of the polynomial `5X² + 55X + 121 ∈ L[X]`. -/
lemma e11_kleinCoord_candidate_zero (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L] :
    Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0 =
      algebraMap (Polynomial L) (Affine.FunctionField ((kleinDataCandidate 𝕜).E.baseChange L))
        (Polynomial.C (algebraMap 𝕜 L 5) * Polynomial.X ^ 2 + Polynomial.C (algebraMap 𝕜 L 55) * Polynomial.X
          + Polynomial.C (algebraMap 𝕜 L 121)) := by
  rw [show Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0 =
      (algebraMap L (Affine.FunctionField ((kleinDataCandidate 𝕜).E.baseChange L)))
          ((algebraMap 𝕜 L) 121) +
      (algebraMap L (Affine.FunctionField ((kleinDataCandidate 𝕜).E.baseChange L)))
          ((algebraMap 𝕜 L) 55) *
        Work.MotV.genX ((kleinDataCandidate 𝕜).E.baseChange L) +
      (algebraMap L (Affine.FunctionField ((kleinDataCandidate 𝕜).E.baseChange L)))
          ((algebraMap 𝕜 L) 5) *
        Work.MotV.genX ((kleinDataCandidate 𝕜).E.baseChange L) ^ 2 from by
    simp only [Work.MotV.kleinCoord]
    rw [e11_candidate_coord_eq]
    rw [Fin.sum_univ_five]
    norm_num [kleinCoordInt]]
  have hgen : algebraMap (Polynomial L) (Affine.FunctionField ((kleinDataCandidate 𝕜).E.baseChange L))
        Polynomial.X
      = Work.MotV.genX ((kleinDataCandidate 𝕜).E.baseChange L) := by
    rw [Work.MotV.genX]
    exact (IsScalarTower.algebraMap_apply (Polynomial L)
      (CoordinateRing ((kleinDataCandidate 𝕜).E.baseChange L))
      (Affine.FunctionField ((kleinDataCandidate 𝕜).E.baseChange L)) Polynomial.X).symm
  simp only [map_add, map_mul, map_pow, hgen, Polynomial.C_eq_algebraMap,
    ← IsScalarTower.algebraMap_apply L (Polynomial L)
      (Affine.FunctionField ((kleinDataCandidate 𝕜).E.baseChange L))]
  first | refl_ring1 | ring

/-- `κ₀ ≠ 0` for the candidate, in every field extension `L/𝕜` with `11 ≠ 0`. -/
lemma e11_coord0_ne_candidate (𝕜 : Type) [Field 𝕜] (h11 : (11 : 𝕜) ≠ 0)
    (L : Type) [Field L] [Algebra 𝕜 L] :
    Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L 0 ≠ 0 := by
  rw [e11_kleinCoord_candidate_zero]
  apply e11_algebraMap_polynomial_ne_zero
  intro h
  have hc : (Polynomial.C (algebraMap 𝕜 L 5) * Polynomial.X ^ 2 + Polynomial.C (algebraMap 𝕜 L 55) * Polynomial.X
      + Polynomial.C (algebraMap 𝕜 L 121) : Polynomial L).coeff 0 = algebraMap 𝕜 L 121 := by
    simp
  have h0 : (algebraMap 𝕜 L 121) = 0 := by
    rw [← hc, h, Polynomial.coeff_zero]
  have h121 : (121 : L) ≠ 0 := by
    have h11L : (11 : L) ≠ 0 := by
      rw [show (11 : L) = algebraMap 𝕜 L (11 : 𝕜) from (map_ofNat (algebraMap 𝕜 L) 11).symm]
      intro hh
      exact h11 ((algebraMap 𝕜 L).injective (by rw [hh, map_zero]))
    have hh : (121 : L) = (11 : L) * (11 : L) := by ring
    rw [hh]
    exact mul_ne_zero h11L h11L
  exact h121 (by rw [← map_ofNat (algebraMap 𝕜 L) 121]; exact h0)

/-! ## §5 The span condition -/

/-- The function field of the candidate over `L`. -/
abbrev e11_Fk (𝕜 : Type) [Field 𝕜] (L : Type) [Field L] [Algebra 𝕜 L] : Type :=
  Affine.FunctionField ((kleinDataCandidate 𝕜).E.baseChange L)

/-- With `e11_eCand` as coefficients, the Klein basis `1, x, y, x², xy` is a `𝕜`-linear combination
of the Klein forms `κ₀, …, κ₄`. -/
lemma e11_spans_candidate_apply (𝕜 : Type) [Field 𝕜] (h11 : (11 : 𝕜) ≠ 0) (L : Type) [Field L]
    [Algebra 𝕜 L] (m : Fin 5) :
    Work.MotV.kleinBas (kleinDataCandidate 𝕜) L m =
      ∑ i : Fin 5, algebraMap L (e11_Fk 𝕜 L) (algebraMap 𝕜 L (e11_eCand 𝕜 m i)) *
        Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L i := by
  have hc : ∀ i : Fin 5, Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L i =
      ∑ j : Fin 5, algebraMap 𝕜 (e11_Fk 𝕜 L) ((kleinCoordInt i j : ℤ) : 𝕜) *
        Work.MotV.kleinBas (kleinDataCandidate 𝕜) L j := by
    intro i
    rw [Work.MotV.kleinCoord_eq_sum, e11_candidate_coord_eq]
    simp only []
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← IsScalarTower.algebraMap_apply 𝕜 L (e11_Fk 𝕜 L)]
  have hmul : ∀ j : Fin 5, (∑ i : Fin 5, algebraMap 𝕜 (e11_Fk 𝕜 L) (e11_eCand 𝕜 m i) *
        algebraMap 𝕜 (e11_Fk 𝕜 L) ((kleinCoordInt i j : ℤ) : 𝕜)) =
        algebraMap 𝕜 (e11_Fk 𝕜 L) (if m = j then 1 else 0) := by
    intro j
    simp only [← map_mul (algebraMap 𝕜 (e11_Fk 𝕜 L)), ← map_sum (algebraMap 𝕜 (e11_Fk 𝕜 L))]
    rw [e11_eCand_mul 𝕜 h11 m j]
  have key : (∑ i : Fin 5, algebraMap 𝕜 (e11_Fk 𝕜 L) (e11_eCand 𝕜 m i) *
        Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L i) =
        Work.MotV.kleinBas (kleinDataCandidate 𝕜) L m := by
    calc ∑ i : Fin 5, algebraMap 𝕜 (e11_Fk 𝕜 L) (e11_eCand 𝕜 m i) *
            Work.MotV.kleinCoord (kleinDataCandidate 𝕜) L i
        = ∑ i : Fin 5, algebraMap 𝕜 (e11_Fk 𝕜 L) (e11_eCand 𝕜 m i) *
            ∑ j : Fin 5, algebraMap 𝕜 (e11_Fk 𝕜 L) ((kleinCoordInt i j : ℤ) : 𝕜) *
              Work.MotV.kleinBas (kleinDataCandidate 𝕜) L j := by
          refine Finset.sum_congr rfl (fun i _ => ?_); rw [hc i]
      _ = ∑ i : Fin 5, ∑ j : Fin 5, algebraMap 𝕜 (e11_Fk 𝕜 L) (e11_eCand 𝕜 m i) *
              (algebraMap 𝕜 (e11_Fk 𝕜 L) ((kleinCoordInt i j : ℤ) : 𝕜) *
                Work.MotV.kleinBas (kleinDataCandidate 𝕜) L j) := by
          simp only [Finset.mul_sum]
      _ = ∑ i : Fin 5, ∑ j : Fin 5, (algebraMap 𝕜 (e11_Fk 𝕜 L) (e11_eCand 𝕜 m i) *
              algebraMap 𝕜 (e11_Fk 𝕜 L) ((kleinCoordInt i j : ℤ) : 𝕜)) *
                Work.MotV.kleinBas (kleinDataCandidate 𝕜) L j := by
          refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
      _ = ∑ j : Fin 5, ∑ i : Fin 5, (algebraMap 𝕜 (e11_Fk 𝕜 L) (e11_eCand 𝕜 m i) *
              algebraMap 𝕜 (e11_Fk 𝕜 L) ((kleinCoordInt i j : ℤ) : 𝕜)) *
                Work.MotV.kleinBas (kleinDataCandidate 𝕜) L j := Finset.sum_comm
      _ = ∑ j : Fin 5, (∑ i : Fin 5, algebraMap 𝕜 (e11_Fk 𝕜 L) (e11_eCand 𝕜 m i) *
              algebraMap 𝕜 (e11_Fk 𝕜 L) ((kleinCoordInt i j : ℤ) : 𝕜)) *
                Work.MotV.kleinBas (kleinDataCandidate 𝕜) L j := by
          simp only [Finset.sum_mul]
      _ = ∑ j : Fin 5, algebraMap 𝕜 (e11_Fk 𝕜 L) (if m = j then 1 else 0) *
                Work.MotV.kleinBas (kleinDataCandidate 𝕜) L j := by
          refine Finset.sum_congr rfl (fun j _ => by rw [hmul j])
      _ = Work.MotV.kleinBas (kleinDataCandidate 𝕜) L m := by
          rw [Finset.sum_eq_single m]
          · simp
          · intro b _ hb; simp [Ne.symm hb]
          · intro h; exact absurd (Finset.mem_univ m) h
  simpa only [IsScalarTower.algebraMap_apply 𝕜 L (e11_Fk 𝕜 L)] using key.symm

/-! ## §6 The main theorem -/

theorem e11_Spans (𝕜 : Type) [Field 𝕜] (h11 : (11 : 𝕜) ≠ 0) :
    (∀ (L : Type) [Field L] [Algebra 𝕜 L],
      Work.MotV.kleinCoord (Work.MotK.kleinDataCandidate 𝕜) L 0 ≠ 0) ∧
    (∃ e : Fin 5 → Fin 5 → 𝕜, ∀ (L : Type) [Field L] [Algebra 𝕜 L] (m : Fin 5),
      Work.MotV.kleinBas (Work.MotK.kleinDataCandidate 𝕜) L m =
        ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) *
          Work.MotV.kleinCoord (Work.MotK.kleinDataCandidate 𝕜) L i) :=
  ⟨fun L _ _ => e11_coord0_ne_candidate 𝕜 h11 L,
   e11_eCand 𝕜, fun L _ _ m => e11_spans_candidate_apply 𝕜 h11 L m⟩

end

end Work.MotK
