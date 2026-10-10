import Mathlib
import Submission.Work.MotV5.KleinData5Defs
import Submission.Work.MotC2.Negation
import Submission.Work.MotV.Defs
import Submission.Work.MotK.KleinData
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotV5.exists_kleinData5`

The explicit characteristic-5 Klein datum `D5` is good, is a genuine curve, and has
`a² - ab - b² ≠ 0`.  See `Submission/Work/MotV5/KleinData5Defs.lean` for the data and for a
description of the computation.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotV5
noncomputable section

variable (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]

/-- `κ₀ = 1`. -/
lemma D5_kC_0 (L : Type) [Field L] [Algebra 𝕜 L] :
    Work.MotV.kleinCoord (D5 𝕜) L 0 = 1 := by
  simp only [Work.MotV.kleinCoord]
  rw [Fin.sum_univ_five]
  simp only [D5_coord, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [← IsScalarTower.algebraMap_apply, RingHom.map_one, RingHom.map_neg,
    RingHom.map_zero]
  first | refl_ring1 | ring

/-- `κ₁ = 1 + x - y - x² - x·y`. -/
lemma D5_kC_1 (L : Type) [Field L] [Algebra 𝕜 L] :
    Work.MotV.kleinCoord (D5 𝕜) L 1 =
      1 + XX 𝕜 L - YY 𝕜 L - XX 𝕜 L ^ 2 - XX 𝕜 L * YY 𝕜 L := by
  simp only [Work.MotV.kleinCoord]
  rw [Fin.sum_univ_five]
  simp only [D5_coord, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [← IsScalarTower.algebraMap_apply, RingHom.map_one, RingHom.map_neg,
    RingHom.map_zero]
  first | refl_ring1 | ring

/-- `κ₂ = -1 - 2x - 2x² - x·y`. -/
lemma D5_kC_2 (L : Type) [Field L] [Algebra 𝕜 L] :
    Work.MotV.kleinCoord (D5 𝕜) L 2 =
      -1 - 2 * XX 𝕜 L - 2 * XX 𝕜 L ^ 2 - XX 𝕜 L * YY 𝕜 L := by
  simp only [Work.MotV.kleinCoord]
  rw [Fin.sum_univ_five]
  simp only [D5_coord, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [← IsScalarTower.algebraMap_apply, RingHom.map_one, RingHom.map_neg,
    RingHom.map_zero]
  have h2 : (algebraMap 𝕜 (Affine.FunctionField ((D5 𝕜).E.baseChange L))) (2 : 𝕜) = 2 := by
    show (algebraMap 𝕜 (Affine.FunctionField ((D5 𝕜).E.baseChange L))) ((2 : ℕ) : 𝕜) =
      ((2 : ℕ) : Affine.FunctionField ((D5 𝕜).E.baseChange L))
    rw [map_natCast]
  rw [h2]
  first | refl_ring1 | ring

/-- `κ₃ = -1 + 2x - 2x² + x·y`. -/
lemma D5_kC_3 (L : Type) [Field L] [Algebra 𝕜 L] :
    Work.MotV.kleinCoord (D5 𝕜) L 3 =
      -1 + 2 * XX 𝕜 L - 2 * XX 𝕜 L ^ 2 + XX 𝕜 L * YY 𝕜 L := by
  simp only [Work.MotV.kleinCoord]
  rw [Fin.sum_univ_five]
  simp only [D5_coord, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [← IsScalarTower.algebraMap_apply, RingHom.map_one, RingHom.map_neg,
    RingHom.map_zero]
  have h2 : (algebraMap 𝕜 (Affine.FunctionField ((D5 𝕜).E.baseChange L))) (2 : 𝕜) = 2 := by
    show (algebraMap 𝕜 (Affine.FunctionField ((D5 𝕜).E.baseChange L))) ((2 : ℕ) : 𝕜) =
      ((2 : ℕ) : Affine.FunctionField ((D5 𝕜).E.baseChange L))
    rw [map_natCast]
  rw [h2]
  first | refl_ring1 | ring

/-- `κ₄ = y - x² + x·y`. -/
lemma D5_kC_4 (L : Type) [Field L] [Algebra 𝕜 L] :
    Work.MotV.kleinCoord (D5 𝕜) L 4 =
      YY 𝕜 L - XX 𝕜 L ^ 2 + XX 𝕜 L * YY 𝕜 L := by
  simp only [Work.MotV.kleinCoord]
  rw [Fin.sum_univ_five]
  simp only [D5_coord, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val,
    Matrix.head_cons, Matrix.tail_cons]
  simp only [← IsScalarTower.algebraMap_apply, RingHom.map_one, RingHom.map_neg,
    RingHom.map_zero]
  ring_nf

/-- The Weierstrass relation `y² - y - x³ + x² = 0` in the function field. -/
lemma D5_relation (L : Type) [Field L] [Algebra 𝕜 L] :
    YY 𝕜 L ^ 2 - YY 𝕜 L - XX 𝕜 L ^ 3 + XX 𝕜 L ^ 2 = 0 := by
  have hrel := Work.MotC2.genX_genY_relation ((D5 𝕜).E.baseChange L)
  have h0 : (algebraMap L (Affine.FunctionField ((D5 𝕜).E.baseChange L))) 0 = 0 := map_zero _
  have hm1 : (algebraMap L (Affine.FunctionField ((D5 𝕜).E.baseChange L))) (-1) = -1 := by
    rw [map_neg, map_one]
  rw [D5_baseChange_a₁, D5_baseChange_a₂, D5_baseChange_a₃, D5_baseChange_a₄, D5_baseChange_a₆,
    h0, hm1] at hrel
  have hrel' : YY 𝕜 L ^ 2 + 0 * XX 𝕜 L * YY 𝕜 L + (-1) * YY 𝕜 L =
      XX 𝕜 L ^ 3 + (-1) * XX 𝕜 L ^ 2 + 0 * XX 𝕜 L + 0 := hrel
  linear_combination (norm := first | refl_ring1 | ring1) hrel'

/-- The five Pfaffian quadrics vanish on the five Klein coordinates: `D5` satisfies
`KleinData.Good.klein_eq`. -/
theorem D5_klein_eq (L : Type) [Field L] [Algebra 𝕜 L] :
    ∀ k : Fin 5,
      Work.MotK.kleinP
        (algebraMap 𝕜 (Affine.FunctionField ((D5 𝕜).E.baseChange L)) 1)
        (algebraMap 𝕜 (Affine.FunctionField ((D5 𝕜).E.baseChange L)) 1)
        (Work.MotV.kleinCoord (D5 𝕜) L) k = 0 := by
  have hW : YY 𝕜 L ^ 2 - YY 𝕜 L - XX 𝕜 L ^ 3 + XX 𝕜 L ^ 2 = 0 := D5_relation 𝕜 L
  haveI hL : CharP L 5 := charP_of_injective_algebraMap (algebraMap 𝕜 L).injective 5
  haveI : CharP (Affine.FunctionField ((D5 𝕜).E.baseChange L)) 5 :=
    charP_of_injective_algebraMap (algebraMap L _).injective 5
  have h5 : (5 : Affine.FunctionField ((D5 𝕜).E.baseChange L)) = 0 :=
    (CharP.cast_eq_zero_iff _ 5 5).mpr (dvd_refl 5)
  have key : ∀ (κ : Fin 5 → Affine.FunctionField ((D5 𝕜).E.baseChange L)),
      κ = Work.MotV.kleinCoord (D5 𝕜) L → ∀ k : Fin 5,
      Work.MotK.kleinP
        (algebraMap 𝕜 (Affine.FunctionField ((D5 𝕜).E.baseChange L)) 1)
        (algebraMap 𝕜 (Affine.FunctionField ((D5 𝕜).E.baseChange L)) 1) κ k = 0 := by
    intro κ hκ k
    fin_cases k <;>
      simp only [Work.MotK.kleinP_zero', Work.MotK.kleinP_one', Work.MotK.kleinP_two',
        Work.MotK.kleinP_three', Work.MotK.kleinP_four', Work.MotK.kleinP0, Work.MotK.kleinP1,
        Work.MotK.kleinP2, Work.MotK.kleinP3, Work.MotK.kleinP4, hκ, D5_kC_0, D5_kC_1, D5_kC_2,
        D5_kC_3, D5_kC_4, RingHom.map_one]
    · linear_combination (norm := first | refl_ring1 | ring1) (2 * XX 𝕜 L + 1) * hW + (XX 𝕜 L ^ 2 * (XX 𝕜 L ^ 2 - YY 𝕜 L)) * h5
    · linear_combination (norm := first | refl_ring1 | ring1) (XX 𝕜 L) * hW + (-(XX 𝕜 L) *
        (XX 𝕜 L ^ 3 + XX 𝕜 L ^ 2 * YY 𝕜 L + XX 𝕜 L ^ 2 + XX 𝕜 L * YY 𝕜 L + 2 * XX 𝕜 L + 1)) * h5
    · linear_combination (norm := first | refl_ring1 | ring1) (-(XX 𝕜 L) - 1) * hW + (XX 𝕜 L *
        (XX 𝕜 L ^ 2 * YY 𝕜 L + XX 𝕜 L * YY 𝕜 L - 1)) * h5
    · linear_combination (norm := first | refl_ring1 | ring1) (-(XX 𝕜 L) - 1) * hW + (-(XX 𝕜 L) *
        (XX 𝕜 L ^ 2 * YY 𝕜 L - XX 𝕜 L - YY 𝕜 L)) * h5
    · linear_combination (norm := first | refl_ring1 | ring1) (XX 𝕜 L) * hW + (-(XX 𝕜 L) *
        (XX 𝕜 L ^ 3 - XX 𝕜 L ^ 2 * YY 𝕜 L - XX 𝕜 L ^ 2 + 2 * XX 𝕜 L - YY 𝕜 L - 1)) * h5
  exact key (Work.MotV.kleinCoord (D5 𝕜) L) rfl

/-- The image of the negation `[-1]` on the ratio `κ₁/κ₀`. -/
lemma D5_neg_ratio (L : Type) [Field L] [Algebra 𝕜 L] :
    (Work.MotC2.negAlgEquiv ((D5 𝕜).E.baseChange L))
        (1 + XX 𝕜 L - YY 𝕜 L - XX 𝕜 L ^ 2 - XX 𝕜 L * YY 𝕜 L) =
      YY 𝕜 L - XX 𝕜 L ^ 2 + XX 𝕜 L * YY 𝕜 L := by
  have hx : (Work.MotC2.negAlgEquiv ((D5 𝕜).E.baseChange L)) (XX 𝕜 L) = XX 𝕜 L :=
    Work.MotC2.negAlgEquiv_genX ((D5 𝕜).E.baseChange L)
  have hy : (Work.MotC2.negAlgEquiv ((D5 𝕜).E.baseChange L)) (YY 𝕜 L) =
      -YY 𝕜 L - (algebraMap L (Affine.FunctionField ((D5 𝕜).E.baseChange L)))
          (((D5 𝕜).E.baseChange L).a₁) * XX 𝕜 L
        - (algebraMap L (Affine.FunctionField ((D5 𝕜).E.baseChange L)))
          (((D5 𝕜).E.baseChange L).a₃) :=
    Work.MotC2.negAlgEquiv_genY ((D5 𝕜).E.baseChange L)
  have h0 : (algebraMap L (Affine.FunctionField ((D5 𝕜).E.baseChange L))) 0 = 0 := map_zero _
  have hm1 : (algebraMap L (Affine.FunctionField ((D5 𝕜).E.baseChange L))) (-1) = -1 := by
    rw [map_neg, map_one]
  simp only [map_one, map_sub, map_add, map_mul, map_pow, hx, hy, D5_baseChange_a₁,
    D5_baseChange_a₃, h0, hm1]
  first | refl_ring1 | ring

/-- The element `1 + x - 2x²` is transcendental over `𝕜`. -/
lemma D5_transcendental (L : Type) [Field L] [Algebra 𝕜 L] :
    Transcendental 𝕜 (1 + XX 𝕜 L - 2 * XX 𝕜 L ^ 2) := by
  haveI hL : CharP L 5 := charP_of_injective_algebraMap (algebraMap 𝕜 L).injective 5
  have hX : Transcendental 𝕜 (XX 𝕜 L) :=
    Transcendental.restrictScalars (algebraMap 𝕜 L).injective
      (Work.MotC2.transcendental_genX ((D5 𝕜).E.baseChange L))
  haveI : CharP (Affine.FunctionField ((D5 𝕜).E.baseChange L)) 5 :=
    charP_of_injective_algebraMap (algebraMap L _).injective 5
  have h5F : (5 : Affine.FunctionField ((D5 𝕜).E.baseChange L)) = 0 :=
    (CharP.cast_eq_zero_iff _ 5 5).mpr (dvd_refl 5)
  have h32F : (3 : Affine.FunctionField ((D5 𝕜).E.baseChange L)) = -2 := by
    linear_combination (norm := first | refl_ring1 | ring1) h5F
  have h3c : (algebraMap 𝕜 (Affine.FunctionField ((D5 𝕜).E.baseChange L))) (3 : 𝕜) = 3 := by
    show (algebraMap 𝕜 (Affine.FunctionField ((D5 𝕜).E.baseChange L))) ((3 : ℕ) : 𝕜) =
      ((3 : ℕ) : Affine.FunctionField ((D5 𝕜).E.baseChange L))
    rw [map_natCast]
  have hq : (Polynomial.C (1 : 𝕜) + Polynomial.X + Polynomial.C 3 * Polynomial.X ^ 2 :
      Polynomial 𝕜).natDegree = 2 := by
    compute_degree!
    intro h
    exact absurd ((CharP.cast_eq_zero_iff 𝕜 5 3).mp h) (by norm_num)
  have hq0 : (Polynomial.C (1 : 𝕜) + Polynomial.X + Polynomial.C 3 * Polynomial.X ^ 2 :
      Polynomial 𝕜).natDegree ≠ 0 := by rw [hq]; norm_num
  have hlc : (Polynomial.C (1 : 𝕜) + Polynomial.X + Polynomial.C 3 * Polynomial.X ^ 2 :
      Polynomial 𝕜).leadingCoeff ∈ nonZeroDivisors 𝕜 := by
    rw [mem_nonZeroDivisors_iff_ne_zero, Polynomial.leadingCoeff, hq]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_X,
      Polynomial.coeff_C_mul_X_pow]
    norm_num
    intro h
    exact absurd ((CharP.cast_eq_zero_iff 𝕜 5 3).mp h) (by norm_num)
  have heq : (Polynomial.aeval (XX 𝕜 L))
      (Polynomial.C (1 : 𝕜) + Polynomial.X + Polynomial.C 3 * Polynomial.X ^ 2)
      = 1 + XX 𝕜 L - 2 * XX 𝕜 L ^ 2 := by
    simp only [Polynomial.aeval_X, Polynomial.aeval_C, map_add, map_mul, map_pow, map_one]
    rw [h3c, h32F]
    first | refl_ring1 | ring
  simpa only [heq] using hX.aeval _ hq0 hlc

/-- `κ₁/κ₀` is transcendental over `𝕜`. -/
lemma D5_transcendental_ratio (L : Type) [Field L] [Algebra 𝕜 L] :
    Transcendental 𝕜 (1 + XX 𝕜 L - YY 𝕜 L - XX 𝕜 L ^ 2 - XX 𝕜 L * YY 𝕜 L) := by
  haveI hL : CharP L 5 := charP_of_injective_algebraMap (algebraMap 𝕜 L).injective 5
  intro halg
  have hσf : IsAlgebraic 𝕜 (YY 𝕜 L - XX 𝕜 L ^ 2 + XX 𝕜 L * YY 𝕜 L) := by
    have h := halg.algHom
      ((Work.MotC2.negAlgEquiv ((D5 𝕜).E.baseChange L)).toAlgHom.restrictScalars 𝕜)
    have hval : ((Work.MotC2.negAlgEquiv ((D5 𝕜).E.baseChange L)).toAlgHom.restrictScalars 𝕜)
        (1 + XX 𝕜 L - YY 𝕜 L - XX 𝕜 L ^ 2 - XX 𝕜 L * YY 𝕜 L)
        = YY 𝕜 L - XX 𝕜 L ^ 2 + XX 𝕜 L * YY 𝕜 L := by
      simp only [AlgHom.restrictScalars_apply]
      exact D5_neg_ratio 𝕜 L
    rw [hval] at h
    exact h
  have h_adj : (Algebra.adjoin 𝕜
      ({(1 + XX 𝕜 L - YY 𝕜 L - XX 𝕜 L ^ 2 - XX 𝕜 L * YY 𝕜 L),
        (YY 𝕜 L - XX 𝕜 L ^ 2 + XX 𝕜 L * YY 𝕜 L)} :
        Set (Affine.FunctionField ((D5 𝕜).E.baseChange L)))).IsAlgebraic :=
    Algebra.isAlgebraic_adjoin_iff.mpr (by
      intro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact halg
      · exact hσf)
  have hmem : (1 + XX 𝕜 L - YY 𝕜 L - XX 𝕜 L ^ 2 - XX 𝕜 L * YY 𝕜 L) +
      (YY 𝕜 L - XX 𝕜 L ^ 2 + XX 𝕜 L * YY 𝕜 L) ∈ Algebra.adjoin 𝕜
      ({(1 + XX 𝕜 L - YY 𝕜 L - XX 𝕜 L ^ 2 - XX 𝕜 L * YY 𝕜 L),
        (YY 𝕜 L - XX 𝕜 L ^ 2 + XX 𝕜 L * YY 𝕜 L)} :
        Set (Affine.FunctionField ((D5 𝕜).E.baseChange L))) :=
    (Algebra.adjoin 𝕜 _).add_mem (Algebra.subset_adjoin (by simp))
      (Algebra.subset_adjoin (by simp))
  have hsum : IsAlgebraic 𝕜 ((1 + XX 𝕜 L - YY 𝕜 L - XX 𝕜 L ^ 2 - XX 𝕜 L * YY 𝕜 L) +
      (YY 𝕜 L - XX 𝕜 L ^ 2 + XX 𝕜 L * YY 𝕜 L)) := h_adj _ hmem
  have h2 : IsAlgebraic 𝕜 (1 + XX 𝕜 L - 2 * XX 𝕜 L ^ 2) := by
    convert hsum using 2
    first | refl_ring1 | ring
  exact D5_transcendental 𝕜 L h2

/-- `D5` is a genuine curve: `KleinData.Nonconstant`. -/
theorem D5_nonconstant : Work.MotV5.KleinData.Nonconstant (D5 𝕜) := by
  refine ⟨1, ?_⟩
  intro L _ _
  rw [D5_kC_0 𝕜 L, D5_kC_1 𝕜 L, div_one]
  exact D5_transcendental_ratio 𝕜 L


/-- The basis `1, x, y, x², xy` bundled in the abbreviations `XX`, `YY`.
The `Fin.mk` form is used because `fin_cases` produces `⟨n, _⟩` rather than the `OfNat`. -/
lemma D5_kleinBas_zero (L : Type) [Field L] [Algebra 𝕜 L] (h : 0 < 5) :
    Work.MotV.kleinBas (D5 𝕜) L ⟨0, h⟩ = 1 := rfl

lemma D5_kleinBas_one (L : Type) [Field L] [Algebra 𝕜 L] (h : 1 < 5) :
    Work.MotV.kleinBas (D5 𝕜) L ⟨1, h⟩ = XX 𝕜 L := rfl

lemma D5_kleinBas_two (L : Type) [Field L] [Algebra 𝕜 L] (h : 2 < 5) :
    Work.MotV.kleinBas (D5 𝕜) L ⟨2, h⟩ = YY 𝕜 L := rfl

lemma D5_kleinBas_three (L : Type) [Field L] [Algebra 𝕜 L] (h : 3 < 5) :
    Work.MotV.kleinBas (D5 𝕜) L ⟨3, h⟩ = XX 𝕜 L ^ 2 := rfl

lemma D5_kleinBas_four (L : Type) [Field L] [Algebra 𝕜 L] (h : 4 < 5) :
    Work.MotV.kleinBas (D5 𝕜) L ⟨4, h⟩ = XX 𝕜 L * YY 𝕜 L := rfl

/-- The inverse of the coordinate matrix of `D5` over `𝔽₅`. -/
def D5_inv (𝕜 : Type) [Field 𝕜] : Fin 5 → Fin 5 → 𝕜 :=
  ![![1, 0, 0, 0, 0],
    ![3, 1, 2, 2, 1],
    ![3, 2, 3, 2, 3],
    ![2, 0, 1, 1, 0],
    ![4, 3, 3, 4, 3]]

/-- The Klein coordinates of `D5` are a `𝕜`-basis of `L(5·O)`: `KleinData.Good.spans`. -/
theorem D5_spans : ∃ e : Fin 5 → Fin 5 → 𝕜,
    ∀ (L : Type) [Field L] [Algebra 𝕜 L] (m : Fin 5),
      Work.MotV.kleinBas (D5 𝕜) L m =
        ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) *
          Work.MotV.kleinCoord (D5 𝕜) L i := by
  refine ⟨D5_inv 𝕜, ?_⟩
  intro L _ _ m
  have h2c : (algebraMap 𝕜 (Affine.FunctionField ((D5 𝕜).E.baseChange L))) (2 : 𝕜) = 2 :=
    map_natCast _ 2
  have h3c : (algebraMap 𝕜 (Affine.FunctionField ((D5 𝕜).E.baseChange L))) (3 : 𝕜) = 3 :=
    map_natCast _ 3
  have h4c : (algebraMap 𝕜 (Affine.FunctionField ((D5 𝕜).E.baseChange L))) (4 : 𝕜) = 4 :=
    map_natCast _ 4
  haveI hL : CharP L 5 := charP_of_injective_algebraMap (algebraMap 𝕜 L).injective 5
  haveI : CharP (Affine.FunctionField ((D5 𝕜).E.baseChange L)) 5 :=
    charP_of_injective_algebraMap (algebraMap L _).injective 5
  have h5 : (5 : Affine.FunctionField ((D5 𝕜).E.baseChange L)) = 0 :=
    (CharP.cast_eq_zero_iff _ 5 5).mpr (dvd_refl 5)
  fin_cases m
  all_goals
    rw [Fin.sum_univ_five, D5_kC_0 𝕜 L, D5_kC_1 𝕜 L, D5_kC_2 𝕜 L, D5_kC_3 𝕜 L, D5_kC_4 𝕜 L]
    simp only [D5_kleinBas_zero, D5_kleinBas_one, D5_kleinBas_two, D5_kleinBas_three,
      D5_kleinBas_four, D5_inv, Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
      ← IsScalarTower.algebraMap_apply, RingHom.map_one, RingHom.map_neg, RingHom.map_zero]
    try rw [h2c]
    try rw [h3c]
    try rw [h4c]
  · first | refl_ring1 | ring
  · linear_combination (norm := first | refl_ring1 | ring1) (2 * XX 𝕜 L ^ 2) * h5
  · linear_combination (norm := first | refl_ring1 | ring1) (3 * XX 𝕜 L ^ 2) * h5
  · linear_combination (norm := first | refl_ring1 | ring1) (XX 𝕜 L ^ 2) * h5
  · linear_combination (norm := first | refl_ring1 | ring1) (4 * XX 𝕜 L ^ 2 - XX 𝕜 L) * h5

theorem exists_kleinData5 (𝕜 : Type) [Field 𝕜] [Infinite 𝕜] [CharP 𝕜 5] :
    ∃ D : Work.MotV.KleinData 𝕜, D.Good ∧ Work.MotV5.KleinData.Nonconstant D ∧
      D.a ^ 2 - D.a * D.b - D.b ^ 2 ≠ 0 := by
  refine ⟨D5 𝕜, ⟨D5_isElliptic 𝕜, ?_, D5_j_ne_zero 𝕜, D5_j_ne 𝕜, ?_, ?_, D5_T_diag 𝕜,
    D5_spans 𝕜⟩, D5_nonconstant 𝕜, D5_smooth 𝕜⟩
  · rw [D5_a, D5_b]; norm_num
  · intro L _ _ k
    exact D5_klein_eq 𝕜 L k
  · intro L _ _
    rw [D5_kC_0 𝕜 L]
    exact one_ne_zero

end
end Work.MotV5
