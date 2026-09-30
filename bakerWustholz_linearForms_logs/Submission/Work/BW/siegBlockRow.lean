/-
Copyright: work of the Baker–Wüstholz formalisation team.
-/
import Mathlib
import Submission.Work.BW.sieg2Defs
import Submission.Work.BW.sieg2KernelDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The place-block of multiplication on the mixed space

The mixed space `mixedSpace F = (∏_{w real} ℝ) × (∏_{w complex} ℂ)` is a product ring, so
multiplication by the mixed embedding `me α` of `α : F` acts place by place.  Consequently the
matrix of that multiplication in the standard basis `stdBasis F` has, in each row belonging to an
infinite place `w`, sum of squares equal to `(w α)²`.  This is the arithmetic input of the
"Hadamard per place" step of the sharp Bombieri–Vaaler kernel-lattice bound
(`Work.BW.sieg2_kernel_family`, step 3): it produces the sharp factor `N^{d/2}·∏_w (⨆_j w(a i j))`
with no loss.
-/

open NumberField
open scoped Classical

namespace Work.BW

noncomputable def siegPlaceOf {F : Type*} [Field F] [NumberField F] :
    NumberField.mixedEmbedding.index F → NumberField.InfinitePlace F :=
  Sum.elim (fun w => w.1) (fun p => p.1.1)

@[simp] lemma siegPlaceOf_inl {F : Type*} [Field F] [NumberField F]
    (w : {w : NumberField.InfinitePlace F // w.IsReal}) :
    siegPlaceOf (F := F) (Sum.inl w) = w.1 := rfl

@[simp] lemma siegPlaceOf_inr {F : Type*} [Field F] [NumberField F]
    (w : {w : NumberField.InfinitePlace F // w.IsComplex}) (j : Fin 2) :
    siegPlaceOf (F := F) (Sum.inr (w, j)) = w.1 := rfl

lemma sieg_stdBasis_repr_self_apply {F : Type*} [Field F] [NumberField F]
    (q' r : NumberField.mixedEmbedding.index F) :
    ((NumberField.mixedEmbedding.stdBasis F).repr (NumberField.mixedEmbedding.stdBasis F q')) r
      = if q' = r then 1 else 0 :=
  Module.Basis.repr_self_apply _ _ _

lemma sieg_real_coord {F : Type*} [Field F] [NumberField F] (α : F)
    (q' : NumberField.mixedEmbedding.index F) (w : {w : NumberField.InfinitePlace F // w.IsReal}) :
    ((NumberField.mixedEmbedding.stdBasis F).repr
        (NumberField.mixedEmbedding F α * NumberField.mixedEmbedding.stdBasis F q')) (Sum.inl w)
      = NumberField.InfinitePlace.embedding_of_isReal w.2 α
          * (if q' = (Sum.inl w : NumberField.mixedEmbedding.index F) then 1 else 0) := by
  rw [NumberField.mixedEmbedding.stdBasis_apply_isReal]
  rw [show (NumberField.mixedEmbedding F α * NumberField.mixedEmbedding.stdBasis F q').1 w
      = (NumberField.mixedEmbedding F α).1 w * (NumberField.mixedEmbedding.stdBasis F q').1 w
      from by simp]
  rw [NumberField.mixedEmbedding.mixedEmbedding_apply_isReal]
  rw [← NumberField.mixedEmbedding.stdBasis_apply_isReal
        (NumberField.mixedEmbedding.stdBasis F q') w]
  congr 1
  exact sieg_stdBasis_repr_self_apply q' (Sum.inl w)

lemma sieg_complex_coord_fst {F : Type*} [Field F] [NumberField F] (α : F)
    (q' : NumberField.mixedEmbedding.index F) (w : {w : NumberField.InfinitePlace F // w.IsComplex}) :
    ((NumberField.mixedEmbedding.stdBasis F).repr
        (NumberField.mixedEmbedding F α * NumberField.mixedEmbedding.stdBasis F q'))
        (Sum.inr (w, 0))
      = Complex.re (w.1.embedding α) *
          (if q' = (Sum.inr (w, 0) : NumberField.mixedEmbedding.index F) then 1 else 0)
        - Complex.im (w.1.embedding α) *
          (if q' = (Sum.inr (w, 1) : NumberField.mixedEmbedding.index F) then 1 else 0) := by
  rw [NumberField.mixedEmbedding.stdBasis_apply_isComplex_fst]
  rw [show (NumberField.mixedEmbedding F α * NumberField.mixedEmbedding.stdBasis F q').2 w
      = (NumberField.mixedEmbedding F α).2 w * (NumberField.mixedEmbedding.stdBasis F q').2 w
      from by simp]
  rw [NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]
  rw [Complex.mul_re]
  rw [← NumberField.mixedEmbedding.stdBasis_apply_isComplex_fst
        (NumberField.mixedEmbedding.stdBasis F q') w]
  rw [← NumberField.mixedEmbedding.stdBasis_apply_isComplex_snd
        (NumberField.mixedEmbedding.stdBasis F q') w]
  rw [sieg_stdBasis_repr_self_apply q' (Sum.inr (w, 0)),
      sieg_stdBasis_repr_self_apply q' (Sum.inr (w, 1))]

lemma sieg_complex_coord_snd {F : Type*} [Field F] [NumberField F] (α : F)
    (q' : NumberField.mixedEmbedding.index F) (w : {w : NumberField.InfinitePlace F // w.IsComplex}) :
    ((NumberField.mixedEmbedding.stdBasis F).repr
        (NumberField.mixedEmbedding F α * NumberField.mixedEmbedding.stdBasis F q'))
        (Sum.inr (w, 1))
      = Complex.re (w.1.embedding α) *
          (if q' = (Sum.inr (w, 1) : NumberField.mixedEmbedding.index F) then 1 else 0)
        + Complex.im (w.1.embedding α) *
          (if q' = (Sum.inr (w, 0) : NumberField.mixedEmbedding.index F) then 1 else 0) := by
  rw [NumberField.mixedEmbedding.stdBasis_apply_isComplex_snd]
  rw [show (NumberField.mixedEmbedding F α * NumberField.mixedEmbedding.stdBasis F q').2 w
      = (NumberField.mixedEmbedding F α).2 w * (NumberField.mixedEmbedding.stdBasis F q').2 w
      from by simp]
  rw [NumberField.mixedEmbedding.mixedEmbedding_apply_isComplex]
  rw [Complex.mul_im]
  rw [← NumberField.mixedEmbedding.stdBasis_apply_isComplex_fst
        (NumberField.mixedEmbedding.stdBasis F q') w]
  rw [← NumberField.mixedEmbedding.stdBasis_apply_isComplex_snd
        (NumberField.mixedEmbedding.stdBasis F q') w]
  rw [sieg_stdBasis_repr_self_apply q' (Sum.inr (w, 0)),
      sieg_stdBasis_repr_self_apply q' (Sum.inr (w, 1))]

theorem sieg_block_row {F : Type*} [Field F] [NumberField F] (α : F)
    (q : NumberField.mixedEmbedding.index F) :
    ∑ q' : NumberField.mixedEmbedding.index F,
        ((NumberField.mixedEmbedding.stdBasis F).repr
          (NumberField.mixedEmbedding F α * NumberField.mixedEmbedding.stdBasis F q')) q ^ 2
      = ‖(siegPlaceOf (F := F) q).embedding α‖ ^ 2 := by
  classical
  rcases q with w | ⟨w, j⟩
  · rw [siegPlaceOf_inl, NumberField.InfinitePlace.norm_embedding_eq,
      ← NumberField.InfinitePlace.norm_embedding_of_isReal w.2 α, Real.norm_eq_abs, sq_abs]
    have h : ∀ q', ((NumberField.mixedEmbedding.stdBasis F).repr
        (NumberField.mixedEmbedding F α * NumberField.mixedEmbedding.stdBasis F q')) (Sum.inl w)
        = NumberField.InfinitePlace.embedding_of_isReal w.2 α
            * (if q' = (Sum.inl w : NumberField.mixedEmbedding.index F) then 1 else 0) :=
      fun q' => sieg_real_coord α q' w
    rw [Finset.sum_congr rfl (fun q' _ => by rw [h q'])]
    rw [Finset.sum_eq_single (Sum.inl w)]
    · simp
    · intro b _ hb; simp [hb]
    · intro hh; exact absurd (Finset.mem_univ (Sum.inl w)) hh
  · fin_cases j
    · show (∑ q' : NumberField.mixedEmbedding.index F,
          ((NumberField.mixedEmbedding.stdBasis F).repr
            (NumberField.mixedEmbedding F α * NumberField.mixedEmbedding.stdBasis F q'))
            (Sum.inr (w, (0 : Fin 2))) ^ 2)
        = ‖w.1.embedding α‖ ^ 2
      have h : ∀ q', ((NumberField.mixedEmbedding.stdBasis F).repr
          (NumberField.mixedEmbedding F α * NumberField.mixedEmbedding.stdBasis F q'))
            (Sum.inr (w, (0 : Fin 2)))
          = Complex.re (w.1.embedding α)
              * (if q' = (Sum.inr (w, 0) : NumberField.mixedEmbedding.index F) then 1 else 0)
            - Complex.im (w.1.embedding α)
              * (if q' = (Sum.inr (w, 1) : NumberField.mixedEmbedding.index F) then 1 else 0) :=
        fun q' => sieg_complex_coord_fst α q' w
      rw [Finset.sum_congr rfl (fun q' _ => by rw [h q'])]
      rw [Complex.sq_norm, Complex.normSq_apply]
      have hpt : ∀ q' : NumberField.mixedEmbedding.index F,
          (Complex.re (w.1.embedding α)
              * (if q' = (Sum.inr (w, 0) : NumberField.mixedEmbedding.index F) then 1 else 0)
            - Complex.im (w.1.embedding α)
              * (if q' = (Sum.inr (w, 1) : NumberField.mixedEmbedding.index F) then 1 else 0)) ^ 2
          = Complex.re (w.1.embedding α) ^ 2
              * (if q' = (Sum.inr (w, 0) : NumberField.mixedEmbedding.index F) then 1 else 0)
            + Complex.im (w.1.embedding α) ^ 2
              * (if q' = (Sum.inr (w, 1) : NumberField.mixedEmbedding.index F) then 1 else 0) := by
        intro q'
        by_cases h0 : q' = (Sum.inr (w, 0) : NumberField.mixedEmbedding.index F) <;>
          by_cases h1 : q' = (Sum.inr (w, 1) : NumberField.mixedEmbedding.index F) <;>
          simp_all <;> ring
      rw [Finset.sum_congr rfl (fun q' _ => hpt q'), Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      simp only [sq]
      simp
    · show (∑ q' : NumberField.mixedEmbedding.index F,
          ((NumberField.mixedEmbedding.stdBasis F).repr
            (NumberField.mixedEmbedding F α * NumberField.mixedEmbedding.stdBasis F q'))
            (Sum.inr (w, (1 : Fin 2))) ^ 2)
        = ‖w.1.embedding α‖ ^ 2
      have h : ∀ q', ((NumberField.mixedEmbedding.stdBasis F).repr
          (NumberField.mixedEmbedding F α * NumberField.mixedEmbedding.stdBasis F q'))
            (Sum.inr (w, (1 : Fin 2)))
          = Complex.re (w.1.embedding α)
              * (if q' = (Sum.inr (w, 1) : NumberField.mixedEmbedding.index F) then 1 else 0)
            + Complex.im (w.1.embedding α)
              * (if q' = (Sum.inr (w, 0) : NumberField.mixedEmbedding.index F) then 1 else 0) :=
        fun q' => sieg_complex_coord_snd α q' w
      rw [Finset.sum_congr rfl (fun q' _ => by rw [h q'])]
      rw [Complex.sq_norm, Complex.normSq_apply]
      have hpt : ∀ q' : NumberField.mixedEmbedding.index F,
          (Complex.re (w.1.embedding α)
              * (if q' = (Sum.inr (w, 1) : NumberField.mixedEmbedding.index F) then 1 else 0)
            + Complex.im (w.1.embedding α)
              * (if q' = (Sum.inr (w, 0) : NumberField.mixedEmbedding.index F) then 1 else 0)) ^ 2
          = Complex.re (w.1.embedding α) ^ 2
              * (if q' = (Sum.inr (w, 1) : NumberField.mixedEmbedding.index F) then 1 else 0)
            + Complex.im (w.1.embedding α) ^ 2
              * (if q' = (Sum.inr (w, 0) : NumberField.mixedEmbedding.index F) then 1 else 0) := by
        intro q'
        by_cases h0 : q' = (Sum.inr (w, 1) : NumberField.mixedEmbedding.index F) <;>
          by_cases h1 : q' = (Sum.inr (w, 0) : NumberField.mixedEmbedding.index F) <;>
          simp_all <;> ring
      rw [Finset.sum_congr rfl (fun q' _ => hpt q'), Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      simp only [sq]
      simp

end Work.BW
