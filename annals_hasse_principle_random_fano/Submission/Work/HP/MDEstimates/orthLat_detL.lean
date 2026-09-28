import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.DetLOrth.Defs
import Submission.Work.HP.DetLOrth.exists_adapted_basis
import Submission.Work.HP.Lat.det_inv_compl_block
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.HPgram

/-!
# `detL (orthLat K) = detL K` for a saturated lattice `K ⊆ ℤ^ι`

The integer-orthogonal complement of a saturated (primitive) sublattice `K ⊆ ℤ^ι` has the same
covolume (determinant in its own real span) as `K` itself.

The proof picks a `ℤ`-basis `b` of `ℤ^ι` adapted to `K` (`DetLOrth.exists_adapted_basis`), so that
`K = span {b i : p i}` for some predicate `p`.  With `M = gramR b` the real Gram matrix of `b`
(whose determinant is `1`, `DetLOrth.gramR_det`):

* the dual basis `b*` of `b` satisfies `orthLat K = span {b* i : ¬ p i}`
  (`orthLat_eq_span_dualVec`);
* `detL` of the span of an independent family is the square root of the Gram determinant of the
  family (`detL_span_gram'`), so `detL K = √(det M[p,p])`
  (`detL_eq_sqrt_gramR_block`) and `detL (orthLat K) = √(det (M⁻¹)[¬p,¬p])`
  (`detL_span_dualVec_eq_inv_block`, using `DetLOrth.gramR_inv_apply`);
* Jacobi's complementary-minor identity (`Lat.det_inv_compl_block`), together with `det M = 1`,
  gives `det (M⁻¹)[¬p,¬p] = det M[p,p]`.
-/

set_option autoImplicit false

noncomputable section

open Matrix Real

namespace Work.HP.MDEstimates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `detL` of the `ℤ`-span of a `ℤ`-linearly independent family indexed by an arbitrary finite
type is the square root of the determinant of its Gram matrix (a generalisation of
`Lat.detL_span_gram` from `Fin k` to any finite index type). -/
theorem detL_span_gram' {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (f : κ → ι → ℤ) (hf : LinearIndependent ℤ f) :
    Work.HP.detL (Submodule.span ℤ (Set.range f)) =
      Real.sqrt (Matrix.det (Matrix.of fun i j : κ => ∑ a, (f i a : ℝ) * (f j a : ℝ))) := by
  rw [Work.HP.Lat.detL_basis_gram _ (Module.Basis.span hf)]
  simp only [Module.Basis.coe_span_apply]

/-- The integer-orthogonal complement of a coordinate sublattice of a `ℤ`-basis is spanned by the
complementary dual vectors. -/
theorem orthLat_eq_span_dualVec (b : Module.Basis ι ℤ (ι → ℤ)) (p : ι → Prop)
    (K : Submodule ℤ (ι → ℤ))
    (h : K = Submodule.span ℤ (Set.range fun i : {i // p i} => (b i.1 : ι → ℤ))) :
    Work.HP.orthLat K =
      Submodule.span ℤ (Set.range fun i : {i // ¬ p i} => Work.HP.DetLOrth.dualVec b i.1) := by
  classical
  rw [h]
  apply le_antisymm
  · intro y hy
    rw [Work.HP.mem_orthLat] at hy
    have hzero : ∀ i, p i → (∑ x, y x * b i x) = 0 := by
      intro i hi
      have hh := hy (b i) (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
      simpa only [Work.HP.dotI] using hh
    have hysum := Work.HP.DetLOrth.sum_dualVec_smul b y
    have hsplit : (∑ i, (∑ x, y x * b i x) • Work.HP.DetLOrth.dualVec b i)
        = ∑ i, if ¬ p i then (∑ x, y x * b i x) • Work.HP.DetLOrth.dualVec b i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hp : p i
      · simp [hp, hzero i hp]
      · simp [hp]
    rw [← hysum, hsplit, ← Finset.sum_filter]
    apply Submodule.sum_mem
    intro i hi
    rw [Finset.mem_filter] at hi
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi.2⟩, rfl⟩)
  · rw [Submodule.span_le]
    rintro x ⟨i, rfl⟩
    change Work.HP.DetLOrth.dualVec b i.1 ∈ Work.HP.orthLat
      (Submodule.span ℤ (Set.range fun j : {j // p j} => (b j.1 : ι → ℤ)))
    rw [Work.HP.mem_orthLat]
    intro w hw
    refine Submodule.span_induction
      (p := fun x (_ : x ∈ Submodule.span ℤ (Set.range fun j : {j // p j} => (b j.1 : ι → ℤ))) =>
        Work.HP.dotI (Work.HP.DetLOrth.dualVec b i.1) x = 0) ?_ ?_ ?_ ?_ hw
    · rintro y ⟨j, rfl⟩
      have hne : i.1 ≠ j := fun he => i.2 (he ▸ j.2)
      rw [Work.HP.dotI, Work.HP.DetLOrth.dualVec_pairing b i.1 j]
      simp [hne]
    · simp [Work.HP.dotI]
    · intro u v _ _ hu hv
      rw [Work.HP.dotI_add_right, hu, hv, add_zero]
    · intro c u _ hu
      rw [Work.HP.dotI_smul_right, hu, mul_zero]

/-- `detL` of a coordinate sublattice of a basis is the square root of the determinant of the
corresponding principal block of the Gram matrix. -/
theorem detL_eq_sqrt_gramR_block (b : Module.Basis ι ℤ (ι → ℤ)) (p : ι → Prop) [DecidablePred p]
    (K : Submodule ℤ (ι → ℤ))
    (h : K = Submodule.span ℤ (Set.range fun i : {i // p i} => (b i.1 : ι → ℤ))) :
    Work.HP.detL K = Real.sqrt ((Work.HP.DetLOrth.gramR b).toSquareBlockProp p).det := by
  rw [h]
  have hmat : (Matrix.of fun i j : {i // p i} => ∑ a, ((b i.1 : ι → ℤ) a : ℝ) *
        ((b j.1 : ι → ℤ) a : ℝ)) = (Work.HP.DetLOrth.gramR b).toSquareBlockProp p := by
    ext i j
    simp [Work.HP.DetLOrth.gramR, Matrix.toSquareBlockProp, Matrix.toBlock]
  rw [detL_span_gram' (fun i : {i // p i} => b i.1)
      ((b.linearIndependent).comp _ Subtype.coe_injective), hmat]

/-- `detL` of the span of the complementary dual vectors is the square root of the determinant of
the complementary principal block of the inverse Gram matrix. -/
theorem detL_span_dualVec_eq_inv_block (b : Module.Basis ι ℤ (ι → ℤ)) (p : ι → Prop)
    [DecidablePred p] :
    Work.HP.detL
        (Submodule.span ℤ (Set.range fun i : {i // ¬ p i} => Work.HP.DetLOrth.dualVec b i.1))
      = Real.sqrt (((Work.HP.DetLOrth.gramR b)⁻¹).toSquareBlockProp (fun i => ¬ p i)).det := by
  have hmat : (Matrix.of fun i j : {i // ¬ p i} => ∑ a, ((Work.HP.DetLOrth.dualVec b i.1) a : ℝ) *
        ((Work.HP.DetLOrth.dualVec b j.1) a : ℝ))
      = ((Work.HP.DetLOrth.gramR b)⁻¹).toSquareBlockProp (fun i => ¬ p i) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.toSquareBlockProp, Matrix.toBlock, Matrix.submatrix_apply]
    exact (Work.HP.DetLOrth.gramR_inv_apply b i.1 j.1).symm
  rw [detL_span_gram' (fun i : {i // ¬ p i} => Work.HP.DetLOrth.dualVec b i.1)
        ((Work.HP.DetLOrth.dualVec_linearIndependent b).comp _ Subtype.coe_injective), hmat]

/-- Reciprocal covolume / duality for a saturated lattice: the lattice of integer vectors orthogonal
to a saturated (primitive, pure) sublattice `K ⊆ ℤ^ι` has the same determinant (covolume in its
real span) as `K` itself. -/
theorem orthLat_detL {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Submodule ℤ (ι → ℤ)) (hK : Work.HP.IsPrimLat K) :
    Work.HP.detL (Work.HP.orthLat K) = Work.HP.detL K := by
  classical
  obtain ⟨b, p, hK'⟩ := Work.HP.DetLOrth.exists_adapted_basis K hK
  have horth := orthLat_eq_span_dualVec b p K hK'
  have hdetK := detL_eq_sqrt_gramR_block b p K hK'
  have hinv := detL_span_dualVec_eq_inv_block b p
  rw [horth, hinv, hdetK]
  have hM : (Work.HP.DetLOrth.gramR b).det ≠ 0 := by
    rw [Work.HP.DetLOrth.gramR_det b]; norm_num
  have hA : ((Work.HP.DetLOrth.gramR b).toSquareBlockProp p).det ≠ 0 :=
    Work.HP.DetLOrth.gramR_block_det_ne_zero b p
  rw [Work.HP.Lat.det_inv_compl_block (Work.HP.DetLOrth.gramR b) hM p hA,
    Work.HP.DetLOrth.gramR_det b, div_one]

end Work.HP.MDEstimates
