import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.numaux.Defs
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.Lat.det_inv_compl_block
import Submission.Work.HP.DetLOrth.Defs
import Submission.Work.HP.DetLOrth.exists_adapted_basis

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.HP

open Work.HP.DetLOrth

/-! ## Auxiliary lemmas

The proof of `detgam_orthLat_detL` goes through a basis `b` of `ℤ^ι` adapted to `K`: the
saturated lattice `K` is spanned by the subfamily `{b i : p i}` (`DetLOrth.exists_adapted_basis`).
Writing `M = gramR b` for the Gram matrix of `b`, the three lemmas below identify the two
determinants with the square roots of the determinants of complementary principal blocks of `M`
and of `M⁻¹`.  Jacobi's identity (`Work.HP.Lat.det_inv_compl_block`) then gives the result, since
`det M = 1`.
-/

/-- For `K = span {b i : i ∈ p}` and a `ℤ`-basis `b` of `ℤ^ι`: `detL K` is the square root of the
determinant of the principal Gram block of `b` on `p`. -/
lemma detgam_detL_eq_sqrt_block {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ (ι → ℤ)) (p : ι → Prop) [DecidablePred p] (K : Submodule ℤ (ι → ℤ))
    (h : K = Submodule.span ℤ (Set.range fun i : {i // p i} => (b i.1 : ι → ℤ))) :
    detL K = Real.sqrt ((gramR b).toSquareBlockProp p).det := by
  let v : {i // p i} → (ι → ℤ) := fun i => (b i.1 : ι → ℤ)
  have h' : K = Submodule.span ℤ (Set.range v) := h
  have hli : LinearIndependent ℤ v :=
    b.linearIndependent.comp (fun i : {i // p i} => i.1) (fun _ _ hh => Subtype.ext hh)
  rw [h']
  rw [Lat.detL_basis_gram _ (Module.Basis.span hli)]
  congr 1
  congr 1
  ext i j
  simp [Matrix.toSquareBlockProp, Matrix.toBlock, v, gramR_apply]

/-- For `K = span {b i : i ∈ p}` and a `ℤ`-basis `b` of `ℤ^ι`: `orthLat K` is spanned by the dual
basis vectors indexed by the complement of `p`. -/
lemma detgam_orthLat_eq_span_dualVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ (ι → ℤ)) (p : ι → Prop) [DecidablePred p] (K : Submodule ℤ (ι → ℤ))
    (h : K = Submodule.span ℤ (Set.range fun i : {i // p i} => (b i.1 : ι → ℤ))) :
    orthLat K = Submodule.span ℤ (Set.range fun i : {i // ¬ p i} => dualVec b i.1) := by
  refine le_antisymm ?_ ?_
  · intro y hy
    have hcoef : ∀ i : {i // p i}, (∑ x, y x * (b i.1) x) = 0 := by
      intro i
      have hmem : (b i.1 : ι → ℤ) ∈ K := by
        rw [h]
        exact Submodule.subset_span ⟨i, rfl⟩
      exact mem_orthLat.mp hy _ hmem
    rw [← sum_dualVec_smul b y]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i => p i)
      (fun i => (∑ x, y x * (b i) x) • dualVec b i)]
    have hzero : (∑ i : {i // p i}, (∑ x, y x * (b ↑i) x) • dualVec b ↑i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [hcoef i, zero_smul]
    rw [hzero, zero_add]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro y ⟨i, rfl⟩
    show dualVec b i.1 ∈ orthLat K
    rw [mem_orthLat]
    intro x hx
    rw [h] at hx
    refine Submodule.span_induction (fun z hz => ?_) ?_ (fun u v _ _ hu hv => ?_)
      (fun c u _ hu => ?_) hx
    · obtain ⟨j, rfl⟩ := hz
      show (∑ k, dualVec b i.1 k * (b j.1) k) = 0
      rw [dualVec_pairing]
      split_ifs with hh
      · exact absurd hh fun hh' => i.2 (hh' ▸ j.2)
      · rfl
    · exact Finset.sum_eq_zero fun k _ => mul_zero _
    · rw [dotI_add_right, hu, hv, add_zero]
    · rw [dotI_smul_right, hu, mul_zero]

/-- For `K = span {b i : i ∈ p}` and a `ℤ`-basis `b` of `ℤ^ι`: `detL (orthLat K)` is the square
root of the determinant of the block of `(gramR b)⁻¹` complementary to `p`. -/
lemma detgam_detL_orthLat_eq_sqrt_inv_block {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℤ (ι → ℤ)) (p : ι → Prop) [DecidablePred p] (K : Submodule ℤ (ι → ℤ))
    (h : K = Submodule.span ℤ (Set.range fun i : {i // p i} => (b i.1 : ι → ℤ))) :
    detL (orthLat K) = Real.sqrt (((gramR b)⁻¹).toSquareBlockProp (fun i => ¬ p i)).det := by
  let w : {i // ¬ p i} → (ι → ℤ) := fun i => dualVec b i.1
  have h' : orthLat K = Submodule.span ℤ (Set.range w) :=
    detgam_orthLat_eq_span_dualVec b p K h
  have hli : LinearIndependent ℤ w :=
    (dualVec_linearIndependent b).comp (fun i : {i // ¬ p i} => i.1)
      (fun _ _ hh => Subtype.ext hh)
  rw [h']
  rw [Lat.detL_basis_gram _ (Module.Basis.span hli)]
  congr 1
  congr 1
  ext i j
  simp [Matrix.toSquareBlockProp, Matrix.toBlock, w, gramR_inv_apply]

/-- Reciprocal-covolume / duality for a saturated lattice: the lattice of integer vectors
orthogonal to a saturated (primitive, pure) sublattice `K ⊆ ℤ^ι` has the same determinant
(covolume in its real span) as `K` itself.

HINT (a concrete route).  `IsPrimLat K` is `PairsAux.IsPrimLat` (`m • v ∈ K`, `m ≠ 0` ⟹ `v ∈ K`).
Use `Submodule.smithNormalForm (Pi.basisFun ℤ ι) K`, which yields a ℤ-basis `bM` of `ℤ^ι`,
a ℤ-basis `bN` of `K`, an embedding `f : Fin n ↪ ι` and `a : Fin n → ℤ` with
`(bN i : ι → ℤ) = a i • bM (f i)`.  Saturation forces each `a i` to be a unit (`bM (f i) ∈ K`
because `a i • bM (f i) ∈ K`; writing `bM (f i) = ∑ c_j bN j` gives `c i * a i = 1`).  Replace
`bM` by `bM.unitsSMul u` with `u (f i) = a i`, `u j = 1` otherwise, so that `bM (f i) = bN i`.
Then `K = Submodule.span ℤ {bM j | j ∈ Set.range f}`.

Now let `p : ι → Prop := fun j => j ∈ Set.range f` and `M : Matrix ι ι ℝ` the Gram matrix
`M i j = ∑ x, ((bM i) x : ℝ) * ((bM j) x : ℝ)`.  Show `M.det = 1` (both bases of `ℤ^ι` have
Gram determinant `detL ⊤ ^ 2 = 1`, using `Lat.detL_basis_gram` for the standard basis
`Pi.basisFun ℤ ι`, and `Real.sq_sqrt`).  Then `(M.toSquareBlockProp p).det = detL K ^ 2`
(`Lat.detL_basis_gram` with the basis `bN`, transporting `det` along `Fin n ≃ {j // p j}` by
`Matrix.det_submatrix_equiv_self`), and Jacobi (`Lat.det_inv_compl_block`, already proved)
gives `((M⁻¹).toSquareBlockProp (fun j => ¬ p j)).det = (M.toSquareBlockProp p).det / M.det`.
Finally the dual basis `b*ᵢ = ∑ j (adjugate M) i j • bM j` satisfies `⟨b*ᵢ, bM j⟩ = δᵢⱼ`
(because `adjugate M * M = M.det • 1 = 1`), is a `ℤ`-basis of `ℤ^ι`, spans `orthLat K`
precisely, and has Gram matrix `M⁻¹`; hence `detL (orthLat K) ^ 2 = (M⁻¹).toSquareBlockProp (¬p)).det`.
Compare the two squared identities and take square roots (`detL` is nonnegative). -/
theorem detgam_orthLat_detL {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Submodule ℤ (ι → ℤ)) (hK : IsPrimLat K) :
    detL (orthLat K) = detL K := by
  obtain ⟨b, p, hspan⟩ := DetLOrth.exists_adapted_basis K hK
  haveI : DecidablePred p := fun a => Classical.propDecidable (p a)
  have hKdet := detgam_detL_eq_sqrt_block b p K hspan
  have hOdet := detgam_detL_orthLat_eq_sqrt_inv_block b p K hspan
  have hM : (gramR b).det = 1 := gramR_det b
  have hA : ((gramR b).toSquareBlockProp p).det ≠ 0 := gramR_block_det_ne_zero b p
  have hjac : (((gramR b)⁻¹).toSquareBlockProp (fun i => ¬ p i)).det
      = ((gramR b).toSquareBlockProp p).det := by
    rw [Lat.det_inv_compl_block (gramR b) (by rw [hM]; norm_num) p hA, hM, div_one]
  rw [hOdet, hKdet, hjac]

end Work.HP
