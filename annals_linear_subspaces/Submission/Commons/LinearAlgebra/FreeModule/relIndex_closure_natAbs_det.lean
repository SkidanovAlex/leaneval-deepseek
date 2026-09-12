import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.card_quotient_range_matrix

open scoped BigOperators

noncomputable section

namespace Commons.LinearAlgebra.FreeModule

open AddSubgroup

variable {G : Type*} [AddCommGroup G]

/-- The `i`-th standard basis vector of `(Fin r → ℤ)`. -/
private def unitVec (r : ℕ) (i : Fin r) : Fin r → ℤ := Pi.single i (1 : ℤ)

/-- The canonical `ℤ`-linear combination map from `Fin r → ℤ` to `G` with coefficients `m`. -/
private def linComb (r : ℕ) (m : Fin r → G) : (Fin r → ℤ) →ₗ[ℤ] G where
  toFun x := ∑ j, x j • m j
  map_add' x y := by
    simp [Finset.sum_add_distrib, add_smul, Pi.add_apply]
  map_smul' a x := by
    rw [Finset.smul_sum]
    simp [Pi.smul_apply, smul_smul]

private lemma linComb_injective {r : ℕ} {m : Fin r → G} (hm : LinearIndependent ℤ m) :
    Function.Injective (linComb r m) := by
  have hfun : ∀ g : Fin r → ℤ, (∑ i, g i • m i) = 0 → ∀ i, g i = 0 :=
    (Fintype.linearIndependent_iff.mp hm)
  have hfun' : ∀ g : Fin r → ℤ, (∑ i, g i • m i) = 0 → g = 0 := by
    intro g hg
    funext i
    simpa using hfun g hg i
  intro x y hxy
  have hxy0 : (linComb r m) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  have hxyeq : x - y = 0 := hfun' (x - y) hxy0
  ext i
  have : (x - y) i = 0 := congr_fun hxyeq i
  exact sub_eq_zero.mp (by simpa [Pi.sub_apply] using this)

private lemma linComb_unitVec_eq {r : ℕ} (m : Fin r → G) (i : Fin r) :
    (linComb r m) (unitVec r i) = m i := by
  change (∑ j : Fin r, (unitVec r i) j • m j) = m i
  have hs : (∑ j : Fin r, (unitVec r i) j • m j) =
      (∑ j : Fin r, (if j = i then m j else 0)) := by
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hji : j = i
    · simp [hji, unitVec]
    · simp [hji, unitVec, Pi.single_eq_of_ne]
  rw [hs]
  simp


/-- The dot product `w ⬝ᵥ x` as a `ℤ`-linear map in `x`. -/
private def dotMap (r : ℕ) (w : Fin r → ℤ) : (Fin r → ℤ) →ₗ[ℤ] ℤ where
  toFun x := w ⬝ᵥ x
  map_add' x y := by
    simp [dotProduct, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    change (∑ i : Fin r, w i * (a • x) i) = a • (∑ i : Fin r, w i * x i)
    simp [Pi.smul_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring

/-- `w ⬝ᵥ (Aᵀ y) = (A w) ⬝ᵥ y`. -/
private lemma dotMap_mulVecLin_transpose {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (w y : Fin r → ℤ) :
    dotMap r w (A.transpose.mulVecLin y) = (A.mulVec w) ⬝ᵥ y := by
  change w ⬝ᵥ (A.transpose.mulVec y) = (A.mulVec w) ⬝ᵥ y
  rw [Matrix.dotProduct_mulVec]
  rw [Matrix.vecMul_transpose]

/-- A vector in the kernel of `A` kills the range of `Aᵀ`. -/
private lemma range_mulVecLin_transpose_le_ker_dotMap {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (w : Fin r → ℤ) (hw : A.mulVec w = 0) :
    ((A.transpose.mulVecLin).range : Submodule ℤ (Fin r → ℤ)) ≤ (dotMap r w).ker := by
  intro x hx
  rw [LinearMap.mem_ker]
  rcases (LinearMap.mem_range.mp hx) with ⟨y, hy⟩
  rw [← hy, dotMap_mulVecLin_transpose, hw]
  simp

private lemma dotMap_unitVec {r : ℕ} (w : Fin r → ℤ) (j : Fin r) :
    dotMap r w (unitVec r j) = w j := by
  change w ⬝ᵥ (unitVec r j) = w j
  rw [unitVec, dotProduct_single, mul_one]

/-- If `det A = 0`, the cokernel of `Aᵀ` is infinite; its cardinality is `0`. -/
private lemma natCard_quotient_range_eq_zero_of_det_eq_zero {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (hA : A.det = 0) :
    Nat.card ((Fin r → ℤ) ⧸ ((A.transpose.mulVecLin).range : Submodule ℤ (Fin r → ℤ))) = 0 := by
  obtain ⟨w, hw0, hAw⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := A)).mpr hA
  have hne : ∃ j : Fin r, w j ≠ 0 := by
    by_contra h
    push Not at h
    apply hw0
    funext j
    exact h j
  classical
  rcases hne with ⟨j, hwj⟩
  let N : Submodule ℤ (Fin r → ℤ) := (A.transpose.mulVecLin).range
  have hNker : N ≤ (dotMap r w).ker := range_mulVecLin_transpose_le_ker_dotMap A w hAw
  let e : Fin r → ℤ := unitVec r j
  let f : ℤ → (Fin r → ℤ) ⧸ N := fun n => Submodule.Quotient.mk (n • e)
  have hf : Function.Injective f := by
    intro n n' h
    have hmem : (n - n') • e ∈ N := by
      have : (n • e) - (n' • e) = (n - n') • e := by
        simp [sub_smul]
      rw [← this]
      exact (Submodule.Quotient.eq N).mp h
    have hker : dotMap r w ((n - n') • e) = 0 := hNker hmem ▸ rfl
    have hcalc : (n - n') * w j = 0 := by
      have hlin : dotMap r w ((n - n') • e) = (n - n') • w j := by
        rw [map_smul, dotMap_unitVec]
      have hsmul : (n - n') • w j = (n - n') * w j := rfl
      simpa [hsmul] using hlin.symm.trans hker
    exact sub_eq_zero.mp (mul_eq_zero.mp hcalc |>.resolve_right hwj)
  have hInf : Infinite ((Fin r → ℤ) ⧸ N) := Infinite.of_injective f hf
  exact @Nat.card_eq_zero_of_infinite ((Fin r → ℤ) ⧸ N) hInf

private lemma linComb_mem_closure {r : ℕ} (m : Fin r → G) (x : Fin r → ℤ) :
    (linComb r m) x ∈ closure (Set.range m) := by
  change (∑ j : Fin r, x j • m j) ∈ closure (Set.range m)
  apply AddSubgroup.sum_mem
  intro j hj
  exact zsmul_mem (subset_closure (Set.mem_range_self j)) (x j)

/-- The image of the canonical map is exactly the closure of `range m`. -/
private lemma linComb_range_closure {r : ℕ} (m : Fin r → G) :
    (linComb r m).toAddMonoidHom.range = closure (Set.range m) := by
  apply le_antisymm
  · intro y hy
    rcases (AddMonoidHom.mem_range.mp hy) with ⟨x, hx⟩
    exact hx ▸ linComb_mem_closure m x
  · rw [closure_le]
    intro y hy
    rcases hy with ⟨i, rfl⟩
    exact AddMonoidHom.mem_range.mpr ⟨unitVec r i, linComb_unitVec_eq m i⟩


/-- `w = A • m` row-by-row: `w i` is the image of the `i`-th row of `A`. -/
private lemma w_eq_linComb_row {r : ℕ} (m w : Fin r → G) (A : Matrix (Fin r) (Fin r) ℤ)
    (hwA : ∀ i, w i = ∑ j, A i j • m j) (i : Fin r) :
    w i = (linComb r m) (A.row i) := by
  rw [hwA i]
  simp [linComb, Matrix.row_apply]

/-- The span of the rows of `A` equals the range of multiplication by `Aᵀ`. -/
private lemma span_row_eq_range_mulVecLin_transpose {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) :
    Submodule.span ℤ (Set.range (A.row : Fin r → (Fin r → ℤ))) =
      ((A.transpose.mulVecLin).range : Submodule ℤ (Fin r → ℤ)) := by
  rw [Matrix.range_mulVecLin]
  congr 1

/-- The closure of the rows of `A` is the additive subgroup of the range of `Aᵀ`. -/
private lemma closure_row_eq_toAddSubgroup {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) :
    AddSubgroup.closure (Set.range (A.row : Fin r → (Fin r → ℤ))) =
      ((A.transpose.mulVecLin).range : Submodule ℤ (Fin r → ℤ)).toAddSubgroup := by
  calc
    AddSubgroup.closure (Set.range (A.row : Fin r → (Fin r → ℤ))) =
        (AddSubgroup.toIntSubmodule
          (AddSubgroup.closure (Set.range (A.row : Fin r → (Fin r → ℤ))))).toAddSubgroup := by
          rw [AddSubgroup.toIntSubmodule_toAddSubgroup]
    _ = (Submodule.span ℤ (Set.range (A.row : Fin r → (Fin r → ℤ)))).toAddSubgroup := by
          rw [AddSubgroup.toIntSubmodule_closure]
    _ = ((A.transpose.mulVecLin).range : Submodule ℤ (Fin r → ℤ)).toAddSubgroup := by
          congr 1
          exact span_row_eq_range_mulVecLin_transpose A

/-- The closure of the image of the rows is the image of the closure of the rows. -/
private lemma closure_range_w_eq_map_closure_row {r : ℕ} (m w : Fin r → G)
    (A : Matrix (Fin r) (Fin r) ℤ) (hwA : ∀ i, w i = ∑ j, A i j • m j) :
    AddSubgroup.closure (Set.range w) =
      AddSubgroup.map (linComb r m).toAddMonoidHom
        (AddSubgroup.closure (Set.range (A.row : Fin r → (Fin r → ℤ)))) := by
  calc
    AddSubgroup.closure (Set.range w) =
        AddSubgroup.closure (Set.range (fun i => (linComb r m) (A.row i))) := by
          apply congrArg AddSubgroup.closure
          apply congrArg Set.range
          funext i
          exact w_eq_linComb_row m w A hwA i
    _ = AddSubgroup.closure (((linComb r m).toAddMonoidHom) ''
          Set.range (A.row : Fin r → (Fin r → ℤ))) := by
          change AddSubgroup.closure
            (Set.range (((linComb r m).toAddMonoidHom) ∘ (A.row : Fin r → (Fin r → ℤ)))) =
            AddSubgroup.closure (((linComb r m).toAddMonoidHom) ''
              Set.range (A.row : Fin r → (Fin r → ℤ)))
          rw [Set.range_comp]
    _ = AddSubgroup.map (linComb r m).toAddMonoidHom
          (AddSubgroup.closure (Set.range (A.row : Fin r → (Fin r → ℤ)))) := by
          rw [AddMonoidHom.map_closure]

/-- The preimage of the closure of the image of the rows is the closure of the rows. -/
private lemma comap_closure_range_w {r : ℕ} (m w : Fin r → G) (hm : LinearIndependent ℤ m)
    (A : Matrix (Fin r) (Fin r) ℤ) (hwA : ∀ i, w i = ∑ j, A i j • m j) :
    AddSubgroup.comap (linComb r m).toAddMonoidHom (AddSubgroup.closure (Set.range w)) =
      AddSubgroup.closure (Set.range (A.row : Fin r → (Fin r → ℤ))) := by
  ext x
  constructor
  · intro hx
    rw [AddSubgroup.mem_comap] at hx
    rw [closure_range_w_eq_map_closure_row m w A hwA] at hx
    rw [AddSubgroup.mem_map] at hx
    rcases hx with ⟨z, hz, hz'⟩
    have hxz : x = z := linComb_injective hm (by simpa using hz'.symm)
    rw [hxz]
    exact hz
  · intro hx
    rw [AddSubgroup.mem_comap]
    rw [closure_range_w_eq_map_closure_row m w A hwA]
    rw [AddSubgroup.mem_map]
    exact ⟨x, hx, rfl⟩

/-- Relative index of closures of images = index of preimage subgroup in `(Fin r → ℤ)`. -/
private lemma relIndex_eq_index_comap {r : ℕ} (m w : Fin r → G) :
    (AddSubgroup.closure (Set.range w)).relIndex (AddSubgroup.closure (Set.range m)) =
      (AddSubgroup.comap (linComb r m).toAddMonoidHom (AddSubgroup.closure (Set.range w))).index := by
  calc
    (AddSubgroup.closure (Set.range w)).relIndex (AddSubgroup.closure (Set.range m)) =
        (AddSubgroup.closure (Set.range w)).relIndex (linComb r m).toAddMonoidHom.range := by
          congr 1
          rw [linComb_range_closure m]
    _ = (AddSubgroup.closure (Set.range w)).relIndex
          (AddSubgroup.map (linComb r m).toAddMonoidHom (⊤ : AddSubgroup (Fin r → ℤ))) := by
          congr 1
          ext z
          simp
    _ = (AddSubgroup.comap (linComb r m).toAddMonoidHom (AddSubgroup.closure (Set.range w))).relIndex
          (⊤ : AddSubgroup (Fin r → ℤ)) := by
          exact (AddSubgroup.relIndex_comap (AddSubgroup.closure (Set.range w))
            (linComb r m).toAddMonoidHom (⊤ : AddSubgroup (Fin r → ℤ))).symm
    _ = (AddSubgroup.comap (linComb r m).toAddMonoidHom (AddSubgroup.closure (Set.range w))).index := by
          rw [AddSubgroup.relIndex_top_right]


/-- The index of the lattice spanned by the rows of `A` (inside `ℤ^r`) is `|det A|`:
the relative index of the subgroup closures is the absolute determinant. -/
theorem relIndex_closure_natAbs_det {G : Type*} [AddCommGroup G] {r : ℕ}
    (m : Fin r → G) (hm : LinearIndependent ℤ m) (A : Matrix (Fin r) (Fin r) ℤ)
    (w : Fin r → G) (hwA : ∀ i : Fin r, w i = ∑ j : Fin r, A i j • m j) :
    (AddSubgroup.closure (Set.range w)).relIndex (AddSubgroup.closure (Set.range m)) =
      A.det.natAbs := by
  have h2 : AddSubgroup.comap (linComb r m).toAddMonoidHom (AddSubgroup.closure (Set.range w)) =
      ((A.transpose.mulVecLin).range : Submodule ℤ (Fin r → ℤ)).toAddSubgroup := by
    rw [comap_closure_range_w m w hm A hwA, closure_row_eq_toAddSubgroup A]
  calc
    (AddSubgroup.closure (Set.range w)).relIndex (AddSubgroup.closure (Set.range m)) =
        (AddSubgroup.comap (linComb r m).toAddMonoidHom (AddSubgroup.closure (Set.range w))).index :=
          relIndex_eq_index_comap m w
    _ = ((A.transpose.mulVecLin).range : Submodule ℤ (Fin r → ℤ)).toAddSubgroup.index := by
          rw [h2]
    _ = Nat.card ((Fin r → ℤ) ⧸ ((A.transpose.mulVecLin).range : Submodule ℤ (Fin r → ℤ))) := by
          rw [AddSubgroup.index_eq_card]
          rfl
    _ = A.det.natAbs := by
          by_cases hA0 : A.det = 0
          · rw [natCard_quotient_range_eq_zero_of_det_eq_zero A hA0]
            exact (Int.natAbs_eq_zero.mpr hA0).symm
          · have hAt : A.transpose.det ≠ 0 := by simpa [Matrix.det_transpose] using hA0
            have hc := Commons.LinearAlgebra.Matrix.card_quotient_range_matrix (M := A.transpose) hAt
            rw [Matrix.det_transpose] at hc
            exact hc

end Commons.LinearAlgebra.FreeModule
