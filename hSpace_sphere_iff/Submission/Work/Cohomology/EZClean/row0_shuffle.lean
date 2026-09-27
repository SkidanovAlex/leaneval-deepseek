import Mathlib
import Submission.Work.Cohomology.EZShuffle
import Submission.Work.Cohomology.Chains

namespace Work.Cohomology.EZClean

open CategoryTheory Simplicial Opposite

noncomputable section

/-! ## The degenerate (row 0) Eilenberg–Zilber shuffle

For `p = 0` there is exactly one `(0,q)`-shuffle, namely `∅`, and the associated staircase
simplex of `a : X_0` and `b : Y_q` is the pair whose first component is `a` whiskered by the
unique map `⦋0+q⦌ ⟶ ⦋0⦌` and whose second component is `b` whiskered by the "identity"
`⦋0+q⦌ ⟶ ⦋q⦌`.  The shuffle lemma in this boundary case computes the boundary of `EZ(a ⊗ b)`
as the signed sum of the shuffle chains of the faces of `b`.
-/

theorem card_filter_lt (n m : ℕ) (hm : m ≤ n) :
    ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < m)).card = m := by
  rw [← Fintype.card_subtype (fun i : Fin n => i.val < m)]
  have e : {i : Fin n // i.val < m} ≃ Fin m :=
    { toFun := fun x => ⟨x.1.val, x.2⟩
      invFun := fun y => ⟨⟨y.1, lt_of_lt_of_le y.2 hm⟩, y.2⟩
      left_inv := fun x => by simp
      right_inv := fun y => by simp }
  rw [Fintype.card_congr e]
  exact Fintype.card_fin m

/-- The `b`-count of the empty shuffle is the identity: it counts all the elements below `j`. -/
theorem bCnt_empty {p q : ℕ} (j : Fin (p+q+1)) :
    Work.Cohomology.bCnt (∅ : Finset (Fin (p+q))) j = j.val := by
  rw [Work.Cohomology.bCnt, Finset.sdiff_empty]
  exact card_filter_lt (p + q) j.val (Nat.lt_succ_iff.mp j.isLt)

/-- The underlying order homomorphism of `shuffleMapB`. -/
theorem shuffleMapB_toOrderHom {p q : ℕ} (A : Finset (Fin (p+q))) (hA : A.card = p)
    (j : Fin (p+q+1)) :
    (Work.Cohomology.shuffleMapB A hA).toOrderHom j =
      ⟨Work.Cohomology.bCnt A j,
        Nat.lt_succ_of_le (Work.Cohomology.bCnt_le A hA j)⟩ := rfl

/-- The underlying order homomorphism of a face map of the simplex category. -/
theorem delta_toOrderHom {n : ℕ} (k : Fin (n+2)) :
    (SimplexCategory.δ k).toOrderHom = Fin.succAbove k := rfl

/-- The value of `Fin.succAbove`, as an explicit `if`. -/
theorem val_succAbove_aux {n : ℕ} (p : Fin (n+1)) (i : Fin n) :
    ((Fin.succAbove p i : Fin (n+1)) : ℕ) =
      if (i:ℕ) < (p:ℕ) then (i:ℕ) else (i:ℕ)+1 := by
  by_cases h : (i:ℕ) < (p:ℕ)
  · rw [Fin.succAbove_of_castSucc_lt p i
        (by simp only [Fin.lt_def, Fin.val_castSucc]; exact h), Fin.val_castSucc, if_pos h]
  · rw [Fin.succAbove_of_le_castSucc p i
        (by simp only [Fin.le_def, Fin.val_castSucc]; omega), Fin.val_succ, if_neg h]

/-- The faces of the `b`-shuffle map of the empty shuffle: taking the `i`-th face of
`⦋0+(Q+1)⦌ ⟶ ⦋Q+1⦌` and then the `b`-shuffle map of the empty shuffle is the same as taking the
`b`-shuffle map of the empty shuffle `⦋0+Q⦌ ⟶ ⦋Q⦌` and then the corresponding face. -/
theorem delta_shuffleMapB_empty (Q : ℕ) (i : Fin ((0+Q)+2)) :
    SimplexCategory.δ i ≫ Work.Cohomology.shuffleMapB (p := 0) (q := Q+1)
        (∅ : Finset (Fin (0+(Q+1)))) Finset.card_empty
      = Work.Cohomology.shuffleMapB (p := 0) (q := Q) (∅ : Finset (Fin (0+Q)))
          Finset.card_empty ≫
        SimplexCategory.δ (finCongr (by omega : (0+Q)+2 = Q+2) i) := by
  have hj : ((finCongr (by omega : (0+Q)+2 = Q+2) i : Fin (Q+2)) : ℕ) = (i : ℕ) := by simp
  ext m
  simp only [SimplexCategory.comp_toOrderHom, OrderHom.comp_coe, Function.comp_apply,
    delta_toOrderHom, shuffleMapB_toOrderHom, bCnt_empty]
  rw [val_succAbove_aux, val_succAbove_aux]
  rw [hj]

/-- The face of a simplex of the tensor product is the pair of the faces. -/
theorem delta_tensor (X Y : SSet.{0}) {n : ℕ} (k : Fin (n+2))
    (p : (MonoidalCategoryStruct.tensorObj X Y).obj (op ⦋n+1⦌)) :
    (MonoidalCategoryStruct.tensorObj X Y).δ k p = (X.δ k p.1, Y.δ k p.2) := by
  rw [SimplicialObject.δ, Monoidal.tensorObj_map]
  exact CategoryTheory.tensor_apply _ _ p

/-- A face of a whiskered simplex is the whiskering of the composite with the face map. -/
theorem delta_map (X : SSet.{0}) {m n : ℕ} (k : Fin (m+2)) (φ : ⦋m+1⦌ ⟶ ⦋n⦌)
    (x : X.obj (op ⦋n⦌)) :
    X.δ k (X.map φ.op x) = X.map (SimplexCategory.δ k ≫ φ).op x := by
  rw [SimplicialObject.δ, op_comp, Functor.map_comp]
  rfl

/-- Two successive applications of the structure maps of a simplicial set compose. -/
theorem map_map {X : SSet.{0}} {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c)
    (x : X.obj (op c)) : X.map f.op (X.map g.op x) = X.map (f ≫ g).op x := by
  rw [op_comp, X.map_comp]
  rfl

/-- The `i`-th face of the staircase simplex of the empty `(0,Q+1)`-shuffle is the staircase
simplex of the empty `(0,Q)`-shuffle of the corresponding face of `b`. -/
theorem delta_staircase_empty (Q : ℕ) (X Y : SSet.{0})
    (a : X.obj (op (SimplexCategory.mk 0)))
    (b : Y.obj (op (SimplexCategory.mk (Q+1)))) (i : Fin ((0+Q)+2)) :
    (MonoidalCategoryStruct.tensorObj X Y).δ i
        (Work.Cohomology.staircase (p := 0) (q := Q+1)
          (∅ : Finset (Fin (0+(Q+1)))) Finset.card_empty a b)
      = Work.Cohomology.staircase (p := 0) (q := Q) (∅ : Finset (Fin (0+Q)))
          Finset.card_empty a (Y.δ (finCongr (by omega : (0+Q)+2 = Q+2) i) b) := by
  have h := delta_tensor X Y i (Work.Cohomology.staircase (p := 0) (q := Q+1)
    (∅ : Finset (Fin (0+(Q+1)))) Finset.card_empty a b)
  rw [h]
  apply Prod.ext
  · show X.δ i (X.map (Work.Cohomology.shuffleMapA (p := 0) (q := Q+1)
          (∅ : Finset (Fin (0+(Q+1)))) Finset.card_empty).op a)
        = X.map (Work.Cohomology.shuffleMapA (p := 0) (q := Q)
          (∅ : Finset (Fin (0+Q))) Finset.card_empty).op a
    rw [delta_map]
    have hhom : SimplexCategory.δ i ≫ Work.Cohomology.shuffleMapA (p := 0) (q := Q+1)
          (∅ : Finset (Fin (0+(Q+1)))) Finset.card_empty
        = Work.Cohomology.shuffleMapA (p := 0) (q := Q) (∅ : Finset (Fin (0+Q)))
            Finset.card_empty :=
      Subsingleton.elim _ _
    rw [hhom]
  · show Y.δ i (Y.map (Work.Cohomology.shuffleMapB (p := 0) (q := Q+1)
          (∅ : Finset (Fin (0+(Q+1)))) Finset.card_empty).op b)
        = Y.map (Work.Cohomology.shuffleMapB (p := 0) (q := Q) (∅ : Finset (Fin (0+Q)))
            Finset.card_empty).op
            (Y.δ (finCongr (by omega : (0+Q)+2 = Q+2) i) b)
    rw [delta_map]
    rw [show Y.δ (finCongr (by omega : (0+Q)+2 = Q+2) i) b
          = Y.map (SimplexCategory.δ (finCongr (by omega : (0+Q)+2 = Q+2) i)).op b from rfl]
    rw [map_map, delta_shuffleMapB_empty]

/-- The shuffle chain of a `0`-simplex and a `q`-simplex is concentrated on the unique
`(0,q)`-shuffle. -/
theorem ezChainB_zero {X Y : SSet.{0}} (q : ℕ) (a : X.obj (op ⦋0⦌))
    (b : Y.obj (op ⦋q⦌)) :
    Work.Cohomology.ezChainB (p := 0) (q := q) a b =
      Finsupp.single (Work.Cohomology.staircase (p := 0) (q := q) (∅ : Finset (Fin (0+q)))
        Finset.card_empty a b) 1 := by
  rw [Work.Cohomology.ezChainB]
  have huniv : (Finset.univ : Finset {A : Finset (Fin (0+q)) // A.card = 0}) =
      {⟨∅, by simp⟩} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro A _
    exact Subtype.ext (Finset.card_eq_zero.mp A.2)
  rw [huniv, Finset.sum_singleton]
  simp only [Work.Cohomology.shuffleSign, Finset.sum_empty, pow_zero, Int.cast_one]
  rw [one_smul]

/-- The boundary of a chain concentrated on a single simplex with coefficient `1`. -/
theorem sbdry_single_one (S : SSet.{0}) (n : ℕ) (σ : S.obj (op ⦋n+1⦌)) :
    Submission.Cohomology.sbdry S ℚ n (Finsupp.single σ 1)
      = ∑ k : Fin (n+2), Finsupp.single (S.δ k σ) ((-1 : ℚ) ^ (k : ℕ)) := by
  rw [Submission.Cohomology.sbdry_single]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [zsmul_eq_mul, mul_one]
  push_cast
  ring

theorem row0_shuffle (Q : ℕ) (X Y : SSet.{0})
    (a : X.obj (Opposite.op (SimplexCategory.mk 0)))
    (b : Y.obj (Opposite.op (SimplexCategory.mk (Q+1)))) :
    Submission.Cohomology.sbdry (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ (0 + Q)
        (Work.Cohomology.ezChainB (p := 0) (q := Q+1) a b)
      = ∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) •
          Work.Cohomology.ezChainB (p := 0) (q := Q) a (Y.δ j b) := by
  rw [ezChainB_zero (q := Q+1) a b]
  rw [sbdry_single_one]
  have hR : (∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) •
        Work.Cohomology.ezChainB (p := 0) (q := Q) a (Y.δ j b))
      = ∑ j : Fin (Q+2), Finsupp.single (Work.Cohomology.staircase (p := 0) (q := Q)
          (∅ : Finset (Fin (0+Q))) Finset.card_empty a (Y.δ j b)) ((-1 : ℚ) ^ (j : ℕ)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ezChainB_zero (q := Q) a (Y.δ j b), Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hR]
  exact Fintype.sum_equiv (finCongr (by omega : (0+Q)+2 = Q+2)) _ _
    (fun i => by
      rw [delta_staircase_empty]
      rw [show ((finCongr (by omega : (0+Q)+2 = Q+2) i : Fin (Q+2)) : ℕ) = (i:ℕ) from by simp])

end

end Work.Cohomology.EZClean
