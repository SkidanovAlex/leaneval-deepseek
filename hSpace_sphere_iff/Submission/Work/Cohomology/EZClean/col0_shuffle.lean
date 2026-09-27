import Mathlib
import Submission.Work.Cohomology.EZShuffle
import Submission.Work.Cohomology.EZShuffleGen
import Submission.Work.Cohomology.EZG.EZShufSetup
import Submission.Work.Cohomology.Chains

namespace Work.Cohomology.EZClean

open CategoryTheory Simplicial Opposite

noncomputable section

variable {X Y : SSet.{0}}

/-- For `q = 0` the shuffle sum `ezChainB` degenerates to its unique summand: the shuffle set
`{A : Finset (Fin (n+0)) // A.card = n}` is a subsingleton, namely `{univ}`, with shuffle sign
`1`.  This is the single simplex of `X ⊗ Y` on which `ezChainB` is concentrated. -/
def col0_ezSing (n : ℕ) (X Y : SSet.{0}) (a : X.obj (op ⦋n⦌)) (b : Y.obj (op ⦋0⦌)) :
    (MonoidalCategoryStruct.tensorObj X Y).obj (op ⦋n⦌) :=
  (X.map (shA (Finset.univ : Finset (Fin n)) (by simp)).op a,
   Y.map (shB (n := n) (q := 0) (Finset.univ : Finset (Fin n)) (by simp)).op b)

/-- The `a`-count map of the full shuffle `univ : Finset (Fin n)` is the identity. -/
lemma col0_shA_univ_id (n : ℕ) (h : (Finset.univ : Finset (Fin n)).card ≤ n) :
    shA (Finset.univ : Finset (Fin n)) h = 𝟙 ⦋n⦌ := by
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext j
  apply Fin.ext
  rw [shA_apply_val]
  simp only [cnt]
  rw [show ((Finset.univ : Finset (Fin n)).filter (fun i => i.val < j.val)).card = j.val
      from card_filter_lt (n := n) (m := j.val) (Nat.lt_succ_iff.mp j.isLt)]
  rfl

/-- There is exactly one morphism `⦋m⦌ ⟶ ⦋0⦌`. -/
lemma col0_hom_zero_subsingleton (m : ℕ) : Subsingleton (⦋m⦌ ⟶ ⦋0⦌) :=
  ⟨fun f g => by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext j
    apply Fin.ext
    simp⟩

/-- For `q = 0` the Eilenberg–Zilber shuffle chain is a single simplex with coefficient `1`. -/
lemma col0_ezChainB_q0 (n : ℕ) (a : X.obj (op ⦋n⦌)) (b : Y.obj (op ⦋0⦌)) :
    ezChainB (p := n) (q := 0) a b = Finsupp.single (col0_ezSing n X Y a b) 1 := by
  rw [show ezChainB (p := n) (q := 0) a b
      = ∑ A : {A : Finset (Fin (n+0)) // A.card = n},
          (sgnA A.1 : ℚ) • Finsupp.single
            (X.map (shA A.1 (le_of_eq A.2)).op a,
             Y.map (shB (n := n+0) (q := 0) A.1 (by have := A.2; omega)).op b) (1 : ℚ) from rfl]
  rw [Fintype.sum_eq_single (⟨Finset.univ, by simp⟩ : {A : Finset (Fin (n+0)) // A.card = n})]
  · simp only [col0_ezSing]
    have hsgn : sgnA (Finset.univ : Finset (Fin (n+0))) = (1:ℤ) := by simp [sgnA, invA]
    simp only [hsgn, Int.cast_one, one_smul]
    congr 1
  · intro A hAne
    exact absurd (Subtype.ext (Finset.eq_univ_of_card A.1 (by rw [A.2]; simp))) hAne

/-- The faces of the single simplex of `ezChainB (p := ·) (q := 0)` are the single simplices of
the faces of `a`. -/
lemma col0_delta_ezSing (P : ℕ) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋0⦌))
    (i : Fin (P+2)) :
    (MonoidalCategoryStruct.tensorObj X Y).δ i (col0_ezSing (P+1) X Y a b)
      = col0_ezSing P X Y (X.δ i a) b := by
  rw [Work.Cohomology.EZG.delta_tensor]
  simp only [col0_ezSing]
  congr 1
  · rw [Work.Cohomology.EZG.delta_map]
    have hm : (SimplexCategory.δ i ≫ shA (Finset.univ : Finset (Fin (P+1))) (by simp))
        = (shA (Finset.univ : Finset (Fin P)) (by simp) ≫ SimplexCategory.δ i) := by
      rw [col0_shA_univ_id, col0_shA_univ_id, Category.comp_id, Category.id_comp]
    rw [hm, op_comp, Functor.map_comp]
    rfl
  · rw [Work.Cohomology.EZG.delta_map]
    have hm : (SimplexCategory.δ i ≫
          shB (n := P+1) (q := 0) (Finset.univ : Finset (Fin (P+1))) (by simp))
        = (shB (n := P) (q := 0) (Finset.univ : Finset (Fin P)) (by simp)) :=
      have := col0_hom_zero_subsingleton P
      Subsingleton.elim _ _
    rw [hm]

/-- The boundary of a chain concentrated on a single simplex with coefficient `1`. -/
lemma col0_sbdry_single_one (S : SSet.{0}) (n : ℕ) (σ : S.obj (op ⦋n+1⦌)) :
    Submission.Cohomology.sbdry S ℚ n (Finsupp.single σ 1)
      = ∑ k : Fin (n+2), Finsupp.single (S.δ k σ) ((-1 : ℚ) ^ (k : ℕ)) := by
  rw [Submission.Cohomology.sbdry_single]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  rw [zsmul_eq_mul, mul_one]
  push_cast
  ring

theorem col0_shuffle (P : ℕ) (X Y : SSet.{0})
    (a : X.obj (Opposite.op (SimplexCategory.mk (P+1))))
    (b : Y.obj (Opposite.op (SimplexCategory.mk 0))) :
    Submission.Cohomology.sbdry (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ P
        (Work.Cohomology.ezChainB (p := P+1) (q := 0) a b)
      = ∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) •
          Work.Cohomology.ezChainB (p := P) (q := 0) (X.δ i a) b := by
  rw [col0_ezChainB_q0]
  rw [col0_sbdry_single_one]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [col0_delta_ezSing, col0_ezChainB_q0, Finsupp.smul_single, smul_eq_mul, mul_one]

end

end Work.Cohomology.EZClean
