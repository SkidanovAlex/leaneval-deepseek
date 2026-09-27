/-
# Setup for the Eilenberg–Zilber shuffle lemma (general degrees)

Shared definitions for `ezChainB_sbdry_gen`: the index set "shuffle together with face index",
the `a`-side and `b`-side predicates, the reindexing maps to the index sets of `ezA` and `ezB`,
and the "shift up"/"insert" operations on shuffles.
-/
import Mathlib
import Submission.Work.Cohomology.EZAssembly
import Submission.Work.Cohomology.EZClassify
import Submission.Work.Cohomology.EZG.faceA_zero
import Submission.Work.Cohomology.EZG.faceA_last
import Submission.Work.Cohomology.EZG.faceB_zero
import Submission.Work.Cohomology.EZG.faceB_last
import Submission.Work.Cohomology.EZG.faceA_zero_g
import Submission.Work.Cohomology.EZG.faceA_last_g
import Submission.Work.Cohomology.EZG.faceB_zero_g
import Submission.Work.Cohomology.EZG.faceB_last_g
import Submission.Work.Cohomology.EZG.sgnA_delPos_succ
import Submission.Work.Cohomology.EZG.sgnA_delPos_succ_B
import Submission.Work.Cohomology.EZG.sgnA_delPos_zero
import Submission.Work.Cohomology.EZG.sgnA_delPos_last
import Submission.Work.Cohomology.EZG.sgnA_swap
import Submission.Work.Cohomology.EZG.cnt_cands_lt

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology.EZG

noncomputable section

variable {X Y : SSet.{0}}

/-! ### Shifting a shuffle up at a missing position -/

/-- `shUp A p` is `A` shifted up at `p` (`p ∉ shUp A p`): the image of `A` under `Fin.succAbove p`.
It is `insUp A p` with `p` removed. -/
def shUp {N : ℕ} (A : Finset (Fin N)) (p : Fin (N+1)) : Finset (Fin (N+1)) :=
  A.image (Fin.succAbove p)

lemma mem_shUp {N : ℕ} {A : Finset (Fin N)} {p : Fin (N+1)} {t : Fin (N+1)} :
    t ∈ shUp A p ↔ ∃ t' ∈ A, Fin.succAbove p t' = t := by
  simp [shUp]

lemma shUp_card {N : ℕ} (A : Finset (Fin N)) (p : Fin (N+1)) : (shUp A p).card = A.card :=
  Finset.card_image_of_injective _ Fin.succAbove_right_injective

lemma delPosP_shUp {N : ℕ} (A : Finset (Fin N)) (p : Fin (N+1)) : delPosP (shUp A p) p = A := by
  ext t
  rw [mem_delPosP, mem_shUp]
  constructor
  · rintro ⟨t', ht', h⟩
    rwa [Fin.succAbove_right_injective h] at ht'
  · intro ht
    exact ⟨t, ht, rfl⟩

lemma notMem_shUp {N : ℕ} (A : Finset (Fin N)) (p : Fin (N+1)) : p ∉ shUp A p := by
  rw [mem_shUp]
  rintro ⟨t, _, ht⟩
  exact Fin.succAbove_ne p t ht


lemma card_univ_sdiff_fin {N : ℕ} (A : Finset (Fin N)) :
    (Finset.univ \ A).card = N - A.card := by
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ A), Finset.card_univ, Fintype.card_fin]

lemma insUp_eq_shUp {N : ℕ} (A : Finset (Fin N)) (p : Fin (N+1)) :
    insUp A p = shUp A p ∪ {p} := rfl

/-! ### The index sets -/

/-- The index set of the expanded boundary of `ezChainB`: a shuffle `A` of `(P+1, Q+1)`-type
together with a face index `k`. -/
abbrev Idx (P Q : ℕ) : Type :=
  {A : Finset (Fin ((P+1)+(Q+1))) // A.card = P+1} × Fin ((P+1)+Q+2)

/-- The `a`-side predicate: the deleted letter is an `a`-letter, and it is either the first letter
or preceded by an `a`-letter. -/
def IsA (N : ℕ) (A : Finset (Fin (N+1))) (k : Fin (N+2)) : Prop :=
  delIdx k ∈ A ∧ (k.val = 0 ∨ k.val = N+1 ∨ (⟨k.val-1, by omega⟩ : Fin (N+1)) ∈ A)

/-- The `b`-side predicate: the deleted letter is a `b`-letter, and it is either the first letter
or preceded by a `b`-letter. -/
def IsB (N : ℕ) (A : Finset (Fin (N+1))) (k : Fin (N+2)) : Prop :=
  delIdx k ∉ A ∧ (k.val = 0 ∨ k.val = N+1 ∨ (⟨k.val-1, by omega⟩ : Fin (N+1)) ∉ A)

/-- The `a`-side of the index set. -/
abbrev IdxA (P Q : ℕ) : Type := {x : Idx P Q // IsA ((P+1)+Q) x.1.1 x.2}

/-- The `b`-side of the index set. -/
abbrev IdxB (P Q : ℕ) : Type := {x : Idx P Q // IsB ((P+1)+Q) x.1.1 x.2}

/-- The index set of `ezA`: a shuffle `A'` of `(P, Q+1)`-type (`A'.card = P`) and an index
`i : Fin (P+2)`. -/
abbrev TargetA (P Q : ℕ) : Type :=
  {A' : Finset (Fin ((P+1)+Q)) // A'.card = P} × Fin (P+2)

/-- The index set of `ezB`: a shuffle `A''` of `(P+1, Q)`-type (`A''.card = P+1`) and an index
`j : Fin (Q+2)`. -/
abbrev TargetB (P Q : ℕ) : Type :=
  {A'' : Finset (Fin ((P+1)+Q)) // A''.card = P+1} × Fin (Q+2)

/-- The `ℚ`-chains on the product `X_n × Y_n`, spelled with the product rather than the monoidal
object so that `Finsupp.single` of a pair lands in the right type.  It is definitionally equal to
`SChain (X ⊗ Y) ℚ n`. -/
abbrev ProdChain (X Y : SSet.{0}) (n : ℕ) : Type := (X.obj (op ⦋n⦌) × Y.obj (op ⦋n⦌)) →₀ ℚ

/-- Distributing a scalar over a sum (via `LinearMap.id`), polymorphically in the module. -/
lemma smul_sum_gen {M : Type*} [AddCommMonoid M] [Module ℚ M] {ι : Type*} [Fintype ι]
    (c : ℚ) (f : ι → M) : c • (∑ i, f i) = ∑ i, c • f i := by
  have h := map_sum (c • (LinearMap.id : M →ₗ[ℚ] M)) f Finset.univ
  simpa only [LinearMap.smul_apply, LinearMap.id_apply] using h

/-- The "mixed" predicate: neither an `a`-side nor a `b`-side index. -/
def IsD (N : ℕ) (A : Finset (Fin (N+1))) (k : Fin (N+2)) : Prop := ¬ IsA N A k ∧ ¬ IsB N A k

/-- The `a`-side indices of the expanded boundary. -/
def sA (P Q : ℕ) : Finset (Idx P Q) := by
  classical
  exact Finset.univ.filter fun x => IsA ((P+1)+Q) x.1.1 x.2

/-- The `b`-side indices of the expanded boundary. -/
def sB (P Q : ℕ) : Finset (Idx P Q) := by
  classical
  exact Finset.univ.filter fun x => IsB ((P+1)+Q) x.1.1 x.2

/-- The "mixed" indices of the expanded boundary. -/
def sD (P Q : ℕ) : Finset (Idx P Q) := by
  classical
  exact Finset.univ.filter fun x => IsD ((P+1)+Q) x.1.1 x.2

@[simp] lemma mem_sA {P Q : ℕ} {x : Idx P Q} :
    x ∈ sA P Q ↔ IsA ((P+1)+Q) x.1.1 x.2 := by
  simp [sA]

@[simp] lemma mem_sB {P Q : ℕ} {x : Idx P Q} :
    x ∈ sB P Q ↔ IsB ((P+1)+Q) x.1.1 x.2 := by
  simp [sB]

@[simp] lemma mem_sD {P Q : ℕ} {x : Idx P Q} :
    x ∈ sD P Q ↔ IsD ((P+1)+Q) x.1.1 x.2 := by
  simp [sD]

/-- Interchanging the membership of the two adjacent positions `q`, `q+1`. -/
def swapA (N : ℕ) (A : Finset (Fin (N+1))) (q : Fin N) : Finset (Fin (N+1)) :=
  if q.castSucc ∈ A then insert q.succ (A.erase q.castSucc)
  else insert q.castSucc (A.erase q.succ)

/-! ### The staircase simplex and the summand -/

/-- The staircase simplex of the shuffle `A` (`A.card = P+1`) applied to `a` and `b`, written with
the `cnt`-based shuffle maps `shA`, `shB`. -/
def ezPair (P Q : ℕ) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌))
    (A : Finset (Fin ((P+1)+(Q+1)))) (hA : A.card = P+1) :
    (MonoidalCategoryStruct.tensorObj X Y).obj (op ⦋(P+1)+(Q+1)⦌) :=
  (X.map (shA A (le_of_eq hA)).op a, Y.map (shB A (by have := hA; omega)).op b)

/-- The summand of the expanded boundary at the index `x = (A,k)`. -/
def Fsum (P Q : ℕ) (X Y : SSet.{0}) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌))
    (x : Idx P Q) : ProdChain X Y ((P+1)+Q) :=
  Finsupp.single (X.δ x.2 (ezPair P Q a b x.1.1 x.1.2).1,
                  Y.δ x.2 (ezPair P Q a b x.1.1 x.1.2).2)
    ((sgnA x.1.1 : ℚ) * (-1 : ℚ) ^ (x.2 : ℕ))

/-! ### The `a`-side reindexing map and its inverse -/

/-- The `a`-side reindexing: `(A,k) ↦ (delPosP A (delIdx k), cnt A k.val)`. -/
def aFwd (P Q : ℕ) (x : IdxA P Q) : TargetA P Q :=
  (⟨delPosP x.1.1.1 (delIdx x.1.2), by
      rw [delPosP_card x.2.1]; have := x.1.1.2; omega⟩,
   ⟨cnt x.1.1.1 x.1.2.val, by have := cnt_le_card x.1.1.1 x.1.2.val; have := x.1.1.2; omega⟩)

/-- The inverse of `aFwd`: insert an `a`-letter at the position determined by `i`. -/
def aInvIdx (P Q : ℕ) (y : TargetA P Q) : Idx P Q :=
  if h0 : y.2.val = 0 then
    (⟨insUp y.1.1 (0 : Fin ((P+1)+Q+1)), by rw [insUp_card]; have := y.1.2; omega⟩,
     (0 : Fin ((P+1)+Q+2)))
  else if hl : y.2.val = P+1 then
    (⟨insUp y.1.1 (Fin.last ((P+1)+Q)), by rw [insUp_card]; have := y.1.2; omega⟩,
     Fin.last ((P+1)+Q+1))
  else
    (⟨insUp y.1.1 (Fin.succ (y.1.1.orderEmbOfFin y.1.2 ⟨y.2.val - 1, by omega⟩)),
       by rw [insUp_card]; have := y.1.2; omega⟩,
     Fin.succ (Fin.castSucc (y.1.1.orderEmbOfFin y.1.2 ⟨y.2.val - 1, by omega⟩)))

/-! ### The `b`-side reindexing map and its inverse -/

/-- The `b`-side reindexing: `(A,k) ↦ (delPosP A (delIdx k), cntB A k.val)`. -/
def bFwd (P Q : ℕ) (x : IdxB P Q) : TargetB P Q :=
  (⟨delPosP x.1.1.1 (delIdx x.1.2), by
      rw [delPosP_card_of_notMem x.2.1]; exact x.1.1.2⟩,
   ⟨cntB x.1.1.1 x.1.2.val, by
      have := cntB_le_card x.1.1.1 x.1.2.val; have := x.1.1.2; omega⟩)

/-- The inverse of `bFwd`: insert a `b`-letter at the position determined by `j`. -/
def bInvIdx (P Q : ℕ) (y : TargetB P Q) : Idx P Q :=
  if h0 : y.2.val = 0 then
    (⟨shUp y.1.1 (0 : Fin ((P+1)+Q+1)), by rw [shUp_card]; exact y.1.2⟩,
     (0 : Fin ((P+1)+Q+2)))
  else if hl : y.2.val = Q+1 then
    (⟨shUp y.1.1 (Fin.last ((P+1)+Q)), by rw [shUp_card]; exact y.1.2⟩,
     Fin.last ((P+1)+Q+1))
  else
    (⟨shUp y.1.1 (Fin.succ ((Finset.univ \ y.1.1).orderEmbOfFin
          (by rw [card_univ_sdiff_fin]; have := y.1.2; omega :
            (Finset.univ \ y.1.1).card = Q)
          (⟨y.2.val - 1, by omega⟩ : Fin Q))),
       by rw [shUp_card]; exact y.1.2⟩,
     Fin.succ (Fin.castSucc ((Finset.univ \ y.1.1).orderEmbOfFin
          (by rw [card_univ_sdiff_fin]; have := y.1.2; omega :
            (Finset.univ \ y.1.1).card = Q)
          (⟨y.2.val - 1, by omega⟩ : Fin Q))))


/-! ### Faces of the tensor product and of whiskered simplices -/

/-- The face of a simplex of the tensor product is the pair of the faces. -/
lemma delta_tensor (X Y : SSet.{0}) {n : ℕ} (k : Fin (n+2))
    (p : (MonoidalCategoryStruct.tensorObj X Y).obj (op ⦋n+1⦌)) :
    (MonoidalCategoryStruct.tensorObj X Y).δ k p = (X.δ k p.1, Y.δ k p.2) := by
  rw [SimplicialObject.δ, Monoidal.tensorObj_map]
  exact CategoryTheory.tensor_apply _ _ p

/-- A face of a whiskered simplex is the whiskering of the composite with the face map. -/
lemma delta_map (X : SSet.{0}) {m n : ℕ} (k : Fin (m+2)) (φ : ⦋m+1⦌ ⟶ ⦋n⦌)
    (x : X.obj (op ⦋n⦌)) :
    X.δ k (X.map φ.op x) = X.map (SimplexCategory.δ k ≫ φ).op x := by
  rw [SimplicialObject.δ, op_comp, Functor.map_comp]
  rfl

/-- The face of the staircase simplex of `A` at the face index `k`. -/
lemma delta_ezPair (P Q : ℕ) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌))
    (A : Finset (Fin ((P+1)+(Q+1)))) (hA : A.card = P+1) (k : Fin ((P+1)+Q+2)) :
    (MonoidalCategoryStruct.tensorObj X Y).δ k (ezPair P Q a b A hA)
      = (X.map ((SimplexCategory.δ k) ≫ shA A (le_of_eq hA)).op a,
         Y.map ((SimplexCategory.δ k) ≫ shB A (by have := hA; omega)).op b) := by
  have h := delta_tensor X Y k (ezPair P Q a b A hA)
  rw [h]
  congr 1
  · show X.δ k (X.map (shA A (le_of_eq hA)).op a) = _
    rw [delta_map]
  · show Y.δ k (Y.map (shB A (by have := hA; omega)).op b) = _
    rw [delta_map]

/-- The summand of `ezA P Q a b` at the index `y = (A', i)`. -/
def ezAsum (P Q : ℕ) (X Y : SSet.{0}) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌))
    (y : TargetA P Q) : ProdChain X Y ((P+1)+Q) :=
  Finsupp.single
    (X.map (shA y.1.1 (le_of_eq y.1.2)).op (X.δ y.2 a),
     Y.map (shB y.1.1 (by have := y.1.2; omega)).op b)
    ((-1 : ℚ) ^ (y.2 : ℕ) * (sgnA y.1.1 : ℚ))

/-- The summand of `ezB P Q a b` at the index `y = (A'', j)`. -/
def ezBsum (P Q : ℕ) (X Y : SSet.{0}) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌))
    (y : TargetB P Q) : ProdChain X Y ((P+1)+Q) :=
  Finsupp.single
    (X.map (shA y.1.1 (by have := y.1.2; omega)).op a,
     Y.map (shB y.1.1 (by have := y.1.2; omega)).op (Y.δ y.2 b))
    ((-1 : ℚ) ^ (y.2 : ℕ) * (sgnA y.1.1 : ℚ))

/-- Swapping the order of a `Fin n`-sum and an `α`-sum. -/
lemma sum_fin_sum_eq_sum_prod {α M : Type*} [Fintype α] [AddCommMonoid M] (n : ℕ)
    (g : Fin n → α → M) :
    (∑ i : Fin n, ∑ a : α, g i a) = ∑ x : α × Fin n, g x.2 x.1 := by
  rw [← Fintype.sum_prod_type (fun p : Fin n × α => g p.1 p.2)]
  exact Equiv.sum_comp (Equiv.prodComm (Fin n) α) (fun q : α × Fin n => g q.2 q.1)

lemma ezA_eq_sum (P Q : ℕ) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌)) :
    ezA P Q a b = ∑ y : TargetA P Q, ezAsum P Q X Y a b y := by
  have h1 : (∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) •
          ∑ A' : {A' : Finset (Fin ((P+1)+Q)) // A'.card = P},
            (sgnA A'.1 : ℚ) • Finsupp.single
              (X.map (shA A'.1 (le_of_eq A'.2)).op (X.δ i a),
               Y.map (shB A'.1 (by have := A'.2; omega)).op b) (1 : ℚ))
      = ezA P Q a b := rfl
  have h3 : (∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) •
          ∑ A' : {A' : Finset (Fin ((P+1)+Q)) // A'.card = P},
            (sgnA A'.1 : ℚ) • Finsupp.single
              (X.map (shA A'.1 (le_of_eq A'.2)).op (X.δ i a),
               Y.map (shB A'.1 (by have := A'.2; omega)).op b) (1 : ℚ))
      = ∑ i : Fin (P+2), ∑ A' : {A' : Finset (Fin ((P+1)+Q)) // A'.card = P},
          ((-1 : ℚ) ^ (i : ℕ) * (sgnA A'.1 : ℚ)) • Finsupp.single
            (X.map (shA A'.1 (le_of_eq A'.2)).op (X.δ i a),
             Y.map (shB A'.1 (by have := A'.2; omega)).op b) (1 : ℚ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_sum_gen]
    refine Finset.sum_congr rfl fun A' _ => ?_
    rw [smul_smul]
  have h2 : (∑ i : Fin (P+2), ∑ A' : {A' : Finset (Fin ((P+1)+Q)) // A'.card = P},
          ((-1 : ℚ) ^ (i : ℕ) * (sgnA A'.1 : ℚ)) • Finsupp.single
            (X.map (shA A'.1 (le_of_eq A'.2)).op (X.δ i a),
             Y.map (shB A'.1 (by have := A'.2; omega)).op b) (1 : ℚ))
      = ∑ y : TargetA P Q, ezAsum P Q X Y a b y := by
    rw [sum_fin_sum_eq_sum_prod (M := ProdChain X Y ((P+1)+Q))]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [ezAsum, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [← h1, h3, h2]

lemma ezB_eq_sum (P Q : ℕ) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌)) :
    ezB P Q a b = ∑ y : TargetB P Q, ezBsum P Q X Y a b y := by
  have h1 : (∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) •
          ∑ A' : {A' : Finset (Fin ((P+1)+Q)) // A'.card = P+1},
            (sgnA A'.1 : ℚ) • Finsupp.single
              (X.map (shA A'.1 (by have := A'.2; omega)).op a,
               Y.map (shB A'.1 (by have := A'.2; omega)).op (Y.δ j b)) (1 : ℚ))
      = ezB P Q a b := rfl
  have h3 : (∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) •
          ∑ A' : {A' : Finset (Fin ((P+1)+Q)) // A'.card = P+1},
            (sgnA A'.1 : ℚ) • Finsupp.single
              (X.map (shA A'.1 (by have := A'.2; omega)).op a,
               Y.map (shB A'.1 (by have := A'.2; omega)).op (Y.δ j b)) (1 : ℚ))
      = ∑ j : Fin (Q+2), ∑ A' : {A' : Finset (Fin ((P+1)+Q)) // A'.card = P+1},
          ((-1 : ℚ) ^ (j : ℕ) * (sgnA A'.1 : ℚ)) • Finsupp.single
            (X.map (shA A'.1 (by have := A'.2; omega)).op a,
             Y.map (shB A'.1 (by have := A'.2; omega)).op (Y.δ j b)) (1 : ℚ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_sum_gen]
    refine Finset.sum_congr rfl fun A' _ => ?_
    rw [smul_smul]
  have h2 : (∑ j : Fin (Q+2), ∑ A' : {A' : Finset (Fin ((P+1)+Q)) // A'.card = P+1},
          ((-1 : ℚ) ^ (j : ℕ) * (sgnA A'.1 : ℚ)) • Finsupp.single
            (X.map (shA A'.1 (by have := A'.2; omega)).op a,
             Y.map (shB A'.1 (by have := A'.2; omega)).op (Y.δ j b)) (1 : ℚ))
      = ∑ y : TargetB P Q, ezBsum P Q X Y a b y := by
    rw [sum_fin_sum_eq_sum_prod (M := ProdChain X Y ((P+1)+Q))]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [ezBsum, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [← h1, h3, h2]

end

end Work.Cohomology.EZG
