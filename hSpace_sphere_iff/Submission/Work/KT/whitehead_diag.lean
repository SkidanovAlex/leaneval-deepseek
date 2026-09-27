import Mathlib
import Submission.Work.KT.WhiteheadSetup
import Submission.Work.KT.whitehead_prod_upper
import Submission.Work.KT.whitehead_prod_lower
import Submission.Work.KT.whitehead_block_algebra

namespace Work.KT

open Matrix

/-! ## Auxiliary enumeration of the elementary matrices

We first isolate the five block matrices appearing in the classical five-step proof of
Whitehead's lemma, and build the explicit list of transvections realising each of them. -/

/-- The list of transvections whose product is the block matrix `[[1, X], [0, 1]]`
(on the index type `Fin n ⊕ Fin n`). -/
private noncomputable def upList {R : Type} [Ring R] (n : ℕ) (X : Matrix (Fin n) (Fin n) R) :
    List (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :=
  (Finset.univ : Finset (Fin n × Fin n)).toList.map
    (fun p => (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
      + Matrix.single (Sum.inl p.1) (Sum.inr p.2) (X p.1 p.2))

/-- The list of transvections whose product is the block matrix `[[1, 0], [Y, 1]]`. -/
private noncomputable def loList {R : Type} [Ring R] (n : ℕ) (Y : Matrix (Fin n) (Fin n) R) :
    List (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :=
  (Finset.univ : Finset (Fin n × Fin n)).toList.map
    (fun p => (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
      + Matrix.single (Sum.inr p.1) (Sum.inl p.2) (Y p.1 p.2))

/-- The concatenation of the five lists realising `[[1,0],[V,1]]`, `[[1,-U],[0,1]]`,
`[[1,1],[0,1]]`, `[[1,0],[-1,1]]` and `[[1,1-V],[0,1]]`, in this order. -/
private noncomputable def bigList {R : Type} [Ring R] (n : ℕ) (U V : Matrix (Fin n) (Fin n) R) :
    List (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :=
  loList n V ++ (upList n (-U) ++ (upList n (1 : Matrix (Fin n) (Fin n) R) ++
    (loList n (-1) ++ upList n (1 - V))))

private lemma upList_prod {R : Type} [Ring R] {n : ℕ} (X : Matrix (Fin n) (Fin n) R) :
    (upList n X).prod = (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) X 0 1 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :=
  whitehead_prod_upper X

private lemma loList_prod {R : Type} [Ring R] {n : ℕ} (Y : Matrix (Fin n) (Fin n) R) :
    (loList n Y).prod = (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) 0 Y 1 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :=
  whitehead_prod_lower Y

private lemma upList_mem {R : Type} [Ring R] {n : ℕ} (X : Matrix (Fin n) (Fin n) R) {M}
    (hM : M ∈ upList n X) :
    ∃ (i j : Fin n ⊕ Fin n) (a : R), i ≠ j ∧ M = 1 + Matrix.single i j a := by
  simp only [upList, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at hM
  obtain ⟨p, rfl⟩ := hM
  exact ⟨Sum.inl p.1, Sum.inr p.2, X p.1 p.2, Sum.inl_ne_inr, rfl⟩

private lemma loList_mem {R : Type} [Ring R] {n : ℕ} (Y : Matrix (Fin n) (Fin n) R) {M}
    (hM : M ∈ loList n Y) :
    ∃ (i j : Fin n ⊕ Fin n) (a : R), i ≠ j ∧ M = 1 + Matrix.single i j a := by
  simp only [loList, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and] at hM
  obtain ⟨p, rfl⟩ := hM
  exact ⟨Sum.inr p.1, Sum.inl p.2, Y p.1 p.2, Sum.inr_ne_inl, rfl⟩

private lemma bigList_mem {R : Type} [Ring R] {n : ℕ} (U V : Matrix (Fin n) (Fin n) R) {M}
    (hM : M ∈ bigList n U V) :
    ∃ (i j : Fin n ⊕ Fin n) (a : R), i ≠ j ∧ M = 1 + Matrix.single i j a := by
  simp only [bigList, List.mem_append] at hM
  rcases hM with h | h | h | h | h
  · exact loList_mem V h
  · exact upList_mem (-U) h
  · exact upList_mem 1 h
  · exact loList_mem (-1) h
  · exact upList_mem (1 - V) h

private lemma bigList_prod {R : Type} [Ring R] {n : ℕ} (U V : Matrix (Fin n) (Fin n) R)
    (hVU : V * U = 1) (hUV : U * V = 1) :
    (bigList n U V).prod = (Matrix.fromBlocks U 0 0 V :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) := by
  simp only [bigList, List.prod_append, upList_prod, loList_prod]
  exact whitehead_block_algebra U V hVU hUV

private lemma map_reindex_prod {R : Type} [Ring R] {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq m] [DecidableEq p] (e : m ≃ p) (l : List (Matrix m m R)) :
    (l.map (Matrix.reindex e e)).prod = Matrix.reindex e e l.prod :=
  (map_list_prod (Matrix.reindexRingEquiv R e) l).symm

private lemma reindex_one_add_single {R : Type} [Ring R] {m p : Type*} [Fintype m] [Fintype p]
    [DecidableEq m] [DecidableEq p] (e : m ≃ p) (i j : m) (a : R) :
    Matrix.reindex e e (1 + Matrix.single i j a) = 1 + Matrix.single (e i) (e j) a := by
  rw [← Matrix.coe_reindexRingEquiv R e, map_add, map_one, Matrix.coe_reindexRingEquiv R e,
    Whitehead.reindex_single]

/-- **Whitehead's lemma** (block form): if `U` and `V` are inverse square matrices over a ring `R`,
then the block matrix `diag(U,V)` is a product of elementary matrices (`1 + single i j a`, `i ≠ j`).

Route (all `n × n` blocks; `X₁ = [[U,0],[0,V]]`):
`[[1,0],[-V,1]]·X₁ = [[U,0],[-1,V]]`, `[[1,U],[0,1]]·[[U,0],[-1,V]] = [[0,1],[-1,V]]`,
`[[1,-1],[0,1]]·[[0,1],[-1,V]] = [[1,1-V],[-1,V]]`, `[[1,0],[1,1]]·[[1,1-V],[-1,V]] = [[1,1-V],[0,1]]`,
`[[1,V-1],[0,1]]·[[1,1-V],[0,1]] = 1`, using `V*U = 1` and `U*V = 1`.  Inverting the five block matrices
gives `X₁` as their product; each block matrix `[[1,X],[0,1]]` splits as the product over `(i,j)` of the
genuine transvections `1 + single i (n+j) X_{ij}` (and symmetrically for `[[1,0],[Y,1]]`). -/
theorem whitehead_diag {R : Type} [Ring R] {n : ℕ} (U V : Matrix (Fin n) (Fin n) R)
    (hVU : V * U = 1) (hUV : U * V = 1) :
    ∃ e : List (Matrix (Fin (n + n)) (Fin (n + n)) R),
      (∀ M ∈ e, ∃ (i j : Fin (n + n)) (a : R), i ≠ j ∧ M = 1 + Matrix.single i j a) ∧
      e.prod = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks U 0 0 V) := by
  refine ⟨(bigList n U V).map (Matrix.reindex finSumFinEquiv finSumFinEquiv), ?_, ?_⟩
  · intro M hM
    rw [List.mem_map] at hM
    obtain ⟨M₀, hM₀, rfl⟩ := hM
    obtain ⟨i₀, j₀, a, hij, hM₀eq⟩ := bigList_mem U V hM₀
    refine ⟨finSumFinEquiv i₀, finSumFinEquiv j₀, a, fun h => hij (finSumFinEquiv.injective h), ?_⟩
    rw [hM₀eq, reindex_one_add_single]
  · rw [map_reindex_prod, bigList_prod U V hVU hUV]

end Work.KT
