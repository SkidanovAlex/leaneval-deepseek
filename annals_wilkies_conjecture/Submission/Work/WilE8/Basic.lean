/-
  WilE8 — area E8 (packaging into a `SOMin`): basic vocabulary and easy API.

  Everything here is a *definition* or an easy lemma about the frozen vocabulary of
  `Submission.Work.Wilkies.E.Spec` (the inductive `Gen`, the predicates `Star`, `StarR`,
  `SemiPf`, …).  The hard lemmas are stated and proved in the sibling modules.

  Conventions:
  * `ocube n` is the open cube `(-1,1)^n`; this is the range of `psiV : ℝⁿ → ℝⁿ`
    (NOT the frozen `WilkiesDesign.openCube`, which is `(0,1)^n`).
  * `psiInv` is the inverse of `psi` on `(-1,1)`.
-/
import Submission.Work.Wilkies.E.Spec
import Mathlib.Topology.Order.Basic

set_option autoImplicit false
noncomputable section
open Classical Topology
namespace Work.WilE8
open WilkiesDesign WilkiesDesign.E

/-! ## The ψ-coordinate change -/

/-- The inverse of `psi` on `(-1,1)`. -/
def psiInv (y : ℝ) : ℝ := y / Real.sqrt (1 - y ^ 2)

/-- The open cube `(-1,1)^n`, i.e. the range of `psiV`. -/
def ocube (n : ℕ) : Set (Fin n → ℝ) := {x | ∀ i, |x i| < 1}

lemma mem_ocube {n : ℕ} {x : Fin n → ℝ} : x ∈ ocube n ↔ ∀ i, |x i| < 1 := Iff.rfl

/-- The union `⋃ P ∈ L, P.set` over a list of pieces, spelled out. -/
lemma mem_list_iUnion {n : ℕ} {L : List (StarPiece n)} {x : Fin n → ℝ} :
    (x ∈ ⋃ P ∈ L, P.set) ↔ ∃ P : StarPiece n, P ∈ L ∧ x ∈ P.set := by
  simp only [Set.mem_iUnion, exists_prop]

/-! ## The cube as a product of intervals -/

lemma cubeC_eq (n : ℕ) : cubeC n = Set.univ.pi (fun _ : Fin n => Set.Icc (-1 : ℝ) 1) := by
  ext x
  simp only [cubeC, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies,
    abs_le]

lemma cubeC_convex (n : ℕ) : Convex ℝ (cubeC n) := by
  rw [cubeC_eq]
  exact convex_pi fun _ _ => convex_Icc _ _

lemma cubeC_preconnected (n : ℕ) : IsPreconnected (cubeC n) := (cubeC_convex n).isPreconnected

lemma zero_mem_cubeC (n : ℕ) : (0 : Fin n → ℝ) ∈ cubeC n := fun i => by simp

lemma connectedComponentIn_cubeC (n : ℕ) :
    connectedComponentIn (cubeC n) (0 : Fin n → ℝ) = cubeC n := by
  refine Set.Subset.antisymm (connectedComponentIn_subset _ _) ?_
  exact IsPreconnected.subset_connectedComponentIn (cubeC_preconnected n) (zero_mem_cubeC n)
    (subset_refl _)

/-- Projection to the first `n` coordinates does not change the cube. -/
lemma projFirst_image_cubeC (n m : ℕ) : projFirst n m '' cubeC (n + m) = cubeC n := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨z, hz, rfl⟩ i
    exact hz (Fin.castAdd m i)
  · intro x hx
    refine ⟨fun i => if h : (i : ℕ) < n then x ⟨i, h⟩ else 0, ?_, ?_⟩
    · intro i
      by_cases h : (i : ℕ) < n
      · simpa [h] using hx ⟨(i : ℕ), h⟩
      · simp [h]
    · funext i
      have h : ((Fin.castAdd m i : Fin (n + m)) : ℕ) < n := by
        rw [Fin.val_castAdd]; exact i.isLt
      show (if h' : ((Fin.castAdd m i : Fin (n + m)) : ℕ) < n then
          x ⟨((Fin.castAdd m i : Fin (n + m)) : ℕ), h'⟩ else 0) = x i
      rw [dite_eq_left h]
      exact congrArg x (Fin.ext (by rw [Fin.val_castAdd]))

/-! ## `SemiPf` sets -/

/-- The `SemiPf` set whose `.set` is the whole closed cube (one empty basic set). -/
def cubeSemiPf (n : ℕ) : SemiPf n := ⟨0, EAChain.nil n, [⟨[], []⟩]⟩

lemma cubeSemiPf_set (n : ℕ) : (cubeSemiPf n).set = cubeC n := by
  ext x
  constructor
  · rintro ⟨hx, B, hB, -⟩
    simpa using hx
  · intro hx
    refine ⟨hx, ⟨[], []⟩, List.mem_singleton_self _, ?_, ?_⟩
    · intro f hf; cases hf
    · intro g hg; cases hg

namespace SemiPf

variable {k : ℕ}

/-- Every semi-Pfaffian set is contained in the cube it is defined in. -/
lemma set_subset_cube (X : SemiPf k) : X.set ⊆ cubeC k := fun _ hx => hx.1

end SemiPf

/-- The `Star`-piece which is the whole cube. -/
def cubePiece (n : ℕ) : StarPiece n := ⟨0, cubeSemiPf n, 0⟩

lemma cubePiece_set (n : ℕ) : (cubePiece n).set = cubeC n := by
  show projFirst n 0 '' connectedComponentIn (cubeSemiPf n).set (0 : Fin (n + 0) → ℝ) = cubeC n
  rw [cubeSemiPf_set, connectedComponentIn_cubeC n]
  simpa using projFirst_image_cubeC n 0

/-! ## `StarPiece` and `Star`: basic API -/

namespace StarPiece

variable {n : ℕ}

/-- Every piece is contained in the closed cube. -/
theorem set_subset_cube (P : StarPiece n) : P.set ⊆ cubeC n := by
  have h : P.set = projFirst n P.m '' connectedComponentIn P.X.set P.p := rfl
  rw [h]
  rintro x ⟨z, hz, rfl⟩ i
  exact SemiPf.set_subset_cube P.X (connectedComponentIn_subset _ _ hz) (Fin.castAdd P.m i)

end StarPiece

namespace Star

variable {F D n : ℕ} {Y Y1 Y2 : Set (Fin n → ℝ)} {D1 D2 : ℕ}

/-- Every `Star`-set is contained in the closed cube. -/
theorem subset_cube (h : Star F D n Y) : Y ⊆ cubeC n := by
  obtain ⟨L, rfl, -, -⟩ := h
  intro x hx
  rw [mem_list_iUnion] at hx
  obtain ⟨P, -, hx⟩ := hx
  exact StarPiece.set_subset_cube P hx

/-- Monotonicity in both format and degree. -/
theorem mono (h : Star F D n Y) {F' D' : ℕ} (hF : F ≤ F') (hD : D ≤ D') : Star F' D' n Y := by
  obtain ⟨L, rfl, h1, h2⟩ := h
  exact ⟨L, rfl, fun P hP => le_trans (h1 P hP) hF, le_trans h2 hD⟩

/-- Monotonicity in the degree. -/
theorem mono_deg (h : Star F D n Y) {D' : ℕ} (hD : D ≤ D') : Star F D' n Y := mono h le_rfl hD

theorem empty (F n : ℕ) : Star F 0 n (∅ : Set (Fin n → ℝ)) :=
  ⟨[], (by simp), by simp, by simp⟩

/-- The whole closed cube is a `Star`-set of degree `0`: the empty conjunction of conditions
is a valid basic set whose zero set is the cube. -/
theorem cubeC (n : ℕ) : Star n 0 n (cubeC n) := by
  refine ⟨[cubePiece n], ?_, ?_, ?_⟩
  · rw [← cubePiece_set n]
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      rw [mem_list_iUnion]
      exact ⟨cubePiece n, by simp, hx⟩
    · intro x hx
      rw [mem_list_iUnion] at hx
      obtain ⟨P, hP, hx⟩ := hx
      rw [List.mem_singleton] at hP
      exact hP ▸ hx
  · rintro P hP
    rw [List.mem_singleton] at hP
    subst hP
    exact le_rfl
  · rw [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    exact le_of_eq (by simp only [cubePiece]; rfl)

theorem union2 (h1 : Star F D1 n Y1) (h2 : Star F D2 n Y2) :
    Star F (D1 + D2) n (Y1 ∪ Y2) := by
  obtain ⟨L1, hY1, h1a, h1b⟩ := h1
  obtain ⟨L2, hY2, h2a, h2b⟩ := h2
  refine ⟨L1 ++ L2, ?_, ?_, ?_⟩
  · rw [hY1, hY2]
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      rcases hx with hx | hx
      · rw [mem_list_iUnion] at hx ⊢
        obtain ⟨P, hP, hx⟩ := hx
        exact ⟨P, List.mem_append_left _ hP, hx⟩
      · rw [mem_list_iUnion] at hx ⊢
        obtain ⟨P, hP, hx⟩ := hx
        exact ⟨P, List.mem_append_right _ hP, hx⟩
    · intro x hx
      rw [mem_list_iUnion] at hx
      obtain ⟨P, hP, hx⟩ := hx
      rcases List.mem_append.mp hP with hP | hP
      · left; rw [mem_list_iUnion]; exact ⟨P, hP, hx⟩
      · right; rw [mem_list_iUnion]; exact ⟨P, hP, hx⟩
  · intro P hP
    rcases List.mem_append.mp hP with hP | hP
    · exact h1a P hP
    · exact h2a P hP
  · rw [List.map_append, List.sum_append]
    exact add_le_add h1b h2b

/-- The union over `insert a s` splits off the term at `a`. -/
lemma iUnion_finset_insert {k n : ℕ} (a : Fin k) (s : Finset (Fin k))
    (A : Fin k → Set (Fin n → ℝ)) :
    (⋃ i ∈ insert a s, A i) = A a ∪ ⋃ i ∈ s, A i := by
  ext x
  simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_insert]
  constructor
  · rintro ⟨i, hi, hx⟩
    rcases hi with rfl | hi
    · exact Or.inl hx
    · exact Or.inr ⟨i, hi, hx⟩
  · rintro (hx | ⟨i, hi, hx⟩)
    · exact ⟨a, Or.inl rfl, hx⟩
    · exact ⟨i, Or.inr hi, hx⟩

/-- Union of finitely many `Star`-sets, the degrees adding up. -/
theorem iUnion {k : ℕ} {D : Fin k → ℕ} {A : Fin k → Set (Fin n → ℝ)}
    (h : ∀ i, Star F (D i) n (A i)) : Star F (∑ i, D i) n (⋃ i, A i) := by
  classical
  have key : ∀ (s : Finset (Fin k)), Star F (∑ i ∈ s, D i) n (⋃ i ∈ s, A i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (Star.empty F n)
    | insert a s ha ih =>
        have h2 := Star.union2 (h a) ih
        have h3 := Star.mono h2 le_rfl (le_of_eq (Finset.sum_insert ha).symm)
        rw [iUnion_finset_insert]
        exact h3
  simpa using key Finset.univ

end Star

namespace StarR

variable {F D n : ℕ} {Y : Set (Fin n → ℝ)}

/-- Monotonicity in both format and degree. -/
theorem mono (h : StarR F D n Y) {F' D' : ℕ} (hF : F ≤ F') (hD : D ≤ D') : StarR F' D' n Y := by
  obtain ⟨Z, hZ, rfl⟩ := h
  exact ⟨Z, Star.mono hZ hF hD, rfl⟩

/-- The empty set. -/
theorem empty (F : ℕ) (n : ℕ) : StarR F 0 n (∅ : Set (Fin n → ℝ)) :=
  ⟨∅, Star.empty F n, by simp⟩

/-- The whole space: `psiV` always lands in the closed cube. -/
theorem univ (F n : ℕ) (hF : n ≤ F) : StarR F 0 n (Set.univ : Set (Fin n → ℝ)) :=
  ⟨cubeC n, Star.mono (Star.cubeC n) hF le_rfl,
    (Set.eq_univ_iff_forall.mpr fun x => psiV_mem_cube x).symm⟩

end StarR

end Work.WilE8
