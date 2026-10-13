/-
  WilE8 — `E8_reduce`: the packaging `Gen ⊆ StarR` (E8a), given the closure data `Close`.

  The induction on the `Gen` derivation uses the level data of `Levels.lean`; the only non-pure
  ingredients are the closure lemmas of `Close` (complement, intersection, projection, the
  hyperplane case), which come from the E7/E2 theorems of area E (see `Assemble.lean`).
-/
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE8.Basic
import Submission.Work.WilE8.Levels
import Submission.Work.WilE8.StarR.compl
import Submission.Work.WilE8.StarR.inter
import Submission.Work.WilE8.Star.lift_right_cube
import Submission.Work.WilE8.Star.lift_left_cube
import Submission.Work.WilE8.Star.starPiece_set_eq_empty_or_cube
import Submission.Work.WilE8.GenZero.eq_empty_or_univ
import Submission.Work.WilE8.Poly.eval_mono_nat

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical Topology
namespace Work.WilE8
open WilkiesDesign WilkiesDesign.E

/-! ## `psiV` and the coordinate maps -/

lemma init_psiV {n : ℕ} (z : Fin (n + 1) → ℝ) :
    Fin.init (psiV z) = psiV (Fin.init z) := by
  funext i; rfl

lemma tail_psiV {n : ℕ} (z : Fin (n + 1) → ℝ) :
    Fin.tail (psiV z) = psiV (Fin.tail z) := by
  funext i; rfl

lemma projLast_empty {n : ℕ} : projLast (∅ : Set (Fin (n + 1) → ℝ)) = ∅ := by
  ext x; simp [projLast]

lemma projLast_univ {n : ℕ} : projLast (Set.univ : Set (Fin (n + 1) → ℝ)) = Set.univ := by
  ext x; simp [projLast]

/-! ## The `StarR`-level product axioms -/

theorem starR_lift_right {n D a0 : ℕ} {X : Set (Fin n → ℝ)} (h : StarR a0 D n X) :
    StarR (a0 + 1) D (n + 1) {z : Fin (n + 1) → ℝ | Fin.init z ∈ X} := by
  obtain ⟨Z, hZ, rfl⟩ := h
  refine ⟨{w : Fin (n + 1) → ℝ | Fin.init w ∈ Z} ∩ cubeC (n + 1), Star.lift_right_cube hZ, ?_⟩
  ext z
  constructor
  · intro hz
    refine ⟨?_, psiV_mem_cube z⟩
    have h2 : psiV (Fin.init z) ∈ Z := hz
    rwa [← init_psiV z] at h2
  · rintro ⟨h1, -⟩
    show psiV z ∈ {w : Fin (n + 1) → ℝ | Fin.init w ∈ Z}
    rw [Set.mem_setOf_eq, init_psiV z]
    exact h1

theorem starR_lift_left {n D a0 : ℕ} {X : Set (Fin n → ℝ)} (h : StarR a0 D n X) :
    StarR (a0 + 1) D (n + 1) {z : Fin (n + 1) → ℝ | Fin.tail z ∈ X} := by
  obtain ⟨Z, hZ, rfl⟩ := h
  refine ⟨{w : Fin (n + 1) → ℝ | Fin.tail w ∈ Z} ∩ cubeC (n + 1), Star.lift_left_cube hZ, ?_⟩
  ext z
  constructor
  · intro hz
    refine ⟨?_, psiV_mem_cube z⟩
    have h2 : psiV (Fin.tail z) ∈ Z := hz
    rwa [← tail_psiV z] at h2
  · rintro ⟨h1, -⟩
    show psiV z ∈ {w : Fin (n + 1) → ℝ | Fin.tail w ∈ Z}
    rw [Set.mem_setOf_eq, tail_psiV z]
    exact h1

namespace Close

variable (C : Close)

/-- The empty set at level `(F, n)` with the degree bound of degree `0`. -/
theorem starR_zero_empty (F n : ℕ) :
    StarR (C.lvlA F n) ((C.lvlP F n).eval 0) n (∅ : Set (Fin n → ℝ)) :=
  StarR.mono (StarR.empty (C.lvlA F n) n) le_rfl (le_of_eq (C.lvlP_eval_zero F n).symm)

/-- The whole space at level `(F, n)` with the degree bound of degree `0`. -/
theorem starR_zero_univ (F n : ℕ) :
    StarR (C.lvlA F n) ((C.lvlP F n).eval 0) n (Set.univ : Set (Fin n → ℝ)) :=
  StarR.mono (StarR.univ (C.lvlA F n) n (C.lvlA_ge_n F n)) le_rfl
    (le_of_eq (C.lvlP_eval_zero F n).symm)

/-- `Finset`-indexed version of the goal, used for `union` and `inter`. -/
theorem reduce_core' {F n k : ℕ} (D : Fin k → ℕ) (A : Fin k → Set (Fin n → ℝ))
    (h : ∀ i, Gen F (D i) n (A i))
    (ih : ∀ i, StarR (C.lvlA F n) ((C.lvlP F n).eval (D i)) n (A i)) :
    StarR (C.lvlA F n) ((C.lvlP F n).eval (∑ i, D i)) n (⋃ i, A i) := by
  refine ⟨⋃ i, (ih i).choose, ?_, ?_⟩
  · exact Star.mono (Star.iUnion fun i => (ih i).choose_spec.1) le_rfl
      (C.lvlP_superadd F n k D)
  · have h1 : (⋃ i, A i) = ⋃ i, (psiV ⁻¹' ((ih i).choose)) :=
      Set.iUnion_congr fun i => (ih i).choose_spec.2
    rw [h1, ← Set.preimage_iUnion]

/-- The main induction: every `Gen`-set is a transported `Star`-set of the level format and
degree. -/
theorem reduce_core (F D n : ℕ) (X : Set (Fin n → ℝ)) (h : Gen F D n X) :
    StarR (C.lvlA F n) ((C.lvlP F n).eval D) n X :=
  Gen.rec (motive := fun F D n X _ => StarR (C.lvlA F n) ((C.lvlP F n).eval D) n X)
    (fun {F D n} {X} hst => StarR.mono hst (C.lvlA_ge_F F n) (C.lvlP_ge_id F n D))
    (fun {F D n} {X} _ ih => StarR.mono ih (C.lvlA_mono F n) (C.lvlP_mono_F F n D))
    (fun {F D n} {X} _ ih => StarR.mono ih le_rfl (C.lvlP_mono_D F n D (D + 1) (Nat.le_succ D)))
    (fun {F D n} {X} hpre ih => by
      rcases Nat.eq_zero_or_pos D with hD | hD
      · subst hD
        rcases GenZero.eq_empty_or_univ hpre with hX | hX
        · rw [hX, Set.compl_empty]
          exact C.starR_zero_univ (F + 1) n
        · rw [hX, Set.compl_univ]
          exact C.starR_zero_empty (F + 1) n
      · exact StarR.mono (C.hcompl (C.lvlA F n) n ((C.lvlP F n).eval D) X ih)
          (C.lvlA_compl F n) (C.lvlP_dom_compl F n D hD))
    (fun {F D n} {X} hpre ih => by
      rcases Nat.eq_zero_or_pos D with hD | hD
      · subst hD
        rcases GenZero.eq_empty_or_univ hpre with hX | hX
        · rw [hX, projLast_empty]
          exact C.starR_zero_empty (F + 1) n
        · rw [hX, projLast_univ]
          exact C.starR_zero_univ (F + 1) n
      · exact StarR.mono (C.hproj (C.lvlA F (n + 1)) n ((C.lvlP F (n + 1)).eval D) X ih)
          (C.lvlA_proj F n) (C.lvlP_dom_proj F n D hD))
    (fun {F D n} {X} hpre ih => by
      rcases Nat.eq_zero_or_pos D with hD | hD
      · subst hD
        rcases GenZero.eq_empty_or_univ hpre with hX | hX
        · subst hX
          have h1 : {z : Fin (n + 1) → ℝ | Fin.init z ∈ (∅ : Set (Fin n → ℝ))} = ∅ := by
            ext z; simp
          rw [h1]
          exact C.starR_zero_empty (F + 1) (n + 1)
        · subst hX
          have h1 : {z : Fin (n + 1) → ℝ | Fin.init z ∈ (Set.univ : Set (Fin n → ℝ))}
              = Set.univ := by ext z; simp
          rw [h1]
          exact C.starR_zero_univ (F + 1) (n + 1)
      · refine StarR.mono (starR_lift_right ih) ?_ (C.lvlP_dom_prod F (n + 1) D hD)
        show C.lvlA F n + 1 ≤ C.lvlA (F + 1) (n + 1)
        simpa using C.lvlA_prod F (n + 1))
    (fun {F D n} {X} hpre ih => by
      rcases Nat.eq_zero_or_pos D with hD | hD
      · subst hD
        rcases GenZero.eq_empty_or_univ hpre with hX | hX
        · subst hX
          have h1 : {z : Fin (n + 1) → ℝ | Fin.tail z ∈ (∅ : Set (Fin n → ℝ))} = ∅ := by
            ext z; simp
          rw [h1]
          exact C.starR_zero_empty (F + 1) (n + 1)
        · subst hX
          have h1 : {z : Fin (n + 1) → ℝ | Fin.tail z ∈ (Set.univ : Set (Fin n → ℝ))}
              = Set.univ := by ext z; simp
          rw [h1]
          exact C.starR_zero_univ (F + 1) (n + 1)
      · refine StarR.mono (starR_lift_left ih) ?_ (C.lvlP_dom_prod F (n + 1) D hD)
        show C.lvlA F n + 1 ≤ C.lvlA (F + 1) (n + 1)
        simpa using C.lvlA_prod F (n + 1))
    (fun {F n k} D A h ih => C.reduce_core' D A h ih)
    (fun {F n k} D A h ih => by
      rcases Nat.eq_zero_or_pos (∑ i, D i) with hD | hD
      · rcases GenZero.eq_empty_or_univ (show Gen (F + 1) 0 n (⋂ i, A i) from by
          rw [← hD]; exact Gen.inter D A h) with hX | hX
        · rw [hX, hD]; exact C.starR_zero_empty (F + 1) n
        · rw [hX, hD]; exact C.starR_zero_univ (F + 1) n
      · refine StarR.mono
          (C.hinter (C.lvlA F n) n k (fun i => (C.lvlP F n).eval (D i)) A ih)
          (C.lvlA_inter F n) ?_
        refine le_trans (Poly.eval_mono_nat (C.interP (C.lvlA F n) n)
          (C.lvlP_superadd F n k D)) (C.lvlP_dom_inter F n (∑ i, D i) hD))
    (fun n Q => by
      rcases Nat.eq_zero_or_pos Q.totalDegree with h0 | h0
      · have hg : Gen n 0 n {x : Fin n → ℝ | MvPolynomial.eval x Q = 0} := h0 ▸ Gen.hyp n Q
        rcases GenZero.eq_empty_or_univ hg with hX | hX
        · rw [hX, h0]; exact C.starR_zero_empty n n
        · rw [hX, h0]; exact C.starR_zero_univ n n
      · refine StarR.mono (C.hhyp n Q h0) ?_ (C.lvlP_dom_hyp n n _ h0)
        have h2 := C.lvlA_ge_hyp n n
        omega) h

end Close

end Work.WilE8
