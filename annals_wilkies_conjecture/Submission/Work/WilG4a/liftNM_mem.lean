import Mathlib
import Submission.Work.WilG0.Defs
import Submission.Work.WilG0.Omega_cast

namespace Work.WilG4a

open WilkiesDesign

/-!
## `liftNM` preserves `Ω`-membership

`Work.WilG0.liftNM n m A` places `A ⊆ ℝ^m` on the *last* `m` coordinates of `ℝ^{n+m}`,
leaving the first `n` coordinates free.  This is exactly the shape produced by iterating
`SOMin.prod_left` `n` times: `prod_left` prepends a fresh free coordinate.

The natural induction runs on the set

`shiftL k m A = {z : Fin (m+k) → ℝ | (fun j => z (Fin.addNat j k)) ∈ A}`,

i.e. `A` on the *last* `k` coordinates of `ℝ^{m+k}`; the step is then definitionally the
`prod_left` construction.  The statement's dimension is `n + m` rather than `m + n`, so the
last step transports along `Nat.add_comm`.
-/

/-- `A` placed on the last `k` coordinates of `Fin (m + k)`. -/
def shiftL (k m : ℕ) (A : Set (Fin m → ℝ)) : Set (Fin (m + k) → ℝ) :=
  {z | (fun j : Fin m => z (Fin.addNat j k)) ∈ A}

/-- Membership in `shiftL k m A`, in the combinatorial coordinates of `Fin.addNat`. -/
lemma shiftL_mem_iff (k m : ℕ) (A : Set (Fin m → ℝ)) (z : Fin (m + k) → ℝ) :
    (z ∈ shiftL k m A) ↔ (fun j : Fin m => z (Fin.addNat j k)) ∈ A := by
  rw [show shiftL k m A =
      {w : Fin (m + k) → ℝ | (fun j : Fin m => w (Fin.addNat j k)) ∈ A} from rfl]
  rw [Set.mem_ofPred_eq]

lemma shiftL_zero (m : ℕ) (A : Set (Fin m → ℝ)) : shiftL 0 m A = A := by
  ext u
  rw [shiftL_mem_iff]
  exact Iff.of_eq (congrArg (fun w => w ∈ A) (funext fun _ => rfl))

lemma shiftL_succ (k m : ℕ) (A : Set (Fin m → ℝ)) :
    shiftL (k + 1) m A = {z : Fin (m + k + 1) → ℝ | Fin.tail z ∈ shiftL k m A} := by
  refine Set.ext fun u => ?_
  have h1 : (u ∈ shiftL (k + 1) m A) ↔
      (fun j : Fin m => u (Fin.addNat j (k + 1))) ∈ A := shiftL_mem_iff _ _ _ _
  have h4 : (fun j : Fin m => u (Fin.addNat j (k + 1))) =
      (fun j : Fin m => u ((Fin.addNat j k).succ)) :=
    funext fun j => congrArg u (Fin.ext rfl)
  exact h1.trans ((Iff.of_eq (congrArg (fun w => w ∈ A) h4)).trans
    (shiftL_mem_iff k m A (Fin.tail u)).symm)

lemma shiftL_mem {S : WilkiesDesign.SOMin} {m F D : ℕ} {A : Set (Fin m → ℝ)}
    (hA : A ∈ S.Ω F D m) (k : ℕ) : shiftL k m A ∈ S.Ω (F + k) D (m + k) := by
  induction k with
  | zero =>
    rw [shiftL_zero]
    exact hA
  | succ k ih =>
    rw [shiftL_succ]
    exact S.prod_left ih

/-- Membership in a `Set` transported along an equality of dimensions. -/
lemma mem_cast_set {a b : ℕ} (h : a = b) (X : Set (Fin a → ℝ)) (u : Fin b → ℝ) :
    u ∈ (h ▸ X) ↔ (fun i : Fin a => u (Fin.cast h i)) ∈ X := by
  cases h
  rfl

/-- Membership in `liftNM`, in the combinatorial coordinates of `Fin.natAdd`. -/
lemma liftNM_mem_iff (n m : ℕ) (A : Set (Fin m → ℝ)) (u : Fin (n + m) → ℝ) :
    (u ∈ Work.WilG0.liftNM n m A) ↔ (fun j : Fin m => u (Fin.natAdd n j)) ∈ A := by
  rw [show Work.WilG0.liftNM n m A =
      {w : Fin (n + m) → ℝ | (fun j : Fin m => w (Fin.natAdd n j)) ∈ A} from rfl]
  rw [Set.mem_ofPred_eq]

/-- `Fin.cast` along `Nat.add_comm` turns the `Fin.addNat` index into the `Fin.natAdd` one. -/
lemma finCast_addNat (m n : ℕ) (j : Fin m) :
    Fin.cast (Nat.add_comm m n) (Fin.addNat j n) = Fin.natAdd n j := by
  apply Fin.ext
  simp only [Fin.cast, Fin.addNat, Fin.natAdd]
  omega

theorem liftNM_mem (S : WilkiesDesign.SOMin) {m F D : ℕ} {A : Set (Fin m → ℝ)} (hA : A ∈ S.Ω F D m) (n : ℕ) : Work.WilG0.liftNM n m A ∈ S.Ω (F + n) D (n + m) := by
  have h1 : shiftL n m A ∈ S.Ω (F + n) D (m + n) := shiftL_mem hA n
  have h2 : (Nat.add_comm m n ▸ shiftL n m A) ∈ S.Ω (F + n) D (n + m) :=
    Work.WilG0.Omega_cast (Nat.add_comm m n) h1
  have h3 : (Nat.add_comm m n ▸ shiftL n m A) = Work.WilG0.liftNM n m A := by
    refine Set.ext fun u => ?_
    have hb1 : (u ∈ (Nat.add_comm m n ▸ shiftL n m A)) ↔
        (fun i : Fin (m + n) => u (Fin.cast (Nat.add_comm m n) i)) ∈ shiftL n m A :=
      mem_cast_set _ _ _
    have hb2 : ((fun i : Fin (m + n) => u (Fin.cast (Nat.add_comm m n) i)) ∈ shiftL n m A) ↔
        (fun j : Fin m => u (Fin.cast (Nat.add_comm m n) (Fin.addNat j n))) ∈ A :=
      shiftL_mem_iff n m A _
    have hb3 : ((fun j : Fin m => u (Fin.cast (Nat.add_comm m n) (Fin.addNat j n))) ∈ A) ↔
        (fun j : Fin m => u (Fin.natAdd n j)) ∈ A :=
      Iff.of_eq (congrArg (fun w => w ∈ A)
        (funext fun j => congrArg u (finCast_addNat m n j)))
    have hb4 : ((fun j : Fin m => u (Fin.natAdd n j)) ∈ A) ↔
        u ∈ Work.WilG0.liftNM n m A := (liftNM_mem_iff n m A u).symm
    exact hb1.trans (hb2.trans (hb3.trans hb4))
  rw [h3] at h2
  exact h2

end Work.WilG4a
