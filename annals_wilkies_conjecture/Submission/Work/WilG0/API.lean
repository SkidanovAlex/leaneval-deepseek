/-
  WilG0 — the elementary Ω API used by the formula calculus: monotonicity in the format and
  the degree, the transport of an Ω-set along an equality of dimensions, and the binary
  operations.  These are thin wrappers around the axioms of `SOMin`; they are stated so that
  every caller can pad formats and degrees with `omega`-provable inequalities instead of
  fighting definitional equality of `Nat`-expressions.
-/
import Submission.Work.WilG0.Defs
import Submission.Work.WilG0.Omega_cast

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG0

open WilkiesDesign

variable {S : SOMin}

/-! ## Monotonicity in the format and in the degree -/

theorem Omega_mono_F {F F' D n : ℕ} {X : Set (Fin n → ℝ)} (h : F ≤ F') (hX : X ∈ S.Ω F D n) :
    X ∈ S.Ω F' D n := by
  have key : ∀ k, X ∈ S.Ω F D n → X ∈ S.Ω (F + k) D n := by
    intro k
    induction k with
    | zero => intro hX; exact hX
    | succ k ih => intro hX; exact S.mono_F (ih hX)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact key k hX

theorem Omega_mono_D {F D D' n : ℕ} {X : Set (Fin n → ℝ)} (h : D ≤ D') (hX : X ∈ S.Ω F D n) :
    X ∈ S.Ω F D' n := by
  have key : ∀ k, X ∈ S.Ω F D n → X ∈ S.Ω F (D + k) n := by
    intro k
    induction k with
    | zero => intro hX; exact hX
    | succ k ih => intro hX; exact S.mono_D (ih hX)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact key k hX

theorem Omega_mono_FD {F F' D D' n : ℕ} {X : Set (Fin n → ℝ)} (hF : F ≤ F') (hD : D ≤ D')
    (hX : X ∈ S.Ω F D n) : X ∈ S.Ω F' D' n :=
  Omega_mono_D hD (Omega_mono_F hF hX)

/-! ## Transport along an equality of dimensions -/

/-- Membership in the transport of a set along `h : a = b`: the two index types are
identified by `Fin.cast`, which preserves the underlying value. -/
theorem cast_mem_iff {a b : ℕ} (h : a = b) {X : Set (Fin a → ℝ)} (z : Fin b → ℝ) :
    z ∈ (h ▸ X) ↔ (fun i : Fin a => z (Fin.cast h i)) ∈ X := by
  subst h
  rfl

/-! ## Binary operations -/

theorem iInter_fin_two {α : Type*} (A : Fin 2 → Set α) : (⋂ i, A i) = A 0 ∩ A 1 := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_iInter, Fin.forall_fin_two]

theorem iUnion_fin_two {α : Type*} (A : Fin 2 → Set α) : (⋃ i, A i) = A 0 ∪ A 1 := by
  ext x
  simp only [Set.mem_union, Set.mem_iUnion, Fin.exists_fin_two]

theorem Omega_inter2 {n F D₁ D₂ : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : A ∈ S.Ω F D₁ n) (hB : B ∈ S.Ω F D₂ n) :
    A ∩ B ∈ S.Ω (F + 1) (D₁ + D₂) n := by
  have h := S.inter (fun i : Fin 2 => ![D₁, D₂] i) (fun i : Fin 2 => ![A, B] i)
    (by intro i; fin_cases i
        · simpa using hA
        · simpa using hB)
  rw [iInter_fin_two] at h
  simpa [Fin.sum_univ_two] using h

theorem Omega_union2 {n F D₁ D₂ : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : A ∈ S.Ω F D₁ n) (hB : B ∈ S.Ω F D₂ n) :
    A ∪ B ∈ S.Ω F (D₁ + D₂) n := by
  have h := S.union (fun i : Fin 2 => ![D₁, D₂] i) (fun i : Fin 2 => ![A, B] i)
    (by intro i; fin_cases i
        · simpa using hA
        · simpa using hB)
  rw [iUnion_fin_two] at h
  simpa [Fin.sum_univ_two] using h

end Work.WilG0
