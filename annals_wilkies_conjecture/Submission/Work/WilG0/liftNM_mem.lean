/-
  WilG0 — `liftNM n m A`: the set coding "prepend `n` free coordinates in front of a `D`-block",
  obtained from `A ∈ S.Ω F D m` by iterating the axiom `SOMin.prod_left`.

  Strategy: `SOMin.prod_left` prepends one *free* coordinate at the front (a `Fin.tail`
  preimage), which is exactly the operation that keeps the `D`-block at the end and adds a
  coordinate in front.  Iterating it `n` times on `A` lands in dimension `m + n`; the
  `Ω`-membership is transported to the index order `n + m` along `Nat.add_comm`.
-/
import Mathlib
import Submission.Work.WilG0.Defs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG0

open WilkiesDesign

/-- Membership in the transport of a set along an equality of dimensions: the two ambient
index types are identified by `Fin.cast`, which preserves the underlying value. -/
private theorem liftNM_cast_mem_iff {a b : ℕ} (h : a = b) {X : Set (Fin a → ℝ)}
    (z : Fin b → ℝ) : z ∈ (h ▸ X) ↔ (fun i : Fin a => z (Fin.cast h i)) ∈ X := by
  subst h
  rfl

/-- `Fin.cast` of `Fin.addNat` is `Fin.natAdd`: the two ways of adding a shift index agree. -/
private theorem cast_addNat_eq_natAdd (n m : ℕ) (j : Fin m) :
    Fin.cast (Nat.add_comm m n) (Fin.addNat j n) = Fin.natAdd n j := by
  ext
  simp only [Fin.val_cast, Fin.val_addNat, Fin.val_natAdd]
  exact Nat.add_comm _ _

/-- Iterating `SOMin.prod_left` `n` times prepends `n` free coordinates to `A`, producing a
set in dimension `m + n` (the `D`-block sits in the last `m` coordinates). -/
private theorem liftMN_mem_aux {S : SOMin} {m F D : ℕ} {A : Set (Fin m → ℝ)}
    (hA : A ∈ S.Ω F D m) (n : ℕ) : liftMN n m A ∈ S.Ω (F + n) D (m + n) := by
  induction n with
  | zero =>
    have h0 : liftMN 0 m A = A := by ext z; simp [liftMN]
    rw [h0]
    simpa using hA
  | succ n ih =>
    -- `liftMN (n+1) m A` is the `Fin.tail`-preimage of `liftMN n m A`
    have hz : liftMN (n+1) m A
        = {z : Fin (m+(n+1)) → ℝ | Fin.tail z ∈ liftMN n m A} := by
      apply Set.ext
      intro z
      have hfun : (fun j : Fin m => (Fin.tail z) (Fin.addNat j n))
          = (fun j : Fin m => z (Fin.addNat j (n+1))) := by
        funext j; rfl
      show ((fun j : Fin m => z (Fin.addNat j (n+1))) ∈ A) ↔
           ((fun j : Fin m => (Fin.tail z) (Fin.addNat j n)) ∈ A)
      rw [hfun]
    rw [hz]
    exact S.prod_left ih

/-- Transport of `liftMN` to the index order `n + m` used by `liftNM`. -/
private theorem liftNM_eq_liftMN_cast (n m : ℕ) (A : Set (Fin m → ℝ)) :
    liftNM n m A = (Nat.add_comm m n) ▸ liftMN n m A := by
  apply Set.ext
  intro z
  rw [liftNM_cast_mem_iff]
  simp only [liftNM, liftMN, Set.mem_ofPred_eq]
  have hfun : (fun j : Fin m => z (Fin.cast (Nat.add_comm m n) (Fin.addNat j n)))
      = (fun j : Fin m => z (Fin.natAdd n j)) := by
    funext j
    rw [cast_addNat_eq_natAdd]
  rw [hfun]

/-- Transport of an `Ω`-set along an equality of dimensions. -/
private theorem Omega_cast_mem {S : SOMin} {a b F D : ℕ} (h : a = b) {X : Set (Fin a → ℝ)}
    (hX : X ∈ S.Ω F D a) : (h ▸ X) ∈ S.Ω F D b := by
  subst h; exact hX

theorem liftNM_mem {S : WilkiesDesign.SOMin} {m F D : ℕ} {A : Set (Fin m → ℝ)} (hA : A ∈ S.Ω F D m) (n : ℕ) :
    liftNM n m A ∈ S.Ω (F + n) D (n + m) := by
  have h1 : liftMN n m A ∈ S.Ω (F + n) D (m + n) := liftMN_mem_aux hA n
  have h2 : (Nat.add_comm m n) ▸ liftMN n m A ∈ S.Ω (F + n) D (n + m) :=
    Omega_cast_mem (Nat.add_comm m n) h1
  rwa [← liftNM_eq_liftMN_cast n m A] at h2

end Work.WilG0
