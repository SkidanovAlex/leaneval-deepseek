/-
  WilG0 — the substitution atom of the formula calculus.

  The `mem` atom of `OShape` is realized by `{x : ℝⁿ | x ∘ ι ∈ A}` for an Ω-set `A ⊆ ℝᵐ`.
  To code it we add `m` fresh coordinates `w`, impose `w = x ∘ ι` by the single polynomial
  equation `Σ_j (w_j - x_{ι j})² = 0` (degree two, the `+2` of the bookkeeping), require
  `w ∈ A` (a lift of `A`, giving format `F+n`), and project the fresh coordinates away
  (`m` projections, giving format `+m`).

  The only compositional subtlety is the order of the two coordinate blocks: `SOMin.prod_left`
  builds `Fin (m+n)` with `A` at the end, while `SOMin.proj` removes the *last* coordinates, so
  the surviving block must come first (`Fin (n+m)`).  `liftNM_eq_cast` bridges the two orders
  along `Nat.add_comm`, which costs nothing because `SOMin.Ω` is a function of the dimension.
-/
import Submission.Work.WilG0.API
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG0.projLastIter_mem
import Submission.Work.WilG0.snocIt_natAdd
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG0.liftNM_mem
import Submission.Work.WilG0.liftNM_eq_cast
import Submission.Work.WilG0.diagSet_mem

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG0

open WilkiesDesign

variable {S : SOMin}

/-- The two membership facts of the glued vector, in the two blocks. -/
theorem snocIt_mem_liftNM {m : ℕ} {A : Set (Fin m → ℝ)} (n : ℕ) (ι : Fin m → Fin n)
    (x : Fin n → ℝ) (w : Fin m → ℝ) :
    snocIt n m x w ∈ liftNM n m A ↔ w ∈ A := by
  rw [liftNM, Set.mem_setOf_eq]
  constructor
  · intro h
    rwa [show (fun j : Fin m => snocIt n m x w (Fin.natAdd n j)) = w from
      funext fun j => snocIt_natAdd n m x w j] at h
  · intro h
    rwa [show (fun j : Fin m => snocIt n m x w (Fin.natAdd n j)) = w from
      funext fun j => snocIt_natAdd n m x w j]

theorem snocIt_mem_diagSet {m : ℕ} (n : ℕ) (ι : Fin m → Fin n) (x : Fin n → ℝ)
    (w : Fin m → ℝ) :
    snocIt n m x w ∈ diagSet n m ι ↔ x ∘ ι = w := by
  rw [diagSet, Set.mem_setOf_eq]
  constructor
  · intro h
    funext j
    have h' := h j
    rw [snocIt_natAdd n m x w j, snocIt_castAdd n m x w (ι j)] at h'
    exact h'.symm
  · intro h j
    rw [snocIt_natAdd n m x w j, snocIt_castAdd n m x w (ι j)]
    exact congrFun h.symm j

/-- **The substitution atom.** If `A ⊆ ℝᵐ` is in `Ω F D`, then for every `ι : Fin m → Fin n`
the pullback `{x | x ∘ ι ∈ A}` is in `Ω (max (F+n) (n+m) + 1 + m + n) (D+2)`:
the `+2` is the diagonal equation, the format is the lift (`F+n`) or the diagonal
(`n+m`, from the hypersurface axiom), plus one for the intersection and `m` projections. -/
theorem substSet_mem {m F D : ℕ} {A : Set (Fin m → ℝ)} (hA : A ∈ S.Ω F D m)
    (n : ℕ) (ι : Fin m → Fin n) :
    {x : Fin n → ℝ | x ∘ ι ∈ A} ∈
      S.Ω (max (F + n) (n + m) + 1 + m + n) (D + 2) n := by
  have hL : liftNM n m A ∈ S.Ω (max (F + n) (n + m)) D (n + m) :=
    Omega_mono_F (le_max_left _ _) (liftNM_mem hA n)
  have hE : diagSet n m ι ∈ S.Ω (max (F + n) (n + m)) 2 (n + m) :=
    Omega_mono_F (le_max_right _ _) (diagSet_mem S n m ι)
  have hI : liftNM n m A ∩ diagSet n m ι ∈
      S.Ω (max (F + n) (n + m) + 1) (D + 2) (n + m) := Omega_inter2 hL hE
  have hP : projLastIter n m (liftNM n m A ∩ diagSet n m ι) ∈
      S.Ω (max (F + n) (n + m) + 1 + m + n) (D + 2) n :=
    projLastIter_mem S n m (max (F + n) (n + m) + 1) (D + 2) _ hI
  have hset : projLastIter n m (liftNM n m A ∩ diagSet n m ι) =
      {x : Fin n → ℝ | x ∘ ι ∈ A} := by
    rw [projLastIter_eq]
    ext x
    constructor
    · rintro ⟨w, hw⟩
      have h1 : w ∈ A := (snocIt_mem_liftNM n ι x w).mp hw.1
      have h2 : x ∘ ι = w := (snocIt_mem_diagSet n ι x w).mp hw.2
      show x ∘ ι ∈ A
      rw [h2]
      exact h1
    · intro hx
      refine ⟨x ∘ ι, ?_, ?_⟩
      · exact (snocIt_mem_liftNM n ι x (x ∘ ι)).mpr hx
      · exact (snocIt_mem_diagSet n ι x (x ∘ ι)).mpr rfl
  rw [hset] at hP
  exact hP

end Work.WilG0
