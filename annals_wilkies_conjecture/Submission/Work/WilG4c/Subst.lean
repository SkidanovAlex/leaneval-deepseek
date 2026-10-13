import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG0.Defs
import Submission.Work.WilG0.API
import Submission.Work.WilG0.snocIt_castAdd
import Submission.Work.WilG0.snocIt_natAdd
import Submission.Work.WilG0.projLastIter_eq
import Submission.Work.WilG0.diagSet_mem

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign Work.WilG0

variable {S : SOMin}

/-! ### Elementary facts about `Fin.addNat` and `Fin.natAdd` -/

/-- `Fin.addNat j 0` is `j` (the ambient dimension `n + 0` is definitionally `n`). -/
theorem addNat_zero {n : ℕ} (j : Fin n) : (Fin.addNat j 0 : Fin (n + 0)) = j :=
  Fin.ext (by simp [Fin.addNat])

/-- `Fin.succ` commutes with `Fin.addNat`: the successor of `j + m` is `j + (m+1)`. -/
theorem addNat_succ {n : ℕ} (j : Fin n) (m : ℕ) :
    (Fin.addNat j m).succ = (Fin.addNat j (m + 1) : Fin (n + (m + 1))) :=
  Fin.ext (by simp only [Fin.val_succ, Fin.addNat, Fin.val_mk]; omega)

/-! ### The two-block membership facts for the glue map `snocIt` -/

/-- On the glued vector `snocIt n m x w`, membership of the trailing `m`-block in `liftNM`
is exactly membership of `w`. -/
theorem snocIt_mem_liftNM_aux {m : ℕ} {A : Set (Fin m → ℝ)} (n : ℕ) (ι : Fin m → Fin n)
    (x : Fin n → ℝ) (w : Fin m → ℝ) :
    snocIt n m x w ∈ liftNM n m A ↔ w ∈ A := by
  rw [liftNM, Set.mem_ofPred_eq]
  constructor
  · intro h
    rwa [show (fun j : Fin m => snocIt n m x w (Fin.natAdd n j)) = w from
      funext fun j => snocIt_natAdd n m x w j] at h
  · intro h
    rwa [show (fun j : Fin m => snocIt n m x w (Fin.natAdd n j)) = w from
      funext fun j => snocIt_natAdd n m x w j]

/-- On the glued vector `snocIt n m x w`, membership in `diagSet n m ι` is the equation
`x ∘ ι = w`. -/
theorem snocIt_mem_diagSet_aux {m : ℕ} (n : ℕ) (ι : Fin m → Fin n) (x : Fin n → ℝ)
    (w : Fin m → ℝ) :
    snocIt n m x w ∈ diagSet n m ι ↔ x ∘ ι = w := by
  rw [diagSet, Set.mem_ofPred_eq]
  constructor
  · intro h
    funext j
    have h' := h j
    rw [snocIt_natAdd n m x w j, snocIt_castAdd n m x w (ι j)] at h'
    exact h'.symm
  · intro h j
    rw [snocIt_natAdd n m x w j, snocIt_castAdd n m x w (ι j)]
    exact congrFun h.symm j

/-! ### The `prod_left` iteration: `liftMN` -/

/-- `liftMN 0 n X` is `X` (the ambient dimensions `n + 0` and `n` agree definitionally). -/
theorem liftMN_zero_eq {n : ℕ} (X : Set (Fin n → ℝ)) : liftMN 0 n X = X := by
  ext z
  simp only [liftMN, Set.mem_ofPred_eq]
  have h : (fun j : Fin n => z (Fin.addNat j 0)) = z := by
    funext j
    rw [addNat_zero j]
  rw [h]

/-- One more `prod_left` step: `liftMN (m+1)` is the `Fin.tail`-preimage of `liftMN m`. -/
theorem liftMN_succ_eq {n : ℕ} (X : Set (Fin n → ℝ)) (m : ℕ) :
    liftMN (m + 1) n X = {z : Fin (n + (m + 1)) → ℝ | Fin.tail z ∈ liftMN m n X} := by
  ext z
  show (fun j : Fin n => z (Fin.addNat j (m + 1))) ∈ X ↔
      (fun j : Fin n => Fin.tail z (Fin.addNat j m)) ∈ X
  have h : (fun j : Fin n => Fin.tail z (Fin.addNat j m)) =
      (fun j : Fin n => z (Fin.addNat j (m + 1))) := by
    funext j
    simp only [Fin.tail, addNat_succ]
  rw [h]

/-- Iterating `SOMin.prod_left` puts `X` on the trailing `n` coordinates: `liftMN n m X` is in
`Ω (F + n) D (m + n)`. -/
theorem liftMN_iter_mem {n : ℕ} {X : Set (Fin n → ℝ)} {F D : ℕ} (hX : X ∈ S.Ω F D n) :
    ∀ m, liftMN m n X ∈ S.Ω (F + m) D (n + m) := by
  intro m
  induction m with
  | zero =>
      rw [liftMN_zero_eq]
      simpa using hX
  | succ m ih =>
      have h2 : {z : Fin (n + (m + 1)) → ℝ | Fin.tail z ∈ liftMN m n X} ∈
          S.Ω (F + (m + 1)) D (n + (m + 1)) := S.prod_left ih
      rw [← liftMN_succ_eq X m] at h2
      exact h2

/-! ### Bridging the two orders `Fin (m+n)` and `Fin (n+m)` -/

/-- `liftNM` is the transport of `liftMN` along `Nat.add_comm`. -/
theorem liftNM_cast_eq {n m : ℕ} (A : Set (Fin m → ℝ)) :
    liftNM n m A = (Nat.add_comm m n) ▸ liftMN n m A := by
  ext z
  rw [Work.WilG0.cast_mem_iff]
  simp only [liftMN, liftNM, Set.mem_ofPred_eq]
  have h : (fun j : Fin m => z (Fin.cast (Nat.add_comm m n) (Fin.addNat j n))) =
      (fun j : Fin m => z (Fin.natAdd n j)) := by
    funext j
    congr 1
    exact Fin.ext (by simp [Fin.addNat, Fin.natAdd, Fin.cast, Nat.add_comm])
  rw [h]

/-- The same statement for `liftNM`, obtained by transporting the `liftMN` version. -/
theorem liftNM_iter_mem {m : ℕ} {A : Set (Fin m → ℝ)} {F D : ℕ} (hA : A ∈ S.Ω F D m) (n : ℕ) :
    liftNM n m A ∈ S.Ω (F + n) D (n + m) := by
  have h := Work.WilG0.Omega_cast (S := S) (Nat.add_comm m n)
    (liftMN_iter_mem (S := S) hA n)
  rwa [← liftNM_cast_eq (n := n) (m := m) A] at h

/-! ### The projection iteration -/

/-- Iterating `SOMin.proj` (the tight format bound `F + m`). -/
theorem projIter_mem {n m F D : ℕ} {X : Set (Fin (n + m) → ℝ)}
    (hX : X ∈ S.Ω F D (n + m)) : projLastIter n m X ∈ S.Ω (F + m) D n := by
  have key : ∀ m (F D : ℕ) (X : Set (Fin (n + m) → ℝ)),
      X ∈ S.Ω F D (n + m) → projLastIter n m X ∈ S.Ω (F + m) D n := by
    intro m
    induction m with
    | zero =>
        intro F D X hX
        simpa [projLastIter] using hX
    | succ m ih =>
        intro F D X hX
        have hX' : projLast X ∈ S.Ω (F + 1) D (n + m) := S.proj hX
        have hres : projLastIter n m (projLast X) ∈ S.Ω ((F + 1) + m) D n :=
          ih (F + 1) D (projLast X) hX'
        have heq : (F + 1) + m = F + (m + 1) := by omega
        change projLastIter n m (projLast X) ∈ S.Ω (F + (m + 1)) D n
        exact heq ▸ hres
  exact key m F D X hX

/-! ### The projection of the glued set -/

/-- Projecting the trailing `n` coordinates of `liftNM m n X ∩ diagSet m n σ` is the
substitution set `{z | z ∘ σ ∈ X}`. -/
theorem substSnocSet_eq {n m : ℕ} (X : Set (Fin n → ℝ)) (σ : Fin n → Fin m) :
    {z : Fin m → ℝ | ∃ w : Fin n → ℝ, snocIt m n z w ∈ liftNM m n X ∩ diagSet m n σ}
      = {z : Fin m → ℝ | z ∘ σ ∈ X} := by
  ext z
  constructor
  · rintro ⟨w, hw⟩
    have h1 : w ∈ X := (snocIt_mem_liftNM_aux (A := X) m σ z w).mp hw.1
    have h2 : z ∘ σ = w := (snocIt_mem_diagSet_aux m σ z w).mp hw.2
    show z ∘ σ ∈ X
    rw [h2]
    exact h1
  · intro hx
    exact ⟨z ∘ σ, (snocIt_mem_liftNM_aux (A := X) m σ z (z ∘ σ)).mpr hx,
      (snocIt_mem_diagSet_aux m σ z (z ∘ σ)).mpr rfl⟩

/-! ### Assembly -/

/-- **Ω is closed under coordinate substitution.**  If `X ⊆ ℝ^n` is `Ω F D n` and
`σ : Fin n → Fin m`, then `{z : Fin m → ℝ | z ∘ σ ∈ X}` is `Ω (…) (D + 2) m`.
Construction: put `n` fresh coordinates `w` as the trailing block of `ℝ^{m+n}`, put `X` on
that block (iterate `SOMin.prod_left`), impose the single hypersurface
`Σ_{i:Fin n} (Z_{m+i} − Z_{σ i})² = 0` (degree `2`, the `+2` of BNZ's substitution atom), and
project the `w`-block away (iterate `SOMin.proj`).  Only `prod_left`, `hyp`, `inter`, `proj`
and `mono_F`/`mono_D` are used.  `Work.WilG1.Basic` has reusable helpers (`inter_mem`,
`projLast_mem`, `prodLeft_mem`, `hyp_mem`, `coordEq_mem`, `mono`). -/
theorem Subst (S : SOMin) {n m F D : ℕ} (σ : Fin n → Fin m) {X : Set (Fin n → ℝ)}
    (hX : X ∈ S.Ω F D n) :
    {z : Fin m → ℝ | z ∘ σ ∈ X} ∈ S.Ω (max (F + m) (m + n) + 1 + n) (D + 2) m := by
  have hA : liftNM m n X ∈ S.Ω (F + m) D (m + n) := liftNM_iter_mem (S := S) hX m
  have hB : diagSet m n σ ∈ S.Ω (m + n) 2 (m + n) := diagSet_mem S m n σ
  have hA' : liftNM m n X ∈ S.Ω (max (F + m) (m + n)) D (m + n) :=
    Omega_mono_F (le_max_left _ _) hA
  have hB' : diagSet m n σ ∈ S.Ω (max (F + m) (m + n)) 2 (m + n) :=
    Omega_mono_F (le_max_right _ _) hB
  have hI : liftNM m n X ∩ diagSet m n σ ∈
      S.Ω (max (F + m) (m + n) + 1) (D + 2) (m + n) :=
    Omega_inter2 hA' hB'
  have hP : projLastIter m n (liftNM m n X ∩ diagSet m n σ) ∈
      S.Ω (max (F + m) (m + n) + 1 + n) (D + 2) m :=
    projIter_mem (S := S) hI
  have hset : projLastIter m n (liftNM m n X ∩ diagSet m n σ) =
      {z : Fin m → ℝ | z ∘ σ ∈ X} := by
    rw [projLastIter_eq]
    exact substSnocSet_eq X σ
  rw [hset] at hP
  exact hP

end Work.WilG4c
