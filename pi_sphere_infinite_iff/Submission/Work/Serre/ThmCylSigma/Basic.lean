import Submission.Work.Serre.ThmCylSigma.Defs

/-!
# The cochain identities of the `σ`-type decomposition

`Work.Serre.Sigma.restr` (restriction to a piece) and `Work.Serre.Sigma.assemble` (assembly of a
family of cochains on the pieces) are inverse to each other, commute with the differentials and
with the Alexander–Whitney cup product.  This is the cochain-level form of the statement that the
singular cochain complex of a `σ`-type is the product of the cochain complexes of the pieces.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial Topology

namespace Work.Serre.Sigma

noncomputable section

variable {ι : Type} {Y : ι → Type} [∀ i, TopologicalSpace (Y i)]
variable {R : Type} [CommRing R]

/-! ## The value of an assembly at faces -/

/-- The value of an assembly at a face of a simplex, with the splitting of the face computed. -/
theorem genEval_assemble_δ (n : ℕ) (w : ∀ i, Work.Cohomology.Cochain R (Spiece ι Y i) n)
    (σ : (Ssig ι Y) _⦋n + 1⦌) (j : Fin (n + 2)) :
    Work.Cohomology.genEval R (Ssig ι Y) (assemble R n w) ((Ssig ι Y).δ j σ) =
      Work.Cohomology.genEval R (Spiece ι Y (split (Y := Y) (n + 1) σ).1)
        (w (split (Y := Y) (n + 1) σ).1)
        ((Spiece ι Y (split (Y := Y) (n + 1) σ).1).δ j (split (Y := Y) (n + 1) σ).2) := by
  rw [genEval_assemble (ι := ι) (Y := Y)]
  exact congrArg (fun p : Σ i, (Spiece ι Y i) _⦋n⦌ =>
    Work.Cohomology.genEval R (Spiece ι Y p.1) (w p.1) p.2) (split_δ (ι := ι) (Y := Y) n j σ)

/-- The value of an assembly at the front face of a simplex, with the splitting computed. -/
theorem genEval_assemble_frontFace (n m : ℕ)
    (c : ∀ i, Work.Cohomology.Cochain R (Spiece ι Y i) n) (σ : (Ssig ι Y) _⦋n + m⦌) :
    Work.Cohomology.genEval R (Ssig ι Y) (assemble R n c)
        (Work.Cohomology.frontFace (Ssig ι Y) n (n + m) (Nat.le_add_right n m) σ) =
      Work.Cohomology.genEval R (Spiece ι Y (split (Y := Y) (n + m) σ).1)
        (c (split (Y := Y) (n + m) σ).1)
        (Work.Cohomology.frontFace (Spiece ι Y (split (Y := Y) (n + m) σ).1) n (n + m)
          (Nat.le_add_right n m) (split (Y := Y) (n + m) σ).2) := by
  rw [genEval_assemble (ι := ι) (Y := Y)]
  exact congrArg (fun p : Σ i, (Spiece ι Y i) _⦋n⦌ =>
    Work.Cohomology.genEval R (Spiece ι Y p.1) (c p.1) p.2)
    (split_frontFace (ι := ι) (Y := Y) n m σ)

/-- The value of an assembly at the back face of a simplex, with the splitting computed. -/
theorem genEval_assemble_backFace (n m : ℕ)
    (c : ∀ i, Work.Cohomology.Cochain R (Spiece ι Y i) m) (σ : (Ssig ι Y) _⦋n + m⦌) :
    Work.Cohomology.genEval R (Ssig ι Y) (assemble R m c)
        (Work.Cohomology.backFace (Ssig ι Y) n m σ) =
      Work.Cohomology.genEval R (Spiece ι Y (split (Y := Y) (n + m) σ).1)
        (c (split (Y := Y) (n + m) σ).1)
        (Work.Cohomology.backFace (Spiece ι Y (split (Y := Y) (n + m) σ).1) n m
          (split (Y := Y) (n + m) σ).2) := by
  rw [genEval_assemble (ι := ι) (Y := Y)]
  exact congrArg (fun p : Σ i, (Spiece ι Y i) _⦋m⦌ =>
    Work.Cohomology.genEval R (Spiece ι Y p.1) (c p.1) p.2)
    (split_backFace (ι := ι) (Y := Y) n m σ)

/-! ## The two maps are inverse to each other -/

/-- **The assembly is a right inverse of the restriction.** -/
theorem restr_assemble (n : ℕ) (w : ∀ i, Work.Cohomology.Cochain R (Spiece ι Y i) n) (j : ι) :
    restr R j n (assemble R n w) = w j := by
  apply Work.Cohomology.genEval_ext
  intro s
  rw [genEval_restr (ι := ι) (Y := Y)]
  rw [genEval_assemble (ι := ι) (Y := Y)]
  exact congrArg (fun p : Σ i, (Spiece ι Y i) _⦋n⦌ =>
    Work.Cohomology.genEval R (Spiece ι Y p.1) (w p.1) p.2)
    (split_pieceIncl (ι := ι) (Y := Y) n j s)

/-- **The assembly is a left inverse of the restriction.** -/
theorem assemble_restr (n : ℕ) (β : Work.Cohomology.Cochain R (Ssig ι Y) n) :
    assemble R n (fun j => restr R j n β) = β := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [genEval_assemble (ι := ι) (Y := Y)]
  rw [genEval_restr (ι := ι) (Y := Y)]
  exact congrArg (fun σ' : (Ssig ι Y) _⦋n⦌ => Work.Cohomology.genEval R (Ssig ι Y) β σ')
    (legs_split (ι := ι) (Y := Y) n σ)

/-! ## Linearity of the assembly -/

theorem assemble_add (n : ℕ) (w w' : ∀ i, Work.Cohomology.Cochain R (Spiece ι Y i) n) :
    assemble R n (fun i => w i + w' i) = assemble R n w + assemble R n w' := by
  apply Work.Cohomology.genEval_ext
  intro σ
  simp only [genEval_assemble (ι := ι) (Y := Y), Work.Cohomology.genEval_add]

theorem assemble_smul (a : R) (n : ℕ) (w : ∀ i, Work.Cohomology.Cochain R (Spiece ι Y i) n) :
    assemble R n (fun i => a • w i) = a • assemble R n w := by
  apply Work.Cohomology.genEval_ext
  intro σ
  simp only [genEval_assemble (ι := ι) (Y := Y), Work.Cohomology.genEval_smul]

theorem assemble_neg (n : ℕ) (w : ∀ i, Work.Cohomology.Cochain R (Spiece ι Y i) n) :
    assemble R n (fun i => - w i) = - assemble R n w := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [genEval_assemble (ι := ι) (Y := Y)]
  rw [show Work.Cohomology.genEval R (Ssig ι Y) (- assemble R n w) σ
      = - Work.Cohomology.genEval R (Ssig ι Y) (assemble R n w) σ from rfl]
  rw [genEval_assemble (ι := ι) (Y := Y)]
  simp only [Work.Cohomology.genEval, LinearMap.neg_apply]

theorem assemble_sub (n : ℕ) (w w' : ∀ i, Work.Cohomology.Cochain R (Spiece ι Y i) n) :
    assemble R n (fun i => w i - w' i) = assemble R n w - assemble R n w' := by
  have h1 : (fun i => w i - w' i) = (fun i => w i + (- w' i)) := by
    funext i
    rw [sub_eq_add_neg]
  rw [h1, assemble_add, assemble_neg, sub_eq_add_neg]

/-! ## Compatibility with the differentials -/

/-- **The assembly commutes with the coboundary**, componentwise. -/
theorem cochainDiff_assemble (n : ℕ) (w : ∀ i, Work.Cohomology.Cochain R (Spiece ι Y i) n) :
    Work.Cohomology.cochainDiff R (Ssig ι Y) (assemble R n w) =
      assemble R (n + 1) (fun i => Work.Cohomology.cochainDiff R (Spiece ι Y i) (w i)) := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Cohomology.genEval_cochainDiff]
  simp only [genEval_assemble_δ (ι := ι) (Y := Y)]
  rw [genEval_assemble (ι := ι) (Y := Y)]
  rw [Work.Cohomology.genEval_cochainDiff]

/-- **The restriction commutes with the coboundary.** -/
theorem cochainDiff_restr (n : ℕ) (i : ι) (β : Work.Cohomology.Cochain R (Ssig ι Y) n) :
    Work.Cohomology.cochainDiff R (Spiece ι Y i) (restr R i n β) =
      restr R i (n + 1) (Work.Cohomology.cochainDiff R (Ssig ι Y) β) := by
  apply Work.Cohomology.genEval_ext
  intro s
  rw [Work.Cohomology.genEval_cochainDiff]
  simp only [genEval_restr (ι := ι) (Y := Y)]
  rw [Work.Cohomology.genEval_cochainDiff]
  simp only [legs_δ (ι := ι) (Y := Y)]

/-! ## Compatibility with the cup product -/

/-- **The assembly is multiplicative**, componentwise. -/
theorem cup_assemble (n m : ℕ) (c : ∀ i, Work.Cohomology.Cochain R (Spiece ι Y i) n)
    (d : ∀ i, Work.Cohomology.Cochain R (Spiece ι Y i) m) :
    Work.Cohomology.cup R (Ssig ι Y) (assemble R n c) (assemble R m d) =
      assemble R (n + m) (fun i => Work.Cohomology.cup R (Spiece ι Y i) (c i) (d i)) := by
  apply Work.Cohomology.genEval_ext
  intro σ
  rw [Work.Cohomology.cup_apply]
  simp only [genEval_assemble_frontFace (ι := ι) (Y := Y),
    genEval_assemble_backFace (ι := ι) (Y := Y)]
  rw [genEval_assemble (ι := ι) (Y := Y)]
  rw [← Work.Cohomology.cup_apply]

/-- **The restriction is multiplicative.** -/
theorem cup_restr (n m : ℕ) (i : ι) (α : Work.Cohomology.Cochain R (Ssig ι Y) n)
    (β : Work.Cohomology.Cochain R (Ssig ι Y) m) :
    restr R i (n + m) (Work.Cohomology.cup R (Ssig ι Y) α β) =
      Work.Cohomology.cup R (Spiece ι Y i) (restr R i n α) (restr R i m β) := by
  apply Work.Cohomology.genEval_ext
  intro s
  rw [genEval_restr (ι := ι) (Y := Y)]
  rw [Work.Cohomology.cup_apply]
  rw [legs_frontFace (ι := ι) (Y := Y)]
  rw [legs_backFace (ι := ι) (Y := Y)]
  rw [← genEval_restr (ι := ι) (Y := Y)]
  rw [← genEval_restr (ι := ι) (Y := Y)]
  rw [← Work.Cohomology.cup_apply]

end

end Work.Serre.Sigma
