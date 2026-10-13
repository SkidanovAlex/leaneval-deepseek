import Mathlib
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4c.TSh
import Submission.Work.WilG5.Basic
import Submission.Work.WilCrux.TripleMem

/-!
# `Work.WilCruxN` — coordinate API for the N4d plumbing lemma `Work.WilCruxN.JointSetMem`

This module is the port of the (sorry-free) `Submission/Work/WilCrux/JointSetMem.lean` into the
clean namespace `Work.WilCruxN`: it carries the ambient-space coordinate maps, the coordinate
arithmetic for `Fin.append`/`Fin.snoc`, the reading of the graph atom `famGraph f`, and the
finite-conjunction shape `Qset` together with its `Ω`-membership proof `Qset_mem`.

`Work.WilCruxN.JointSetMem` imports this module and carries the shape calculus and the final
quantifier elimination.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilCruxN

open WilkiesDesign WilkiesDesign.CG
open Work.WilG4c

/-! ## 1. The coordinate maps -/

/-- Dimension of the innermost ambient space: `w, ε, δ` (that is `a+2` coordinates) together
with the block `(w', z, t)` of `a+b+1` coordinates. -/
abbrev D4 (a b : ℕ) : ℕ := (a + 2) + (a + b + 1)

/-- The `i`-th parameter coordinate `w_i`, at the level `a+2`. -/
def w2 {a : ℕ} (i : Fin a) : Fin (a + 2) := ⟨i, by omega⟩
/-- The `ε` coordinate, at the level `a+2`. -/
def e2 {a : ℕ} : Fin (a + 2) := ⟨a, by omega⟩
/-- The `δ` coordinate, at the level `a+2`. -/
def d2 {a : ℕ} : Fin (a + 2) := ⟨a + 1, by omega⟩

/-- The `i`-th parameter coordinate `w'_i` inside the block. -/
def wpB {a b : ℕ} (i : Fin a) : Fin (a + b + 1) := ⟨i, by omega⟩
/-- The `j`-th fibre coordinate `z_j` inside the block. -/
def zB {a b : ℕ} (j : Fin b) : Fin (a + b + 1) := ⟨a + j, by omega⟩
/-- The value coordinate `t` inside the block. -/
def tB {a b : ℕ} : Fin (a + b + 1) := ⟨a + b, by omega⟩

/-- `w_i` in the innermost ambient space. -/
def wc {a b : ℕ} (i : Fin a) : Fin (D4 a b) := Fin.castAdd (a + b + 1) (w2 i)
/-- `ε` in the innermost ambient space. -/
def ec {a b : ℕ} : Fin (D4 a b) := Fin.castAdd (a + b + 1) (e2 (a := a))
/-- `δ` in the innermost ambient space. -/
def dc {a b : ℕ} : Fin (D4 a b) := Fin.castAdd (a + b + 1) (d2 (a := a))
/-- `w'_i` in the innermost ambient space. -/
def wpc {a b : ℕ} (i : Fin a) : Fin (D4 a b) := Fin.natAdd (a + 2) (wpB i)
/-- `z_j` in the innermost ambient space. -/
def zc {a b : ℕ} (j : Fin b) : Fin (D4 a b) := Fin.natAdd (a + 2) (zB j)
/-- `t` in the innermost ambient space. -/
def tc {a b : ℕ} : Fin (D4 a b) := Fin.natAdd (a + 2) (tB (a := a) (b := b))
/-- The index map placing the block `(w',z,t)` into the innermost ambient space. -/
def iG {a b : ℕ} : Fin (a + b + 1) → Fin (D4 a b) := Fin.natAdd (a + 2)

/-! ## 2. Coordinate arithmetic -/

lemma tB_eq_last {a b : ℕ} : tB (a := a) (b := b) = Fin.last (a + b) := Fin.ext rfl

/-- The point `(w,ε,δ)` of the level `a+2`, written with `Fin.snoc`. -/
def ss {a : ℕ} (w : Fin a → ℝ) (ε δ : ℝ) : Fin (a + 2) → ℝ :=
  Fin.snoc (Fin.snoc (α := fun _ : Fin (a + 1) => ℝ) w ε) (α := fun _ : Fin (a + 2) => ℝ) δ

lemma ss_w2 {a : ℕ} (w : Fin a → ℝ) (ε δ : ℝ) (i : Fin a) : ss w ε δ (w2 i) = w i := by
  have h : w2 (a := a) i = (Fin.castSucc (Fin.castSucc i) : Fin (a + 2)) := Fin.ext rfl
  rw [ss, h, Fin.snoc_castSucc, Fin.snoc_castSucc]

lemma ss_e2 {a : ℕ} (w : Fin a → ℝ) (ε δ : ℝ) : ss w ε δ (e2 (a := a)) = ε := by
  have h : e2 (a := a) = (Fin.last a).castSucc := Fin.ext rfl
  rw [ss, h, Fin.snoc_castSucc, Fin.snoc_last]

lemma ss_d2 {a : ℕ} (w : Fin a → ℝ) (ε δ : ℝ) : ss w ε δ (d2 (a := a)) = δ := by
  have h : d2 (a := a) = Fin.last (a + 1) := Fin.ext rfl
  rw [ss, h, Fin.snoc_last]

lemma append_wc {a b : ℕ} (x : Fin (a + 2) → ℝ) (y : Fin (a + b + 1) → ℝ) (i : Fin a) :
    Fin.append x y (wc (a := a) (b := b) i) = x (w2 i) := by
  change Fin.append x y (Fin.castAdd (a + b + 1) (w2 i)) = x (w2 i)
  exact Fin.append_left _ _ _

lemma append_ec {a b : ℕ} (x : Fin (a + 2) → ℝ) (y : Fin (a + b + 1) → ℝ) :
    Fin.append x y (ec (a := a) (b := b)) = x (e2 (a := a)) := by
  change Fin.append x y (Fin.castAdd (a + b + 1) (e2 (a := a))) = x (e2 (a := a))
  exact Fin.append_left _ _ _

lemma append_dc {a b : ℕ} (x : Fin (a + 2) → ℝ) (y : Fin (a + b + 1) → ℝ) :
    Fin.append x y (dc (a := a) (b := b)) = x (d2 (a := a)) := by
  change Fin.append x y (Fin.castAdd (a + b + 1) (d2 (a := a))) = x (d2 (a := a))
  exact Fin.append_left _ _ _

lemma append_wpc {a b : ℕ} (x : Fin (a + 2) → ℝ) (y : Fin (a + b + 1) → ℝ) (i : Fin a) :
    Fin.append x y (wpc (a := a) (b := b) i) = y (wpB (b := b) i) := by
  change Fin.append x y (Fin.natAdd (a + 2) (wpB (b := b) i)) = y (wpB (b := b) i)
  exact Fin.append_right _ _ _

lemma append_zc {a b : ℕ} (x : Fin (a + 2) → ℝ) (y : Fin (a + b + 1) → ℝ) (j : Fin b) :
    Fin.append x y (zc (a := a) (b := b) j) = y (zB (a := a) j) := by
  change Fin.append x y (Fin.natAdd (a + 2) (zB (a := a) j)) = y (zB (a := a) j)
  exact Fin.append_right _ _ _

lemma append_tc {a b : ℕ} (x : Fin (a + 2) → ℝ) (y : Fin (a + b + 1) → ℝ) :
    Fin.append x y (tc (a := a) (b := b)) = y (tB (a := a) (b := b)) := by
  change Fin.append x y (Fin.natAdd (a + 2) (tB (a := a) (b := b))) = y (tB (a := a) (b := b))
  exact Fin.append_right _ _ _

lemma append_iG {a b : ℕ} (x : Fin (a + 2) → ℝ) (y : Fin (a + b + 1) → ℝ) :
    (Fin.append x y) ∘ (iG (a := a) (b := b)) = y := by
  funext k
  change Fin.append x y (Fin.natAdd (a + 2) k) = y k
  exact Fin.append_right _ _ _

lemma append_append_wpB {a b : ℕ} (w' : Fin a → ℝ) (z : Fin b → ℝ) (c : ℝ) (i : Fin a) :
    Fin.append (Fin.append w' z) (fun _ : Fin 1 => c) (wpB (b := b) i) = w' i := by
  change Fin.append (Fin.append w' z) (fun _ : Fin 1 => c)
      (Fin.castAdd 1 (Fin.castAdd b i)) = w' i
  rw [Fin.append_left, Fin.append_left]

lemma append_append_zB {a b : ℕ} (w' : Fin a → ℝ) (z : Fin b → ℝ) (c : ℝ) (j : Fin b) :
    Fin.append (Fin.append w' z) (fun _ : Fin 1 => c) (zB (a := a) j) = z j := by
  change Fin.append (Fin.append w' z) (fun _ : Fin 1 => c)
      (Fin.castAdd 1 (Fin.natAdd a j)) = z j
  rw [Fin.append_left, Fin.append_right]

lemma append_append_tB {a b : ℕ} (w' : Fin a → ℝ) (z : Fin b → ℝ) (c : ℝ) :
    Fin.append (Fin.append w' z) (fun _ : Fin 1 => c) (tB (a := a) (b := b)) = c := by
  change Fin.append (Fin.append w' z) (fun _ : Fin 1 => c)
      (Fin.natAdd (a + b) (0 : Fin 1)) = c
  exact Fin.append_right _ _ _

lemma init_append_append {a b : ℕ} (w' : Fin a → ℝ) (z : Fin b → ℝ) (c : ℝ) :
    Fin.init (Fin.append (Fin.append w' z) (fun _ : Fin 1 => c)) = Fin.append w' z := by
  funext k
  show Fin.append (Fin.append w' z) (fun _ : Fin 1 => c) (Fin.castAdd 1 k) =
    Fin.append w' z k
  exact Fin.append_left _ _ _

/-! ## 3. Reading the graph -/

lemma mem_famGraph_iff {a b : ℕ} (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (y : Fin (a + b + 1) → ℝ) :
    y ∈ famGraph f ↔ y (Fin.last (a + b)) = famFun f (Fin.init y) := by
  rw [← Work.WilG4c.graphOf_famFun, WilkiesDesign.graphOf, Set.mem_ofPred_eq]

lemma famFun_append {a b : ℕ} (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (w' : Fin a → ℝ) (z : Fin b → ℝ) :
    famFun f (Fin.append w' z) = f w' z := by
  have h1 : (fun i : Fin a => Fin.append w' z (Fin.castAdd b i)) = w' :=
    funext fun i => Fin.append_left _ _ _
  have h2 : (fun j : Fin b => Fin.append w' z (Fin.natAdd a j)) = z :=
    funext fun j => Fin.append_right _ _ _
  simp only [Work.WilG4c.famFun, h1, h2]

lemma famFun_init_coords {a b : ℕ} (f : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (y : Fin (a + b + 1) → ℝ) :
    famFun f (Fin.init y) = f (fun i : Fin a => y (wpB (b := b) i))
      (fun j : Fin b => y (zB (a := a) j)) := by
  have h1 : (fun i : Fin a => Fin.init y (Fin.castAdd b i)) =
      fun i : Fin a => y (wpB (b := b) i) :=
    funext fun i => congrArg y (Fin.ext rfl)
  have h2 : (fun j : Fin b => Fin.init y (Fin.natAdd a j)) =
      fun j : Fin b => y (zB (a := a) j) :=
    funext fun j => congrArg y (Fin.ext rfl)
  simp only [Work.WilG4c.famFun, h1, h2]

/-! ## 4. The shape -/

/-- The finite conjunction `∀ i, |w'_i - w_i| < δ ∧ z ≠ 0 ∧ ∀ j, |z_j| < δ` as a single
`Ω`-set in the ambient space `D4` (the value coordinate `t` is unused). -/
def Qset (a b : ℕ) : Set (Fin (D4 a b) → ℝ) :=
  {u | (∀ i : Fin a, |u (wpc i) - u (wc i)| < u (dc))
    ∧ (fun j : Fin b => u (zc j)) ≠ 0
    ∧ (∀ j : Fin b, |u (zc j)| < u (dc))}

lemma Qset_mem (S : SOMin) {a b : ℕ} :
    ∃ (A0 : ℕ) (q : Polynomial ℕ), ∀ D : ℕ, Qset a b ∈ S.Ω A0 (q.eval D) (D4 a b) := by
  obtain ⟨A0, q, h⟩ := Work.WilCrux.TripleMem (S := S) (N := D4 a b) (a := a) (b := b)
    (fun i => wpc i) (fun i => wc i) (fun j => zc j) (dc)
  exact ⟨A0, q, fun D => h D⟩

end Work.WilCruxN
