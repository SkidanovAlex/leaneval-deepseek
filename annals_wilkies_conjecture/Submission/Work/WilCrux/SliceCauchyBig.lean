/-
  WilCrux — the big-space construction behind `Work.WilCrux.sliceCauchy_mem`.

  The set `sliceCauchySet G j k ε ⊆ ℝ^a` is exhibited as the projection (away from a big
  ambient space `ℝ^N`, `N = ((a+1) + (b+b)) + 2`) of the intersection/complement of a handful
  of `Ω`-sets built from the derivative graph `derivGraph (famFun G) (Fin.natAdd a j)`.

  Coordinates of the big space `ℝ^N` are read as `(w, η, z, z', y, y')`:
    * `w : Fin a` in the first block `Fin.castAdd 2 (Fin.castAdd (b+b) (Fin.castAdd 1 ·))`;
    * `η : ℝ` at `etaIx`;
    * `z : Fin b` at `zIx`;
    * `z' : Fin b` at `zIx'`;
    * the last two coordinates are `y` (`yIx`) and `y'` (`yIx'`).

  The outermost block structure is `Fin.append (Fin.append (Fin.append w η) (Fin.append z z')) yy`
  with `w : Fin a → ℝ`, `η : Fin 1 → ℝ`, `z z' : Fin b → ℝ`, `yy : Fin 2 → ℝ`, which makes the
  successive projections `projN 2`, `projN (b+b)`, `projN 1` line up with the block sizes.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4b.Basic
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG5.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section
open Classical

namespace Work.WilCrux

open WilkiesDesign

variable {a b : ℕ}

/-! ## The big-space coordinate indices -/

/-- `wIx i` is the `i`-th `w`-coordinate of the big space `ℝ^{((a+1)+(b+b))+2}`. -/
def wIx (i : Fin a) : Fin (((a + 1) + (b + b)) + 2) :=
  Fin.castAdd 2 (Fin.castAdd (b + b) (Fin.castAdd 1 i))

/-- The `η`-coordinate of the big space. -/
def etaIx : Fin (((a + 1) + (b + b)) + 2) :=
  Fin.castAdd 2 (Fin.castAdd (b + b) (Fin.natAdd a (0 : Fin 1)))

/-- `zIx j` is the `j`-th `z`-coordinate of the big space. -/
def zIx (j : Fin b) : Fin (((a + 1) + (b + b)) + 2) :=
  Fin.castAdd 2 (Fin.natAdd (a + 1) (Fin.castAdd b j))

/-- `zIx' j` is the `j`-th `z'`-coordinate of the big space. -/
def zIx' (j : Fin b) : Fin (((a + 1) + (b + b)) + 2) :=
  Fin.castAdd 2 (Fin.natAdd (a + 1) (Fin.natAdd b j))

/-- The `y`-coordinate (second to last) of the big space. -/
def yIx : Fin (((a + 1) + (b + b)) + 2) :=
  Fin.natAdd ((a + 1) + (b + b)) (0 : Fin 2)

/-- The `y'`-coordinate (last) of the big space. -/
def yIx' : Fin (((a + 1) + (b + b)) + 2) :=
  Fin.natAdd ((a + 1) + (b + b)) (1 : Fin 2)

/-- The reindexing `e1 : Fin (a+b+1) → Fin N` reading the parameter block `w`, the fibre
block `z` and the value coordinate `y` of the big space as the coordinates of the derivative
graph space `ℝ^{a+b+1}`. -/
def e1 : Fin ((a + b) + 1) → Fin (((a + 1) + (b + b)) + 2) :=
  Fin.append (Fin.append wIx zIx) (fun _ : Fin 1 => yIx)

/-- As `e1` but reading the `z'` block and the value coordinate `y'`. -/
def e2 : Fin ((a + b) + 1) → Fin (((a + 1) + (b + b)) + 2) :=
  Fin.append (Fin.append wIx zIx') (fun _ : Fin 1 => yIx')

/-! ## A canonical point of the big space -/

/-- The canonical point of the big space with block decomposition
`(w, η, z, z', (y, y'))`, written in the `Fin.append` shape produced by the projections. -/
def pt (w : Fin a → ℝ) (η : Fin 1 → ℝ) (q : Fin (b + b) → ℝ) (yy : Fin 2 → ℝ) :
    Fin (((a + 1) + (b + b)) + 2) → ℝ :=
  Fin.append (Fin.append (Fin.append w η) q) yy

/-- Reassembly: any big point is the `Fin.append`-decomposition of its blocks. -/
theorem pt_eta_ext (w : Fin a → ℝ) (η : Fin 1 → ℝ) (q : Fin (b + b) → ℝ) (yy : Fin 2 → ℝ) :
    pt w η q yy
      = Fin.append (Fin.append (Fin.append w η) q) yy := rfl

@[simp] theorem pt_wIx (w : Fin a → ℝ) (η : Fin 1 → ℝ) (q : Fin (b + b) → ℝ)
    (yy : Fin 2 → ℝ) (i : Fin a) : pt w η q yy (wIx i) = w i := by
  simp only [pt, wIx, Fin.append_left, Fin.append_right]

@[simp] theorem pt_etaIx (w : Fin a → ℝ) (η : Fin 1 → ℝ) (q : Fin (b + b) → ℝ)
    (yy : Fin 2 → ℝ) : pt w η q yy etaIx = η 0 := by
  simp only [pt, etaIx, Fin.append_left, Fin.append_right]

@[simp] theorem pt_zIx (w : Fin a → ℝ) (η : Fin 1 → ℝ) (q : Fin (b + b) → ℝ)
    (yy : Fin 2 → ℝ) (j : Fin b) : pt w η q yy (zIx j) = q (Fin.castAdd b j) := by
  simp only [pt, zIx, Fin.append_left, Fin.append_right]

@[simp] theorem pt_zIx' (w : Fin a → ℝ) (η : Fin 1 → ℝ) (q : Fin (b + b) → ℝ)
    (yy : Fin 2 → ℝ) (j : Fin b) : pt w η q yy (zIx' j) = q (Fin.natAdd b j) := by
  simp only [pt, zIx', Fin.append_left, Fin.append_right]

@[simp] theorem pt_yIx (w : Fin a → ℝ) (η : Fin 1 → ℝ) (q : Fin (b + b) → ℝ)
    (yy : Fin 2 → ℝ) : pt w η q yy yIx = yy 0 := by
  simp only [pt, yIx, Fin.append_right]

@[simp] theorem pt_yIx' (w : Fin a → ℝ) (η : Fin 1 → ℝ) (q : Fin (b + b) → ℝ)
    (yy : Fin 2 → ℝ) : pt w η q yy yIx' = yy 1 := by
  simp only [pt, yIx', Fin.append_right]

/-! ## Basic block lemmas -/

/-- Composition distributes over `Fin.append`. -/
theorem comp_append {m n : ℕ} {α β : Type*} (u : α → β) (f : Fin m → α) (g : Fin n → α) :
    u ∘ Fin.append f g = Fin.append (u ∘ f) (u ∘ g) := by
  funext i
  refine Fin.addCases
    (motive := fun i => u (Fin.append f g i) = Fin.append (u ∘ f) (u ∘ g) i) ?_ ?_ i
  · intro j; simp [Fin.append_left]
  · intro k; simp [Fin.append_right]

/-- `Fin.init`
of `e1` reads off the `(w, z)` block. -/
theorem init_e1 :
    (Fin.init (e1 (a := a) (b := b))) = (Fin.append (wIx (a := a)) (zIx (b := b)) :
      Fin (a + b) → Fin (((a + 1) + (b + b)) + 2)) := by
  funext k
  show e1 (a := a) (b := b) k.castSucc = _
  rw [show k.castSucc = Fin.castAdd 1 k from Fin.ext rfl]
  simp only [e1, Fin.append_left]

/-- `Fin.init` of `e2` reads off the `(w, z')` block. -/
theorem init_e2 :
    (Fin.init (e2 (a := a) (b := b))) = (Fin.append (wIx (a := a)) (zIx' (b := b)) :
      Fin (a + b) → Fin (((a + 1) + (b + b)) + 2)) := by
  funext k
  show e2 (a := a) (b := b) k.castSucc = _
  rw [show k.castSucc = Fin.castAdd 1 k from Fin.ext rfl]
  simp only [e2, Fin.append_left]

/-- `e1` at the last coordinate reads off `y`. -/
theorem last_e1 : e1 (a := a) (b := b) (Fin.last (a + b)) = yIx (a := a) (b := b) := by
  rw [show Fin.last (a + b) = Fin.natAdd (a + b) (0 : Fin 1) from Fin.ext (by simp [Fin.natAdd])]
  simp only [e1, Fin.append_right]

/-- `e2` at the last coordinate reads off `y'`. -/
theorem last_e2 : e2 (a := a) (b := b) (Fin.last (a + b)) = yIx' (a := a) (b := b) := by
  rw [show Fin.last (a + b) = Fin.natAdd (a + b) (0 : Fin 1) from Fin.ext (by simp [Fin.natAdd])]
  simp only [e2, Fin.append_right]

/-- The `(w, z)`-part of `pt` reads off `w` and the first half of `q`. -/
theorem pt_init_e1 (w : Fin a → ℝ) (η : Fin 1 → ℝ) (q : Fin (b + b) → ℝ) (yy : Fin 2 → ℝ) :
    Fin.init (pt w η q yy ∘ e1) = Fin.append w (fun j : Fin b => q (Fin.castAdd b j)) := by
  rw [← Fin.comp_init, init_e1, comp_append]
  rw [show (pt w η q yy) ∘ (wIx (a := a)) = w from funext (fun i => pt_wIx w η q yy i),
      show (pt w η q yy) ∘ (zIx (b := b)) =
        (fun j : Fin b => q (Fin.castAdd b j)) from funext (fun j => pt_zIx w η q yy j)]

/-- The last coordinate of `pt ∘ e1` reads off `y`. -/
theorem pt_last_e1 (w : Fin a → ℝ) (η : Fin 1 → ℝ) (q : Fin (b + b) → ℝ) (yy : Fin 2 → ℝ) :
    (pt w η q yy ∘ e1) (Fin.last (a + b)) = yy 0 := by
  show pt w η q yy (e1 (Fin.last (a + b))) = yy 0
  rw [last_e1, pt_yIx]

/-- The `(w, z')`-part of `pt` reads off `w` and the second half of `q`. -/
theorem pt_init_e2 (w : Fin a → ℝ) (η : Fin 1 → ℝ) (q : Fin (b + b) → ℝ) (yy : Fin 2 → ℝ) :
    Fin.init (pt w η q yy ∘ e2) = Fin.append w (fun j : Fin b => q (Fin.natAdd b j)) := by
  rw [← Fin.comp_init, init_e2, comp_append]
  rw [show (pt w η q yy) ∘ (wIx (a := a)) = w from funext (fun i => pt_wIx w η q yy i),
      show (pt w η q yy) ∘ (zIx' (b := b)) =
        (fun j : Fin b => q (Fin.natAdd b j)) from funext (fun j => pt_zIx' w η q yy j)]

/-- The last coordinate of `pt ∘ e2` reads off `y'`. -/
theorem pt_last_e2 (w : Fin a → ℝ) (η : Fin 1 → ℝ) (q : Fin (b + b) → ℝ) (yy : Fin 2 → ℝ) :
    (pt w η q yy ∘ e2) (Fin.last (a + b)) = yy 1 := by
  show pt w η q yy (e2 (Fin.last (a + b))) = yy 1
  rw [last_e2, pt_yIx']

/-- Membership of `pt w η (Fin.append z z') yy ∘ e1` in the derivative graph. -/
theorem pt_derivGraph_e1 (f : (Fin (a + b) → ℝ) → ℝ) (i : Fin (a + b))
    (w : Fin a → ℝ) (η : Fin 1 → ℝ) (z z' : Fin b → ℝ) (yy : Fin 2 → ℝ) :
    (pt w η (Fin.append z z') yy ∘ e1) ∈ Work.WilG4b.derivGraph f i ↔
      Fin.append w z ∈ Work.WilG4b.c1Loc f ∧ yy 0 = Work.WilG4b.dDir f i (Fin.append w z) := by
  rw [Work.WilG4b.derivGraph]
  simp only [Set.mem_ofPred_eq]
  rw [pt_init_e1, pt_last_e1]
  simp only [Fin.append_left]

/-- Membership of `pt w η (Fin.append z z') yy ∘ e2` in the derivative graph. -/
theorem pt_derivGraph_e2 (f : (Fin (a + b) → ℝ) → ℝ) (i : Fin (a + b))
    (w : Fin a → ℝ) (η : Fin 1 → ℝ) (z z' : Fin b → ℝ) (yy : Fin 2 → ℝ) :
    (pt w η (Fin.append z z') yy ∘ e2) ∈ Work.WilG4b.derivGraph f i ↔
      Fin.append w z' ∈ Work.WilG4b.c1Loc f ∧ yy 1 = Work.WilG4b.dDir f i (Fin.append w z') := by
  rw [Work.WilG4b.derivGraph]
  simp only [Set.mem_ofPred_eq]
  rw [pt_init_e2, pt_last_e2]
  simp only [Fin.append_right]

/-! ## The middle and small coordinate indices -/

/-- The `η`-coordinate of the middle space `ℝ^{(a+1)+(b+b)}`. -/
def etaM : Fin ((a + 1) + (b + b)) := Fin.castAdd (b + b) (Fin.natAdd a (0 : Fin 1))

/-- The `z`-coordinate of the middle space. -/
def zM (j : Fin b) : Fin ((a + 1) + (b + b)) := Fin.natAdd (a + 1) (Fin.castAdd b j)

/-- The `z'`-coordinate of the middle space. -/
def zM' (j : Fin b) : Fin ((a + 1) + (b + b)) := Fin.natAdd (a + 1) (Fin.natAdd b j)

/-- The `η`-coordinate of the small space `ℝ^{a+1}`. -/
def etaS : Fin (a + 1) := Fin.natAdd a (0 : Fin 1)

@[simp] theorem mid_eta (w : Fin a → ℝ) (η : Fin 1 → ℝ) (q : Fin (b + b) → ℝ) :
    Fin.append (Fin.append w η) q etaM = η 0 := by
  simp only [etaM, Fin.append_left, Fin.append_right]

@[simp] theorem mid_z (w : Fin a → ℝ) (η : Fin 1 → ℝ) (q : Fin (b + b) → ℝ) (j : Fin b) :
    Fin.append (Fin.append w η) q (zM j) = q (Fin.castAdd b j) := by
  simp only [zM, Fin.append_left, Fin.append_right]

@[simp] theorem mid_z' (w : Fin a → ℝ) (η : Fin 1 → ℝ) (q : Fin (b + b) → ℝ) (j : Fin b) :
    Fin.append (Fin.append w η) q (zM' j) = q (Fin.natAdd b j) := by
  simp only [zM', Fin.append_left, Fin.append_right]

@[simp] theorem small_eta (w : Fin a → ℝ) (η : Fin 1 → ℝ) : Fin.append w η etaS = η 0 := by
  simp only [etaS, Fin.append_right]

/-! ## The three constituent sets -/

/-- The core set: both derivative graphs visited with matching value coordinates. -/
def coreSet (T : Set (Fin ((a + b) + 1) → ℝ)) (ε : ℝ) :
    Set (Fin (((a + 1) + (b + b)) + 2) → ℝ) :=
  {u | u ∘ e1 ∈ T ∧ u ∘ e2 ∈ T ∧ |u yIx - u yIx'| < ε}

/-- The hypothesis set: `z ≠ 0`, `z' ≠ 0` and all coordinates of `z, z'` bounded by `η`. -/
def hypSet : Set (Fin ((a + 1) + (b + b)) → ℝ) :=
  {x | (fun j : Fin b => x (zM j)) ≠ 0 ∧
       (∀ j : Fin b, |x (zM j)| < x etaM) ∧
       (fun j : Fin b => x (zM' j)) ≠ 0 ∧
       (∀ j : Fin b, |x (zM' j)| < x etaM)}

/-- The threshold set: `1/((k:ℝ)+1) < η ≤ 1`. -/
def threshSet (k : ℕ) : Set (Fin (a + 1) → ℝ) :=
  {x | 1 / ((k : ℝ) + 1) < x etaS ∧ x etaS ≤ 1}

/-- The big-space presentation of `sliceCauchySet`. -/
def bigSet (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (j : Fin b) (k : ℕ) (ε : ℝ) :
    Set (Fin a → ℝ) :=
  Work.WilG5.projN 1
    (threshSet (a := a) k ∩
      (Work.WilG5.projN (b + b)
        (hypSet (a := a) (b := b) ∩
          (Work.WilG5.projN 2 (coreSet (a := a) (b := b)
            (Work.WilG4b.derivGraph (Work.WilG4c.famFun G) (Fin.natAdd a j)) ε))ᶜ))ᶜ)

end Work.WilCrux
