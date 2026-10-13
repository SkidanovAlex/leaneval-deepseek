import Mathlib
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG1.Cell.thin_closure
import Submission.Work.WilG1.Cell.thin_union

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign

/-! ## The fibre of a set over the parameter, and the "bad parameter" set

Throughout, `p` is the number of *parameters* and `k` the number of *fibre* coordinates.
A set `κ ⊆ ℝ^{p+k}` has fibre `fibSet p k κ l ⊆ ℝ^k` over the parameter `l ∈ ℝ^p`.
`BadFib p q V` is the set of parameters `l` for which the fibre `V_l` contains a ball. -/

/-- The fibre of `κ ⊆ ℝ^{p+k}` over the parameter `l ∈ ℝ^p`, as a subset of `ℝ^k`. -/
def fibSet (p k : ℕ) (κ : Set (Fin (p + k) → ℝ)) (l : Fin p → ℝ) : Set (Fin k → ℝ) :=
  {y | Fin.append l y ∈ κ}

/-- `Fin.append` with the fibre length made explicit, for predictable elaboration. -/
def apPt (p k : ℕ) (l : Fin p → ℝ) (y : Fin k → ℝ) : Fin (p + k) → ℝ := Fin.append l y

@[simp] theorem apPt_apply {p k : ℕ} (l : Fin p → ℝ) (y : Fin k → ℝ) :
    apPt p k l y = Fin.append l y := rfl

/-- A set that is either empty or a cylindrical cell. -/
def IsCellOrEmpty (k : ℕ) (s : Set (Fin k → ℝ)) : Prop := s = ∅ ∨ IsCell k s

/-- The parameters `l` for which the fibre `V_l` contains a ball. -/
def BadFib (p q : ℕ) (V : Set (Fin (p + q) → ℝ)) : Set (Fin p → ℝ) :=
  {l | ∃ (y₀ : Fin q → ℝ) (ε : ℝ), 0 < ε ∧ ∀ y : Fin q → ℝ, dist y y₀ < ε → Fin.append l y ∈ V}

/-! ## Index lemmas for `Fin.append` -/

theorem init_append {p q : ℕ} (l : Fin p → ℝ) (y : Fin (q + 1) → ℝ) :
    (Fin.init (Fin.append l y : Fin (p + (q + 1)) → ℝ) : Fin (p + q) → ℝ) =
      Fin.append l (Fin.init y) := by
  ext i
  rw [Fin.init]
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · have h : (Fin.castAdd q i).castSucc = Fin.castAdd (q + 1) i := by ext; rfl
    rw [h, Fin.append_left, Fin.append_left]
  · have h : (Fin.natAdd p j).castSucc = Fin.natAdd p j.castSucc := by ext; rfl
    rw [h, Fin.append_right, Fin.append_right]
    rfl

theorem init_append_snoc {p q : ℕ} (l : Fin p → ℝ) (y : Fin q → ℝ) (t : ℝ) :
    (Fin.init (Fin.append l (Fin.snoc y t) : Fin (p + (q + 1)) → ℝ) : Fin (p + q) → ℝ) =
      Fin.append l y := by
  ext i
  rw [Fin.init]
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · have h : (Fin.castAdd q i).castSucc = Fin.castAdd (q + 1) i := by ext; rfl
    rw [h, Fin.append_left, Fin.append_left]
  · have h : (Fin.natAdd p j).castSucc = Fin.natAdd p j.castSucc := by ext; rfl
    rw [h, Fin.append_right, Fin.append_right, Fin.snoc_castSucc]

theorem append_last {p q : ℕ} (l : Fin p → ℝ) (y : Fin (q + 1) → ℝ) :
    (Fin.append l y : Fin (p + (q + 1)) → ℝ) (Fin.last (p + q)) = y (Fin.last q) := by
  rw [show (Fin.last (p + q) : Fin (p + (q + 1))) = Fin.natAdd p (Fin.last q) from Fin.ext rfl,
    Fin.append_right]

/-- Appending a fixed prefix is continuous. -/
theorem continuous_append {p k : ℕ} (l : Fin p → ℝ) :
    Continuous (fun y : Fin k → ℝ => (Fin.append l y : Fin (p + k) → ℝ)) := by
  refine continuous_pi (fun j => ?_)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · have h : (fun y : Fin k → ℝ => Fin.append l y (Fin.castAdd k i)) = fun _ => l i := by
      funext y; exact Fin.append_left l y i
    rw [h]; exact continuous_const
  · have h : (fun y : Fin k → ℝ => Fin.append l y (Fin.natAdd p i)) = fun y => y i := by
      funext y; exact Fin.append_right l y i
    rw [h]; exact continuous_apply i

theorem apPt_init {p q : ℕ} (l : Fin p → ℝ) (y : Fin (q + 1) → ℝ) :
    (Fin.init (apPt p (q + 1) l y) : Fin (p + q) → ℝ) = apPt p q l (Fin.init y) :=
  init_append l y

theorem apPt_last {p q : ℕ} (l : Fin p → ℝ) (y : Fin (q + 1) → ℝ) :
    (apPt p (q + 1) l y) (Fin.last (p + q)) = y (Fin.last q) :=
  append_last l y

end Work.WilG4c
