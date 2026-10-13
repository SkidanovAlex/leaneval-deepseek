/-
  Area G4b: shared vocabulary for the `Ω`-membership of the choice set `ESet`.

  `ESet f c d M` is the set of `C¹` points `z` of `ℝ^{n+1}` with `z 0 ∈ (c,d)`,
  `Fin.tail z` in the open cube and `|∂₀ f(z)| > M (1 + n u)` for a common bound `u` of the
  `y`-partials.  To exhibit it as an `Ω`-set we pass through a joint space

    `ℝ^{(n+1) + ((n+1)+1)}`

  whose coordinates are, in order,

  * `z ∈ ℝ^{n+1}` — the point of `ESet` (indices `zIdx`),
  * `w ∈ ℝ^{n+1}` — the partials `w i = ∂ᵢ f(z)` (indices `wIdx`),
  * `u ∈ ℝ` — the threshold (index `uIdx`).

  (The ambient is written `m + (m+1)` with `m = n+1` so that it is *syntactically* of the form
  `Fin (n + k)` used by `Work.WilG5.projN` with `k = m+1`: `simp`/`rw` work at fixed
  transparency and would otherwise regard two definitionally equal formulations of the same
  dimension as different types.)

  `ECond f i` links the `z`-block to the `i`-th partial by pulling back the derivative graph
  `derivGraph f i` of `SharpDeriv` along the index map `eIdx`.  `EDerSet f` is their
  intersection (so `z ∈ c1Loc f` and `w i = dDir f i z` for all `i`).  `EInner f M` adds the
  inequalities `0 ≤ u`, `|w (j+1)| ≤ u`, `M (1 + n u) < |w 0|`, and `ESetD f M` is the
  projection of `EInner f M` to the `z`-block.
-/
import Mathlib
import Submission.Work.WilG4b.Basic
import Submission.Work.WilG5.Basic

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4b
open WilkiesDesign WilkiesConjecture

/-! ## Index bookkeeping for the joint space `ℝ^{m + (m+1)}` -/

/-- The index of the `z`-coordinate `j` in `Fin (m + (m+1))`. -/
def zIdx (m : ℕ) (j : Fin m) : Fin (m + (m + 1)) := ⟨j.val, by omega⟩

/-- The index of the partial `w i` in `Fin (m + (m+1))`. -/
def wIdx (m : ℕ) (i : Fin m) : Fin (m + (m + 1)) := ⟨m + i.val, by omega⟩

/-- The index of the threshold `u` in `Fin (m + (m+1))`. -/
def uIdx (m : ℕ) : Fin (m + (m + 1)) := ⟨m + m, by omega⟩

/-- The index map `Fin (m+1) → Fin (m + (m+1))` selecting the `z`-block and the `i`-th
partial: `j ↦ z j` for `j : Fin m` and the last index `m ↦ w i`. -/
def eIdx (m : ℕ) (i : Fin m) : Fin (m + 1) → Fin (m + (m + 1)) :=
  Fin.lastCases (wIdx m i) (fun j => zIdx m j)

@[simp] theorem eIdx_last (m : ℕ) (i : Fin m) : eIdx m i (Fin.last m) = wIdx m i := by
  simp [eIdx]

@[simp] theorem eIdx_castSucc (m : ℕ) (i j : Fin m) : eIdx m i j.castSucc = zIdx m j := by
  simp [eIdx]

theorem zIdx_eq_castAdd (m : ℕ) (j : Fin m) : zIdx m j = Fin.castAdd (m + 1) j := by
  apply Fin.ext
  simp [zIdx]

theorem wIdx_eq_natAdd (m : ℕ) (i : Fin m) : wIdx m i = Fin.natAdd m i.castSucc := by
  apply Fin.ext
  simp [wIdx, Fin.natAdd]

theorem uIdx_eq_natAdd (m : ℕ) : uIdx m = Fin.natAdd m (Fin.last m) := by
  apply Fin.ext
  simp [uIdx, Fin.natAdd]

/-- `eIdx` only shuffles coordinates: composing with `eIdx` reads the `z`-block and the `i`-th
partial out of a point obtained by `Fin.append`. -/
theorem append_comp_eIdx (m : ℕ) (i : Fin m) (z : Fin m → ℝ) (y : Fin (m + 1) → ℝ) :
    (Fin.append z y) ∘ (eIdx m i) = (Fin.snoc z (y i.castSucc) : Fin (m + 1) → ℝ) := by
  funext k
  refine Fin.lastCases ?_ ?_ k
  · show Fin.append z y (eIdx m i (Fin.last m))
      = (Fin.snoc z (y i.castSucc) : Fin (m + 1) → ℝ) (Fin.last m)
    rw [eIdx_last,
      show (Fin.snoc z (y i.castSucc) : Fin (m + 1) → ℝ) (Fin.last m) = y i.castSucc from
        Fin.snoc_last _ _,
      wIdx_eq_natAdd, Fin.append_right]
  · intro j
    show Fin.append z y (eIdx m i j.castSucc)
      = (Fin.snoc z (y i.castSucc) : Fin (m + 1) → ℝ) j.castSucc
    rw [eIdx_castSucc,
      show (Fin.snoc z (y i.castSucc) : Fin (m + 1) → ℝ) j.castSucc = z j from
        Fin.snoc_castSucc _ _ _,
      zIdx_eq_castAdd, Fin.append_left]

@[simp] theorem append_zIdx (m : ℕ) (z : Fin m → ℝ) (y : Fin (m + 1) → ℝ) (j : Fin m) :
    Fin.append z y (zIdx m j) = z j := by
  rw [zIdx_eq_castAdd, Fin.append_left]

@[simp] theorem append_wIdx (m : ℕ) (z : Fin m → ℝ) (y : Fin (m + 1) → ℝ) (i : Fin m) :
    Fin.append z y (wIdx m i) = y i.castSucc := by
  rw [wIdx_eq_natAdd, Fin.append_right]

@[simp] theorem append_uIdx (m : ℕ) (z : Fin m → ℝ) (y : Fin (m + 1) → ℝ) :
    Fin.append z y (uIdx m) = y (Fin.last m) := by
  rw [uIdx_eq_natAdd, Fin.append_right]

/-! ## The joint sets -/

/-- The pullback of the derivative graph `derivGraph f i` along `eIdx`: the points `x` of the
joint space whose `z`-block lies in the `C¹` locus and whose `i`-th slot is `∂ᵢ f` at that
point. -/
def ECond {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (i : Fin (n + 1)) :
    Set (Fin ((n + 1) + ((n + 1) + 1)) → ℝ) :=
  {x | x ∘ eIdx (n + 1) i ∈ derivGraph f i}

/-- The derivative-set of `f`: the intersection of all `ECond f i`. -/
def EDerSet {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) :
    Set (Fin ((n + 1) + ((n + 1) + 1)) → ℝ) :=
  ⋂ i : Fin (n + 1), ECond f i

/-- The joint set of the reduction: the derivative-set together with the chosen threshold
`u ≥ 0` dominating the `y`-partials and strictly below `|∂₀ f| / M`. -/
def EInner {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (M : ℝ) :
    Set (Fin ((n + 1) + ((n + 1) + 1)) → ℝ) :=
  EDerSet f ∩ {x | 0 ≤ x (uIdx (n + 1))}
    ∩ (⋂ j : Fin n, {x | |x (wIdx (n + 1) j.succ)| ≤ x (uIdx (n + 1))})
    ∩ {x | M * (1 + n * x (uIdx (n + 1))) < |x (wIdx (n + 1) (0 : Fin (n + 1)))|}

/-- The projection of the joint set to the `z`-block. -/
def ESetD {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (M : ℝ) : Set (Fin (n + 1) → ℝ) :=
  Work.WilG5.projN (n := n + 1) ((n + 1) + 1) (EInner f M)

end Work.WilG4b
