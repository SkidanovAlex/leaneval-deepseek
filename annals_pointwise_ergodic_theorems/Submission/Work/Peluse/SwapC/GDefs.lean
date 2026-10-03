/-
Vocabulary for the *index-set-agnostic* Gowers--Cauchy--Schwarz inequality for the multiset cube
sum `Work.Peluse.SwapC.mCubeSum`.

`mCubeSum d X ν S F` averages, over pairs of index tuples `h, h' : Fin d → X` and the base point
`x : ℤ`, the cube term `∏_ω C^{|ω|} F_ω (x + cornerShift (ν ∘ h) (ν ∘ h') ω)`.  The proof of the
Gowers--Cauchy--Schwarz inequality (`gWinForm_norm_le` below) is the one of
`Work.Peluse.BoxNorm.winForm_norm_le` (Cauchy--Schwarz at `d = 1`, then split the first
coordinate, Cauchy--Schwarz, induction, generalised Hölder); that proof only ever uses the corner
`z i` / `z' i` and the *sum* of the directions, so it is index-set agnostic.

This file freezes the vocabulary in the general form: coordinate types `Y i`, direction maps
`β i : Y i → ℤ`, the index tuple type `GIdx d Y`, the corner `gcorner`, the total shift `gtotal`,
the box form `gWinForm` and its `2^d`-th root `gWinNorm`.

## Main definitions

* `Work.Peluse.SwapC.GIdx`, `gtotal`, `gcorner`, `gWinForm`, `gWinNorm`, `gHalf`, `gSlotF`,
  `gSlotT`
-/
import Mathlib
import Submission.Work.Peluse.BoxNorm.WinDefs

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse

/-- The index tuple type of the `d`-fold cube with coordinate types `Y i`. -/
abbrev GIdx (d : ℕ) (Y : Fin d → Type*) : Type _ := (i : Fin d) → Y i

variable {d : ℕ} {Y : Fin d → Type*} [∀ i, Fintype (Y i)]

/-- The total shift of an index tuple: `∑_i β i (z i)`. -/
def gtotal (β : (i : Fin d) → Y i → ℤ) (z : GIdx d Y) : ℤ := ∑ i, β i (z i)

/-- The `ω`-corner of the cube: coordinate `i` is taken from `z` if `ω i`, else from `z'`. -/
def gcorner (z z' : GIdx d Y) (ω : Fin d → Bool) : GIdx d Y := fun i => if ω i then z i else z' i

/-- The total shift of the `ω`-corner is `cornerShift (β ∘ z) (β ∘ z') ω`. -/
lemma gtotal_gcorner (β : (i : Fin d) → Y i → ℤ) (z z' : GIdx d Y) (ω : Fin d → Bool) :
    gtotal β (gcorner z z' ω)
      = cornerShift (fun i => β i (z i)) (fun i => β i (z' i)) ω := by
  simp only [gtotal, gcorner, cornerShift]
  exact Finset.sum_congr rfl (fun i _ => by by_cases h : ω i <;> simp [h])

/-- The **general box form** over the index tuple type `GIdx d Y` with directions `β` and window
`W`: `∑_{z,z'} ∑_{x ∈ W} ∏_ω C^{|ω|} φ_ω (x + gtotal β (gcorner z z' ω))`. -/
def gWinForm (d : ℕ) (Y : Fin d → Type*) [∀ i, Fintype (Y i)]
    (β : (i : Fin d) → Y i → ℤ) (W : Finset ℤ) (φ : (Fin d → Bool) → ℤ → ℂ) : ℂ :=
  ∑ z : GIdx d Y, ∑ z' : GIdx d Y, ∑ x ∈ W,
    ∏ ω : Fin d → Bool, (star^[weight ω]) (φ ω (x + gtotal β (gcorner z z' ω)))

/-- The `2^d`-th root of the box form of a single function. -/
def gWinNorm (d : ℕ) (Y : Fin d → Type*) [∀ i, Fintype (Y i)]
    (β : (i : Fin d) → Y i → ℤ) (W : Finset ℤ) (g : ℤ → ℂ) : ℝ :=
  ‖gWinForm d Y β W (fun _ => g)‖ ^ (1 / (2 : ℝ) ^ d)

lemma gWinNorm_nonneg (β : (i : Fin d) → Y i → ℤ) (W : Finset ℤ) (g : ℤ → ℂ) :
    0 ≤ gWinNorm d Y β W g := Real.rpow_nonneg (norm_nonneg _) _

/-- The "half product" of the box form: the `ω`-product over the first half of the cube. -/
def gHalf (n : ℕ) (Y : Fin n → Type*) [∀ i, Fintype (Y i)]
    (β : (i : Fin n) → Y i → ℤ) (u : (Fin n → Bool) → ℤ → ℂ)
    (z z' : GIdx n Y) (x a : ℤ) : ℂ :=
  ∏ ω : Fin n → Bool, (star^[weight ω]) (u ω (x + gtotal β (gcorner z z' ω) + a))

/-- The slot `ω ↦ φ (false :: ω)`. -/
def gSlotF {n : ℕ} (φ : (Fin (n+1) → Bool) → ℤ → ℂ) : (Fin n → Bool) → ℤ → ℂ :=
  fun ω y => φ (Fin.cons false ω) y

/-- The slot `ω ↦ φ (true :: ω)`. -/
def gSlotT {n : ℕ} (φ : (Fin (n+1) → Bool) → ℤ → ℂ) : (Fin n → Bool) → ℤ → ℂ :=
  fun ω y => φ (Fin.cons true ω) y

end

end Work.Peluse.SwapC
