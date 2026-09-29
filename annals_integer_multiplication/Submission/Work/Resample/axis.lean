import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.defs

/-!
# Applying one-dimensional maps along a single axis of a flat array

`axisApply1Gen s t B Φ` applies the map `Φ : (Fin s → ℂ) → (Fin t → ℂ)` along the first axis of a
flat lexicographic array of shape `s × B`; `blockwise` applies a map to each block of a `t × N`
array; `tensorRec` iterates these over a list of dimensions.  This is exactly the computation
performed by `HvdH.LayoutLib.applyAlong` iterated over the axes, and (by
`tensorRec_eq_tensorFun`) it computes the tensor `⊗ᵢ Mᵢ` of `Submission.Work.Resample.defs`.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- The matrix with entries given by an unbundled entry function. -/
noncomputable def matOf (n m : ℕ) (f : ℕ → ℕ → ℂ) : Matrix (Fin n) (Fin m) ℂ := fun i j => f i j

/-- `Φ` applied along the first axis of a `s × B` array. -/
noncomputable def axisApply1Gen (s t B : ℕ) (Φ : (Fin s → ℂ) → (Fin t → ℂ))
    (u : Fin (s * B) → ℂ) : Fin (t * B) → ℂ :=
  fun idx => vget (Φ (fun j => vget u ((j : ℕ) * B + (idx : ℕ) % B))) ((idx : ℕ) / B)

/-- `M` applied along the first axis of a `s × B` array. -/
noncomputable def axisApply1 (s t B : ℕ) (M : Matrix (Fin t) (Fin s) ℂ)
    (u : Fin (s * B) → ℂ) : Fin (t * B) → ℂ :=
  fun idx => ∑ j : Fin s, unb t s M ((idx : ℕ) / B) (j : ℕ) *
    vget u ((j : ℕ) * B + (idx : ℕ) % B)

/-- Apply `Φ` to each block of size `N` of a `t × N` array, getting a `t × N'` array. -/
noncomputable def blockwise (t N N' : ℕ) (Φ : (Fin N → ℂ) → (Fin N' → ℂ))
    (u : Fin (t * N) → ℂ) : Fin (t * N') → ℂ :=
  fun idx => vget (Φ (fun K' => vget u ((idx : ℕ) / N' * N + (K' : ℕ)))) ((idx : ℕ) % N')

/-- Iterated axis application over a list of dimensions; computes the tensor `⊗ᵢ Mᵢ`. -/
noncomputable def tensorRec (ss ts : List ℕ) (f : ℕ → ℕ → ℕ → ℂ) :
    (Fin ss.prod → ℂ) → (Fin ts.prod → ℂ) :=
  match ss, ts with
  | [], [] => id
  | s :: ss', t :: ts' => fun u =>
      blockwise t ss'.prod ts'.prod (tensorRec ss' ts' (fun i j k => f (i + 1) j k))
        (axisApply1 s t ss'.prod (matOf t s (f 0)) u)
  | _, _ => fun _ => 0

/-- Iterated axis application for an arbitrary family of one-dimensional maps. -/
noncomputable def tensorMapRec (ss ts : List ℕ)
    (F : (i : ℕ) → (Fin (ss.getD i 0) → ℂ) → (Fin (ts.getD i 0) → ℂ)) :
    (Fin ss.prod → ℂ) → (Fin ts.prod → ℂ) :=
  match ss, ts with
  | [], [] => id
  | s :: ss', t :: ts' => fun u =>
      blockwise t ss'.prod ts'.prod (tensorMapRec ss' ts' (fun i => F (i + 1)))
        (axisApply1Gen s t ss'.prod (F 0) u)
  | _, _ => fun _ => 0

/-- The matrix family associated with an entry function. -/
noncomputable def matFam (ss ts : List ℕ) (f : ℕ → ℕ → ℕ → ℂ) :
    (i : ℕ) → (Fin (ss.getD i 0) → ℂ) → (Fin (ts.getD i 0) → ℂ) :=
  fun i => (matOf (ts.getD i 0) (ss.getD i 0) (f i)).mulVec

end Work.Resample
