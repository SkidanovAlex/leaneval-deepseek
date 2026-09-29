import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.defs
import Submission.Work.Resample.axis

/-!
# Fixed-point arrays and the error of a tensor of approximations

`fxTensorRec` is the fixed-point analogue of `tensorMapRec`: it applies a family of fixed-point
slice maps `Fh i : (Fin sᵢ → ℤ×ℤ) → (Fin tᵢ → ℤ×ℤ)` successively along the axes of a flat
lexicographic array.  `fxTensorErr` (paper Lemma 2.11 / Corollary 2.8) bounds the resulting error
`2^p‖fxC (result) - (⊗ Aᵢ)(v)‖` by the sum of the one-dimensional errors, provided each `Aᵢ` is
linear and contractive and each `Fh i` keeps the disc `C̃◦` invariant.
-/

set_option autoImplicit false

namespace Work.Resample

open HvdH

/-- read a fixed-point vector at a natural index (`(0,0)` outside). -/
def zget {n : ℕ} (u : Fin n → ℤ × ℤ) (i : ℕ) : ℤ × ℤ := if h : i < n then u ⟨i, h⟩ else (0, 0)

/-- `Φ` applied along the first axis of a `s × B` fixed-point array. -/
noncomputable def axisFx1Gen (s t B : ℕ) (Φ : (Fin s → ℤ × ℤ) → (Fin t → ℤ × ℤ))
    (u : Fin (s * B) → ℤ × ℤ) : Fin (t * B) → ℤ × ℤ :=
  fun idx => if h : (idx : ℕ) / B < t then
      Φ (fun j => zget u ((j : ℕ) * B + (idx : ℕ) % B)) ⟨(idx : ℕ) / B, h⟩ else (0, 0)

/-- Apply `Φ` to each block of size `N` of a `t × N` fixed-point array. -/
noncomputable def fxBlockwise (t N N' : ℕ) (Φ : (Fin N → ℤ × ℤ) → (Fin N' → ℤ × ℤ))
    (u : Fin (t * N) → ℤ × ℤ) : Fin (t * N') → ℤ × ℤ :=
  fun idx => if h : (idx : ℕ) % N' < N' then
      Φ (fun K' => zget u ((idx : ℕ) / N' * N + (K' : ℕ))) ⟨(idx : ℕ) % N', h⟩ else (0, 0)

/-- Iterated fixed-point axis application over a list of dimensions. -/
noncomputable def fxTensorRec (ss ts : List ℕ)
    (Fh : (i : ℕ) → (Fin (ss.getD i 0) → ℤ × ℤ) → (Fin (ts.getD i 0) → ℤ × ℤ)) :
    (Fin ss.prod → ℤ × ℤ) → (Fin ts.prod → ℤ × ℤ) :=
  match ss, ts with
  | [], [] => id
  | s :: ss', t :: ts' => fun u =>
      fxBlockwise t ss'.prod ts'.prod (fxTensorRec ss' ts' (fun i => Fh (i + 1)))
        (axisFx1Gen s t ss'.prod (Fh 0) u)
  | _, _ => fun _ => 0

end Work.Resample
