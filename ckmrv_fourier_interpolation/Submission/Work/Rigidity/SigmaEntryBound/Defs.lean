/-
# Definitions for the polynomial growth bound on the entries of `σ_R`

This file sets up the vocabulary used to prove
`Work.Rigidity.SigmaEntryBound.sigmaR_entry_bound`.

Two independent ingredients:

* `Work.Rigidity.SigmaEntryBound.W` : the monoid homomorphism
  `SL(2,ℤ) →* M₆(ℂ)` given by `γ ↦ σ_R (of γ)`, together with the explicit values on the
  generators `S`, `T`, `T⁻¹` (the paper's matrices `σ(S)`, `σ(T)`, `σ(T)⁻¹`), and the squared
  Frobenius norm `frob2C` on `M₆(ℂ)`, which is submultiplicative.

* the Euclidean recursion on `2 × 2` integer matrices: for a matrix `M = !![a,b;c,d]` with
  `c ≠ 0` one writes `a = q c + r` with `|r| ≤ |c|/2` (`rnd`, `rem`), so that
  `M = T^q · S · nxt M` with `nxt M = !![c, d; -r, -(b - q d)]`.  Iterating this gives the
  continued fraction expansion `M = ±(T^{q₀} S T^{q₁} S ⋯ S T^{q_k})`, which is what makes the
  bound polynomial in the Frobenius norm of `M`.
-/
import Mathlib
import Submission.Work.Residues.IdealImRowDiffAll
import Submission.Work.Residues.ResidueTheorem
import Submission.Work.Asymptotics.PropagateBounds.Defs
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.Slash

noncomputable section

open Matrix
open scoped MatrixGroups MonoidAlgebra

namespace Work.Rigidity.SigmaEntryBound

open Work.Kernels

/-! ## The representation, as a monoid homomorphism -/

/-- The squared Frobenius norm of a `6 × 6` complex matrix. -/
def frob2C (A : Matrix (Fin 6) (Fin 6) ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

/-- The paper's six dimensional representation, viewed as a monoid homomorphism
`SL(2,ℤ) →* M₆(ℂ)`: `γ ↦ σ_R (of γ)`. -/
def W : SL(2,ℤ) →* Matrix (Fin 6) (Fin 6) ℂ where
  toFun γ := Work.Residues.sigmaR (MonoidAlgebra.of ℂ SL(2,ℤ) γ)
  map_one' := by
    show Work.Residues.sigmaR (MonoidAlgebra.of ℂ SL(2,ℤ) (1 : SL(2,ℤ))) = 1
    rw [map_one, map_one]
  map_mul' γ δ := by
    show Work.Residues.sigmaR (MonoidAlgebra.of ℂ SL(2,ℤ) (γ * δ)) = _
    rw [map_mul, map_mul]

@[simp] theorem W_S : W ModularGroup.S = Work.Modular.sigmaS := by
  have h : MonoidAlgebra.of ℂ SL(2,ℤ) ModularGroup.S = Work.Kernels.R_S := rfl
  rw [show W ModularGroup.S = Work.Residues.sigmaR (MonoidAlgebra.of ℂ SL(2,ℤ) ModularGroup.S)
    from rfl, h, Work.Residues.sigmaR_R_S]

@[simp] theorem W_T : W ModularGroup.T = Work.Modular.sigmaT := by
  have h : MonoidAlgebra.of ℂ SL(2,ℤ) ModularGroup.T = Work.Kernels.R_T := rfl
  rw [show W ModularGroup.T = Work.Residues.sigmaR (MonoidAlgebra.of ℂ SL(2,ℤ) ModularGroup.T)
    from rfl, h, Work.Residues.sigmaR_R_T]

/-- `σ_R` kills `-I`, hence `W (-γ) = W γ` for all `γ`. -/
theorem W_neg (γ : SL(2,ℤ)) : W (-γ) = W γ := by
  have h : (-γ : SL(2,ℤ)) = (-1 : SL(2,ℤ)) * γ := by rw [neg_one_mul]
  rw [h, map_mul, show W (-1 : SL(2,ℤ)) = 1 from ?_, one_mul]
  show Work.Residues.sigmaR (MonoidAlgebra.of ℂ SL(2,ℤ) (-1 : SL(2,ℤ))) = 1
  rw [show MonoidAlgebra.of ℂ SL(2,ℤ) (-1 : SL(2,ℤ)) = Work.Residues.Rneg from rfl,
    Work.Residues.sigmaR_Rneg]

/-! ## The Euclidean recursion on `2 × 2` integer matrices -/

/-- The nearest integer to `a / c`, i.e. `⌊a/c + 1/2⌋`. -/
def rnd (a c : ℤ) : ℤ :=
  if 0 < c then (2 * a + c) / (2 * c) else (-(2 * a + c)) / (-(2 * c))

/-- The quotient associated with the state `M`: `a/c` rounded to the nearest integer (and, for
a terminal state where `c = 0`, the value `a * b` so that `M = ±T^(a*b)`). -/
def quo (M : Matrix (Fin 2) (Fin 2) ℤ) : ℤ :=
  if M 1 0 = 0 then M 0 0 * M 0 1 else rnd (M 0 0) (M 1 0)

/-- The remainder of the Euclidean division of the state `M`. -/
def remz (M : Matrix (Fin 2) (Fin 2) ℤ) : ℤ := M 0 0 - quo M * M 1 0

/-- One step of the Euclidean recursion: `M = T^q · S · nxt M` with `q = quo M`, whenever
`M 1 0 ≠ 0`.  When `M 1 0 = 0` (`M` is already terminal) the state is left unchanged. -/
def nxt (M : Matrix (Fin 2) (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  if M 1 0 = 0 then M
  else !![M 1 0, M 1 1; -(remz M), -(M 0 1 - quo M * M 1 1)]

/-- The `n`-th state of the Euclidean recursion started at `M`. -/
def stateZ (M : Matrix (Fin 2) (Fin 2) ℤ) : ℕ → Matrix (Fin 2) (Fin 2) ℤ
  | 0 => M
  | n + 1 => nxt (stateZ M n)

/-- The list of the first `n + 1` quotients of the Euclidean recursion started at `M`. -/
def qsl (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) : List ℤ :=
  (List.range (n + 1)).map (fun j => quo (stateZ M j))

/-- The sum of the absolute values of the first column of an integer matrix. -/
def uZ (M : Matrix (Fin 2) (Fin 2) ℤ) : ℕ := (M 0 0).natAbs + (M 1 0).natAbs

/-- The squared Frobenius norm of a `2 × 2` integer matrix, as a natural number. -/
def frob2Z (M : Matrix (Fin 2) (Fin 2) ℤ) : ℕ :=
  (M 0 0).natAbs ^ 2 + (M 0 1).natAbs ^ 2 + (M 1 0).natAbs ^ 2 + (M 1 1).natAbs ^ 2

/-- The termination measure of the Euclidean recursion. -/
def muZ (M : Matrix (Fin 2) (Fin 2) ℤ) : ℕ := (uZ M) ^ 2 + (M 1 0).natAbs

/-- The determinant of a `2 × 2` integer matrix, written out. -/
def detZ (M : Matrix (Fin 2) (Fin 2) ℤ) : ℤ := M 0 0 * M 1 1 - M 0 1 * M 1 0

/-- The `2 × 2` matrix `!![1,q;0,1]`. -/
def Tpow (q : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, q; 0, 1]

/-- The `2 × 2` matrix `!![0,-1;1,0]`. -/
def Smat : Matrix (Fin 2) (Fin 2) ℤ := !![0, -1; 1, 0]

/-- The product `T^{q₀} S T^{q₁} S ⋯ S T^{q_k}` of a list of integers. -/
def recon : List ℤ → Matrix (Fin 2) (Fin 2) ℤ
  | [] => 1
  | [q] => Tpow q
  | q :: q' :: rest => Tpow q * Smat * recon (q' :: rest)

/-- The product `∏ (1 + |q|)` over a list. -/
def prod1p (l : List ℤ) : ℕ := l.foldr (fun q acc => (1 + q.natAbs) * acc) 1

end Work.Rigidity.SigmaEntryBound
