/-
  annals_wilkies_conjecture, area C4aL (`C4a_lift`): definitions.

  The C4aL step turns the `rexp` slice of an `RExpExist` set at a parameter `c` into a
  finite union of bounded basic semianalytic pieces with entire data, over the `t = 1/x`
  axis.  See `Submission/Work/Wilkies/CG/C4a/DESIGN.md`.

  Vocabulary: the `k+2+m` variables of the defining polynomial are laid out as
    positions 0,1       : `x` and `y`,
    positions 2..k+1    : the constants `c _`,
    positions k+2..     : the witnesses `w _`.
  A *case assignment* `σ : Fin (m+2) → VC` sends each case coordinate to
    `small` (`|v|<1`), `one` (`v^2 = 1`) or `big` (`|v|>1`, coordinate inverted).
  Piece coordinate `j` is `v j` for `small`/`one` and `v j⁻¹` for `big`.
-/
import Submission.Work.Wilkies.CG.C4a.Spec
import Mathlib.Analysis.Analytic.Polynomial

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilC4aL
open WilkiesDesign WilkiesDesign.CG.C4a

/-! ## 0. The case split -/

/-- Case of a variable in the lift.  `small`: `|v| < 1`, `one`: `v ^ 2 = 1`,
`big`: `|v| > 1` (coordinate inverted). -/
inductive VC where
  | small : VC
  | one : VC
  | big : VC
  deriving DecidableEq

instance : Fintype VC where
  elems := {VC.small, VC.one, VC.big}
  complete := by intro x; cases x <;> simp

variable {k m : ℕ}

/-! ## 1. Index layout -/

/-- `Sum.inl j` (`j : Fin k`) is the constant parameter `c j`; `Sum.inr j` (`j : Fin (m+2)`)
is the case variable with piece coordinate `j` (`0` = `x`, `1` = `y`, `j+2` = `w_j`). -/
def piIdx (i : Fin (k + 2 + m)) : Fin k ⊕ Fin (m + 2) :=
  if h : (i : ℕ) < 2 then Sum.inr ⟨(i : ℕ), by omega⟩
  else if h2 : (i : ℕ) < k + 2 then Sum.inl ⟨(i : ℕ) - 2, by omega⟩
  else Sum.inr ⟨(i : ℕ) - k, by omega⟩

/-- Piece coordinate attached to variable `i` (junk for constant variables). -/
def coordOf (i : Fin (k + 2 + m)) : Fin (m + 2) := (piIdx i).elim (fun _ => 0) id

/-- Is variable `i` one whose coordinate is inverted? -/
def isBigB (σ : Fin (m + 2) → VC) (i : Fin (k + 2 + m)) : Bool :=
  (piIdx i).elim (fun _ => false) (fun j => decide (σ j = VC.big))

/-- The same flag over the two variable blocks (`inl` = value variables, `inr` = `rexp`
variables); `rexp` coordinates are never inverted. -/
def bigSum (σ : Fin (m + 2) → VC) : Fin (k + 2 + m) ⊕ Fin (k + 2 + m) → Bool :=
  Sum.elim (isBigB σ) (fun _ => false)

/-- The index of `x` in the `k+2+m` variables. -/
def idxX : Fin (k + 2 + m) := Fin.castAdd m (0 : Fin (k + 2))
/-- The index of `y`. -/
def idxY : Fin (k + 2 + m) := Fin.castAdd m (1 : Fin (k + 2))
/-- The index of the constant `c j`. -/
def idxC (j : Fin k) : Fin (k + 2 + m) := Fin.castAdd m (Fin.succ (Fin.succ j))
/-- The index of the witness `w j`. -/
def idxW (j : Fin m) : Fin (k + 2 + m) := Fin.natAdd (k + 2) j

/-! ## 2. The substitution -/

/-- True value of variable `i` at piece point `z`. -/
def valE (c : Fin k → ℝ) (σ : Fin (m + 2) → VC) (i : Fin (k + 2 + m))
    (z : Fin (m + 2) → ℝ) : ℝ :=
  (piIdx i).elim (fun j => c j) (fun j => if σ j = VC.big then (z j)⁻¹ else z j)

/-- Cleared (entire) version of the value of variable `i` at piece point `z`. -/
def valC (c : Fin k → ℝ) (σ : Fin (m + 2) → VC) (i : Fin (k + 2 + m))
    (z : Fin (m + 2) → ℝ) : ℝ :=
  (piIdx i).elim (fun j => c j) (fun j => z j)

/-- Value substituted for `rexp` of variable `i`. -/
def rvE (c : Fin k → ℝ) (σ : Fin (m + 2) → VC) (i : Fin (k + 2 + m))
    (z : Fin (m + 2) → ℝ) : ℝ :=
  (piIdx i).elim (fun j => rexp (c j)) (fun j => if σ j = VC.big then 0 else Real.exp (z j))

/-- The (non-entire) slice equation: `P` evaluated at the substituted values. -/
def Efun (c : Fin k → ℝ) (σ : Fin (m + 2) → VC)
    (P : MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ)
    (z : Fin (m + 2) → ℝ) : ℝ :=
  MvPolynomial.eval (Sum.elim (fun i => valE c σ i z) (fun i => rvE c σ i z)) P

/-- One factor of the clearing factor, indexed by a variable of the two blocks. -/
def Kx (σ : Fin (m + 2) → VC) (D : ℕ) (z : Fin (m + 2) → ℝ)
    (x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) : ℝ :=
  if bigSum σ x then (z (Sum.elim coordOf coordOf x)) ^ D else 1

/-- The clearing factor, spread over the two variable blocks. -/
def Kall (σ : Fin (m + 2) → VC) (D : ℕ) (z : Fin (m + 2) → ℝ) : ℝ :=
  ∏ x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m), Kx σ D z x

/-- Exponent of one monomial after reversal for the inverted coordinates. -/
def ddExp (σ : Fin (m + 2) → VC) (D : ℕ)
    (d : Fin (k + 2 + m) ⊕ Fin (k + 2 + m) →₀ ℕ)
    (x : Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) : ℕ :=
  if bigSum σ x then D - d x else d x

theorem ddExp_support_finite (σ : Fin (m + 2) → VC) (D : ℕ)
    (d : Fin (k + 2 + m) ⊕ Fin (k + 2 + m) →₀ ℕ) :
    (Function.support (ddExp σ D d)).Finite := by
  refine (d.support.finite_toSet.union
    (Finset.finite_toSet ((Finset.univ : Finset (Fin (k + 2 + m) ⊕ Fin (k + 2 + m))).filter
      fun x => bigSum σ x))).subset ?_
  intro x hx
  simp only [Set.mem_union, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
    Finsupp.mem_support_iff, Function.mem_support] at hx ⊢
  by_cases hb : bigSum σ x = true
  · exact Or.inr hb
  · exact Or.inl (by simpa [ddExp, hb] using hx)

/-- The monomial exponent vector after reversal. -/
def ddMon (σ : Fin (m + 2) → VC) (D : ℕ)
    (d : Fin (k + 2 + m) ⊕ Fin (k + 2 + m) →₀ ℕ) :
    Fin (k + 2 + m) ⊕ Fin (k + 2 + m) →₀ ℕ :=
  Finsupp.ofSupportFinite (ddExp σ D d) (ddExp_support_finite σ D d)

/-- `P` with the exponents of the value variables of inverted coordinates reversed. -/
def clePoly (σ : Fin (m + 2) → VC) (D : ℕ)
    (P : MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ) :
    MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ :=
  ∑ d ∈ P.support, MvPolynomial.monomial (ddMon σ D d) (P.coeff d)

/-- The cleared, entire slice equation. -/
def Ppart (c : Fin k → ℝ) (σ : Fin (m + 2) → VC) (D : ℕ)
    (P : MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ)
    (z : Fin (m + 2) → ℝ) : ℝ :=
  MvPolynomial.eval (Sum.elim (fun i => valC c σ i z) (fun i => rvE c σ i z)) (clePoly σ D P)

/-! ## 3. The pieces -/

/-- Equation of the piece: the cleared equation, plus `z j ^ 2 = 1` for `one`-coordinates. -/
def pieceF (c : Fin k → ℝ) (σ : Fin (m + 2) → VC) (D : ℕ)
    (P : MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ)
    (z : Fin (m + 2) → ℝ) : ℝ :=
  (Ppart c σ D P z) ^ 2 +
    ∑ j : Fin (m + 2), if σ j = VC.one then (z j ^ 2 - 1) ^ 2 else 0

/-- Inequalities of the piece, indexed by `(coordinate, slot)`. -/
def pieceG (σ : Fin (m + 2) → VC) (j : Fin (m + 2)) (q : Fin 2) (z : Fin (m + 2) → ℝ) : ℝ :=
  if (j : ℕ) = 0 then (if (q : ℕ) = 0 then z 0 else 1 - z 0)
  else if σ j = VC.small then (if (q : ℕ) = 0 then 1 - (z j) ^ 2 else 1)
  else if σ j = VC.one then 1
  else if (q : ℕ) = 0 then (z j) ^ 2 else 1 - (z j) ^ 2

/-- The piece attached to a case assignment `Fin.cons VC.big σ'`. -/
def piece (c : Fin k → ℝ) (σ' : Fin (m + 1) → VC)
    (P : MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ) : LiftPiece where
  m := m
  l := (m + 2) * 2
  F := fun z => pieceF c (Fin.cons VC.big σ') P.totalDegree P z
  g := fun q z =>
    pieceG (Fin.cons VC.big σ') (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2 z
  inv := decide (σ' 0 = VC.big)

/-- The list of all pieces. -/
def pieceList (c : Fin k → ℝ)
    (P : MvPolynomial (Fin (k + 2 + m) ⊕ Fin (k + 2 + m)) ℝ) : List LiftPiece :=
  (Finset.univ : Finset (Fin (m + 1) → VC)).toList.map fun σ' => piece c σ' P

end Work.WilC4aL
