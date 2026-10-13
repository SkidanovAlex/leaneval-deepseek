/-
  WilE10 — `E10_subpf_to_rexp` (the `SubPf → RExpExist` direction): definitions.

  Given a restricted semi-Pfaffian set `X ⊆ ℝ^{n+m}` over an EA chain `c` with `r` chain
  functions, and `Z = projFirst n m '' X.set`, we must exhibit `psiV ⁻¹' Z` as the projection of
  the zero set of a single `rexp`-polynomial.

  The ingredients of the encoding:
  * the compactification is encoded through its graph, `u = psi x ↔ u ^ 2 * (1 + x ^ 2) = x ^ 2 ∧
    ∃ v, u * x = v ^ 2`;
  * the chain value `exp (c.ell j z)` is encoded by a witness `t_j` with `L_j * t_j = c.ell j z`,
    where `L_j` is a natural number bounding `|c.ell j z|` on the cube; on the cube
    `rexp (t_j) = exp (t_j)`, hence `rexp (t_j) ^ L_j = exp (c.ell j z)`;
  * the positivity atoms `0 < eaEval c g z` are encoded by witnesses `pw` with
    `eaEval c g z * pw ^ 2 = 1`.

  This file sets up the witness index type `Wit`, the substitution `subst` of an EA polynomial
  by the ambient coordinates, and the constraint polynomial `constrPoly` (a sum of squares whose
  vanishing encodes all the constraints at once).
-/
import Submission.Work.WilC0.Basic
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE10.Basic.abs_le_one_iff_exists_sq
import Submission.Work.WilE10.Basic.psi_eq_iff_sq_and_exists_sq
import Submission.Work.WilE10.Basic.exp_eq_rexp_pow
import Submission.Work.WilE10.Basic.pos_iff_exists_mul_sq_eq_one

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilE10.SubPfRexp

open WilkiesDesign WilkiesDesign.E
open Work.WilC0 (rexpEval RExPoly RExpExistI)

/-! ## 1. The witness index type -/

/-- The block of existential witnesses for one branch: `u` (candidates for `psi x`), `v` (sign
tags), `w` (the projected coordinates), `qq` (`|w| ≤ 1` tags), `t` (the values `ell_j z / L_j`),
`s` (`|t| ≤ 1` tags) and `pw` (positivity tags, one per positivity atom of the branch). -/
abbrev Wit (n m r P : ℕ) : Type :=
  Fin n ⊕ (Fin n ⊕ (Fin m ⊕ (Fin m ⊕ (Fin r ⊕ (Fin r ⊕ Fin P)))))

/-- The `u`-coordinate (candidate for `psi x`). -/
def Wit.uIdx {n m r P : ℕ} (a : Fin n) : Wit n m r P := Sum.inl a
/-- The `v`-coordinate (sign tag). -/
def Wit.vIdx {n m r P : ℕ} (a : Fin n) : Wit n m r P := Sum.inr (Sum.inl a)
/-- The `w`-coordinate (projected coordinate). -/
def Wit.wIdx {n m r P : ℕ} (b : Fin m) : Wit n m r P := Sum.inr (Sum.inr (Sum.inl b))
/-- The `qq`-coordinate (`|w| ≤ 1` tag). -/
def Wit.qqIdx {n m r P : ℕ} (b : Fin m) : Wit n m r P :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inl b)))
/-- The `t`-coordinate (`ell_j z / L_j`). -/
def Wit.tIdx {n m r P : ℕ} (j : Fin r) : Wit n m r P :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j))))
/-- The `s`-coordinate (`|t| ≤ 1` tag). -/
def Wit.sIdx {n m r P : ℕ} (j : Fin r) : Wit n m r P :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))))
/-- The `pw`-coordinate (positivity tag). -/
def Wit.pwIdx {n m r P : ℕ} (l : Fin P) : Wit n m r P :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr l)))))

variable {n m r : ℕ}

/-- The index, inside `Fin n ⊕ Wit n m r P`, of the `i`-th coordinate of `z = Fin.append u w`. -/
def coordIdx {P : ℕ} : Fin (n + m) → Fin n ⊕ Wit n m r P :=
  Fin.addCases (fun a => Sum.inr (Wit.uIdx a)) (fun b => Sum.inr (Wit.wIdx b))

/-! ## 2. The substitution of an EA polynomial by the ambient coordinates -/

/-- The variable `X (Sum.inl q)`, i.e. the raw coordinate `q` of the ambient vector. -/
def Xc {κ : Type} (q : κ) : MvPolynomial (κ ⊕ κ) ℝ := MvPolynomial.X (Sum.inl q)

/-- The variable `X (Sum.inr q)`, i.e. `rexp` of the raw coordinate `q`. -/
def Xr {κ : Type} (q : κ) : MvPolynomial (κ ⊕ κ) ℝ := MvPolynomial.X (Sum.inr q)

/-- The polynomial version of the chain function `c.ell j z`. -/
def ellPoly {P : ℕ} (c : EAChain (n + m) r) (j : Fin r) :
    MvPolynomial ((Fin n ⊕ Wit n m r P) ⊕ (Fin n ⊕ Wit n m r P)) ℝ :=
  ∑ i : Fin (n + m), MvPolynomial.C (c.a j i) * Xc (coordIdx i) + MvPolynomial.C (c.b j)

/-- The substitution sending the variable `Sum.inl i` of an EA polynomial to the ambient
coordinate holding `z i`, and the variable `Sum.inr j` to `rexp (t_j) ^ L_j`. -/
def substVar {P : ℕ} (c : EAChain (n + m) r) (L : Fin r → ℕ) :
    (Fin (n + m) ⊕ Fin r) → MvPolynomial ((Fin n ⊕ Wit n m r P) ⊕ (Fin n ⊕ Wit n m r P)) ℝ
  | Sum.inl i => Xc (coordIdx i)
  | Sum.inr j => Xr (Sum.inr (Wit.tIdx j)) ^ (L j)

/-- The substituted EA polynomial. -/
def subst {P : ℕ} (c : EAChain (n + m) r) (L : Fin r → ℕ) (f : EAPoly (n + m) r) :
    MvPolynomial ((Fin n ⊕ Wit n m r P) ⊕ (Fin n ⊕ Wit n m r P)) ℝ :=
  MvPolynomial.eval₂Hom (algebraMap ℝ _) (substVar c L) f

/-! ## 3. The cube bound on the chain functions -/

/-- A natural number bounding `|c.ell j z|` for every `z` in the cube: the ceiling of the sum of
the absolute values of the coefficients. -/
def Lbound {k : ℕ} (c : EAChain k r) (j : Fin r) : ℕ :=
  ⌈(∑ i : Fin k, |c.a j i|) + |c.b j|⌉₊

/-! ## 4. The constraint polynomial -/

/-- The index of a single constraint atom. The seven blocks are the `u`-relation, the
`v`-relation, the `w`-bound, the `t`-definition, the `t`-bound, the equations of the branch and
its positivity atoms. -/
abbrev ConstrIdx (n m r : ℕ) (B : Basic (n + m) r) : Type :=
  Fin n ⊕ (Fin n ⊕ (Fin m ⊕ (Fin r ⊕ (Fin r ⊕ (Fin B.eqs.length ⊕ Fin B.pos.length)))))

/-- The constraint atoms; `constrPoly` is the sum of their squares. -/
def constrAtom (c : EAChain (n + m) r) (L : Fin r → ℕ) (B : Basic (n + m) r) :
    ConstrIdx n m r B →
      MvPolynomial ((Fin n ⊕ Wit n m r B.pos.length) ⊕ (Fin n ⊕ Wit n m r B.pos.length)) ℝ
  | Sum.inl a => Xc (Sum.inr (Wit.uIdx a)) ^ 2 * (1 + Xc (Sum.inl a) ^ 2) - Xc (Sum.inl a) ^ 2
  | Sum.inr (Sum.inl a) =>
      Xc (Sum.inr (Wit.uIdx a)) * Xc (Sum.inl a) - Xc (Sum.inr (Wit.vIdx a)) ^ 2
  | Sum.inr (Sum.inr (Sum.inl b)) =>
      1 - Xc (Sum.inr (Wit.wIdx b)) ^ 2 - Xc (Sum.inr (Wit.qqIdx b)) ^ 2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl j))) =>
      MvPolynomial.C ((L j : ℝ)) * Xc (Sum.inr (Wit.tIdx j)) - ellPoly c j
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl j)))) =>
      1 - Xc (Sum.inr (Wit.tIdx j)) ^ 2 - Xc (Sum.inr (Wit.sIdx j)) ^ 2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl k))))) => subst c L (B.eqs.get k)
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr l))))) =>
      subst c L (B.pos.get l) * Xc (Sum.inr (Wit.pwIdx l)) ^ 2 - 1

/-- The constraint polynomial: the sum of the squares of the atoms. -/
def constrPoly (c : EAChain (n + m) r) (L : Fin r → ℕ) (B : Basic (n + m) r) :
    MvPolynomial ((Fin n ⊕ Wit n m r B.pos.length) ⊕ (Fin n ⊕ Wit n m r B.pos.length)) ℝ :=
  ∑ k : ConstrIdx n m r B, constrAtom c L B k ^ 2

/-- The set attached to one branch `B` of the DNF. -/
def branchSet (c : EAChain (n + m) r) (L : Fin r → ℕ) (B : Basic (n + m) r) :
    Set (Fin n → ℝ) :=
  {x | ∃ y : Wit n m r B.pos.length → ℝ, Sum.elim x y ∈ RExPoly (constrPoly c L B)}

end Work.WilE10.SubPfRexp
