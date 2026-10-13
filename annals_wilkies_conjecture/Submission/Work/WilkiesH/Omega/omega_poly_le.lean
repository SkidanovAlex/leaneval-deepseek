import Mathlib
import Submission.Work.WilkiesH.Defs

/-!
# `Ω`-membership of polynomial sublevel sets

For a sharply o-minimal structure `S` (BNZ, *Wilkie's conjecture for Pfaffian structures*, §2.1)
the filtration `S.Ω F D n` contains all sets definable from the `n`-ary hypersurfaces by
complementation, projection, products and finite Boolean combinations, with the usual
cost in format `F` and degree `D`.

Here we show that the sublevel set `{x | P.eval x ≤ 0}` of a polynomial `P` in `n` variables
belongs to `S.Ω (n + 2) (P.totalDegree + 2) n`.

The point is that a *one-sided* (non-strict) inequality is obtained by a **single** projection,
with no complementation:

* `P.eval x ≤ 0` iff the equation `P.eval x + t ^ 2 = 0` has a real solution `t`
  (take `t = √(-P.eval x)` for `≤`, and read off `P.eval x = -t²` for `≥`).
* Hence `{x | P.eval x ≤ 0}` is the projection along the last coordinate of the zero set of
  the polynomial `polyLeAux n P = rename Fin.castSucc P + (last variable)²` in `n + 1`
  variables.
* A hypersurface sits in format `n + 1` with degree equal to the total degree (`SOMin.hyp`),
  projecting costs exactly one format and no degree (`SOMin.proj`), and the auxiliary
  polynomial has total degree `≤ P.totalDegree + 2`.

So the format is `(n + 1) + 1 = n + 2` and the degree is `P.totalDegree + 2`, as claimed.
-/

set_option autoImplicit false
noncomputable section

namespace Work.WilkiesH.Omega

/-- Auxiliary polynomial: `P` in the first `n` coordinates plus the square of the last
coordinate.  Its zero set projects, along the last coordinate, onto `{x | P.eval x ≤ 0}`. -/
def polyLeAux (n : ℕ) (P : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin (n + 1)) ℝ :=
  MvPolynomial.rename Fin.castSucc P + MvPolynomial.X (Fin.last n) ^ 2

/-- Evaluation of the auxiliary polynomial. -/
lemma eval_polyLeAux (n : ℕ) (P : MvPolynomial (Fin n) ℝ) (z : Fin (n + 1) → ℝ) :
    (polyLeAux n P).eval z = P.eval (Fin.init z) + (z (Fin.last n)) ^ 2 := by
  simp only [polyLeAux, MvPolynomial.eval_add, MvPolynomial.eval_pow, MvPolynomial.eval_X,
    MvPolynomial.eval_rename]
  rw [show (z ∘ Fin.castSucc) = Fin.init z from funext fun _ => rfl]

/-- The total degree of the auxiliary polynomial is at most `P.totalDegree + 2`. -/
lemma totalDegree_polyLeAux_le (n : ℕ) (P : MvPolynomial (Fin n) ℝ) :
    (polyLeAux n P).totalDegree ≤ P.totalDegree + 2 := by
  rw [polyLeAux]
  refine (MvPolynomial.totalDegree_add _ _).trans ?_
  rw [max_le_iff]
  refine ⟨(MvPolynomial.totalDegree_rename_le Fin.castSucc P).trans (Nat.le_add_right _ _), ?_⟩
  calc (MvPolynomial.X (Fin.last n) ^ 2 : MvPolynomial (Fin (n + 1)) ℝ).totalDegree
      = 2 := MvPolynomial.totalDegree_X_pow (Fin.last n) 2
    _ ≤ P.totalDegree + 2 := Nat.le_add_left 2 P.totalDegree

/-- Monotonicity of the degree index: raising `D` only helps. -/
private theorem mono_nat {S : WilkiesDesign.SOMin} {F D D' n : ℕ} {X : Set (Fin n → ℝ)}
    (h : X ∈ S.Ω F D n) (hD : D ≤ D') : X ∈ S.Ω F D' n :=
  Nat.le_induction h (fun _ _ ih => S.mono_D ih) D' hD

theorem omega_poly_le (S : WilkiesDesign.SOMin) (n : ℕ) (P : MvPolynomial (Fin n) ℝ) : {x : Fin n → ℝ | P.eval x ≤ 0} ∈ S.Ω (n + 2) (P.totalDegree + 2) n := by
  have hzero : {z : Fin (n + 1) → ℝ | (polyLeAux n P).eval z = 0}
      ∈ S.Ω (n + 1) (polyLeAux n P).totalDegree (n + 1) := S.hyp (n + 1) (polyLeAux n P)
  have hzero' : {z : Fin (n + 1) → ℝ | (polyLeAux n P).eval z = 0}
      ∈ S.Ω (n + 1) (P.totalDegree + 2) (n + 1) :=
    mono_nat hzero (totalDegree_polyLeAux_le n P)
  have hproj := S.proj hzero'
  have hset : WilkiesDesign.projLast {z : Fin (n + 1) → ℝ | (polyLeAux n P).eval z = 0}
      = {x : Fin n → ℝ | P.eval x ≤ 0} := by
    ext x
    simp only [WilkiesDesign.projLast, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht⟩
      rw [eval_polyLeAux, Fin.init_snoc, Fin.snoc_last] at ht
      nlinarith [sq_nonneg t]
    · intro hx
      refine ⟨Real.sqrt (- P.eval x), ?_⟩
      rw [eval_polyLeAux, Fin.init_snoc, Fin.snoc_last, Real.sq_sqrt (by linarith)]
      ring
  rw [hset] at hproj
  simpa using hproj

end Work.WilkiesH.Omega
