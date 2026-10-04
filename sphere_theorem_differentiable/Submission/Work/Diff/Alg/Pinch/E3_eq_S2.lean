import Mathlib
import Submission.Work.Diff.Alg.Pinch.Q2Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The index identity `E3 = S2`

`Work.Diff.Alg.Pinch.Q2Defs` expands the two sides of

`Phi (Q2 R) X (bar X) = (Tmat R X * Rm R).trace`

into explicit sums `S1, S2` (left-hand side) and `E1, E2, E3, E4` (right-hand side).
The present file proves `E3 R X = S2 R X` for an algebraic curvature tensor `R`
(`Submission.Diff.Alg.IsAlgCurv`).

In components (`R i j k l = ⟪R(eᵢ,eⱼ)eₗ, eₖ⟫`),

* `E3 R X = ∑ i j k l b c, R i j k l · R c l i b · conj (X (b,j)) · X (k,c)`;
* `S2 R X = ∑ i j k l p q, R i p l q · R j p k q · X (i,j) · conj (X (k,l))`.

The proof is index manipulation, but not a single relabelling: relabel the six
summation indices of `S2` by the involution-like permutation

`(i',j',k',l',p',q') ↦ (i,j,k,l,b,c) = (f,d,a,e,c,b)`  (see `sig`/`sigInv`),

equivalently substitute `(i',j',k',l',p',q') = (k,c,b,j,l,i)` in `S2`.  The two
curvature factors become

`R k l j i = - R i j k l`  (swap the two pairs, then antisymmetry in the first pair)
`R c l b i = - R c l i b`  (antisymmetry in the second pair, via the pair symmetry),

and the two `-`-signs cancel, while the `X`-factors simply reorder by commutativity
of `ℂ`.  Both `E3` and `S2` are flattened to sums over three pairs of indices
(`Fintype.sum_prod_type`) and the relabelling is realised as an `Equiv` of the index
set, handled by `Equiv.sum_comp`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The index type of the flattened sums: three pairs. -/
private abbrev P (n : ℕ) := (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n)

/-- `E3` flattened to a sum over three pairs `(i,j)`, `(k,l)`, `(b,c)`. -/
private def e3F {n : ℕ} (R : Curv4 n) (X : Fin n × Fin n → ℂ) : P n → ℂ :=
  fun x => (R x.1.1 x.1.2 x.2.1.1 x.2.1.2 : ℂ) * (R x.2.2.2 x.2.1.2 x.1.1 x.2.2.1 : ℂ)
    * bar X (x.2.2.1, x.1.2) * X (x.2.1.1, x.2.2.2)

/-- `S2` flattened to a sum over three pairs `(i,j)`, `(k,l)`, `(p,q)`. -/
private def s2F {n : ℕ} (R : Curv4 n) (X : Fin n × Fin n → ℂ) : P n → ℂ :=
  fun x => (R x.1.1 x.2.2.1 x.2.1.2 x.2.2.2 : ℂ) * (R x.1.2 x.2.2.1 x.2.1.1 x.2.2.2 : ℂ)
    * X (x.1.1, x.1.2) * bar X (x.2.1.1, x.2.1.2)

/-- The involution-like relabelling realising `S2` in terms of `E3`: with
`x = ((i,j),(k,l),(b,c))` it sends `x` to `((k,c),(b,j),(l,i))`. -/
private def sig {n : ℕ} : P n → P n :=
  fun x => ((x.2.1.1, x.2.2.2), (x.2.2.1, x.1.2), (x.2.1.2, x.1.1))

/-- The inverse of `sig`: with `y = ((a,b),(c,d),(e,f))` it sends `y` to
`((f,d),(a,e),(c,b))`. -/
private def sigInv {n : ℕ} : P n → P n :=
  fun y => ((y.2.2.2, y.2.1.2), (y.1.1, y.2.2.1), (y.2.1.1, y.1.2))

/-- `sig` packaged as an equivalence (`sigInv` is a two-sided inverse). -/
private def sigEquiv {n : ℕ} : P n ≃ P n :=
  ⟨sig, sigInv,
    by rintro ⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩⟩; rfl,
    by rintro ⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩⟩; rfl⟩

/-- Exchanging the two pairs and the first pair's indices: `R c d b a = - R a b c d`
for an algebraic curvature tensor (pair symmetry followed by antisymmetry in the
first pair). -/
private lemma R_klji {n : ℕ} (R : Curv4 n) (hR : IsAlgCurv R) (a b c d : Fin n) :
    R c d b a = - R a b c d := by
  rw [hR.2.1 b a c d, hR.1 a b c d]

/-- Antisymmetry in the *second* pair, derived from the two axioms:
`R a b c d = - R a b d c`. -/
private lemma R_abdc {n : ℕ} (R : Curv4 n) (hR : IsAlgCurv R) (a b c d : Fin n) :
    R a b c d = - R a b d c := by
  rw [hR.2.1 c d a b, hR.1 d c a b, hR.2.1 a b d c]

/-- `E3` as a sum over three pairs of indices. -/
private lemma E3_flat {n : ℕ} (R : Curv4 n) (X : Fin n × Fin n → ℂ) :
    E3 R X = ∑ x, e3F R X x := by
  simp only [E3, e3F, Fintype.sum_prod_type]

/-- `S2` as a sum over three pairs of indices. -/
private lemma S2_flat {n : ℕ} (R : Curv4 n) (X : Fin n × Fin n → ℂ) :
    S2 R X = ∑ x, s2F R X x := by
  simp only [S2, s2F, Fintype.sum_prod_type]

/-- The pointwise identity `e3F = s2F ∘ sig`, using the two index symmetries of `R`
and commutativity of the product in `ℂ`. -/
private lemma e3F_eq_s2F {n : ℕ} (R : Curv4 n) (hR : IsAlgCurv R) (X : Fin n × Fin n → ℂ)
    (x : P n) : e3F R X x = s2F R X (sig x) := by
  have h1 : (R x.2.1.1 x.2.1.2 x.1.2 x.1.1 : ℂ)
      = - (R x.1.1 x.1.2 x.2.1.1 x.2.1.2 : ℂ) := by
    exact_mod_cast R_klji R hR x.1.1 x.1.2 x.2.1.1 x.2.1.2
  have h2 : (R x.2.2.2 x.2.1.2 x.2.2.1 x.1.1 : ℂ)
      = - (R x.2.2.2 x.2.1.2 x.1.1 x.2.2.1 : ℂ) := by
    exact_mod_cast R_abdc R hR x.2.2.2 x.2.1.2 x.2.2.1 x.1.1
  simp only [e3F, s2F, sig]
  rw [h1, h2]
  ring

theorem E3_eq_S2 (n : ℕ) (R : Submission.Diff.Alg.Curv4 n) (hR : Submission.Diff.Alg.IsAlgCurv R)
    (X : Fin n × Fin n → ℂ) :
    Work.Diff.Alg.Pinch.E3 R X = Work.Diff.Alg.Pinch.S2 R X := by
  rw [E3_flat R X, S2_flat R X]
  rw [← Equiv.sum_comp (sigEquiv (n := n)) (s2F R X)]
  apply Finset.sum_congr rfl
  intro x _
  exact e3F_eq_s2F R hR X x

end Work.Diff.Alg.Pinch
