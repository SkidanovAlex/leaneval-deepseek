/-
  WilG4a — the diagonal/substitution set of the Ω-calculus.

  `Work.WilG0.diagSet n m ι` is the graph of the coordinate substitution `x ↦ x ∘ ι` inside
  `ℝ^{n+m}` (the surviving `n` coordinates first, the `m` substituted coordinates at the end).
  It is the common zero set of the polynomials `W_j - X_{ι j}`, i.e. of
  `diagPoly n m ι = Σ_j (X_{n+j} - X_{ι j})²`, which has total degree `≤ 2`.  Hence it is an
  `Ω`-set of format `n + m` (the ambient dimension) and degree `2`.

  The two algebraic inputs (the set identity and the degree bound) are proved here, together
  with the iterated `mono_D` push-forward of the degree; the target lemma is then a direct
  application of the `hyp` axiom of `SOMin`.
-/
import Mathlib
import Submission.Work.WilG0.Defs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4a

open Work.WilG0

/-- `diagSet` is exactly the zero set of the polynomial `diagPoly`.

The evaluation of `Σ_j (X_{n+j} - X_{ι j})²` at `z` is `Σ_j (z_{n+j} - z_{ι j})²`, a sum of
squares; such a sum vanishes iff every summand does, i.e. iff `z_{n+j} = z_{ι j}` for all `j`. -/
private theorem diagSet_eq_diagPoly (n m : ℕ) (ι : Fin m → Fin n) :
    diagSet n m ι = {z : Fin (n + m) → ℝ | MvPolynomial.eval z (diagPoly n m ι) = 0} := by
  ext z
  simp only [diagSet, Set.mem_ofPred_eq, diagPoly, map_sum, MvPolynomial.eval_sub,
    MvPolynomial.eval_X, MvPolynomial.eval_mul]
  constructor
  · intro h
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [h j, sub_self, mul_zero]
  · intro h j
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin m)),
        0 ≤ (z (Fin.natAdd n i) - z (Fin.castAdd m (ι i))) *
          (z (Fin.natAdd n i) - z (Fin.castAdd m (ι i))) :=
      fun i _ => mul_self_nonneg _
    have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h j (Finset.mem_univ j)
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h0)

/-- `diagPoly n m ι` has total degree at most `2`: it is a sum of products of two polynomials
of total degree at most `1`. -/
private theorem diagPoly_totalDegree_le_two (n m : ℕ) (ι : Fin m → Fin n) :
    (diagPoly n m ι).totalDegree ≤ 2 := by
  rw [diagPoly]
  refine le_trans (MvPolynomial.totalDegree_finsetSum Finset.univ
    (fun j => (MvPolynomial.X (Fin.natAdd n j) - MvPolynomial.X (Fin.castAdd m (ι j))) *
      (MvPolynomial.X (Fin.natAdd n j) - MvPolynomial.X (Fin.castAdd m (ι j))))) ?_
  rw [Finset.sup_le_iff]
  intro j _
  have h1 : MvPolynomial.totalDegree
      ((MvPolynomial.X (Fin.natAdd n j) - MvPolynomial.X (Fin.castAdd m (ι j)) :
        MvPolynomial (Fin (n + m)) ℝ)) ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
    omega
  have h2 := MvPolynomial.totalDegree_mul
    ((MvPolynomial.X (Fin.natAdd n j) - MvPolynomial.X (Fin.castAdd m (ι j)) :
      MvPolynomial (Fin (n + m)) ℝ))
    ((MvPolynomial.X (Fin.natAdd n j) - MvPolynomial.X (Fin.castAdd m (ι j)) :
      MvPolynomial (Fin (n + m)) ℝ))
  linarith

/-- Iterated monotonicity in the degree slot of `Ω`. -/
private theorem mono_D_le' (S : WilkiesDesign.SOMin) {F D n : ℕ} {X : Set (Fin n → ℝ)}
    (h : X ∈ S.Ω F D n) : ∀ {D' : ℕ}, D ≤ D' → X ∈ S.Ω F D' n :=
  fun {D'} hle => Nat.le_induction h (fun _ _ ih => S.mono_D ih) D' hle

theorem diagSet_mem (S : WilkiesDesign.SOMin) (n m : ℕ) (ι : Fin m → Fin n) : Work.WilG0.diagSet n m ι ∈ S.Ω (n + m) 2 (n + m) := by
  have hmem : Work.WilG0.diagSet n m ι ∈
      S.Ω (n + m) (Work.WilG0.diagPoly n m ι).totalDegree (n + m) := by
    rw [diagSet_eq_diagPoly n m ι]
    exact S.hyp (n + m) (diagPoly n m ι)
  exact mono_D_le' S hmem (diagPoly_totalDegree_le_two n m ι)

end Work.WilG4a
