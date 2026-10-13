import Mathlib
import Submission.Work.WilG0.Defs

/-!
# The graph of a coordinate substitution is an `Ω`-set of format `n + m` and degree `2`

The set `diagSet n m ι ⊆ ℝ^{n+m}` (last `m` coordinates equal the first `n` composed with
`ι : Fin m → Fin n`) is the zero set of the polynomial `diagPoly n m ι = Σ_j (W_j - X_{ι j})²`,
which has total degree at most two.  Hence the `hyp` axiom of `SOMin` places it in
`S.Ω (n+m) 2 (n+m)`: the format is the number of variables of the polynomial, and the degree
is its total degree, raised to `2` by monotonicity in the degree slot.

The sum-of-squares form (rather than the intersection of the `m` hyperplanes) is what keeps the
degree at `2` independently of `m`.
-/

namespace Work.WilG0

open WilkiesDesign

/-- `Ω` is monotone in the degree bound. -/
private theorem omega_mono_D' (S : SOMin) {F D n : ℕ} {X : Set (Fin n → ℝ)}
    (hX : X ∈ S.Ω F D n) {D' : ℕ} (h : D ≤ D') : X ∈ S.Ω F D' n := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction e with
  | zero => simpa using hX
  | succ e ih => exact S.mono_D ih

/-- `diagSet n m ι` is the zero set of the sum of squares `diagPoly n m ι`. -/
private theorem diagSet_eq_zero' (n m : ℕ) (ι : Fin m → Fin n) :
    diagSet n m ι = {z : Fin (n + m) → ℝ | MvPolynomial.eval z (diagPoly n m ι) = 0} := by
  ext z
  simp only [diagSet, Set.mem_ofPred_eq, diagPoly, MvPolynomial.eval_sum]
  constructor
  · intro h
    refine Finset.sum_eq_zero fun j _ => ?_
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X, map_sub, h j]
    ring
  · intro h j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
      (f := fun i : Fin m =>
        MvPolynomial.eval z ((MvPolynomial.X (Fin.natAdd n i) - MvPolynomial.X (Fin.castAdd m (ι i))) *
          (MvPolynomial.X (Fin.natAdd n i) - MvPolynomial.X (Fin.castAdd m (ι i)))))
      (fun i _ => by
        simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X, map_sub]
        nlinarith [sq_nonneg (z (Fin.natAdd n i) - z (Fin.castAdd m (ι i)))])).mp h j
      (Finset.mem_univ j)
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_X, map_sub] at hj
    have hsq : (z (Fin.natAdd n j) - z (Fin.castAdd m (ι j))) ^ 2 = 0 := by nlinarith [hj]
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)

/-- `diagPoly n m ι` has total degree at most `2`, independently of `m`. -/
private theorem diagPoly_totalDegree_le' (n m : ℕ) (ι : Fin m → Fin n) :
    (diagPoly n m ι).totalDegree ≤ 2 := by
  rw [diagPoly]
  refine MvPolynomial.totalDegree_finsetSum_le (s := Finset.univ) (fun j _ => ?_)
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  have hlin : ∀ a b : Fin (n + m),
      (MvPolynomial.X a - MvPolynomial.X b : MvPolynomial (Fin (n + m)) ℝ).totalDegree ≤ 1 := by
    intro a b
    refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_X]
    simp
  have := hlin (Fin.natAdd n j) (Fin.castAdd m (ι j))
  omega

theorem diagSet_mem (S : WilkiesDesign.SOMin) (n m : ℕ) (ι : Fin m → Fin n) :
    diagSet n m ι ∈ S.Ω (n + m) 2 (n + m) := by
  rw [diagSet_eq_zero' n m ι]
  exact omega_mono_D' S (S.hyp (n + m) (diagPoly n m ι)) (diagPoly_totalDegree_le' n m ι)

end Work.WilG0
