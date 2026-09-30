import Mathlib
import Submission.Work.BMF.linnik_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Newton's identity for a tuple of integers

We prove the classical Newton identity relating the elementary symmetric functions
`Work.BMF.esymm a ·` of a tuple `a : Fin k → ℤ` to its power sums `Work.BMF.pw a ·`:

`j * esymm a j = ∑_{i < j} (-1)^(j+1+i) * esymm a i * pw a (j - i)`.

The mathematical content is already available in Mathlib for the *multivariate
polynomial* elementary symmetric functions (`MvPolynomial.mul_esymm_eq_sum`); we
transport it to the concrete tuple by evaluating the polynomial at `a`. The two
bridging facts are that the evaluation of `MvPolynomial.esymm`/`MvPolynomial.psum`
at `a` recovers `Work.BMF.esymm a ·`/`Work.BMF.pw a ·` (immediate from the
definitions), together with a reshaping of the `Finset.antidiagonal`-indexed sum in
Newton's identity into a sum over `Finset.range j`.
-/

namespace Work.BMF.linnik

/-- The subset of the antidiagonal `{(i, j - i) : i + (j - i) = j}` consisting of the
pairs with first component `< j` is exactly the image of `range j` under `i ↦ (i, j - i)`. -/
private lemma antidiagonal_filter_eq_map (j : ℕ) :
    (Finset.HasAntidiagonal.antidiagonal j).filter (fun x : ℕ × ℕ => x.1 < j) =
      (Finset.range j).map ⟨fun i => (i, j - i), fun _ _ h => congrArg Prod.fst h⟩ := by
  ext x
  simp only [Finset.mem_filter, Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_map,
    Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨x.1, h2, ?_⟩
    exact Prod.ext rfl (by show j - x.1 = x.2; omega)
  · rintro ⟨i, hi, hix⟩
    rw [← hix]
    refine ⟨?_, hi⟩
    show i + (j - i) = j
    omega

/-- Evaluating the `j`-th elementary symmetric *polynomial* in `k` variables at the
tuple `a` gives the `j`-th elementary symmetric function `Work.BMF.esymm a j`. -/
private lemma eval_esymm {k : ℕ} (a : Fin k → ℤ) (j : ℕ) :
    MvPolynomial.eval a (MvPolynomial.esymm (Fin k) ℤ j) = Work.BMF.esymm a j := by
  simp [MvPolynomial.esymm, Work.BMF.esymm, MvPolynomial.eval_X]

/-- Evaluating the `j`-th power sum polynomial in `k` variables at the tuple `a` gives
the `j`-th power sum `Work.BMF.pw a j`. -/
private lemma eval_psum {k : ℕ} (a : Fin k → ℤ) (j : ℕ) :
    MvPolynomial.eval a (MvPolynomial.psum (Fin k) ℤ j) = Work.BMF.pw a j := by
  simp [MvPolynomial.psum, Work.BMF.pw, MvPolynomial.eval_X]

/-- **Newton's identity** for the tuple `a : Fin k → ℤ`: for every `j`,
`j * esymm a j = ∑_{i < j} (-1)^(j+1+i) * esymm a i * pw a (j - i)`. -/
theorem mul_esymm_eq_sum_range_pw {k : ℕ} (a : Fin k → ℤ) (j : ℕ) :
    (j : ℤ) * Work.BMF.esymm a j =
      ∑ i ∈ Finset.range j, (-1 : ℤ) ^ (j + 1 + i) * Work.BMF.esymm a i * Work.BMF.pw a (j - i) := by
  have h := MvPolynomial.mul_esymm_eq_sum (Fin k) ℤ j
  have h2 := congrArg (MvPolynomial.eval a) h
  simp only [map_mul, map_pow, map_sum, map_neg, map_one, map_natCast] at h2
  simp only [eval_esymm, eval_psum] at h2
  rw [h2]
  rw [antidiagonal_filter_eq_map, Finset.sum_map]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  show (-1 : ℤ) ^ (j + 1) * ((-1) ^ i * Work.BMF.esymm a i * Work.BMF.pw a (j - i)) =
      (-1 : ℤ) ^ (j + 1 + i) * Work.BMF.esymm a i * Work.BMF.pw a (j - i)
  have hp : (-1 : ℤ) ^ (j + 1) * (-1) ^ i = (-1 : ℤ) ^ (j + 1 + i) := by rw [← pow_add]
  rw [← hp]
  ring

end Work.BMF.linnik
