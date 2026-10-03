import Mathlib
import Submission.Work.FIPlan.Interface
import Submission.Commons.NumberTheory.GaussianInt.two_squares_repr_count_le_tau_of_pos

namespace Work.FITop4.Red5

open Finset

/-- The number of Gaussian integers in the box `gBox n = {|Re| ≤ n, |Im| ≤ n}` whose norm
`gnorm z = |z|²` equals `n` is at most `4 * d(n)`.

The set `{z : gnorm z = n}` is `Commons.NumberTheory.GaussianInt.elemF n`, whose cardinality is
`(targetF n).card`, and `two_squares_repr_count_le_tau_of_pos` bounds that by `4 * d(n)`.  The box
filter is a subset of `elemF n` (every point of `gBox n` with `gnorm = n` lies in `elemF n` since
`elemF n` is exactly the set of elements of norm `n`), so its cardinality is at most that of
`elemF n`. -/
theorem gauss_repr_card_le (n : ℕ) (hn : 1 ≤ n) :
    ((Work.FIPlan.gBox (n : ℤ)).filter (fun z : GaussianInt => Work.FIPlan.gnorm z = n)).card
      ≤ 4 * n.divisors.card := by
  -- The box-filtered set is contained in `elemF n = {z : gnorm z = n}`.
  have hsub : (Work.FIPlan.gBox (n : ℤ)).filter
        (fun z : GaussianInt => Work.FIPlan.gnorm z = n)
      ⊆ Commons.NumberTheory.GaussianInt.elemF n := by
    intro z hz
    rw [Finset.mem_filter] at hz
    exact (Commons.NumberTheory.GaussianInt.mem_elemF hn z).mpr hz.2
  have h1 : ((Work.FIPlan.gBox (n : ℤ)).filter
        (fun z : GaussianInt => Work.FIPlan.gnorm z = n)).card
      ≤ (Commons.NumberTheory.GaussianInt.elemF n).card := Finset.card_le_card hsub
  rw [← Commons.NumberTheory.GaussianInt.targetF_card_eq_elemF_card n] at h1
  -- `(targetF n).card ≤ 4 * d(n)` from the two-squares rep count.
  have hZ := Commons.NumberTheory.GaussianInt.two_squares_repr_count_le_tau_of_pos n hn
  have h2 : ((Commons.NumberTheory.GaussianInt.targetF n).card : ℤ)
      ≤ ((4 * n.divisors.card : ℕ) : ℤ) := by
    push_cast
    exact hZ
  have h3 : (Commons.NumberTheory.GaussianInt.targetF n).card ≤ 4 * n.divisors.card :=
    Nat.cast_le.mp h2
  exact le_trans h1 h3

end Work.FITop4.Red5
