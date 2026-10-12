import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Archimedean.Real.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/--

For an injective label map `n : ι → Fin 3 → ℤ` that is odd with respect to an
involution on `ι` (`n (-i) = -n i`) and a coefficient function `c` invariant
under the involution (`c (-i) = c i`), the "pairing" double sum that counts the
two pairings of a momentum (`n i = n j` and `n i = -n j`, weight `1/2` each)
collapses to the diagonal: `∑ i, c i ^ 2`.

The proof is row by row: for fixed `i` the two indicator sums each admit a
single nonzero term (`j = i` resp. `j = -i`) by injectivity of `n`, and the
values there are both `c i * c i` thanks to `hc`; the factor `1/2` is exactly
what turns `c i ^ 2 + c i ^ 2` back into `c i ^ 2`.

-/
theorem sum_pair_delta {ι : Type*} [Fintype ι] [DecidableEq ι] [InvolutiveNeg ι]
    (n : ι → Fin 3 → ℤ) (hn : Function.Injective n) (hneg : ∀ i, n (-i) = -n i)
    (c : ι → ℝ) (hc : ∀ i, c (-i) = c i) :
    (∑ i, ∑ j, c i * c j * (((if n i = n j then (1 : ℝ) else 0)
        + (if n i = -n j then (1 : ℝ) else 0)) / 2)) = ∑ i, (c i) ^ 2 := by
  refine Finset.sum_congr rfl fun i _ => ?_
  -- First pairing: only `j = i` survives.
  have h1 : (∑ j, c i * c j * (if n i = n j then (1 : ℝ) else 0)) = c i ^ 2 := by
    have h := Finset.sum_eq_single (s := Finset.univ)
      (f := fun j => c i * c j * (if n i = n j then (1 : ℝ) else 0)) i
      (fun j _ hj => by rw [if_neg (fun h => hj (hn h).symm), mul_zero])
      (fun h => absurd (Finset.mem_univ i) h)
    rw [h, if_pos rfl, mul_one]
    ring
  -- Second pairing: only `j = -i` survives.
  have h2 : (∑ j, c i * c j * (if n i = -n j then (1 : ℝ) else 0)) = c i ^ 2 := by
    have h := Finset.sum_eq_single (s := Finset.univ)
      (f := fun j => c i * c j * (if n i = -n j then (1 : ℝ) else 0)) (-i)
      (fun j _ hj => by
        have hne : ¬ (n i = -n j) := by
          intro hcon
          have e : i = -j := hn (by rw [hneg j, hcon])
          exact hj (by rw [e]; exact (neg_neg j).symm)
        rw [if_neg hne, mul_zero])
      (fun h => absurd (Finset.mem_univ (-i)) h)
    have hval : n i = -n (-i) := by rw [hneg i, neg_neg]
    rw [h, if_pos hval, mul_one, hc i]
    ring
  -- Split the row sum into the two indicator sums and divide by two.
  have hsplit : (∑ j, c i * c j * (((if n i = n j then (1 : ℝ) else 0)
        + (if n i = -n j then (1 : ℝ) else 0)) / 2))
      = ((∑ j, c i * c j * (if n i = n j then (1 : ℝ) else 0))
        + (∑ j, c i * c j * (if n i = -n j then (1 : ℝ) else 0))) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit, h1, h2]
  ring

end Work.BoseBoxFock
