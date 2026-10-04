import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.commutator_core

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `Hᵏ` energy of `∂_c ∂_d u` is controlled by the top-order `L²` bounds

The hypothesis of the target theorem bounds the `L²` norm of *every* `(k+1)`-fold iterated
partial derivative `∂^β u` (`β : Fin (k+1) → ι`) by a common constant `Q1`.  We have to
transfer this to the `H^{k-1}` energy of `∂_c ∂_d u`, i.e. to the sum of the `L²` norms of the
`(k-1)`-fold derivatives of `∂_c ∂_d u`.

The point is that this is *purely combinatorial*: for `l : Fin (k-1) → ι`,
`∂^l (∂_c ∂_d u) = ∂^{l ++ [c,d]} u` is again an iterated derivative of `u` of order `k+1`,
namely the one along the list `List.ofFn l ++ [c, d]`; and every list of length `k+1` is
`List.ofFn β` for the function `β i = q.get i`.  Hence each of the `(card ι)^{k-1}` summands of
`ENormSq (k-1) (∂_c ∂_d u)` is one of the summands of the hypothesis, and the factor
`(card ι)^{k-1}` is just the number of summands.

No smoothness of `u` is used: all the identities below are identities of the *definitions*
(`pd` and `pdList` are iterated `fderiv`s and do not commute the derivatives, so `∂^l ∂_c ∂_d`
and `∂^{l ++ [c,d]}` are literally the same term).
-/

noncomputable section

namespace Work.Diff.STE.Lead.GalTame

open MeasureTheory BigOperators Work.Diff.STE

/-- `ENormSq 0` is the `L²`-norm squared on the unit cube: there is exactly one `0`-fold
derivative and it is the function itself. -/
lemma ENormSq_zero_eq_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℂ) :
    ENormSq 0 f = ∫ x in unitCube, ‖f x‖ ^ 2 := by
  simp [ENormSq, pdVec, pdList]

/-- Two partial derivatives, read from the inside out, form the list `[c, d]`. -/
lemma pd_pd_eq_pdList {ι : Type*} [DecidableEq ι] (u : (ι → ℝ) → ℂ) (c d : ι) :
    pd c (pd d u) = pdList [c, d] u := rfl

/-- An iterated derivative along a `Fin`-index of length `k+1` is the iterated derivative along
the corresponding list: every list `q` of length `k+1` is `List.ofFn q.get`. -/
lemma pdVec_get_eq_pdList {ι : Type*} [DecidableEq ι] (k : ℕ) (u : (ι → ℝ) → ℂ) (q : List ι)
    (hlen : q.length = k + 1) :
    pdVec (k + 1) (fun i => q.get (Fin.cast hlen.symm i)) u = pdList q u := by
  have hq : List.ofFn (fun i : Fin (k + 1) => q.get (Fin.cast hlen.symm i)) = q :=
    (List.ofFn_congr hlen q.get).symm.trans (List.ofFn_get q)
  simp only [pdVec, hq]

/-- A block of `k-1` derivatives, followed by `∂_c ∂_d`, is a derivative of order `k+1`. -/
lemma pdVec_pd_pd_eq_pdList {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (u : (ι → ℝ) → ℂ) (c d : ι) (l : Fin (k - 1) → ι) :
    pdVec (k - 1) l (pd c (pd d u)) = pdList (List.ofFn l ++ [c, d]) u := by
  rw [pdVec, pd_pd_eq_pdList]
  exact (cm_pdList_append (List.ofFn l) [c, d] u).symm

theorem ENormSq_pd_pd_le {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (hk : 1 ≤ k)
    (u : (ι → ℝ) → ℂ) (c d : ι) (Q1 : ℝ) (hQ1 : 0 ≤ Q1)
    (h : ∀ (β : Fin (k + 1) → ι), Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec (k + 1) β u) ≤ Q1) :
    Work.Diff.STE.ENormSq (k - 1) (Work.Diff.STE.pd c (Work.Diff.STE.pd d u))
      ≤ (Fintype.card ι : ℝ) ^ (k - 1) * Q1 := by
  have hQ1' : (0 : ℝ) ≤ Q1 := hQ1
  -- Every summand of the left-hand side is one of the summands controlled by `h`.
  have hterm : ∀ l : Fin (k - 1) → ι,
      ∫ x in unitCube, ‖pdVec (k - 1) l (pd c (pd d u)) x‖ ^ 2 ≤ Q1 := by
    intro l
    set q : List ι := List.ofFn l ++ [c, d] with hq
    have hlen : q.length = k + 1 := by
      rw [hq]
      simp only [List.length_append, List.length_ofFn, List.length_cons, List.length_nil]
      omega
    have h1 : pdVec (k - 1) l (pd c (pd d u)) = pdList q u := by
      rw [hq]
      exact pdVec_pd_pd_eq_pdList k u c d l
    have h2 : pdVec (k + 1) (fun i => q.get (Fin.cast hlen.symm i)) u = pdList q u :=
      pdVec_get_eq_pdList k u q hlen
    rw [h1, ← h2, ← ENormSq_zero_eq_integral]
    exact h _
  calc ENormSq (k - 1) (pd c (pd d u))
      = ∑ l : Fin (k - 1) → ι, ∫ x in unitCube, ‖pdVec (k - 1) l (pd c (pd d u)) x‖ ^ 2 := rfl
    _ ≤ ∑ _l : Fin (k - 1) → ι, Q1 := Finset.sum_le_sum (fun l _ => hterm l)
    _ = (Fintype.card ι : ℝ) ^ (k - 1) * Q1 := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
        push_cast
        ring

end Work.Diff.STE.Lead.GalTame
