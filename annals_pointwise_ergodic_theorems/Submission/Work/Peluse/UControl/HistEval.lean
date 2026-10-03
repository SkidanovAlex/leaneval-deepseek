import Mathlib
import Submission.Work.Peluse.UControl.HistInit

/-!
# Evaluating the history shift

`HistData.shift h = Σ_{i : h i} a_i` is the polynomial whose evaluation at a concrete parameter is
the subset sum that the datum's directions `dir D d (lc P) 1 ω` produce.  This file records the
evaluation (`histShift_eval`) and the corresponding form of `Phase1Terminal`
(`phase1Terminal_dir`): the terminal leading coefficient of the slot `(P,h)` is the datum's
direction at the subset `{i : h i}`.

The datum is `D` with `S 0` an arbitrary nonempty type and `S 1 = Fin n`, the attachment
`par 0 : S 1 → I 0` being the constant map; then
`dir D d c 1 ω a = Σ_{s ∈ ω} (d - 0)·dir D d c 0 _ a · a(1) s = d·c·Σ_{s∈ω} a(1)s`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Polynomial

lemma histShift_eval {n : ℕ} (a : Fin n → ℤ) (h : Fin n → Bool) :
    MvPolynomial.eval a (HistData.shift h)
      = ∑ i ∈ Finset.univ.filter (fun i : Fin n => h i), a i := by
  classical
  rw [HistData.shift, map_sum]
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hi : h i <;> simp [hi]

/-- The evaluation of the terminal leading coefficient, in the form of a subset sum. -/
lemma phase1Terminal_lc_eval {d n : ℕ} {lc : ℤ} {Y : HistData d (n + 1)}
    (hT : Phase1Terminal d (n + 1) lc Y) (a : Fin (n + 1) → ℤ)
    {h : Fin (n + 1) → Bool} (hh : h ≠ 0) :
    MvPolynomial.eval a ((Y.Q (Sum.inr 0 : InitIdx d) h).leadingCoeff)
      = (d : ℤ) * lc * ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => h i), a i := by
  obtain ⟨h1, h2⟩ := hT
  have hlive := h2 h hh
  obtain ⟨-, -, -, hlc⟩ := h1 _ hlive
  rw [hlc, map_mul, map_mul, histShift_eval]
  simp [MvPolynomial.eval_C]

end

end Work.Peluse.UControl
