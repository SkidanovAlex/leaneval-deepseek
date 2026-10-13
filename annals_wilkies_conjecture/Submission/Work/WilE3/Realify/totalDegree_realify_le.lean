/-
  annals_wilkies_conjecture, AREA E3, `Realify`: the total-degree bound for the realified system.

  On the chart, the realified equations of `Realify/Defs.lean` are
  `Wval^N · (eaEvalC c P (u + i v)).re` and its imaginary part, where `Wval = ∏_j (1 + t_j²)`.
  Khovanskii's bound for separable chains (`Work.WilE3.SepKhovanskiiLocal`) applies to these only
  once we know their *total degree* as polynomials in `(u, v, y, t)`, which is what this file
  supplies: it is `O (deg P + r N)`, uniformly in the chain coefficients and in the chart offsets.

  The bookkeeping is this.  Writing `monoNum N e m` for the image of the monomial of exponent
  vector `m`, and `rePoly`/`imPoly` for the coefficientwise parts,

  * `realifyRe N e P = ∑_{m ∈ P.support} P.coeff m • rePoly (monoNum N e m)` (`realifyRe_sum`),
    and the total degree of a finite sum of polynomials is at most the sup of the summands'
    (`MvPolynomial.totalDegree_finsetSum_le`), while `a • p` and the coefficientwise parts
    `rePoly`/`imPoly` never raise the total degree;
  * for `m ∈ P.support` the degree of `monoNum N e m` is at most `∑ m + 2 ∑_{j} m (inr j) + 2 r N`
    (`monoNum_totalDegree_le`), because each of the three factors of `monoNum` has bases of degree
    `1` (the `u + i v`), `3` (the `C (e j) * y_j * (1 + 2 i t_j - t_j²)`) and `2`
    (the clearing factor `1 + t_j²`);
  * `∑ m ≤ P.totalDegree` for `m ∈ P.support` (`MvPolynomial.le_totalDegree`), so altogether the
    degree is at most `3 * P.totalDegree + 2 r N ≤ 3 * P.totalDegree + 3 r (N + 1)`.

  The two supporting lemmas are proved in the sibling modules
  `Realify/rePoly_imPoly_totalDegree_le.lean` and `Realify/monoNum_totalDegree_le.lean`.
-/
import Mathlib
import Submission.Work.WilE3.Realify.EvalMain
import Submission.Work.WilE3.Realify.rePoly_imPoly_totalDegree_le
import Submission.Work.WilE3.Realify.monoNum_totalDegree_le

namespace Work.WilE3.Realify

theorem totalDegree_realify_le {k r : ℕ} (N : ℕ) (e : Fin r → ℝ)
    (Q : WilkiesDesign.E.EAPoly k r) :
    (Work.WilE3.Realify.realifyRe N e Q).totalDegree ≤ 3 * Q.totalDegree + 3 * r * (N + 1) ∧
    (Work.WilE3.Realify.realifyIm N e Q).totalDegree ≤ 3 * Q.totalDegree + 3 * r * (N + 1) := by
  -- The degree bound for a single monomial of the support of `Q`.
  have key : ∀ m ∈ Q.support,
      (monoNum (k := k) (r := r) N e m).totalDegree
        ≤ 3 * Q.totalDegree + 3 * r * (N + 1) := by
    intro m hm
    have h1 := monoNum_totalDegree_le (k := k) (r := r) N e m
    have h2 : (m.sum fun _ e => e) ≤ Q.totalDegree := MvPolynomial.le_totalDegree hm
    have h3 : (∑ j : Fin r, m (Sum.inr j)) ≤ Q.totalDegree := by
      have h : (∑ j : Fin r, m (Sum.inr j)) ≤ (m.sum fun _ e => e) := by
        rw [show (m.sum fun _ e => e) = ∑ a : Fin k ⊕ Fin r, m a from
          Finsupp.sum_fintype m (fun _ e => e) (fun i => rfl), Fintype.sum_sum_type]
        exact Nat.le_add_left _ _
      omega
    have h4 : 2 * r * N ≤ 3 * r * (N + 1) := by
      calc 2 * r * N ≤ 3 * r * N := Nat.mul_le_mul_right N (Nat.mul_le_mul_right r (by norm_num))
        _ ≤ 3 * r * (N + 1) := Nat.mul_le_mul_left (3 * r) (Nat.le_succ N)
    calc (monoNum (k := k) (r := r) N e m).totalDegree
        ≤ (m.sum fun _ e => e) + 2 * (∑ j : Fin r, m (Sum.inr j)) + 2 * r * N := h1
      _ ≤ Q.totalDegree + 2 * Q.totalDegree + 2 * r * N :=
          Nat.add_le_add (Nat.add_le_add h2 (Nat.mul_le_mul_left 2 h3)) le_rfl
      _ = 3 * Q.totalDegree + 2 * r * N := by ring
      _ ≤ 3 * Q.totalDegree + 3 * r * (N + 1) := Nat.add_le_add_left h4 _
  constructor
  · rw [realifyRe_sum]
    exact MvPolynomial.totalDegree_finsetSum_le (fun m hm =>
      (MvPolynomial.totalDegree_smul_le (Q.coeff m) _).trans
        ((rePoly_imPoly_totalDegree_le _).1.trans (key m hm)))
  · rw [realifyIm_sum]
    exact MvPolynomial.totalDegree_finsetSum_le (fun m hm =>
      (MvPolynomial.totalDegree_smul_le (Q.coeff m) _).trans
        ((rePoly_imPoly_totalDegree_le _).2.trans (key m hm)))

end Work.WilE3.Realify
