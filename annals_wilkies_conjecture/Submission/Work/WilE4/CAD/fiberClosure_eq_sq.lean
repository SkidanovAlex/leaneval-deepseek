import Mathlib
import Submission.Work.Wilkies.E.Spec

/-!
# Fibrewise closure via the squared Euclidean distance

`WilkiesDesign.E.fiberClosure X` is the set of points `z : ℝ^{p+q}` whose second
component `projSnd p q z` lies in the (topological) closure of the fibre of `X`
over `projFirst p q z`.

This file identifies that closure with the elementary ε-condition: a point is in
the fibrewise closure iff for every `ε > 0` there is a point of the fibre within
squared Euclidean distance `< ε²` of `projSnd p q z`.

The mathematical content is that on the finite product `Fin q → ℝ` (whose
topology is the product topology, induced by the sup-metric) the family of
sets `{y | ∑ i, (y i - y0 i)² < ε²}` is a neighbourhood basis at `y0`.
-/

set_option autoImplicit false

namespace Work.WilE4.CAD

open Filter

/-- A single coordinate contributes at most the whole sum of squares (all terms
are non-negative). -/
private lemma coord_le_sum_sq {q : ℕ} (y' y0 : Fin q → ℝ) (i : Fin q) :
    (y' i - y0 i) ^ 2 ≤ ∑ j, (y' j - y0 j) ^ 2 := by
  have := Finset.single_le_sum (s := Finset.univ) (f := fun j => (y' j - y0 j) ^ 2)
      (fun j _ => sq_nonneg (y' j - y0 j)) (Finset.mem_univ i)
  simpa using this

/-- `q` coordinates each of modulus `< ε/(q+1)` give a sum of squares `< ε²`. -/
private lemma nat_mul_div_sq_lt {q : ℕ} {ε : ℝ} (hε : 0 < ε) :
    (q : ℝ) * (ε / ((q : ℝ) + 1)) ^ 2 < ε ^ 2 := by
  have hsq : (0 : ℝ) < ((q : ℝ) + 1) ^ 2 := by positivity
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hq_lt : (q : ℝ) < ((q : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg (q : ℝ)]
  have he2 : 0 < ε ^ 2 := sq_pos_of_ne_zero (ne_of_gt hε : (ε : ℝ) ≠ 0)
  rw [div_pow, mul_div_assoc', div_lt_iff₀ hsq]
  nlinarith [hq_lt, he2]

/-- The squared-Euclidean balls form a neighbourhood basis at `y0` in `Fin q → ℝ`
(the product topology is the one induced by the sup-metric on a finite product). -/
private lemma sq_hasBasis {q : ℕ} (y0 : Fin q → ℝ) :
    (nhds y0).HasBasis (fun ε : ℝ => 0 < ε)
      (fun ε => {y' : Fin q → ℝ | ∑ i, (y' i - y0 i) ^ 2 < ε ^ 2}) := by
  refine (Metric.nhds_basis_ball).to_hasBasis ?_ ?_
  · rintro ε hε
    refine ⟨ε / 2, by linarith, ?_⟩
    intro y' hy'
    simp only [Metric.mem_ball] at hy' ⊢
    have h2 : |ε / 2| = ε / 2 := abs_of_nonneg (by linarith)
    have hii : ∀ i, dist (y' i) (y0 i) < ε / 2 := by
      intro i
      rw [Real.dist_eq, ← h2]
      exact sq_lt_sq.mp (lt_of_le_of_lt (coord_le_sum_sq y' y0 i) hy')
    have : dist y' y0 ≤ ε / 2 :=
      (dist_pi_le_iff (by linarith : (0 : ℝ) ≤ ε / 2)).mpr (fun i => le_of_lt (hii i))
    linarith
  · rintro ε hε
    refine ⟨ε / ((q : ℝ) + 1), by positivity, ?_⟩
    intro y' hy'
    simp only [Metric.mem_ball] at hy' ⊢
    have hii : ∀ i, (y' i - y0 i) ^ 2 < (ε / ((q : ℝ) + 1)) ^ 2 := by
      intro i
      rw [sq_lt_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ε / ((q : ℝ) + 1)),
        ← Real.dist_eq]
      exact lt_of_le_of_lt (dist_le_pi_dist y' y0 i) hy'
    have hsum_le : ∑ i : Fin q, (y' i - y0 i) ^ 2 ≤ (q : ℝ) * (ε / ((q : ℝ) + 1)) ^ 2 := by
      calc ∑ i : Fin q, (y' i - y0 i) ^ 2
          ≤ ∑ _i : Fin q, (ε / ((q : ℝ) + 1)) ^ 2 :=
            Finset.sum_le_sum (fun i _ => le_of_lt (hii i))
        _ = (q : ℝ) * (ε / ((q : ℝ) + 1)) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact lt_of_le_of_lt hsum_le (nat_mul_div_sq_lt hε)

theorem fiberClosure_eq_sq {p q : ℕ} (X : Set (Fin (p + q) → ℝ)) :
    WilkiesDesign.E.fiberClosure X =
      {z : Fin (p + q) → ℝ | ∀ ε : ℝ, 0 < ε → ∃ y' : Fin q → ℝ,
        Fin.append (WilkiesDesign.E.projFirst p q z) y' ∈ X ∧
          (Finset.univ.sum fun i : Fin q =>
            (y' i - WilkiesDesign.E.projSnd p q z i) ^ 2) < ε ^ 2} := by
  ext z
  simp only [WilkiesDesign.E.fiberClosure, WilkiesDesign.E.fiber, Set.mem_ofPred_eq]
  constructor
  · intro hz ε hε
    have hb := sq_hasBasis (WilkiesDesign.E.projSnd p q z)
    have hmem : {y' : Fin q → ℝ | ∑ i, (y' i - WilkiesDesign.E.projSnd p q z i) ^ 2 < ε ^ 2}
        ∈ nhds (WilkiesDesign.E.projSnd p q z) :=
      (hb.mem_iff).mpr ⟨ε, hε, fun x hx => hx⟩
    rcases (mem_closure_iff_nhds.mp hz _ hmem) with ⟨y', hy't, hy'X⟩
    exact ⟨y', hy'X, hy't⟩
  · intro h
    rw [mem_closure_iff_nhds]
    intro t ht
    rcases (sq_hasBasis (WilkiesDesign.E.projSnd p q z)).mem_iff.mp ht with ⟨ε, hε, hsub⟩
    rcases h ε hε with ⟨y', hy'X, hy'lt⟩
    exact ⟨y', hsub hy'lt, hy'X⟩

end Work.WilE4.CAD
