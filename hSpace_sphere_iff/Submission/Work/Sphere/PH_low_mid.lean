import Mathlib
import Submission.Work.Sphere.ProdRec
import Submission.Work.Sphere.H1_prod_sph_circle
import Submission.Work.Sphere.Values

namespace Work.Sphere

open Submission.Cohomology Submission.Sphere

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- The iterated degree shift: for `1 ≤ a < q`, `H^a(S^a × S^q; ℚ) ≅ ℚ`.  Proved by inducting
`a` down the degree shifts `prod_fst_shift`, the base case `a = 1` being `H1_prod_sph_circle`. -/
theorem PH_low_mid_aux (a q : ℕ) (ha : 1 ≤ a) (hq : a < q) :
    Nonempty (H (TopCat.toSSet.obj (TopProd (Sph a) (Sph q))) ℚ a ≃ₗ[ℚ] ℚ) := by
  revert ha q
  refine Nat.strong_induction_on a ?_
  intro a ih q ha hq
  rcases eq_or_lt_of_le ha with ha1 | ha2
  · subst ha1
    exact H1_prod_sph_circle q (by omega)
  · have hsub : (a - 1) + 1 = a := Nat.sub_add_cancel (by omega)
    obtain ⟨e⟩ := prod_fst_shift (a - 1) q (a - 1) (by omega)
      (sphere_subsingleton q (a - 1) (by omega) (by omega))
      (sphere_subsingleton q ((a - 1) + 1) (by omega) (by omega))
    rw [hsub] at e
    obtain ⟨e₂⟩ := ih (a - 1) (by omega) q (by omega) (by omega)
    exact ⟨e.trans e₂⟩

/-- The "lower middle" degree of the cohomology of `S^a × S^{a+1}` is one-dimensional: for
`a ≥ 1` the group `H^a(S^a × S^{a+1}; ℚ)` is `ℚ`.

Proof: iterate the degree shift `Work.Sphere.prod_fst_shift`
(`H^{k+1}(S^{n+1} × S^q) ≅ H^k(S^n × S^q)` for `k ≥ 1` when `S^q` is acyclic in degrees `k` and
`k+1`, the acyclicity hypotheses being discharged by `Work.Sphere.sphere_subsingleton`) from
`(n,q,k) = (a-1, a+1, a-1)` down to `(n,q,k) = (0, a+1, 1)`: this identifies
`H^a(S^a × S^{a+1})` with `H^1(S^1 × S^{a+1}) ≅ ℚ` (`Work.Sphere.H1_prod_sph_circle`).
For `a = 1` it is `H1_prod_sph_circle` directly. -/
theorem PH_low_mid (a : ℕ) (ha : 1 ≤ a) :
    Nonempty (Submission.Cohomology.H
      (TopCat.toSSet.obj (Work.Sphere.TopProd (Submission.Sphere.Sph a)
        (Submission.Sphere.Sph (a + 1)))) ℚ a
      ≃ₗ[ℚ] ℚ) :=
  PH_low_mid_aux a (a + 1) ha (by omega)

end

end Work.Sphere
