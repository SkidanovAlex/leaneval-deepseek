/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# New cases of the Magnus step: the two-letter torus-knot-type roots

This module records a family of roots for which the Magnus step
(`Work.OROneRel.MagnusStepData`, i.e. the conclusion of
`Work.OROneRel.magnus_step_root_no_eps_zero`) is *proved* through the Nielsen route of
`Submission/Work/OROneRel/magnusStepNielsenRoute.lean`.

The roots are the two-letter words `u = x ^ p y ^ q` with `p, q ≥ 2`.  These are precisely the
"hard" shape for the divisibility condition of the weighted Magnus step
(`Work.OROneRel.magnusStepCase2_of_weight`): for `u` itself, the condition
`∃ t, c, c t = 1 ∧ Σ_x c_x * eps_x u = 0` is solvable only when one of `p`, `q` divides the other.
The transvection `ψ : x ↦ x y ^ m`, `y ↦ y` (with `m < 0` chosen so that `p m + q = ±1`) produces
the image `ψ u = (x y ^ m) ^ p y ^ q`, whose exponent sums are `(p, ± 1)`; hence the weight with
`c x = 1`, `c y = -p/(pm+q)` kills `ψ u`, and the number of non-`x` letters of `ψ u` is
`(p-1)|m| + (m+q)`.  Whenever that number is smaller than `relatorNorm u = p + q`, the count form of
the weighted step (`Work.OROneRel.magnusStepCase2_of_weight_count`) applies to `ψ u` and the result
transports back to `u` (`Work.OROneRel.MagnusStepData.of_aut`), giving the Magnus step for `u` with
the *same* exponent `l`.

Cases covered include `(p,q) = (2,3), (2,5), (2,7), (3,4), (3,5), (3,7), (4,3), (4,5), (5,4)`;
the count is exactly `p + q` (so the family does not apply) for `(3,8)` and `(4,7)`.
-/
import Mathlib
import Submission.Work.OROneRel.magnusStepNielsenRoute
import Submission.Work.OROneRel.transvectionNielsenData
import Submission.Work.OROneRel.letterPow_mul_letterPow_hypotheses

namespace Work.OROneRel

universe u

/-- **A family of new cases: the two-letter torus-knot-type roots.**  For `p, q ≥ 2` and `m < 0` with
`p m + q = ±1` (so that the transvection `x ↦ x y ^ m`, `y ↦ y` produces an image whose exponent sums
are `(p, ±1)`, whence a weight of weight `1` on the letter `x` kills it), and provided the resulting
number `(p-1)|m| + (m+q)` of `y`-letters is smaller than `relatorNorm u = p + q`, the Magnus step
holds for `u = x ^ p y ^ q` and *every* `l ≥ 1`.

The two-letter roots are exactly the cases in which the divisibility condition fails for `u` itself
(no Nielsen transformation being available for free) and in which the `ℤ`-domain argument of the
literature is normally invoked; the hypotheses above select the sub-family reachable by a
transvection.  Solutions exist e.g. for `(p,q) = (2,3), (2,5), (3,4), (3,5), (3,7), (4,3), (5,4)`;
they fail (the count is exactly `p + q`) for `(3,8)` and `(4,7)`. -/
theorem magnusStepData_torusFamily (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (m : ℤ) (hm : m < 0)
    (hpm : (p : ℤ) * m + (q : ℤ) = 1 ∨ (p : ℤ) * m + (q : ℤ) = -1)
    (hcount : (p - 1) * m.natAbs + (m + (q : ℤ)).toNat < p + q) :
    ∀ (l : ℕ), 1 ≤ l →
      MagnusStepData ((FreeGroup.of (0 : Fin 2)) ^ p * (FreeGroup.of (1 : Fin 2)) ^ q) l := by
  intro l hl
  obtain ⟨hpp0, hcyc0, hnorm0, hbad0⟩ := letterPow_mul_letterPow_hypotheses p q hp hq
  obtain ⟨ψ, t, c, hpp, hcyc, hn', hbad, ht, hct, hcu, hbound⟩ :=
    transvectionNielsenData p q hp hq m hm hpm
  refine magnusStepData_of_count_image _ l hl hpp0 hcyc0 ?_ hbad0 ψ t c hpp hcyc hn' hbad ht
    hct hcu ?_
  · rw [hnorm0]; omega
  · rw [hnorm0]; omega

/-- **The trefoil case**: the Magnus step holds for `u = x ^ 2 * y ^ 3` (the trefoil group
`⟨x, y | x ^ 2 y ^ 3⟩`) for **every** `l ≥ 1`.  This is the smallest root in the residual of the
divisibility condition (`gcd {3} ∤ 2` and `gcd {2} ∤ 3`), reached here through the transvection
`x ↦ x y⁻¹`. -/
theorem magnusStepData_two_three :
    ∀ (l : ℕ), 1 ≤ l →
      MagnusStepData ((FreeGroup.of (0 : Fin 2)) ^ 2 * (FreeGroup.of (1 : Fin 2)) ^ 3) l :=
  magnusStepData_torusFamily 2 3 (by norm_num) (by norm_num) (-1) (by norm_num)
    (Or.inl (by norm_num)) (by decide)

/-- **`x ^ 3 y ^ 5`**: another root in the residual (`gcd {5} ∤ 3`, `gcd {3} ∤ 5`), reached through
the transvection `x ↦ x y⁻²` (the count is `7 < 8`). -/
theorem magnusStepData_three_five :
    ∀ (l : ℕ), 1 ≤ l →
      MagnusStepData ((FreeGroup.of (0 : Fin 2)) ^ 3 * (FreeGroup.of (1 : Fin 2)) ^ 5) l :=
  magnusStepData_torusFamily 3 5 (by norm_num) (by norm_num) (-2) (by norm_num)
    (Or.inr (by norm_num)) (by decide)

/-- **`x ^ 3 y ^ 7`**: reached through the transvection `x ↦ x y⁻²` (`3·(-2) + 7 = 1`, count
`2·2 + 5 = 9 < 10`). -/
theorem magnusStepData_three_seven :
    ∀ (l : ℕ), 1 ≤ l →
      MagnusStepData ((FreeGroup.of (0 : Fin 2)) ^ 3 * (FreeGroup.of (1 : Fin 2)) ^ 7) l :=
  magnusStepData_torusFamily 3 7 (by norm_num) (by norm_num) (-2) (by norm_num)
    (Or.inl (by norm_num)) (by decide)

end Work.OROneRel
