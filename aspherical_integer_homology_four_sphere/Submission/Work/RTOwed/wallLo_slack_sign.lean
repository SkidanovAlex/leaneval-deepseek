import Mathlib
import Submission.Work.RTOwed.cuspChart
import Submission.Work.RTOwed.chartKlein_mem
import Submission.Work.RTOwed.cuspDev

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The sign of the lower-wall slack of the cusp charts

This file proves `Work.RTOwed.wallLo_slack_sign`: for a cube `a : Fin 48` of the cusp development,
a coordinate `i : Fin 3` and a height `s ≥ 11/10`, the *lower wall* side `wallLo a i` (the side of
`Q̄` through the truncated ideal vertex whose facet contains the face `{x i = cubeCorner a i}`) has,
at the chart point `chartKlein a (mkE4 u s)`, the sign of `u i - cubeCorner a i`.

## Method

Write `V = chartVec a u s` for the chart vector, so that
`sideSlack S (chartKlein a (mkE4 u s)) = Nside a S u s / V 4` (`chartKleinMem.sideSlack_eq`), the
numerator being the side functional applied to `V`.  For the wall sides the numerator is *exactly*
proportional to `u i - cubeCorner a i`:

  `Nside a (wallLo a i) u s = L * (u i - cubeCorner a i)`,  `L = Ls a (wallLo a i) i > 0`,

an identity of the quadratic forms `Nside_eq a (wallLo a i) u s` whose integer coefficients
(`Qs`, `Ls`, `Ks`) are pinned down by a finite check over the `48 × 3` walls (`decide`): the
quadratic coefficient `Qs` vanishes, the linear coefficients off the `i`-th coordinate vanish, and
the constant term is `-L · cubeCorner a i`.  Since the denominator `V 4` is positive for every `u`
and every `s ≥ 11/10` (the certificate `cert4_pos` giving the vertex bound `quad_pos_of_pos`), the
sign of the slack is the sign of `u i - cubeCorner a i`.
-/

namespace Work.RTOwed

open scoped BigOperators

open Work.RTOwed.chartKleinMem

/-! ### The finite coefficient check for the wall sides -/

/-- **The quadratic coefficient of the wall-side numerator vanishes.** -/
theorem wallLo_Qs_all : ∀ (a : Fin 48) (i : Fin 3), Qs a (wallLo a i) = 0 := by decide

/-- **The linear coefficients of the wall-side numerator off the `i`-th coordinate vanish.** -/
theorem wallLo_Ls_all : ∀ (a : Fin 48) (i j : Fin 3), j ≠ i → Ls a (wallLo a i) j = 0 := by decide

/-- **The constant term of the wall-side numerator.** -/
theorem wallLo_Ks_all : ∀ (a : Fin 48) (i : Fin 3),
    Ks a (wallLo a i) + Ls a (wallLo a i) i * Work.Cusp.cubeCorner a i = 0 := by decide

/-- **The remaining linear coefficient is strictly positive.** -/
theorem wallLo_Ls_pos_all : ∀ (a : Fin 48) (i : Fin 3), 0 < Ls a (wallLo a i) i := by decide

/-- **The wall-side numerator is `L · (u i - cubeCorner a i)`.** -/
theorem wallLo_Nside (a : Fin 48) (i : Fin 3) (x : CuspE3) (s : ℝ) :
    Nside a (wallLo a i) x s
      = (Ls a (wallLo a i) i : ℝ) * (x i - (Work.Cusp.cubeCorner a i : ℝ)) := by
  rw [Nside_eq]
  have hKs : Ks a (wallLo a i) = -(Ls a (wallLo a i) i) * Work.Cusp.cubeCorner a i := by
    have h := wallLo_Ks_all a i
    linarith
  have hsum : ∑ j : Fin 3, (Ls a (wallLo a i) j : ℝ) * x.ofLp j
      = (Ls a (wallLo a i) i : ℝ) * x.ofLp i := by
    refine Finset.sum_eq_single i ?_ ?_
    · intro j _ hj
      rw [wallLo_Ls_all a i j hj]; ring
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [wallLo_Qs_all a i, hKs, hsum]
  push_cast
  ring

/-- **The fourth chart coordinate is positive** for every cube coordinate `u` and every height
`s ≥ 11/10` (the certificate `cert4_pos` gives the vertex bound at `σ = 1`). -/
theorem chartVec4_pos_all (a : Fin 48) (x : CuspE3) {s : ℝ} (hs : 11 / 10 ≤ s) :
    0 < chartVec a x s 4 := by
  rw [chartVec_eq]
  exact quad_pos_of_pos (by exact_mod_cast Cq4_pos a)
    (certPos_bound_pos (cert4_pos a)) x s hs

/-! ### The sign of the wall slack -/

set_option linter.unusedVariables false in
theorem wallLo_slack_sign (a : Fin 48) (i : Fin 3) {u : CuspE3} {s : ℝ} (hs : 11 / 10 ≤ s)
    (hu : ∀ j : Fin 3, (Work.Cusp.cubeCorner a j : ℝ) - 1 ≤ u j
      ∧ u j ≤ (Work.Cusp.cubeCorner a j : ℝ) + 2) :
    (0 < Work.FoldInst.sideSlack (wallLo a i) (chartKlein a (mkE4 u s))
        ↔ (Work.Cusp.cubeCorner a i : ℝ) < u i) ∧
    (Work.FoldInst.sideSlack (wallLo a i) (chartKlein a (mkE4 u s)) = 0
        ↔ u i = (Work.Cusp.cubeCorner a i : ℝ)) ∧
    (Work.FoldInst.sideSlack (wallLo a i) (chartKlein a (mkE4 u s)) < 0
        ↔ u i < (Work.Cusp.cubeCorner a i : ℝ)) := by
  have hs0 : s ≠ 0 := by linarith
  have hVpos : 0 < chartVec a u s 4 := chartVec4_pos_all a u hs
  have hPpos : 0 < (Ls a (wallLo a i) i : ℝ) := by
    exact_mod_cast wallLo_Ls_pos_all a i
  set q : ℝ := (Ls a (wallLo a i) i : ℝ) / chartVec a u s 4 with hqdef
  have hq : 0 < q := div_pos hPpos hVpos
  have hkey : Work.FoldInst.sideSlack (wallLo a i) (chartKlein a (mkE4 u s))
      = q * (u i - (Work.Cusp.cubeCorner a i : ℝ)) := by
    rw [sideSlack_eq a (wallLo a i) u s hs0 hVpos.ne', wallLo_Nside]
    rw [hqdef]; ring
  rw [hkey]
  refine ⟨?_, ?_, ?_⟩
  · exact (mul_pos_iff_of_pos_left hq).trans sub_pos
  · rw [mul_eq_zero]
    constructor
    · rintro (h | h)
      · exact absurd h hq.ne'
      · exact sub_eq_zero.mp h
    · intro h; exact Or.inr (sub_eq_zero.mpr h)
  · have h := mul_lt_mul_iff_of_pos_left
      (a := q) (b := u i - (Work.Cusp.cubeCorner a i : ℝ)) (c := 0) hq
    rw [mul_zero] at h
    exact h.trans sub_neg

end Work.RTOwed
