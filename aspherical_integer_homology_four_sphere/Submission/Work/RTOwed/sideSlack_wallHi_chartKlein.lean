import Mathlib
import Submission.Work.RTOwed.chartKlein_mem
import Submission.Work.RTOwed.cuspCertWalls
import Submission.Work.RTOwed.chartKlein_wall

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.RTOwed

open chartKleinMem

/-!
# The high wall of a cube is a facet of `Q̄` for the cube chart

The side numerator `Nside a S x s = V 4 - ∑ n_i V i` of the chart vector
`V = chartVec a x s = chartMat a *ᵥ uhsVec x s` is, by `Nside_eq`, the quadratic form

  `Nside a S x s = Qs a S · (∑ x_j² + s²) + ∑_j Ls a S j · x_j + Ks a S`.

For the *high* wall `S = wallHi a i` (the side through the truncated ideal vertex of the cube whose
facet is the face `{x i = cubeCorner a i + 1}`) the integer coefficients satisfy, for every cube `a`
and every direction `i`,

* `Qs a (wallHi a i) = 0` (no quadratic term),
* `Ls a (wallHi a i) j = 0` for `j ≠ i` (only the `i`-th coordinate survives),
* `Ls a (wallHi a i) i · (cubeCorner a i + 1) + Ks a (wallHi a i) = 0` (the surviving affine
  function vanishes exactly on the face `{x i = cubeCorner a i + 1}`).

Hence on the high wall the numerator is the single affine expression

  `Nside a (wallHi a i) x s = Ls a (wallHi a i) i · (x i - (cubeCorner a i + 1))`,

which vanishes as soon as `x i = cubeCorner a i + 1`.  Dividing by the (positive) fourth chart
coordinate `chartVec a x s 4` (`sideSlack_eq`, `chartVec4_pos`) gives the requested identity.
-/

/-- **The finite certificate of the high walls.**  The integer coefficients of the side numerator of
the high wall `wallHi a i` reduce to the single affine function vanishing on the face
`{x i = cubeCorner a i + 1}`. -/
theorem Nside_wallHi_cert : ∀ (a : Fin 48) (i : Fin 3),
    Qs a (wallHi a i) = 0
      ∧ (∀ j : Fin 3, j ≠ i → Ls a (wallHi a i) j = 0)
      ∧ Ls a (wallHi a i) i * ((Work.Cusp.cubeCorner a i : ℤ) + 1) + Ks a (wallHi a i) = 0 := by
  decide

/-- **The side numerator on the high wall is affine in the single coordinate `x i`.** -/
theorem Nside_wallHi_eq (a : Fin 48) (i : Fin 3) (x : CuspE3) (s : ℝ) :
    Nside a (wallHi a i) x s
      = (Ls a (wallHi a i) i : ℝ) * (x i - ((Work.Cusp.cubeCorner a i : ℝ) + 1)) := by
  obtain ⟨hQ, hL, hK⟩ := Nside_wallHi_cert a i
  have hsum : ∑ j : Fin 3, (Ls a (wallHi a i) j : ℝ) * x j
      = (Ls a (wallHi a i) i : ℝ) * x i := by
    refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
    rw [hL j hj]
    ring
  have hK' : (Ls a (wallHi a i) i : ℝ) * ((Work.Cusp.cubeCorner a i : ℝ) + 1)
      + (Ks a (wallHi a i) : ℝ) = 0 := by
    have h := congrArg (fun z : ℤ => (z : ℝ)) hK
    push_cast at h
    linarith [h]
  rw [Nside_eq, hQ, hsum]
  push_cast
  linarith [hK']

/-- **The high wall of the cube chart is tight.** (The main statement, in the numerator form.) -/
theorem Nside_wallHi_eq_zero (a : Fin 48) (i : Fin 3) {y : CuspE3} {s : ℝ}
    (hface : y i = (Work.Cusp.cubeCorner a i : ℝ) + 1) :
    Nside a (wallHi a i) y s = 0 := by
  rw [Nside_wallHi_eq, hface]
  ring

theorem sideSlack_wallHi_chartKlein (a : Fin 48) (i : Fin 3) {y : Work.RTOwed.CuspE3} {s : ℝ}
    (hy : y ∈ Work.RTOwed.cubeBox a)
    (hface : y i = (Work.Cusp.cubeCorner a i : ℝ) + 1)
    (hs : 11 / 10 ≤ s) :
    Work.FoldInst.sideSlack (Work.RTOwed.wallHi a i)
      (Work.RTOwed.chartKlein a (Work.RTOwed.mkE4 y s)) = 0 := by
  have hs0 : s ≠ 0 := by linarith
  have h4 : 0 < chartVec a y s 4 := chartVec4_pos a hy hs
  rw [sideSlack_eq a (wallHi a i) y s hs0 h4.ne',
    Nside_wallHi_eq_zero a i hface]
  ring

end Work.RTOwed
