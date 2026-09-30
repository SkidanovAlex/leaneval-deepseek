/-
# The facet-row certificate of the cusp cube charts (W2)

The chart of the cube `a` maps the *whole vertical hyperplane* of a wall of the cube into the
facet hyperplane of the corresponding side of the truncated 24-cell.  With

* `fragRow S j = - (sideNormal S) j` for `j < 4` and `fragRow S 4 = 1`: the facet functional
  (`ℓ_S(P) = P 4 · sideSlack S (kleinOfHyp P)`),
* `cwFv a i side` the wall functional `w_W = e_i + c e_3 - c e_4`, `c = cubeCorner a i + side`,

the row relation

  `fragRow (wallSide a i side) ᵥ* chartMat a = wallMu a i side • cwFv a i side`

holds for all `48 × 3 × 2` walls (`wallMu a i side ∈ {±1, ±2}`); it is a finite verification by
`decide`.  Consequently `sideSlack (wallSide a i side) (chartKlein a (mkE4 y s)) = 0` on the wall
`y i = cubeCorner a i + side` (for heights `s ≥ 11/10`).

The table `wallMu` is generated; do not edit by hand.
-/
import Mathlib
import Submission.Work.RTOwed.cuspChartWallReflect
import Submission.Work.RTOwed.chartKlein_self_facet

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

open scoped Matrix BigOperators
open Set Topology Function

namespace Work.RTOwed

open SelfFacet

noncomputable section

/-- The facet functional of the side `S` of `Q̄`, as an integral row vector on `Fin 5`:
`ℓ_S(P) = P 4 - ∑_{j<4} (sideNormal S) j · P j`. -/
def fragRow (S : Fin 24) : Fin 5 → ℤ :=
  fun j => if h : (j : ℕ) < 4 then - Work.FoldInst.sideNormal S ⟨j, h⟩ else 1

@[simp] theorem fragRow_zero (S : Fin 24) : fragRow S 0 = - Work.FoldInst.sideNormal S 0 := rfl
@[simp] theorem fragRow_one (S : Fin 24) : fragRow S 1 = - Work.FoldInst.sideNormal S 1 := rfl
@[simp] theorem fragRow_two (S : Fin 24) : fragRow S 2 = - Work.FoldInst.sideNormal S 2 := rfl
@[simp] theorem fragRow_three (S : Fin 24) : fragRow S 3 = - Work.FoldInst.sideNormal S 3 := rfl
@[simp] theorem fragRow_four (S : Fin 24) : fragRow S 4 = 1 := rfl

/-- The side of the cube wall: `wallLo a i` for the lower face (`side = 0`), `wallHi a i` for the
upper one. -/
def wallSide (a : Fin 48) (i : Fin 3) (side : Fin 2) : Fin 24 :=
  if (side : ℕ) = 0 then wallLo a i else wallHi a i

/-- The proportionality constant of the facet row relation at each wall (`±1` or `±2`). -/
def wallMu : Fin 48 → Fin 3 → Fin 2 → ℤ := ![
    ![![2, -2],
      ![2, -2],
      ![2, -2]],
    ![![2, -2],
      ![2, -2],
      ![2, -2]],
    ![![2, -2],
      ![2, -2],
      ![2, -2]],
    ![![2, -2],
      ![2, -2],
      ![2, -2]],
    ![![2, -2],
      ![2, -2],
      ![2, -2]],
    ![![2, -2],
      ![2, -2],
      ![2, -2]],
    ![![2, -2],
      ![2, -2],
      ![2, -2]],
    ![![2, -2],
      ![2, -2],
      ![2, -2]],
    ![![2, -2],
      ![2, -2],
      ![2, -2]],
    ![![2, -2],
      ![2, -2],
      ![2, -2]],
    ![![2, -2],
      ![2, -2],
      ![2, -2]],
    ![![2, -2],
      ![2, -2],
      ![2, -2]],
    ![![2, -2],
      ![2, -2],
      ![2, -2]],
    ![![2, -2],
      ![2, -2],
      ![2, -2]],
    ![![2, -2],
      ![2, -2],
      ![2, -2]],
    ![![2, -2],
      ![2, -2],
      ![2, -2]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]],
    ![![1, -1],
      ![1, -1],
      ![1, -1]]
  ]

/-- **The finite verification (W2)**: the facet functional of the wall side is proportional to the
wall functional.  Identity of integer row vectors, verified over the `48 × 3 × 2` walls by
`decide`. -/
theorem cwFacetRow_pt : ∀ (a : Fin 48) (i : Fin 3) (side : Fin 2) (j : Fin 5),
    (Matrix.vecMul (fragRow (wallSide a i side)) (chartMat a)) j
      = wallMu a i side * cwFv a i side j := by
  decide

/-- The real form of the finite verification, entrywise. -/
theorem cwFacetRowR_pt (a : Fin 48) (i : Fin 3) (side : Fin 2) (j : Fin 5) :
    (Matrix.vecMul (fun k => (fragRow (wallSide a i side) k : ℝ)) (cwMat a)) j
      = (wallMu a i side : ℝ) * (cwFv a i side j : ℝ) := by
  have h := cwFacetRow_pt a i side j
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_five] at h
  simp only [Matrix.vecMul, dotProduct, Fin.sum_univ_five, cwMat, Matrix.of_apply]
  exact_mod_cast h

/-- The facet row relation on an arbitrary vector. -/
theorem fragRow_dotP (a : Fin 48) (i : Fin 3) (side : Fin 2) (P : Fin 5 → ℝ) :
    ∑ j : Fin 5, (fragRow (wallSide a i side) j : ℝ) * (cwMat a *ᵥ P) j
      = (wallMu a i side : ℝ) * ∑ j : Fin 5, (cwFv a i side j : ℝ) * P j := by
  calc ∑ j : Fin 5, (fragRow (wallSide a i side) j : ℝ) * (cwMat a *ᵥ P) j
      = (fun j => (fragRow (wallSide a i side) j : ℝ)) ⬝ᵥ (cwMat a *ᵥ P) := rfl
    _ = (Matrix.vecMul (fun j => (fragRow (wallSide a i side) j : ℝ)) (cwMat a)) ⬝ᵥ P :=
          (dotProduct_assoc (fun j => (fragRow (wallSide a i side) j : ℝ)) P (cwMat a)).symm
    _ = ∑ j : Fin 5,
          (Matrix.vecMul (fun j => (fragRow (wallSide a i side) j : ℝ)) (cwMat a)) j * P j := rfl
    _ = ∑ j : Fin 5, (wallMu a i side : ℝ) * (cwFv a i side j : ℝ) * P j :=
          Finset.sum_congr rfl fun j _ => by rw [cwFacetRowR_pt a i side]
    _ = (wallMu a i side : ℝ) * ∑ j : Fin 5, (cwFv a i side j : ℝ) * P j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => by ring

/-- The wall functional on the upper half space vector: `∑ w_W · Π(y,s) = (y i - c)/s`. -/
theorem cwFv_dot_hypOfUHS (a : Fin 48) (i : Fin 3) (side : Fin 2) {y : CuspE3} {s : ℝ}
    (hs : s ≠ 0) :
    ∑ j : Fin 5, (cwFv a i side j : ℝ) * Work.HypModel.hypOfUHS (mkE4 y s) j
      = (y i - (cwC a i side : ℝ)) / s := by
  rw [cwHyp y s]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [show (∑ j : Fin 5, (cwFv a i side j : ℝ) * ((2 * s)⁻¹ * cwU y s j))
        = (2 * s)⁻¹ * ∑ j : Fin 5, (cwFv a i side j : ℝ) * cwU y s j by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring]
  rw [cwFv_sum]
  field_simp

/-- **The facet identity**: the slack of the side `S` at the chart of the cube `a` is the facet
functional applied to the chart vector, divided by its last coordinate. -/
theorem sideSlack_chartKlein (a : Fin 48) (S : Fin 24) (q : CuspE4)
    (h4 : (cwMat a *ᵥ Work.HypModel.hypOfUHS q) 4 ≠ 0) :
    Work.FoldInst.sideSlack S (chartKlein a q)
      = ((cwMat a *ᵥ Work.HypModel.hypOfUHS q) 4)⁻¹ *
          ∑ j : Fin 5, (fragRow S j : ℝ) * (cwMat a *ᵥ Work.HypModel.hypOfUHS q) j := by
  rw [chartKlein, ← cwMat_eq]
  simp only [Work.FoldInst.sideSlack, Fin.sum_univ_four, Fin.sum_univ_five,
    fragRow_zero, fragRow_one, fragRow_two, fragRow_three, fragRow_four,
    Work.HypModel.kleinOfHyp_apply_zero, Work.HypModel.kleinOfHyp_apply_one,
    Work.HypModel.kleinOfHyp_apply_two, Work.HypModel.kleinOfHyp_apply_three]
  field_simp
  push_cast
  ring

/-- `uhsVec y s = 2s · Π(y,s)`. -/
theorem uhsVec_eq_smul_hypOfUHS (y : CuspE3) (s : ℝ) (hs : s ≠ 0) :
    uhsVec y s = (2 * s) • Work.HypModel.hypOfUHS (mkE4 y s) := by
  rw [hypOfUHS_mkE4 y s, smul_smul,
    mul_inv_cancel₀ (by simp [hs] : (2 * s) ≠ 0), one_smul]

/-- The fourth coordinate of the chart vector is `2s` times the fourth coordinate of the Möbius
chart vector of the cube. -/
theorem chartVec_four_eq (a : Fin 48) (y : CuspE3) (s : ℝ) (hs : s ≠ 0) :
    chartVec a y s 4 = 2 * s * (cwMat a *ᵥ Work.HypModel.hypOfUHS (mkE4 y s)) 4 := by
  have hR : chartMatR a = cwMat a := by rw [chartMatR, ← cwMat_eq]
  rw [chartVec, uhsVec_eq_smul_hypOfUHS y s hs, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul,
    hR]

/-- **The fourth coordinate of the chart vector of the cube `a` never vanishes** above the level
`11/10` (the certificate `cert4_pos` of the positivity of the quadratic form). -/
theorem cwMat_hypOfUHS_four_ne (a : Fin 48) {y : CuspE3} {s : ℝ} (hs : 11 / 10 ≤ s) :
    (cwMat a *ᵥ Work.HypModel.hypOfUHS (mkE4 y s)) 4 ≠ 0 := by
  have hs0 : s ≠ 0 := by linarith
  have hpos : 0 < chartVec a y s 4 := by
    rw [chartVec_eq a y s 4]
    exact quad_pos_of_pos (by exact_mod_cast Cq4_pos a) (certPos_bound_pos (cert4_pos a)) y s hs
  intro h
  rw [chartVec_four_eq a y s hs0, h, mul_zero] at hpos
  exact lt_irrefl _ hpos

/-- **The facet-row certificate (W2)**: the chart of the cube maps the whole vertical hyperplane of
the wall `{y i = cubeCorner a i + side}` into the facet hyperplane of the corresponding side. -/
theorem sideSlack_chartKlein_wall (a : Fin 48) (i : Fin 3) (side : Fin 2) {y : CuspE3} {s : ℝ}
    (hs : 11 / 10 ≤ s) (hy : y i = (cwC a i side : ℝ)) :
    Work.FoldInst.sideSlack (wallSide a i side) (chartKlein a (mkE4 y s)) = 0 := by
  rw [sideSlack_chartKlein a (wallSide a i side) (mkE4 y s) (cwMat_hypOfUHS_four_ne a hs),
    fragRow_dotP a i side (Work.HypModel.hypOfUHS (mkE4 y s)),
    cwFv_dot_hypOfUHS a i side (by linarith), hy]
  simp

end

end Work.RTOwed
