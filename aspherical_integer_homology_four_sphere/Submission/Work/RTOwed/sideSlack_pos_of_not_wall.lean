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


namespace Work.RTOwed

open Work.RTOwed.chartKleinMem

/-!
# Strict positivity of the side slacks of the cube chart off the walls

`chartKlein_mem` proves that the chart `chartKlein a (mkE4 x s)` of a cube `a` at a point `x` of its
closed unit cube and a height `s ∈ [11/10, ceilH a x]` lies in `Q̄`: every side slack is
non-negative.  The lower bound used is the certificate `certS a S`.

Here we need the *strict* statement for the sides `S` that are not walls of the cube: the only side
constraints that may be tight at the chart point are the six wall sides `wallLo a i`, `wallHi a i`.
This is the strict form of the certificate: for those `S` the certificate `certS a S` is strictly
positive (a finite check, `certS_pos_of_not_wall`), and each of the three bound arguments of
`chartKlein_mem` upgrades to a strict one, so `Nside a S x s > 0` on the whole closed region, whence
the slack is positive (`sideSlack_eq`).

## The strict certificates

The three real inequalities `certPos_bound`, `certZero_bound`, `certNeg_bound` of `chartKlein_mem`
have strict counterparts `certPos_bound_pos`, `certZero_bound_pos`, `certNeg_bound_pos`; the two
bounds `affine_nonneg`/`ceiling_nonneg` likewise (`affine_pos_of_pos`, `ceiling_pos_of_pos`).
-/

/-- **The certificate of the side constraint is strictly positive off the walls of the cube.** -/
theorem certS_pos_of_not_wall :
    ∀ (a : Fin 48) (S : Fin 24),
      (∀ i : Fin 3, S ≠ wallLo a i ∧ S ≠ wallHi a i) → 0 < certS a S := by
  decide +kernel

/-- A positive `certZero` is the strict form of the `c = 0` certificate. -/
theorem certZero_bound_pos {e : ℤ} {l lc : Fin 3 → ℤ} (h : 0 < certZero e l lc) :
    0 < (e:ℝ) + ∑ j : Fin 3, min ((l j : ℝ)) 0 + ∑ j : Fin 3, (l j : ℝ) * (lc j : ℝ) := by
  have heq : ((certZero e l lc : ℤ) : ℝ)
      = (e:ℝ) + ∑ j : Fin 3, min ((l j : ℝ)) 0 + ∑ j : Fin 3, (l j : ℝ) * (lc j : ℝ) := by
    simp only [certZero]
    push_cast
    ring
  rw [← heq]
  exact_mod_cast h

/-- A positive `certNeg` is the strict form of the `c < 0` certificate. -/
theorem certNeg_bound_pos {c e : ℤ} {l lc : Fin 3 → ℤ} (h : 0 < certNeg c e l lc) :
    0 < (∑ j : Fin 3, min (2*(c:ℝ)*((lc j : ℝ) + 1/2) + (l j : ℝ)) 0)
        + (c:ℝ) * (∑ j : Fin 3, (lc j : ℝ)^2) + (∑ j : Fin 3, (l j : ℝ) * (lc j : ℝ))
        + 3*(c:ℝ)/2 + (e:ℝ) := by
  have harg : ∀ j : Fin 3, (2 * (c:ℝ) * (lc j : ℝ) + (c:ℝ) + (l j : ℝ))
      = 2*(c:ℝ)*((lc j : ℝ) + 1/2) + (l j : ℝ) := fun j => by ring
  have heq : ((certNeg c e l lc : ℤ) : ℝ) / 2
      = (∑ j : Fin 3, min (2*(c:ℝ)*((lc j : ℝ) + 1/2) + (l j : ℝ)) 0)
        + (c:ℝ) * (∑ j : Fin 3, (lc j : ℝ)^2) + (∑ j : Fin 3, (l j : ℝ) * (lc j : ℝ))
        + 3*(c:ℝ)/2 + (e:ℝ) := by
    simp only [certNeg, Fin.sum_univ_three]
    push_cast
    rw [harg 0, harg 1, harg 2]
    ring
  rw [← heq]
  exact div_pos (by exact_mod_cast h) (by norm_num)

/-- **The strict `c = 0` bound.**  An affine function on the cube is bounded below by its minimum;
a positive minimum makes it strictly positive. -/
theorem affine_pos_of_pos {e : ℝ} {l : Fin 3 → ℝ} {lc : Fin 3 → ℝ}
    (hcert : 0 < e + ∑ j : Fin 3, min (l j) 0 + ∑ j : Fin 3, l j * lc j) :
    ∀ x : CuspE3, (∀ j, lc j ≤ x j ∧ x j ≤ lc j + 1) →
      0 < ∑ j : Fin 3, l j * x j + e := by
  intro x hx
  have hb : ∀ j : Fin 3, min (l j) 0 ≤ l j * (x j - lc j) :=
    fun j => min_le_mul _ _ (by linarith [(hx j).1]) (by linarith [(hx j).2])
  have hs' : ∑ j : Fin 3, min (l j) 0 ≤ ∑ j : Fin 3, l j * (x j - lc j) :=
    Finset.sum_le_sum fun j _ => hb j
  simp only [Fin.sum_univ_three] at hs' hcert ⊢
  linarith [hs', hcert]

/-- **The strict `c < 0` bound.**  Below the ceiling the quadratic is at least its value at the
ceiling, which is affine in `x` with a positive minimum. -/
theorem ceiling_pos_of_pos {c e : ℝ} {l : Fin 3 → ℝ} {lc : Fin 3 → ℝ} (hc : c ≤ 0)
    (hcert : 0 < (∑ j : Fin 3, min (2*c*(lc j + 1/2) + l j) 0) + c * (∑ j : Fin 3, (lc j)^2)
        + (∑ j : Fin 3, l j * lc j) + 3*c/2 + e) :
    ∀ x : CuspE3, (∀ j, lc j ≤ x j ∧ x j ≤ lc j + 1) → ∀ s : ℝ,
      s^2 ≤ 9/4 - ∑ j : Fin 3, (x j - (lc j + 1/2))^2 →
      0 < c * qsq x s + ∑ j : Fin 3, l j * x j + e := by
  intro x hx s hs
  have hcs : c * (9/4 - ∑ j : Fin 3, (x j - (lc j + 1/2))^2) ≤ c * s^2 := by nlinarith [hc]
  have hb : ∀ j : Fin 3, min (2*c*(lc j + 1/2) + l j) 0 ≤ (2*c*(lc j + 1/2) + l j) * (x j - lc j) :=
    fun j => min_le_mul _ _ (by linarith [(hx j).1]) (by linarith [(hx j).2])
  have hs' : ∑ j : Fin 3, min (2*c*(lc j + 1/2) + l j) 0
      ≤ ∑ j : Fin 3, (2*c*(lc j + 1/2) + l j) * (x j - lc j) :=
    Finset.sum_le_sum fun j _ => hb j
  have hid : c * (∑ j : Fin 3, x j^2 + (9/4 - ∑ j : Fin 3, (x j - (lc j + 1/2))^2)) + ∑ j : Fin 3, l j * x j + e
      = ∑ j : Fin 3, (2*c*(lc j + 1/2) + l j) * x j
        + (9*c/4 - c * ∑ j : Fin 3, (lc j + 1/2)^2 + e) := by
    simp only [Fin.sum_univ_three]
    ring
  have hid2 : ∑ j : Fin 3, (2*c*(lc j + 1/2) + l j) * lc j
      + (9*c/4 - c * ∑ j : Fin 3, (lc j + 1/2)^2 + e)
      = c * (∑ j : Fin 3, (lc j)^2) + (∑ j : Fin 3, l j * lc j) + 3*c/2 + e := by
    simp only [Fin.sum_univ_three]
    ring
  simp only [qsq, Fin.sum_univ_three] at hs' hid hid2 hcert hcs ⊢
  linarith [hs', hid, hid2, hcert, hcs]

/-! ## Strict positivity of the side numerator off the walls -/

/-- **The side numerator is strictly positive off the walls** of the cube, on the closed region
`{x ∈ cubeBox a, 11/10 ≤ s ≤ ceilH a x}`. -/
theorem Nside_pos_of_not_wall (a : Fin 48) (S : Fin 24) {x : CuspE3} (hx : x ∈ cubeBox a)
    {s : ℝ} (hs1 : 11 / 10 ≤ s) (hs2 : s ≤ ceilH a x)
    (hS : ∀ i : Fin 3, S ≠ wallLo a i ∧ S ≠ wallHi a i) : 0 < Nside a S x s := by
  have hcertpos : 0 < certS a S := certS_pos_of_not_wall a S hS
  have hx' : ∀ j : Fin 3, ((Work.Cusp.cubeCorner a j : ℝ)) ≤ x j
      ∧ x j ≤ ((Work.Cusp.cubeCorner a j : ℝ)) + 1 := hx
  rw [Nside_eq]
  by_cases hc : 0 < Qs a S
  · have hcert' : 0 < certPos (Qs a S) (Ks a S) (Ls a S) := by
      rw [certS] at hcertpos
      rw [if_pos hc] at hcertpos
      exact hcertpos
    exact quad_pos_of_pos (by exact_mod_cast hc) (certPos_bound_pos hcert') x s hs1
  · by_cases hc0 : Qs a S = 0
    · have hcert' : 0 < certZero (Ks a S) (Ls a S) (Work.Cusp.cubeCorner a) := by
        rw [certS] at hcertpos
        rw [if_neg hc, if_pos hc0] at hcertpos
        exact hcertpos
      have h0 : ((Qs a S : ℤ) : ℝ) = 0 := by rw [hc0]; norm_num
      rw [h0, zero_mul, zero_add]
      exact affine_pos_of_pos (certZero_bound_pos hcert') x hx'
    · have hclt : Qs a S < 0 := lt_of_le_of_ne (le_of_not_gt hc) hc0
      have hcert' : 0 < certNeg (Qs a S) (Ks a S) (Ls a S) (Work.Cusp.cubeCorner a) := by
        rw [certS] at hcertpos
        rw [if_neg hc, if_neg hc0] at hcertpos
        exact hcertpos
      exact ceiling_pos_of_pos (by exact_mod_cast hclt.le) (certNeg_bound_pos hcert')
        x hx' s (sq_le_ceiling a hx hs1 hs2)

/-- **The side slacks of the cube chart are strictly positive off the walls.** -/
theorem sideSlack_pos_of_not_wall (a : Fin 48) {u : CuspE3} (hu : u ∈ cubeBox a) {s : ℝ}
    (hs : 11 / 10 ≤ s) (hs2 : s ≤ ceilH a u) {S : Fin 24}
    (hS : ∀ i : Fin 3, S ≠ wallLo a i ∧ S ≠ wallHi a i) :
    0 < Work.FoldInst.sideSlack S (chartKlein a (mkE4 u s)) := by
  have hs0 : s ≠ 0 := by linarith
  have h4 : 0 < chartVec a u s 4 := chartVec4_pos a hu hs
  rw [sideSlack_eq a S u s hs0 h4.ne']
  exact div_pos (Nside_pos_of_not_wall a S hu hs hs2 hS) h4

end Work.RTOwed
