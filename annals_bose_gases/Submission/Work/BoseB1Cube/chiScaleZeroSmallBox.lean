import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseB1Cube.half_le_norm_of_coord_abs_ge
import Submission.Work.BoseB1Cube.mul_sq_le_prod_fin3
import Submission.Work.BoseB1Cube.shortSideBetaGeom
import Submission.Work.BoseFixB1S.mfZeroHoleFixB1S
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

open scoped BigOperators

-- INTENDED PROOF SKETCH: with `w := (ℓd)•u`, `dlBox ℓ d u = ∏_j I_j` with `I_j ⊆ [−ℓ/2,ℓ/2]` the
-- intersection of `[−ℓ/2,ℓ/2]` with `[w_j − ℓd/2, w_j + ℓd/2]`, of length
-- `s_j := max 0 (Work.SmallBoxSliding.shortSide ℓ d u j)`.
-- (1) `Work.BoseFixB1S.oneBodyB1.sqrtW.boxMassProdB1` (needs `0 < d ≤ 1`) gives
--     `boxMass ℓ d u = ∏_j s_j`, and `Work.SmallBoxSliding.goodSet_shortSide` (needs `hreg`) gives
--     `μ^{-1/3} ≤ s_j` for every `j`.
-- (2) `μ·boxMass ≤ K` then gives `s_j ≤ K·μ^{-1/3}` for every `j`.
-- (3) `shortSide ℓ d u j = min (ℓ*d) (½ℓ(1+d) − |w_j|)`: either `s_j = ℓd` (excluded by `hshort`),
--     or `s_j = ½ℓ(1+d) − |w_j| ≤ Kμ^{-1/3}` and then each `x ∈ dlBox` satisfies
--     `x_j ≥ ℓ/2 − Kμ^{-1/3}` (when `w_j ≥ 0`) or `x_j ≤ −ℓ/2 + Kμ^{-1/3}` (when `w_j ≤ 0`).
-- (4) Hence `|x_j| ≥ ℓ/2 − Kμ^{-1/3}` for every `j`, so `‖x‖ ≥ √3(ℓ/2 − Kμ^{-1/3}) ≥ ℓ/2` by
--     `hbig`, and `Work.BoseFixB1S.chiScale_eq_zero_of_half_le_norm` (needs only `0 < ℓ`) closes.
theorem chiScaleZeroSmallBox {ℓ d μ K : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1)
    (hμ : 0 < μ) (hK : 0 < K)
    (hreg : μ ^ (-(1 / 3) : ℝ) ≤ ℓ * d)
    (hshort : 2 * K * μ ^ (-(1 / 3) : ℝ) ≤ ℓ * d)
    (hbig : 5 * K * μ ^ (-(1 / 3) : ℝ) ≤ ℓ)
    {u : EuclideanSpace ℝ (Fin 3)} (hu : u ∈ Work.SmallBoxSliding.goodSet ℓ d μ)
    (hU : μ * Work.SmallBoxSliding.boxMass ℓ d u ≤ K) :
    ∀ x ∈ Submission.BoseGases.dlBox ℓ d u, Submission.BoseGases.chiScale ℓ x = 0 := by
  intro x hx
  refine Work.BoseFixB1S.chiScale_eq_zero_of_half_le_norm hℓ ?_
  -- the shortest-side scale `δ := μ^{-1/3}`
  set δ : ℝ := μ ^ (-(1 / 3) : ℝ) with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact Real.rpow_pos_of_pos hμ _
  -- `δ³ = μ⁻¹`, hence `μ·δ² = δ⁻¹`
  have hδ3 : δ ^ 3 = μ⁻¹ := by
    rw [hδdef, ← Real.rpow_natCast (μ ^ (-(1 / 3) : ℝ)) 3, ← Real.rpow_mul hμ.le,
      show ((-(1 / 3) : ℝ) * ((3 : ℕ) : ℝ)) = (-1 : ℝ) by norm_num, Real.rpow_neg_one]
  have hμδ : μ * δ ^ 2 = δ⁻¹ := by
    have hcube : μ * δ ^ 3 = 1 := by rw [hδ3, mul_inv_cancel₀ (ne_of_gt hμ)]
    have h : (μ * δ ^ 2) * δ = 1 := by rw [← hcube]; ring
    exact eq_inv_of_mul_eq_one_left h
  -- (1) on the good set every side of `B(u)` is at least `δ`
  have hside : ∀ j : Fin 3, δ ≤ Work.SmallBoxSliding.shortSide ℓ d u j := by
    intro j
    have hreg'' : μ ^ (-1 / 3 : ℝ) ≤ ℓ * d := by
      rw [show (-1 : ℝ) / 3 = -(1 / 3 : ℝ) by norm_num]; exact hreg
    have h := Work.SmallBoxSliding.goodSet_shortSide hreg'' hu j
    rw [hδdef]
    rwa [show (-1 : ℝ) / 3 = -(1 / 3 : ℝ) by norm_num] at h
  have hprodcongr : (∏ j : Fin 3, max 0 (Work.SmallBoxSliding.shortSide ℓ d u j))
      = ∏ j : Fin 3, Work.SmallBoxSliding.shortSide ℓ d u j :=
    Finset.prod_congr rfl (fun j _ => max_eq_right (le_trans hδpos.le (hside j)))
  rw [Work.BoseFixB1S.oneBodyB1.sqrtW.boxMassProdB1 hℓ hd hd1 u, hprodcongr] at hU
  -- (2) the volume bound `μ·|B(u)| ≤ K` bounds every side by `K·δ`
  have hsle : ∀ j : Fin 3, Work.SmallBoxSliding.shortSide ℓ d u j ≤ K * δ := by
    intro j
    have hkey := mul_sq_le_prod_fin3 hδpos.le hside j
    have h1 : μ * (Work.SmallBoxSliding.shortSide ℓ d u j * δ ^ 2) ≤ K :=
      le_trans (mul_le_mul_of_nonneg_left hkey hμ.le) hU
    have h2 : Work.SmallBoxSliding.shortSide ℓ d u j * δ⁻¹ ≤ K := by
      have heq : μ * (Work.SmallBoxSliding.shortSide ℓ d u j * δ ^ 2)
          = Work.SmallBoxSliding.shortSide ℓ d u j * δ⁻¹ := by
        rw [← hμδ]; ring
      rwa [heq] at h1
    have h3 : (Work.SmallBoxSliding.shortSide ℓ d u j * δ⁻¹) * δ ≤ K * δ :=
      mul_le_mul_of_nonneg_right h2 hδpos.le
    rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hδpos), mul_one] at h3
    exact h3
  -- (3) consequently the centre coordinate is far from the origin in every direction,
  -- hence so is every coordinate of every `x ∈ B(u)`
  have hcoord : ∀ j : Fin 3, ℓ / 2 - K * δ ≤ |x.ofLp j| := by
    intro j
    have hslt : Work.SmallBoxSliding.shortSide ℓ d u j < ℓ * d := by
      have h2 : 2 * (K * δ) ≤ ℓ * d := by linarith [hshort]
      have h3 : 0 < K * δ := mul_pos hK hδpos
      have h1 : K * δ < ℓ * d := by linarith
      linarith [hsle j]
    have hsmin : min (ℓ * d) ((1 / 2) * ℓ * (1 + d) - |((ℓ * d) • u).ofLp j|) < ℓ * d := by
      have h := hslt
      rw [Work.SmallBoxSliding.shortSide] at h
      exact h
    have hA : (1 / 2) * ℓ * (1 + d) - |((ℓ * d) • u).ofLp j|
        = Work.SmallBoxSliding.shortSide ℓ d u j := by
      rcases min_lt_iff.mp hsmin with h' | h'
      · exact absurd h' (lt_irrefl _)
      · rw [Work.SmallBoxSliding.shortSide]
        exact (min_eq_right h'.le).symm
    have h2 : (1 / 2) * ℓ * (1 + d) - |((ℓ * d) • u).ofLp j| ≤ K * δ := by
      rw [hA]; exact hsle j
    have h3 : ℓ / 2 - K * δ ≤ |((ℓ * d) • u).ofLp j| - ℓ * d / 2 := by
      have heq : (1 / 2) * ℓ * (1 + d) - ℓ * d / 2 = ℓ / 2 := by ring
      linarith
    have h4 : ℓ / 2 - K * δ ≤ max 0 (|((ℓ * d) • u).ofLp j| - ℓ * d / 2) :=
      le_max_of_le_right h3
    exact le_trans h4 (Work.BoseB1Cube.max_sub_le_abs_coord hx j)
  -- (4) `√3(ℓ/2 - Kδ) ≥ ℓ/2` by the gate `5Kδ ≤ ℓ`
  exact half_le_norm_of_coord_abs_ge hℓ hbig hcoord

end Work.BoseB1Cube
