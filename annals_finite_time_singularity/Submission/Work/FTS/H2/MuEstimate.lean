import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Construction.MufunS

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2

/-- `1 ≤ α^c` for `c ≤ 0` when `0 < α ≤ 1`; equivalently `α^z ≤ α^y` for `y ≤ z`.  This is
`Work.Construction.rpow_le_of_le_one`, reproved here to avoid importing the whole
`Apriori` chapter. -/
private theorem rpow_le_of_le_one' {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {y z : ℝ}
    (hyz : y ≤ z) : α ^ z ≤ α ^ y := by
  have h : α ^ z = α ^ y * α ^ (z - y) := by
    rw [← Real.rpow_add hα]
    ring_nf
  rw [h]
  calc α ^ y * α ^ (z - y) ≤ α ^ y * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hα.le y)
        exact Real.rpow_le_one hα.le hα1 (by linarith)
    _ = α ^ y := by ring

private theorem one_le_rpow_of_nonpos {α c : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hc : c ≤ 0) :
    1 ≤ α ^ c := by
  have h := rpow_le_of_le_one' hα hα1 (show c ≤ (0 : ℝ) from hc)
  rwa [Real.rpow_zero] at h

/-- The pure arithmetic of `muestimate`: for `0 < α ≤ 1` and `X ≥ 0`,
`(1/(2α))(2α² + 2αX + 2α^{-1/2}X² + X) ≤ 4(α + α^{-3/2}X + α^{-5/2}X²)`. -/
private theorem mu_arith {α X : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hX : 0 ≤ X) :
    (1 / (2 * α)) * (2 * α ^ 2 + 2 * (α * X) + 2 * (α ^ (-(1 / 2 : ℝ)) * X ^ 2) + X)
      ≤ 4 * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) := by
  have hX2 : 0 ≤ X ^ 2 := sq_nonneg X
  have hone1 : 1 ≤ α ^ (-(1 / 2 : ℝ)) :=
    one_le_rpow_of_nonpos hα hα1 (by norm_num)
  have hle13 : α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(3 / 2 : ℝ)) :=
    rpow_le_of_le_one' hα hα1 (show (-(3 / 2 : ℝ)) ≤ (-(1 / 2 : ℝ)) by norm_num)
  have e1 : α * α ^ (-(3 / 2 : ℝ)) = α ^ (-(1 / 2 : ℝ)) := by
    nth_rewrite 1 [← Real.rpow_one α]
    rw [← Real.rpow_add hα]
    norm_num
  have e2 : α * α ^ (-(5 / 2 : ℝ)) = α ^ (-(3 / 2 : ℝ)) := by
    nth_rewrite 1 [← Real.rpow_one α]
    rw [← Real.rpow_add hα]
    norm_num
  have hA : 2 * α ^ 2 ≤ 8 * α ^ 2 := by nlinarith [sq_nonneg α]
  have hB : 2 * α * X + X ≤ 8 * (α ^ (-(1 / 2 : ℝ)) * X) := by
    have h : 2 * α + 1 ≤ 8 * α ^ (-(1 / 2 : ℝ)) := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h hX]
  have hC : 2 * α ^ (-(1 / 2 : ℝ)) * X ^ 2 ≤ 8 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_right hle13 hX2]
  have hfin : 8 * (α * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2))
      = 8 * α ^ 2 + 8 * (α ^ (-(1 / 2 : ℝ)) * X) + 8 * (α ^ (-(3 / 2 : ℝ)) * X ^ 2) := by
    rw [show α * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2)
        = α * α + (α * α ^ (-(3 / 2 : ℝ))) * X + (α * α ^ (-(5 / 2 : ℝ))) * X ^ 2 by ring]
    rw [e1, e2]
    ring
  have hB8 : 2 * α ^ 2 + 2 * (α * X) + 2 * (α ^ (-(1 / 2 : ℝ)) * X ^ 2) + X
      ≤ 8 * (α * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2)) := by
    linarith [hA, hB, hC, hfin]
  have hkey : (1 / (2 * α)) * (2 * α ^ 2 + 2 * (α * X) + 2 * (α ^ (-(1 / 2 : ℝ)) * X ^ 2) + X)
      ≤ (1 / (2 * α))
        * (8 * (α * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2))) :=
    mul_le_mul_of_nonneg_left hB8 (by positivity)
  have hsimp : (1 / (2 * α))
        * (8 * (α * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2)))
      = 4 * (α + α ^ (-(3 / 2 : ℝ)) * X + α ^ (-(5 / 2 : ℝ)) * X ^ 2) := by
    field_simp
    ring
  linarith [hkey, hsimp]

/-- Elgindi, Proposition `muestimate` (tex 1508): `|μ| ≤ C(α + α^{-3/2}|g|_{ℋ⁴} + α^{-5/2}|g|²_{ℋ⁴})`,
where the modulation constant is
`μ = (1/(2α))(L₁₂(N₀)(0) + L₁₂(N)(0)) + (1/(2α)) L₁₂(3 D_θ g/(1+z))(0)`
(the sign-corrected `Work.Construction.mufunS`, `FTS_MUFUN_SIGN.md` §5).

The paper proves this from the three `L₁₂(·)(0)`-estimates it has established for `N₀`, `N` and
`3 D_θ g/(1+z)`; those are supplied here as the three hypotheses, in the shapes produced by
`Work.FTS.H2.L12ZeroLe` applied to the term-by-term bounds of Propositions `N0Estimate` and
`NEstimate` (the second two terms of the paper's display are indeed over-estimates, as the
Remark after tex 1508 says).  The conclusion is then pure arithmetic: the triangle inequality
gives `|μ| ≤ α + X + α^{-3/2}X² + X/(2α)` with `X = HkNorm α 4 g`, and
`X ≤ α^{-3/2}X`, `X/(2α) ≤ ½α^{-3/2}X`, `α^{-3/2}X² ≤ α^{-5/2}X²` for `0 < α ≤ 1`
(`Work.Construction.rpow_le_of_le_one`).  -/
theorem MuEstimate : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (N0v Nv g : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 →
    |Work.Construction.L12 N0v 0| ≤ α ^ 2 + α * Work.Spaces.HkNorm α 4 g
        + α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 g ^ 2 →
    |Work.Construction.L12 Nv 0| ≤ α ^ 2 + α * Work.Spaces.HkNorm α 4 g
        + α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 g ^ 2 →
    |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0|
        ≤ Work.Spaces.HkNorm α 4 g →
    |Work.Construction.mufunS α N0v Nv g|
      ≤ C * (α + α ^ (-(3 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 g
        + α ^ (-(5 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 g ^ 2) := by
  refine ⟨4, by norm_num, ?_⟩
  intro α N0v Nv g hα hα1 h1 h2 h3
  set X := Work.Spaces.HkNorm α 4 g with hXdef
  have hX : 0 ≤ X := Work.Spaces.HkNorm_nonneg α 4 g
  -- `μ` is `(1/(2α))` times the *sum* of the three `L₁₂`-integrals (`mufunS`)
  have hmu : Work.Construction.mufunS α N0v Nv g
      = (1 / (2 * α)) * (Work.Construction.L12 N0v 0 + Work.Construction.L12 Nv 0
          + Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0) := by
    rw [Work.Construction.mufunS]
    ring
  -- triangle inequality for the three integrals (sign-free)
  have htri : |Work.Construction.L12 N0v 0 + Work.Construction.L12 Nv 0
        + Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0|
      ≤ |Work.Construction.L12 N0v 0| + |Work.Construction.L12 Nv 0|
        + |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0| := by
    linarith [abs_add_le (Work.Construction.L12 N0v 0) (Work.Construction.L12 Nv 0),
      abs_add_le (Work.Construction.L12 N0v 0 + Work.Construction.L12 Nv 0)
        (Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0)]
  -- the three hypotheses bound the three integrals
  have hstep : |Work.Construction.L12 N0v 0 + Work.Construction.L12 Nv 0
        + Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth g z θ / (1 + z)) 0|
      ≤ 2 * α ^ 2 + 2 * (α * X) + 2 * (α ^ (-(1 / 2 : ℝ)) * X ^ 2) + X := by
    linarith [htri, h1, h2, h3, hX]
  have hbound : |Work.Construction.mufunS α N0v Nv g|
      ≤ (1 / (2 * α)) * (2 * α ^ 2 + 2 * (α * X) + 2 * (α ^ (-(1 / 2 : ℝ)) * X ^ 2) + X) := by
    rw [hmu, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * α))]
    exact mul_le_mul_of_nonneg_left hstep (by positivity)
  exact le_trans hbound (mu_arith hα hα1 hX)

end Work.FTS.H2
