import Mathlib
import Submission.Work.NAKANE2.Defs
import Submission.Work.NAKANE2.Surgery.gv_wirtinger

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.NAKANE2.Surgery

open LeanEval.ComplexAnalysis (Tantibar)

/-!
# The dilatation ratio of the Shishikura deformation `g_v`

`gv_wirtinger` computes the two Wirtinger derivatives of `g_v = σ_v ∘ T_{c₀}`:

`∂g_v z = v · (∂̄χ)(T_{c₀} z) · 2z`,   `∂̄g_v z = (1 + v · (∂χ)(T_{c₀} z)) · 2 star z`.

The derivative bound `D.hΛ` of the surgery datum gives `‖∂χ‖ ≤ Λ`, `‖∂̄χ‖ ≤ Λ`, while
`‖v‖ Λ ≤ 1/4` (from `hv` and `rConst D ≤ 1/(4Λ)`) forces
`‖1 + v · (∂χ)(T_{c₀} z)‖ ≥ 1 - ‖v‖ Λ ≥ 3/4`.  Dividing the two equalities the common
factor `‖2z‖ = 2‖z‖` cancels, and the inequality `Λ ≤ 2Λ · 3/4` is what makes the ratio
bound hold; the strict inequality away from `z = 0` comes from `‖v‖ Λ ≤ 1/4 < 3/4`.
-/

/-- The elementary real inequality behind `gv_ratio`: if `b ≤ L`, `L ≥ 0`, `a, c ≥ 0`,
`d ≥ 3/4` and `a L ≤ 1/4`, then `a b (2c) ≤ (2 L a)(d (2c))`, and strictly
`a b (2c) < d (2c)` when `c > 0`. -/
private lemma gv_ratio_aux {a b d c L : ℝ} (ha : 0 ≤ a) (hbL : b ≤ L) (hL : 0 ≤ L)
    (hc : 0 ≤ c) (hd : 3 / 4 ≤ d) (haL : a * L ≤ 1 / 4) :
    a * b * (2 * c) ≤ (2 * L * a) * (d * (2 * c)) ∧
      (0 < c → a * b * (2 * c) < d * (2 * c)) := by
  have h2c : (0 : ℝ) ≤ 2 * c := by linarith
  have hab : a * b ≤ a * L := mul_le_mul_of_nonneg_left hbL ha
  have h1 : a * b * (2 * c) ≤ a * L * (2 * c) := mul_le_mul_of_nonneg_right hab h2c
  have h2 : (0 : ℝ) ≤ a * L * (2 * c) := by positivity
  constructor
  · nlinarith [h1, h2, hd, hL, ha, h2c]
  · intro hcpos
    have h3 : a * L * (2 * c) ≤ (1 / 4) * (2 * c) := mul_le_mul_of_nonneg_right haL h2c
    have h4 : (3 / 4 : ℝ) * (2 * c) ≤ d * (2 * c) := mul_le_mul_of_nonneg_right hd h2c
    nlinarith [h1, h3, h4, hcpos]

theorem gv_ratio {c₀ : ℂ} (D : Work.NAKANE2.SurgeryData c₀) {v : ℂ} (hv : ‖v‖ < Work.NAKANE2.rConst D) :
    (∀ z : ℂ, ‖Work.MRMT.dz (Work.NAKANE2.gv c₀ D.χ v) z‖
        ≤ (2 * D.Λ * ‖v‖) * ‖Work.MRMT.dzbar (Work.NAKANE2.gv c₀ D.χ v) z‖) ∧
      (∀ z : ℂ, z ≠ 0 → ‖Work.MRMT.dz (Work.NAKANE2.gv c₀ D.χ v) z‖
        < ‖Work.MRMT.dzbar (Work.NAKANE2.gv c₀ D.χ v) z‖) := by
  have hΛpos : 0 < D.Λ := by linarith [D.hΛ1]
  have hΛnn : (0 : ℝ) ≤ D.Λ := le_of_lt hΛpos
  have hvΛ : ‖v‖ * D.Λ ≤ 1 / 4 := Work.NAKANE2.norm_mul_Λ_le D hv
  have hvn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  -- `‖∂̄χ‖ ≤ Λ` and `‖∂χ‖ ≤ Λ` everywhere
  have hdzbχ : ∀ w : ℂ, ‖Work.MRMT.dzbar (Work.NAKANE2.chiC c₀ D.χ) w‖ ≤ D.Λ :=
    fun w => Work.MRMT.QC.norm_dzbar_le_of_norm_fderiv_le (D.hΛ w)
  have hdzχ : ∀ w : ℂ, ‖Work.MRMT.dz (Work.NAKANE2.chiC c₀ D.χ) w‖ ≤ D.Λ :=
    fun w => Work.MRMT.QC.norm_dz_le_of_norm_fderiv_le (D.hΛ w)
  -- the lower bound `3/4 ≤ ‖1 + v ∂χ‖`
  have hlow : ∀ w : ℂ,
      (3 : ℝ) / 4 ≤ ‖(1 : ℂ) + v * Work.MRMT.dz (Work.NAKANE2.chiC c₀ D.χ) w‖ := by
    intro w
    have hB : ‖v * Work.MRMT.dz (Work.NAKANE2.chiC c₀ D.χ) w‖ ≤ 1 / 4 := by
      rw [norm_mul]
      exact le_trans (mul_le_mul_of_nonneg_left (hdzχ w) hvn) hvΛ
    have hsub : ((1 : ℂ) + v * Work.MRMT.dz (Work.NAKANE2.chiC c₀ D.χ) w)
        - (v * Work.MRMT.dz (Work.NAKANE2.chiC c₀ D.χ) w) = 1 := by ring
    have h2 : ‖(1 : ℂ)‖ - ‖v * Work.MRMT.dz (Work.NAKANE2.chiC c₀ D.χ) w‖
        ≤ ‖(1 : ℂ) + v * Work.MRMT.dz (Work.NAKANE2.chiC c₀ D.χ) w‖ := by
      have h := norm_sub_le ((1 : ℂ) + v * Work.MRMT.dz (Work.NAKANE2.chiC c₀ D.χ) w)
        (v * Work.MRMT.dz (Work.NAKANE2.chiC c₀ D.χ) w)
      rw [hsub] at h
      linarith [norm_nonneg (v * Work.MRMT.dz (Work.NAKANE2.chiC c₀ D.χ) w)]
    simp only [norm_one] at h2
    linarith
  -- the two norms, written as products of the two norms `‖v‖`, `‖∂̄χ‖` / `‖1 + v ∂χ‖` and `‖z‖`
  have hLnorm : ∀ z : ℂ,
      ‖(v * Work.MRMT.dzbar (Work.NAKANE2.chiC c₀ D.χ) (Tantibar c₀ z)) * (2 * z)‖
        = ‖v‖ * ‖Work.MRMT.dzbar (Work.NAKANE2.chiC c₀ D.χ) (Tantibar c₀ z)‖ * (2 * ‖z‖) := by
    intro z
    simp only [norm_mul]
    norm_num
  have hRnorm : ∀ z : ℂ,
      ‖(1 + v * Work.MRMT.dz (Work.NAKANE2.chiC c₀ D.χ) (Tantibar c₀ z)) * (2 * star z)‖
        = ‖1 + v * Work.MRMT.dz (Work.NAKANE2.chiC c₀ D.χ) (Tantibar c₀ z)‖ * (2 * ‖z‖) := by
    intro z
    simp only [norm_mul]
    norm_num
  constructor
  · intro z
    obtain ⟨hdz, hdzb⟩ := Work.NAKANE2.Surgery.gv_wirtinger D v z
    rw [hdz, hdzb, hLnorm z, hRnorm z]
    exact (gv_ratio_aux hvn (hdzbχ _) hΛnn (norm_nonneg z) (hlow _) hvΛ).1
  · intro z hz
    obtain ⟨hdz, hdzb⟩ := Work.NAKANE2.Surgery.gv_wirtinger D v z
    rw [hdz, hdzb, hLnorm z, hRnorm z]
    exact (gv_ratio_aux hvn (hdzbχ _) hΛnn (norm_nonneg z) (hlow _) hvΛ).2
      (norm_pos_iff.mpr hz)

end Work.NAKANE2.Surgery
