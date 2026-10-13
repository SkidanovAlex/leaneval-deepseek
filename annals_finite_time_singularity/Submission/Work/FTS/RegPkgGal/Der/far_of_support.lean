import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.Regularity.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.Der

theorem far_of_support {α S : ℝ} {g : Work.FTS.RegPkgGal.Fam} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hsupp : ∃ L : ℝ, 0 < L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, L ≤ z →
      Work.FTS.Regularity.profFull α (Work.FTS.RegPkgGal.extG g) z θ τ = 0) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Cf ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.FTS.RegPkgGal.extG g z θ τ| ≤ Cf * Work.FTS.Regularity.Gamma α θ := by
  -- Beyond the support radius `L` the extension `g̃` coincides with `g` (for `τ ≥ 0`, `z > 0`)
  -- and the full profile `F = F_* + g̃` vanishes, so `g = -F_*` there; and `F_*` obeys the
  -- angular bound `|F_*| ≤ 20·(3α)·Γ`.
  obtain ⟨L, hLpos, hL⟩ := hsupp
  refine ⟨max L 20, le_trans hLpos.le (le_max_left L 20), ?_⟩
  intro τ hτ z θ hz hθ
  have hzL : L ≤ z := le_trans (le_max_left L 20) hz
  have hzpos : 0 < z := lt_of_lt_of_le hLpos hzL
  have hτ0 : 0 ≤ τ := hτ.1
  have hext : Work.FTS.RegPkgGal.extG g z θ τ = g z θ τ :=
    Work.FTS.RegPkgGal.extG_of_pos hzpos hτ0
  have hzero : Work.FTS.Regularity.profFull α (Work.FTS.RegPkgGal.extG g) z θ τ = 0 :=
    hL τ hτ z θ hzL
  rw [Work.FTS.Regularity.profFull_apply, hext] at hzero
  have hg : g z θ τ = -Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ := by
    linarith
  rw [hext, hg, abs_neg]
  have hp0 : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hp1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hF := Work.ConstructionInstance.Fstar_abs_le (p := Work.FTS.Regularity.pExp α) hp0 hp1
    hzpos.le hθ
  have hp3 : Work.FTS.Regularity.pExp α / 3 = α := by rw [Work.FTS.Regularity.pExp]; ring
  rw [hp3] at hF
  have hGam0 : 0 ≤ Work.FTS.Regularity.Gamma α θ :=
    Work.ConstructionInstance.Gamma_nonneg hθ
  calc |Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ|
      ≤ 20 * Work.FTS.Regularity.pExp α * Work.FTS.Regularity.Gamma α θ := hF
    _ ≤ 20 * Work.FTS.Regularity.Gamma α θ := by
        have h := mul_le_mul_of_nonneg_right hp1 hGam0
        linarith
    _ ≤ max L 20 * Work.FTS.Regularity.Gamma α θ :=
        mul_le_mul_of_nonneg_right (le_max_right L 20) hGam0

end Work.FTS.RegPkgGal.Der
