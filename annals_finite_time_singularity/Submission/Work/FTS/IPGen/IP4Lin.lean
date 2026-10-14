import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.NonlinRows.HkMem_mul_pth_flat
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.DelicateHon
import Submission.Work.FTS.StrongPersist.N6Trans.LeibMajor.EasyLeib_le_EasyMajor
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.Vocab
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
-- ===== merged: Submission.Work.FTS.CoercivityFix.Assembly.Main =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Assembly

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (RegQ CoerAdm UnifIP Xn)

set_option autoImplicit false




end Work.FTS.CoercivityFix.Assembly
end
end
-- ===== merged: Submission.Work.FTS.IPGen.IP4Lin =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.IPGen

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (Xn)

set_option autoImplicit false

/-! ## The leaf sum is bounded by the `ℋ⁴`-product -/

/-- **The leaf sum is dominated by `75 · |f|_{ℋ⁴} · |g|_{ℋ⁴}`.**  Each of the `75` leaves
(`15` slots `(a,b)` with `a + b ≤ 4`, times the three leaf weights — `leafGam α` only for
`a ≥ 1`) is at most `3 · |f|_{ℋ⁴}|g|_{ℋ⁴}` by the single-slot bound `slotPairing_abs_le`
(`IPGen/slotPairing_abs_le.lean`). -/
theorem leafSum_le {α : ℝ} (hα : 0 < α) {f g : Fn}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α 4 f) (hmg : Work.Spaces.HkMem α 4 g) :
    Work.FTS.TransportS.leafSum α f g ≤ 75 * (Xn α f * Xn α g) := by
  set R : ℝ := Xn α f * Xn α g with hR
  have hRnn : 0 ≤ R := by
    rw [hR]
    exact mul_nonneg (Work.Spaces.HkNorm_nonneg α 4 f) (Work.Spaces.HkNorm_nonneg α 4 g)
  have h₁ : Work.FTS.TransportS.leafSum α f g
      ≤ ∑ _a ∈ Finset.range 5, ∑ _b ∈ Finset.range 5, (3 : ℝ) * R := by
    unfold Work.FTS.TransportS.leafSum
    refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
    by_cases hab : a + b ≤ 4
    · rw [if_pos hab]
      have h1 := slotPairing_abs_le hα hab (Or.inl rfl) hf hg hmf hmg
      have h2 := slotPairing_abs_le hα hab (Or.inr (Or.inl rfl)) hf hg hmf hmg
      by_cases ha1 : 1 ≤ a
      · rw [if_pos ha1]
        have h3 := slotPairing_abs_le hα hab (Or.inr (Or.inr ⟨ha1, rfl⟩)) hf hg hmf hmg
        rw [← hR] at h1 h2 h3
        linarith
      · rw [if_neg ha1]; rw [← hR] at h1 h2; linarith
    · rw [if_neg hab]
      have : (0 : ℝ) ≤ 3 * R := mul_nonneg (by norm_num) hRnn
      linarith
  have h₂ : (∑ _a ∈ Finset.range 5, ∑ _b ∈ Finset.range 5, (3 : ℝ) * R) = 75 * R := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [h₂, hR] at h₁
  exact h₁

/-! ## Cauchy–Schwarz for `IP4` on the open class -/

/-- **Cauchy–Schwarz for the coercive `IP4` on `HQo α 4`**: from the slot domination
`ip4SlotDomGen` (`|IP4 …| ≤ K · leafSum`) and the leaf bound `leafSum_le`. -/
theorem ip4_cs_HQo {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂)
    (h₁' : 0 ≤ c₁') (h₂' : 0 ≤ c₂') (h₁'' : 0 ≤ c₁'') (h₂'' : 0 ≤ c₂'') :
    ∃ Ct α₂ : ℝ, 0 < Ct ∧ 0 < α₂ ∧ ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Fn,
      Work.FTS.VocabO.HQo α 4 f → Work.FTS.VocabO.HQo α 4 g →
      |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g|
        ≤ Ct * Xn α f * Xn α g := by
  obtain ⟨hKpos, hD⟩ := ip4SlotDomGen (c₁ := c₁) (c₂ := c₂) (c₁' := c₁') (c₂' := c₂')
    (c₁'' := c₁'') (c₂'' := c₂'') h₁ h₂ h₁' h₂' h₁'' h₂''
  refine ⟨(max 1 (max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂''))))) ^ 3 * 3 ^ 3 * 10 ^ 22) * 75,
    1, mul_pos hKpos (by norm_num), one_pos, ?_⟩
  intro α hα f g hf hg
  have hstep := hD α hα f g hf.1 hg.1
  have hleaf := leafSum_le hα.1 hf.1 hg.1 hf.2 hg.2
  calc |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α f g|
      ≤ (max 1 (max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂''))))) ^ 3 * 3 ^ 3 * 10 ^ 22)
          * Work.FTS.TransportS.leafSum α f g := hstep
    _ ≤ (max 1 (max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂''))))) ^ 3 * 3 ^ 3 * 10 ^ 22)
          * (75 * (Xn α f * Xn α g)) := mul_le_mul_of_nonneg_left hleaf hKpos.le
    _ = ((max 1 (max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂''))))) ^ 3 * 3 ^ 3 * 10 ^ 22) * 75)
          * Xn α f * Xn α g := by ring

/-! ## The `IPLinHQo` package -/


end Work.FTS.IPGen
end
end
