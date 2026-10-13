/-
Copyright: work module for the Elgindi finite-time singularity project.

# `IPGen/IP4Lin.lean` — the `IPLinHQo` package for the coercive `IP4`

This is the assembly of the four clauses of `IPGen.IPLinHQo` (design §4, "IP linearity on the
open class") for the concrete inner product `Assembly.IP4 c₁ … c₂''`:

* `add` — `IPGen.ip4_add_HQo` (the `Comm2o` induction of `IPGen/IP4Add.lean`);
* `smul` — `IPGen.ip4_smul` (unconditional homogeneity, `IPGen/IP4Smul.lean`);
* `congr` on `Qd` — `IPGen.ip4_congr_Qd` (the membership-free `Comm2` congruence of
  `Assembly.Comm2_levels`);
* Cauchy–Schwarz against `|·|_{ℋ⁴}` on the open class — `ip4_cs_HQo` below, from the slot
  domination `ip4SlotDomGen` and the leaf bound `leafSum_le` (which is the summation over the
  `75` leaves of `IPGen.slotPairing_abs_le`).

Everything here is `sorry`-free.
-/
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.IPGen.Defs
import Submission.Work.FTS.IPGen.IP4Add
import Submission.Work.FTS.IPGen.IP4Smul
import Submission.Work.FTS.IPGen.ip4SlotDomGen
import Submission.Work.FTS.IPGen.slotPairing_abs_le

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

/-- **The linearity/Cauchy–Schwarz/congruence package for the coercive `IP4` on the open
class `HQo α 4`** (design §4, consumed by `weakDetermines'_of`). -/
theorem ip4_IPLinHQo {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂)
    (h₁' : 0 ≤ c₁') (h₂' : 0 ≤ c₂') (h₁'' : 0 ≤ c₁'') (h₂'' : 0 ≤ c₂'') :
    ∃ α₂ Ct : ℝ, 0 < α₂ ∧ 0 < Ct ∧
      IPLinHQo (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') α₂ Ct := by
  obtain ⟨Ct, α₂cs, hCt, hα₂cs, hcs⟩ := ip4_cs_HQo h₁ h₂ h₁' h₂' h₁'' h₂''
  obtain ⟨α₂, hα₂, hadd⟩ := ip4_add_HQo (c₁ := c₁) (c₂ := c₂) (c₁' := c₁') (c₂' := c₂')
    (c₁'' := c₁'') (c₂'' := c₂'')
  refine ⟨min α₂cs α₂, Ct, lt_min hα₂cs hα₂, hCt, ?_⟩
  intro α hα f₁ f₂ g hf₁ hf₂ hg
  have hαcs : α ≤ α₂cs := le_trans hα.2 (min_le_left _ _)
  have hαα₂ : α ≤ α₂ := le_trans hα.2 (min_le_right _ _)
  exact ⟨hadd α ⟨hα.1, hαα₂⟩ f₁ f₂ g hf₁ hf₂ hg,
    fun c => ip4_smul c₁ c₂ c₁' c₂' c₁'' c₂'' c α f₁ g,
    hcs α ⟨hα.1, hαcs⟩ f₁ g hf₁ hg,
    fun f' h => ip4_congr_Qd (c₁ := c₁) (c₂ := c₂) (c₁' := c₁') (c₂' := c₂')
      (c₁'' := c₁'') (c₂'' := c₂'') hα.1 h⟩

end Work.FTS.IPGen
