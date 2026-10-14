import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.LocData.bumpZ_eq_zero_of_notMem_Icc
import Submission.Work.FTS.NonlinRows.pure_slot_mul_pth_le
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.ip4SlotDomFixed
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.Pinning.integrableOn_sq_rpow_of_HkMem
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.H2.T1Q.SliceIntQ
import Submission.Work.H2.WPQ.m_term_le_smoothQuad
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.IPGen.ip4SlotDomGen =====
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
open Work.FTS.TransportS

set_option autoImplicit false

/-! ## One step of the recursion, with bounded coefficients -/

/-- **One step of the coercive recursion at a fixed level.**  If `IP` is dominated at level `n`
by `K · SlotSum α n` on the open-quadrant smooth class, and the two step coefficients are
dominated by a single constant `C ≥ 1`, then `HkIPStep c₁ c₂ IP` is dominated at level `n + 1`
by `3 C K · SlotSum α (n+1)`: the `D_θ`- and `D_z`-shifts are each dominated by the level
`n + 1` slot sum (`SlotSum_dth_le`, `SlotSum_dz_le`), and the unsplit term by the level-`n`
one (`SlotSum_mono`). -/
theorem HkIPStep_slot_bound {c₁ c₂ C K : ℝ} (hC : 1 ≤ C) (hc₁ : |c₁| ≤ C) (hc₂ : |c₂| ≤ C)
    (hK : 0 ≤ K) {α : ℝ} {n : ℕ} {IP : Fn → Fn → ℝ}
    (hIP : ∀ u v : Fn, Work.FTS.EllipticEst.SmoothOpen u →
      Work.FTS.EllipticEst.SmoothOpen v → |IP u v| ≤ K * SlotSum α n u v) :
    ∀ u v : Fn, Work.FTS.EllipticEst.SmoothOpen u → Work.FTS.EllipticEst.SmoothOpen v →
      |Work.Coercivity.HkIPStep c₁ c₂ IP u v|
        ≤ 3 * C * K * SlotSum α (n + 1) u v := by
  intro u v hu hv
  have hC0 : 0 ≤ C := le_trans zero_le_one hC
  have h0 := hIP u v hu hv
  have h1 := hIP (Work.Spaces.Dth u) (Work.Spaces.Dth v) hu.Dth hv.Dth
  have h2 := hIP (Work.Spaces.Dz u) (Work.Spaces.Dz v) hu.Dz hv.Dz
  have hT : 0 ≤ SlotSum α (n + 1) u v := SlotSum_nonneg α (n + 1) u v
  have hd := SlotSum_dth_le α n hu hv
  have hz := SlotSum_dz_le α n hu hv
  have hm := SlotSum_mono (α := α) (u := u) (v := v) (n := n) (m := n + 1) (by omega)
  -- the triangle inequality for the three terms of `HkIPStep`
  have htri : |IP u v + c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)
        + c₂ * IP (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
      ≤ |IP u v| + |c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
        + |c₂ * IP (Work.Spaces.Dz u) (Work.Spaces.Dz v)| := by
    have h := abs_add_le (IP u v + c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v))
      (c₂ * IP (Work.Spaces.Dz u) (Work.Spaces.Dz v))
    have h' := abs_add_le (IP u v) (c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v))
    linarith
  have hb1 : |c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)|
      ≤ C * (K * SlotSum α n (Work.Spaces.Dth u) (Work.Spaces.Dth v)) := by
    rw [abs_mul]
    exact mul_le_mul hc₁ h1 (abs_nonneg _) hC0
  have hb2 : |c₂ * IP (Work.Spaces.Dz u) (Work.Spaces.Dz v)|
      ≤ C * (K * SlotSum α n (Work.Spaces.Dz u) (Work.Spaces.Dz v)) := by
    rw [abs_mul]
    exact mul_le_mul hc₂ h2 (abs_nonneg _) hC0
  -- the three slot sums at level `n` are dominated by the ones at level `n + 1`
  have hS0 : K * SlotSum α n u v ≤ C * (K * SlotSum α (n + 1) u v) := by
    have ha : K * SlotSum α n u v ≤ K * SlotSum α (n + 1) u v :=
      mul_le_mul_of_nonneg_left hm hK
    have hb : K * SlotSum α (n + 1) u v ≤ C * (K * SlotSum α (n + 1) u v) :=
      le_mul_of_one_le_left (mul_nonneg hK hT) hC
    linarith
  have hS1 : C * (K * SlotSum α n (Work.Spaces.Dth u) (Work.Spaces.Dth v))
      ≤ C * (K * SlotSum α (n + 1) u v) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hd hK) hC0
  have hS2 : C * (K * SlotSum α n (Work.Spaces.Dz u) (Work.Spaces.Dz v))
      ≤ C * (K * SlotSum α (n + 1) u v) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz hK) hC0
  have hfin : 3 * C * K * SlotSum α (n + 1) u v
      = 3 * (C * (K * SlotSum α (n + 1) u v)) := by ring
  rw [hfin]
  have hexp : Work.Coercivity.HkIPStep c₁ c₂ IP u v
      = IP u v + c₁ * IP (Work.Spaces.Dth u) (Work.Spaces.Dth v)
        + c₂ * IP (Work.Spaces.Dz u) (Work.Spaces.Dz v) := rfl
  rw [hexp]
  linarith [htri, h0, hb1, hb2, hS0, hS1, hS2]

/-! ## The slot domination of `IP4` with arbitrary nonnegative step coefficients -/

/-- **The slot domination of the concrete `IP4` with *general* step coefficients.**  For
nonnegative coefficients the constant `CoefMax c₁ … c₂'' = max 1 (max c₁ (… (max c₁'' c₂'')))`
dominates all six of them, so three applications of `HkIPStep_slot_bound` starting from
`H1IP α` produce the bound `CoefMax³ · 3³ · 10^22 · leafSum α u v`.

This is the coefficient-free form of `ip4SlotDomFixed` (which covers only the unit coefficients
of `CoercivityStep.IP4`). -/
theorem ip4SlotDomGen {c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ} (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂)
    (h₁' : 0 ≤ c₁') (h₂' : 0 ≤ c₂') (h₁'' : 0 ≤ c₁'') (h₂'' : 0 ≤ c₂'') :
    Work.FTS.TransportS.SlotDomIP 1
      (max 1 (max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂''))))) ^ 3 * 3 ^ 3 * 10 ^ 22)
      (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'') := by
  change Work.FTS.TransportS.SlotDomIP 1
    (CoefMax c₁ c₂ c₁' c₂' c₁'' c₂'' ^ 3 * 3 ^ 3 * 10 ^ 22)
    (Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'')
  set C := CoefMax c₁ c₂ c₁' c₂' c₁'' c₂'' with hCdef
  have hC1 : (1 : ℝ) ≤ C := by rw [hCdef]; exact one_le_coefMax c₁ c₂ c₁' c₂' c₁'' c₂''
  have hc₁ : |c₁| ≤ C := by rw [abs_of_nonneg h₁, hCdef]; exact le_coefMax₁
  have hc₂ : |c₂| ≤ C := by rw [abs_of_nonneg h₂, hCdef]; exact le_coefMax₂
  have hc₁' : |c₁'| ≤ C := by rw [abs_of_nonneg h₁', hCdef]; exact le_coefMax₁'
  have hc₂' : |c₂'| ≤ C := by rw [abs_of_nonneg h₂', hCdef]; exact le_coefMax₂'
  have hc₁'' : |c₁''| ≤ C := by rw [abs_of_nonneg h₁'', hCdef]; exact le_coefMax₁''
  have hc₂'' : |c₂''| ≤ C := by rw [abs_of_nonneg h₂'', hCdef]; exact le_coefMax₂''
  refine ⟨?_, ?_⟩
  · have hCpos : 0 < C := lt_of_lt_of_le one_pos hC1
    positivity
  · intro α hα u v hu hv
    -- the level-`1` base: `H1IP α` is dominated by `10^22 · SlotSum α 1`
    have hIP0 : ∀ u v : Fn, Work.FTS.EllipticEst.SmoothOpen u →
        Work.FTS.EllipticEst.SmoothOpen v →
        |Work.Coercivity.H1IP α u v| ≤ (10 : ℝ) ^ 22 * SlotSum α 1 u v :=
      fun u v _ _ => H1IP_le_SlotSum_one α u v
    -- step 1: level `2`, constant `3 C 10^22`
    have hIP1 : ∀ u v : Fn, Work.FTS.EllipticEst.SmoothOpen u →
        Work.FTS.EllipticEst.SmoothOpen v →
        |IPnG c₁ c₂ α 1 u v| ≤ (3 * C * (10 : ℝ) ^ 22) * SlotSum α 2 u v :=
      fun u v hu hv =>
        HkIPStep_slot_bound (c₁ := c₁) (c₂ := c₂) (C := C) (K := (10 : ℝ) ^ 22)
          hC1 hc₁ hc₂ (by norm_num) (α := α) (n := 1) (IP := Work.Coercivity.H1IP α)
          hIP0 u v hu hv
    -- step 2: level `3`, constant `3 C (3 C 10^22)`
    have hIP2 : ∀ u v : Fn, Work.FTS.EllipticEst.SmoothOpen u →
        Work.FTS.EllipticEst.SmoothOpen v →
        |Work.Coercivity.HkIPStep c₁' c₂' (IPnG c₁ c₂ α 1) u v|
          ≤ (3 * C * (3 * C * (10 : ℝ) ^ 22)) * SlotSum α 3 u v :=
      fun u v hu hv =>
        HkIPStep_slot_bound (c₁ := c₁') (c₂ := c₂') (C := C)
          (K := 3 * C * (10 : ℝ) ^ 22) hC1 hc₁' hc₂'
          (mul_nonneg (mul_nonneg (by norm_num) (le_trans zero_le_one hC1)) (by norm_num))
          (α := α) (n := 2) (IP := IPnG c₁ c₂ α 1) hIP1 u v hu hv
    -- step 3: level `4`, constant `3 C (3 C (3 C 10^22))`
    have hIP3 : ∀ u v : Fn, Work.FTS.EllipticEst.SmoothOpen u →
        Work.FTS.EllipticEst.SmoothOpen v →
        |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α u v|
          ≤ (3 * C * (3 * C * (3 * C * (10 : ℝ) ^ 22))) * SlotSum α 4 u v :=
      fun u v hu hv =>
        HkIPStep_slot_bound (c₁ := c₁'') (c₂ := c₂'') (C := C)
          (K := 3 * C * (3 * C * (10 : ℝ) ^ 22)) hC1 hc₁'' hc₂''
          (mul_nonneg (mul_nonneg (by norm_num) (le_trans zero_le_one hC1))
            (mul_nonneg (mul_nonneg (by norm_num) (le_trans zero_le_one hC1)) (by norm_num)))
          (α := α) (n := 3)
          (IP := Work.Coercivity.HkIPStep c₁' c₂' (IPnG c₁ c₂ α 1)) hIP2 u v hu hv
    have h3 := hIP3 u v hu hv
    calc |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α u v|
        ≤ (3 * C * (3 * C * (3 * C * (10 : ℝ) ^ 22))) * SlotSum α 4 u v := h3
      _ = C ^ 3 * 3 ^ 3 * 10 ^ 22 * Work.FTS.TransportS.leafSum α u v := by
          rw [leafSum_eq_SlotSum_four]; ring

end Work.FTS.IPGen
end
end
-- ===== merged: Submission.Work.FTS.NonlinRows.HkMem_mul_pth_flat =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Auxiliary facts -/



/-! ## The target -/


end Work.FTS.NonlinRows
end
end
