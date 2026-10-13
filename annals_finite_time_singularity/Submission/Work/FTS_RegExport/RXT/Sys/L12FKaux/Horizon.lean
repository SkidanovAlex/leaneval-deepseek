import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.Standing
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKaux.FKDeriv
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS.StrongEps.classC_mixed_sup_le_four

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `L12FKaux.Horizon` — the standing estimates on a fake-time horizon `[0,T]`

The class-`C` data of `LimApprox` restricted to a horizon `[0,T]` give, uniformly in the
approximating index `n` and in `τ ∈ [0,T]`:

* `approx_slot_bound` — the weighted slot bound
  `|D_z^k (slice (gn n) τ)| ≤ Cw · z^{3/2}/(1+z)²` (`k ≤ 2`) — the restricted variant of
  `Standing.app_slot_le`;
* `ftau_slot_bound` — the order-`3` slot bound of the profiles `F(τ) = F_* + slice (gn n) τ`,
  uniform in `τ ∈ [0,T]` (the restricted variant of `FKDeriv.Ftau_slot_le3`);
* `app_diff_unif_Icc` — the uniform `L^∞`-modulus in `τ` (restricted `Standing.app_diff_unif`);
* `app_diff_le_Icc` — the weighted `τ`-modulus (restricted `Standing.app_diff_le`).

Everything is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_RegExport.RXT.Sys.L12FKaux

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- **Weighted slot bounds on a horizon**: `|D_z^k (slice (gn n) τ)| ≤ Cw · z^{3/2}/(1+z)²`. -/
theorem approx_slot_bound {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {T : ℝ} (hT : 0 < T)
    (hcl : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) (slice (gn n) τ))
    (hXn : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      Work.FTS.Nonlin.Xn (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
        ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T → ∀ (k : ℕ), k ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (slice (gn n) τ) z θ| ≤ Cw * SW z := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨Cd, hCd0, hCd⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hβ hβ1
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hX0 : 0 ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 :=
    le_trans (Work.Spaces.HkNorm_nonneg (Work.FTS.Regularity.pExp α) 4 (slice (gn 0) 0))
      (hXn 0 0 hmem0)
  refine ⟨Cd * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2), mul_nonneg hCd0 hX0, ?_⟩
  intro n τ hτ k hk z θ hz hθ0 hθ1
  have hcln := hcl n τ hτ
  have h4 : ContDiffOn ℝ 4 (Function.uncurry (slice (gn n) τ)) Work.FTS.EllipticEst.Q0 :=
    hcln.reg.forall 4
  have hmem : Work.Spaces.HkMem (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ) :=
    Work.FTS.ClassC.classC_hkMem_four hcln
  have htr : Work.FTS.Nonlin.BdryTraces (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ) :=
    Work.FTS.ClassC.bdryTraces_mono (by norm_num) hcln.tr
  have h1 := hCd _ h4 hmem htr k 0 (by omega) z θ hz hθ0 hθ1
  have h2 : Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ)
      ≤ C₀ * (Work.FTS.Regularity.pExp α) ^ 2 := hXn n τ hτ
  calc |Work.Spaces.DzIter k (slice (gn n) τ) z θ|
      = |Work.Spaces.mixed k 0 (slice (gn n) τ) z θ| := by rw [Work.Spaces.mixed_zero_right]
    _ ≤ Cd * SW z * Work.Spaces.HkNorm (Work.FTS.Regularity.pExp α) 4 (slice (gn n) τ) := h1
    _ ≤ Cd * SW z * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hCd0 (SW_nonneg hz.le))
    _ = (Cd * (C₀ * (Work.FTS.Regularity.pExp α) ^ 2)) * SW z := by ring

/-- **Order-`3` slot bounds of the profiles, uniform on the horizon.** -/
theorem ftau_slot_bound {α B : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {gn : ℕ → Fam} {T : ℝ}
    (hcl : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      Work.FTS.ClassC.ClassC (Work.FTS.Regularity.pExp α) (slice (gn n) τ))
    (hXn6 : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α) (slice (gn n) τ) ≤ B) :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      ∀ (n : ℕ) (k : ℕ), k ≤ 3 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ| ≤ CB := by
  have hβ : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hβ1 : Work.FTS.Regularity.pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  obtain ⟨C4, hC4pos, hC4⟩ := Work.FTS.StrongEps.classC_mixed_sup_le_four
  obtain ⟨M, hM0, hM⟩ := Work.FTS.StrongPersist.H6Pair6Aux.FstarJet7
  refine ⟨10 * M + C4 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
    * max B 0, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 10 * M := by linarith
    have h2 : (0 : ℝ) ≤ C4 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
        * max B 0 :=
      mul_nonneg (div_nonneg hC4pos.le (Real.sqrt_nonneg _)) (le_max_right B 0)
    linarith
  · intro τ hτ n k hk z θ hz h0 h1
    have hadd : Work.Spaces.DzIter k (Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        (gn n) τ) z θ
        = Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter k (slice (gn n) τ) z θ := by
      have h := Work.FTS.CoercivityFix.Transfer.E2pkg.DzIter_add_of_contDiffOn
        (n := 4) (f₁ := Work.Construction.Fstar (Work.FTS.Regularity.pExp α))
        (f₂ := fun z θ => gn n z θ τ) Work.FTS.EllipticEst.isOpen_Q0
        (Fstar_contDiffOn hβ hβ1 4) ((hcl n τ hτ).reg.forall 4) k (by omega)
        (z, θ) ⟨hz, h0, h1⟩
      rw [show Work.Construction.Ftau (Work.FTS.Regularity.pExp α) (gn n) τ
          = Work.Construction.Fstar (Work.FTS.Regularity.pExp α)
            + fun z θ => gn n z θ τ from rfl]
      rw [show slice (gn n) τ = fun z θ => gn n z θ τ from rfl]
      exact h
    rw [hadd]
    have hA' : |Work.Spaces.DzIter k (Work.Construction.Fstar
        (Work.FTS.Regularity.pExp α)) z θ| ≤ 10 * M :=
      Work.FTS_RegExport.RXT.ftau_DzIter_Fstar_le (α := α) hα hα13 hM k (by omega)
        z θ hz h0 h1
    have hB' : |Work.Spaces.DzIter k (slice (gn n) τ) z θ|
        ≤ C4 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1) * max B 0 := by
      have h := hC4 (Work.FTS.Regularity.pExp α) ⟨hβ, hβ1⟩ (hcl n τ hτ) k 0
        (by omega) ⟨hz, h0, h1⟩
      have hX : Work.FTS.StrongGlobal.Xn6 (Work.FTS.Regularity.pExp α) (slice (gn n) τ)
          ≤ max B 0 := le_trans (hXn6 n τ hτ) (le_max_left B 0)
      rw [Work.Spaces.mixed_zero_right] at h
      exact le_trans h (mul_le_mul_of_nonneg_left hX
        (div_nonneg hC4pos.le (Real.sqrt_nonneg _)))
    calc |Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ
          + Work.Spaces.DzIter k (slice (gn n) τ) z θ|
        ≤ |Work.Spaces.DzIter k (Work.Construction.Fstar (Work.FTS.Regularity.pExp α)) z θ|
          + |Work.Spaces.DzIter k (slice (gn n) τ) z θ| := abs_add_le _ _
      _ ≤ 10 * M + C4 / Real.sqrt (Work.Spaces.gam (Work.FTS.Regularity.pExp α) - 1)
            * max B 0 := add_le_add hA' hB'

/-- **Uniform `L^∞`-modulus in `τ`** on a horizon (the restricted `Standing.app_diff_unif`). -/
theorem app_diff_unif_Icc {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {gn : ℕ → Fam} {L : ℝ} {T : ℝ}
    (hcl : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      Work.FTS.ClassC.ClassC α (slice (gn n) τ))
    (hlip : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T → ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 4 (slice (gn n) τ - slice (gn n) τ') ≤ L * |τ - τ'|) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      ∀ τ' ∈ Set.Icc (0 : ℝ) T, ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      |slice (gn n) τ z θ - slice (gn n) τ' z θ| ≤ K * |τ - τ'| := by
  refine ⟨10 / Real.sqrt (Work.Spaces.gam α - 1) * max L 0,
    mul_nonneg (div_nonneg (by norm_num) (Real.sqrt_nonneg _)) (le_max_right L 0), ?_⟩
  intro n τ hτ τ' hτ' z θ hQd
  have hsub := Work.FTS.StrongEps.EComparison.classC_sub (hcl n τ hτ) (hcl n τ' hτ')
  have h1 := Work.FTS.StrongEps.SupPort.classC_mixed_sup_le hα hα1 hsub 0 0 (by norm_num) hQd
  have h2 : Work.FTS.Nonlin.Xn α (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ)
      ≤ max L 0 * |τ - τ'| :=
    le_trans (hlip n τ hτ τ' hτ') (mul_le_mul_of_nonneg_right (le_max_left L 0) (abs_nonneg _))
  have h3 : (0 : ℝ) ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  calc |slice (gn n) τ z θ - slice (gn n) τ' z θ|
      = |Work.Spaces.mixed 0 0 (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) z θ| := rfl
    _ ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1)
          * Work.FTS.Nonlin.Xn α
            (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) := h1
    _ ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * (max L 0 * |τ - τ'|) :=
        mul_le_mul_of_nonneg_left h2 h3
    _ = 10 / Real.sqrt (Work.Spaces.gam α - 1) * max L 0 * |τ - τ'| := by ring

/-- **Weighted `τ`-modulus** on a horizon (the restricted `Standing.app_diff_le`). -/
theorem app_diff_le_Icc {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {gn : ℕ → Fam} {L : ℝ} {T : ℝ}
    (hcl : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      Work.FTS.ClassC.ClassC α (slice (gn n) τ))
    (hlip : ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T → ∀ τ' ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkNorm α 4 (slice (gn n) τ - slice (gn n) τ') ≤ L * |τ - τ'|) :
    ∃ CwD : ℝ, 0 ≤ CwD ∧ ∀ (n : ℕ) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) T →
      ∀ τ' ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ, k ≤ 2 → ∀ z θ : ℝ,
      0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.DzIter k (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) z θ|
        ≤ (CwD * |τ - τ'|) * SW z := by
  obtain ⟨C, hC0, hC⟩ := Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hα hα1
  refine ⟨C * max L 0, mul_nonneg hC0 (le_max_right L 0), ?_⟩
  intro n τ hτ τ' hτ' k hk z θ hz hθ0 hθ1
  obtain ⟨hsm, hm, hb⟩ := Work.FTS_RegExport.RXR1.classC_sub_hyp (hcl n τ hτ) (hcl n τ' hτ')
  have h1 := hC _ (hsm.forall 4) hm hb k 0 (by omega) z θ hz hθ0 hθ1
  have hHk : Work.Spaces.HkNorm α 4 (slice (gn n) τ - slice (gn n) τ')
      ≤ max L 0 * |τ - τ'| :=
    le_trans (hlip n τ hτ τ' hτ') (mul_le_mul_of_nonneg_right (le_max_left L 0) (abs_nonneg _))
  show |Work.Spaces.mixed k 0 (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) z θ|
      ≤ (C * max L 0 * |τ - τ'|) * SW z
  calc |Work.Spaces.mixed k 0 (fun z θ => slice (gn n) τ z θ - slice (gn n) τ' z θ) z θ|
      ≤ C * SW z * Work.Spaces.HkNorm α 4 (slice (gn n) τ - slice (gn n) τ') := h1
    _ ≤ C * SW z * (max L 0 * |τ - τ'|) :=
        mul_le_mul_of_nonneg_left hHk (mul_nonneg hC0 (SW_nonneg hz.le))
    _ = (C * max L 0 * |τ - τ'|) * SW z := by ring

end Work.FTS_RegExport.RXT.Sys.L12FKaux
