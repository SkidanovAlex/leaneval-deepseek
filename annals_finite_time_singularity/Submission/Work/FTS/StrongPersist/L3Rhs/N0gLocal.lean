/-
# `Work.FTS.StrongPersist.L3Rhs.N0gLocal` — the *local* half of the `N₀`-block

This file proves the estimate for the row-7 term of the `g`-dependent block of `N₀`,

  `Wf α f = c₂(θ) · L₁₂(F_*(α))(z) · D_z f`     (`Work.FTS.StrongPersist.L3Rhs.Wf`, `c₂ = c2m`),

i.e. the half of `N0gSum = L₁₂(f)·Bf α f - Wf α f` in which the nonlocal operator `L₁₂` is
applied to the *profile* `F_*` (so that the factor in front of `D_z f` is a fixed coefficient,
not a functional of `f`).  By `Work.Construction.L12_Fstar_eq_of_gt_neg_one` this coefficient is
the elementary `c₂(θ)·2α/(1+z)`, so the whole estimate is a *multiplication* estimate:

  `HkMem α 3 (Wf α f)`  and  `HkNorm α 3 (Wf α f) ≤ C (1 + M)`   when  `Xn α f = HkNorm α 4 f ≤ M`.

## Route

Write `Wf α f = c₂ · (L₁₂(F_*) · D_z f)` (associativity, `Wf_factor`).  Three ingredients:

* **the `D_z`-shift** (`HkMem_HkSq_Dz_shift`): `D_z f ∈ ℋ³` and its square is dominated by the
  `ℋ⁴`-square of `f` — the existing `Work.FTS.IPGen.HkMem_Dz_le` (membership) and
  `Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm` (norm) — so `D_z f` costs exactly one order;
* **the radial multiplier** (delegated: `L12F_mul_HkSq_le`): multiplication by the fixed radial
  coefficient `L₁₂(F_*(α))`, which on `(-1,∞)` is `2α/(1+z)`, controlled by the general
  multiplier estimate `Work.FTS.StrongPersist.L3Aux.HkIntegrand_zmul_le` at order `3`;
* **the angular multiplier** (delegated: `c2m_mul_HkSq_le`): multiplication by the bounded
  angular profile `c₂(θ) = cos 2θ - sin²θ`, controlled by the angular multiplier machinery
  `Work.Blocks.HkMul_ang_le`.

All three are *lossless in the order*: multiplication by a bounded (angular/radial) coefficient
does not raise the `ℋ`-order, while `D_z` raises it by one, and the top order `4` is exactly the
one bounded by `M`.  The assembly is `N0gLocal_assembly` below; the constants `CA`, `CB` of the
two multipliers are existential and universal (independent of `α ∈ (0,1]`), and the final
constant is `√(CA·CB) + 1`, the radius of convergence `α₂ = 1`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gDecomp
import Submission.Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulCore
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.Nonlinear.FstarPkg.c2m_L12Fstar_W
import Submission.Work.FTS.StrongPersist.L3Rhs.L12F_mul_HkSq_le
import Submission.Work.FTS.StrongPersist.L3Rhs.c2m_mul_HkSq_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The factored form of `Wf` -/

/-- `Wf α f = c₂(θ) · (L₁₂(F_*(α))(z) · D_z f)` — the association of the product
`(c₂ · L₁₂(F_*)) · D_z f` in the form in which the two multipliers are applied successively. -/
private theorem Wf_factor (α : ℝ) (f : Fn) :
    Wf α f = fun z θ => Work.Construction.c2m θ
      * (Work.Construction.L12 (Work.Construction.Fstar α) z * Work.Spaces.Dz f z θ) := by
  funext z θ
  simp only [Wf]
  ring

/-! ## The `D_z`-shift -/

/-- **`D_z` costs exactly one `ℋ`-order**: for `SmoothOpen f ∈ ℋ⁴`, the radial derivative
`D_z f` is in `ℋ³` and its `ℋ³`-square is dominated by the `ℋ⁴`-square of `f`.  This is the
pair `Work.FTS.IPGen.HkMem_Dz_le` (membership) and
`Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm` (integrated pointwise domination of the
integrands). -/
private theorem HkMem_HkSq_Dz_shift {α : ℝ} {f : Fn}
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α 4 f) :
    Work.Spaces.HkMem α 3 (Work.Spaces.Dz f) ∧
      Work.Spaces.HkSq α 3 (Work.Spaces.Dz f) ≤ Work.Spaces.HkSq α 4 f := by
  have hq : Work.FTS.CoercivityFix.Transfer.Q0Sm 4 f := by
    rw [Work.FTS.CoercivityFix.Transfer.q0Sm_iff]
    exact (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsm 4
  exact ⟨Work.FTS.IPGen.HkMem_Dz_le hsm hm,
    Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α 3 hq hm⟩

/-! ## Smoothness of the radial coefficient -/

/-- `L₁₂(F_*(α))` is `C^∞` on `(-1,∞)`: there it is the explicit rational function
`z ↦ 2α/(1+z)` (`Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one`). -/
private theorem contDiffOn_smoothOrder_L12Fstar {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ContDiffOn ℝ Work.Stability.smoothOrder
      (fun z : ℝ => Work.Construction.L12 (Work.Construction.Fstar α) z)
      (Set.Ioi (-1)) := by
  have hbase : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => 2 * α / (1 + z))
      (Set.Ioi (-1)) := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (fun z : ℝ => (1 : ℝ) + z)
        (Set.Ioi (-1)) := contDiffOn_const.add contDiffOn_id
    have h2 := (contDiffOn_const (c := 2 * α) :
      ContDiffOn ℝ Work.Stability.smoothOrder (fun _ : ℝ => 2 * α) (Set.Ioi (-1))).div h1
      (fun z hz => by
        have hz' : (-1 : ℝ) < z := hz
        have : (0 : ℝ) < 1 + z := by linarith
        linarith)
    exact h2
  refine hbase.congr (fun z hz => ?_)
  exact Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one hα hα1 hz

/-! ## The assembly -/

/-- **The assembly of `N0gLocal`** from the two multiplier estimates.  `CA` bounds the radial
multiplier `L₁₂(F_*(α))` and `CB` the angular one `c₂`; both are universal (independent of
`α ∈ (0,1]`), and the final constant is `√(CA·CB) + 1`. -/
private theorem N0gLocal_assembly (CA CB : ℝ) (hCA : 0 < CA) (hCB : 0 < CB)
    (hA : ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ g : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 3 g →
      Work.Spaces.HkMem α 3
          (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z * g z θ) ∧
      Work.Spaces.HkSq α 3
          (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z * g z θ)
        ≤ CA * Work.Spaces.HkSq α 3 g)
    (hB : ∀ α ∈ Set.Ioc (0 : ℝ) 1, ∀ g : ℝ → ℝ → ℝ,
      Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 3 g →
      Work.Spaces.HkMem α 3 (fun z θ => Work.Construction.c2m θ * g z θ) ∧
      Work.Spaces.HkSq α 3 (fun z θ => Work.Construction.c2m θ * g z θ)
        ≤ CB * Work.Spaces.HkSq α 3 g) :
    ∃ C α₂ : ℝ, 0 < C ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Fn) (M : ℝ),
        H6Adm α f → Work.FTS.Nonlin.Xn α f ≤ M →
        Work.Spaces.HkMem α 3 (Wf α f) ∧
        Work.Spaces.HkNorm α 3 (Wf α f) ≤ C * (1 + M) := by
  refine ⟨Real.sqrt (CA * CB) + 1, 1, by positivity, one_pos, ?_⟩
  intro α hα f M hadm hM
  obtain ⟨hα0, hα1⟩ := hα
  have hαIoc : α ∈ Set.Ioc (0 : ℝ) 1 := ⟨hα0, hα1⟩
  -- the honest regularity of the datum
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hadm.reg.1
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 4 (by norm_num) hadm.reg.2
  -- the `D_z`-shift
  obtain ⟨hUmem, hUshift⟩ := HkMem_HkSq_Dz_shift hsm hmem4
  -- the radial multiplier
  have hV : Work.Spaces.HkMem α 3
        (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz f z θ) ∧
      Work.Spaces.HkSq α 3
        (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z
          * Work.Spaces.Dz f z θ)
        ≤ CA * Work.Spaces.HkSq α 3 (Work.Spaces.Dz f) :=
    hA α hαIoc (Work.Spaces.Dz f) hsm.Dz hUmem
  -- the angular multiplier
  have hVsm : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z * Work.Spaces.Dz f z θ) :=
    Work.FTS.StrongPersist.L3Aux.smoothOpen_zmul
      (contDiffOn_smoothOrder_L12Fstar hα0 hα1) hsm.Dz
  have hW : Work.Spaces.HkMem α 3 (fun z θ => Work.Construction.c2m θ
        * (Work.Construction.L12 (Work.Construction.Fstar α) z * Work.Spaces.Dz f z θ)) ∧
      Work.Spaces.HkSq α 3 (fun z θ => Work.Construction.c2m θ
        * (Work.Construction.L12 (Work.Construction.Fstar α) z * Work.Spaces.Dz f z θ))
        ≤ CB * Work.Spaces.HkSq α 3
          (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z
            * Work.Spaces.Dz f z θ) :=
    hB α hαIoc (fun z θ => Work.Construction.L12 (Work.Construction.Fstar α) z
      * Work.Spaces.Dz f z θ) hVsm hV.1
  refine ⟨?_, ?_⟩
  · rw [Wf_factor]
    exact hW.1
  · -- the squared estimate
    have hsq : Work.Spaces.HkSq α 3 (Wf α f) ≤ CA * CB * Work.Spaces.HkSq α 4 f := by
      rw [Wf_factor]
      calc Work.Spaces.HkSq α 3 (fun z θ => Work.Construction.c2m θ
              * (Work.Construction.L12 (Work.Construction.Fstar α) z * Work.Spaces.Dz f z θ))
          ≤ CB * Work.Spaces.HkSq α 3 (fun z θ => Work.Construction.L12
              (Work.Construction.Fstar α) z * Work.Spaces.Dz f z θ) := hW.2
        _ ≤ CB * (CA * Work.Spaces.HkSq α 3 (Work.Spaces.Dz f)) :=
              mul_le_mul_of_nonneg_left hV.2 hCB.le
        _ ≤ CB * (CA * Work.Spaces.HkSq α 4 f) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hUshift hCA.le) hCB.le
        _ = CA * CB * Work.Spaces.HkSq α 4 f := by ring
    have hM0 : 0 ≤ M := le_trans (Real.sqrt_nonneg _) hM
    have hroot : Work.Spaces.HkNorm α 3 (Wf α f) ≤ Real.sqrt (CA * CB) * M := by
      have hkey : Real.sqrt (Work.Spaces.HkSq α 3 (Wf α f)) ≤ Real.sqrt (CA * CB) * M := by
        calc Real.sqrt (Work.Spaces.HkSq α 3 (Wf α f))
            ≤ Real.sqrt (CA * CB * Work.Spaces.HkSq α 4 f) := Real.sqrt_le_sqrt hsq
          _ = Real.sqrt (CA * CB) * Real.sqrt (Work.Spaces.HkSq α 4 f) :=
                Real.sqrt_mul (mul_nonneg hCA.le hCB.le) _
          _ ≤ Real.sqrt (CA * CB) * M :=
                mul_le_mul_of_nonneg_left (by simpa only [Work.Spaces.HkNorm] using hM)
                  (Real.sqrt_nonneg _)
      simpa only [Work.Spaces.HkNorm] using hkey
    refine le_trans hroot ?_
    nlinarith [Real.sqrt_nonneg (CA * CB), hM0]

theorem N0gLocal : ∃ C α₂ : ℝ, 0 < C ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Adm α f → Work.FTS.Nonlin.Xn α f ≤ M →
      Work.Spaces.HkMem α 3 (Work.FTS.StrongPersist.L3Rhs.Wf α f) ∧
      Work.Spaces.HkNorm α 3 (Work.FTS.StrongPersist.L3Rhs.Wf α f) ≤ C * (1 + M) := by
  obtain ⟨CA, hCA, hA⟩ := L12F_mul_HkSq_le
  obtain ⟨CB, hCB, hB⟩ := c2m_mul_HkSq_le
  exact N0gLocal_assembly CA CB hCA hCB hA hB

end Work.FTS.StrongPersist.L3Rhs
