import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.ClassCRHS.HkMemXnN0
import Submission.Work.FTS.GalFields.RHS.sharp_N0_diff
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongEps.EpsRLX.N0SubEqRsum
import Submission.Work.FTS.StrongEps.EpsRLX.RsumClassC

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The `ClassC`-level auxiliary facts underlying `N0DiffClassC`

The target `N0DiffClassC` is the `ClassC`-analogue of
`Work.FTS.GalFields.RHS.sharp_N0_diff`: for `W₁, W₂` of class `C` (`ClassC α`), the
`N₀`-difference `N₀ α (F_*+W₁) W₁ − N₀ α (F_*+W₂) W₂` is `ℋ⁴`-honest and `C^∞` on the open
quadrant, and its `ℋ⁴`-norm is bounded by
`K(α)·(1 + |W₁|_{ℋ⁵} + |W₂|_{ℋ⁵})·|W₁−W₂|_{ℋ⁵}` — a *linear-in-the-difference* bound.

The construction is in three layers:

1. **the telescoping identity** (`Work.FTS.StrongEps.EpsRLX.N0SubEqRsum`): on the open quadrant
   the difference equals the nine-piece sum `Rsum α W₁ W₂ (W₁−W₂)` of
   `GalFields/RHS/sharpN0_defs.lean`;
2. **the `ℋ⁴`-bound for the nine pieces** (`Work.FTS.StrongEps.EpsRLX.RsumClassC`), which is
   where the estimate lives (products, `c2m`, the fixed atoms `F_*`, `D_θF_*`, `D_zF_*`,
   `L₁₂F_*` and the linearity of `L₁₂`);
3. **the transfer of smoothness/honesty from `Rsum` to the difference** plus the `L₁₂`-zero-mode
   clause, which is what this file supplies below (`smoothOpen_of_eqOn_Q0`, `hkMem_sub_of`,
   `hkMem_N0_of_classC`, `smoothOpen_N0_of_classC`, `abs_L12_N0_sub_le`, `hkSq_N0_diff_eq`,
   `hkMem_N0_diff_of_Rsum`).  The two `Hᵏ`-transfers along the pointwise identity `D = Rsum` use
   `Work.FTS.EllipticEst.HkSq_congr_open` and `…Cert.GbarSin.HkMem_congr_Q0`.

The constants are allowed to depend on `α` (the pieces carry `α^{-1}`, `α^{-1/2}` and `α^{+1}`
factors), which is why `∃ K` sits *inside* the `∀ α ∈ Ioc 0 1` in the statement. -/

/-- **`SmoothOpen` only depends on the values on the open quadrant.** -/
theorem smoothOpen_of_eqOn_Q0 {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (h : ∀ z θ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    Work.FTS.EllipticEst.SmoothOpen g := by
  refine (Work.FTS.EllipticEst.smoothOpen_iff_forall g).mpr (fun n => ?_)
  refine ((Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hf n).congr (fun p hp => ?_)
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  exact (h p.1 p.2 hz hθ0 hθ1).symm

/-- **`HkMem α k` is closed under subtraction** (pointwise, in the open class). -/
theorem hkMem_sub_of {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (fun z θ => f z θ - g z θ) := by
  have hgsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => -g z θ) :=
    Work.FTS.GalFields.RHS.smoothOpen_neg' hg
  have hadd : Work.Spaces.HkMem α k (fun z θ => f z θ + -g z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open hf hgsm hmf
      (Work.FTS.StrongEps.ClassCRHS.mem_neg hmg)
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α k hadd (fun z hz θ hθ => ?_)
  ring

/-- **The `N₀`-block of a class-`C` datum is `ℋ⁴`-honest.**

`HkMemXnN0` is stated with the two *size* hypotheses `Xn α w ≤ C₀ α²` and `HkNorm α 6 w ≤ B`
(the constant `K` depends on them); here they are met by taking `C₀ := Xn α W / α²` and
`B := HkNorm α 6 W`, both of which are legitimate because the right-hand sides are exactly the
available norms. -/
theorem hkMem_N0_of_classC {α : ℝ} (hαIoc : α ∈ Set.Ioc 0 1)
    {W : Work.FTS.Galerkin.Fn} (hW : Work.FTS.ClassC.ClassC α W) :
    Work.Spaces.HkMem α 4 (Work.Construction.N0 α (Work.Construction.Ftot α W) W) := by
  obtain ⟨K, -, hN⟩ := Work.FTS.StrongEps.ClassCRHS.HkMemXnN0 (α := α) hαIoc
    (C₀ := Work.FTS.Nonlin.Xn α W / α ^ 2) (B := Work.Spaces.HkNorm α 6 W)
  refine (hN hW ?_ le_rfl).1
  exact le_of_eq (div_mul_cancel₀ _ (pow_ne_zero 2 hαIoc.1.ne')).symm

/-- **Open-quadrant smoothness of the `N₀`-block of a class-`C` datum** (from the smoothness of
`W` and of the radial function `z ↦ L₁₂(W)(z)`, which the class supplies). -/
theorem smoothOpen_N0_of_classC {α : ℝ} (hα : 0 < α)
    {W : Work.FTS.Galerkin.Fn} (hW : Work.FTS.ClassC.ClassC α W) :
    Work.FTS.EllipticEst.SmoothOpen
      (Work.Construction.N0 α (Work.Construction.Ftot α W) W) :=
  Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0 hα hW.reg
    (Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_aux hα hW)

/-- **The `L₁₂`-zero-mode of the `N₀`-difference is controlled by the `ℋ⁴`-norm of that
difference.**  This is the `L₁₂`-clause of `N0DiffClassC`, in the factored form which composes
with the `ℋ⁴`-bound for the difference.

Route: `L₁₂` is additive on pointwise differences of `C^∞`-on-the-open-quadrant, `ℋ⁴`-honest
profiles (`Work.FTS.GalFields.RHS.L12_sub_eq_of_smoothOpen`), and its zero mode at `z = 0` is
controlled by the `ℋ⁴`-norm (`Work.FTS.GalBasis.cc.abs_L12_le_HkNorm`). -/
theorem abs_L12_N0_sub_le {α : ℝ} (hαIoc : α ∈ Set.Ioc 0 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {W₁ W₂ : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
        - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0|
      ≤ C * Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
            - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ) := by
  obtain ⟨C, hC, hspec⟩ := Work.FTS.GalBasis.cc.abs_L12_le_HkNorm
  refine ⟨C, hC, ?_⟩
  intro W₁ W₂ hW₁ hW₂
  have hα : 0 < α := hαIoc.1
  have hsm₁ := smoothOpen_N0_of_classC hα hW₁
  have hsm₂ := smoothOpen_N0_of_classC hα hW₂
  have hm₁ := hkMem_N0_of_classC hαIoc hW₁
  have hm₂ := hkMem_N0_of_classC hαIoc hW₂
  have hmemD : Work.Spaces.HkMem α 4 (fun z θ =>
      Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
        - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ) :=
    hkMem_sub_of hsm₁ hsm₂ hm₁ hm₂
  have hlin := Work.FTS.GalFields.RHS.L12_sub_eq_of_smoothOpen hsm₁ hsm₂ hm₁ hm₂ 0 (le_refl 0)
  rw [hlin]
  exact hspec α _ hmemD

/-- **The `ℋ⁴`-energy of the `N₀`-difference is that of the nine-piece sum** (the a.e.-in-`z`
transfer of `Work.FTS.StrongEps.EpsRLX.N0SubEqRsum` across the null set `{z = 0}`). -/
theorem hkSq_N0_diff_eq {α : ℝ} (hα : 0 < α) {W₁ W₂ : Work.FTS.Galerkin.Fn}
    (hsm₁ : Work.FTS.EllipticEst.SmoothOpen W₁)
    (hsm₂ : Work.FTS.EllipticEst.SmoothOpen W₂)
    (hm₁ : Work.Spaces.HkMem α 4 W₁) (hm₂ : Work.Spaces.HkMem α 4 W₂) :
    Work.Spaces.HkSq α 4 (fun z θ =>
        Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
          - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ)
      = Work.Spaces.HkSq α 4 (Work.FTS.GalFields.RHS.Rsum α W₁ W₂
          (fun z θ => W₁ z θ - W₂ z θ)) := by
  refine Work.FTS.EllipticEst.HkSq_congr_open α 4 (fun z θ hz hθ0 hθ1 => ?_)
  exact Work.FTS.StrongEps.EpsRLX.N0SubEqRsum hα hsm₁ hsm₂ hm₁ hm₂ z θ ⟨hz, hθ0, hθ1⟩

/-- **The `ℋ⁴`-honesty of the `N₀`-difference**, transported from the nine-piece sum. -/
theorem hkMem_N0_diff_of_Rsum {α : ℝ} (hα : 0 < α) {W₁ W₂ : Work.FTS.Galerkin.Fn}
    (hsm₁ : Work.FTS.EllipticEst.SmoothOpen W₁)
    (hsm₂ : Work.FTS.EllipticEst.SmoothOpen W₂)
    (hm₁ : Work.Spaces.HkMem α 4 W₁) (hm₂ : Work.Spaces.HkMem α 4 W₂)
    (hRmem : Work.Spaces.HkMem α 4 (Work.FTS.GalFields.RHS.Rsum α W₁ W₂
      (fun z θ => W₁ z θ - W₂ z θ))) :
    Work.Spaces.HkMem α 4 (fun z θ =>
        Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
          - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ) := by
  refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 α 4 hRmem (fun z hz θ hθ => ?_)
  exact (Work.FTS.StrongEps.EpsRLX.N0SubEqRsum hα hsm₁ hsm₂ hm₁ hm₂ z θ
    ⟨hz, hθ.1, hθ.2⟩).symm

/-- **The `ℋ⁴`-norm of the `N₀`-difference is that of the nine-piece sum.** -/
theorem Xn_N0_diff_eq {α : ℝ} (hα : 0 < α) {W₁ W₂ : Work.FTS.Galerkin.Fn}
    (hsm₁ : Work.FTS.EllipticEst.SmoothOpen W₁)
    (hsm₂ : Work.FTS.EllipticEst.SmoothOpen W₂)
    (hm₁ : Work.Spaces.HkMem α 4 W₁) (hm₂ : Work.Spaces.HkMem α 4 W₂) :
    Work.FTS.Nonlin.Xn α (fun z θ =>
        Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
          - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ)
      = Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Rsum α W₁ W₂
          (fun z θ => W₁ z θ - W₂ z θ)) := by
  show Real.sqrt (Work.Spaces.HkSq α 4 (fun z θ =>
        Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
          - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ))
      = Real.sqrt (Work.Spaces.HkSq α 4 (Work.FTS.GalFields.RHS.Rsum α W₁ W₂
          (fun z θ => W₁ z θ - W₂ z θ)))
  rw [hkSq_N0_diff_eq hα hsm₁ hsm₂ hm₁ hm₂]

theorem N0DiffClassC :
    ∀ α ∈ Set.Ioc 0 1, ∃ K : ℝ, 0 < K ∧ ∀ {W₁ W₂ : Work.FTS.Galerkin.Fn},
      Work.FTS.ClassC.ClassC α W₁ → Work.FTS.ClassC.ClassC α W₂ →
      Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
          Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
            - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ) ∧
      Work.Spaces.HkMem α 4 (fun z θ =>
          Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
            - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ =>
          Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
            - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ)
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) ∧
      |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
          - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0|
        ≤ K * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
  intro α hαIoc
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  -- the two ingredients: the `ℋ⁴`-bound for the nine pieces, and the `L₁₂`-clause
  obtain ⟨K₁, hK₁, hRsum⟩ := Work.FTS.StrongEps.EpsRLX.RsumClassC (α := α) hα hα1
  obtain ⟨CL, hCL, hL12⟩ := abs_L12_N0_sub_le (α := α) hαIoc
  have hprod : 0 < CL * K₁ := mul_pos hCL hK₁
  refine ⟨K₁ + CL * K₁ + 1, by linarith, ?_⟩
  intro W₁ W₂ hW₁ hW₂
  have hsm₁ : Work.FTS.EllipticEst.SmoothOpen W₁ := hW₁.reg
  have hsm₂ : Work.FTS.EllipticEst.SmoothOpen W₂ := hW₂.reg
  have hm₁ : Work.Spaces.HkMem α 4 W₁ :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm₁ 4 (by norm_num) hW₁.mem
  have hm₂ : Work.Spaces.HkMem α 4 W₂ :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm₂ 4 (by norm_num) hW₂.mem
  obtain ⟨hRmem, hRxn⟩ := hRsum hW₁ hW₂
  -- the pairwise abbreviations
  have hTnn : 0 ≤ (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
      * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by
    refine mul_nonneg (by linarith [Work.Spaces.HkNorm_nonneg α 5 W₁,
      Work.Spaces.HkNorm_nonneg α 5 W₂]) ?_
    exact Work.Spaces.HkNorm_nonneg α 5 _
  have hleK : K₁ ≤ K₁ + CL * K₁ + 1 := by linarith
  have hleK' : CL * K₁ ≤ K₁ + CL * K₁ + 1 := by linarith
  have hxnD := Xn_N0_diff_eq (α := α) hα hsm₁ hsm₂ hm₁ hm₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `SmoothOpen` of the difference
    exact Work.FTS.EllipticEst.smoothOpen_sub (smoothOpen_N0_of_classC hα hW₁)
      (smoothOpen_N0_of_classC hα hW₂)
  · -- `ℋ⁴`-honesty of the difference
    exact hkMem_N0_diff_of_Rsum hα hsm₁ hsm₂ hm₁ hm₂ hRmem
  · -- the `ℋ⁴`-bound for the difference
    rw [hxnD]
    calc Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Rsum α W₁ W₂
            (fun z θ => W₁ z θ - W₂ z θ))
        ≤ K₁ * (1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := hRxn
      _ = K₁ * ((1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) := by ring
      _ ≤ (K₁ + CL * K₁ + 1) * ((1 + Work.FTS.GalFields.Xn5 α W₁
            + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) :=
          mul_le_mul_of_nonneg_right hleK hTnn
      _ = (K₁ + CL * K₁ + 1) * (1 + Work.FTS.GalFields.Xn5 α W₁
            + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by ring
  · -- the `L₁₂`-zero-mode clause
    calc |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁) 0
          - Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂) 0|
        ≤ CL * Work.FTS.Nonlin.Xn α (fun z θ =>
            Work.Construction.N0 α (Work.Construction.Ftot α W₁) W₁ z θ
              - Work.Construction.N0 α (Work.Construction.Ftot α W₂) W₂ z θ) :=
          hL12 hW₁ hW₂
      _ = CL * Work.FTS.Nonlin.Xn α (Work.FTS.GalFields.RHS.Rsum α W₁ W₂
            (fun z θ => W₁ z θ - W₂ z θ)) := by rw [hxnD]
      _ ≤ CL * (K₁ * ((1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ))) :=
          mul_le_mul_of_nonneg_left
            (le_trans hRxn (le_of_eq (by ring))) hCL.le
      _ = CL * K₁ * ((1 + Work.FTS.GalFields.Xn5 α W₁ + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) := by ring
      _ ≤ (K₁ + CL * K₁ + 1) * ((1 + Work.FTS.GalFields.Xn5 α W₁
            + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ)) :=
          mul_le_mul_of_nonneg_right hleK' hTnn
      _ = (K₁ + CL * K₁ + 1) * (1 + Work.FTS.GalFields.Xn5 α W₁
            + Work.FTS.GalFields.Xn5 α W₂)
            * Work.FTS.GalFields.Xn5 α (fun z θ => W₁ z θ - W₂ z θ) := by ring

end Work.FTS.StrongEps.EpsRLX
