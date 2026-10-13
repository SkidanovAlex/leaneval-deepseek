/-
# `L3RhsNggBlock` — the `ℋ³`-block estimate for `N₁^{gg} + N₂^{gg} + N₃^{gg}`

This module proves the block estimate for the pure-`gg` part

  `NGgSum α f Φg = N₁^{gg} + N₂^{gg} + N₃^{gg}`
    `= 2ℛ(Φ̃_g)·f - 2U(Φ̃_g)·∂_θf - 2α V(Φ̃_g)·D_zf`

of the level-three nonlinear right-hand side (the `rhs` field of `L3Data`).

**Route.**  All the input data lie at level six: `EllPkgK α 6 Ce f Φg` gives the *residual
coefficients* `ℛ(Φ̃_g)`, `U(Φ̃_g)/sin 2θ`, `V(Φ̃_g)` as `ℋ⁶`-functions bounded by `Ce·|f|_{ℋ⁶}`,
and `H6Adm α f` gives `f ∈ ℋ⁶`.  The estimate is assembled from

1. **the level-four product rule of the paper** (`Work.FTS.OpenPkg.prod_field`):
   `HQo α 4 u → HQo α 4 v → HkMem α 4 (u·v) ∧ |u·v|_{ℋ⁴} ≤ C α^{-1/2}|u|_{ℋ⁴}|v|_{ℋ⁴}`;
2. **the descent of `ℋ⁶` to `ℋ⁴`** (`Work.FTS.OpenPkg.HkMem_mono_open`,
   `Work.FTS.StrongLWP.HkNorm_mono_of_mem`);
3. **the one-level descent of the elliptic derivatives** `D_θ`, `D_z`
   (`Work.FTS.IPGen.HkMem_Dth_le`, `…HkMem_Dz_le`) together with their norm bounds
   (`Work.FTS.CoercivityFix.Assembly.HkSq_Dth_le_ge`,
   `Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm`), which show
   `|D_θf|_{ℋ⁴} ≤ |f|_{ℋ⁶}` and `|D_zf|_{ℋ⁴} ≤ |f|_{ℋ⁶}`;
4. **the descent `ℋ⁴ → ℋ³`** (`HkNorm_mono_of_mem`, `HkMem_mono_open`);
5. the additive triangle inequality of the weighted norm (`HkNorm_add_le`) and the congruences
   `HkSq_congr_open`/`HkMem_congr_Q0`, which identify `NGgSum` on the open quadrant with the
   product form `2(ℛ(Φ̃_g)·f) - 2((U(Φ̃_g)/sin2θ)·D_θf) - 2α(V(Φ̃_g)·D_zf)`.

The `α`-loss `α^{-1/2}` is the one of the product rule; the factor `(1+|Ce|)^4(1+M)^4(1+Xn6)^2`
is the loose but uniform bookkeeping of the three blocks.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.OpenPkg.prod_field
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.CoercivityFix.Assembly.HkSq_Dth_le_ge
import Submission.Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.LocData.HkSq_const_mul
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.EllHyp_certificates
import Submission.Work.FTS.StrongLWP.Basic
import Submission.Work.FTS.Nonlinear.Pieces.Basic

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
open Work.Spaces (HkMem HkSq HkNorm Dz Dth pth)
open Work.FTS.EllipticEst (SmoothOpen Q0)
open Work.FTS.VocabO (HQo)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Elementary closures -/

/-- `SmoothOpen` is closed under multiplication (the `SmoothOpen`-analogue of
`ContDiffOn.mul`, with the uncurrying made explicit). -/
theorem smoothOpen_mulNgg {F G : ℝ → ℝ → ℝ} (hF : SmoothOpen F) (hG : SmoothOpen G) :
    SmoothOpen (fun z θ => F z θ * G z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => F z θ * G z θ)) Work.FTS.EllipticEst.Q0
  have h1 : Function.uncurry (fun z θ => F z θ * G z θ)
      = Function.uncurry F * Function.uncurry G := rfl
  rw [h1]
  exact hF.mul hG

/-- The finite-order smoothness class of the open quadrant is implied by `SmoothOpen`
(the two sets `Work.FTS.EllipticEst.Q0` and `Work.Construction.Qd` are the same set). -/
theorem q0Sm_of_smoothOpenNgg {k : ℕ} {F : ℝ → ℝ → ℝ} (h : SmoothOpen F) :
    Work.FTS.CoercivityFix.Transfer.Q0Sm k F :=
  h.forall k

/-- Scalar homogeneity of the `ℋ^k`-norm (the `SmoothOpen`-form used below). -/
theorem hkNorm_const_mulNgg (α : ℝ) (k : ℕ) (c : ℝ) {F : ℝ → ℝ → ℝ} (hF : SmoothOpen F) :
    HkNorm α k (fun z θ => c * F z θ) = |c| * HkNorm α k F :=
  Work.FTS.EllipticEst.HkNorm_const_mul α k c hF.forall

/-- `HkNorm` only sees the open quadrant: the `HkNorm`-congruence form of
`Work.FTS.EllipticEst.HkSq_congr_open`. -/
theorem hkNorm_congr_openNgg (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 → f z θ = g z θ) :
    HkNorm α k f = HkNorm α k g := by
  simp only [HkNorm, Work.FTS.EllipticEst.HkSq_congr_open α k h]

/-! ## The one-level descents of `D_θ` and `D_z` -/

/-- **`D_θf` stays in `ℋ⁴` with `|D_θf|_{ℋ⁴} ≤ |f|_{ℋ⁶}`.**  The membership is
`IPGen.HkMem_Dth_le`, the norm bound is the chain
`HkSq α 4 (D_θf) ≤ HkSq α 5 f ≤ HkSq α 6 f` (`HkSq_Dth_le_ge`, `HkSq_mono_of_mem`). -/
theorem HkMem_HkNorm_Dth_le6 {α : ℝ} (hα : 0 < α) {f : Fn} (hsm : SmoothOpen f)
    (hmem : HkMem α 6 f) :
    HkMem α 4 (Dth f) ∧ HkNorm α 4 (Dth f) ≤ HkNorm α 6 f := by
  have h5 : HkMem α 5 f := Work.FTS.OpenPkg.HkMem_mono_open hsm 5 (by norm_num) hmem
  refine ⟨Work.FTS.IPGen.HkMem_Dth_le (by linarith : -(1 / 10 : ℝ) ≤ α) hsm h5, ?_⟩
  have h1 : HkSq α 4 (Dth f) ≤ HkSq α 5 f :=
    Work.FTS.CoercivityFix.Assembly.HkSq_Dth_le_ge α (by linarith : -(1 / 10 : ℝ) ≤ α) 4 h5
  have h2 : HkSq α 5 f ≤ HkSq α 6 f := Work.FTS.StrongLWP.HkSq_mono_of_mem (by norm_num) hmem
  simp only [HkNorm]
  exact le_trans (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2)

/-- **`D_zf` stays in `ℋ⁴` with `|D_zf|_{ℋ⁴} ≤ |f|_{ℋ⁶}`.**  The membership is
`IPGen.HkMem_Dz_le`, the norm bound is the chain
`HkSq α 4 (D_zf) ≤ HkSq α 5 f ≤ HkSq α 6 f` (`HkSq_Dz_le_Q0Sm`, `HkSq_mono_of_mem`). -/
theorem HkMem_HkNorm_Dz_le6 {α : ℝ} {f : Fn} (hsm : SmoothOpen f)
    (hmem : HkMem α 6 f) :
    HkMem α 4 (Dz f) ∧ HkNorm α 4 (Dz f) ≤ HkNorm α 6 f := by
  have h5 : HkMem α 5 f := Work.FTS.OpenPkg.HkMem_mono_open hsm 5 (by norm_num) hmem
  refine ⟨Work.FTS.IPGen.HkMem_Dz_le hsm h5, ?_⟩
  have h1 : HkSq α 4 (Dz f) ≤ HkSq α 5 f :=
    Work.FTS.CoercivityFix.Transfer.HkSq_Dz_le_Q0Sm α 4 (q0Sm_of_smoothOpenNgg hsm) h5
  have h2 : HkSq α 5 f ≤ HkSq α 6 f := Work.FTS.StrongLWP.HkSq_mono_of_mem (by norm_num) hmem
  simp only [HkNorm]
  exact le_trans (Real.sqrt_le_sqrt h1) (Real.sqrt_le_sqrt h2)

/-! ## The level-three product estimate -/

/-- **The `ℋ³` product estimate.**  From two `ℋ⁴`-data `u`, `v` (interior `C^∞` and honest
`ℋ⁴`-membership) the product lies in `ℋ³` with
`|u v|_{ℋ³} ≤ C α^{-1/2}|u|_{ℋ⁴}|v|_{ℋ⁴}`: the level-four product rule
(`Work.FTS.OpenPkg.prod_field`) gives `ℋ⁴`-membership and the `ℋ⁴`-bound, and the `ℋ³`-norm is
dominated by the `ℋ⁴`-one. -/
theorem lvl3_mul_bound {C4 : ℝ}
    (hprod : ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ f g : Fn, HQo α 4 f → HQo α 4 g →
      HkMem α 4 (fun z θ => f z θ * g z θ) ∧
      Work.FTS.Nonlin.Xn α (fun z θ => f z θ * g z θ)
        ≤ C4 * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f * Work.FTS.Nonlin.Xn α g)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {u v : Fn} (hu : HQo α 4 u) (hv : HQo α 4 v) :
    HkMem α 3 (fun z θ => u z θ * v z θ) ∧
    HkNorm α 3 (fun z θ => u z θ * v z θ)
      ≤ C4 * α ^ (-(1 / 2 : ℝ)) * HkNorm α 4 u * HkNorm α 4 v := by
  obtain ⟨hmem4, hbnd⟩ := hprod α hα hα1 u v hu hv
  have hso : SmoothOpen (fun z θ => u z θ * v z θ) := smoothOpen_mulNgg hu.1 hv.1
  refine ⟨Work.FTS.OpenPkg.HkMem_mono_open hso 3 (by norm_num) hmem4, ?_⟩
  exact le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 4) (k' := 3)
    (by norm_num) hmem4) hbnd

/-! ## The target -/

private theorem smoothOpen_const_mul_loc (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => c * f z θ) := by
  rw [Work.FTS.EllipticEst.SmoothOpen] at hf ⊢
  have h : (Function.uncurry fun z θ => c * f z θ)
      = fun p : ℝ × ℝ => c * Function.uncurry f p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [h]
  exact (contDiffOn_const (c := c) (s := Work.FTS.EllipticEst.Q0)).mul hf

theorem L3RhsNggBlock : ∃ C Cpow α₂ : ℝ, 0 < C ∧ 0 ≤ Cpow ∧ 0 < α₂ ∧
    ∀ α ∈ Set.Ioc 0 α₂, ∀ (Ce M : ℝ) (f Φg : Work.FTS.Galerkin.Fn),
      Work.FTS.StrongPersist.EllPkgK α 6 Ce f Φg → Work.FTS.StrongPersist.H6Adm α f →
      Work.FTS.Nonlin.Xn α f ≤ M →
      ContDiffOn ℝ 3 (Function.uncurry (Work.FTS.StrongPersist.L3Rhs.NGgSum α f Φg)) Work.FTS.EllipticEst.Q0 ∧
      Work.Spaces.HkMem α 3 (Work.FTS.StrongPersist.L3Rhs.NGgSum α f Φg) ∧
      Work.Spaces.HkNorm α 3 (Work.FTS.StrongPersist.L3Rhs.NGgSum α f Φg)
        ≤ C * (1 + |Ce|) ^ 4 * α ^ (-Cpow) * (1 + M) ^ 4 * (1 + Work.FTS.StrongPersist.Xn6 α f) ^ 2 := by
  obtain ⟨C4, hC4, hprod0⟩ := Work.FTS.OpenPkg.prod_field
  refine ⟨100 * (C4 + 1), 1 / 2, 1, by positivity, by norm_num, one_pos, ?_⟩
  intro α hαIoc Ce M f Φg hell hadm hM
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  -- the elliptic residual coefficients
  set R : Fn := Work.Construction.Rop α (Work.Construction.PhiTil α f Φg) with hR
  set U : Fn := fun z θ => Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ
    / Work.Construction.s2 θ with hU
  set V : Fn := Work.Construction.Vop (Work.Construction.PhiTil α f Φg) with hV
  have hR6 : HQo α 6 R := by rw [hR]; exact hell.R.1
  have hU6 : HQo α 6 U := by rw [hU]; exact hell.U.1
  have hV6 : HQo α 6 V := by rw [hV]; exact hell.V.1
  have hRb : HkNorm α 6 R ≤ Ce * HkNorm α 6 f := by rw [hR]; exact hell.R.2
  have hUb : HkNorm α 6 U ≤ Ce * HkNorm α 6 f := by rw [hU]; exact hell.U.2
  have hVb : HkNorm α 6 V ≤ Ce * HkNorm α 6 f := by rw [hV]; exact hell.V.2
  -- the datum `f`
  have hfso : SmoothOpen f := hadm.reg.1
  have hfmem6 : HkMem α 6 f := hadm.reg.2
  have hfmem4 : HkMem α 4 f := Work.FTS.OpenPkg.HkMem_mono_open hfso 4 (by norm_num) hfmem6
  have hXn4f : HkNorm α 4 f ≤ M := hM
  have hN6nn : (0 : ℝ) ≤ HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
  have hMnn : (0 : ℝ) ≤ M := le_trans (Work.Spaces.HkNorm_nonneg α 4 f) hXn4f
  -- descent to level four
  have hR4 : HQo α 4 R := ⟨hR6.1, Work.FTS.OpenPkg.HkMem_mono_open hR6.1 4 (by norm_num) hR6.2⟩
  have hU4 : HQo α 4 U := ⟨hU6.1, Work.FTS.OpenPkg.HkMem_mono_open hU6.1 4 (by norm_num) hU6.2⟩
  have hV4 : HQo α 4 V := ⟨hV6.1, Work.FTS.OpenPkg.HkMem_mono_open hV6.1 4 (by norm_num) hV6.2⟩
  have hf4 : HQo α 4 f := ⟨hfso, hfmem4⟩
  have hXn4R : HkNorm α 4 R ≤ Ce * HkNorm α 6 f :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 6) (k' := 4)
      (by norm_num) hR6.2) hRb
  have hXn4U : HkNorm α 4 U ≤ Ce * HkNorm α 6 f :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 6) (k' := 4)
      (by norm_num) hU6.2) hUb
  have hXn4V : HkNorm α 4 V ≤ Ce * HkNorm α 6 f :=
    le_trans (Work.FTS.StrongLWP.HkNorm_mono_of_mem (α := α) (k := 6) (k' := 4)
      (by norm_num) hV6.2) hVb
  -- the elliptic derivative slots of `f`
  obtain ⟨hDthmem, hDthb⟩ := HkMem_HkNorm_Dth_le6 hα hfso hfmem6
  obtain ⟨hDzmem, hDzb⟩ := HkMem_HkNorm_Dz_le6 hfso hfmem6
  have hDth4 : HQo α 4 (Dth f) := ⟨hfso.Dth, hDthmem⟩
  have hDz4 : HQo α 4 (Dz f) := ⟨hfso.Dz, hDzmem⟩
  -- `A`-bookkeeping
  set A : ℝ := 1 + |Ce| with hA
  have hAnn : 0 ≤ A := by rw [hA]; positivity
  have hA1 : 1 ≤ A := by rw [hA]; linarith [abs_nonneg Ce]
  have hCenn : Ce ≤ A := by rw [hA]; linarith [le_abs_self Ce]
  have hRA : HkNorm α 4 R ≤ A * HkNorm α 6 f :=
    le_trans hXn4R (mul_le_mul_of_nonneg_right hCenn hN6nn)
  have hUA : HkNorm α 4 U ≤ A * HkNorm α 6 f :=
    le_trans hXn4U (mul_le_mul_of_nonneg_right hCenn hN6nn)
  have hVA : HkNorm α 4 V ≤ A * HkNorm α 6 f :=
    le_trans hXn4V (mul_le_mul_of_nonneg_right hCenn hN6nn)
  -- the three products
  set P1 : Fn := fun z θ => R z θ * f z θ with hP1
  set P2 : Fn := fun z θ => U z θ * Dth f z θ with hP2
  set P3 : Fn := fun z θ => V z θ * Dz f z θ with hP3
  set G1 : Fn := fun z θ => 2 * P1 z θ with hG1
  set G2 : Fn := fun z θ => -2 * P2 z θ with hG2
  set G3 : Fn := fun z θ => (-2 * α) * P3 z θ with hG3
  set Gsum : Fn := fun z θ => G1 z θ + G2 z θ + G3 z θ with hGsum
  have hP1so : SmoothOpen P1 := by rw [hP1]; exact smoothOpen_mulNgg hR6.1 hfso
  have hP2so : SmoothOpen P2 := by rw [hP2]; exact smoothOpen_mulNgg hU6.1 hfso.Dth
  have hP3so : SmoothOpen P3 := by rw [hP3]; exact smoothOpen_mulNgg hV6.1 hfso.Dz
  have hG1so : SmoothOpen G1 := by rw [hG1]; exact smoothOpen_const_mul_loc 2 hP1so
  have hG2so : SmoothOpen G2 := by
    rw [hG2]; exact smoothOpen_const_mul_loc (-2) hP2so
  have hG3so : SmoothOpen G3 := by
    rw [hG3]; exact smoothOpen_const_mul_loc (-2 * α) hP3so
  have hp1 := lvl3_mul_bound hprod0 hα hα1 hR4 hf4
  have hp2 := lvl3_mul_bound hprod0 hα hα1 hU4 hDth4
  have hp3 := lvl3_mul_bound hprod0 hα hα1 hV4 hDz4
  have hP1mem : HkMem α 3 P1 := by rw [hP1]; exact hp1.1
  have hP2mem : HkMem α 3 P2 := by rw [hP2]; exact hp2.1
  have hP3mem : HkMem α 3 P3 := by rw [hP3]; exact hp3.1
  have hP1bnd : HkNorm α 3 P1
      ≤ C4 * α ^ (-(1 / 2 : ℝ)) * HkNorm α 4 R * HkNorm α 4 f := by rw [hP1]; exact hp1.2
  have hP2bnd : HkNorm α 3 P2
      ≤ C4 * α ^ (-(1 / 2 : ℝ)) * HkNorm α 4 U * HkNorm α 4 (Dth f) := by
    rw [hP2]; exact hp2.2
  have hP3bnd : HkNorm α 3 P3
      ≤ C4 * α ^ (-(1 / 2 : ℝ)) * HkNorm α 4 V * HkNorm α 4 (Dz f) := by
    rw [hP3]; exact hp3.2
  have hG1mem : HkMem α 3 G1 := by
    rw [hG1]; exact Work.FTS.LocData.HkMem_const_mul α 3 2 hP1mem
  have hG2mem : HkMem α 3 G2 := by
    rw [hG2]; exact Work.FTS.LocData.HkMem_const_mul α 3 (-2) hP2mem
  have hG3mem : HkMem α 3 G3 := by
    rw [hG3]; exact Work.FTS.LocData.HkMem_const_mul α 3 (-2 * α) hP3mem
  -- the three block bounds
  have hb1 : HkNorm α 3 G1 ≤ 2 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * M) := by
    rw [hG1, hkNorm_const_mulNgg α 3 2 hP1so, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
    refine le_trans hP1bnd ?_
    have hstep : HkNorm α 4 R * HkNorm α 4 f ≤ A * HkNorm α 6 f * M :=
      mul_le_mul hRA hXn4f (Work.Spaces.HkNorm_nonneg α 4 f)
        (mul_nonneg hAnn hN6nn)
    calc C4 * α ^ (-(1 / 2 : ℝ)) * HkNorm α 4 R * HkNorm α 4 f
        = C4 * α ^ (-(1 / 2 : ℝ)) * (HkNorm α 4 R * HkNorm α 4 f) := by ring
      _ ≤ C4 * α ^ (-(1 / 2 : ℝ)) * (A * HkNorm α 6 f * M) :=
          mul_le_mul_of_nonneg_left hstep (mul_nonneg hC4.le (Real.rpow_nonneg hα.le _))
      _ = C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * M := by ring
  have hb2 : HkNorm α 3 G2 ≤ 2 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f) := by
    rw [hG2, hkNorm_const_mulNgg α 3 (-2) hP2so, show |(-2 : ℝ)| = 2 by norm_num]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
    refine le_trans hP2bnd ?_
    have hstep : HkNorm α 4 U * HkNorm α 4 (Dth f) ≤ A * HkNorm α 6 f * HkNorm α 6 f :=
      mul_le_mul hUA hDthb (Work.Spaces.HkNorm_nonneg α 4 (Dth f)) (mul_nonneg hAnn hN6nn)
    calc C4 * α ^ (-(1 / 2 : ℝ)) * HkNorm α 4 U * HkNorm α 4 (Dth f)
        = C4 * α ^ (-(1 / 2 : ℝ)) * (HkNorm α 4 U * HkNorm α 4 (Dth f)) := by ring
      _ ≤ C4 * α ^ (-(1 / 2 : ℝ)) * (A * HkNorm α 6 f * HkNorm α 6 f) :=
          mul_le_mul_of_nonneg_left hstep (mul_nonneg hC4.le (Real.rpow_nonneg hα.le _))
      _ = C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f := by ring
  have hb3 : HkNorm α 3 G3 ≤ 2 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f) := by
    rw [hG3, hkNorm_const_mulNgg α 3 (-2 * α) hP3so,
      show |(-2 * α : ℝ)| = 2 * α by
        rw [abs_of_neg (by linarith : (-2 : ℝ) * α < 0)]; ring]
    have hP3bnd' : HkNorm α 3 P3
        ≤ C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f := by
      refine le_trans hP3bnd ?_
      have hstep : HkNorm α 4 V * HkNorm α 4 (Dz f) ≤ A * HkNorm α 6 f * HkNorm α 6 f :=
        mul_le_mul hVA hDzb (Work.Spaces.HkNorm_nonneg α 4 (Dz f)) (mul_nonneg hAnn hN6nn)
      calc C4 * α ^ (-(1 / 2 : ℝ)) * HkNorm α 4 V * HkNorm α 4 (Dz f)
          = C4 * α ^ (-(1 / 2 : ℝ)) * (HkNorm α 4 V * HkNorm α 4 (Dz f)) := by ring
        _ ≤ C4 * α ^ (-(1 / 2 : ℝ)) * (A * HkNorm α 6 f * HkNorm α 6 f) :=
            mul_le_mul_of_nonneg_left hstep (mul_nonneg hC4.le (Real.rpow_nonneg hα.le _))
        _ = C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f := by ring
    have hαr : α * α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(1 / 2 : ℝ)) := by
      have h1 : α * α ^ (-(1 / 2 : ℝ)) = α ^ (1 / 2 : ℝ) := by
        have h := Real.rpow_add hα 1 (-(1 / 2))
        rw [Real.rpow_one] at h
        rw [← h]
        congr 1
        norm_num
      rw [h1]
      exact Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)
    have h0 : (0 : ℝ) ≤ 2 * C4 * A * HkNorm α 6 f * HkNorm α 6 f := by positivity
    have hkey : 2 * α * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f)
        ≤ 2 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f) := by
      have h2 := mul_le_mul_of_nonneg_left hαr h0
      linarith [h2]
    calc 2 * α * HkNorm α 3 P3
        ≤ 2 * α * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f) :=
          mul_le_mul_of_nonneg_left hP3bnd' (by linarith)
      _ ≤ 2 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f) := hkey
  -- the sum of the three blocks
  have hG12so : SmoothOpen (fun z θ => G1 z θ + G2 z θ) :=
    Work.FTS.EllipticEst.smoothOpen_add hG1so hG2so
  have hG12mem : HkMem α 3 (fun z θ => G1 z θ + G2 z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open hG1so hG2so hG1mem hG2mem
  have hG12bnd : HkNorm α 3 (fun z θ => G1 z θ + G2 z θ)
      ≤ Real.sqrt 2 * (HkNorm α 3 G1 + HkNorm α 3 G2) :=
    Work.FTS.EllipticEst.HkNorm_add_le α 3 hG1so.forall hG2so.forall hG1mem hG2mem
  have hGsummem : HkMem α 3 Gsum := by
    rw [hGsum]; exact Work.FTS.EllipticEst.HkMem_add_open hG12so hG3so hG12mem hG3mem
  have hGsum_bnd : HkNorm α 3 Gsum
      ≤ Real.sqrt 2 * (HkNorm α 3 (fun z θ => G1 z θ + G2 z θ) + HkNorm α 3 G3) := by
    rw [hGsum]
    exact Work.FTS.EllipticEst.HkNorm_add_le α 3 hG12so.forall hG3so.forall hG12mem hG3mem
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    rw [← sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hsum : HkNorm α 3 Gsum
      ≤ 4 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * M)
        + 8 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f) := by
    nlinarith [hGsum_bnd, hG12bnd, hb1, hb2, hb3, hsqrt2, hsq2,
      Work.Spaces.HkNorm_nonneg α 3 G1, Work.Spaces.HkNorm_nonneg α 3 G2,
      Work.Spaces.HkNorm_nonneg α 3 G3, Real.sqrt_nonneg 2]
  -- the final arithmetic
  have hN4nn : (0 : ℝ) ≤ HkNorm α 6 f := hN6nn
  have hfinal : HkNorm α 3 Gsum
      ≤ 100 * (C4 + 1) * A ^ 4 * α ^ (-(1 / 2 : ℝ)) * (1 + M) ^ 4 * (1 + HkNorm α 6 f) ^ 2 := by
    have hA4 : A ≤ A ^ 4 := by
      have h3 : (1 : ℝ) ≤ A ^ 3 := one_le_pow₀ hA1 (n := 3)
      calc A = A * 1 := by ring
        _ ≤ A * A ^ 3 := mul_le_mul_of_nonneg_left h3 hAnn
        _ = A ^ 4 := by ring
    have hM4 : (1 + M) ≤ (1 + M) ^ 4 := by
      have h1 : (1 : ℝ) ≤ 1 + M := by linarith
      have h3 : (1 : ℝ) ≤ (1 + M) ^ 3 := one_le_pow₀ h1 (n := 3)
      calc (1 + M) = (1 + M) * 1 := by ring
        _ ≤ (1 + M) * (1 + M) ^ 3 := mul_le_mul_of_nonneg_left h3 (by linarith)
        _ = (1 + M) ^ 4 := by ring
    have hM2 : M + 2 * HkNorm α 6 f ≤ 3 * ((1 + M) * (1 + HkNorm α 6 f)) := by
      nlinarith [hMnn, hN6nn]
    have hNN : HkNorm α 6 f * (1 + HkNorm α 6 f) ≤ (1 + HkNorm α 6 f) ^ 2 := by
      nlinarith [hN6nn]
    have hKnn : (0 : ℝ) ≤ C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f := by positivity
    have hXnn : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
    have s1 : 4 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * M)
          + 8 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f)
        = 4 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f) * (M + 2 * HkNorm α 6 f) := by
      ring
    have s2 : 4 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f) * (M + 2 * HkNorm α 6 f)
        ≤ 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A) * ((1 + M) * (HkNorm α 6 f * (1 + HkNorm α 6 f))) := by
      calc 4 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f) * (M + 2 * HkNorm α 6 f)
          ≤ 4 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f)
              * (3 * ((1 + M) * (1 + HkNorm α 6 f))) :=
            mul_le_mul_of_nonneg_left hM2 (by positivity)
        _ = 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A)
              * ((1 + M) * (HkNorm α 6 f * (1 + HkNorm α 6 f))) := by ring
    have s3 : 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A) * ((1 + M) * (HkNorm α 6 f * (1 + HkNorm α 6 f)))
        ≤ 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A) * ((1 + M) * (1 + HkNorm α 6 f) ^ 2) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hNN (by linarith : (0 : ℝ) ≤ 1 + M))
        (by positivity)
    have s4 : 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A) * ((1 + M) * (1 + HkNorm α 6 f) ^ 2)
        ≤ 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A ^ 4)
            * ((1 + M) ^ 4 * (1 + HkNorm α 6 f) ^ 2) := by
      have h1 : A * (1 + M) ≤ A ^ 4 * (1 + M) ^ 4 :=
        mul_le_mul hA4 hM4 (by linarith) (by positivity)
      have h0 : (0 : ℝ) ≤ 12 * C4 * α ^ (-(1 / 2 : ℝ)) := by positivity
      calc 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A) * ((1 + M) * (1 + HkNorm α 6 f) ^ 2)
          = 12 * C4 * α ^ (-(1 / 2 : ℝ)) * (A * (1 + M)) * (1 + HkNorm α 6 f) ^ 2 := by ring
        _ ≤ 12 * C4 * α ^ (-(1 / 2 : ℝ)) * (A ^ 4 * (1 + M) ^ 4)
              * (1 + HkNorm α 6 f) ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 h0) (by positivity)
        _ = 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A ^ 4)
              * ((1 + M) ^ 4 * (1 + HkNorm α 6 f) ^ 2) := by ring
    have s5 : 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A ^ 4) * ((1 + M) ^ 4 * (1 + HkNorm α 6 f) ^ 2)
        ≤ 100 * (C4 + 1) * A ^ 4 * α ^ (-(1 / 2 : ℝ)) * (1 + M) ^ 4
            * (1 + HkNorm α 6 f) ^ 2 := by
      have hc : 12 * C4 ≤ 100 * (C4 + 1) := by linarith
      have h0 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) * A ^ 4 * (1 + M) ^ 4 * (1 + HkNorm α 6 f) ^ 2 := by
        positivity
      calc 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A ^ 4) * ((1 + M) ^ 4 * (1 + HkNorm α 6 f) ^ 2)
          = (12 * C4) * (α ^ (-(1 / 2 : ℝ)) * A ^ 4 * (1 + M) ^ 4 * (1 + HkNorm α 6 f) ^ 2) := by
            ring
        _ ≤ (100 * (C4 + 1))
              * (α ^ (-(1 / 2 : ℝ)) * A ^ 4 * (1 + M) ^ 4 * (1 + HkNorm α 6 f) ^ 2) :=
            mul_le_mul_of_nonneg_right hc h0
        _ = 100 * (C4 + 1) * A ^ 4 * α ^ (-(1 / 2 : ℝ)) * (1 + M) ^ 4
              * (1 + HkNorm α 6 f) ^ 2 := by ring
    calc HkNorm α 3 Gsum
        ≤ 4 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * M)
          + 8 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f * HkNorm α 6 f) := hsum
      _ = 4 * (C4 * α ^ (-(1 / 2 : ℝ)) * A * HkNorm α 6 f) * (M + 2 * HkNorm α 6 f) := s1
      _ ≤ 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A)
            * ((1 + M) * (HkNorm α 6 f * (1 + HkNorm α 6 f))) := s2
      _ ≤ 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A) * ((1 + M) * (1 + HkNorm α 6 f) ^ 2) := s3
      _ ≤ 12 * (C4 * α ^ (-(1 / 2 : ℝ)) * A ^ 4)
            * ((1 + M) ^ 4 * (1 + HkNorm α 6 f) ^ 2) := s4
      _ ≤ 100 * (C4 + 1) * A ^ 4 * α ^ (-(1 / 2 : ℝ)) * (1 + M) ^ 4
            * (1 + HkNorm α 6 f) ^ 2 := s5
  -- transfer from `Gsum` to `NGgSum`
  have hEqOn : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      NGgSum α f Φg z θ = Gsum z θ := by
    intro z θ hz hθ hθ2
    have hsin : Real.sin (2 * θ) ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
    have hkey : (Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ
          / (Real.sin (2 * θ)))
          * (Real.sin (2 * θ) * Work.Spaces.pth f z θ)
        = Work.Construction.Uop α (Work.Construction.PhiTil α f Φg) z θ
          * Work.Spaces.pth f z θ := by
      rw [← mul_assoc, div_mul_cancel₀ _ hsin]
    simp only [NGgSum, Work.FTS.Nonlin.N1gg, Work.FTS.Nonlin.N2gg, Work.FTS.Nonlin.N3gg,
      Work.FTS.Nonlin.PhiTg, hR, hU, hV, hP1, hP2, hP3, hG1, hG2, hG3, hGsum,
      Work.Spaces.Dth, Work.Construction.s2_eq]
    rw [hkey]
    ring
  have hmemN : HkMem α 3 (NGgSum α f Φg) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 (α := α) (k := 3)
      (u := Gsum) (v := NGgSum α f Φg) hGsummem
      (fun z hz θ hθ => (hEqOn z θ hz hθ.1 hθ.2).symm)
  have hnormN : HkNorm α 3 (NGgSum α f Φg) = HkNorm α 3 Gsum :=
    hkNorm_congr_openNgg α 3 (fun z θ hz hθ hθ2 => hEqOn z θ hz hθ hθ2)
  have hGsumso : SmoothOpen Gsum := by
    rw [hGsum]
    exact Work.FTS.EllipticEst.smoothOpen_add
      (Work.FTS.EllipticEst.smoothOpen_add hG1so hG2so) hG3so
  have hcont : ContDiffOn ℝ 3 (Function.uncurry (NGgSum α f Φg)) Work.FTS.EllipticEst.Q0 :=
    (hGsumso.forall 3).congr (fun p hp => by
      have hp' := hp
      rw [Work.FTS.EllipticEst.mem_Q0] at hp'
      exact hEqOn p.1 p.2 hp'.1 hp'.2.1 hp'.2.2)
  refine ⟨hcont, hmemN, ?_⟩
  rw [hnormN]
  have hfin := hfinal
  rw [hA] at hfin
  exact hfin

end Work.FTS.StrongPersist.L3Rhs
