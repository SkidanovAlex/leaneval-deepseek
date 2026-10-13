/-
# `Work.FTS.EllSol.PkgK5.ropTransferK5c` — the `ℛ`-slot at levels `2 ≤ k ≤ 5`

This is the **pinned, restricted-level** form of `Work.FTS.EllSol.PkgK5.ropTransferK5`: the level
`k` is confined to `2 ≤ k ≤ 5`, which is the range in which the three operator slots of the
elliptic package are honest (`ClassC` only supplies `HkMem α 7 g`, so the `sin 2θ`-mode of the
source is controlled up to level `7`; the sibling slot estimates fail for `k ≥ 8`, see
`PkgK5/NOTES_ropTransferK5.md`).

## The proof

Everything is the pointwise identity `ℛ(Ξ) = -2 sin²θ · (U(Ξ)/sin 2θ) + V(Ξ)` on the open
quadrant, with `Ξ := PhiTil α g Φg = Elliptic.EllResid α g Φg`.  Both factors on the right are
*bounded angular profiles* of the two sibling slots:

* the `U`-slot `Q := U(Ξ)/sin 2θ` is the deliverable of `PkgK5.uopTransferK5c`;
* the `V`-slot `Vf := V(Ξ)` is the deliverable of `PkgK5.vopTransferK5c`;

so the `ℛ`-slot is the bookkeeping `P := (-2)·(sin²θ · Q)`, `ℛ(Ξ) = P + Vf` a.e.:

* the *smoothness* half of `HQo` from `SmoothOpen.congr` applied to `SmoothOpen_add_local` of the
  two summands (`SmoothOpen_mul_sin_sq_local`, `const_mul'`);
* the *membership* half from `HkMem_add_open` and `HkMem_agreeOnQ` (the a.e. identity);
* the *norm bound* from the `sin²θ`-multiplier estimate `Work.Blocks.HkMul_ang_le`,
  `HkNorm_const_mul` and the triangle inequality `HkNorm_add_le`, with the constant
  `√2 · (2√Ca + 1) · (CU + CV)`.

(`rop_eq_uop_vop_point` is re-proved here — rather than imported from the module
`PkgK5.ropTransferK5`, whose target is the unrestricted-level statement — so that this file
depends only on the two `c`-siblings.)
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllSol.PkgK5.K5c.RopFinal
import Submission.Work.FTS.EllSol.PkgK5.vopTransferK5c
import Submission.Work.FTS.EllSol.ropBasic
import Submission.Work.Blocks.HkMul_ang_le
import Submission.Work.FTS.EllipticEst.HkNorm_add_le
import Submission.Work.FTS.EllipticEst.HkNorm_const_mul
import Submission.Work.FTS.EllipticEst.HkSq_congr_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.PkgK5

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The linking identity -/

/-- `ℛ(Ξ) = -2 sin²θ · (U(Ξ)/sin 2θ) + V(Ξ)` for `θ ∈ (0,π/2)`. -/
theorem rop_eq_uop_vop_point {α : ℝ} {Ξ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : 0 < θ) (hθ2 : θ < Real.pi / 2) :
    Work.Construction.Rop α Ξ z θ
      = -2 * Real.sin θ ^ 2
          * (Work.Construction.Uop α Ξ z θ / Work.Construction.s2 θ)
        + Work.Construction.Vop Ξ z θ := by
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ2⟩)
  have hsin : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith)
      (by linarith [hθ2, Real.pi_pos]))
  have hs2 : Work.Construction.s2 θ = 2 * Real.sin θ * Real.cos θ := by
    rw [Work.Construction.s2_eq, Real.sin_two_mul]
  rw [Work.Construction.Rop, Work.Construction.Uop, Work.Construction.Vop, Work.Spaces.pz,
    Work.Spaces.pth, Real.tan_eq_sin_div_cos, hs2]
  field_simp
  ring

/-! ## The target -/

theorem ropTransferK5c (k : ℕ) (hk : 2 ≤ k) (hk5 : k ≤ 5) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (g Φg : Work.FTS.Galerkin.Fn), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllSol.ClassC α g →
      Work.FTS.StrongGlobal.IsBslSolPos α g Φg →
      Work.FTS.EllipticEst.SmoothOpen Φg →
      Work.FTS.EllipticEst.TT.EllWeakPos α k (Work.Elliptic.orthSource g)
        (Work.FTS.EllSol.ellShift α g Φg) →
      Work.Spaces.HkMem α (k + 3) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2
        (Work.FTS.EllSol.ellShift α g Φg) z θ) →
      Work.Spaces.HkMem α (k + 2) (Work.Elliptic.orthSource g) →
      Work.FTS.VocabO.HQo α k (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg)) ∧
      Work.Spaces.HkNorm α k (Work.Construction.Rop α (Work.Construction.PhiTil α g Φg))
        ≤ C * (α ^ 2 * Work.Spaces.HkNorm α k
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Φg) z θ)
            + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
            + Work.Spaces.HkNorm α k g) := by
  obtain ⟨CU, hCUpos, hU⟩ := Work.FTS.EllSol.PkgK5.K5c.uopTransferK5c_c k hk hk5
  obtain ⟨CV, hCVpos, hV⟩ := vopTransferK5c k hk hk5
  obtain ⟨Ca, hCapos, ha⟩ := Work.Blocks.HkMul_ang_le k
  have hCU0 : (0 : ℝ) ≤ CU := le_of_lt hCUpos
  have hCV0 : (0 : ℝ) ≤ CV := le_of_lt hCVpos
  have hCa0 : (0 : ℝ) ≤ Ca := le_of_lt hCapos
  have hsCa0 : (0 : ℝ) ≤ Real.sqrt Ca := Real.sqrt_nonneg Ca
  refine ⟨Real.sqrt 2 * (2 * Real.sqrt Ca + 1) * (CU + CV), by positivity, ?_⟩
  intro α g Φg hα hα4 hC hsol hsmo hW hA hF
  have hα1 : α ≤ 1 := by linarith
  set Ξ : ℝ → ℝ → ℝ := Work.Construction.PhiTil α g Φg with hΞdef
  set X : ℝ := α ^ 2 * Work.Spaces.HkNorm α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Φg) z θ)
      + Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
      + Work.Spaces.HkNorm α k g with hXdef
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    have h1 : (0 : ℝ) ≤ α ^ 2 * Work.Spaces.HkNorm α k
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.EllSol.ellShift α g Φg) z θ) :=
      mul_nonneg (sq_nonneg α) (Work.Spaces.HkNorm_nonneg α k _)
    have h2 := Work.Spaces.HkNorm_nonneg α k
      (Work.Spaces.pthIter 2 (Work.FTS.EllSol.ellShift α g Φg))
    have h3 := Work.Spaces.HkNorm_nonneg α k g
    linarith
  -- the two sibling slots
  obtain ⟨hQHQo, hQb⟩ := hU α g Φg hα hα4 hC hsol hsmo hW hA hF
  obtain ⟨hVHQo, hVb⟩ := hV α g Φg hα hα4 hC hsol hsmo hW hA hF
  set Q : ℝ → ℝ → ℝ := fun z θ =>
    Work.Construction.Uop α Ξ z θ / Work.Construction.s2 θ with hQdef
  set Vf : ℝ → ℝ → ℝ := Work.Construction.Vop Ξ with hVdef
  set S : ℝ → ℝ → ℝ := fun z θ => Real.sin θ ^ 2 * Q z θ with hSdef
  set P : ℝ → ℝ → ℝ := fun z θ => (-2 : ℝ) * S z θ with hPdef
  have hQsmo : Work.FTS.EllipticEst.SmoothOpen Q := hQHQo.1
  have hQmem : Work.Spaces.HkMem α k Q := hQHQo.2
  have hVsmo : Work.FTS.EllipticEst.SmoothOpen Vf := hVHQo.1
  have hVmem : Work.Spaces.HkMem α k Vf := hVHQo.2
  -- the `sin²θ`-multiplier comparison and the two honesty transfers
  have hSsmem : Work.Spaces.HkMem α k S :=
    ((ha α Q hα hα1 hQsmo).2.2 hQmem).2.2.1
  have hSsq : Work.Spaces.HkSq α k S ≤ Ca * Work.Spaces.HkSq α k Q :=
    ((ha α Q hα hα1 hQsmo).2.2 hQmem).2.2.2
  have hSsmo : Work.FTS.EllipticEst.SmoothOpen S :=
    Work.FTS.EllSol.SmoothOpen_mul_sin_sq_local hQsmo
  have hPsmo : Work.FTS.EllipticEst.SmoothOpen P := hSsmo.const_mul' (-2)
  have hPmem : Work.Spaces.HkMem α k P := by
    rw [hPdef]
    exact Work.FTS.LocData.HkMem_const_mul α k (-2) hSsmem
  have hsum_smo : Work.FTS.EllipticEst.SmoothOpen (fun z θ => P z θ + Vf z θ) :=
    Work.FTS.EllSol.SmoothOpen_add_local hPsmo hVsmo
  have hsum_mem : Work.Spaces.HkMem α k (fun z θ => P z θ + Vf z θ) :=
    Work.FTS.EllipticEst.HkMem_add_open hPsmo hVsmo hPmem hVmem
  -- the a.e. identity
  have hAgree : Work.FTS.EllipticEst.AgreeOnQ (fun z θ => P z θ + Vf z θ)
      (Work.Construction.Rop α Ξ) := by
    intro z θ hz hθ0 hθ1
    rw [rop_eq_uop_vop_point hθ0 hθ1]
    simp only [hPdef, hSdef, hQdef, hVdef]
    ring
  have hRopsmo : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Rop α Ξ) :=
    Work.FTS.EllipticEst.SmoothOpen.congr hsum_smo hAgree
  have hRopmem : Work.Spaces.HkMem α k (Work.Construction.Rop α Ξ) :=
    Work.FTS.EllipticEst.HkMem_agreeOnQ hRopsmo hAgree hsum_mem
  -- the norm
  have hSnorm : Work.Spaces.HkNorm α k S ≤ Real.sqrt Ca * Work.Spaces.HkNorm α k Q := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, ← Real.sqrt_mul hCa0]
    exact Real.sqrt_le_sqrt hSsq
  have hPnorm : Work.Spaces.HkNorm α k P ≤ 2 * Work.Spaces.HkNorm α k S := by
    rw [hPdef, Work.FTS.EllipticEst.HkNorm_const_mul α k (-2) hSsmo.forall]
    norm_num
  have hQnorm : Work.Spaces.HkNorm α k Q ≤ CU * X := by
    rw [hXdef]
    exact hQb
  have hVnorm : Work.Spaces.HkNorm α k Vf ≤ CV * X := by
    rw [hXdef]
    exact hVb
  have htri : Work.Spaces.HkNorm α k (fun z θ => P z θ + Vf z θ)
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k P + Work.Spaces.HkNorm α k Vf) :=
    Work.FTS.EllipticEst.HkNorm_add_le α k hPsmo.forall hVsmo.forall hPmem hVmem
  have hsqeq : Work.Spaces.HkSq α k (Work.Construction.Rop α Ξ)
      = Work.Spaces.HkSq α k (fun z θ => P z θ + Vf z θ) :=
    (Work.FTS.EllipticEst.HkSq_congr_open α k hAgree).symm
  have hnormRop : Work.Spaces.HkNorm α k (Work.Construction.Rop α Ξ)
      = Work.Spaces.HkNorm α k (fun z θ => P z θ + Vf z θ) := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm, hsqeq]
  -- the final arithmetic
  have hfinal : Real.sqrt 2 * (2 * (Real.sqrt Ca * (CU * X)) + CV * X)
      ≤ Real.sqrt 2 * (2 * Real.sqrt Ca + 1) * (CU + CV) * X := by
    have hcoef : 2 * Real.sqrt Ca * CU + CV ≤ (2 * Real.sqrt Ca + 1) * (CU + CV) := by
      have h0 : (0 : ℝ) ≤ 2 * Real.sqrt Ca * CV + CU := by nlinarith [hsCa0, hCU0, hCV0]
      nlinarith
    calc Real.sqrt 2 * (2 * (Real.sqrt Ca * (CU * X)) + CV * X)
        = Real.sqrt 2 * ((2 * Real.sqrt Ca * CU + CV) * X) := by ring
      _ ≤ Real.sqrt 2 * (((2 * Real.sqrt Ca + 1) * (CU + CV)) * X) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoef hX0)
            (Real.sqrt_nonneg 2)
      _ = Real.sqrt 2 * (2 * Real.sqrt Ca + 1) * (CU + CV) * X := by ring
  refine ⟨⟨hRopsmo, hRopmem⟩, ?_⟩
  rw [hnormRop]
  calc Work.Spaces.HkNorm α k (fun z θ => P z θ + Vf z θ)
      ≤ Real.sqrt 2 * (Work.Spaces.HkNorm α k P + Work.Spaces.HkNorm α k Vf) := htri
    _ ≤ Real.sqrt 2 * (2 * (Real.sqrt Ca * (CU * X)) + CV * X) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 2)
        have h1 : Work.Spaces.HkNorm α k P ≤ 2 * (Real.sqrt Ca * (CU * X)) := by
          calc Work.Spaces.HkNorm α k P ≤ 2 * Work.Spaces.HkNorm α k S := hPnorm
            _ ≤ 2 * (Real.sqrt Ca * Work.Spaces.HkNorm α k Q) :=
                mul_le_mul_of_nonneg_left hSnorm (by norm_num)
            _ ≤ 2 * (Real.sqrt Ca * (CU * X)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left hQnorm hsCa0) (by norm_num)
        have h2 : Work.Spaces.HkNorm α k Vf ≤ CV * X := hVnorm
        linarith
    _ ≤ Real.sqrt 2 * (2 * Real.sqrt Ca + 1) * (CU + CV) * X := hfinal

end Work.FTS.EllSol.PkgK5
