/-
# `N0Aux.B4P1` — level-`4` bounds for the pieces `NP3` and `NP4b`

Both are of the form `(const/α) · (L₁₂w · (slot of w))`, so the level-`4` radial majorant
`radialMaj4` applies with `X = L₁₂w` and `f ∈ {w, D_θw}`; the `L₁₂`-jet bound is
`H6Pair6Aux.L12Sup4` (jets of order `≤ 4` bounded by `CL · Xn α w`), and the `α`-powers are
absorbed by `Xn α w ≤ C₀ α²`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.B4Aux
import Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.Maj4
import Submission.Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
import Submission.Work.FTS.StrongPersist.H6Aux.Facts
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.N0row_defs
import Submission.Work.FTS.IPGen.OpenBasic
import Submission.Work.FTS.StrongEps.HkSq_const_mul
import Submission.Work.FTS.ClassC.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux

open Work.FTS.StrongPersist.H6Pair6Aux (NA1 NA4 NA5 NA6 NP3 NP4a NP4b NP5a NP5b NP6)

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! ## Elementary nonnegativity helpers (the opaque constant `Maj4C` defeats `positivity`) -/

theorem sq_nn (x : ℝ) : (0 : ℝ) ≤ x ^ 2 := sq_nonneg x

theorem four_nn (x : ℝ) : (0 : ℝ) ≤ x ^ 4 := by
  rw [show x ^ 4 = (x ^ 2) ^ 2 by ring]
  exact sq_nonneg _

theorem maj4C1_pos : (0 : ℝ) < Maj4C + 1 := by
  have h := Maj4C_pos
  linarith

theorem maj4C1_nn : (0 : ℝ) ≤ Maj4C + 1 := maj4C1_pos.le

theorem NP3_HkSq4_le (C₀ : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 4 (NP3 α w) ≤ K * (1 + Work.Spaces.HkSq α 5 w) := by
  obtain ⟨CL, hCL, hL12sup⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
  have hK4nn : (0 : ℝ) ≤ (Maj4C + 1) * CL ^ 2 * C₀ ^ 4 :=
    mul_nonneg (mul_nonneg maj4C1_nn (sq_nn CL)) (four_nn C₀)
  refine ⟨(Maj4C + 1) * CL ^ 2 * C₀ ^ 4 + 1, by linarith, ?_⟩
  intro α hαIoc w hw hXw
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hw.reg
  have hm7 : Work.Spaces.HkMem α 7 w := hw.mem
  have hm6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 6 (by norm_num) hm7
  have hm4 : Work.Spaces.HkMem α 4 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 4 (by norm_num) hm7
  have hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hw
  have hLcd : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 w z) (Set.Ioi 0) := by
    have h1 : ContDiffOn ℝ 6
        (Function.uncurry (fun z (_ : ℝ) => Work.Construction.L12 w z))
        Work.FTS.EllipticEst.Q0 := hL.forall 6
    have h2 : ContDiffOn ℝ 6 (fun z : ℝ => (z, (1 : ℝ))) (Set.Ioi 0) :=
      ContDiffOn.prodMk contDiffOn_id contDiffOn_const
    have h3 := h1.comp h2 (fun z hz => ⟨hz, by norm_num, by linarith [Real.pi_gt_three]⟩)
    exact h3.congr (fun z _ => rfl)
  have hjet : ∀ j : ℕ, j ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 w z) z|
        ≤ CL * Work.FTS.Nonlin.Xn α w :=
    fun j hj z hz => hL12sup α w hα hα1 hsmw hm6 hw.l12 j hj z hz
  have hCB : (0 : ℝ) ≤ CL * Work.FTS.Nonlin.Xn α w :=
    mul_nonneg hCL.le (Work.Spaces.HkNorm_nonneg α 4 w)
  have hCsq : (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ C₀ ^ 2 * α ^ 4 := by
    calc (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ (C₀ * α ^ 2) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 w) hXw 2
      _ = C₀ ^ 2 * α ^ 4 := by ring
  have hw5 : Work.Spaces.HkSq α 4 w ≤ C₀ ^ 2 * α ^ 4 := by
    rw [sq_xn w]; exact hCsq
  have hsqCL : (CL * Work.FTS.Nonlin.Xn α w) ^ 2 ≤ CL ^ 2 * (C₀ ^ 2 * α ^ 4) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hCsq (sq_nonneg CL)
  have h5w : (0 : ℝ) ≤ Work.Spaces.HkSq α 5 w := Work.Spaces.HkSq_nonneg α 5 w
  have hone : (1 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by linarith
  have hMaj4 : (0 : ℝ) < Maj4C := Maj4C_pos
  have hRnn : (0 : ℝ) ≤ (Maj4C + 1) * (CL ^ 2 * (C₀ ^ 2 * α ^ 4)) :=
    mul_nonneg maj4C1_nn (mul_nonneg (sq_nn CL) (mul_nonneg (sq_nn C₀) (four_nn α)))
  have hM := radialMaj4 (α := α) (B := CL * Work.FTS.Nonlin.Xn α w)
    (X := fun z => Work.Construction.L12 w z) (f := w) hCB hLcd hsmw hm4 hjet
  have h1 : Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.L12 w z * w z θ)
      ≤ (Maj4C + 1) * CL ^ 2 * C₀ ^ 4 * α ^ 8 := by
    refine le_trans hM ?_
    calc (Maj4C + 1) * (CL * Work.FTS.Nonlin.Xn α w) ^ 2 * Work.Spaces.HkSq α 4 w
        ≤ (Maj4C + 1) * (CL ^ 2 * (C₀ ^ 2 * α ^ 4)) * (C₀ ^ 2 * α ^ 4) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hsqCL maj4C1_nn) hw5
            (Work.Spaces.HkSq_nonneg α 4 w) hRnn
      _ = (Maj4C + 1) * CL ^ 2 * C₀ ^ 4 * α ^ 8 := by ring
  have hs : Work.Spaces.HkSq α 4 (NP3 α w)
      = (1 / α) ^ 2 * Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.L12 w z * w z θ) :=
    Work.FTS.StrongEps.HkSq_const_mul α 4 (1 / α)
      (fun z θ => Work.Construction.L12 w z * w z θ)
  rw [hs]
  have h2 : (1 / α) ^ 2 * ((Maj4C + 1) * CL ^ 2 * C₀ ^ 4 * α ^ 8)
      = (Maj4C + 1) * CL ^ 2 * C₀ ^ 4 * α ^ 6 := by
    field_simp <;> ring
  have h3 : (0 : ℝ) ≤ (Maj4C + 1) * CL ^ 2 * C₀ ^ 4 := hK4nn
  calc (1 / α) ^ 2 * Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.L12 w z * w z θ)
      ≤ (1 / α) ^ 2 * ((Maj4C + 1) * CL ^ 2 * C₀ ^ 4 * α ^ 8) :=
        mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = (Maj4C + 1) * CL ^ 2 * C₀ ^ 4 * α ^ 6 := h2
    _ ≤ (Maj4C + 1) * CL ^ 2 * C₀ ^ 4 * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ hα.le hα1) h3
    _ ≤ (Maj4C + 1) * CL ^ 2 * C₀ ^ 4 * (1 + Work.Spaces.HkSq α 5 w) :=
        mul_le_mul_of_nonneg_left hone h3
    _ ≤ ((Maj4C + 1) * CL ^ 2 * C₀ ^ 4 + 1) * (1 + Work.Spaces.HkSq α 5 w) := by
        nlinarith [h3, hone, h5w]

theorem NP4b_HkSq4_le (C₀ : ℝ) : ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 4 (NP4b α w) ≤ K * (1 + Work.Spaces.HkSq α 5 w) := by
  obtain ⟨CL, hCL, hL12sup⟩ := Work.FTS.StrongPersist.H6Pair6Aux.L12Sup4
  have hK0nn : (0 : ℝ) ≤ 4 * (Maj4C + 1) * CL ^ 2 * C₀ ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) maj4C1_nn) (sq_nn CL)) (sq_nn C₀)
  refine ⟨4 * (Maj4C + 1) * CL ^ 2 * C₀ ^ 2 + 1, by linarith, ?_⟩
  intro α hαIoc w hw hXw
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  have hsmw : Work.FTS.EllipticEst.SmoothOpen w := hw.reg
  have hm7 : Work.Spaces.HkMem α 7 w := hw.mem
  have hm6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 6 (by norm_num) hm7
  have hm5 : Work.Spaces.HkMem α 5 w :=
    Work.FTS.OpenPkg.HkMem_mono_open hsmw 5 (by norm_num) hm7
  have hL : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.L12 w z) :=
    Work.FTS.StrongEps.ClassCRHS.smoothOpen_L12_radial_classC hα hw
  have hLcd : ContDiffOn ℝ 6 (fun z => Work.Construction.L12 w z) (Set.Ioi 0) := by
    have h1 : ContDiffOn ℝ 6
        (Function.uncurry (fun z (_ : ℝ) => Work.Construction.L12 w z))
        Work.FTS.EllipticEst.Q0 := hL.forall 6
    have h2 : ContDiffOn ℝ 6 (fun z : ℝ => (z, (1 : ℝ))) (Set.Ioi 0) :=
      ContDiffOn.prodMk contDiffOn_id contDiffOn_const
    have h3 := h1.comp h2 (fun z hz => ⟨hz, by norm_num, by linarith [Real.pi_gt_three]⟩)
    exact h3.congr (fun z _ => rfl)
  have hjet : ∀ j : ℕ, j ≤ 4 → ∀ z ∈ Set.Ioi (0 : ℝ),
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 w z) z|
        ≤ CL * Work.FTS.Nonlin.Xn α w :=
    fun j hj z hz => hL12sup α w hα hα1 hsmw hm6 hw.l12 j hj z hz
  have hCB : (0 : ℝ) ≤ CL * Work.FTS.Nonlin.Xn α w :=
    mul_nonneg hCL.le (Work.Spaces.HkNorm_nonneg α 4 w)
  have hCsq : (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ C₀ ^ 2 * α ^ 4 := by
    calc (Work.FTS.Nonlin.Xn α w) ^ 2 ≤ (C₀ * α ^ 2) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 4 w) hXw 2
      _ = C₀ ^ 2 * α ^ 4 := by ring
  have hsqCL : (CL * Work.FTS.Nonlin.Xn α w) ^ 2 ≤ CL ^ 2 * (C₀ ^ 2 * α ^ 4) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hCsq (sq_nonneg CL)
  have h5w : (0 : ℝ) ≤ Work.Spaces.HkSq α 5 w := Work.Spaces.HkSq_nonneg α 5 w
  have hα2 : α ^ 2 ≤ 1 := by nlinarith [hα, hα1]
  have hRnn : (0 : ℝ) ≤ (Maj4C + 1) * (CL ^ 2 * (C₀ ^ 2 * α ^ 4)) :=
    mul_nonneg maj4C1_nn (mul_nonneg (sq_nn CL) (mul_nonneg (sq_nn C₀) (four_nn α)))
  have hM := radialMaj4 (α := α) (B := CL * Work.FTS.Nonlin.Xn α w)
    (X := fun z => Work.Construction.L12 w z) (f := Work.Spaces.Dth w)
    hCB hLcd hsmw.Dth
    (Work.FTS.IPGen.HkMem_Dth_le (α := α) (k := 4) (by linarith [hα]) hsmw hm5) hjet
  have hDth : Work.Spaces.HkSq α 4 (Work.Spaces.Dth w) ≤ Work.Spaces.HkSq α 5 w :=
    Work.FTS.StrongPersist.H6Aux.HkSq_Dth_le_succ' α (by linarith [hα]) 4 hm5
  have h1 : Work.Spaces.HkSq α 4 (fun z θ => Work.Construction.L12 w z * Work.Spaces.Dth w z θ)
      ≤ (Maj4C + 1) * CL ^ 2 * C₀ ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 5 w) := by
    refine le_trans hM ?_
    calc (Maj4C + 1) * (CL * Work.FTS.Nonlin.Xn α w) ^ 2
          * Work.Spaces.HkSq α 4 (Work.Spaces.Dth w)
        ≤ (Maj4C + 1) * (CL ^ 2 * (C₀ ^ 2 * α ^ 4)) * Work.Spaces.HkSq α 5 w := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hsqCL maj4C1_nn) hDth
            (Work.Spaces.HkSq_nonneg α 4 (Work.Spaces.Dth w)) hRnn
      _ = (Maj4C + 1) * CL ^ 2 * C₀ ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 5 w) := by ring
  have hs : Work.Spaces.HkSq α 4 (NP4b α w)
      = (3 / (2 * α)) ^ 2 * Work.Spaces.HkSq α 4
          (fun z θ => Work.Construction.L12 w z * Work.Spaces.Dth w z θ) :=
    Work.FTS.StrongEps.HkSq_const_mul α 4 (3 / (2 * α))
      (fun z θ => Work.Construction.L12 w z * Work.Spaces.Dth w z θ)
  rw [hs]
  have h2 : (3 / (2 * α)) ^ 2
        * ((Maj4C + 1) * CL ^ 2 * C₀ ^ 2 * (α ^ 4 * Work.Spaces.HkSq α 5 w))
      = (9 / 4) * ((Maj4C + 1) * CL ^ 2 * C₀ ^ 2) * α ^ 2 * Work.Spaces.HkSq α 5 w := by
    field_simp <;> ring
  have h5 : (0 : ℝ) ≤ (Maj4C + 1) * CL ^ 2 * C₀ ^ 2 :=
    mul_nonneg (mul_nonneg maj4C1_nn (sq_nn CL)) (sq_nn C₀)
  have h6 : (9 / 4 : ℝ) * α ^ 2 * Work.Spaces.HkSq α 5 w
      ≤ 4 * (1 + Work.Spaces.HkSq α 5 w) := by
    have h7 : (9 / 4 : ℝ) * α ^ 2 ≤ 4 := by nlinarith [hα2]
    calc (9 / 4) * α ^ 2 * Work.Spaces.HkSq α 5 w ≤ 4 * Work.Spaces.HkSq α 5 w :=
          mul_le_mul_of_nonneg_right h7 h5w
      _ ≤ 4 * (1 + Work.Spaces.HkSq α 5 w) := by linarith [h5w]
  have hHnn : (0 : ℝ) ≤ 1 + Work.Spaces.HkSq α 5 w := by linarith
  calc (3 / (2 * α)) ^ 2 * Work.Spaces.HkSq α 4
        (fun z θ => Work.Construction.L12 w z * Work.Spaces.Dth w z θ)
      ≤ (3 / (2 * α)) ^ 2 * ((Maj4C + 1) * CL ^ 2 * C₀ ^ 2
          * (α ^ 4 * Work.Spaces.HkSq α 5 w)) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
    _ = (9 / 4) * ((Maj4C + 1) * CL ^ 2 * C₀ ^ 2) * α ^ 2 * Work.Spaces.HkSq α 5 w := h2
    _ = ((Maj4C + 1) * CL ^ 2 * C₀ ^ 2) * ((9 / 4) * α ^ 2 * Work.Spaces.HkSq α 5 w) := by ring
    _ ≤ ((Maj4C + 1) * CL ^ 2 * C₀ ^ 2) * (4 * (1 + Work.Spaces.HkSq α 5 w)) :=
        mul_le_mul_of_nonneg_left h6 h5
    _ = 4 * (Maj4C + 1) * CL ^ 2 * C₀ ^ 2 * (1 + Work.Spaces.HkSq α 5 w) := by ring
    _ ≤ (4 * (Maj4C + 1) * CL ^ 2 * C₀ ^ 2 + 1) * (1 + Work.Spaces.HkSq α 5 w) := by
        nlinarith [hHnn, hK0nn]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux
