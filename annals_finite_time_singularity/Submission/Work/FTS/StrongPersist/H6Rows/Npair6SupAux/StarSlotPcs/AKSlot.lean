/-
# The `F_*`-slot: `z/(1+z)·F_* = α·AK α`

`Work.Construction.AK α = (Γ(θ)/c α)·2z²/(1+z)³` is the separated form of the shifted star
slot, `z/(1+z)·F_* = α·AK α`.  The sharp pointwise bound of `Work.FTS.StrongPersist.AK6`
(`AK_integrand_le6`) together with `HkIntegrand_const_mul` gives the corresponding bound for
`α·AK α`, whence the honesty (`LocData.HkMem_const_mul`) and the norm bound
(`AK6.hkSq_le_of_integrand_le6`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.AK_Mem6
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.OpenPkg.Good
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.Congr

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology
open MeasureTheory Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Pointwise `ℋ⁶`-bound for `α·AK α`, obtained from the sharp bound for `AK α`
(`AK6.AK_integrand_le6`) by scaling (`HkIntegrand_const_mul`) and `α² ≤ 1`. -/
theorem alphaAK_integrand_le {R : ℝ} (hR : 0 ≤ R)
    (hrad : ∀ (j : ℕ), j ≤ 6 → ∀ (z : ℝ), z ∈ Work.Spaces.Iz → ∀ (θ : ℝ),
      (Work.Spaces.DzIter j (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z θ * Work.Spaces.w z) ^ 2
        ≤ R / (1 + z) ^ 2) :
    ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 6 (fun z θ => α * Work.Construction.AK α z θ) z θ
        ≤ (1 / (1 + z) ^ 2) *
          (700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
            + 49 * 10 ^ 12 * R * ((α + Real.sin (2 * θ)) ^ 2
                * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α))) := by
  intro α hα hα1 z hz θ hθ
  have hAK := Work.FTS.StrongPersist.AK6.AK_integrand_le6 hR hrad α hα hα1 z hz θ hθ
  rw [Work.FTS.Nonlinear.Pieces.RowsN0Aux.HkIntegrand_const_mul]
  have hs0 : 0 ≤ Real.sin (2 * θ) := Work.FTS.LocData.sin_two_nonneg hθ
  set X : ℝ := 700 * R * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      + 49 * 10 ^ 12 * R * ((α + Real.sin (2 * θ)) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * α / 5 - Work.Spaces.gam α)) with hX
  have hX0 : 0 ≤ X := by
    rw [hX]
    refine add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hR) (Real.rpow_nonneg hs0 _)) ?_
    exact mul_nonneg (mul_nonneg (by norm_num) hR)
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs0 _))
  have ha2 : α ^ 2 ≤ 1 := by nlinarith [hα, hα1]
  have hc0 : 0 ≤ 1 / (1 + z) ^ 2 := by positivity
  calc α ^ 2 * Work.Spaces.HkIntegrand α 6 (Work.Construction.AK α) z θ
      ≤ α ^ 2 * ((1 / (1 + z) ^ 2) * X) := mul_le_mul_of_nonneg_left hAK (sq_nonneg α)
    _ = (1 / (1 + z) ^ 2) * (α ^ 2 * X) := by ring
    _ ≤ (1 / (1 + z) ^ 2) * (1 * X) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ha2 hX0) hc0
    _ = (1 / (1 + z) ^ 2) * X := by ring

/-- `α·AK α` is `C^∞` on the open quadrant. -/
theorem smoothOpen_alphaAK (α : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => α * Work.Construction.AK α z θ) := by
  have hGam : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Work.Spaces.Gam α θ) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall
      (fun n => Work.FTS.OpenPkg.contDiffOn_Gam_Q0 α n)
  have hRho : Work.FTS.EllipticEst.SmoothOpen (fun z θ => 2 * z ^ 2 / (1 + z) ^ 3) := by
    refine Work.FTS.StrongPersist.H6Pair6Aux.so_radial (fun n => ?_)
    exact (contDiffOn_const.mul (contDiffOn_id.pow 2)).div
      ((contDiffOn_const.add contDiffOn_id).pow 3)
      (fun z hz => by
        have hz' : (0 : ℝ) < 1 + z := by
          have hz'' := hz; simp only [Set.mem_Ioi] at hz''; linarith
        exact pow_ne_zero 3 (ne_of_gt hz'))
  have hAK : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.AK α) := by
    refine (Work.FTS.StrongPersist.H6Pair6Aux.so_mul
      (Work.FTS.StrongPersist.H6Pair6Aux.so_mul hGam
        (Work.FTS.StrongPersist.H6Pair6Aux.so_const (Work.Spaces.c α)⁻¹)) hRho).congr ?_
    intro z θ hz hθ0 hθ1
    rw [Work.Construction.AK]
    ring
  exact Work.FTS.StrongPersist.H6Pair6Aux.so_const_mul α hAK

/-- `z/(1+z)·F_* = α·AK α` on `Iz`. -/
theorem zShift_Fstar_eq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      z / (1 + z) * Work.Construction.Fstar α z θ = α * Work.Construction.AK α z θ := by
  intro z hz θ _hθ
  have hz1 : (1 : ℝ) + z ≠ 0 := by
    have h := hz; simp only [Work.Spaces.Iz, Set.mem_Ici] at h; linarith
  have hc : Work.Spaces.c α ≠ 0 := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    intro h0; rw [h0] at h; norm_num at h
  rw [Work.Construction.Fstar, Work.FM.Fstar, Work.Construction.AK]
  field_simp <;> ring

/-- The `ℋ⁶`-membership and norm bound of the `F_*`-slot. -/
theorem starSlotA : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    Work.Spaces.HkMem α 6 (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ∧
    Work.Spaces.HkNorm α 6 (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) ≤ C := by
  obtain ⟨R, hR0, hrad⟩ := Work.FTS.StrongPersist.AK6.akRho_jet_bound6
  obtain ⟨_CAK, _hCAK, hAKb⟩ := Work.FTS.StrongPersist.AK_Mem6
  refine ⟨Real.sqrt (2 * (700 * R * 10 ^ 4 + 49 * 10 ^ 12 * R * 700)) + 1, by positivity, ?_⟩
  intro α hαIoc
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  obtain ⟨hAKmem, _hAKnorm⟩ := hAKb α hα hα1
  have hid := zShift_Fstar_eq hα hα1
  have hmem : Work.Spaces.HkMem α 6
      (fun z θ => z / (1 + z) * Work.Construction.Fstar α z θ) :=
    hkMem_congr_Izθ (fun z hz θ hθ => (hid z hz θ hθ).symm)
      (Work.FTS.LocData.HkMem_const_mul α 6 α hAKmem)
  refine ⟨hmem, ?_⟩
  have hpt := alphaAK_integrand_le hR0 hrad α hα hα1
  have hsq := Work.FTS.StrongPersist.AK6.hkSq_le_of_integrand_le6 hα hα1
    (by positivity) (by positivity) hpt
  rw [hkNorm_congr_Izθ hid]
  have h1 : Work.Spaces.HkNorm α 6 (fun z θ => α * Work.Construction.AK α z θ)
      ≤ Real.sqrt (2 * (700 * R * 10 ^ 4 + 49 * 10 ^ 12 * R * 700)) := by
    rw [Work.Spaces.HkNorm]
    exact Real.sqrt_le_sqrt hsq
  linarith [Real.sqrt_nonneg (2 * (700 * R * 10 ^ 4 + 49 * 10 ^ 12 * R * 700))]

end

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
