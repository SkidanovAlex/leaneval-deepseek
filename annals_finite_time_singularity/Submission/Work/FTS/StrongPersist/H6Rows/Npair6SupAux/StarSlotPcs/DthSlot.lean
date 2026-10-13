/-
# The `D_θF_*`-slot: `z/(1+z)·D_θF_* = (α qfun θ)·(α·AK α)`

`D_θF_* = α qfun θ·F_*` (`Dth_Fstar_eq`) and `z/(1+z)·F_* = α·AK α` (`zShift_Fstar_eq`), so the
slot is the product of `α·AK α` with the *angular* multiplier `a θ = α qfun θ`.

The multiplier satisfies `|a θ| ≤ α Bq` and `|D_θ^i a| ≤ (α Bq)·sin 2θ` for `1 ≤ i ≤ 6`
(because `D_θ` carries a factor `sin 2θ` and the derivatives of `qfun` are bounded), so
`L3Rhs.ang_mul_HkSq_le` gives the honesty and `HkSq (a·f) ≤ C·(α Bq)²·HkSq f`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.AK_Mem6
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.L3Rhs.c2m_mul_HkSq_le
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.N0SlotSplitAux
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.Congr
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.AKSlot
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.Identities

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

/-- The `ℋ⁶`-membership and norm bound of the `D_θF_*`-slot. -/
theorem starSlotB : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    Work.Spaces.HkMem α 6
        (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
    Work.Spaces.HkNorm α 6
        (fun z θ => z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ≤ C := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongPersist.L3Rhs.ang_mul_HkSq_le 6
  obtain ⟨R, hR0, hrad⟩ := Work.FTS.StrongPersist.AK6.akRho_jet_bound6
  obtain ⟨_SAK, _hSAK, hAKb⟩ := Work.FTS.StrongPersist.AK_Mem6
  choose Sq hSq0 hSq using fun m : ℕ => Work.FTS.StrongPersist.W6Aux.deriv_iter_qfun_bounded m
  set Bq : ℝ := 4 / 3 + Sq 0 + Sq 1 + Sq 2 + Sq 3 + Sq 4 + Sq 5 with hBqdef
  have hBq0 : 0 < Bq := by
    rw [hBqdef]; linarith [hSq0 0, hSq0 1, hSq0 2, hSq0 3, hSq0 4, hSq0 5]
  have hBq43 : (4 : ℝ) / 3 ≤ Bq := by
    rw [hBqdef]; linarith [hSq0 0, hSq0 1, hSq0 2, hSq0 3, hSq0 4, hSq0 5]
  have hBqle : ∀ m : ℕ, m ≤ 5 → Sq m ≤ Bq := by
    intro m hm
    rw [hBqdef]
    interval_cases m <;> linarith [hSq0 0, hSq0 1, hSq0 2, hSq0 3, hSq0 4, hSq0 5]
  set X2 : ℝ := 2 * (700 * R * 10 ^ 4 + 49 * 10 ^ 12 * R * 700) with hX2def
  have hX20 : 0 ≤ X2 := by rw [hX2def]; positivity
  refine ⟨Real.sqrt (C₁ * Bq ^ 2 * X2) + 1, by positivity, ?_⟩
  intro α hαIoc
  have hα : 0 < α := hαIoc.1
  have hα1 : α ≤ 1 := hαIoc.2
  obtain ⟨hAKmem, _⟩ := hAKb α hα hα1
  have hmemAK : Work.Spaces.HkMem α 6 (fun z θ => α * Work.Construction.AK α z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 6 α hAKmem
  have hSOAK : Work.FTS.EllipticEst.SmoothOpen (fun z θ => α * Work.Construction.AK α z θ) :=
    smoothOpen_alphaAK α
  have hSOa : Work.FTS.EllipticEst.SmoothOpen (fun x (θ : ℝ) => α * Work.Spaces.qfun θ) :=
    Work.FTS.StrongPersist.H6Pair6Aux.so_snd (contDiff_const.mul Work.Spaces.qfun_smooth)
  have haB : ∀ θ ∈ Work.Spaces.Iθ, |α * Work.Spaces.qfun θ| ≤ α * Bq := by
    intro θ hθ
    rw [abs_mul, abs_of_pos hα]
    have hq : |Work.Spaces.qfun θ| ≤ 4 / 3 := by
      have hq' : Work.Spaces.qfun θ = Real.cos (2 * θ) - 1 / 3 := rfl
      rw [hq', abs_le]
      constructor <;> linarith [Real.neg_one_le_cos (2 * θ), Real.cos_le_one (2 * θ)]
    exact mul_le_mul_of_nonneg_left (le_trans hq hBq43) hα.le
  have hjet : ∀ i : ℕ, 1 ≤ i → i ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter i (fun x (θ' : ℝ) => α * Work.Spaces.qfun θ') 0 θ|
        ≤ (α * Bq) * Real.sin (2 * θ) := by
    intro i hi hi6 θ hθ
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hDth : Work.Spaces.DthIter (j + 1)
          (fun x (θ' : ℝ) => α * Work.Spaces.qfun θ') 0 θ
        = Work.Spaces.dthU^[j + 1] (fun θ' => α * Work.Spaces.qfun θ') θ := by
      have h := Work.Spaces.DthIter_decomp (j + 1)
        (fun θ' => α * Work.Spaces.qfun θ') (fun _ => (1 : ℝ)) 0 θ
      simpa using h
    have hval : Work.Spaces.dthU^[j + 1] (fun θ' => α * Work.Spaces.qfun θ') θ
        = α * (Real.sin (2 * θ) * deriv (Work.Spaces.dthU^[j] Work.Spaces.qfun) θ) := by
      rw [Function.iterate_succ_apply', Work.Spaces.dthU_apply,
        Work.Spaces.dthU_iter_const_mul, Work.Spaces.deriv_const_mul']
      ring
    rw [hDth, hval, abs_mul, abs_mul, abs_of_pos hα,
      abs_of_nonneg (Work.FTS.LocData.sin_two_nonneg hθ)]
    have hb : |deriv (Work.Spaces.dthU^[j] Work.Spaces.qfun) θ| ≤ Sq j := hSq j θ hθ
    have hj5 : j ≤ 5 := by omega
    have hsin : 0 ≤ Real.sin (2 * θ) := Work.FTS.LocData.sin_two_nonneg hθ
    calc α * (Real.sin (2 * θ) * |deriv (Work.Spaces.dthU^[j] Work.Spaces.qfun) θ|)
        ≤ α * (Real.sin (2 * θ) * Bq) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (le_trans hb (hBqle j hj5)) hsin) hα.le
      _ = (α * Bq) * Real.sin (2 * θ) := by ring
  obtain ⟨hmem, hsq⟩ := hC₁ α hα hα1 (fun θ => α * Work.Spaces.qfun θ) (α * Bq)
    (mul_pos hα hBq0) hSOa haB hjet (fun z θ => α * Work.Construction.AK α z θ) hSOAK hmemAK
  have hpt := alphaAK_integrand_le hR0 hrad α hα hα1
  have hsqAK : Work.Spaces.HkSq α 6 (fun z θ => α * Work.Construction.AK α z θ) ≤ X2 := by
    rw [hX2def]
    exact Work.FTS.StrongPersist.AK6.hkSq_le_of_integrand_le6 hα hα1
      (by positivity) (by positivity) hpt
  have hid : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      z / (1 + z) * Work.Spaces.Dth (Work.Construction.Fstar α) z θ
        = (α * Work.Spaces.qfun θ) * (α * Work.Construction.AK α z θ) := by
    intro z hz θ hθ
    rw [Dth_Fstar_eq hα z θ hθ,
      show z / (1 + z) * (α * Work.Spaces.qfun θ * Work.Construction.Fstar α z θ)
          = (α * Work.Spaces.qfun θ)
              * (z / (1 + z) * Work.Construction.Fstar α z θ) from by ring,
      zShift_Fstar_eq hα hα1 z hz θ hθ]
  refine ⟨hkMem_congr_Izθ (fun z hz θ hθ => (hid z hz θ hθ).symm) hmem, ?_⟩
  rw [hkNorm_congr_Izθ hid]
  have hnorm : Work.Spaces.HkNorm α 6
      (fun z θ => (fun θ => α * Work.Spaces.qfun θ) θ
        * (fun z θ => α * Work.Construction.AK α z θ) z θ) ≤ Real.sqrt (C₁ * Bq ^ 2 * X2) := by
    rw [Work.Spaces.HkNorm]
    refine Real.sqrt_le_sqrt ?_
    calc Work.Spaces.HkSq α 6 (fun z θ => (fun θ => α * Work.Spaces.qfun θ) θ
          * (fun z θ => α * Work.Construction.AK α z θ) z θ)
        ≤ C₁ * (α * Bq) ^ 2 * Work.Spaces.HkSq α 6
            (fun z θ => α * Work.Construction.AK α z θ) := hsq
      _ ≤ C₁ * (α * Bq) ^ 2 * X2 := mul_le_mul_of_nonneg_left hsqAK (by positivity)
      _ = C₁ * α ^ 2 * Bq ^ 2 * X2 := by ring
      _ ≤ 1 * (C₁ * Bq ^ 2 * X2) := by
          have h1 : α ^ 2 ≤ 1 := by nlinarith [hα, hα1]
          have h3 : (0 : ℝ) ≤ C₁ * Bq ^ 2 * X2 := by positivity
          calc C₁ * α ^ 2 * Bq ^ 2 * X2 = (C₁ * Bq ^ 2 * X2) * α ^ 2 := by ring
            _ ≤ (C₁ * Bq ^ 2 * X2) * 1 := mul_le_mul_of_nonneg_left h1 h3
            _ = 1 * (C₁ * Bq ^ 2 * X2) := by ring
      _ = C₁ * Bq ^ 2 * X2 := by ring
  linarith [hnorm, Real.sqrt_nonneg (C₁ * Bq ^ 2 * X2)]

end

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
