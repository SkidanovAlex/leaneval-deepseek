import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.N6_fkH
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.FKstarSlotPiece
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.hkMem_fk_mul
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fk_hkMem
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.hknorm_mul_of_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Row6.fkH6_norm_le
import Submission.Work.FTS.StrongPersist.Fstar_W6
import Submission.Work.FTS.GalBasis.exists_cc_of_honClass

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary helpers

The `ℋ⁶`-energy of a function is the square of its `ℋ⁶`-norm (`HkNorm` is *defined* as the
square root of `HkSq`), so a bound on the norm squares into a bound on the energy.  The three
`rpow` facts are the small arithmetic of `α ∈ (0,1]` used to convert the `α`-powers of the
three product estimates (`α^{-1/2}·α ≤ 1`, `(α^{-1})² = α^{-2}`, `1 ≤ α^{-2}`) into the single
factor `α^{-2}` of the statement. -/

private theorem HkSq_eq_norm_sq (α : ℝ) (k : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α k g = (Work.Spaces.HkNorm α k g) ^ 2 :=
  (Real.sq_sqrt (Work.Spaces.HkSq_nonneg α k g)).symm

private theorem rpow_neg_half_mul_le_one {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    α ^ (-(1 / 2 : ℝ)) * α ≤ 1 := by
  have h1 : α ^ (-(1 / 2 : ℝ)) * α ^ (1 : ℝ) ≤ 1 := by
    rw [← Real.rpow_add hα0, show (-(1 / 2 : ℝ)) + 1 = (1 / 2 : ℝ) by norm_num]
    exact Real.rpow_le_one hα0.le hα1 (by norm_num)
  simpa [Real.rpow_one] using h1

private theorem rpow_neg_one_sq {α : ℝ} (hα0 : 0 < α) :
    (α ^ (-(1 : ℝ))) ^ 2 = α ^ (-(2 : ℝ)) := by
  rw [pow_two, ← Real.rpow_add hα0]
  norm_num

private theorem one_le_rpow_neg_two {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    1 ≤ α ^ (-(2 : ℝ)) := by
  have h1 : (1 : ℝ) ≤ α ^ (-(1 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα0 hα1 (show (-(1 : ℝ)) ≤ 0 by norm_num)
    rwa [Real.rpow_zero] at h
  calc (1 : ℝ) = 1 ^ 2 := by norm_num
    _ ≤ (α ^ (-(1 : ℝ))) ^ 2 := pow_le_pow_left₀ zero_le_one h1 2
    _ = α ^ (-(2 : ℝ)) := rpow_neg_one_sq hα0

/-! ## The four pieces -/

theorem fkStarPieces : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1,
    ∀ (f : Work.FTS.Galerkin.Fn) (M : ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M →
      Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK f z)
          ≤ C * Real.sqrt (Work.Spaces.HkSq α 6 f) ∧
      Work.Spaces.HkSq α 6 (fun z θ => Work.Construction.FK f z * Work.Construction.Fstar α z θ)
          ≤ C * α ^ (-(2 : ℝ)) * Work.Spaces.HkSq α 6 f ∧
      Work.Spaces.HkSq α 6 (fun z θ => Work.Construction.FK f z
            * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
          ≤ C * α ^ (-(2 : ℝ)) * Work.Spaces.HkSq α 6 f ∧
      Work.Spaces.HkSq α 6 (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z
            * Work.Construction.Fstar α z θ)
          ≤ C * α ^ (-(2 : ℝ)) * Work.Spaces.HkSq α 6 f := by
  -- the four universal constants
  obtain ⟨A, hApos, hA⟩ := Work.FTS.StrongPersist.H6Row6.fkH6_norm_le
  obtain ⟨Cmul, hCmulpos, hmul⟩ :=
    Work.FTS.StrongPersist.H6Rows.Npair6SupAux.hknorm_mul_WlInf6_cd6'
  obtain ⟨CF, hCFpos, hFsW⟩ := Work.FTS.StrongPersist.Fstar_W6
  obtain ⟨Css, hCsspos, hFSS⟩ := Work.FTS.StrongPersist.H6Rows.Npair6SupAux.FKstarSlotPiece
  have hAnn : 0 ≤ A := hApos.le
  have hCmulnn : 0 ≤ Cmul := hCmulpos.le
  have hCFnn : 0 ≤ CF := hCFpos.le
  have hCssnn : 0 ≤ Css := hCsspos.le
  refine ⟨1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2, by positivity, ?_⟩
  intro α hα f M hD
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  have hsm : Work.FTS.EllipticEst.SmoothOpen f := hD.sm
  have hmem6 : Work.Spaces.HkMem α 6 f := hD.h6
  have hmem7 : Work.Spaces.HkMem α 7 f := hD.h7
  -- `FK f` is `C⁶` on the open quadrant and lies in `ℋ⁶`
  have hFKcd : ContDiffOn ℝ 6
      (Function.uncurry (fun z (_ : ℝ) => Work.Construction.FK f z))
      Work.FTS.EllipticEst.Q0 := by
    have h6 : ContDiffOn ℝ 6 (fun z => Work.Construction.FK f z) (Set.Ioi (0 : ℝ)) := by
      have hF : ContDiffOn ℝ 6 (Work.Elliptic.Fstar f) (Set.Ioi (0 : ℝ)) :=
        Work.FTS.EllipticEst.UopHk.contDiffOn_Fstar_of_smoothOpen_Hk α 7 f hsm hmem7
          (by norm_num)
      rw [Work.FTS.StrongPersist.L3Rhs.NfkAux.fk_eq_three_Fstar f]
      have h3 : ContDiffOn ℝ 6 (fun z => (3 : ℝ) • Work.Elliptic.Fstar f z)
          (Set.Ioi (0 : ℝ)) := hF.const_smul (3 : ℝ)
      simpa only [Pi.smul_apply, smul_eq_mul] using h3
    exact Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_radial h6
  have hFKmem : Work.Spaces.HkMem α 6 (fun z (_ : ℝ) => Work.Construction.FK f z) :=
    Work.FTS.StrongPersist.H6Rows.Npair6BWork.fk_hkMem α hα f hsm hmem6
  -- the norm bound for `FK f`
  have hKfbd : Work.Spaces.HkNorm α 6 (fun z (_ : ℝ) => Work.Construction.FK f z)
      ≤ A * Work.Spaces.HkNorm α 6 f := hA α hα0 hα1 f hsm hmem6
  have hKfnn : 0 ≤ Work.Spaces.HkNorm α 6 (fun z (_ : ℝ) => Work.Construction.FK f z) :=
    Work.Spaces.HkNorm_nonneg α 6 _
  -- the constant comparisons
  have hAleC : A ≤ 1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2 := by
    nlinarith [sq_nonneg (Cmul * CF * A), sq_nonneg (Css * A)]
  have hC2leC : (Cmul * CF * A) ^ 2 ≤ 1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2 := by
    nlinarith [sq_nonneg (Css * A)]
  have hC3leC : (Css * A) ^ 2 ≤ 1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2 := by
    nlinarith [sq_nonneg (Cmul * CF * A)]
  -- the norm bound for the `F_* · FK f` product
  have hFstarcd : ContDiffOn ℝ 6 (Function.uncurry (Work.Construction.Fstar α))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).forall 6
  have hstep2 : Work.Spaces.HkNorm α 6
      (fun z θ => Work.Construction.Fstar α z θ * Work.Construction.FK f z)
      ≤ Cmul * CF * A * Work.Spaces.HkNorm α 6 f := by
    obtain ⟨-, hbd2⟩ := hmul α (Work.Construction.Fstar α)
      (fun z (_ : ℝ) => Work.Construction.FK f z) hα0 hα1 hFstarcd
      (hFsW α hα0 hα1).1 hFKcd hFKmem
    have hx : 0 ≤ Cmul * α ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg hCmulnn (Real.rpow_nonneg hα0.le _)
    refine le_trans hbd2 ?_
    calc Cmul * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 6 (Work.Construction.Fstar α)
          * Work.Spaces.HkNorm α 6 (fun z (_ : ℝ) => Work.Construction.FK f z)
        ≤ Cmul * α ^ (-(1 / 2 : ℝ)) * (CF * α) * (A * Work.Spaces.HkNorm α 6 f) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (hFsW α hα0 hα1).2 hx) hKfbd
            (Work.Spaces.HkNorm_nonneg α 6 _) ?_
          positivity
      _ = Cmul * CF * A * (α ^ (-(1 / 2 : ℝ)) * α) * Work.Spaces.HkNorm α 6 f := by ring
      _ ≤ Cmul * CF * A * 1 * Work.Spaces.HkNorm α 6 f := by
          refine mul_le_mul_of_nonneg_right ?_ (Work.Spaces.HkNorm_nonneg α 6 f)
          refine mul_le_mul_of_nonneg_left (rpow_neg_half_mul_le_one hα0 hα1) ?_
          positivity
      _ = Cmul * CF * A * Work.Spaces.HkNorm α 6 f := by ring
  -- ============ conjunct 1 ============
  have hconj1 : Work.Spaces.HkNorm α 6 (fun z _ => Work.Construction.FK f z)
      ≤ (1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2) * Real.sqrt (Work.Spaces.HkSq α 6 f) := by
    refine le_trans hKfbd ?_
    simpa only [Work.Spaces.HkNorm] using
      mul_le_mul_of_nonneg_right hAleC (Work.Spaces.HkNorm_nonneg α 6 f)
  -- ============ conjunct 2 ============
  have hconj2 : Work.Spaces.HkSq α 6
        (fun z θ => Work.Construction.FK f z * Work.Construction.Fstar α z θ)
      ≤ (1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2) * α ^ (-(2 : ℝ))
        * Work.Spaces.HkSq α 6 f := by
    have hsq : Work.Spaces.HkSq α 6
          (fun z θ => Work.Construction.FK f z * Work.Construction.Fstar α z θ)
        = (Work.Spaces.HkNorm α 6
            (fun z θ => Work.Construction.Fstar α z θ * Work.Construction.FK f z)) ^ 2 := by
      rw [Work.FTS.GalBasis.HkSq_congr_all (fun z θ => mul_comm _ _) α 6]
      exact HkSq_eq_norm_sq α 6 _
    rw [hsq]
    calc (Work.Spaces.HkNorm α 6
            (fun z θ => Work.Construction.Fstar α z θ * Work.Construction.FK f z)) ^ 2
        ≤ (Cmul * CF * A * Work.Spaces.HkNorm α 6 f) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 _) hstep2 2
      _ = (Cmul * CF * A) ^ 2 * Work.Spaces.HkSq α 6 f := by
          simp only [mul_pow, Work.Spaces.HkNorm,
            Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 f)]
      _ ≤ (Cmul * CF * A) ^ 2 * α ^ (-(2 : ℝ)) * Work.Spaces.HkSq α 6 f := by
          refine mul_le_mul_of_nonneg_right ?_ (Work.Spaces.HkSq_nonneg α 6 f)
          calc (Cmul * CF * A) ^ 2 = (Cmul * CF * A) ^ 2 * 1 := (mul_one _).symm
            _ ≤ (Cmul * CF * A) ^ 2 * α ^ (-(2 : ℝ)) :=
                mul_le_mul_of_nonneg_left (one_le_rpow_neg_two hα0 hα1) (sq_nonneg _)
      _ ≤ (1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2) * α ^ (-(2 : ℝ))
            * Work.Spaces.HkSq α 6 f := by
          refine mul_le_mul_of_nonneg_right ?_ (Work.Spaces.HkSq_nonneg α 6 f)
          exact mul_le_mul_of_nonneg_right hC2leC (Real.rpow_nonneg hα0.le _)
  -- ============ conjunct 3 ============
  have hconj3 : Work.Spaces.HkSq α 6 (fun z θ => Work.Construction.FK f z
        * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
      ≤ (1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2) * α ^ (-(2 : ℝ))
        * Work.Spaces.HkSq α 6 f := by
    obtain ⟨⟨-, -, hbd3⟩, -⟩ := hFSS (α := α)
      (Kf := Work.Spaces.HkNorm α 6 (fun z (_ : ℝ) => Work.Construction.FK f z))
      hα0 hα1 hKfnn hsm hmem6 hFKcd hFKmem le_rfl
    have hstep : Work.Spaces.HkNorm α 6 (fun z θ => Work.Construction.FK f z
          * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
        ≤ Css * A * α ^ (-(1 : ℝ)) * Work.Spaces.HkNorm α 6 f := by
      refine le_trans hbd3 ?_
      calc Css * α ^ (-(1 : ℝ))
            * Work.Spaces.HkNorm α 6 (fun z (_ : ℝ) => Work.Construction.FK f z)
          ≤ Css * α ^ (-(1 : ℝ)) * (A * Work.Spaces.HkNorm α 6 f) := by
            refine mul_le_mul_of_nonneg_left hKfbd ?_
            exact mul_nonneg hCssnn (Real.rpow_nonneg hα0.le _)
        _ = Css * A * α ^ (-(1 : ℝ)) * Work.Spaces.HkNorm α 6 f := by ring
    rw [HkSq_eq_norm_sq]
    calc (Work.Spaces.HkNorm α 6 (fun z θ => Work.Construction.FK f z
            * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)) ^ 2
        ≤ (Css * A * α ^ (-(1 : ℝ)) * Work.Spaces.HkNorm α 6 f) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 _) hstep 2
      _ = (Css * A) ^ 2 * α ^ (-(2 : ℝ)) * Work.Spaces.HkSq α 6 f := by
          simp only [mul_pow, Work.Spaces.HkNorm,
            Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 f), rpow_neg_one_sq hα0]
      _ ≤ (1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2) * α ^ (-(2 : ℝ))
            * Work.Spaces.HkSq α 6 f := by
          refine mul_le_mul_of_nonneg_right ?_ (Work.Spaces.HkSq_nonneg α 6 f)
          exact mul_le_mul_of_nonneg_right hC3leC (Real.rpow_nonneg hα0.le _)
  -- ============ conjunct 4 ============
  have hconj4 : Work.Spaces.HkSq α 6 (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z
        * Work.Construction.Fstar α z θ)
      ≤ (1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2) * α ^ (-(2 : ℝ))
        * Work.Spaces.HkSq α 6 f := by
    obtain ⟨-, ⟨-, -, hbd4⟩⟩ := hFSS (α := α)
      (Kf := Work.Spaces.HkNorm α 6 (fun z (_ : ℝ) => Work.Construction.FK f z))
      hα0 hα1 hKfnn hsm hmem6 hFKcd hFKmem le_rfl
    have hstep : Work.Spaces.HkNorm α 6 (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z
          * Work.Construction.Fstar α z θ)
        ≤ Css * A * α ^ (-(1 : ℝ)) * Work.Spaces.HkNorm α 6 f := by
      refine le_trans hbd4 ?_
      calc Css * α ^ (-(1 : ℝ))
            * Work.Spaces.HkNorm α 6 (fun z (_ : ℝ) => Work.Construction.FK f z)
          ≤ Css * α ^ (-(1 : ℝ)) * (A * Work.Spaces.HkNorm α 6 f) := by
            refine mul_le_mul_of_nonneg_left hKfbd ?_
            exact mul_nonneg hCssnn (Real.rpow_nonneg hα0.le _)
        _ = Css * A * α ^ (-(1 : ℝ)) * Work.Spaces.HkNorm α 6 f := by ring
    rw [HkSq_eq_norm_sq]
    calc (Work.Spaces.HkNorm α 6 (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z
            * Work.Construction.Fstar α z θ)) ^ 2
        ≤ (Css * A * α ^ (-(1 : ℝ)) * Work.Spaces.HkNorm α 6 f) ^ 2 :=
          pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 _) hstep 2
      _ = (Css * A) ^ 2 * α ^ (-(2 : ℝ)) * Work.Spaces.HkSq α 6 f := by
          simp only [mul_pow, Work.Spaces.HkNorm,
            Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 f), rpow_neg_one_sq hα0]
      _ ≤ (1 + A + (Cmul * CF * A) ^ 2 + (Css * A) ^ 2) * α ^ (-(2 : ℝ))
            * Work.Spaces.HkSq α 6 f := by
          refine mul_le_mul_of_nonneg_right ?_ (Work.Spaces.HkSq_nonneg α 6 f)
          exact mul_le_mul_of_nonneg_right hC3leC (Real.rpow_nonneg hα0.le _)
  exact ⟨hconj1, hconj2, hconj3, hconj4⟩

end Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux
