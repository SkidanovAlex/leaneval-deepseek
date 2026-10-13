/-
# `FKstarSlotPiece` — the two `FK f × star-slot` pieces of the `N`-row

The `N`-row of the level-`6` nonlinear estimate contains the two terms
`FK F · D_θF_*` and `sin²θ · FK F · F_*` (`Work.Construction.N`), where
`FK F z = ∫_θ F z θ K θ` is the angular moment and `F_* = Fstar α` the star profile.
This module proves that both are honest `ℋ⁶`-functions with an explicit bound, *priced by the
`ℋ⁶`-norm of `FK f` alone* (the star slots are priced by their `𝒲^{6,∞}`-data, which is
`O(α)` uniformly in `α ∈ (0,1]`).

The route is the `C^6` `𝒲^{6,∞}`-priced product rule (`hknorm_mul_of_WlInf6_cd6`, applied at
the honest range `0 < α ≤ 1` as `hknorm_mul_WlInf6_cd6'`).  The second piece uses it twice:

* `F_* · FK f`: the star slot `F_*` is `𝒲^{6,∞}` with `|F_*| ≤ C_F α` (`Fstar_W6`), and
  `FK f` is `C^6` + `ℋ⁶` with norm `≤ Kf`;
* `sin²θ · (F_* · FK f)`: the angular factor `sin²θ` is a function of `θ` alone, so its
  `𝒲^{6,∞}`-data is the level-`6` `θ`-only reduction (`WlInf_theta_only_level6`) fed with the
  weighted bounds for `D_θ^j(sin²θ)` (`dthU_sinSq_weight`).

The first piece is one product rule with the star slot `D_θF_*` (`DthFstar_W6`, whose
`𝒲^{6,∞}`-norm is `O(α²)`) and `FK f`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.Construction.Defs
import Submission.Work.FTS.StrongPersist.N6_fkH
import Submission.Work.FTS.NonlinRows.NRow10aux.hkmem_of_majorant
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongPersist.DthFstar_W6
import Submission.Work.FTS.StrongPersist.Fstar_W6
import Submission.Work.FTS.GalBasis.exists_cc_of_honClass
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.hknorm_mul_of_WlInf6_cd6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.WlInf_theta_only_level6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.dthU_sinSq_weight

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary `rpow` helpers (real exponents throughout) -/

private theorem rpow_neg_half_mul_two_le {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ^ (-(1 / 2 : ℝ)) * α ^ (2 : ℝ) ≤ α ^ (-(1 : ℝ)) := by
  rw [← Real.rpow_add hα, show (-(1 / 2 : ℝ)) + 2 = (3 / 2 : ℝ) by norm_num]
  exact Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)

private theorem rpow_neg_half_mul_one_le_one {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ^ (-(1 / 2 : ℝ)) * α ^ (1 : ℝ) ≤ 1 := by
  rw [← Real.rpow_add hα, show (-(1 / 2 : ℝ)) + 1 = (1 / 2 : ℝ) by norm_num]
  exact Real.rpow_le_one hα.le hα1 (by norm_num)

/-! ## Two auxiliary lemmas -/

/-- The `𝒲^{6,∞}`-data of the explicit angular profile `sin²θ`: a function of `θ` alone, so
only the angular slots of `WlInf` survive (`WlInf_theta_only_level6`), and the angular
iterates satisfy the weighted bound (`dthU_sinSq_weight`). -/
theorem WlInf_sinSq : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    Work.Spaces.WlInfMem α 6 (fun z θ => Real.sin θ ^ 2) ∧
    Work.Spaces.WlInf α 6 (fun z θ => Real.sin θ ^ 2) ≤ C := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := dthU_sinSq_weight
  refine ⟨7 * max 1 C₂, by positivity, fun α hα hα1 => ?_⟩
  have hC : 0 < max 1 C₂ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hg : ∀ θ ∈ Work.Spaces.Iθ, |Real.sin θ ^ 2| ≤ max 1 C₂ := by
    intro θ _
    have h1 : Real.sin θ ^ 2 ≤ 1 := by
      nlinarith [Real.sin_le_one θ, Real.neg_one_le_sin θ]
    rw [abs_of_nonneg (sq_nonneg _)]
    exact le_trans h1 (le_max_left _ _)
  have hw : ∀ j : ℕ, 1 ≤ j → j ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] (fun θ => Real.sin θ ^ 2) θ| * (Real.sin (2 * θ)) ^ (-(α / 5))
        / (α + Real.sin (2 * θ)) ≤ max 1 C₂ :=
    fun j hj1 hj6 θ hθ => le_trans (hC₂ α hα hα1 j hj1 hj6 θ hθ) (le_max_right _ _)
  obtain ⟨hmem, hle⟩ := WlInf_theta_only_level6 α (max 1 C₂) hα hC
    (fun θ => Real.sin θ ^ 2) hg hw
  exact ⟨hmem, hle⟩

/-- The `𝒲^{6,∞}`-priced `C^6` product rule at every `α ∈ (0,1]`: the auxiliary
`hknorm_mul_aux6` fed with the `C^6` slot lemmas
(`Cd6.zslot_le_winf6_cd6`, `Cd6.dzIter_w_mean_le6_cd6`, `Cd6.mslot_le_winf6_cd6`). -/
theorem hknorm_mul_WlInf6_cd6' : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ),
    0 < α → α ≤ 1 →
    ContDiffOn ℝ 6 (Function.uncurry f) Work.FTS.EllipticEst.Q0 →
    Work.Spaces.WlInfMem α 6 f →
    ContDiffOn ℝ 6 (Function.uncurry g) Work.FTS.EllipticEst.Q0 →
    Work.Spaces.HkMem α 6 g →
    Work.Spaces.HkMem α 6 (fun z θ => f z θ * g z θ) ∧
    Work.Spaces.HkNorm α 6 (fun z θ => f z θ * g z θ)
      ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 6 f * Work.Spaces.HkNorm α 6 g := by
  obtain ⟨Cz, hCz, hZ⟩ := Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.zslot_le_winf6_cd6
  obtain ⟨CB, _hCB, hCBmean⟩ :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.dzIter_w_mean_le6_cd6
  obtain ⟨Cm, hCm, hMx⟩ :=
    Work.FTS.StrongPersist.H6Rows.N0pair6bWork.Cd6.mslot_le_winf6_cd6 CB
  refine ⟨Real.sqrt ((7 * Cz + 49 * Cm) * 42701), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro α f g hα hα1 hfs hfw hgs hgm
  exact hknorm_mul_aux6 hα hα1 hfs hfw hgs hgm hCz hCm
    (fun i hi z θ hz hθ0 hθ1 => hZ α f g hα hα1 hfs hfw hgs i hi z θ hz hθ0 hθ1)
    (fun I J hI hIJ z θ hz hθ0 hθ1 => hMx α f g hα hα1 hfs hfw hgs hgm
      (fun d hd z' θ' hz' hθ0' hθ1' =>
        hCBmean α g d hα hα1 hgs hgm hd z' θ' hz' hθ0' hθ1')
      I J hI hIJ z θ hz hθ0 hθ1)

/-! ## The requested lemma -/

theorem FKstarSlotPiece : ∃ C : ℝ, 0 < C ∧ ∀ {α Kf : ℝ} {f : ℝ → ℝ → ℝ},
    0 < α → α ≤ 1 → 0 ≤ Kf →
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f →
    ContDiffOn ℝ 6 (Function.uncurry (fun z (_ : ℝ) => Work.Construction.FK f z))
      Work.FTS.EllipticEst.Q0 →
    Work.Spaces.HkMem α 6 (fun z (_ : ℝ) => Work.Construction.FK f z) →
    Work.Spaces.HkNorm α 6 (fun z (_ : ℝ) => Work.Construction.FK f z) ≤ Kf →
    (ContDiffOn ℝ 6 (Function.uncurry
        (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth (Work.Construction.Fstar α) z θ))
        Work.FTS.EllipticEst.Q0 ∧
      Work.Spaces.HkMem α 6
        (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) ∧
      Work.Spaces.HkNorm α 6
        (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
        ≤ C * α ^ (-(1 : ℝ)) * Kf) ∧
    (ContDiffOn ℝ 6 (Function.uncurry
        (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z
          * Work.Construction.Fstar α z θ)) Work.FTS.EllipticEst.Q0 ∧
      Work.Spaces.HkMem α 6
        (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z
          * Work.Construction.Fstar α z θ) ∧
      Work.Spaces.HkNorm α 6
        (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z
          * Work.Construction.Fstar α z θ)
        ≤ C * α ^ (-(1 : ℝ)) * Kf) := by
  obtain ⟨Cmul, hCmulpos, hmul⟩ := hknorm_mul_WlInf6_cd6'
  obtain ⟨Cd, hCdpos, hDth⟩ := Work.FTS.StrongPersist.DthFstar_W6
  obtain ⟨CF, hCFpos, hFstar⟩ := Work.FTS.StrongPersist.Fstar_W6
  obtain ⟨CA, hCApos, hAsin⟩ := WlInf_sinSq
  refine ⟨max 1 (Cmul * Cd + Cmul * Cmul * CF * CA), by positivity, ?_⟩
  intro α Kf f hα hα1 hKf _hfSmooth _hfMem hFKcd hFKmem hFKnrm
  have hα0 : 0 ≤ α := hα.le
  have hKfnn : 0 ≤ Kf := hKf
  have hCmulnn : 0 ≤ Cmul := hCmulpos.le
  have hCdnn : 0 ≤ Cd := hCdpos.le
  have hCFnn : 0 ≤ CF := hCFpos.le
  have hCAnn : 0 ≤ CA := hCApos.le
  have hrp_nn : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0 _
  have hrp1_nn : 0 ≤ α ^ (-(1 : ℝ)) := Real.rpow_nonneg hα0 _
  have hrp_le : α ^ (-(1 / 2 : ℝ)) ≤ α ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hα hα1 (by norm_num)
  -- the star-slot inputs
  have hψ1sm : ContDiffOn ℝ 6 (Function.uncurry (Work.Spaces.Dth (Work.Construction.Fstar α)))
      Work.FTS.EllipticEst.Q0 :=
    (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).Dth.forall 6
  have hψ1mem : Work.Spaces.WlInfMem α 6 (Work.Spaces.Dth (Work.Construction.Fstar α)) :=
    (hDth α hα hα1).1
  have hψ1bd : Work.Spaces.WlInf α 6 (Work.Spaces.Dth (Work.Construction.Fstar α))
      ≤ Cd * α ^ (2 : ℝ) := by
    rw [Real.rpow_two]
    exact (hDth α hα hα1).2
  have hψ2mem : Work.Spaces.WlInfMem α 6 (fun z θ => Real.sin θ ^ 2) := (hAsin α hα hα1).1
  have hψ2bd : Work.Spaces.WlInf α 6 (fun z θ => Real.sin θ ^ 2) ≤ CA := (hAsin α hα hα1).2
  have hFmem : Work.Spaces.WlInfMem α 6 (Work.Construction.Fstar α) := (hFstar α hα hα1).1
  have hFbd : Work.Spaces.WlInf α 6 (Work.Construction.Fstar α) ≤ CF * α ^ (1 : ℝ) := by
    rw [Real.rpow_one]
    exact (hFstar α hα hα1).2
  have hFsm : ContDiffOn ℝ 6 (Function.uncurry (Work.Construction.Fstar α))
      Work.FTS.EllipticEst.Q0 := (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α).forall 6
  have hAsm : ContDiff ℝ (6 : WithTop ℕ∞) (fun p : ℝ × ℝ => Real.sin p.2 ^ 2) := by fun_prop
  have hAcd : ContDiffOn ℝ 6 (Function.uncurry (fun z θ => Real.sin θ ^ 2))
      Work.FTS.EllipticEst.Q0 := by
    convert hAsm.contDiffOn using 1
    funext p
    rcases p with ⟨z, θ⟩
    rfl
  -- the two `max`-bounds for the final constant
  have hcle1 : Cmul * Cd ≤ max 1 (Cmul * Cd + Cmul * Cmul * CF * CA) := by
    refine le_trans ?_ (le_max_right _ _)
    exact le_add_of_nonneg_right (by positivity)
  have hcle2 : Cmul * Cmul * CF * CA ≤ max 1 (Cmul * Cd + Cmul * Cmul * CF * CA) := by
    refine le_trans ?_ (le_max_right _ _)
    exact le_add_of_nonneg_left (by positivity)
  -- ============ conjunct 1 ============
  obtain ⟨hmem1r, hbd1r⟩ := hmul α (Work.Spaces.Dth (Work.Construction.Fstar α))
    (fun z (_ : ℝ) => Work.Construction.FK f z) hα hα1 hψ1sm hψ1mem hFKcd hFKmem
  have hmem1 : Work.Spaces.HkMem α 6
      (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth (Work.Construction.Fstar α) z θ) :=
    Work.FTS.GalBasis.HkMem_congr_all (fun z θ => mul_comm _ _) α 6 hmem1r
  have hbd1 : Work.Spaces.HkNorm α 6
      (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
      ≤ max 1 (Cmul * Cd + Cmul * Cmul * CF * CA) * α ^ (-(1 : ℝ)) * Kf := by
    have heq : Work.Spaces.HkNorm α 6
          (fun z θ => Work.Construction.FK f z * Work.Spaces.Dth (Work.Construction.Fstar α) z θ)
        = Work.Spaces.HkNorm α 6
          (fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ * Work.Construction.FK f z) :=
      Work.FTS.GalBasis.HkNorm_congr_all (fun z θ => mul_comm _ _) α 6
    rw [heq]
    refine le_trans hbd1r ?_
    calc Cmul * α ^ (-(1 / 2 : ℝ))
          * Work.Spaces.WlInf α 6 (Work.Spaces.Dth (Work.Construction.Fstar α))
          * Work.Spaces.HkNorm α 6 (fun z (_ : ℝ) => Work.Construction.FK f z)
        ≤ Cmul * α ^ (-(1 / 2 : ℝ)) * (Cd * α ^ (2 : ℝ)) * Kf := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hψ1bd (mul_nonneg hCmulnn hrp_nn)) hFKnrm
            (Real.sqrt_nonneg _) ?_
          positivity
      _ = (Cmul * Cd) * (α ^ (-(1 / 2 : ℝ)) * α ^ (2 : ℝ)) * Kf := by ring
      _ ≤ (Cmul * Cd) * α ^ (-(1 : ℝ)) * Kf := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (rpow_neg_half_mul_two_le hα hα1) (by positivity)) hKfnn
      _ ≤ max 1 (Cmul * Cd + Cmul * Cmul * CF * CA) * α ^ (-(1 : ℝ)) * Kf := by
          gcongr
  -- ============ conjunct 2 ============
  -- step 1: `F_* · FK f`
  obtain ⟨hmemFφ, hbdFφ⟩ := hmul α (Work.Construction.Fstar α)
    (fun z (_ : ℝ) => Work.Construction.FK f z) hα hα1 hFsm hFmem hFKcd hFKmem
  have hbdFφ' : Work.Spaces.HkNorm α 6
      (fun z θ => Work.Construction.Fstar α z θ * Work.Construction.FK f z)
      ≤ Cmul * CF * Kf := by
    refine le_trans hbdFφ ?_
    calc Cmul * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 6 (Work.Construction.Fstar α)
          * Work.Spaces.HkNorm α 6 (fun z (_ : ℝ) => Work.Construction.FK f z)
        ≤ Cmul * α ^ (-(1 / 2 : ℝ)) * (CF * α ^ (1 : ℝ)) * Kf := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hFbd (mul_nonneg hCmulnn hrp_nn)) hFKnrm
            (Real.sqrt_nonneg _) ?_
          positivity
      _ = (Cmul * CF) * (α ^ (-(1 / 2 : ℝ)) * α ^ (1 : ℝ)) * Kf := by ring
      _ ≤ (Cmul * CF) * 1 * Kf := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (rpow_neg_half_mul_one_le_one hα hα1) (by positivity)) hKfnn
      _ = Cmul * CF * Kf := by ring
  have hFφcd : ContDiffOn ℝ 6
      (Function.uncurry (fun z θ => Work.Construction.Fstar α z θ * Work.Construction.FK f z))
      Work.FTS.EllipticEst.Q0 := hFsm.mul hFKcd
  -- step 2: `sin²θ · (F_* · FK f)`
  obtain ⟨hmem2r, hbd2r⟩ := hmul α (fun z θ => Real.sin θ ^ 2)
    (fun z θ => Work.Construction.Fstar α z θ * Work.Construction.FK f z)
    hα hα1 hAcd hψ2mem hFφcd hmemFφ
  have hbd2r' : Work.Spaces.HkNorm α 6
      (fun z θ => Real.sin θ ^ 2 * (Work.Construction.Fstar α z θ * Work.Construction.FK f z))
      ≤ Cmul * Cmul * CF * CA * α ^ (-(1 / 2 : ℝ)) * Kf := by
    refine le_trans hbd2r ?_
    calc Cmul * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.WlInf α 6 (fun z θ => Real.sin θ ^ 2)
          * Work.Spaces.HkNorm α 6
            (fun z θ => Work.Construction.Fstar α z θ * Work.Construction.FK f z)
        ≤ Cmul * α ^ (-(1 / 2 : ℝ)) * CA * (Cmul * CF * Kf) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hψ2bd (mul_nonneg hCmulnn hrp_nn)) hbdFφ'
            (Real.sqrt_nonneg _) ?_
          positivity
      _ = Cmul * Cmul * CF * CA * α ^ (-(1 / 2 : ℝ)) * Kf := by ring
  have hmem2 : Work.Spaces.HkMem α 6
      (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * Work.Construction.Fstar α z θ) :=
    Work.FTS.GalBasis.HkMem_congr_all (fun z θ => by ring) α 6 hmem2r
  have hbd2 : Work.Spaces.HkNorm α 6
      (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * Work.Construction.Fstar α z θ)
      ≤ max 1 (Cmul * Cd + Cmul * Cmul * CF * CA) * α ^ (-(1 : ℝ)) * Kf := by
    have heq : Work.Spaces.HkNorm α 6
          (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * Work.Construction.Fstar α z θ)
        = Work.Spaces.HkNorm α 6
          (fun z θ => Real.sin θ ^ 2 * (Work.Construction.Fstar α z θ * Work.Construction.FK f z)) :=
      Work.FTS.GalBasis.HkNorm_congr_all (fun z θ => by ring) α 6
    rw [heq]
    refine le_trans hbd2r' ?_
    have hXnn : 0 ≤ Cmul * Cmul * CF * CA := by positivity
    calc Cmul * Cmul * CF * CA * α ^ (-(1 / 2 : ℝ)) * Kf
        ≤ Cmul * Cmul * CF * CA * α ^ (-(1 : ℝ)) * Kf := by
          refine mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hrp_le hXnn) hKfnn
      _ ≤ max 1 (Cmul * Cd + Cmul * Cmul * CF * CA) * α ^ (-(1 : ℝ)) * Kf := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcle2 hrp1_nn) hKfnn
  have hcd2r : ContDiffOn ℝ 6 (Function.uncurry
      (fun z θ => Real.sin θ ^ 2 * (Work.Construction.Fstar α z θ * Work.Construction.FK f z)))
      Work.FTS.EllipticEst.Q0 := hAcd.mul hFφcd
  have hcd2 : ContDiffOn ℝ 6 (Function.uncurry
      (fun z θ => Real.sin θ ^ 2 * Work.Construction.FK f z * Work.Construction.Fstar α z θ))
      Work.FTS.EllipticEst.Q0 := by
    refine hcd2r.congr (fun p _ => ?_)
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry]
    ring
  refine ⟨⟨?_, hmem1, hbd1⟩, ⟨hcd2, hmem2, hbd2⟩⟩
  convert hFKcd.mul hψ1sm using 1
  funext p
  rcases p with ⟨z, θ⟩
  rfl

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
