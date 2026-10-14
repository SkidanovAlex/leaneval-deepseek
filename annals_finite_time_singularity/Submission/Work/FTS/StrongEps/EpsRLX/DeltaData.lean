import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.GalBasis.exists_cc_of_honClass
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongEps.EComparison.L12_sub_HkMem
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_const_mul
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsMemOfClassCJeps
import Submission.Work.FTS.StrongEps.EpsRLX.DeltaSlotEpsSq
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartAux
import Submission.Work.FTS.StrongEps.L12Sub4.L12ZeroLog
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongPersist.H6Aux.RStep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkDzdIterSharp
import Submission.Work.FTS.StrongPersist.H6Rows.H6Pair_of_rows_C6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.rowSumZ0
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.AuxProof
import Submission.Work.FTS.StrongPersist.SP6.EH6
import Submission.Work.FTS.StrongPersist.SP6.F0SixYblk
import Submission.Work.FTS.StrongPersist.StarPkg6Assembly
import Submission.Work.FTS.StrongPersist.StarPkg6Fields
import Submission.Work.FTS_BSIdentP.Slim.TendstoPhiOddPi
import Submission.Work.FTS_LocDatum3a.Assembly
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform
import Submission.Work.Spaces.pz_DthIter_mul_eq
-- ===== merged: Submission.Work.FTS.StrongEps.EpsE4Thr.TransO.LevelPkgInstO =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.TransO

open Work.FTS.Galerkin (Fn)
open Work.FTS.StrongEps.EpsE4Thr (CoerAdmO)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two defects as finite-order classes -/

/-- `E1 α f` is `Q0Sm n` for `CoerAdmO α f` and `n ≤ 3`. -/
theorem Q0Sm_E1_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hf : CoerAdmO α f) (n : ℕ) (hn : n ≤ 3) :
    Work.FTS.CoercivityFix.Transfer.Q0Sm n (Work.FTS.CoercivityFix.Transfer.E1 α f) :=
  (ContDiffOn_E1_O α hα hα1 hf).of_le (m := (((n : ℕ)) : WithTop ℕ∞))
    (by exact_mod_cast hn)

/-- `E2 α f` is `Q0Sm n` for `CoerAdmO α f` and `n ≤ 3`. -/
theorem Q0Sm_E2_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : Fn}
    (hf : CoerAdmO α f) (n : ℕ) (hn : n ≤ 3) :
    Work.FTS.CoercivityFix.Transfer.Q0Sm n (Work.FTS.CoercivityFix.Transfer.E2 α f) :=
  (ContDiffOn_E2_O α hα hα1 hf).of_le (m := (((n : ℕ)) : WithTop ℕ∞))
    (by exact_mod_cast hn)

/-! ## The two `AddOKSm` triples -/

/-- **The `AddOKSm` half of `LevelPkgO`**, from the regularity of the two defects. -/
theorem AddOKSm_of_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (hn : n ≤ 3) {f : Fn}
    (hf : CoerAdmO α f) :
    Work.FTS.CoercivityFix.Transfer.AddOKSm α n
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f))
        (Work.FTS.CoercivityFix.Transfer.E1 α f) (Work.Spaces.Dth f)
      ∧ Work.FTS.CoercivityFix.Transfer.AddOKSm α n
          (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dz f))
          (Work.FTS.CoercivityFix.Transfer.E2 α f) (Work.Spaces.Dz f) := by
  obtain ⟨hsLth, hsLdz, hsdth, hsdz⟩ := HkMem_slots_O α hα hn hf
  obtain ⟨hqLth, hqLdz⟩ := Q0Sm_Lhat_slots_O hf.1.1 n
  obtain ⟨hqdth, hqdz⟩ := Q0Sm_Dth_Dz_O hf.1.1 n
  exact
    ⟨⟨hqLth, Q0Sm_E1_O α hα hα1 hf n hn, hqdth,
        hsLth, HkMem_E1_O α hα hα1 hf n hn, hsdth⟩,
      ⟨hqLdz, Q0Sm_E2_O α hα hα1 hf n hn, hqdz,
        hsLdz, HkMem_E2_O α hα hα1 hf n hn, hsdz⟩⟩

/-- **`LevelPkgO` of a concrete level**, from the algebraic and Cauchy–Schwarz packages. -/
theorem levelPkg_of_O (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (hn : n ≤ 3)
    {IP : Fn → Fn → ℝ} {CC : ℝ} (hcomm : Work.FTS.CoercivityFix.Transfer.CommSm α n IP)
    (hCS : Work.FTS.CoercivityFix.Transfer.CSQ α n IP CC) :
    LevelPkgO α n IP CC := by
  refine ⟨hcomm, fun f hf => ?_⟩
  obtain ⟨hAdd1, hAdd2⟩ := AddOKSm_of_O α hα hα1 n hn hf
  obtain ⟨hLdth, hLdz, hdth, hdz⟩ := HkMem_slots_O α hα hn hf
  obtain ⟨hqdth, hqdz⟩ := Q0Sm_Dth_Dz_O hf.1.1 n
  exact ⟨hAdd1, hAdd2,
    hCS (Work.FTS.CoercivityFix.Transfer.E1 α f) (Work.Spaces.Dth f)
      (Q0Sm_E1_O α hα hα1 hf n hn) hqdth (HkMem_E1_O α hα hα1 hf n hn) hdth,
    hCS (Work.FTS.CoercivityFix.Transfer.E2 α f) (Work.Spaces.Dz f)
      (Q0Sm_E2_O α hα hα1 hf n hn) hqdz (HkMem_E2_O α hα hα1 hf n hn) hdz⟩

end Work.FTS.StrongEps.EpsE4Thr.TransO
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsRLX.DeltaData =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `EpsRLX/DeltaData.lean` — the Lipschitz data of the profile map `u ↦ W_u = P₀(J_ε u)`

This module proves `Work.FTS.StrongEps.EpsRLX.DeltaData`: for a smooth kernel `ρ` there is a
constant `C > 0` (independent of `α ∈ (0,1]`, `ε ∈ (0,1]`, of `C₀`, `B` and of the two data) such
that for any two admissible profiles `u`, `v` (i.e. `ProfileData α C₀ B ε ρ u` and
`ProfileData α C₀ B ε ρ v`) the difference `W_u - W_v` of the projected-mollified profiles

* is again of class `ClassC α`,
* lies in the weighted space `X` of the scheme (`EpsMem`),
* is controlled in `X` (`EpsSq`) and in `ℋ⁵` (`HkNorm`) by the `X`-size of the *difference* of the
  two data, with the loss `C(C/ε)¹²` (the `ε`-cost of the six derivatives spent by
  `HkSq_JepsPz_le`).

The mathematical content is the additivity of the two structure maps `J_ε` and `P₀`:
`J_ε` is additive on the open-quadrant class (`JepsSubApply`, for which the key point is that
outside the open quadrant all three occurrences of `Jeps` vanish), and `P₀` is affine
(`Pz_sub_eq`), `L₁₂` being additive on the honest `ℋ⁴`-class (`L12_sub_HkMem`).  Hence

`W_u - W_v = Pz(J_ε u) - Pz(J_ε v) = Pz(J_ε (u - v)) = W_{u-v}`

as *functions*, so both the `X`- and the `ℋ⁵`-sizes of the difference can be read off from the
single-datum bounds `EpsSq_Pz_sub_le` + `EpsSq_mixed_Jeps_le` (for `EpsSq`) and
`HkSq_JepsPz_le` (for `ℋ⁵`).
-/

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Additivity of `J_ε` -/

/-- **`J_ε` is additive in its argument** on the open-quadrant class: the mollification of a
difference is the difference of the mollifications.  On the open quadrant this is the linearity of
the Bochner integral (`JepsSubApply`); off the open quadrant all three occurrences of `Jeps`
vanish by definition. -/
theorem Jeps_sub_eq {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {u v : Fn} (hu : Work.FTS.EllipticEst.SmoothOpen u)
    (hv : Work.FTS.EllipticEst.SmoothOpen v) :
    Work.FTS.StrongEps.Jeps ρ ε u - Work.FTS.StrongEps.Jeps ρ ε v
      = Work.FTS.StrongEps.Jeps ρ ε (fun z θ => u z θ - v z θ) := by
  funext z θ
  by_cases h : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
  · exact JepsSubApply ρ hρ hε ((hu.forall 0).continuousOn) ((hv.forall 0).continuousOn)
      h.1 h.2
  · show Work.FTS.StrongEps.Jeps ρ ε u z θ - Work.FTS.StrongEps.Jeps ρ ε v z θ = _
    rw [Work.FTS.StrongEps.Jeps, Work.FTS.StrongEps.Jeps, Work.FTS.StrongEps.Jeps,
      ite_eq_right h, ite_eq_right h, ite_eq_right h]
    ring

/-! ## Additivity of the projection `P₀` -/

/-- **`P₀` is affine**: `Pz f - Pz g = Pz (f - g)` as soon as `L₁₂` splits on the pair `(f,g)`. -/
theorem Pz_sub_eq {f g : Fn}
    (h : Work.Construction.L12 (fun z θ => f z θ - g z θ) 0
        = Work.Construction.L12 f 0 - Work.Construction.L12 g 0) :
    Work.FTS.StrongEps.Pz f - Work.FTS.StrongEps.Pz g
      = Work.FTS.StrongEps.Pz (fun z θ => f z θ - g z θ) := by
  funext z θ
  show Work.FTS.StrongEps.Pz f z θ - Work.FTS.StrongEps.Pz g z θ
      = Work.FTS.StrongEps.Pz (fun z θ => f z θ - g z θ) z θ
  rw [Work.FTS.StrongEps.Pz_apply, Work.FTS.StrongEps.Pz_apply,
    Work.FTS.StrongEps.Pz_apply, h]
  ring

/-! ## The difference of two projected-mollified profiles -/

/-- **The key structural identity of the module**: the difference of the two projected-mollified
profiles is the projected-mollified profile of the difference.  This is the combination of
`Jeps_sub_eq` with the affinity of `P₀` (`Pz_sub_eq`), the `L₁₂`-additivity hypothesis of the
latter being supplied by `L12_sub_HkMem` (which needs the honest `ℋ⁴`-size of both mollified
data, available from `HkMem_Jeps`). -/
theorem Wp_sub_eq {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε) {u v : Fn}
    (hu : Work.FTS.EllipticEst.SmoothOpen u) (hv : Work.FTS.EllipticEst.SmoothOpen v)
    (hmu : Work.Spaces.HkMem α 6 u) (hmv : Work.Spaces.HkMem α 6 v) :
    Work.FTS.StrongEps.EpsRLX.Wp ρ ε u - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v
      = Work.FTS.StrongEps.EpsRLX.Wp ρ ε (fun z θ => u z θ - v z θ) := by
  have huc : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall u).mp hu
  have hvc : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall v).mp hv
  have hsmu : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε u) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε huc
  have hsmv : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε v) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hvc
  have hmemu : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε u) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε huc
      (Work.FTS.OpenPkg.HkMem_mono_open hu 4 (by norm_num) hmu)
  have hmemv : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε v) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε hvc
      (Work.FTS.OpenPkg.HkMem_mono_open hv 4 (by norm_num) hmv)
  have hL : Work.Construction.L12
        (fun z θ => Work.FTS.StrongEps.Jeps ρ ε u z θ - Work.FTS.StrongEps.Jeps ρ ε v z θ) 0
      = Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε u) 0
        - Work.Construction.L12 (Work.FTS.StrongEps.Jeps ρ ε v) 0 :=
    Work.FTS.StrongEps.EComparison.L12_sub_HkMem hsmu hsmv hmemu hmemv 0
      (Set.mem_Ici.mpr le_rfl)
  have hJ : Work.FTS.StrongEps.Jeps ρ ε u - Work.FTS.StrongEps.Jeps ρ ε v
      = Work.FTS.StrongEps.Jeps ρ ε (fun z θ => u z θ - v z θ) :=
    Jeps_sub_eq hρ.moll hε hu hv
  show Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)
      - Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε v)
      = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (fun z θ => u z θ - v z θ))
  calc Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε u)
        - Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε v)
      = Work.FTS.StrongEps.Pz
          (fun z θ => Work.FTS.StrongEps.Jeps ρ ε u z θ
            - Work.FTS.StrongEps.Jeps ρ ε v z θ) := Pz_sub_eq hL
    _ = Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (fun z θ => u z θ - v z θ)) := by
        rw [show (fun z θ => Work.FTS.StrongEps.Jeps ρ ε u z θ
              - Work.FTS.StrongEps.Jeps ρ ε v z θ)
            = Work.FTS.StrongEps.Jeps ρ ε (fun z θ => u z θ - v z θ) from hJ]

/-! ## Two elementary arithmetic lemmas for the constant chase -/

/-- `a * s ≤ C (C/ε)¹² s` for `a ≤ C`, `C ≥ 1`, `ε ∈ (0,1]`, `s ≥ 0`. -/
private lemma mul_le_C_pow {a C ε s : ℝ} (ha : a ≤ C) (hC1 : 1 ≤ C) (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (hs : 0 ≤ s) : a * s ≤ C * (C / ε) ^ 12 * s := by
  have hbase1 : 1 ≤ C / ε := by
    rw [le_div_iff₀ hε0]
    linarith
  have hpow : 1 ≤ (C / ε) ^ 12 := one_le_pow₀ hbase1
  have hCnn : 0 ≤ C := le_trans zero_le_one hC1
  calc a * s ≤ C * s := mul_le_mul_of_nonneg_right ha hs
    _ ≤ C * ((C / ε) ^ 12 * s) :=
        mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hs hpow) hCnn
    _ = C * (C / ε) ^ 12 * s := by ring

/-- `a (a/ε)^k s ≤ C (C/ε)¹² s` for `0 ≤ a ≤ C`, `C ≥ 1`, `ε ∈ (0,1]`, `s ≥ 0`, `k ≤ 12`. -/
private lemma mul_pow_le_pow {a C ε s : ℝ} (ha : a ≤ C) (ha0 : 0 ≤ a) (hC1 : 1 ≤ C)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hs : 0 ≤ s) {k : ℕ} (hk : k ≤ 12) :
    a * (a / ε) ^ k * s ≤ C * (C / ε) ^ 12 * s := by
  have hbase : a / ε ≤ C / ε := div_le_div_of_nonneg_right ha hε0.le
  have hbase1 : 1 ≤ C / ε := by
    rw [le_div_iff₀ hε0]
    linarith
  have hCnn : 0 ≤ C := le_trans zero_le_one hC1
  have hae : 0 ≤ a / ε := div_nonneg ha0 hε0.le
  have hpow : (a / ε) ^ k ≤ (C / ε) ^ 12 :=
    le_trans (pow_le_pow_left₀ hae hbase k) (pow_le_pow_right₀ hbase1 hk)
  calc a * (a / ε) ^ k * s ≤ C * (C / ε) ^ 12 * s :=
    mul_le_mul_of_nonneg_right (mul_le_mul ha hpow (pow_nonneg hae k) hCnn) hs

/-! ## The target -/

theorem DeltaData {α C₀ B ε : ℝ} {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hα : α ∈ Set.Ioc 0 1) (hε : ε ∈ Set.Ioc 0 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ {u v : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.EpsRLX.ProfileData α C₀ B ε ρ u →
      Work.FTS.StrongEps.EpsRLX.ProfileData α C₀ B ε ρ v →
      Work.FTS.ClassC.ClassC α (fun z θ =>
        Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ) ∧
      Work.FTS.StrongEps.EpsMem α (fun z θ =>
        Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ) ∧
      Work.FTS.StrongEps.EpsSq α (fun z θ =>
          Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ)
        ≤ C * (C / ε) ^ 12 * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ) ∧
      (Work.Spaces.HkNorm α 5 (fun z θ =>
          Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ)) ^ 2
        ≤ C * (C / ε) ^ 12 * Work.FTS.StrongEps.EpsSq α (fun z θ => u z θ - v z θ) := by
  -- the four constants furnished by the library
  obtain ⟨CH, hCHpos, hCH⟩ := Work.FTS.StrongEps.EpsSqTools.HkSq_JepsPz_le ρ hρ
  obtain ⟨CP, hCPpos, hCP⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSq_Pz_sub_le
  obtain ⟨CS, hCSpos, hCS⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSq_mixed_Jeps_le ρ hρ
  obtain ⟨CM, hCMpos, hCM⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSqIter_mixed_Jeps_le6 ρ hρ
  obtain ⟨CE, hCEpos, hCE⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSq_le_HkSq_ClassC
  obtain ⟨_, _, hPF⟩ := Work.FTS.StrongEps.EpsRLX.ProfileFacts ρ hρ
  have hα0 : 0 < α := hα.1
  have hε0 : 0 < ε := hε.1
  have hε1 : ε ≤ 1 := hε.2
  -- the final constant
  set C : ℝ := max 1 (max (CP * CS) CH) with hCdef
  have hC1 : 1 ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hCPCS : CP * CS ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCHle : CH ≤ C := by
    rw [hCdef]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨C, hCpos, ?_⟩
  intro u v hdu hdv
  -- the difference datum
  set hd : Fn := fun z θ => u z θ - v z θ
  -- the two data lie in `X`
  have hmem_u : Work.FTS.StrongEps.EpsMem α u := (hPF α hα ε hε hdu).1
  have hmem_v : Work.FTS.StrongEps.EpsMem α v := (hPF α hα ε hε hdv).1
  -- a.e. strong measurability of the two data
  have hak_u : Work.FTS.StrongEps.EpsSqTools.AK α u :=
    Work.FTS.StrongEps.EpsSqTools.AK_of_uncurry
      (Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry u)
        ((hdu.smo.forall 0).continuousOn))
  have hak_v : Work.FTS.StrongEps.EpsSqTools.AK α v :=
    Work.FTS.StrongEps.EpsSqTools.AK_of_uncurry
      (Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry v)
        ((hdv.smo.forall 0).continuousOn))
  -- the difference datum lies in `X` and is smooth on the open quadrant
  have hmem_h : Work.FTS.StrongEps.EpsMem α hd :=
    Work.FTS.StrongEps.EpsSqTools.EpsMem_sub hak_u hak_v hmem_u hmem_v
  have hsm_h : Work.FTS.EllipticEst.SmoothOpen hd :=
    Work.FTS.StrongEps.EpsSqTools.smoothOpen_subP hdu.smo hdv.smo
  -- the `∀n`-form of the three smoothness hypotheses
  have huc : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall u).mp hdu.smo
  have hvc : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall v).mp hdv.smo
  have hhc : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry hd) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall hd).mp hsm_h
  -- the mollified data
  have hJu_sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε u) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε0 huc
  have hJv_sm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε v) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε0 hvc
  have hJu_mem4 : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε u) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε0 huc
      (Work.FTS.OpenPkg.HkMem_mono_open hdu.smo 4 (by norm_num) hdu.hkmem)
  have hJv_mem4 : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε v) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε0 hvc
      (Work.FTS.OpenPkg.HkMem_mono_open hdv.smo 4 (by norm_num) hdv.hkmem)
  have hJu_mem : Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Jeps ρ ε u) :=
    (hCM α hα ε hε0 hε1 u huc hmem_u).1
  have hJv_mem : Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Jeps ρ ε v) :=
    (hCM α hα ε hε0 hε1 v hvc hmem_v).1
  have hJh_mem : Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Jeps ρ ε hd) :=
    (hCM α hα ε hε0 hε1 hd hhc hmem_h).1
  have hak_Ju : Work.FTS.StrongEps.EpsSqTools.AK α (Work.FTS.StrongEps.Jeps ρ ε u) :=
    Work.FTS.StrongEps.EpsSqTools.AK_of_uncurry
      (Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry (Work.FTS.StrongEps.Jeps ρ ε u))
        ((hJu_sm.forall 0).continuousOn))
  have hak_Jv : Work.FTS.StrongEps.EpsSqTools.AK α (Work.FTS.StrongEps.Jeps ρ ε v) :=
    Work.FTS.StrongEps.EpsSqTools.AK_of_uncurry
      (Work.Spaces.aesm_of_continuousOn_Qd (Function.uncurry (Work.FTS.StrongEps.Jeps ρ ε v))
        ((hJv_sm.forall 0).continuousOn))
  have hsub_mem : Work.FTS.StrongEps.EpsMem α
      (fun z θ => Work.FTS.StrongEps.Jeps ρ ε u z θ - Work.FTS.StrongEps.Jeps ρ ε v z θ) :=
    Work.FTS.StrongEps.EpsSqTools.EpsMem_sub hak_Ju hak_Jv hJu_mem hJv_mem
  -- the class and the `X`-membership of the difference of the profiles
  have hCsub : Work.FTS.ClassC.ClassC α (fun z θ =>
      Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ) :=
    Work.FTS.StrongEps.EComparison.classC_sub hdu.cls hdv.cls
  have hmemC : Work.FTS.StrongEps.EpsMem α (fun z θ =>
      Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ) :=
    (hCE α hα (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
      - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ) hCsub).1
  -- the mollifier identity and the `X`-bound for the mollified difference
  have hJsub : Work.FTS.StrongEps.Jeps ρ ε u - Work.FTS.StrongEps.Jeps ρ ε v
      = Work.FTS.StrongEps.Jeps ρ ε hd :=
    Jeps_sub_eq hρ.moll hε0 hdu.smo hdv.smo
  have hsqJ : Work.FTS.StrongEps.EpsSq α
        (fun z θ => Work.FTS.StrongEps.Jeps ρ ε u z θ - Work.FTS.StrongEps.Jeps ρ ε v z θ)
      = Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε hd) :=
    Work.FTS.StrongEps.EpsSq_congr (fun z θ => congrFun (congrFun hJsub z) θ)
  have hJsq : Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε hd)
      ≤ CS * Work.FTS.StrongEps.EpsSq α hd := by
    have h := hCS α hα ε hε hd hhc hmem_h 0 0 (by norm_num)
    rw [show Work.Spaces.mixed 0 0 (Work.FTS.StrongEps.Jeps ρ ε hd)
          = Work.FTS.StrongEps.Jeps ρ ε hd from rfl,
      show (2 : ℕ) * (0 + 0) = 0 from rfl, pow_zero, mul_one] at h
    exact h
  -- the projection bound
  have hPzsq : Work.FTS.StrongEps.EpsSq α
        (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
          - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ)
      ≤ CP * Work.FTS.StrongEps.EpsSq α
        (fun z θ => Work.FTS.StrongEps.Jeps ρ ε u z θ
          - Work.FTS.StrongEps.Jeps ρ ε v z θ) :=
    (hCP α hα (Work.FTS.StrongEps.Jeps ρ ε u) (Work.FTS.StrongEps.Jeps ρ ε v)
      hJu_sm hJv_sm hJu_mem4 hJv_mem4 hsub_mem).2
  -- the projected-mollified difference identity
  have hid : (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
        - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ)
      = Work.FTS.StrongEps.EpsRLX.Wp ρ ε hd :=
    Wp_sub_eq hα hρ hε0 hdu.smo hdv.smo hdu.hkmem hdv.hkmem
  refine ⟨hCsub, hmemC, ?_, ?_⟩
  · calc Work.FTS.StrongEps.EpsSq α (fun z θ => Work.FTS.StrongEps.EpsRLX.Wp ρ ε u z θ
          - Work.FTS.StrongEps.EpsRLX.Wp ρ ε v z θ)
        ≤ CP * Work.FTS.StrongEps.EpsSq α
            (fun z θ => Work.FTS.StrongEps.Jeps ρ ε u z θ
              - Work.FTS.StrongEps.Jeps ρ ε v z θ) := hPzsq
      _ = CP * Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Jeps ρ ε hd) := by rw [hsqJ]
      _ ≤ CP * (CS * Work.FTS.StrongEps.EpsSq α hd) :=
          mul_le_mul_of_nonneg_left hJsq hCPpos.le
      _ = (CP * CS) * Work.FTS.StrongEps.EpsSq α hd := by ring
      _ ≤ C * (C / ε) ^ 12 * Work.FTS.StrongEps.EpsSq α hd :=
          mul_le_C_pow hCPCS hC1 hε0 hε1 (Work.FTS.StrongEps.EpsSq_nonneg α hd)
  · have h := hCH α hα ε hε0 hε1 5 (by norm_num) hd hsm_h hmem_h
    rw [hid]
    rw [Work.Spaces.HkNorm,
      Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 5 (Work.FTS.StrongEps.EpsRLX.Wp ρ ε hd))]
    exact le_trans h (mul_pow_le_pow hCHle hCHpos.le hC1 hε0 hε1
      (Work.FTS.StrongEps.EpsSq_nonneg α hd) (by norm_num))

end Work.FTS.StrongEps.EpsRLX
end
