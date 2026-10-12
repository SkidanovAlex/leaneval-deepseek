import ChallengeDeps
import Submission.Work.BoseRowQ2.RowQ2All_of_coreN
import Submission.Work.BoseRowQ2.rowArith2_honest
import Submission.Work.BoseRowQ2.rowGchiN_honest
import Submission.Work.BoseRowQ2.rowMainN_honest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.rowQ2AllRegimeN_honest` — row 3 at the frozen `NH` (lead's NH ruling)

The **gate's `hrow3All` producer**: `RowQ2AllRegimeN` follows from the `NH`-form core
`RowQ2AllCoreN` (`RowsN.lean`), whose four conjuncts are supplied by

* (C) `rowGchiN_honest` — `GchiAtN` with `κ_lat = RowGchiMaskRowAux.honCutRad v = ℓκ` and an
  absolute `C₁ = 2 C_fc S₁` (`gchiN_oneBody` + `besselOpMat_le_of_mat`),
* (D) `rowArith2_honest` — `ArithAt2` at `ε = fsEps v 58982400` (cloning `RowArith_at_fsEps`),
* `rowMainN_honest` — `MainAtN` at the current `NH`, and
* `RowArith_at_fsEps` — the `ℓ⁻²` arithmetic,

packed at the combined cube size `Ng = max` and threshold `εg' = min` (each row is monotone in the
easy direction: a *larger* `Ng` and a *smaller* `εg` weaken the `∀ HM` / `∀ μ` hypotheses), and
then assembled by the compiled `RowQ2AllRegimeN_of_coreN`.

The only `W1omega0`-input of the assembly is its **nonnegativity**, and the honest row
`honE_W1omega0_row` (`rowMain_honest.lean`) supplies it *together with* the upper bound `16πa v`
inside the régime `μa³ ≤ εg` — which is exactly the régime in which every object of
`RowQ2AllRegimeN` is used.  That is why `RowQ2AllRegimeN_of_coreN`'s `hw0` is stated
régime-conditionally.  (The *unconditional* form `Work.BoseRowQ2.honE_W1omega0_nonneg` is proved
in `honE_W1omega0_nonneg.lean`; it is not needed here.)
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseRowQ2

open Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB
open Work.BoseGateFS

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-- **Row 3 at the frozen `NH`** (lead's NH ruling): the assembly of `RowQ2AllRegimeN` from the
`NH`-form core.  This is the object the gate consumes as `hrow3All` (the caller moves its own
threshold bundle to the produced `εg'` by monotonicity, exactly as for rows 1 and 2). -/
theorem rowQ2AllRegimeN_honest {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R)
    (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (εg : ℝ) (hεg : 0 < εg) (hεg1 : εg ≤ 1)
    (hrég : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      1 ≤ Work.BoseBoxFock.ellH v μ
        ∧ R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0) :
    ∃ Ng : ℝ → ℕ, ∃ εg' : ℝ, 0 < εg' ∧ εg' ≤ εg ∧
      RowQ2AllRegimeN (h := h) (fc := fc) (fu := fu) Ng R εg' := by
  classical
  -- (C): `GchiAtN` with `κ_lat = honCutRad` and `C₁ = 2 C_fc S₁`
  obtain ⟨C₁, hC₁, NgG, hGchi⟩ :=
    rowGchiN_honest (v := v) (h := h) (fc := fc) (fu := fu) R hav
  -- (D): `ArithAt2` at FS's `ε`, for every cube size
  obtain ⟨εgD, hεgD0, hεgDle, hArith2⟩ :=
    rowArith2_honest (v := v) (h := h) (fc := fc) (fu := fu) R hR hav hv_nonneg hvrad hv_supp
      εg hεg hεg1 hrég C₁ hC₁
  -- `MainAtN` at the current `NH`
  obtain ⟨NgM, εgM, hεgM0, hεgMle, hMain⟩ :=
    rowMainN_honest (v := v) (h := h) (fc := fc) (fu := fu) R hR hav hv_nonneg hvrad hv_supp
      εg hεg hεg1 hrég
  -- the `ℓ⁻²` arithmetic, at the strongest cube-size condition (`Ng := 0`)
  have hWrow := honE_W1omega0_row (v := v) (h := h) (fc := fc) (fu := fu) (R := R) (εg := εg)
    hR hav hv_nonneg hvrad hv_supp hrég
  have hArith : RowArith (h := h) (fc := fc) (fu := fu) R εg (fun _ => 0)
      (96 / Real.pi) (fsEps v 58982400) :=
    RowArith_at_fsEps (v := v) (h := h) (fc := fc) (fu := fu) R
      hR hav hv_nonneg hvrad hv_supp εg (fun _ => 0) hεg hεg1 hrég hWrow
  -- the combined cube size and threshold
  have hεg'0 : 0 < min εgD (min εgM εg) := lt_min hεgD0 (lt_min hεgM0 hεg)
  have hεg'le : min εgD (min εgM εg) ≤ εg :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  have hposE : ∀ μ : ℝ, 0 < μ → 0 < fsEps v 58982400 μ := by
    intro μ hμ
    rw [fsEps_eq hμ hav]
    exact mul_pos (by norm_num)
      (Real.rpow_pos_of_pos (mul_pos hμ (pow_pos hav 3)) _)
  have hcore : RowQ2AllCoreN (h := h) (fc := fc) (fu := fu) R εg := by
    refine ⟨fun μ => max (NgG μ) (NgM μ), min εgD (min εgM εg), hεg'0, hεg'le, ?_⟩
    refine ⟨C₁, hC₁, RowGchiMaskRowAux.honCutRad v, fsEps v 58982400, ?_, hposE, ?_, ?_, ?_, ?_⟩
    · intro μ hμ
      exact RowGchiMaskRowAux.honCutRad_pos hav hμ
    · -- `RowArith` (at the outer `εg`, hence the régime `εg` for its own row)
      intro hεg'1 HM _hN μ hμ hμa ρ hρ
      exact hArith hεg1 HM (fun _ => Nat.zero_le _) μ hμ (le_trans hμa hεg'le) ρ hρ
    · -- `RowArith2` (at its own threshold `εgD`)
      intro hεg'1 HM hN μ hμ hμa ρ hρ
      exact hArith2 (fun ν => max (NgG ν) (NgM ν)) (le_trans hεgDle hεg1) HM hN μ hμ
        (le_trans hμa (min_le_left _ _)) ρ hρ
    · -- `RowGchiN` at the combined cube size and threshold `εg'`
      intro hεg'1 HM hN μ hμ hμa ρ hρ
      exact hGchi (min εgD (min εgM εg)) (fsEps v 58982400) hposE hεg'1 HM
        (fun ν => le_trans (le_max_left _ _) (hN ν)) μ hμ hμa ρ hρ
    · -- `RowMainN` (at its own threshold `εgM` and cube size `NgM`)
      intro hεg'1 HM hN μ hμ hμa ρ hρ
      exact hMain (le_trans hεgMle hεg1) HM
        (fun ν => le_trans (le_max_right _ _) (hN ν)) μ hμ
        (le_trans hμa (le_trans (min_le_right _ _) (min_le_left _ _))) ρ hρ
  exact RowQ2AllRegimeN_of_coreN (h := h) (fc := fc) (fu := fu) (R := R) (εg := εg) hεg1 hav
    (fun HM μ hμ hμa => (hWrow HM μ hμ hμa).1) hcore

end Work.BoseRowQ2
