import ChallengeDeps
import Submission.Work.BoseRowsL.Regime.a16_threshold
import Submission.Work.BoseRowsL.Tails.tailFields
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsL.Exists` — `exists_honestInterfaceL`

The decay-free honest interface `Work.BoseRowsL.HonestInterfaceL` is **inhabited** at every
admissible potential (`v ≥ 0`, radial, `tsupport v ⊆ ball 0 R`, `0 < a v`).

| field | source |
|---|---|
| `Cw`, `Cw_nonneg` | `Cw = 16π` |
| `bndW` | `Work.BoseB7AK.W1rows.W1hat_abs_le` (`Work.BoseRowsL.bndW_data`) |
| `lipW` | `Work.BoseGateFS.chat_W1fun_lipschitz` (`Work.BoseRowsL.lipW_data`) |
| `Ng'`, `Ng'_ge`, `cutR`, `tailL`, `tailC` | `Work.BoseRowsL.Tails.tailFields` |
| `fsp` | `Work.BoseBoxFock.nonempty_fsParamsView_HonestBoxFam` |
| `fspKz` | `Work.BoseFixR.FSParamsView_KzEnvAt` + `AdmRho` |
| `rkh` | `Work.BoseRowsL.Regime.rkh_threshold` |
| `a16` | `Work.BoseRowsL.Regime.a16_threshold` |

The bundle `hthr` is `Work.BoseGateFS.exists_gateThresholds`'s output **shrunk**
(`GateThresholds.mono`) to `min (min hthr₀.εg (min ε_r ε_a)) (1/2)^400`, where `ε_r`, `ε_a` are
the thresholds of the two delegated régime rows; shrinking keeps every field of `hthr₀`.

The four régime rows are stated **without** the cut hypothesis `∀ μ, Ng μ ≤ (HM μ).N` that
`GateThresholds`'s fields carry (that is their design shape): `rkh` and `a16` are therefore proved
from the *closed monomial forms* of the honest parameters rather than from `GateThresholds.dil`,
and `fsp`/`fspKz` are cut-independent as well.
-/

noncomputable section

open scoped Real BigOperators Topology
open MeasureTheory Metric

namespace Work.BoseRowsL

open Work.BoseB7 Work.BoseB7A
open Work.BoseFixR Work.BoseBoxFock Work.BoseBoxFix Work.UBB Work.BoseRowsFS
open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The interface is inhabited** at every admissible `v`. -/
theorem exists_honestInterfaceL {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} (R : ℝ) (hR : 0 < R) (hav : 0 < _root_.BoseGases.a v)
    (hv_nonneg : ∀ x : ℝ³, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R) :
    ∃ hthr : Work.BoseGateFS.GateThresholds v h fc fu R, Nonempty (HonestInterfaceL R hthr) := by
  obtain ⟨hthr₀⟩ := Work.BoseGateFS.exists_gateThresholds (v := v) (h := h) fc fu hav R
  obtain ⟨εr, hεrpos, hrkh⟩ :=
    Work.BoseRowsL.Regime.rkh_threshold (v := v) (h := h) (fc := fc) (fu := fu)
      R hR hav hv_nonneg hvrad hv_supp
  obtain ⟨εa, hεapos, ha16⟩ :=
    Work.BoseRowsL.Regime.a16_threshold (v := v) (h := h) (fc := fc) (fu := fu) R hav
  set εg : ℝ := min (min hthr₀.εg (min εr εa)) ((1 / 2 : ℝ) ^ (400 : ℕ)) with hεgdef
  have hεgpos : 0 < εg := by
    rw [hεgdef]
    exact lt_min (lt_min hthr₀.pos (lt_min hεrpos hεapos))
      (pow_pos (by norm_num : (0 : ℝ) < 1 / 2) 400)
  have hεg₀ : εg ≤ hthr₀.εg := by
    rw [hεgdef]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  set hthr : Work.BoseGateFS.GateThresholds v h fc fu R :=
    hthr₀.mono hεgpos hεg₀ with hthrdef
  -- the two UV-tail fields (the tower `Ng'` of `tailFields`)
  obtain ⟨Ng', hge, hcutR, htailL, htailC⟩ :=
    Work.BoseRowsL.Tails.tailFields (v := v) (h := h) (fc := fc) (fu := fu)
      R hR hav hv_nonneg hvrad hv_supp hthr (16 * Real.pi) (by positivity)
  have hεg_eq : hthr.εg = εg := rfl
  have hεg_le_r : εg ≤ εr := by
    rw [hεgdef]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεg_le_a : εg ≤ εa := by
    rw [hεgdef]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hεg_le_1 : εg ≤ 1 := by
    rw [hεgdef]
    refine le_trans (min_le_right _ _) ?_
    have h2 : (1 / 2 : ℝ) ^ (400 : ℕ) ≤ (1 : ℝ) ^ (400 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) 400
    simpa using h2
  have hεr' : ∀ μ : ℝ, μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
      μ * _root_.BoseGases.a v ^ 3 ≤ εr := fun μ h => le_trans (hεg_eq ▸ h) hεg_le_r
  have hεa' : ∀ μ : ℝ, μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
      μ * _root_.BoseGases.a v ^ 3 ≤ εa := fun μ h => le_trans (hεg_eq ▸ h) hεg_le_a
  have hε1 : ∀ μ : ℝ, μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
      μ * _root_.BoseGases.a v ^ 3 ≤ 1 := fun μ h => le_trans (hεg_eq ▸ h) hεg_le_1
  have hfsp : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
      μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
      Work.BoseB7.FSParamsView (honE v h fc fu HM μ) := by
    intro HM μ hμ hdil
    exact (Work.BoseBoxFock.nonempty_fsParamsView_HonestBoxFam (HM := HM) hμ hav
      (hε1 μ hdil)).some
  have hfspKz : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ ρ : ℝ), 0 < μ →
      μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
      Work.BoseGateFS.AdmRho (honE v h fc fu HM μ) ρ →
      Work.BoseB7.FSParamsView (Work.BoseFixR.KzEnvAt (honE v h fc fu HM μ) ρ) := by
    intro HM μ ρ hμ hdil hadm
    have hvE : Work.BoseB7.FSParamsView (honE v h fc fu HM μ) :=
      (Work.BoseBoxFock.nonempty_fsParamsView_HonestBoxFam (HM := HM) hμ hav
        (hε1 μ hdil)).some
    have hell : (honE v h fc fu HM μ).ell ≠ 0 := ne_of_gt (Work.BoseB7.ell_pos _ hvE)
    have hmu : (honE v h fc fu HM μ).mu = μ := rfl
    have hρpos : 0 < ρ := by
      have h2 := hadm.2.1
      rw [hmu] at h2
      linarith
    have hclose : |ρ - (honE v h fc fu HM μ).mu| ≤ (honE v h fc fu HM μ).mu / 2 := by
      rw [hmu, abs_le]
      exact ⟨by linarith [hadm.2.1, hadm.2.2], by linarith [hadm.2.2]⟩
    exact (Work.BoseFixR.FSParamsView_KzEnvAt hvE hρpos hell hclose).some
  have hrkhF : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
      μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
      (R / (honE v h fc fu HM μ).ell) ^ 2 ≤ (honE v h fc fu HM μ).KH⁻¹ :=
    fun HM μ hμ hdil => hrkh HM μ hμ (hεr' μ hdil)
  have ha16F : ∀ (HM : ∀ μ : ℝ, HonestModes v μ) (μ : ℝ), 0 < μ →
      μ * _root_.BoseGases.a v ^ 3 ≤ hthr.εg →
      (honE v h fc fu HM μ).aScat * (honE v h fc fu HM μ).KH
        / ((honE v h fc fu HM μ).s * (honE v h fc fu HM μ).ell) ≤ 1 / 16 :=
    fun HM μ hμ hdil => ha16 HM μ hμ (hεa' μ hdil)
  have hinst : HonestInterfaceL R hthr :=
    { Cw := 16 * Real.pi
      Cw_nonneg := by positivity
      bndW := bndW_data (v := v) (h := h) (R := R) hR hav hv_nonneg hvrad hv_supp
      lipW := lipW_data (v := v) (h := h) (R := R) hR hav hv_nonneg hvrad hv_supp
      Ng' := Ng'
      Ng'_ge := hge
      cutR := hcutR
      tailL := htailL
      tailC := htailC
      fsp := hfsp
      fspKz := hfspKz
      rkh := hrkhF
      a16 := ha16F }
  exact ⟨hthr, ⟨hinst⟩⟩

end Work.BoseRowsL
