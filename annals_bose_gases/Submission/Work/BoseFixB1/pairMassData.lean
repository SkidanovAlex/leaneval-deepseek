import ChallengeDeps
import Submission.Work.BoseFixB1.CrossWordsDefs
import Submission.Work.BoseFixB1S.mfM2_sub_mfM1_ge_const_mul_mfM1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.pairMassData` — the localised pair-mass excess at the sliding box

`Work.BoseFixB1S.mfM2M1_key` states, for the sliding box `B(u) = dlBox ℓ d u`, every `ℓ > 0`,
`d > 0`, every `M ≥ 1` and **without any small-range hypothesis on `v`**,

    (a v)/(2R)·boxM1 ℓ A w₁  ≤  boxM2 V A w₂ − boxM1 ℓ A w₁ ,

i.e. `M₂ ≥ (1 + a(v)/(2R))·M₁`.  Specialising to FS's parameters (`ℓ = PBℓ v μ`, `d = PBd v μ`,
`M = PBM v μ = 48`) and discharging `0 < ℓ`, `0 < d`, `1 ≤ M` from `Adm` gives
`Work.BoseFixB1.PairMassData v h 1 (a v/(2R))` — the pair-mass payer of the condensed
per-sector bound (see `FINDING_perSectorBoundG_condensed.md` §2). -/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.FockBridge
open Work.BoseFixB1B

set_option autoImplicit false
set_option linter.unusedVariables false

theorem pairMassData {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ γ₀ : ℝ, PairMassData v h ε₀ γ₀ := by
  refine ⟨1, _root_.BoseGases.a v / (2 * R), one_pos, ?_, ?_⟩
  · exact div_pos hav (by linarith)
  · intro μ hAdm u _hvol
    have hM : 1 ≤ PBM v μ := by
      simp [PBM, Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]
    have hex := Work.BoseFixB1S.mfM2M1_key (v := v) (R := R) hv_supp hR hv hvrad hv1 h hav
      (M' := PBM v μ) hM (ℓ := PBℓ v μ) (d := PBd v μ) (adm_ell_pos hAdm) (adm_d_pos hAdm) u
    simp only [PBℓ, PBd, PBM, PBB, div_eq_mul_inv, one_add_mul] at hex ⊢
    linarith [hex]

end Work.BoseFixB1
