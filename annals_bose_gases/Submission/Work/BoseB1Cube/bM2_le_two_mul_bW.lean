import ChallengeDeps
import Submission.Work.BoseFixB1.boxSlack_le_pcBlock
import Submission.Work.BoseFixB1S.flatBranchB1_boxConstant
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.bM2_le_two_mul_bW` — the mass sandwich `M₂ ≤ 2 W` at the sliding box

    ∃ ε₀ > 0, ∀ μ, Adm v ε₀ μ → ∀ u, bM2 v h μ u ≤ 2 · bW v h μ u .

This is the *integral form of FS's `g₂ ≤ 2 g₀`*, i.e. of `0 ≤ ω₀ ≤ 1`: written out,
`bM2 = ∬_{B(u)×B(u)}w₂` and `bW = bM1 = ∬_{B(u)×B(u)}w_{1,B(u)}`, and the two kernels differ by the
`ω`-factor (they are the `w₂ = (1+ω₀)w₁` pair).  Equivalently it is the upper half of the sandwich
`0 ≤ MΔ ≤ M₁` (`Submission/Work/BoseB1Cube/boxMDeltaLeBW.lean`, `MΔ = bM2 − bM1`), which is what
the localized ledgers need when they take the free slot `G` at `MΔ`.

## Proof (a two-lemma assembly, no new mathematics)

Both ingredients are already proved in the corpus, at exactly these parameters, and are
*state-independent* (they hold for every `u`, in particular on the corner/shell configurations
where `M₂ = M₁ = 0`):

* `Work.BoseFixB1.boxM2_le_two_mul_boxM1` — `boxM2 ≤ 2 · boxM1` at the sliding box, from the
  pointwise `w₂ ≤ 2 w₁` (`w₂ = (1+ω₀)w₁` with `0 ≤ ω₀ ≤ 1`) and the pointwise equality of supports;
* the fibre/global bridge `Work.BoseFixB1S.mfW_eq_mfM1` (`bM1 = bW`): `bW` is the *global* nested
  integral `∫∫ w_{1,B(u)}` and `bM1` the *fibre* one, and they agree because the kernel vanishes
  off the box (`wSmallPair_eq_zero_of_notMem_dlBox`).

The only bookkeeping is the diluteness regime: `R ≤ ℓd/16` and `R ≤ ℓ·chiR0` come from
`Work.BoseFixB1.regime_sideAt_ge` at a *smaller* threshold `εr`, which is then merged with the
target's own `ε₀` by `min` (`Adm.mono`), and `1 ≤ M = 48` from `M_eq_mValue`.  This mirrors the
assembly of `boxMDeltaLeBW`, keeping only its upper half.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

theorem bM2_le_two_mul_bW {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3),
        Work.BoseFixB1.bM2 v h μ u ≤ 2 * Work.BoseFixB1.bW v h μ u := by
  -- the diluteness regime at the sliding parameters (`R ≤ ℓd/16`, `R ≤ ℓ·chiR0`)
  obtain ⟨εr, hεr, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨min εr 1, lt_min hεr one_pos, ?_⟩
  intro μ hAdm u
  have hAdmr : Work.BoseBoxFix.Adm v εr μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hεR : μ * (_root_.BoseGases.a v) ^ 3 ≤ εr := hAdmr.2.1
  obtain ⟨hRd, hRχ⟩ := hreg μ hAdmr.1 hεR
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  -- `1 ≤ M = 48` at the internal parameter `μ`
  have hMv : 1 ≤ Work.BoseFixB1.bM v μ := by
    show 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
    rw [Work.BoseFixB1.M_eq_mValue]
    norm_num [Work.BoseBox.mValue]
  -- the kernel-side sandwich `M₂ ≤ 2 M₁`
  have h2 := Work.BoseFixB1.boxM2_le_two_mul_boxM1 (v := v) (R0 := R) hv_supp hR hv hvrad hv1 h
    hMv hℓ hd hRd hRχ u
  -- the fibre/global bridge `M₁ = W`
  have hW : Work.BoseFixB1.bM1 v h μ u = Work.BoseFixB1.bW v h μ u := by
    simp only [Work.BoseFixB1.bM1, Work.BoseFixB1.bW, Work.BoseFixB1.bSide, Work.BoseFixB1.bD,
      Work.BoseFixB1.bA, Work.BoseFixB1.bM]
    exact (Work.BoseFixB1S.mfW_eq_mfM1 (v := v) (h := h) (μ := μ) (u := u) hMv hℓ hd).symm
  -- `h2` is stated at the unfolded `boxM2`/`boxM1`; fold it back to the `bM2`/`bM1` spelling
  have h2' : Work.BoseFixB1.bM2 v h μ u ≤ 2 * Work.BoseFixB1.bM1 v h μ u := h2
  linarith [h2', hW]

end Work.BoseB1Cube
