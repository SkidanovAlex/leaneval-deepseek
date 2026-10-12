import ChallengeDeps
import Submission.Work.BoseFixB1.WB.mass_upper
import Submission.Work.BoseFixB1.regime_sideAt_ge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime`

The **regime-correct** form of the per-`u` mass bound for the localised one-body
kernel `w_{1,B(u)}` (FS `eq:appw1sliding`, sharp form):

    ∃ ε₀ C, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ, Adm v ε₀ μ → ∀ u,
      ∬ w_{1,B(u)} ≤ C · (a v) · chiMass M ℓ d u ,

i.e. the version with the diluteness threshold *existentially quantified*, for
which the pointwise domination is available.  This is the repair of
`Work.BoseFixB1.w1MassB_le_const_mul_chiMass`, which is **false** as stated: see
`FINDING_w1MassB_le_const_mul_chiMass.md` of this chapter.  The pointwise input
`Work.UBBInputs8.A.abs_wSmall1Pair_chiB_le` requires the two regime conditions
`R ≤ ℓ d/16` and `R ≤ ℓ·chiR0` (so that `convScaleSmall` and `convScale ℓ` stay
bounded below on `supp g₀`), which do **not** follow from an arbitrary
diluteness threshold — but *do* follow from one depending on the support radius
`R` (`regime_sideAt_ge`).  That is exactly the shape of the sibling lemma
`Work.BoseFixB1.w1MassB_integral_le` (and of
`Work.BoseFixB1B.w1MassB_integral_le_holds`), and of the shape consumed by
`Work.BoseFixB1.perBoxF_integrated` (`hCw`).

## The proof

* The per-`u` bound **with** the regime hypotheses is already available and
  `sorry`-free as `Work.BoseFixB1.WB.mass_upper`, at every fixed support radius
  `R0` and regularity `M`:

      R0 ≤ ℓ d/16 → R0 ≤ ℓ·chiR0 → ∀ u,
        w1MassB h M ℓ d u ≤ C · (a v) · chiMass M ℓ d u     (0 ≤ C),

  proved there by `abs_wSmall1Pair_chiB_le` + AM–GM + Tonelli and
  `∫|g₀| = 8π (a v)`.
* FS's parameter block has the **fixed** regularity `M = mValue = 48`
  (`M_eq_mValue`), so the constant `C` may be chosen once and for all,
  *outside* the `μ`-quantifier, by invoking `mass_upper` at `M := mValue`.
* The two regime conditions at the FS parameters are produced by
  `regime_sideAt_ge` (with `hav : 0 < a v`): there is `ε₀ > 0` depending only on
  `R` and `a v` with `R ≤ ℓ(μ)·d(μ)/16` and `R ≤ ℓ(μ)·chiR0` whenever
  `0 < μ` and `μ(a v)³ ≤ ε₀`.
* The remaining case `¬ 0 < a v` is **vacuous**: `Adm v ε₀ μ` forces `0 < a v`
  (`adm_a_pos`), so *every* pair `(ε₀, C)` works there.  In particular the
  statement needs no explicit hypothesis `0 < a v` (nor `MemLp v 1`): the
  `a v ≤ 0` branch carries no admissible `μ` at all.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

theorem w1MassB_le_const_mul_chiMass_regime {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3),
      Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      ≤ C * (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u := by
  by_cases hav : 0 < _root_.BoseGases.a v
  · -- ## the `0 < a v` branch: the diluteness threshold of `regime_sideAt_ge`
    obtain ⟨ε₀, hε₀, hreg⟩ := regime_sideAt_ge (v := v) hav hR
    -- the mass bound at the *fixed* regularity `M = mValue`, giving a constant
    -- `C` independent of `μ` (chosen here, outside the `μ`-quantifier)
    obtain ⟨C, hC0, hCb⟩ :=
      Work.BoseFixB1.WB.mass_upper (v := v) (h := h) (R0 := R) (M := Work.BoseBox.mValue)
        hv hvrad hv_supp hR (by norm_num [Work.BoseBox.mValue])
    refine ⟨ε₀, C, hε₀, hC0, ?_⟩
    intro μ hAdm u
    have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := adm_ell_pos hAdm
    have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := adm_d_pos hAdm
    -- the two regime conditions, from the (existential) diluteness threshold
    obtain ⟨hR16, hRχ⟩ := hreg μ (adm_mu_pos hAdm) (adm_dilute hAdm)
    have hkey := hCb (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) hℓ hd hR16 hRχ u
    simpa only [M_eq_mValue] using hkey
  · -- ## the `a v ≤ 0` branch is vacuous: `Adm` forces `0 < a v`
    refine ⟨1, 0, one_pos, le_refl 0, ?_⟩
    intro μ hAdm u
    exact absurd (adm_a_pos hAdm) hav

end Work.BoseFixB1
