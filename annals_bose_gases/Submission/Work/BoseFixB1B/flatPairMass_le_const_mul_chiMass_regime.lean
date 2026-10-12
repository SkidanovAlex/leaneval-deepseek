import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseFixB1.integrable_psiPairKernel
import Submission.Work.BoseFixB1.psiAutocorrIdentity
import Submission.Work.BoseFixB1S.BoxPIndFlat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.flatPairMass_le_const_mul_chiMass_regime`

The **regime-correct** per-`u` upper bound for the localised *pair* mass

    `W₂ = flatPairMass v M ℓ d u = ∬_{ℝ³×ℝ³} wSmallPair M ℓ d u v`

at FS's parameters, in the shape in which the flat ledger consumes it
(`Work.BoseFixB1S.flatLedgerSharpB1`, `Work.BoseFixB1B.flatPair_row`):

    ∃ ε₀ C, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ, Adm v ε₀ μ → ∀ u,
      flatPairMass v M ℓ d u ≤ C · (a v) · chiMass M ℓ d u .

This is the pair-kernel companion of `Work.BoseFixB1.w1MassB_le_const_mul_chiMass_regime`
(proved there with the *sharp* constant `16π/smallConvLower`: the one-body numerator is
`g₀`, whose total mass is exactly `8π(a v)`).  The *pair* numerator is `v` itself, whose
total mass is **not** `8π(a v)`; the honest mass law is `W₂ ≈ 8πβ(a v)·chiMass` with
`β = ∫v/(8π a v) ≥ 1` (`FINDING_flatPair_row_analysis.md` §1), and `β` is a fixed finite
constant of `v` — which is why the bound is stated with an **existential** constant `C`,
allowed to depend on `v` (and `R`), exactly as in the sibling lemma above.

## The proof

The two ingredients are the corpus's pair-mass interface:

* `Work.BoseFixB1.integrable_psiPairKernel` — joint integrability of the lag kernel
  `ψ(x,z) = χ_B(x)·(v z/E z)·χ_B(x−z)`, `E = (χ_M⋆χ_M)(·/(ℓd))·(χ⋆χ)(·/ℓ)`, under the
  renormalisation regime `R ≤ ℓd/16`, `R ≤ ℓ·chiR0` and `v ∈ L¹`;
* `Work.BoseFixB1.psiAutocorrIdentity` — the Fubini/change-of-variable identity

      `flatPairMass v M ℓ d u = ∫_z (v z/E z)·A(z)`,  `A(z) = ∫_x χ_B(x)χ_B(x−z)`,

  i.e. the mass is the *lag*-integral of the renormalised numerator against the
  autocorrelation of the sliding cutoff.

Then everything is elementary:

* `|v z/E z| ≤ (2/smallConvLower M)·|v z|` on the support (the regime makes both
  convolution factors bounded below there, `abs_div_convScaleSmall_mul_convScale_le`);
* `0 ≤ A(z) ≤ chiMass M ℓ d u` for **every** `z`: nonnegativity is pointwise, and the upper
  bound is the arithmetic–geometric mean `χ(x)χ(x−z) ≤ (χ(x)² + χ(x−z)²)/2` integrated
  (translation invariance gives `∫χ(·−z)² = ∫χ²`), i.e. the elementary Cauchy–Schwarz at the
  cutoff;
* whence `W₂ ≤ (2/smallConvLower M)·(∫|v|)·chiMass`.

The diluteness threshold `ε₀` is the one of `Work.BoseFixB1.regime_sideAt_ge` (which makes
`ℓ(μ)d(μ) ≥ 16R` and `ℓ(μ)·chiR0 ≥ R` for all admissible `μ`); the branch `a v ≤ 0` is
vacuous, `Adm` forcing `0 < a v` (`Work.BoseFixB1.adm_a_pos`).

Note: the *pointwise* form (fixed `M`, uniform in `μ`) is `flatPairMass_le_regime` below;
`M` is then set to the constant `mValue = 48` of FS's parameter block
(`Work.BoseFixB1.M_eq_mValue`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

-- NOTE: `ℝ³` is the *global* notation `EuclideanSpace ℝ (Fin 3)` of
-- `Submission/Work/BoseKinLoc/Defs.lean`, already in this file's import cone.

/-- **Nonnegativity of the autocorrelation** of the sliding cutoff,
`A(z) = ∫_x χ_B(x)χ_B(x−z) ≥ 0`. -/
lemma autocorr_nonneg {M : ℕ} {ℓ d : ℝ} (u z : ℝ³) :
    0 ≤ Work.BoseFixB1.autocorr (M := M) ℓ d u z := by
  simp only [Work.BoseFixB1.autocorr_apply]
  exact integral_nonneg (fun x => mul_nonneg
    (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u x)
    (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u (x - z)))

/-- **The autocorrelation of the sliding cutoff is dominated by its `L²`-mass**: for every
lag `z`,

    `A(z) = ∫_x χ_B(x)·χ_B(x−z) ≤ ∫_x χ_B(x)² = chiMass M ℓ d u`.

This is the arithmetic–geometric mean `χ(x)χ(x−z) ≤ (χ(x)² + χ(x−z)²)/2` integrated,
together with the translation invariance of Lebesgue measure
(`∫_x χ(x−z)² = ∫_x χ(x)²`). -/
lemma autocorr_le_chiMass {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u z : ℝ³) :
    Work.BoseFixB1.autocorr (M := M) ℓ d u z ≤ Work.SmallBoxSliding.chiMass M ℓ d u := by
  have hχc : Continuous (fun x : ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u x) :=
    Submission.BoseGases.chiSmallB_continuous hM hℓ hd u
  have hχcs : HasCompactSupport (fun x : ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u x) :=
    Submission.BoseGases.chiSmallB_hasCompactSupport hM hℓ u
  have hχint : MeasureTheory.Integrable
      (fun x : ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u x) :=
    hχc.integrable_of_hasCompactSupport hχcs
  have hχ2int : MeasureTheory.Integrable
      (fun x : ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u x ^ 2) := by
    obtain ⟨B, hB⟩ := hχc.bounded_above_of_compact_support hχcs
    refine (hχint.const_mul B).mono' (hχc.pow 2).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 : Submission.BoseGases.chiSmallB M ℓ d u x ≤ B := by
      have hx := hB x
      rwa [Real.norm_eq_abs,
        abs_of_nonneg (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u x)] at hx
    simpa only [pow_two] using mul_le_mul_of_nonneg_right h1
      (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u x)
  have hχ2intz : MeasureTheory.Integrable
      (fun x : ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u (x - z) ^ 2) :=
    hχ2int.comp_sub_right z
  have hgint : MeasureTheory.Integrable (fun x : ℝ³ =>
      (Submission.BoseGases.chiSmallB M ℓ d u x ^ 2
        + Submission.BoseGases.chiSmallB M ℓ d u (x - z) ^ 2) / 2) :=
    (hχ2int.add hχ2intz).div_const 2
  have hle : Work.BoseFixB1.autocorr (M := M) ℓ d u z
      ≤ ∫ x : ℝ³, (Submission.BoseGases.chiSmallB M ℓ d u x ^ 2
          + Submission.BoseGases.chiSmallB M ℓ d u (x - z) ^ 2) / 2 := by
    simp only [Work.BoseFixB1.autocorr_apply]
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun x => mul_nonneg
        (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u x)
        (Work.SmallBoxSliding.chiSmallB_nonneg M ℓ d u (x - z))))
      hgint (Filter.Eventually.of_forall (fun x => ?_))
    nlinarith [sq_nonneg (Submission.BoseGases.chiSmallB M ℓ d u x
      - Submission.BoseGases.chiSmallB M ℓ d u (x - z))]
  have hval : (∫ x : ℝ³, (Submission.BoseGases.chiSmallB M ℓ d u x ^ 2
        + Submission.BoseGases.chiSmallB M ℓ d u (x - z) ^ 2) / 2)
      = Work.SmallBoxSliding.chiMass M ℓ d u := by
    rw [Work.SmallBoxSliding.chiMass_def]
    rw [show (fun x : ℝ³ => (Submission.BoseGases.chiSmallB M ℓ d u x ^ 2
          + Submission.BoseGases.chiSmallB M ℓ d u (x - z) ^ 2) / 2)
        = (fun x : ℝ³ => (1 / 2) * (Submission.BoseGases.chiSmallB M ℓ d u x ^ 2
          + Submission.BoseGases.chiSmallB M ℓ d u (x - z) ^ 2)) from by
      funext x; ring]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hχ2int hχ2intz,
      MeasureTheory.integral_sub_right_eq_self
        (fun x : ℝ³ => Submission.BoseGases.chiSmallB M ℓ d u x ^ 2) z]
    ring
  exact hle.trans hval.le

/-- **The per-`u` pair-mass bound at fixed parameters** (the pointwise form of the target):
under the renormalisation regime `R₀ ≤ ℓd/16`, `R₀ ≤ ℓ·chiR0` and `v ∈ L¹` with
`tsupport v ⊆ ball 0 R₀`,

    `flatPairMass v M ℓ d u ≤ (2/smallConvLower M)·(∫|v|)·chiMass M ℓ d u`. -/
lemma flatPairMass_le_regime {v : ℝ³ → ℝ} {R0 : ℝ} (hR0 : 0 < R0)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R0) (hv1 : MeasureTheory.MemLp v 1)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ ℓ * Submission.BoseGases.chiR0)
    (u : ℝ³) :
    Work.BoseFixB1.flatPairMass v M ℓ d u
      ≤ (2 / Work.SmallBoxSliding.smallConvLower M) * (∫ z : ℝ³, |v z|)
          * Work.SmallBoxSliding.chiMass M ℓ d u := by
  have hvint : MeasureTheory.Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hfsupp : ∀ z : ℝ³, R0 ≤ ‖z‖ → v z = 0 :=
    fun z hz => Work.SmallBoxSliding.eq_zero_of_tsupport_subset_ball hv_supp hz
  have hs0 : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  -- the joint integrability of the lag kernel and the Fubini identity
  have hIv := Work.BoseFixB1.integrable_psiPairKernel (v := v) (R0 := R0) hR0 hv_supp hv1
    hM hℓ hd hR16 hRχ u
  have hid := Work.BoseFixB1.psiAutocorrIdentity (f := v) (M := M) (ℓ := ℓ) (d := d) u hIv
  -- abbreviations
  set q : ℝ³ → ℝ := fun z => v z / (Submission.BoseGases.convScaleSmall M (ℓ * d) z
      * Submission.BoseGases.convScale ℓ z) with hq
  set A : ℝ³ → ℝ := fun z => Work.BoseFixB1.autocorr (M := M) ℓ d u z with hA
  have hfp : Work.BoseFixB1.flatPairMass v M ℓ d u = ∫ z : ℝ³, q z * A z := by
    rw [Work.BoseFixB1.flatPairMass]
    simp only [hq, hA]
    exact hid
  rw [hfp]
  -- pointwise bounds
  have hqbound : ∀ z : ℝ³, |q z| ≤ (2 / Work.SmallBoxSliding.smallConvLower M) * |v z| := by
    intro z
    simp only [hq]
    exact Work.BoseFixB1.abs_div_convScaleSmall_mul_convScale_le hM hℓ hd hR16 hRχ hfsupp z
  have hAbound : ∀ z : ℝ³, A z ≤ Work.SmallBoxSliding.chiMass M ℓ d u := by
    intro z
    simp only [hA]
    exact autocorr_le_chiMass hM hℓ hd u z
  have hA0 : ∀ z : ℝ³, 0 ≤ A z := by
    intro z
    simp only [hA]
    exact autocorr_nonneg u z
  -- the dominating function is integrable
  have hgint : MeasureTheory.Integrable (fun z : ℝ³ =>
      (2 / Work.SmallBoxSliding.smallConvLower M) * |v z|
        * Work.SmallBoxSliding.chiMass M ℓ d u) :=
    (hvint.abs.const_mul _).mul_const _
  -- the integral bound
  have h1 : |∫ z : ℝ³, q z * A z| ≤ ∫ z : ℝ³,
      (2 / Work.SmallBoxSliding.smallConvLower M) * |v z|
        * Work.SmallBoxSliding.chiMass M ℓ d u := by
    refine le_trans (by
      simpa only [Real.norm_eq_abs] using
        MeasureTheory.norm_integral_le_integral_norm
          (μ := (volume : Measure ℝ³)) (fun z : ℝ³ => q z * A z)) ?_
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun z => abs_nonneg _)) hgint
      (Filter.Eventually.of_forall (fun z => ?_))
    dsimp only
    rw [abs_mul, abs_of_nonneg (hA0 z)]
    calc |q z| * A z
        ≤ ((2 / Work.SmallBoxSliding.smallConvLower M) * |v z|)
            * Work.SmallBoxSliding.chiMass M ℓ d u :=
          mul_le_mul (hqbound z) (hAbound z) (hA0 z)
            (mul_nonneg (div_nonneg (by norm_num) hs0.le) (abs_nonneg _))
      _ = (2 / Work.SmallBoxSliding.smallConvLower M) * |v z|
            * Work.SmallBoxSliding.chiMass M ℓ d u := by ring
  -- the value of the dominating integral
  have hval : (∫ z : ℝ³, (2 / Work.SmallBoxSliding.smallConvLower M) * |v z|
        * Work.SmallBoxSliding.chiMass M ℓ d u)
      = (2 / Work.SmallBoxSliding.smallConvLower M) * (∫ z : ℝ³, |v z|)
        * Work.SmallBoxSliding.chiMass M ℓ d u := by
    rw [show (fun z : ℝ³ => (2 / Work.SmallBoxSliding.smallConvLower M) * |v z|
          * Work.SmallBoxSliding.chiMass M ℓ d u)
        = (fun z : ℝ³ => ((2 / Work.SmallBoxSliding.smallConvLower M)
            * Work.SmallBoxSliding.chiMass M ℓ d u) * |v z|) from by
      funext z; ring]
    rw [MeasureTheory.integral_const_mul]
    ring
  refine le_trans (le_abs_self _) ?_
  exact le_trans h1 (le_of_eq hval)

theorem flatPairMass_le_const_mul_chiMass_regime {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (h : Work.UBB.ScatSol v) (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3),
      Work.BoseFixB1.flatPairMass v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      ≤ C * (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u := by
  by_cases hav : 0 < _root_.BoseGases.a v
  · -- ## the `0 < a v` branch: the diluteness threshold of `regime_sideAt_ge`
    obtain ⟨ε₀, hε₀, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
    have hs0 : 0 < Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue :=
      Work.SmallBoxSliding.smallConvLower_pos _
    have hQ0 : 0 ≤ (∫ z : ℝ³, |v z|) := integral_nonneg (fun z => abs_nonneg (v z))
    refine ⟨ε₀, (2 / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue)
      * (∫ z : ℝ³, |v z|) / (_root_.BoseGases.a v), hε₀,
      div_nonneg (mul_nonneg (div_nonneg (by norm_num) hs0.le) hQ0) hav.le, ?_⟩
    intro μ hAdm u
    have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
      Work.BoseFixB1.adm_ell_pos hAdm
    have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
      Work.BoseFixB1.adm_d_pos hAdm
    obtain ⟨hR16, hRχ⟩ := hreg μ (Work.BoseFixB1.adm_mu_pos hAdm)
      (Work.BoseFixB1.adm_dilute hAdm)
    have hMv : 1 ≤ Work.BoseBox.mValue := by norm_num [Work.BoseBox.mValue]
    have hkey := flatPairMass_le_regime (v := v) (R0 := R) hR hv_supp hv1
      (M := Work.BoseBox.mValue) hMv hℓ hd hR16 hRχ u
    -- the constant cancellation `((2/s)·Q/a)·a = (2/s)·Q`
    have hcancel : ((2 / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue)
          * (∫ z : ℝ³, |v z|) / (_root_.BoseGases.a v)) * (_root_.BoseGases.a v)
        = (2 / Work.SmallBoxSliding.smallConvLower Work.BoseBox.mValue)
          * (∫ z : ℝ³, |v z|) :=
      div_mul_cancel₀ _ (ne_of_gt hav)
    refine le_trans hkey ?_
    rw [hcancel, Work.BoseFixB1.M_eq_mValue]
  · -- ## the `a v ≤ 0` branch is vacuous: `Adm` forces `0 < a v`
    refine ⟨1, 0, one_pos, le_refl 0, ?_⟩
    intro μ hAdm u
    exact absurd (Work.BoseFixB1.adm_a_pos hAdm) hav

end Work.BoseFixB1B
