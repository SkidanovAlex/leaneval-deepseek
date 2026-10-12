import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1S.flatFibDeviationB1
import Submission.Work.BoseFixB1S.pairing_le_chiSq_mul_abs_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.w1MassB_le_sharp` — the **sharp** per-box one-body mass bound

FS `eq:appw1sliding`, sharp form: for every `δ > 0` there is a diluteness threshold `ε₀ > 0`
such that for every admissible chemical potential `μ` (`Adm v ε₀ μ`) and every sliding-box
parameter `u`,

    ∬ w_{1,B(u)}  =  w1MassB h M ℓ d u   ≤   (1 + δ)·8π(a v)·chiMass M ℓ d u ,

with `M = pM v μ`, `ℓ = pL v μ`, `d = pD v μ` the FS small-box parameters.

## Why the exact constant `8π a v`

The localised one-body kernel factors as

    wSmall1Pair h M ℓ d u x y = χ_{B(u)}(x)·g₀(x−y)/(csm(x−y)·cs(x−y))·χ_{B(u)}(y) ,

where `csm = convScaleSmall M (ℓd)` and `cs = convScale ℓ` are the two renormalisation
denominators (`DLSmallKernels.wSmallScaled`, `KernelIds.convScale`).  As `μ → 0⁺` both `ℓ` and
`ℓd` blow up, so on the support `ball 0 R` of `g₀` both denominators approach their value at
`0`, which is `1` (`conv3Small_zero`, `conv3_at_zero`).  Hence for diluteness small enough,
*pointwise*

    |wSmall1Pair … x y| ≤ (1 + δ)·χ_{B(u)}(x)·|g₀(x−y)|·χ_{B(u)}(y) ,

and then the elementary AM–GM pairing bound
`∬ χ x·|g₀(x−y)|·χ y ≤ (∫χ²)(∫|g₀|)` (`pairing_le_chiSq_mul_abs_integral`) together with
`∫|g₀| = 8π(a v)` (`g0_abs_integral`) gives the constant `8π a v` **exactly**, with no further
loss.  This is the sharpness that the crude `WB.mass_upper` (constant `16π/smallConvLower M`,
of size `≈ 10^{46}` at `M = 48`) cannot reach: there the pointwise domination
`abs_wSmall1Pair_chiB_le` has the constant `2/smallConvLower M`, which is far too large for the
razor `suppR v/(a v) − 1` of the flat arm.

## Contents

* `radius_lower_of_continuousAt` — from continuity at `0` and value `1`, a ball on which a
  function dominates any prescribed `p < 1` (the quantitative form of the packaged
  `chiR0`-type witnesses);
* `exists_eps_regime` — the two box-size conditions `R ≤ ℓ·r` and `R ≤ ℓ·d·s` at *arbitrary*
  prescribed radii `r, s > 0` (the generalisation of `regime_sideAt_ge`, whose constants are
  `1/16` and `chiR0`);
* `wSmall1Pair_abs_le_sharp` — the pointwise sharp kernel bound;
* `w1MassB_le_of_pointwise_sharp` — the integration step: a pointwise bound of the above shape
  integrates to the sharp mass bound (`w1MassB = ∫∫ wSmall1Pair`, AM–GM pairing, `∫|g₀| = 8πa`);
* `w1MassB_le_sharp` — the target, assembled from the pointwise bound and the integration step.
-/

namespace Work.BoseB1Cube

open MeasureTheory Metric
open scoped Topology Real BigOperators ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **A ball on which a continuous function with value `1` at `0` dominates `p`.**  For
`f` continuous at `0` with `f 0 = 1` and any `p < 1` there is `r > 0` with `p ≤ f x` whenever
`‖x‖ ≤ r`.  (Quantitative form of `BoseGases.half_lower_ball_of_continuousAt_one`, at an
arbitrary threshold `p < 1`; used with `p = (1+δ)^{-1/2}` so that the *product* of the two
renormalisation denominators dominates `1/(1+δ)`.) -/
lemma radius_lower_of_continuousAt {f : E3 → ℝ} (hc : ContinuousAt f 0) (h0 : f 0 = 1)
    {p : ℝ} (hp : p < 1) : ∃ r : ℝ, 0 < r ∧ ∀ x : E3, ‖x‖ ≤ r → p ≤ f x := by
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδpos, hδ⟩ := hc (1 - p) (by linarith)
  refine ⟨δ / 2, by positivity, ?_⟩
  intro x hx
  have hxd : dist x 0 < δ := by
    rw [dist_eq_norm, sub_zero]
    linarith
  have hd := hδ hxd
  rw [h0, Real.dist_eq] at hd
  have := (abs_lt.mp hd).1
  linarith

/-- **The general box-size regime.**  For every prescribed `r, s > 0` and every admissible
chemical potential with diluteness below a threshold depending on `r, s`, the box side `ℓ` and
the small-box side `ℓd` satisfy `R ≤ ℓ·r` and `R ≤ ℓ·d·s`.

This is `regime_sideAt_ge` with the two hard-wired constants (`1/16`, `chiR0`) replaced by
arbitrary positive radii; both statements are elementary consequences of the closed forms
`ℓ = a·(μa³)^{-163/323}` (`BoseBox.sideAt_large`) and `ℓd = a·(μa³)^{-157/323}`
(`BoseFixB1.d_mul_sideAt_eq`, consumed through `eventually_sideAt_mul_d_ge`). -/
lemma exists_eps_regime {v : E3 → ℝ} (hav : 0 < _root_.BoseGases.a v) {R : ℝ} (hR : 0 < R)
    {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      R ≤ Work.BoseFixB1.pL v μ * r ∧ R ≤ Work.BoseFixB1.pL v μ * Work.BoseFixB1.pD v μ * s := by
  have ha3 : 0 < (_root_.BoseGases.a v) ^ 3 := by positivity
  have h1 : ∀ᶠ μ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * r :=
    Work.BoseBox.sideAt_large (a := _root_.BoseGases.a v) hav R r hr
  have hRs : 0 < R / s := div_pos hR hs
  have h2 : ∀ᶠ μ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      R / s ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16 :=
    Work.BoseFixB1.eventually_sideAt_mul_d_ge (a := _root_.BoseGases.a v) hav hRs
  have h := h1.and h2
  rw [eventually_nhdsWithin_iff] at h
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδpos, hδ⟩ := h
  refine ⟨min 1 (δ * (_root_.BoseGases.a v) ^ 3 / 2), lt_min one_pos (by positivity), ?_⟩
  intro μ hAdm
  have hμpos : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have ht : μ * (_root_.BoseGases.a v) ^ 3
      ≤ min 1 (δ * (_root_.BoseGases.a v) ^ 3 / 2) := Work.BoseFixB1.adm_dilute hAdm
  have htδ : μ * (_root_.BoseGases.a v) ^ 3 ≤ δ * (_root_.BoseGases.a v) ^ 3 / 2 :=
    le_trans ht (min_le_right _ _)
  have hμδ : μ < δ := by nlinarith
  have hdist : dist μ 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hμpos]
    exact hμδ
  obtain ⟨hr1, hrs⟩ := hδ hdist hμpos
  refine ⟨hr1, ?_⟩
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  -- `R/s ≤ ℓd/16` gives, after multiplying by `16s`, `16R ≤ ℓds`, hence `R ≤ ℓds`
  have h4 : 16 * R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d * s := by
    have h := mul_le_mul_of_nonneg_right hrs (by positivity : (0 : ℝ) ≤ 16 * s)
    have e1 : (R / s) * (16 * s) = 16 * R := by field_simp
    have e2 : (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16) * (16 * s)
        = Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d * s := by field_simp
    rwa [e1, e2] at h
  have h6 : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d * s := by
    have h5 : (0 : ℝ) ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d * s := by positivity
    linarith
  exact h6

/-- **The pointwise sharp kernel bound.**  With `p > 0`, `(p²)⁻¹ = 1 + δ`, and the two
continuity balls supplied by `radius_lower_of_continuousAt`/`exists_eps_regime`, the localised
one-body kernel is dominated by `(1+δ)` times the ideal kernel
`χ_{B(u)}·|g₀|·χ_{B(u)}`.

The proof splits on `R ≤ ‖x−y‖`: there `g₀ = 0` (`g0_zero_of_norm_ge`) and both sides vanish;
otherwise `‖x−y‖ ≤ R` gives `‖(ℓd)⁻¹(x−y)‖ ≤ s` and `‖ℓ⁻¹(x−y)‖ ≤ r` (from the two regime
conditions), so the two renormalisation denominators — the self-convolutions `conv3Small M` and
`conv3 chi chi` evaluated at those arguments — dominate `p`, whence `(1+δ)` from `1/p² = 1 + δ`. -/
lemma wSmall1Pair_abs_le_sharp {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d δ p r s : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hδ : 0 < δ)
    (hp0 : 0 < p) (hp : (p ^ 2)⁻¹ = 1 + δ)
    (hreg1 : R ≤ ℓ * r) (hreg2 : R ≤ ℓ * d * s)
    (hrp : ∀ w : E3, ‖w‖ ≤ r →
      p ≤ Submission.BoseGases.conv3 Submission.BoseGases.chi Submission.BoseGases.chi w)
    (hsp : ∀ w : E3, ‖w‖ ≤ s → p ≤ Submission.BoseGases.conv3Small M w)
    (u x y : E3) :
    |Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
      ≤ (1 + δ) * Submission.BoseGases.chiSmallB M ℓ d u x
        * |Submission.BoseGases.g0 v h (x - y)| * Submission.BoseGases.chiSmallB M ℓ d u y := by
  have h1δ : (0 : ℝ) < 1 + δ := by linarith
  have hχx : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u x
  have hχy : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u y :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u y
  by_cases hRz : R ≤ ‖x - y‖
  · -- the support case: `g₀` vanishes and so does the kernel
    have hg0 : Submission.BoseGases.g0 v h (x - y) = 0 :=
      Submission.BoseGases.g0_zero_of_norm_ge hv_supp hRz h
    have hzero : Submission.BoseGases.wSmall1Pair h M ℓ d u x y = 0 := by
      unfold Submission.BoseGases.wSmall1Pair Submission.BoseGases.wSmallPair
        Submission.BoseGases.wSmallScaled
      rw [hg0]
      simp
    rw [hzero, abs_zero]
    have hnn : 0 ≤ (1 + δ) * Submission.BoseGases.chiSmallB M ℓ d u x
        * |Submission.BoseGases.g0 v h (x - y)| * Submission.BoseGases.chiSmallB M ℓ d u y :=
      mul_nonneg (mul_nonneg (mul_nonneg h1δ.le hχx) (abs_nonneg _)) hχy
    linarith
  · push_neg at hRz
    have hzR : ‖x - y‖ ≤ R := le_of_lt hRz
    have hldpos : 0 < ℓ * d := mul_pos hℓ hd
    have hinv_ld : 0 ≤ (ℓ * d)⁻¹ := inv_nonneg.mpr hldpos.le
    have hinv_l : 0 ≤ ℓ⁻¹ := inv_nonneg.mpr hℓ.le
    have hsm : ‖((ℓ * d)⁻¹ : ℝ) • (x - y)‖ ≤ s := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv_ld]
      calc (ℓ * d)⁻¹ * ‖x - y‖ ≤ (ℓ * d)⁻¹ * (ℓ * d * s) :=
            mul_le_mul_of_nonneg_left (le_trans hzR hreg2) hinv_ld
        _ = s := by field_simp
    have hℓz : ‖(ℓ⁻¹ : ℝ) • (x - y)‖ ≤ r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv_l]
      calc ℓ⁻¹ * ‖x - y‖ ≤ ℓ⁻¹ * (ℓ * r) :=
            mul_le_mul_of_nonneg_left (le_trans hzR hreg1) hinv_l
        _ = r := by field_simp
    have hcsm_ge : p ≤ Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y) := by
      simpa [Submission.BoseGases.convScaleSmall] using hsp _ hsm
    have hcs_ge : p ≤ Submission.BoseGases.convScale ℓ (x - y) := by
      simpa [Submission.BoseGases.convScale] using hrp _ hℓz
    have hcsm_pos : 0 < Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y) :=
      lt_of_lt_of_le hp0 hcsm_ge
    have hcs_pos : 0 < Submission.BoseGases.convScale ℓ (x - y) := lt_of_lt_of_le hp0 hcs_ge
    have hkey : |Submission.BoseGases.g0 v h (x - y)|
          / Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
          / Submission.BoseGases.convScale ℓ (x - y)
        ≤ (1 + δ) * |Submission.BoseGases.g0 v h (x - y)| := by
      have h1 : |Submission.BoseGases.g0 v h (x - y)|
            / Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
          ≤ |Submission.BoseGases.g0 v h (x - y)| / p :=
        div_le_div_of_nonneg_left (abs_nonneg _) hp0 hcsm_ge
      have h2 : |Submission.BoseGases.g0 v h (x - y)| / p
            / Submission.BoseGases.convScale ℓ (x - y)
          ≤ |Submission.BoseGases.g0 v h (x - y)| / p / p :=
        div_le_div_of_nonneg_left (div_nonneg (abs_nonneg _) hp0.le) hp0 hcs_ge
      have h3 : |Submission.BoseGases.g0 v h (x - y)| / p / p
          = (1 + δ) * |Submission.BoseGases.g0 v h (x - y)| := by
        rw [div_div, ← pow_two, div_eq_mul_inv, hp]
        ring
      calc |Submission.BoseGases.g0 v h (x - y)|
              / Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
              / Submission.BoseGases.convScale ℓ (x - y)
          ≤ |Submission.BoseGases.g0 v h (x - y)| / p
              / Submission.BoseGases.convScale ℓ (x - y) :=
            div_le_div_of_nonneg_right h1 hcs_pos.le
        _ ≤ |Submission.BoseGases.g0 v h (x - y)| / p / p := h2
        _ = (1 + δ) * |Submission.BoseGases.g0 v h (x - y)| := h3
    have habs : |Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
        = Submission.BoseGases.chiSmallB M ℓ d u x
          * (|Submission.BoseGases.g0 v h (x - y)|
              / Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
              / Submission.BoseGases.convScale ℓ (x - y))
          * Submission.BoseGases.chiSmallB M ℓ d u y := by
      unfold Submission.BoseGases.wSmall1Pair Submission.BoseGases.wSmallPair
        Submission.BoseGases.wSmallScaled
      rw [abs_mul, abs_mul, abs_of_nonneg hχx, abs_of_nonneg hχy, abs_div, abs_div,
        abs_of_pos hcsm_pos, abs_of_pos hcs_pos]
    rw [habs]
    calc Submission.BoseGases.chiSmallB M ℓ d u x
          * (|Submission.BoseGases.g0 v h (x - y)|
              / Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
              / Submission.BoseGases.convScale ℓ (x - y))
          * Submission.BoseGases.chiSmallB M ℓ d u y
        ≤ Submission.BoseGases.chiSmallB M ℓ d u x
          * ((1 + δ) * |Submission.BoseGases.g0 v h (x - y)|)
          * Submission.BoseGases.chiSmallB M ℓ d u y :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey hχx) hχy
      _ = (1 + δ) * Submission.BoseGases.chiSmallB M ℓ d u x
          * |Submission.BoseGases.g0 v h (x - y)| * Submission.BoseGases.chiSmallB M ℓ d u y := by
          ring

/-- **The integration step.**  A pointwise domination of the localised one-body kernel by
`(1+δ)·χ_{B(u)}(x)·|g₀(x−y)|·χ_{B(u)}(y)` integrates to the sharp mass bound

    w1MassB h M ℓ d u ≤ (1 + δ)·8π(a v)·chiMass M ℓ d u .

Indeed `w1MassB = ∫∫ wSmall1Pair`; the pointwise bound makes the uncurried kernel a.e. strongly
measurable (the two denominators are continuous, `g₀` is integrable, and the difference map is
quasi-measure-preserving) and integrable, `integral_prod` identifies the double integral with the
integral over the product space, and the AM–GM pairing bound
`Work.BoseFixB1S.pairing_le_chiSq_mul_abs_integral` — `∬χ(x)|g₀(x−y)|χ(y) ≤ (∫χ²)(∫|g₀|)` —
with `∫|g₀| = 8π(a v)` (`g0_abs_integral`) finishes. -/
lemma w1MassB_le_of_pointwise_sharp {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d δ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hδ : 0 < δ)
    (hpt : ∀ u x y : E3,
        |Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
          ≤ (1 + δ) * Submission.BoseGases.chiSmallB M ℓ d u x
              * |Submission.BoseGases.g0 v h (x - y)| * Submission.BoseGases.chiSmallB M ℓ d u y) :
    ∀ u : E3,
      Work.BoseFixB1.w1MassB h M ℓ d u
        ≤ (1 + δ) * (8 * Real.pi * _root_.BoseGases.a v)
            * Work.SmallBoxSliding.chiMass M ℓ d u := by
  intro u
  have h1δ : (0 : ℝ) < 1 + δ := by linarith
  have hGint : Integrable (Submission.BoseGases.g0 v h) :=
    Submission.BoseGases.g0_integrable hR hv_supp h
  obtain ⟨hpairInt, hpairLe⟩ := Work.BoseFixB1S.pairing_le_chiSq_mul_abs_integral
    (χ := Submission.BoseGases.chiSmallB M ℓ d u)
    (fun x => Submission.BoseGases.chiSmallB_nonneg M ℓ d u x)
    (Submission.BoseGases.chiSmallB_continuous hM hℓ hd u)
    (Submission.BoseGases.chiSmallB_hasCompactSupport hM hℓ u)
    hGint
  have hmajInt : Integrable (fun p : E3 × E3 =>
      (1 + δ) * (Submission.BoseGases.chiSmallB M ℓ d u p.1
        * |Submission.BoseGases.g0 v h (p.1 - p.2)| * Submission.BoseGases.chiSmallB M ℓ d u p.2))
      volume := hpairInt.const_mul (1 + δ)
  have hpt' : ∀ u x y : E3, |Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
      ≤ (1 + δ) * (Submission.BoseGases.chiSmallB M ℓ d u x
          * |Submission.BoseGases.g0 v h (x - y)| * Submission.BoseGases.chiSmallB M ℓ d u y) := by
    intro u x y
    calc |Submission.BoseGases.wSmall1Pair h M ℓ d u x y|
        ≤ (1 + δ) * Submission.BoseGases.chiSmallB M ℓ d u x
            * |Submission.BoseGases.g0 v h (x - y)| * Submission.BoseGases.chiSmallB M ℓ d u y :=
          hpt u x y
      _ = (1 + δ) * (Submission.BoseGases.chiSmallB M ℓ d u x
            * |Submission.BoseGases.g0 v h (x - y)| * Submission.BoseGases.chiSmallB M ℓ d u y) := by
          ring
  -- the localised kernel is a.e. strongly measurable on the product
  have hKmeas : AEMeasurable (fun z : E3 =>
      Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
        / Submission.BoseGases.convScale ℓ z) volume := by
    have hg0m : AEMeasurable (Submission.BoseGases.g0 v h) volume := hGint.aemeasurable
    have hcont1 : Continuous (fun z : E3 => Submission.BoseGases.convScaleSmall M (ℓ * d) z) :=
      (Submission.BoseGases.conv3Small_continuous hM).comp (continuous_id.const_smul ((ℓ * d)⁻¹))
    have hWsm : AEMeasurable (fun z : E3 =>
        Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z) volume :=
      (hg0m.div hcont1.measurable.aemeasurable).congr
        (Filter.Eventually.of_forall (fun z => by
          simp only [Submission.BoseGases.wSmallScaled, div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply]))
    have hcont2 : Continuous (fun z : E3 => Submission.BoseGases.convScale ℓ z) :=
      (Submission.BoseGases.conv_contDiff.continuous).comp (continuous_id.const_smul (ℓ⁻¹))
    exact hWsm.div hcont2.measurable.aemeasurable
  have hWmeas : AEStronglyMeasurable (fun p : E3 × E3 =>
      Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2) volume := by
    have hKp : AEMeasurable (fun p : E3 × E3 =>
        (fun z : E3 => Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
          / Submission.BoseGases.convScale ℓ z) (p.1 - p.2)) volume :=
      Work.BoseFixB1S.subPair_aemeasurable hKmeas
    have hχ1 : AEMeasurable (fun p : E3 × E3 => Submission.BoseGases.chiSmallB M ℓ d u p.1)
        volume :=
      ((Submission.BoseGases.chiSmallB_continuous hM hℓ hd u).comp continuous_fst).aemeasurable
    have hχ2 : AEMeasurable (fun p : E3 × E3 => Submission.BoseGases.chiSmallB M ℓ d u p.2)
        volume :=
      ((Submission.BoseGases.chiSmallB_continuous hM hℓ hd u).comp continuous_snd).aemeasurable
    refine ((hχ1.mul hKp).mul hχ2).aestronglyMeasurable.congr ?_
    filter_upwards with p
    simp only [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair, Pi.mul_apply]
  have hWbound : ∀ᵐ p : E3 × E3 ∂(volume : Measure (E3 × E3)),
      ‖Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2‖
        ≤ (1 + δ) * (Submission.BoseGases.chiSmallB M ℓ d u p.1
            * |Submission.BoseGases.g0 v h (p.1 - p.2)|
            * Submission.BoseGases.chiSmallB M ℓ d u p.2) := by
    filter_upwards with p
    rw [Real.norm_eq_abs]
    exact hpt' u p.1 p.2
  have hWint : Integrable (fun p : E3 × E3 =>
      Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2) volume :=
    Integrable.mono' hmajInt hWmeas hWbound
  -- identify the double integral with the product-space integral
  have hprod : (∫ p : E3 × E3, Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2)
      = ∫ x : E3, ∫ y : E3, Submission.BoseGases.wSmall1Pair h M ℓ d u x y := by
    rw [Measure.volume_eq_prod E3 E3]
    exact MeasureTheory.integral_prod _ hWint
  have hmain : Work.BoseFixB1.w1MassB h M ℓ d u
      = ∫ p : E3 × E3, Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2 := hprod.symm
  rw [hmain]
  calc (∫ p : E3 × E3, Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2)
      ≤ ∫ p : E3 × E3, (1 + δ) * (Submission.BoseGases.chiSmallB M ℓ d u p.1
          * |Submission.BoseGases.g0 v h (p.1 - p.2)|
          * Submission.BoseGases.chiSmallB M ℓ d u p.2) :=
        integral_mono hWint hmajInt (fun p => le_trans (le_abs_self _) (hpt' u p.1 p.2))
    _ = (1 + δ) * ∫ p : E3 × E3, (Submission.BoseGases.chiSmallB M ℓ d u p.1
          * |Submission.BoseGases.g0 v h (p.1 - p.2)|
          * Submission.BoseGases.chiSmallB M ℓ d u p.2) :=
        MeasureTheory.integral_const_mul (1 + δ) _
    _ ≤ (1 + δ) * ((∫ x : E3, (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2)
          * (∫ z : E3, |Submission.BoseGases.g0 v h z|)) :=
        mul_le_mul_of_nonneg_left hpairLe h1δ.le
    _ = (1 + δ) * (8 * Real.pi * _root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass M ℓ d u := by
        rw [Submission.BoseGases.g0_abs_integral hR hv hvrad hv_supp h,
          Work.SmallBoxSliding.chiMass_def]
        ring

theorem w1MassB_le_sharp {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ → ∀ u : EuclideanSpace ℝ (Fin 3),
      Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u
        ≤ (1 + δ) * (8 * Real.pi * _root_.BoseGases.a v)
            * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u := by
  have h1δ : (0 : ℝ) < 1 + δ := by linarith
  have hM0 : 1 ≤ Work.BoseBox.mValue := by norm_num [Work.BoseBox.mValue]
  -- the sharp factor `p := (1+δ)^{-1/2}` on the *product* of the two denominators
  set p : ℝ := (Real.sqrt (1 + δ))⁻¹ with hpdef
  have hsq1 : 1 < Real.sqrt (1 + δ) := by
    have := Real.sqrt_lt_sqrt (x := 1) (y := 1 + δ) (by norm_num) (by linarith : (1 : ℝ) < 1 + δ)
    rwa [Real.sqrt_one] at this
  have hp0 : 0 < p := by rw [hpdef]; positivity
  have hp1 : p < 1 := by rw [hpdef]; exact inv_lt_one_of_one_lt₀ hsq1
  have hp2 : (p ^ 2)⁻¹ = 1 + δ := by
    rw [hpdef, inv_pow, inv_inv, Real.sq_sqrt h1δ.le]
  -- the two continuity radii
  obtain ⟨r, hrpos, hrp⟩ := radius_lower_of_continuousAt
    (Submission.BoseGases.conv_contDiff.continuous.continuousAt)
    Submission.BoseGases.conv3_at_zero hp1
  obtain ⟨s, hspos, hsp⟩ := radius_lower_of_continuousAt
    ((Submission.BoseGases.conv3Small_continuous hM0).continuousAt)
    (Submission.BoseGases.conv3Small_zero hM0) hp1
  -- the diluteness regime making the two arguments `(ℓd)⁻¹(x−y)`, `ℓ⁻¹(x−y)` small
  obtain ⟨ε₀, hε₀, hreg⟩ := exists_eps_regime (v := v) hav hR hrpos hspos
  refine ⟨ε₀, hε₀, ?_⟩
  intro μ hAdm u
  obtain ⟨hreg1, hreg2⟩ := hreg μ hAdm
  have hℓ : 0 < Work.BoseFixB1.pL v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.pD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hMμ : 1 ≤ Work.BoseFixB1.pM v μ := by
    simpa [Work.BoseFixB1.pM, Work.BoseFixB1.M_eq_mValue] using hM0
  have hpt : ∀ u x y : E3,
      |Submission.BoseGases.wSmall1Pair h (Work.BoseFixB1.pM v μ)
          (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u x y|
        ≤ (1 + δ) * Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ)
            (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u x
          * |Submission.BoseGases.g0 v h (x - y)|
          * Submission.BoseGases.chiSmallB (Work.BoseFixB1.pM v μ)
            (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u y := by
    intro u x y
    exact wSmall1Pair_abs_le_sharp h hv_supp hMμ hℓ hd hδ hp0 hp2 hreg1 hreg2
      (fun w hw => hrp w hw) (fun w hw => hsp w hw) u x y
  exact w1MassB_le_of_pointwise_sharp h hv hvrad hR hv_supp hMμ hℓ hd hδ hpt u

end Work.BoseB1Cube
