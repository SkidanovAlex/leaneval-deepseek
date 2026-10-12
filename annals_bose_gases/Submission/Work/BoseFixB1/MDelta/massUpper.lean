import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.MDelta.defs
import Submission.Work.BoseFixB1B.boxM2_sub_boxM1_eq_omegaMass
import Submission.Work.BoseFixB1S.PlateauDefs
import Submission.Work.BoseFixB1S.pairing_le_chiSq_mul_abs_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.MDelta.massUpper` — the upper mass estimate `MΔ ≤ (1+16)·D·χ_m + 16·a·χ_m`

The `MΔ`-payer lane (`FINDING_MDeltaConversion.md`): the *upper* direction of FS `lm:w2>w1` at
the corpus's two-factor cutoff.  The target `Work.BoseFixB1.MassUpper v h 16` asks for a
diluteness threshold such that on the good set

    MΔ = bM2 − bM1 ≤ (1+16)·(g₀ω₀-mass)·chiMass + 16·(a v)·chiMass .

## The mathematics (no Bogoliubov, no commutator)

`boxM2 − boxM1 = ∬_{B(u)×B(u)} ω₀(x−y)·w_{1,B(u)}(x,y)` is the PROVED identity
`boxM2_sub_boxM1_eq_omegaMass`, and the localised kernel factors as

    w_{1,B}(x,y) = χ_B(x)·(g₀(x−y)/[C_{ℓd}(x−y)·convScale_ℓ(x−y)])·χ_B(y) ,

so the whole content is that the *two* renormalisation denominators are bounded below by
`1/2` on `supp g₀ ⊆ ball 0 R`:

* `convScale ℓ ≥ 1/2` on `ball 0 R` for `R ≤ ℓ·χR₀` (`convScale_ge_half_ball`, PROVED);
* `convScaleSmall M (ℓd) z = (χ_M ⋆ χ_M)(z/(ℓd))`, and the self-convolution satisfies the
  *quantitative* flatness estimate `1 − (χ_M⋆χ_M)(t) = ½∫(χ_M y − χ_M(y−t))² ≤ L²‖t‖²`
  (`devQuad_one_sub_eq_half_integral` + `devQuad_integral_diff_sq_le`), so the diluteness
  condition `R ≤ ℓd/(2L²)` — available from `regime_sideAt_ge_div`, since `ℓd = a·(μa³)^{−157/323}`
  blows up in the dilute limit — gives `(χ_M⋆χ_M)(z/(ℓd)) ≥ 1/2` on `‖z‖ ≤ R`.  This is where the
  sharp constant `1/convScale ≤ 2` of the FINDING comes from, and it is why the *crude* bounds
  (`smallConvLower M = 2^{−3M−6}`; `boxM2 ≤ 10^{47}·a·χ_m`) cannot close the row.

With `1/(denominator) ≤ 4` pointwise on the support, `ω₀ ≥ 0` a.e. and AM–GM
(`pairing_le_chiSq_mul_abs_integral`, `∬χ(x)k(x−y)χ(y) ≤ (∫χ²)(∫k)` for `k ≥ 0`):

    MΔ ≤ 4·∬_{ℝ³×ℝ³} χ(x)χ(y)(g₀ω₀)(x−y) ≤ 4·chiMass·g0w0Mass ≤ 17·chiMass·g0w0Mass .

-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1.MDelta

open _root_.BoseGases Submission.BoseGases Work.SmallBoxSliding Work.BoseBox Work.UBB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1. Toolbox: the flatness constant of the `dℓ` self-convolution, and the regime -/

/-- **The quadratic-deviation constant of `conv3Small`**, in the normalised form used below:
there is `L ≥ 1` with `|(χ_M ⋆ χ_M)(t) − 1| ≤ L²‖t‖²` for *every* `t`.

This is `chiSmall_lipschitz` (a Lipschitz constant `L₀` of `χ_M`) combined with
`devQuad_one_sub_eq_half_integral` and `devQuad_integral_diff_sq_le` (the polarisation identity
`1 − (χ_M⋆χ_M)(t) = ½∫(χ_M y − χ_M(y−t))² ≤ L₀²‖t‖²`); replacing `L₀` by `max 1 L₀` makes the
constant `≥ 1`, so that `‖t‖ ≤ 1/(2L²)` gives `L²‖t‖² ≤ 1/4`. -/
theorem conv3Small_dev_L2 {M : ℕ} (hM : 1 ≤ M) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ t : E3,
      |Submission.BoseGases.conv3Small M t - 1| ≤ L ^ 2 * ‖t‖ ^ 2 := by
  obtain ⟨L₀, hL₀nn, hLip⟩ := Work.BoseFixB1S.chiSmall_lipschitz hM
  refine ⟨max 1 L₀, le_max_left _ _, fun t => ?_⟩
  have hid := Work.BoseFixB1S.devQuad_one_sub_eq_half_integral hM t
  have hle := Work.BoseFixB1S.devQuad_integral_diff_sq_le hM hLip t
  have hnn : 0 ≤ 1 - Submission.BoseGases.conv3Small M t := by
    rw [hid]; positivity
  have hkey : |Submission.BoseGases.conv3Small M t - 1| = 1 - Submission.BoseGases.conv3Small M t := by
    rw [abs_sub_comm, abs_of_nonneg hnn]
  rw [hkey]
  calc 1 - Submission.BoseGases.conv3Small M t
      = (1 / 2) * ∫ y : E3,
          (Submission.BoseGases.chiSmall M y - Submission.BoseGases.chiSmall M (y - t)) ^ 2 := hid
    _ ≤ (1 / 2) * (2 * L₀ ^ 2 * ‖t‖ ^ 2) := mul_le_mul_of_nonneg_left hle (by norm_num)
    _ = L₀ ^ 2 * ‖t‖ ^ 2 := by ring
    _ ≤ (max 1 L₀) ^ 2 * ‖t‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
        exact pow_le_pow_left₀ hL₀nn (le_max_right _ _) 2

/-- **The dilute regime with a prescribed constant.**  For every fixed radius `R > 0` and every
fixed `K > 0` there is a diluteness threshold `ε₀ > 0` such that `μ·(a v)³ ≤ ε₀` forces the box
side to satisfy `R ≤ ℓ(μ)·d(μ)/K`.

This is the generalisation of `Work.BoseFixB1.eventually_sideAt_mul_d_ge` (the case `K = 16`)
along the same monomial computation: `ℓ·d = a·(μa³)^{−157/323}` (`d_mul_sideAt_eq`), so the
claim is `(μa³)^{−157/323} ≥ KR/a`. -/
lemma eventually_sideAt_mul_d_ge_div {a : ℝ} (ha : 0 < a) {R K : ℝ} (hR : 0 < R) (hK : 0 < K) :
    ∀ᶠ μ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      R ≤ Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d / K := by
  set C : ℝ := K * R / a with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have ha3 : 0 < a ^ 3 := by positivity
  set δ : ℝ := C ^ (-(323 / 157 : ℝ)) / a ^ 3 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  rw [eventually_nhdsWithin_iff]
  filter_upwards [Ioo_mem_nhds (show -(δ) < (0 : ℝ) by linarith) hδpos]
    with μ hμmem hμpos
  have hμlt : μ < δ := hμmem.2
  have ht0 : 0 < μ * a ^ 3 := mul_pos hμpos ha3
  have htle : μ * a ^ 3 ≤ C ^ (-(323 / 157 : ℝ)) := by
    have h : μ * a ^ 3 < δ * a ^ 3 := mul_lt_mul_of_pos_right hμlt ha3
    rw [hδdef, div_mul_cancel₀ _ (ne_of_gt ha3)] at h
    exact le_of_lt h
  have hCpow : (C ^ (-(323 / 157 : ℝ))) ^ (-(157 / 323 : ℝ)) = C := by
    rw [← Real.rpow_mul hCpos.le]
    norm_num
  have hkey : C ≤ (μ * a ^ 3) ^ (-(157 / 323 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_nonpos ht0 htle (show (-(157 / 323 : ℝ)) ≤ 0 by norm_num)
    rwa [hCpow] at h
  have hprod : Work.BoseBox.sideAt μ a * (Work.BoseBox.paramsAt μ a).d
      = a * (μ * a ^ 3) ^ (-(157 / 323 : ℝ)) := by
    have h := Work.BoseFixB1.d_mul_sideAt_eq (A := a) (μ := μ) ha hμpos
    rw [Work.BoseBox.fsXp] at h
    rw [mul_comm (Work.BoseBox.sideAt μ a) (Work.BoseBox.paramsAt μ a).d, h]
    norm_num
  rw [hprod]
  rw [le_div_iff₀ hK]
  have h1 : K * R ≤ a * (μ * a ^ 3) ^ (-(157 / 323 : ℝ)) := by
    have h := mul_le_mul_of_nonneg_left hkey ha.le
    rwa [show a * C = K * R by rw [hCdef]; field_simp] at h
  linarith

/-- **The dilute regime with a prescribed constant and the `χ`-radius condition**: there is
`ε₀ > 0` such that `0 < μ`, `μ(a v)³ ≤ ε₀` imply both `R ≤ ℓ(μ)d(μ)/K` and `R ≤ ℓ(μ)·χR₀`. -/
lemma regime_sideAt_ge_div {v : E3 → ℝ} (hav : 0 < _root_.BoseGases.a v) {R K : ℝ}
    (hR : 0 < R) (hK : 0 < K) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ →
      R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / K ∧
      R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0 := by
  have h1 := eventually_sideAt_mul_d_ge_div (a := _root_.BoseGases.a v) hav hR hK
  have h2 := Work.BoseBox.sideAt_large (a := _root_.BoseGases.a v) hav R Submission.BoseGases.chiR0
    Submission.BoseGases.chiR0_pos
  have h := h1.and h2
  rw [eventually_nhdsWithin_iff] at h
  rw [Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδpos, hδ⟩ := h
  have ha3 : 0 < (_root_.BoseGases.a v) ^ 3 := by positivity
  refine ⟨min 1 (δ * (_root_.BoseGases.a v) ^ 3 / 2), lt_min one_pos (by positivity), ?_⟩
  intro μ hμpos ht
  have htδ : μ * (_root_.BoseGases.a v) ^ 3 ≤ δ * (_root_.BoseGases.a v) ^ 3 / 2 :=
    le_trans ht (min_le_right _ _)
  have hμδ : μ < δ := by nlinarith [ha3, hδpos]
  exact hδ (y := μ) (by rw [Real.dist_eq, sub_zero, abs_of_pos hμpos]; exact hμδ) hμpos

/-! ## §2. The pointwise kernel comparison -/

/-- **The pointwise comparison of the localised one-body kernel with `4·χ_B ⊗ g₀ω₀ ⊗ χ_B`.**

If the two renormalisation denominators multiply to at least `1/4` on `ball 0 R`, if `g₀` vanishes
outside that ball, and if `ω₀` and `g₀` are non-negative at the point, then

    ω₀(x−y)·w_{1,B}(x,y) ≤ 4·χ_B(x)·|g₀(x−y)ω₀(x−y)|·χ_B(y) .

Indeed `w_{1,B}(x,y) = χ_B(x)·(g₀(z)/(C_{ℓd}(z)·convScale_ℓ(z)))·χ_B(y)` with `z = x−y`; on the
ball the denominator is `≥ 1/4`, so `g₀(z)/denom ≤ 4·g₀(z)` (for `g₀ ≥ 0`), and off the ball both
sides vanish because `g₀` does.  No hypothesis on the *signs* of the two factors of the
denominator is needed beyond the product bound, and `ω₀ ≤ 1` is never used. -/
lemma pair_le_four_of_denom_lower {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {R ℓ d : ℝ} {M : ℕ}
    (u : E3)
    (hden : ∀ z : E3, ‖z‖ ≤ R → (1 / 4 : ℝ) ≤
      Submission.BoseGases.convScaleSmall M (ℓ * d) z * Submission.BoseGases.convScale ℓ z)
    (hg0supp : ∀ z : E3, R ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0)
    {x y : E3} (hω : 0 ≤ (Classical.choose h) (x - y))
    (hg0 : 0 ≤ Submission.BoseGases.g0 v h (x - y)) :
    (Classical.choose h) (x - y) * Submission.BoseGases.wSmall1Pair h M ℓ d u x y
      ≤ 4 * (Submission.BoseGases.chiSmallB M ℓ d u x
              * |Submission.BoseGases.g0 v h (x - y) * (Classical.choose h) (x - y)|
              * Submission.BoseGases.chiSmallB M ℓ d u y) := by
  have hχx : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u x
  have hχy : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u y :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u y
  have hunfold : Submission.BoseGases.wSmall1Pair h M ℓ d u x y
      = Submission.BoseGases.chiSmallB M ℓ d u x
        * ((Submission.BoseGases.g0 v h (x - y) / Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y))
            / Submission.BoseGases.convScale ℓ (x - y))
        * Submission.BoseGases.chiSmallB M ℓ d u y := rfl
  by_cases hz : ‖x - y‖ ≤ R
  · have hcscv : (1 / 4 : ℝ) ≤ Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
        * Submission.BoseGases.convScale ℓ (x - y) := hden (x - y) hz
    have hpos : 0 < Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
        * Submission.BoseGases.convScale ℓ (x - y) := lt_of_lt_of_le (by norm_num) hcscv
    have hle : Submission.BoseGases.g0 v h (x - y)
          / (Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
              * Submission.BoseGases.convScale ℓ (x - y))
        ≤ 4 * Submission.BoseGases.g0 v h (x - y) := by
      rw [div_le_iff₀ hpos]
      nlinarith [hcscv, hg0]
    rw [hunfold, div_div]
    have h1 : Submission.BoseGases.chiSmallB M ℓ d u x
          * (Submission.BoseGases.g0 v h (x - y)
              / (Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
                  * Submission.BoseGases.convScale ℓ (x - y)))
          * Submission.BoseGases.chiSmallB M ℓ d u y
        ≤ Submission.BoseGases.chiSmallB M ℓ d u x
          * (4 * Submission.BoseGases.g0 v h (x - y))
          * Submission.BoseGases.chiSmallB M ℓ d u y :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hχx) hχy
    have h2 := mul_le_mul_of_nonneg_left h1 hω
    have hfinal : (Classical.choose h) (x - y) * (Submission.BoseGases.chiSmallB M ℓ d u x
          * (4 * Submission.BoseGases.g0 v h (x - y))
          * Submission.BoseGases.chiSmallB M ℓ d u y)
        = 4 * (Submission.BoseGases.chiSmallB M ℓ d u x
              * |Submission.BoseGases.g0 v h (x - y) * (Classical.choose h) (x - y)|
              * Submission.BoseGases.chiSmallB M ℓ d u y) := by
      rw [abs_of_nonneg (mul_nonneg hg0 hω)]
      ring
    exact h2.trans (le_of_eq hfinal)
  · have hRz : R ≤ ‖x - y‖ := le_of_lt (not_le.mp hz)
    have hgz : Submission.BoseGases.g0 v h (x - y) = 0 := hg0supp (x - y) hRz
    have hLHS : (Classical.choose h) (x - y) * Submission.BoseGases.wSmall1Pair h M ℓ d u x y
        = 0 := by
      rw [hunfold, hgz]
      simp only [zero_div, zero_mul, mul_zero]
    rw [hLHS, hgz]
    simp only [zero_mul, abs_zero, mul_zero]
    norm_num

/-- **Non-negativity of the `ω₀`-weighted localised one-body kernel**, pointwise: if `ω₀` and `g₀`
are non-negative at `x − y` then `ω₀(x−y)·w_{1,B}(x,y) ≥ 0`.  (The kernel is
`χ_B(x)·((g₀(z)/C_{ℓd}(z))/convScale_ℓ(z))·χ_B(y)` and both renormalisation denominators are
non-negative — `conv3Small_nonneg'` and `convScale_nonneg` — so no diluteness is needed.) -/
lemma omega_mul_wSmall1Pair_nonneg {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {ℓ d : ℝ} {M : ℕ}
    (u : E3) {x y : E3} (hω : 0 ≤ (Classical.choose h) (x - y))
    (hg0 : 0 ≤ Submission.BoseGases.g0 v h (x - y)) :
    0 ≤ (Classical.choose h) (x - y) * Submission.BoseGases.wSmall1Pair h M ℓ d u x y := by
  have hχx : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u x
  have hχy : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u y :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u y
  have hcs : 0 ≤ Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y) := by
    rw [Submission.BoseGases.convScaleSmall]
    exact Work.BoseFixB1S.conv3Small_nonneg' M _
  have hcv : 0 ≤ Submission.BoseGases.convScale ℓ (x - y) :=
    Submission.BoseGases.convScale_nonneg ℓ (x - y)
  have hunfold : Submission.BoseGases.wSmall1Pair h M ℓ d u x y
      = Submission.BoseGases.chiSmallB M ℓ d u x
        * ((Submission.BoseGases.g0 v h (x - y) / Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y))
            / Submission.BoseGases.convScale ℓ (x - y))
        * Submission.BoseGases.chiSmallB M ℓ d u y := rfl
  rw [hunfold]
  exact mul_nonneg hω (mul_nonneg (mul_nonneg hχx (div_nonneg (div_nonneg hg0 hcs) hcv)) hχy)

/-! ## §3. The mass-difference bound -/

/-- **The `MΔ`-bound from the denominator lower bound** (the analytic core):

    boxM2 (B(u)) − boxM1 (B(u)) ≤ 4·(g₀ω₀-mass)·chiMass_{B(u)} .

`boxM2_sub_boxM1_eq_omegaMass` writes the difference as the box integral of
`ω₀(x−y)·w_{1,B}(x,y)`; the pointwise comparison above (a.e., using `0 ≤ ω₀ ≤ 1` and `g₀ ≥ 0`
a.e. from the scattering bounds) turns it into `4·∬χ(x)|(g₀ω₀)(x−y)|χ(y)`, AM–GM
(`pairing_le_chiSq_mul_abs_integral`) bounds that by `4·(∫χ²)·∫|g₀ω₀|`, and `g₀ω₀ ≥ 0` a.e.
identifies `∫|g₀ω₀|` with the `g₀ω₀`-mass. -/
theorem massDiff_le_four {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {R : ℝ}
    (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv1 : MeasureTheory.MemLp v 1)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {M : ℕ} (hM : 1 ≤ M) (u : E3)
    (hden : ∀ z : E3, ‖z‖ ≤ R → (1 / 4 : ℝ) ≤
      Submission.BoseGases.convScaleSmall M (ℓ * d) z * Submission.BoseGases.convScale ℓ z) :
    Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
      - Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Submission.BoseGases.wSmall1Pair h M ℓ d u)
    ≤ 4 * Submission.BoseGases.g0w0Mass h * Work.SmallBoxSliding.chiMass M ℓ d u := by
  classical
  have hId := Work.BoseFixB1B.boxM2_sub_boxM1_eq_omegaMass (v := v) (R0 := R) hv_supp hR hv hvrad
    hv1 h hM hℓ hd u
  have hIntG : Integrable (fun z : E3 => Submission.BoseGases.g0 v h z * Classical.choose h z) :=
    Submission.BoseGases.g0w0_integrable (v := v) (R := R) hR hv hvrad hv_supp h
  have hχ0 : ∀ x : E3, 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x :=
    fun x => Submission.BoseGases.chiSmallB_nonneg M ℓ d u x
  have hχc : Continuous (fun x : E3 => Submission.BoseGases.chiSmallB M ℓ d u x) :=
    Submission.BoseGases.chiSmallB_continuous hM hℓ hd u
  have hχs : HasCompactSupport (fun x : E3 => Submission.BoseGases.chiSmallB M ℓ d u x) :=
    Submission.BoseGases.chiSmallB_hasCompactSupport hM hℓ u
  have hpair := Work.BoseFixB1S.pairing_le_chiSq_mul_abs_integral
    (χ := fun x : E3 => Submission.BoseGases.chiSmallB M ℓ d u x)
    (f := fun z : E3 => Submission.BoseGases.g0 v h z * Classical.choose h z) hχ0 hχc hχs hIntG
  have hqmp : Measure.QuasiMeasurePreserving (fun p : E3 × E3 => p.1 - p.2)
      ((volume : Measure E3).prod (volume : Measure E3)) (volume : Measure E3) :=
    quasiMeasurePreserving_sub_of_right_invariant _ _
  have hωnn : ∀ᵐ z ∂(volume : Measure E3), 0 ≤ Classical.choose h z :=
    (Submission.BoseGases.scattering_bounds_ae (w := Classical.choose h) hR hv hvrad hv_supp
      (Classical.choose_spec h).1 (Classical.choose_spec h).2).1
  have hg0nn : ∀ᵐ z ∂(volume : Measure E3), 0 ≤ Submission.BoseGases.g0 v h z :=
    Submission.BoseGases.g0_nonneg_ae (R := R) hR hv hvrad hv_supp h
  have hωnnp : ∀ᵐ p ∂((volume : Measure E3).prod (volume : Measure E3)),
      0 ≤ Classical.choose h (p.1 - p.2) := hqmp.ae hωnn
  have hg0nnp : ∀ᵐ p ∂((volume : Measure E3).prod (volume : Measure E3)),
      0 ≤ Submission.BoseGases.g0 v h (p.1 - p.2) := hqmp.ae hg0nn
  have hg0supp : ∀ z : E3, R ≤ ‖z‖ → Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  have hcomp : (fun p : E3 × E3 =>
        Classical.choose h (p.1 - p.2) * Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2)
      ≤ᵐ[((volume : Measure E3).prod (volume : Measure E3))]
      (fun p : E3 × E3 => 4 * (Submission.BoseGases.chiSmallB M ℓ d u p.1
          * |Submission.BoseGases.g0 v h (p.1 - p.2) * Classical.choose h (p.1 - p.2)|
          * Submission.BoseGases.chiSmallB M ℓ d u p.2)) := by
    filter_upwards [hωnnp, hg0nnp] with p hpω hpg
    exact pair_le_four_of_denom_lower h u hden hg0supp hpω hpg
  have hF1nn : 0 ≤ᵐ[((volume : Measure E3).prod (volume : Measure E3))]
      (fun p : E3 × E3 =>
        Classical.choose h (p.1 - p.2) * Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2) := by
    filter_upwards [hωnnp, hg0nnp] with p hpω hpg
    exact omega_mul_wSmall1Pair_nonneg h u hpω hpg
  have hInt2 : Integrable (fun p : E3 × E3 => 4 * (Submission.BoseGases.chiSmallB M ℓ d u p.1
      * |Submission.BoseGases.g0 v h (p.1 - p.2) * Classical.choose h (p.1 - p.2)|
      * Submission.BoseGases.chiSmallB M ℓ d u p.2)) := hpair.1.const_mul 4
  have hGnn : 0 ≤ᵐ[(volume : Measure E3)]
      (fun z : E3 => Submission.BoseGases.g0 v h z * Classical.choose h z) := by
    filter_upwards [hg0nn, hωnn] with z h1 h2
    exact mul_nonneg h1 h2
  calc Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
          (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
        - Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Submission.BoseGases.wSmall1Pair h M ℓ d u)
      = ∫ p in Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u,
          Classical.choose h (p.1 - p.2) * Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2 := hId
    _ = ∫ p : E3 × E3,
          Classical.choose h (p.1 - p.2) * Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2 := by
        refine MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => ?_)
        have hp' : ¬ (p.1 ∈ Submission.BoseGases.dlBox ℓ d u
            ∧ p.2 ∈ Submission.BoseGases.dlBox ℓ d u) := fun hc => hp hc
        have hzero : Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2 = 0 := by
          by_cases h1 : p.1 ∈ Submission.BoseGases.dlBox ℓ d u
          · exact Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u
              (f := Submission.BoseGases.g0 v h) (Or.inr (fun h2 => hp' ⟨h1, h2⟩))
          · exact Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u
              (f := Submission.BoseGases.g0 v h) (Or.inl h1)
        rw [hzero, mul_zero]
    _ ≤ ∫ p : E3 × E3, 4 * (Submission.BoseGases.chiSmallB M ℓ d u p.1
          * |Submission.BoseGases.g0 v h (p.1 - p.2) * Classical.choose h (p.1 - p.2)|
          * Submission.BoseGases.chiSmallB M ℓ d u p.2) :=
        MeasureTheory.integral_mono_of_nonneg hF1nn hInt2 hcomp
    _ = 4 * ∫ p : E3 × E3, Submission.BoseGases.chiSmallB M ℓ d u p.1
          * |Submission.BoseGases.g0 v h (p.1 - p.2) * Classical.choose h (p.1 - p.2)|
          * Submission.BoseGases.chiSmallB M ℓ d u p.2 :=
        MeasureTheory.integral_const_mul 4 _
    _ ≤ 4 * ((∫ x : E3, (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2)
          * ∫ z : E3, |Submission.BoseGases.g0 v h z * Classical.choose h z|) :=
        mul_le_mul_of_nonneg_left hpair.2 (by norm_num)
    _ = 4 * Submission.BoseGases.g0w0Mass h * Work.SmallBoxSliding.chiMass M ℓ d u := by
        have habs : (∫ z : E3, |Submission.BoseGases.g0 v h z * Classical.choose h z|)
            = Submission.BoseGases.g0w0Mass h := by
          rw [MeasureTheory.integral_congr_ae (hGnn.mono (fun z hz => abs_of_nonneg hz))]
          rfl
        have hchimass : (∫ x : E3, (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2)
            = Work.SmallBoxSliding.chiMass M ℓ d u :=
          (Work.SmallBoxSliding.chiMass_def M ℓ d u).symm
        rw [hchimass, habs]
        ring

/-! ## §4. Non-negativity of the payer -/

/-- `0 ≤ g₀ω₀-mass`: the integrand is a.e. non-negative (`g₀ ≥ 0` from `scattering_g_nonneg`,
`ω₀ ≥ 0` from `scattering_bounds_ae`). -/
lemma g0w0Mass_nonneg' {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {R : ℝ} (hR : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) :
    0 ≤ Submission.BoseGases.g0w0Mass h := by
  have h1 : ∀ᵐ z ∂(volume : Measure E3), 0 ≤ Submission.BoseGases.g0 v h z :=
    Submission.BoseGases.g0_nonneg_ae (R := R) hR hv hvrad hv_supp h
  have h2 : ∀ᵐ z ∂(volume : Measure E3), 0 ≤ Classical.choose h z :=
    (Submission.BoseGases.scattering_bounds_ae (w := Classical.choose h) hR hv hvrad hv_supp
      (Classical.choose_spec h).1 (Classical.choose_spec h).2).1
  have h3 : 0 ≤ ∫ z : E3, Submission.BoseGases.g0 v h z * Classical.choose h z := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [h1, h2] with z hz1 hz2
    exact mul_nonneg hz1 hz2
  exact h3

/-! ## §5. The target -/

theorem massUpper {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseFixB1.MassUpper v h 16 := by
  -- the flatness constant of the `dℓ` self-convolution at `M = mValue`
  obtain ⟨L, hL1, hLdev⟩ :=
    conv3Small_dev_L2 (M := Work.BoseBox.mValue) (by norm_num [Work.BoseBox.mValue])
  set K : ℝ := 2 * L ^ 2 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  obtain ⟨ε₀, hε₀pos, hreg⟩ := regime_sideAt_ge_div (v := v) hav hR hKpos
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro μ hAdm u _hu
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hdil : μ * (_root_.BoseGases.a v) ^ 3 ≤ ε₀ := Work.BoseFixB1.adm_dilute hAdm
  obtain ⟨hRd, hRχ⟩ := hreg μ hμ hdil
  have hℓ : 0 < Work.BoseFixB1.bSide v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.bD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hMb : Work.BoseFixB1.bM v μ = Work.BoseBox.mValue := by
    rw [Work.BoseFixB1.bM]
    exact Work.BoseFixB1.M_eq_mValue μ (_root_.BoseGases.a v)
  have hM : 1 ≤ Work.BoseFixB1.bM v μ := by
    rw [hMb]; norm_num [Work.BoseBox.mValue]
  -- ### the denominator lower bound on `ball 0 R`
  have hdenM : ∀ z : E3, ‖z‖ ≤ R → (1 / 4 : ℝ) ≤
      Submission.BoseGases.convScaleSmall Work.BoseBox.mValue
        (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) z
      * Submission.BoseGases.convScale (Work.BoseFixB1.bSide v μ) z := by
    intro z hz
    set ℓ := Work.BoseFixB1.bSide v μ with hℓdef
    set d := Work.BoseFixB1.bD v μ with hddef
    have hℓd : 0 < ℓ * d := mul_pos hℓ hd
    have hℓinv : 0 ≤ (ℓ * d)⁻¹ := inv_nonneg.mpr hℓd.le
    -- the scaled point is in the `1/K`-ball
    have hzm : ‖(ℓ * d)⁻¹ • z‖ ≤ 1 / K := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hℓinv]
      have h1 : (ℓ * d)⁻¹ * ‖z‖ ≤ (ℓ * d)⁻¹ * R := mul_le_mul_of_nonneg_left hz hℓinv
      have h2 : (ℓ * d)⁻¹ * R ≤ (ℓ * d)⁻¹ * (ℓ * d / K) := mul_le_mul_of_nonneg_left hRd hℓinv
      have h3 : (ℓ * d)⁻¹ * (ℓ * d / K) = 1 / K := by field_simp
      linarith [h1, h2, h3]
    -- the flatness estimate at that point
    have hdev := hLdev ((ℓ * d)⁻¹ • z)
    have hle14 : L ^ 2 * ‖(ℓ * d)⁻¹ • z‖ ^ 2 ≤ 1 / 4 := by
      have hsq : ‖(ℓ * d)⁻¹ • z‖ ^ 2 ≤ (1 / K) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hzm 2
      have hstep : L ^ 2 * ‖(ℓ * d)⁻¹ • z‖ ^ 2 ≤ L ^ 2 * (1 / K) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (sq_nonneg L)
      have hval : L ^ 2 * (1 / K) ^ 2 = 1 / (4 * L ^ 2) := by
        rw [hKdef]; field_simp; ring
      have hL2 : (1 : ℝ) ≤ L ^ 2 := by nlinarith [hL1]
      have hfin : (1 : ℝ) / (4 * L ^ 2) ≤ 1 / 4 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith)
      linarith [hstep, hval ▸ le_refl (L ^ 2 * (1 / K) ^ 2), hfin]
    have hcs : (1 / 2 : ℝ) ≤ Submission.BoseGases.convScaleSmall Work.BoseBox.mValue (ℓ * d) z := by
      rw [Submission.BoseGases.convScaleSmall]
      have h4 : |Submission.BoseGases.conv3Small Work.BoseBox.mValue ((ℓ * d)⁻¹ • z) - 1| ≤ 1 / 4 :=
        le_trans hdev hle14
      have h5 := abs_le.mp h4
      linarith [h5.1, h5.2]
    have hcv : (1 / 2 : ℝ) ≤ Submission.BoseGases.convScale ℓ z :=
      Submission.BoseGases.convScale_ge_half_ball hℓ (le_of_lt hR) hRχ hz
    nlinarith [hcs, hcv]
  have hden : ∀ z : E3, ‖z‖ ≤ R → (1 / 4 : ℝ) ≤
      Submission.BoseGases.convScaleSmall (Work.BoseFixB1.bM v μ)
        (Work.BoseFixB1.bSide v μ * Work.BoseFixB1.bD v μ) z
      * Submission.BoseGases.convScale (Work.BoseFixB1.bSide v μ) z := by
    intro z hz
    rw [hMb]
    exact hdenM z hz
  -- ### the core bound
  have hcore := massDiff_le_four (v := v) h hR hv hvrad hv1 hv_supp hℓ hd hM u hden
  have hcore' : Work.BoseFixB1.bMDelta v h μ u ≤ 4 * Submission.BoseGases.g0w0Mass h
      * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
          (Work.BoseFixB1.bD v μ) u := by
    simpa only [Work.BoseFixB1.bMDelta, Work.BoseFixB1.bM2, Work.BoseFixB1.bM1,
      Work.BoseFixB1.bV, Work.BoseFixB1.bA] using hcore
  -- ### arithmetic
  have hDnn : 0 ≤ Submission.BoseGases.g0w0Mass h := g0w0Mass_nonneg' h hR hv hvrad hv_supp
  have hχnn : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseFixB1.bM v μ)
      (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hann : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  have h4 : 4 * Submission.BoseGases.g0w0Mass h * Work.SmallBoxSliding.chiMass
        (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u
      ≤ 17 * Submission.BoseGases.g0w0Mass h * Work.SmallBoxSliding.chiMass
        (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u := by
    nlinarith [hDnn, hχnn]
  have h16 : (0 : ℝ) ≤ 16 * (_root_.BoseGases.a v) * Work.SmallBoxSliding.chiMass
      (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ) (Work.BoseFixB1.bD v μ) u := by
    have := mul_nonneg hann hχnn
    linarith
  nlinarith [hcore', h4, h16]

end Work.BoseFixB1.MDelta
