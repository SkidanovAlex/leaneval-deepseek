import ChallengeDeps
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.fsRegimeAt
import Submission.Work.BoseFixB1.regime_sideAt_ge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.bandCostAbsorb`

The numerical absorption (†) of the band cost of the `I₋`-to-`ℝ³` bookkeeping
(consumed by `Work.BoseFixB1B.trimOffInterior`):

    C₁·(μ²(a v)·∫_{bandSet} χ_{B(u)}² + μ(a v)·|bandSet|)
      ≤ C·μ²(a v)ℓ³K_B³(μ(a v)³)^{1/2}

for all admissible `μ`, with `ε₀`, `C` depending only on `v` (through `a v`) and
`C₁`.

## Contents

* the two closed-form band identities `bandMassRatio` (`χ`-mass, exponent
  `27887/1938`) and `bandVolRatio` (Lebesgue volume, exponent `359/1938`),
  expressing the band averages in FS's monomials
  `d = (μA³)^{6/323}`, `K_B = (μA³)^{-6/323}`, `ℓ = A(μA³)^{-163/323}`;
* `tPowAbsorb` — the pure-arithmetic absorb
  `12(1+d)²2^{96}K_c t^{E₁} + 12(1+d)²t^{E₂} ≤ 1`;
* the theorem itself, with `ε₀ = min ε_regime ((48·2^{96}K_c+49)^{-1938/359})`
  and `C = |C₁|`.

Everything here is `sorry`-free and rests only on the corpus's closed bad-band
law (`SmallBoxSliding.bandSet_mass_integral_le_law`), the closed band-volume law
(`SmallBoxSliding.bandSet_measure_le`) and FS's parameter regime
(`BoseFixB1.fsRegimeAt`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open Work.BoseBox Work.BoseFixB1

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

/-! ## 0. Elementary algebra and `fsXp` bookkeeping -/

/-- `c * x / (c * y) = x / y` in a field. -/
lemma mul_div_mul_self {K : Type*} [Field K] (c x y : K) (h : c ≠ 0) :
    c * x / (c * y) = x / y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv_rev]
  calc c * x * (y⁻¹ * c⁻¹) = (c * c⁻¹) * (x * y⁻¹) := by ring
    _ = 1 * (x * y⁻¹) := by rw [mul_inv_cancel₀ h]
    _ = x * y⁻¹ := by ring

lemma fsXp_merge3 {t : ℝ} (ht : 0 < t) (a b c : ℝ) :
    fsXp t a * fsXp t b * fsXp t c = fsXp t (a + b + c) := by
  rw [fsXp_mul ht, fsXp_mul ht]

lemma fsXp_merge4 {t : ℝ} (ht : 0 < t) (a b c d : ℝ) :
    fsXp t a * fsXp t b * fsXp t c * fsXp t d = fsXp t (a + b + c + d) := by
  rw [fsXp_mul ht, fsXp_mul ht, fsXp_mul ht]

/-- `chiSmallBandDecay` at `M = 48` is the explicit monomial. -/
lemma chiSmallBandDecay_48 (d : ℝ) :
    Submission.BoseGases.chiSmallBandDecay 48 d
      = Submission.BoseGases.chiSupAbs ^ 2 * (Submission.BoseGases.chiSmallDecay 48) ^ 2
          * (d⁻¹) ^ 96 := rfl

/-- `(paramsAt μ A).d⁻¹ ^ 96 = (μA³)^{-576}`. -/
lemma d_inv_pow96 {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    ((paramsAt μ A).d)⁻¹ ^ 96 = fsXp (μ * A^3) (-576) := by
  have ht : 0 < μ * A^3 := by positivity
  rw [d_eq_fsXp, fsXp_inv ht, fsXp_pow ht.le]
  norm_num

/-- `(paramsAt μ A).d⁻¹ ^ 3 = (μA³)^{-18}`. -/
lemma d_inv_pow3 {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    ((paramsAt μ A).d)⁻¹ ^ 3 = fsXp (μ * A^3) (-18) := by
  have ht : 0 < μ * A^3 := by positivity
  rw [d_eq_fsXp, fsXp_inv ht, fsXp_pow ht.le]
  norm_num

/-- `μ^{-1/3} = A·(μA³)^{-1/3}`. -/
lemma mu_inv_third_closed {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    μ ^ (-1/3 : ℝ) = A * fsXp (μ * A^3) (-(323/3)) := by
  rw [show (-1/3 : ℝ) = -(1/3) by norm_num]
  exact mu_inv_third_eq hA hμ

/-- `ℓ² = A²·(μA³)^{-326}`. -/
lemma sideAt_sq_closed {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    (sideAt μ A)^2 = A^2 * fsXp (μ * A^3) (-326) := by
  have ht : 0 < μ * A^3 := by positivity
  rw [sideAt_eq_fsXp hA hμ, mul_pow, fsXp_pow ht.le]
  norm_num

/-- `ℓ³ = A³·(μA³)^{-489}`. -/
lemma sideAt_cube_closed {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    (sideAt μ A)^3 = A^3 * fsXp (μ * A^3) (-489) :=
  sideAt_cube_eq hA hμ

/-- `K_B³ = (μA³)^{-18}`. -/
lemma KB_cube_closed {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    (paramsAt μ A).KB ^ 3 = fsXp (μ * A^3) (-18) := by
  have ht : 0 < μ * A^3 := by positivity
  rw [KB_eq_fsXp, fsXp_pow ht.le]
  norm_num

/-- **The `A`-cancellation**: `μ^{-1/3}·ℓ⁻¹ = (μA³)^{166/3}`. -/
lemma mu_inv_third_mul_sideAt_inv {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    μ ^ (-1/3 : ℝ) * (sideAt μ A)⁻¹ = fsXp (μ * A^3) (166/3) := by
  have ht : 0 < μ * A^3 := by positivity
  rw [mu_inv_third_closed hA hμ, sideAt_eq_fsXp hA hμ, ← div_eq_mul_inv]
  rw [mul_div_mul_self A _ _ (ne_of_gt hA)]
  rw [div_eq_mul_inv, fsXp_inv ht, fsXp_mul ht]
  rw [show (-(323/3:ℝ) + -(-163)) = 166/3 by norm_num]

/-- The `96`-th power: `(μ^{-1/3}ℓ⁻¹)^{96} = (μA³)^{5312}`. -/
lemma mu_inv_third_mul_sideAt_inv_pow96 {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    (μ ^ (-1/3 : ℝ) * (sideAt μ A)⁻¹)^96 = fsXp (μ * A^3) 5312 := by
  have ht : 0 < μ * A^3 := by positivity
  rw [mu_inv_third_mul_sideAt_inv hA hμ, fsXp_pow ht.le]
  norm_num

/-! ## 1. The two closed-form band identities -/

/-- **The band `χ`-mass identity.**  At FS's parameters, with `A = a v` and
`t = μA³`,

    μ²A·(d⁻¹)^{96}·(μ^{-1/3}ℓ⁻¹)^{96}·μ^{-1/3}·ℓ²
      = (μ²Aℓ³K_B³t^{1/2})·t^{27887/1938} . -/
theorem bandMassRatio {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    μ ^ 2 * A * ((paramsAt μ A).d)⁻¹ ^ 96
        * (μ ^ (-1/3 : ℝ) * (sideAt μ A)⁻¹) ^ 96
        * μ ^ (-1/3 : ℝ) * (sideAt μ A) ^ 2
      = (μ ^ 2 * A * (sideAt μ A) ^ 3 * (paramsAt μ A).KB ^ 3
            * (μ * A ^ 3) ^ (1 / 2 : ℝ))
          * (μ * A ^ 3) ^ ((27887 : ℝ) / 1938) := by
  have ht : 0 < μ * A^3 := by positivity
  rw [d_inv_pow96 hA hμ, mu_inv_third_mul_sideAt_inv_pow96 hA hμ, mu_inv_third_closed hA hμ,
    sideAt_sq_closed hA hμ, sideAt_cube_closed hA hμ, KB_cube_closed hA hμ, half_eq_fsXp]
  rw [show (μ * A^3) ^ ((27887:ℝ)/1938) = fsXp (μ * A^3) (27887/6) by
        rw [show (27887:ℝ)/1938 = (27887/6)/323 by norm_num]; rfl]
  have hL : μ ^ 2 * A * fsXp (μ*A^3) (-576) * fsXp (μ*A^3) 5312
        * (A * fsXp (μ*A^3) (-(323/3))) * (A^2 * fsXp (μ*A^3) (-326))
      = μ ^ 2 * A^4 * (fsXp (μ*A^3) (-576) * fsXp (μ*A^3) 5312 * fsXp (μ*A^3) (-(323/3))
          * fsXp (μ*A^3) (-326)) := by ring
  have hR : (μ ^ 2 * A * (A^3 * fsXp (μ*A^3) (-489)) * fsXp (μ*A^3) (-18)
        * fsXp (μ*A^3) (323/2)) * fsXp (μ*A^3) (27887/6)
      = μ ^ 2 * A^4 * (fsXp (μ*A^3) (-489) * fsXp (μ*A^3) (-18)
          * fsXp (μ*A^3) (323/2) * fsXp (μ*A^3) (27887/6)) := by ring
  rw [hL, fsXp_merge4 ht, hR, fsXp_merge4 ht]
  rw [show (-576:ℝ) + 5312 + (-(323/3)) + (-326)
        = (-489:ℝ) + (-18) + 323/2 + 27887/6 by norm_num]

/-- **The band volume identity.**  At FS's parameters,

    μA·μ^{-1/3}ℓ⁻¹·(d⁻¹)³ = (μ²Aℓ³K_B³t^{1/2})·t^{359/1938} . -/
theorem bandVolRatio {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    μ * A * (μ ^ (-1/3 : ℝ) * (sideAt μ A)⁻¹) * ((paramsAt μ A).d)⁻¹ ^ 3
      = (μ ^ 2 * A * (sideAt μ A) ^ 3 * (paramsAt μ A).KB ^ 3
            * (μ * A ^ 3) ^ (1 / 2 : ℝ))
          * (μ * A ^ 3) ^ ((359 : ℝ) / 1938) := by
  have ht : 0 < μ * A^3 := by positivity
  rw [mu_inv_third_mul_sideAt_inv hA hμ, d_inv_pow3 hA hμ, sideAt_cube_closed hA hμ,
    KB_cube_closed hA hμ, half_eq_fsXp]
  rw [show (μ * A^3) ^ ((359:ℝ)/1938) = fsXp (μ * A^3) (359/6) by
        rw [show (359:ℝ)/1938 = (359/6)/323 by norm_num]; rfl]
  have hL : μ * A * fsXp (μ*A^3) (166/3) * fsXp (μ*A^3) (-18)
      = μ * A * (fsXp (μ*A^3) (166/3) * fsXp (μ*A^3) (-18)) := by ring
  have hR : μ ^ 2 * A * (A^3 * fsXp (μ*A^3) (-489)) * fsXp (μ*A^3) (-18)
        * fsXp (μ*A^3) (323/2) * fsXp (μ*A^3) (359/6)
      = μ ^ 2 * A^4 * (fsXp (μ*A^3) (-489) * fsXp (μ*A^3) (-18) * fsXp (μ*A^3) (323/2)
          * fsXp (μ*A^3) (359/6)) := by ring
  rw [hL, fsXp_mul ht, hR, fsXp_merge4 ht]
  rw [show (166/3:ℝ) + -18 = 112/3 by norm_num]
  have hkey : fsXp (μ * A^3) 323 * fsXp (μ * A^3) ((-489) + (-18) + 323/2 + 359/6)
      = fsXp (μ * A^3) (112/3) := by
    rw [fsXp_mul ht]
    rw [show (323:ℝ) + ((-489) + (-18) + 323/2 + 359/6) = 112/3 by norm_num]
  rw [← hkey, fsXp_323 (μ * A^3)]
  rw [show μ ^ 2 * A ^ 4 = μ * A * (μ * A ^ 3) by ring]
  ring

/-! ## 2. The pure-arithmetic absorb -/

/-- **The absorb.**  For `0 < t ≤ 1`, `0 ≤ d ≤ 1`, `K_c ≥ 0` and
`t ≤ (48·2^{96}K_c + 49)^{-1938/359}`,

    12(1+d)²2^{96}K_c t^{27887/1938} + 12(1+d)²t^{359/1938} ≤ 1 . -/
theorem tPowAbsorb {t d Kc : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hKc : 0 ≤ Kc) (htnew : t ≤ (48 * 2^96 * Kc + 48 + 1) ^ (-(1938/359 : ℝ))) :
    12 * (1 + d)^2 * 2^96 * Kc * t ^ ((27887:ℝ)/1938)
      + 12 * (1 + d)^2 * t ^ ((359:ℝ)/1938) ≤ 1 := by
  set aa : ℝ := 48 * 2^96 * Kc + 48 + 1 with haadef
  have h2p : (0:ℝ) < 2^96 := by positivity
  have haa : 0 < aa := by rw [haadef]; linarith [hKc, h2p]
  have h12 : 12 * (1 + d)^2 ≤ 48 := by nlinarith
  have htE1 : t ^ ((27887:ℝ)/1938) ≤ t ^ ((359:ℝ)/1938) :=
    Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by norm_num)
  have htE2 : t ^ ((359:ℝ)/1938) ≤ (aa ^ (-(1938/359 : ℝ))) ^ ((359:ℝ)/1938) :=
    Real.rpow_le_rpow (le_of_lt ht0) htnew (by norm_num)
  have haapow : (aa ^ (-(1938/359 : ℝ))) ^ ((359:ℝ)/1938) = aa⁻¹ := by
    rw [← Real.rpow_mul (le_of_lt haa)]
    rw [show (-(1938/359:ℝ)) * (359/1938) = -1 by norm_num, Real.rpow_neg_one]
  have htE2' : t ^ ((359:ℝ)/1938) ≤ aa⁻¹ := by rw [← haapow]; exact htE2
  have h1 : 12 * (1 + d)^2 * 2^96 * Kc * t ^ ((27887:ℝ)/1938)
      ≤ 48 * 2^96 * Kc * t ^ ((359:ℝ)/1938) := by
    have hb : 12 * (1 + d)^2 * 2^96 * Kc ≤ 48 * 2^96 * Kc := by
      have h1' : 12 * (1 + d)^2 * 2^96 ≤ 48 * 2^96 :=
        mul_le_mul_of_nonneg_right h12 (le_of_lt h2p)
      exact mul_le_mul_of_nonneg_right h1' hKc
    exact mul_le_mul hb htE1 (Real.rpow_nonneg (le_of_lt ht0) _)
      (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt h2p)) hKc)
  have h2 : 12 * (1 + d)^2 * t ^ ((359:ℝ)/1938) ≤ 48 * t ^ ((359:ℝ)/1938) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (le_of_lt ht0) _)
  have h3 : 48 * 2^96 * Kc * t ^ ((359:ℝ)/1938) + 48 * t ^ ((359:ℝ)/1938)
      = (48 * 2^96 * Kc + 48) * t ^ ((359:ℝ)/1938) := by ring
  have h4 : (48 * 2^96 * Kc + 48) * t ^ ((359:ℝ)/1938) ≤ 1 := by
    have h7 : (48 * 2^96 * Kc + 48) = aa - 1 := by rw [haadef]; ring
    have h8 : aa - 1 ≤ aa := by linarith
    calc (48 * 2^96 * Kc + 48) * t ^ ((359:ℝ)/1938)
        = (aa - 1) * t ^ ((359:ℝ)/1938) := by rw [h7]
      _ ≤ (aa - 1) * aa⁻¹ := mul_le_mul_of_nonneg_left htE2' (by linarith)
      _ ≤ 1 := by
          have h9 : (aa - 1) * aa⁻¹ ≤ aa * aa⁻¹ :=
            mul_le_mul_of_nonneg_right h8 (inv_nonneg.mpr (le_of_lt haa))
          rw [mul_inv_cancel₀ (ne_of_gt haa)] at h9
          exact h9
  linarith [h1, h2, h3.le, h4]

/-! ## 3. The theorem -/

theorem bandCostAbsorb {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (C₁ : ℝ) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      C₁ * (μ ^ 2 * (_root_.BoseGases.a v)
              * (∫ u in Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
                    Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
            + μ * (_root_.BoseGases.a v)
              * (MeasureTheory.volume (Work.SmallBoxSliding.bandSet
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal)
        ≤ C * (μ ^ 2 * (_root_.BoseGases.a v) * Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ^ 3
                * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) := by
  obtain ⟨εreg, hεreg, hreg⟩ :=
    fsRegimeAt (A := _root_.BoseGases.a v) (R := R) hav hR
  -- the arithmetic constant of the absorb
  set Kc : ℝ := Submission.BoseGases.chiSupAbs ^ 2 * (Submission.BoseGases.chiSmallDecay 48) ^ 2
    with hKcdef
  have hKc : 0 ≤ Kc := by
    rw [hKcdef]
    exact mul_nonneg (pow_nonneg Submission.BoseGases.chiSupAbs_nonneg 2)
      (pow_nonneg (Submission.BoseGases.chiSmallDecay_nonneg 48) 2)
  set εnew : ℝ := (48 * 2^96 * Kc + 48 + 1) ^ (-(1938/359 : ℝ)) with hεnewdef
  have hone : (1 : ℝ) ≤ 48 * 2^96 * Kc + 48 + 1 := by
    have h2p : (0:ℝ) ≤ 2^96 := by positivity
    have h : 0 ≤ 48 * 2^96 * Kc := mul_nonneg (mul_nonneg (by norm_num) h2p) hKc
    linarith
  have hεnew_pos : 0 < εnew := by
    rw [hεnewdef]
    exact Real.rpow_pos_of_pos (by linarith) _
  have hεnew_le1 : εnew ≤ 1 := by
    rw [hεnewdef]
    exact Real.rpow_le_one_of_one_le_of_nonpos hone (by norm_num)
  refine ⟨min εreg εnew, |C₁|, lt_min hεreg hεnew_pos, abs_nonneg C₁, ?_⟩
  intro μ hAdm
  have hμ : 0 < μ := hAdm.1
  have ha : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
  have ht_reg : μ * (_root_.BoseGases.a v) ^ 3 ≤ εreg := le_trans hAdm.2.1 (min_le_left _ _)
  have ht_new : μ * (_root_.BoseGases.a v) ^ 3 ≤ εnew := le_trans hAdm.2.1 (min_le_right _ _)
  obtain ⟨-, -, -, -, -, -, -, -, -, hAδ, -⟩ := hreg μ hμ ht_reg
  have hAδ' : 0 ≤ (1 / 2) * sideAt μ (_root_.BoseGases.a v)
      * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) - 2 * μ ^ (-1 / 3 : ℝ) := by
    have h1 : (-1 / 3 : ℝ) = -(1 / 3) := by norm_num
    rw [h1]
    exact hAδ
  have ht0 : 0 < μ * (_root_.BoseGases.a v) ^ 3 := mul_pos hμ (pow_pos hav 3)
  have ht1 : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 := le_trans ht_new hεnew_le1
  have hℓ : 0 < sideAt μ (_root_.BoseGases.a v) := adm_ell_pos hAdm
  have hdpos : 0 < (paramsAt μ (_root_.BoseGases.a v)).d := adm_d_pos hAdm
  have hdle1 : (paramsAt μ (_root_.BoseGases.a v)).d ≤ 1 := by
    rw [d_eq_fsXp]
    exact fsXp_le_one ht0 ht1 (by norm_num)
  have hM48 : (paramsAt μ (_root_.BoseGases.a v)).M = 48 := by
    rw [M_eq_mValue]
    rfl
  rw [hM48]
  -- the mass factor after splitting off the `2^96`
  have hYpos : 0 < (μ * (_root_.BoseGases.a v) ^ 3) ^ (16:ℝ)
      * (sideAt μ (_root_.BoseGases.a v)) ^ 3 :=
    mul_pos (Real.rpow_pos_of_pos (mul_pos hμ (pow_pos hav 3)) _) (pow_pos hℓ 3)
  have hYne : (μ * (_root_.BoseGases.a v) ^ 3) ^ (16:ℝ) * (sideAt μ (_root_.BoseGases.a v)) ^ 3
      ≠ 0 := ne_of_gt hYpos
  have hXsplit : (2 * μ ^ (-1/3 : ℝ) / sideAt μ (_root_.BoseGases.a v)) ^ 96
        * μ ^ (-1/3 : ℝ) * (sideAt μ (_root_.BoseGases.a v)) ^ 2
      = 2 ^ 96 * ((μ ^ (-1/3 : ℝ) * (sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 96
          * μ ^ (-1/3 : ℝ) * (sideAt μ (_root_.BoseGases.a v)) ^ 2) := by
    rw [div_eq_mul_inv, mul_pow, mul_pow, ← mul_pow]
    ring
  -- the `χ`-mass bound from the closed bad-band law
  set C1' : ℝ := ((2 * μ ^ (-1/3 : ℝ) / sideAt μ (_root_.BoseGases.a v)) ^ 96
          * μ ^ (-1/3 : ℝ) * (sideAt μ (_root_.BoseGases.a v)) ^ 2)
        / ((μ * (_root_.BoseGases.a v) ^ 3) ^ (16:ℝ) * (sideAt μ (_root_.BoseGases.a v)) ^ 3)
    with hC1'def
  have hC1'nonneg : 0 ≤ C1' := by
    rw [hC1'def]
    refine div_nonneg ?_ ?_
    · exact mul_nonneg (mul_nonneg
        (pow_nonneg (div_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (le_of_lt hμ) _))
          (le_of_lt hℓ)) 96) (Real.rpow_nonneg (le_of_lt hμ) _)) (sq_nonneg _)
    · exact mul_nonneg (Real.rpow_nonneg (mul_nonneg (le_of_lt hμ) (pow_nonneg ha 3)) _)
        (pow_nonneg (le_of_lt hℓ) 3)
  have hEst : (2 * μ ^ (-1/3 : ℝ) / sideAt μ (_root_.BoseGases.a v)) ^ (96 : ℕ)
        * μ ^ (-1/3 : ℝ) * (sideAt μ (_root_.BoseGases.a v)) ^ 2
      ≤ C1' * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((↑(48:ℕ) : ℝ) / 3)
          * (sideAt μ (_root_.BoseGases.a v)) ^ 3 := by
    have h16 : ((↑(48:ℕ) : ℝ) / 3) = 16 := by norm_num
    have hkey : C1' * (μ * (_root_.BoseGases.a v) ^ 3) ^ (16:ℝ)
          * (sideAt μ (_root_.BoseGases.a v)) ^ 3
        = (2 * μ ^ (-1/3 : ℝ) / sideAt μ (_root_.BoseGases.a v)) ^ 96
            * μ ^ (-1/3 : ℝ) * (sideAt μ (_root_.BoseGases.a v)) ^ 2 := by
      rw [hC1'def]
      field_simp
    rw [h16, hkey]
  have hIraw := Work.SmallBoxSliding.bandSet_mass_integral_le_law (M := 48) (by norm_num)
    hℓ hdpos hμ ha hC1'nonneg hAδ' hEst
  have hI : (∫ u in Work.SmallBoxSliding.bandSet (sideAt μ (_root_.BoseGases.a v))
          (paramsAt μ (_root_.BoseGases.a v)).d μ,
          Work.SmallBoxSliding.chiMass 48 (sideAt μ (_root_.BoseGases.a v))
            (paramsAt μ (_root_.BoseGases.a v)).d u)
      ≤ 12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
          * Submission.BoseGases.chiSmallBandDecay 48 (paramsAt μ (_root_.BoseGases.a v)).d
          * (2 ^ 96 * ((μ ^ (-1/3 : ℝ) * (sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 96
              * μ ^ (-1/3 : ℝ) * (sideAt μ (_root_.BoseGases.a v)) ^ 2)) := by
    refine le_trans hIraw (le_of_eq ?_)
    have h16 : ((↑(48:ℕ) : ℝ) / 3) = 16 := by norm_num
    rw [h16, hC1'def, hXsplit]
    field_simp
  -- the volume bound
  have hV : (MeasureTheory.volume (Work.SmallBoxSliding.bandSet
          (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal
      ≤ ((sideAt μ (_root_.BoseGases.a v) * (paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹
          * (12 * μ ^ (-1/3 : ℝ) * (sideAt μ (_root_.BoseGases.a v)) ^ 2
              * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2) :=
    Work.SmallBoxSliding.bandSet_measure_le hℓ hdpos hμ hAδ'
  -- the two ratio rewrites
  have hmass := bandMassRatio (A := _root_.BoseGases.a v) (μ := μ) hav hμ
  have hvol := bandVolRatio (A := _root_.BoseGases.a v) (μ := μ) hav hμ
  -- (1) the `χ`-mass term
  have hstep1 : μ ^ 2 * (_root_.BoseGases.a v)
        * (12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
            * Submission.BoseGases.chiSmallBandDecay 48 (paramsAt μ (_root_.BoseGases.a v)).d
            * (2 ^ 96 * ((μ ^ (-1/3 : ℝ) * (sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 96
                * μ ^ (-1/3 : ℝ) * (sideAt μ (_root_.BoseGases.a v)) ^ 2)))
      = (12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2 * 2 ^ 96 * Kc
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((27887:ℝ)/1938))
          * (μ ^ 2 * (_root_.BoseGases.a v) * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) := by
    rw [chiSmallBandDecay_48]
    rw [show (12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2 * 2 ^ 96 * Kc
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((27887:ℝ)/1938))
          * (μ ^ 2 * (_root_.BoseGases.a v) * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
        = (12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2 * 2 ^ 96 * Kc)
          * ((μ ^ 2 * (_root_.BoseGases.a v) * (sideAt μ (_root_.BoseGases.a v)) ^ 3
                * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((27887:ℝ)/1938)) by ring]
    rw [← hmass]
    rw [hKcdef]
    ring
  -- (2) the volume term
  have hstep2 : μ * (_root_.BoseGases.a v)
        * (((sideAt μ (_root_.BoseGases.a v) * (paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹
          * (12 * μ ^ (-1/3 : ℝ) * (sideAt μ (_root_.BoseGases.a v)) ^ 2
              * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2))
      = (12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((359:ℝ)/1938))
          * (μ ^ 2 * (_root_.BoseGases.a v) * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) := by
    rw [show (12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
          * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((359:ℝ)/1938))
          * (μ ^ 2 * (_root_.BoseGases.a v) * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
        = 12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
          * ((μ ^ 2 * (_root_.BoseGases.a v) * (sideAt μ (_root_.BoseGases.a v)) ^ 3
                * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((359:ℝ)/1938)) by ring]
    rw [← hvol]
    field_simp
  -- (3) the arithmetic absorb
  have habsorb : 12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2 * 2 ^ 96 * Kc
        * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((27887:ℝ)/1938)
      + 12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
        * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((359:ℝ)/1938) ≤ 1 :=
    tPowAbsorb ht0 ht1 (le_of_lt hdpos) hdle1 hKc ht_new
  -- (4) assembly
  have hKBpos : 0 < (paramsAt μ (_root_.BoseGases.a v)).KB := paramsAt_KB_pos hAdm
  have hRHSnn : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v) * (sideAt μ (_root_.BoseGases.a v)) ^ 3
      * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
      * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha)
      (pow_nonneg (le_of_lt hℓ) 3)) (pow_nonneg (le_of_lt hKBpos) 3))
      (Real.rpow_nonneg (le_of_lt ht0) _)
  have hInn : 0 ≤ ∫ u in Work.SmallBoxSliding.bandSet (sideAt μ (_root_.BoseGases.a v))
        (paramsAt μ (_root_.BoseGases.a v)).d μ,
        Work.SmallBoxSliding.chiMass 48 (sideAt μ (_root_.BoseGases.a v))
          (paramsAt μ (_root_.BoseGases.a v)).d u :=
    integral_nonneg fun u => Work.SmallBoxSliding.chiMass_nonneg 48 _ _ u
  have hVnn : 0 ≤ (MeasureTheory.volume (Work.SmallBoxSliding.bandSet
        (sideAt μ (_root_.BoseGases.a v)) (paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal :=
    ENNReal.toReal_nonneg
  have hbrnn : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v)
        * (∫ u in Work.SmallBoxSliding.bandSet (sideAt μ (_root_.BoseGases.a v))
              (paramsAt μ (_root_.BoseGases.a v)).d μ,
              Work.SmallBoxSliding.chiMass 48 (sideAt μ (_root_.BoseGases.a v))
                (paramsAt μ (_root_.BoseGases.a v)).d u)
      + μ * (_root_.BoseGases.a v)
        * (MeasureTheory.volume (Work.SmallBoxSliding.bandSet
              (sideAt μ (_root_.BoseGases.a v))
              (paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal :=
    add_nonneg (mul_nonneg (by positivity) hInn) (mul_nonneg (by positivity) hVnn)
  have hI1 : μ ^ 2 * (_root_.BoseGases.a v)
        * (∫ u in Work.SmallBoxSliding.bandSet (sideAt μ (_root_.BoseGases.a v))
              (paramsAt μ (_root_.BoseGases.a v)).d μ,
              Work.SmallBoxSliding.chiMass 48 (sideAt μ (_root_.BoseGases.a v))
                (paramsAt μ (_root_.BoseGases.a v)).d u)
      ≤ (12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2 * 2 ^ 96 * Kc
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((27887:ℝ)/1938))
          * (μ ^ 2 * (_root_.BoseGases.a v) * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) := by
    calc μ ^ 2 * (_root_.BoseGases.a v)
          * (∫ u in Work.SmallBoxSliding.bandSet (sideAt μ (_root_.BoseGases.a v))
                (paramsAt μ (_root_.BoseGases.a v)).d μ,
                Work.SmallBoxSliding.chiMass 48 (sideAt μ (_root_.BoseGases.a v))
                  (paramsAt μ (_root_.BoseGases.a v)).d u)
        ≤ μ ^ 2 * (_root_.BoseGases.a v)
            * (12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
                * Submission.BoseGases.chiSmallBandDecay 48 (paramsAt μ (_root_.BoseGases.a v)).d
                * (2 ^ 96 * ((μ ^ (-1/3 : ℝ) * (sideAt μ (_root_.BoseGases.a v))⁻¹) ^ 96
                    * μ ^ (-1/3 : ℝ) * (sideAt μ (_root_.BoseGases.a v)) ^ 2))) :=
          mul_le_mul_of_nonneg_left hI (by positivity)
      _ = _ := hstep1
  have hV1 : μ * (_root_.BoseGases.a v)
        * (MeasureTheory.volume (Work.SmallBoxSliding.bandSet (sideAt μ (_root_.BoseGases.a v))
              (paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal
      ≤ (12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((359:ℝ)/1938))
          * (μ ^ 2 * (_root_.BoseGases.a v) * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) := by
    calc μ * (_root_.BoseGases.a v)
          * (MeasureTheory.volume (Work.SmallBoxSliding.bandSet (sideAt μ (_root_.BoseGases.a v))
                (paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal
        ≤ μ * (_root_.BoseGases.a v)
            * (((sideAt μ (_root_.BoseGases.a v) * (paramsAt μ (_root_.BoseGases.a v)).d) ^ 3)⁻¹
              * (12 * μ ^ (-1/3 : ℝ) * (sideAt μ (_root_.BoseGases.a v)) ^ 2
                  * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2)) :=
          mul_le_mul_of_nonneg_left hV (by positivity)
      _ = _ := hstep2
  have hsum : μ ^ 2 * (_root_.BoseGases.a v)
        * (∫ u in Work.SmallBoxSliding.bandSet (sideAt μ (_root_.BoseGases.a v))
              (paramsAt μ (_root_.BoseGases.a v)).d μ,
              Work.SmallBoxSliding.chiMass 48 (sideAt μ (_root_.BoseGases.a v))
                (paramsAt μ (_root_.BoseGases.a v)).d u)
      + μ * (_root_.BoseGases.a v)
        * (MeasureTheory.volume (Work.SmallBoxSliding.bandSet (sideAt μ (_root_.BoseGases.a v))
              (paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal
      ≤ (12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2 * 2 ^ 96 * Kc
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((27887:ℝ)/1938)
          + 12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((359:ℝ)/1938))
          * (μ ^ 2 * (_root_.BoseGases.a v) * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) := by
    have hEq : (12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2 * 2 ^ 96 * Kc
          * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((27887:ℝ)/1938))
          * (μ ^ 2 * (_root_.BoseGases.a v) * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
        + (12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((359:ℝ)/1938))
          * (μ ^ 2 * (_root_.BoseGases.a v) * (sideAt μ (_root_.BoseGases.a v)) ^ 3
              * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
        = (12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2 * 2 ^ 96 * Kc
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((27887:ℝ)/1938)
            + 12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((359:ℝ)/1938))
            * (μ ^ 2 * (_root_.BoseGases.a v) * (sideAt μ (_root_.BoseGases.a v)) ^ 3
                * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) := by ring
    linarith [hI1, hV1, hEq]
  have hfinal : (12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2 * 2 ^ 96 * Kc
          * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((27887:ℝ)/1938)
        + 12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
          * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((359:ℝ)/1938))
        * (μ ^ 2 * (_root_.BoseGases.a v) * (sideAt μ (_root_.BoseGases.a v)) ^ 3
            * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
      ≤ (μ ^ 2 * (_root_.BoseGases.a v) * (sideAt μ (_root_.BoseGases.a v)) ^ 3
            * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) := by
    have h := mul_le_mul_of_nonneg_right habsorb hRHSnn
    simpa using h
  calc C₁ * (μ ^ 2 * (_root_.BoseGases.a v)
          * (∫ u in Work.SmallBoxSliding.bandSet (sideAt μ (_root_.BoseGases.a v))
                (paramsAt μ (_root_.BoseGases.a v)).d μ,
                Work.SmallBoxSliding.chiMass 48 (sideAt μ (_root_.BoseGases.a v))
                  (paramsAt μ (_root_.BoseGases.a v)).d u)
        + μ * (_root_.BoseGases.a v)
          * (MeasureTheory.volume (Work.SmallBoxSliding.bandSet (sideAt μ (_root_.BoseGases.a v))
                (paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal)
      ≤ |C₁| * (μ ^ 2 * (_root_.BoseGases.a v)
          * (∫ u in Work.SmallBoxSliding.bandSet (sideAt μ (_root_.BoseGases.a v))
                (paramsAt μ (_root_.BoseGases.a v)).d μ,
                Work.SmallBoxSliding.chiMass 48 (sideAt μ (_root_.BoseGases.a v))
                  (paramsAt μ (_root_.BoseGases.a v)).d u)
        + μ * (_root_.BoseGases.a v)
          * (MeasureTheory.volume (Work.SmallBoxSliding.bandSet (sideAt μ (_root_.BoseGases.a v))
                (paramsAt μ (_root_.BoseGases.a v)).d μ)).toReal) :=
        mul_le_mul_of_nonneg_right (le_abs_self C₁) hbrnn
    _ ≤ |C₁| * ((12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2 * 2 ^ 96 * Kc
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((27887:ℝ)/1938)
            + 12 * (1 + (paramsAt μ (_root_.BoseGases.a v)).d) ^ 2
              * (μ * (_root_.BoseGases.a v) ^ 3) ^ ((359:ℝ)/1938))
            * (μ ^ 2 * (_root_.BoseGases.a v) * (sideAt μ (_root_.BoseGases.a v)) ^ 3
                * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum (abs_nonneg C₁)
    _ ≤ |C₁| * (μ ^ 2 * (_root_.BoseGases.a v) * (sideAt μ (_root_.BoseGases.a v)) ^ 3
                * (paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hfinal (abs_nonneg C₁)

end Work.BoseFixB1B
