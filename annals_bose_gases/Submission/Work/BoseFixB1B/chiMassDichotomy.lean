import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.SmallBoxSliding.Sliding
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.chiMassDichotomy` — the sliding-box `χ`-mass on the deep interior

Written by the holder of `Submission/Work/BoseFixB1B/lowCountBound.lean`.

## Why

`Work.SmallBoxSliding.chiMass M ℓ d u = ∫_x χ_{B(u)}(x)² dx` is the **same** factor that
appears in every data law of the per-box / per-sector chapter: it normalises the smooth density
`t = nCountB / chiMass` (`PerBoxF`, `SectorSmoothIneq`, `RPsiB`), it is the measure in the error
bracket `bErr = μ²(a v)Γ chiMass + μ(a v)`, and it enters the mass laws (`w1MassB`).  The
*interiority dichotomy* for `chiMass` — "comparable to the box volume on the deep interior,
degenerate in the shell" — is therefore the factor every such law is stated modulo, and it is
recorded as the missing item 3 in `FINDING_perSectorSmoothHighDens_s3.md` §6.

The `χ` here is the corpus `ContDiffBump`-based `Submission.BoseGases.chi`: a
`ContDiffBump (0 : ℝ³)` with `rIn = 1/4`, `rOut = 1/2`, normalised so `∫χ² = 1`
(`Submission/CubicChi.lean`), scaled by `chiScale ℓ x = χ(ℓ⁻¹ • x)`.  The small-box factor is the
explicit cosine bump `chiSmall M` (`∫chiSmall M² = 1`, `chiSmall_L2`).

Because `chiBump.rIn = 1/4` (`chiBase_eq_one_of_norm_le`) and `chiSmall M` is supported in
`[-1/2,1/2]³` (`chiSmallBase_support_mem_abs_le`), the dichotomy is **exact** and its thresholds
are `1/4` and `1/2`:

* `chiMass M ℓ d u = chiSupAbs² · (ℓd)³` whenever `‖d • u‖ + √3 d/2 ≤ 1/4`
  (`chiMass_eq_deep`);
* `chiMass M ℓ d u = 0` whenever `1/2 + √3 d/2 ≤ ‖d • u‖` (`chiMass_eq_zero_of_far`);
* in between, `chiMass M ℓ d u ≤ chiSupAbs² (ℓd)³` (`chiMass_le_sup`).

(Note in particular that the natural guess "`chiMass ≍ V` for `d‖u‖_∞ ≤ 1/2 − δ`" is *not*
available as stated: at `‖d • u‖ ≥ 1/2` the `ℓ`-scale factor already vanishes identically, because
`χ`'s support is the **ball** of radius `1/2`, not the cube.  The correct interior threshold is
`rIn = 1/4`, and the collision point is `1/2`.)

## Contents

* `chiSmall_ne_zero_coord` — support of the small-box factor, coordinatewise;
* `norm_le_sqrt_three_div_two` — `‖z‖ ≤ √3/2` for a point of the unit cube;
* `chi_eq_chiSupAbs_of_chiBase_eq_one` — `χ = chiSupAbs` where `chiBase = 1`;
* `integrable_chiSmall_sq` — `(χ_M)²` is integrable;
* `integral_chiSmall_rescale_sub` — the **exact** rescaled/translated `χ_M`-mass `= c³`
  (the companion of `integral_chiScale_sub_sq_eq_one`);
* `chiMass_eq_scaled` — the **exact change of variables**
  `chiMass M ℓ d u = (ℓd)³ ∫_z χ(d • (z + u))² χ_M(z)²`;
* `chiMass_le_sup`, `chiMass_eq_deep`, `chiMass_eq_zero_of_far` — the dichotomy.

All declarations are axiom-clean (`#print axioms` = propext, Classical.choice, Quot.sound).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.SmallBoxSliding

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## §0  Elementary facts about the two bumps and the scaling -/

/-- The small-box factor vanishes off the unit cube: `χ_M(z) ≠ 0` forces `|z_j| ≤ 1/2`. -/
lemma chiSmall_ne_zero_coord {M : ℕ} (hM : 1 ≤ M) {z : E3} (hz : chiSmall M z ≠ 0) (j : Fin 3) :
    |z j| ≤ 1 / 2 := by
  have hb : chiSmallBase M z ≠ 0 := by
    intro h
    exact hz (by simp [chiSmall, h])
  simpa using chiSmallBase_support_mem_abs_le hM hb j

/-- A point of the unit cube has norm at most `√3/2`. -/
lemma norm_le_sqrt_three_div_two {z : E3} (hz : ∀ j : Fin 3, |z j| ≤ 1 / 2) :
    ‖z‖ ≤ Real.sqrt 3 / 2 := by
  have h2 : ‖z‖ ^ 2 ≤ (Real.sqrt 3 / 2) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hsum : ∑ j : Fin 3, (z j) ^ 2 ≤ ∑ _j : Fin 3, ((1 : ℝ) / 2) ^ 2 :=
      Finset.sum_le_sum fun j _ => by
        rw [sq_le_sq, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        exact hz j
    calc ∑ j : Fin 3, (z j) ^ 2 ≤ ∑ _j : Fin 3, ((1 : ℝ) / 2) ^ 2 := hsum
      _ = 3 * ((1 : ℝ) / 2) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num
      _ = (Real.sqrt 3 / 2) ^ 2 := by
            rw [div_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
  have h := sq_le_sq.mp h2
  rwa [abs_of_nonneg (norm_nonneg z),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 3 / 2)] at h

/-- `chiSupAbs = (√chiNormSq)⁻¹` and `χ(v) = chiSupAbs` as soon as `chiBase v = 1`. -/
lemma chi_eq_chiSupAbs_of_chiBase_eq_one {v : E3} (hv : chiBase v = 1) :
    chi v = chiSupAbs := by
  rw [chi, hv, one_div, chiSupAbs]

/-- `(χ_M)²` is integrable (continuous, compactly supported). -/
lemma integrable_chiSmall_sq {M : ℕ} (hM : 1 ≤ M) :
    Integrable (fun z : E3 => (chiSmall M z) ^ 2) := by
  have hmain : Integrable (fun z : E3 => chiSmall M z * chiSmall M z) :=
    ((chiSmall_continuous hM).mul (chiSmall_continuous hM)).integrable_of_hasCompactSupport
      (HasCompactSupport.mul_right (f' := chiSmall M) (chiSmall_hasCompactSupport hM))
  refine hmain.congr (Filter.Eventually.of_forall fun z => ?_)
  ring

/-- `c • (c⁻¹ • x) = x`. -/
lemma smul_smul_inv_cancel {c : ℝ} (hc : c ≠ 0) (x : E3) : c • (c⁻¹ • x) = x := by
  rw [smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- `c⁻¹ • (c • x) = x`. -/
lemma smul_inv_smul_cancel {c : ℝ} (hc : c ≠ 0) (x : E3) : c⁻¹ • (c • x) = x := by
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul]

/-- `ℓ⁻¹ • ((ℓ * d) • w) = d • w`. -/
lemma inv_smul_smul_mul {ℓ d : ℝ} (hℓ : ℓ ≠ 0) (w : E3) : ℓ⁻¹ • ((ℓ * d) • w) = d • w := by
  rw [smul_smul, ← mul_assoc, inv_mul_cancel₀ hℓ, one_mul]

/-! ## §1  The exact rescaled/translated `χ_M`-mass -/

/-- **`∫_x χ_M(c⁻¹ • x − u)² dx = c³`** — the rescaled-and-translated `χ_M`-mass is exactly the
scaling volume.  (Companion of `integral_chiScale_sub_sq_eq_one`: the cosine bump is
`L²`-normalised, `chiSmall_L2`.)

Proof: translate by `c • u`, then apply the Haar rescaling
`Measure.integral_comp_inv_smul_of_nonneg` with `finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3`. -/
lemma integral_chiSmall_rescale_sub {M : ℕ} (hM : 1 ≤ M) {c : ℝ} (hc : 0 < c) (u : E3) :
    (∫ x : E3, (chiSmall M (c⁻¹ • x - u)) ^ 2) = c ^ 3 := by
  have hne : c ≠ 0 := ne_of_gt hc
  have hshift : (∫ x : E3, (chiSmall M (c⁻¹ • x - u)) ^ 2)
      = ∫ y : E3, (chiSmall M (c⁻¹ • y)) ^ 2 := by
    have hpt : (fun x : E3 => (chiSmall M (c⁻¹ • x - u)) ^ 2)
        = fun y : E3 => (fun w : E3 => (chiSmall M (c⁻¹ • w)) ^ 2) (y + (-(c • u))) := by
      funext x
      have h1 : c⁻¹ • (x + (-(c • u))) = c⁻¹ • x - u := by
        rw [smul_add, smul_neg, smul_smul, inv_mul_cancel₀ hne, one_smul]
        abel
      rw [← h1]
    rw [hpt]
    exact integral_add_right_eq_self (fun y : E3 => (chiSmall M (c⁻¹ • y)) ^ 2) (-(c • u))
  rw [hshift]
  have hscale := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure E3)
    (fun z : E3 => (chiSmall M z) ^ 2) (R := c) (le_of_lt hc)
  rw [finrank_euclideanSpace (𝕜 := ℝ), Fintype.card_fin] at hscale
  rw [hscale, chiSmall_L2 hM, smul_eq_mul, mul_one]

/-! ## §2  The exact change of variables -/

/-- **The exact change of variables for the sliding-box `χ`-mass**:
with `z = (ℓd)⁻¹ • x − u`, i.e. `x = (ℓd) • (z + u)`,

    chiMass M ℓ d u = (ℓd)³ ∫_z χ(d • (z + u))² · χ_M(z)² dz .

Proof: the `ℓ`-scale factor is definitionally `χ(ℓ⁻¹ • x)`, and `ℓ⁻¹ • ((ℓd) • w) = d • w`; then
translate by `u` and rescale by `(ℓd)` (Haar). -/
theorem chiMass_eq_scaled {M : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) :
    Work.SmallBoxSliding.chiMass M ℓ d u
      = (ℓ * d) ^ 3 * ∫ z : E3, (chi (d • (z + u))) ^ 2 * (chiSmall M z) ^ 2 := by
  have hc : 0 < ℓ * d := mul_pos hℓ hd
  have hne : ℓ * d ≠ 0 := ne_of_gt hc
  have hneℓ : ℓ ≠ 0 := ne_of_gt hℓ
  let F : E3 → ℝ := fun y => (chi (ℓ⁻¹ • y)) ^ 2 * (chiSmall M ((ℓ * d)⁻¹ • y - u)) ^ 2
  let G : E3 → ℝ := fun z => (chi (d • (z + u))) ^ 2 * (chiSmall M z) ^ 2
  have hF : F = fun y : E3 => (chi (ℓ⁻¹ • y)) ^ 2
      * (chiSmall M ((ℓ * d)⁻¹ • y - u)) ^ 2 := rfl
  have hG : G = fun z : E3 => (chi (d • (z + u))) ^ 2 * (chiSmall M z) ^ 2 := rfl
  have h1 : Work.SmallBoxSliding.chiMass M ℓ d u = ∫ x : E3, F x := by
    rw [Work.SmallBoxSliding.chiMass_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [hF]
    simp only [chiSmallB, chiScale, mul_pow]
  -- pointwise identity for the substituted variable
  have hFpt : ∀ z : E3, F ((ℓ * d) • (z + u)) = G z := by
    intro z
    simp only [hF, hG]
    have h1' : ℓ⁻¹ • ((ℓ * d) • (z + u)) = d • (z + u) := inv_smul_smul_mul hneℓ (z + u)
    have h2' : (ℓ * d)⁻¹ • ((ℓ * d) • (z + u)) - u = z := by
      rw [smul_inv_smul_cancel hne (z + u), add_sub_cancel_right]
    rw [h1', h2']
  -- Haar rescaling
  have hcomp : (∫ x : E3, F ((ℓ * d) • x)) = ((ℓ * d) ^ 3)⁻¹ * ∫ x : E3, F x := by
    have h := Measure.integral_comp_smul_of_nonneg (volume : Measure E3) F (ℓ * d)
      (hR := le_of_lt hc)
    rw [finrank_euclideanSpace (𝕜 := ℝ), Fintype.card_fin] at h
    rw [h, smul_eq_mul]
  -- translation
  have htrans : (∫ z : E3, F ((ℓ * d) • (z + u))) = ∫ z : E3, F ((ℓ * d) • z) :=
    integral_add_right_eq_self (fun z : E3 => F ((ℓ * d) • z)) u
  have hGval : (∫ z : E3, G z) = ((ℓ * d) ^ 3)⁻¹ * ∫ x : E3, F x := by
    have hg : (∫ z : E3, G z) = ∫ z : E3, F ((ℓ * d) • (z + u)) := by
      apply integral_congr_ae
      filter_upwards with z
      exact (hFpt z).symm
    rw [hg, htrans, hcomp]
  rw [h1, hGval, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 3 hne), one_mul]

/-! ## §3  The universal upper bound -/

/-- **The universal upper bound**: `chiMass M ℓ d u ≤ chiSupAbs² (ℓd)³`. -/
theorem chiMass_le_sup {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) :
    Work.SmallBoxSliding.chiMass M ℓ d u ≤ chiSupAbs ^ 2 * (ℓ * d) ^ 3 := by
  have hc : 0 < ℓ * d := mul_pos hℓ hd
  rw [chiMass_eq_scaled hℓ hd u]
  have hmono : (∫ z : E3, (chi (d • (z + u))) ^ 2 * (chiSmall M z) ^ 2)
      ≤ ∫ z : E3, chiSupAbs ^ 2 * (chiSmall M z) ^ 2 := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => ?_)
      ((integrable_chiSmall_sq hM).const_mul _) (Filter.Eventually.of_forall fun z => ?_)
    · positivity
    · have hsnn : 0 ≤ (chiSmall M z) ^ 2 := by positivity
      have hchi : (chi (d • (z + u))) ^ 2 ≤ chiSupAbs ^ 2 := by
        have h := chi_abs_le_sup (d • (z + u))
        nlinarith [abs_nonneg (chi (d • (z + u))), chiSupAbs_nonneg,
          sq_abs (chi (d • (z + u)))]
      exact mul_le_mul_of_nonneg_right hchi hsnn
  have hval : (∫ z : E3, chiSupAbs ^ 2 * (chiSmall M z) ^ 2) = chiSupAbs ^ 2 := by
    rw [integral_const_mul, chiSmall_L2 hM, mul_one]
  calc (ℓ * d) ^ 3 * (∫ z : E3, (chi (d • (z + u))) ^ 2 * (chiSmall M z) ^ 2)
      ≤ (ℓ * d) ^ 3 * (∫ z : E3, chiSupAbs ^ 2 * (chiSmall M z) ^ 2) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = chiSupAbs ^ 2 * (ℓ * d) ^ 3 := by rw [hval]; ring

/-! ## §4  The dichotomy -/

/-- **The deep interior**: on the region `‖d • u‖ + √3 d/2 ≤ 1/4` the `ℓ`-scale factor is
*constantly* `chiSupAbs` on the support of the small-box factor, and the mass is exactly
`chiSupAbs² (ℓd)³`. -/
theorem chiMass_eq_deep {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u : E3}
    (hu : ‖d • u‖ + Real.sqrt 3 * d / 2 ≤ 1 / 4) :
    Work.SmallBoxSliding.chiMass M ℓ d u = chiSupAbs ^ 2 * (ℓ * d) ^ 3 := by
  have hc : 0 < ℓ * d := mul_pos hℓ hd
  have hne : ℓ * d ≠ 0 := ne_of_gt hc
  have hneℓ : ℓ ≠ 0 := ne_of_gt hℓ
  let s : E3 → ℝ := fun x => (chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2
  have h1 : Work.SmallBoxSliding.chiMass M ℓ d u
      = ∫ x : E3, (chi (ℓ⁻¹ • x)) ^ 2 * s x := by
    rw [Work.SmallBoxSliding.chiMass_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (chiSmallB M ℓ d u x) ^ 2 = (chi (ℓ⁻¹ • x)) ^ 2 * s x
    simp only [chiSmallB, chiScale, s, mul_pow]
  rw [h1]
  -- pointwise: on the support of `s` the `ℓ`-factor is `chiSupAbs`
  have hpt : ∀ x, (chi (ℓ⁻¹ • x)) ^ 2 * s x = chiSupAbs ^ 2 * s x := by
    intro x
    by_cases hx : s x = 0
    · rw [hx, mul_zero, mul_zero]
    · have hz : chiSmall M ((ℓ * d)⁻¹ • x - u) ≠ 0 := by
        intro h
        exact hx (by simp only [s, h]; ring)
      let z : E3 := (ℓ * d)⁻¹ • x - u
      have hzcoord : ∀ j : Fin 3, |z j| ≤ 1 / 2 := fun j => chiSmall_ne_zero_coord hM hz j
      have hznorm : ‖z‖ ≤ Real.sqrt 3 / 2 := norm_le_sqrt_three_div_two hzcoord
      have hxeq : x = (ℓ * d) • (z + u) := by
        have hz1 : z + u = (ℓ * d)⁻¹ • x := by
          simp only [z]; exact sub_add_cancel _ _
        rw [hz1]
        exact (smul_smul_inv_cancel hne x).symm
      have hsn : ‖ℓ⁻¹ • x‖ ≤ 1 / 4 := by
        rw [hxeq]
        simp only [smul_add]
        rw [inv_smul_smul_mul hneℓ z, inv_smul_smul_mul hneℓ u]
        calc ‖d • z + d • u‖ ≤ ‖d • z‖ + ‖d • u‖ := norm_add_le _ _
          _ = d * ‖z‖ + ‖d • u‖ := by rw [norm_smul, Real.norm_of_nonneg hd.le]
          _ ≤ d * (Real.sqrt 3 / 2) + ‖d • u‖ := by
                have := mul_le_mul_of_nonneg_left hznorm hd.le
                linarith
          _ ≤ 1 / 4 := by linarith [hu]
      have hchi : chi (ℓ⁻¹ • x) = chiSupAbs :=
        chi_eq_chiSupAbs_of_chiBase_eq_one (chiBase_eq_one_of_norm_le hsn)
      rw [hchi]
  rw [show (∫ x : E3, (chi (ℓ⁻¹ • x)) ^ 2 * s x) = ∫ x : E3, chiSupAbs ^ 2 * s x from
    integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_const_mul]
  rw [show (∫ x : E3, s x) = (ℓ * d) ^ 3 by
    simp only [s]; exact integral_chiSmall_rescale_sub hM hc u]

/-- **The shell**: for `1/2 + √3 d/2 ≤ ‖d • u‖` the `ℓ`-scale factor vanishes identically on the
support of the small-box factor and the `χ`-mass is **zero**. -/
theorem chiMass_eq_zero_of_far {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u : E3}
    (hu : 1 / 2 + Real.sqrt 3 * d / 2 ≤ ‖d • u‖) :
    Work.SmallBoxSliding.chiMass M ℓ d u = 0 := by
  have hc : 0 < ℓ * d := mul_pos hℓ hd
  have hne : ℓ * d ≠ 0 := ne_of_gt hc
  have hneℓ : ℓ ≠ 0 := ne_of_gt hℓ
  have h1 : Work.SmallBoxSliding.chiMass M ℓ d u
      = ∫ x : E3, (chi (ℓ⁻¹ • x)) ^ 2 * (chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2 := by
    rw [Work.SmallBoxSliding.chiMass_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show (chiSmallB M ℓ d u x) ^ 2
      = (chi (ℓ⁻¹ • x)) ^ 2 * (chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2
    simp only [chiSmallB, chiScale, mul_pow]
  rw [h1]
  have hzero : ∀ x : E3,
      (chi (ℓ⁻¹ • x)) ^ 2 * (chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2 = 0 := by
    intro x
    by_cases hx : chiSmall M ((ℓ * d)⁻¹ • x - u) = 0
    · rw [hx]; ring
    · let z : E3 := (ℓ * d)⁻¹ • x - u
      have hzcoord : ∀ j : Fin 3, |z j| ≤ 1 / 2 :=
        fun j => chiSmall_ne_zero_coord hM hx j
      have hznorm : ‖z‖ ≤ Real.sqrt 3 / 2 := norm_le_sqrt_three_div_two hzcoord
      have hxeq : x = (ℓ * d) • (z + u) := by
        have hz1 : z + u = (ℓ * d)⁻¹ • x := by
          simp only [z]; exact sub_add_cancel _ _
        rw [hz1]
        exact (smul_smul_inv_cancel hne x).symm
      have hbig : 1 / 2 ≤ ‖ℓ⁻¹ • x‖ := by
        rw [hxeq]
        simp only [smul_add]
        rw [inv_smul_smul_mul hneℓ z, inv_smul_smul_mul hneℓ u]
        have hlow : ‖d • u‖ - ‖d • z‖ ≤ ‖d • z + d • u‖ := by
          have h : (d • z + d • u) + (-(d • z)) = d • u := by abel
          have h' := norm_add_le (d • z + d • u) (-(d • z))
          rw [h, norm_neg] at h'
          linarith
        have hdz : ‖d • z‖ ≤ Real.sqrt 3 * d / 2 := by
          rw [norm_smul, Real.norm_of_nonneg hd.le]
          have := mul_le_mul_of_nonneg_left hznorm hd.le
          linarith
        linarith
      have hchi0 : chi (ℓ⁻¹ • x) = 0 := chi_eq_zero_of_half_le_norm _ hbig
      rw [hchi0]; ring
  rw [show (∫ x : E3, (chi (ℓ⁻¹ • x)) ^ 2 * (chiSmall M ((ℓ * d)⁻¹ • x - u)) ^ 2)
      = ∫ _x : E3, (0 : ℝ) from
    integral_congr_ae (Filter.Eventually.of_forall hzero)]
  simp

/-- `chiSupAbs = (√chiNormSq)⁻¹ > 0`. -/
lemma chiSupAbs_pos : 0 < chiSupAbs := by
  rw [chiSupAbs]
  exact inv_pos.mpr (Real.sqrt_pos.mpr chiNormSq_pos)

/-- **The mass is strictly positive on the deep interior** — the `chiMass ≠ 0` side condition
that the corpus statements dividing by `chiMass` need. -/
theorem chiMass_pos_of_deep {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {u : E3}
    (hu : ‖d • u‖ + Real.sqrt 3 * d / 2 ≤ 1 / 4) :
    0 < Work.SmallBoxSliding.chiMass M ℓ d u := by
  rw [chiMass_eq_deep hM hℓ hd hu]
  have h1 : 0 < chiSupAbs ^ 2 := pow_pos chiSupAbs_pos 2
  have h2 : 0 < (ℓ * d) ^ 3 := pow_pos (mul_pos hℓ hd) 3
  exact mul_pos h1 h2

end Work.BoseFixB1B
