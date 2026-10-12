import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.DLSmallKernels
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A uniform positive lower bound for `(χ_M ⋆ χ_M)` on the polydisc `{|z_j| ≤ ρ}`, `ρ < 1`

The cosine-`M`-th-power bump `χ_M = chiSmall M` is supported in the cube
`{|z_j| ≤ 1/2}` (`zeta1d y = cos (π y)·1_{|y| ≤ 1/2}`), hence its self-convolution
`Submission.BoseGases.conv3Small M z = ∫_y χ_M(y)·χ_M(z − y) dy` is supported in the
cube `{|z_j| ≤ 1}`.  This file proves that the convolution is *uniformly bounded
below on the open polydisc*: for every `ρ < 1` and every `M ≥ 1` there is `c > 0`
with `c ≤ (χ_M ⋆ χ_M)(z)` for all `z` with `|z_j| ≤ ρ` (`j : Fin 3`).

**Proof (midpoint form of the convolution).**  Write `u := z/2`, so that
`z = u + u`.  Translating the integration variable by `u`
(`integral_add_left_eq_self`) turns the defining integral into the symmetric form

  `(χ_M ⋆ χ_M)(z) = ∫_w χ_M(u + w)·χ_M(u − w) dw`,

in which the two factors are the bump evaluated at the two points symmetric about
`u`.  Put `ρ' := max ρ 0 < 1`, `δ := (1 − ρ')/4` and `q := (1 + ρ')/4 = ρ'/2 + δ`;
then `q < 1/2`.  For `|z_j| ≤ ρ ≤ ρ'` we have `|u_j| ≤ ρ'/2`, so for `w` in the cube
`{|w_j| ≤ δ}` the two arguments of the bump satisfy
`|(u ± w)_j| ≤ ρ'/2 + δ = q < 1/2`.  On the cube of coordinate radius `q` the bump is
bounded below by the explicit constant
`chiSmall_cube_lower_gen`: `χ_M(x) ≥ (cos (π q)³)^M / √(∫ χ̃_M²) > 0` (the unnormalised
profile satisfies `ζ(x_j) ≥ cos (π q)` there, by monotonicity of `cos` on `[0, π]`).
Hence the integrand is `≥ c₁²` on the cube `{|w_j| ≤ δ}` of volume `(2δ)³ > 0`, and

  `(χ_M ⋆ χ_M)(z) ≥ c₁²·(2δ)³ > 0`.

All constants are explicit in the parameters `M`, `ρ`; only positivity of the lower
bound is used.
-/

noncomputable section

open MeasureTheory Metric
open scoped Real BigOperators ENNReal Topology

namespace Work.BoseFixB1B

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## One-dimensional / cube lower bounds for the bump -/

/-- Monotonicity of `cos` on the cube: for `|x| ≤ q ≤ 1/2`, `ζ(x) ≥ cos (π q)`. -/
lemma zeta1d_lower {q x : ℝ} (hq1 : q ≤ 1 / 2) (hx : |x| ≤ q) :
    Real.cos (Real.pi * q) ≤ Submission.BoseGases.zeta1d x := by
  have hxhalf : |x| ≤ 1 / 2 := le_trans hx hq1
  rw [Submission.BoseGases.zeta1d_of_abs_le hxhalf,
    Submission.BoseGases.cos_pi_mul_eq_cos_pi_abs x]
  have hqpi : Real.pi * q ≤ Real.pi := by nlinarith [Real.pi_pos]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (x := Real.pi * |x|) (y := Real.pi * q)
    (by positivity) hqpi (by nlinarith [Real.pi_pos, abs_nonneg x, hx])

/-- **Cube lower bound for the unnormalised bump**: for `0 ≤ q ≤ 1/2` and
`|x_j| ≤ q` (all `j`), `(cos (π q)³)^M ≤ χ̃_M(x)`. -/
lemma chiSmallBase_cube_lower {M : ℕ} {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1 / 2)
    (x : ℝ³) (hx : ∀ j : Fin 3, |x.ofLp j| ≤ q) :
    (Real.cos (Real.pi * q) ^ 3) ^ M ≤ Submission.BoseGases.chiSmallBase M x := by
  have hcnn : 0 ≤ Real.cos (Real.pi * q) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos, hq1])
  have h0 : Real.cos (Real.pi * q) ≤ Submission.BoseGases.zeta1d (x.ofLp 0) :=
    zeta1d_lower hq1 (hx 0)
  have h1 : Real.cos (Real.pi * q) ≤ Submission.BoseGases.zeta1d (x.ofLp 1) :=
    zeta1d_lower hq1 (hx 1)
  have h2 : Real.cos (Real.pi * q) ≤ Submission.BoseGases.zeta1d (x.ofLp 2) :=
    zeta1d_lower hq1 (hx 2)
  have h12 : Real.cos (Real.pi * q) * Real.cos (Real.pi * q)
      ≤ Submission.BoseGases.zeta1d (x.ofLp 0) * Submission.BoseGases.zeta1d (x.ofLp 1) :=
    mul_le_mul h0 h1 hcnn (Submission.BoseGases.zeta1d_nonneg _)
  have h123 : (Real.cos (Real.pi * q) * Real.cos (Real.pi * q)) * Real.cos (Real.pi * q)
      ≤ (Submission.BoseGases.zeta1d (x.ofLp 0) * Submission.BoseGases.zeta1d (x.ofLp 1))
        * Submission.BoseGases.zeta1d (x.ofLp 2) :=
    mul_le_mul h12 h2 hcnn
      (mul_nonneg (Submission.BoseGases.zeta1d_nonneg _) (Submission.BoseGases.zeta1d_nonneg _))
  have hpow := pow_le_pow_left₀
    (by positivity : (0 : ℝ) ≤ Real.cos (Real.pi * q) * Real.cos (Real.pi * q) * Real.cos (Real.pi * q))
    h123 M
  calc (Real.cos (Real.pi * q) ^ 3) ^ M
      = (Real.cos (Real.pi * q) * Real.cos (Real.pi * q) * Real.cos (Real.pi * q)) ^ M := by
        ring_nf
    _ ≤ Submission.BoseGases.chiSmallBase M x := by
        simpa [Submission.BoseGases.chiSmallBase] using hpow

/-- **Cube lower bound for the normalised bump**: for `0 ≤ q ≤ 1/2` and `|x_j| ≤ q`,
`(cos (π q)³)^M / √(∫ χ̃_M²) ≤ χ_M(x)`. -/
lemma chiSmall_cube_lower_gen {M : ℕ} (hM : 1 ≤ M) {q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1 / 2) (x : ℝ³) (hx : ∀ j : Fin 3, |x.ofLp j| ≤ q) :
    (Real.cos (Real.pi * q) ^ 3) ^ M / Real.sqrt (Submission.BoseGases.chiSmallNormSq M)
      ≤ Submission.BoseGases.chiSmall M x := by
  have hbase := chiSmallBase_cube_lower (M := M) hq0 hq1 x hx
  have hspos : 0 < Real.sqrt (Submission.BoseGases.chiSmallNormSq M) :=
    Real.sqrt_pos.mpr (Submission.BoseGases.chiSmallNormSq_pos hM)
  have := div_le_div_of_nonneg_right hbase hspos.le
  simpa [Submission.BoseGases.chiSmall] using this

/-- **Midpoint form of the self-convolution**: if `u + u = z` (so `u = z/2`), then
`(χ_M ⋆ χ_M)(z) = ∫_w χ_M(u + w)·χ_M(u − w) dw`. -/
lemma conv3Small_eq_midpoint {M : ℕ} {u z : ℝ³} (hu : u + u = z) :
    Submission.BoseGases.conv3Small M z
      = ∫ w : ℝ³, Submission.BoseGases.chiSmall M (u + w)
          * Submission.BoseGases.chiSmall M (u - w) := by
  rw [show Submission.BoseGases.conv3Small M z
      = ∫ y : ℝ³, Submission.BoseGases.chiSmall M y * Submission.BoseGases.chiSmall M (z - y)
        from rfl,
    ← MeasureTheory.integral_add_left_eq_self
      (fun y : ℝ³ => Submission.BoseGases.chiSmall M y * Submission.BoseGases.chiSmall M (z - y)) u]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with w
  have harg : z - (u + w) = u - w := by
    rw [← hu]
    abel
  rw [harg]

/-! ## The polydisc bound -/

theorem exists_pos_le_conv3Small_of_polydisc {M : ℕ} (hM : 1 ≤ M) {ρ : ℝ} (hρ : ρ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : EuclideanSpace ℝ (Fin 3),
      (∀ j : Fin 3, |z.ofLp j| ≤ ρ) → c ≤ Submission.BoseGases.conv3Small M z := by
  set ρ' : ℝ := max ρ 0 with hρ'def
  have hρ'1 : ρ' < 1 := max_lt hρ zero_lt_one
  have hρ'0 : 0 ≤ ρ' := le_max_right _ _
  set δ : ℝ := (1 - ρ') / 4 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  set q : ℝ := (1 + ρ') / 4 with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef]; linarith
  have hqhalf : q ≤ 1 / 2 := by rw [hqdef]; linarith
  have hsum : ρ' / 2 + δ = q := by rw [hqdef, hδdef]; ring
  have hcos : 0 < Real.cos (Real.pi * q) := by
    apply Real.cos_pos_of_mem_Ioo
    exact ⟨by nlinarith [Real.pi_pos], by rw [hqdef]; nlinarith [Real.pi_pos, hρ'1]⟩
  set c₁ : ℝ :=
    (Real.cos (Real.pi * q) ^ 3) ^ M / Real.sqrt (Submission.BoseGases.chiSmallNormSq M)
    with hc₁def
  have hc₁pos : 0 < c₁ := by
    rw [hc₁def]
    exact div_pos (pow_pos (pow_pos hcos 3) M)
      (Real.sqrt_pos.mpr (Submission.BoseGases.chiSmallNormSq_pos hM))
  refine ⟨c₁ ^ 2 * (2 * δ) ^ 3, by positivity, ?_⟩
  intro z hz
  have hzρ' : ∀ j : Fin 3, |z.ofLp j| ≤ ρ' := fun j => le_trans (hz j) (le_max_left _ _)
  set u : ℝ³ := (2 : ℝ)⁻¹ • z with hudef
  have hu2 : u + u = z := by
    rw [hudef, ← two_smul ℝ ((2 : ℝ)⁻¹ • z), smul_smul]
    norm_num
  have hu_coord : ∀ j : Fin 3, |u.ofLp j| ≤ ρ' / 2 := by
    intro j
    have hco : u.ofLp j = (2 : ℝ)⁻¹ * z.ofLp j := by
      rw [hudef]
      simp
    rw [hco, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
    linarith [hzρ' j]
  have hmid : Submission.BoseGases.conv3Small M z
      = ∫ w : ℝ³, Submission.BoseGases.chiSmall M (u + w)
          * Submission.BoseGases.chiSmall M (u - w) :=
    conv3Small_eq_midpoint hu2
  set C : Set ℝ³ := {w : ℝ³ | ∀ j : Fin 3, |w.ofLp j| ≤ δ} with hCdef
  have hCmeas : MeasurableSet C := Submission.BoseGases.eucl_cube_measurable
  have hCvol : (volume : Measure ℝ³) C = ENNReal.ofReal ((2 * δ) ^ 3) :=
    Submission.BoseGases.eucl_cube_volume hδpos.le
  have hCfin : (volume : Measure ℝ³) C ≠ ∞ := by
    rw [hCvol]
    exact ENNReal.ofReal_ne_top
  have hCreal : (volume : Measure ℝ³).real C = (2 * δ) ^ 3 := by
    rw [MeasureTheory.measureReal_def, hCvol, ENNReal.toReal_ofReal (by positivity)]
  have hcont : Continuous (fun w : ℝ³ => Submission.BoseGases.chiSmall M (u - w)) :=
    (Submission.BoseGases.chiSmall_continuous hM).comp (continuous_const.sub continuous_id)
  have hI : Integrable (fun y : ℝ³ => Submission.BoseGases.chiSmall M y) :=
    (Submission.BoseGases.chiSmall_continuous hM).integrable_of_hasCompactSupport
      (Submission.BoseGases.chiSmall_hasCompactSupport hM)
  have hint : Integrable (fun w : ℝ³ => Submission.BoseGases.chiSmall M (u + w)
      * Submission.BoseGases.chiSmall M (u - w)) :=
    (hI.comp_add_left u).mul_bdd hcont.aestronglyMeasurable
      (ae_of_all _ (fun w => by
        rw [Real.norm_eq_abs]
        exact Submission.BoseGases.chiSmall_decay_coord_le_decay hM (u - w)))
  have hpt : ∀ w ∈ C, c₁ ^ 2 ≤ Submission.BoseGases.chiSmall M (u + w)
      * Submission.BoseGases.chiSmall M (u - w) := by
    intro w hw
    rw [hCdef] at hw
    have h1 : c₁ ≤ Submission.BoseGases.chiSmall M (u + w) := by
      rw [hc₁def]
      apply chiSmall_cube_lower_gen hM hq0 hqhalf
      intro j
      have hcoord : (u + w).ofLp j = u.ofLp j + w.ofLp j := by simp
      rw [hcoord]
      calc |u.ofLp j + w.ofLp j| ≤ |u.ofLp j| + |w.ofLp j| := abs_add_le _ _
        _ ≤ ρ' / 2 + δ := add_le_add (hu_coord j) (hw j)
        _ = q := hsum
    have h2 : c₁ ≤ Submission.BoseGases.chiSmall M (u - w) := by
      rw [hc₁def]
      apply chiSmall_cube_lower_gen hM hq0 hqhalf
      intro j
      have hcoord : (u - w).ofLp j = u.ofLp j - w.ofLp j := by simp
      rw [hcoord]
      calc |u.ofLp j - w.ofLp j| ≤ |u.ofLp j| + |w.ofLp j| := abs_sub _ _
        _ ≤ ρ' / 2 + δ := add_le_add (hu_coord j) (hw j)
        _ = q := hsum
    calc c₁ ^ 2 = c₁ * c₁ := by ring
      _ ≤ Submission.BoseGases.chiSmall M (u + w) * Submission.BoseGases.chiSmall M (u - w) :=
          mul_le_mul h1 h2 hc₁pos.le (Submission.BoseGases.chiSmall_nonneg M _)
  have hmono : ∫ w in C, c₁ ^ 2 ≤ ∫ w in C, Submission.BoseGases.chiSmall M (u + w)
      * Submission.BoseGases.chiSmall M (u - w) := by
    refine MeasureTheory.setIntegral_mono_on ?_ ?_ hCmeas hpt
    · exact MeasureTheory.integrableOn_const (s := C) hCfin
    · exact hint.integrableOn
  have hconst : (∫ w in C, c₁ ^ 2) = c₁ ^ 2 * (2 * δ) ^ 3 := by
    rw [MeasureTheory.setIntegral_const, hCreal, smul_eq_mul]
    ring
  have hle : ∫ w in C, Submission.BoseGases.chiSmall M (u + w)
        * Submission.BoseGases.chiSmall M (u - w)
      ≤ ∫ w : ℝ³, Submission.BoseGases.chiSmall M (u + w)
        * Submission.BoseGases.chiSmall M (u - w) :=
    MeasureTheory.setIntegral_le_integral hint
      (ae_of_all _ (fun w => mul_nonneg (Submission.BoseGases.chiSmall_nonneg M _)
        (Submission.BoseGases.chiSmall_nonneg M _)))
  rw [hmid]
  linarith [hmono, hconst, hle]

end Work.BoseFixB1B
