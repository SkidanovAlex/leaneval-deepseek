/-
# `PggEnvTools` — the measure-theoretic tools for the `gg`-rows of the `rl¹`-norm

The five `gg`-pieces `N₁^{gg}, …, N₅^{gg}` of the nonlinearity `N` of §8 of Elgindi's paper
are estimated in the `rl¹`-norm

`rl¹(N) = ∫⁻_r r⁻¹ (∫⁻_θ |K θ · N(r,θ)|)`.

Unlike the `gs`/`sg`/`ss`-rows, in which every nonlinearity contains one factor (`F_*` or one of
its derivatives) whose *pointwise* size decays like `r/(1+r)²` in `r`, the `gg`-rows have two
factors (`g`, `D_θg`, `D_zg`, `FK(g)`) about which only *integral* information is available:
the `ℋ⁴`-norm

`X = Xn α g = √(HkSq α 4 g) = √(∫_r ∫_θ HkIntegrand α 4 g r θ)`.

Everything is therefore proved by **two nested Cauchy–Schwarz steps**:

* an *angular* step on the slice `θ ↦ B(r,θ)`
  (`inner_abs_lintegral_le`: `∫⁻_θ ofReal |B| ≤ ofReal (2 √(∫_θ B²))`), and
* a *radial* step, using the pointwise domination of the angular mass by the `ℋ⁴`-integrand
  slice of `g`, `Φ r := ∫_θ HkIntegrand α 4 g r θ` (which is what the definitions of `gSlots`
  provide: `w² g² ≤ HkIntegrand`, `w² (D_θg)² sin(2θ)^{-γ} ≤ HkIntegrand`,
  `w (D_zg)² ≤ HkIntegrand`).

The radial step is the content of the two engines `zinv_lintegral_sqrt_le` (one angular factor)
and `zinv_lintegral_prod_sqrt_le` (two angular factors, i.e. the `FK(g)`-rows): for `r > 0`,

`r⁻¹ √(S r) ≤ √(Φ r)/(1+r)`  whenever  `w r · S r ≤ Φ r`,

because `√w r = (1+r)/r`; the resulting weight `1/(1+r)` is square-integrable with
`∫_0^∞ (1+r)^{-2} = 1`, and for the product of two such factors the weight becomes
`Φ r · r/(1+r)² ≤ Φ r/4`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.gPt
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.gSlots
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Pieces.rl1Pieces

set_option autoImplicit false

/-! ## Elementary angular facts -/

theorem integrableOn_one_Iθ : IntegrableOn (fun _ : ℝ => (1 : ℝ)) Work.Spaces.Iθ :=
  MeasureTheory.integrableOn_const (μ := volume)
    (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

theorem integral_one_Iθ : ∫ θ in Work.Spaces.Iθ, (1 : ℝ) = Real.pi / 2 := by
  rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, MeasureTheory.measureReal_def,
    Work.Spaces.Iθ, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

theorem sqrt_pi_half_le_two : Real.sqrt (Real.pi / 2) ≤ 2 := by
  calc Real.sqrt (Real.pi / 2) ≤ Real.sqrt 4 :=
        Real.sqrt_le_sqrt (by linarith [Real.pi_le_four])
    _ = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-! ## The angular Cauchy–Schwarz step -/

/-- **The angular Cauchy–Schwarz step in `∫⁻`-form.**  For a slice `u` which is a.e. strongly
measurable and whose square is integrable,
`∫⁻_θ ofReal |u θ| ≤ ofReal (2 √(∫_θ u θ²))`; the constant `2` comes from
`∫_{Iθ} 1 = π/2 ≤ 4` and `√(π/2) ≤ 2`. -/
theorem inner_abs_lintegral_le {u : ℝ → ℝ}
    (hu : AEStronglyMeasurable u (volume.restrict Work.Spaces.Iθ))
    (hint : IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ) :
    (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |u θ|)
      ≤ ENNReal.ofReal (2 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
  have hui : IntegrableOn (fun θ => |u θ|) Work.Spaces.Iθ := by
    refine Integrable.mono' (g := fun θ => (1 + (u θ) ^ 2) / 2) ?_ hu.norm ?_
    · exact (integrableOn_one_Iθ.add hint).mul_const (2 : ℝ)⁻¹
    · exact Eventually.of_forall fun θ => by
        rw [Real.norm_eq_abs, abs_abs]
        have h := sq_nonneg (|u θ| - 1)
        nlinarith [sq_abs (u θ), h]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hui
    (Eventually.of_forall fun θ => abs_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h2 : IntegrableOn (fun θ => (|u θ|) ^ 2) Work.Spaces.Iθ := by
    simpa only [sq_abs] using hint
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict Work.Spaces.Iθ)
    (f := fun θ => |u θ|) (g := fun _ => (1 : ℝ)) hu.norm aestronglyMeasurable_const h2
    (by simpa using integrableOn_one_Iθ)
  have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, |u θ| :=
    MeasureTheory.integral_nonneg fun θ => abs_nonneg _
  have hsq : (∫ θ in Work.Spaces.Iθ, (|u θ|) ^ 2)
      = ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
    MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => sq_abs (u θ))
  have hg2 : (∫ θ in Work.Spaces.Iθ, (1 : ℝ) ^ 2) = Real.pi / 2 := by
    rw [show (1 : ℝ) ^ 2 = 1 by norm_num, integral_one_Iθ]
  calc (∫ θ in Work.Spaces.Iθ, |u θ|)
      = |∫ θ in Work.Spaces.Iθ, |u θ| * 1| := by
        simp only [mul_one]
        exact (abs_of_nonneg hnn).symm
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (|u θ|) ^ 2)
          * Real.sqrt (∫ θ in Work.Spaces.Iθ, (1 : ℝ) ^ 2) := hcs
    _ = Real.sqrt (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) * Real.sqrt (Real.pi / 2) := by
        rw [hsq, hg2]
    _ ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) * 2 :=
        mul_le_mul_of_nonneg_left sqrt_pi_half_le_two (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) := by ring

/-- `√(w z) = (1+z)/z` for `z > 0`, `w z = (1+z)²/z²`. -/
theorem sqrt_w_eq {z : ℝ} (hz : 0 < z) : Real.sqrt (Work.Spaces.w z) = (1 + z) / z := by
  have h1 : (0 : ℝ) < 1 + z := by linarith
  have h2 : Work.Spaces.w z = (1 + z) ^ 2 / z ^ 2 := rfl
  rw [h2, Real.sqrt_div (by positivity)]
  rw [Real.sqrt_sq h1.le, Real.sqrt_sq hz.le]

/-- The two algebraic identities behind the radial Cauchy–Schwarz steps, for `z > 0`:
`z⁻¹ · (a / w z) = a · (z/(1+z)²)` and `√(a/w z) = √a · (z/(1+z))` for `a ≥ 0`. -/
theorem zinv_div_w (z a : ℝ) (hz : 0 < z) :
    z⁻¹ * (a / Work.Spaces.w z) = a * (z / (1 + z) ^ 2) := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1 : (1 + z) ≠ 0 := by positivity
  rw [Work.Spaces.w]
  field_simp

theorem sqrt_div_w (z a : ℝ) (hz : 0 < z) (ha : 0 ≤ a) :
    Real.sqrt (a / Work.Spaces.w z) = Real.sqrt a * (z / (1 + z)) := by
  have hz0 : z ≠ 0 := ne_of_gt hz
  have h1 : (1 + z) ≠ 0 := by positivity
  rw [Real.sqrt_div ha, sqrt_w_eq hz]
  field_simp

/-! ## The radial Cauchy–Schwarz steps -/

/-- **The radial Cauchy–Schwarz step, one angular factor.**

If `w z · S z ≤ Φ z` for `z > 0` and `Φ ≥ 0` is integrable on `(0,∞)`, then
`∫⁻_z z⁻¹ · ofReal (c √(S z)) ≤ ofReal (c √(∫_z Φ z))`. -/
theorem zinv_lintegral_sqrt_le {Φ S : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hΦnn : ∀ z, 0 < z → 0 ≤ Φ z)
    (hΦint : IntegrableOn Φ (Set.Ioi (0 : ℝ)))
    (hslot : ∀ z, 0 < z → Work.Spaces.w z * S z ≤ Φ z) :
    (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal z⁻¹ * ENNReal.ofReal (c * Real.sqrt (S z)))
      ≤ ENNReal.ofReal (c * Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Φ z)) := by
  have hΦsm : AEStronglyMeasurable Φ (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hΦint.aestronglyMeasurable
  have hdiv : AEStronglyMeasurable (fun z => 1 / (1 + z)) (volume.restrict (Set.Ioi (0 : ℝ))) :=
    (continuousOn_const.div (continuousOn_const.add continuousOn_id)
      (fun z hz => by
        have hz0 : (0 : ℝ) < z := Set.mem_Ioi.mp hz
        simp only [Pi.add_apply, id_eq]
        positivity)).aestronglyMeasurable
      measurableSet_Ioi
  have hFsm : AEStronglyMeasurable (fun z => Real.sqrt (Φ z) / (1 + z))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h := (Real.continuous_sqrt.comp_aestronglyMeasurable hΦsm).mul hdiv
    refine h.congr ?_
    exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun z _ => by simp only [Pi.mul_apply, div_eq_mul_inv, one_mul])
  have hF : IntegrableOn (fun z => Real.sqrt (Φ z) / (1 + z)) (Set.Ioi (0 : ℝ)) := by
    refine Integrable.mono' (g := fun z => (Φ z + 1 / (1 + z) ^ 2) / 2) ?_ hFsm ?_
    · exact (hΦint.add Work.FTS.Nonlinear.Pieces.rl1Tools.integrableOn_one_div_one_add_sq).mul_const
        (2 : ℝ)⁻¹
    · refine (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono fun z hz => ?_
      have hz0 : 0 < z := hz
      have h1 : (0 : ℝ) < 1 + z := by linarith
      have hsq : ((1 + z)⁻¹) ^ 2 = 1 / (1 + z) ^ 2 := by rw [inv_pow, one_div]
      have hkey := two_mul_le_add_sq (Real.sqrt (Φ z)) ((1 + z)⁻¹)
      rw [Real.sq_sqrt (hΦnn z hz0), hsq] at hkey
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) h1.le)]
      have hdiv : Real.sqrt (Φ z) / (1 + z) = Real.sqrt (Φ z) * (1 + z)⁻¹ := rfl
      rw [hdiv]
      linarith
  have hpt : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ENNReal.ofReal z⁻¹ * ENNReal.ofReal (c * Real.sqrt (S z))
        ≤ ENNReal.ofReal (c * (Real.sqrt (Φ z) / (1 + z))) := by
    refine (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono fun z hz => ?_
    have hz0 : 0 < z := hz
    have hw : 0 < Work.Spaces.w z := Work.FTS.Nonlinear.Pieces.rl1Tools.w_pos_of_pos hz0
    have hinv : 0 ≤ z⁻¹ := inv_nonneg.mpr hz0.le
    have hle : z⁻¹ * Real.sqrt (S z) ≤ Real.sqrt (Φ z) / (1 + z) := by
      have hSw : Real.sqrt (S z) ≤ Real.sqrt (Φ z) * (z / (1 + z)) := by
        rw [← sqrt_div_w z (Φ z) hz0 (hΦnn z hz0)]
        refine Real.sqrt_le_sqrt ((le_div_iff₀ hw).mpr ?_)
        rw [mul_comm]
        exact hslot z hz0
      calc z⁻¹ * Real.sqrt (S z) ≤ z⁻¹ * (Real.sqrt (Φ z) * (z / (1 + z))) :=
            mul_le_mul_of_nonneg_left hSw hinv
        _ = Real.sqrt (Φ z) / (1 + z) := by field_simp
    rw [← ENNReal.ofReal_mul hinv]
    refine ENNReal.ofReal_le_ofReal ?_
    calc z⁻¹ * (c * Real.sqrt (S z)) = c * (z⁻¹ * Real.sqrt (S z)) := by ring
      _ ≤ c * (Real.sqrt (Φ z) / (1 + z)) := mul_le_mul_of_nonneg_left hle hc
  refine (MeasureTheory.lintegral_mono_ae hpt).trans ?_
  have hG : IntegrableOn (fun z => c * (Real.sqrt (Φ z) / (1 + z))) (Set.Ioi (0 : ℝ)) :=
    hF.const_mul c
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hG
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun z hz => mul_nonneg hc (div_nonneg (Real.sqrt_nonneg _) (by linarith [Set.mem_Ioi.mp hz]))))]
  rw [MeasureTheory.integral_const_mul]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hc)
  have hsqint : IntegrableOn (fun z => (Real.sqrt (Φ z)) ^ 2) (Set.Ioi (0 : ℝ)) :=
    hΦint.congr (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun z hz => (Real.sq_sqrt (hΦnn z (Set.mem_Ioi.mp hz))).symm))
  have hG2int : IntegrableOn (fun z => (1 / (1 + z)) ^ 2) (Set.Ioi (0 : ℝ)) :=
    Work.FTS.Nonlinear.Pieces.rl1Tools.integrableOn_one_div_one_add_sq.congr
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
        (fun z _ => by simp only [div_pow, one_pow]))
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict (Set.Ioi (0 : ℝ)))
    (f := fun z => Real.sqrt (Φ z)) (g := fun z => 1 / (1 + z))
    (Real.continuous_sqrt.comp_aestronglyMeasurable hΦsm) hdiv hsqint hG2int
  have hcongr : (∫ z in Set.Ioi (0 : ℝ), (Real.sqrt (Φ z)) ^ 2)
      = ∫ z in Set.Ioi (0 : ℝ), Φ z :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun z hz => Real.sq_sqrt (hΦnn z (Set.mem_Ioi.mp hz)))
  have hG2eq : (∫ z in Set.Ioi (0 : ℝ), (1 / (1 + z)) ^ 2)
      = ∫ z in Set.Ioi (0 : ℝ), 1 / (1 + z) ^ 2 :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun z _ => by simp only [div_pow, one_pow])
  have hnn : 0 ≤ ∫ z in Set.Ioi (0 : ℝ), Real.sqrt (Φ z) * (1 / (1 + z)) :=
    MeasureTheory.integral_nonneg_of_ae
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz =>
        mul_nonneg (Real.sqrt_nonneg _)
          (div_nonneg zero_le_one (by linarith [Set.mem_Ioi.mp hz]))))
  calc ∫ z in Set.Ioi (0 : ℝ), Real.sqrt (Φ z) / (1 + z)
      = ∫ z in Set.Ioi (0 : ℝ), Real.sqrt (Φ z) * (1 / (1 + z)) :=
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          (fun z _ => by rw [div_eq_mul_inv, one_div])
    _ = |∫ z in Set.Ioi (0 : ℝ), Real.sqrt (Φ z) * (1 / (1 + z))| :=
        (abs_of_nonneg hnn).symm
    _ ≤ Real.sqrt (∫ z in Set.Ioi (0 : ℝ), (Real.sqrt (Φ z)) ^ 2)
          * Real.sqrt (∫ z in Set.Ioi (0 : ℝ), (1 / (1 + z)) ^ 2) := hcs
    _ = Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Φ z)
          * Real.sqrt (∫ z in Set.Ioi (0 : ℝ), (1 / (1 + z)) ^ 2) := by rw [hcongr]
    _ ≤ Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Φ z) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
        rw [Real.sqrt_le_one, hG2eq]
        exact (Work.FTS.Nonlinear.Pieces.rl1Tools.integral_one_div_one_add_sq).le
    _ = Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Φ z) := mul_one _

/-- **The radial Cauchy–Schwarz step, two angular factors** (the `FK(g)`-rows).

If `w z · Sᵢ z ≤ Φ z` for `i = 1,2` and `Φ ≥ 0` is integrable, then
`∫⁻_z z⁻¹ ofReal (c √(S₁ z) √(S₂ z)) ≤ ofReal (c · (1/4) ∫_z Φ z)`: the product of the two
angular factors is at most `Φ z/w z`, so the integrand is at most
`c Φ z · z/(1+z)² ≤ c Φ z/4`. -/
theorem zinv_lintegral_prod_sqrt_le {Φ S₁ S₂ : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hΦnn : ∀ z, 0 < z → 0 ≤ Φ z)
    (hΦint : IntegrableOn Φ (Set.Ioi (0 : ℝ)))
    (hslot1 : ∀ z, 0 < z → Work.Spaces.w z * S₁ z ≤ Φ z)
    (hslot2 : ∀ z, 0 < z → Work.Spaces.w z * S₂ z ≤ Φ z) :
    (∫⁻ z in Set.Ioi (0 : ℝ),
        ENNReal.ofReal z⁻¹ * ENNReal.ofReal (c * (Real.sqrt (S₁ z) * Real.sqrt (S₂ z))))
      ≤ ENNReal.ofReal (c * ((1 / 4) * ∫ z in Set.Ioi (0 : ℝ), Φ z)) := by
  have hpt : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ENNReal.ofReal z⁻¹ * ENNReal.ofReal (c * (Real.sqrt (S₁ z) * Real.sqrt (S₂ z)))
        ≤ ENNReal.ofReal (c * (Φ z * (z / (1 + z) ^ 2))) := by
    refine (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono fun z hz => ?_
    have hz0 : 0 < z := hz
    have hw : 0 < Work.Spaces.w z := Work.FTS.Nonlinear.Pieces.rl1Tools.w_pos_of_pos hz0
    have hinv : 0 ≤ z⁻¹ := inv_nonneg.mpr hz0.le
    have h1 : Real.sqrt (S₁ z) ≤ Real.sqrt (Φ z) * (z / (1 + z)) := by
      rw [← sqrt_div_w z (Φ z) hz0 (hΦnn z hz0)]
      refine Real.sqrt_le_sqrt ((le_div_iff₀ hw).mpr ?_)
      rw [mul_comm]
      exact hslot1 z hz0
    have h2 : Real.sqrt (S₂ z) ≤ Real.sqrt (Φ z) * (z / (1 + z)) := by
      rw [← sqrt_div_w z (Φ z) hz0 (hΦnn z hz0)]
      refine Real.sqrt_le_sqrt ((le_div_iff₀ hw).mpr ?_)
      rw [mul_comm]
      exact hslot2 z hz0
    have hΦ0 : 0 ≤ Real.sqrt (Φ z) * (z / (1 + z)) :=
      mul_nonneg (Real.sqrt_nonneg _) (div_nonneg hz0.le (by linarith))
    have hprod : Real.sqrt (S₁ z) * Real.sqrt (S₂ z) ≤ Φ z / Work.Spaces.w z := by
      calc Real.sqrt (S₁ z) * Real.sqrt (S₂ z)
          ≤ (Real.sqrt (Φ z) * (z / (1 + z))) * (Real.sqrt (Φ z) * (z / (1 + z))) :=
            mul_le_mul h1 h2 (Real.sqrt_nonneg _) hΦ0
        _ = (Real.sqrt (Φ z) * (z / (1 + z))) ^ 2 := (sq _).symm
        _ = (Real.sqrt (Φ z)) ^ 2 * (z / (1 + z)) ^ 2 := by rw [mul_pow]
        _ = Φ z / Work.Spaces.w z := by
            rw [Real.sq_sqrt (hΦnn z hz0)]
            rw [Work.Spaces.w]
            field_simp
    have hle : z⁻¹ * (Real.sqrt (S₁ z) * Real.sqrt (S₂ z))
        ≤ Φ z * (z / (1 + z) ^ 2) := by
      calc z⁻¹ * (Real.sqrt (S₁ z) * Real.sqrt (S₂ z))
          ≤ z⁻¹ * (Φ z / Work.Spaces.w z) := mul_le_mul_of_nonneg_left hprod hinv
        _ = Φ z * (z / (1 + z) ^ 2) := zinv_div_w z (Φ z) hz0
    rw [← ENNReal.ofReal_mul hinv]
    refine ENNReal.ofReal_le_ofReal ?_
    calc z⁻¹ * (c * (Real.sqrt (S₁ z) * Real.sqrt (S₂ z)))
        = c * (z⁻¹ * (Real.sqrt (S₁ z) * Real.sqrt (S₂ z))) := by ring
      _ ≤ c * (Φ z * (z / (1 + z) ^ 2)) := mul_le_mul_of_nonneg_left hle hc
  refine (MeasureTheory.lintegral_mono_ae hpt).trans ?_
  have hcontq : ContinuousOn (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi (0 : ℝ)) :=
    continuousOn_id.div ((continuousOn_const.add continuousOn_id).pow 2)
      (fun z hz => pow_ne_zero 2 (ne_of_gt (by linarith [Set.mem_Ioi.mp hz])))
  have hG : IntegrableOn (fun z => c * (Φ z * (z / (1 + z) ^ 2))) (Set.Ioi (0 : ℝ)) := by
    refine Integrable.mono' (g := fun z => c * (Φ z * (1 / 4))) ?_ ?_ ?_
    · exact (hΦint.mul_const (1 / 4)).const_mul c
    · exact ((hΦint.aestronglyMeasurable.mul
        (hcontq.aestronglyMeasurable measurableSet_Ioi)).const_mul c)
    · refine (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono fun z hz => ?_
      have hz0 : 0 < z := hz
      have h1z : (0 : ℝ) < 1 + z := by linarith
      have hq : z / (1 + z) ^ 2 ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [sq_nonneg (1 - z)]
      have hnonneg : (0 : ℝ) ≤ c * (Φ z * (z / (1 + z) ^ 2)) :=
        mul_nonneg hc (mul_nonneg (hΦnn z hz0)
          (div_nonneg hz0.le (by positivity)))
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (hΦnn z hz0)) hc
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hG
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun z hz => mul_nonneg hc (mul_nonneg (hΦnn z (Set.mem_Ioi.mp hz))
        (div_nonneg (Set.mem_Ioi.mp hz).le (by positivity)))))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [MeasureTheory.integral_const_mul]
  have hmono : (∫ z in Set.Ioi (0 : ℝ), Φ z * (z / (1 + z) ^ 2))
      ≤ ∫ z in Set.Ioi (0 : ℝ), Φ z * (1 / 4) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
        (fun z hz => mul_nonneg (hΦnn z (Set.mem_Ioi.mp hz))
          (div_nonneg (Set.mem_Ioi.mp hz).le (by positivity))))
      (hΦint.mul_const _) ?_
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    have h1z : (0 : ℝ) < 1 + z := by linarith [Set.mem_Ioi.mp hz]
    have hq : z / (1 + z) ^ 2 ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [sq_nonneg (1 - z)]
    exact mul_le_mul_of_nonneg_left hq (hΦnn z (Set.mem_Ioi.mp hz))
  calc c * (∫ z in Set.Ioi (0 : ℝ), Φ z * (z / (1 + z) ^ 2))
      ≤ c * (∫ z in Set.Ioi (0 : ℝ), Φ z * (1 / 4)) := mul_le_mul_of_nonneg_left hmono hc
    _ = c * ((1 / 4) * ∫ z in Set.Ioi (0 : ℝ), Φ z) := by
        rw [MeasureTheory.integral_mul_const]
        ring

/-! ## The `ℋ⁴`-integrand slice `Φ` of `g` -/

theorem Phi_int {α : ℝ} {g : ℝ → ℝ → ℝ} (hmem : Work.Spaces.HkMem α 4 g) :
    IntegrableOn (fun r => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
      (Set.Ioi (0 : ℝ)) :=
  hmem.2.mono_set Set.Ioi_subset_Ici_self

theorem Phi_nonneg (α : ℝ) (g : ℝ → ℝ → ℝ) (r : ℝ) :
    0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ :=
  MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α 4 g r θ

theorem Phi_integral {α : ℝ} {g : ℝ → ℝ → ℝ} :
    (∫ r in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ)
      = Work.Spaces.HkSq α 4 g :=
  (Work.FTS.Nonlinear.Pieces.rl1Tools.HkSq_eq_integral_Ioi α g).symm

theorem sqrt_Phi_integral {α : ℝ} {g : ℝ → ℝ → ℝ} :
    Real.sqrt (∫ r in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 4 g r θ) = Work.FTS.Nonlin.Xn α g := by
  rw [Phi_integral]
  rfl

/-! ## The angular slice masses of `g`, `D_θg`, `D_zg` -/

theorem slice_sq_int_g {α : ℝ} {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z, 0 < z → IntegrableOn (fun θ => (g z θ) ^ 2) Work.Spaces.Iθ := by
  intro z hz
  change Integrable (fun θ => (g z θ) ^ 2) (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
  refine Integrable.mono' (g := fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
    ((hmem.1 z hz.le).mono_set (fun θ hθ => ⟨hθ.1.le, hθ.2.le⟩)) ?_ ?_
  · exact (((hsm.curry_θ (by simp only [Set.mem_Ioi]; linarith)).continuousOn).pow 2)
      |>.aestronglyMeasurable measurableSet_Ioo
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hw1 : 1 ≤ Work.Spaces.w z := Work.FTS.Nonlinear.Pieces.rl1Tools.one_le_w_of_pos hz
    have hw0 : 0 ≤ Work.Spaces.w z := Work.FTS.Nonlinear.Pieces.rl1Tools.w_nonneg z
    have hw2 : 1 ≤ (Work.Spaces.w z) ^ 2 := by nlinarith
    have hpt : (Work.Spaces.w z) ^ 2 * (g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      Work.FTS.Nonlinear.Pieces.rl1Tools.w2_sq_le_HkIntegrand α hz hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hpt, hw2, sq_nonneg (g z θ)]

theorem aesm_g_slice {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g) :
    ∀ z, 0 < z → AEStronglyMeasurable (fun θ => g z θ) (volume.restrict Work.Spaces.Iθ) := by
  intro z hz
  change AEStronglyMeasurable (fun θ => g z θ) (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
  exact ((hsm.curry_θ (by simp only [Set.mem_Ioi]; linarith)).continuousOn)
    |>.aestronglyMeasurable measurableSet_Ioo

theorem slot_g_fun {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ r, 0 < r → Work.Spaces.w r * (∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ := by
  intro r hr
  have h2 := Work.FTS.Nonlinear.Pieces.rl1Tools.wsq_mul_slice_le α hα hsm hmem r hr
  have hw1 : 1 ≤ Work.Spaces.w r := Work.FTS.Nonlinear.Pieces.rl1Tools.one_le_w_of_pos hr
  have hw0 : 0 ≤ Work.Spaces.w r := Work.FTS.Nonlinear.Pieces.rl1Tools.w_nonneg r
  have hS0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hw12 : Work.Spaces.w r ≤ (Work.Spaces.w r) ^ 2 := by nlinarith
  calc Work.Spaces.w r * (∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2)
      ≤ (Work.Spaces.w r) ^ 2 * (∫ θ in Work.Spaces.Iθ, (g r θ) ^ 2) :=
        mul_le_mul_of_nonneg_right hw12 hS0
    _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ := h2

/-- The `D_θ`-mass with the `sin(2θ)^{-γ}` weight is integrable: it is dominated by the
`ℋ⁴`-integrand (`w² · (D_θg)² sin(2θ)^{-γ} ≤ HkIntegrand`). -/
theorem slice_Dth_gam_int {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z, 0 < z → IntegrableOn (fun θ => (Work.Spaces.Dth g z θ) ^ 2
      * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ := by
  intro z hz
  change Integrable (fun θ => (Work.Spaces.Dth g z θ) ^ 2
    * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
  refine Integrable.mono' (g := fun θ => Work.Spaces.HkIntegrand α 4 g z θ / (Work.Spaces.w z) ^ 2)
    ((hmem.1 z hz.le).mono_set (fun θ hθ => ⟨hθ.1.le, hθ.2.le⟩) |>.div_const _) ?_ ?_
  · refine (((Work.FTS.Nonlinear.Pieces.rl1Tools.continuousOn_Dth_slice hsm hz).pow 2).mul
      (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn).rpow_const
        (fun θ hθ => Or.inl (ne_of_gt
          (Work.FTS.Nonlinear.Pieces.rl1Tools.sin_two_pos hθ))))).aestronglyMeasurable
      measurableSet_Ioo
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hw : 0 < (Work.Spaces.w z) ^ 2 := by
      have := Work.FTS.Nonlinear.Pieces.rl1Tools.w_pos_of_pos hz
      positivity
    have hpt : (Work.Spaces.w z) ^ 2 * ((Work.Spaces.Dth g z θ) ^ 2
        * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      Work.FTS.Nonlinear.Pieces.rl1Tools.w2_Dth_sq_le_HkIntegrand α hα hz hθ
    have hnn : 0 ≤ (Work.Spaces.Dth g z θ) ^ 2
        * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) :=
      mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (le_of_lt (Work.FTS.Nonlinear.Pieces.rl1Tools.sin_two_pos hθ)) _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, le_div_iff₀ hw]
    calc (Work.Spaces.Dth g z θ) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.w z) ^ 2
        = (Work.Spaces.w z) ^ 2
          * ((Work.Spaces.Dth g z θ) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) := by
          ring
      _ ≤ Work.Spaces.HkIntegrand α 4 g z θ := hpt

theorem slice_sq_int_Dth {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z, 0 < z → IntegrableOn (fun θ => (Work.Spaces.Dth g z θ) ^ 2) Work.Spaces.Iθ := by
  intro z hz
  change Integrable (fun θ => (Work.Spaces.Dth g z θ) ^ 2) (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
  refine Integrable.mono' (g := fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
    ((hmem.1 z hz.le).mono_set (fun θ hθ => ⟨hθ.1.le, hθ.2.le⟩)) ?_ ?_
  · exact ((Work.FTS.Nonlinear.Pieces.rl1Tools.continuousOn_Dth_slice hsm hz).pow 2)
      |>.aestronglyMeasurable measurableSet_Ioo
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hd : (Work.Spaces.Dth g z θ) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
        ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      Work.FTS.Nonlinear.Pieces.rl1Tools.Dth_sq_le_HkIntegrand α hα hz hθ
    have hs := Work.FTS.Nonlinear.Pieces.rl1Tools.sin_two_pos hθ
    have hrp : 1 ≤ Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
      have h := Real.rpow_le_rpow_of_exponent_ge hs (Real.sin_le_one _)
        (show -(Work.Spaces.gam α) ≤ 0 by linarith [Work.Spaces.gam_pos hα])
      rwa [Real.rpow_zero] at h
    have hle : (Work.Spaces.Dth g z θ) ^ 2
        ≤ (Work.Spaces.Dth g z θ) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
      nlinarith [sq_nonneg (Work.Spaces.Dth g z θ)]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    linarith

theorem aesm_Dth_slice {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g) :
    ∀ z, 0 < z → AEStronglyMeasurable (fun θ => Work.Spaces.Dth g z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  intro z hz
  change AEStronglyMeasurable (fun θ => Work.Spaces.Dth g z θ)
    (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
  exact (Work.FTS.Nonlinear.Pieces.rl1Tools.continuousOn_Dth_slice hsm hz)
    |>.aestronglyMeasurable measurableSet_Ioo

/-- `w r · (∫_θ (D_θg)²) ≤ ∫_θ HkIntegrand`. -/
theorem slot_Dth_fun {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α)
    (hsm : Work.FTS.LocData.SmoothQuad g) (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ r, 0 < r → Work.Spaces.w r * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g r θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ := by
  intro r hr
  have h2 := Work.FTS.Nonlinear.Pieces.rl1Tools.wsq_mul_slice_Dth_le α hα hsm hmem r hr
  have hTint := slice_Dth_gam_int hα hsm hmem r hr
  have hmono : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g r θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.Dth g r θ) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => sq_nonneg _) hTint ?_
    change ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
      (Work.Spaces.Dth g r θ) ^ 2
        ≤ (Work.Spaces.Dth g r θ) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
    rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hs := Work.FTS.Nonlinear.Pieces.rl1Tools.sin_two_pos hθ
    have hrp : 1 ≤ Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := by
      have h := Real.rpow_le_rpow_of_exponent_ge hs (Real.sin_le_one _)
        (show -(Work.Spaces.gam α) ≤ 0 by linarith [Work.Spaces.gam_pos hα])
      rwa [Real.rpow_zero] at h
    nlinarith [sq_nonneg (Work.Spaces.Dth g r θ)]
  have hw1 : 1 ≤ Work.Spaces.w r := Work.FTS.Nonlinear.Pieces.rl1Tools.one_le_w_of_pos hr
  have hw0 : 0 ≤ Work.Spaces.w r := Work.FTS.Nonlinear.Pieces.rl1Tools.w_nonneg r
  have hw12 : Work.Spaces.w r ≤ (Work.Spaces.w r) ^ 2 := by nlinarith
  have hS0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g r θ) ^ 2 :=
    MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  calc Work.Spaces.w r * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g r θ) ^ 2)
      ≤ (Work.Spaces.w r) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dth g r θ) ^ 2) :=
        mul_le_mul_of_nonneg_right hw12 hS0
    _ ≤ (Work.Spaces.w r) ^ 2
          * (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.Dth g r θ) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ := h2

theorem slice_sq_int_Dz {α : ℝ} {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z, 0 < z → IntegrableOn (fun θ => (Work.Spaces.Dz g z θ) ^ 2) Work.Spaces.Iθ := by
  intro z hz
  change Integrable (fun θ => (Work.Spaces.Dz g z θ) ^ 2) (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
  refine Integrable.mono' (g := fun θ => Work.Spaces.HkIntegrand α 4 g z θ)
    ((hmem.1 z hz.le).mono_set (fun θ hθ => ⟨hθ.1.le, hθ.2.le⟩)) ?_ ?_
  · have hcd : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => Work.Spaces.Dz g z θ)
        (Set.Ioo 0 (π / 2)) :=
      Work.FTS.LocData.contDiffOn_slice_θ (hsm.DzIter 1) (by simp only [Set.mem_Ioi]; linarith)
    exact (hcd.continuousOn.pow 2).aestronglyMeasurable measurableSet_Ioo
  · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
    have hw1 : 1 ≤ Work.Spaces.w z := Work.FTS.Nonlinear.Pieces.rl1Tools.one_le_w_of_pos hz
    have hpt : Work.Spaces.w z * (Work.Spaces.Dz g z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      Work.FTS.Nonlinear.Pieces.rl1Tools.slot_Dz α hz hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [hpt, hw1, sq_nonneg (Work.Spaces.Dz g z θ)]

theorem aesm_Dz_slice {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g) :
    ∀ z, 0 < z → AEStronglyMeasurable (fun θ => Work.Spaces.Dz g z θ)
      (volume.restrict Work.Spaces.Iθ) := by
  intro z hz
  change AEStronglyMeasurable (fun θ => Work.Spaces.Dz g z θ)
    (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
  have hcd : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ => Work.Spaces.Dz g z θ)
      (Set.Ioo 0 (π / 2)) :=
    Work.FTS.LocData.contDiffOn_slice_θ (hsm.DzIter 1) (by simp only [Set.mem_Ioi]; linarith)
  exact hcd.continuousOn.aestronglyMeasurable measurableSet_Ioo

theorem slot_Dz_fun {α : ℝ} {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ r, 0 < r → Work.Spaces.w r * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz g r θ) ^ 2)
      ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 g r θ := by
  intro r hr
  rw [← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ _ => mul_nonneg (Work.FTS.Nonlinear.Pieces.rl1Tools.w_nonneg r) (sq_nonneg _)))
    (hmem.1 r hr.le) ?_
  change ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
    Work.Spaces.w r * (Work.Spaces.Dz g r θ) ^ 2 ≤ Work.Spaces.HkIntegrand α 4 g r θ
  rw [Work.FTS.Nonlinear.Pieces.rl1Tools.restrict_Iθ_eq_Ioo]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
    (fun θ hθ => Work.FTS.Nonlinear.Pieces.rl1Tools.slot_Dz α hr hθ)

/-! ## The pointwise size of the angular moment `FK g` -/

theorem K_continuous : Continuous fun θ : ℝ => Work.Spaces.K θ := by
  unfold Work.Spaces.K
  fun_prop

theorem K_abs_le_three (θ : ℝ) : |Work.Spaces.K θ| ≤ 3 := by
  have hs : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
  have hc : |Real.cos θ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
  rw [Work.Spaces.K, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  calc 3 * |Real.sin θ| * |Real.cos θ ^ 2| ≤ 3 * 1 * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num)) hc (abs_nonneg _) (by norm_num)
    _ = 3 := by norm_num

theorem fk_pointwise_le {α : ℝ} {g : ℝ → ℝ → ℝ} (hsm : Work.FTS.LocData.SmoothQuad g)
    (hmem : Work.Spaces.HkMem α 4 g) :
    ∀ z, 0 < z → |Work.Construction.FK g z|
      ≤ 3 * Real.sqrt (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) := by
  intro z hz
  have hgint := slice_sq_int_g hsm hmem z hz
  have hgsm := aesm_g_slice hsm z hz
  have hKsm : AEStronglyMeasurable (fun θ => Work.Spaces.K θ) (volume.restrict Work.Spaces.Iθ) :=
    K_continuous.aestronglyMeasurable
  have hgabs : IntegrableOn (fun θ => |g z θ|) Work.Spaces.Iθ := by
    refine Integrable.mono' (g := fun θ => (1 + (g z θ) ^ 2) / 2) ?_ hgsm.norm ?_
    · exact (integrableOn_one_Iθ.add hgint).mul_const (2 : ℝ)⁻¹
    · filter_upwards with θ
      rw [Real.norm_eq_abs, abs_abs]
      have h := sq_nonneg (|g z θ| - 1)
      nlinarith [sq_abs (g z θ), h]
  have hgabs2 : Integrable (fun θ => (|g z θ|) ^ 2) (volume.restrict Work.Spaces.Iθ) :=
    Integrable.congr (show Integrable (fun θ => (g z θ) ^ 2) (volume.restrict Work.Spaces.Iθ)
      from hgint) (Eventually.of_forall fun θ => (sq_abs (g z θ)).symm)
  have hcs := Work.Blocks.IMC.cs_integral_mul_le (volume.restrict Work.Spaces.Iθ)
    (f := fun θ => |g z θ|) (g := fun _ => (1 : ℝ)) hgsm.norm aestronglyMeasurable_const
    hgabs2 (by
      have h : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict Work.Spaces.Iθ) :=
        integrableOn_one_Iθ
      exact h.congr (Eventually.of_forall fun x => by norm_num))
  have hCS : (∫ θ in Work.Spaces.Iθ, |g z θ|)
      ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) * Real.sqrt (Real.pi / 2) := by
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, |g z θ| :=
      MeasureTheory.integral_nonneg fun θ => abs_nonneg _
    have habs : |∫ θ in Work.Spaces.Iθ, |g z θ| * 1| = ∫ θ in Work.Spaces.Iθ, |g z θ| := by
      simp only [mul_one]
      exact abs_of_nonneg hnn
    have hg2 : (∫ θ in Work.Spaces.Iθ, (|g z θ|) ^ 2)
        = ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 :=
      MeasureTheory.integral_congr_ae (Eventually.of_forall fun θ => sq_abs (g z θ))
    have h1 : (∫ θ in Work.Spaces.Iθ, (1 : ℝ) ^ 2) = Real.pi / 2 := by
      rw [show (1 : ℝ) ^ 2 = 1 by norm_num, integral_one_Iθ]
    rw [habs, hg2, h1] at hcs
    exact hcs
  have hInt : IntegrableOn (fun θ => g z θ * Work.Spaces.K θ) Work.Spaces.Iθ := by
    refine Integrable.mono' (g := fun θ => 3 * |g z θ|) (hgabs.const_mul 3)
      (hgsm.mul hKsm) ?_
    filter_upwards with θ
    rw [Real.norm_eq_abs, abs_mul]
    calc |g z θ| * |Work.Spaces.K θ| ≤ |g z θ| * 3 :=
          mul_le_mul_of_nonneg_left (K_abs_le_three θ) (abs_nonneg _)
      _ = 3 * |g z θ| := by ring
  have h1 : |Work.Construction.FK g z| ≤ ∫ θ in Work.Spaces.Iθ, 3 * |g z θ| := by
    rw [Work.Construction.FK]
    refine le_trans (abs_integral_le_integral_abs (f := fun θ => g z θ * Work.Spaces.K θ)) ?_
    refine MeasureTheory.integral_mono_of_nonneg (Eventually.of_forall fun θ => abs_nonneg _)
      (hgabs.const_mul 3) ?_
    filter_upwards with θ
    calc |g z θ * Work.Spaces.K θ| = |g z θ| * |Work.Spaces.K θ| := abs_mul _ _
      _ ≤ |g z θ| * 3 := mul_le_mul_of_nonneg_left (K_abs_le_three θ) (abs_nonneg _)
      _ = 3 * |g z θ| := by ring
  have h2 : (∫ θ in Work.Spaces.Iθ, 3 * |g z θ|)
      ≤ 3 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) * Real.sqrt (Real.pi / 2)) := by
    rw [MeasureTheory.integral_const_mul]
    exact mul_le_mul_of_nonneg_left hCS (by norm_num)
  calc |Work.Construction.FK g z| ≤ ∫ θ in Work.Spaces.Iθ, 3 * |g z θ| := h1
    _ ≤ 3 * (Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) * Real.sqrt (Real.pi / 2)) := h2
    _ = 3 * Real.sqrt (Real.pi / 2) * Real.sqrt (∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2) := by ring

/-! ## The two row engines -/

theorem ggRow_single {N B : ℝ → ℝ → ℝ} {Φ S : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hΦnn : ∀ z, 0 < z → 0 ≤ Φ z) (hΦint : IntegrableOn Φ (Set.Ioi (0 : ℝ)))
    (hslot : ∀ z, 0 < z → Work.Spaces.w z * S z ≤ Φ z)
    (hBS : ∀ z, 0 < z → (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2) ≤ S z)
    (hBsm : ∀ z, 0 < z → AEStronglyMeasurable (fun θ => B z θ)
      (volume.restrict Work.Spaces.Iθ))
    (hBint : ∀ z, 0 < z → IntegrableOn (fun θ => (B z θ) ^ 2) Work.Spaces.Iθ)
    (hpt : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        |Work.Spaces.K θ * N z θ| ≤ c * |B z θ|) :
    (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal z⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |Work.Spaces.K θ * N z θ|))
      ≤ ENNReal.ofReal (2 * c * Real.sqrt (∫ z in Set.Ioi (0 : ℝ), Φ z)) := by
  have hinner : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N z θ|)
        ≤ ENNReal.ofReal (2 * c * Real.sqrt (S z)) := by
    intro z hz
    have hz0 : 0 < z := hz
    calc (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |Work.Spaces.K θ * N z θ|)
        ≤ ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal (c * |B z θ|) := by
          refine MeasureTheory.lintegral_mono_ae ?_
          filter_upwards [hpt z hz] with θ hθ
          exact ENNReal.ofReal_le_ofReal hθ
      _ = ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal c * ENNReal.ofReal |B z θ| :=
          MeasureTheory.lintegral_congr_ae
            (Eventually.of_forall fun θ => ENNReal.ofReal_mul hc)
      _ = ENNReal.ofReal c * ∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |B z θ| :=
          MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal c
            * ENNReal.ofReal (2 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2)) :=
          mul_le_mul_right (inner_abs_lintegral_le (hBsm z hz0) (hBint z hz0)) _
      _ = ENNReal.ofReal (c * (2 * Real.sqrt (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2))) :=
          (ENNReal.ofReal_mul hc).symm
      _ ≤ ENNReal.ofReal (2 * c * Real.sqrt (S z)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hsq : Real.sqrt (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2) ≤ Real.sqrt (S z) :=
            Real.sqrt_le_sqrt (hBS z hz0)
          nlinarith [Real.sqrt_nonneg (∫ θ in Work.Spaces.Iθ, (B z θ) ^ 2), hsq, hc]
  refine (MeasureTheory.lintegral_mono_ae ?_).trans
    (zinv_lintegral_sqrt_le (c := 2 * c) (by linarith) hΦnn hΦint hslot)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
  exact mul_le_mul_right (hinner z hz) (ENNReal.ofReal z⁻¹)

theorem ggRow_prod {N : ℝ → ℝ → ℝ} {Φ S₁ S₂ : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hΦnn : ∀ z, 0 < z → 0 ≤ Φ z) (hΦint : IntegrableOn Φ (Set.Ioi (0 : ℝ)))
    (hslot1 : ∀ z, 0 < z → Work.Spaces.w z * S₁ z ≤ Φ z)
    (hslot2 : ∀ z, 0 < z → Work.Spaces.w z * S₂ z ≤ Φ z)
    (hinner : ∀ z ∈ Set.Ioi (0 : ℝ), (∫⁻ θ in Work.Spaces.Iθ, ENNReal.ofReal |N z θ|)
        ≤ ENNReal.ofReal (c * (Real.sqrt (S₁ z) * Real.sqrt (S₂ z)))) :
    (∫⁻ z in Set.Ioi (0 : ℝ), ENNReal.ofReal z⁻¹ * (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal |N z θ|))
      ≤ ENNReal.ofReal (c * ((1 / 4) * ∫ z in Set.Ioi (0 : ℝ), Φ z)) := by
  refine (MeasureTheory.lintegral_mono_ae ?_).trans
    (zinv_lintegral_prod_sqrt_le hc hΦnn hΦint hslot1 hslot2)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
  exact mul_le_mul_right (hinner z hz) (ENNReal.ofReal z⁻¹)

end Work.FTS.Nonlinear.Pieces.rl1Pieces
