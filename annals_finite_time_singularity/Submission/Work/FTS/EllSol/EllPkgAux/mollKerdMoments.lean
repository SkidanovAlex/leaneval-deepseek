/-
# `Work.FTS.EllSol.EllPkgAux.mollKerdMoments`

Moment and size bounds for the derivative `sKerd ε = deriv (sKer ε)` of the normalised
smooth mollifying bump `sKer ε = (ε * sMass)⁻¹ * sBump (· / ε)` of
`Submission.Work.FTS.EllSol.PkgK5.K5c.MollDefs`.

The kernel `sKer ε` is smooth, even, compactly supported and of total mass one, so:
* `∫ sKerd ε = 0` — the derivative of a compactly supported `C¹` function integrates to `0`;
* `∫ u * sKerd ε u = -∫ sKer ε = -1` — integration by parts;
* `sKer ε t = ε⁻¹ * sKer 1 (t / ε)`, hence `sKerd ε t = ε⁻² * sKerd 1 (t / ε)`, which by the
  change of variables `t ↦ ε t` gives the three size bounds
  `∫ |sKerd ε| ≤ C / ε`, `∫ |u * sKerd ε u| ≤ C`, `∫ u² * |sKerd ε u| ≤ C * ε`.

The constant `C` is `max 1 (max I₁ (max I₂ I₃))` with
`I₁ = ∫ |sKerd 1|`, `I₂ = ∫ |u * sKerd 1 u|`, `I₃ = ∫ u² * |sKerd 1 u|` — all finite because
`sKerd 1` is continuous with compact support.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

open Work.FTS.EllSol.PkgK5.K5c

/-! ### Scaling of `sKer` and of its derivative -/

/-- `sKer ε` is the `ε`-rescaling of `sKer 1`. -/
theorem mk_sKer_eq_scale (ε t : ℝ) : sKer ε t = ε⁻¹ * sKer 1 (t / ε) := by
  rw [sKer, sKer]
  simp only [one_mul, div_one]
  ring

/-- The derivative of `sKer ε` is `ε⁻²` times the rescaled derivative of `sKer 1`. -/
theorem mk_deriv_sKerd_scale (ε t : ℝ) :
    deriv (sKer ε) t = ε⁻¹ * (ε⁻¹ * deriv (sKer 1) (t / ε)) := by
  have h1 : deriv (sKer ε) t = deriv (fun s : ℝ => ε⁻¹ * sKer 1 (s / ε)) t := by
    congr 1
    funext s
    exact mk_sKer_eq_scale ε s
  rw [h1, deriv_const_mul_field]
  congr 1
  rw [show (fun s : ℝ => sKer 1 (s / ε)) = (fun s : ℝ => sKer 1 (ε⁻¹ * s)) from by
        funext s; rw [div_eq_inv_mul]]
  rw [deriv_comp_mul_left]
  simp only [smul_eq_mul]
  rw [div_eq_inv_mul]

/-! ### Change of variables `t ↦ ε t` -/

theorem mk_integral_abs_scale (D : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ t : ℝ, |D (t / ε)| = ε * ∫ y : ℝ, |D y| := by
  have h : ∀ t : ℝ, |D (t / ε)| = |D (ε⁻¹ * t)| := by
    intro t; rw [div_eq_inv_mul]
  simp_rw [h]
  have key := MeasureTheory.Measure.integral_comp_mul_left (g := fun y : ℝ => |D y|) (a := ε⁻¹)
  rw [key, inv_inv, abs_of_pos hε, smul_eq_mul]

theorem mk_integral_abs_mul_scale (D : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ t : ℝ, |t| * |D (t / ε)| = ε ^ 2 * ∫ y : ℝ, |y| * |D y| := by
  have h : ∀ t : ℝ, |t| * |D (t / ε)| = ε * ((fun y : ℝ => |y| * |D y|) (ε⁻¹ * t)) := by
    intro t
    have ht : |t| = ε * |ε⁻¹ * t| := by
      rw [abs_mul, abs_of_pos (inv_pos.mpr hε)]
      field_simp
    rw [div_eq_inv_mul, ht]
    ring
  simp_rw [h]
  rw [MeasureTheory.integral_const_mul]
  have key := MeasureTheory.Measure.integral_comp_mul_left (g := fun y : ℝ => |y| * |D y|)
    (a := ε⁻¹)
  rw [key, inv_inv, abs_of_pos hε, smul_eq_mul]
  ring

theorem mk_integral_sq_abs_scale (D : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∫ t : ℝ, t ^ 2 * |D (t / ε)| = ε ^ 3 * ∫ y : ℝ, y ^ 2 * |D y| := by
  have h : ∀ t : ℝ, t ^ 2 * |D (t / ε)| = ε ^ 2 * ((fun y : ℝ => y ^ 2 * |D y|) (ε⁻¹ * t)) := by
    intro t
    have ht : t ^ 2 = ε ^ 2 * (ε⁻¹ * t) ^ 2 := by
      conv_lhs => rw [show t = ε * (ε⁻¹ * t) from by field_simp]
      ring
    rw [div_eq_inv_mul]
    conv_lhs => rw [ht]
    ring
  simp_rw [h]
  rw [MeasureTheory.integral_const_mul]
  have key := MeasureTheory.Measure.integral_comp_mul_left (g := fun y : ℝ => y ^ 2 * |D y|)
    (a := ε⁻¹)
  rw [key, inv_inv, abs_of_pos hε, smul_eq_mul]
  ring

/-! ### The three L¹-norms of `sKerd ε` -/

theorem mk_integral_abs_deriv_sKer {ε : ℝ} (hε : 0 < ε) :
    (∫ t : ℝ, |deriv (sKer ε) t|) = ε⁻¹ * ∫ y : ℝ, |deriv (sKer 1) y| := by
  have h : ∀ t : ℝ, |deriv (sKer ε) t| = ε⁻¹ * (ε⁻¹ * |deriv (sKer 1) (t / ε)|) := by
    intro t
    rw [mk_deriv_sKerd_scale]
    simp only [abs_mul, abs_of_pos (inv_pos.mpr hε)]
  simp_rw [h]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [mk_integral_abs_scale (deriv (sKer 1)) hε]
  field_simp

theorem mk_integral_abs_mul_deriv_sKer {ε : ℝ} (hε : 0 < ε) :
    (∫ t : ℝ, |t * deriv (sKer ε) t|) = ∫ y : ℝ, |y| * |deriv (sKer 1) y| := by
  have h : ∀ t : ℝ,
      |t * deriv (sKer ε) t| = ε⁻¹ * (ε⁻¹ * (|t| * |deriv (sKer 1) (t / ε)|)) := by
    intro t
    rw [mk_deriv_sKerd_scale]
    simp only [abs_mul, abs_of_pos (inv_pos.mpr hε)]
    ring
  simp_rw [h]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [mk_integral_abs_mul_scale (deriv (sKer 1)) hε]
  field_simp

theorem mk_integral_sq_abs_deriv_sKer {ε : ℝ} (hε : 0 < ε) :
    (∫ t : ℝ, t ^ 2 * |deriv (sKer ε) t|) = ε * ∫ y : ℝ, y ^ 2 * |deriv (sKer 1) y| := by
  have h : ∀ t : ℝ,
      t ^ 2 * |deriv (sKer ε) t| = ε⁻¹ * (ε⁻¹ * (t ^ 2 * |deriv (sKer 1) (t / ε)|)) := by
    intro t
    rw [mk_deriv_sKerd_scale]
    simp only [abs_mul, abs_of_pos (inv_pos.mpr hε)]
    ring
  simp_rw [h]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [mk_integral_sq_abs_scale (deriv (sKer 1)) hε]
  field_simp

/-! ### Continuity, compact support and integrability -/

theorem mk_continuous_sKer (ε : ℝ) : Continuous (sKer ε) := by
  have h : sKer ε = fun t : ℝ => (ε * sMass)⁻¹ * sBump (t / ε) := by
    funext t; rw [sKer]
  rw [h]
  exact continuous_const.mul (sBump_continuous.comp (continuous_id.div_const ε))

theorem mk_hasCompactSupport_sKer {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (sKer ε) := by
  refine HasCompactSupport.of_support_subset_isCompact (K := Set.Icc (-ε) ε) isCompact_Icc ?_
  intro t ht
  rw [Function.mem_support] at ht
  have hlt : |t| < ε := by
    by_contra h
    exact ht (sKer_eq_zero_of_le_abs hε (not_lt.mp h))
  rw [abs_lt] at hlt
  exact ⟨le_of_lt hlt.1, le_of_lt hlt.2⟩

theorem mk_integrable_sKer {ε : ℝ} (hε : 0 < ε) : Integrable (sKer ε) :=
  (mk_continuous_sKer ε).integrable_of_hasCompactSupport (mk_hasCompactSupport_sKer hε)

theorem mk_integrable_deriv_sKer {ε : ℝ} (hε : 0 < ε) : Integrable (deriv (sKer ε)) :=
  (contDiff_sKer ε).continuous_deriv_one.integrable_of_hasCompactSupport
    (mk_hasCompactSupport_sKer hε).deriv

theorem mk_integrable_id_sKer {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : ℝ => x * sKer ε x) :=
  (continuous_id.mul (mk_continuous_sKer ε)).integrable_of_hasCompactSupport
    (mk_hasCompactSupport_sKer hε).mul_left

theorem mk_integrable_id_deriv_sKer {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : ℝ => x * deriv (sKer ε) x) :=
  (continuous_id.mul (contDiff_sKer ε).continuous_deriv_one).integrable_of_hasCompactSupport
    (mk_hasCompactSupport_sKer hε).deriv.mul_left

theorem mk_integrable_sq_deriv_sKer {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : ℝ => x ^ 2 * deriv (sKer ε) x) := by
  have hcs : HasCompactSupport (fun x : ℝ => x * (x * deriv (sKer ε) x)) :=
    (mk_hasCompactSupport_sKer hε).deriv.mul_left.mul_left
  have hcont : Continuous (fun x : ℝ => x * (x * deriv (sKer ε) x)) :=
    continuous_id.mul (continuous_id.mul (contDiff_sKer ε).continuous_deriv_one)
  have hfun : (fun x : ℝ => x ^ 2 * deriv (sKer ε) x)
      = (fun x : ℝ => x * (x * deriv (sKer ε) x)) := by
    funext x; ring
  rw [hfun]
  exact hcont.integrable_of_hasCompactSupport hcs

/-! ### The two moment identities -/

/-- The derivative of the compactly supported mass-one kernel has zero integral. -/
theorem mk_integral_sKerd_eq_zero {ε : ℝ} (hε : 0 < ε) :
    (∫ u : ℝ, deriv (sKer ε) u) = 0 := by
  have hderiv : ∀ x : ℝ, HasDerivAt (sKer ε) (deriv (sKer ε) x) x :=
    fun x => ((contDiff_sKer ε : ContDiff ℝ 1 (sKer ε)).differentiable
      one_ne_zero).differentiableAt.hasDerivAt
  have hintd : Integrable (deriv (sKer ε)) := mk_integrable_deriv_sKer hε
  have key := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun _ : ℝ => (1 : ℝ)) (u' := fun _ : ℝ => (0 : ℝ))
    (v := sKer ε) (v' := fun x : ℝ => deriv (sKer ε) x)
    (fun x _ => hasDerivAt_const x (1 : ℝ))
    (fun x _ => hderiv x)
    (by
      rw [show (fun _ : ℝ => (1 : ℝ)) * (fun x : ℝ => deriv (sKer ε) x)
            = (fun x : ℝ => deriv (sKer ε) x) from by funext x; simp]
      exact hintd)
    (by
      rw [show (fun _ : ℝ => (0 : ℝ)) * sKer ε = (fun _ : ℝ => (0 : ℝ)) from by
            funext x; simp]
      exact integrable_zero ℝ ℝ volume)
    (by
      rw [show (fun _ : ℝ => (1 : ℝ)) * sKer ε = sKer ε from by funext x; simp]
      exact mk_integrable_sKer hε)
  simpa using key

/-- The first moment of `sKerd ε`: `∫ u * sKerd ε u = -∫ sKer ε = -1`. -/
theorem mk_integral_id_sKerd {ε : ℝ} (hε : 0 < ε) :
    (∫ u : ℝ, u * deriv (sKer ε) u) = -1 := by
  have hderiv : ∀ x : ℝ, HasDerivAt (sKer ε) (deriv (sKer ε) x) x :=
    fun x => ((contDiff_sKer ε : ContDiff ℝ 1 (sKer ε)).differentiable
      one_ne_zero).differentiableAt.hasDerivAt
  have key := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => x) (u' := fun _ : ℝ => (1 : ℝ))
    (v := sKer ε) (v' := fun x : ℝ => deriv (sKer ε) x)
    (fun x _ => hasDerivAt_id x)
    (fun x _ => hderiv x)
    (by
      rw [show (fun x : ℝ => x) * (fun x : ℝ => deriv (sKer ε) x)
            = (fun x : ℝ => x * deriv (sKer ε) x) from by funext x; simp]
      exact mk_integrable_id_deriv_sKer hε)
    (by
      rw [show (fun _ : ℝ => (1 : ℝ)) * sKer ε = sKer ε from by funext x; simp]
      exact mk_integrable_sKer hε)
    (by
      rw [show (fun x : ℝ => x) * sKer ε = (fun x : ℝ => x * sKer ε x) from by
            funext x; simp]
      exact mk_integrable_id_sKer hε)
  rw [key]
  simp [sKer_integral_eq_one hε]

/-- **Moments and size bounds of the derivative kernel `sKerd ε`.**

There is a universal constant `C > 0` such that for every `0 < ε ≤ 1/2` the derivative
`sKerd ε = deriv (sKer ε)` of the mollifying kernel is compactly supported and integrable,
together with its first and second moments, has vanishing zeroth moment, has first moment
`-1`, and satisfies the three size bounds
`∫ |sKerd ε| ≤ C / ε`, `∫ |u * sKerd ε u| ≤ C`, `∫ u² * |sKerd ε u| ≤ C * ε`. -/
theorem mollKerdMoments : ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → (∫ u : ℝ, Work.FTS.EllSol.EllPkgAux.sKerd ε u = 0) ∧ (∫ u : ℝ, u * Work.FTS.EllSol.EllPkgAux.sKerd ε u = -1) ∧ (∫ u : ℝ, |Work.FTS.EllSol.EllPkgAux.sKerd ε u| ≤ C / ε) ∧ (∫ u : ℝ, |u * Work.FTS.EllSol.EllPkgAux.sKerd ε u| ≤ C) ∧ (∫ u : ℝ, u ^ 2 * |Work.FTS.EllSol.EllPkgAux.sKerd ε u| ≤ C * ε) ∧ HasCompactSupport (Work.FTS.EllSol.EllPkgAux.sKerd ε) ∧ MeasureTheory.Integrable (Work.FTS.EllSol.EllPkgAux.sKerd ε) ∧ MeasureTheory.Integrable (fun u : ℝ => u * Work.FTS.EllSol.EllPkgAux.sKerd ε u) ∧ MeasureTheory.Integrable (fun u : ℝ => u ^ 2 * Work.FTS.EllSol.EllPkgAux.sKerd ε u) := by
  set I1 : ℝ := ∫ y : ℝ, |deriv (sKer 1) y| with hI1
  set I2 : ℝ := ∫ y : ℝ, |y| * |deriv (sKer 1) y| with hI2
  set I3 : ℝ := ∫ y : ℝ, y ^ 2 * |deriv (sKer 1) y| with hI3
  have h1 : I1 ≤ max 1 (max I1 (max I2 I3)) :=
    le_trans (le_max_left I1 (max I2 I3)) (le_max_right 1 (max I1 (max I2 I3)))
  have h2 : I2 ≤ max 1 (max I1 (max I2 I3)) :=
    le_trans (le_trans (le_max_left I2 I3) (le_max_right I1 (max I2 I3)))
      (le_max_right 1 (max I1 (max I2 I3)))
  have h3 : I3 ≤ max 1 (max I1 (max I2 I3)) :=
    le_trans (le_trans (le_max_right I2 I3) (le_max_right I1 (max I2 I3)))
      (le_max_right 1 (max I1 (max I2 I3)))
  refine ⟨max 1 (max I1 (max I2 I3)), lt_of_lt_of_le zero_lt_one (le_max_left 1 _), ?_⟩
  intro ε hε _hεhalf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [sKerd] using mk_integral_sKerd_eq_zero hε
  · simpa [sKerd] using mk_integral_id_sKerd hε
  · have h := mk_integral_abs_deriv_sKer hε
    simp only [sKerd]
    rw [h, ← hI1, div_eq_mul_inv]
    calc ε⁻¹ * I1 ≤ ε⁻¹ * max 1 (max I1 (max I2 I3)) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hε.le)
      _ = max 1 (max I1 (max I2 I3)) * ε⁻¹ := by ring
  · have h := mk_integral_abs_mul_deriv_sKer hε
    simp only [sKerd]
    rw [h, ← hI2]
    exact h2
  · have h := mk_integral_sq_abs_deriv_sKer hε
    simp only [sKerd]
    rw [h, ← hI3]
    calc ε * I3 ≤ ε * max 1 (max I1 (max I2 I3)) :=
          mul_le_mul_of_nonneg_left h3 hε.le
      _ = max 1 (max I1 (max I2 I3)) * ε := by ring
  · simpa [sKerd] using (mk_hasCompactSupport_sKer hε).deriv
  · simpa [sKerd] using mk_integrable_deriv_sKer hε
  · simpa [sKerd] using mk_integrable_id_deriv_sKer hε
  · simpa [sKerd] using mk_integrable_sq_deriv_sKer hε

end Work.FTS.EllSol.EllPkgAux
