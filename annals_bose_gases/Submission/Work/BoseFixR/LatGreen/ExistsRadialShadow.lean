import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.SmallBoxA0.PolarSphere.integral_eq_sphere_radius
import Submission.Work.SmallBoxA0.PolarSphere.polarNullAe
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Work.BoseFixR.LatGreen

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S" => Metric.sphere (0 : E3) 1

/-! ## Elementary interface lemmas for the radial shadow -/

/-- A point of the unit sphere has norm `1`. -/
lemma norm_coe_unitSphere (ω : S) : ‖(ω : E3)‖ = 1 := by
  simp

/-- **Sphere-slice identity.**  If the sphere slice `{ω | r • ω ∈ N}` is null and `g` agrees with
`x ↦ ψ ‖x‖ * φ x` off `N`, then the spherical averages of `g` and of `ψ r * φ (r • ·)` agree.
The scalar may be pulled out because `integral_const_mul` holds unconditionally. -/
lemma sphereIntegral_eq_of_null_slice {ψ : ℝ → ℝ} {N : Set E3} {g φ : E3 → ℝ} {r : ℝ}
    (hr : 0 < r)
    (hNslice : (volume : Measure E3).toSphere {ω : S | r • (ω : E3) ∈ N} = 0)
    (hgf : ∀ x : E3, x ∉ N → g x = ψ ‖x‖ * φ x) :
    (∫ ω : S, g (r • (ω : E3)) ∂(volume : Measure E3).toSphere)
      = ψ r * ∫ ω : S, φ (r • (ω : E3)) ∂(volume : Measure E3).toSphere := by
  have hnorm : ∀ ω : S, ‖r • (ω : E3)‖ = r := fun ω => by
    rw [norm_smul, Real.norm_of_nonneg hr.le, norm_coe_unitSphere, mul_one]
  have hae : (fun ω : S => g (r • (ω : E3))) =ᵐ[(volume : Measure E3).toSphere]
      (fun ω : S => ψ r * φ (r • (ω : E3))) := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null ?_ hNslice
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    by_contra hmem
    exact hω (by rw [hgf _ hmem, hnorm ω])
  rw [integral_congr_ae hae, integral_const_mul]

/-- If the spherical integral of the square of `φ` vanishes, the spherical integral of `φ`
vanishes (the integrand is nonnegative). -/
lemma sphereIntegral_eq_zero_of_sq_eq_zero {φ : S → ℝ}
    (hint : Integrable (fun ω : S => (φ ω) ^ 2) (volume : Measure E3).toSphere)
    (h : (∫ ω : S, (φ ω) ^ 2 ∂(volume : Measure E3).toSphere) = 0) :
    (∫ ω : S, φ ω ∂(volume : Measure E3).toSphere) = 0 := by
  have h0 : (fun ω : S => (φ ω) ^ 2) =ᵐ[(volume : Measure E3).toSphere] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (φ ω)) hint).mp h
  have h1 : φ =ᵐ[(volume : Measure E3).toSphere] 0 :=
    h0.mono fun ω hω => sq_eq_zero_iff.mp hω
  rw [integral_congr_ae h1]
  simp

/-! ## The three analytic ingredients -/

/-- **Measurability of the spherical average in the radius.**  For a measurable `h` on `ℝ³` the
function `r ↦ ∫_{S²} h (r • ω) dσ(ω)` is measurable: the integrand `(r, ω) ↦ h (r • ω)` is jointly
measurable, so Mathlib's unconditional Fubini measurability
(`MeasureTheory.StronglyMeasurable.integral_prod_right'`) applies. -/
lemma sphereIntegral_measurable {h : E3 → ℝ} (hh : Measurable h) :
    Measurable (fun r : ℝ => ∫ ω : S, h (r • (ω : E3)) ∂(volume : Measure E3).toSphere) := by
  have hsm : StronglyMeasurable (fun p : ℝ × S => h (p.1 • (p.2 : E3))) :=
    (hh.comp (by fun_prop)).stronglyMeasurable
  exact (MeasureTheory.StronglyMeasurable.integral_prod_right' hsm).measurable

/-- **Moment bookkeeping.**  If `ρ` is measurable, vanishes on `[R,∞)`, is dominated by `|ψ|`
a.e. on `(0,∞)` and `r ↦ r|ψ r|` is integrable on `(0,∞)`, then `r ↦ r²|ρ r|` and `r ↦ r|ρ r|`
are integrable on `(0,∞)` and the first moment of `ρ` is at most that of `ψ`. -/
lemma integrableOn_mul_abs_of_le {ρ ψ : ℝ → ℝ} {R : ℝ}
    (hρm : Measurable ρ) (hρ0 : ∀ r : ℝ, R ≤ r → ρ r = 0)
    (hψR : ∀ r : ℝ, R ≤ r → ψ r = 0)
    (hbound : ∀ᵐ r ∂((volume : Measure ℝ).restrict (Set.Ioi (0 : ℝ))), |ρ r| ≤ |ψ r|)
    (hint : IntegrableOn (fun r : ℝ => r * |ψ r|) (Set.Ioi (0 : ℝ))) :
    IntegrableOn (fun r : ℝ => r ^ 2 * |ρ r|) (Set.Ioi (0 : ℝ)) ∧
      IntegrableOn (fun r : ℝ => r * |ρ r|) (Set.Ioi (0 : ℝ)) ∧
      (∫ r in Set.Ioi (0 : ℝ), r * |ρ r|) ≤ ∫ r in Set.Ioi (0 : ℝ), r * |ψ r| := by
  have hρ1 : IntegrableOn (fun r : ℝ => r * |ρ r|) (Set.Ioi (0 : ℝ)) := by
    refine Integrable.mono' hint (f := fun r : ℝ => r * |ρ r|) (g := fun r : ℝ => r * |ψ r|)
      ((measurable_id.mul hρm.abs).aestronglyMeasurable) ?_
    filter_upwards [hbound, ae_restrict_mem measurableSet_Ioi] with r hb hr
    rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos hr]
    exact mul_le_mul_of_nonneg_left hb hr.le
  refine ⟨?_, hρ1, ?_⟩
  · refine Integrable.mono' (g := fun r : ℝ => max 1 R * (r * |ψ r|))
      ((show Integrable (fun r : ℝ => r * |ψ r|) ((volume : Measure ℝ).restrict (Set.Ioi 0))
        from hint).const_mul (max 1 R)) (f := fun r : ℝ => r ^ 2 * |ρ r|)
      ((measurable_id.pow_const 2).mul hρm.abs).aestronglyMeasurable ?_
    filter_upwards [hbound, ae_restrict_mem measurableSet_Ioi] with r hb hr
    have hr0 : 0 ≤ r := hr.le
    have hCpos : (0 : ℝ) < max 1 R := lt_of_lt_of_le one_pos (le_max_left 1 R)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg r), abs_abs]
    by_cases hRr : R ≤ r
    · rw [hρ0 r hRr, hψR r hRr]
      simp
    · have hrR : r < R := not_le.mp hRr
      have hCr : r ≤ max 1 R := le_trans hrR.le (le_max_right 1 R)
      have h1 : r ^ 2 * |ρ r| ≤ max 1 R * (r * |ρ r|) := by
        have hstep : r * |ρ r| ≤ max 1 R * |ρ r| :=
          mul_le_mul_of_nonneg_right hCr (abs_nonneg _)
        have h2 := mul_le_mul_of_nonneg_left hstep hr0
        nlinarith [h2]
      have h3 : max 1 R * (r * |ρ r|) ≤ max 1 R * (r * |ψ r|) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb hr0) hCpos.le
      linarith [h1, h3]
  · refine integral_mono_ae (f := fun r : ℝ => r * |ρ r|) (g := fun r : ℝ => r * |ψ r|)
      hρ1 hint ?_
    filter_upwards [hbound, ae_restrict_mem measurableSet_Ioi] with r hb hr
    exact mul_le_mul_of_nonneg_left hb hr.le

/-- **The radial-weighted function is integrable on `ℝ³`.**  If `r ↦ r²|ρ r|` is integrable on
`(0,∞)` (so `ρ(‖·‖)` is integrable on `ℝ³`) and `|v| ≤ C`, then `x ↦ ρ ‖x‖ * v x` is integrable.
The spherical-coordinates equivalence `MeasureTheory.integrable_fun_norm_addHaar` converts the
radial integrability into the `ℝ³`-integrability of the radial majorant. -/
lemma integrable_radial_mul {ρ : ℝ → ℝ} {v : E3 → ℝ} {C : ℝ}
    (hρm : Measurable ρ)
    (hρ2 : IntegrableOn (fun r : ℝ => r ^ 2 * |ρ r|) (Set.Ioi (0 : ℝ)))
    (hv : ∀ x : E3, |v x| ≤ C)
    (hvmeas : AEStronglyMeasurable v (volume : Measure E3)) :
    Integrable (fun x : E3 => ρ ‖x‖ * v x) (volume : Measure E3) := by
  have hrad : Integrable (fun x : E3 => |ρ ‖x‖| * C) (volume : Measure E3) := by
    rw [MeasureTheory.integrable_fun_norm_addHaar (μ := (volume : Measure E3))
      (f := fun y : ℝ => |ρ y| * C)]
    rw [show Module.finrank ℝ E3 - 1 = 2 from by simp]
    have hC : Integrable (fun y : ℝ => C * (y ^ 2 * |ρ y|))
        ((volume : Measure ℝ).restrict (Set.Ioi 0)) :=
      (show Integrable (fun y : ℝ => y ^ 2 * |ρ y|)
        ((volume : Measure ℝ).restrict (Set.Ioi 0)) from hρ2).const_mul C
    refine IntegrableOn.congr_fun (f := fun y : ℝ => C * (y ^ 2 * |ρ y|)) hC ?_ measurableSet_Ioi
    intro y _
    show C * (y ^ 2 * |ρ y|) = y ^ 2 • (|ρ y| * C)
    rw [smul_eq_mul]; ring
  refine Integrable.mono' hrad (f := fun x : E3 => ρ ‖x‖ * v x) (g := fun x : E3 => |ρ ‖x‖| * C)
    ((hρm.comp measurable_norm).aestronglyMeasurable.mul hvmeas) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (hv x) (abs_nonneg _)

/-- **Radial shadow of an a.e.-radial measurable function** (namespace `Work.BoseFixR.LatGreen`).

Let `w : ℝ³ → ℝ` be integrable and a.e. equal to `x ↦ ψ ‖x‖ · v x`, where `v` is continuous and
bounded, and `ψ` vanishes on `[R,∞)` with `r ↦ r|ψ r|` integrable on `(0,∞)`. **No measurability
is assumed on `ψ`** (this is the point: the sign of `ψ` is invisible to the hypotheses, so the
measurable profile below must be built out of `w` and `v`). Then there is a *measurable* profile
`ρ : ℝ → ℝ`, zero on `[R,∞)`, such that the radial pairing reproduces `∫ w` and whose first moment
is no larger:

`∫ x, w x = ∫ x, ρ ‖x‖ · v x`, `IntegrableOn (fun r => r|ρ r|) (Ioi 0)`,
`∫₀^∞ r|ρ r| ≤ ∫₀^∞ r|ψ r|`.

Construction / proof. Let `N` be a measurable null superset of `{x | w x ≠ ψ ‖x‖ · v x}`
(`MeasureTheory.Measure.exists_measurable_superset_of_null`); off `N`,
`w x · v x = ψ ‖x‖ · (v x)^2` and `|w x| · |v x| = |ψ ‖x‖| · (v x)^2` **pointwise** (no division
needed). Set

`ρ r := (if R ≤ r then 0 else (∫ ω : Metric.sphere (0:ℝ³) 1, w (r•ω) · v (r•ω) ∂volume.toSphere)
        / (∫ ω : Metric.sphere (0:ℝ³) 1, (v (r•ω))^2 ∂volume.toSphere))`  (with `x/0 = 0`).

* `ρ` measurable: both partial integrals are strongly measurable in `r`
  (`MeasureTheory.StronglyMeasurable.integral_prod_left'` applied to the strongly measurable
  `(ω,r) ↦ w (r•ω)·v (r•ω)` and the continuous `(ω,r) ↦ (v (r•ω))^2` on
  `Metric.sphere 0 1 × ℝ`), and division is measurable.
* Slice nullity. For a.e. `r`, the slice `N ∩ S_r` is surface-null. Proof: apply
  `Work.SmallBoxA0.PolarSphere.integral_eq_sphere_radius`
  (`∫ x, f x = ∫ r in Ioi 0, (∫ ω : Metric.sphere 0 1, f (r•ω) ∂volume.toSphere) * r²`) to the
  integrable truncations `f_n x := 1_N x · 1_{‖x‖ ≤ n}`. Its left side is `0` (the integrand
  vanishes off the null set `N`, so `f_n =ᵐ 0`: use `MeasureTheory.integral_congr_ae` with the
  ae-equality supplied by `MeasureTheory.ae_iff` and `N` null), so
  `∫ r in Ioi 0, (1_{r ≤ n} · G r) · r² = 0` where `G r := ∫ ω, 1_N (r•ω) ∂volume.toSphere`. That
  outer integrand is nonnegative, a.e. strongly measurable (Fubini measurability) and bounded by
  `4π n² · 1_{r ≤ n}` (compact support), hence integrable, so
  `MeasureTheory.integral_eq_zero_iff_of_nonneg` gives `1_{r≤n}·G r = 0` for a.e. `r`; as `r > 0`,
  `G r = 0` for a.e. `r ≤ n`. Every `r > 0` is `≤ n` for some `n`, so `G =ᵐ 0` on `Ioi 0`
  (`Filter.Eventually.all` over `ℕ`).
* Consequences for a.e. `r`: the numerator equals `ψ r · ∫ ω, (v (r•ω))² ∂volume.toSphere` and its
  absolute value is at most `|ψ r| · ∫ ω, (v (r•ω))² ∂volume.toSphere` (integrals over the
  surface-null slice vanish, `MeasureTheory.setIntegral_measure_zero`); hence `ρ r = ψ r` when the
  denominator is nonzero, and `|ρ r| ≤ |ψ r|` always. This gives
  `IntegrableOn (fun r => r|ρ r|) (Ioi 0)` and the moment bound (domination by `r|ψ r|`, `hint`).
* Integral identity: apply the polar formula to the integrable `w` and to the integrable
  `x ↦ ρ ‖x‖ · v x` (dominated by `(|ψ| ‖·‖)·sup|v|`); for a.e. `r`,
  `∫ ω, w (r•ω) ∂volume.toSphere = ψ r · ∫ ω, v (r•ω) ∂volume.toSphere` (same slice argument with
  `v` instead of `v²`) and `ρ r · ∫ ω, v (r•ω) ∂volume.toSphere = ψ r · ∫ ω, v (r•ω) ∂volume.toSphere`.

Implementation note (the route actually taken).  The slice-nullity step is not redone from
truncations: it is taken from the already proved `Work.SmallBoxA0.PolarSphere.polarNullAe`
(`Submission/Work/SmallBoxA0/PolarSphere/polarNullAe.lean`), which says that for a measurable null
`N ⊆ ℝ³` and Lebesgue-a.e. `r` the sphere slice `{ω | r • ω ∈ N}` has zero
`volume.toSphere`-measure.  Two further points:
* `ρ` is built out of a *measurable representative* `f` of `w` (`AEMeasurable.mk`), because
  `r ↦ ∫ ω, w (r•ω) v (r•ω) dσ` is in general only a.e. strongly measurable; the measurable
  representative gives genuine measurability of both partial integrals
  (`sphereIntegral_measurable`), while the null set `N` is enlarged to contain `{f ≠ w}` too.
* The integrability of `x ↦ ρ ‖x‖ * v x` on `ℝ³` is obtained from the radial bound
  `∫₀^∞ r² |ρ r| < ∞` (a consequence of the bounded support of `ρ` and `|ρ| ≤ |ψ|` a.e.) via the
  spherical-coordinates equivalence `MeasureTheory.integrable_fun_norm_addHaar`. -/
theorem ExistsRadialShadow {ψ : ℝ → ℝ} {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {w : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hψR : ∀ r : ℝ, R ≤ r → ψ r = 0)
    (hint : MeasureTheory.IntegrableOn (fun r : ℝ => r * |ψ r|) (Set.Ioi (0 : ℝ)))
    (hw : MeasureTheory.AEStronglyMeasurable w MeasureTheory.volume)
    (hwint : MeasureTheory.Integrable w MeasureTheory.volume)
    (hv : Continuous v) (hvbd : ∃ M : ℝ, ∀ x, |v x| ≤ M)
    (h : w =ᵐ[MeasureTheory.volume] fun x : EuclideanSpace ℝ (Fin 3) => ψ ‖x‖ * v x) :
    ∃ ρ : ℝ → ℝ, Measurable ρ ∧ (∀ r : ℝ, R ≤ r → ρ r = 0) ∧
      (∫ x : EuclideanSpace ℝ (Fin 3), w x) = ∫ x : EuclideanSpace ℝ (Fin 3), ρ ‖x‖ * v x ∧
      MeasureTheory.IntegrableOn (fun r : ℝ => r * |ρ r|) (Set.Ioi (0 : ℝ)) ∧
      (∫ r in Set.Ioi (0 : ℝ), r * |ρ r|) ≤ ∫ r in Set.Ioi (0 : ℝ), r * |ψ r| := by
  classical
  -- a bound for `v`
  obtain ⟨M₀, hM₀⟩ := hvbd
  set Cv : ℝ := max M₀ 0 with hCvdef
  have hCv : ∀ x : E3, |v x| ≤ Cv := fun x => le_trans (hM₀ x) (le_max_left _ _)
  have hCvnn : 0 ≤ Cv := le_max_right _ _
  -- a measurable representative of `w`
  have hwaem : AEMeasurable w (volume : Measure E3) := hw.aemeasurable
  set f : E3 → ℝ := AEMeasurable.mk w hwaem with hfdef
  have hfmeas : Measurable f := AEMeasurable.measurable_mk hwaem
  have hfw : w =ᵐ[volume] f := AEMeasurable.ae_eq_mk hwaem
  -- the measurable null set off which everything is radial
  set D : Set E3 := {x : E3 | ¬ (w x = ψ ‖x‖ * v x)} ∪ {x : E3 | ¬ (f x = w x)} with hDdef
  have hD0 : (volume : Measure E3) D = 0 := by
    rw [hDdef, measure_union_null_iff]
    exact ⟨by rw [← ae_iff]; exact h, by rw [← ae_iff]; exact hfw.symm⟩
  set N : Set E3 := toMeasurable (volume : Measure E3) D with hNdef
  have hNmeas : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : (volume : Measure E3) N = 0 := by
    rw [hNdef, measure_toMeasurable]; exact hD0
  have hDN : D ⊆ N := by rw [hNdef]; exact subset_toMeasurable _ _
  have hw_eq : ∀ x : E3, x ∉ N → w x = ψ ‖x‖ * v x := by
    intro x hx
    by_contra hc
    exact hx (hDN (by rw [hDdef]; exact Or.inl hc))
  have hf_eq : ∀ x : E3, x ∉ N → f x = w x := by
    intro x hx
    by_contra hc
    exact hx (hDN (by rw [hDdef]; exact Or.inr hc))
  -- almost every sphere slice of `N` is null, by the polar Fubini theorem
  have hslice : ∀ᵐ r ∂(volume : Measure ℝ),
      (volume : Measure E3).toSphere {ω : S | r • (ω : E3) ∈ N} = 0 :=
    Work.SmallBoxA0.PolarSphere.polarNullAe hNmeas hN0
  have hgood : ∀ᵐ r ∂((volume : Measure ℝ).restrict (Set.Ioi 0)),
      0 < r ∧ (volume : Measure E3).toSphere {ω : S | r • (ω : E3) ∈ N} = 0 := by
    filter_upwards [ae_restrict_of_ae hslice, ae_restrict_mem measurableSet_Ioi] with r h1 h2
    exact ⟨h2, h1⟩
  -- the three profiles
  set Bv : ℝ → ℝ := fun r => ∫ ω : S, v (r • (ω : E3)) ∂(volume : Measure E3).toSphere
    with hBvdef
  set P : ℝ → ℝ :=
    fun r => ∫ ω : S, f (r • (ω : E3)) * v (r • (ω : E3)) ∂(volume : Measure E3).toSphere
    with hPdef
  set Q : ℝ → ℝ :=
    fun r => ∫ ω : S, (v (r • (ω : E3))) ^ 2 ∂(volume : Measure E3).toSphere with hQdef
  set ρ : ℝ → ℝ := fun r => if R ≤ r then 0 else P r / Q r with hρdef
  -- the a.e. identities on the open half line
  have hw_slice : ∀ᵐ r ∂((volume : Measure ℝ).restrict (Set.Ioi 0)),
      (∫ ω : S, w (r • (ω : E3)) ∂(volume : Measure E3).toSphere) = ψ r * Bv r := by
    filter_upwards [hgood] with r hr
    simpa only [hBvdef] using
      sphereIntegral_eq_of_null_slice (ψ := ψ) hr.1 hr.2 hw_eq
  have hP_slice : ∀ᵐ r ∂((volume : Measure ℝ).restrict (Set.Ioi 0)), P r = ψ r * Q r := by
    filter_upwards [hgood] with r hr
    have hmain := sphereIntegral_eq_of_null_slice (ψ := ψ) hr.1 hr.2
      (g := fun x : E3 => f x * v x) (φ := fun x : E3 => (v x) ^ 2)
      (fun x hx => by rw [hf_eq x hx, hw_eq x hx]; ring)
    simpa only [hPdef, hQdef] using hmain
  -- vanishing of the denominator forces vanishing of the `v`-average
  have hQ0 : ∀ r : ℝ, Q r = 0 → Bv r = 0 := by
    intro r hr
    have hcont : Continuous (fun ω : S => (v (r • (ω : E3))) ^ 2) := by fun_prop
    have hint_sq : Integrable (fun ω : S => (v (r • (ω : E3))) ^ 2)
        (volume : Measure E3).toSphere := by
      refine Integrable.of_bound hcont.aestronglyMeasurable (Cv ^ 2) ?_
      filter_upwards with ω
      have h1 : |v (r • (ω : E3))| ≤ Cv := hCv _
      have h2 := pow_le_pow_left₀ (abs_nonneg (v (r • (ω : E3)))) h1 2
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact h2
    rw [hQdef] at hr
    rw [hBvdef]
    exact sphereIntegral_eq_zero_of_sq_eq_zero hint_sq hr
  -- the a.e. bound on `ρ`, and the a.e. identity `ρ r * Bv r = ψ r * Bv r`
  have habs_le : ∀ᵐ r ∂((volume : Measure ℝ).restrict (Set.Ioi 0)), |ρ r| ≤ |ψ r| := by
    filter_upwards [hP_slice] with r hr
    change |(if R ≤ r then 0 else P r / Q r)| ≤ |ψ r|
    by_cases hRr : R ≤ r
    · rw [if_pos hRr, abs_zero]; exact abs_nonneg _
    · rw [if_neg hRr]
      by_cases hQr : Q r = 0
      · rw [hQr, div_zero, abs_zero]; exact abs_nonneg _
      · rw [hr, mul_div_cancel_right₀ _ hQr]
  have hρBv : ∀ᵐ r ∂((volume : Measure ℝ).restrict (Set.Ioi 0)), ρ r * Bv r = ψ r * Bv r := by
    filter_upwards [hP_slice] with r hr
    change (if R ≤ r then 0 else P r / Q r) * Bv r = ψ r * Bv r
    by_cases hRr : R ≤ r
    · rw [if_pos hRr, zero_mul, hψR r hRr, zero_mul]
    · rw [if_neg hRr]
      by_cases hQr : Q r = 0
      · rw [hQr, div_zero, zero_mul, hQ0 r hQr, mul_zero]
      · rw [hr, mul_div_cancel_right₀ _ hQr]
  -- measurability of `ρ`
  have hBv_meas : Measurable Bv := by
    rw [hBvdef]; exact sphereIntegral_measurable hv.measurable
  have hP_meas : Measurable P := by
    rw [hPdef]; exact sphereIntegral_measurable (hfmeas.mul hv.measurable)
  have hQ_meas : Measurable Q := by
    rw [hQdef]; exact sphereIntegral_measurable (hv.measurable.pow_const 2)
  have hρ_meas : Measurable ρ := by
    rw [hρdef]
    exact Measurable.ite measurableSet_Ici measurable_const (hP_meas.div hQ_meas)
  have hρ_zero : ∀ r : ℝ, R ≤ r → ρ r = 0 := by
    intro r hr; rw [hρdef]; exact if_pos hr
  -- integrability and the moment bound
  obtain ⟨hρ2, hρ1, hmoment⟩ := integrableOn_mul_abs_of_le hρ_meas hρ_zero hψR habs_le hint
  have hInt : Integrable (fun x : E3 => ρ ‖x‖ * v x) :=
    integrable_radial_mul hρ_meas hρ2 hCv hv.measurable.aestronglyMeasurable
  -- polar decomposition of both sides
  have hw_polar := Work.SmallBoxA0.PolarSphere.integral_eq_sphere_radius hwint
  have hρ_polar := Work.SmallBoxA0.PolarSphere.integral_eq_sphere_radius hInt
  have hinner : ∀ r ∈ Set.Ioi (0 : ℝ),
      (∫ ω : S, ρ ‖r • (ω : E3)‖ * v (r • (ω : E3)) ∂(volume : Measure E3).toSphere)
        = ρ r * Bv r := by
    intro r hr
    have hnorm : ∀ ω : S, ‖r • (ω : E3)‖ = r := fun ω => by
      rw [norm_smul, Real.norm_of_nonneg (le_of_lt hr), norm_coe_unitSphere, mul_one]
    rw [show (fun ω : S => ρ ‖r • (ω : E3)‖ * v (r • (ω : E3)))
        = (fun ω : S => ρ r * v (r • (ω : E3))) from by
      funext ω; rw [hnorm ω]]
    rw [integral_const_mul, hBvdef]
  refine ⟨ρ, hρ_meas, hρ_zero, ?_, hρ1, hmoment⟩
  calc (∫ x : E3, w x)
      = ∫ r in Set.Ioi (0 : ℝ),
          (∫ ω : S, w (r • (ω : E3)) ∂(volume : Measure E3).toSphere) * r ^ 2 := hw_polar
    _ = ∫ r in Set.Ioi (0 : ℝ), (ψ r * Bv r) * r ^ 2 := by
        refine integral_congr_ae ?_
        filter_upwards [hw_slice] with r hr
        rw [hr]
    _ = ∫ r in Set.Ioi (0 : ℝ), (ρ r * Bv r) * r ^ 2 := by
        refine integral_congr_ae ?_
        filter_upwards [hρBv] with r hr
        rw [hr]
    _ = ∫ r in Set.Ioi (0 : ℝ),
          (∫ ω : S, ρ ‖r • (ω : E3)‖ * v (r • (ω : E3)) ∂(volume : Measure E3).toSphere)
            * r ^ 2 := by
        refine integral_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        rw [hinner r hr]
    _ = ∫ x : E3, ρ ‖x‖ * v x := hρ_polar.symm

end Work.BoseFixR.LatGreen
