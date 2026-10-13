import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.RegQ
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.OpenQAux
import Submission.Work.FTS.EllipticEst.Fstar_Hk_le_open
import Submission.Work.FTS.EllipticEst.integrableOn_Bmom_div
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.FTS.EllipticEst.UopHk.GsingFactsInterior
import Submission.Work.FTS.EllipticEst.UopHk.Gsing_cDiff_kp1
import Submission.Work.FTS.EllipticEst.remov.SourceBound.weakSliceBounds
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceMomentIdentity
import Submission.Work.FTS.EllipticEst.remov.SourceBound.sliceTendstoZeroOfMoment
import Submission.Work.FTS.EllipticEst.Endpt.Lzero1_integral_eq_neg_limit
import Submission.Work.FTS.EllipticEst.Endpt.slice_regularity_of_uncurry
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.FTS.EllipticEst.Endpt.Lzero1_slice_mul_integrable
import Submission.Work.Elliptic.integral_sin_two_mul_sinCos2
import Submission.Work.Elliptic.Gsing_ode
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option linter.unusedVariables false

/-!
# `OrthCond_lambda_zero`: the `θ → 0⁺` trace of a solution with orthogonal data vanishes

Target: for `0 < α ≤ 1/4`, `k ≥ 2`, a datum `(F,Ψ)` of the trace-free class `EllHypT α k F Ψ`
satisfying the orthogonality condition

  `OrthCond (fun z θ => Ψ z θ + Gsing α F z · sin 2θ)`

(equivalently `F_*(Ψ) = -(4/15) Gsing α F`), the angular slice `θ ↦ Ψ z θ` tends to `0` at
`θ → 0⁺` for **every** `z > 0`.

## Route

Write `B_j = Bmom Ψ j` for the `j`-th radial moment `∫_θ D_z^jΨ·sinθcos²θ` and
`Λ(z) = lim_{θ→0⁺} Ψ z θ`.  Two facts about `Λ` are available in the workspace:

* the `θ`-integration by parts `∫_θ Lzero1(Ψ z ·)·sinθcos²θ = -Λ(z)`
  (`Endpt.Lzero1_integral_eq_neg_limit`), with the existence of `Λ` from
  `remov.SourceBound.auxLimitAtZero`;
* the decomposition of the *same* integral along the equation
  (`remov.SourceBound.moment_decomposition`):

  `-Λ(z) = F_*(F)(z) + α²z²M₂(z) + α(5+α)zM₁(z)`,  `M_j = ∫_θ ∂_z^jΨ·sinθcos²θ`.

So the whole content is the pointwise identity

  **(S)**  `F_*(F)(z) + α²B₂(z) + 5αB₁(z) = 0`  for every `z > 0`

(the relation between the plain moments `M_j` and the `D_z`-moments `B_j` being `B₁ = zM₁`,
`B₂ = B₁ + z²M₂`).

The function `Sfun = B₀(F) + α²B₂ + 5αB₁` is

* **continuous** on `(0,∞)`: `B₀(F)` and `B₁` are moments of `F` and `Ψ`, and
  `B₂ = B₁ + B₀(z²∂_zzΨ)` is a moment of `z²∂_zzΨ` — all continuous by
  `Fstar_Hk_le_open.continuousOn_Bmom`;
* **zero almost everywhere**: `OrthCond` gives `B₀(Ψ) = -(4/15) Gsing α F`, the moment tower
  `Fstar_Hk_le_open.ae_hasDerivAt_Bmom` gives `B₁' = B₂/z` a.e., so with `Gsing ∈ C²`
  (`UopHk.Gsing_cDiff_kp1`) and the Euler ODE for `Gsing` (`Elliptic.Gsing_ode`) one gets
  `B₁ = -(4/15) z ∂_zGsing` and `B₂ = -(4/15) z(∂_zGsing + z∂_zzGsing)` a.e., whence

  `Sfun = F_*(F) - (4/15)(α²z²G'' + α(5+α)zG') = F_*(F) - F_*(F) = 0`  a.e.

A continuous function vanishing a.e. on `(0,∞)` vanishes identically, which is **(S)**; the
endpoint data then give `Λ = 0`.
-/

/-! ## The function whose vanishing is proved -/

/-- `Sfun α F Ψ = B₀(F) + α²B₂(Ψ) + 5αB₁(Ψ)`, the combination for which the equation, the
orthogonality condition and the `Gsing`-ODE give both continuity and a.e. vanishing. -/
def Sfun (α : ℝ) (F Ψ : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun w => Work.FTS.EllipticEst.Bmom F 0 w + α ^ 2 * Work.FTS.EllipticEst.Bmom Ψ 2 w
    + 5 * α * Work.FTS.EllipticEst.Bmom Ψ 1 w

/-! ## Elementary integrability and moment identities -/

/-- `θ ↦ sin 2θ · sinθcos²θ` is integrable on `Iθ` (it is continuous and bounded). -/
theorem integrableOn_sin_two_mul_sinCos2 :
    IntegrableOn (fun θ : ℝ => Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := by
  have hvol : (volume : Measure ℝ) Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  refine MeasureTheory.IntegrableOn.of_bound hvol.lt_top ?_ 1 ?_
  · exact ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
      (by unfold Work.Elliptic.sinCos2; fun_prop)).aestronglyMeasurable
  · filter_upwards with θ
    rw [Real.norm_eq_abs, abs_mul]
    have h1 : |Real.sin (2 * θ)| ≤ 1 := Real.abs_sin_le_one (2 * θ)
    have h2 : |Work.Elliptic.sinCos2 θ| ≤ 1 := by
      rw [Work.Elliptic.sinCos2, abs_mul, abs_pow]
      nlinarith [Real.abs_sin_le_one θ, Real.abs_cos_le_one θ, abs_nonneg (Real.cos θ)]
    calc |Real.sin (2 * θ)| * |Work.Elliptic.sinCos2 θ| ≤ 1 * 1 :=
          mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
      _ = 1 := by ring

/-- `F_*` of a slice plus `c(z)·sin 2θ`: `F_*(Φ + c·sin 2θ) = F_*(Φ) + (4/15)·c`. -/
theorem Fstar_add_sin_fun (Φ : ℝ → ℝ → ℝ) (c : ℝ → ℝ) {z : ℝ}
    (hΦ : IntegrableOn (fun θ : ℝ => Φ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) :
    Work.Elliptic.Fstar (fun z θ => Φ z θ + c z * Real.sin (2 * θ)) z
      = Work.Elliptic.Fstar Φ z + c z * (4 / 15) := by
  rw [Work.Elliptic.Fstar, Work.Elliptic.Fstar]
  rw [show (∫ θ in Work.Spaces.Iθ,
        (Φ z θ + c z * Real.sin (2 * θ)) * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ,
          (Φ z θ * Work.Elliptic.sinCos2 θ
            + c z * (Real.sin (2 * θ) * Work.Elliptic.sinCos2 θ)) from
    setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [MeasureTheory.integral_add hΦ (integrableOn_sin_two_mul_sinCos2.const_mul (c z)),
    MeasureTheory.integral_const_mul, Work.Elliptic.integral_sin_two_mul_sinCos2]

/-- **Slice integrability of `g z · · sinθcos²θ` from level-`0` honesty.**  For `g` continuous on
the open quadrant with `HkMem α 0 g`, the absorption
`|g z θ·sinθcos²θ| ≤ (g z θ·w z/sin(2θ)^{η/2})² + 1` and the honesty of the level-`0` integrand
give integrability of the slice for every `z > 0`. -/
theorem integrableOn_slice_mul_sinCos2 {α : ℝ} {g : ℝ → ℝ → ℝ} {z : ℝ}
    (hcont : ContinuousOn (Function.uncurry g) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmem : Work.Spaces.HkMem α 0 g) (hz : 0 < z) :
    IntegrableOn (fun θ : ℝ => g z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ := by
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr (le_of_lt hz)
  have h1 : IntegrableOn (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 g z θ) Work.Spaces.Iθ :=
    hmem.1 z hzI
  have hvol : (volume : Measure ℝ) Work.Spaces.Iθ ≠ ⊤ := by
    rw [Work.Spaces.Iθ, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  have h2 : IntegrableOn
      (fun θ : ℝ => Work.Spaces.HkIntegrand α 0 g z θ + 1) Work.Spaces.Iθ :=
    h1.add (integrableOn_const hvol)
  have hsc : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    unfold Work.Elliptic.sinCos2
    fun_prop
  have haesm : AEStronglyMeasurable (fun θ : ℝ => g z θ * Work.Elliptic.sinCos2 θ)
      (volume.restrict Work.Spaces.Iθ) :=
    Work.Spaces.aesm_slice_of_continuousOn_Qd
      (fun p : ℝ × ℝ => g p.1 p.2 * Work.Elliptic.sinCos2 p.2) (hcont.mul hsc) hz
  refine Integrable.mono' h2 haesm ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with θ hθ
  rw [Real.norm_eq_abs]
  have hb := abs_mul_sinCos2_le_weighted (f := fun θ : ℝ => g z θ) hz hθ
  have hkey : Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    simp [Work.Spaces.HkIntegrand]
  rw [hkey]
  linarith [hb]

/-- `B₁ = z·M₁`: the first `D_z`-moment is the plain first moment times `z`. -/
theorem Bmom_one_eq {Ψ : ℝ → ℝ → ℝ} {z : ℝ}
    (hint : IntegrableOn (fun θ : ℝ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.Bmom Ψ 1 z
      = z * ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ := by
  simp only [Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter, Work.Spaces.DzIter_succ,
    Work.Spaces.DzIter_zero, Work.Spaces.Dz, Work.Spaces.pz, Work.Elliptic.Fstar]
  rw [show (∫ θ in Work.Spaces.Iθ,
        (z * (fun θ' : ℝ => deriv (fun z' : ℝ => Ψ z' θ') z) θ)
          * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ,
          z * (deriv (fun z' : ℝ => Ψ z' θ) z * Work.Elliptic.sinCos2 θ) from
    setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [MeasureTheory.integral_const_mul]

/-- `B₀(z²∂_zzΨ) = z²·M₂`: the level-`0` moment of `w ↦ w²∂_zzΨ` is `z²` times the second plain
angular moment. -/
theorem Bmom_zero_zsq {Ψ : ℝ → ℝ → ℝ} {z : ℝ}
    (hint : IntegrableOn (fun θ : ℝ => Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.Bmom (fun w θ => w ^ 2 * Work.Spaces.pzIter 2 Ψ w θ) 0 z
      = z ^ 2 * ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ := by
  simp only [Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter, Work.Spaces.DzIter_zero,
    Work.Elliptic.Fstar]
  rw [show (∫ θ in Work.Spaces.Iθ,
        (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ,
          z ^ 2 * (Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ) from
    setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [MeasureTheory.integral_const_mul]

/-- **The `D_z`-splitting of the second moment**: `D_z² = D_z + z²∂_z²`, hence
`B₂ = B₁ + B₀(z²∂_zzΨ)` for every `z > 0`. -/
theorem Bmom_two_eq {Ψ : ℝ → ℝ → ℝ} {z : ℝ} (hΨopen : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hz : 0 < z)
    (hA : IntegrableOn (fun θ : ℝ => Work.Spaces.DzIter 1 Ψ z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ)
    (hB : IntegrableOn (fun θ : ℝ =>
      (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.Bmom Ψ 2 z
      = Work.FTS.EllipticEst.Bmom Ψ 1 z
        + Work.FTS.EllipticEst.Bmom (fun w θ => w ^ 2 * Work.Spaces.pzIter 2 Ψ w θ) 0 z := by
  -- the pointwise identity `D_z(D_zΨ) = D_zΨ + z²∂_z²Ψ` on the angular interval
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.DzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ
        = (Work.Spaces.DzIter 1 Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          * Work.Elliptic.sinCos2 θ := by
    intro θ hθ
    rcases eq_or_lt_of_le hθ.1 with h0 | h0
    · subst h0; simp [Work.Elliptic.sinCos2]
    rcases eq_or_lt_of_le hθ.2 with hpi | hpi
    · subst hpi; simp [Work.Elliptic.sinCos2, Real.cos_pi_div_two]
    have hder0 : HasDerivAt (fun w : ℝ => Work.Spaces.pz Ψ w θ)
        (Work.Spaces.pzIter 2 Ψ z θ) z :=
      hΨopen.hasDerivAt_slice_pzIter 1 ⟨h0, hpi⟩ hz
    have hprod : HasDerivAt (fun w : ℝ => w * Work.Spaces.pz Ψ w θ)
        (Work.Spaces.pz Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ) z := by
      have hh := (hasDerivAt_id z).mul hder0
      have hfun : (id * fun w : ℝ => Work.Spaces.pz Ψ w θ)
          = fun w : ℝ => w * Work.Spaces.pz Ψ w θ := by
        funext w; simp only [Pi.mul_apply, id_eq]
      rw [hfun] at hh
      simpa only [one_mul, id_eq] using hh
    have hval : Work.Spaces.pz (Work.Spaces.Dz Ψ) z θ
        = Work.Spaces.pz Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ := by
      have hfun : (fun w : ℝ => Work.Spaces.Dz Ψ w θ)
          = fun w : ℝ => w * Work.Spaces.pz Ψ w θ := by
        funext w; simp only [Work.Spaces.Dz]
      rw [Work.Spaces.pz, hfun]
      exact hprod.deriv
    have hD2 : Work.Spaces.DzIter 2 Ψ z θ
        = Work.Spaces.DzIter 1 Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ := by
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero, Work.Spaces.Dz]
      rw [hval]; ring
    rw [hD2]
  simp only [Work.FTS.EllipticEst.Bmom_eq_Fstar_DzIter, Work.Spaces.DzIter_zero,
    Work.Elliptic.Fstar]
  rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.DzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter 1 Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
            * Work.Elliptic.sinCos2 θ from by
    rw [Work.Spaces.Iθ]
    exact setIntegral_congr_fun measurableSet_Icc hpt]
  rw [show (∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.DzIter 1 Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          * Work.Elliptic.sinCos2 θ)
      = ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter 1 Ψ z θ * Work.Elliptic.sinCos2 θ
            + (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) * Work.Elliptic.sinCos2 θ) from
    setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [MeasureTheory.integral_add hA hB]

/-- **The orthogonality condition in the form used below**: `F_*(Ψ) = -(4/15)·Gsing α F`. -/
theorem Fstar_eq_neg_Gsing {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} {z : ℝ}
    (hint : IntegrableOn (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ)
    (hOrth : Work.Elliptic.OrthCond
      (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))) :
    Work.Elliptic.Fstar Ψ z = -(4 / 15) * Work.Elliptic.Gsing α F z := by
  have h := hOrth z
  rw [Fstar_add_sin_fun Ψ (Work.Elliptic.Gsing α F) hint] at h
  linarith [h]

/-- **A continuous function on `(0,∞)` vanishing almost everywhere vanishes identically.**  For
`w > 0` the primitive `x ↦ ∫_{w/2}^x f` is identically zero near `w` (the integrand is `0` a.e.
on the whole half-line), so its derivative `f w` is `0`. -/
theorem eq_zero_of_continuousOn_of_ae_eq_zero {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ioi 0))
    (hae : ∀ᵐ w ∂(volume : Measure ℝ), w ∈ Set.Ioi (0 : ℝ) → f w = 0) :
    ∀ w ∈ Set.Ioi (0 : ℝ), f w = 0 := by
  intro w hw
  have hw0 : 0 < w := hw
  obtain ⟨a, ha0, haw⟩ : ∃ a : ℝ, 0 < a ∧ a < w := ⟨w / 2, by linarith, by linarith⟩
  have hsub : Set.uIcc a w ⊆ Set.Ioi 0 := by
    rw [Set.uIcc_of_le haw.le]
    intro x hx
    exact lt_of_lt_of_le ha0 hx.1
  have hIi : IntervalIntegrable f volume a w := (hcont.mono hsub).intervalIntegrable
  have hzero : ∀ x ∈ Set.Ici a, (∫ u in a..x, f u) = 0 := by
    intro x hx
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hx) with hx' | hx'
    · subst hx'; simp
    · rw [intervalIntegral.integral_of_le hx'.le]
      have hae' : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.Ioc a x → f u = (0 : ℝ) := by
        filter_upwards [hae] with u hu huI
        exact hu (lt_trans ha0 huI.1)
      rw [MeasureTheory.setIntegral_congr_ae measurableSet_Ioc hae']
      simp
  have hderiv : HasDerivAt (fun x : ℝ => ∫ u in a..x, f u) (f w) w :=
    intervalIntegral.integral_hasDerivAt_right hIi
      (hcont.stronglyMeasurableAtFilter isOpen_Ioi w hw0)
      (hcont.continuousAt (isOpen_Ioi.mem_nhds hw0))
  have heq : (fun x : ℝ => ∫ u in a..x, f u) =ᶠ[𝓝 w] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds haw] with x hx
    exact hzero x (Set.mem_Ici.mpr (le_of_lt hx))
  have hd0 : HasDerivAt (fun _ : ℝ => (0 : ℝ)) (f w) w :=
    hderiv.congr_of_eventuallyEq heq.symm
  exact hd0.unique (hasDerivAt_const w (0 : ℝ))

/-! ## The target -/

theorem OrthCond_lambda_zero (α : ℝ) (k : ℕ) (hk : 2 ≤ k) (F Ψ : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα4 : α ≤ 1 / 4) (hHyp : Work.FTS.EllipticEst.EllHypT α k F Ψ)
    (hOrth : Work.Elliptic.OrthCond (fun z θ => Ψ z θ + Work.Elliptic.Gsing α F z * Real.sin (2 * θ))) :
    ∀ z : ℝ, 0 < z → Filter.Tendsto (fun θ : ℝ => Ψ z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hα1 : α ≤ 1 := by linarith
  have hk1 : 1 ≤ k := by omega
  -- ## open-quadrant smoothness and honesty of the pieces
  have hΨopen : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.UopHk.smoothOpen_of_smoothQuad hHyp.quadPsi
  have hΨforall : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall Ψ).mp hΨopen
  have hΨmem : Work.Spaces.HkMem α k Ψ := hHyp.memPsi
  have hΨmem0 : Work.Spaces.HkMem α 0 Ψ :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (by omega) hΨforall hΨmem
  have hDth2mem : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 Ψ) := hHyp.memDth2
  have hDth2forall : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
      (Work.FTS.EllipticEst.remov.SourceBound.smoothOpen_pthIter hΨopen 2)
  have hDth2mem0 : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 Ψ) :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (by omega) hDth2forall hDth2mem
  have hFopen : Work.FTS.EllipticEst.SmoothOpen F :=
    Work.FTS.EllipticEst.UopHk.smoothOpen_of_smoothQuad hHyp.quadF
  have hFforall : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall F).mp hFopen
  have hFmem : Work.Spaces.HkMem α k F := hHyp.regF.2.1
  have hFmem0 : Work.Spaces.HkMem α 0 F :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (by omega) hFforall hFmem
  -- ## the auxiliary function `w ↦ w²∂_z²Ψ w`
  have hgforall : ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (fun w θ => w ^ 2 * Work.Spaces.pzIter 2 Ψ w θ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    intro n
    have h1 : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pzIter 2 Ψ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp
        (Work.FTS.EllipticEst.SmoothOpen.pzIter hΨopen 2) n
    have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1 ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (contDiff_fst.pow 2).contDiffOn
    have hu : Function.uncurry (fun w θ => w ^ 2 * Work.Spaces.pzIter 2 Ψ w θ)
        = fun p : ℝ × ℝ => p.1 ^ 2 * Function.uncurry (Work.Spaces.pzIter 2 Ψ) p := by
      rfl
    rw [hu]
    exact h2.mul h1
  have hgmem : Work.Spaces.HkMem α k (fun w θ => w ^ 2 * Work.Spaces.pzIter 2 Ψ w θ) :=
    hHyp.memZ2
  have hgmem0 : Work.Spaces.HkMem α 0 (fun w θ => w ^ 2 * Work.Spaces.pzIter 2 Ψ w θ) :=
    Work.FTS.EllipticEst.TT.HkMem_descend_open (by omega) hgforall hgmem
  have hgcont : ContinuousOn (Function.uncurry (fun w θ => w ^ 2 * Work.Spaces.pzIter 2 Ψ w θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (hgforall 0).continuousOn
  -- ## slicewise integrability of the plain moments
  have h2m_all : ∀ w ∈ Set.Ioi (0 : ℝ),
      IntegrableOn (fun θ : ℝ => Work.Spaces.pzIter 2 Ψ w θ * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ := by
    intro w hw
    have hgint : IntegrableOn
        (fun θ : ℝ => (w ^ 2 * Work.Spaces.pzIter 2 Ψ w θ) * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ := integrableOn_slice_mul_sinCos2 hgcont hgmem0 hw
    have h := hgint.const_mul ((w ^ 2)⁻¹)
    refine h.congr (Eventually.of_forall fun θ => ?_)
    show (w ^ 2)⁻¹ * (w ^ 2 * Work.Spaces.pzIter 2 Ψ w θ * Work.Elliptic.sinCos2 θ)
        = Work.Spaces.pzIter 2 Ψ w θ * Work.Elliptic.sinCos2 θ
    rw [show (w ^ 2 * Work.Spaces.pzIter 2 Ψ w θ * Work.Elliptic.sinCos2 θ)
        = w ^ 2 * (Work.Spaces.pzIter 2 Ψ w θ * Work.Elliptic.sinCos2 θ) from by ring]
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 (ne_of_gt hw)), one_mul]
  -- ## the splitting `B₂ = B₁ + B₀(w²∂_z²Ψ)`
  have hsplit2 : ∀ w ∈ Set.Ioi (0 : ℝ),
      Work.FTS.EllipticEst.Bmom Ψ 2 w
        = Work.FTS.EllipticEst.Bmom Ψ 1 w
          + Work.FTS.EllipticEst.Bmom (fun w θ => w ^ 2 * Work.Spaces.pzIter 2 Ψ w θ) 0 w := by
    intro w hw
    have hA : IntegrableOn
        (fun θ : ℝ => Work.Spaces.DzIter 1 Ψ w θ * Work.Elliptic.sinCos2 θ)
        Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.integrableOn_DzIter_mul_sinCos2 α k hΨopen hΨmem 1 (by omega) hw
    exact Bmom_two_eq hΨopen hw hA (integrableOn_slice_mul_sinCos2 hgcont hgmem0 hw)
  -- ## `OrthCond` gives `B₀(Ψ) = -(4/15)·Gsing`
  have hM0 : ∀ w ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.Fstar Ψ w = -(4 / 15) * Work.Elliptic.Gsing α F w :=
    fun w hw => Fstar_eq_neg_Gsing
      (integrableOn_slice_mul_sinCos2 (α := α) hΨopen.continuousOn hΨmem0 hw) hOrth
  -- ## regularity of `Gsing` and its derivative data
  have hG2 : ContDiffOn ℝ 2 (Work.Elliptic.Gsing α F) (Set.Ioi 0) :=
    (Work.FTS.EllipticEst.UopHk.Gsing_cDiff_kp1 α k F hα hα1 hk hHyp.regF).1 2 (by omega)
  have hGderiv : ∀ w ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Gsing α F) (deriv (Work.Elliptic.Gsing α F) w) w :=
    fun w hw => ((hG2.differentiableOn (by norm_num)).differentiableAt
      (isOpen_Ioi.mem_nhds hw)).hasDerivAt
  have hFstar_sm : ContDiffOn ℝ (k - 1) (Work.Elliptic.Fstar F) (Set.Ioi 0) :=
    Work.FTS.EllipticEst.UopHk.contDiffOn_Fstar_of_smoothOpen_Hk α k F hFopen hFmem hk1
  have hFc : ∀ w ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) w) w := by
    intro w hw
    have h1 : ContDiffOn ℝ 1 (Work.Elliptic.Fstar F) (Set.Ioi 0) := by
      have hle : ((1 : ℕ) : ℕ∞ω) ≤ ((k - 1 : ℕ) : ℕ∞ω) := by
        exact_mod_cast (by omega : 1 ≤ k - 1)
      exact hFstar_sm.of_le hle
    exact ((h1.differentiableOn (by simp)).differentiableAt
      (isOpen_Ioi.mem_nhds hw)).hasDerivAt
  have hL12diff : ∀ w ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.L12 F) (-(3 * Work.Elliptic.Fstar F w / w)) w :=
    (Work.FTS.EllipticEst.UopHk.contDiffOn_L12_of_smoothOpen_Hk α k F hFopen hFmem hk).2
  have hJ : ∀ w ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Jfun α F)
        (w ^ ((5 - α) / α) * Work.Elliptic.Fstar F w) w := by
    intro w hw
    have h := (Work.FTS.EllipticEst.UopHk.contDiffOn_Jfun_of_smoothOpen_Hk
      α k F hα hα1 hFopen hFmem hk).2 w hw
    have hfun : (fun z' : ℝ => ∫ s in (0 : ℝ)..z',
        s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s) = Work.Elliptic.Jfun α F := rfl
    rwa [hfun] at h
  have hode : ∀ w ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * w ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') w
        + α * (5 + α) * w * deriv (Work.Elliptic.Gsing α F) w
      = (15 / 4) * Work.Elliptic.Fstar F w :=
    Work.Elliptic.Gsing_ode α F hα hL12diff hFc hJ
  -- ## `B₁ = -(4/15)·w·G'(w)`
  have hhat1 : ∀ w ∈ Set.Ioi (0 : ℝ),
      Work.FTS.EllipticEst.Bmom Ψ 1 w
        = -(4 / 15) * (w * deriv (Work.Elliptic.Gsing α F) w) := by
    intro w hw
    have h1 : HasDerivAt (fun w => Work.FTS.EllipticEst.Bmom Ψ 0 w)
        (Work.FTS.EllipticEst.Bmom Ψ 1 w / w) w :=
      Work.FTS.EllipticEst.hasDerivAt_Bmom α k hΨopen hΨmem 0 (by omega) hw
    have h2 : HasDerivAt (fun w => Work.FTS.EllipticEst.Bmom Ψ 0 w)
        (-(4 / 15) * deriv (Work.Elliptic.Gsing α F) w) w := by
      have hd : HasDerivAt (fun w => -(4 / 15) * Work.Elliptic.Gsing α F w)
          (-(4 / 15) * deriv (Work.Elliptic.Gsing α F) w) w :=
        (hGderiv w hw).const_mul (-(4 / 15))
      refine hd.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Ioi.mem_nhds hw] with w' hw'
      rw [Work.FTS.EllipticEst.Bmom_zero]
      exact hM0 w' hw'
    have huniq : Work.FTS.EllipticEst.Bmom Ψ 1 w / w
        = -(4 / 15) * deriv (Work.Elliptic.Gsing α F) w := h1.unique h2
    rw [div_eq_iff (ne_of_gt hw)] at huniq
    rw [huniq]; ring
  -- ## `Sfun` is continuous and vanishes a.e.
  have hScont : ContinuousOn (Sfun α F Ψ) (Set.Ioi 0) := by
    have h1 : ContinuousOn (fun w => Work.FTS.EllipticEst.Bmom F 0 w) (Set.Ioi 0) :=
      Work.FTS.EllipticEst.continuousOn_Bmom α k hFopen hFmem 0 (by omega)
    have h2 : ContinuousOn (fun w => Work.FTS.EllipticEst.Bmom Ψ 1 w) (Set.Ioi 0) :=
      Work.FTS.EllipticEst.continuousOn_Bmom α k hΨopen hΨmem 1 (by omega)
    have h3 : ContinuousOn
        (fun w => Work.FTS.EllipticEst.Bmom (fun w θ => w ^ 2 * Work.Spaces.pzIter 2 Ψ w θ) 0 w)
        (Set.Ioi 0) :=
      Work.FTS.EllipticEst.continuousOn_Bmom α k
        (Work.FTS.EllipticEst.smoothOpen_of_forall hgforall) hgmem 0 (by omega)
    have hc : ContinuousOn (fun w => Work.FTS.EllipticEst.Bmom F 0 w
        + α ^ 2 * (Work.FTS.EllipticEst.Bmom Ψ 1 w
          + Work.FTS.EllipticEst.Bmom (fun w θ => w ^ 2 * Work.Spaces.pzIter 2 Ψ w θ) 0 w)
        + 5 * α * Work.FTS.EllipticEst.Bmom Ψ 1 w) (Set.Ioi 0) :=
      (h1.add ((h2.add h3).const_mul (α ^ 2))).add (h2.const_mul (5 * α))
    refine hc.congr fun w hw => ?_
    simp only [Sfun]
    rw [hsplit2 w hw]
  have hN1 : ∀ᵐ w ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      HasDerivAt (fun w => Work.FTS.EllipticEst.Bmom Ψ 1 w)
        (Work.FTS.EllipticEst.Bmom Ψ 2 w / w) w := by
    by_cases h3 : 3 ≤ k
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with w hw
      exact Work.FTS.EllipticEst.hasDerivAt_Bmom α k hΨopen hΨmem 1 (by omega) hw
    · have hk2 : k = 2 := by omega
      have h := Work.FTS.EllipticEst.ae_hasDerivAt_Bmom α 2 hΨopen (hk2 ▸ hΨmem) (by omega)
      simpa using h
  have hSae_r : ∀ᵐ w ∂(volume.restrict (Set.Ioi (0 : ℝ))), Sfun α F Ψ w = 0 := by
    filter_upwards [hN1, self_mem_ae_restrict measurableSet_Ioi] with w hN1w hw
    have hwpos : 0 < w := hw
    have hhat1w := hhat1 w hw
    -- the derivative of `w ↦ -(4/15)·(w·G'(w))` at `w`
    have hG'd : HasDerivAt (fun y : ℝ => deriv (Work.Elliptic.Gsing α F) y)
        (deriv (fun y : ℝ => deriv (Work.Elliptic.Gsing α F) y) w) w := by
      have h1 : ContDiffOn ℝ 1 (deriv (Work.Elliptic.Gsing α F)) (Set.Ioi 0) :=
        hG2.deriv_of_isOpen isOpen_Ioi (by norm_num)
      exact ((h1.differentiableOn (by simp)).differentiableAt
        (isOpen_Ioi.mem_nhds hw)).hasDerivAt
    have hd2 : HasDerivAt
        (fun w' : ℝ => -(4 / 15) * (w' * deriv (Work.Elliptic.Gsing α F) w'))
        (-(4 / 15) * (deriv (Work.Elliptic.Gsing α F) w
          + w * deriv (fun w' => deriv (Work.Elliptic.Gsing α F) w') w)) w := by
      have hh := ((hasDerivAt_id w).mul hG'd).const_mul (-(4 / 15))
      simpa only [Pi.mul_apply, id_eq, one_mul] using hh
    have hd2' : HasDerivAt (fun w' : ℝ => Work.FTS.EllipticEst.Bmom Ψ 1 w')
        (-(4 / 15) * (deriv (Work.Elliptic.Gsing α F) w
          + w * deriv (fun w' => deriv (Work.Elliptic.Gsing α F) w') w)) w :=
      hd2.congr_of_eventuallyEq (by
        filter_upwards [isOpen_Ioi.mem_nhds hw] with w' hw'
        exact hhat1 w' hw')
    have huniq : Work.FTS.EllipticEst.Bmom Ψ 2 w / w
        = -(4 / 15) * (deriv (Work.Elliptic.Gsing α F) w
          + w * deriv (fun w' => deriv (Work.Elliptic.Gsing α F) w') w) :=
      hN1w.unique hd2'
    have hN2w : Work.FTS.EllipticEst.Bmom Ψ 2 w
        = -(4 / 15) * (w * (deriv (Work.Elliptic.Gsing α F) w
          + w * deriv (fun w' => deriv (Work.Elliptic.Gsing α F) w') w)) := by
      have h := (div_eq_iff (ne_of_gt hwpos)).mp huniq
      rw [h]; ring
    have hode_w := hode w hw
    have hF_eq : Work.Elliptic.Fstar F w
        = (4 / 15) * (α ^ 2 * w ^ 2
            * deriv (fun w' => deriv (Work.Elliptic.Gsing α F) w') w
          + α * (5 + α) * w * deriv (Work.Elliptic.Gsing α F) w) := by
      linarith [hode_w]
    simp only [Sfun]
    rw [Work.FTS.EllipticEst.Bmom_zero, hhat1w, hN2w, hF_eq]
    ring
  have hS0 : ∀ w ∈ Set.Ioi (0 : ℝ), Sfun α F Ψ w = 0 :=
    eq_zero_of_continuousOn_of_ae_eq_zero hScont
      ((ae_restrict_iff' measurableSet_Ioi).mp hSae_r)
  intro z hz
  -- ## the slice data at `z`
  have hslice2 : ContDiffOn ℝ 2 (fun θ : ℝ => Ψ z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.Endpt.slice_regularity_of_uncurry hz hΨforall).1
  have h2 : IntegrableOn
      (fun θ : ℝ => (Work.Spaces.pthIter 2 Ψ z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Endpt.integrableOn_pthIter2_sEta_of_HkMem hDth2mem0 hz
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB hΨforall hDth2mem0 hz
  have hL : IntegrableOn
      (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ
        * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    Work.FTS.EllipticEst.Endpt.Lzero1_slice_mul_integrable hΨforall hDth2mem0 hz hC
  have hFm : IntegrableOn (fun θ : ℝ => F z θ * Work.Elliptic.sinCos2 θ) Work.Spaces.Iθ :=
    integrableOn_slice_mul_sinCos2 (α := α) hFopen.continuousOn hFmem0 hz
  have h2m : IntegrableOn
      (fun θ : ℝ => Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ := h2m_all z hz
  obtain ⟨hdec1, hdec2⟩ :=
    Work.FTS.EllipticEst.remov.SourceBound.moment_decomposition (α := α) (F := F) (Ψ := Ψ) hz
      (by positivity) (fun θ hθ1 hθ2 => hHyp.sol.1 z hz θ hθ1 hθ2) hFm h2m hL
  -- ## the `Lzero1`-moment vanishes
  have hA : (∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.Lzero1 (fun θ' => Ψ z θ') θ * Work.Elliptic.sinCos2 θ) = 0 := by
    rw [hdec2]
    have i1 : (∫ θ in Work.Spaces.Iθ, F z θ * Work.Elliptic.sinCos2 θ)
        = Work.FTS.EllipticEst.Bmom F 0 z := by
      rw [Work.FTS.EllipticEst.Bmom_zero]; rfl
    have i2 : (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
        = (Work.FTS.EllipticEst.Bmom Ψ 2 z - Work.FTS.EllipticEst.Bmom Ψ 1 z) / z ^ 2 := by
      have h5 : Work.FTS.EllipticEst.Bmom (fun w θ => w ^ 2 * Work.Spaces.pzIter 2 Ψ w θ) 0 z
          = Work.FTS.EllipticEst.Bmom Ψ 2 z - Work.FTS.EllipticEst.Bmom Ψ 1 z := by
        have h4 := hsplit2 z hz
        linarith [h4]
      have h := h5
      rw [Bmom_zero_zsq (Ψ := Ψ) (z := z) h2m] at h
      rw [eq_div_iff (pow_ne_zero 2 (ne_of_gt hz))]
      ring_nf at h ⊢
      linarith [h]
    have i3 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ)
        = Work.FTS.EllipticEst.Bmom Ψ 1 z / z := by
      rw [Bmom_one_eq hdec1, mul_div_cancel_left₀ _ (ne_of_gt hz)]
    have hEq : (∫ θ in Work.Spaces.Iθ, F z θ * Work.Elliptic.sinCos2 θ)
        + α ^ 2 * z ^ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.pzIter 2 Ψ z θ * Work.Elliptic.sinCos2 θ)
        + (α * (5 + α) * z) * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) = Sfun α F Ψ z := by
      simp only [Sfun]
      rw [i1, i2, i3]
      field_simp
      ring
    rw [hEq, hS0 z hz]
  -- ## the endpoint limit exists and the moment identity kills it
  obtain ⟨β, hβ⟩ := Work.FTS.EllipticEst.remov.SourceBound.auxLimitAtZero hslice2 h2
  have hid := Work.FTS.EllipticEst.Endpt.Lzero1_integral_eq_neg_limit hslice2 h2 hL hβ
  have hβ0 : β = 0 := by linarith [hid, hA]
  simpa [hβ0] using hβ

end Work.FTS.EllipticEst.Cores
