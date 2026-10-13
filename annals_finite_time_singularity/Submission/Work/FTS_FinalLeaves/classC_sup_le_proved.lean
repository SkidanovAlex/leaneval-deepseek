import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.H2.HQ.LinfQpt
import Submission.Work.FTS.H2.LinfQ
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.RegPkgGal.Der.abs_mixed_le_HkNorm_RegQ
import Submission.Work.FTS.H2.SupMixedLeH4
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.StrongEps.SupPort.HardyThetaOpen
import Submission.Work.FTS.StrongEps.SupPort.slotM_open
import Submission.Work.FTS.StrongEps.SupPort.integrableOn_pth_mixed_sq_sin

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_FinalLeaves.classC_sup_le_proved`

Elgindi's Corollary `SecondDerivativesBounded` in the `(b,a) = (0,0)` case, on the elliptic
class `Work.FTS.ClassC.ClassC`:

  `|f(z,θ)| ≤ 10/√(γ-1) · |f|_{ℋ⁴}`   (`γ = 1 + α/10`, `f ∈ ClassC α`, `(z,θ) ∈ Qd`).

The class `ClassC` constrains `f` only on the **open** quadrant (`SmoothOpen f`, `C^∞` on
`z > 0`, `0 < θ < π/2`), together with the honesty `HkMem α 7 f` and the boundary traces
`BdryTraces α 6 f`; it gives no smoothness across `z = 0`, so the `RegQ`/`SmoothQuad` form
`Work.FTS.RegPkgGal.Der.abs_mixed_le_HkNorm_RegQ` of the corollary does not apply.

The proof below is the two one-dimensional Hardy steps of the corollary, run entirely in the
open class:

* **angular step.**  `f` is `C^∞` on the open quadrant, its `θ`-slices are `C^∞` on `(0,π/2)`,
  and the angular clause of `BdryTraces` makes the slice vanish at `θ → 0⁺`; the weighted
  Cauchy–Schwarz/Hardy inequality on the interval (with the singular weight
  `sin(2σ)^{2-γ}`) gives

    `f(z,θ)² ≤ (100/(γ-1)) ∫_Iθ (∂_θf(z,σ))² sin(2σ)^{2-γ} dσ`.

* **radial step.**  On the open quadrant the identity `D_z(D_θf) = sin(2θ)·(z∂_z∂_θf)` puts
  the angular Hardy integrand into the mixed slot `D_zD_θf`; applying the radial Hardy
  inequality (`Work.FTS.H2.hardyZ_open`) to the `z`-slice of `D_θf` — which decays at
  `z → ∞` by the radial clause of `BdryTraces` — turns that slot into the `(1,1)`-slot of the
  `ℋ⁴`-norm, which the Tonelli lemma `Work.FTS.StrongEps.SupPort.slotM_open` bounds by
  `HkSq α 4 f`.

Both Hardy inequalities and the slot Tonelli swap are one-purpose lemmas proved elsewhere in
the workspace (`HardyThetaOpen`, `hardyZ_open`, `slotM_open`,
`integrableOn_pth_mixed_sq_sin`); the assembly below is the argument of the corollary.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_FinalLeaves

/-- **The interior `L^∞`–`ℋ⁴` trade-off on the class `C`** (Elgindi, Corollary
`SecondDerivativesBounded`, `(b,a) = (0,0)` instance): on the open quadrant `Qd = (0,∞)×(0,π/2)`
every `f ∈ ClassC α` with `0 < α ≤ 1` satisfies `|f(z,θ)| ≤ 10/√(γ-1)·|f|_{ℋ⁴}`. -/
theorem classC_sup_le_proved {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∀ f : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α f → ∀ z θ,
      (z, θ) ∈ Work.Construction.Qd →
      |f z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := by
  intro f hf z θ hzθ
  -- unpack the point of the open quadrant and the class
  have hz : 0 < z := hzθ.1
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hzθ.2.1, hzθ.2.2⟩
  have hF : Work.FTS.EllipticEst.SmoothOpen f := hf.reg
  have hmem : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hf.reg 4 (by norm_num) hf.mem
  have hbd : Work.FTS.Nonlin.BdryTraces α 4 f := hf.bdry_le_six (by norm_num)
  have hγ1 : 0 < Work.Spaces.gam α - 1 := by rw [Work.Spaces.gam_sub_one]; linarith
  have hγne : Work.Spaces.gam α ≠ 0 := by
    have h1 : 1 < Work.Spaces.gam α := Work.Spaces.one_lt_gam hα
    linarith
  have hKnn : 0 ≤ 100 / (Work.Spaces.gam α - 1) := div_nonneg (by norm_num) hγ1.le
  -- the `(1,1)`-slot of the `ℋ⁴`-norm, and its two integrability consequences
  obtain ⟨hslot_le, hslot_int, hslot_ae⟩ :=
    Work.FTS.StrongEps.SupPort.slotM_open α f hF hmem 1 1 (le_refl 1) (by norm_num)
  -- the radial-slice energy of the `(1,1)`-slot
  set B : ℝ → ℝ := fun σ => ∫ s in Work.Spaces.Iz,
    (Work.Spaces.mixed 1 1 f s σ) ^ 2 * (Work.Spaces.w s) ^ 2 with hBdef
  -- the angular Hardy integrand is integrable at the fixed `z`
  have hint_ang : IntegrableOn (fun σ => (Work.Spaces.pth f z σ) ^ 2
      * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ :=
    Work.FTS.StrongEps.SupPort.integrableOn_pth_mixed_sq_sin hα hα1 hF hmem 0 0
      (by norm_num) hz
  -- the slice vanishes at `θ → 0⁺`, from the angular clause of `BdryTraces`
  have hlim0 : Tendsto (fun θ' => f z θ') (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
    have h := Work.FTS.H2.HQ.BdryTraces.tendsto_theta_zero (f := f) hα hbd (a := 0) (b := 0)
      (by norm_num) hz
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
  -- the angular Hardy inequality at `(z,θ)`
  have hHT :=
    Work.FTS.StrongEps.SupPort.HardyThetaOpen α hα hα1 f z hF hz hlim0 hint_ang θ hθ
  -- the angular Hardy integrand is the `(0,1)`-slot against `sin(2σ)^{-γ}`
  have hI1 : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth f z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
      = ∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
          * (Work.Spaces.Dth f z σ) ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    show (Work.Spaces.pth f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.Dth f z σ) ^ 2
    rw [Work.FTS.H2.pth_sq_mul_sin_eq α hα hα1 f z σ hσ]
    ring
  have hDth_int : IntegrableOn (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
      * (Work.Spaces.Dth f z σ) ^ 2) Work.Spaces.Iθ := by
    refine hint_ang.congr_fun (fun σ hσ => ?_) measurableSet_Icc
    show (Work.Spaces.pth f z σ) ^ 2 * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.Dth f z σ) ^ 2
    rw [Work.FTS.H2.pth_sq_mul_sin_eq α hα hα1 f z σ hσ]
    ring
  -- the radial Hardy inequality on the `D_θ f`-slice, for almost every angle
  have hrad : ∀ᵐ σ ∂(volume.restrict Work.Spaces.Iθ),
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * (Work.Spaces.Dth f z σ) ^ 2
        ≤ (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ := by
    filter_upwards [hslot_ae, ae_restrict_mem (show MeasurableSet Work.Spaces.Iθ from
      measurableSet_Icc)] with σ hσint hσI
    rcases eq_or_lt_of_le hσI.1 with hσeq | hσpos
    · -- the endpoint `σ = 0`, where the singular weight vanishes
      have hs0 : Real.sin (2 * σ) = 0 := by rw [← hσeq]; simp
      have hz0 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) = 0 := by
        rw [hs0]
        exact Real.zero_rpow (neg_ne_zero.mpr hγne)
      simp [hz0]
    rcases eq_or_lt_of_le hσI.2 with hσeq | hσlt
    · -- the endpoint `σ = π/2`
      have hs0 : Real.sin (2 * σ) = 0 := by
        rw [hσeq, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      have hz0 : (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) = 0 := by
        rw [hs0]
        exact Real.zero_rpow (neg_ne_zero.mpr hγne)
      simp [hz0]
    · -- an interior angle: the radial Hardy inequality for `s ↦ D_θ f(s,σ)`
      have hσ' : σ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨hσpos, hσlt⟩
      refine mul_le_mul_of_nonneg_left ?_
        (Real.rpow_nonneg (Work.FTS.H2.sin_two_nonneg hσI) _)
      have hcd : ContDiffOn ℝ 1 (fun s => Work.Spaces.Dth f s σ) (Set.Ioi 0) :=
        (hF.Dth.curry_z hσ').of_le (by simp [Work.Stability.smoothOrder])
      have hdec : Tendsto (fun s => Work.Spaces.Dth f s σ) atTop (𝓝 0) := by
        have h := Work.FTS.H2.HQ.BdryTraces.tendsto_atTop_zero (f := f) hbd (a := 1) (b := 0)
          (by norm_num) hσ'
        simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DzIter_zero,
          Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero] using h
      have hint2 : IntegrableOn
          (fun s => (s * deriv (fun s => Work.Spaces.Dth f s σ) s) ^ 2
            * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz := hσint
      have hzr := Work.FTS.H2.hardyZ_open hcd hdec hint2 z (Set.mem_Ioi.mpr hz)
      rw [hBdef]
      exact hzr
  -- the radial-slice energy is the `θ`-first form of the `(1,1)`-slot
  have hBpt : ∀ σ ∈ Set.Ioo 0 (Real.pi / 2),
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ
        = ∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed 1 1 f s σ * Work.Spaces.Wt α s σ) ^ 2 := by
    intro σ hσ
    rw [hBdef]
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ici fun s _ => ?_
    show (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * ((Work.Spaces.mixed 1 1 f s σ) ^ 2 * (Work.Spaces.w s) ^ 2)
      = (Work.Spaces.mixed 1 1 f s σ * Work.Spaces.Wt α s σ) ^ 2
    rw [mul_pow, Work.FTS.H2.HQ.Wt_sq_quad α s σ hσ]
    ring
  have hBeq : (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ)
      =ᵐ[volume.restrict Work.Spaces.Iθ]
      (fun σ => ∫ s in Work.Spaces.Iz,
        (Work.Spaces.mixed 1 1 f s σ * Work.Spaces.Wt α s σ) ^ 2) := by
    rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    exact ae_restrict_of_forall_mem measurableSet_Ioo (fun σ hσ => hBpt σ hσ)
  have hTint : Integrable
      (fun σ => (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ)
      (volume.restrict Work.Spaces.Iθ) := hslot_int.congr hBeq.symm
  -- the angular Hardy integrand is dominated by the radial-slice energy
  have hIntLe : (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α))
        * (Work.Spaces.Dth f z σ) ^ 2) ≤ ∫ σ in Work.Spaces.Iθ,
      (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ :=
    integral_mono_ae hDth_int hTint hrad
  have hfin : (f z θ) ^ 2 ≤ (100 / (Work.Spaces.gam α - 1))
      * (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ) := by
    have h1 : (∫ σ in Work.Spaces.Iθ, (Work.Spaces.pth f z σ) ^ 2
        * (Real.sin (2 * σ)) ^ (2 - Work.Spaces.gam α))
        ≤ ∫ σ in Work.Spaces.Iθ,
            (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ := by
      rw [hI1]; exact hIntLe
    exact le_trans hHT (mul_le_mul_of_nonneg_left h1 hKnn)
  -- bound the energy by the `ℋ⁴`-norm (Tonelli for the `(1,1)`-slot, in the `θ`-first order)
  have hTle : (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ)
      ≤ Work.Spaces.HkSq α 4 f := by
    rw [show (∫ σ in Work.Spaces.Iθ, (Real.sin (2 * σ)) ^ (-(Work.Spaces.gam α)) * B σ)
        = ∫ σ in Work.Spaces.Iθ, ∫ s in Work.Spaces.Iz,
            (Work.Spaces.mixed 1 1 f s σ * Work.Spaces.Wt α s σ) ^ 2
        from integral_congr_ae hBeq]
    exact hslot_le
  -- the constants
  have hfinal : (f z θ) ^ 2 ≤ (100 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f :=
    le_trans hfin (mul_le_mul_of_nonneg_left hTle hKnn)
  have hsqrt : Real.sqrt (100 / (Work.Spaces.gam α - 1))
      = 10 / Real.sqrt (Work.Spaces.gam α - 1) := by
    have h2 : (0 : ℝ) ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) :=
      div_nonneg (by norm_num) (Real.sqrt_nonneg _)
    rw [← Real.sqrt_sq h2]
    congr 1
    rw [div_pow, Real.sq_sqrt hγ1.le]
    norm_num
  have hconst : Real.sqrt ((100 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f)
      = 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := by
    rw [Real.sqrt_mul hKnn, hsqrt]
    simp only [Work.FTS.Nonlin.Xn, Work.Spaces.HkNorm]
  calc |f z θ| = Real.sqrt ((f z θ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((100 / (Work.Spaces.gam α - 1)) * Work.Spaces.HkSq α 4 f) :=
        Real.sqrt_le_sqrt hfinal
    _ = 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := hconst

end Work.FTS_FinalLeaves
