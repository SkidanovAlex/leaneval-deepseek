/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.Blocks.interpol_mixed_box_proof`

The compactly `z`-supported case of the mixed weighted interpolation estimate of the paper's
§Elliptic Estimates, in the exact form requested:

`α² ∫∫ (D_z∂_θG)² w² σ ≤ C (α⁴ ∫∫ (D_z²G)² w² σ + ∫∫ (∂_θ²G)² w² σ + α² ∫∫ (D_zG)² w² σ)`,

with `σ = sin(2θ)^{-η}`, `w = (1+z)²/z²`, `D_z = z∂_z`, for `G` of class `C^∞` on the open
strip `(0,∞) × (-1, π/2+1)`, vanishing on the two angular boundary lines and supported in a
compact interval `[a,b] ⊂ (0,∞)`.  The constant is uniform in `G` and in `a,b`.

Route (the paper's, both boundary terms being killed by the compact support):

* the **angular** integration by parts in `θ` (`Work.FTS.EllipticEst.ThetaU.ang_ibp_eta`)
  applied to the slices `θ ↦ D_zG z θ`, which vanish at `θ = 0, π/2`;
* the **radial** integration by parts (`Work.Blocks.IMC.mixed_pairing_identity`: Fubini plus the
  slicewise `D_z`-IBP, with drift coefficient `b(z) = (z-3)/(1+z)`);
* the sharp angular Hardy inequality `Work.Blocks.IMC.hardy_weighted_slice` absorbing the
  `cot²` weight, Cauchy–Schwarz (`Work.Blocks.IMC.cs_integral_mul_le`) for the two pairings, and
  elementary AM–GM in `α`.

The assembly is the one developed in `interp_mixed_compact_clean.lean`, but it is carried out
here against the *proved* lemmas of `Submission/Work/Blocks/IMC/` rather than the local `IMCtmp`
copies, and it does not use that file's (unused) `FourInt` hypothesis; the constant obtained is
independent of the support interval, which is what allows the `∃ C` to be pulled outside the
`∀ δ R`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.interpol_defs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.hardy_shift_two_same_weight
import Submission.Work.FTS.EllipticEst.ThetaU.OpenAux
import Submission.Work.FTS.EllipticEst.ThetaU.AngIbp
import Submission.Work.FTS.EllipticEst.ThetaU.K1Aux
import Submission.Work.Blocks.IMC.cs_integral_mul_le
import Submission.Work.Blocks.IMC.hardy_weighted_slice
import Submission.Work.Blocks.IMC.mixed_pairing_identity
import Submission.Work.Blocks.IMC.Dz_cot_box_bound
import Submission.Work.Blocks.IMC.weighted_sq_idents

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Blocks

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## Elementary one-dimensional tools -/

/-- `√(a+b) ≤ √a + √b` for `a,b ≥ 0`. -/
private theorem sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : (Real.sqrt a + Real.sqrt b) ^ 2 = a + b + 2 * (Real.sqrt a * Real.sqrt b) := by
    rw [add_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]
    ring
  have h2 : 0 ≤ 2 * (Real.sqrt a * Real.sqrt b) := by positivity
  have h3 : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by rw [h1]; linarith
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h3
    _ = |Real.sqrt a + Real.sqrt b| := Real.sqrt_sq_eq_abs _
    _ = Real.sqrt a + Real.sqrt b := abs_of_nonneg (by positivity)

/-- Weighted AM–GM: `2√(xy) ≤ c x + y/c` for `x,y ≥ 0`, `c > 0`. -/
private theorem two_sqrt_mul_le {x y c : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 < c) :
    2 * Real.sqrt (x * y) ≤ c * x + y / c := by
  have hcx : 0 ≤ c * x := mul_nonneg hc.le hx
  have hyc : 0 ≤ y / c := div_nonneg hy hc.le
  have hxy : c * x * (y / c) = x * y := by field_simp
  have h2 : 2 * (Real.sqrt (c * x) * Real.sqrt (y / c)) = 2 * Real.sqrt (x * y) := by
    rw [← Real.sqrt_mul hcx, hxy]
  have := sq_nonneg (Real.sqrt (c * x) - Real.sqrt (y / c))
  rw [sub_sq, Real.sq_sqrt hcx, Real.sq_sqrt hyc] at this
  linarith [this, h2]

/-- AM–GM in the form `2 a √(xy) ≤ a² x + y` for `a,x,y ≥ 0`. -/
private theorem two_mul_sqrt_mul_le {a x y : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * (a * Real.sqrt (x * y)) ≤ a ^ 2 * x + y := by
  have h1 : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := Real.sqrt_mul hx y
  rw [h1]
  have := sq_nonneg (a * Real.sqrt x - Real.sqrt y)
  rw [sub_sq, mul_pow, Real.sq_sqrt hx, Real.sq_sqrt hy] at this
  linarith [this]

/-- `√(9·D) = 3√D` for `D ≥ 0`. -/
private theorem sqrt_nine_mul {D : ℝ} (hD : 0 ≤ D) : Real.sqrt (9 * D) = 3 * Real.sqrt D := by
  rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3 ^ 2) D,
    Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 3)]
/-! ## The main theorem -/

/-- **The mixed weighted interpolation for compactly `z`-supported data**, with the box
endpoints `δ < R` and the support hypothesis as explicit arguments, so that the constant is
manifestly independent of `δ`, `R` and `G`. -/
theorem interp_box_uniform_aux :
    ∃ C : ℝ, 0 < C ∧
      ∀ (α : ℝ), 0 < α → α ≤ 1 / 4 → ∀ (G : ℝ → ℝ → ℝ),
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
          (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))) →
        (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
        ∀ (δ R : ℝ), 0 < δ → δ < R →
          (∀ z : ℝ, z ∉ Set.Icc δ R → ∀ θ : ℝ, G z θ = 0) →
        α ^ 2 * Work.FTS.EllipticEst.mixInt G
          ≤ C * (α ^ 4 * Work.FTS.EllipticEst.ddInt G + Work.FTS.EllipticEst.ttInt G
              + α ^ 2 * Work.FTS.EllipticEst.dInt G) := by
  obtain ⟨CH, hCHpos, hHardy⟩ := Work.Blocks.IMC.hardy_weighted_slice
  have hηpos : (0 : ℝ) < Work.Spaces.eta := Work.Spaces.eta_pos
  have hη1 : Work.Spaces.eta < 1 := Work.Spaces.eta_lt_one
  have h1mη : (0 : ℝ) < 1 - Work.Spaces.eta := by linarith
  have hηnn : (0 : ℝ) ≤ Work.Spaces.eta := hηpos.le
  -- the numerical constants
  set K : ℝ := 2 * (1 + Work.Spaces.eta) / (1 - Work.Spaces.eta) with hKdef
  set Cp : ℝ := K * (2 * Work.Spaces.eta ^ 2 * CH * (1 + Work.Spaces.eta)
      / (1 - Work.Spaces.eta)) with hCpdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  have hCppos : 0 < Cp := by rw [hCpdef]; positivity
  set Cfin : ℝ := max (K / 2) (max (7 * K / 8) (3 * K / 8 + Cp)) with hCfindef
  have hCfinpos : 0 < Cfin := by
    rw [hCfindef]
    exact lt_of_lt_of_le (by linarith : 0 < K / 2) (le_max_left _ _)
  refine ⟨Cfin, hCfinpos, ?_⟩
  intro α hα hα4 G hsm h0 h1 δ R hδ hδR hsupp
  -- ## abbreviations
  set M : ℝ := Work.FTS.EllipticEst.mixInt G with hMdef
  set DD : ℝ := Work.FTS.EllipticEst.ddInt G with hDDdef
  set TT : ℝ := Work.FTS.EllipticEst.ttInt G with hTTdef
  set D : ℝ := Work.FTS.EllipticEst.dInt G with hDdef
  have hα0 : (0 : ℝ) < α := hα
  -- ## nonnegativity of the four functionals
  have hM0 : 0 ≤ M := by
    rw [hMdef, Work.FTS.EllipticEst.mixInt]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ici (fun z hz => ?_)
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Work.FTS.EllipticEst.thEta_nonneg hθ)
  have hDD0 : 0 ≤ DD := by
    rw [hDDdef, Work.FTS.EllipticEst.ddInt]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ici (fun z hz => ?_)
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Work.FTS.EllipticEst.thEta_nonneg hθ)
  have hTT0 : 0 ≤ TT := by
    rw [hTTdef, Work.FTS.EllipticEst.ttInt]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ici (fun z hz => ?_)
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Work.FTS.EllipticEst.thEta_nonneg hθ)
  have hD0 : 0 ≤ D := by
    rw [hDdef, Work.FTS.EllipticEst.dInt]
    refine MeasureTheory.setIntegral_nonneg measurableSet_Ici (fun z hz => ?_)
    refine MeasureTheory.setIntegral_nonneg measurableSet_Icc (fun θ hθ => ?_)
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Work.FTS.EllipticEst.thEta_nonneg hθ)
  -- ## the product measure
  set μM : MeasureTheory.Measure (ℝ × ℝ) :=
    (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) with hμM
  have hμM_def : μM = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := hμM
  -- the a.e. membership facts
  have hae_Iz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), z ∈ Work.Spaces.Iz :=
    MeasureTheory.ae_restrict_mem measurableSet_Ici
  have hae_Iθ : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ), θ ∈ Work.Spaces.Iθ :=
    MeasureTheory.ae_restrict_mem measurableSet_Icc
  have hae_prod : ∀ᵐ p ∂μM, p.1 ∈ Work.Spaces.Iz ∧ p.2 ∈ Work.Spaces.Iθ := by
    rw [hμM]
    refine (MeasureTheory.Measure.ae_prod_iff_ae_ae
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (ν := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (p := fun p : ℝ × ℝ => p.1 ∈ Work.Spaces.Iz ∧ p.2 ∈ Work.Spaces.Iθ)
      ((measurableSet_Ici.preimage measurable_fst).inter
        (measurableSet_Icc.preimage measurable_snd))).mpr ?_
    filter_upwards [hae_Iz] with a ha
    filter_upwards [hae_Iθ] with b hb
    exact ⟨ha, hb⟩
  -- the "half weight" `w · √σ`
  set hw : ℝ × ℝ → ℝ :=
    fun p => (Work.Spaces.w p.1) * Real.sqrt (Work.FTS.EllipticEst.thEta p.2) with hhw
  have hhw_sq : ∀ᵐ p ∂μM, hw p ^ 2 = (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 := by
    filter_upwards [hae_prod] with p hp
    rw [hhw]
    simp only
    rw [mul_pow, Real.sq_sqrt (Work.FTS.EllipticEst.thEta_nonneg hp.2)]
  -- ## the `θ`-slices of `Dz G` vanish at the two angular endpoints
  have hDz0 : ∀ z : ℝ, Work.Spaces.Dz G z 0 = 0 := by
    intro z
    show z * Work.Spaces.pz G z 0 = 0
    have hfun : (fun z' : ℝ => G z' 0) = fun _ => (0 : ℝ) := funext fun z' => h0 z'
    rw [show Work.Spaces.pz G z 0 = deriv (fun z' : ℝ => G z' 0) z from rfl, hfun, deriv_const,
      mul_zero]
  have hDzpi : ∀ z : ℝ, Work.Spaces.Dz G z (Real.pi / 2) = 0 := by
    intro z
    show z * Work.Spaces.pz G z (Real.pi / 2) = 0
    have hfun : (fun z' : ℝ => G z' (Real.pi / 2)) = fun _ => (0 : ℝ) := funext fun z' => h1 z'
    rw [show Work.Spaces.pz G z (Real.pi / 2) = deriv (fun z' : ℝ => G z' (Real.pi / 2)) z from rfl,
      hfun, deriv_const, mul_zero]
  -- ## smoothness of the slice `θ ↦ Dz G z θ` on an open neighbourhood of `Iθ`
  have hstrip : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
      (Work.FTS.EllipticEst.ThetaU.OStrip) := fun n => hsm n
  have hslice_cd : ∀ z : ℝ, 0 < z →
      ContDiffOn ℝ 2 (fun θ => Work.Spaces.Dz G z θ) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
    intro z hz
    have hcomp : ContDiffOn ℝ 2 (fun θ : ℝ => (z, θ))
        (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := contDiffOn_const.prodMk contDiffOn_id
    have hmaps : Set.MapsTo (fun θ : ℝ => (z, θ)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))
        Work.FTS.EllipticEst.ThetaU.OStrip := fun θ hθ => ⟨hz, hθ⟩
    have h := (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (n := 2)
      (hstrip 3)).comp hcomp hmaps
    simpa [Function.comp_def] using h
  have hcd2 : ∀ z : ℝ, 0 < z → ∀ θ ∈ Work.Spaces.Iθ,
      ContDiffAt ℝ 2 (Function.uncurry G) (z, θ) := by
    intro z hz θ hθ
    exact (hstrip 2).contDiffAt (Work.FTS.EllipticEst.ThetaU.isOpen_OStrip.mem_nhds
      ⟨hz, ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩)
  -- ## vanishing of the derived functions off the box
  have hpz_supp : ∀ z ∉ Set.Icc δ R, ∀ θ, Work.Spaces.pz G z θ = 0 := by
    intro z hz θ
    have hnb : ∀ᶠ z' in 𝓝 z, z' ∉ Set.Icc δ R := isClosed_Icc.isOpen_compl.mem_nhds hz
    have hev : (fun z' : ℝ => G z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [hnb] with z' hz'
      exact hsupp z' hz' θ
    show deriv (fun z' : ℝ => G z' θ) z = 0
    rw [hev.deriv_eq, deriv_const]
  have hDz_supp : ∀ z ∉ Set.Icc δ R, ∀ θ, Work.Spaces.Dz G z θ = 0 := by
    intro z hz θ
    show z * Work.Spaces.pz G z θ = 0
    rw [hpz_supp z hz θ, mul_zero]
  have hpth_supp : ∀ z ∉ Set.Icc δ R, ∀ θ, Work.Spaces.pth G z θ = 0 := by
    intro z hz θ
    have hfun : (fun θ' : ℝ => G z θ') = fun _ => (0 : ℝ) := funext fun θ' => hsupp z hz θ'
    show deriv (fun θ' : ℝ => G z θ') θ = 0
    rw [hfun, deriv_const]
  have hpthpth_supp : ∀ z ∉ Set.Icc δ R, ∀ θ, Work.Spaces.pth (Work.Spaces.pth G) z θ = 0 := by
    intro z hz θ
    have hfun : (fun θ' : ℝ => Work.Spaces.pth G z θ') = fun _ => (0 : ℝ) :=
      funext fun θ' => hpth_supp z hz θ'
    show deriv (fun θ' : ℝ => Work.Spaces.pth G z θ') θ = 0
    rw [hfun, deriv_const]
  have hDzpth_supp : ∀ z ∉ Set.Icc δ R, ∀ θ, Work.Spaces.Dz (Work.Spaces.pth G) z θ = 0 := by
    intro z hz θ
    have hnb : ∀ᶠ z' in 𝓝 z, z' ∉ Set.Icc δ R := isClosed_Icc.isOpen_compl.mem_nhds hz
    have hev : (fun z' : ℝ => Work.Spaces.pth G z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [hnb] with z' hz'
      exact hpth_supp z' hz' θ
    show z * Work.Spaces.pz (Work.Spaces.pth G) z θ = 0
    rw [show Work.Spaces.pz (Work.Spaces.pth G) z θ
        = deriv (fun z' : ℝ => Work.Spaces.pth G z' θ) z from rfl,
      hev.deriv_eq, deriv_const, mul_zero]
  have hDzpthpth_supp : ∀ z ∉ Set.Icc δ R, ∀ θ,
      Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ = 0 := by
    intro z hz θ
    have hnb : ∀ᶠ z' in 𝓝 z, z' ∉ Set.Icc δ R := isClosed_Icc.isOpen_compl.mem_nhds hz
    have hev : (fun z' : ℝ => Work.Spaces.pth (Work.Spaces.pth G) z' θ) =ᶠ[𝓝 z]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hnb] with z' hz'
      exact hpthpth_supp z' hz' θ
    show z * Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth G)) z θ = 0
    rw [show Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
        = deriv (fun z' : ℝ => Work.Spaces.pth (Work.Spaces.pth G) z' θ) z from rfl,
      hev.deriv_eq, deriv_const, mul_zero]
  have hDzDz_supp : ∀ z ∉ Set.Icc δ R, ∀ θ, Work.Spaces.Dz (Work.Spaces.Dz G) z θ = 0 := by
    intro z hz θ
    have hnb : ∀ᶠ z' in 𝓝 z, z' ∉ Set.Icc δ R := isClosed_Icc.isOpen_compl.mem_nhds hz
    have hev : (fun z' : ℝ => Work.Spaces.Dz G z' θ) =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
      filter_upwards [hnb] with z' hz'
      exact hDz_supp z' hz' θ
    show z * Work.Spaces.pz (Work.Spaces.Dz G) z θ = 0
    rw [show Work.Spaces.pz (Work.Spaces.Dz G) z θ
        = deriv (fun z' : ℝ => Work.Spaces.Dz G z' θ) z from rfl,
      hev.deriv_eq, deriv_const, mul_zero]
  -- ## continuity on the strip, the open quadrant and the box
  have hcontQ : ∀ {F : ℝ → ℝ → ℝ},
      ContinuousOn (Function.uncurry F) (Work.FTS.EllipticEst.ThetaU.OStrip) →
      ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    intro F hF
    refine hF.mono ?_
    rintro p ⟨hp1, hp2⟩
    exact ⟨hp1, ⟨by linarith [hp2.1], by linarith [hp2.2, Real.pi_pos]⟩⟩
  have hboxmono : ∀ {F : ℝ → ℝ → ℝ},
      ContinuousOn (Function.uncurry F) (Work.FTS.EllipticEst.ThetaU.OStrip) →
      ContinuousOn (Function.uncurry F) (Set.Icc δ R ×ˢ Work.Spaces.Iθ) := by
    intro F hF
    refine hF.mono ?_
    rintro p ⟨hp1, hp2⟩
    exact ⟨lt_of_lt_of_le hδ hp1.1, ⟨by linarith [hp2.1], by linarith [hp2.2, Real.pi_pos]⟩⟩
  have hstDz : ContinuousOn (Function.uncurry (Work.Spaces.Dz G))
      (Work.FTS.EllipticEst.ThetaU.OStrip) :=
    (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (n := 1) (hstrip 2)).continuousOn
  have hstDzpth : ContinuousOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth G)))
      (Work.FTS.EllipticEst.ThetaU.OStrip) :=
    (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin
      (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin (n := 2) (hstrip 3))).continuousOn
  have hstDzpthpth : ContinuousOn
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G))))
      (Work.FTS.EllipticEst.ThetaU.OStrip) :=
    (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin
      (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin
        (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin (n := 2) (hstrip 3)))).continuousOn
  have hstpthpth : ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth G)))
      (Work.FTS.EllipticEst.ThetaU.OStrip) :=
    (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin
      (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_pth_fin (n := 2) (hstrip 3))).continuousOn
  have hstDzDz : ContinuousOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dz G)))
      (Work.FTS.EllipticEst.ThetaU.OStrip) :=
    (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin
      (Work.FTS.EllipticEst.ThetaU.contDiffOn_uncurry_Dz_fin (n := 2) (hstrip 3))).continuousOn
  have hcontQ_Dz : ContinuousOn (Function.uncurry (Work.Spaces.Dz G))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hcontQ hstDz
  have hcontQ_Dzpth : ContinuousOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth G)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hcontQ hstDzpth
  have hcontQ_Dzpthpth : ContinuousOn
      (Function.uncurry (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G))))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hcontQ hstDzpthpth
  have hcontQ_pthpth : ContinuousOn (Function.uncurry (Work.Spaces.pth (Work.Spaces.pth G)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hcontQ hstpthpth
  have hcontQ_DzDz : ContinuousOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.Dz G)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hcontQ hstDzDz
  have hcontQ_cot : ContinuousOn (fun p : ℝ × ℝ => Real.cot (2 * p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Real.cot (2 * p.2))
        = fun p : ℝ × ℝ => Real.cos (2 * p.2) / Real.sin (2 * p.2) := by
      funext p
      rw [Real.cot_eq_cos_div_sin]
    rw [hfun]
    refine ContinuousOn.div
      ((Real.continuous_cos.comp (continuous_const.mul continuous_snd)).continuousOn)
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn) ?_
    intro p hp
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
      (by linarith [hp.2.2]))
  have hcontQ_bcoef : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.ThetaU.bcoef p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hfun : (fun p : ℝ × ℝ => Work.FTS.EllipticEst.ThetaU.bcoef p.1)
        = fun p : ℝ × ℝ => (p.1 - 3) / (1 + p.1) := by
      funext p
      rw [Work.FTS.EllipticEst.ThetaU.bcoef]
    rw [hfun]
    refine ContinuousOn.div ((continuous_fst.sub continuous_const).continuousOn)
      ((continuous_const.add continuous_fst).continuousOn) ?_
    intro p hp
    have h1 : (0 : ℝ) < p.1 := hp.1
    exact ne_of_gt (by linarith)
  -- ## box bounds for the derived functions
  obtain ⟨M_Dz, hM_Dz0, hM_Dz⟩ := Work.FTS.EllipticEst.ThetaU.exists_bound_box hδ hδR
    (f := Work.Spaces.Dz G) (hboxmono hstDz)
  obtain ⟨M_Dzpth, hM_Dzpth0, hM_Dzpth⟩ := Work.FTS.EllipticEst.ThetaU.exists_bound_box hδ hδR
    (f := Work.Spaces.Dz (Work.Spaces.pth G)) (hboxmono hstDzpth)
  obtain ⟨M_Dzpthpth, hM_Dzpthpth0, hM_Dzpthpth⟩ :=
    Work.FTS.EllipticEst.ThetaU.exists_bound_box hδ hδR
      (f := Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G))) (hboxmono hstDzpthpth)
  obtain ⟨M_pthpth, hM_pthpth0, hM_pthpth⟩ := Work.FTS.EllipticEst.ThetaU.exists_bound_box hδ hδR
    (f := Work.Spaces.pth (Work.Spaces.pth G)) (hboxmono hstpthpth)
  obtain ⟨M_DzDz, hM_DzDz0, hM_DzDz⟩ := Work.FTS.EllipticEst.ThetaU.exists_bound_box hδ hδR
    (f := Work.Spaces.Dz (Work.Spaces.Dz G)) (hboxmono hstDzDz)
  have hbcoef_le : ∀ z ∈ Set.Icc δ R, |Work.FTS.EllipticEst.ThetaU.bcoef z| ≤ 3 :=
    fun z hz => Work.FTS.EllipticEst.ThetaU.bcoef_abs_le (le_trans hδ.le hz.1)
  -- ## the pointwise bound for `Dz G · cot (2θ)` on the box (delegated)
  obtain ⟨Mcot, hMcot0, hMcot⟩ :=
    Work.Blocks.IMC.Dz_cot_box_bound hδ hδR (G := G) hstrip h0 h1
  -- ## a.e. strong measurability and box integrability of `w² σ F`
  have aesm_Q : ∀ {g : ℝ × ℝ → ℝ},
      ContinuousOn g (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.AEStronglyMeasurable g μM := by
    intro g hg
    rw [hμM]
    exact Work.Spaces.aesm_of_continuousOn_Qd g hg
  have integrable_box : ∀ {F : ℝ → ℝ → ℝ} {MA : ℝ},
      ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      (∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0) →
      (∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ, |F z θ| ≤ MA) →
      MeasureTheory.Integrable
        (Function.uncurry (fun z θ => (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ * F z θ))
        μM := by
    intro F MA hFc hF0 hFb
    rw [hμM]
    exact Work.FTS.EllipticEst.ThetaU.integrable_prod_quad_of_bound hδ hFc hF0 hFb
  have ident_prod : ∀ {F : ℝ → ℝ → ℝ},
      ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      (∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0) →
      (∃ MA : ℝ, ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ, |F z θ| ≤ MA) →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.EllipticEst.thEta θ))
        = ∫ p, (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 * F p.1 p.2 ∂μM := by
    intro F hFc hF0 hFb
    rw [hμM]
    exact Work.FTS.EllipticEst.ThetaU.iterated_eq_prod hδ hFc hF0 hFb
  have ident_prod2 : ∀ {F : ℝ → ℝ → ℝ} {MA : ℝ},
      ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      (∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0) →
      (∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ, |F z θ| ≤ MA) →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, F z θ * Work.FTS.EllipticEst.thEta θ))
        = ∫ p, F p.1 p.2 * (Work.Spaces.w p.1) ^ 2
            * Work.FTS.EllipticEst.thEta p.2 ∂μM := by
    intro F MA hc hs hb
    refine (ident_prod hc hs ⟨MA, hb⟩).trans ?_
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => by ring))
  -- ## the four functionals in "pull-the-weight-out" iterated form
  have hpull : ∀ (A : ℝ → ℝ → ℝ) (z : ℝ),
      (∫ θ in Work.Spaces.Iθ, A z θ * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        = (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, A z θ * Work.FTS.EllipticEst.thEta θ) := by
    intro A z
    rw [show (fun θ => A z θ * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        = (fun θ => (A z θ * Work.FTS.EllipticEst.thEta θ) * (Work.Spaces.w z) ^ 2) from by
      funext θ; ring,
      MeasureTheory.integral_mul_const]
    ring
  have hmix : M = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) := by
    rw [hMdef]
    show Work.FTS.EllipticEst.mixInt G = _
    rw [show Work.FTS.EllipticEst.mixInt G
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
              * Work.FTS.EllipticEst.thEta θ from rfl]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (hpull _))
  have hdInt : D = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ) := by
    rw [hDdef]
    show Work.FTS.EllipticEst.dInt G = _
    rw [show Work.FTS.EllipticEst.dInt G
        = ∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.Dz G z θ) ^ 2 * (Work.Spaces.w z) ^ 2
              * Work.FTS.EllipticEst.thEta θ from rfl]
    exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (hpull _))
  -- ## `z > 0` almost everywhere on `Iz`
  have hae_neg : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      z ∈ Set.Ioi (0 : ℝ) := by
    rw [show MeasureTheory.volume.restrict Work.Spaces.Iz
        = MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)) from
      (MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici).symm]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioi
  -- ## the angular integration by parts, slicewise in `z`
  have hslice_ibp : ∀ z ∈ Set.Ioi (0 : ℝ),
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
        = - (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
              * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
              * Work.FTS.EllipticEst.thEta θ)
          + 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ)
              * (Work.Spaces.Dz (Work.Spaces.pth G) z θ) * Real.cot (2 * θ)
              * Work.FTS.EllipticEst.thEta θ) := by
    intro z hz
    have h := Work.FTS.EllipticEst.ThetaU.ang_ibp_eta (hslice_cd z hz) (hDz0 z) (hDzpi z)
    have e1 : (∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ' => Work.Spaces.Dz G z θ') θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      rw [show deriv (fun θ' => Work.Spaces.Dz G z θ') θ
          = Work.Spaces.pth (Work.Spaces.Dz G) z θ from rfl,
        Work.FTS.EllipticEst.ThetaU.pth_Dz_eq (hcd2 z hz θ hθ)]
    have e2 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
          * deriv (deriv (fun θ' => Work.Spaces.Dz G z θ')) θ * Work.FTS.EllipticEst.thEta θ)
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
            * (Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ)
            * Work.FTS.EllipticEst.thEta θ := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      rw [show deriv (deriv (fun θ' => Work.Spaces.Dz G z θ')) θ
          = Work.Spaces.pth (Work.Spaces.pth (Work.Spaces.Dz G)) z θ from rfl,
        Work.FTS.EllipticEst.ThetaU.pth_pth_Dz_eq (hstrip 3) hz
          ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩]
    have e3 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
          * deriv (fun θ' => Work.Spaces.Dz G z θ') θ * Real.cot (2 * θ)
          * Work.FTS.EllipticEst.thEta θ)
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
            * (Work.Spaces.Dz (Work.Spaces.pth G) z θ) * Real.cot (2 * θ)
            * Work.FTS.EllipticEst.thEta θ := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      rw [show deriv (fun θ' => Work.Spaces.Dz G z θ') θ
          = Work.Spaces.pth (Work.Spaces.Dz G) z θ from rfl,
        Work.FTS.EllipticEst.ThetaU.pth_Dz_eq (hcd2 z hz θ hθ)]
    rw [e1, e2, e3] at h
    exact h
  -- ## the two scalar integrals of the slice identity
  set T : ℝ := ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
          * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
          * Work.FTS.EllipticEst.thEta θ) with hT
  set T2 : ℝ := ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
          * (Work.Spaces.Dz (Work.Spaces.pth G) z θ) * Real.cot (2 * θ)
          * Work.FTS.EllipticEst.thEta θ) with hT2
  -- ## integrability of the two outer integrands of the slice identity
  have hcontQ_J : ContinuousOn (Function.uncurry (fun z θ => Work.Spaces.Dz G z θ
      * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hcontQ_Dz.mul hcontQ_Dzpthpth
  have hsupp_J : ∀ z, z ∉ Set.Icc δ R → ∀ θ, Work.Spaces.Dz G z θ
      * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ = 0 :=
    fun z hz θ => by rw [hDz_supp z hz θ, zero_mul]
  have hbdd_J : ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dz G z θ * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ|
        ≤ M_Dz * M_Dzpthpth :=
    fun z hz θ hθ => by
      rw [abs_mul]
      exact mul_le_mul (hM_Dz z hz θ hθ) (hM_Dzpthpth z hz θ hθ) (abs_nonneg _) hM_Dz0
  have hcontQ_K : ContinuousOn (Function.uncurry (fun z θ => Work.Spaces.Dz G z θ
      * Work.Spaces.Dz (Work.Spaces.pth G) z θ * Real.cot (2 * θ)))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (hcontQ_Dz.mul hcontQ_Dzpth).mul hcontQ_cot
  have hsupp_K : ∀ z, z ∉ Set.Icc δ R → ∀ θ, Work.Spaces.Dz G z θ
      * Work.Spaces.Dz (Work.Spaces.pth G) z θ * Real.cot (2 * θ) = 0 :=
    fun z hz θ => by rw [hDz_supp z hz θ, zero_mul, zero_mul]
  have hbdd_K : ∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.Dz G z θ * Work.Spaces.Dz (Work.Spaces.pth G) z θ * Real.cot (2 * θ)|
        ≤ Mcot * M_Dzpth :=
    fun z hz θ hθ => by
      rw [show Work.Spaces.Dz G z θ * Work.Spaces.Dz (Work.Spaces.pth G) z θ
            * Real.cot (2 * θ)
          = (Work.Spaces.Dz G z θ * Real.cot (2 * θ))
            * Work.Spaces.Dz (Work.Spaces.pth G) z θ from by ring, abs_mul]
      exact mul_le_mul (hMcot z hz θ hθ) (hM_Dzpth z hz θ hθ) (abs_nonneg _) hMcot0
  have hJintpos : MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
          * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
          * Work.FTS.EllipticEst.thEta θ)) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    Work.FTS.EllipticEst.ThetaU.integrable_outer_of_bound hδ hcontQ_J hsupp_J
      ⟨_, hbdd_J⟩
  have hKintpos : MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2
      * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
          * Work.Spaces.Dz (Work.Spaces.pth G) z θ * Real.cot (2 * θ)
          * Work.FTS.EllipticEst.thEta θ)) (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    Work.FTS.EllipticEst.ThetaU.integrable_outer_of_bound hδ hcontQ_K hsupp_K
      ⟨_, hbdd_K⟩
  have hJint : MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2
      * (-(∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
          * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
          * Work.FTS.EllipticEst.thEta θ))) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine hJintpos.neg.congr ?_
    filter_upwards with z
    simp
  have hKint : MeasureTheory.Integrable (fun z => (Work.Spaces.w z) ^ 2
      * (2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
          * Work.Spaces.Dz (Work.Spaces.pth G) z θ * Real.cot (2 * θ)
          * Work.FTS.EllipticEst.thEta θ))) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
    refine (hKintpos.const_mul (2 * Work.Spaces.eta)).congr ?_
    filter_upwards with z
    simp [mul_assoc, mul_comm, mul_left_comm]
  -- ## `M = -T + 2η T2`
  have hM_eq : M = -T + 2 * Work.Spaces.eta * T2 := by
    rw [hmix, hT, hT2]
    have hstep : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ))
        = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (-(∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
                  * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
                  * Work.FTS.EllipticEst.thEta θ)
              + 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
                  * Work.Spaces.Dz (Work.Spaces.pth G) z θ * Real.cot (2 * θ)
                  * Work.FTS.EllipticEst.thEta θ)) := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z hz => ?_)
      have hz' : (0 : ℝ) ≤ z := hz
      rcases eq_or_lt_of_le hz' with hz0 | hz0
      · rw [← hz0]
        simp [Work.Spaces.Dz]
      · exact congrArg (fun t => (Work.Spaces.w z) ^ 2 * t) (hslice_ibp z hz0)
    rw [hstep]
    have hsplit : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (-(∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
                * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
                * Work.FTS.EllipticEst.thEta θ)
            + 2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
                * Work.Spaces.Dz (Work.Spaces.pth G) z θ * Real.cot (2 * θ)
                * Work.FTS.EllipticEst.thEta θ)))
        = (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (-(∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
                * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
                * Work.FTS.EllipticEst.thEta θ)))
          + ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
                * Work.Spaces.Dz (Work.Spaces.pth G) z θ * Real.cot (2 * θ)
                * Work.FTS.EllipticEst.thEta θ)) := by
      rw [← MeasureTheory.integral_add hJint hKint]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
    have hsplitJ : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (-(∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
                * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
                * Work.FTS.EllipticEst.thEta θ)))
        = -(∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
                * Work.Spaces.Dz (Work.Spaces.pth (Work.Spaces.pth G)) z θ
                * Work.FTS.EllipticEst.thEta θ)) := by
      rw [← MeasureTheory.integral_neg]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
    have hsplitK : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (2 * Work.Spaces.eta * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
                * Work.Spaces.Dz (Work.Spaces.pth G) z θ * Real.cot (2 * θ)
                * Work.FTS.EllipticEst.thEta θ)))
        = 2 * Work.Spaces.eta * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, Work.Spaces.Dz G z θ
                * Work.Spaces.Dz (Work.Spaces.pth G) z θ * Real.cot (2 * θ)
                * Work.FTS.EllipticEst.thEta θ)) := by
      rw [← MeasureTheory.integral_const_mul]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => by ring))
    rw [hsplit, hsplitJ, hsplitK]
  -- ## `w² σ F` integrability, in the factor order used below
  have integrable_box' : ∀ {F : ℝ → ℝ → ℝ} {MA : ℝ},
      ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      (∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0) →
      (∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ, |F z θ| ≤ MA) →
      MeasureTheory.Integrable (fun p => F p.1 p.2 * (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2) μM := by
    intro F MA hc hs hb
    refine (integrable_box hc hs hb).congr ?_
    filter_upwards with p
    simp only [Function.uncurry]
    ring
  -- ## the product-measure forms of the three energies
  obtain ⟨hDDid, hDid, hTTid⟩ := Work.Blocks.IMC.weighted_sq_idents hδ (G := G) hstrip hsupp
  have hDDprod : (∫ p, (Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2) ^ 2
      * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 ∂μM) = DD := by
    rw [hDDdef]; exact hDDid
  have hDprod : (∫ p, (Work.Spaces.Dz G p.1 p.2) ^ 2
      * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 ∂μM) = D := by
    rw [hDdef]; exact hDid
  have hTTprod : (∫ p, (Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2) ^ 2
      * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 ∂μM) = TT := by
    rw [hTTdef]; exact hTTid
  have hMprod : (∫ p, (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2) ^ 2
      * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 ∂μM) = M := by
    have h := ident_prod2 (F := fun z θ => (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2)
      (MA := M_Dzpth ^ 2)
      (show ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from hcontQ_Dzpth.pow 2)
      (fun z hz θ => by rw [hDzpth_supp z hz θ]; ring)
      (fun z hz θ hθ => by
        show |(Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2| ≤ M_Dzpth ^ 2
        rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hM_Dzpth z hz θ hθ) 2)
    have h' : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz (Work.Spaces.pth G) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ))
        = ∫ p, (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2) ^ 2
            * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 ∂μM := h
    rw [← h', hmix]
  -- ## the `cot²` energy in `z`-iterated form
  have hH2z : (∫ p, (Work.Spaces.Dz G p.1 p.2) ^ 2 * (Real.cot (2 * p.2)) ^ 2
      * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 ∂μM)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
          * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
              * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ) := by
    have h := ident_prod2 (F := fun z θ => (Work.Spaces.Dz G z θ) ^ 2 * (Real.cot (2 * θ)) ^ 2)
      (MA := Mcot ^ 2)
      (show ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.Dz G p.1 p.2) ^ 2
        * (Real.cot (2 * p.2)) ^ 2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from
        (hcontQ_Dz.pow 2).mul (hcontQ_cot.pow 2))
      (fun z hz θ => by rw [hDz_supp z hz θ]; ring)
      (fun z hz θ hθ => by
        show |(Work.Spaces.Dz G z θ) ^ 2 * (Real.cot (2 * θ)) ^ 2| ≤ Mcot ^ 2
        have h1 : (Work.Spaces.Dz G z θ) ^ 2 * (Real.cot (2 * θ)) ^ 2
            = (Work.Spaces.Dz G z θ * Real.cot (2 * θ)) ^ 2 := by ring
        rw [h1, abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hMcot z hz θ hθ) 2)
    have h' : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, ((Work.Spaces.Dz G z θ) ^ 2 * (Real.cot (2 * θ)) ^ 2)
            * Work.FTS.EllipticEst.thEta θ))
        = ∫ p, ((Work.Spaces.Dz G p.1 p.2) ^ 2 * (Real.cot (2 * p.2)) ^ 2)
            * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 ∂μM := h
    rw [← h']
  -- ## the pairing identity
  have hTpair : T = - ∫ p, ((Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2
      + Work.FTS.EllipticEst.ThetaU.bcoef p.1 * Work.Spaces.Dz G p.1 p.2)
      * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2 * (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2) ∂μM := by
    rw [hT]
    exact Work.Blocks.IMC.mixed_pairing_identity hδ hδR (G := G) hstrip h0 h1 hsupp
  -- ## `T2` in product form
  have hT2prod : T2 = ∫ p, (Work.Spaces.Dz G p.1 p.2 * Real.cot (2 * p.2))
      * (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2)
      * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 ∂μM := by
    rw [hT2]
    have h := ident_prod2 (F := fun z θ => Work.Spaces.Dz G z θ
      * Work.Spaces.Dz (Work.Spaces.pth G) z θ * Real.cot (2 * θ)) (MA := Mcot * M_Dzpth)
      hcontQ_K hsupp_K (fun z hz θ hθ => hbdd_K z hz θ hθ)
    have h' : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ
            * Work.Spaces.Dz (Work.Spaces.pth G) z θ * Real.cot (2 * θ))
            * Work.FTS.EllipticEst.thEta θ))
        = ∫ p, (Work.Spaces.Dz G p.1 p.2 * Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2
            * Real.cot (2 * p.2)) * (Work.Spaces.w p.1) ^ 2
            * Work.FTS.EllipticEst.thEta p.2 ∂μM := h
    rw [h']
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => by ring))
  -- ## continuity of the half weight and of the Cauchy–Schwarz functions
  have hcontQ_w : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rw [show (fun p : ℝ × ℝ => Work.Spaces.w p.1) = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2
      from rfl]
    refine ContinuousOn.div ((continuous_const.add continuous_fst).continuousOn.pow 2)
      (continuous_fst.continuousOn.pow 2) ?_
    intro p hp
    have h1 : (0 : ℝ) < p.1 := hp.1
    exact pow_ne_zero 2 (ne_of_gt h1)
  have hcontQ_thEta : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hbase : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
    have hne : ∀ p ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) : Set (ℝ × ℝ)),
        Real.sin (2 * p.2) ≠ 0 := by
      intro p hp
      have h1 : (0 : ℝ) < p.2 := hp.2.1
      have h2 : p.2 < Real.pi / 2 := hp.2.2
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
    rw [show (fun p : ℝ × ℝ => Work.FTS.EllipticEst.thEta p.2)
        = fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Work.Spaces.eta)) from rfl]
    exact hbase.rpow_const (fun p hp => Or.inl (hne p hp))
  have hcontQ_hw : ContinuousOn (fun p : ℝ × ℝ => hw p)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    rw [hhw]
    exact hcontQ_w.mul hcontQ_thEta.sqrt
  have aesm_A : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2 * hw p) μM :=
    aesm_Q (show ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2 * hw p) _ from hcontQ_DzDz.mul hcontQ_hw)
  have aesm_bB : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        (Work.FTS.EllipticEst.ThetaU.bcoef p.1 * Work.Spaces.Dz G p.1 p.2) * hw p) μM :=
    aesm_Q (show ContinuousOn (fun p : ℝ × ℝ =>
      (Work.FTS.EllipticEst.ThetaU.bcoef p.1 * Work.Spaces.Dz G p.1 p.2) * hw p) _
      from (hcontQ_bcoef.mul hcontQ_Dz).mul hcontQ_hw)
  have aesm_Y : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2 * hw p) μM :=
    aesm_Q (show ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2 * hw p) _ from hcontQ_pthpth.mul hcontQ_hw)
  have aesm_Bc : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => (Work.Spaces.Dz G p.1 p.2 * Real.cot (2 * p.2)) * hw p) μM :=
    aesm_Q (show ContinuousOn (fun p : ℝ × ℝ =>
      (Work.Spaces.Dz G p.1 p.2 * Real.cot (2 * p.2)) * hw p) _
      from (hcontQ_Dz.mul hcontQ_cot).mul hcontQ_hw)
  have aesm_Bp : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2 * hw p) μM :=
    aesm_Q (show ContinuousOn (fun p : ℝ × ℝ =>
      Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2 * hw p) _ from hcontQ_Dzpth.mul hcontQ_hw)
  -- ## integrability of the Cauchy–Schwarz squares (with the half weight `w·√σ`)
  have integrable_box_hw : ∀ {F : ℝ → ℝ → ℝ} {MA : ℝ},
      ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      (∀ z, z ∉ Set.Icc δ R → ∀ θ, F z θ = 0) →
      (∀ z ∈ Set.Icc δ R, ∀ θ ∈ Work.Spaces.Iθ, |F z θ| ≤ MA) →
      MeasureTheory.Integrable (fun p : ℝ × ℝ => (F p.1 p.2 * (Work.Spaces.w p.1
        * Real.sqrt (Work.FTS.EllipticEst.thEta p.2))) ^ 2) μM := by
    intro F MA hc hs hb
    refine (integrable_box (F := fun z θ => (F z θ) ^ 2) (MA := MA ^ 2)
      (show ContinuousOn (Function.uncurry (fun z θ => (F z θ) ^ 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from
        (show ContinuousOn (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
          from hc).pow 2)
      (fun z hz θ => by rw [hs z hz θ]; ring)
      (fun z hz θ hθ => by
        show |(F z θ) ^ 2| ≤ MA ^ 2
        rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hb z hz θ hθ) 2)).congr ?_
    filter_upwards [hae_prod] with p hp
    show (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 * (F p.1 p.2) ^ 2
        = (F p.1 p.2 * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2))) ^ 2
    rw [mul_pow, mul_pow, Real.sq_sqrt (Work.FTS.EllipticEst.thEta_nonneg hp.2)]
    ring
  have hint_A : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2
        * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2))) ^ 2) μM :=
    integrable_box_hw (F := fun z θ => Work.Spaces.Dz (Work.Spaces.Dz G) z θ)
      (MA := M_DzDz)
      (show ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from hcontQ_DzDz)
      (fun z hz θ => hDzDz_supp z hz θ)
      (fun z hz θ hθ => hM_DzDz z hz θ hθ)
  have hint_b : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ((Work.FTS.EllipticEst.ThetaU.bcoef p.1
        * Work.Spaces.Dz G p.1 p.2)
        * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2))) ^ 2) μM :=
    integrable_box_hw (F := fun z θ => Work.FTS.EllipticEst.ThetaU.bcoef z
      * Work.Spaces.Dz G z θ) (MA := 3 * M_Dz)
      (show ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.ThetaU.bcoef p.1
        * Work.Spaces.Dz G p.1 p.2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from
        hcontQ_bcoef.mul hcontQ_Dz)
      (fun z hz θ => by rw [hDz_supp z hz θ]; ring)
      (fun z hz θ hθ => by
        simp only [abs_mul]
        exact mul_le_mul (hbcoef_le z hz) (hM_Dz z hz θ hθ) (abs_nonneg _) (by norm_num))
  have hint_Y : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2
        * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2))) ^ 2) μM :=
    integrable_box_hw (F := fun z θ => Work.Spaces.pth (Work.Spaces.pth G) z θ)
      (MA := M_pthpth)
      (show ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from hcontQ_pthpth)
      (fun z hz θ => hpthpth_supp z hz θ)
      (fun z hz θ hθ => hM_pthpth z hz θ hθ)
  have hint_Bc : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ((Work.Spaces.Dz G p.1 p.2 * Real.cot (2 * p.2))
        * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2))) ^ 2) μM :=
    integrable_box_hw (F := fun z θ => Work.Spaces.Dz G z θ * Real.cot (2 * θ))
      (MA := Mcot)
      (show ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dz G p.1 p.2 * Real.cot (2 * p.2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from hcontQ_Dz.mul hcontQ_cot)
      (fun z hz θ => by rw [hDz_supp z hz θ]; ring)
      (fun z hz θ hθ => hMcot z hz θ hθ)
  have hint_Bp : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2
        * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2))) ^ 2) μM :=
    integrable_box_hw (F := fun z θ => Work.Spaces.Dz (Work.Spaces.pth G) z θ)
      (MA := M_Dzpth)
      (show ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from hcontQ_Dzpth)
      (fun z hz θ => hDzpth_supp z hz θ)
      (fun z hz θ hθ => hM_Dzpth z hz θ hθ)
  have hint_b' : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.FTS.EllipticEst.ThetaU.bcoef p.1) ^ 2
        * (Work.Spaces.Dz G p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2) μM := by
    refine ((integrable_box' (F := fun z θ => (Work.FTS.EllipticEst.ThetaU.bcoef z
      * Work.Spaces.Dz G z θ) ^ 2) (MA := (3 * M_Dz) ^ 2)
      (show ContinuousOn (fun p : ℝ × ℝ => (Work.FTS.EllipticEst.ThetaU.bcoef p.1
        * Work.Spaces.Dz G p.1 p.2) ^ 2) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from
        (hcontQ_bcoef.mul hcontQ_Dz).pow 2)
      (fun z hz θ => by rw [hDz_supp z hz θ]; ring)
      (fun z hz θ hθ => by
        show |(Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ) ^ 2|
            ≤ (3 * M_Dz) ^ 2
        have hprod : |Work.FTS.EllipticEst.ThetaU.bcoef z * Work.Spaces.Dz G z θ|
            ≤ 3 * M_Dz := by
          rw [abs_mul]
          exact mul_le_mul (hbcoef_le z hz) (hM_Dz z hz θ hθ) (abs_nonneg _)
            (by linarith [hM_Dz0])
        rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hprod 2))).congr
      (Filter.Eventually.of_forall (fun p => by ring))
  have hint_D : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Work.Spaces.Dz G p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2) μM :=
    integrable_box' (F := fun z θ => (Work.Spaces.Dz G z θ) ^ 2) (MA := M_Dz ^ 2)
      (show ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.Dz G p.1 p.2) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from hcontQ_Dz.pow 2)
      (fun z hz θ => by rw [hDz_supp z hz θ]; ring)
      (fun z hz θ hθ => by
        rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hM_Dz z hz θ hθ) 2)
  -- ## the two summands of the pairing
  have hint_AY : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2 * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2
        * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2) μM :=
    integrable_box' (F := fun z θ => Work.Spaces.Dz (Work.Spaces.Dz G) z θ
      * Work.Spaces.pth (Work.Spaces.pth G) z θ) (MA := M_DzDz * M_pthpth)
      (show ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2
        * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from hcontQ_DzDz.mul hcontQ_pthpth)
      (fun z hz θ => by rw [hDzDz_supp z hz θ]; ring)
      (fun z hz θ hθ => by
        simp only [abs_mul]
        exact mul_le_mul (hM_DzDz z hz θ hθ) (hM_pthpth z hz θ hθ) (abs_nonneg _) hM_DzDz0)
  have hint_bBY : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.FTS.EllipticEst.ThetaU.bcoef p.1 * Work.Spaces.Dz G p.1 p.2)
        * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2 * (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2) μM :=
    integrable_box' (F := fun z θ => (Work.FTS.EllipticEst.ThetaU.bcoef z
      * Work.Spaces.Dz G z θ) * Work.Spaces.pth (Work.Spaces.pth G) z θ)
      (MA := (3 * M_Dz) * M_pthpth)
      (show ContinuousOn (fun p : ℝ × ℝ => (Work.FTS.EllipticEst.ThetaU.bcoef p.1
        * Work.Spaces.Dz G p.1 p.2) * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from
        (hcontQ_bcoef.mul hcontQ_Dz).mul hcontQ_pthpth)
      (fun z hz θ => by rw [hDz_supp z hz θ]; ring)
      (fun z hz θ hθ => by
        simp only [abs_mul]
        exact mul_le_mul (mul_le_mul (hbcoef_le z hz) (hM_Dz z hz θ hθ) (abs_nonneg _)
          (by norm_num)) (hM_pthpth z hz θ hθ) (abs_nonneg _) (by positivity))
  set iA : ℝ := ∫ p, (Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2
      * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2 * (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2) ∂μM with hiA
  set iB : ℝ := ∫ p, ((Work.FTS.EllipticEst.ThetaU.bcoef p.1 * Work.Spaces.Dz G p.1 p.2)
      * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2 * (Work.Spaces.w p.1) ^ 2
      * Work.FTS.EllipticEst.thEta p.2) ∂μM with hiB
  have hsplitT : (∫ p, ((Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2
        + Work.FTS.EllipticEst.ThetaU.bcoef p.1 * Work.Spaces.Dz G p.1 p.2)
        * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2 * (Work.Spaces.w p.1) ^ 2
        * Work.FTS.EllipticEst.thEta p.2) ∂μM) = iA + iB := by
    rw [show (∫ p, ((Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2
          + Work.FTS.EllipticEst.ThetaU.bcoef p.1 * Work.Spaces.Dz G p.1 p.2)
          * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2 * (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2) ∂μM)
        = ∫ p, ((Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2
              * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2 * (Work.Spaces.w p.1) ^ 2
              * Work.FTS.EllipticEst.thEta p.2)
            + ((Work.FTS.EllipticEst.ThetaU.bcoef p.1 * Work.Spaces.Dz G p.1 p.2)
              * Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2 * (Work.Spaces.w p.1) ^ 2
              * Work.FTS.EllipticEst.thEta p.2)) ∂μM from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => by ring_nf))]
    rw [MeasureTheory.integral_add hint_AY hint_bBY]
  -- ## Cauchy–Schwarz for the two summands
  have hcsA : |iA| ≤ Real.sqrt DD * Real.sqrt TT := by
    have hcs := Work.Blocks.IMC.cs_integral_mul_le μM
      (f := fun p : ℝ × ℝ => Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2
        * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2)))
      (g := fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2
        * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2)))
      (aesm_Q (show ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2
        * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from
        hcontQ_DzDz.mul (hcontQ_w.mul hcontQ_thEta.sqrt)))
      (aesm_Q (show ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2
        * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from
        hcontQ_pthpth.mul (hcontQ_w.mul hcontQ_thEta.sqrt)))
      hint_A hint_Y
    have hfg : (∫ p, (Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2
          * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2)))
          * (Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2
            * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2))) ∂μM)
        = iA := by
      rw [hiA]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hae_prod] with p hp
      ring_nf
      rw [Real.sq_sqrt (Work.FTS.EllipticEst.thEta_nonneg hp.2)]
      ring
    have hf2 : (∫ p, (Work.Spaces.Dz (Work.Spaces.Dz G) p.1 p.2
          * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2))) ^ 2 ∂μM) = DD := by
      rw [← hDDprod]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hae_prod] with p hp
      ring_nf
      rw [Real.sq_sqrt (Work.FTS.EllipticEst.thEta_nonneg hp.2)]
    have hg2 : (∫ p, (Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2
          * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2))) ^ 2 ∂μM) = TT := by
      rw [← hTTprod]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hae_prod] with p hp
      ring_nf
      rw [Real.sq_sqrt (Work.FTS.EllipticEst.thEta_nonneg hp.2)]
    rw [hfg, hf2, hg2] at hcs
    exact hcs
  have hB2 : (∫ p, ((Work.FTS.EllipticEst.ThetaU.bcoef p.1 * Work.Spaces.Dz G p.1 p.2)
        * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2))) ^ 2 ∂μM)
      ≤ 9 * D := by
    have h1 : (∫ p, ((Work.FTS.EllipticEst.ThetaU.bcoef p.1 * Work.Spaces.Dz G p.1 p.2)
          * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2))) ^ 2 ∂μM)
        = ∫ p, (Work.FTS.EllipticEst.ThetaU.bcoef p.1) ^ 2
            * (Work.Spaces.Dz G p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
            * Work.FTS.EllipticEst.thEta p.2 ∂μM := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hae_prod] with p hp
      ring_nf
      rw [Real.sq_sqrt (Work.FTS.EllipticEst.thEta_nonneg hp.2)]
    rw [h1]
    have h2 : (∫ p, (Work.FTS.EllipticEst.ThetaU.bcoef p.1) ^ 2
          * (Work.Spaces.Dz G p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
          * Work.FTS.EllipticEst.thEta p.2 ∂μM)
        ≤ ∫ p, 9 * ((Work.Spaces.Dz G p.1 p.2) ^ 2 * (Work.Spaces.w p.1) ^ 2
            * Work.FTS.EllipticEst.thEta p.2) ∂μM := by
      refine MeasureTheory.integral_mono_ae hint_b' (hint_D.const_mul 9) ?_
      filter_upwards [hae_prod] with p hp
      have hb : (Work.FTS.EllipticEst.ThetaU.bcoef p.1) ^ 2 ≤ 9 := by
        have h := Work.FTS.EllipticEst.ThetaU.bcoef_abs_le (show (0 : ℝ) ≤ p.1 from hp.1)
        nlinarith [abs_nonneg (Work.FTS.EllipticEst.ThetaU.bcoef p.1),
          sq_abs (Work.FTS.EllipticEst.ThetaU.bcoef p.1)]
      have hσ : 0 ≤ Work.FTS.EllipticEst.thEta p.2 := Work.FTS.EllipticEst.thEta_nonneg hp.2
      have hw2 : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
      have hB : 0 ≤ (Work.Spaces.Dz G p.1 p.2) ^ 2 := sq_nonneg _
      have h := mul_le_mul_of_nonneg_right hb (mul_nonneg hB (mul_nonneg hw2 hσ))
      linarith [h]
    rw [MeasureTheory.integral_const_mul] at h2
    rw [hDprod] at h2
    linarith [h2]
  have hcsB : |iB| ≤ 3 * Real.sqrt D * Real.sqrt TT := by
    have hcs := Work.Blocks.IMC.cs_integral_mul_le μM
      (f := fun p : ℝ × ℝ => (Work.FTS.EllipticEst.ThetaU.bcoef p.1
        * Work.Spaces.Dz G p.1 p.2)
        * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2)))
      (g := fun p : ℝ × ℝ => Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2
        * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2)))
      (aesm_Q (show ContinuousOn (fun p : ℝ × ℝ => (Work.FTS.EllipticEst.ThetaU.bcoef p.1
        * Work.Spaces.Dz G p.1 p.2)
        * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from
        (hcontQ_bcoef.mul hcontQ_Dz).mul (hcontQ_w.mul hcontQ_thEta.sqrt)))
      (aesm_Q (show ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2
        * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from
        hcontQ_pthpth.mul (hcontQ_w.mul hcontQ_thEta.sqrt)))
      hint_b hint_Y
    have hfg : (∫ p, ((Work.FTS.EllipticEst.ThetaU.bcoef p.1 * Work.Spaces.Dz G p.1 p.2)
          * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2)))
          * (Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2
            * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2))) ∂μM)
        = iB := by
      rw [hiB]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hae_prod] with p hp
      ring_nf
      rw [Real.sq_sqrt (Work.FTS.EllipticEst.thEta_nonneg hp.2)]
      ring
    have hg2 : (∫ p, (Work.Spaces.pth (Work.Spaces.pth G) p.1 p.2
          * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2))) ^ 2 ∂μM) = TT := by
      rw [← hTTprod]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hae_prod] with p hp
      ring_nf
      rw [Real.sq_sqrt (Work.FTS.EllipticEst.thEta_nonneg hp.2)]
    rw [hfg, hg2] at hcs
    have h2 : Real.sqrt (∫ p, ((Work.FTS.EllipticEst.ThetaU.bcoef p.1
        * Work.Spaces.Dz G p.1 p.2)
        * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2))) ^ 2 ∂μM)
        ≤ 3 * Real.sqrt D := by
      have h3 := Real.sqrt_le_sqrt hB2
      rwa [sqrt_nine_mul hD0] at h3
    have h5 : Real.sqrt (∫ p, ((Work.FTS.EllipticEst.ThetaU.bcoef p.1
        * Work.Spaces.Dz G p.1 p.2)
        * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2))) ^ 2 ∂μM)
        * Real.sqrt TT ≤ 3 * Real.sqrt D * Real.sqrt TT :=
      mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
    linarith [hcs, h5]
  -- ## the bound on `|T|`
  have hTabs : |T| ≤ Real.sqrt DD * Real.sqrt TT + 3 * Real.sqrt D * Real.sqrt TT := by
    have hTi : T = -(iA + iB) := by rw [hTpair, hsplitT]
    have h1 : |iA + iB| ≤ |iA| + |iB| := abs_add_le _ _
    rw [hTi, abs_neg]
    linarith [h1, hcsA, hcsB]
  -- ## the `cot²` energy and the bound on `|T2|`
  set H2 : ℝ := ∫ p, (Work.Spaces.Dz G p.1 p.2) ^ 2 * (Real.cot (2 * p.2)) ^ 2
      * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 ∂μM with hH2def
  have hH2pos : 0 ≤ H2 := by
    rw [hH2def]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [hae_prod] with p hp
    have hσ : 0 ≤ Work.FTS.EllipticEst.thEta p.2 := Work.FTS.EllipticEst.thEta_nonneg hp.2
    have hc2 : 0 ≤ (Real.cot (2 * p.2)) ^ 2 := sq_nonneg _
    have hw2 : 0 ≤ (Work.Spaces.w p.1) ^ 2 := sq_nonneg _
    have hB : 0 ≤ (Work.Spaces.Dz G p.1 p.2) ^ 2 := sq_nonneg _
    exact mul_nonneg (mul_nonneg (mul_nonneg hB hc2) hw2) hσ
  have hT2cs : |T2| ≤ Real.sqrt H2 * Real.sqrt M := by
    rw [hT2prod]
    have hcs := Work.Blocks.IMC.cs_integral_mul_le μM
      (f := fun p : ℝ × ℝ => (Work.Spaces.Dz G p.1 p.2 * Real.cot (2 * p.2))
        * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2)))
      (g := fun p : ℝ × ℝ => Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2
        * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2)))
      (aesm_Q (show ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.Dz G p.1 p.2
        * Real.cot (2 * p.2))
        * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from
        (hcontQ_Dz.mul hcontQ_cot).mul (hcontQ_w.mul hcontQ_thEta.sqrt)))
      (aesm_Q (show ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2
        * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2)))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) from
        hcontQ_Dzpth.mul (hcontQ_w.mul hcontQ_thEta.sqrt)))
      hint_Bc hint_Bp
    have hfg : (∫ p, ((Work.Spaces.Dz G p.1 p.2 * Real.cot (2 * p.2))
          * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2)))
          * (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2
            * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2))) ∂μM)
        = ∫ p, (Work.Spaces.Dz G p.1 p.2 * Real.cot (2 * p.2))
            * (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2)
            * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 ∂μM := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hae_prod] with p hp
      ring_nf
      rw [Real.sq_sqrt (Work.FTS.EllipticEst.thEta_nonneg hp.2)]
      ring
    have hf2 : (∫ p, ((Work.Spaces.Dz G p.1 p.2 * Real.cot (2 * p.2))
          * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2))) ^ 2 ∂μM)
        = H2 := by
      rw [hH2def]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hae_prod] with p hp
      ring_nf
      rw [Real.sq_sqrt (Work.FTS.EllipticEst.thEta_nonneg hp.2)]
    have hg2 : (∫ p, (Work.Spaces.Dz (Work.Spaces.pth G) p.1 p.2
          * (Work.Spaces.w p.1 * Real.sqrt (Work.FTS.EllipticEst.thEta p.2))) ^ 2 ∂μM)
        = M := by
      rw [← hMprod]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [hae_prod] with p hp
      ring_nf
      rw [Real.sq_sqrt (Work.FTS.EllipticEst.thEta_nonneg hp.2)]
    rw [hfg, hf2, hg2] at hcs
    exact hcs
  have hH2le : H2 ≤ 1 / (1 + Work.Spaces.eta) ^ 2 * M + CH * D := by
    have h := hHardy hδ hδR (G := G) hstrip h0 h1 hsupp
    calc H2 = ∫ p, (Work.Spaces.Dz G p.1 p.2) ^ 2 * (Real.cot (2 * p.2)) ^ 2
            * (Work.Spaces.w p.1) ^ 2 * Work.FTS.EllipticEst.thEta p.2 ∂μM := hH2def
      _ = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2
            * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz G z θ) ^ 2
                * (Real.cot (2 * θ)) ^ 2 * Work.FTS.EllipticEst.thEta θ) := hH2z
      _ ≤ 1 / (1 + Work.Spaces.eta) ^ 2 * M + CH * D := by
            rw [hmix, hdInt]
            exact h
  -- ## assembling the scalar bound `M ≤ K P + Cp D`
  set P : ℝ := Real.sqrt DD * Real.sqrt TT + 3 * Real.sqrt D * Real.sqrt TT with hPdef
  have hM_le_P : M ≤ P + 2 * Work.Spaces.eta * Real.sqrt H2 * Real.sqrt M := by
    have h1 : -T ≤ |T| := neg_le_abs T
    have h2 : 0 ≤ 2 * Work.Spaces.eta := by linarith [hηpos]
    have h3 : 2 * Work.Spaces.eta * T2 ≤ 2 * Work.Spaces.eta * |T2| :=
      mul_le_mul_of_nonneg_left (le_abs_self T2) h2
    have h4 : 2 * Work.Spaces.eta * |T2| ≤ 2 * Work.Spaces.eta * Real.sqrt H2 * Real.sqrt M := by
      have h := mul_le_mul_of_nonneg_left hT2cs h2
      have h' : 2 * Work.Spaces.eta * (Real.sqrt H2 * Real.sqrt M)
          = 2 * Work.Spaces.eta * Real.sqrt H2 * Real.sqrt M := by ring
      linarith [h, h']
    have h5 : M ≤ |T| + 2 * Work.Spaces.eta * Real.sqrt H2 * Real.sqrt M := by
      linarith [hM_eq, h1, h3, h4]
    rw [hPdef]
    linarith [h5, hTabs]
  have hsqrtH2 : Real.sqrt H2 ≤ 1 / (1 + Work.Spaces.eta) * Real.sqrt M
      + Real.sqrt (CH * D) := by
    have h1 : 0 ≤ 1 / (1 + Work.Spaces.eta) ^ 2 * M := by positivity
    have h2 : 0 ≤ CH * D := mul_nonneg hCHpos.le hD0
    have hstep : Real.sqrt H2 ≤ Real.sqrt (1 / (1 + Work.Spaces.eta) ^ 2 * M + CH * D) :=
      Real.sqrt_le_sqrt hH2le
    have h3 : Real.sqrt (1 / (1 + Work.Spaces.eta) ^ 2 * M + CH * D)
        ≤ Real.sqrt (1 / (1 + Work.Spaces.eta) ^ 2 * M) + Real.sqrt (CH * D) :=
      sqrt_add_le' h1 h2
    have h4 : Real.sqrt (1 / (1 + Work.Spaces.eta) ^ 2 * M)
        = 1 / (1 + Work.Spaces.eta) * Real.sqrt M := by
      have h5 : (1 : ℝ) / (1 + Work.Spaces.eta) ^ 2 * M
          = (1 / (1 + Work.Spaces.eta)) ^ 2 * M := by
        rw [div_pow, one_pow]
      rw [h5, Real.sqrt_mul (by positivity) M, Real.sqrt_sq (by positivity)]
    linarith [hstep, h3, h4]
  have hM_scal : ((1 - Work.Spaces.eta) / (2 * (1 + Work.Spaces.eta))) * M
      ≤ P + 2 * Work.Spaces.eta ^ 2 * CH * (1 + Work.Spaces.eta) / (1 - Work.Spaces.eta) * D := by
    have hηle : (0 : ℝ) < 2 * Work.Spaces.eta := by linarith
    have hA : ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * M
        ≤ P + 2 * Work.Spaces.eta * Real.sqrt (CH * D) * Real.sqrt M := by
      have h2 : 2 * Work.Spaces.eta * Real.sqrt H2 * Real.sqrt M
          ≤ (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * M
            + 2 * Work.Spaces.eta * Real.sqrt (CH * D) * Real.sqrt M := by
        have h3 : 2 * Work.Spaces.eta * Real.sqrt H2 * Real.sqrt M
            ≤ 2 * Work.Spaces.eta
              * (1 / (1 + Work.Spaces.eta) * Real.sqrt M + Real.sqrt (CH * D))
              * Real.sqrt M := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          exact mul_le_mul_of_nonneg_left hsqrtH2 hηle.le
        have h4 : 2 * Work.Spaces.eta
              * (1 / (1 + Work.Spaces.eta) * Real.sqrt M + Real.sqrt (CH * D))
              * Real.sqrt M
            = (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * M
              + 2 * Work.Spaces.eta * Real.sqrt (CH * D) * Real.sqrt M := by
          have hs : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM0
          calc 2 * Work.Spaces.eta
                * (1 / (1 + Work.Spaces.eta) * Real.sqrt M + Real.sqrt (CH * D))
                * Real.sqrt M
              = 2 * Work.Spaces.eta * (1 / (1 + Work.Spaces.eta) * Real.sqrt M) * Real.sqrt M
                + 2 * Work.Spaces.eta * Real.sqrt (CH * D) * Real.sqrt M := by ring
            _ = (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * (Real.sqrt M * Real.sqrt M)
                + 2 * Work.Spaces.eta * Real.sqrt (CH * D) * Real.sqrt M := by ring
            _ = (2 * Work.Spaces.eta / (1 + Work.Spaces.eta)) * M
                + 2 * Work.Spaces.eta * Real.sqrt (CH * D) * Real.sqrt M := by rw [hs]
        linarith [h3, h4]
      have hcoef : (1 : ℝ) - 2 * Work.Spaces.eta / (1 + Work.Spaces.eta)
          = (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta) := by
        field_simp
        ring
      nlinarith [hM_le_P, h2, hcoef]
    have h5 : 2 * Real.sqrt (M * (Work.Spaces.eta ^ 2 * (CH * D)))
        ≤ ((1 - Work.Spaces.eta) / (2 * (1 + Work.Spaces.eta))) * M
          + (Work.Spaces.eta ^ 2 * (CH * D))
            / ((1 - Work.Spaces.eta) / (2 * (1 + Work.Spaces.eta))) :=
      two_sqrt_mul_le hM0 (by positivity) (by positivity)
    have h6 : 2 * Work.Spaces.eta * Real.sqrt (CH * D) * Real.sqrt M
        = 2 * Real.sqrt (M * (Work.Spaces.eta ^ 2 * (CH * D))) := by
      rw [show M * (Work.Spaces.eta ^ 2 * (CH * D))
          = Work.Spaces.eta ^ 2 * ((CH * D) * M) from by ring,
        Real.sqrt_mul (by positivity) ((CH * D) * M),
        Real.sqrt_sq (by positivity), Real.sqrt_mul (mul_nonneg hCHpos.le hD0) M]
      ring
    have h7 : (Work.Spaces.eta ^ 2 * (CH * D))
          / ((1 - Work.Spaces.eta) / (2 * (1 + Work.Spaces.eta)))
        = 2 * Work.Spaces.eta ^ 2 * CH * (1 + Work.Spaces.eta) / (1 - Work.Spaces.eta) * D := by
      rw [div_eq_iff (by positivity : ((1 - Work.Spaces.eta) / (2 * (1 + Work.Spaces.eta))) ≠ 0)]
      field_simp
    have hA' := hA
    rw [h6] at hA'
    have h9 : ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * M
        ≤ P + (((1 - Work.Spaces.eta) / (2 * (1 + Work.Spaces.eta))) * M
          + (Work.Spaces.eta ^ 2 * (CH * D))
            / ((1 - Work.Spaces.eta) / (2 * (1 + Work.Spaces.eta)))) := by
      linarith [hA', h5]
    rw [h7] at h9
    have hcf : (1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)
        - (1 - Work.Spaces.eta) / (2 * (1 + Work.Spaces.eta))
        = (1 - Work.Spaces.eta) / (2 * (1 + Work.Spaces.eta)) := by
      field_simp
      ring
    have hcf' : ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * M
        - ((1 - Work.Spaces.eta) / (2 * (1 + Work.Spaces.eta))) * M
        = ((1 - Work.Spaces.eta) / (2 * (1 + Work.Spaces.eta))) * M := by
      rw [← sub_mul, hcf]
    linarith [h9, hcf']
  have hMbound : M ≤ K * P + Cp * D := by
    have hk : 0 < 2 * (1 + Work.Spaces.eta) / (1 - Work.Spaces.eta) := by positivity
    have h2 := mul_le_mul_of_nonneg_left hM_scal hk.le
    have h3 : (2 * (1 + Work.Spaces.eta) / (1 - Work.Spaces.eta))
        * (((1 - Work.Spaces.eta) / (2 * (1 + Work.Spaces.eta))) * M) = M := by
      have hc : (2 * (1 + Work.Spaces.eta) / (1 - Work.Spaces.eta))
          * ((1 - Work.Spaces.eta) / (2 * (1 + Work.Spaces.eta))) = 1 := by
        have h1 : (1 - Work.Spaces.eta) ≠ 0 := ne_of_gt (by linarith)
        have h2 : (2 * (1 + Work.Spaces.eta)) ≠ 0 := by positivity
        field_simp
      rw [← mul_assoc, hc, one_mul]
    rw [h3] at h2
    rw [hKdef, hCpdef]
    linarith [h2]
  -- ## the `α`-arithmetic
  have hαP : α ^ 2 * P ≤ (α ^ 4 * DD + TT) / 2 + (3 / 8) * (α ^ 2 * D + TT) := by
    have h1 : α ^ 2 * (Real.sqrt DD * Real.sqrt TT) ≤ (α ^ 4 * DD + TT) / 2 := by
      have h := two_mul_sqrt_mul_le (a := α ^ 2) (x := DD) (y := TT)
        (by positivity) hDD0 hTT0
      rw [Real.sqrt_mul hDD0 TT] at h
      have h2 : (α ^ 2) ^ 2 = α ^ 4 := by ring
      linarith [h, h2]
    have h2 : α ^ 2 * (3 * Real.sqrt D * Real.sqrt TT) ≤ (3 / 8) * (α ^ 2 * D + TT) := by
      have h := two_mul_sqrt_mul_le (a := α) (x := D) (y := TT)
        hα0.le hD0 hTT0
      rw [Real.sqrt_mul hD0 TT] at h
      have hh : 2 * (α * (Real.sqrt D * Real.sqrt TT))
          = 2 * (α * Real.sqrt D * Real.sqrt TT) := by ring
      rw [hh] at h
      have h3 : α ^ 2 * (3 * Real.sqrt D * Real.sqrt TT)
          = (3 / 2) * α * (2 * (α * Real.sqrt D * Real.sqrt TT)) := by ring
      have h4 : (3 / 2) * α * (2 * (α * Real.sqrt D * Real.sqrt TT))
          ≤ (3 / 2) * α * (α ^ 2 * D + TT) :=
        mul_le_mul_of_nonneg_left h (by positivity)
      have h5 : (3 / 2) * α * (α ^ 2 * D + TT) ≤ (3 / 8) * (α ^ 2 * D + TT) := by
        have h6 : 0 ≤ α ^ 2 * D + TT := by positivity
        nlinarith [hα4, hα0, h6]
      linarith [h3, h4, h5]
    rw [hPdef]
    nlinarith [h1, h2]
  have hmain : α ^ 2 * M ≤ (K / 2) * (α ^ 4 * DD) + (7 * K / 8) * TT
      + (3 * K / 8 + Cp) * (α ^ 2 * D) := by
    have h1 : α ^ 2 * M ≤ K * (α ^ 2 * P) + Cp * (α ^ 2 * D) := by
      have h := mul_le_mul_of_nonneg_left hMbound (by positivity : (0 : ℝ) ≤ α ^ 2)
      nlinarith [h]
    have h2 : K * (α ^ 2 * P) ≤ K * ((α ^ 4 * DD + TT) / 2 + (3 / 8) * (α ^ 2 * D + TT)) :=
      mul_le_mul_of_nonneg_left hαP hKpos.le
    have h3 : K * ((α ^ 4 * DD + TT) / 2 + (3 / 8) * (α ^ 2 * D + TT)) + Cp * (α ^ 2 * D)
        = (K / 2) * (α ^ 4 * DD) + (7 * K / 8) * TT + (3 * K / 8 + Cp) * (α ^ 2 * D) := by
      ring
    linarith [h1, h2, h3]
  have hfinal : (K / 2) * (α ^ 4 * DD) + (7 * K / 8) * TT + (3 * K / 8 + Cp) * (α ^ 2 * D)
      ≤ Cfin * (α ^ 4 * DD + TT + α ^ 2 * D) := by
    have h1 : K / 2 ≤ Cfin := by rw [hCfindef]; exact le_max_left _ _
    have h2 : 7 * K / 8 ≤ Cfin := by
      rw [hCfindef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have h3 : 3 * K / 8 + Cp ≤ Cfin := by
      rw [hCfindef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hA : 0 ≤ α ^ 4 * DD := mul_nonneg (by positivity) hDD0
    have hB : 0 ≤ TT := hTT0
    have hC : 0 ≤ α ^ 2 * D := mul_nonneg (by positivity) hD0
    linarith [mul_le_mul_of_nonneg_right h1 hA, mul_le_mul_of_nonneg_right h2 hB,
      mul_le_mul_of_nonneg_right h3 hC]
  exact le_trans hmain hfinal

/-! ## The requested form -/

theorem interpol_mixed_box_proof : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ), 0 < α → α ≤ 1 / 4 → ∀ (G : ℝ → ℝ → ℝ),
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry G)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))) →
      (∀ z : ℝ, G z 0 = 0) → (∀ z : ℝ, G z (Real.pi / 2) = 0) →
      (∃ a b : ℝ, 0 < a ∧ a < b ∧ ∀ z ∉ Set.Icc a b, ∀ θ, G z θ = 0) →
      α ^ 2 * Work.FTS.EllipticEst.mixInt G
        ≤ C * (α ^ 4 * Work.FTS.EllipticEst.ddInt G
            + Work.FTS.EllipticEst.ttInt G
            + α ^ 2 * Work.FTS.EllipticEst.dInt G) := by
  obtain ⟨C, hC, hmain⟩ := interp_box_uniform_aux
  refine ⟨C, hC, ?_⟩
  intro α hα hα4 G hsm h0 hπ hbox
  obtain ⟨a, b, ha, hab, hsupp⟩ := hbox
  exact hmain α hα hα4 G hsm h0 hπ a b ha hab hsupp

end Work.Blocks
