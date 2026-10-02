/-
Work.MRMT.Found — the Beurling transform on `L²(ℂ)` agrees, on `C¹` compactly supported data,
with the Cauchy transform of the Wirtinger derivative `∂u`.

`beurlingL2` is the `L²` Fourier multiplier with symbol `beurlingSymbol ξ = ξ̄/ξ`; the proof
never uses the singular-integral representation of `beurlingL2`.  It shows that the `L²`
function `w = beurlingL2 u - C(∂u)` has vanishing weak `∂̄`-derivative and lies in `L²`; by
Weyl's lemma `w` agrees almost everywhere with an entire function, which is square-integrable
and therefore zero.

The weak-`∂̄` computation for `beurlingL2 u` is done on the Fourier side.  For a Schwartz
function `ψ` one has, by Plancherel and the Fourier rules for `∂`, `∂̄`,
`⟪∂ψ, S u⟫ = -(π i) ∫ ξ̄ (𝓕u)(ξ) conj((𝓕ψ)(ξ)) dξ = ⟪∂̄ψ, u⟫`,
and integration by parts converts the right-hand side into `-⟪ψ, ∂u⟫`.  Hence `∂̄(S u) = ∂u`
weakly.
-/
import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Cauchy.Defs
import Submission.Work.MRMT.QC.WirtingerCalc
import Submission.Work.MRMT.Beltrami.integral_mul_dz_eq_neg
import Submission.Work.MRMT.Beltrami.cauchyTransform_inversion
import Submission.Work.MRMT.Sobolev.is_dbar_deriv_unique
import Submission.Work.MRMT.Weyl.weyl_lemma
import Submission.Work.MRMT.Found.memLp_cauchyTransform_dz
import Submission.Work.MRMT.Found.analytic_eq_zero_of_memLp_two

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found
open MeasureTheory Filter Topology Complex Function SchwartzMap LineDeriv
open scoped Distributions Topology ENNReal FourierTransform ComplexInnerProductSpace ComplexConjugate
noncomputable section
open Work.MRMT

noncomputable def dzSM (f : 𝓢(ℂ,ℂ)) : 𝓢(ℂ,ℂ) :=
  (2:ℂ)⁻¹ • (∂_{(1:ℂ)} f - Complex.I • ∂_{(Complex.I)} f)
noncomputable def dzbarSM (f : 𝓢(ℂ,ℂ)) : 𝓢(ℂ,ℂ) :=
  (2:ℂ)⁻¹ • (∂_{(1:ℂ)} f + Complex.I • ∂_{(Complex.I)} f)

lemma dzSM_apply (f : 𝓢(ℂ,ℂ)) (z : ℂ) : (dzSM f) z = dz (f:ℂ→ℂ) z := by
  simp only [dzSM, smul_apply, sub_apply, smul_eq_mul, lineDerivOp_apply_eq_fderiv,
    Work.MRMT.dz, div_eq_mul_inv]
  ring

lemma dzbarSM_apply (f : 𝓢(ℂ,ℂ)) (z : ℂ) : (dzbarSM f) z = dzbar (f:ℂ→ℂ) z := by
  simp only [dzbarSM, smul_apply, add_apply, smul_eq_mul, lineDerivOp_apply_eq_fderiv,
    Work.MRMT.dzbar, div_eq_mul_inv]
  ring

lemma inner_toLp_schwartz_left (f : 𝓢(ℂ,ℂ)) (F : Lp ℂ 2 (volume:Measure ℂ)) :
    ⟪f.toLp 2 (volume:Measure ℂ), F⟫ = ∫ z, (F : ℂ→ℂ) z * starRingEnd ℂ (f z) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [SchwartzMap.coeFn_toLp f 2 (volume:Measure ℂ)] with z hz
  rw [hz, RCLike.inner_apply]

lemma inner_schwartz_toLp_right (f : 𝓢(ℂ,ℂ)) {g : ℂ→ℂ} (hg : MemLp g 2 (volume:Measure ℂ)) :
    ⟪f.toLp 2 (volume:Measure ℂ), hg.toLp g⟫ = ∫ z, g z * starRingEnd ℂ (f z) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hg, SchwartzMap.coeFn_toLp f 2 (volume:Measure ℂ)] with z h1 h2
  rw [h1, h2, RCLike.inner_apply]

lemma inner_dz_eq (ξ a b : ℂ) :
    inner ℂ ((Real.pi:ℂ)*Complex.I*starRingEnd ℂ ξ*b) (beurlingSymbol ξ * a)
      = -((Real.pi:ℂ))*Complex.I*starRingEnd ℂ ξ*a*starRingEnd ℂ b := by
  rw [RCLike.inner_apply]
  rw [map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I]
  simp only [Complex.conj_conj]
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [beurlingSymbol]
  · rw [beurlingSymbol_of_ne_zero hξ]; field_simp

lemma inner_dzbar_eq (ξ a b : ℂ) :
    inner ℂ ((Real.pi:ℂ)*Complex.I*ξ*b) a
      = -((Real.pi:ℂ))*Complex.I*starRingEnd ℂ ξ*a*starRingEnd ℂ b := by
  rw [RCLike.inner_apply]
  rw [map_mul, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

lemma fourier_dzSM_val (f : 𝓢(ℂ,ℂ)) :
    ((𝓕 (dzSM f) : 𝓢(ℂ,ℂ)) : ℂ → ℂ)
      = fun ξ => Real.pi * Complex.I * starRingEnd ℂ ξ * ((𝓕 f : 𝓢(ℂ,ℂ)) : ℂ → ℂ) ξ := by
  have hval : ∀ m : ℂ, ∀ ξ : ℂ, ((𝓕 (∂_{m} f) : 𝓢(ℂ,ℂ)) : ℂ → ℂ) ξ
      = (2*Real.pi*Complex.I) * (((inner ℝ ξ m : ℝ)) : ℂ) * ((𝓕 f : 𝓢(ℂ,ℂ)) : ℂ → ℂ) ξ := by
    intro m ξ
    rw [SchwartzMap.fourier_lineDerivOp_eq]
    have htg : (fun ξ : ℂ => inner ℝ ξ m).HasTemperateGrowth := by
      have : (innerSL ℝ).flip m = fun ξ : ℂ => inner ℝ ξ m := rfl
      rw [← this]; exact ((innerSL ℝ).flip m).hasTemperateGrowth
    rw [smul_apply, SchwartzMap.smulLeftCLM_apply_apply htg]
    simp only [smul_eq_mul, RCLike.real_smul_eq_coe_mul]
    set Y : ℂ := ((𝓕 f : 𝓢(ℂ,ℂ)) : ℂ → ℂ) ξ with hY
    simp only [mul_assoc]; rfl
  have hlin : (𝓕 (dzSM f) : 𝓢(ℂ,ℂ))
      = (2:ℂ)⁻¹ • (𝓕 (∂_{(1:ℂ)} f) - Complex.I • 𝓕 (∂_{(Complex.I)} f)) := by
    change fourierTransformCLM ℂ (dzSM f) = _
    simp only [dzSM, map_smul, map_sub, SchwartzMap.fourierTransformCLM_apply]
  rw [hlin]
  funext ξ
  simp only [smul_apply, sub_apply, smul_eq_mul]
  rw [hval (1:ℂ) ξ, hval (Complex.I) ξ]
  rw [show inner ℝ ξ (1:ℂ) = ξ.re from by rw [Complex.inner]; simp,
      show inner ℝ ξ Complex.I = ξ.im from by
        rw [Complex.inner]; simp [Complex.mul_re, Complex.conj_re, Complex.conj_im],
      show starRingEnd ℂ ξ = (ξ.re:ℂ) - (ξ.im:ℂ)*Complex.I from by
        nth_rewrite 1 [← Complex.re_add_im ξ]
        simp only [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring]
  set Y : ℂ := ((𝓕 f : 𝓢(ℂ,ℂ)) : ℂ → ℂ) ξ with hY
  ring_nf

lemma fourier_dzbarSM_val (f : 𝓢(ℂ,ℂ)) :
    ((𝓕 (dzbarSM f) : 𝓢(ℂ,ℂ)) : ℂ → ℂ)
      = fun ξ => Real.pi * Complex.I * ξ * ((𝓕 f : 𝓢(ℂ,ℂ)) : ℂ → ℂ) ξ := by
  have hval : ∀ m : ℂ, ∀ ξ : ℂ, ((𝓕 (∂_{m} f) : 𝓢(ℂ,ℂ)) : ℂ → ℂ) ξ
      = (2*Real.pi*Complex.I) * (((inner ℝ ξ m : ℝ)) : ℂ) * ((𝓕 f : 𝓢(ℂ,ℂ)) : ℂ → ℂ) ξ := by
    intro m ξ
    rw [SchwartzMap.fourier_lineDerivOp_eq]
    have htg : (fun ξ : ℂ => inner ℝ ξ m).HasTemperateGrowth := by
      have : (innerSL ℝ).flip m = fun ξ : ℂ => inner ℝ ξ m := rfl
      rw [← this]; exact ((innerSL ℝ).flip m).hasTemperateGrowth
    rw [smul_apply, SchwartzMap.smulLeftCLM_apply_apply htg]
    simp only [smul_eq_mul, RCLike.real_smul_eq_coe_mul]
    set Y : ℂ := ((𝓕 f : 𝓢(ℂ,ℂ)) : ℂ → ℂ) ξ with hY
    simp only [mul_assoc]; rfl
  have hlin : (𝓕 (dzbarSM f) : 𝓢(ℂ,ℂ))
      = (2:ℂ)⁻¹ • (𝓕 (∂_{(1:ℂ)} f) + Complex.I • 𝓕 (∂_{(Complex.I)} f)) := by
    change fourierTransformCLM ℂ (dzbarSM f) = _
    simp only [dzbarSM, map_smul, map_add, SchwartzMap.fourierTransformCLM_apply]
  rw [hlin]
  funext ξ
  simp only [smul_apply, add_apply, smul_eq_mul]
  rw [hval (1:ℂ) ξ, hval (Complex.I) ξ]
  rw [show inner ℝ ξ (1:ℂ) = ξ.re from by rw [Complex.inner]; simp,
      show inner ℝ ξ Complex.I = ξ.im from by
        rw [Complex.inner]; simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]]
  set Y : ℂ := ((𝓕 f : 𝓢(ℂ,ℂ)) : ℂ → ℂ) ξ with hY
  conv_rhs => rw [← Complex.re_add_im ξ]
  ring_nf

-- (A)
lemma inner_dzS_eq_inner_dzbarS {u : ℂ → ℂ} (hLp : MemLp u 2 (volume : Measure ℂ)) (ψ : 𝓢(ℂ,ℂ)) :
    ⟪(dzSM ψ).toLp 2 (volume : Measure ℂ), beurlingL2 (hLp.toLp u)⟫
      = ⟪(dzbarSM ψ).toLp 2 (volume : Measure ℂ), hLp.toLp u⟫ := by
  set Fu : Lp ℂ 2 (volume:Measure ℂ) := 𝓕 (hLp.toLp u) with hFu
  have hFS : 𝓕 (beurlingL2 (hLp.toLp u))
      = mulL2 beurlingSymbol aestronglyMeasurable_beurlingSymbol
          (Eventually.of_forall norm_beurlingSymbol_le) Fu := by
    refine Lp.ext ?_
    have h1 : (((𝓕 (beurlingL2 (hLp.toLp u))) : Lp ℂ 2 (volume:Measure ℂ)) : ℂ → ℂ)
        =ᵐ[(volume:Measure ℂ)] fun ξ => beurlingSymbol ξ * ((Fu : Lp ℂ 2 (volume:Measure ℂ)) : ℂ → ℂ) ξ :=
      fourier_beurlingL2 (hLp.toLp u)
    exact h1.trans (mulL2_apply_ae beurlingSymbol aestronglyMeasurable_beurlingSymbol
        (Eventually.of_forall norm_beurlingSymbol_le) Fu).symm
  have hA : ⟪(dzSM ψ).toLp 2 (volume:Measure ℂ), beurlingL2 (hLp.toLp u)⟫
      = ∫ ξ, -((Real.pi:ℂ))*Complex.I*starRingEnd ℂ ξ*((Fu:ℂ→ℂ) ξ)*starRingEnd ℂ (((𝓕 ψ : 𝓢(ℂ,ℂ)) : ℂ→ℂ) ξ) := by
    rw [← Lp.inner_fourier_eq]
    rw [SchwartzMap.toLp_fourier_eq (dzSM ψ), hFS]
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [SchwartzMap.coeFn_toLp (𝓕 (dzSM ψ)) 2 (volume:Measure ℂ),
      mulL2_apply_ae beurlingSymbol aestronglyMeasurable_beurlingSymbol
        (Eventually.of_forall norm_beurlingSymbol_le) Fu] with ξ h1 h2
    rw [h1, h2, fourier_dzSM_val ψ]
    exact inner_dz_eq ξ ((Fu:ℂ→ℂ) ξ) (((𝓕 ψ : 𝓢(ℂ,ℂ)) : ℂ→ℂ) ξ)
  have hB : ⟪(dzbarSM ψ).toLp 2 (volume:Measure ℂ), hLp.toLp u⟫
      = ∫ ξ, -((Real.pi:ℂ))*Complex.I*starRingEnd ℂ ξ*((Fu:ℂ→ℂ) ξ)*starRingEnd ℂ (((𝓕 ψ : 𝓢(ℂ,ℂ)) : ℂ→ℂ) ξ) := by
    rw [← Lp.inner_fourier_eq]
    rw [SchwartzMap.toLp_fourier_eq (dzbarSM ψ)]
    rw [← hFu]
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [SchwartzMap.coeFn_toLp (𝓕 (dzbarSM ψ)) 2 (volume:Measure ℂ)] with ξ h1
    rw [h1, fourier_dzbarSM_val ψ]
    exact inner_dzbar_eq ξ ((Fu:ℂ→ℂ) ξ) (((𝓕 ψ : 𝓢(ℂ,ℂ)) : ℂ→ℂ) ξ)
  rw [hA, hB]

-- (B)
lemma inner_dzbarS_eq_neg {u : ℂ → ℂ} (hc : ContDiff ℝ 1 u) (hs : HasCompactSupport u)
    (hLp : MemLp u 2 (volume:Measure ℂ)) (hdz : MemLp (fun z => dz u z) 2 (volume:Measure ℂ))
    (ψ : 𝓢(ℂ,ℂ)) :
    ⟪(dzbarSM ψ).toLp 2 (volume:Measure ℂ), hLp.toLp u⟫
      = -⟪ψ.toLp 2 (volume:Measure ℂ), hdz.toLp (fun z => dz u z)⟫ := by
  have hconjcd : ContDiff ℝ 1 (fun z : ℂ => starRingEnd ℂ ((ψ:ℂ→ℂ) z)) := by
    have h : ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (⇑Complex.conjCLE) :=
      ContinuousLinearEquiv.contDiff (n := (((⊤ : ℕ∞)) : WithTop ℕ∞)) Complex.conjCLE
    have h2 : ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) ((fun z : ℂ => starRingEnd ℂ z) ∘ (ψ:ℂ→ℂ)) := by
      simpa [Function.comp_def] using h.comp (ψ.smooth (⊤ : ℕ∞))
    exact h2.of_le (by simp)
  have hibp := Work.MRMT.Beltrami.integral_mul_dz_eq_neg
    (f := fun z : ℂ => starRingEnd ℂ ((ψ:ℂ→ℂ) z)) (g := u) hconjcd hc hs
  have hL : ⟪(dzbarSM ψ).toLp 2 (volume:Measure ℂ), hLp.toLp u⟫
      = ∫ z, u z * starRingEnd ℂ (dzbar ((ψ:ℂ→ℂ)) z) := by
    rw [inner_toLp_schwartz_left (dzbarSM ψ) (hLp.toLp u)]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hLp] with z hz
    rw [hz, dzbarSM_apply]
  have hR : ⟪ψ.toLp 2 (volume:Measure ℂ), hdz.toLp (fun z => dz u z)⟫
      = ∫ z, dz u z * starRingEnd ℂ ((ψ:ℂ→ℂ) z) :=
    inner_schwartz_toLp_right ψ hdz
  rw [hL, hR]
  have hdz_conj : ∀ z, dz (fun y : ℂ => starRingEnd ℂ ((ψ:ℂ→ℂ) y)) z = starRingEnd ℂ (dzbar ((ψ:ℂ→ℂ)) z) :=
    fun z => Work.MRMT.QC.dz_conj (ψ.differentiableAt)
  have h1 : (∫ z, dz u z * starRingEnd ℂ ((ψ:ℂ→ℂ) z))
      = ∫ z, starRingEnd ℂ ((ψ:ℂ→ℂ) z) * dz u z := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_); ring
  have h2 : (∫ z, dz (fun y : ℂ => starRingEnd ℂ ((ψ:ℂ→ℂ) y)) z * u z)
      = ∫ z, u z * starRingEnd ℂ (dzbar ((ψ:ℂ→ℂ)) z) := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hdz_conj z]; ring
  rw [h1, ← h2, hibp]
  ring

lemma inner_dzS_eq_neg {u : ℂ → ℂ} (hc : ContDiff ℝ 1 u) (hs : HasCompactSupport u)
    (hLp : MemLp u 2 (volume:Measure ℂ)) (hdz : MemLp (fun z => dz u z) 2 (volume:Measure ℂ))
    (ψ : 𝓢(ℂ,ℂ)) :
    ⟪(dzSM ψ).toLp 2 (volume:Measure ℂ), beurlingL2 (hLp.toLp u)⟫
      = -⟪ψ.toLp 2 (volume:Measure ℂ), hdz.toLp (fun z => dz u z)⟫ :=
  (inner_dzS_eq_inner_dzbarS hLp ψ).trans (inner_dzbarS_eq_neg hc hs hLp hdz ψ)

lemma memLp_dz {u : ℂ → ℂ} (hc : ContDiff ℝ 1 u) (hs : HasCompactSupport u) :
    MemLp (fun z => dz u z) 2 (volume : Measure ℂ) := by
  have hcont : Continuous (fun z => dz u z) := by
    have h := hc.continuous_fderiv (by norm_num)
    simp only [Work.MRMT.dz]
    exact ((h.clm_apply continuous_const).sub
      (continuous_const.mul (h.clm_apply continuous_const))).div_const 2
  have hcs : HasCompactSupport (fun z => dz u z) := by
    have h1 : HasCompactSupport (fun z : ℂ => fderiv ℝ u z 1) := hs.fderiv_apply ℝ 1
    have h2 : HasCompactSupport (fun z : ℂ => fderiv ℝ u z Complex.I) := hs.fderiv_apply ℝ Complex.I
    have h3 : HasCompactSupport (fun z : ℂ => Complex.I * fderiv ℝ u z Complex.I) :=
      h2.comp_left (g := fun w : ℂ => Complex.I * w) (by simp)
    have h4 : HasCompactSupport (fun z : ℂ => fderiv ℝ u z 1 - Complex.I * fderiv ℝ u z Complex.I) :=
      h1.sub h3
    have h5 := h4.comp_left (g := fun w : ℂ => w * (2:ℂ)⁻¹) (by simp)
    simpa only [Work.MRMT.dz, div_eq_mul_inv, Function.comp_def] using h5
  have hcs2 : HasCompactSupport (fun z => ‖dz u z‖ ^ 2) :=
    hcs.comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)
  have hcont2 : Continuous (fun z => ‖dz u z‖ ^ 2) := hcont.norm.pow 2
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  exact hcont2.integrable_of_hasCompactSupport hcs2

noncomputable def conjTest (φ : 𝓓^{⊤}((⊤ : TopologicalSpace.Opens ℂ), ℂ)) : 𝓢(ℂ,ℂ) :=
  HasCompactSupport.toSchwartzMap (E := ℂ) (F := ℂ)
    (φ.hasCompactSupport.comp_left (g := fun z : ℂ => starRingEnd ℂ z) (by simp))
    (by
      have h : ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (⇑Complex.conjCLE) :=
        ContinuousLinearEquiv.contDiff (n := (((⊤ : ℕ∞)) : WithTop ℕ∞)) Complex.conjCLE
      have h2 : ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞)
          ((fun z : ℂ => starRingEnd ℂ z) ∘ (φ:ℂ→ℂ)) := by
        simpa [Function.comp_def] using h.comp φ.contDiff
      exact h2)

lemma conjTest_coe (φ : 𝓓^{⊤}((⊤ : TopologicalSpace.Opens ℂ), ℂ)) : ⇑(conjTest φ) = fun z => starRingEnd ℂ (φ z) := rfl

lemma isDbarDeriv_sub {f1 f2 g1 g2 : ℂ → ℂ} (h1 : IsDbarDeriv f1 g1) (h2 : IsDbarDeriv f2 g2) :
    IsDbarDeriv (fun z => f1 z - f2 z) (fun z => g1 z - g2 z) := by
  refine ⟨h1.1.sub h2.1, h1.2.1.sub h2.2.1, fun φ => ?_⟩
  obtain ⟨ha1, hb1, hc1⟩ := h1.2.2 φ
  obtain ⟨ha2, hb2, hc2⟩ := h2.2.2 φ
  refine ⟨?_, ?_, ?_⟩
  · refine (ha1.sub ha2).congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply]; ring
  · refine (hb1.sub hb2).congr (Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply]; ring
  · rw [show (∫ z, (f1 z - f2 z) * dzbar (φ:ℂ→ℂ) z)
        = ∫ z, (f1 z * dzbar (φ:ℂ→ℂ) z - f2 z * dzbar (φ:ℂ→ℂ) z) from
      integral_congr_ae (Eventually.of_forall fun z => by ring)]
    rw [integral_sub ha1 ha2, hc1, hc2]
    rw [show (∫ z, (g1 z - g2 z) * (φ:ℂ→ℂ) z)
        = ∫ z, (g1 z * (φ:ℂ→ℂ) z - g2 z * (φ:ℂ→ℂ) z) from
      integral_congr_ae (Eventually.of_forall fun z => by ring)]
    rw [integral_sub hb1 hb2]
    ring


lemma memLp_two_of_continuous_hasCompactSupport {g : ℂ → ℂ} (hcont : Continuous g)
    (hcs : HasCompactSupport g) : MemLp g 2 (volume : Measure ℂ) := by
  have hcs2 : HasCompactSupport (fun z => ‖g z‖ ^ 2) :=
    hcs.comp_left (g := fun w : ℂ => ‖w‖ ^ 2) (by simp)
  have hcont2 : Continuous (fun z => ‖g z‖ ^ 2) := hcont.norm.pow 2
  rw [memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable]
  exact hcont2.integrable_of_hasCompactSupport hcs2

lemma continuous_dz {u : ℂ → ℂ} (hc : ContDiff ℝ 1 u) : Continuous (fun z => dz u z) := by
  have h := hc.continuous_fderiv (by norm_num)
  simp only [Work.MRMT.dz]
  exact ((h.clm_apply continuous_const).sub
    (continuous_const.mul (h.clm_apply continuous_const))).div_const 2

lemma hasCompactSupport_dz_aux {u : ℂ → ℂ} (hs : HasCompactSupport u) :
    HasCompactSupport (fun z => dz u z) := by
  have h1 : HasCompactSupport (fun z : ℂ => fderiv ℝ u z 1) := hs.fderiv_apply ℝ 1
  have h2 : HasCompactSupport (fun z : ℂ => fderiv ℝ u z Complex.I) := hs.fderiv_apply ℝ Complex.I
  have h3 : HasCompactSupport (fun z : ℂ => Complex.I * fderiv ℝ u z Complex.I) :=
    h2.comp_left (g := fun w : ℂ => Complex.I * w) (by simp)
  have h4 : HasCompactSupport (fun z : ℂ => fderiv ℝ u z 1 - Complex.I * fderiv ℝ u z Complex.I) :=
    h1.sub h3
  have h5 := h4.comp_left (g := fun w : ℂ => (w * (2:ℂ)⁻¹)) (by simp)
  simpa only [Work.MRMT.dz, div_eq_mul_inv, Function.comp_def] using h5

lemma continuous_dzbar_test (φ : 𝓓^{⊤}((⊤ : TopologicalSpace.Opens ℂ), ℂ)) :
    Continuous (fun z => dzbar (φ:ℂ→ℂ) z) := by
  exact Work.MRMT.Weyl.continuous_dzbar_of_contDiff (u := (φ:ℂ→ℂ)) (n := 1)
    (φ.contDiff.of_le (by simp)) (by norm_num)

lemma hasCompactSupport_dzbar_test (φ : 𝓓^{⊤}((⊤ : TopologicalSpace.Opens ℂ), ℂ)) :
    HasCompactSupport (fun z => dzbar (φ:ℂ→ℂ) z) := by
  have h1 : HasCompactSupport (fun z : ℂ => fderiv ℝ (φ:ℂ→ℂ) z 1) := φ.hasCompactSupport.fderiv_apply ℝ 1
  have h2 : HasCompactSupport (fun z : ℂ => fderiv ℝ (φ:ℂ→ℂ) z Complex.I) := φ.hasCompactSupport.fderiv_apply ℝ Complex.I
  have h3 : HasCompactSupport (fun z : ℂ => Complex.I * fderiv ℝ (φ:ℂ→ℂ) z Complex.I) :=
    h2.comp_left (g := fun w : ℂ => Complex.I * w) (by simp)
  have h4 : HasCompactSupport
      (fun z : ℂ => fderiv ℝ (φ:ℂ→ℂ) z 1 + Complex.I * fderiv ℝ (φ:ℂ→ℂ) z Complex.I) := h1.add h3
  have h5 := h4.comp_left (g := fun w : ℂ => (w * (2:ℂ)⁻¹)) (by simp)
  simpa only [Work.MRMT.dzbar, div_eq_mul_inv, Function.comp_def] using h5

lemma isDbarDeriv_beurlingL2 {u : ℂ → ℂ} (hc : ContDiff ℝ 1 u) (hs : HasCompactSupport u)
    (hLp : MemLp u 2 (volume:Measure ℂ)) :
    IsDbarDeriv (fun z => ((beurlingL2 (hLp.toLp u) : Lp ℂ 2 (volume:Measure ℂ)) : ℂ→ℂ) z)
      (fun z => dz u z) := by
  have hdz : MemLp (fun z => dz u z) 2 (volume:Measure ℂ) :=
    memLp_two_of_continuous_hasCompactSupport (continuous_dz hc) (hasCompactSupport_dz_aux hs)
  refine ⟨(Lp.memLp (beurlingL2 (hLp.toLp u))).locallyIntegrable (by norm_num),
    hdz.locallyIntegrable (by norm_num), fun φ => ?_⟩
  have hpair := inner_dzS_eq_neg hc hs hLp hdz (conjTest φ)
  have e1 : ⟪(dzSM (conjTest φ)).toLp 2 (volume:Measure ℂ), beurlingL2 (hLp.toLp u)⟫
      = ∫ z, ((beurlingL2 (hLp.toLp u) : Lp ℂ 2 (volume:Measure ℂ)) : ℂ→ℂ) z * dzbar (φ:ℂ→ℂ) z := by
    rw [inner_toLp_schwartz_left (dzSM (conjTest φ)) (beurlingL2 (hLp.toLp u))]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [dzSM_apply, conjTest_coe]
    rw [Work.MRMT.QC.dz_conj (F := (φ:ℂ→ℂ)) ((φ.contDiff.differentiable (by simp)).differentiableAt)]
    simp
  have e2 : ⟪(conjTest φ).toLp 2 (volume:Measure ℂ), hdz.toLp (fun z => dz u z)⟫
      = ∫ z, dz u z * (φ:ℂ→ℂ) z := by
    rw [inner_schwartz_toLp_right (conjTest φ) hdz]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [conjTest_coe]; simp
  rw [e1, e2] at hpair
  refine ⟨?_, ?_, hpair⟩
  · exact MemLp.integrable_mul (Lp.memLp (beurlingL2 (hLp.toLp u)))
      (memLp_two_of_continuous_hasCompactSupport (continuous_dzbar_test φ) (hasCompactSupport_dzbar_test φ))
  · exact (continuous_dz hc).mul φ.continuous |>.integrable_of_hasCompactSupport
      (hasCompactSupport_dz_aux hs |>.mul_right)

theorem beurlingL2_eq_cauchyTransform_dz {u : ℂ → ℂ} (hc : ContDiff ℝ 1 u) (hs : HasCompactSupport u)
    (hLp : MeasureTheory.MemLp u 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) :
    (((beurlingL2 (hLp.toLp u) : MeasureTheory.Lp ℂ 2 (MeasureTheory.volume : MeasureTheory.Measure ℂ)) :
        ℂ → ℂ) =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure ℂ)]
      cauchyTransform (fun w => dz u w)) := by
  have hdz := memLp_two_of_continuous_hasCompactSupport (continuous_dz hc) (hasCompactSupport_dz_aux hs)
  have hSu := isDbarDeriv_beurlingL2 hc hs hLp
  have hint : Integrable (fun z => dz u z) volume :=
    (continuous_dz hc).integrable_of_hasCompactSupport (hasCompactSupport_dz_aux hs)
  have hC : IsDbarDeriv (cauchyTransform (fun z => dz u z)) (fun z => dz u z) :=
    Work.MRMT.Beltrami.cauchyTransform_inversion (fun z => dz u z) hint
  have hsub : IsDbarDeriv
      (fun z => ((beurlingL2 (hLp.toLp u) : Lp ℂ 2 (volume:Measure ℂ)) : ℂ→ℂ) z
        - cauchyTransform (fun w => dz u w) z) (fun _ => 0) := by
    have h := isDbarDeriv_sub hSu hC
    simpa using h
  have hwLp : MemLp (fun z => ((beurlingL2 (hLp.toLp u) : Lp ℂ 2 (volume:Measure ℂ)) : ℂ→ℂ) z
        - cauchyTransform (fun w => dz u w) z) 2 volume :=
    (Lp.memLp (beurlingL2 (hLp.toLp u))).sub (memLp_cauchyTransform_dz hc hs)
  have hwc : IsWeaklyConformal (fun z => ((beurlingL2 (hLp.toLp u) : Lp ℂ 2 (volume:Measure ℂ)) : ℂ→ℂ) z
        - cauchyTransform (fun w => dz u w) z) :=
    ⟨0, hsub, Eventually.of_forall fun z => rfl⟩
  obtain ⟨F, hFana, hFeq⟩ := Work.MRMT.Weyl.weyl_lemma hsub.1 hwc
  have hFmem : MemLp F 2 volume := MemLp.ae_eq hFeq hwLp
  have hFzero : F = 0 := analytic_eq_zero_of_memLp_two hFana hFmem
  have hw0 : (fun z => ((beurlingL2 (hLp.toLp u) : Lp ℂ 2 (volume:Measure ℂ)) : ℂ→ℂ) z
        - cauchyTransform (fun w => dz u w) z) =ᵐ[(volume:Measure ℂ)] 0 := by
    rw [hFzero] at hFeq; simpa using hFeq
  filter_upwards [hw0] with z hz
  exact sub_eq_zero.mp hz

end
end Work.MRMT.Found
