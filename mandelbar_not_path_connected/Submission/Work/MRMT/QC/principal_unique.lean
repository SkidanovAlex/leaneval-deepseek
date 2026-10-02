/-
Copyright: Work.MRMT (mandelbar) subproject.

# Uniqueness of the principal quasiconformal solution

This file proves `Work.MRMT.QC.principal_unique`: two quasiconformal maps of `ℂ` with the same
complex dilatation `μ` and the same principal normalisation `φ z = z + O(1/z)` at infinity are
equal.

The route is the `L²`-energy argument of the theory of quasiregular maps, carried out in full:

* put `h := φ - ψ`; then `h` is continuous, `h z = O(1/z)`, `h ∈ W^{1,2}_{loc}` and
  `∂̄h = μ ∂h` a.e.;
* cut off `h` by the standard family `ψₙ` (one on `B(0,Rₙ)`, supported in `B(0,2Rₙ)`) and apply
  the **energy identity for compactly supported `W^{1,2}` functions**
  (`energy_identity_of_w12_compactSupport`, proved below by mollification from the smooth case
  `Work.MRMT.Beltrami.energy_identity_of_contDiff_two`) to `uₙ = ψₙ h`, together with the a priori
  estimate `Work.MRMT.QC.l2_bound_of_energy`;
* the error term is `O(1/Rₙ)` in `L²` because `h z = O(1/z)` on the support of `∂ψₙ`, so
  `∫_{B(0,ρ)} ‖∂h‖² = 0` for every `ρ`, hence `∂h = 0` a.e. and then `∂̄h = 0` a.e.;
* Weyl's lemma (`Work.MRMT.Weyl.differentiable_of_isDbarDeriv`) makes `h` entire, and
  `h = O(1/z)` plus Liouville's theorem force `h = 0`.
-/
import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.QC.CompHolo.Basic
import Submission.Work.MRMT.Wirtinger.dz_comp
import Submission.Work.MRMT.Wirtinger.dzbar_comp
import Submission.Work.MRMT.Weyl.Defs
import Submission.Work.MRMT.Weyl.differentiable_of_isDbarDeriv
import Submission.Work.MRMT.Weyl.isDzDeriv_moll_gen
import Submission.Work.MRMT.Weyl.isDbarDeriv_moll_gen
import Submission.Work.MRMT.QC.isDzDeriv_mul_and_isDbarDeriv_mul
import Submission.Work.MRMT.Beltrami.energy_identity
import Submission.Work.MRMT.QC.l2_bound_of_energy

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

set_option maxHeartbeats 4000000

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal Convolution

namespace Work.MRMT.QC

/-! ## Decay at infinity encoded by the principal normalisation -/

/-- The principal normalisation `f z = z + O(1/‖z‖)` is a `1/‖z‖` decay estimate on the
exterior of a large ball. -/
theorem isPrincipalAtInfinity_decay {f : ℂ → ℂ} (h : IsPrincipalAtInfinity f) :
    ∃ C R : ℝ, 0 ≤ C ∧ ∀ z : ℂ, R ≤ ‖z‖ → ‖f z - z‖ ≤ C / ‖z‖ := by
  rw [IsPrincipalAtInfinity] at h
  obtain ⟨c, hc⟩ := Asymptotics.isBigO_iff.mp h
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.mp (Filter.eventually_iff.mp hc)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuousOn_id
  refine ⟨max c 0, max M 0 + 1, le_max_right _ _, fun z hz => ?_⟩
  have hzK : z ∉ K := by
    intro hz'
    have h1 : ‖z‖ ≤ M := by simpa using hM z hz'
    have h2 : M ≤ max M 0 := le_max_left M 0
    linarith
  have hb : ‖z * (f z - z)‖ ≤ c * ‖(1 : ℂ)‖ := hKs hzK
  rw [norm_mul, norm_one, mul_one] at hb
  have hzpos : 0 < ‖z‖ := by
    have h2 : M ≤ max M 0 := le_max_left M 0
    have h3 : (0 : ℝ) ≤ max M 0 := le_max_right M 0
    linarith
  have h3 : ‖f z - z‖ ≤ c / ‖z‖ := by
    rw [le_div_iff₀ hzpos]
    linarith
  have h4 : c / ‖z‖ ≤ max c 0 / ‖z‖ :=
    div_le_div_of_nonneg_right (le_max_left c 0) hzpos.le
  linarith

/-! ## Linearity of the weak Wirtinger derivatives -/

/-- The weak (distributional) `∂`-derivatives form a linear relation: the difference of two
pairs is a pair. -/
theorem IsDzDeriv.sub {f₁ f₂ g₁ g₂ : ℂ → ℂ} (h₁ : IsDzDeriv f₁ g₁) (h₂ : IsDzDeriv f₂ g₂) :
    IsDzDeriv (f₁ - f₂) (g₁ - g₂) := by
  obtain ⟨hf₁, hg₁, hm₁⟩ := h₁
  obtain ⟨hf₂, hg₂, hm₂⟩ := h₂
  refine ⟨hf₁.sub hf₂, hg₁.sub hg₂, fun φ => ?_⟩
  obtain ⟨i₁, j₁, e₁⟩ := hm₁ φ
  obtain ⟨i₂, j₂, e₂⟩ := hm₂ φ
  have hi : Integrable (fun z => (f₁ z - f₂ z) * dz (φ : ℂ → ℂ) z) :=
    (i₁.sub i₂).congr (Eventually.of_forall fun z => by
      simp only [Pi.sub_apply]; ring)
  have hj : Integrable (fun z => (g₁ z - g₂ z) * (φ : ℂ → ℂ) z) :=
    (j₁.sub j₂).congr (Eventually.of_forall fun z => by
      simp only [Pi.sub_apply]; ring)
  refine ⟨hi, hj, ?_⟩
  have hL : ∫ z, (f₁ z - f₂ z) * dz (φ : ℂ → ℂ) z
      = (∫ z, f₁ z * dz (φ : ℂ → ℂ) z) - ∫ z, f₂ z * dz (φ : ℂ → ℂ) z := by
    rw [← integral_sub i₁ i₂]
    exact integral_congr_ae (Eventually.of_forall fun z => by ring)
  have hR : ∫ z, (g₁ z - g₂ z) * (φ : ℂ → ℂ) z
      = (∫ z, g₁ z * (φ : ℂ → ℂ) z) - ∫ z, g₂ z * (φ : ℂ → ℂ) z := by
    rw [← integral_sub j₁ j₂]
    exact integral_congr_ae (Eventually.of_forall fun z => by ring)
  simp only [Pi.sub_apply]
  rw [hL, hR, e₁, e₂]
  ring

/-- The weak (distributional) `∂̄`-derivatives form a linear relation. -/
theorem IsDbarDeriv.sub {f₁ f₂ g₁ g₂ : ℂ → ℂ} (h₁ : IsDbarDeriv f₁ g₁) (h₂ : IsDbarDeriv f₂ g₂) :
    IsDbarDeriv (f₁ - f₂) (g₁ - g₂) := by
  obtain ⟨hf₁, hg₁, hm₁⟩ := h₁
  obtain ⟨hf₂, hg₂, hm₂⟩ := h₂
  refine ⟨hf₁.sub hf₂, hg₁.sub hg₂, fun φ => ?_⟩
  obtain ⟨i₁, j₁, e₁⟩ := hm₁ φ
  obtain ⟨i₂, j₂, e₂⟩ := hm₂ φ
  have hi : Integrable (fun z => (f₁ z - f₂ z) * dzbar (φ : ℂ → ℂ) z) :=
    (i₁.sub i₂).congr (Eventually.of_forall fun z => by
      simp only [Pi.sub_apply]; ring)
  have hj : Integrable (fun z => (g₁ z - g₂ z) * (φ : ℂ → ℂ) z) :=
    (j₁.sub j₂).congr (Eventually.of_forall fun z => by
      simp only [Pi.sub_apply]; ring)
  refine ⟨hi, hj, ?_⟩
  have hL : ∫ z, (f₁ z - f₂ z) * dzbar (φ : ℂ → ℂ) z
      = (∫ z, f₁ z * dzbar (φ : ℂ → ℂ) z) - ∫ z, f₂ z * dzbar (φ : ℂ → ℂ) z := by
    rw [← integral_sub i₁ i₂]
    exact integral_congr_ae (Eventually.of_forall fun z => by ring)
  have hR : ∫ z, (g₁ z - g₂ z) * (φ : ℂ → ℂ) z
      = (∫ z, g₁ z * (φ : ℂ → ℂ) z) - ∫ z, g₂ z * (φ : ℂ → ℂ) z := by
    rw [← integral_sub j₁ j₂]
    exact integral_congr_ae (Eventually.of_forall fun z => by ring)
  simp only [Pi.sub_apply]
  rw [hL, hR, e₁, e₂]
  ring

/-- Weak derivatives on `Set.univ` are global weak derivatives. -/
theorem isDzDeriv_of_isDzDerivOn_univ {f g : ℂ → ℂ} (h : IsDzDerivOn f g Set.univ) :
    IsDzDeriv f g :=
  ⟨MeasureTheory.locallyIntegrableOn_univ.mp h.1, MeasureTheory.locallyIntegrableOn_univ.mp h.2.1,
    fun φ => h.2.2 φ (Set.subset_univ _)⟩

/-- Weak `∂̄`-derivatives on `Set.univ` are global weak `∂̄`-derivatives. -/
theorem isDbarDeriv_of_isDbarDerivOn_univ {f g : ℂ → ℂ} (h : IsDbarDerivOn f g Set.univ) :
    IsDbarDeriv f g :=
  ⟨MeasureTheory.locallyIntegrableOn_univ.mp h.1, MeasureTheory.locallyIntegrableOn_univ.mp h.2.1,
    fun φ => h.2.2 φ (Set.subset_univ _)⟩

/-- `MemL2Loc` is closed under differences, by `‖f - g‖² ≤ 2‖f‖² + 2‖g‖²`. -/
theorem MemL2LocOn.sub {f g : ℂ → ℂ} {U : Set ℂ} (hf : MemL2LocOn f U) (hg : MemL2LocOn g U)
    (hmf : AEStronglyMeasurable f (volume.restrict U))
    (hmg : AEStronglyMeasurable g (volume.restrict U)) :
    MemL2LocOn (f - g) U := by
  intro K hK
  have h1 : Integrable (fun z => ‖f z‖ ^ 2) (volume.restrict (K ∩ U)) := hf K hK
  have h2 : Integrable (fun z => ‖g z‖ ^ 2) (volume.restrict (K ∩ U)) := hg K hK
  have hle : (volume.restrict (K ∩ U)) ≤ (volume.restrict U) :=
    Measure.restrict_mono Set.inter_subset_right le_rfl
  have hm : AEStronglyMeasurable (fun z => ‖(f - g) z‖ ^ 2) (volume.restrict (K ∩ U)) :=
    (((hmf.mono_measure hle).sub (hmg.mono_measure hle)).norm).pow 2
  have hbound : Integrable (fun z => 2 * ‖f z‖ ^ 2 + 2 * ‖g z‖ ^ 2) (volume.restrict (K ∩ U)) :=
    (h1.const_mul 2).add (h2.const_mul 2)
  refine Integrable.mono' hbound hm ?_
  filter_upwards with z
  rw [Real.norm_of_nonneg (by positivity)]
  change ‖f z - g z‖ ^ 2 ≤ 2 * ‖f z‖ ^ 2 + 2 * ‖g z‖ ^ 2
  have h4 : ‖f z - g z‖ ^ 2 ≤ (‖f z‖ + ‖g z‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (f z) (g z)) 2
  have h5 : (‖f z‖ + ‖g z‖) ^ 2 ≤ 2 * ‖f z‖ ^ 2 + 2 * ‖g z‖ ^ 2 := by
    nlinarith [sq_nonneg (‖f z‖ - ‖g z‖)]
  linarith

/-! ## Uniqueness of weak `∂`-derivatives -/

/-- The weak (distributional) `∂`-derivative is unique almost everywhere; the `∂`-analogue of
`Work.MRMT.Sobolev.is_dbar_deriv_unique`. -/
theorem is_dz_deriv_unique {f g g' : ℂ → ℂ} (h : IsDzDeriv f g) (h' : IsDzDeriv f g') :
    ∀ᵐ z ∂(volume : Measure ℂ), g z = g' z := by
  refine ae_eq_of_integral_contDiff_smul_eq h.2.1 h'.2.1 ?_
  intro ψ hψ hψc
  let φ : 𝓓(⊤, ℂ) :=
    ⟨fun z => Complex.ofReal (ψ z),
      (ContinuousLinearMap.contDiff (Complex.ofRealCLM)).comp hψ,
      hψc.mono (fun z hz => by
        rw [Function.mem_support] at hz ⊢
        exact fun h => hz (by rw [h]; simp)),
      by intro z _; trivial⟩
  have hφ : ∀ z, (φ : ℂ → ℂ) z = Complex.ofReal (ψ z) := fun _ => rfl
  have key : ∫ z, g z * (φ : ℂ → ℂ) z = ∫ z, g' z * (φ : ℂ → ℂ) z := by
    have h1 : ∫ z, f z * dz (φ : ℂ → ℂ) z = - ∫ z, g z * (φ : ℂ → ℂ) z := (h.2.2 φ).2.2
    have h2 : ∫ z, f z * dz (φ : ℂ → ℂ) z = - ∫ z, g' z * (φ : ℂ → ℂ) z := (h'.2.2 φ).2.2
    have h3 : - ∫ z, g z * (φ : ℂ → ℂ) z = - ∫ z, g' z * (φ : ℂ → ℂ) z := h1.symm.trans h2
    simpa using h3
  have hfun : ∀ z, ψ z • g z = g z * (φ : ℂ → ℂ) z := by
    intro z
    rw [hφ z, RCLike.real_smul_eq_coe_mul]
    exact mul_comm _ _
  have hfun' : ∀ z, ψ z • g' z = g' z * (φ : ℂ → ℂ) z := by
    intro z
    rw [hφ z, RCLike.real_smul_eq_coe_mul]
    exact mul_comm _ _
  calc ∫ z, ψ z • g z = ∫ z, g z * (φ : ℂ → ℂ) z :=
        integral_congr_ae (Eventually.of_forall hfun)
    _ = ∫ z, g' z * (φ : ℂ → ℂ) z := key
    _ = ∫ z, ψ z • g' z := (integral_congr_ae (Eventually.of_forall hfun')).symm

/-! ## A weak `∂̄`-derivative vanishing a.e. may be replaced by `0` -/

theorem isDbarDeriv_zero_of_ae_eq_zero {G h : ℂ → ℂ} (hweak : IsDbarDeriv G h)
    (hae : h =ᵐ[(volume : Measure ℂ)] fun _ => 0) : IsDbarDeriv G (fun _ => 0) := by
  obtain ⟨hG, _hh, hm⟩ := hweak
  refine ⟨hG, MeasureTheory.locallyIntegrable_zero (μ := volume), fun φ => ?_⟩
  obtain ⟨i, _j, e⟩ := hm φ
  have hz : (fun z => h z * (φ : ℂ → ℂ) z) =ᵐ[(volume : Measure ℂ)] fun _ => 0 := by
    filter_upwards [hae] with z hz
    simp [hz]
  have hz0 : (∫ z, h z * (φ : ℂ → ℂ) z) = 0 := by
    rw [integral_congr_ae hz]
    simp
  exact ⟨i, by simp, by rw [e, hz0]; simp⟩

/-! ## Entire functions with `O(1/‖z‖)` decay vanish -/

/-- An entire function with `h z = O(1/‖z‖)` at infinity is identically zero (Liouville). -/
theorem eq_zero_of_differentiable_of_decay {h : ℂ → ℂ} (hd : Differentiable ℂ h)
    (hdec : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖h z‖ ≤ C / ‖z‖) : h = fun _ => 0 := by
  obtain ⟨C, R, hCR⟩ := hdec
  have htend : Tendsto h (cocompact ℂ) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [Filter.eventually_iff, Filter.mem_cocompact]
    refine ⟨Metric.closedBall 0 (max (max R 1) (C / ε) + 1), isCompact_closedBall _ _, ?_⟩
    intro z hz
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, sub_zero, not_le] at hz
    have hz' : max (max R 1) (C / ε) < ‖z‖ := lt_trans (lt_add_one _) hz
    have hR : R ≤ ‖z‖ := (le_max_left R 1).trans ((le_max_left (max R 1) _).trans hz'.le)
    have h1 : (1 : ℝ) ≤ ‖z‖ := (le_max_right R 1).trans ((le_max_left (max R 1) _).trans hz'.le)
    have hC : C / ε < ‖z‖ := lt_of_le_of_lt (le_max_right (max R 1) _) hz'
    have hzpos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one h1
    have hbdd : C / ‖z‖ < ε := by
      rcases le_or_gt 0 C with hC0 | hC0
      · rw [div_lt_iff₀ hε] at hC
        rw [div_lt_iff₀ hzpos]
        linarith [mul_comm ε ‖z‖]
      · have : C / ‖z‖ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hC0.le (norm_nonneg z)
        linarith
    simp only [dist_zero_right]
    exact lt_of_le_of_lt (hCR z hR) hbdd
  exact hd.eq_const_of_tendsto_cocompact htend


/-! ## The cut-off family `psiC` -/

/-- The standard bump function on `ℂ`, `1` on `closedBall 0 1` and supported in `closedBall 0 2`. -/
def cBump : ContDiffBump (0 : ℂ) := ⟨1, 2, zero_lt_one, one_lt_two⟩

/-- The complex-valued version of `cBump`. -/
def cChi : ℂ → ℂ := fun z => (cBump z : ℂ)

/-- The radius `Rₙ = n + 1`. -/
def cRad (n : ℕ) : ℝ := (n : ℝ) + 1

/-- The scale factor `Rₙ⁻¹`, as a complex number. -/
def cScl (n : ℕ) : ℂ := ((cRad n)⁻¹ : ℝ)

/-- The cut-off `ψₙ(z) = χ(z/Rₙ)`. -/
def cPsi (n : ℕ) : ℂ → ℂ := fun z => cChi (cScl n * z)

theorem cRad_pos (n : ℕ) : 0 < cRad n := by unfold cRad; positivity

theorem cRad_one_le (n : ℕ) : 1 ≤ cRad n := by
  unfold cRad
  linarith [Nat.cast_nonneg (α := ℝ) n]

theorem norm_cScl (n : ℕ) : ‖cScl n‖ = (cRad n)⁻¹ := by
  rw [cScl, Complex.ofReal_inv, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (le_of_lt (cRad_pos n))]

theorem cScl_ne_zero (n : ℕ) : cScl n ≠ 0 := by
  rw [← norm_ne_zero_iff, norm_cScl]
  exact inv_ne_zero (ne_of_gt (cRad_pos n))

theorem star_cScl (n : ℕ) : star (cScl n) = cScl n := by
  rw [cScl, Complex.star_def, Complex.conj_ofReal]

theorem cChi_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) cChi := by
  unfold cChi
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cBump : ℂ → ℝ) :=
    ContDiffBump.contDiff cBump
  have := (Complex.ofRealCLM.contDiff).comp hcd
  simpa [Function.comp_def] using this

theorem cChi_cs : HasCompactSupport cChi := by
  unfold cChi
  have := (ContDiffBump.hasCompactSupport cBump).comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  simpa [Function.comp_def] using this

theorem cPsi_contDiff (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cPsi n) := by
  unfold cPsi
  exact cChi_contDiff.comp (ContDiff.const_smul (cScl n) contDiff_id)

theorem cPsi_cs (n : ℕ) : HasCompactSupport (cPsi n) := by
  unfold cPsi
  exact cChi_cs.comp_smul (c := cScl n) (cScl_ne_zero n)

theorem cChi_one {w : ℂ} (h : ‖w‖ ≤ 1) : cChi w = 1 := by
  have hmem : w ∈ Metric.closedBall (0 : ℂ) cBump.rIn := by
    rw [Metric.mem_closedBall, dist_zero_right]; simpa [cBump] using h
  unfold cChi
  rw [ContDiffBump.one_of_mem_closedBall (f := cBump) hmem]
  norm_num

theorem cChi_zero {w : ℂ} (h : 2 ≤ ‖w‖) : cChi w = 0 := by
  have hmem : cBump.rOut ≤ dist w (0 : ℂ) := by
    rw [dist_zero_right]; simpa [cBump] using h
  unfold cChi
  rw [ContDiffBump.zero_of_le_dist (f := cBump) hmem]
  norm_num

theorem cPsi_one (n : ℕ) {z : ℂ} (h : ‖z‖ ≤ cRad n) : cPsi n z = 1 := by
  unfold cPsi
  apply cChi_one
  rw [norm_mul, norm_cScl, inv_mul_le_one₀ (cRad_pos n)]
  exact h

theorem cPsi_zero (n : ℕ) {z : ℂ} (h : 2 * cRad n ≤ ‖z‖) : cPsi n z = 0 := by
  unfold cPsi
  apply cChi_zero
  rw [norm_mul, norm_cScl, inv_mul_eq_div, le_div_iff₀ (cRad_pos n)]
  linarith

theorem cChi_eventuallyEq_one {w : ℂ} (h : ‖w‖ < 1) : cChi =ᶠ[𝓝 w] (fun _ => (1 : ℂ)) := by
  have hmem : Metric.ball (0 : ℂ) (1 : ℝ) ∈ 𝓝 w :=
    Metric.isOpen_ball.mem_nhds (by simpa [Metric.mem_ball, dist_eq_norm] using h)
  refine mem_of_superset hmem ?_
  intro x hx
  exact cChi_one (le_of_lt (by simpa [Metric.mem_ball, dist_eq_norm] using hx))

theorem cChi_dz_zero {w : ℂ} (h : ‖w‖ < 1) : dz cChi w = 0 := by
  have hf : fderiv ℝ cChi w = 0 := by
    rw [(cChi_eventuallyEq_one h).fderiv_eq]; simp
  simp only [dz, hf]; simp

theorem cChi_dzbar_zero {w : ℂ} (h : ‖w‖ < 1) : dzbar cChi w = 0 := by
  have hf : fderiv ℝ cChi w = 0 := by
    rw [(cChi_eventuallyEq_one h).fderiv_eq]; simp
  simp only [dzbar, hf]; simp

theorem cChi_eventuallyEq_zero {w : ℂ} (h : 2 < ‖w‖) : cChi =ᶠ[𝓝 w] (fun _ => (0 : ℂ)) := by
  have hmem : {x : ℂ | 2 < ‖x‖} ∈ 𝓝 w :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds h
  refine mem_of_superset hmem ?_
  intro x hx
  exact cChi_zero (le_of_lt hx)

theorem cChi_dz_zero_of_gt {w : ℂ} (h : 2 < ‖w‖) : dz cChi w = 0 := by
  have hf : fderiv ℝ cChi w = 0 := by
    rw [(cChi_eventuallyEq_zero h).fderiv_eq]; simp
  simp only [dz, hf]; simp

theorem cChi_dzbar_zero_of_gt {w : ℂ} (h : 2 < ‖w‖) : dzbar cChi w = 0 := by
  have hf : fderiv ℝ cChi w = 0 := by
    rw [(cChi_eventuallyEq_zero h).fderiv_eq]; simp
  simp only [dzbar, hf]; simp

theorem cPsi_eventuallyEq_one (n : ℕ) {z : ℂ} (h : ‖z‖ < cRad n) :
    cPsi n =ᶠ[𝓝 z] (fun _ => (1 : ℂ)) := by
  have hmem : {w : ℂ | ‖w‖ < cRad n} ∈ 𝓝 z :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds h
  refine mem_of_superset hmem ?_
  intro w hw
  exact cPsi_one n (le_of_lt hw)

theorem cPsi_dz_zero (n : ℕ) {z : ℂ} (h : ‖z‖ < cRad n) : dz (cPsi n) z = 0 := by
  have hf : fderiv ℝ (cPsi n) z = 0 := by
    rw [(cPsi_eventuallyEq_one n h).fderiv_eq]; simp
  simp only [dz, hf]; simp

theorem cPsi_dzbar_zero (n : ℕ) {z : ℂ} (h : ‖z‖ < cRad n) : dzbar (cPsi n) z = 0 := by
  have hf : fderiv ℝ (cPsi n) z = 0 := by
    rw [(cPsi_eventuallyEq_one n h).fderiv_eq]; simp
  simp only [dzbar, hf]; simp

theorem dz_const_mul (c : ℂ) (z : ℂ) : dz (fun w : ℂ => c * w) z = c := by
  rw [dz_holo
    (by simpa using (differentiableAt_id (𝕜 := ℂ) (x := z)).const_mul c)]
  simpa using ((hasDerivAt_id z).const_mul c).deriv

theorem dzbar_const_mul (c : ℂ) (z : ℂ) : dzbar (fun w : ℂ => c * w) z = 0 :=
  dzbar_holo
    (by simpa using (differentiableAt_id (𝕜 := ℂ) (x := z)).const_mul c)

theorem cPsi_dz (n : ℕ) (z : ℂ) : dz (cPsi n) z = cScl n * dz cChi (cScl n * z) := by
  have h1 : cPsi n = cChi ∘ (fun w : ℂ => cScl n * w) := rfl
  have hd : DifferentiableAt ℝ (fun w : ℂ => cScl n * w) z :=
    (ContinuousLinearMap.mul ℝ ℂ (cScl n)).differentiableAt
  rw [h1, Wirtinger.dz_comp ((cChi_contDiff.differentiable (by simp)).differentiableAt) hd]
  rw [dz_const_mul, dzbar_const_mul]
  simp [mul_comm]

theorem cPsi_dzbar (n : ℕ) (z : ℂ) : dzbar (cPsi n) z = cScl n * dzbar cChi (cScl n * z) := by
  have h1 : cPsi n = cChi ∘ (fun w : ℂ => cScl n * w) := rfl
  have hd : DifferentiableAt ℝ (fun w : ℂ => cScl n * w) z :=
    (ContinuousLinearMap.mul ℝ ℂ (cScl n)).differentiableAt
  rw [h1, Wirtinger.dzbar_comp ((cChi_contDiff.differentiable (by simp)).differentiableAt) hd]
  rw [dz_const_mul, dzbar_const_mul, star_cScl]
  simp [mul_comm]

theorem cPsi_dz_zero_of_gt (n : ℕ) {z : ℂ} (h : 2 * cRad n < ‖z‖) : dz (cPsi n) z = 0 := by
  rw [cPsi_dz, cChi_dz_zero_of_gt]
  · ring
  · rw [norm_mul, norm_cScl, inv_mul_eq_div, lt_div_iff₀ (cRad_pos n)]
    linarith

theorem cPsi_dzbar_zero_of_gt (n : ℕ) {z : ℂ} (h : 2 * cRad n < ‖z‖) :
    dzbar (cPsi n) z = 0 := by
  rw [cPsi_dzbar, cChi_dzbar_zero_of_gt]
  · ring
  · rw [norm_mul, norm_cScl, inv_mul_eq_div, lt_div_iff₀ (cRad_pos n)]
    linarith

theorem cChi_deriv_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℂ, ‖dz cChi w‖ ≤ M ∧ ‖dzbar cChi w‖ ≤ M := by
  have hc1 : Continuous (dz cChi) := continuous_dz_of_contDiff (by simp) cChi_contDiff
  have hc2 : Continuous (dzbar cChi) := continuous_dzbar_of_contDiff (by simp) cChi_contDiff
  obtain ⟨M1, hM1⟩ :=
    (isCompact_closedBall (0 : ℂ) (2 : ℝ)).exists_bound_of_continuousOn hc1.continuousOn
  obtain ⟨M2, hM2⟩ :=
    (isCompact_closedBall (0 : ℂ) (2 : ℝ)).exists_bound_of_continuousOn hc2.continuousOn
  refine ⟨max (max M1 M2) 0, le_max_right (max M1 M2) (0 : ℝ), fun w => ⟨?_, ?_⟩⟩
  · rcases le_or_gt ‖w‖ 2 with hw | hw
    · have hw' : w ∈ Metric.closedBall (0 : ℂ) 2 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hw
      exact le_trans (hM1 w hw')
        (le_trans (le_max_left M1 M2) (le_max_left (max M1 M2) 0))
    · rw [cChi_dz_zero_of_gt hw, norm_zero]
      exact le_max_right (max M1 M2) (0 : ℝ)
  · rcases le_or_gt ‖w‖ 2 with hw | hw
    · have hw' : w ∈ Metric.closedBall (0 : ℂ) 2 := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hw
      exact le_trans (hM2 w hw')
        (le_trans (le_max_right M1 M2) (le_max_left (max M1 M2) 0))
    · rw [cChi_dzbar_zero_of_gt hw, norm_zero]
      exact le_max_right (max M1 M2) (0 : ℝ)

theorem cPsi_deriv_bound {M : ℝ} (hM1 : ∀ w : ℂ, ‖dz cChi w‖ ≤ M)
    (hM2 : ∀ w : ℂ, ‖dzbar cChi w‖ ≤ M) (n : ℕ) (z : ℂ) :
    ‖dz (cPsi n) z‖ ≤ M / cRad n ∧ ‖dzbar (cPsi n) z‖ ≤ M / cRad n := by
  constructor
  · rw [cPsi_dz, norm_mul, norm_cScl]
    calc (cRad n)⁻¹ * ‖dz cChi (cScl n * z)‖ ≤ (cRad n)⁻¹ * M :=
          mul_le_mul_of_nonneg_left (hM1 _) (le_of_lt (inv_pos.mpr (cRad_pos n)))
      _ = M / cRad n := by ring
  · rw [cPsi_dzbar, norm_mul, norm_cScl]
    calc (cRad n)⁻¹ * ‖dzbar cChi (cScl n * z)‖ ≤ (cRad n)⁻¹ * M :=
          mul_le_mul_of_nonneg_left (hM2 _) (le_of_lt (inv_pos.mpr (cRad_pos n)))
      _ = M / cRad n := by ring



/-! ## The mollifying kernels and the `L²` contraction estimate -/

/-- The mollifying kernels `ρₙ`, normalised bump functions whose outer radii tend to `0`. -/
def mollRad (n : ℕ) : ℂ → ℝ := (Weyl.bump n).normed volume

theorem mollRad_contDiff (n : ℕ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mollRad n) :=
  (Weyl.bump n).contDiff_normed

theorem mollRad_continuous (n : ℕ) : Continuous (mollRad n) := (mollRad_contDiff n).continuous

theorem mollRad_cs (n : ℕ) : HasCompactSupport (mollRad n) :=
  (Weyl.bump n).hasCompactSupport_normed

theorem mollRad_nonneg (n : ℕ) (z : ℂ) : 0 ≤ mollRad n z := (Weyl.bump n).nonneg_normed z

theorem mollRad_integral (n : ℕ) : ∫ z, mollRad n z = 1 := (Weyl.bump n).integral_normed

/-- **The pointwise Cauchy–Schwarz estimate for mollification.** For a nonnegative kernel `ρ`
of total mass `1` and `f ∈ L²`,
`‖ρ ⋆ f (z)‖² ≤ ∫ t, ρ (z - t) ‖f t‖² dt`. -/
theorem sq_norm_moll_le {f : ℂ → ℂ} {ρ : ℂ → ℝ} (hρ0 : ∀ z, 0 ≤ ρ z)
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρ1 : ∫ z, ρ z = 1)
    (hf : MemLp f 2 (volume : Measure ℂ)) (z : ℂ) :
    ‖Weyl.moll ρ f z‖ ^ 2 ≤ ∫ t, ρ (z - t) * ‖f t‖ ^ 2 := by
  have hfli : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  have hf2 : Integrable (fun z => ‖f z‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hf2li : LocallyIntegrable (fun z => ‖f z‖ ^ 2) volume := hf2.locallyIntegrable
  have hρsub_c : Continuous (fun t : ℂ => ρ (z - t)) :=
    hρc.comp (continuous_const.sub continuous_id)
  have hρsub_s : HasCompactSupport (fun t : ℂ => ρ (z - t)) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := (fun t : ℂ => z - t) '' tsupport ρ) ?_ ?_
    · exact hρs.isCompact.image (continuous_const.sub continuous_id)
    · intro t ht
      rw [Function.mem_support] at ht
      exact ⟨z - t, subset_tsupport ρ (fun hz => ht (by simp [hz])), by simp⟩
  have hstep1 : ‖Weyl.moll ρ f z‖ ≤ ∫ t, ρ (z - t) * ‖f t‖ := by
    have hint : Integrable (fun t : ℂ => (ρ t : ℂ) * f (z - t)) volume := by
      have h := (hρs.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
        hρc hfli) z
      exact h.congr (Eventually.of_forall fun t => by
        simp [ContinuousLinearMap.lsmul_apply])
    calc ‖Weyl.moll ρ f z‖ = ‖∫ t, (ρ t : ℂ) * f (z - t)‖ := by rw [Weyl.moll_apply]
      _ ≤ ∫ t, ‖(ρ t : ℂ) * f (z - t)‖ := norm_integral_le_integral_norm _
      _ = ∫ t, ρ t * ‖f (z - t)‖ := by
            refine integral_congr_ae (Eventually.of_forall fun t => ?_)
            simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hρ0 t)]
      _ = ∫ t, ρ (z - t) * ‖f t‖ := by
            have h := integral_sub_left_eq_self (fun u : ℂ => ρ u * ‖f (z - u)‖) volume z
            simpa using h.symm
  have hstep2 : (∫ t, ρ (z - t) * ‖f t‖) ^ 2 ≤ ∫ t, ρ (z - t) * ‖f t‖ ^ 2 := by
    have ha0 : 0 ≤ᵐ[volume] (fun t : ℂ => Real.sqrt (ρ (z - t))) :=
      Eventually.of_forall fun t => Real.sqrt_nonneg _
    have hb0 : 0 ≤ᵐ[volume] (fun t : ℂ => Real.sqrt (ρ (z - t)) * ‖f t‖) :=
      Eventually.of_forall fun t => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    have ham : MemLp (fun t : ℂ => Real.sqrt (ρ (z - t))) 2 volume := by
      refine (memLp_two_iff_integrable_sq
        (Real.continuous_sqrt.comp hρsub_c).aestronglyMeasurable).mpr ?_
      change Integrable (fun t : ℂ => Real.sqrt (ρ (z - t)) ^ 2) volume
      have hfun : (fun t : ℂ => Real.sqrt (ρ (z - t)) ^ 2) = fun t : ℂ => ρ (z - t) := by
        funext t; exact Real.sq_sqrt (hρ0 (z - t))
      rw [hfun]
      exact hρsub_c.integrable_of_hasCompactSupport hρsub_s
    have hbm : MemLp (fun t : ℂ => Real.sqrt (ρ (z - t)) * ‖f t‖) 2 volume := by
      refine (memLp_two_iff_integrable_sq
        ((Real.continuous_sqrt.comp hρsub_c).aestronglyMeasurable.mul
          hf.aestronglyMeasurable.norm)).mpr ?_
      change Integrable (fun t : ℂ => (Real.sqrt (ρ (z - t)) * ‖f t‖) ^ 2) volume
      have hfun : (fun t : ℂ => (Real.sqrt (ρ (z - t)) * ‖f t‖) ^ 2)
          = fun t : ℂ => ρ (z - t) * ‖f t‖ ^ 2 := by
        funext t; rw [mul_pow, Real.sq_sqrt (hρ0 (z - t))]
      rw [hfun]
      have h := LocallyIntegrable.integrable_smul_right_of_hasCompactSupport
        hf2li hρsub_c hρsub_s
      exact h.congr (Eventually.of_forall fun t => by
        show ‖f t‖ ^ 2 • ρ (z - t) = ρ (z - t) * ‖f t‖ ^ 2
        rw [smul_eq_mul, mul_comm])
    have hpq : (2 : ℝ).HolderConjugate 2 :=
      Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) hpq ha0 hb0
      (by simpa using ham) (by simpa using hbm)
    have h1 : ∫ t, Real.sqrt (ρ (z - t)) * (Real.sqrt (ρ (z - t)) * ‖f t‖)
        = ∫ t, ρ (z - t) * ‖f t‖ := by
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      show Real.sqrt (ρ (z - t)) * (Real.sqrt (ρ (z - t)) * ‖f t‖) = ρ (z - t) * ‖f t‖
      rw [← mul_assoc, Real.mul_self_sqrt (hρ0 (z - t))]
    have h2 : ∫ t, Real.sqrt (ρ (z - t)) ^ (2 : ℝ) = 1 := by
      have hfun : (fun t : ℂ => Real.sqrt (ρ (z - t)) ^ (2 : ℝ)) = fun t : ℂ => ρ (z - t) := by
        funext t; rw [Real.rpow_two]; exact Real.sq_sqrt (hρ0 (z - t))
      rw [hfun, integral_sub_left_eq_self ρ volume z, hρ1]
    have h3 : ∫ t, (Real.sqrt (ρ (z - t)) * ‖f t‖) ^ (2 : ℝ)
        = ∫ t, ρ (z - t) * ‖f t‖ ^ 2 := by
      have hfun : (fun t : ℂ => (Real.sqrt (ρ (z - t)) * ‖f t‖) ^ (2 : ℝ))
          = fun t : ℂ => ρ (z - t) * ‖f t‖ ^ 2 := by
        funext t
        rw [Real.mul_rpow (Real.sqrt_nonneg _) (norm_nonneg _), Real.rpow_two, Real.rpow_two,
          Real.sq_sqrt (hρ0 (z - t))]
      rw [hfun]
    have h4 : 0 ≤ ∫ t, ρ (z - t) * ‖f t‖ :=
      integral_nonneg fun t => mul_nonneg (hρ0 _) (norm_nonneg _)
    have h5 : 0 ≤ ∫ t, ρ (z - t) * ‖f t‖ ^ 2 :=
      integral_nonneg fun t => mul_nonneg (hρ0 _) (by positivity)
    have hCS' : (∫ t, ρ (z - t) * ‖f t‖)
        ≤ (∫ t, ρ (z - t) * ‖f t‖ ^ 2) ^ (1 / 2 : ℝ) :=
      calc ∫ t, ρ (z - t) * ‖f t‖
          = ∫ t, Real.sqrt (ρ (z - t)) * (Real.sqrt (ρ (z - t)) * ‖f t‖) := h1.symm
        _ ≤ (∫ t, Real.sqrt (ρ (z - t)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
              * (∫ t, (Real.sqrt (ρ (z - t)) * ‖f t‖) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := hCS
        _ = 1 ^ (1 / 2 : ℝ) * (∫ t, ρ (z - t) * ‖f t‖ ^ 2) ^ (1 / 2 : ℝ) := by rw [h2, h3]
        _ = (∫ t, ρ (z - t) * ‖f t‖ ^ 2) ^ (1 / 2 : ℝ) := by simp
    have h6 : ((∫ t, ρ (z - t) * ‖f t‖ ^ 2) ^ (1 / 2 : ℝ)) ^ 2
        = ∫ t, ρ (z - t) * ‖f t‖ ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul h5]
      norm_num
    calc (∫ t, ρ (z - t) * ‖f t‖) ^ 2
        ≤ ((∫ t, ρ (z - t) * ‖f t‖ ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := pow_le_pow_left₀ h4 hCS' 2
      _ = ∫ t, ρ (z - t) * ‖f t‖ ^ 2 := h6
  exact le_trans (pow_le_pow_left₀ (norm_nonneg _) hstep1 2) hstep2

/-- The convolution `z ↦ ∫ t, ρ (z - t) ‖f t‖² dt` is integrable when `ρ` and `‖f‖²` are. -/
theorem integrable_sub_conv {f : ℂ → ℂ} {ρ : ℂ → ℝ} (hf : Integrable (fun z => ‖f z‖ ^ 2) volume)
    (hρ : Integrable ρ volume) :
    Integrable (fun z : ℂ => ∫ t, ρ (z - t) * ‖f t‖ ^ 2) volume := by
  have h := hf.integrable_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hρ
  refine h.congr (Eventually.of_forall fun z => ?_)
  rw [MeasureTheory.convolution_def]
  exact integral_congr_ae (Eventually.of_forall fun t => by
    simp [ContinuousLinearMap.lsmul_apply, mul_comm])

/-- The mollification of an `L²` function is again in `L²`. -/
theorem memLp_moll {f : ℂ → ℂ} {ρ : ℂ → ℝ} (hρ0 : ∀ z, 0 ≤ ρ z) (hρc : Continuous ρ)
    (hρs : HasCompactSupport ρ) (hρ1 : ∫ z, ρ z = 1)
    (hf : MemLp f 2 (volume : Measure ℂ)) : MemLp (Weyl.moll ρ f) 2 (volume : Measure ℂ) := by
  have hf2 : Integrable (fun z => ‖f z‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hρint : Integrable ρ volume := hρc.integrable_of_hasCompactSupport hρs
  have hmeas : AEStronglyMeasurable (Weyl.moll ρ f) volume := by
    have h := hρc.aestronglyMeasurable.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ)
      hf.aestronglyMeasurable
    simpa only [Weyl.moll] using h
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  refine Integrable.mono' (integrable_sub_conv hf2 hρint) (hmeas.norm.pow 2) ?_
  filter_upwards with z
  rw [Real.norm_of_nonneg (by positivity)]
  exact sq_norm_moll_le hρ0 hρc hρs hρ1 hf z

/-- **The `L²`-contraction estimate for mollification**, in `lintegral` form. -/
theorem lintegral_ofReal_moll_le {f : ℂ → ℂ} {ρ : ℂ → ℝ} (hρ0 : ∀ z, 0 ≤ ρ z)
    (hρc : Continuous ρ) (hρs : HasCompactSupport ρ) (hρ1 : ∫ z, ρ z = 1)
    (hf : MemLp f 2 (volume : Measure ℂ)) :
    ∫⁻ z, ENNReal.ofReal (‖Weyl.moll ρ f z‖ ^ 2) ≤ ∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) := by
  have hf2 : Integrable (fun z => ‖f z‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have hρint : Integrable ρ volume := hρc.integrable_of_hasCompactSupport hρs
  have hconvint : Integrable (fun z : ℂ => ∫ t, ρ (z - t) * ‖f t‖ ^ 2) volume :=
    integrable_sub_conv hf2 hρint
  have hconvnn : 0 ≤ᵐ[volume] (fun z : ℂ => ∫ t, ρ (z - t) * ‖f t‖ ^ 2) :=
    Eventually.of_forall fun z => integral_nonneg fun t => mul_nonneg (hρ0 _) (by positivity)
  have hfun : (fun z : ℂ => ∫ t, ρ (z - t) * ‖f t‖ ^ 2)
      = fun z : ℂ =>
          ((fun t : ℂ => ‖f t‖ ^ 2) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) z := by
    funext z
    rw [MeasureTheory.convolution_def]
    exact integral_congr_ae (Eventually.of_forall fun t => by
      simp [ContinuousLinearMap.lsmul_apply, mul_comm])
  calc ∫⁻ z, ENNReal.ofReal (‖Weyl.moll ρ f z‖ ^ 2)
      ≤ ∫⁻ z, ENNReal.ofReal (∫ t, ρ (z - t) * ‖f t‖ ^ 2) :=
        lintegral_mono fun z => ENNReal.ofReal_le_ofReal (sq_norm_moll_le hρ0 hρc hρs hρ1 hf z)
    _ = ENNReal.ofReal (∫ z, ∫ t, ρ (z - t) * ‖f t‖ ^ 2) :=
        (ofReal_integral_eq_lintegral_ofReal hconvint hconvnn).symm
    _ = ENNReal.ofReal (∫ z, ‖f z‖ ^ 2) := by
        congr 1
        rw [hfun, integral_convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hf2 hρint]
        simp [ContinuousLinearMap.lsmul_apply, hρ1]
    _ = ∫⁻ z, ENNReal.ofReal (‖f z‖ ^ 2) :=
        ofReal_integral_eq_lintegral_ofReal hf2 (Eventually.of_forall fun z => by positivity)

/-- **The energy identity for compactly supported `W^{1,2}` functions**: if `u` has compact
support and `p`, `q` are its weak Wirtinger derivatives `∂u`, `∂̄u`, both in `L²`, then
`∫ ‖p‖² = ∫ ‖q‖²`. -/
theorem energy_identity_of_w12_compactSupport {u p q : ℂ → ℂ} (hus : HasCompactSupport u)
    (hp : IsDzDeriv u p) (hq : IsDbarDeriv u q)
    (hpm : MemLp p 2 (volume : Measure ℂ)) (hqm : MemLp q 2 (volume : Measure ℂ)) :
    ∫ z, ‖p z‖ ^ 2 = ∫ z, ‖q z‖ ^ 2 := by
  have hp2 : Integrable (fun z => ‖p z‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hpm.aestronglyMeasurable).mp hpm
  have hq2 : Integrable (fun z => ‖q z‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hqm.aestronglyMeasurable).mp hqm
  have hp0 : 0 ≤ ∫ z, ‖p z‖ ^ 2 := integral_nonneg fun z => by positivity
  have hq0 : 0 ≤ ∫ z, ‖q z‖ ^ 2 := integral_nonneg fun z => by positivity
  have hpnn : 0 ≤ᵐ[volume] (fun z : ℂ => ‖p z‖ ^ 2) := Eventually.of_forall fun z => by positivity
  have hqnn : 0 ≤ᵐ[volume] (fun z : ℂ => ‖q z‖ ^ 2) := Eventually.of_forall fun z => by positivity
  have hmollp : ∀ n, MemLp (Weyl.moll (mollRad n) p) 2 (volume : Measure ℂ) := fun n =>
    memLp_moll (mollRad_nonneg n) (mollRad_continuous n) (mollRad_cs n) (mollRad_integral n) hpm
  have hmollq : ∀ n, MemLp (Weyl.moll (mollRad n) q) 2 (volume : Measure ℂ) := fun n =>
    memLp_moll (mollRad_nonneg n) (mollRad_continuous n) (mollRad_cs n) (mollRad_integral n) hqm
  have hintp : ∀ n, Integrable (fun z => ‖Weyl.moll (mollRad n) p z‖ ^ 2) volume := fun n =>
    (memLp_two_iff_integrable_sq_norm (hmollp n).aestronglyMeasurable).mp (hmollp n)
  have hintq : ∀ n, Integrable (fun z => ‖Weyl.moll (mollRad n) q z‖ ^ 2) volume := fun n =>
    (memLp_two_iff_integrable_sq_norm (hmollq n).aestronglyMeasurable).mp (hmollq n)
  have henergy : ∀ n, ∫ z, ‖Weyl.moll (mollRad n) p z‖ ^ 2
      = ∫ z, ‖Weyl.moll (mollRad n) q z‖ ^ 2 := by
    intro n
    have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Weyl.moll (mollRad n) u) :=
      Weyl.contDiff_moll (mollRad_contDiff n) (mollRad_cs n) (hp.1)
    have hcs : HasCompactSupport (Weyl.moll (mollRad n) u) := by
      have h := (mollRad_cs n).convolution (L := ContinuousLinearMap.lsmul ℝ ℝ)
        (μ := (volume : Measure ℂ)) hus
      simpa only [Weyl.moll] using h
    have hen := Beltrami.energy_identity_of_contDiff_two (Weyl.moll (mollRad n) u)
      (hcd.of_le (by norm_num)) hcs
    have e1 : Work.MRMT.dz (Weyl.moll (mollRad n) u) =ᵐ[volume] Weyl.moll (mollRad n) p :=
      EventuallyEq.symm
        (is_dz_deriv_unique (f := Weyl.moll (mollRad n) u) (g := Weyl.moll (mollRad n) p)
          (g' := Work.MRMT.dz (Weyl.moll (mollRad n) u))
          (Weyl.isDzDeriv_moll_gen hp (mollRad_contDiff n) (mollRad_cs n))
          (Weyl.isDzDeriv_dz hcd (by simp)))
    have e2 : Work.MRMT.dzbar (Weyl.moll (mollRad n) u) =ᵐ[volume] Weyl.moll (mollRad n) q :=
      EventuallyEq.symm
        (Sobolev.is_dbar_deriv_unique (f := Weyl.moll (mollRad n) u)
          (g := Weyl.moll (mollRad n) q) (g' := Work.MRMT.dzbar (Weyl.moll (mollRad n) u))
          (Weyl.isDbarDeriv_moll_gen hq (mollRad_contDiff n) (mollRad_cs n))
          (Weyl.isDbarDeriv_dzbar hcd (by simp)))
    have f1 : ∫ z, ‖Weyl.moll (mollRad n) p z‖ ^ 2
        = ∫ z, ‖Work.MRMT.dz (Weyl.moll (mollRad n) u) z‖ ^ 2 :=
      integral_congr_ae (by
        filter_upwards [e1] with z hz
        rw [← hz])
    have f2 : ∫ z, ‖Weyl.moll (mollRad n) q z‖ ^ 2
        = ∫ z, ‖Work.MRMT.dzbar (Weyl.moll (mollRad n) u) z‖ ^ 2 :=
      integral_congr_ae (by
        filter_upwards [e2] with z hz
        rw [← hz])
    rw [f1, f2]
    exact hen
  have hratio : ∀ᶠ i : ℕ in atTop, (Weyl.bump i).rOut ≤ 2 * (Weyl.bump i).rIn := by
    filter_upwards with i
    show 1 / ((i : ℝ) + 1) ≤ 2 * (1 / ((i : ℝ) + 2))
    rw [show (2 : ℝ) * (1 / ((i : ℝ) + 2)) = 2 / ((i : ℝ) + 2) by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hae_p : ∀ᵐ z ∂volume, Tendsto (fun n => Weyl.moll (mollRad n) p z) atTop (𝓝 (p z)) := by
    have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := (volume : Measure ℂ)) (φ := Weyl.bump) Weyl.tendsto_rOut_bump hratio
      (hpm.locallyIntegrable (by norm_num))
    filter_upwards [h] with z hz
    simpa only [Weyl.moll, mollRad] using hz
  have hae_q : ∀ᵐ z ∂volume, Tendsto (fun n => Weyl.moll (mollRad n) q z) atTop (𝓝 (q z)) := by
    have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := (volume : Measure ℂ)) (φ := Weyl.bump) Weyl.tendsto_rOut_bump hratio
      (hqm.locallyIntegrable (by norm_num))
    filter_upwards [h] with z hz
    simpa only [Weyl.moll, mollRad] using hz
  have hmeas_p : ∀ n, AEMeasurable
      (fun z => ENNReal.ofReal (‖Weyl.moll (mollRad n) p z‖ ^ 2)) volume := fun n =>
    (((hmollp n).aestronglyMeasurable).norm.pow 2).aemeasurable.ennreal_ofReal
  have hmeas_q : ∀ n, AEMeasurable
      (fun z => ENNReal.ofReal (‖Weyl.moll (mollRad n) q z‖ ^ 2)) volume := fun n =>
    (((hmollq n).aestronglyMeasurable).norm.pow 2).aemeasurable.ennreal_ofReal
  have hfat_p : ∫⁻ z, ENNReal.ofReal (‖p z‖ ^ 2)
      ≤ liminf (fun n => ∫⁻ z, ENNReal.ofReal (‖Weyl.moll (mollRad n) p z‖ ^ 2)) atTop := by
    have h1 : ∫⁻ z, ENNReal.ofReal (‖p z‖ ^ 2)
        = ∫⁻ z, liminf (fun n => ENNReal.ofReal (‖Weyl.moll (mollRad n) p z‖ ^ 2)) atTop := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae_p] with z hz
      have h2 : Tendsto (fun n => ENNReal.ofReal (‖Weyl.moll (mollRad n) p z‖ ^ 2)) atTop
          (𝓝 (ENNReal.ofReal (‖p z‖ ^ 2))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp (hz.norm.pow 2)
      exact h2.liminf_eq.symm
    rw [h1]
    exact MeasureTheory.lintegral_liminf_le' hmeas_p
  have hfat_q : ∫⁻ z, ENNReal.ofReal (‖q z‖ ^ 2)
      ≤ liminf (fun n => ∫⁻ z, ENNReal.ofReal (‖Weyl.moll (mollRad n) q z‖ ^ 2)) atTop := by
    have h1 : ∫⁻ z, ENNReal.ofReal (‖q z‖ ^ 2)
        = ∫⁻ z, liminf (fun n => ENNReal.ofReal (‖Weyl.moll (mollRad n) q z‖ ^ 2)) atTop := by
      refine lintegral_congr_ae ?_
      filter_upwards [hae_q] with z hz
      have h2 : Tendsto (fun n => ENNReal.ofReal (‖Weyl.moll (mollRad n) q z‖ ^ 2)) atTop
          (𝓝 (ENNReal.ofReal (‖q z‖ ^ 2))) :=
        (ENNReal.continuous_ofReal.tendsto _).comp (hz.norm.pow 2)
      exact h2.liminf_eq.symm
    rw [h1]
    exact MeasureTheory.lintegral_liminf_le' hmeas_q
  have hle_p : liminf (fun n => ∫⁻ z, ENNReal.ofReal (‖Weyl.moll (mollRad n) p z‖ ^ 2)) atTop
      ≤ ∫⁻ z, ENNReal.ofReal (‖p z‖ ^ 2) := by
    refine liminf_le_of_frequently_le' ?_
    refine Eventually.frequently ?_
    filter_upwards with n
    exact lintegral_ofReal_moll_le (mollRad_nonneg n) (mollRad_continuous n)
      (mollRad_cs n) (mollRad_integral n) hpm
  have hle_q : liminf (fun n => ∫⁻ z, ENNReal.ofReal (‖Weyl.moll (mollRad n) q z‖ ^ 2)) atTop
      ≤ ∫⁻ z, ENNReal.ofReal (‖q z‖ ^ 2) := by
    refine liminf_le_of_frequently_le' ?_
    refine Eventually.frequently ?_
    filter_upwards with n
    exact lintegral_ofReal_moll_le (mollRad_nonneg n) (mollRad_continuous n)
      (mollRad_cs n) (mollRad_integral n) hqm
  have hAeq : ∫⁻ z, ENNReal.ofReal (‖p z‖ ^ 2)
      = liminf (fun n => ∫⁻ z, ENNReal.ofReal (‖Weyl.moll (mollRad n) p z‖ ^ 2)) atTop :=
    le_antisymm hfat_p hle_p
  have hBeq : ∫⁻ z, ENNReal.ofReal (‖q z‖ ^ 2)
      = liminf (fun n => ∫⁻ z, ENNReal.ofReal (‖Weyl.moll (mollRad n) q z‖ ^ 2)) atTop :=
    le_antisymm hfat_q hle_q
  have hST : liminf (fun n => ∫⁻ z, ENNReal.ofReal (‖Weyl.moll (mollRad n) p z‖ ^ 2)) atTop
      = liminf (fun n => ∫⁻ z, ENNReal.ofReal (‖Weyl.moll (mollRad n) q z‖ ^ 2)) atTop := by
    congr 1
    funext n
    calc ∫⁻ z, ENNReal.ofReal (‖Weyl.moll (mollRad n) p z‖ ^ 2)
        = ENNReal.ofReal (∫ z, ‖Weyl.moll (mollRad n) p z‖ ^ 2) :=
          (ofReal_integral_eq_lintegral_ofReal (hintp n)
            (Eventually.of_forall fun z => by positivity)).symm
      _ = ENNReal.ofReal (∫ z, ‖Weyl.moll (mollRad n) q z‖ ^ 2) := by rw [henergy n]
      _ = ∫⁻ z, ENNReal.ofReal (‖Weyl.moll (mollRad n) q z‖ ^ 2) :=
          ofReal_integral_eq_lintegral_ofReal (hintq n)
            (Eventually.of_forall fun z => by positivity)
  have hfin : ENNReal.ofReal (∫ z, ‖p z‖ ^ 2) = ENNReal.ofReal (∫ z, ‖q z‖ ^ 2) :=
    calc ENNReal.ofReal (∫ z, ‖p z‖ ^ 2)
        = ∫⁻ z, ENNReal.ofReal (‖p z‖ ^ 2) := ofReal_integral_eq_lintegral_ofReal hp2 hpnn
      _ = liminf (fun n => ∫⁻ z, ENNReal.ofReal (‖Weyl.moll (mollRad n) p z‖ ^ 2)) atTop := hAeq
      _ = liminf (fun n => ∫⁻ z, ENNReal.ofReal (‖Weyl.moll (mollRad n) q z‖ ^ 2)) atTop := hST
      _ = ∫⁻ z, ENNReal.ofReal (‖q z‖ ^ 2) := hBeq.symm
      _ = ENNReal.ofReal (∫ z, ‖q z‖ ^ 2) :=
          (ofReal_integral_eq_lintegral_ofReal hq2 hqnn).symm
  calc ∫ z, ‖p z‖ ^ 2 = (ENNReal.ofReal (∫ z, ‖p z‖ ^ 2)).toReal :=
        (ENNReal.toReal_ofReal hp0).symm
    _ = (ENNReal.ofReal (∫ z, ‖q z‖ ^ 2)).toReal := by rw [hfin]
    _ = ∫ z, ‖q z‖ ^ 2 := ENNReal.toReal_ofReal hq0


/-- The cut-off `cPsi n` takes values in the unit disc. -/
theorem norm_cPsi_le_one (n : ℕ) (z : ℂ) : ‖cPsi n z‖ ≤ 1 := by
  have h1 : (0 : ℝ) ≤ cBump (cScl n * z) := ContDiffBump.nonneg cBump
  have h2 : cBump (cScl n * z) ≤ 1 := ContDiffBump.le_one cBump
  rw [cPsi, cChi, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h1]
  exact h2

theorem support_pow_two_subset {f : ℂ → ℝ} {K : Set ℂ} (h : Function.support f ⊆ K) :
    Function.support (fun z => f z ^ 2) ⊆ K := by
  intro z hz
  refine h ?_
  rw [Function.mem_support] at hz ⊢
  intro h0
  exact hz (by rw [h0]; ring)

/-- `HasCompactSupport` is preserved by multiplying on the right by an arbitrary function. -/
theorem hasCompactSupport_mul_of_left {f g : ℂ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (fun z => f z * g z) := by
  have h : HasCompactSupport (f * g) := hf.mul_right
  have hfun : (f * g) = fun z => f z * g z := by
    funext z
    rw [Pi.mul_apply]
  rwa [hfun] at h

/-- A function supported in a compact set and `L²` there is `L²`. -/
theorem memLp_two_of_support_subset {F : ℂ → ℂ} {K : Set ℂ} (hKF : Function.support F ⊆ K)
    (hm : AEStronglyMeasurable F volume) (hint : IntegrableOn (fun z => ‖F z‖ ^ 2) K volume) :
    MemLp F 2 (volume : Measure ℂ) := by
  rw [memLp_two_iff_integrable_sq_norm hm]
  rw [integrableOn_iff_integrable_of_support_subset (s := K) ?_] at hint
  · exact hint
  · intro z hz
    rw [Function.mem_support] at hz
    exact hKF (by
      rw [Function.mem_support]
      intro h0
      exact hz (by rw [h0]; simp))

/-- **A solution of the Beltrami equation with decay has vanishing `∂`.** -/
theorem dz_eq_zero_of_beltrami_of_decay_weak {h p q μ : ℂ → ℂ} {k : ℝ}
    (hhc : Continuous h) (hp : IsDzDeriv h p) (hq : IsDbarDeriv h q)
    (hpL : MemL2Loc p) (hqL : MemL2Loc q) (hk : k < 1)
    (hμ : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k)
    (hrel : ∀ᵐ z ∂(volume : Measure ℂ), q z = μ z * p z)
    (hdec : ∃ C R : ℝ, 0 ≤ C ∧ ∀ z : ℂ, R ≤ ‖z‖ → ‖h z‖ ≤ C / ‖z‖) :
    p =ᵐ[(volume : Measure ℂ)] fun _ => 0 := by
  obtain ⟨C, R, hC0, hCR⟩ := hdec
  have hk0 : 0 ≤ k := by
    obtain ⟨z, hz⟩ := hμ.exists
    exact le_trans (norm_nonneg _) hz
  obtain ⟨M, hM0, hM⟩ := cChi_deriv_bound
  have hMz : ∀ w : ℂ, ‖dz cChi w‖ ≤ M := fun w => (hM w).1
  have hMzb : ∀ w : ℂ, ‖dzbar cChi w‖ ≤ M := fun w => (hM w).2
  have hpme : AEStronglyMeasurable p volume := hp.2.1.aestronglyMeasurable
  have hqme : AEStronglyMeasurable q volume := hq.2.1.aestronglyMeasurable
  have hhme : AEStronglyMeasurable h volume := hhc.aestronglyMeasurable
  
  have hstep : ∀ n : ℕ, R ≤ cRad n → ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ cRad n →
      ∫ z in Metric.ball 0 ρ, ‖p z‖ ^ 2 ≤
        (4 * Real.pi * (C * M * (1 + k)) ^ 2 / (1 - k) ^ 2) / (cRad n) ^ 2 := by
    intro n hRn ρ _hρ0 hρn
    obtain ⟨hPu, hQu⟩ := isDzDeriv_mul_and_isDbarDeriv_mul_of_contDiff_infty
      (cPsi_contDiff n) (cPsi_cs n) hp hq
    have hus : HasCompactSupport (fun z => cPsi n z * h z) :=
      hasCompactSupport_mul_of_left (cPsi_cs n)
    have hKc : IsCompact (Metric.closedBall (0 : ℂ) (2 * cRad n)) := isCompact_closedBall _ _
    have hPmeas : AEStronglyMeasurable
        (fun z => cPsi n z * p z + h z * dz (cPsi n) z) volume :=
      (((cPsi_contDiff n).continuous.aestronglyMeasurable).mul hpme).add
        (hhme.mul (continuous_dz_of_contDiff (by simp) (cPsi_contDiff n)).aestronglyMeasurable)
    have hQmeas : AEStronglyMeasurable
        (fun z => cPsi n z * q z + h z * dzbar (cPsi n) z) volume :=
      (((cPsi_contDiff n).continuous.aestronglyMeasurable).mul hqme).add
        (hhme.mul (continuous_dzbar_of_contDiff (by simp) (cPsi_contDiff n)).aestronglyMeasurable)
    have hcontE : Continuous (fun z => ‖h z‖ *
        (k * ‖dz (cPsi n) z‖ + ‖dzbar (cPsi n) z‖)) :=
      hhc.norm.mul ((continuous_const.mul
        (continuous_dz_of_contDiff (by simp) (cPsi_contDiff n)).norm).add
        (continuous_dzbar_of_contDiff (by simp) (cPsi_contDiff n)).norm)
    have hPK : Function.support (fun z => cPsi n z * p z + h z * dz (cPsi n) z)
        ⊆ Metric.closedBall 0 (2 * cRad n) := by
      intro z hz
      by_contra hzc
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hzc
      rw [Function.mem_support] at hz
      refine hz ?_
      rw [cPsi_zero n (le_of_lt (by linarith)), cPsi_dz_zero_of_gt n (by linarith)]
      ring
    have hQK : Function.support (fun z => cPsi n z * q z + h z * dzbar (cPsi n) z)
        ⊆ Metric.closedBall 0 (2 * cRad n) := by
      intro z hz
      by_contra hzc
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hzc
      rw [Function.mem_support] at hz
      refine hz ?_
      rw [cPsi_zero n (le_of_lt (by linarith)), cPsi_dzbar_zero_of_gt n (by linarith)]
      ring
    have hpK : IntegrableOn (fun z => ‖p z‖ ^ 2) (Metric.closedBall 0 (2 * cRad n)) volume := by
      simpa [Set.inter_univ] using hpL (Metric.closedBall 0 (2 * cRad n)) hKc
    have hqK : IntegrableOn (fun z => ‖q z‖ ^ 2) (Metric.closedBall 0 (2 * cRad n)) volume := by
      simpa [Set.inter_univ] using hqL (Metric.closedBall 0 (2 * cRad n)) hKc
    have hhK : IntegrableOn (fun z => ‖h z‖ ^ 2) (Metric.closedBall 0 (2 * cRad n)) volume :=
      ContinuousOn.integrableOn_compact hKc (hhc.continuousOn.norm.pow 2)
    have hdomP : IntegrableOn (fun z => 2 * ‖p z‖ ^ 2 + 2 * M ^ 2 * ‖h z‖ ^ 2)
        (Metric.closedBall 0 (2 * cRad n)) volume :=
      (hpK.const_mul 2).add (hhK.const_mul (2 * M ^ 2))
    have hdomQ : IntegrableOn (fun z => 2 * ‖q z‖ ^ 2 + 2 * M ^ 2 * ‖h z‖ ^ 2)
        (Metric.closedBall 0 (2 * cRad n)) volume :=
      (hqK.const_mul 2).add (hhK.const_mul (2 * M ^ 2))
    have hbP : ∀ z, ‖‖(fun z => cPsi n z * p z + h z * dz (cPsi n) z) z‖ ^ 2‖
        ≤ 2 * ‖p z‖ ^ 2 + 2 * M ^ 2 * ‖h z‖ ^ 2 := by
      intro z
      have h1 : ‖cPsi n z‖ ≤ 1 := norm_cPsi_le_one n z
      have h2 : ‖dz (cPsi n) z‖ ≤ M := by
        have h := (cPsi_deriv_bound hMz hMzb n z).1
        rw [le_div_iff₀ (cRad_pos n)] at h
        nlinarith [cRad_one_le n, h, norm_nonneg (dz (cPsi n) z)]
      rw [Real.norm_of_nonneg (by positivity)]
      calc ‖cPsi n z * p z + h z * dz (cPsi n) z‖ ^ 2
          ≤ (‖cPsi n z * p z‖ + ‖h z * dz (cPsi n) z‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
        _ = (‖cPsi n z‖ * ‖p z‖ + ‖h z‖ * ‖dz (cPsi n) z‖) ^ 2 := by
            rw [norm_mul, norm_mul]
        _ ≤ (‖p z‖ + ‖h z‖ * M) ^ 2 := by
            refine pow_le_pow_left₀ (by positivity) ?_ 2
            have h4 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (p z))
            have h5 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (h z))
            linarith
        _ ≤ 2 * ‖p z‖ ^ 2 + 2 * M ^ 2 * ‖h z‖ ^ 2 := by
            nlinarith [sq_nonneg (‖p z‖ - M * ‖h z‖)]
    have hbQ : ∀ z, ‖‖(fun z => cPsi n z * q z + h z * dzbar (cPsi n) z) z‖ ^ 2‖
        ≤ 2 * ‖q z‖ ^ 2 + 2 * M ^ 2 * ‖h z‖ ^ 2 := by
      intro z
      have h1 : ‖cPsi n z‖ ≤ 1 := norm_cPsi_le_one n z
      have h2 : ‖dzbar (cPsi n) z‖ ≤ M := by
        have h := (cPsi_deriv_bound hMz hMzb n z).2
        rw [le_div_iff₀ (cRad_pos n)] at h
        nlinarith [cRad_one_le n, h, norm_nonneg (dzbar (cPsi n) z)]
      rw [Real.norm_of_nonneg (by positivity)]
      calc ‖cPsi n z * q z + h z * dzbar (cPsi n) z‖ ^ 2
          ≤ (‖cPsi n z * q z‖ + ‖h z * dzbar (cPsi n) z‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2
        _ = (‖cPsi n z‖ * ‖q z‖ + ‖h z‖ * ‖dzbar (cPsi n) z‖) ^ 2 := by
            rw [norm_mul, norm_mul]
        _ ≤ (‖q z‖ + ‖h z‖ * M) ^ 2 := by
            refine pow_le_pow_left₀ (by positivity) ?_ 2
            have h4 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (q z))
            have h5 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (h z))
            linarith
        _ ≤ 2 * ‖q z‖ ^ 2 + 2 * M ^ 2 * ‖h z‖ ^ 2 := by
            nlinarith [sq_nonneg (‖q z‖ - M * ‖h z‖)]
    have hmP : MemLp (fun z => cPsi n z * p z + h z * dz (cPsi n) z) 2 volume :=
      memLp_two_of_support_subset hPK hPmeas
        (Integrable.mono' hdomP ((hPmeas.norm.pow 2).mono_measure
          Measure.restrict_le_self) (Eventually.of_forall hbP))
    have hmQ : MemLp (fun z => cPsi n z * q z + h z * dzbar (cPsi n) z) 2 volume :=
      memLp_two_of_support_subset hQK hQmeas
        (Integrable.mono' hdomQ ((hQmeas.norm.pow 2).mono_measure
          Measure.restrict_le_self) (Eventually.of_forall hbQ))
    have he_le : ∀ z, ‖h z‖ * (k * ‖dz (cPsi n) z‖ + ‖dzbar (cPsi n) z‖)
        ≤ C * M * (1 + k) / (cRad n) ^ 2 := by
      intro z
      by_cases hz : ‖z‖ < cRad n
      · rw [cPsi_dz_zero n hz, cPsi_dzbar_zero n hz, norm_zero, mul_zero, add_zero, mul_zero]
        exact div_nonneg (mul_nonneg (mul_nonneg hC0 hM0) (by linarith))
          (pow_pos (cRad_pos n) 2).le
      · rw [not_lt] at hz
        have h1 : ‖dz (cPsi n) z‖ ≤ M / cRad n := (cPsi_deriv_bound hMz hMzb n z).1
        have h2 : ‖dzbar (cPsi n) z‖ ≤ M / cRad n := (cPsi_deriv_bound hMz hMzb n z).2
        have h3 : ‖h z‖ ≤ C / cRad n := by
          refine le_trans (hCR z (le_trans hRn hz)) ?_
          exact div_le_div_of_nonneg_left hC0 (cRad_pos n) hz
        calc ‖h z‖ * (k * ‖dz (cPsi n) z‖ + ‖dzbar (cPsi n) z‖)
            ≤ (C / cRad n) * (k * (M / cRad n) + M / cRad n) := by
              refine mul_le_mul h3 ?_ ?_ (div_nonneg hC0 (cRad_pos n).le)
              · exact add_le_add (mul_le_mul_of_nonneg_left h1 hk0) h2
              · exact add_nonneg (mul_nonneg hk0 (norm_nonneg _)) (norm_nonneg _)
          _ = C * M * (1 + k) / (cRad n) ^ 2 := by ring
    have hE : Function.support (fun z => ‖h z‖ *
        (k * ‖dz (cPsi n) z‖ + ‖dzbar (cPsi n) z‖)) ⊆ Metric.closedBall 0 (2 * cRad n) := by
      intro z hz
      by_contra hzc
      simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hzc
      rw [Function.mem_support] at hz
      refine hz ?_
      rw [cPsi_dz_zero_of_gt n (by linarith), cPsi_dzbar_zero_of_gt n (by linarith),
        norm_zero, mul_zero, add_zero, mul_zero]
    have hEm : Integrable (fun z => (‖h z‖ *
        (k * ‖dz (cPsi n) z‖ + ‖dzbar (cPsi n) z‖)) ^ 2) volume := by
      rw [← integrableOn_iff_integrable_of_support_subset
        (s := Metric.closedBall 0 (2 * cRad n)) (support_pow_two_subset hE)]
      exact ContinuousOn.integrableOn_compact hKc (hcontE.pow 2).continuousOn
    have hvol : (volume (Metric.closedBall (0 : ℂ) (2 * cRad n))).toReal
        = 4 * Real.pi * (cRad n) ^ 2 := by
      have h1 : volume (Metric.closedBall (0 : ℂ) (2 * cRad n))
          = ENNReal.ofReal ((2 * cRad n) ^ 2)
              * ENNReal.ofReal (Real.pi ^ 1 / ((Nat.factorial 1 : ℕ) : ℝ)) := by
        rw [InnerProductSpace.volume_closedBall_of_dim_even (E := ℂ) (k := 1) (by simp),
          Complex.finrank_real_complex,
          ← ENNReal.ofReal_pow (show (0 : ℝ) ≤ 2 * cRad n by linarith [cRad_pos n])]
      rw [h1]
      simp only [Nat.factorial_one, Nat.cast_one]
      rw [ENNReal.toReal_mul]
      rw [show (ENNReal.ofReal (Real.pi ^ 1 / (1 : ℝ))).toReal = Real.pi by
        rw [ENNReal.toReal_ofReal (show (0 : ℝ) ≤ Real.pi ^ 1 / 1 by positivity)]
        norm_num]
      rw [ENNReal.toReal_ofReal (sq_nonneg (2 * cRad n))]
      ring
    have hEbound : ∫ z, (‖h z‖ * (k * ‖dz (cPsi n) z‖ + ‖dzbar (cPsi n) z‖)) ^ 2
        ≤ 4 * Real.pi * (C * M * (1 + k)) ^ 2 / (cRad n) ^ 2 := by
      have hzero : ∀ x : ℂ, x ∉ Metric.closedBall 0 (2 * cRad n) →
          (‖h x‖ * (k * ‖dz (cPsi n) x‖ + ‖dzbar (cPsi n) x‖)) ^ 2 = 0 := by
        intro x hx
        have h1 : ¬((‖h x‖ * (k * ‖dz (cPsi n) x‖ + ‖dzbar (cPsi n) x‖)) ≠ 0) :=
          fun hc => hx (hE hc)
        rw [not_not] at h1
        rw [h1]
        ring
      have hmono : ∫ z in Metric.closedBall (0 : ℂ) (2 * cRad n),
            (‖h z‖ * (k * ‖dz (cPsi n) z‖ + ‖dzbar (cPsi n) z‖)) ^ 2
          ≤ ∫ _ in Metric.closedBall (0 : ℂ) (2 * cRad n),
              (C * M * (1 + k) / (cRad n) ^ 2) ^ 2 := by
        have hae : ∀ᵐ z ∂(volume.restrict (Metric.closedBall (0 : ℂ) (2 * cRad n))),
            (‖h z‖ * (k * ‖dz (cPsi n) z‖ + ‖dzbar (cPsi n) z‖)) ^ 2
              ≤ (C * M * (1 + k) / (cRad n) ^ 2) ^ 2 :=
          (ae_restrict_iff' hKc.measurableSet).mpr
            (Eventually.of_forall fun z _ => pow_le_pow_left₀ (by positivity) (he_le z) 2)
        exact integral_mono_ae hEm.integrableOn
          (integrableOn_const hKc.measure_lt_top.ne) hae
      have hval : (∫ _ in Metric.closedBall (0 : ℂ) (2 * cRad n),
              (C * M * (1 + k) / (cRad n) ^ 2) ^ 2)
          = (volume (Metric.closedBall (0 : ℂ) (2 * cRad n))).toReal *
              (C * M * (1 + k) / (cRad n) ^ 2) ^ 2 := by
        rw [setIntegral_const]
        rfl
      have hfirst : ∫ z, (‖h z‖ * (k * ‖dz (cPsi n) z‖ + ‖dzbar (cPsi n) z‖)) ^ 2
          = ∫ z in Metric.closedBall (0 : ℂ) (2 * cRad n),
              (‖h z‖ * (k * ‖dz (cPsi n) z‖ + ‖dzbar (cPsi n) z‖)) ^ 2 :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
      rw [hfirst]
      calc ∫ z in Metric.closedBall (0 : ℂ) (2 * cRad n),
            (‖h z‖ * (k * ‖dz (cPsi n) z‖ + ‖dzbar (cPsi n) z‖)) ^ 2
          ≤ ∫ _ in Metric.closedBall (0 : ℂ) (2 * cRad n),
              (C * M * (1 + k) / (cRad n) ^ 2) ^ 2 := hmono
        _ = (volume (Metric.closedBall (0 : ℂ) (2 * cRad n))).toReal *
              (C * M * (1 + k) / (cRad n) ^ 2) ^ 2 := hval
        _ = 4 * Real.pi * (C * M * (1 + k)) ^ 2 / (cRad n) ^ 2 := by
            rw [hvol]
            field_simp
    have henergy : ∫ z, ‖cPsi n z * p z + h z * dz (cPsi n) z‖ ^ 2
        = ∫ z, ‖cPsi n z * q z + h z * dzbar (cPsi n) z‖ ^ 2 :=
      energy_identity_of_w12_compactSupport hus hPu hQu hmP hmQ
    have hbp : ∀ᵐ z ∂(volume : Measure ℂ),
        ‖cPsi n z * q z + h z * dzbar (cPsi n) z‖
          ≤ k * ‖cPsi n z * p z + h z * dz (cPsi n) z‖
            + ‖h z‖ * (k * ‖dz (cPsi n) z‖ + ‖dzbar (cPsi n) z‖) := by
      filter_upwards [hμ, hrel] with z hzμ hzr
      have e1 : cPsi n z * q z + h z * dzbar (cPsi n) z
          = cPsi n z * (μ z * p z) + h z * dzbar (cPsi n) z := by rw [hzr]
      rw [e1]
      set A : ℂ := cPsi n z * p z + h z * dz (cPsi n) z with hA
      set B : ℂ := h z * dz (cPsi n) z with hB
      have e2 : cPsi n z * (μ z * p z) = μ z * (A - B) := by rw [hA, hB]; ring
      rw [e2]
      calc ‖μ z * (A - B) + h z * dzbar (cPsi n) z‖
          ≤ ‖μ z * (A - B)‖ + ‖h z * dzbar (cPsi n) z‖ := norm_add_le _ _
        _ = ‖μ z‖ * ‖A - B‖ + ‖h z‖ * ‖dzbar (cPsi n) z‖ := by rw [norm_mul, norm_mul]
        _ ≤ k * (‖A‖ + ‖B‖) + ‖h z‖ * ‖dzbar (cPsi n) z‖ := by
            have h1 : ‖A - B‖ ≤ ‖A‖ + ‖B‖ := norm_sub_le _ _
            have h2 : ‖μ z‖ * ‖A - B‖ ≤ k * (‖A‖ + ‖B‖) := by
              have h3 := mul_le_mul hzμ h1 (norm_nonneg _) hk0
              linarith
            linarith
        _ = k * ‖A‖ + ‖h z‖ * (k * ‖dz (cPsi n) z‖ + ‖dzbar (cPsi n) z‖) := by
            rw [hB, norm_mul]
            ring
    have hmain : ∫ z, ‖cPsi n z * p z + h z * dz (cPsi n) z‖ ^ 2
        ≤ (∫ z, (‖h z‖ * (k * ‖dz (cPsi n) z‖ + ‖dzbar (cPsi n) z‖)) ^ 2)
          / (1 - k) ^ 2 :=
      l2_bound_of_energy hk0 hk hmP hmQ
        ((memLp_two_iff_integrable_sq_norm (hcontE.aestronglyMeasurable)).mpr
          (hEm.congr (Eventually.of_forall fun z => by
            dsimp only
            rw [Real.norm_of_nonneg (by positivity)])))
        (Eventually.of_forall fun z => by positivity) henergy hbp
    have hPeq : ∀ z, ‖z‖ < cRad n → cPsi n z * p z + h z * dz (cPsi n) z = p z := by
      intro z hz
      rw [cPsi_one n (le_of_lt hz), cPsi_dz_zero n hz]
      ring
    have hball : ∫ z in Metric.ball 0 ρ, ‖p z‖ ^ 2
        ≤ ∫ z, ‖cPsi n z * p z + h z * dz (cPsi n) z‖ ^ 2 := by
      have h1 : (∫ z in Metric.ball 0 ρ, ‖p z‖ ^ 2)
          = ∫ z in Metric.ball 0 ρ, ‖cPsi n z * p z + h z * dz (cPsi n) z‖ ^ 2 := by
        refine setIntegral_congr_fun measurableSet_ball fun z hz => ?_
        have hz' : ‖z‖ < cRad n := by
          have := Metric.mem_ball.mp hz
          rw [dist_zero_right] at this
          linarith
        rw [hPeq z hz']
      rw [h1]
      refine setIntegral_le_integral
        ((memLp_two_iff_integrable_sq_norm hmP.aestronglyMeasurable).mp hmP) ?_
      filter_upwards with z
      positivity
    calc ∫ z in Metric.ball 0 ρ, ‖p z‖ ^ 2
        ≤ ∫ z, ‖cPsi n z * p z + h z * dz (cPsi n) z‖ ^ 2 := hball
      _ ≤ (∫ z, (‖h z‖ * (k * ‖dz (cPsi n) z‖ + ‖dzbar (cPsi n) z‖)) ^ 2)
            / (1 - k) ^ 2 := hmain
      _ ≤ (4 * Real.pi * (C * M * (1 + k)) ^ 2 / (cRad n) ^ 2) / (1 - k) ^ 2 :=
            div_le_div_of_nonneg_right hEbound (by positivity)
      _ = (4 * Real.pi * (C * M * (1 + k)) ^ 2 / (1 - k) ^ 2) / (cRad n) ^ 2 := by ring
  have hρ : ∀ ρ : ℝ, 0 ≤ ρ → ∫ z in Metric.ball 0 ρ, ‖p z‖ ^ 2 = 0 := by
    intro ρ hρ0
    have htend : Tendsto
        (fun n : ℕ => (4 * Real.pi * (C * M * (1 + k)) ^ 2 / (1 - k) ^ 2) / (cRad n) ^ 2)
        atTop (𝓝 0) := by
      refine Tendsto.div_atTop tendsto_const_nhds ?_
      refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
      have h1 := cRad_one_le n
      have h0 : (0:ℝ) < cRad n := cRad_pos n
      have h2 : cRad n = (n : ℝ) + 1 := rfl
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    refine le_antisymm ?_ (integral_nonneg fun z => by positivity)
    refine le_of_tendsto_of_tendsto tendsto_const_nhds htend ?_
    filter_upwards [eventually_ge_atTop (Nat.ceil (max (max ρ R) 1))] with n hn
    have h1 : max (max ρ R) 1 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hn)
    have h2 : ρ ≤ cRad n := by
      have h5 : ρ ≤ max (max ρ R) 1 := le_trans (le_max_left ρ R) (le_max_left (max ρ R) 1)
      have h3 : cRad n = (n:ℝ) + 1 := rfl
      linarith
    have h4 : R ≤ cRad n := by
      have h5 : R ≤ max (max ρ R) 1 := le_trans (le_max_right ρ R) (le_max_left (max ρ R) 1)
      have h3 : cRad n = (n:ℝ) + 1 := rfl
      linarith
    exact hstep n h4 ρ hρ0 h2
  have hnull : ∀ m : ℕ, volume {z : ℂ | z ∈ Metric.ball 0 ((m : ℝ) + 1) ∧ p z ≠ 0} = 0 := by
    intro m
    have h1 : IntegrableOn (fun z => ‖p z‖ ^ 2) (Metric.ball 0 ((m : ℝ) + 1)) volume :=
      (hpL (Metric.closedBall 0 ((m:ℝ)+1)) (isCompact_closedBall (0:ℂ) ((m:ℝ)+1))).mono_set
        (Set.subset_inter Metric.ball_subset_closedBall (Set.subset_univ _))
    have h2 : ∫ z in Metric.ball 0 ((m : ℝ) + 1), ‖p z‖ ^ 2 = 0 := hρ _ (by positivity)
    have h3 : (fun z => ‖p z‖ ^ 2) =ᵐ[volume.restrict (Metric.ball 0 ((m : ℝ) + 1))] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun z => by positivity) h1).mp h2
    have h5 := MeasureTheory.ae_iff.mp h3
    rw [Measure.restrict_apply' measurableSet_ball] at h5
    have h6 : {z : ℂ | z ∈ Metric.ball 0 ((m : ℝ) + 1) ∧ p z ≠ 0}
        = {z : ℂ | ¬(‖p z‖ ^ 2 = 0)} ∩ Metric.ball 0 ((m : ℝ) + 1) := by
      ext z
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun h0 => h2 (norm_eq_zero.mp (sq_eq_zero_iff.mp h0)), h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, fun hp0 => h1 (by rw [hp0]; simp)⟩
    rw [h6]
    exact h5
  have hmem : ∀ᵐ z ∂(volume : Measure ℂ), p z = 0 := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_ (measure_iUnion_null hnull)
    intro z hz
    simp only [Set.mem_setOf_eq, ne_eq] at hz
    obtain ⟨m, hm⟩ := exists_nat_gt ‖z‖
    exact Set.mem_iUnion.mpr ⟨m, by
      refine ⟨?_, hz⟩
      rw [Metric.mem_ball, dist_zero_right]
      linarith⟩
  exact hmem

/-- **A continuous solution of the Beltrami equation with `O(1/‖z‖)` decay vanishes.** -/
theorem eq_zero_of_beltrami_of_decay_weak {h p q μ : ℂ → ℂ} {k : ℝ}
    (hhc : Continuous h) (hp : IsDzDeriv h p) (hq : IsDbarDeriv h q)
    (hpL : MemL2Loc p) (hqL : MemL2Loc q) (hk : k < 1)
    (hμ : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k)
    (hrel : ∀ᵐ z ∂(volume : Measure ℂ), q z = μ z * p z)
    (hdec : ∃ C R : ℝ, 0 ≤ C ∧ ∀ z : ℂ, R ≤ ‖z‖ → ‖h z‖ ≤ C / ‖z‖) :
    h = fun _ => 0 := by
  obtain ⟨C, R, hC0, hCR⟩ := hdec
  have hpzero : p =ᵐ[(volume : Measure ℂ)] fun _ => 0 :=
    dz_eq_zero_of_beltrami_of_decay_weak hhc hp hq hpL hqL hk hμ hrel ⟨C, R, hC0, hCR⟩
  have hqzero : q =ᵐ[(volume : Measure ℂ)] fun _ => 0 := by
    filter_upwards [hpzero, hrel] with z hp0 hr
    rw [hr, hp0]
    simp
  have hdiff : Differentiable ℂ h :=
    Weyl.differentiable_of_isDbarDeriv hhc (isDbarDeriv_zero_of_ae_eq_zero hq hqzero)
  exact eq_zero_of_differentiable_of_decay hdiff ⟨C, R, fun z hz => hCR z hz⟩

/-- **Uniqueness of the principal solution.** Two quasiconformal maps of `ℂ` with the
same complex dilatation `μ` and the same principal normalisation `φ z = z + O(1/z)` at infinity
are equal.

Route.  Put `h := φ - ψ`.  Then `h` is continuous, `h z = O(1/z)`, and `∂̄h = μ ∂h` a.e., with
finite energy `∫ ‖∂h‖² = ∫ ‖∂̄h‖² < ∞` (the `L²` finiteness of the exterior part follows from the
area theorem `∑ n ‖a_n‖²/R^{2n} ≤ R²` for the exterior expansions of `φ` and `ψ`).  Hence
`∫ ‖∂h‖² = ∫ ‖μ ∂h‖² ≤ k² ∫ ‖∂h‖²`, so `∂h = 0` a.e.; Weyl's lemma
(`Work.MRMT.Weyl.differentiable_of_isDbarDeriv`, `Work.MRMT.QC.isDbarDeriv_zero_of_ae_dzbar_eq_zero`)
makes `h` entire, and `h = O(1/z)` forces `h = 0` by Liouville
(`Work.MRMT.QC.principal_eq_id_of_differentiable_of_decay` after adding back `id`).  The two
analytic inputs that need care are the energy identity for the *decaying* (non-compactly
supported) function `h` — obtained from `Work.MRMT.Beltrami.energy_identity_of_contDiff_two`
(clean) by a cut-off/mollification limit — and the linearity/uniqueness of the weak Wirtinger
derivatives (`Work.MRMT.Sobolev.is_dbar_deriv_unique`). -/
theorem principal_unique {φ ψ : ℂ → ℂ} {μ : ℂ → ℂ}
    (hφ : Work.MRMT.IsQCOn φ Set.univ μ) (hψ : Work.MRMT.IsQCOn ψ Set.univ μ)
    (hpφ : Work.MRMT.IsPrincipalAtInfinity φ) (hpψ : Work.MRMT.IsPrincipalAtInfinity ψ) :
    φ = ψ := by
  obtain ⟨Cφ, Rφ, hCφ0, hφd⟩ := isPrincipalAtInfinity_decay hpφ
  obtain ⟨Cψ, Rψ, hCψ0, hψd⟩ := isPrincipalAtInfinity_decay hpψ
  obtain ⟨gzφ, gzbφ, hzφ, hbφ, hlzφ, hlbφ, hzagφ, hbagφ⟩ := hφ.2.2.1.2
  obtain ⟨gzψ, gzbψ, hzψ, hbψ, hlzψ, hlbψ, hzagψ, hbagψ⟩ := hψ.2.2.1.2
  have hcont : Continuous (φ - ψ) :=
    (continuousOn_univ.mp hφ.2.1.1).sub (continuousOn_univ.mp hψ.2.1.1)
  have hp : IsDzDeriv (φ - ψ) (gzφ - gzψ) :=
    IsDzDeriv.sub (isDzDeriv_of_isDzDerivOn_univ hzφ) (isDzDeriv_of_isDzDerivOn_univ hzψ)
  have hq : IsDbarDeriv (φ - ψ) (gzbφ - gzbψ) :=
    IsDbarDeriv.sub (isDbarDeriv_of_isDbarDerivOn_univ hbφ)
      (isDbarDeriv_of_isDbarDerivOn_univ hbψ)
  have hpL : MemL2Loc (gzφ - gzψ) :=
    MemL2LocOn.sub hlzφ hlzψ hzφ.2.1.aestronglyMeasurable hzψ.2.1.aestronglyMeasurable
  have hqL : MemL2Loc (gzbφ - gzbψ) :=
    MemL2LocOn.sub hlbφ hlbψ hbφ.2.1.aestronglyMeasurable hbψ.2.1.aestronglyMeasurable
  have hrel : ∀ᵐ z ∂(volume : Measure ℂ), (gzbφ - gzbψ) z = μ z * (gzφ - gzψ) z := by
    have h1 : ∀ᵐ z ∂(volume : Measure ℂ), gzbφ z = μ z * gzφ z := by
      filter_upwards [hbagφ, hzagφ, hφ.2.2.2.2] with z hb hz hr
      rw [hb, hz]
      exact hr (Set.mem_univ z)
    have h2 : ∀ᵐ z ∂(volume : Measure ℂ), gzbψ z = μ z * gzψ z := by
      filter_upwards [hbagψ, hzagψ, hψ.2.2.2.2] with z hb hz hr
      rw [hb, hz]
      exact hr (Set.mem_univ z)
    filter_upwards [h1, h2] with z h1z h2z
    simp only [Pi.sub_apply]
    rw [h1z, h2z]
    ring
  obtain ⟨k, hk, hμ⟩ := hφ.2.2.2.1
  have hμ' : ∀ᵐ z ∂(volume : Measure ℂ), ‖μ z‖ ≤ k := by
    filter_upwards [hμ] with z hz
    exact hz (Set.mem_univ z)
  have hdec : ∃ C R : ℝ, 0 ≤ C ∧ ∀ z : ℂ, R ≤ ‖z‖ → ‖(φ - ψ) z‖ ≤ C / ‖z‖ :=
    ⟨Cφ + Cψ, max Rφ Rψ, add_nonneg hCφ0 hCψ0, fun z hz => by
      have h1 := hφd z (le_trans (le_max_left _ _) hz)
      have h2 := hψd z (le_trans (le_max_right _ _) hz)
      have h3 : ‖(φ - ψ) z‖ ≤ ‖φ z - z‖ + ‖ψ z - z‖ := by
        have h4 := norm_sub_le (φ z - z) (ψ z - z)
        simpa [Pi.sub_apply] using h4
      calc ‖(φ - ψ) z‖ ≤ ‖φ z - z‖ + ‖ψ z - z‖ := h3
        _ ≤ Cφ / ‖z‖ + Cψ / ‖z‖ := add_le_add h1 h2
        _ = (Cφ + Cψ) / ‖z‖ := by ring⟩
  have hz0 : (φ - ψ) = fun _ => 0 :=
    eq_zero_of_beltrami_of_decay_weak hcont hp hq hpL hqL hk hμ' hrel hdec
  funext z
  have hz := congrFun hz0 z
  simp only [Pi.sub_apply, Pi.zero_apply] at hz
  exact sub_eq_zero.mp hz

end Work.MRMT.QC
