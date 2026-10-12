import Mathlib.Tactic.Have
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Submission.BracketCount
import Submission.Commons.Measure.Integral.integrable_uncurry_of_lintegral_le_sfinite
import Submission.Work.SmallBoxBridge.Resolve.winModeForm_sq_eq_dirichlet
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `T0Form_slot_eq_dirichlet` — the fibre Plancherel identity

This is the `F = ‖·‖²` specialisation of the kinetic bridge: for a smooth state `Ψ`
supported in the centred box `abox (n+1) s`, the `i`-th slot contribution to the
windowed-exponential Fourier form of `𝒯₀ = Σ_i Q_i χ_i F(√−Δ_i) χ_i Q_i` equals the
Dirichlet energy of the windowed `Q_i`-projected `i`-th fibre.

The proof peels the `i`-th coordinate (`kcInsN`), swaps the `p`- and fibre-integrals,
and applies the one-particle Plancherel identity `winModeForm_sq_eq_dirichlet` fibre by
fibre.
-/

noncomputable section
open MeasureTheory
open Filter
open scoped ContDiff Topology Real BigOperators ENNReal FourierTransform

namespace Work.SmallBoxBridge.Fourier

open Submission.BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. Slot bookkeeping

`kcInsN n i (y,r)` inserts `y` in the `i`-th slot and `r` in the others. -/

/-- Updating the `i`-th slot of `kcInsN n i (y,r)` gives `kcInsN n i (z,r)`. -/
lemma update_kcInsN {n : ℕ} (i : Fin (n + 1)) (y z : ℝ³) (r : X n) :
    Function.update (kcInsN n i (y, r)) i z = kcInsN n i (z, r) := by
  funext j
  by_cases hj : j = i
  · rw [hj, Function.update_self, kc_insN_apply_same]
  · rw [Function.update_of_ne hj]
    exact kc_insN_other_indep n i y z r j hj

/-- Perturbing `kcInsN n i (y,r)` in the `i`-slot by `kcDir` is inserting `y + t•e_k`. -/
lemma kcInsN_add_smul {n : ℕ} (i : Fin (n + 1)) (y : ℝ³) (r : X n) (t : ℝ) (k : Fin 3) :
    kcInsN n i (y, r) + t • kcDir (n + 1) i k = kcInsN n i (y + t • kcStdBasis k, r) := by
  funext j
  by_cases hj : j = i
  · rw [hj, Pi.add_apply, Pi.smul_apply, kcDir_apply_eq, kc_insN_apply_same, kc_insN_apply_same]
  · rw [Pi.add_apply, Pi.smul_apply, kcDir_apply_ne (N := n + 1) i k hj, smul_zero, add_zero]
    exact kc_insN_other_indep n i y (y + t • kcStdBasis k) r j hj

/-- `z ↦ kcInsN n i (z, r)` is smooth. -/
lemma contDiff_kcInsN_right {n : ℕ} (i : Fin (n + 1)) (r : X n) :
    ContDiff ℝ ∞ (fun z : ℝ³ => kcInsN n i (z, r)) := by
  have hEq : (fun z : ℝ³ => kcInsN n i (z, r))
      = fun z : ℝ³ => kcInsN n i (0, r) + Function.update (0 : X (n + 1)) i z := by
    funext z j
    by_cases hj : j = i
    · rw [hj]
      simp only [Pi.add_apply, Function.update_self, kc_insN_apply_same, zero_add]
    · rw [Pi.add_apply, Function.update_of_ne hj, Pi.zero_apply, add_zero]
      exact kc_insN_other_indep n i z 0 r j hj
  rw [hEq]
  exact contDiff_const.add (contDiff_update ∞ (0 : X (n + 1)) i)


/-! ## 2. The slot amplitude is a windowed Fourier transform -/

/-- `rawSlotAmp` is the (`p`-convention) Fourier transform of the windowed `i`-th fibre:
the set integral over `acube s` may be extended to `ℝ³` because `chiScale s` vanishes off
`acube s`. -/
theorem rawSlotAmp_eq_kinFT {N : ℕ} {s : ℝ} (hs : 0 < s) (p : ℝ³)
    (Φ : X N → ℝ) (i : Fin N) (x : X N) :
    rawSlotAmp s p Φ i x
      = kinFT (fun z : ℝ³ => (chiScale s z : ℂ) * (Φ (Function.update x i z) : ℂ)) p := by
  have hzero : ∀ z : ℝ³, z ∉ acube s → chiScale s z = 0 := by
    intro z hz
    by_contra h
    exact hz (chiScale_mem_acube hs h)
  rw [rawSlotAmp, kinFT]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := acube s)
    (f := fun z : ℝ³ => (chiScale s z : ℂ) *
      Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) * (Φ (Function.update x i z) : ℂ))
    (fun z hz => by simp [hzero z hz])]
  refine integral_congr_ae (Eventually.of_forall (fun z => ?_))
  ring

/-! ## 3. The one-particle Plancherel identity -/

/-- **Plancherel for a compactly supported smooth real function**: the `p`-convention
kinetic energy equals the Dirichlet energy.  This is the `χ ≡ 1` case of
`winModeForm_sq_eq_dirichlet`. -/
theorem kinFT_energy_cspt (u : ℝ³ → ℝ) (hu : ContDiff ℝ ∞ u) (hcs : HasCompactSupport u) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖p‖ ^ 2 *
        ‖kinFT (fun z : ℝ³ => (u z : ℂ)) p‖ ^ 2
      = ∫ z : ℝ³, ∑ k : Fin 3,
          (fderiv ℝ u z (kcStdBasis k)) ^ 2 := by
  have h := Work.SmallBoxBridge.Resolve.winModeForm_sq_eq_dirichlet (fun _ : ℝ³ => (1 : ℝ)) u contDiff_const hu hcs
  have harg : (fun y : ℝ³ => (((1 : ℝ)) : ℂ) * (u y : ℂ)) = (fun z : ℝ³ => (u z : ℂ)) := by
    funext y; simp
  have h2 : winModeForm (fun _ : ℝ³ => (1 : ℝ)) (fun r => r ^ 2) u
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖p‖ ^ 2 *
          ‖kinFT (fun z : ℝ³ => (u z : ℂ)) p‖ ^ 2 := by
    unfold winModeForm
    rw [harg]
  rw [← h2, h]
  refine integral_congr_ae (Eventually.of_forall (fun z => ?_))
  simp

/-- **Support shrinking**: the Dirichlet integrand of the windowed fibre vanishes off
`acube s`, so the integral over `ℝ³` is the integral over `acube s`. -/
theorem energy_support_shrink {s : ℝ} (hs : 0 < s) (ψ : ℝ³ → ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    (∫ z : ℝ³, ∑ k : Fin 3,
        (fderiv ℝ (fun w : ℝ³ => chiScale s w * ψ w) z (kcStdBasis k)) ^ 2)
      = ∫ z in acube s, ∑ k : Fin 3,
          (fderiv ℝ (fun w : ℝ³ => chiScale s w * ψ w) z (kcStdBasis k)) ^ 2 := by
  have hzero : ∀ z ∉ acube s, (∑ k : Fin 3,
      (fderiv ℝ (fun w : ℝ³ => chiScale s w * ψ w) z (kcStdBasis k)) ^ 2) = 0 := by
    intro z hz
    have hz_norm : s / 2 < ‖z‖ := by
      by_contra h
      simp only [not_lt] at h
      exact hz (mem_acube_of_norm_le (le_of_lt hs) h)
    have hev : (fun w : ℝ³ => chiScale s w * ψ w) =ᶠ[𝓝 z] (fun _ => 0) := by
      have hopen : IsOpen {w : ℝ³ | s / 2 < ‖w‖} := isOpen_lt continuous_const continuous_norm
      filter_upwards [hopen.mem_nhds hz_norm] with w hw
      have hw0 : chiScale s w = 0 := by
        by_contra h
        exact absurd (chiScale_support_le hs h) (not_le.mpr hw)
      rw [hw0, zero_mul]
    have hfd : fderiv ℝ (fun w : ℝ³ => chiScale s w * ψ w) z = 0 := by
      rw [hev.fderiv_eq, fderiv_const_apply]
    simp [hfd]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (s := acube s) hzero]

/-- **The fibre Plancherel identity**: for smooth `ψ`, the windowed mode form of the
symbol `‖·‖²` equals the Dirichlet energy of `χ_s ψ` over `acube s`. -/
theorem fibre_energy {s : ℝ} (hs : 0 < s) {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖p‖ ^ 2 *
        ‖kinFT (fun z : ℝ³ => (chiScale s z : ℂ) * (ψ z : ℂ)) p‖ ^ 2
      = ∫ z in acube s, ∑ k : Fin 3,
          (fderiv ℝ (fun w : ℝ³ => chiScale s w * ψ w) z (kcStdBasis k)) ^ 2 := by
  have h1 := kinFT_energy_cspt (fun w : ℝ³ => chiScale s w * ψ w)
    ((chiScale_contDiff (ne_of_gt hs)).mul hψ)
    ((chiScale_hasCompactSupport (ne_of_gt hs)).mul_right)
  have h2 := energy_support_shrink hs ψ hψ
  have harg : (fun z : ℝ³ => (chiScale s z : ℂ) * (ψ z : ℂ))
      = (fun z : ℝ³ => ((chiScale s z * ψ z : ℝ) : ℂ)) := by
    funext z; rw [Complex.ofReal_mul]
  rw [harg, h1, h2]

/-! ## 4. The directional derivative in the `i`-th slot is the fibre derivative -/

/-- The `kcDir`-directional derivative of `z ↦ χ_s(z i)·Φ z` at `kcInsN n i (y,r)` equals the
derivative of the one-variable fibre `w ↦ χ_s w·Φ(kcInsN n i (w,r))` at `y`. -/
theorem fderiv_slot_eq_fibre {n : ℕ} {s : ℝ} (hs : 0 < s) {Φ : X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (i : Fin (n + 1)) (r : X n) (y : ℝ³) (k : Fin 3) :
    fderiv ℝ (fun z : X (n + 1) => chiScale s (z i) * Φ z)
      (kcInsN n i (y, r)) (kcDir (n + 1) i k)
      = fderiv ℝ (fun w : ℝ³ => chiScale s w * Φ (kcInsN n i (w, r)))
        y (kcStdBasis k) := by
  set A : X (n + 1) → ℝ := fun z => chiScale s (z i) * Φ z with hA
  set B : ℝ³ → ℝ := fun w => chiScale s w * Φ (kcInsN n i (w, r)) with hB
  have hchi : ContDiff ℝ ∞ (fun z : X (n + 1) => chiScale s (z i)) :=
    (chiScale_contDiff (ne_of_gt hs)).comp (by fun_prop)
  have hA_diff : DifferentiableAt ℝ A (kcInsN n i (y, r)) :=
    (hchi.mul hΦ).differentiable (by norm_num) _
  have hB_diff : DifferentiableAt ℝ B y :=
    (((chiScale_contDiff (ne_of_gt hs)).mul
      (hΦ.comp (contDiff_kcInsN_right i r)))).differentiable (by norm_num) _
  have hc : HasDerivAt (fun t : ℝ => kcInsN n i (y, r) + t • kcDir (n + 1) i k)
      (kcDir (n + 1) i k) 0 := by
    have h : HasDerivAt (fun t : ℝ => t • kcDir (n + 1) i k) (kcDir (n + 1) i k) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (kcDir (n + 1) i k)
    simpa using h.const_add (kcInsN n i (y, r))
  have hd : HasDerivAt (fun t : ℝ => y + t • kcStdBasis k) (kcStdBasis k) 0 := by
    have h : HasDerivAt (fun t : ℝ => t • kcStdBasis k) (kcStdBasis k) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (kcStdBasis k)
    simpa using h.const_add y
  have hA2 : HasFDerivAt A (fderiv ℝ A (kcInsN n i (y, r)))
      (kcInsN n i (y, r) + (0 : ℝ) • kcDir (n + 1) i k) := by
    simpa using hA_diff.hasFDerivAt
  have hB2 : HasFDerivAt B (fderiv ℝ B y) (y + (0 : ℝ) • kcStdBasis k) := by
    simpa using hB_diff.hasFDerivAt
  have h1 : HasDerivAt (A ∘ fun t : ℝ => kcInsN n i (y, r) + t • kcDir (n + 1) i k)
      ((fderiv ℝ A (kcInsN n i (y, r))) (kcDir (n + 1) i k)) 0 :=
    hA2.comp_hasDerivAt 0 hc
  have h2 : HasDerivAt (B ∘ fun t : ℝ => y + t • kcStdBasis k)
      ((fderiv ℝ B y) (kcStdBasis k)) 0 := hB2.comp_hasDerivAt 0 hd
  have hfun : (A ∘ fun t : ℝ => kcInsN n i (y, r) + t • kcDir (n + 1) i k)
      = (B ∘ fun t : ℝ => y + t • kcStdBasis k) := by
    funext t
    simp only [Function.comp_apply, hA, hB]
    rw [kcInsN_add_smul, kc_insN_apply_same]
  rw [hfun] at h1
  exact h1.unique h2

/-- The `i`-slot Dirichlet integrand is continuous on the compact box. -/
theorem exists_bound_dirichlet_integrand {n : ℕ} {s : ℝ} (hs : 0 < s)
    {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (i : Fin (n + 1)) :
    ∃ C : ℝ, ∀ x ∈ abox (n + 1) s,
      (∑ k : Fin 3, (fderiv ℝ (fun z : X (n + 1) =>
          chiScale s (z i) * Φ z) x (kcDir (n + 1) i k)) ^ 2) ≤ C := by
  have hchi : ContDiff ℝ ∞ (fun z : X (n + 1) => chiScale s (z i)) :=
    (chiScale_contDiff (ne_of_gt hs)).comp (by fun_prop)
  have hA : ContDiff ℝ ∞ (fun z : X (n + 1) => chiScale s (z i) * Φ z) := hchi.mul hΦ
  have hfd : Continuous (fun x : X (n + 1) => fderiv ℝ (fun z : X (n + 1) =>
      chiScale s (z i) * Φ z) x) := hA.continuous_fderiv (by simp)
  have hcont : Continuous (fun x : X (n + 1) => ∑ k : Fin 3, (fderiv ℝ (fun z : X (n + 1) =>
      chiScale s (z i) * Φ z) x (kcDir (n + 1) i k)) ^ 2) :=
    continuous_finsetSum _ (fun k _ => ((hfd.clm_apply continuous_const).pow 2))
  obtain ⟨C, hC⟩ := (abox_compact (n + 1) hs).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨C, fun x hx => ?_⟩
  have h := hC x hx
  rwa [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun k _ => sq_nonneg _))] at h

/-- `rawSlotAmp` is continuous in the configuration. -/
theorem continuous_rawSlotAmp {N : ℕ} {s : ℝ} (hs : 0 < s) (p : ℝ³)
    {Φ : X N → ℝ} (hΦ : Continuous Φ) (i : Fin N) :
    Continuous (fun x : X N => rawSlotAmp s p Φ i x) := by
  have hF : Continuous (Function.uncurry (fun (x : X N) (z : ℝ³) =>
      (chiScale s z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
        (Φ (Function.update x i z) : ℂ))) := by
    rw [show (Function.uncurry (fun (x : X N) (z : ℝ³) =>
        (chiScale s z : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p z : ℂ))) *
          (Φ (Function.update x i z) : ℂ)))
        = fun q : X N × ℝ³ => (chiScale s q.2 : ℂ) *
            Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ))) *
            (Φ (Function.update q.1 i q.2) : ℂ) from rfl]
    have h1 : Continuous (fun q : X N × ℝ³ => (chiScale s q.2 : ℂ)) :=
      Complex.continuous_ofReal.comp ((chiScale_continuous s).comp continuous_snd)
    have h2 : Continuous (fun q : X N × ℝ³ =>
        Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ)))) :=
      Complex.continuous_exp.comp
        ((continuous_const.mul (Complex.continuous_ofReal.comp
          (continuous_const.inner continuous_snd))).neg)
    have h3 : Continuous (fun q : X N × ℝ³ => (Φ (Function.update q.1 i q.2) : ℂ)) :=
      Complex.continuous_ofReal.comp (hΦ.comp (continuous_update i))
    exact (h1.mul h2).mul h3
  have h := Commons.Analysis.Calculus.continuous_setIntegral_isCompact (E := ℂ)
    (acube_compact hs) hF
  simpa [rawSlotAmp] using h


/-! ## 5. Integrability and the uniform bound -/

/-- The Fourier transform of a Schwartz function is Schwartz, so `ξ ↦ ‖ξ‖²‖𝓕F ξ‖²` is
integrable. -/
lemma integrable_norm_sq_fourier (F : SchwartzMap ℝ³ ℂ) :
    Integrable (fun ξ : ℝ³ => ‖ξ‖ ^ 2 * ‖(𝓕 F) ξ‖ ^ 2) := by
  have hk : ∀ k : Fin 3, Integrable (fun ξ : ℝ³ =>
      (inner ℝ ξ (kcStdBasis k)) ^ 2 * ‖(𝓕 F) ξ‖ ^ 2) :=
    fun k => Work.SmallBoxBridge.Resolve.integrable_inner_sq_mul_norm_sq (𝓕 F) (kcStdBasis k)
  have hsum : Integrable (fun ξ : ℝ³ => ∑ k : Fin 3,
      (inner ℝ ξ (kcStdBasis k)) ^ 2 * ‖(𝓕 F) ξ‖ ^ 2) :=
    integrable_finsetSum (Finset.univ) (fun k _ => hk k)
  refine hsum.congr (Eventually.of_forall (fun ξ => ?_))
  change (∑ k, inner ℝ ξ (kcStdBasis k) ^ 2 * ‖(𝓕 F) ξ‖ ^ 2)
    = ‖ξ‖ ^ 2 * ‖(𝓕 F) ξ‖ ^ 2
  rw [← Finset.sum_mul, Work.SmallBoxBridge.Resolve.sum_inner_kcStdBasis_sq_local]

/-- Integrability in `p` of the windowed kinetic energy of a smooth fibre. -/
theorem integrable_kinFT_energy {s : ℝ} (hs : 0 < s) {ψ : ℝ³ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    Integrable (fun p : ℝ³ => ‖p‖ ^ 2 *
      ‖kinFT (fun z : ℝ³ => (chiScale s z : ℂ) * (ψ z : ℂ)) p‖ ^ 2) := by
  have hwR_diff : ContDiff ℝ ∞ (fun z : ℝ³ => chiScale s z * ψ z) :=
    (chiScale_contDiff (ne_of_gt hs)).mul hψ
  have hwR_cs : HasCompactSupport (fun z : ℝ³ => chiScale s z * ψ z) :=
    (chiScale_hasCompactSupport (ne_of_gt hs)).mul_right
  let F : SchwartzMap ℝ³ ℂ := (hwR_cs.comp_left (by simp : ((0 : ℝ) : ℂ) = 0)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hwR_diff)
  have hF_coe : (F : ℝ³ → ℂ) = fun z => ((chiScale s z * ψ z : ℝ) : ℂ) := rfl
  have hIntξ : Integrable (fun ξ : ℝ³ => ‖ξ‖ ^ 2 * ‖(𝓕 F) ξ‖ ^ 2) :=
    integrable_norm_sq_fourier F
  have hInt2 : Integrable (fun p : ℝ³ => ‖(((2 * Real.pi)⁻¹ : ℝ)) • p‖ ^ 2 *
      ‖(𝓕 F) ((((2 * Real.pi)⁻¹ : ℝ)) • p)‖ ^ 2) :=
    hIntξ.comp_smul (R := (2 * Real.pi)⁻¹) (by positivity)
  have hnorm : ∀ p : ℝ³, ‖p‖ ^ 2 * ‖(𝓕 F) ((((2 * Real.pi)⁻¹ : ℝ)) • p)‖ ^ 2
      = (2 * Real.pi) ^ 2 * (‖(((2 * Real.pi)⁻¹ : ℝ)) • p‖ ^ 2 *
          ‖(𝓕 F) ((((2 * Real.pi)⁻¹ : ℝ)) • p)‖ ^ 2) := by
    intro p
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹)]
    field_simp
  have hkft : ∀ p : ℝ³, kinFT (fun z : ℝ³ => (chiScale s z : ℂ) * (ψ z : ℂ)) p
      = (𝓕 F) ((((2 * Real.pi)⁻¹ : ℝ)) • p) := by
    intro p
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
    have hfun : (fun z : ℝ³ => (chiScale s z : ℂ) * (ψ z : ℂ)) = ⇑F := by
      funext z
      simp only [hF_coe]
      exact (Complex.ofReal_mul (chiScale s z) (ψ z)).symm
    rw [hfun, SchwartzMap.fourier_coe]
  refine (hInt2.const_mul ((2 * Real.pi) ^ 2)).congr (Eventually.of_forall (fun p => ?_))
  simp only [hnorm p, hkft p]

/-- Uniform bound on the fibre Dirichlet energy over the box `abox n s`. -/
theorem fibre_energy_bound {n : ℕ} {s : ℝ} (hs : 0 < s)
    {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (i : Fin (n + 1)) :
    ∃ C : ℝ, ∀ r ∈ abox n s,
      (∫ z in acube s, ∑ k : Fin 3,
        (fderiv ℝ (fun w : ℝ³ => chiScale s w * Φ (kcInsN n i (w, r))) z
          (kcStdBasis k)) ^ 2) ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_dirichlet_integrand hs hΦ i
  refine ⟨C * s ^ 3, fun r hr => ?_⟩
  have hmem : ∀ z : ℝ³, z ∈ acube s → kcInsN n i (z, r) ∈ abox (n + 1) s := by
    intro z hz j
    by_cases hj : j = i
    · rw [hj, kc_insN_apply_same]; exact hz
    · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
      rw [kc_insN_apply_succ]; exact hr j'
  have hpt : ∀ z : ℝ³, (∑ k : Fin 3,
      (fderiv ℝ (fun w : ℝ³ => chiScale s w * Φ (kcInsN n i (w, r))) z (kcStdBasis k)) ^ 2)
      = ∑ k : Fin 3, (fderiv ℝ (fun x : X (n + 1) => chiScale s (x i) * Φ x)
          (kcInsN n i (z, r)) (kcDir (n + 1) i k)) ^ 2 := by
    intro z
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [fderiv_slot_eq_fibre hs hΦ i r z k]
  have hchi : ContDiff ℝ ∞ (fun x : X (n + 1) => chiScale s (x i)) :=
    (chiScale_contDiff (ne_of_gt hs)).comp (by fun_prop)
  have hA : ContDiff ℝ ∞ (fun x : X (n + 1) => chiScale s (x i) * Φ x) := hchi.mul hΦ
  have hfd : Continuous (fun x : X (n + 1) => fderiv ℝ (fun x : X (n + 1) =>
      chiScale s (x i) * Φ x) x) := hA.continuous_fderiv (by simp)
  have hcont : Continuous (fun z : ℝ³ => ∑ k : Fin 3,
      (fderiv ℝ (fun x : X (n + 1) => chiScale s (x i) * Φ x)
        (kcInsN n i (z, r)) (kcDir (n + 1) i k)) ^ 2) :=
    continuous_finsetSum _ (fun k _ => ((hfd.comp
      ((kcInsN_cont i).comp (continuous_id.prodMk continuous_const))).clm_apply
        continuous_const).pow 2)
  have hf_eq : (∫ z in acube s, ∑ k : Fin 3,
      (fderiv ℝ (fun w : ℝ³ => chiScale s w * Φ (kcInsN n i (w, r))) z (kcStdBasis k)) ^ 2)
      = ∫ z in acube s, ∑ k : Fin 3, (fderiv ℝ (fun x : X (n + 1) => chiScale s (x i) * Φ x)
          (kcInsN n i (z, r)) (kcDir (n + 1) i k)) ^ 2 :=
    integral_congr_ae (Eventually.of_forall (fun z => hpt z))
  rw [hf_eq]
  calc (∫ z in acube s, ∑ k : Fin 3, (fderiv ℝ (fun x : X (n + 1) => chiScale s (x i) * Φ x)
          (kcInsN n i (z, r)) (kcDir (n + 1) i k)) ^ 2)
      ≤ ∫ z in acube s, C := by
        apply integral_mono_ae
        · exact ContinuousOn.integrableOn_compact (acube_compact hs) hcont.continuousOn
        · exact integrableOn_const (by rw [acube_volume s (le_of_lt hs)]; exact ENNReal.ofReal_lt_top.ne)
        · filter_upwards [ae_restrict_mem (acube_measurable s)] with z hz
          exact hC (kcInsN n i (z, r)) (hmem z hz)
    _ = C * s ^ 3 := by
        rw [setIntegral_const, Measure.real, acube_volume s (le_of_lt hs),
          ENNReal.toReal_ofReal (by positivity)]
        ring

/-! ## 6. Fubini: swap the `p`-integral with the fibre integral -/

/-- **Fubini for the fibre kinetic energy.**  The `p`-integral of the fibre kinetic energy
factors into the fibre integral of the `p`-integral; the integrability input is the uniform
bound `fibre_energy_bound` combined with the pointwise Plancherel identity `fibre_energy`. -/
theorem swap_p_r_energy {n : ℕ} {s : ℝ} (hs : 0 < s)
    {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (i : Fin (n + 1)) :
    (∫ p : ℝ³, ‖p‖ ^ 2 * (∫ r : X n, ‖kinFT
          (fun z : ℝ³ => (chiScale s z : ℂ) * (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2
          ∂((volume : Measure (X n)).restrict (abox n s))))
      = ∫ r : X n,
          (∫ p : ℝ³, ‖p‖ ^ 2 * ‖kinFT
            (fun z : ℝ³ => (chiScale s z : ℂ) * (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2)
          ∂((volume : Measure (X n)).restrict (abox n s)) := by
  set ν : Measure (X n) := (volume : Measure (X n)).restrict (abox n s) with hν
  obtain ⟨C, hC⟩ := fibre_energy_bound hs hΦ i
  let f : ℝ³ → X n → ℝ := fun p r => ‖p‖ ^ 2 * ‖kinFT
      (fun z : ℝ³ => (chiScale s z : ℂ) * (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2
  have hf_nonneg : ∀ p r, 0 ≤ f p r := fun p r => by positivity
  have hconv : ∀ r : X n, (∫ p : ℝ³, f p r)
      = (2 * Real.pi) ^ 3 * (∫ z in acube s, ∑ k : Fin 3,
          (fderiv ℝ (fun w : ℝ³ => chiScale s w * Φ (kcInsN n i (w, r))) z
            (kcStdBasis k)) ^ 2) := by
    intro r
    have hψ : ContDiff ℝ ∞ (fun z : ℝ³ => Φ (kcInsN n i (z, r))) :=
      hΦ.comp (contDiff_kcInsN_right i r)
    have hen := fibre_energy hs hψ
    have h1 : (∫ p : ℝ³, f p r) = (2 * Real.pi) ^ 3 *
        (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, f p r)) := by
      rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    have h2 : (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, f p r))
        = (∫ z in acube s, ∑ k : Fin 3, (fderiv ℝ (fun w : ℝ³ => chiScale s w *
            Φ (kcInsN n i (w, r))) z (kcStdBasis k)) ^ 2) := by
      simpa only [f] using hen
    rw [h1, h2]
  have hmeas : AEStronglyMeasurable (Function.uncurry f) (volume.prod ν) := by
    have hjoint : AEStronglyMeasurable (fun w : (ℝ³ × X n) × ℝ³ =>
        Complex.exp (-(Complex.I * (inner ℝ w.1.1 w.2 : ℂ))) *
          ((chiScale s w.2 : ℂ) * (Φ (kcInsN n i (w.2, w.1.2)) : ℂ)))
        ((volume.prod ν).prod volume) := by
      have h1 : Continuous (fun w : (ℝ³ × X n) × ℝ³ =>
          Complex.exp (-(Complex.I * (inner ℝ w.1.1 w.2 : ℂ)))) :=
        Complex.continuous_exp.comp ((continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_inner.comp
            (continuous_fst.fst.prodMk continuous_snd)))).neg)
      have h2 : Continuous (fun w : (ℝ³ × X n) × ℝ³ => (chiScale s w.2 : ℂ)) :=
        Complex.continuous_ofReal.comp ((chiScale_continuous s).comp continuous_snd)
      have h3 : Continuous (fun w : (ℝ³ × X n) × ℝ³ => (Φ (kcInsN n i (w.2, w.1.2)) : ℂ)) :=
        Complex.continuous_ofReal.comp (hΦ.continuous.comp
          ((kcInsN_cont i).comp (continuous_snd.prodMk continuous_fst.snd)))
      exact ((h1.mul (h2.mul h3))).stronglyMeasurable.aestronglyMeasurable
    have hK : AEStronglyMeasurable (fun q : ℝ³ × X n => ∫ z : ℝ³,
        Complex.exp (-(Complex.I * (inner ℝ q.1 z : ℂ))) *
          ((chiScale s z : ℂ) * (Φ (kcInsN n i (z, q.2)) : ℂ))) (volume.prod ν) :=
      hjoint.integral_prod_right'
    have h2 : AEStronglyMeasurable (fun q : ℝ³ × X n => ‖q.1‖ ^ 2) (volume.prod ν) :=
      ((continuous_norm.comp continuous_fst).pow 2).aestronglyMeasurable
    have hgoal : AEStronglyMeasurable (fun q : ℝ³ × X n => ‖q.1‖ ^ 2 *
        ‖∫ z : ℝ³, Complex.exp (-(Complex.I * (inner ℝ q.1 z : ℂ))) *
          ((chiScale s z : ℂ) * (Φ (kcInsN n i (z, q.2)) : ℂ))‖ ^ 2) (volume.prod ν) :=
      h2.mul (hK.norm.pow 2)
    exact hgoal
  have hint : Integrable (Function.uncurry f) (volume.prod ν) := by
    refine Commons.Measure.Integral.integrable_uncurry_of_lintegral_le_sfinite (μ := volume)
      (ν := ν) (g := fun _ : X n => ENNReal.ofReal ((2 * Real.pi) ^ 3 * max C 0)) hmeas ?_ ?_
    · rw [lintegral_const]
      have hfin : ν Set.univ < ⊤ := by
        rw [hν, Measure.restrict_apply_univ]
        exact abox_lt_top n s (le_of_lt hs)
      exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin).ne
    · filter_upwards [ae_restrict_mem (abox_measurable n s)] with r hr
      have hψ : ContDiff ℝ ∞ (fun z : ℝ³ => Φ (kcInsN n i (z, r))) :=
        hΦ.comp (contDiff_kcInsN_right i r)
      have hInt : Integrable (fun p : ℝ³ => f p r) volume :=
        by simpa only [f] using integrable_kinFT_energy hs hψ
      have hnn : 0 ≤ᵐ[volume] (fun p : ℝ³ => f p r) :=
        Eventually.of_forall (fun p => hf_nonneg p r)
      have hcongr : (∫⁻ p, ENNReal.ofReal ‖f p r‖ ∂volume)
          = ∫⁻ p, ENNReal.ofReal (f p r) ∂volume :=
        lintegral_congr (fun p => by rw [Real.norm_of_nonneg (hf_nonneg p r)])
      rw [hcongr, ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn]
      apply ENNReal.ofReal_le_ofReal
      rw [hconv r]
      exact mul_le_mul_of_nonneg_left (le_trans (hC r hr) (le_max_left C 0)) (by positivity)
  have hL : (∫ p : ℝ³, ‖p‖ ^ 2 * (∫ r : X n, ‖kinFT
          (fun z : ℝ³ => (chiScale s z : ℂ) * (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2 ∂ν) ∂volume)
      = ∫ p : ℝ³, ∫ r : X n, f p r ∂ν ∂volume := by
    refine integral_congr_ae (Eventually.of_forall (fun p => ?_))
    simp only [f]
    rw [← MeasureTheory.integral_const_mul]
  rw [hL, MeasureTheory.integral_integral_swap (μ := volume) (ν := ν) hint]

/-! ## 7. The fibre Plancherel identity, per slot -/

theorem T0Form_slot_eq_dirichlet {n : ℕ} {s : ℝ} (hs : 0 < s)
    {Ψ : (Fin (n + 1) → EuclideanSpace ℝ (Fin 3)) → ℝ} (hΨ : ContDiff ℝ (⊤ : ENat) Ψ)
    (hsupp : tsupport Ψ ⊆ Submission.BoseGases.abox (n + 1) s) (i : Fin (n + 1)) :
    ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3), ‖p‖ ^ 2 *
        ((s ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (n + 1) s,
          ‖Submission.BoseGases.rawSlotAmp s p (Submission.BoseGases.aQ s i Ψ) i x‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox (n + 1) s, ∑ k : Fin 3,
          (fderiv ℝ (fun z : Fin (n + 1) → EuclideanSpace ℝ (Fin 3) =>
              Submission.BoseGases.chiScale s (z i) * Submission.BoseGases.aQ s i Ψ z) x
            (Submission.BoseGases.kcDir (n + 1) i k)) ^ 2 := by
  set Φ : X (n + 1) → ℝ := aQ s i Ψ with hΦdef
  have hΦs : ContDiff ℝ ∞ Φ := contDiff_aQ hs i hΨ
  have hΦc : Continuous Φ := hΦs.continuous
  -- (1) peel the `x`-integral for each `p`
  have step1 : ∀ p : ℝ³,
      (s ^ 3)⁻¹ * (∫ x in abox (n + 1) s, ‖rawSlotAmp s p Φ i x‖ ^ 2)
        = ∫ r : X n, ‖kinFT (fun z : ℝ³ => (chiScale s z : ℂ) *
            (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2
            ∂((volume : Measure (X n)).restrict (abox n s)) := by
    intro p
    have hInt : IntegrableOn (fun x : X (n + 1) => ‖rawSlotAmp s p Φ i x‖ ^ 2)
        (abox (n + 1) s) :=
      ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs)
        ((((continuous_rawSlotAmp hs p hΦc i).norm).pow 2)).continuousOn
    rw [abox_integral_peel (i := i) (F := fun x => ‖rawSlotAmp s p Φ i x‖ ^ 2) hInt]
    have hinner : ∀ r : X n,
        (∫ y in acube s, ‖rawSlotAmp s p Φ i (kcInsN n i (y, r))‖ ^ 2)
          = s ^ 3 * ‖kinFT (fun z : ℝ³ => (chiScale s z : ℂ) *
              (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2 := by
      intro r
      have hpt : ∀ y : ℝ³, ‖rawSlotAmp s p Φ i (kcInsN n i (y, r))‖ ^ 2
          = ‖kinFT (fun z : ℝ³ => (chiScale s z : ℂ) *
              (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2 := by
        intro y
        have hfun : (fun z : ℝ³ => (chiScale s z : ℂ) * (Φ (Function.update (kcInsN n i (y, r)) i z) : ℂ))
            = (fun z : ℝ³ => (chiScale s z : ℂ) * (Φ (kcInsN n i (z, r)) : ℂ)) := by
          funext z; rw [update_kcInsN]
        rw [rawSlotAmp_eq_kinFT hs p Φ i (kcInsN n i (y, r)), hfun]
      rw [integral_congr_ae (Eventually.of_forall hpt), setIntegral_const,
        show Measure.real (volume : Measure ℝ³) (acube s) = s ^ 3 from by
          rw [Measure.real, acube_volume s (le_of_lt hs), ENNReal.toReal_ofReal (by positivity)],
        smul_eq_mul]
    rw [integral_congr_ae (Eventually.of_forall hinner), ← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with r
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity : s ^ 3 ≠ 0), one_mul]
  -- (2) peel the RHS
  have hRpeel : (∫ x in abox (n + 1) s, ∑ k : Fin 3,
        (fderiv ℝ (fun z : X (n + 1) => chiScale s (z i) * Φ z) x
          (kcDir (n + 1) i k)) ^ 2)
      = ∫ r : X n, (∫ y in acube s, ∑ k : Fin 3,
          (fderiv ℝ (fun w : ℝ³ => chiScale s w * Φ (kcInsN n i (w, r))) y
            (kcStdBasis k)) ^ 2)
          ∂((volume : Measure (X n)).restrict (abox n s)) := by
    have hchi : ContDiff ℝ ∞ (fun x : X (n + 1) => chiScale s (x i)) :=
      (chiScale_contDiff (ne_of_gt hs)).comp (by fun_prop)
    have hA : ContDiff ℝ ∞ (fun z : X (n + 1) => chiScale s (z i) * Φ z) := hchi.mul hΦs
    have hfd : Continuous (fun x : X (n + 1) => fderiv ℝ (fun z : X (n + 1) =>
        chiScale s (z i) * Φ z) x) := hA.continuous_fderiv (by simp)
    have hInt : IntegrableOn (fun x : X (n + 1) => ∑ k : Fin 3,
        (fderiv ℝ (fun z : X (n + 1) => chiScale s (z i) * Φ z) x
          (kcDir (n + 1) i k)) ^ 2) (abox (n + 1) s) :=
      ContinuousOn.integrableOn_compact (abox_compact (n + 1) hs)
        (continuous_finsetSum _ (fun k _ =>
          ((hfd.clm_apply continuous_const).pow 2))).continuousOn
    rw [abox_integral_peel (i := i) (F := fun x : X (n + 1) => ∑ k : Fin 3,
      (fderiv ℝ (fun z : X (n + 1) => chiScale s (z i) * Φ z) x
        (kcDir (n + 1) i k)) ^ 2) hInt]
    refine integral_congr_ae (Eventually.of_forall (fun r => ?_))
    refine integral_congr_ae (Eventually.of_forall (fun y => ?_))
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [fderiv_slot_eq_fibre hs hΦs i r y k]
  -- (3) assemble
  have hL : ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ‖p‖ ^ 2 *
        ((s ^ 3)⁻¹ * ∫ x in abox (n + 1) s, ‖rawSlotAmp s p Φ i x‖ ^ 2)
      = ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, ‖p‖ ^ 2 * (∫ r : X n, ‖kinFT
            (fun z : ℝ³ => (chiScale s z : ℂ) * (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2
            ∂((volume : Measure (X n)).restrict (abox n s)))) := by
    congr 1
    refine integral_congr_ae (Eventually.of_forall (fun p => ?_))
    simp only [step1 p]
  rw [hL, swap_p_r_energy hs hΦs i, hRpeel]
  have hpt : ∀ r : X n, (∫ p : ℝ³, ‖p‖ ^ 2 * ‖kinFT
        (fun z : ℝ³ => (chiScale s z : ℂ) * (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2)
      = (2 * Real.pi) ^ 3 * (∫ y in acube s, ∑ k : Fin 3,
          (fderiv ℝ (fun w : ℝ³ => chiScale s w * Φ (kcInsN n i (w, r))) y
            (kcStdBasis k)) ^ 2) := by
    intro r
    have hψ : ContDiff ℝ ∞ (fun z : ℝ³ => Φ (kcInsN n i (z, r))) :=
      hΦs.comp (contDiff_kcInsN_right i r)
    have hen := fibre_energy hs hψ
    have h1 : (∫ p : ℝ³, ‖p‖ ^ 2 * ‖kinFT (fun z : ℝ³ => (chiScale s z : ℂ) *
        (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2)
        = (2 * Real.pi) ^ 3 * (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, ‖p‖ ^ 2 *
            ‖kinFT (fun z : ℝ³ => (chiScale s z : ℂ) * (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2)) := by
      rw [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
    have h2 : (((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, ‖p‖ ^ 2 *
            ‖kinFT (fun z : ℝ³ => (chiScale s z : ℂ) * (Φ (kcInsN n i (z, r)) : ℂ)) p‖ ^ 2))
        = (∫ y in acube s, ∑ k : Fin 3, (fderiv ℝ (fun w : ℝ³ => chiScale s w *
            Φ (kcInsN n i (w, r))) y (kcStdBasis k)) ^ 2) := by
      simpa only using hen
    rw [h1, h2]
  rw [integral_congr_ae (Eventually.of_forall hpt), ← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards with r
  rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

end Work.SmallBoxBridge.Fourier
