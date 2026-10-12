import Mathlib
import Submission.Commons.Analysis.Integral.radial_integral_three_Ioi
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.corrAuxKin` — the analytic inputs of `corrCutWordsSharp`

Three auxiliary lemmas used by `Work.BoseFixB1S.corrCutWordsSharp`:

* `norm_kinFT_mul_norm_pow_le` — `n`-fold integration by parts for the `p`-convention Fourier
  transform `kinFT`: `‖p‖^n ‖kinFT f p‖ ≤ (2π)^n ∫ ‖iteratedFDeriv ℝ n f‖`.
* `exists_iteratedFDeriv_chiB_L1_le` — the `L¹` norm of the `N`-th order derivative of the sliding
  small-box window `chiB ℓ d u` is at most `C N · ℓ³ (ℓd)^{-N}`, uniformly in the shift `u`.
* `integral_norm_tail_pow` — the exterior integral `∫_{‖p‖>c} ‖p‖^{-n} = 4π/(n-3)·c^{3-n}` (`n ≥ 4`).

All three are sorry-free.  This is the "decay/scale" input that turns the *sharp* bound
`∫ [‖p‖−c]_+² ‖𝓕χ_{B(u)}‖² ≤ C ℓ^{-2}` (with `c = (dsℓ)^{-1}`) into a finite computation: the
window `χ_{B(u)}` is `C^∞` with compact support, so its Fourier transform decays faster than any
polynomial, and the `(1/ℓ)`- and `(1/(ℓd))`-scalings of its `N`-th derivative are exactly what the
parameter comparison of the main file consumes.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Real

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Integration by parts for `kinFT` -/

theorem norm_kinFT_mul_norm_pow_le (n : ℕ) {f : E3 → ℂ}
    (hf : ContDiff ℝ n f)
    (hint : ∀ k : ℕ, k ≤ n → MeasureTheory.Integrable (iteratedFDeriv ℝ k f))
    (p : E3) :
    ‖p‖ ^ n * ‖Submission.BoseGases.kinFT f p‖
      ≤ (2 * Real.pi) ^ n * ∫ z, ‖iteratedFDeriv ℝ n f z‖ := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    simp only [pow_zero, one_mul]
    rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
    calc ‖FourierTransform.fourier f ((2 * Real.pi)⁻¹ • p)‖
        ≤ ∫ z, ‖f z‖ :=
          VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
            (innerₗ E3) f _
      _ = ∫ z, ‖iteratedFDeriv ℝ 0 f z‖ := by simp [norm_iteratedFDeriv_zero]
  · rcases eq_or_ne p 0 with rfl | hp
    · rw [norm_zero, zero_pow hn.ne', zero_mul]
      exact mul_nonneg (pow_nonneg (by positivity) n) (integral_nonneg fun z => norm_nonneg _)
    · have hπ1 : (1:ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      set ξ : E3 := (2 * Real.pi)⁻¹ • p with hξdef
      set v : E3 := (‖p‖)⁻¹ • p with hvdef
      have hpn : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp
      have hv1 : ‖v‖ = 1 := by
        rw [hvdef, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg p))]
        exact inv_mul_cancel₀ hpn
      have hξv : inner ℝ ξ v = (2 * Real.pi)⁻¹ * ‖p‖ := by
        rw [hξdef, hvdef, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      have hξvabs : 2 * Real.pi * |inner ℝ ξ v| = ‖p‖ := by
        rw [hξv, abs_of_nonneg (by positivity)]
        field_simp
      have hf' : ContDiff ℝ ((n : ℕ∞)) f := hf
      have hint' : ∀ k : ℕ, (k : ℕ∞) ≤ ((n : ℕ∞)) →
          MeasureTheory.Integrable (iteratedFDeriv ℝ k f) := by
        intro k hk
        exact hint k (by exact_mod_cast hk)
      have hfourier : FourierTransform.fourier (iteratedFDeriv ℝ n f) =
          fun w => VectorFourier.fourierPowSMulRight (-innerSL ℝ)
            (FourierTransform.fourier f) w n :=
        Real.fourier_iteratedFDeriv (N := ((n : ℕ∞))) (f := f) (n := n) hf' hint' le_rfl
      have hn_int : MeasureTheory.Integrable (iteratedFDeriv ℝ n f) := hint n le_rfl
      have h1 : (FourierTransform.fourier (iteratedFDeriv ℝ n f) ξ) (fun _ : Fin n => v)
          = (VectorFourier.fourierPowSMulRight (-innerSL ℝ) (FourierTransform.fourier f) ξ n)
              (fun _ : Fin n => v) := by
        rw [congrFun hfourier ξ]
      rw [Real.fourier_continuousMultilinearMap_apply hn_int,
        VectorFourier.fourierPowSMulRight_apply] at h1
      have hprod : (∏ i : Fin n, ((-innerSL ℝ) ξ) v) = (-(inner ℝ ξ v)) ^ n := by simp
      have hnormeq : ‖FourierTransform.fourier
            (fun x => (iteratedFDeriv ℝ n f x) (fun _ : Fin n => v)) ξ‖
          = (2 * Real.pi * |inner ℝ ξ v|) ^ n * ‖FourierTransform.fourier f ξ‖ := by
        rw [h1, hprod, norm_smul, norm_smul, norm_pow, norm_pow]
        rw [show ‖(-(2 * Real.pi * Complex.I) : ℂ)‖ = 2 * Real.pi by
          simp only [norm_neg, norm_mul, Complex.norm_I, mul_one]
          norm_num
          try positivity]
        simp only [Real.norm_eq_abs, abs_neg]
        ring
      rw [Work.SmallBoxBridge.Resolve.kinFT_eq_fourier]
      calc ‖p‖ ^ n * ‖FourierTransform.fourier f ξ‖
          = (2 * Real.pi * |inner ℝ ξ v|) ^ n * ‖FourierTransform.fourier f ξ‖ := by rw [hξvabs]
        _ = ‖FourierTransform.fourier
              (fun x => (iteratedFDeriv ℝ n f x) (fun _ : Fin n => v)) ξ‖ := hnormeq.symm
        _ ≤ ∫ x, ‖(iteratedFDeriv ℝ n f x) (fun _ : Fin n => v)‖ :=
            VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume
              (innerₗ E3) (fun x => (iteratedFDeriv ℝ n f x) (fun _ : Fin n => v)) ξ
        _ ≤ ∫ x, ‖iteratedFDeriv ℝ n f x‖ := by
            apply integral_mono_of_nonneg
            · exact Filter.Eventually.of_forall fun x => norm_nonneg _
            · exact hn_int.norm
            · exact Filter.Eventually.of_forall fun x => by
                calc ‖(iteratedFDeriv ℝ n f x) (fun _ : Fin n => v)‖
                    ≤ ‖iteratedFDeriv ℝ n f x‖ * ∏ i : Fin n, ‖v‖ :=
                      ContinuousMultilinearMap.le_opNorm _ _
                  _ = ‖iteratedFDeriv ℝ n f x‖ := by
                      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hv1, one_pow,
                        mul_one]
        _ ≤ (2 * Real.pi) ^ n * ∫ x, ‖iteratedFDeriv ℝ n f x‖ := by
            have h1' : (1:ℝ) ≤ (2 * Real.pi) ^ n := one_le_pow₀ hπ1
            calc ∫ x, ‖iteratedFDeriv ℝ n f x‖
                = 1 * ∫ x, ‖iteratedFDeriv ℝ n f x‖ := (one_mul _).symm
              _ ≤ (2 * Real.pi) ^ n * ∫ x, ‖iteratedFDeriv ℝ n f x‖ :=
                  mul_le_mul_of_nonneg_right h1' (integral_nonneg fun x => norm_nonneg _)

/-! ## 2. The derivative bounds of the sliding window `chiB` -/

/-- The chain rule for the rescaled bump: `‖D^k chiScale s‖ ≤ A k · s^{-k}`. -/
private lemma corrAux_chiScale_iteratedFDeriv_le (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k)
    (hAb : ∀ (k : ℕ) (z : E3), ‖iteratedFDeriv ℝ k Submission.BoseGases.chi z‖ ≤ A k) :
    ∀ (k : ℕ) (s : ℝ), 0 < s → ∀ z : E3,
      ‖iteratedFDeriv ℝ k (Submission.BoseGases.chiScale s) z‖ ≤ A k * (s ^ k)⁻¹ := by
  intro k s hs z
  have hcd : ContDiff ℝ k Submission.BoseGases.chi := Submission.BoseGases.chi_contDiff_nat k
  have hshape : Submission.BoseGases.chiScale s =
      Submission.BoseGases.chi ∘ ((s⁻¹) • ContinuousLinearMap.id ℝ E3) := by
    ext w; simp [Submission.BoseGases.chiScale]
  have hcomp := ContinuousLinearMap.iteratedFDeriv_comp_right
    (g := (s⁻¹) • ContinuousLinearMap.id ℝ E3) (f := Submission.BoseGases.chi) hcd z
    (i := k) (hi := le_rfl)
  rw [hshape, hcomp]
  have h2 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (g := iteratedFDeriv ℝ k Submission.BoseGases.chi ((s⁻¹) • z))
    (f := fun _ : Fin k => ((s⁻¹) • ContinuousLinearMap.id ℝ E3 : E3 →L[ℝ] E3))
  have h3 : ‖((s⁻¹) • ContinuousLinearMap.id ℝ E3 : E3 →L[ℝ] E3)‖ = s⁻¹ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), ContinuousLinearMap.norm_id, mul_one]
  refine le_trans h2 ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, h3]
  have h4 : (0:ℝ) ≤ s⁻¹ ^ k := by positivity
  calc ‖iteratedFDeriv ℝ k Submission.BoseGases.chi (s⁻¹ • z)‖ * s⁻¹ ^ k
      ≤ A k * s⁻¹ ^ k := mul_le_mul_of_nonneg_right (hAb k _) h4
    _ = A k * (s ^ k)⁻¹ := by rw [inv_pow]

/-- The complexified version of `corrAux_chiScale_iteratedFDeriv_le`. -/
private lemma corrAux_chiScaleC_iteratedFDeriv_le (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k)
    (hAb : ∀ (k : ℕ) (z : E3), ‖iteratedFDeriv ℝ k Submission.BoseGases.chi z‖ ≤ A k) :
    ∀ (k : ℕ) (s : ℝ), 0 < s → ∀ z : E3,
      ‖iteratedFDeriv ℝ k (fun z => (Submission.BoseGases.chiScale s z : ℂ)) z‖
        ≤ A k * (s ^ k)⁻¹ := by
  intro k s hs z
  have hreal : ‖iteratedFDeriv ℝ k (Submission.BoseGases.chiScale s) z‖ ≤ A k * (s ^ k)⁻¹ :=
    corrAux_chiScale_iteratedFDeriv_le A hA hAb k s hs z
  have hcd : ContDiffAt ℝ k (Submission.BoseGases.chiScale s) z :=
    ((Submission.BoseGases.chiScale_contDiff (ne_of_gt hs)).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt
  have hcle := ContinuousLinearMap.iteratedFDeriv_comp_left
    (g := Complex.ofRealCLM) (f := Submission.BoseGases.chiScale s) hcd (i := k) (hi := le_rfl)
  have hfun : (fun z : E3 => (Submission.BoseGases.chiScale s z : ℂ))
      = Complex.ofRealCLM ∘ Submission.BoseGases.chiScale s := rfl
  rw [hfun, hcle]
  refine le_trans (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _) ?_
  rw [Complex.ofRealCLM_norm, one_mul]
  exact hreal

/-- Leibniz at order `N` for `chiB = chiScale ℓ · chiScale (ℓd)(· − (ℓd)•u)`. -/
private lemma corrAux_chiB_iteratedFDeriv_le (A : ℕ → ℝ) (hA : ∀ k, 0 ≤ A k)
    (hscale : ∀ (k : ℕ) (s : ℝ), 0 < s → ∀ z : E3,
        ‖iteratedFDeriv ℝ k (fun z => (Submission.BoseGases.chiScale s z : ℂ)) z‖
          ≤ A k * (s^k)⁻¹) :
    ∀ (N : ℕ) (ℓ d : ℝ), 0 < ℓ → 0 < d → d ≤ 1 → ∀ (u z : E3),
      ‖iteratedFDeriv ℝ N (fun z => (Submission.BoseGases.chiB ℓ d u z : ℂ)) z‖
        ≤ ∑ j ∈ Finset.range (N+1), (N.choose j : ℝ) * (A j * (ℓ^j)⁻¹)
            * (A (N-j) * ((ℓ*d)^(N-j))⁻¹) := by
  intro N ℓ d hℓ hd hd1 u z
  have hℓd : 0 < ℓ*d := mul_pos hℓ hd
  have hfun : (fun z => (Submission.BoseGases.chiB ℓ d u z : ℂ))
      = fun z => (Submission.BoseGases.chiScale ℓ z : ℂ) *
          (Submission.BoseGases.chiScale (ℓ*d) (z - (ℓ*d)•u) : ℂ) := by
    funext z; simp [Submission.BoseGases.chiB]
  rw [hfun]
  have hf : ContDiff ℝ (⊤ : ℕ∞) (fun z : E3 => (Submission.BoseGases.chiScale ℓ z : ℂ)) :=
    (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuousLinearMap_comp
      Complex.ofRealCLM
  have hg : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : E3 => (Submission.BoseGases.chiScale (ℓ*d) (z - (ℓ*d)•u) : ℂ)) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : E3 => (Submission.BoseGases.chiScale (ℓ*d) z : ℂ)) :=
      (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓd)).continuousLinearMap_comp
        Complex.ofRealCLM
    exact h1.comp (by fun_prop)
  refine (norm_iteratedFDeriv_mul_le hf hg z (WithTop.coe_le_coe.mpr le_top)).trans ?_
  apply Finset.sum_le_sum
  intro j hj
  rw [Finset.mem_range] at hj
  have h1 : ‖iteratedFDeriv ℝ j (fun z : E3 => (Submission.BoseGases.chiScale ℓ z : ℂ)) z‖
      ≤ A j * (ℓ^j)⁻¹ := hscale j ℓ hℓ z
  have h2 : ‖iteratedFDeriv ℝ (N-j)
        (fun z : E3 => (Submission.BoseGases.chiScale (ℓ*d) (z - (ℓ*d)•u) : ℂ)) z‖
      ≤ A (N-j) * ((ℓ*d)^(N-j))⁻¹ := by
    have hsub := iteratedFDeriv_comp_sub (𝕜 := ℝ) (n := N-j)
      (f := fun w : E3 => (Submission.BoseGases.chiScale (ℓ*d) w : ℂ)) ((ℓ*d)•u) z
    rw [hsub]
    exact hscale (N-j) (ℓ*d) hℓd _
  have hnn1 : (0:ℝ) ≤ A j * (ℓ^j)⁻¹ :=
    mul_nonneg (hA j) (inv_nonneg.mpr (pow_nonneg hℓ.le j))
  have hc : (0:ℝ) ≤ (N.choose j : ℝ) := by positivity
  calc (N.choose j : ℝ) * ‖iteratedFDeriv ℝ j
          (fun z : E3 => (Submission.BoseGases.chiScale ℓ z : ℂ)) z‖
        * ‖iteratedFDeriv ℝ (N-j)
          (fun z : E3 => (Submission.BoseGases.chiScale (ℓ*d) (z - (ℓ*d)•u) : ℂ)) z‖
      = ((N.choose j : ℝ) * ‖iteratedFDeriv ℝ j
            (fun z : E3 => (Submission.BoseGases.chiScale ℓ z : ℂ)) z‖)
        * ‖iteratedFDeriv ℝ (N-j)
            (fun z : E3 => (Submission.BoseGases.chiScale (ℓ*d) (z - (ℓ*d)•u) : ℂ)) z‖ := by
          ring
    _ ≤ ((N.choose j : ℝ) * (A j * (ℓ^j)⁻¹)) * (A (N-j) * ((ℓ*d)^(N-j))⁻¹) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left h1 hc
        · exact h2
        · exact norm_nonneg _
        · exact mul_nonneg hc hnn1
    _ = (N.choose j : ℝ) * (A j * (ℓ^j)⁻¹) * (A (N-j) * ((ℓ*d)^(N-j))⁻¹) := by ring

/-- `(ℓ^j)⁻¹ ((ℓd)^{N-j})⁻¹ ≤ ((ℓd)^N)⁻¹` for `d ≤ 1`. -/
private lemma corrAux_inv_pow_le {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1)
    (N j : ℕ) (hj : j ≤ N) :
    (ℓ^j)⁻¹ * ((ℓ*d)^(N-j))⁻¹ ≤ ((ℓ*d)^N)⁻¹ := by
  have hL : 0 < ℓ*d := mul_pos hℓ hd
  rw [← mul_inv]
  refine (inv_le_inv₀ (by positivity) (by positivity)).mpr ?_
  rw [show (ℓ*d)^N = (ℓ*d)^(N-j) * (ℓ*d)^j by rw [← pow_add]; congr 1; omega]
  have hle : (ℓ*d)^j ≤ ℓ^j := pow_le_pow_left₀ hL.le (by nlinarith [hd1, hℓ]) j
  calc (ℓ*d)^(N-j) * (ℓ*d)^j ≤ (ℓ*d)^(N-j) * ℓ^j :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = ℓ^j * (ℓ*d)^(N-j) := by ring

/-- The integral of `‖D^N F‖` is at most the sup bound times `ℓ³` when `F` is supported in
`acube ℓ`. -/
private lemma corrAux_integral_iteratedFDeriv_le (N : ℕ) (ℓ : ℝ) (hℓ : 0 < ℓ) {F : E3 → ℂ}
    {E : ℝ} (hpt : ∀ z, ‖iteratedFDeriv ℝ N F z‖ ≤ E)
    (hsub : Function.support F ⊆ Submission.BoseGases.acube ℓ) :
    ∫ z, ‖iteratedFDeriv ℝ N F z‖ ≤ E * ℓ^3 := by
  have hzero : ∀ z ∉ Submission.BoseGases.acube ℓ, iteratedFDeriv ℝ N F z = 0 := by
    intro z hz
    have hts : tsupport F ⊆ Submission.BoseGases.acube ℓ :=
      closure_minimal hsub (Submission.BoseGases.acube_isClosed ℓ)
    by_contra hne
    have h1 : z ∈ Function.support (iteratedFDeriv ℝ N F) := by
      simpa [Function.mem_support] using hne
    exact hz (hts (support_iteratedFDeriv_subset N h1))
  have hfin : volume (Submission.BoseGases.acube ℓ) < ⊤ := by
    rw [Submission.BoseGases.acube_volume ℓ hℓ.le]; exact ENNReal.ofReal_lt_top
  have h1 : ‖∫ z in Submission.BoseGases.acube ℓ, ‖iteratedFDeriv ℝ N F z‖‖ ≤
      E * volume.real (Submission.BoseGases.acube ℓ) :=
    norm_setIntegral_le_of_norm_le_const hfin (fun z _ => by
      rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hpt z)
  have hnn : 0 ≤ ∫ z in Submission.BoseGases.acube ℓ, ‖iteratedFDeriv ℝ N F z‖ :=
    setIntegral_nonneg (Submission.BoseGases.acube_measurable ℓ) (fun z _ => norm_nonneg _)
  rw [Real.norm_of_nonneg hnn] at h1
  have hreal : volume.real (Submission.BoseGases.acube ℓ) = ℓ^3 := by
    rw [Measure.real_def, Submission.BoseGases.acube_volume ℓ hℓ.le,
      ENNReal.toReal_ofReal (by positivity)]
  rw [hreal] at h1
  calc ∫ z, ‖iteratedFDeriv ℝ N F z‖
      = ∫ z in Submission.BoseGases.acube ℓ, ‖iteratedFDeriv ℝ N F z‖ :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun z hz => by rw [hzero z hz, norm_zero])).symm
    _ ≤ E * ℓ^3 := h1

/-- **`L¹` bound on the iterated derivatives of the sliding window.** -/
theorem exists_iteratedFDeriv_chiB_L1_le :
    ∃ C : ℕ → ℝ, (∀ N, 0 ≤ C N) ∧
      ∀ (N : ℕ) (ℓ d : ℝ), 0 < ℓ → 0 < d → d ≤ 1 → ∀ u : E3,
          ∫ z, ‖iteratedFDeriv ℝ N (fun z => (Submission.BoseGases.chiB ℓ d u z : ℂ)) z‖
            ≤ C N * (ℓ ^ 3 * ((ℓ * d) ^ N)⁻¹) := by
  obtain ⟨A, hA0, hAb⟩ := Submission.BoseGases.exists_iteratedFDeriv_chi_le
  refine ⟨fun N => ∑ j ∈ Finset.range (N+1), (N.choose j : ℝ) * A j * A (N-j), ?_, ?_⟩
  · intro N
    exact Finset.sum_nonneg fun j hj => mul_nonneg (mul_nonneg (by positivity) (hA0 j)) (hA0 (N-j))
  · intro N ℓ d hℓ hd hd1 u
    set E : ℝ := ∑ j ∈ Finset.range (N+1),
      (N.choose j : ℝ) * (A j * (ℓ^j)⁻¹) * (A (N-j) * ((ℓ*d)^(N-j))⁻¹) with hEdef
    have hpt : ∀ z : E3,
        ‖iteratedFDeriv ℝ N (fun z => (Submission.BoseGases.chiB ℓ d u z : ℂ)) z‖ ≤ E :=
      corrAux_chiB_iteratedFDeriv_le A hA0 (corrAux_chiScaleC_iteratedFDeriv_le A hA0 hAb)
        N ℓ d hℓ hd hd1 u
    have hsub : Function.support (fun z => (Submission.BoseGases.chiB ℓ d u z : ℂ)) ⊆
        Submission.BoseGases.acube ℓ := by
      intro z hz
      rw [Function.mem_support] at hz
      have hz' : Submission.BoseGases.chiB ℓ d u z ≠ 0 := by
        simpa [Complex.ofReal_eq_zero] using hz
      have h1 : Submission.BoseGases.chiScale ℓ z ≠ 0 := fun hh => hz' (by
        simp [Submission.BoseGases.chiB, hh])
      exact Submission.BoseGases.chiScale_mem_acube hℓ h1
    have hle : ∫ z, ‖iteratedFDeriv ℝ N (fun z => (Submission.BoseGases.chiB ℓ d u z : ℂ)) z‖
        ≤ E * ℓ^3 := corrAux_integral_iteratedFDeriv_le N ℓ hℓ hpt hsub
    refine hle.trans ?_
    have hstep : ∀ j ∈ Finset.range (N+1),
        (N.choose j : ℝ) * (A j * (ℓ^j)⁻¹) * (A (N-j) * ((ℓ*d)^(N-j))⁻¹) * ℓ^3
          ≤ (N.choose j : ℝ) * A j * A (N-j) * (ℓ^3 * ((ℓ*d)^N)⁻¹) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hjN : j ≤ N := by omega
      have hkey := corrAux_inv_pow_le hℓ hd hd1 N j hjN
      have hnn : (0:ℝ) ≤ (N.choose j : ℝ) * A j * A (N-j) * ℓ^3 :=
        mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (hA0 j)) (hA0 (N-j))) (by positivity)
      calc (N.choose j : ℝ) * (A j * (ℓ^j)⁻¹) * (A (N-j) * ((ℓ*d)^(N-j))⁻¹) * ℓ^3
          = ((N.choose j : ℝ) * A j * A (N-j) * ℓ^3) * ((ℓ^j)⁻¹ * ((ℓ*d)^(N-j))⁻¹) := by ring
        _ ≤ ((N.choose j : ℝ) * A j * A (N-j) * ℓ^3) * ((ℓ*d)^N)⁻¹ :=
            mul_le_mul_of_nonneg_left hkey hnn
        _ = (N.choose j : ℝ) * A j * A (N-j) * (ℓ^3 * ((ℓ*d)^N)⁻¹) := by ring
    calc E * ℓ^3
        = ∑ j ∈ Finset.range (N+1),
            (N.choose j : ℝ) * (A j * (ℓ^j)⁻¹) * (A (N-j) * ((ℓ*d)^(N-j))⁻¹) * ℓ^3 := by
          rw [hEdef, Finset.sum_mul]
      _ ≤ ∑ j ∈ Finset.range (N+1),
            (N.choose j : ℝ) * A j * A (N-j) * (ℓ^3 * ((ℓ*d)^N)⁻¹) :=
          Finset.sum_le_sum hstep
      _ = (∑ j ∈ Finset.range (N+1), (N.choose j : ℝ) * A j * A (N-j))
            * (ℓ^3 * ((ℓ*d)^N)⁻¹) := by
          rw [Finset.sum_mul]

/-! ## 3. The exterior integral of `‖p‖^{-n}` -/

/-- The exterior integral of `‖p‖^{-n}` in `ℝ³`: for `n ≥ 4` and `c > 0`,
`∫_{‖p‖>c} ‖p‖^{-n} = 4π/(n-3) · c^{3-n}`, and the integrand is integrable there. -/
theorem integral_norm_tail_pow (n : ℕ) (hn : 4 ≤ n) {c : ℝ} (hc : 0 < c) :
    MeasureTheory.IntegrableOn (fun p : E3 => ((‖p‖ : ℝ) ^ n)⁻¹) {p | c < ‖p‖}
    ∧ (∫ p : E3 in {p | c < ‖p‖}, ((‖p‖ : ℝ) ^ n)⁻¹)
        = 4 * Real.pi / ((n : ℝ) - 3) * c ^ ((3 : ℝ) - (n : ℝ)) := by
  refine ⟨?_, ?_⟩
  · have hms : MeasurableSet {p : E3 | c < ‖p‖} :=
      (isOpen_lt continuous_const continuous_norm).measurableSet
    rw [← MeasureTheory.integrable_indicator_iff hms]
    have hnR : (3:ℝ) < (n:ℝ) := by
      have : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
      linarith
    have hrank : ((Module.finrank ℝ E3 : ℕ) : ℝ) < (n:ℝ) := by
      have : Module.finrank ℝ E3 = 3 := by simp
      rw [this]; exact hnR
    have hG : Integrable (fun p : E3 => (1 + c⁻¹)^n * (1 + ‖p‖) ^ (-(n:ℝ))) volume :=
      (integrable_one_add_norm (μ := volume) (r := (n:ℝ)) hrank).const_mul _
    have hmeas : AEStronglyMeasurable (fun p : E3 => ((‖p‖ : ℝ) ^ n)⁻¹) volume := by
      apply Measurable.aestronglyMeasurable
      measurability
    refine MeasureTheory.Integrable.mono' hG (hmeas.indicator hms) ?_
    refine Filter.Eventually.of_forall fun p => ?_
    by_cases hp : p ∈ {p : E3 | c < ‖p‖}
    · rw [Set.indicator_of_mem hp]
      have hpc : c < ‖p‖ := hp
      have hp0 : 0 < ‖p‖ := lt_trans hc hpc
      have hnorm : ‖((‖p‖ : ℝ) ^ n)⁻¹‖ = ((‖p‖ : ℝ) ^ n)⁻¹ := by
        rw [Real.norm_of_nonneg]; positivity
      rw [hnorm]
      have hbase : 1 + ‖p‖ ≤ (1 + c⁻¹) * ‖p‖ := by
        have h1 : 1 ≤ ‖p‖ / c := by rw [le_div_iff₀ hc]; linarith [hpc]
        have h2 : (1 + c⁻¹) * ‖p‖ = ‖p‖ + ‖p‖ / c := by field_simp
        rw [h2]; linarith
      have hpown : (1 + ‖p‖) ^ n ≤ ((1 + c⁻¹) * ‖p‖) ^ n :=
        pow_le_pow_left₀ (by positivity) hbase n
      rw [mul_pow] at hpown
      have hgoal : (1 + ‖p‖) ^ n ≤ (1 + c⁻¹) ^ n * ‖p‖ ^ n := hpown
      have hrp : (1 + ‖p‖) ^ (-(n:ℝ)) = ((1 + ‖p‖) ^ n)⁻¹ := by
        rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
      rw [hrp, le_mul_inv_iff₀ (by positivity : (0:ℝ) < (1 + ‖p‖)^n),
        inv_mul_le_iff₀ (by positivity : (0:ℝ) < ‖p‖ ^ n)]
      linarith [hgoal]
    · rw [Set.indicator_of_notMem hp, norm_zero]
      positivity
  · rw [Commons.Analysis.Integral.radial_integral_three_Ioi
      (fun y : ℝ => ((y : ℝ) ^ n)⁻¹) hc.le]
    have hnR : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hpt : Set.EqOn (fun y : ℝ => y ^ 2 * ((y : ℝ) ^ n)⁻¹)
        (fun y : ℝ => y ^ ((2 : ℝ) - (n : ℝ))) (Set.Ioi c) := by
      intro y hy
      rw [Set.mem_Ioi] at hy
      have hy0 : 0 < y := lt_trans hc hy
      show y ^ 2 * ((y : ℝ) ^ n)⁻¹ = y ^ ((2 : ℝ) - (n : ℝ))
      have h1 : (y ^ 2 : ℝ) = y ^ ((2 : ℝ)) := by rw [← Real.rpow_natCast y 2]; norm_num
      have h2 : ((y : ℝ) ^ n)⁻¹ = y ^ (-(n : ℝ)) := by
        rw [← Real.rpow_natCast y n, Real.rpow_neg hy0.le]
      rw [h1, h2, ← Real.rpow_add hy0]
      ring_nf
    have key : (∫ y in Set.Ioi c, y ^ 2 * ((y : ℝ) ^ n)⁻¹)
        = -c ^ ((2 : ℝ) - (n : ℝ) + 1) / ((2 : ℝ) - (n : ℝ) + 1) := by
      rw [setIntegral_congr_fun measurableSet_Ioi hpt,
        integral_Ioi_rpow_of_lt (a := (2 : ℝ) - (n : ℝ)) (c := c) (by linarith) hc]
    rw [key]
    have h : (2 : ℝ) - (n : ℝ) + 1 = 3 - (n : ℝ) := by ring
    rw [h]
    have hn3 : (3 : ℝ) - (n : ℝ) ≠ 0 := by intro hh; linarith
    have hn3' : (n : ℝ) - 3 ≠ 0 := by intro hh; linarith
    field_simp
    ring

/-! ## 4. Tail domination: from a pointwise `‖p‖^{-n}` bound to an integral bound -/

/-- Every iterated derivative of a smooth compactly supported function on `ℝ³` is integrable. -/
theorem integrable_iteratedFDeriv_of_contDiff {f : E3 → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcs : HasCompactSupport f) (k : ℕ) :
    Integrable (iteratedFDeriv ℝ k f) :=
  (hf.continuous_iteratedFDeriv (WithTop.coe_le_coe.mpr le_top)).integrable_of_hasCompactSupport
    (hcs.iteratedFDeriv k)

/-- If `g` vanishes off `{‖p‖ > c}` and is bounded there by `A‖p‖^{-n}` (`n ≥ 4`, `c > 0`), then
`∫ g ≤ A·(4π/(n-3))·c^{3-n}`. -/
theorem integral_le_tail_bound {g : E3 → ℝ} {A c : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (n : ℕ) (hn : 4 ≤ n)
    (hbound : ∀ p, c < ‖p‖ → g p ≤ A * ((‖p‖ : ℝ) ^ n)⁻¹)
    (hzero : ∀ p, ¬ (c < ‖p‖) → g p = 0)
    (hgnonneg : ∀ p, 0 ≤ g p) :
    ∫ p, g p ≤ A * (4 * Real.pi / ((n:ℝ) - 3) * c ^ ((3:ℝ) - (n:ℝ))) := by
  have hms : MeasurableSet {p : E3 | c < ‖p‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  obtain ⟨hIntOn, hval⟩ := integral_norm_tail_pow n hn hc
  have hInt : Integrable ({p : E3 | c < ‖p‖}.indicator (fun p => ((‖p‖ : ℝ) ^ n)⁻¹)) :=
    (MeasureTheory.integrable_indicator_iff hms).mpr hIntOn
  have hIntA : Integrable (fun p : E3 => A * ({p : E3 | c < ‖p‖}.indicator
      (fun p => ((‖p‖ : ℝ) ^ n)⁻¹) p)) := hInt.const_mul A
  have hle : ∀ p, g p ≤ A * ({p : E3 | c < ‖p‖}.indicator (fun p => ((‖p‖ : ℝ) ^ n)⁻¹) p) := by
    intro p
    by_cases hp : p ∈ {p : E3 | c < ‖p‖}
    · rw [Set.indicator_of_mem hp]; exact hbound p hp
    · rw [hzero p hp, Set.indicator_of_notMem hp, mul_zero]
  have hmain := MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall hgnonneg)
    hIntA (Filter.Eventually.of_forall hle)
  rwa [MeasureTheory.integral_const_mul, MeasureTheory.integral_indicator hms, hval] at hmain

/-- If `g` vanishes off `{‖p‖ > c}` and is bounded there by `A‖p‖^{-n}` (`n ≥ 4`, `c > 0`), then
`g` is integrable. -/
theorem integrable_of_tail_bound {g : E3 → ℝ} {A c : ℝ} (hc : 0 < c) (hA : 0 ≤ A)
    (n : ℕ) (hn : 4 ≤ n)
    (hbound : ∀ p, c < ‖p‖ → g p ≤ A * ((‖p‖ : ℝ) ^ n)⁻¹)
    (hzero : ∀ p, ¬ (c < ‖p‖) → g p = 0)
    (hgnonneg : ∀ p, 0 ≤ g p) (hmeas : AEStronglyMeasurable g volume) :
    Integrable g := by
  have hms : MeasurableSet {p : E3 | c < ‖p‖} :=
    (isOpen_lt continuous_const continuous_norm).measurableSet
  obtain ⟨hIntOn, -⟩ := integral_norm_tail_pow n hn hc
  have hInt : Integrable ({p : E3 | c < ‖p‖}.indicator (fun p => ((‖p‖ : ℝ) ^ n)⁻¹)) :=
    (MeasureTheory.integrable_indicator_iff hms).mpr hIntOn
  have hIntA : Integrable (fun p : E3 => A * ({p : E3 | c < ‖p‖}.indicator
      (fun p => ((‖p‖ : ℝ) ^ n)⁻¹) p)) := hInt.const_mul A
  refine MeasureTheory.Integrable.mono' hIntA hmeas (Filter.Eventually.of_forall fun p => ?_)
  by_cases hp : p ∈ {p : E3 | c < ‖p‖}
  · rw [Set.indicator_of_mem hp, Real.norm_of_nonneg (hgnonneg p)]
    exact hbound p hp
  · rw [hzero p hp, Set.indicator_of_notMem hp, mul_zero, norm_zero]

end Work.BoseFixB1S
