/-
# Lemma `iw-prop`(i): off-diagonal decay of the Ionescu--Wainger projections

Krause--Mirek--Tao, Ann. of Math. 195 (2022), Lemma `iw-prop`(i), second half: for good major
arcs `(l,k)`, every `1 < q < ∞` and every `M`, the projection `Π_{≤l,≤k}` decays off the support
of its input:

`‖ Π_{≤l,≤k} f ‖_{ℓ^q(J)} ≤ C ⟨l⟩ ⟨2^k dist(I,J)⟩^{-M} ‖f‖_{ℓ^q(I)}`.

The statement is `Work.KMTAreas.A4.OffDecayClaim ρ`, and the proof is the one of Appendix A of the
paper: the kernel `R(j) λ_k(j)` of the projection is cut into three pieces

* `η_{≤jj} λ_k` (supported on `|x| ≤ 2^{jj}`, chosen with `2^{jj} < dist(I,J)`: it does not see
  the window),
* `(λ_k - η_{≤jj} λ_k) ∗ λ_{-v}` (a smooth symbol, bounded with the Ionescu--Wainger multiplier
  theorem, i.e. with the constant `⟨l⟩` and not the huge `#(ℚ/ℤ)_{≤l}`),
* the leftover `B - B ∗ λ_{-v}`, `B = λ_k - η_{≤jj} λ_k`, whose *sampled* `ℓ¹` mass is small
  (`Work.KMTAreas.A4.offPieceHigh`) and which is beaten by Young's inequality,

the arithmetic factor `#(ℚ/ℤ)_{≤l}` of the third piece being absorbed by `2^{2(k+v)}` on the good
major arcs (`v` being the height of `(ℚ/ℤ)_{≤l}`).

## Layout

* the kernel of `iwConv` on a periodised Schwartz symbol (`iwConv_eq_Rfac`);
* the *Case A* (`2^k dist ≤ 2`) trivial bound, which is the plain `ℓ^q` bound of `iw-prop`(i);
* the *Case B* (`2^k dist > 2`) off-diagonal argument, with the three kernel pieces.

## Main result

* `Work.KMTAreas.A4.offDecayKMT`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.improvOneZDefs
import Submission.Work.KMTAreas.A4.offKernNormLe
import Submission.Work.KMTAreas.A4.offYoung
import Submission.Work.KMTAreas.A4.offPieceHigh
import Submission.Work.KMTAreas.A7.IwLqGeneral
import Submission.Work.KMTAreas.A7.eLpNorm_iwConv_le_of_IWLqBound
import Submission.Work.KMTAreas.A7.IsLqMultiplierBound_star
import Submission.Work.KMTAreas.A7rand.eLpNorm_iwConv_le_kernelMass
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory
open scoped ENNReal NNReal BigOperators FourierTransform

namespace Work.KMTAreas.A4

open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier


noncomputable section

/-! ## Evenness of the kernels, and the Fourier involution on even functions -/

/-- **The Fourier transform of an even function is even.** -/
theorem fourier_even_of_even (F : ℝ → ℂ) (hF : ∀ y : ℝ, F (-y) = F y) (w : ℝ) :
    𝓕 F (-w) = 𝓕 F w := by
  have h := Real.fourier_comp_linearIsometry (A := LinearIsometryEquiv.neg ℝ) (f := F) w
  have h2 : (F ∘ (LinearIsometryEquiv.neg ℝ)) = F := funext hF
  rw [h2, LinearIsometryEquiv.coe_neg] at h
  exact h.symm

/-- **The rescaled cutoff kernel `λ_k = 𝓕⁻ η_{≤k}` is even.** -/
theorem lam_even (k : ℤ) (x : ℝ) : lam k (-x) = lam k x := by
  have hcoe : (lam k : ℝ → ℂ) = 𝓕⁻ ((bmp k : SchwartzMap ℝ ℂ) : ℝ → ℂ) :=
    SchwartzMap.fourierInv_coe (bmp k)
  have hF : ∀ w : ℝ,
      𝓕 ((bmp k : SchwartzMap ℝ ℂ) : ℝ → ℂ) (-w)
        = 𝓕 ((bmp k : SchwartzMap ℝ ℂ) : ℝ → ℂ) w :=
    fun w => fourier_even_of_even _ (fun y => bmp_neg_apply k y) w
  rw [hcoe, Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg]
  simpa using (hF x).symm

/-- Pointwise product of two even Schwartz functions is even. -/
theorem mS_even {u v : SchwartzMap ℝ ℂ} (hu : ∀ x : ℝ, u (-x) = u x)
    (hv : ∀ x : ℝ, v (-x) = v x) : ∀ x : ℝ, mS u v (-x) = mS u v x := by
  intro x
  rw [mS_apply, mS_apply, hu x, hv x]

/-- Difference of two even Schwartz functions is even. -/
theorem sub_even {u v : SchwartzMap ℝ ℂ} (hu : ∀ x : ℝ, u (-x) = u x)
    (hv : ∀ x : ℝ, v (-x) = v x) : ∀ x : ℝ, (u - v) (-x) = (u - v) x := by
  intro x
  show (u : ℝ → ℂ) (-x) - (v : ℝ → ℂ) (-x) = (u : ℝ → ℂ) x - (v : ℝ → ℂ) x
  rw [hu x, hv x]

/-- **The convolution of two even Schwartz functions is even.** -/
theorem cS_even {u v : SchwartzMap ℝ ℂ} (hu : ∀ x : ℝ, u (-x) = u x)
    (hv : ∀ x : ℝ, v (-x) = v x) : ∀ x : ℝ, cS u v (-x) = cS u v x := by
  have hGu : ∀ w : ℝ, 𝓕 (u : ℝ → ℂ) (-w) = 𝓕 (u : ℝ → ℂ) w :=
    fun w => fourier_even_of_even _ hu w
  have hGv : ∀ w : ℝ, 𝓕 (v : ℝ → ℂ) (-w) = 𝓕 (v : ℝ → ℂ) w :=
    fun w => fourier_even_of_even _ hv w
  have hG : ∀ w : ℝ, (mS (𝓕 u) (𝓕 v) : ℝ → ℂ) (-w) = (mS (𝓕 u) (𝓕 v) : ℝ → ℂ) w := by
    intro w
    have e1 : ((𝓕 u : SchwartzMap ℝ ℂ) : ℝ → ℂ) (-w)
        = ((𝓕 u : SchwartzMap ℝ ℂ) : ℝ → ℂ) w := by
      rw [congrFun (SchwartzMap.fourier_coe u) (-w),
        congrFun (SchwartzMap.fourier_coe u) w]
      exact hGu w
    have e2 : ((𝓕 v : SchwartzMap ℝ ℂ) : ℝ → ℂ) (-w)
        = ((𝓕 v : SchwartzMap ℝ ℂ) : ℝ → ℂ) w := by
      rw [congrFun (SchwartzMap.fourier_coe v) (-w),
        congrFun (SchwartzMap.fourier_coe v) w]
      exact hGv w
    rw [mS_apply, mS_apply, e1, e2]
  have h1 : (cS u v : SchwartzMap ℝ ℂ) = 𝓕⁻ (mS (𝓕 u) (𝓕 v)) := by
    rw [← fourier_cS u v, FourierPair.fourierInv_fourier_eq]
  have hcoe : (cS u v : ℝ → ℂ)
      = 𝓕⁻ ((mS (𝓕 u) (𝓕 v) : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
    rw [congrArg (fun g : SchwartzMap ℝ ℂ => (g : ℝ → ℂ)) h1, SchwartzMap.fourierInv_coe]
  have hFeven : ∀ w : ℝ,
      𝓕 ((mS (𝓕 u) (𝓕 v) : SchwartzMap ℝ ℂ) : ℝ → ℂ) (-w)
        = 𝓕 ((mS (𝓕 u) (𝓕 v) : SchwartzMap ℝ ℂ) : ℝ → ℂ) w :=
    fun w => fourier_even_of_even _ hG w
  intro x
  rw [hcoe, Real.fourierInv_eq_fourier_neg, Real.fourierInv_eq_fourier_neg]
  simpa using (hFeven x).symm

/-- **The Fourier transform of an even Schwartz function is an involution.** -/
theorem fourier_fourier_of_even (P : SchwartzMap ℝ ℂ) (hP : ∀ x : ℝ, P (-x) = P x) :
    𝓕 (𝓕 P) = P := by
  have hfun : ((𝓕 (𝓕 P) : SchwartzMap ℝ ℂ) : ℝ → ℂ) = 𝓕 (𝓕 (P : ℝ → ℂ)) := by
    rw [SchwartzMap.fourier_coe (𝓕 P), SchwartzMap.fourier_coe P]
  have hinv : 𝓕⁻ (𝓕 (P : ℝ → ℂ)) = (P : ℝ → ℂ) := by
    refine Continuous.fourierInv_fourier_eq P.continuous P.integrable ?_
    rw [← SchwartzMap.fourier_coe P]
    exact (𝓕 P).integrable
  ext x
  rw [hfun]
  have hstep : 𝓕 (𝓕 (P : ℝ → ℂ)) x = 𝓕⁻ (𝓕 (P : ℝ → ℂ)) (-x) := by
    rw [Real.fourierInv_eq_fourier_neg]
    simp
  rw [hstep, hinv]
  exact hP x

/-! ## The kernel of the projection -/

/-- The arithmetic factor `R(j) = ∑_{α ∈ (ℚ/ℤ)_{≤l}} e(-j a_α)` carried by the kernel of
`Π_{≤l,≤k}`. -/
noncomputable def Rfac (ρ : ℝ) (l : ℕ) (j : ℤ) : ℂ :=
  ∑ α ∈ iwArithFreqs ρ l,
    (Real.fourierChar (-(((AddCircle.equivIco (1 : ℝ) 0 α).val) * (j : ℝ))) : ℂ)

theorem norm_Rfac_le (ρ : ℝ) (l : ℕ) (j : ℤ) :
    ‖Rfac ρ l j‖ ≤ ((iwArithFreqs ρ l).card : ℝ) := by
  have hterm : ∀ α ∈ iwArithFreqs ρ l,
      ‖(Real.fourierChar (-(((AddCircle.equivIco (1 : ℝ) 0 α).val) * (j : ℝ))) : ℂ)‖ = 1 :=
    fun α _ => Circle.norm_coe _
  calc ‖Rfac ρ l j‖
      = ‖∑ α ∈ iwArithFreqs ρ l,
          (Real.fourierChar (-(((AddCircle.equivIco (1 : ℝ) 0 α).val) * (j : ℝ))) : ℂ)‖ := rfl
    _ ≤ ∑ α ∈ iwArithFreqs ρ l,
          ‖(Real.fourierChar (-(((AddCircle.equivIco (1 : ℝ) 0 α).val) * (j : ℝ))) : ℂ)‖ :=
        norm_sum_le _ _
    _ = ∑ _α ∈ iwArithFreqs ρ l, (1 : ℝ) := Finset.sum_congr rfl hterm
    _ = ((iwArithFreqs ρ l).card : ℝ) := by simp

/-- **The `ℤ`-kernel of the Ionescu--Wainger projection with a periodised Schwartz symbol.** -/
theorem iwKernel_eq_Rfac_mul (ρ : ℝ) (l : ℕ) (Φ : SchwartzMap ℝ ℂ) (j : ℤ) :
    iwKernel (iwSymbolSet (iwArithFreqs ρ l) (periodize (Φ : ℝ → ℂ))) j
      = Rfac ρ l j * 𝓕 (Φ : ℝ → ℂ) (j : ℝ) := by
  rw [offKernelId ρ l Φ j]
  rw [fourier_finsetSum_sub (iwArithFreqs ρ l)
        (fun α => (AddCircle.equivIco (1 : ℝ) 0 α).val) (Φ : ℝ → ℂ) Φ.integrable (j : ℝ)]
  rw [Rfac, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [fourier_comp_sub Φ ((AddCircle.equivIco (1 : ℝ) 0 α).val) (j : ℝ), Circle.smul_def,
    smul_eq_mul]

/-- **The projection as a convolution with the kernel `R(j) 𝓕Φ(j)`.** -/
theorem iwConv_eq_Rfac (ρ : ℝ) (l : ℕ) (Φ : SchwartzMap ℝ ℂ) (f : ℤ → ℂ) (n : ℤ) :
    iwConv (iwArithFreqs ρ l) (periodize (Φ : ℝ → ℂ)) f n
      = ∑' j : ℤ, (Rfac ρ l j * 𝓕 (Φ : ℝ → ℂ) (j : ℝ)) * f (n - j) := by
  rw [iwConv_apply]
  refine tsum_congr fun j => ?_
  rw [iwKernel_eq_Rfac_mul, smul_eq_mul]

/-- **The projection `Π_{≤l,≤k}` as a convolution with the kernel `R(j) λ_k(j)`.** -/
theorem kmtProj_eq_Rfac (ρ : ℝ) (l : ℕ) (k : ℤ) (f : ℤ → ℂ) (n : ℤ) :
    Work.KMTContract.kmtProj ρ l k f n
      = ∑' j : ℤ, (Rfac ρ l j * lam k (j : ℝ)) * f (n - j) := by
  rw [Work.KMTContract.kmtProj]
  rw [show periodize (etaCut Work.KMTContract.kmtEta k)
        = periodize ((bmp k : SchwartzMap ℝ ℂ) : ℝ → ℂ) from by
      rw [show ((bmp k : SchwartzMap ℝ ℂ) : ℝ → ℂ) = etaCut Work.KMTContract.kmtEta k from
        bmp_coe k]]
  rw [iwConv_eq_Rfac ρ l (bmp k) f n]
  refine tsum_congr fun j => ?_
  have hfourier : 𝓕 ((bmp k : SchwartzMap ℝ ℂ) : ℝ → ℂ) (j : ℝ)
      = (lam k : SchwartzMap ℝ ℂ) (j : ℝ) := by
    rw [← congrFun (SchwartzMap.fourier_coe (bmp k)) (j : ℝ)]
    exact congrFun (congrArg (fun g : SchwartzMap ℝ ℂ => (g : ℝ → ℂ)) (fourier_bmp k)) (j : ℝ)
  rw [hfourier]

/-! ## Sampled summability of Schwartz functions -/

/-- The sampled values of a Schwartz function form a summable family. -/
theorem summable_schwartzSamples (F : SchwartzMap ℝ ℂ) :
    Summable (fun j : ℤ => ‖F (j : ℝ)‖) := by
  obtain ⟨C, hC, hdec⟩ := F.decay 2 0
  simp only [norm_iteratedFDeriv_zero] at hdec
  have hbase0 : Summable (fun j : ℤ => 1 / |((j : ℤ) : ℝ)| ^ (2 : ℝ)) := by
    have h := (Real.summable_one_div_int_add_rpow (0 : ℝ) (2 : ℝ)).mpr
      (by norm_num : (1 : ℝ) < 2)
    simpa using h
  have hbase : Summable (fun j : ℤ => C * (1 / |((j : ℤ) : ℝ)| ^ (2 : ℝ))) :=
    hbase0.mul_left C
  refine Summable.of_norm_bounded_eventually hbase ?_
  rw [Filter.eventually_cofinite]
  refine (Set.finite_singleton (0 : ℤ)).subset ?_
  intro j hj
  rw [Set.mem_singleton_iff]
  by_contra h0
  refine hj ?_
  have hjabs : 0 < |((j : ℤ) : ℝ)| := by
    rw [abs_pos]
    exact_mod_cast h0
  have hpow : |((j : ℤ) : ℝ)| ^ (2 : ℝ) = |((j : ℤ) : ℝ)| ^ 2 := Real.rpow_natCast _ 2
  have hle := hdec ((j : ℤ) : ℝ)
  rw [Real.norm_eq_abs] at hle
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg ((F : ℝ → ℂ) ((j : ℤ) : ℝ)))]
  have hdiv : ‖(F : ℝ → ℂ) ((j : ℤ) : ℝ)‖ ≤ C / |((j : ℤ) : ℝ)| ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    calc ‖(F : ℝ → ℂ) ((j : ℤ) : ℝ)‖ * |((j : ℤ) : ℝ)| ^ 2
        = |((j : ℤ) : ℝ)| ^ 2 * ‖(F : ℝ → ℂ) ((j : ℤ) : ℝ)‖ := by ring
      _ ≤ C := hle
  calc ‖(F : ℝ → ℂ) ((j : ℤ) : ℝ)‖ ≤ C / |((j : ℤ) : ℝ)| ^ 2 := hdiv
    _ = C * (1 / |((j : ℤ) : ℝ)| ^ (2 : ℝ)) := by
      rw [one_div, div_eq_mul_inv, ← hpow]

/-! ## The masses of the pieces -/

/-- **Young's inequality for the Schwartz convolution, in mass form.** -/
theorem eLpNorm_cS_le (u v : SchwartzMap ℝ ℂ) :
    eLpNorm ((cS u v : SchwartzMap ℝ ℂ) : ℝ → ℂ) 1 (volume : Measure ℝ)
      ≤ eLpNorm ((u : SchwartzMap ℝ ℂ) : ℝ → ℂ) 1 volume
        * eLpNorm ((v : SchwartzMap ℝ ℂ) : ℝ → ℂ) 1 volume := by
  set K : ℝ → ℝ≥0∞ := fun z => ‖(v : SchwartzMap ℝ ℂ) z‖ₑ with hK
  set Φ : ℝ → ℝ≥0∞ := fun y => ‖(u : SchwartzMap ℝ ℂ) y‖ₑ with hΦ
  have hKae : AEMeasurable K volume := by
    rw [hK]; exact (continuous_enorm.comp v.continuous).aemeasurable
  have hΦae : AEMeasurable Φ volume := by
    rw [hΦ]; exact (continuous_enorm.comp u.continuous).aemeasurable
  have hpt : ∀ x : ℝ, ‖((cS u v : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖ₑ
      ≤ ∫⁻ y : ℝ, K (x - y) * Φ y := by
    intro x
    rw [cS_eq, SchwartzMap.convolution_apply, MeasureTheory.convolution_def]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    simp only [ContinuousLinearMap.mul_apply', hK, hΦ, enorm_mul]
    rw [mul_comm]
  calc eLpNorm ((cS u v : SchwartzMap ℝ ℂ) : ℝ → ℂ) 1 volume
      ≤ eLpNorm (fun x : ℝ => ∫⁻ y : ℝ, K (x - y) * Φ y) (ENNReal.ofReal 1) volume := by
        rw [← ENNReal.ofReal_one]
        refine eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)
        simpa using hpt x
    _ ≤ eLpNorm K (ENNReal.ofReal 1) volume * eLpNorm Φ (ENNReal.ofReal 1) volume :=
        Commons.Analysis.Convolution.eLpNorm_convolution_le_ennreal (p := 1) (q := 1) (r := 1)
          le_rfl le_rfl (by ring) hKae hΦae
    _ = eLpNorm ((u : SchwartzMap ℝ ℂ) : ℝ → ℂ) 1 volume
          * eLpNorm ((v : SchwartzMap ℝ ℂ) : ℝ → ℂ) 1 volume := by
        rw [hK, hΦ, eLpNorm_enorm (hf := by pw_aesm), eLpNorm_enorm (hf := by pw_aesm), ENNReal.ofReal_one]
        ring

/-- **The mass of `λ_k` is bounded uniformly in `k`.** -/
theorem eLpNorm_lam_le :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℤ,
      eLpNorm ((lam k : SchwartzMap ℝ ℂ) : ℝ → ℂ) 1 (volume : Measure ℝ)
        ≤ ENNReal.ofReal C := by
  obtain ⟨C, hC, hb⟩ := offLamTail 0 0
  refine ⟨C, hC, fun k => ?_⟩
  have h1 : eLpNorm ((lam k : SchwartzMap ℝ ℂ) : ℝ → ℂ) 1 volume
      = ∫⁻ x : ℝ,
          ‖((Work.KMTAreas.A7.etaMult_K k : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖ₑ := by
    rw [show ((lam k : SchwartzMap ℝ ℂ) : ℝ → ℂ)
          = ((Work.KMTAreas.A7.etaMult_K k : SchwartzMap ℝ ℂ) : ℝ → ℂ) from by
      rw [lam_eq_etaMult_K]]
    exact eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)
  have h2 := hb k 0 (le_refl (0 : ℝ))
  have h2' : ∫⁻ x : ℝ,
      ‖((Work.KMTAreas.A7.etaMult_K k : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖ₑ ≤ ENNReal.ofReal C := by
    simpa using h2
  exact h1.trans_le h2'

/-! ## Arithmetic bookkeeping for the off-diagonal decay -/

/-- The tail factor `(2^{k+jj-1})^{-(M+1)}` is dominated by `4^{M+1} (2^k D)^{-M}`, provided
`D ≤ 2^{jj+1}` and `2 < 2^k D`. -/
theorem tailAbsorb {M : ℕ} {k jj : ℤ} {D : ℝ} (hkjj : 0 ≤ k + jj - 1)
    (hD2 : 2 < (2 : ℝ) ^ k * D) (hjj : D ≤ (2 : ℝ) ^ (jj + 1)) :
    ((2 : ℝ) ^ (k + jj - 1)) ^ (-(((M + 1 : ℕ) : ℝ)))
      ≤ (4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹ * ((2 : ℝ) ^ k * D) ^ (-(M : ℝ)) := by
  set x : ℝ := (2 : ℝ) ^ k * D with hx
  set y : ℝ := (2 : ℝ) ^ (k + jj - 1) with hy
  have hx1 : (1 : ℝ) < x := by rw [hx]; linarith
  have hx2 : (2 : ℝ) ≤ x := by rw [hx]; linarith
  have hxpos : (0 : ℝ) < x := by linarith
  have hy1 : (1 : ℝ) ≤ y := by
    rw [hy]
    exact one_le_zpow₀ (by norm_num) hkjj
  have hypos : (0 : ℝ) < y := lt_of_lt_of_le one_pos hy1
  have hkey : x / 4 ≤ y := by
    rw [hx, hy]
    have h4 : (2 : ℝ) ^ (jj + 1) = 4 * (2 : ℝ) ^ (jj - 1) := by
      rw [show jj + 1 = (jj - 1) + 2 from by ring, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    have h2k : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
    have hstep2 : (2 : ℝ) ^ k * (4 * (2 : ℝ) ^ (jj - 1)) / 4 = (2 : ℝ) ^ (k + jj - 1) := by
      rw [show (2 : ℝ) ^ k * (4 * (2 : ℝ) ^ (jj - 1)) / 4
            = (2 : ℝ) ^ k * (2 : ℝ) ^ (jj - 1) from by ring]
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      ring
    calc (2 : ℝ) ^ k * D / 4 ≤ (2 : ℝ) ^ k * (2 : ℝ) ^ (jj + 1) / 4 := by
          have := mul_le_mul_of_nonneg_left hjj h2k.le
          linarith
      _ = (2 : ℝ) ^ k * (4 * (2 : ℝ) ^ (jj - 1)) / 4 := by rw [h4]
      _ = (2 : ℝ) ^ (k + jj - 1) := hstep2
  have hstep1 : y ^ (-(((M + 1 : ℕ) : ℝ))) ≤ (x / 4) ^ (-(((M + 1 : ℕ) : ℝ))) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hkey (by
      have hMnn : (0 : ℝ) ≤ ((M + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith)
  have hstep2 : (x / 4) ^ (-(((M + 1 : ℕ) : ℝ)))
      = (4 : ℝ) ^ (M + 1) * x ^ (-(((M + 1 : ℕ) : ℝ))) := by
    rw [show x / 4 = x * (4 : ℝ)⁻¹ from by ring]
    rw [Real.mul_rpow hxpos.le (by norm_num)]
    rw [Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show (((4 : ℝ) ^ (-(((M + 1 : ℕ) : ℝ))))⁻¹) = (4 : ℝ) ^ (((M + 1 : ℕ)) : ℝ) from by
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4)]
      congr 1
      ring]
    rw [Real.rpow_natCast]
    ring
  have hstep3 : x ^ (-(((M + 1 : ℕ) : ℝ))) ≤ (2 : ℝ)⁻¹ * x ^ (-(M : ℝ)) := by
    rw [show -(((M + 1 : ℕ) : ℝ)) = -(M : ℝ) + (-1) from by push_cast; ring]
    rw [Real.rpow_add hxpos]
    have hinv : x ^ (-1 : ℝ) ≤ (2 : ℝ)⁻¹ := by
      rw [Real.rpow_neg_one, inv_le_inv₀ hxpos (by norm_num : (0 : ℝ) < 2)]
      exact hx2
    calc x ^ (-(M : ℝ)) * x ^ (-1 : ℝ) ≤ x ^ (-(M : ℝ)) * (2 : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hxpos.le _)
      _ = (2 : ℝ)⁻¹ * x ^ (-(M : ℝ)) := by ring
  calc y ^ (-(((M + 1 : ℕ) : ℝ))) ≤ (x / 4) ^ (-(((M + 1 : ℕ) : ℝ))) := hstep1
    _ = (4 : ℝ) ^ (M + 1) * x ^ (-(((M + 1 : ℕ) : ℝ))) := hstep2
    _ ≤ (4 : ℝ) ^ (M + 1) * ((2 : ℝ)⁻¹ * x ^ (-(M : ℝ))) :=
        mul_le_mul_of_nonneg_left hstep3 (by positivity)
    _ = (4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹ * x ^ (-(M : ℝ)) := by ring

/-- The arithmetic factor `#(ℚ/ℤ)_{≤l}` times `2^{k+v}` is absorbed by the good-major-arc
condition `k + v ≤ -cIw 2^{ρl}` with `cIw ≥ 1`. -/
theorem card_zpow_absorb {ρ : ℝ} {l : ℕ} {k v : ℤ} {C_card cIw : ℝ}
    (hCard : ((iwArithFreqs ρ l).card : ℝ) ≤ C_card * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l : ℝ))))
    (hC_card : 0 < C_card) (hcIw : 1 ≤ cIw)
    (hkv : (k : ℝ) + (v : ℝ) ≤ -cIw * (2 : ℝ) ^ (ρ * (l : ℝ))) :
    ((iwArithFreqs ρ l).card : ℝ) * (2 : ℝ) ^ (k + v) ≤ C_card := by
  have hpl : (0 : ℝ) < (2 : ℝ) ^ (ρ * (l : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have h2kv : (2 : ℝ) ^ (k + v) ≤ (2 : ℝ) ^ (-cIw * (2 : ℝ) ^ (ρ * (l : ℝ))) := by
    rw [show (2 : ℝ) ^ (k + v) = (2 : ℝ) ^ (((k + v : ℤ)) : ℝ) from
      (Real.rpow_intCast 2 (k + v)).symm]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    rw [Int.cast_add]
    exact hkv
  calc ((iwArithFreqs ρ l).card : ℝ) * (2 : ℝ) ^ (k + v)
      ≤ C_card * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l : ℝ))) * (2 : ℝ) ^ (k + v) :=
        mul_le_mul_of_nonneg_right hCard (by positivity)
    _ ≤ C_card * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l : ℝ))) *
          (2 : ℝ) ^ (-cIw * (2 : ℝ) ^ (ρ * (l : ℝ))) :=
        mul_le_mul_of_nonneg_left h2kv (by positivity)
    _ = C_card * (2 : ℝ) ^ ((2 : ℝ) ^ (ρ * (l : ℝ)) - cIw * (2 : ℝ) ^ (ρ * (l : ℝ))) := by
        rw [sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        ring_nf
    _ ≤ C_card * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hC_card.le
        refine Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) ?_
        nlinarith [hpl, hcIw]
    _ = C_card := by ring

/-! ## The main theorem -/

theorem offDecayKMT (hA1 : Work.KMTContract.AreaA1) :
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → Work.KMTAreas.A4.OffDecayClaim ρ := by
  intro ρ hρ hρ1
  obtain ⟨Cρ_iw, hCρ_iw, hIwLq⟩ := Work.KMTAreas.A7.IwLqGeneral hA1 ρ hρ hρ1
  obtain ⟨C_lt, hC_lt, hLt⟩ := eLpNorm_lam_le
  obtain ⟨C_card, hC_card, hCard⟩ := Work.Analysis.IonescuWainger.iw_height_card_le hρ
  intro q hq M
  obtain ⟨Cρ_pl, hCρ_pl, C_pl, hC_pl, hPlain⟩ :=
    Work.KMTAreas.A7.kmtProj_lp_bound_holds hA1 ρ hρ hρ1 q hq
  obtain ⟨C_M, hC_M, hMid⟩ := offPieceMid (M + 1)
  obtain ⟨C_H, hC_H, hHigh⟩ := offPieceHigh (M + 1)
  obtain ⟨C_q, hC_q, hIwq⟩ := hIwLq q hq
  set cIw : ℝ := max Cρ_iw 2 with hcIw
  have hcIw2 : (2 : ℝ) ≤ cIw := le_max_right _ _
  have hcIw_iw : Cρ_iw ≤ cIw := le_max_left _ _
  set Cρ : ℝ := max Cρ_pl (2 * cIw + 4) + 12 with hCρdef
  have hCρ_pl_le : Cρ_pl ≤ Cρ := by
    rw [hCρdef]; linarith [le_max_left Cρ_pl (2 * cIw + 4)]
  have hCρ_big : 2 * cIw + 4 ≤ Cρ := by
    rw [hCρdef]; linarith [le_max_right Cρ_pl (2 * cIw + 4)]
  have hCρ_pos : 0 < Cρ := by rw [hCρdef]; linarith
  set Cf : ℝ := 2 + (2 : ℝ) ^ (M : ℝ) * (C_pl : ℝ) + (C_q : ℝ) * C_M * C_lt
      * (4 : ℝ) ^ (M + 1) + C_card * C_H * (4 : ℝ) ^ (M + 1) + 12 with hCf
  have hCf_pos : 0 < Cf := by rw [hCf]; positivity
  refine ⟨Cρ, hCρ_pos, ⟨Real.toNNReal Cf,
    ⟨Real.toNNReal_pos.mpr hCf_pos, ?_⟩⟩⟩
  intro l k hgood a b c d f hbc hsupp
  set D : ℝ := ((c - b : ℤ) : ℝ) with hD
  have hD1 : 1 ≤ D := by rw [hD]; exact_mod_cast (by omega : (1 : ℤ) ≤ c - b)
  have hgood_pl : GoodMajorArcs ρ Cρ_pl l k := GoodMajorArcs.mono_const hCρ_pl_le hgood
  have hgoal : MeasureTheory.eLpNorm (fun x : ℤ =>
        if c ≤ x ∧ x ≤ d then Work.KMTContract.kmtProj ρ l k f x else 0)
        (ENNReal.ofReal q) (MeasureTheory.Measure.count : Measure ℤ)
      ≤ ENNReal.ofReal Cf * ENNReal.ofReal (max ((l : ℝ)) 1) *
          ENNReal.ofReal ((max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ))) *
          MeasureTheory.eLpNorm f (ENNReal.ofReal q) (MeasureTheory.Measure.count : Measure ℤ) := by
    by_cases hcase : (2 : ℝ) ^ k * D ≤ 2
    · -- Case A: the plain `ℓ^q` bound
      have hCf_ge : (2 : ℝ) ^ (M : ℝ) * (C_pl : ℝ) ≤ Cf := by
        rw [hCf]
        have h1 : (0 : ℝ) ≤ (C_q : ℝ) * C_M * C_lt * (4 : ℝ) ^ (M + 1) := by positivity
        have h2 : (0 : ℝ) ≤ C_card * C_H * (4 : ℝ) ^ (M + 1) := by positivity
        nlinarith [h1, h2]
      have h2M : (2 : ℝ) ^ (M : ℝ) * (2 : ℝ) ^ (-(M : ℝ)) = 1 := by
        rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
      have hEq : (2 : ℝ) ^ (M : ℝ) * (C_pl : ℝ) * (2 : ℝ) ^ (-(M : ℝ)) = (C_pl : ℝ) := by
        rw [mul_assoc, mul_comm ((C_pl : ℝ)) ((2 : ℝ) ^ (-(M : ℝ))), ← mul_assoc, h2M, one_mul]
      have hconst : (C_pl : ℝ) ≤ Cf * (2 : ℝ) ^ (-(M : ℝ)) := by
        rw [← hEq]
        exact mul_le_mul_of_nonneg_right hCf_ge (by positivity)
      have hfac : (2 : ℝ) ^ (-(M : ℝ)) ≤ (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ)) := by
        have h2le : (max ((2 : ℝ) ^ k * D) 1) ≤ 2 := max_le hcase (by norm_num)
        have h1le : (1 : ℝ) ≤ max ((2 : ℝ) ^ k * D) 1 := le_max_right _ _
        have hpos : (0 : ℝ) < max ((2 : ℝ) ^ k * D) 1 := lt_of_lt_of_le one_pos h1le
        exact Real.rpow_le_rpow_of_nonpos hpos h2le (by
          have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
          linarith)
      calc MeasureTheory.eLpNorm (fun x : ℤ =>
              if c ≤ x ∧ x ≤ d then Work.KMTContract.kmtProj ρ l k f x else 0)
            (ENNReal.ofReal q) (MeasureTheory.Measure.count : Measure ℤ)
          ≤ MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTContract.kmtProj ρ l k f x)
              (ENNReal.ofReal q) (MeasureTheory.Measure.count : Measure ℤ) := by
            refine eLpNorm_mono (hf := by pw_aesm) (fun x => ?_)
            by_cases hx : c ≤ x ∧ x ≤ d
            · rw [if_pos hx]
            · rw [if_neg hx]; simp only [norm_zero]; positivity
        _ ≤ ENNReal.ofReal (C_pl : ℝ) * ENNReal.ofReal (angleBracket l : ℝ) *
              MeasureTheory.eLpNorm f (ENNReal.ofReal q) (MeasureTheory.Measure.count : Measure ℤ) := by
            refine (hPlain l k hgood_pl f).trans (le_of_eq ?_)
            rw [angleBracket, max_comm]
        _ = ENNReal.ofReal ((C_pl : ℝ) * (angleBracket l : ℝ)) *
              MeasureTheory.eLpNorm f (ENNReal.ofReal q) (MeasureTheory.Measure.count : Measure ℤ) := by
            rw [ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal (Cf * max ((l : ℝ)) 1 *
              (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ))) *
              MeasureTheory.eLpNorm f (ENNReal.ofReal q) (MeasureTheory.Measure.count : Measure ℤ) := by
            refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
            rw [angleBracket, max_comm]
            calc (C_pl : ℝ) * max ((l : ℝ)) 1
                ≤ Cf * (2 : ℝ) ^ (-(M : ℝ)) * max ((l : ℝ)) 1 :=
                  mul_le_mul_of_nonneg_right hconst (le_trans zero_le_one (le_max_right _ _))
              _ ≤ Cf * (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ)) * max ((l : ℝ)) 1 :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hfac hCf_pos.le)
                    (le_trans zero_le_one (le_max_right _ _))
              _ = Cf * max ((l : ℝ)) 1 * (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ)) := by ring
        _ = ENNReal.ofReal Cf * ENNReal.ofReal (max ((l : ℝ)) 1) *
              ENNReal.ofReal ((max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ))) *
              MeasureTheory.eLpNorm f (ENNReal.ofReal q) (MeasureTheory.Measure.count : Measure ℤ) := by
            rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hCf_pos.le]
    · -- Case B
      have hcase' : 2 < (2 : ℝ) ^ k * D := lt_of_not_ge hcase
      by_cases hfin : MeasureTheory.eLpNorm f (ENNReal.ofReal q)
          (MeasureTheory.Measure.count : Measure ℤ) = ⊤
      · rw [hfin]
        have h1 : (0 : ℝ≥0∞) < ENNReal.ofReal Cf := ENNReal.ofReal_pos.mpr hCf_pos
        have h2 : (0 : ℝ≥0∞) < ENNReal.ofReal (max ((l : ℝ)) 1) :=
          ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
        have h3 : (0 : ℝ≥0∞) < ENNReal.ofReal ((max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ))) :=
          ENNReal.ofReal_pos.mpr
            (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one (le_max_right _ _)) _)
        rw [ENNReal.mul_top (mul_ne_zero (mul_ne_zero h1.ne' h2.ne') h3.ne')]
        exact le_top
      · have hq1 : (1 : ℝ≥0∞) < ENNReal.ofReal q := by
          rw [show (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) from ENNReal.ofReal_one.symm]
          exact (ENNReal.ofReal_lt_ofReal_iff (by linarith : (0 : ℝ) < q)).mpr hq
        have hmem : MeasureTheory.MemLp f (ENNReal.ofReal q)
            (MeasureTheory.Measure.count : Measure ℤ) :=
          MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hfin)
        obtain ⟨Bf, hBf⟩ := Work.KMTContract.bound_of_memLp_count hq1 hmem
        -- ### the parameters
        set Nn : ℕ := (c - b).toNat with hNn
        have hNn_cast : (Nn : ℤ) = c - b := Int.toNat_of_nonneg (by omega)
        have hNn_eq : (Nn : ℝ) = D := by rw [hD]; exact_mod_cast hNn_cast
        have hkh : (k : ℝ) ≤ -Cρ * (2 : ℝ) ^ (ρ * (l : ℝ)) := hgood
        have hk_nonpos : k ≤ 0 := by
          have h3 : (0 : ℝ) ≤ Cρ * (2 : ℝ) ^ (ρ * (l : ℝ)) := by positivity
          have h4 : (k : ℝ) ≤ 0 := by linarith
          exact_mod_cast h4
        have h2k_le_one : (2 : ℝ) ^ k ≤ 1 := by
          rw [← Real.rpow_intCast]
          exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2)
            (by exact_mod_cast hk_nonpos : (k : ℝ) ≤ 0)
        have hNn_ge : 3 ≤ Nn := by
          have h1 : (2 : ℝ) < (Nn : ℝ) := by
            rw [hNn_eq]
            nlinarith [hcase', h2k_le_one]
          have h2 : (2 : ℤ) < (Nn : ℤ) := by exact_mod_cast h1
          exact_mod_cast (by omega : (3 : ℤ) ≤ (Nn : ℤ))
        set jj : ℤ := (Nat.log 2 (Nn - 1) : ℤ) with hjj
        have hNn1 : Nn - 1 ≠ 0 := by omega
        have hjj_lt : (2 : ℝ) ^ jj < D := by
          have h1 : 2 ^ Nat.log 2 (Nn - 1) ≤ Nn - 1 := Nat.pow_log_le_self 2 hNn1
          have h1' : 2 ^ Nat.log 2 (Nn - 1) < Nn :=
            lt_of_le_of_lt h1 (Nat.sub_one_lt (by omega : Nn ≠ 0))
          have h2 : ((2 ^ Nat.log 2 (Nn - 1) : ℕ) : ℝ) < (Nn : ℝ) := by
            exact_mod_cast h1'
          rw [hNn_eq] at h2
          simpa [hjj, zpow_natCast, Nat.cast_pow] using h2
        have hjj_ge : D ≤ (2 : ℝ) ^ (jj + 1) := by
          have h1 : Nn - 1 < 2 ^ (Nat.log 2 (Nn - 1)).succ :=
            Nat.lt_pow_succ_log_self (by norm_num) (Nn - 1)
          have h2 : Nn ≤ 2 ^ (Nat.log 2 (Nn - 1)).succ := by
            have hsucc := Nat.succ_le_of_lt h1
            have hEq : (Nn - 1).succ = Nn := Nat.succ_pred_eq_of_pos (by omega : 0 < Nn)
            rwa [hEq] at hsucc
          have h2' : (Nn : ℝ) ≤ ((2 ^ (Nat.log 2 (Nn - 1)).succ : ℕ) : ℝ) := by
            exact_mod_cast h2
          rw [hNn_eq] at h2'
          have h3 : (2 : ℝ) ^ (jj + 1) = ((2 ^ (Nat.log 2 (Nn - 1)).succ : ℕ) : ℝ) := by
            rw [show jj + 1 = ((Nat.log 2 (Nn - 1)).succ : ℤ) from by simp [hjj]]
            rw [zpow_natCast, Nat.cast_pow]
            norm_num
          rw [h3]
          exact h2'
        have hjj_half : D / 2 ≤ (2 : ℝ) ^ jj := by
          have h2 : (2 : ℝ) ^ (jj + 1) = 2 * (2 : ℝ) ^ jj := by
            rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
            ring
          linarith [hjj_ge, h2]
        have hD3 : (3 : ℝ) ≤ D := by rw [← hNn_eq]; exact_mod_cast hNn_ge
        have hjj_nonneg : 0 ≤ jj := by
          have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ jj := by linarith [hjj_half, hD3]
          exact (one_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h1
        have hkjjpos : 0 < k + jj := by
          have h2 : (2 : ℝ) ^ (k + jj) = (2 : ℝ) ^ k * (2 : ℝ) ^ jj :=
            zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) k jj
          have h1 : (1 : ℝ) < (2 : ℝ) ^ (k + jj) := by
            have h3 : (2 : ℝ) ^ k * (D / 2) ≤ (2 : ℝ) ^ k * (2 : ℝ) ^ jj :=
              mul_le_mul_of_nonneg_left hjj_half (zpow_pos (by norm_num) k).le
            nlinarith [h2, h3, hcase', h2k_le_one, hD1]
          exact (one_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp h1
        have hkjj : 0 ≤ k + jj := le_of_lt hkjjpos
        have hkjj' : 0 ≤ k + jj - 1 := by omega
        set v : ℤ := ⌈cIw * (2 : ℝ) ^ (ρ * (l : ℝ))⌉ with hvdef
        have hv_ge : cIw * (2 : ℝ) ^ (ρ * (l : ℝ)) ≤ (v : ℝ) := Int.le_ceil _
        have hv_le : (v : ℝ) < cIw * (2 : ℝ) ^ (ρ * (l : ℝ)) + 1 := Int.ceil_lt_add_one _
        have hgood_v : GoodMajorArcs ρ cIw l (-v) := by
          show ((-v : ℤ) : ℝ) ≤ -cIw * (2 : ℝ) ^ (ρ * (l : ℝ))
          simp only [Int.cast_neg]
          linarith
        have hpl_one : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) :=
          Real.one_le_rpow (by norm_num) (by positivity)
        have hpl_pos : (0 : ℝ) < (2 : ℝ) ^ (ρ * (l : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
        have hk_le : (k : ℝ) ≤ -2 * (v : ℝ) := by
          nlinarith [hkh, hCρ_big, hv_le, hpl_one, hpl_pos]
        have hkv : (k : ℝ) + (v : ℝ) ≤ -cIw * (2 : ℝ) ^ (ρ * (l : ℝ)) := by
          nlinarith [hk_le, hv_ge]
        have hCard_a : ((iwArithFreqs ρ l).card : ℝ) * (2 : ℝ) ^ (k + v) ≤ C_card :=
          card_zpow_absorb (hCard l) hC_card (by linarith) hkv
        -- ### the kernel pieces
        set P1 : SchwartzMap ℝ ℂ := mS (bmp jj) (lam k) with hP1
        set B1 : SchwartzMap ℝ ℂ := lam k - P1 with hB1
        set P2 : SchwartzMap ℝ ℂ := cS B1 (lam (-v)) with hP2
        set P3 : SchwartzMap ℝ ℂ := B1 - P2 with hP3
        set Φ2 : SchwartzMap ℝ ℂ := 𝓕 P2 with hΦ2
        have hpt : ∀ x : ℝ, lam k x = P1 x + P2 x + P3 x := by
          intro x
          rw [hP3, hP2, hB1, hP1]
          simp only [sub_apply, mS_apply]
          ring
        have hP1even : ∀ x : ℝ, P1 (-x) = P1 x := by
          rw [hP1]
          exact mS_even (fun x => bmp_neg_apply jj x) (lam_even k)
        have hB1even : ∀ x : ℝ, B1 (-x) = B1 x := by
          rw [hB1]
          exact sub_even (lam_even k) hP1even
        have hP2even : ∀ x : ℝ, P2 (-x) = P2 x := by
          rw [hP2]
          exact cS_even hB1even (lam_even (-v))
        have hΦ2fourier : 𝓕 (Φ2 : ℝ → ℂ) = (P2 : ℝ → ℂ) := by
          rw [← SchwartzMap.fourier_coe Φ2, hΦ2]
          exact congrArg (fun g : SchwartzMap ℝ ℂ => (g : ℝ → ℂ))
            (fourier_fourier_of_even P2 hP2even)
        have hΦ2eq : (Φ2 : SchwartzMap ℝ ℂ) = mS (𝓕 B1) (bmp (-v)) := by
          rw [hΦ2, hP2, fourier_cS, lam_fourier]
        have hΦ2support : ∀ x : ℝ, Φ2 x ≠ 0 → x ∈ realArc (-v) := by
          intro x hx
          have hx2 : (mS (𝓕 B1) (bmp (-v)) : ℝ → ℂ) x ≠ 0 := by
            rw [← hΦ2eq]; exact hx
          rw [mS_apply] at hx2
          have hb : (bmp (-v)) x ≠ 0 := fun h => hx2 (by rw [h, mul_zero])
          have hb' := bmp_support (-v) hb
          rw [realArc]
          exact abs_le.mp hb'
        -- ### the mass of the first piece
        have hB1int : (∫ x : ℝ, ‖(B1 : SchwartzMap ℝ ℂ) x‖)
            ≤ C_M * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(((M + 1 : ℕ) : ℝ))) := by
          have h := hMid k jj hk_nonpos hjj_nonneg
          have heq : (2 : ℝ) ^ k * (2 : ℝ) ^ (jj - 1) = (2 : ℝ) ^ (k + jj - 1) := by
            rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
            congr 1
            ring
          rw [hB1, hP1, ← heq]
          exact h
        have hB1mass : eLpNorm ((B1 : SchwartzMap ℝ ℂ) : ℝ → ℂ) 1 (volume : Measure ℝ)
            ≤ ENNReal.ofReal
              (C_M * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(((M + 1 : ℕ) : ℝ)))) := by
          have heq : eLpNorm ((B1 : SchwartzMap ℝ ℂ) : ℝ → ℂ) 1 (volume : Measure ℝ)
              = ENNReal.ofReal (∫ x : ℝ, ‖(B1 : SchwartzMap ℝ ℂ) x‖) := by
            rw [eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm)]
            rw [show (fun x : ℝ => ‖(B1 : SchwartzMap ℝ ℂ) x‖ₑ)
                  = (fun x : ℝ => ENNReal.ofReal ‖(B1 : SchwartzMap ℝ ℂ) x‖) from
                funext fun x => (ofReal_norm _).symm]
            exact (ofReal_integral_eq_lintegral_ofReal (B1.integrable.norm)
                (Filter.Eventually.of_forall fun x => norm_nonneg _)).symm
          rw [heq]
          exact ENNReal.ofReal_le_ofReal hB1int
        -- ### the multiplier constant and the Ionescu--Wainger bound
        set M2 : ℝ≥0 := Real.toNNReal (C_lt * (C_M * (max ((2 : ℝ) ^ (k + jj - 1)) 1)
            ^ (-(((M + 1 : ℕ) : ℝ))))) with hM2
        have hM2pos : (0 : ℝ≥0) < M2 := by
          rw [hM2]
          exact Real.toNNReal_pos.mpr (by positivity)
        have hM2real : (M2 : ℝ) = C_lt * (C_M * (max ((2 : ℝ) ^ (k + jj - 1)) 1)
            ^ (-(((M + 1 : ℕ) : ℝ)))) := by
          rw [hM2, Real.toNNReal_of_nonneg (by positivity)]
          rfl
        have hP2mass : eLpNorm ((P2 : SchwartzMap ℝ ℂ) : ℝ → ℂ) 1 (volume : Measure ℝ)
            ≤ ENNReal.ofReal (M2 : ℝ) := by
          rw [hM2real, hP2]
          refine (eLpNorm_cS_le B1 (lam (-v))).trans ?_
          refine (mul_le_mul' hB1mass (hLt (-v))).trans ?_
          rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤
            C_M * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(((M + 1 : ℕ) : ℝ))))]
          exact le_of_eq (congrArg ENNReal.ofReal (by
            rw [show C_M * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(((M + 1 : ℕ) : ℝ))) * C_lt
                = C_lt * (C_M * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(((M + 1 : ℕ) : ℝ)))) from by
              ring]))
        have hgood_v' : GoodMajorArcs ρ Cρ_iw l (-v) := GoodMajorArcs.mono_const hcIw_iw hgood_v
        have hIsLq : ∀ q' : ℝ, 1 < q' →
            IsLqMultiplierBound (ENNReal.ofReal q') (Φ2 : ℝ → ℂ) M2 := by
          intro q' hq'
          have hphi : ∀ ξ : ℝ, 𝓕 (P2 : ℝ → ℂ) ξ = (Φ2 : ℝ → ℂ) ξ :=
            fun ξ => (congrFun (SchwartzMap.fourier_coe P2) ξ).symm
          exact Work.KMTAreas.A7.etaMult_lqBound_finite (K := P2) hphi hP2mass
            (ENNReal.one_le_ofReal.mpr hq'.le) ENNReal.ofReal_ne_top
        have hIsLqStar : ∀ q' : ℝ, 1 < q' →
            IsLqMultiplierBound (ENNReal.ofReal q') (fun x => star (Φ2 x)) M2 :=
          fun q' hq' => Work.KMTAreas.A7.IsLqMultiplierBound_star (hIsLq q' hq')
        have hIW := hIwq l (-v) hgood_v' Φ2 M2 hΦ2support hIsLq hIsLqStar
        have hIW' : eLpNorm (fun n : ℤ =>
              iwConv (iwArithFreqs ρ l) (periodize (Φ2 : ℝ → ℂ)) f n)
            (ENNReal.ofReal q) (MeasureTheory.Measure.count : Measure ℤ)
            ≤ ENNReal.ofReal ((C_q * angleBracket l * M2 : ℝ≥0) : ℝ) *
              MeasureTheory.eLpNorm f (ENNReal.ofReal q)
                (MeasureTheory.Measure.count : Measure ℤ) :=
          Work.KMTAreas.A7.eLpNorm_iwConv_le_of_IWLqBound (iwArithFreqs ρ l) Φ2 hq
            (mul_pos (mul_pos hC_q (angleBracket_pos l)) hM2pos) hIW f
        -- ### the sampled mass of the third piece
        have hP3mass : ∑' j : ℤ, ‖(P3 : SchwartzMap ℝ ℂ) (j : ℝ)‖
            ≤ C_H * (2 : ℝ) ^ (k + v) * (max ((2 : ℝ) ^ (k + jj - 1)) 1)
                ^ (-(((M + 1 : ℕ) : ℝ))) := by
          exact hHigh k jj v hk_nonpos hjj_nonneg hkjj
        have hbnd'' : ∀ (M : ℕ), max ((2 : ℝ) ^ (k + jj - 1)) 1 ^ (-(((M + 1 : ℕ) : ℝ)))
            ≤ (4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹ * (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ)) := by
          intro M
          rw [show max ((2 : ℝ) ^ (k + jj - 1)) 1 = (2 : ℝ) ^ (k + jj - 1) from
              max_eq_left (one_le_zpow₀ (by norm_num) hkjj'),
            show max ((2 : ℝ) ^ k * D) 1 = (2 : ℝ) ^ k * D from
              max_eq_left (le_of_lt (by linarith [hcase']))]
          exact tailAbsorb (M := M) hkjj' hcase' hjj_ge
        have hP3sum : ∑' t : ℤ, ENNReal.ofReal ‖Rfac ρ l t * P3 (t : ℝ)‖
            ≤ ENNReal.ofReal (C_card * C_H * (4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹ *
                (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ))) := by
          have h1 : ∑' t : ℤ, ENNReal.ofReal ‖Rfac ρ l t * P3 (t : ℝ)‖
              ≤ ∑' t : ℤ, ENNReal.ofReal (((iwArithFreqs ρ l).card : ℝ) * ‖P3 (t : ℝ)‖) := by
            refine ENNReal.tsum_le_tsum fun t => ?_
            refine ENNReal.ofReal_le_ofReal ?_
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (norm_Rfac_le ρ l t) (norm_nonneg _)
          refine h1.trans ?_
          have h2 : ∑' t : ℤ, ENNReal.ofReal (((iwArithFreqs ρ l).card : ℝ) * ‖P3 (t : ℝ)‖)
              = ENNReal.ofReal (((iwArithFreqs ρ l).card : ℝ) * ∑' t : ℤ, ‖P3 (t : ℝ)‖) := by
            rw [show (fun t : ℤ => ENNReal.ofReal (((iwArithFreqs ρ l).card : ℝ) * ‖P3 (t : ℝ)‖))
                  = (fun t : ℤ => ENNReal.ofReal ((iwArithFreqs ρ l).card : ℝ) *
                      ENNReal.ofReal ‖P3 (t : ℝ)‖) from
                funext fun t => ENNReal.ofReal_mul (Nat.cast_nonneg _)]
            rw [ENNReal.tsum_mul_left,
              ← ENNReal.ofReal_tsum_of_nonneg (fun t => norm_nonneg _) (summable_schwartzSamples P3),
              ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          rw [h2]
          refine ENNReal.ofReal_le_ofReal ?_
          calc ((iwArithFreqs ρ l).card : ℝ) * (∑' t : ℤ, ‖P3 (t : ℝ)‖)
              ≤ ((iwArithFreqs ρ l).card : ℝ) *
                  (C_H * (2 : ℝ) ^ (k + v) * (max ((2 : ℝ) ^ (k + jj - 1)) 1)
                    ^ (-(((M + 1 : ℕ) : ℝ)))) :=
                mul_le_mul_of_nonneg_left hP3mass (Nat.cast_nonneg _)
            _ = (((iwArithFreqs ρ l).card : ℝ) * (2 : ℝ) ^ (k + v)) *
                  (C_H * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(((M + 1 : ℕ) : ℝ)))) := by ring
            _ ≤ C_card * (C_H * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(((M + 1 : ℕ) : ℝ)))) :=
                mul_le_mul_of_nonneg_right hCard_a (by positivity)
            _ = C_card * C_H * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(((M + 1 : ℕ) : ℝ))) := by ring
            _ ≤ C_card * C_H * ((4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹ *
                  (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ))) :=
                mul_le_mul_of_nonneg_left (hbnd'' M) (by positivity)
            _ = C_card * C_H * (4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹ *
                  (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ)) := by ring
        -- ### summability and the pointwise splitting
        have hsumm : ∀ (P : SchwartzMap ℝ ℂ) (n : ℤ),
            Summable (fun j : ℤ => (Rfac ρ l j * P (j : ℝ)) * f (n - j)) := by
          intro P n
          refine Summable.of_norm_bounded
            ((summable_schwartzSamples P).mul_left (((iwArithFreqs ρ l).card : ℝ) * (Bf : ℝ))) ?_
          intro j
          rw [norm_mul, norm_mul]
          calc ‖Rfac ρ l j‖ * ‖P (j : ℝ)‖ * ‖f (n - j)‖
              ≤ ((iwArithFreqs ρ l).card : ℝ) * ‖P (j : ℝ)‖ * (Bf : ℝ) :=
                mul_le_mul (mul_le_mul (norm_Rfac_le ρ l j) le_rfl (norm_nonneg _) (by positivity))
                  (hBf (n - j)) (norm_nonneg _) (by positivity)
            _ = ((iwArithFreqs ρ l).card : ℝ) * (Bf : ℝ) * ‖P (j : ℝ)‖ := by ring
        have hP1vanish : ∀ (n : ℤ), (c ≤ n ∧ n ≤ d) → ∀ j : ℤ,
            (Rfac ρ l j * P1 (j : ℝ)) * f (n - j) = 0 := by
          intro n _ j
          by_cases hj : (c - b) ≤ j
          · have h1 : (bmp jj) (j : ℝ) = 0 := by
              by_contra hb
              have hbs := bmp_support jj hb
              have h2 : (D : ℝ) ≤ (j : ℝ) := by rw [hD]; exact_mod_cast hj
              have h4 : (0 : ℝ) ≤ (j : ℝ) := by
                have : (0 : ℤ) ≤ j := by omega
                exact_mod_cast this
              rw [abs_of_nonneg h4] at hbs
              linarith [hbs, h2, hjj_lt]
            rw [hP1, mS_apply, h1]
            simp
          · have hj' : j < c - b := lt_of_not_ge hj
            have h1 : b < n - j := by omega
            have h2 : f (n - j) = 0 := hsupp (n - j) (Or.inr h1)
            rw [h2]
            simp
        have hsplit : ∀ n : ℤ, (c ≤ n ∧ n ≤ d) →
            Work.KMTContract.kmtProj ρ l k f n
              = (∑' j : ℤ, (Rfac ρ l j * P2 (j : ℝ)) * f (n - j))
                + (∑' j : ℤ, (Rfac ρ l j * P3 (j : ℝ)) * f (n - j)) := by
          intro n hn
          rw [kmtProj_eq_Rfac ρ l k f n, ← Summable.tsum_add (hsumm P2 n) (hsumm P3 n)]
          refine tsum_congr fun j => ?_
          rw [hpt (j : ℝ)]
          have hexp : (Rfac ρ l j * (P1 (j : ℝ) + P2 (j : ℝ) + P3 (j : ℝ))) * f (n - j)
              = (Rfac ρ l j * P1 (j : ℝ)) * f (n - j)
                + (Rfac ρ l j * P2 (j : ℝ)) * f (n - j)
                + (Rfac ρ l j * P3 (j : ℝ)) * f (n - j) := by ring
          rw [hexp, hP1vanish n hn j, zero_add]
        have hT2eq : ∀ n : ℤ, (∑' j : ℤ, (Rfac ρ l j * P2 (j : ℝ)) * f (n - j))
            = iwConv (iwArithFreqs ρ l) (periodize (Φ2 : ℝ → ℂ)) f n := by
          intro n
          rw [iwConv_eq_Rfac ρ l Φ2 f n]
          refine tsum_congr fun j => ?_
          rw [congrFun hΦ2fourier (j : ℝ)]
        -- ### the two pieces
        have hG2 : eLpNorm (fun n : ℤ => if c ≤ n ∧ n ≤ d then
              (∑' j : ℤ, (Rfac ρ l j * P2 (j : ℝ)) * f (n - j)) else 0)
            (ENNReal.ofReal q) (MeasureTheory.Measure.count : Measure ℤ)
            ≤ ENNReal.ofReal ((C_q * angleBracket l * M2 : ℝ≥0) : ℝ) *
              MeasureTheory.eLpNorm f (ENNReal.ofReal q)
                (MeasureTheory.Measure.count : Measure ℤ) := by
          refine (eLpNorm_mono (hf := by pw_aesm) (fun n => ?_)).trans hIW'
          by_cases hn : c ≤ n ∧ n ≤ d
          · rw [if_pos hn, hT2eq n]
          · rw [if_neg hn]
            simp only [norm_zero]
            positivity
        have hG3 : eLpNorm (fun n : ℤ => if c ≤ n ∧ n ≤ d then
              (∑' j : ℤ, (Rfac ρ l j * P3 (j : ℝ)) * f (n - j)) else 0)
            (ENNReal.ofReal q) (MeasureTheory.Measure.count : Measure ℤ)
            ≤ (∑' t : ℤ, ENNReal.ofReal ‖Rfac ρ l t * P3 (t : ℝ)‖) *
              MeasureTheory.eLpNorm f (ENNReal.ofReal q)
                (MeasureTheory.Measure.count : Measure ℤ) := by
          have hmono : eLpNorm (fun n : ℤ => if c ≤ n ∧ n ≤ d then
                (∑' j : ℤ, (Rfac ρ l j * P3 (j : ℝ)) * f (n - j)) else 0)
              (ENNReal.ofReal q) (MeasureTheory.Measure.count : Measure ℤ)
              ≤ eLpNorm (fun n : ℤ => ∑' j : ℤ, (Rfac ρ l j * P3 (j : ℝ)) * f (n - j))
                (ENNReal.ofReal q) (MeasureTheory.Measure.count : Measure ℤ) := by
            refine eLpNorm_mono (hf := by pw_aesm) (fun n => ?_)
            by_cases hn : c ≤ n ∧ n ≤ d
            · rw [if_pos hn]
            · rw [if_neg hn]
              simp only [norm_zero]
              positivity
          exact hmono.trans (offYoung_conv_count_le (p := q) hq.le
            (fun t : ℤ => Rfac ρ l t * P3 (t : ℝ)) f)
        -- ### the arithmetic
        have hA2real : ((C_q * angleBracket l * M2 : ℝ≥0) : ℝ)
            = (C_q : ℝ) * (max ((l : ℝ)) 1) * (M2 : ℝ) := by
          rw [angleBracket, max_comm]
          push_cast
          ring
        have hM2b : (M2 : ℝ) ≤ C_lt * C_M * ((4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹) *
            (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ)) := by
          rw [hM2real]
          calc C_lt * (C_M * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(((M + 1 : ℕ) : ℝ))))
              ≤ C_lt * (C_M * ((4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹ *
                    (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ)))) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (hbnd'' M) (by positivity))
                  (by positivity)
            _ = C_lt * C_M * ((4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹) *
                  (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ)) := by ring
        have hK1 : (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ)) ≤ 1 := by
          refine Real.rpow_le_one_of_one_le_of_nonpos (le_max_right _ _) ?_
          have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
          linarith
        have hK0 : (0 : ℝ) ≤ (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ)) := by positivity
        have hl1 : (1 : ℝ) ≤ max ((l : ℝ)) 1 := le_max_right _ _
        have hl0 : (0 : ℝ) ≤ max ((l : ℝ)) 1 := le_trans zero_le_one hl1
        have hCf4 : (C_q : ℝ) * C_lt * C_M * (4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹ +
            C_card * C_H * (4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹ ≤ Cf := by
          rw [hCf]
          have h1 : (0 : ℝ) ≤ C_card * C_H * (2 : ℝ) ^ (2 * (M : ℝ)) := by positivity
          have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (M : ℝ) * (C_pl : ℝ) := by positivity
          have h3 : (0 : ℝ) ≤ (4 : ℝ) ^ (M + 1) := by positivity
          nlinarith [h1, h2, h3]
        have hfinal : ((C_q * angleBracket l * M2 : ℝ≥0) : ℝ) +
              C_card * C_H * (4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹ *
                (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ))
            ≤ Cf * max ((l : ℝ)) 1 * (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ)) := by
          rw [hA2real]
          have hstep1 : (C_q : ℝ) * max ((l : ℝ)) 1 * (M2 : ℝ)
              ≤ (C_q : ℝ) * C_lt * C_M * (4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹ * max ((l : ℝ)) 1 *
                  (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ)) := by
            have h1 := mul_le_mul_of_nonneg_left hM2b
              (by positivity : (0 : ℝ) ≤ (C_q : ℝ) * max ((l : ℝ)) 1)
            calc (C_q : ℝ) * max ((l : ℝ)) 1 * (M2 : ℝ)
                ≤ (C_q : ℝ) * max ((l : ℝ)) 1 *
                    (C_lt * C_M * ((4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹) *
                      (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ))) := h1
              _ = (C_q : ℝ) * C_lt * C_M * (4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹ * max ((l : ℝ)) 1 *
                    (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ)) := by ring
          have hstep2 : C_card * C_H * (4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹ *
                (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ))
              ≤ C_card * C_H * (4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹ * max ((l : ℝ)) 1 *
                  (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ)) := by
            have h1 : (0 : ℝ) ≤ C_card * C_H * (4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹ *
                (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ)) := by positivity
            nlinarith [h1, hl1, hK0]
          calc (C_q : ℝ) * max ((l : ℝ)) 1 * (M2 : ℝ) +
                C_card * C_H * (4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹ *
                  (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ))
              ≤ (C_q : ℝ) * C_lt * C_M * (4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹ * max ((l : ℝ)) 1 *
                    (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ)) +
                  C_card * C_H * (4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹ * max ((l : ℝ)) 1 *
                    (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ)) := add_le_add hstep1 hstep2
            _ = (((C_q : ℝ) * C_lt * C_M * (4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹ +
                  C_card * C_H * (4 : ℝ) ^ (M + 1) * (2 : ℝ)⁻¹) * max ((l : ℝ)) 1) *
                    (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ)) := by ring
            _ ≤ (Cf * max ((l : ℝ)) 1) * (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ)) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCf4 hl0) hK0
            _ = Cf * max ((l : ℝ)) 1 * (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ)) := by ring
        -- ### the assembly
        have hwin : (fun n : ℤ => if c ≤ n ∧ n ≤ d then Work.KMTContract.kmtProj ρ l k f n else 0)
            = (fun n : ℤ => if c ≤ n ∧ n ≤ d then
                  (∑' j : ℤ, (Rfac ρ l j * P2 (j : ℝ)) * f (n - j)) else 0)
              + (fun n : ℤ => if c ≤ n ∧ n ≤ d then
                  (∑' j : ℤ, (Rfac ρ l j * P3 (j : ℝ)) * f (n - j)) else 0) := by
          funext n
          by_cases hn : c ≤ n ∧ n ≤ d
          · rw [if_pos hn, Pi.add_apply, if_pos hn, if_pos hn]
            exact hsplit n hn
          · rw [if_neg hn, Pi.add_apply, if_neg hn, if_neg hn, add_zero]
        have hcombine : eLpNorm (fun x : ℤ =>
              if c ≤ x ∧ x ≤ d then Work.KMTContract.kmtProj ρ l k f x else 0)
            (ENNReal.ofReal q) (MeasureTheory.Measure.count : Measure ℤ)
            ≤ ENNReal.ofReal (Cf * max ((l : ℝ)) 1 *
                (max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ))) *
              MeasureTheory.eLpNorm f (ENNReal.ofReal q)
                (MeasureTheory.Measure.count : Measure ℤ) := by
          rw [hwin]
          refine (eLpNorm_add_le (le_of_lt hq1)).trans ?_
          · refine (add_le_add hG2 hG3).trans ?_
            rw [← add_mul]
            refine mul_le_mul' ?_ le_rfl
            refine le_trans (add_le_add le_rfl hP3sum) ?_
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
            exact ENNReal.ofReal_le_ofReal hfinal
        refine hcombine.trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Cf * max ((l : ℝ)) 1),
          ENNReal.ofReal_mul (by positivity)]

  have hgoal' := hgoal
  have hwrap : ENNReal.ofReal Cf * ENNReal.ofReal (max ((l : ℝ)) 1) *
        ENNReal.ofReal ((max ((2 : ℝ) ^ k * D) 1) ^ (-(M : ℝ))) *
        MeasureTheory.eLpNorm f (ENNReal.ofReal q) (MeasureTheory.Measure.count : Measure ℤ)
      ≤ (Real.toNNReal Cf : ℝ≥0∞) *
        ENNReal.ofReal (max ((l : ℝ)) 1 *
          (max ((2 : ℝ) ^ k * ((c - b : ℤ) : ℝ)) 1) ^ (-(M : ℝ))) *
        MeasureTheory.eLpNorm f (ENNReal.ofReal q) (MeasureTheory.Measure.count : Measure ℤ) := by
    have hD' : D = ((c - b : ℤ) : ℝ) := rfl
    rw [hD']
    refine le_of_eq ?_
    have hCeq : (↑(Real.toNNReal Cf) : ℝ≥0∞) = ENNReal.ofReal Cf := rfl
    rw [ENNReal.ofReal_mul (le_trans zero_le_one (le_max_right _ _)), hCeq]
    ring
  exact hgoal'.trans hwrap

end

end Work.KMTAreas.A4
