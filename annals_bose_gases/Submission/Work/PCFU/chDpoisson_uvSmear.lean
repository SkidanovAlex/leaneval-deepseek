import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Submission.Work.BoseB7AK.W1rows.W1hat_abs_le
import Submission.Work.PCFU.chDconv_continuous_decay
import Submission.Work.PCFU.chDconv_kinFT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace Work.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-!
# `Work.PCFU.chDpoisson_uvSmear`

The Poisson-summation identity of the `(D)`-channel alias slot, in its **convolution form**

    KχfrU v h μ fu N z = Σ'_d (χ_ℓ ⋆ uvSmear(W₁))(z + ℓ•d) ,    ℓ = ellH v μ .

## Route

The Fourier series of the periodisation `P(y) = Σ'_d F(y + ℓ d)` of `F := χ_ℓ ⋆ uvSmear(W₁)` is
`Σ'_m FT(F)(κ_m)e^{i⟪κ_m,z⟫}`; since `FT(F) = (ℓ³χ̂(ℓ·))·(ζ_Λ·Ŵ₁)` is compactly supported in
`‖p‖ < 2Λ = (2π/ℓ)(N/2)`, the lattice sum truncates to the label group `Lab N = (ZMod (2N+1))³`:

    Σ'_m FT(F)(κ_m)e^{i⟪κ_m,z⟫} = ℓ³ Σ_{k : Lab N} χ̂(ℓκ_k)·(ζ_Λ(κ_k)Ŵ₁(κ_k))·e^{i⟪κ_k,z⟫}
                                = ℓ³ Σ_{k : Lab N} hatChih k · W1h k · e^{i⟪κ_k,z⟫} ,

which is exactly `ℓ³ KχfrU`.  The file contains the two analytic inputs as delegated lemmas
(`chDconv_kinFT`: the value of `FT(F)`; `chDconv_continuous_decay`: the decay of `F`), the general
Poisson step `poisson_conv` (with the `Lab N` truncation and the cancellation of `ℓ³`), and the
final bookkeeping matching `uvCut·chat` with `W1h` and `χ̂(ℓ·)` with `hatChih` (using
`ellH v μ = sideAt μ (a v)`).
-/

/-- The smoothed convolution kernel `F(y) = ∫_w χ_ℓ(w)·uvSmear fu Λ W (y - w) dw`, as a complex
number. -/
private def chDsmear (ℓ Λ : ℝ) (fu : Work.BoseBoxFix.LowCut) (W : E3 → ℝ) : E3 → ℂ :=
  fun y => ((∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w
      * Work.BoseBoxFock.uvSmear fu Λ W (y - w) : ℝ) : ℂ)

/-! ## Lattice bookkeeping -/

private lemma kmomLab_eq_smul_latVec' (ℓ : ℝ) (N : ℕ) (k : Work.BoseBoxFock.Lab N) :
    Work.BoseBoxFock.kmomLab ℓ N k
      = (2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec (Work.BoseBoxFock.labVec N k) := by
  rw [Work.BoseBoxFock.kmomLab]
  have h : Work.BoseB4.vec (Work.BoseBoxFock.labVec N k)
      = (2 * Real.pi) • Work.BoseBoxFock.latVec (Work.BoseBoxFock.labVec N k) := by
    refine PiLp.ext fun i => ?_
    simp only [Work.BoseB4.vec, Work.BoseBoxFock.latVec, WithLp.ofLp_smul, WithLp.ofLp_toLp,
      Pi.smul_apply, smul_eq_mul]
  rw [h, smul_smul]
  congr 1
  rw [div_eq_mul_inv]
  ring

private lemma uvRad_pos_one_le' {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (hN : 1 ≤ N) :
    0 < Work.BoseBoxFock.uvRad ℓ N := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [Work.BoseBoxFock.uvRad]
  exact div_pos (mul_pos (div_pos (by positivity) hℓ) hNpos) (by norm_num)

private lemma uvCut_eq_zero_of_two_mul_le' {fu : Work.BoseBoxFix.LowCut} {Λ : ℝ} (hΛ : 0 < Λ)
    {k : E3} (hk : 2 * Λ ≤ ‖k‖) : Work.BoseBoxFock.uvCut fu Λ k = 0 := by
  rw [Work.BoseBoxFock.uvCut, fu.zero _ ?_]
  rw [le_div_iff₀ hΛ]
  linarith

private lemma uvCut_smul_latVec_eq_zero' {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} (hN : 1 ≤ N)
    (fu : Work.BoseBoxFix.LowCut) {m : Fin 3 → ℤ}
    (hm : (N : ℝ) / 2 ≤ ‖Work.BoseBoxFock.latVec m‖) :
    Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
      ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) = 0 := by
  refine uvCut_eq_zero_of_two_mul_le' (uvRad_pos_one_le' hℓ hN) ?_
  have hc : 0 < 2 * Real.pi / ℓ := by positivity
  have h2 : 2 * Work.BoseBoxFock.uvRad ℓ N = (2 * Real.pi / ℓ) * ((N : ℝ) / 2) := by
    rw [Work.BoseBoxFock.uvRad]; ring
  rw [h2, norm_smul, Real.norm_of_nonneg hc.le]
  exact mul_le_mul_of_nonneg_left hm hc.le

private lemma labVec_mk' (N : ℕ) {m : Fin 3 → ℤ}
    (hm : ∀ i : Fin 3, -(N : ℤ) ≤ m i ∧ m i ≤ (N : ℤ)) :
    Work.BoseBoxFock.labVec N (fun i => ((m i : ℤ) : ZMod (2 * N + 1))) = m := by
  funext i
  show (((m i : ℤ) : ZMod (2 * N + 1))).valMinAbs = m i
  haveI : NeZero (2 * N + 1) := ⟨by omega⟩
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_⟩
  rw [Set.mem_Ioc]
  obtain ⟨h1, h2⟩ := hm i
  constructor <;> omega

/-- A `ℤ³`-series supported in the `ℓ²`-ball of radius `N/2` is the `Lab N`-sum. -/
private lemma tsum_eq_labSum' (N : ℕ) {F : (Fin 3 → ℤ) → ℂ}
    (hF : ∀ m : Fin 3 → ℤ, (N : ℝ) / 2 ≤ ‖Work.BoseBoxFock.latVec m‖ → F m = 0) :
    (∑' m : Fin 3 → ℤ, F m) = ∑ k : Work.BoseBoxFock.Lab N, F (Work.BoseBoxFock.labVec N k) := by
  classical
  have hinj : Set.InjOn (Work.BoseBoxFock.labVec N)
      (↑(Finset.univ : Finset (Work.BoseBoxFock.Lab N)) : Set (Work.BoseBoxFock.Lab N)) :=
    fun a _ b _ hab => funext fun i => ZMod.valMinAbs_inj.mp (congrFun hab i)
  rw [tsum_eq_sum (s := (Finset.univ.image (Work.BoseBoxFock.labVec N) : Finset (Fin 3 → ℤ))) ?_,
    Finset.sum_image hinj]
  intro m hm
  by_contra hne
  have hlt : ‖Work.BoseBoxFock.latVec m‖ < (N : ℝ) := by
    by_contra hcon
    push_neg at hcon
    refine hne (hF m ?_)
    have hNnn : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hcoord : ∀ i : Fin 3, -(N : ℤ) ≤ m i ∧ m i ≤ (N : ℤ) := by
    intro i
    have h1 : |((m i : ℤ) : ℝ)| ≤ ‖Work.BoseBoxFock.latVec m‖ := by
      have h2 := PiLp.norm_apply_le (Work.BoseBoxFock.latVec m) i
      rwa [Work.BoseBoxFock.latVec_apply] at h2
    have h3 : |((m i : ℤ) : ℝ)| < (N : ℝ) := lt_of_le_of_lt h1 hlt
    have h4 : |((m i : ℤ) : ℝ)| ≤ (N : ℝ) := le_of_lt h3
    rw [abs_le] at h4
    exact ⟨by exact_mod_cast h4.1, by exact_mod_cast h4.2⟩
  exact hm (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, labVec_mk' N hcoord⟩)

/-! ## The two Poisson hypotheses, from the closed form -/

/-- **Rapid decay of the Fourier transform** of `chDsmear`, from its closed form: the transform is
`ℓ³χ̂(ℓp)·ζ_Λ(p)·Ŵ₁(p)`, hence vanishes for `2Λ ≤ ‖p‖` (`ζ_Λ = 0` above `2Λ`) and is bounded
by `ℓ³∫|W|` everywhere. -/
private lemma ftDecay_of_form {ℓ Λ : ℝ} (hℓ : 0 < ℓ) (hΛ : 0 < Λ) {W : E3 → ℝ}
    {fu : Work.BoseBoxFix.LowCut}
    (hform : ∀ p : E3, Submission.BoseGases.kinFT (chDsmear ℓ Λ fu W) p
        = ((ℓ ^ 3 : ℝ) : ℂ) * ((Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ)
          * ((Work.BoseBoxFock.uvCut fu Λ p * Work.BoseFixR.chat W p : ℝ) : ℂ)) :
    ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : E3,
      ‖Submission.BoseGases.kinFT (chDsmear ℓ Λ fu W) p‖ ≤ C * (1 + ‖p‖) ^ (-(n : ℤ)) := by
  intro n
  refine ⟨ℓ ^ 3 * (∫ x : E3, |W x|) * (1 + 2 * Λ) ^ n, by positivity, fun p => ?_⟩
  rw [hform p]
  have hWmass : (0 : ℝ) ≤ ∫ x : E3, |W x| := integral_nonneg fun x => abs_nonneg _
  have hC0 : (0 : ℝ) ≤ ℓ ^ 3 * (∫ x : E3, |W x|) := by positivity
  by_cases hp : 2 * Λ ≤ ‖p‖
  · have hcut : Work.BoseBoxFock.uvCut fu Λ p = 0 := uvCut_eq_zero_of_two_mul_le' hΛ hp
    have hz : ((ℓ ^ 3 : ℝ) : ℂ) * ((Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ)
        * ((Work.BoseBoxFock.uvCut fu Λ p * Work.BoseFixR.chat W p : ℝ) : ℂ) = 0 := by
      rw [hcut, zero_mul, Complex.ofReal_zero, mul_zero]
    rw [hz, norm_zero]
    positivity
  · push_neg at hp
    have h1 : |Work.BoseK15.corpusBox.hatChi (ℓ • p)| ≤ 1 :=
      Work.BoseK15.hatChi_le_one.1 (ℓ • p)
    have h2 : |Work.BoseBoxFock.uvCut fu Λ p| ≤ 1 := by
      rw [Work.BoseBoxFock.uvCut, abs_le]
      exact ⟨by linarith [fu.nonneg (‖p‖ / Λ)], fu.le_one _⟩
    have h3 : |Work.BoseFixR.chat W p| ≤ ∫ x : E3, |W x| :=
      Work.BoseB7AK.W1rows.abs_chat_le_integral_abs p
    have h1nn : (0 : ℝ) ≤ ℓ ^ 3 := by positivity
    have hb : ‖((ℓ ^ 3 : ℝ) : ℂ) * ((Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ)
        * ((Work.BoseBoxFock.uvCut fu Λ p * Work.BoseFixR.chat W p : ℝ) : ℂ)‖
        ≤ ℓ ^ 3 * (∫ x : E3, |W x|) := by
      rw [norm_mul, norm_mul]
      rw [show ‖((ℓ ^ 3 : ℝ) : ℂ)‖ = ℓ ^ 3 from by
            rw [Complex.norm_real, Real.norm_of_nonneg h1nn]]
      rw [show ‖((Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ)‖
            = |Work.BoseK15.corpusBox.hatChi (ℓ • p)| from by
            rw [Complex.norm_real, Real.norm_eq_abs]]
      rw [show ‖((Work.BoseBoxFock.uvCut fu Λ p * Work.BoseFixR.chat W p : ℝ) : ℂ)‖
            = |Work.BoseBoxFock.uvCut fu Λ p| * |Work.BoseFixR.chat W p| from by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]]
      have h4 : ℓ ^ 3 * |Work.BoseK15.corpusBox.hatChi (ℓ • p)| ≤ ℓ ^ 3 * 1 :=
        mul_le_mul_of_nonneg_left h1 h1nn
      have h5 : |Work.BoseBoxFock.uvCut fu Λ p| * |Work.BoseFixR.chat W p|
          ≤ 1 * (∫ x : E3, |W x|) :=
        mul_le_mul h2 h3 (abs_nonneg _) (by norm_num)
      calc ℓ ^ 3 * |Work.BoseK15.corpusBox.hatChi (ℓ • p)|
            * (|Work.BoseBoxFock.uvCut fu Λ p| * |Work.BoseFixR.chat W p|)
          ≤ (ℓ ^ 3 * 1) * (1 * (∫ x : E3, |W x|)) :=
            mul_le_mul h4 h5 (by positivity) (by positivity)
        _ = ℓ ^ 3 * (∫ x : E3, |W x|) := by ring
    calc ‖((ℓ ^ 3 : ℝ) : ℂ) * ((Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ)
          * ((Work.BoseBoxFock.uvCut fu Λ p * Work.BoseFixR.chat W p : ℝ) : ℂ)‖
        ≤ ℓ ^ 3 * (∫ x : E3, |W x|) := hb
      _ ≤ ℓ ^ 3 * (∫ x : E3, |W x|) * ((1 + 2 * Λ) ^ n * (1 + ‖p‖) ^ (-(n : ℤ))) :=
          le_mul_of_one_le_right hC0 (by
            rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, ← div_pow]
            exact one_le_pow₀ (by
              rw [le_div_iff₀ (by positivity)]
              linarith))
      _ = ℓ ^ 3 * (∫ x : E3, |W x|) * (1 + 2 * Λ) ^ n * (1 + ‖p‖) ^ (-(n : ℤ)) := by ring

/-! ## The general Poisson step -/

/-- **Poisson summation for the smoothed `χ`-convolution.**  The periodisation of
`F = χ_ℓ ⋆ uvSmear fu (uvRad ℓ N) W` has Fourier series with the truncated lattice sum; the
`ℓ³` of the sampling identity is cancelled against the `ℓ³` of `kinFT (χ_ℓ)`. -/
private theorem poisson_conv {ℓ : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ} {fu : Work.BoseBoxFix.LowCut}
    {N : ℕ} (hN : 1 ≤ N)
    (hcont : Continuous (fun y : E3 => ∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w
        * Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad ℓ N) W (y - w)))
    (hdec : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : E3,
        |∫ w : E3, Work.BoseK15.corpusBox.chiLam ℓ w
          * Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad ℓ N) W (y - w)|
        ≤ C * (1 + ‖y‖) ^ (-(n : ℤ)))
    (hform : ∀ p : E3, Submission.BoseGases.kinFT (chDsmear ℓ (Work.BoseBoxFock.uvRad ℓ N) fu W) p
        = ((ℓ ^ 3 : ℝ) : ℂ) * ((Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ)
          * ((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N) p
              * Work.BoseFixR.chat W p : ℝ) : ℂ))
    (z : E3) :
    (∑' d : Fin 3 → ℤ, chDsmear ℓ (Work.BoseBoxFock.uvRad ℓ N) fu W
        (z + ℓ • Work.BoseBoxFock.latVec d))
      = ∑ k : Work.BoseBoxFock.Lab N,
          ((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomLab ℓ N k) : ℝ) : ℂ)
          * ((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
                (Work.BoseBoxFock.kmomLab ℓ N k)
              * Work.BoseFixR.chat W (Work.BoseBoxFock.kmomLab ℓ N k) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) z : ℂ)) := by
  classical
  have hΛ : 0 < Work.BoseBoxFock.uvRad ℓ N := uvRad_pos_one_le' hℓ hN
  have hcontc : Continuous (chDsmear ℓ (Work.BoseBoxFock.uvRad ℓ N) fu W) :=
    Complex.continuous_ofReal.comp hcont
  have hdecc : ∀ n : ℕ, ∃ C : ℝ, ∀ y : E3,
      ‖chDsmear ℓ (Work.BoseBoxFock.uvRad ℓ N) fu W y‖ ≤ C * (1 + ‖y‖) ^ (-(n : ℤ)) := by
    intro n
    obtain ⟨C, -, hC⟩ := hdec n
    exact ⟨C, fun y => by
      rw [chDsmear, Complex.norm_real, Real.norm_eq_abs]
      exact hC y⟩
  have hFTc : ∀ n : ℕ, ∃ C : ℝ, ∀ p : E3,
      ‖Submission.BoseGases.kinFT (chDsmear ℓ (Work.BoseBoxFock.uvRad ℓ N) fu W) p‖
        ≤ C * (1 + ‖p‖) ^ (-(n : ℤ)) := by
    intro n
    obtain ⟨C, -, hC⟩ := ftDecay_of_form hℓ hΛ hform n
    exact ⟨C, hC⟩
  have hpois := Work.BoseBoxFock.latSampling_decay hℓ hcontc hdecc hFTc z
  set G : (Fin 3 → ℤ) → ℂ := fun m => (∫ x : E3,
      Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) x : ℂ)))
        * chDsmear ℓ (Work.BoseBoxFock.uvRad ℓ N) fu W x)
      * Complex.exp (Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) z : ℂ))
    with hG
  have hpois' : (∑' m : Fin 3 → ℤ, G m)
      = (↑ℓ : ℂ) ^ 3 * ∑' d : Fin 3 → ℤ, chDsmear ℓ (Work.BoseBoxFock.uvRad ℓ N) fu W
          (z + ℓ • Work.BoseBoxFock.latVec d) := by
    rw [hG]
    exact hpois
  have hvan : ∀ m : Fin 3 → ℤ, (N : ℝ) / 2 ≤ ‖Work.BoseBoxFock.latVec m‖ → G m = 0 := by
    intro m hm
    have hcut : Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
        ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) = 0 :=
      uvCut_smul_latVec_eq_zero' hℓ hN fu hm
    have hcut' : (Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
          ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m)
        * Work.BoseFixR.chat W ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) : ℝ) = 0 := by
      rw [hcut, zero_mul]
    simp only [hG]
    rw [show (∫ x : E3,
          Complex.exp (-(Complex.I * (inner ℝ ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) x : ℂ)))
            * chDsmear ℓ (Work.BoseBoxFock.uvRad ℓ N) fu W x)
        = Submission.BoseGases.kinFT (chDsmear ℓ (Work.BoseBoxFock.uvRad ℓ N) fu W)
            ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m) from rfl]
    rw [hform ((2 * Real.pi / ℓ) • Work.BoseBoxFock.latVec m), hcut', Complex.ofReal_zero,
      mul_zero, zero_mul]
  have hred : (∑' m : Fin 3 → ℤ, G m)
      = ∑ k : Work.BoseBoxFock.Lab N, G (Work.BoseBoxFock.labVec N k) :=
    tsum_eq_labSum' N hvan
  have hterm : ∀ k : Work.BoseBoxFock.Lab N, G (Work.BoseBoxFock.labVec N k)
      = ((ℓ ^ 3 : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomLab ℓ N k) : ℝ) : ℂ)
          * ((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
                (Work.BoseBoxFock.kmomLab ℓ N k)
              * Work.BoseFixR.chat W (Work.BoseBoxFock.kmomLab ℓ N k) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) z : ℂ)) := by
    intro k
    simp only [hG, ← kmomLab_eq_smul_latVec' ℓ N k]
    rw [show (∫ x : E3,
          Complex.exp (-(Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) x : ℂ)))
            * chDsmear ℓ (Work.BoseBoxFock.uvRad ℓ N) fu W x)
        = Submission.BoseGases.kinFT (chDsmear ℓ (Work.BoseBoxFock.uvRad ℓ N) fu W)
            (Work.BoseBoxFock.kmomLab ℓ N k) from rfl]
    rw [hform (Work.BoseBoxFock.kmomLab ℓ N k)]
  have hℓ3 : ((ℓ : ℂ)) ^ 3 ≠ 0 := by
    rw [← Complex.ofReal_pow]
    exact Complex.ofReal_ne_zero.mpr (pow_ne_zero 3 (ne_of_gt hℓ))
  have hsum : (∑ k : Work.BoseBoxFock.Lab N, ((ℓ ^ 3 : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomLab ℓ N k) : ℝ) : ℂ)
        * ((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
              (Work.BoseBoxFock.kmomLab ℓ N k)
            * Work.BoseFixR.chat W (Work.BoseBoxFock.kmomLab ℓ N k) : ℝ) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) z : ℂ)))
      = (ℓ : ℂ) ^ 3 * (∑ k : Work.BoseBoxFock.Lab N,
          ((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomLab ℓ N k) : ℝ) : ℂ)
          * ((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
                (Work.BoseBoxFock.kmomLab ℓ N k)
              * Work.BoseFixR.chat W (Work.BoseBoxFock.kmomLab ℓ N k) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) z : ℂ))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show ((ℓ ^ 3 : ℝ) : ℂ) = (ℓ : ℂ) ^ 3 from Complex.ofReal_pow ℓ 3]
    ring
  refine mul_left_cancel₀ hℓ3 ?_
  calc (ℓ : ℂ) ^ 3 * (∑' d : Fin 3 → ℤ, chDsmear ℓ (Work.BoseBoxFock.uvRad ℓ N) fu W
        (z + ℓ • Work.BoseBoxFock.latVec d))
      = ∑' m : Fin 3 → ℤ, G m := hpois'.symm
    _ = ∑ k : Work.BoseBoxFock.Lab N, G (Work.BoseBoxFock.labVec N k) := hred
    _ = ∑ k : Work.BoseBoxFock.Lab N, ((ℓ ^ 3 : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomLab ℓ N k) : ℝ) : ℂ)
          * ((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
                (Work.BoseBoxFock.kmomLab ℓ N k)
              * Work.BoseFixR.chat W (Work.BoseBoxFock.kmomLab ℓ N k) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) z : ℂ)) :=
        Finset.sum_congr rfl fun k _ => hterm k
    _ = (ℓ : ℂ) ^ 3 * (∑ k : Work.BoseBoxFock.Lab N,
          ((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomLab ℓ N k) : ℝ) : ℂ)
          * ((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad ℓ N)
                (Work.BoseBoxFock.kmomLab ℓ N k)
              * Work.BoseFixR.chat W (Work.BoseBoxFock.kmomLab ℓ N k) : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) z : ℂ))) := hsum

/-! ## The target -/

theorem chDpoisson_uvSmear {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {fu : Work.BoseBoxFix.LowCut} {N : ℕ}
    (hℓ0 : 0 < Work.BoseBox.sideAt μ (BoseGases.a v)) (hN : 1 ≤ N)
    (hI : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))
    (hcs : HasCompactSupport (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))
    (hev : ∀ x, Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) (-x)
        = Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x) (z : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z
      = ∑' d : Fin 3 → ℤ, Work.BoseBoxFock.PCFU.chDconv (Work.BoseBoxFock.ellH v μ)
          (Work.BoseBoxFock.PCFU.chDkerS (h := h) fu (Work.BoseBoxFock.ellH v μ) N)
          (z + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) := by
  classical
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  have hside : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
    rw [Work.BoseBoxFock.ellH, if_pos hℓ0]
  have hΛ : 0 < Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N :=
    uvRad_pos_one_le' hℓ hN
  -- the two analytic inputs
  have hcd := chDconv_continuous_decay (v := v) (h := h) (fu := fu)
    (ℓ := Work.BoseBoxFock.ellH v μ) (Λ := Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
    hℓ hΛ hI hcs
  have hform : ∀ p : E3,
      Submission.BoseGases.kinFT (chDsmear (Work.BoseBoxFock.ellH v μ)
          (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N) fu
          (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))) p
        = ((Work.BoseBoxFock.ellH v μ ^ 3 : ℝ) : ℂ)
          * ((Work.BoseK15.corpusBox.hatChi (Work.BoseBoxFock.ellH v μ • p) : ℝ) : ℂ)
          * ((Work.BoseBoxFock.uvCut fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N) p
              * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) p
              : ℝ) : ℂ) := by
    intro p
    exact chDconv_kinFT (v := v) (h := h) (fu := fu)
      (ℓ := Work.BoseBoxFock.ellH v μ)
      (Λ := Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N) hℓ hΛ hI hev p
  have hmain := poisson_conv (ℓ := Work.BoseBoxFock.ellH v μ)
    (W := Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (fu := fu) (N := N)
    hℓ hN hcd.1 hcd.2 hform z
  -- the `chDconv`/`chDkerS` unfolding
  have hconv_eq : ∀ u : E3,
      Work.BoseBoxFock.PCFU.chDconv (Work.BoseBoxFock.ellH v μ)
          (Work.BoseBoxFock.PCFU.chDkerS (h := h) fu (Work.BoseBoxFock.ellH v μ) N) u
        = chDsmear (Work.BoseBoxFock.ellH v μ)
            (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N) fu
            (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) u := by
    intro u
    dsimp only [Work.BoseBoxFock.PCFU.chDconv, Work.BoseBoxFock.PCFU.chDkerS, chDsmear]
    rw [show (∫ w : E3, ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
          * ((Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
              (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (u - w) : ℝ) : ℂ))
        = ∫ w : E3, (((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w)
              * (Work.BoseBoxFock.uvSmear fu (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
                  (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) (u - w)) : ℝ) : ℂ) from
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun w => (Complex.ofReal_mul _ _).symm)]
    exact integral_ofReal
  -- the identification of the label sum with `KχfrU`
  have hRHS : (∑ k : Work.BoseBoxFock.Lab N,
        ((Work.BoseK15.corpusBox.hatChi
              (Work.BoseBoxFock.ellH v μ • Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k)
            : ℝ) : ℂ)
        * ((Work.BoseBoxFock.uvCut fu
              (Work.BoseBoxFock.uvRad (Work.BoseBoxFock.ellH v μ) N)
              (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k)
            * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
              (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k) : ℝ) : ℂ)
        * Complex.exp (Complex.I *
            (inner ℝ (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k) z : ℂ)))
      = Work.BoseBoxFock.PCFU.KχfrU v h μ fu N z := by
    rw [Work.BoseBoxFock.PCFU.KχfrU]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Work.BoseBoxFock.W1h, Work.BoseBoxFock.hatChih, ← hside]
    push_cast
    ring
  rw [← hRHS, ← hmain]
  exact tsum_congr fun d => (hconv_eq (z + (Work.BoseBoxFock.ellH v μ)
    • Work.BoseBoxFock.latVec d)).symm

end Work.PCFU
