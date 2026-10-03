import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.ftLp_coeff_integral
import Submission.Work.KMTAreas.A7.sublatticeShannonReproduction

/-!
# The `ℓ²`-band sublattice Shannon reproduction with a uniform coset bound

This file proves `Work.KMTAreas.A7Hi.sublatticeReproL2Band`: there is a universal constant `C`
such that for every `β > 0`, `q ≥ 1` with `β q ≤ 1/8` and every `r₀ : ℤ` there is a summable
kernel `K : ℤ → ℂ` with

* `∑'_l ‖K (q * l + s)‖ ≤ C` for every `s : ℤ` (uniformly in `s`, `β`, `q`, `r₀`), and
* `G x = ∑'_m G (q * m + r₀) · K (x - (q * m + r₀))` for every `G ∈ ℓ²(ℤ)` whose Fourier
  transform (an element of `L²(𝕋)`) vanishes off the arc `arcSet 0 β` — i.e. the samples of `G`
  on the coset `qℤ + r₀` reproduce `G` pointwise.

## The construction

`ψ ∈ 𝓢(ℝ,ℂ)` is a fixed bump (`1` on `[-1/2,1/2]`, `0` off `(-1,1)`), and for fixed `q`
one takes the multiplier `χ_q(ξ) = q · ψ(2qξ)` (which is `q` on `[-1/(4q), 1/(4q)] ⊇ [-β,β]` since
`β q ≤ 1/8`, and vanishes off `(-1/(2q), 1/(2q))`), and the kernel `K = 𝓕⁻χ_q` sampled at the
integers.  Because `𝓕⁻χ_q (x) = (1/2) · (𝓕⁻ψ)(x/(2q))`, the decay of `K` is that of a *fixed*
Schwartz function read at scale `1/(2q)`, which gives the uniform coset bound.

## The proof of the reproduction identity

The `L²`-band case is handled directly (no continuity of the band-limited function is available):
the Fourier coefficients of `G` are the circle integrals `G n = ∫_𝕋 𝓕G(θ) conj(e^{2πinθ}) dθ`
(`ftLp_coeff_integral`), the sum `∑'_m G(qm+r₀) K(x-(qm+r₀))` is exchanged with the integral by
dominated convergence, and the resulting pointwise identity
`∑'_m conj(e^{2πi(qm+r₀)θ}) K(x-(qm+r₀)) = conj(e^{2πixθ})` on the arc `arcSet 0 β` is the
Poisson/decimation identity `shannon_decimation_poisson` (the `j ≠ 0` terms of the decimation
vanish because the multiplier is `1` on the band and `0` outside `(-1/(2q),1/(2q))`).
-/

namespace Work.KMTAreas.A7Hi

open MeasureTheory Filter
open scoped FourierTransform Topology SchwartzMap BigOperators ENNReal

noncomputable section

/-- The frequency circle `𝕋 = ℝ/ℤ`, in the convention of the Ionescu–Wainger development. -/
abbrev Circ : Type := Work.BourgainPlan.IonescuWainger.Circle

/-! ## The fixed reference bump and the multiplier `χ_q` -/

/-- The reference bump on `ℝ`: `1` on `[-1/2, 1/2]`, `0` off `(-1,1)`. -/
def srbBump : ContDiffBump (0 : ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩

lemma srbBump_hasCompactSupport : HasCompactSupport (fun x : ℝ => (srbBump x : ℂ)) := by
  have h := HasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) srbBump.hasCompactSupport
    (by norm_num)
  convert h using 1
  ext x
  rfl

/-- The reference bump, as a Schwartz function. -/
def srbPsi : 𝓢(ℝ, ℂ) :=
  srbBump_hasCompactSupport.toSchwartzMap (Complex.ofRealCLM.contDiff.comp srbBump.contDiff)

lemma srbPsi_apply (x : ℝ) : (srbPsi : ℝ → ℂ) x = (srbBump x : ℂ) := rfl

lemma srbPsi_hasCompactSupport : HasCompactSupport (srbPsi : ℝ → ℂ) := by
  rw [show (srbPsi : ℝ → ℂ) = fun x => (srbBump x : ℂ) from funext srbPsi_apply]
  exact srbBump_hasCompactSupport

lemma srbPsi_eq_one {x : ℝ} (hx : |x| ≤ 1 / 2) : (srbPsi : ℝ → ℂ) x = 1 := by
  have h1 : (srbBump : ℝ → ℝ) x = 1 := by
    refine srbBump.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    exact hx
  rw [srbPsi_apply, h1]
  norm_num

lemma srbPsi_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : (srbPsi : ℝ → ℂ) x = 0 := by
  have h1 : (srbBump : ℝ → ℝ) x = 0 := by
    refine srbBump.zero_of_le_dist ?_
    rw [Real.dist_eq, sub_zero]
    exact hx
  rw [srbPsi_apply, h1]
  norm_num

/-- The values of the multiplier `χ_q`: `ξ ↦ q · ψ(2qξ)`. -/
def srbChiFun (q : ℕ) : ℝ → ℂ := fun ξ => (q : ℂ) * (srbPsi : ℝ → ℂ) (2 * (q : ℝ) * ξ)

lemma srbChiFun_contDiff (q : ℕ) : ContDiff ℝ (↑(⊤ : ℕ∞)) (srbChiFun q) := by
  refine ContDiff.mul contDiff_const ?_
  exact (srbPsi.smooth (⊤ : ℕ∞)).comp (contDiff_const.mul contDiff_id)

lemma srbChiFun_hasCompactSupport (q : ℕ) : HasCompactSupport (srbChiFun q) := by
  by_cases hq : q = 0
  · subst hq
    rw [show srbChiFun 0 = fun _ : ℝ => (0 : ℂ) from ?_]
    · exact HasCompactSupport.zero
    · funext ξ; simp [srbChiFun]
  · have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast hq
    have h2qne : (2 * (q : ℝ)) ≠ 0 := by
      have hpos : (0 : ℝ) < 2 * (q : ℝ) := by
        have : (0 : ℝ) < (q : ℝ) := lt_of_le_of_ne (by positivity) (Ne.symm hqne)
        linarith
      exact ne_of_gt hpos
    have h1 : HasCompactSupport (fun ξ : ℝ => (srbPsi : ℝ → ℂ) (2 * (q : ℝ) * ξ)) := by
      have h := srbPsi_hasCompactSupport.comp_homeomorph
        (Homeomorph.mulLeft₀ (2 * (q : ℝ)) h2qne)
      convert h using 1
      ext ξ
      rfl
    exact h1.comp_left (g := fun z : ℂ => (q : ℂ) * z) (by simp)

/-- The multiplier `χ_q = q · ψ(2q·)`, as a Schwartz function. -/
def srbChi (q : ℕ) : 𝓢(ℝ, ℂ) :=
  (srbChiFun_hasCompactSupport q).toSchwartzMap (srbChiFun_contDiff q)

lemma srbChi_coe (q : ℕ) : (srbChi q : ℝ → ℂ) = srbChiFun q := rfl

/-! ## The reproducing kernel -/

/-- The reproducing kernel, as a Schwartz function: the inverse Fourier transform of `χ_q`. -/
def srbK (q : ℕ) : 𝓢(ℝ, ℂ) := 𝓕⁻ (srbChi q)

lemma srbK_fourier (q : ℕ) : (𝓕 (srbK q : ℝ → ℂ)) = (srbChi q : ℝ → ℂ) := by
  have h1 : 𝓕 (srbK q) = srbChi q := by rw [srbK]; simp
  rw [← SchwartzMap.fourier_coe (srbK q), h1]

/-- The reproducing kernel on the lattice `ℤ`. -/
def srbKernel (q : ℕ) : ℤ → ℂ := fun n => (srbK q : ℝ → ℂ) (n : ℝ)

/-! ## Affine rescaling of the Fourier inversion integral -/

/-- Substitution `ξ ↦ u/a` in the Fourier inversion integral. -/
lemma srb_dilate (f : ℝ → ℂ) {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    (∫ ξ : ℝ, (𝐞 (ξ * x) : ℂ) * f (a * ξ))
      = |a⁻¹| * (∫ u : ℝ, (𝐞 (u * (x / a)) : ℂ) * f u) := by
  set g : ℝ → ℂ := fun u => (𝐞 (u * (x / a)) : ℂ) * f u with hgdef
  have h1 : (fun ξ : ℝ => (𝐞 (ξ * x) : ℂ) * f (a * ξ)) = fun ξ => g (a * ξ) := by
    funext ξ
    rw [hgdef]
    simp only []
    rw [show (a * ξ) * (x / a) = ξ * x from by field_simp]
  have h2 := Measure.integral_comp_mul_left g a
  rw [h1, h2, Complex.real_smul]

lemma srb_natCast_coeff (q : ℕ) (hq : 0 < q) :
    (q : ℂ) * (((2 * (q : ℝ))⁻¹ : ℝ) : ℂ) = (1 / 2 : ℂ) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqC : ((q : ℂ)) = (((q : ℝ)) : ℂ) := by push_cast; ring
  rw [hqC, ← Complex.ofReal_mul]
  have hreal : (q : ℝ) * (2 * (q : ℝ))⁻¹ = 1 / 2 := by
    rw [mul_inv_eq_iff_eq_mul₀]
    · ring
    · positivity
  rw [hreal]; norm_num

/-- **The kernel at scale `1/(2q)`**: `K(x) = (1/2) · (𝓕⁻ψ)(x/(2q))`. -/
lemma srbK_eq (q : ℕ) (hq : 0 < q) (x : ℝ) :
    (srbK q : ℝ → ℂ) x
      = (1 / 2) * ((𝓕⁻ srbPsi : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (x / (2 * (q : ℝ))) := by
  have hstep1 : (srbK q : ℝ → ℂ) x
      = ∫ ξ : ℝ, (𝐞 (ξ * x) : ℂ) * srbChiFun q ξ := by
    rw [srbK, SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
    apply integral_congr_ae
    filter_upwards with ξ
    simp only [Circle.smul_def, smul_eq_mul, Real.inner_apply]
    rfl
  rw [hstep1]
  have hc2 : (∫ ξ : ℝ, (𝐞 (ξ * x) : ℂ) * (srbChiFun q ξ))
      = ∫ ξ : ℝ, (𝐞 (ξ * x) : ℂ) * ((q : ℂ) * (srbPsi : ℝ → ℂ) (2 * (q : ℝ) * ξ)) := by
    apply integral_congr_ae
    filter_upwards with ξ
    rw [srbChiFun]
  rw [hc2]
  have hfac : (∫ ξ : ℝ, (𝐞 (ξ * x) : ℂ) * ((q : ℂ) * (srbPsi : ℝ → ℂ) (2 * (q : ℝ) * ξ)))
      = (q : ℂ) * (∫ ξ : ℝ, (𝐞 (ξ * x) : ℂ) * (srbPsi : ℝ → ℂ) (2 * (q : ℝ) * ξ)) := by
    have h : (∫ ξ : ℝ, (𝐞 (ξ * x) : ℂ) * ((q : ℂ) * (srbPsi : ℝ → ℂ) (2 * (q : ℝ) * ξ)))
        = ∫ ξ : ℝ, (q : ℂ) * ((𝐞 (ξ * x) : ℂ) * (srbPsi : ℝ → ℂ) (2 * (q : ℝ) * ξ)) := by
      apply integral_congr_ae; filter_upwards with ξ; ring
    rw [h, integral_const_mul]
  rw [hfac, srb_dilate (srbPsi : ℝ → ℂ) (a := 2 * (q : ℝ)) (by positivity) x]
  have hcoef : (q : ℂ) * ((↑|(2 * (q : ℝ))⁻¹| : ℂ)) = 1 / 2 := by
    rw [abs_of_pos (by positivity : (0 : ℝ) < (2 * (q : ℝ))⁻¹)]
    exact srb_natCast_coeff q hq
  have hI : (∫ u : ℝ, (𝐞 (u * (x / (2 * (q : ℝ)))) : ℂ) * (srbPsi : ℝ → ℂ) u)
      = ((𝓕⁻ srbPsi : 𝓢(ℝ, ℂ)) : ℝ → ℂ) (x / (2 * (q : ℝ))) := by
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
    apply integral_congr_ae
    filter_upwards with u
    simp only [Circle.smul_def, smul_eq_mul, Real.inner_apply]
  rw [← mul_assoc, hcoef, hI]

/-- The scaled decay of the kernel, with the decay constant of the *fixed* Schwartz function
`𝓕⁻ψ`. -/
lemma srbKernel_decay (q : ℕ) (hq : 0 < q) {C₂ : ℝ}
    (hC₂ : ∀ x : ℝ, ‖((𝓕⁻ srbPsi : 𝓢(ℝ, ℂ)) : ℝ → ℂ) x‖ ≤ C₂ * (1 + |x|) ^ (-2 : ℝ)) :
    ∀ n : ℤ, ‖srbKernel q n‖ ≤ (C₂ / 2) * (1 + |(n : ℝ)| / (2 * (q : ℝ))) ^ (-2 : ℝ) := by
  intro n
  rw [srbKernel, srbK_eq q hq (n : ℝ), norm_mul]
  have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h12]
  have hdiv : |(n : ℝ) / (2 * (q : ℝ))| = |(n : ℝ)| / (2 * (q : ℝ)) := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * (q : ℝ))]
  have hbd := hC₂ ((n : ℝ) / (2 * (q : ℝ)))
  rw [hdiv] at hbd
  calc (1 / 2) * ‖((𝓕⁻ srbPsi : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ((n : ℝ) / (2 * (q : ℝ)))‖
      ≤ (1 / 2) * (C₂ * (1 + |(n : ℝ)| / (2 * (q : ℝ))) ^ (-2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hbd (by norm_num)
    _ = (C₂ / 2) * (1 + |(n : ℝ)| / (2 * (q : ℝ))) ^ (-2 : ℝ) := by ring

/-! ## The uniform coset bound -/

lemma srb_cosetTest_pointwise {t : ℝ} {m : ℤ} (hm : |2 * t - (m : ℝ)| ≤ 1) (u : ℤ) :
    (1 + |(u : ℝ) / 2 + t|) ^ (-2 : ℝ) ≤ 4 * (1 + |(u : ℝ) + (m : ℝ)|) ^ (-2 : ℝ) := by
  have hu2 : |(u : ℝ) / 2 + t| = |(u : ℝ) + 2 * t| / 2 := by
    rw [show (u : ℝ) + 2 * t = 2 * ((u : ℝ) / 2 + t) by ring,
      abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring
  have h1 : |(u : ℝ) + (m : ℝ)| ≤ |(u : ℝ) + 2 * t| + |2 * t - (m : ℝ)| := by
    have he : (u : ℝ) + (m : ℝ) = ((u : ℝ) + 2 * t) + ((m : ℝ) - 2 * t) := by ring
    rw [he, abs_sub_comm (2 * t) (m : ℝ)]
    exact abs_add_le ((u : ℝ) + 2 * t) ((m : ℝ) - 2 * t)
  have h2 : |(u : ℝ) + (m : ℝ)| ≤ |(u : ℝ) + 2 * t| + 1 := by linarith
  have h3 : (1 + |(u : ℝ) + (m : ℝ)|) / 2 ≤ 1 + |(u : ℝ) / 2 + t| := by
    rw [hu2]; linarith
  have h4 := Real.rpow_le_rpow_of_nonpos (x := (1 + |(u : ℝ) + (m : ℝ)|) / 2)
    (y := 1 + |(u : ℝ) / 2 + t|) (by positivity) h3 (show (-2 : ℝ) ≤ 0 by norm_num)
  calc (1 + |(u : ℝ) / 2 + t|) ^ (-2 : ℝ)
      ≤ ((1 + |(u : ℝ) + (m : ℝ)|) / 2) ^ (-2 : ℝ) := h4
    _ = 4 * (1 + |(u : ℝ) + (m : ℝ)|) ^ (-2 : ℝ) := by
        rw [Real.div_rpow (by positivity) (show (0 : ℝ) ≤ 2 by norm_num) (-2 : ℝ),
          Work.KMTAreas.A7.shannon_two_rpow_neg_two]
        field_simp

/-- The discrete sum of the test function `(1 + |u/2 + t|)^{-2}` is uniformly bounded in `t`. -/
lemma srb_cosetTest_all (t : ℝ) :
    Summable (fun u : ℤ => (1 + |(u : ℝ) / 2 + t|) ^ (-2 : ℝ)) ∧
      (∑' u : ℤ, (1 + |(u : ℝ) / 2 + t|) ^ (-2 : ℝ))
        ≤ 4 * (∑' l : ℤ, (1 + |(l : ℝ)|) ^ (-2 : ℝ)) := by
  set m : ℤ := ⌊2 * t⌋ with hm
  have hm1 : |2 * t - (m : ℝ)| ≤ 1 := by
    rw [hm]
    have h1 : (((⌊2 * t⌋ : ℤ)) : ℝ) ≤ 2 * t := Int.floor_le (2 * t)
    have h2 : 2 * t < (((⌊2 * t⌋ : ℤ)) : ℝ) + 1 := Int.lt_floor_add_one (2 * t)
    rw [abs_le]; constructor <;> linarith
  have hpt : ∀ u : ℤ,
      (1 + |(u : ℝ) / 2 + t|) ^ (-2 : ℝ) ≤ 4 * (1 + |(u : ℝ) + (m : ℝ)|) ^ (-2 : ℝ) :=
    fun u => srb_cosetTest_pointwise hm1 u
  have hbase : Summable (fun l : ℤ => (1 + |(l : ℝ)|) ^ (-2 : ℝ)) :=
    Work.KMTAreas.A7.shannon_one_add_rpow_int_summable (b := 2) (by norm_num)
  have hsummR : Summable (fun u : ℤ => 4 * (1 + |(u : ℝ) + (m : ℝ)|) ^ (-2 : ℝ)) := by
    have hinj : Function.Injective (fun u : ℤ => u + m) := fun a b h => add_right_cancel h
    have h1 : Summable (fun u : ℤ => (1 + |((u + m : ℤ) : ℝ)|) ^ (-2 : ℝ)) :=
      hbase.comp_injective hinj
    have h2 : (fun u : ℤ => (1 + |((u + m : ℤ) : ℝ)|) ^ (-2 : ℝ))
        = fun u : ℤ => (1 + |(u : ℝ) + (m : ℝ)|) ^ (-2 : ℝ) := by
      funext u; rw [Int.cast_add]
    rw [h2] at h1
    exact h1.mul_left 4
  have hsummL : Summable (fun u : ℤ => (1 + |(u : ℝ) / 2 + t|) ^ (-2 : ℝ)) :=
    Summable.of_nonneg_of_le (fun u => Real.rpow_nonneg (by positivity) _)
      (fun u => hpt u) hsummR
  refine ⟨hsummL, ?_⟩
  calc (∑' u : ℤ, (1 + |(u : ℝ) / 2 + t|) ^ (-2 : ℝ))
      ≤ ∑' u : ℤ, 4 * (1 + |(u : ℝ) + (m : ℝ)|) ^ (-2 : ℝ) :=
        Summable.tsum_le_tsum hpt hsummL hsummR
    _ = 4 * (∑' u : ℤ, (1 + |(u : ℝ) + (m : ℝ)|) ^ (-2 : ℝ)) := tsum_mul_left
    _ = 4 * (∑' l : ℤ, (1 + |(l : ℝ)|) ^ (-2 : ℝ)) := by
        congr 1
        rw [← Equiv.tsum_eq (Equiv.addRight m) (fun l : ℤ => (1 + |(l : ℝ)|) ^ (-2 : ℝ))]
        apply tsum_congr
        intro u
        rw [Equiv.coe_addRight, Int.cast_add]

lemma srb_scaled_decay {q : ℕ} (hq : 0 < q) (n : ℤ) :
    (1 + |(n : ℝ)| / (2 * (q : ℝ))) ^ (-2 : ℝ)
      ≤ (2 * (q : ℝ)) ^ 2 * (1 + |(n : ℝ)|) ^ (-2 : ℝ) := by
  have h : (0 : ℝ) < 2 * (q : ℝ) := by positivity
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have h1 : (1 + |(n : ℝ)|) / (2 * (q : ℝ)) ≤ 1 + |(n : ℝ)| / (2 * (q : ℝ)) := by
    rw [div_le_iff₀ h]
    have hexp : (1 + |(n : ℝ)| / (2 * (q : ℝ))) * (2 * (q : ℝ)) = 2 * (q : ℝ) + |(n : ℝ)| := by
      rw [add_mul, one_mul, div_mul_cancel₀]
      exact ne_of_gt h
    rw [hexp]
    linarith
  have h2 := Real.rpow_le_rpow_of_nonpos (x := (1 + |(n : ℝ)|) / (2 * (q : ℝ)))
    (y := 1 + |(n : ℝ)| / (2 * (q : ℝ))) (by positivity) h1 (show (-2 : ℝ) ≤ 0 by norm_num)
  calc (1 + |(n : ℝ)| / (2 * (q : ℝ))) ^ (-2 : ℝ)
      ≤ ((1 + |(n : ℝ)|) / (2 * (q : ℝ))) ^ (-2 : ℝ) := h2
    _ = (2 * (q : ℝ)) ^ 2 * (1 + |(n : ℝ)|) ^ (-2 : ℝ) := by
        rw [Real.div_rpow (by positivity) (le_of_lt h) (-2 : ℝ), Real.rpow_neg (le_of_lt h)]
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        field_simp

/-- **The uniform coset bound.**  A kernel whose decay is that of a fixed Schwartz function at
scale `1/(2q)` is summable on `ℤ` and has uniformly bounded `ℓ¹`-mass on every coset `qℤ + d`,
with a constant depending only on the decay constant. -/
lemma srb_coset_bound :
    ∃ S : ℝ, 0 < S ∧
      ∀ (B : ℝ), 0 ≤ B → ∀ (q : ℕ), 0 < q → ∀ K : ℤ → ℂ,
        (∀ n : ℤ, ‖K n‖ ≤ B * (1 + |(n : ℝ)| / (2 * (q : ℝ))) ^ (-2 : ℝ)) →
        Summable (fun n : ℤ => ‖K n‖) ∧
        ∀ d : ℤ, Summable (fun u : ℤ => ‖K (q * u + d)‖) ∧
          (∑' u : ℤ, ‖K (q * u + d)‖) ≤ S * B := by
  have hbase : Summable (fun l : ℤ => (1 + |(l : ℝ)|) ^ (-2 : ℝ)) :=
    Work.KMTAreas.A7.shannon_one_add_rpow_int_summable (b := 2) (by norm_num)
  have hbase0 : 0 ≤ ∑' l : ℤ, (1 + |(l : ℝ)|) ^ (-2 : ℝ) :=
    tsum_nonneg (fun l => Real.rpow_nonneg (by positivity) _)
  refine ⟨4 * (∑' l : ℤ, (1 + |(l : ℝ)|) ^ (-2 : ℝ)) + 1, by linarith, ?_⟩
  intro B hB q hq K hK
  have hline : Summable (fun n : ℤ => ‖K n‖) := by
    have hmaj : Summable (fun n : ℤ => B * (2 * (q : ℝ)) ^ 2 * (1 + |(n : ℝ)|) ^ (-2 : ℝ)) :=
      hbase.mul_left (B * (2 * (q : ℝ)) ^ 2)
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hmaj
    calc ‖K n‖ ≤ B * (1 + |(n : ℝ)| / (2 * (q : ℝ))) ^ (-2 : ℝ) := hK n
      _ ≤ B * ((2 * (q : ℝ)) ^ 2 * (1 + |(n : ℝ)|) ^ (-2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (srb_scaled_decay hq n) hB
      _ = B * (2 * (q : ℝ)) ^ 2 * (1 + |(n : ℝ)|) ^ (-2 : ℝ) := by ring
  refine ⟨hline, fun d => ?_⟩
  set t : ℝ := (d : ℝ) / (2 * (q : ℝ)) with ht
  have hmain : ∀ u : ℤ, ‖K (q * u + d)‖ ≤ B * (1 + |(u : ℝ) / 2 + t|) ^ (-2 : ℝ) := by
    intro u
    refine (hK (q * u + d)).trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) hB)
    have hqq : (0 : ℝ) < 2 * (q : ℝ) := by positivity
    have harg : |(((q * u + d : ℤ)) : ℝ)| / (2 * (q : ℝ)) = |(u : ℝ) / 2 + t| := by
      have hcast : (((q * u + d : ℤ)) : ℝ) = (q : ℝ) * (u : ℝ) + (d : ℝ) := by push_cast; ring
      have heq : (q : ℝ) * (u : ℝ) + (d : ℝ)
          = (2 * (q : ℝ)) * ((u : ℝ) / 2 + (d : ℝ) / (2 * (q : ℝ))) := by field_simp
      rw [hcast, heq, abs_mul, abs_of_pos hqq, ht,
        mul_div_cancel_left₀ _ (ne_of_gt hqq)]
    rw [harg]
  have htest := srb_cosetTest_all t
  refine ⟨Summable.of_nonneg_of_le (fun u => norm_nonneg _) (fun u => hmain u)
    (htest.1.mul_left B), ?_⟩
  calc (∑' u : ℤ, ‖K (q * u + d)‖)
      ≤ ∑' u : ℤ, B * (1 + |(u : ℝ) / 2 + t|) ^ (-2 : ℝ) :=
        Summable.tsum_le_tsum hmain
          (Summable.of_nonneg_of_le (fun u => norm_nonneg _) (fun u => hmain u)
            (htest.1.mul_left B))
          (htest.1.mul_left B)
    _ = B * (∑' u : ℤ, (1 + |(u : ℝ) / 2 + t|) ^ (-2 : ℝ)) := tsum_mul_left
    _ ≤ B * (4 * (∑' l : ℤ, (1 + |(l : ℝ)|) ^ (-2 : ℝ))) :=
        mul_le_mul_of_nonneg_left htest.2 hB
    _ ≤ (4 * (∑' l : ℤ, (1 + |(l : ℝ)|) ^ (-2 : ℝ)) + 1) * B := by nlinarith [hbase0, hB]

/-! ## The Poisson sampling identity -/

/-- The Fourier monomial evaluated at a real point of the circle. -/
lemma srb_fourier_coe (n : ℤ) (η : ℝ) :
    fourier (T := 1) n ((η : ℝ) : Circ) = (𝐞 ((n : ℝ) * η) : ℂ) := by
  rw [fourier_coe_apply, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/-- The conjugate of the Fourier monomial evaluated at a real point of the circle. -/
lemma srb_star_fourier_coe (n : ℤ) (η : ℝ) :
    star (fourier (T := 1) n ((η : ℝ) : Circ)) = (𝐞 (-((n : ℝ) * η)) : ℂ) := by
  change (starRingEnd ℂ) ((fourier (T := 1) n) ((η : ℝ) : Circ)) = _
  rw [← fourier_neg]
  rw [fourier_coe_apply, Real.fourierChar_apply]
  congr 1
  push_cast
  ring

/-- **The Poisson/decimation sampling identity** in the form matching the reproducing sum:
for `|η| ≤ β` and `β q ≤ 1/4`, sampling the kernel along `qℤ + r₀` synthesises the character
`e^{2πiηx}`. -/
lemma srb_key (β : ℝ) (q : ℕ) (hq : 0 < q) (hβ4 : β * (q : ℝ) ≤ 1 / 4) (r₀ : ℤ) (x : ℤ)
    (η : ℝ) (hη : η ∈ Set.Icc (-β) β) :
    (∑' m : ℤ, (𝐞 (η * (((q * m + r₀ : ℤ)) : ℝ)) : ℂ)
        * ((srbK q : ℝ → ℂ) ((x : ℝ) - (((q * m + r₀ : ℤ)) : ℝ))))
      = (𝐞 (η * (x : ℝ)) : ℂ) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hβ2m : β * (2 * (q : ℝ)) ≤ 1 := by nlinarith [hβ4]
  have hchi1 : ∀ η ∈ Set.Icc (-β) β, (srbChi q : ℝ → ℂ) η = (q : ℂ) := by
    intro η hη
    rw [srbChi_coe]
    have h1 : |η| ≤ β := abs_le.mpr hη
    have h2 : |2 * (q : ℝ) * η| = 2 * (q : ℝ) * |η| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * (q : ℝ))]
    have h3 : 2 * (q : ℝ) * |η| ≤ 2 * (q : ℝ) * β := mul_le_mul_of_nonneg_left h1 (by positivity)
    have hg : |2 * (q : ℝ) * η| ≤ 1 / 2 := by rw [h2]; nlinarith [h3, hβ4]
    rw [srbChiFun, srbPsi_eq_one hg, mul_one]
  have hchi0 : ∀ η : ℝ, 1 / (2 * (q : ℝ)) ≤ |η| → (srbChi q : ℝ → ℂ) η = 0 := by
    intro η hη
    rw [srbChi_coe]
    have h2 : |2 * (q : ℝ) * η| = 2 * (q : ℝ) * |η| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * (q : ℝ))]
    have h4 : 2 * (q : ℝ) * (1 / (2 * (q : ℝ))) = 1 := by
      rw [← div_eq_mul_one_div, div_self (ne_of_gt (by positivity : (0 : ℝ) < 2 * (q : ℝ)))]
    have h5 : 2 * (q : ℝ) * (1 / (2 * (q : ℝ))) ≤ 2 * (q : ℝ) * |η| :=
      mul_le_mul_of_nonneg_left hη (by positivity)
    have hg : 1 ≤ |2 * (q : ℝ) * η| := by rw [h2]; linarith
    rw [srbChiFun, srbPsi_eq_zero hg, mul_zero]
  obtain ⟨Ck, hCk, hkbd⟩ := Work.KMTAreas.A7.shannon_schwartz_bound (srbK q)
  obtain ⟨Ci, hCi, hFbd⟩ := Work.KMTAreas.A7.shannon_schwartz_bound (srbChi q)
  have hC : 0 ≤ max Ck Ci := le_trans hCk (le_max_left _ _)
  have hkbdC : ∀ y : ℝ, ‖(srbK q : ℝ → ℂ) y‖ ≤ max Ck Ci * (1 + |y|) ^ (-2 : ℝ) := fun y =>
    (hkbd y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Real.rpow_nonneg (by positivity) _))
  have hFbdC : ∀ y : ℝ, ‖𝓕 (srbK q : ℝ → ℂ) y‖ ≤ max Ck Ci * (1 + |y|) ^ (-2 : ℝ) := by
    intro y
    rw [srbK_fourier]
    exact (hFbd y).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
      (Real.rpow_nonneg (by positivity) _))
  set s : ℤ → ℝ := fun m => (((q * m + r₀ : ℤ)) : ℝ) with hsdef
  set t : ℤ → ℝ := fun m => (x : ℝ) - s m with htdef
  have ht_eq : ∀ m : ℤ, t m = (x : ℝ) - (((q * m + r₀ : ℤ)) : ℝ) := by
    intro m; rw [htdef, hsdef]
  have hdec := Work.KMTAreas.A7.shannon_decimation_poisson (k := (srbK q : ℝ → ℂ))
    (srbK q).continuous (b := 2) (C := max Ck Ci) (by norm_num) hC hkbdC hFbdC
    (a := (q : ℝ)) hqR ((x : ℝ) - (r₀ : ℝ)) η
  have hsingle : ∀ j : ℤ, j ≠ 0 → (𝓕 (srbK q : ℝ → ℂ)) (η - (j : ℝ) / (q : ℝ))
      * (𝐞 (-((j : ℝ) / (q : ℝ) * ((x : ℝ) - (r₀ : ℝ)))) : ℂ) = 0 := by
    intro j hj
    rw [srbK_fourier, srbChi_coe, srbChiFun]
    have hz : (srbPsi : ℝ → ℂ) (2 * (q : ℝ) * (η - (j : ℝ) / (q : ℝ))) = 0 := by
      refine srbPsi_eq_zero ?_
      have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
        have h1 : (0 : ℤ) < |j| := abs_pos.mpr hj
        have h2 : (1 : ℤ) ≤ |j| := by omega
        exact_mod_cast h2
      have h2' : (1 : ℝ) / (q : ℝ) - β ≤ |η - (j : ℝ) / (q : ℝ)| := by
        have h := abs_add_le ((j : ℝ) / (q : ℝ) - η) η
        have he : (j : ℝ) / (q : ℝ) - η + η = (j : ℝ) / (q : ℝ) := by ring
        rw [he, abs_div, abs_of_pos hqR] at h
        have h3 : (1 : ℝ) / (q : ℝ) ≤ |(j : ℝ)| / (q : ℝ) :=
          div_le_div_of_nonneg_right hj1 hqR.le
        have h4 : |η| ≤ β := abs_le.mpr hη
        have h5 : |η - (j : ℝ) / (q : ℝ)| = |((j : ℝ) / (q : ℝ) - η)| := abs_sub_comm _ _
        linarith
      have h7 : 1 / (2 * (q : ℝ)) ≤ (1 : ℝ) / (q : ℝ) - β := by
        have hβ2 : β ≤ 1 / (2 * (q : ℝ)) := by
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (q : ℝ))]
          exact hβ2m
        have hkey : (1 : ℝ) / (q : ℝ) - 1 / (2 * (q : ℝ)) = 1 / (2 * (q : ℝ)) := by
          field_simp; ring
        linarith [hβ2, hkey]
      have h8 : 1 / (2 * (q : ℝ)) ≤ |η - (j : ℝ) / (q : ℝ)| := le_trans h7 h2'
      have hgeom : 2 * (q : ℝ) * (1 / (2 * (q : ℝ))) = 1 := by
        rw [← div_eq_mul_one_div, div_self (ne_of_gt (by positivity : (0 : ℝ) < 2 * (q : ℝ)))]
      have hmul : 2 * (q : ℝ) * (1 / (2 * (q : ℝ))) ≤ 2 * (q : ℝ) * |η - (j : ℝ) / (q : ℝ)| :=
        mul_le_mul_of_nonneg_left h8 (by positivity)
      rw [hgeom] at hmul
      have hfinal : |2 * (q : ℝ) * (η - (j : ℝ) / (q : ℝ))|
          = 2 * (q : ℝ) * |η - (j : ℝ) / (q : ℝ)| := by
        rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * (q : ℝ))]
      rw [hfinal]; exact hmul
    rw [hz]
    ring
  have hR : (∑' j : ℤ, (𝓕 (srbK q : ℝ → ℂ)) (η - (j : ℝ) / (q : ℝ))
      * (𝐞 (-((j : ℝ) / (q : ℝ) * ((x : ℝ) - (r₀ : ℝ)))) : ℂ)) = (q : ℂ) := by
    calc (∑' j : ℤ, (𝓕 (srbK q : ℝ → ℂ)) (η - (j : ℝ) / (q : ℝ))
        * (𝐞 (-((j : ℝ) / (q : ℝ) * ((x : ℝ) - (r₀ : ℝ)))) : ℂ))
        = (𝓕 (srbK q : ℝ → ℂ)) (η - ((0 : ℤ) : ℝ) / (q : ℝ))
          * (𝐞 (-((((0 : ℤ) : ℝ) / (q : ℝ)) * ((x : ℝ) - (r₀ : ℝ)))) : ℂ) :=
          tsum_eq_single (0 : ℤ) hsingle
      _ = (q : ℂ) := by
          rw [srbK_fourier]
          have h1 : (srbChi q : ℝ → ℂ) η = (q : ℂ) := hchi1 η hη
          simp [h1]
  have hD : (∑' m : ℤ, (srbK q : ℝ → ℂ) (t m) * (𝐞 (-(η * t m)) : ℂ)) = 1 := by
    have hD' : (∑' m : ℤ, (srbK q : ℝ → ℂ) ((x : ℝ) - (r₀ : ℝ) - (q : ℝ) * (m : ℝ))
        * (𝐞 (-(η * ((x : ℝ) - (r₀ : ℝ) - (q : ℝ) * (m : ℝ)))) : ℂ)) = 1 := by
      rw [hdec, hR]
      have hqC : ((q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hqR.ne'
      rw [← Complex.ofReal_natCast]
      exact inv_mul_cancel₀ hqC
    rw [← hD']
    apply tsum_congr
    intro m
    have harg : t m = (x : ℝ) - (r₀ : ℝ) - (q : ℝ) * (m : ℝ) := by
      rw [ht_eq m]; push_cast; ring
    rw [harg]
  have h1 : (∑' m : ℤ, (𝐞 (η * s m) : ℂ) * (srbK q : ℝ → ℂ) (t m))
      = (𝐞 (η * (x : ℝ)) : ℂ)
        * (∑' m : ℤ, (srbK q : ℝ → ℂ) (t m) * (𝐞 (-(η * t m)) : ℂ)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    have hs : s m = (x : ℝ) - t m := by rw [htdef, hsdef]; ring
    have harg : η * ((x : ℝ) - t m) = η * (x : ℝ) + -(η * t m) := by ring
    rw [hs, harg, ← Work.KMTAreas.A7.shannon_fourierChar_mul]
    ring
  rw [h1, hD, mul_one]

/-- The sampling identity, in the form used by the `ℓ²` reproduction: for `θ` in the arc
`arcSet 0 β` the conjugate characters along `qℤ + r₀` synthesise `conj (e^{2πixθ})`. -/
lemma srb_key_circle {β : ℝ} {q : ℕ} (hq : 0 < q) (hβ4 : β * (q : ℝ) ≤ 1 / 4) (r₀ : ℤ)
    (x : ℤ) {θ : Circ} (hθ : θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 β) :
    (∑' m : ℤ, star (fourier (T := 1) (q * m + r₀) θ) * srbKernel q (x - (q * m + r₀)))
      = star (fourier (T := 1) x θ) := by
  obtain ⟨η, hηabs, hθeq⟩ := hθ
  have hη : η ∈ Set.Icc (-β) β := abs_le.mp hηabs
  have hneg : -η ∈ Set.Icc (-β) β := by
    simp only [Set.mem_Icc] at hη ⊢
    exact ⟨by linarith [hη.2], by linarith [hη.1]⟩
  have hR : star (fourier (T := 1) x θ) = (𝐞 ((-η) * (x : ℝ)) : ℂ) := by
    rw [hθeq, zero_add, srb_star_fourier_coe]
    have harg : -((x : ℝ) * η) = (-η) * (x : ℝ) := by ring
    rw [harg]
  rw [hR, ← srb_key β q hq hβ4 r₀ x (-η) hneg]
  apply tsum_congr
  intro m
  have h1 : star (fourier (T := 1) (q * m + r₀) θ)
      = (𝐞 ((-η) * (((q * m + r₀ : ℤ)) : ℝ)) : ℂ) := by
    rw [hθeq, zero_add, srb_star_fourier_coe]
    have harg : -(((((q * m + r₀ : ℤ)) : ℝ)) * η) = (-η) * ((((q * m + r₀ : ℤ)) : ℝ)) := by ring
    rw [harg]
  have h2 : ((srbK q : ℝ → ℂ) ((x : ℝ) - (((q * m + r₀ : ℤ)) : ℝ))) = srbKernel q (x - (q * m + r₀)) := by
    rw [srbKernel]
    congr 1
    push_cast
    ring
  rw [h1, h2]

/-! ## The `ℓ²`-band sublattice Shannon reproduction -/

theorem sublatticeReproL2Band :
    ∃ C : ℝ, 0 < C ∧
      ∀ (β : ℝ) (hβ : 0 < β) (q : ℕ) (hq : 0 < q) (hβq : β * (q : ℝ) ≤ 1 / 8) (r₀ : ℤ),
        ∃ K : ℤ → ℂ, Summable (fun m : ℤ => ‖K m‖) ∧
          (∀ s : ℤ, (∑' l : ℤ, ‖K (q * l + s)‖) ≤ C) ∧
          ∀ (G : ℤ → ℂ) (hG : Memℓp G 2)
            (hsupp : Work.BourgainPlan.IonescuWainger.HasFreqSupport G hG
              (Work.BourgainPlan.IonescuWainger.arcSet 0 β)) (x : ℤ),
            G x = ∑' m : ℤ, G (q * m + r₀) * K (x - (q * m + r₀)) := by
  obtain ⟨S, hSpos, hScoset⟩ := srb_coset_bound
  obtain ⟨C₂, hC₂, hC₂bd⟩ := Work.KMTAreas.A7.shannon_schwartz_bound (𝓕⁻ srbPsi)
  have hC2pos : 0 ≤ C₂ / 2 := by linarith
  refine ⟨S * (C₂ / 2) + 1, by nlinarith [hSpos, hC2pos], ?_⟩
  intro β hβ q hq hβq r₀
  have hβ4 : β * (q : ℝ) ≤ 1 / 4 := by linarith
  have hdecay := srbKernel_decay q hq hC₂bd
  obtain ⟨hKsumm, hKcosetall⟩ := hScoset (C₂ / 2) hC2pos q hq (srbKernel q) hdecay
  refine ⟨srbKernel q, hKsumm, fun s => ?_, ?_⟩
  · have := (hKcosetall s).2
    linarith
  · intro G hG hsupp x
    set μ := AddCircle.haarAddCircle (T := 1) with hμdef
    set F : Circ → ℂ := (Work.BourgainPlan.IonescuWainger.ftLp G hG : Circ → ℂ) with hFdef
    have hsupp' : ∀ᵐ θ ∂μ, θ ∉ Work.BourgainPlan.IonescuWainger.arcSet 0 β → F θ = 0 := by
      rw [hμdef, hFdef]
      exact hsupp
    have hcoeff : ∀ n : ℤ, G n = ∫ θ : Circ, F θ * star (fourier (T := 1) n θ) ∂μ := by
      intro n
      rw [hFdef, hμdef]
      exact Work.BourgainPlan.IonescuWainger.ftLp_coeff_integral hG n
    have hFmem : MemLp F 2 μ := by
      rw [hFdef, hμdef]
      exact Lp.memLp (Work.BourgainPlan.IonescuWainger.ftLp G hG)
    have hFasm : AEStronglyMeasurable F μ := hFmem.aestronglyMeasurable
    have hFint : Integrable F μ := hFmem.integrable (by norm_num)
    have hFnint : Integrable (fun θ => ‖F θ‖) μ := hFint.norm
    have hshift : Summable (fun m : ℤ => ‖srbKernel q (x - (q * m + r₀))‖) := by
      have hinj1 : Function.Injective (fun m : ℤ => (q : ℤ) * m + r₀) := by
        intro a b hab
        have h1 : (q : ℤ) * a = (q : ℤ) * b := add_right_cancel hab
        exact mul_left_cancel₀ (by exact_mod_cast hq.ne' : ((q : ℤ)) ≠ 0) h1
      have hinj2 : Function.Injective (fun y : ℤ => x - y) := by
        intro a b hab
        exact sub_right_inj.mp hab
      exact hKsumm.comp_injective (hinj2.comp hinj1)
    have hsumm_arc : ∀ θ : Circ, θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 β →
        Summable (fun m : ℤ =>
          star (fourier (T := 1) (q * m + r₀) θ) * srbKernel q (x - (q * m + r₀))) := by
      intro θ hθ
      refine Summable.of_norm_bounded hshift (fun m => ?_)
      rw [norm_mul, norm_star, Work.BourgainPlan.IonescuWainger.norm_fourier_apply', one_mul]
    have hpointwise : ∀ᵐ θ ∂μ, HasSum (fun m : ℤ =>
        F θ * star (fourier (T := 1) (q * m + r₀) θ) * srbKernel q (x - (q * m + r₀)))
        (F θ * star (fourier (T := 1) x θ)) := by
      filter_upwards [hsupp'] with θ hθ
      by_cases hmem : θ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 β
      · have hkey := srb_key_circle (β := β) (q := q) hq hβ4 r₀ x hmem
        have hscaled : Summable (fun m : ℤ =>
            F θ * star (fourier (T := 1) (q * m + r₀) θ) * srbKernel q (x - (q * m + r₀))) := by
          rw [show (fun m : ℤ => F θ * star (fourier (T := 1) (q * m + r₀) θ)
                * srbKernel q (x - (q * m + r₀)))
              = fun m : ℤ => F θ * (star (fourier (T := 1) (q * m + r₀) θ)
                * srbKernel q (x - (q * m + r₀))) from funext fun m => (mul_assoc _ _ _)]
          exact (hsumm_arc θ hmem).mul_left (F θ)
        have htsum : (∑' m : ℤ, F θ * star (fourier (T := 1) (q * m + r₀) θ)
            * srbKernel q (x - (q * m + r₀))) = F θ * star (fourier (T := 1) x θ) := by
          rw [show (fun m : ℤ => F θ * star (fourier (T := 1) (q * m + r₀) θ)
                * srbKernel q (x - (q * m + r₀)))
              = fun m : ℤ => F θ * (star (fourier (T := 1) (q * m + r₀) θ)
                * srbKernel q (x - (q * m + r₀))) from funext fun m => (mul_assoc _ _ _)]
          rw [tsum_mul_left, hkey]
        rw [← htsum]
        exact hscaled.hasSum
      · rw [hθ hmem]
        simp only [zero_mul]
        exact hasSum_zero
    have hmain : HasSum (fun m : ℤ => ∫ θ, F θ * star (fourier (T := 1) (q * m + r₀) θ)
          * srbKernel q (x - (q * m + r₀)) ∂μ)
        (∫ θ, F θ * star (fourier (T := 1) x θ) ∂μ) :=
      hasSum_integral_of_dominated_convergence
        (fun (m : ℤ) (θ : Circ) => ‖F θ‖ * ‖srbKernel q (x - (q * m + r₀))‖)
        (fun m => ((hFasm.mul ((continuous_star.comp
          (fourier (T := 1) (q * m + r₀)).continuous)).aestronglyMeasurable)).mul_const _)
        (fun m => Filter.Eventually.of_forall (fun θ => by
          rw [norm_mul, norm_mul, norm_star,
            Work.BourgainPlan.IonescuWainger.norm_fourier_apply', mul_one]))
        (Filter.Eventually.of_forall (fun θ => hshift.mul_left ‖F θ‖))
        (by
          have h : (fun θ : Circ => ∑' m : ℤ, ‖F θ‖ * ‖srbKernel q (x - (q * m + r₀))‖)
              = fun θ => ‖F θ‖ * (∑' m : ℤ, ‖srbKernel q (x - (q * m + r₀))‖) := by
            funext θ; rw [tsum_mul_left]
          rw [h]
          exact hFnint.mul_const _)
        hpointwise
    have hgoal : (∑' m : ℤ, G (q * m + r₀) * srbKernel q (x - (q * m + r₀))) = G x := by
      rw [hcoeff x, ← hmain.tsum_eq]
      apply tsum_congr
      intro m
      rw [hcoeff (q * m + r₀), integral_mul_const]
    rw [hgoal]

end

end Work.KMTAreas.A7Hi
