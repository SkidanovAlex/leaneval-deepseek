import Mathlib
import Submission.Work.Core.Gaussian
import Submission.Work.Radial.Basic
import Submission.Work.RadialSpace.Basic
import Submission.Work.RadialSpace.exists_contDiff_comp_sq
import Submission.Work.RadialSpace.iteratedDeriv_comp_sqrt_pow_mul_le
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.FunctionalEquations.DensityAux.composite_seminorm_smooth
import Submission.Work.FunctionalEquations.DensityAux.approx_onesided_smooth
import Submission.Work.FunctionalEquations.DensityAux.kills_compactProfile

/-!
# Density of the complex Gaussians among radial Schwartz functions

**Paper Lemma 3.3** (Cohn-Kumar-Miller-Radchenko-Viazovska, *Universal optimality of the
`E8` and Leech lattices and interpolation formulas*, Ann. of Math. 196 (2022)):
for a fixed `y > 0` the complex Gaussians `x ↦ exp (π i τ ‖x‖²)`, `Im τ = y`, span a dense
subspace of the radial complex Schwartz functions on `ℝ^D`.

Consequently a continuous linear functional `Λ` on `𝓢(ℝ^D, ℂ)` that vanishes on all those
Gaussians vanishes on every radial Schwartz function.

The proof follows the paper.  If `f` is radial Schwartz with profile `Ξ(s) = e^{π y s} f(√s e₁)`
on `[0, ∞)` (`DensityAux.dgp`), then `f(x) = e^{-π y ‖x‖²} Ξ(‖x‖²)`.  One approximates `Ξ`
in finitely many weighted seminorms by a globally smooth compactly supported `h`
(`approx_onesided_smooth`), which produces a Schwartz function `F_h(x) = e^{-π y ‖x‖²} h(‖x‖²)`
that `Λ` kills (`kills_compactProfile`, the paper's Fourier-inversion plus Riemann-sum step),
and whose difference from `f` has small Schwartz seminorms by `composite_seminorm_smooth`.
Since `Λ` is continuous, `Λ f = 0`.
-/

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

namespace Work.FunctionalEquations

namespace DensityAux

open LeanEval.Analysis.CKMRVInterpolation Work.Core
open Filter Topology
open scoped SchwartzMap ContDiff

variable {D : ℕ} [NeZero D]

/-! ### The de-Gaussed profile -/

/-- The de-Gaussed profile `s ↦ exp (π y s) · f (√s • e₁)` of `f`. -/
noncomputable def dgp (y : ℝ) (f : EuclideanSpace ℝ (Fin D) → ℂ) : ℝ → ℂ :=
  fun s => (Real.exp (Real.pi * y * s) : ℂ) * Work.Radial.profile f s

lemma dgp_apply (y : ℝ) (f : EuclideanSpace ℝ (Fin D) → ℂ) (s : ℝ) :
    dgp y f s = (Real.exp (Real.pi * y * s) : ℂ) * Work.Radial.profile f s := rfl

lemma norm_ofReal_coe (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  simpa [Complex.ofRealLI_apply, Real.norm_eq_abs] using Complex.ofRealLI.norm_map r

lemma norm_natCast_coe (n : ℕ) : ‖(n : ℂ)‖ = (n : ℝ) := by
  rw [← Complex.ofReal_natCast, norm_ofReal_coe, abs_of_nonneg (Nat.cast_nonneg n)]

/-- `Work.Radial.profile` is `Work.RadialSpace.profile` composed with `√·`. -/
lemma profile_eq_comp_sqrt_local (f : EuclideanSpace ℝ (Fin D) → ℂ) (t : ℝ) :
    Work.Radial.profile f t = Work.RadialSpace.profile f (Real.sqrt t) := by
  rw [Work.Radial.profile, Work.RadialSpace.profile, Work.Radial.axis,
    ← Work.Sampling.realIncl_eq_smul (n := D) (Real.sqrt t)]
  rfl

lemma radial_profile_norm_sq {f : EuclideanSpace ℝ (Fin D) → ℂ} (hf : Radial f)
    (x : EuclideanSpace ℝ (Fin D)) : f x = Work.Radial.profile f (‖x‖ ^ 2) := by
  have h1 : Work.Radial.profile f (‖x‖ ^ 2) =
      f (realIncl (n := D) (Real.sqrt (‖x‖ ^ 2))) := by
    rw [Work.Radial.profile, Work.Radial.axis,
      ← Work.Sampling.realIncl_eq_smul (n := D) (Real.sqrt (‖x‖ ^ 2))]
  rw [h1, Real.sqrt_sq (norm_nonneg x)]
  exact Work.RadialSpace.profile_eq_of_radial hf x

/-- For a radial `f`, `f x = exp (-π y ‖x‖²) · Ξ (‖x‖²)`. -/
lemma radial_eq_exp_mul_dgp (y : ℝ) {f : EuclideanSpace ℝ (Fin D) → ℂ}
    (hf : Radial f) (x : EuclideanSpace ℝ (Fin D)) :
    f x = (Real.exp (-(Real.pi * y * ‖x‖ ^ 2)) : ℂ) * dgp y f (‖x‖ ^ 2) := by
  rw [dgp_apply, radial_profile_norm_sq hf x]
  have h2 : Real.exp (-(Real.pi * y * ‖x‖ ^ 2)) *
      Real.exp (Real.pi * y * ‖x‖ ^ 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [← mul_assoc, ← Complex.ofReal_mul, h2, Complex.ofReal_one, one_mul]

/-- Smoothness on `[0, ∞)` of `s ↦ g (√s)` for even smooth `g`. -/
lemma contDiffOn_comp_sqrt {g : ℝ → ℂ} (hg : ContDiff ℝ Work.RadialSpace.Smooth g)
    (he : Function.Even g) :
    ContDiffOn ℝ Work.RadialSpace.Smooth (fun s : ℝ => g (Real.sqrt s)) (Set.Ici 0) := by
  obtain ⟨h, hsm, hgh⟩ := Work.RadialSpace.exists_contDiff_comp_sq hg he
  refine hsm.contDiffOn.congr (fun s hs => ?_)
  rw [hgh (Real.sqrt s), Real.sq_sqrt hs]

/-- Smoothness on `[0, ∞)` of `s ↦ exp (-(c s))` (coerced to `ℂ`). -/
lemma contDiffOn_exp_neg_mul (c : ℝ) :
    ContDiffOn ℝ Work.RadialSpace.Smooth (fun s : ℝ => (Real.exp (-(c * s)) : ℂ))
      (Set.Ici 0) := by
  have h1 : ContDiffOn ℝ Work.RadialSpace.Smooth (fun s : ℝ => -(c * s)) (Set.Ici 0) := by
    fun_prop
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn (Real.contDiff_exp.comp_contDiffOn h1)

/-- Smoothness on `[0, ∞)` of `s ↦ exp (c s)` (coerced to `ℂ`). -/
lemma contDiffOn_exp_mul (c : ℝ) :
    ContDiffOn ℝ Work.RadialSpace.Smooth (fun s : ℝ => (Real.exp (c * s) : ℂ))
      (Set.Ici 0) := by
  have h1 : ContDiffOn ℝ Work.RadialSpace.Smooth (fun s : ℝ => c * s) (Set.Ici 0) := by
    fun_prop
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn (Real.contDiff_exp.comp_contDiffOn h1)

/-- The de-Gaussed profile of a radial function whose profile is smooth is smooth on
`[0, ∞)`. -/
lemma contDiffOn_dgp (y : ℝ) {f : EuclideanSpace ℝ (Fin D) → ℂ} (hf : Radial f)
    (hfG : ContDiff ℝ Work.RadialSpace.Smooth (Work.RadialSpace.profile f)) :
    ContDiffOn ℝ Work.RadialSpace.Smooth (dgp y f) (Set.Ici 0) := by
  have heven : Function.Even (Work.RadialSpace.profile f) := Work.RadialSpace.profile_even hf
  have hcomp := contDiffOn_comp_sqrt hfG heven
  have hfun : dgp y f = fun s : ℝ => (Real.exp (Real.pi * y * s) : ℂ) *
      Work.RadialSpace.profile f (Real.sqrt s) := by
    funext s
    rw [dgp_apply, profile_eq_comp_sqrt_local]
  rw [hfun]
  exact (contDiffOn_exp_mul (Real.pi * y)).mul hcomp

/-! ### Weighted decay of the de-Gaussed profile -/

lemma hasDerivAt_exp_mul (c t : ℝ) :
    HasDerivAt (fun s : ℝ => (Real.exp (c * s) : ℂ)) ((c : ℂ) * (Real.exp (c * t) : ℂ)) t := by
  have h1 : HasDerivAt (fun s : ℝ => c * s) c t := by
    simpa using (hasDerivAt_id t).const_mul c
  have h2 : HasDerivAt (fun s : ℝ => (Real.exp (c * s) : ℂ))
      (((Real.exp (c * t) * c : ℝ)) : ℂ) t := (h1.exp).ofReal_comp
  rwa [show ((Real.exp (c * t) * c : ℝ) : ℂ) = (c : ℂ) * (Real.exp (c * t) : ℂ) from by
    push_cast; ring] at h2

lemma iteratedDeriv_exp_mul (c t : ℝ) (i : ℕ) :
    iteratedDeriv i (fun s : ℝ => (Real.exp (c * s) : ℂ)) t
      = (c : ℂ) ^ i * (Real.exp (c * t) : ℂ) := by
  induction i generalizing t with
  | zero => simp
  | succ i ih =>
    rw [iteratedDeriv_succ,
      show iteratedDeriv i (fun s : ℝ => (Real.exp (c * s) : ℂ))
        = fun t => (c : ℂ) ^ i * (Real.exp (c * t) : ℂ) from funext ih]
    rw [((hasDerivAt_exp_mul c t).const_mul ((c : ℂ) ^ i)).deriv, pow_succ]
    ring

lemma norm_exp_coe (x : ℝ) : ‖(Real.exp x : ℂ)‖ = Real.exp x := by
  rw [norm_ofReal_coe, abs_of_nonneg (Real.exp_pos x).le]

lemma norm_exp_neg_mul (c t : ℝ) :
    Real.exp (-(c * t)) * ‖(Real.exp (c * t) : ℂ)‖ = 1 := by
  rw [norm_ofReal_coe, abs_of_nonneg (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel,
    Real.exp_zero]

/-- **Weighted decay.**  For a Schwartz function `g` and `c ∈ ℝ`, the derivatives of
`s ↦ exp (c s) g (√s)` decay faster than any polynomial against the weight
`exp (-(c ·))`. -/
theorem decay_exp_sqrt (c : ℝ) (g : SchwartzMap ℝ ℂ) (he : Function.Even (⇑g)) :
    ∀ j K : ℕ, ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      (1 + t) ^ K * Real.exp (-(c * t)) *
        ‖iteratedDerivWithin j (fun s : ℝ => (Real.exp (c * s) : ℂ) * ⇑g (Real.sqrt s))
          (Set.Ici 0) t‖ ≤ ε := by
  intro j K ε hε
  choose C hC using fun i => Work.RadialSpace.iteratedDeriv_comp_sqrt_pow_mul_le g he i (K + 2)
  have hCnn : ∀ i, 0 ≤ C i := fun i =>
    le_trans (norm_nonneg _) (by simpa using hC i 1 le_rfl)
  set S : ℝ := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * |c| ^ i * (2 ^ K * C (j - i)) with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg (fun i _ => by
    have := hCnn (j - i)
    positivity)
  refine ⟨max 1 (S / ε + 1), fun t ht => ?_⟩
  have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
  have htS : S / ε + 1 ≤ t := le_trans (le_max_right _ _) ht
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  -- smoothness at `t > 0`
  have hF : ContDiffAt ℝ ((j : ℕ) : ℕ∞ω) (fun s : ℝ => (Real.exp (c * s) : ℂ)) t := by
    have h1 : ContDiffAt ℝ ((j : ℕ) : ℕ∞ω) (fun s : ℝ => c * s) t := by fun_prop
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp t
      ((Real.contDiff_exp.contDiffAt).comp t h1)
  have hG : ContDiffAt ℝ ((j : ℕ) : ℕ∞ω) (fun s : ℝ => ⇑g (Real.sqrt s)) t :=
    ((g.smooth (j : ℕ∞)).contDiffAt).comp t (Real.contDiffAt_sqrt (ne_of_gt htpos))
  rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) (hF.mul hG)
    (Set.mem_Ici.mpr htpos.le),
    show iteratedDeriv j (fun x : ℝ => (Real.exp (c * x) : ℂ) * ⇑g (Real.sqrt x)) t
      = iteratedDeriv j ((fun s : ℝ => (Real.exp (c * s) : ℂ)) *
          (fun s : ℝ => ⇑g (Real.sqrt s))) t from rfl,
    iteratedDeriv_mul hF hG]
  have hterm : ∀ i ∈ Finset.range (j + 1),
      (1 + t) ^ K * Real.exp (-(c * t)) *
        ‖(↑(j.choose i) : ℂ) * iteratedDeriv i (fun s : ℝ => (Real.exp (c * s) : ℂ)) t *
          iteratedDeriv (j - i) (fun s : ℝ => ⇑g (Real.sqrt s)) t‖
        ≤ (j.choose i : ℝ) * |c| ^ i * (2 ^ K * C (j - i)) / t ^ 2 := by
    intro i hi
    have hnorm : ‖(↑(j.choose i) : ℂ) * iteratedDeriv i (fun s : ℝ => (Real.exp (c * s) : ℂ)) t *
          iteratedDeriv (j - i) (fun s : ℝ => ⇑g (Real.sqrt s)) t‖
        = (j.choose i : ℝ) * (Real.exp (c * t) * |c| ^ i) *
          ‖iteratedDeriv (j - i) (fun s : ℝ => ⇑g (Real.sqrt s)) t‖ := by
      rw [iteratedDeriv_exp_mul, norm_mul, norm_mul, norm_mul, norm_natCast_coe, norm_pow,
        norm_ofReal_coe, norm_exp_coe]
      ring
    rw [hnorm]
    have hkey : ‖iteratedDeriv (j - i) (fun s : ℝ => ⇑g (Real.sqrt s)) t‖
        ≤ C (j - i) / t ^ (K + 2) := by
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact hC (j - i) t ht1
    have hle : (1 + t) ^ K ≤ (2 * t) ^ K :=
      pow_le_pow_left₀ (by positivity) (by linarith) K
    calc (1 + t) ^ K * Real.exp (-(c * t)) *
          ((j.choose i : ℝ) * (Real.exp (c * t) * |c| ^ i) *
            ‖iteratedDeriv (j - i) (fun s : ℝ => ⇑g (Real.sqrt s)) t‖)
        = (j.choose i : ℝ) * |c| ^ i *
            ((Real.exp (-(c * t)) * Real.exp (c * t)) *
              ((1 + t) ^ K * ‖iteratedDeriv (j - i) (fun s : ℝ => ⇑g (Real.sqrt s)) t‖)) := by
          ring
      _ = (j.choose i : ℝ) * |c| ^ i *
            ((1 + t) ^ K * ‖iteratedDeriv (j - i) (fun s : ℝ => ⇑g (Real.sqrt s)) t‖) := by
          rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
      _ ≤ (j.choose i : ℝ) * |c| ^ i * (2 ^ K * C (j - i) / t ^ 2) := by
          have h2 : (1 + t) ^ K * ‖iteratedDeriv (j - i) (fun s : ℝ => ⇑g (Real.sqrt s)) t‖
              ≤ 2 ^ K * C (j - i) / t ^ 2 := by
            calc (1 + t) ^ K * ‖iteratedDeriv (j - i) (fun s : ℝ => ⇑g (Real.sqrt s)) t‖
                ≤ (2 * t) ^ K * (C (j - i) / t ^ (K + 2)) :=
                  mul_le_mul hle hkey (norm_nonneg _) (by positivity)
              _ = 2 ^ K * C (j - i) / t ^ 2 := by
                  rw [mul_pow]
                  field_simp
                  ring
          exact mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (j.choose i : ℝ) * |c| ^ i * (2 ^ K * C (j - i)) / t ^ 2 := by ring
  have hsum : (1 + t) ^ K * Real.exp (-(c * t)) *
      ‖∑ i ∈ Finset.range (j + 1), (↑(j.choose i) : ℂ) *
        iteratedDeriv i (fun s : ℝ => (Real.exp (c * s) : ℂ)) t *
        iteratedDeriv (j - i) (fun s : ℝ => ⇑g (Real.sqrt s)) t‖
      ≤ S / t ^ 2 := by
    calc (1 + t) ^ K * Real.exp (-(c * t)) *
        ‖∑ i ∈ Finset.range (j + 1), (↑(j.choose i) : ℂ) *
          iteratedDeriv i (fun s : ℝ => (Real.exp (c * s) : ℂ)) t *
          iteratedDeriv (j - i) (fun s : ℝ => ⇑g (Real.sqrt s)) t‖
        ≤ (1 + t) ^ K * Real.exp (-(c * t)) *
          ∑ i ∈ Finset.range (j + 1), ‖(↑(j.choose i) : ℂ) *
            iteratedDeriv i (fun s : ℝ => (Real.exp (c * s) : ℂ)) t *
            iteratedDeriv (j - i) (fun s : ℝ => ⇑g (Real.sqrt s)) t‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ = ∑ i ∈ Finset.range (j + 1), (1 + t) ^ K * Real.exp (-(c * t)) *
            ‖(↑(j.choose i) : ℂ) * iteratedDeriv i (fun s : ℝ => (Real.exp (c * s) : ℂ)) t *
              iteratedDeriv (j - i) (fun s : ℝ => ⇑g (Real.sqrt s)) t‖ := by
          rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * |c| ^ i * (2 ^ K * C (j - i)) / t ^ 2 :=
          Finset.sum_le_sum hterm
      _ = S / t ^ 2 := by
          rw [hS, Finset.sum_div]
  have hfin : S / t ^ 2 ≤ ε := by
    have h1 : S ≤ ε * t := by
      have hh := (div_le_iff₀ hε).mp (by linarith : S / ε ≤ t)
      linarith
    have h2 : ε * t / t ^ 2 ≤ ε := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < t ^ 2)]
      nlinarith [hε, ht1]
    exact le_trans (div_le_div_of_nonneg_right h1 (by positivity)) h2
  exact le_trans hsum hfin

/-- Weighted decay for the de-Gaussed profile. -/
lemma dgp_decay (y : ℝ) (g : SchwartzMap ℝ ℂ) (he : Function.Even (⇑g))
    {f : EuclideanSpace ℝ (Fin D) → ℂ}
    (hfG : dgp y f = fun s : ℝ => (Real.exp ((Real.pi * y) * s) : ℂ) * ⇑g (Real.sqrt s)) :
    ∀ j K : ℕ, ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      (1 + t) ^ K * Real.exp (-(Real.pi * y * t)) *
        ‖iteratedDerivWithin j (dgp y f) (Set.Ici 0) t‖ ≤ ε :=
  fun j K ε hε => by
    simpa only [hfG] using decay_exp_sqrt (Real.pi * y) g he j K ε hε

/-! ### The Gaussian factor and compactly supported profiles -/

/-- The Gaussian factor `x ↦ exp (-π y ‖x‖²)`, as the coercion of a real exponential. -/
lemma contDiff_exp_neg (y : ℝ) :
    ContDiff ℝ Work.RadialSpace.Smooth (fun x : EuclideanSpace ℝ (Fin D) =>
      (Real.exp (-(Real.pi * y * ‖x‖ ^ 2)) : ℂ)) := by
  have h1 : ContDiff ℝ Work.RadialSpace.Smooth (fun x : EuclideanSpace ℝ (Fin D) =>
      -(Real.pi * y * ‖x‖ ^ 2)) := by
    have h2 : ContDiff ℝ Work.RadialSpace.Smooth
        (fun x : EuclideanSpace ℝ (Fin D) => ‖x‖ ^ 2) := contDiff_norm_sq ℝ
    exact (contDiff_const (c := Real.pi * y)).mul h2 |>.neg
  exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp h1)

/-- A function on `ℝ^D` vanishing outside a ball has compact support. -/
lemma hasCompactSupport_of_norm_le {F : EuclideanSpace ℝ (Fin D) → ℂ} {R : ℝ}
    (hR : ∀ x, R ≤ ‖x‖ → F x = 0) : HasCompactSupport F := by
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact]
  have hnorm : Tendsto (fun x : EuclideanSpace ℝ (Fin D) => ‖x‖) (cocompact _) atTop :=
    tendsto_norm_cocompact_atTop
  filter_upwards [hnorm.eventually (eventually_ge_atTop R)] with x hx
  exact hR x hx

/-- A function on `ℝ` vanishing outside a bounded interval has compact support. -/
lemma hasCompactSupport_of_abs_le {h : ℝ → ℂ} {R : ℝ}
    (hR : ∀ t : ℝ, R ≤ |t| → h t = 0) : HasCompactSupport h := by
  rw [hasCompactSupport_iff_eventuallyEq, Filter.coclosedCompact_eq_cocompact,
    cocompact_eq_atBot_atTop]
  change ∀ᶠ t in (atBot ⊔ atTop : Filter ℝ), h t = 0
  rw [Filter.eventually_sup]
  constructor
  · rw [Filter.eventually_atBot]
    exact ⟨-R, fun t ht => hR t (by linarith [neg_le_abs t])⟩
  · rw [Filter.eventually_atTop]
    exact ⟨R, fun t ht => hR t (by linarith [le_abs_self t])⟩

/-- **Conditional assembly.**  Assuming the approximation `Happrox` and the killing
`Hkill`, `Λ` vanishes on every radial Schwartz function. -/
theorem density_of_gaussians_of
    (y : ℝ) (hy : 0 < y)
    (Λ : 𝓢(EuclideanSpace ℝ (Fin D), ℂ) →L[ℂ] ℂ)
    (hkills : ∀ (τ : ℂ), τ.im = y → ∀ F : 𝓢(EuclideanSpace ℝ (Fin D), ℂ),
      (∀ x, F x = gaussianFun D τ x) → Λ F = 0)
    (Happrox : ∀ (Ξ : ℝ → ℂ), ContDiffOn ℝ Work.RadialSpace.Smooth Ξ (Set.Ici 0) →
      (∀ j K : ℕ, ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
        (1 + t) ^ K * Real.exp (-(Real.pi * y * t)) *
          ‖iteratedDerivWithin j Ξ (Set.Ici 0) t‖ ≤ ε) →
      ∀ (J K : ℕ) {ε : ℝ}, 0 < ε →
        ∃ h : ℝ → ℂ, ContDiff ℝ Work.RadialSpace.Smooth h ∧
          (∃ R : ℝ, ∀ t : ℝ, R ≤ |t| → h t = 0) ∧
          ∀ j : ℕ, j ≤ J → ∀ t : ℝ, 0 ≤ t →
            (1 + t) ^ K * ‖iteratedDerivWithin j
              (fun s : ℝ => Real.exp (-(Real.pi * y * s)) * (Ξ s - h s)) (Set.Ici 0) t‖ ≤ ε)
    (Hkill : ∀ (h : ℝ → ℂ), ContDiff ℝ Work.RadialSpace.Smooth h →
      (∃ R : ℝ, ∀ t : ℝ, R ≤ |t| → h t = 0) →
      ∀ (F : 𝓢(EuclideanSpace ℝ (Fin D), ℂ)),
        (∀ x, F x = (Real.exp (-(Real.pi * y * ‖x‖ ^ 2)) : ℂ) * h (‖x‖ ^ 2)) →
        Λ F = 0) :
    ∀ f : 𝓢(EuclideanSpace ℝ (Fin D), ℂ), Radial f → Λ f = 0 := by
  intro f hf
  set Ξ : ℝ → ℂ := dgp y (⇑f) with hΞdef
  have hGsm : ContDiff ℝ Work.RadialSpace.Smooth (Work.RadialSpace.profile (⇑f)) := by
    have h1 : ContDiff ℝ Work.RadialSpace.Smooth (⇑(Work.RadialSpace.profileCLM f)) :=
      (Work.RadialSpace.profileCLM f).smooth ⊤
    rwa [Work.RadialSpace.profileCLM_apply] at h1
  have hΞcont : ContDiffOn ℝ Work.RadialSpace.Smooth Ξ (Set.Ici 0) :=
    contDiffOn_dgp y hf hGsm
  have hGeven : Function.Even (⇑(Work.RadialSpace.profileCLM f)) := by
    rw [Work.RadialSpace.profileCLM_apply]
    exact Work.RadialSpace.profile_even hf
  have hΞfun : Ξ = fun s : ℝ => (Real.exp ((Real.pi * y) * s) : ℂ) *
      ⇑(Work.RadialSpace.profileCLM f) (Real.sqrt s) := by
    rw [hΞdef]
    funext s
    rw [dgp_apply, profile_eq_comp_sqrt_local, Work.RadialSpace.profileCLM_apply]
  have hΞdec : ∀ j K : ℕ, ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      (1 + t) ^ K * Real.exp (-(Real.pi * y * t)) *
        ‖iteratedDerivWithin j Ξ (Set.Ici 0) t‖ ≤ ε :=
    dgp_decay y (Work.RadialSpace.profileCLM f) hGeven hΞfun
  let hseq : ℕ → ℝ → ℂ := fun n =>
    Classical.choose (Happrox Ξ hΞcont hΞdec n n (by positivity : (0:ℝ) < 1 / ((n : ℝ) + 1)))
  have hseq_spec : ∀ n : ℕ, ContDiff ℝ Work.RadialSpace.Smooth (hseq n) ∧
      (∃ R : ℝ, ∀ t : ℝ, R ≤ |t| → hseq n t = 0) ∧
      ∀ j : ℕ, j ≤ n → ∀ t : ℝ, 0 ≤ t →
        (1 + t) ^ n * ‖iteratedDerivWithin j
          (fun s : ℝ => Real.exp (-(Real.pi * y * s)) * (Ξ s - hseq n s)) (Set.Ici 0) t‖
            ≤ 1 / ((n : ℝ) + 1) := by
    intro n
    exact Classical.choose_spec
      (Happrox Ξ hΞcont hΞdec n n (by positivity : (0:ℝ) < 1 / ((n : ℝ) + 1)))
  have hFexists : ∀ n : ℕ, ∃ F : 𝓢(EuclideanSpace ℝ (Fin D), ℂ),
      ∀ x, F x = (Real.exp (-(Real.pi * y * ‖x‖ ^ 2)) : ℂ) * hseq n (‖x‖ ^ 2) := by
    intro n
    obtain ⟨R, hR⟩ := (hseq_spec n).2.1
    have hsm : ContDiff ℝ Work.RadialSpace.Smooth (fun x : EuclideanSpace ℝ (Fin D) =>
        (Real.exp (-(Real.pi * y * ‖x‖ ^ 2)) : ℂ) * hseq n (‖x‖ ^ 2)) :=
      (contDiff_exp_neg y).mul ((hseq_spec n).1.comp (contDiff_norm_sq ℝ))
    have hsupp : HasCompactSupport (fun x : EuclideanSpace ℝ (Fin D) =>
        (Real.exp (-(Real.pi * y * ‖x‖ ^ 2)) : ℂ) * hseq n (‖x‖ ^ 2)) := by
      refine hasCompactSupport_of_norm_le (R := max R 1) (fun x hx => ?_)
      have hx1 : (1:ℝ) ≤ ‖x‖ := le_trans (le_max_right R 1) hx
      have hxR : R ≤ ‖x‖ ^ 2 := by
        have h2 : ‖x‖ ≤ ‖x‖ ^ 2 := by nlinarith [norm_nonneg x, hx1]
        exact le_trans (le_trans (le_max_left R 1) hx) h2
      have h3 : hseq n (‖x‖ ^ 2) = 0 := hR _ (by rw [abs_of_nonneg (sq_nonneg _)]; exact hxR)
      rw [h3, mul_zero]
    exact ⟨HasCompactSupport.toSchwartzMap hsupp hsm, fun x => rfl⟩
  let Fn : ℕ → 𝓢(EuclideanSpace ℝ (Fin D), ℂ) := fun n => Classical.choose (hFexists n)
  have hFn_spec : ∀ n x, Fn n x =
      (Real.exp (-(Real.pi * y * ‖x‖ ^ 2)) : ℂ) * hseq n (‖x‖ ^ 2) :=
    fun n => Classical.choose_spec (hFexists n)
  have hsub : ∀ n x, (f - Fn n) x = (fun s : ℝ =>
      (Real.exp (-(Real.pi * y * s)) : ℂ) * (Ξ s - hseq n s)) (‖x‖ ^ 2) := by
    intro n x
    have h1 : (f - Fn n) x = f x - Fn n x := rfl
    have h2 : f x = (Real.exp (-(Real.pi * y * ‖x‖ ^ 2)) : ℂ) * Ξ (‖x‖ ^ 2) := by
      rw [hΞdef, radial_eq_exp_mul_dgp y hf x]
    have h3 : Fn n x = (Real.exp (-(Real.pi * y * ‖x‖ ^ 2)) : ℂ) * hseq n (‖x‖ ^ 2) :=
      hFn_spec n x
    rw [h1, h2, h3]
    ring
  have hconv : ∀ k l : ℕ, Tendsto (fun n : ℕ =>
      (SchwartzMap.seminorm ℂ k l) (f - Fn n)) atTop (𝓝 0) := by
    intro k l
    obtain ⟨C, hC0, hC⟩ := composite_seminorm_smooth D k l
    have hbound : ∀ᶠ n : ℕ in atTop, (SchwartzMap.seminorm ℂ k l) (f - Fn n)
        ≤ C * (1 / ((n : ℝ) + 1)) := by
      refine eventually_atTop.mpr ⟨max l (k + 2 * l), fun n hn => ?_⟩
      have hln : l ≤ n := le_trans (le_max_left _ _) hn
      have hkn : k + 2 * l ≤ n := le_trans (le_max_right _ _) hn
      have hfun : (fun x : EuclideanSpace ℝ (Fin D) =>
          (fun s : ℝ => (Real.exp (-(Real.pi * y * s)) : ℂ) * (Ξ s - hseq n s)) (‖x‖ ^ 2))
          = ⇑(f - Fn n) := by
        funext x
        exact (hsub n x).symm
      have hmain := hC (fun s : ℝ => (Real.exp (-(Real.pi * y * s)) : ℂ) * (Ξ s - hseq n s))
        (1 / ((n : ℝ) + 1)) ?hcont ?hbound'
      · rw [hfun] at hmain
        exact SchwartzMap.seminorm_le_bound ℂ k l (f - Fn n)
          (mul_nonneg hC0 (by positivity)) (fun x => hmain x)
      · have hexp : ContDiffOn ℝ Work.RadialSpace.Smooth
            (fun s : ℝ => (Real.exp (-(Real.pi * y * s)) : ℂ)) (Set.Ici 0) :=
          contDiffOn_exp_neg_mul (Real.pi * y)
        exact hexp.mul (hΞcont.sub ((hseq_spec n).1.contDiffOn))
      · intro j hj t ht
        have h1 := (hseq_spec n).2.2 j (le_trans hj hln) t ht
        have h2 : (1 + t) ^ (k + 2 * l) ≤ (1 + t) ^ n :=
          pow_le_pow_right₀ (by linarith) hkn
        calc (1 + t) ^ (k + 2 * l) * ‖iteratedDerivWithin j
              (fun s : ℝ => (Real.exp (-(Real.pi * y * s)) : ℂ) * (Ξ s - hseq n s))
              (Set.Ici 0) t‖
            ≤ (1 + t) ^ n * ‖iteratedDerivWithin j
              (fun s : ℝ => (Real.exp (-(Real.pi * y * s)) : ℂ) * (Ξ s - hseq n s))
              (Set.Ici 0) t‖ :=
              mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
          _ ≤ 1 / ((n : ℝ) + 1) := h1
    have hg : Tendsto (fun n : ℕ => C * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1))) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using h0.const_mul C
    exact squeeze_zero' (Eventually.of_forall (fun n => apply_nonneg _ _)) hbound hg
  have hconv0 : Tendsto (fun n : ℕ => f - Fn n) atTop (𝓝 0) := by
    rw [(schwartz_withSeminorms ℂ (EuclideanSpace ℝ (Fin D)) ℂ).tendsto_nhds
      (fun n => f - Fn n) 0]
    rintro ⟨k, l⟩ ε hε
    have h1 : ∀ᶠ n : ℕ in atTop, (SchwartzMap.seminorm ℂ k l) (f - Fn n) < ε := by
      obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp (hconv k l)) ε hε
      filter_upwards [eventually_ge_atTop N] with n hn
      have h2 := hN n hn
      rwa [Real.dist_eq, sub_zero, abs_of_nonneg (apply_nonneg _ _)] at h2
    filter_upwards [h1] with n hn
    simpa using hn
  have hFtt : Tendsto Fn atTop (𝓝 f) := by
    have h3 : Tendsto (fun n : ℕ => f - (f - Fn n)) atTop (𝓝 (f - 0)) :=
      tendsto_const_nhds.sub hconv0
    have h4 : (fun n : ℕ => f - (f - Fn n)) = Fn := by
      funext n
      abel
    rw [h4] at h3
    simpa using h3
  have hΛ : Tendsto (fun n : ℕ => Λ (Fn n)) atTop (𝓝 (Λ f)) :=
    (ContinuousLinearMap.continuous Λ).tendsto f |>.comp hFtt
  have hzero : ∀ n : ℕ, Λ (Fn n) = 0 := fun n =>
    Hkill (hseq n) (hseq_spec n).1 (hseq_spec n).2.1 (Fn n) (hFn_spec n)
  have h0 : Tendsto (fun n : ℕ => Λ (Fn n)) atTop (𝓝 0) := by
    rw [funext hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hΛ h0

end DensityAux


/-- **Density of the complex Gaussians (paper Lemma 3.3).**  A continuous linear functional
on `𝓢(ℝ^D, ℂ)` that vanishes on all complex Gaussians `x ↦ exp (π i τ ‖x‖²)` with fixed
imaginary part `Im τ = y > 0` vanishes on every radial Schwartz function. -/
theorem DensityOfGaussians (D : ℕ) [NeZero D] (y : ℝ) (hy : 0 < y)
    (Λ : 𝓢(E D, ℂ) →L[ℂ] ℂ)
    (h : ∀ (τ : ℂ), τ.im = y → ∀ G : 𝓢(E D, ℂ),
      (∀ x, G x = Work.Core.gaussianFun D τ x) → Λ G = 0) :
    ∀ f : 𝓢(E D, ℂ), Radial f → Λ f = 0 :=
  DensityAux.density_of_gaussians_of (D := D) y hy Λ h
    (fun Ξ hsm hdec => DensityAux.approx_onesided_smooth y hy Ξ hsm hdec)
    (fun h' hh hsupp F hF => by
      obtain ⟨R, hR⟩ := hsupp
      exact DensityAux.kills_compactProfile (D := D) (y := y) hy Λ h hh
        (DensityAux.hasCompactSupport_of_abs_le (R := R) hR) (F := F) (fun x => by
          rw [hF x]
          congr 1
          have hw : ((-(Real.pi * y * ‖x‖ ^ 2) : ℝ) : ℂ) =
              -(↑Real.pi * ↑y * ↑(‖x‖ ^ 2)) := by
            push_cast
            ring
          rw [← hw]
          exact Complex.ofReal_exp (-(Real.pi * y * ‖x‖ ^ 2))))

end Work.FunctionalEquations
