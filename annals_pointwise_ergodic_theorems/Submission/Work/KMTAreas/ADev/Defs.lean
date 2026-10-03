/-
# The deviation operators of the lacunary bump-dilation family: symbols and kernels

This module sets up the vocabulary for `Work.KMTAreas.A7.lacDilDevLin`, the ℓᵖ bound for signed
sums of the deviation operators `devOp K σ n = bumpOp K σ n - (∫K) · triSmooth σ n`.

It is deliberately stated in terms of the *sampled bump kernel*

`sampKern K m z = (1/m) K (z/m)`

at an arbitrary natural scale `m`, and of an arbitrary level function `L : ℕ → ℕ` (the link with
`Work.KMTAreas.A7.bumpKern` / `devKern` at `L n = lacLev σ n` is made in the file that proves
`lacDilDevLin`).  The key objects are

* `chr j θ = e^{2πijθ}` — the character of the circle;
* `bumpSym K m θ = ∑' k, 𝓕K (m (k - θ))` — the *symbol* of `sampKern K m`, written in the
  Poisson-summation form.  `bumpSym_eq_tsum` (modulated Poisson summation) says that this is
  exactly the Fourier series `∑_z sampKern K m z · e^{2πizθ}` of the sampled kernel;
* `triK L` — the triangular (Fejér) kernel at level `L` (the corpus's
  `Work.Analysis.Hilbert.triKernel`), and `triSym L θ = ∑_{|j| ≤ 2^L} triK L j · e^{2πijθ}` its
  symbol;
* `devSymK K m L θ = bumpSym K m θ - (𝓕K 0) · triSym L θ` and
  `devK K m L z = sampKern K m z - (𝓕K 0) · triK L z` — the symbol and kernel of the deviation
  operator at scale `m`, level `L`;
* `symSu K σ L U ω`, `kernSu K σ L U ω` — the signed sums over `n ∈ U` of the `n`-th symbols and
  kernels; `symSu_eq_tsum` identifies the symbol of `kernSu` as `symSu`.
-/
import Mathlib
import Submission.Commons.Analysis.Fourier.schwartz_decay_real
import Submission.Commons.Analysis.Fourier.poisson_summation_scaled

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.ADev

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators FourierTransform

noncomputable section

/-! ## The character and the sign -/

/-- The sign attached to the `n`-th term of a signed sum. -/
def bSign (ω : ℕ → Bool) (n : ℕ) : ℂ := if ω n then 1 else -1

lemma norm_bSign (ω : ℕ → Bool) (n : ℕ) : ‖bSign ω n‖ = 1 := by
  unfold bSign; split <;> norm_num

lemma norm_bSign_le (ω : ℕ → Bool) (n : ℕ) : ‖bSign ω n‖ ≤ 1 := le_of_eq (norm_bSign ω n)

/-- The character `θ ↦ e^{2πijθ}`. -/
def chr (j : ℤ) (θ : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (θ : ℂ))

@[simp] lemma chr_zero (θ : ℝ) : chr 0 θ = 1 := by simp [chr]

lemma chr_add (j l : ℤ) (θ : ℝ) : chr (j + l) θ = chr j θ * chr l θ := by
  rw [chr, chr, chr, ← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma norm_chr (j : ℤ) (θ : ℝ) : ‖chr j θ‖ = 1 := by
  have h : (2 * (Real.pi : ℂ) * Complex.I * (j : ℂ) * (θ : ℂ))
      = (((2 * Real.pi * (j : ℝ) * θ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [chr, h, Complex.norm_exp_ofReal_mul_I]

lemma chr_one_periodic (j : ℤ) : Function.Periodic (chr j) 1 := by
  intro θ
  have h : (2 * Real.pi * Complex.I * (j : ℂ) * (((θ + 1 : ℝ)) : ℂ))
      = (2 * Real.pi * Complex.I * (j : ℂ) * (θ : ℂ)) + (j : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [chr, chr, h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma continuous_chr (j : ℤ) : Continuous (chr j) := by
  unfold chr; fun_prop

/-! ## The sampled kernel and its symbol -/

/-- The sampled bump kernel at scale `m`: `z ↦ (1/m) K (z/m)`. -/
def sampKern (K : SchwartzMap ℝ ℂ) (m : ℕ) (z : ℤ) : ℂ := (1 / (m : ℝ)) * K ((z : ℝ) / (m : ℝ))

/-- The symbol of the sampled bump kernel at scale `m`, in Poisson-summation form. -/
def bumpSym (K : SchwartzMap ℝ ℂ) (m : ℕ) (θ : ℝ) : ℂ :=
  ∑' k : ℤ, FourierTransform.fourier (K : ℝ → ℂ) ((m : ℝ) * ((k : ℝ) - θ))

lemma bumpSym_one_periodic (K : SchwartzMap ℝ ℂ) (m : ℕ) (θ : ℝ) :
    bumpSym K m (θ + 1) = bumpSym K m θ := by
  rw [bumpSym, bumpSym]
  rw [← Equiv.tsum_eq (Equiv.addRight (-1 : ℤ))
    (fun k : ℤ => FourierTransform.fourier (K : ℝ → ℂ) ((m : ℝ) * ((k : ℝ) - θ)))]
  refine tsum_congr fun k => ?_
  simp only [Equiv.coe_addRight]
  congr 2
  push_cast
  ring


/-! ## Poisson summation, modulated -/

/-- The Fourier transform of the Fourier transform is the reflection. -/
lemma fourier_fourier_apply (g : SchwartzMap ℝ ℂ) (x : ℝ) :
    (𝓕 (𝓕 g)) x = g (-x) := by
  have h_inv : (𝓕⁻ (𝓕 g) : SchwartzMap ℝ ℂ) = g := FourierPair.fourierInv_fourier_eq _
  have hneg : ∀ w, (𝓕 (𝓕 g)) (-w) = g w := by
    intro w
    have h := Real.fourierInv_eq_fourier_neg ((𝓕 g : SchwartzMap ℝ ℂ) : ℝ → ℂ) w
    rw [← SchwartzMap.fourierInv_coe (𝓕 g), ← SchwartzMap.fourier_coe (𝓕 g)] at h
    rw [congrFun (congrArg DFunLike.coe h_inv) w] at h
    exact h.symm
  simpa using hneg (-x)

/-- **Modulated Poisson summation.**  For a Schwartz function `f` and real `ξ`,
`∑_n f(n) e^{-2πinξ} = ∑_k 𝓕f (ξ + k)`. -/
lemma poisson_modulated (f : SchwartzMap ℝ ℂ) (ξ : ℝ) :
    (∑' n : ℤ, f (n : ℝ) * Complex.exp (-(2 * Real.pi * Complex.I * (n : ℂ) * (ξ : ℂ))))
      = ∑' k : ℤ, (𝓕 f) (ξ + (k : ℝ)) := by
  rw [SchwartzMap.tsum_eq_tsum_fourier (𝓕 f) ξ]
  have hR : (∑' n : ℤ, (𝓕 (𝓕 f)) (n : ℝ) * (fourier n) (ξ : UnitAddCircle))
      = ∑' n : ℤ, f (-(n : ℝ)) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (ξ : ℂ)) := by
    refine tsum_congr fun n => ?_
    rw [fourier_fourier_apply, fourier_coe_apply]
    norm_num
  rw [hR]
  have hre : (∑' n : ℤ, f (n : ℝ) * Complex.exp (-(2 * Real.pi * Complex.I * (n : ℂ) * (ξ : ℂ))))
      = ∑' n : ℤ, f (-(n : ℝ)) * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * (ξ : ℂ)) := by
    have h := Equiv.tsum_eq (Equiv.neg ℤ) (fun m : ℤ =>
      f (m : ℝ) * Complex.exp (-(2 * Real.pi * Complex.I * (m : ℂ) * (ξ : ℂ))))
    rw [← h]
    refine tsum_congr fun n => ?_
    simp only [Equiv.neg_apply, Int.cast_neg]
    have harg : (-(2 * Real.pi * Complex.I * (-(n : ℂ)) * (ξ : ℂ)))
        = 2 * Real.pi * Complex.I * (n : ℂ) * (ξ : ℂ) := by ring
    rw [harg]
  exact hre

/-- **The symbol of the sampled kernel is the Fourier series of the sampled kernel.** -/
lemma bumpSym_eq_tsum (K : SchwartzMap ℝ ℂ) (m : ℕ) (hm : 1 ≤ m) (θ : ℝ) :
    (∑' z : ℤ, sampKern K m z * chr z θ) = bumpSym K m θ := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hm0
  let u : ℝˣ := Units.mk0 ((m : ℝ))⁻¹ (inv_ne_zero hmne)
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ u
  let g : SchwartzMap ℝ ℂ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e K
  have hg : ∀ x : ℝ, g x = K (x / (m : ℝ)) := by
    intro x
    simp only [g, e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      ContinuousLinearEquiv.unitsEquivAut_apply, u, Units.val_mk0, div_eq_mul_inv]
  have hgf : ∀ y : ℝ, (𝓕 g) y
      = (((m : ℝ)) : ℂ) * FourierTransform.fourier (K : ℝ → ℂ) (y * (m : ℝ)) := by
    intro y
    rw [SchwartzMap.fourier_coe g]
    have hgfun : (⇑g : ℝ → ℂ) = fun x : ℝ => K (x / (m : ℝ)) := funext fun x => hg x
    rw [hgfun, Commons.Analysis.Fourier.fourier_comp_div (K : ℝ → ℂ) hm0]
  have hp := poisson_modulated g (-θ)
  have hL : (∑' n : ℤ, g (n : ℝ)
        * Complex.exp (-(2 * Real.pi * Complex.I * (n : ℂ) * ((-θ : ℝ) : ℂ))))
      = ∑' n : ℤ, K ((n : ℝ) / (m : ℝ)) * chr n θ := by
    refine tsum_congr fun n => ?_
    simp only [hg n]
    rw [chr]
    congr 1
    push_cast
    ring
  have hR : (∑' k : ℤ, (𝓕 g) ((-θ) + (k : ℝ))) = (((m : ℝ)) : ℂ) * bumpSym K m θ := by
    rw [bumpSym, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    rw [hgf ((-θ) + (k : ℝ))]
    congr 2
    ring
  have hmain : (∑' n : ℤ, K ((n : ℝ) / (m : ℝ)) * chr n θ)
      = (((m : ℝ)) : ℂ) * bumpSym K m θ := by
    rw [← hL, hp, hR]
  have hcoef : (((1 / (m : ℝ)) : ℝ) : ℂ) * (((m : ℝ)) : ℂ) = 1 := by
    rw [show ((1 / (m : ℝ)) : ℝ) = ((m : ℝ))⁻¹ by rw [one_div]]
    rw [Complex.ofReal_inv]
    exact inv_mul_cancel₀ (by exact_mod_cast hmne)
  have hsplit : (∑' z : ℤ, sampKern K m z * chr z θ)
      = (((1 / (m : ℝ)) : ℝ) : ℂ) * (∑' n : ℤ, K ((n : ℝ) / (m : ℝ)) * chr n θ) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun z => ?_
    rw [sampKern]
    push_cast
    ring
  rw [hsplit, hmain, ← mul_assoc, hcoef, one_mul]

/-- The triangular (Fejér) kernel at scale `2^L` (the corpus's `triKernel`). -/
def triK (L : ℕ) (n : ℤ) : ℝ := max 0 (((2 : ℝ) ^ L - |(n : ℝ)|) / (2 : ℝ) ^ (2 * L))

/-- The symbol of the triangular kernel at level `L`. -/
def triSym (L : ℕ) (θ : ℝ) : ℂ :=
  ∑ j ∈ Finset.Icc (-((2 : ℤ) ^ L)) ((2 : ℤ) ^ L), (triK L j : ℂ) * chr j θ

lemma triSym_one_periodic (L : ℕ) (θ : ℝ) : triSym L (θ + 1) = triSym L θ := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [chr_one_periodic j]

/-- The symbol of the deviation operator at scale `m` and level `L`. -/
def devSymK (K : SchwartzMap ℝ ℂ) (m L : ℕ) (θ : ℝ) : ℂ :=
  bumpSym K m θ - (((𝓕 (K : ℝ → ℂ)) 0)) * triSym L θ

/-- The kernel of the deviation operator at scale `m` and level `L`. -/
def devK (K : SchwartzMap ℝ ℂ) (m L : ℕ) (z : ℤ) : ℂ :=
  sampKern K m z - (((𝓕 (K : ℝ → ℂ)) 0)) * (triK L z : ℂ)

/-- The signed sum of the deviation symbols over `n ∈ U`, at scales `σ` and levels `L`. -/
def symSu (K : SchwartzMap ℝ ℂ) (σ L : ℕ → ℕ) (U : Finset ℕ) (ω : ℕ → Bool) (θ : ℝ) : ℂ :=
  ∑ n ∈ U, bSign ω n * devSymK K (σ n) (L n) θ

/-- The signed sum of the deviation kernels over `n ∈ U`, at scales `σ` and levels `L`. -/
def kernSu (K : SchwartzMap ℝ ℂ) (σ L : ℕ → ℕ) (U : Finset ℕ) (ω : ℕ → Bool) (z : ℤ) : ℂ :=
  ∑ n ∈ U, bSign ω n * devK K (σ n) (L n) z

lemma symSu_one_periodic (K : SchwartzMap ℝ ℂ) (σ L : ℕ → ℕ) (U : Finset ℕ) (ω : ℕ → Bool)
    (θ : ℝ) : symSu K σ L U ω (θ + 1) = symSu K σ L U ω θ := by
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold devSymK
  rw [bumpSym_one_periodic, triSym_one_periodic]

end

end Work.KMTAreas.ADev
