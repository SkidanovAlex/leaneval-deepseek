/-
# The `r`-seminorms of the `high` part of the CKMRV layer

This file proves `Work.Asymptotics.highPart_seminorm`: the `r`-seminorms of the explicit `high`
part `highPart` of the CKMRV layer are bounded, with moderate growth in `τ` on the fundamental
domain `𝒟 = Work.Asymptotics.DomainD`.

The mathematical content is the following.  Writing `λ = π r²` and `μ = π r² - 2π`, the `high`
part is the sum of four terms

  `G₀₀ τ · λ psi1(λ) e^{-λ}`, `G₀₁ τ · psi1(λ)(λ+1) e^{-λ}`,
  `G₁₀ τ · μ psi1(μ) e^{-μ}`, `G₁₁ τ · psi1(μ)(μ+1) e^{-μ}`,

and each of the four explicit real-analytic factors is the composition of an amplitude
`φ(π r² - a)` (`φ = x·psi1 x` or `φ = (x+1)·psi1 x`, `a = 0` or `a = 2π`) with the Gaussian
`e^{-π r²}`.  Since `e^{-μ} = e^{2π} e^{-π r²}`, the whole `r`-dependence of `highPart G τ ·`
is a linear combination (with coefficients depending only on `τ`) of four *fixed* functions:

* `highFac φ a r = φ (π r² - a) · e^{-π r²}`.

The seminorms of `highFac φ a` are finite — the content of
`Work.Asymptotics.seminorm_highFac`, built from

* `Work.Asymptotics.compose_grow`: derivatives of a composition `r ↦ φ (π r² - a)` grow at most
  polynomially when the derivatives of `φ` do,
* `Work.Asymptotics.gaussian_deriv_bound` and
  `Work.Asymptotics.poly_mul_gaussian_bounded`: the Gaussian kills the polynomial factors,
* `Work.Asymptotics.psi1_deriv_bounded`: `psi1 x = 2∫₀¹(1-s)cos(sx)ds` has uniformly bounded
  derivatives (so `x·psi1 x` and `(x+1)·psi1 x` have derivatives of at most linear growth).

The `τ`-dependence enters only through the four coefficients `G i j τ`, whose moderate growth on
`𝒟` (the hypothesis `hG`) supplies the factor `c · (scale τ)^N`.

## Main results

* `Work.Asymptotics.highPart_decomp`: the pointwise decomposition of `highPart` into the four
  fixed functions above.
* `Work.Asymptotics.highAmp0_grow`, `Work.Asymptotics.highAmp1_grow`: the polynomial growth of
  the derivatives of the two amplitudes `x·psi1 x`, `(x+1)·psi1 x`.
* `Work.Asymptotics.seminorm_highFac`: the seminorm bound for `highFac φ a`.
* `Work.Asymptotics.highPart_seminorm`: the target.
-/
import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ModerateGrowth
import Submission.Work.RadialSpace.iteratedDeriv_ofReal
import Submission.Work.Asymptotics.psi1_contDiff
import Submission.Work.Asymptotics.psi1_deriv_bounded
import Submission.Work.Asymptotics.gaussian_deriv_bound
import Submission.Work.Asymptotics.poly_mul_gaussian_bounded
import Submission.Work.Asymptotics.compose_grow

open scoped ContDiff

noncomputable section

open UpperHalfPlane

namespace Work.Asymptotics

/-! ## The four explicit factors of the `high` part -/

/-- The amplitude `x ↦ x · psi1 x` of the first and third factors of `highPart`. -/
def highAmp0 (x : ℝ) : ℂ := ((x * psi1 x : ℝ) : ℂ)

/-- The amplitude `x ↦ (x + 1) · psi1 x` of the second and fourth factors of `highPart`. -/
def highAmp1 (x : ℝ) : ℂ := (((x + 1) * psi1 x : ℝ) : ℂ)

/-- The composed factor `r ↦ φ (π r² - a) · e^{-π r²}`, a fixed function of `r` for each pair
`(φ, a)` (the case `a = 2π` corresponds to `μ = π r² - 2π`, for which
`e^{-μ} = e^{2π} e^{-π r²}`). -/
def highFac (φ : ℝ → ℂ) (a r : ℝ) : ℂ :=
  φ (Real.pi * r ^ 2 - a) * ((Real.exp (-(Real.pi * r ^ 2)) : ℝ) : ℂ)

/-! ## Smoothness of `psi1` and of the amplitudes -/

/-- `psi1` is smooth.  Obtained from the smoothness of its complexification
(`Work.Asymptotics.psi1_contDiff`) by composing with the real part. -/
lemma psi1_contDiff_real : ContDiff ℝ (↑(⊤ : ℕ∞)) psi1 :=
  Complex.reCLM.contDiff.comp psi1_contDiff

lemma highAmp0_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) highAmp0 := by
  have h : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => x * psi1 x) := contDiff_id.mul psi1_contDiff_real
  exact Complex.ofRealCLM.contDiff.comp h

lemma highAmp1_contDiff : ContDiff ℝ (↑(⊤ : ℕ∞)) highAmp1 := by
  have h : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => (x + 1) * psi1 x) :=
    (contDiff_id.add contDiff_const).mul psi1_contDiff_real
  exact Complex.ofRealCLM.contDiff.comp h

lemma highFac_contDiff (φ : ℝ → ℂ) (a : ℝ) (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (highFac φ a) := by
  have h1 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun r : ℝ => φ (Real.pi * r ^ 2 - a)) :=
    hφ.comp (by fun_prop)
  have h2 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun r : ℝ => ((Real.exp (-(Real.pi * r ^ 2)) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp
        (by fun_prop : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun r : ℝ => -(Real.pi * r ^ 2))))
  exact h1.mul h2

/-! ## Polynomial growth of the amplitudes -/

/-- The norm of a real number viewed as a complex number. -/
private lemma norm_ofReal_eq (a : ℝ) : ‖((a : ℝ) : ℂ)‖ = |a| := RCLike.norm_ofReal a

/-- The norm of a sum of two real numbers viewed as complex numbers. -/
private lemma norm_ofReal_add_eq (a b : ℝ) : ‖((a : ℝ) : ℂ) + ((b : ℝ) : ℂ)‖ = |a + b| := by
  rw [← Complex.ofReal_add]
  exact RCLike.norm_ofReal _

/-- The derivatives of `x ↦ x · psi1 x` grow at most linearly.  The Leibniz rule expresses the
`j`-th derivative as a combination of `x · psi1^{(j)} x` and `j · psi1^{(j-1)} x`, and
`psi1_deriv_bounded` bounds every `psi1^{(i)}`. -/
lemma highAmp0_grow (L : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ j ≤ L, ∀ x : ℝ,
    ‖iteratedDeriv j highAmp0 x‖ ≤ A * (1 + |x|) ^ 1 := by
  choose B hB hbound using psi1_deriv_bounded
  set Bs : ℝ := ∑ i ∈ Finset.range (L + 1), B i with hBs
  have hBs_nn : 0 ≤ Bs := Finset.sum_nonneg fun i _ => hB i
  have hBle : ∀ i ≤ L, B i ≤ Bs := fun i hi =>
    Finset.single_le_sum (fun j _ => hB j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  refine ⟨(2 : ℝ) ^ L * Bs, by positivity, fun j hj x => ?_⟩
  have hco : iteratedDeriv j highAmp0 x
      = ((iteratedDeriv j (fun y : ℝ => y * psi1 y) x : ℝ) : ℂ) :=
    Work.RadialSpace.iteratedDeriv_ofReal j (fun y : ℝ => y * psi1 y) x
  rw [hco, norm_ofReal_eq]
  have hid : ContDiffAt ℝ (↑j) id x := contDiffAt_id
  have hpsi : ContDiffAt ℝ (↑j) psi1 x :=
    psi1_contDiff_real.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hmul : iteratedDeriv j (fun y : ℝ => y * psi1 y) x
      = ∑ i ∈ Finset.range (j + 1),
          (↑(j.choose i) : ℝ) * iteratedDeriv i id x * iteratedDeriv (j - i) psi1 x :=
    iteratedDeriv_mul hid hpsi
  rw [hmul]
  have hterm : ∀ i ∈ Finset.range (j + 1),
      |(↑(j.choose i) : ℝ) * iteratedDeriv i id x * iteratedDeriv (j - i) psi1 x|
        ≤ (j.choose i : ℝ) * ((1 + |x|) * Bs) := by
    intro i hi
    have hj' : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have h1 : |iteratedDeriv i id x| ≤ 1 + |x| := by
      rw [iteratedDeriv_id]
      split_ifs <;> simp <;> linarith [abs_nonneg x]
    have h2 : |iteratedDeriv (j - i) psi1 x| ≤ Bs :=
      le_trans (hbound (j - i) x)
        (hBle (j - i) (le_trans (Nat.sub_le j i) hj))
    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (j.choose i))]
    calc (j.choose i : ℝ) * |iteratedDeriv i id x| * |iteratedDeriv (j - i) psi1 x|
        ≤ (j.choose i : ℝ) * (1 + |x|) * Bs :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)) h2 (abs_nonneg _)
            (by positivity)
      _ = (j.choose i : ℝ) * ((1 + |x|) * Bs) := by ring
  have hsum2 : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = (2 : ℝ) ^ j := by
    rw [← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    ring
  calc |∑ i ∈ Finset.range (j + 1),
          (↑(j.choose i) : ℝ) * iteratedDeriv i id x * iteratedDeriv (j - i) psi1 x|
      ≤ ∑ i ∈ Finset.range (j + 1),
          |(↑(j.choose i) : ℝ) * iteratedDeriv i id x * iteratedDeriv (j - i) psi1 x| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ((1 + |x|) * Bs) :=
        Finset.sum_le_sum hterm
    _ = (2 : ℝ) ^ j * ((1 + |x|) * Bs) := by
        rw [← Finset.sum_mul]
        rw [hsum2]
    _ ≤ (2 : ℝ) ^ L * Bs * (1 + |x|) ^ 1 := by
        rw [pow_one]
        have h2j : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ L := pow_le_pow_right₀ (by norm_num) hj
        calc (2 : ℝ) ^ j * ((1 + |x|) * Bs)
            ≤ (2 : ℝ) ^ L * ((1 + |x|) * Bs) :=
              mul_le_mul_of_nonneg_right h2j (by positivity)
          _ = (2 : ℝ) ^ L * Bs * (1 + |x|) := by ring

/-- The derivatives of `x ↦ (x+1) · psi1 x` grow at most linearly; this follows from the
previous lemma and `(x+1)·psi1 x = x·psi1 x + psi1 x`. -/
lemma highAmp1_grow (L : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ j ≤ L, ∀ x : ℝ,
    ‖iteratedDeriv j highAmp1 x‖ ≤ A * (1 + |x|) ^ 1 := by
  obtain ⟨A0, hA0, hb0⟩ := highAmp0_grow L
  choose B hB hbound using psi1_deriv_bounded
  set Bs : ℝ := ∑ i ∈ Finset.range (L + 1), B i with hBs
  have hBs_nn : 0 ≤ Bs := Finset.sum_nonneg fun i _ => hB i
  have hBle : ∀ i ≤ L, B i ≤ Bs := fun i hi =>
    Finset.single_le_sum (fun j _ => hB j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  refine ⟨A0 + Bs, by positivity, fun j hj x => ?_⟩
  have hfun : highAmp1 = (fun y : ℝ => ((y * psi1 y : ℝ) : ℂ))
      + (fun y : ℝ => ((psi1 y : ℝ) : ℂ)) := by
    funext y
    simp only [highAmp1, Pi.add_apply]
    push_cast
    ring
  have hcd1 : ContDiffAt ℝ (↑j) (fun y : ℝ => ((y * psi1 y : ℝ) : ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_id.mul psi1_contDiff_real)).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hcd2 : ContDiffAt ℝ (↑j) (fun y : ℝ => ((psi1 y : ℝ) : ℂ)) x :=
    psi1_contDiff.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [hfun, iteratedDeriv_add hcd1 hcd2]
  rw [Work.RadialSpace.iteratedDeriv_ofReal j (fun y : ℝ => y * psi1 y) x,
    Work.RadialSpace.iteratedDeriv_ofReal j psi1 x]
  rw [norm_ofReal_add_eq]
  have h0 : |iteratedDeriv j (fun y : ℝ => y * psi1 y) x| ≤ A0 * (1 + |x|) ^ 1 := by
    have hco : iteratedDeriv j highAmp0 x
        = ((iteratedDeriv j (fun y : ℝ => y * psi1 y) x : ℝ) : ℂ) :=
      Work.RadialSpace.iteratedDeriv_ofReal j (fun y : ℝ => y * psi1 y) x
    have h := hb0 j hj x
    rw [hco, norm_ofReal_eq] at h
    exact h
  have h1 : |iteratedDeriv j psi1 x| ≤ Bs * (1 + |x|) ^ 1 := by
    have hle : B j ≤ Bs := hBle j hj
    have h := hbound j x
    have hpos : (0 : ℝ) ≤ (1 + |x|) ^ 1 := by positivity
    calc |iteratedDeriv j psi1 x| ≤ B j := h
      _ ≤ Bs := hle
      _ = Bs * 1 := (mul_one Bs).symm
      _ ≤ Bs * (1 + |x|) ^ 1 := by
          rw [pow_one]
          exact mul_le_mul_of_nonneg_left (by linarith [abs_nonneg x]) hBs_nn
  calc |iteratedDeriv j (fun y : ℝ => y * psi1 y) x + iteratedDeriv j psi1 x|
      ≤ |iteratedDeriv j (fun y : ℝ => y * psi1 y) x| + |iteratedDeriv j psi1 x| :=
        abs_add_le _ _
    _ ≤ A0 * (1 + |x|) ^ 1 + Bs * (1 + |x|) ^ 1 := add_le_add h0 h1
    _ = (A0 + Bs) * (1 + |x|) ^ 1 := by ring

/-! ## The decomposition of `highPart` -/

/-- **The four explicit factors of `highPart`.**  Since `e^{-μ} = e^{2π} e^{-π r²}` for
`μ = π r² - 2π`, the `high` part is a linear combination (with `τ`-dependent coefficients) of the
four fixed functions `highFac highAmp0 0`, `highFac highAmp1 0`, `highFac highAmp0 (2π)` and
`highFac highAmp1 (2π)`. -/
lemma highPart_decomp (G : Fin 2 → Fin 2 → ℍ → ℂ) (τ : ℍ) (r : ℝ) :
    highPart G τ r = G 0 0 τ * highFac highAmp0 0 r
      + (Complex.I * G 0 1 τ) * highFac highAmp1 0 r
      + (Complex.exp ((2 * Real.pi : ℝ) : ℂ) * G 1 0 τ) * highFac highAmp0 (2 * Real.pi) r
      + (Complex.exp ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * G 1 1 τ))
          * highFac highAmp1 (2 * Real.pi) r := by
  have hexp : ∀ x y : ℂ, Complex.exp (-(x - y)) = Complex.exp y * Complex.exp (-x) := by
    intro x y
    rw [show -(x - y) = y + (-x) by ring, Complex.exp_add]
  simp only [highPart, highFac, highAmp0, highAmp1, Fin.isValue]
  simp only [hexp, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_pow,
    Complex.ofReal_add, Complex.ofReal_one]
  push_cast
  ring_nf

/-! ## The seminorm bound for one factor -/

/-- **Seminorm bound for one factor.**  If the derivatives of `φ` grow at most polynomially, so
do the derivatives of `r ↦ φ (π r² - a) e^{-π r²}`, and multiplying by `|r|^k` keeps the result
bounded (the Gaussian beats every polynomial). -/
lemma seminorm_highFac (φ : ℝ → ℂ) (a : ℝ) (k l : ℕ) (A : ℝ) (m : ℕ)
    (hA : 0 ≤ A) (hφ : ContDiff ℝ (↑(⊤ : ℕ∞)) φ)
    (h : ∀ j ≤ l + 1, ∀ x : ℝ, ‖iteratedDeriv j φ x‖ ≤ A * (1 + |x|) ^ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
      |r| ^ k * ‖iteratedDeriv l (highFac φ a) r‖ ≤ C := by
  obtain ⟨C₁, hC₁, h₁⟩ := compose_grow φ a l A m hA hφ h
  choose C₂ hC₂ h₂ using gaussian_deriv_bound
  obtain ⟨C₃, hC₃, h₃⟩ := poly_mul_gaussian_bounded k (2 * m + 2 * l)
  set C₂s : ℝ := ∑ i ∈ Finset.range (l + 1), C₂ i with hC₂s
  have hC₂s_nn : 0 ≤ C₂s := Finset.sum_nonneg fun i _ => hC₂ i
  have hC₂le : ∀ i ≤ l, C₂ i ≤ C₂s := by
    intro i hi
    exact Finset.single_le_sum (fun j _ => hC₂ j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  refine ⟨(2 : ℝ) ^ l * C₁ * C₂s * C₃, by positivity, fun r => ?_⟩
  have hf_smo : ContDiff ℝ (↑l) (fun s : ℝ => φ (Real.pi * s ^ 2 - a)) :=
    ((hφ.comp (by fun_prop : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun s : ℝ => Real.pi * s ^ 2 - a))).of_le
      (WithTop.coe_le_coe.mpr le_top))
  have hg_smo : ContDiff ℝ (↑l) (fun s : ℝ => ((Real.exp (-(Real.pi * s ^ 2)) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (by fun_prop : ContDiff ℝ (↑l) (fun s : ℝ => Real.exp (-(Real.pi * s ^ 2))))
  rw [show highFac φ a = (fun s : ℝ => φ (Real.pi * s ^ 2 - a))
        * (fun s : ℝ => ((Real.exp (-(Real.pi * s ^ 2)) : ℝ) : ℂ)) from rfl,
    iteratedDeriv_mul hf_smo.contDiffAt hg_smo.contDiffAt]
  have key : ‖∑ i ∈ Finset.range (l + 1), (↑(l.choose i) : ℂ) *
        iteratedDeriv i (fun s : ℝ => φ (Real.pi * s ^ 2 - a)) r *
        iteratedDeriv (l - i) (fun s : ℝ => ((Real.exp (-(Real.pi * s ^ 2)) : ℝ) : ℂ)) r‖
      ≤ (2 : ℝ) ^ l * C₁ * C₂s * (1 + |r|) ^ (2 * m + 2 * l) * Real.exp (-(Real.pi * r ^ 2)) := by
    have hterm : ∀ i ∈ Finset.range (l + 1),
        ‖(↑(l.choose i) : ℂ) * iteratedDeriv i (fun s : ℝ => φ (Real.pi * s ^ 2 - a)) r *
            iteratedDeriv (l - i) (fun s : ℝ => ((Real.exp (-(Real.pi * s ^ 2)) : ℝ) : ℂ)) r‖
          ≤ (l.choose i : ℝ) * (C₁ * C₂s) * (1 + |r|) ^ (2 * m + 2 * l)
              * Real.exp (-(Real.pi * r ^ 2)) := by
      intro i hi
      have hi' : i ≤ l := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have hli : l - i ≤ l := Nat.sub_le _ _
      have hone : (1 : ℝ) ≤ 1 + |r| := by have := abs_nonneg r; linarith
      have h1i : ‖iteratedDeriv i (fun s : ℝ => φ (Real.pi * s ^ 2 - a)) r‖
          ≤ C₁ * (1 + |r|) ^ (2 * m + l) := h₁ i hi' r
      have h2i : ‖iteratedDeriv (l - i) (fun s : ℝ => ((Real.exp (-(Real.pi * s ^ 2)) : ℝ) : ℂ)) r‖
          ≤ C₂s * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2)) := by
        have h0 := h₂ (l - i) r
        have hC : C₂ (l - i) ≤ C₂s := hC₂le (l - i) hli
        have hle : (1 + |r|) ^ (l - i) ≤ (1 + |r|) ^ l := pow_le_pow_right₀ hone hli
        have hCnn : (0 : ℝ) ≤ C₂ (l - i) := hC₂ (l - i)
        calc ‖iteratedDeriv (l - i) (fun s : ℝ => ((Real.exp (-(Real.pi * s ^ 2)) : ℝ) : ℂ)) r‖
            ≤ C₂ (l - i) * (1 + |r|) ^ (l - i) * Real.exp (-(Real.pi * r ^ 2)) := h0
          _ ≤ C₂s * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2)) :=
              mul_le_mul (mul_le_mul hC hle (by positivity) hC₂s_nn) le_rfl
                (Real.exp_nonneg _) (by positivity)
      have hpowmul : (1 + |r|) ^ (2 * m + l) * (1 + |r|) ^ l = (1 + |r|) ^ (2 * m + 2 * l) := by
        rw [← pow_add]; ring_nf
      calc ‖(↑(l.choose i) : ℂ) * iteratedDeriv i (fun s : ℝ => φ (Real.pi * s ^ 2 - a)) r *
              iteratedDeriv (l - i) (fun s : ℝ => ((Real.exp (-(Real.pi * s ^ 2)) : ℝ) : ℂ)) r‖
          = (l.choose i : ℝ) * ‖iteratedDeriv i (fun s : ℝ => φ (Real.pi * s ^ 2 - a)) r‖ *
              ‖iteratedDeriv (l - i)
                (fun s : ℝ => ((Real.exp (-(Real.pi * s ^ 2)) : ℝ) : ℂ)) r‖ := by
            rw [norm_mul, norm_mul, Complex.norm_natCast]
        _ ≤ ((l.choose i : ℝ) * (C₁ * (1 + |r|) ^ (2 * m + l))) *
              (C₂s * (1 + |r|) ^ l * Real.exp (-(Real.pi * r ^ 2))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1i (Nat.cast_nonneg _)) h2i
              (norm_nonneg _) (by positivity)
        _ = (l.choose i : ℝ) * (C₁ * C₂s) * (1 + |r|) ^ (2 * m + 2 * l)
              * Real.exp (-(Real.pi * r ^ 2)) := by
            rw [← hpowmul]; ring
    calc ‖∑ i ∈ Finset.range (l + 1), (↑(l.choose i) : ℂ) *
            iteratedDeriv i (fun s : ℝ => φ (Real.pi * s ^ 2 - a)) r *
            iteratedDeriv (l - i) (fun s : ℝ => ((Real.exp (-(Real.pi * s ^ 2)) : ℝ) : ℂ)) r‖
        ≤ ∑ i ∈ Finset.range (l + 1), ‖(↑(l.choose i) : ℂ) *
            iteratedDeriv i (fun s : ℝ => φ (Real.pi * s ^ 2 - a)) r *
            iteratedDeriv (l - i) (fun s : ℝ => ((Real.exp (-(Real.pi * s ^ 2)) : ℝ) : ℂ)) r‖ :=
          norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ) * (C₁ * C₂s)
            * (1 + |r|) ^ (2 * m + 2 * l) * Real.exp (-(Real.pi * r ^ 2)) :=
          Finset.sum_le_sum hterm
      _ = (∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ)) *
            ((C₁ * C₂s) * (1 + |r|) ^ (2 * m + 2 * l) * Real.exp (-(Real.pi * r ^ 2))) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = (2 : ℝ) ^ l * C₁ * C₂s * (1 + |r|) ^ (2 * m + 2 * l)
            * Real.exp (-(Real.pi * r ^ 2)) := by
          have h2l : (∑ i ∈ Finset.range (l + 1), (l.choose i : ℝ)) = (2 : ℝ) ^ l := by
            rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
          rw [h2l]; ring
  calc |r| ^ k * ‖∑ i ∈ Finset.range (l + 1), (↑(l.choose i) : ℂ) *
          iteratedDeriv i (fun s : ℝ => φ (Real.pi * s ^ 2 - a)) r *
          iteratedDeriv (l - i) (fun s : ℝ => ((Real.exp (-(Real.pi * s ^ 2)) : ℝ) : ℂ)) r‖
      ≤ |r| ^ k * ((2 : ℝ) ^ l * C₁ * C₂s * (1 + |r|) ^ (2 * m + 2 * l)
          * Real.exp (-(Real.pi * r ^ 2))) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = (2 : ℝ) ^ l * C₁ * C₂s
          * (|r| ^ k * (1 + |r|) ^ (2 * m + 2 * l) * Real.exp (-(Real.pi * r ^ 2))) := by ring
    _ ≤ (2 : ℝ) ^ l * C₁ * C₂s * C₃ := mul_le_mul_of_nonneg_left (h₃ r) (by positivity)

/-! ## Two elementary estimates -/

/-- The triangle inequality for four terms. -/
private lemma norm_four_add_le (a b c d : ℂ) : ‖a + b + c + d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
  have h1 := norm_add_le (a + b + c) d
  have h2 := norm_add_le (a + b) c
  have h3 := norm_add_le a b
  calc ‖a + b + c + d‖ ≤ ‖a + b + c‖ + ‖d‖ := h1
    _ ≤ (‖a + b‖ + ‖c‖) + ‖d‖ := add_le_add h2 le_rfl
    _ ≤ ((‖a‖ + ‖b‖) + ‖c‖) + ‖d‖ := add_le_add (add_le_add h3 le_rfl) le_rfl

/-! ## Linearity of `iteratedDeriv` over a four-term linear combination -/

/-- `iteratedDeriv` is linear over a four-term linear combination. -/
lemma iteratedDeriv_four (c0 c1 c2 c3 : ℂ) (F0 F1 F2 F3 : ℝ → ℂ) (n : ℕ) (r : ℝ)
    (h0 : ContDiffAt ℝ (↑n) F0 r) (h1 : ContDiffAt ℝ (↑n) F1 r)
    (h2 : ContDiffAt ℝ (↑n) F2 r) (h3 : ContDiffAt ℝ (↑n) F3 r) :
    iteratedDeriv n (fun s : ℝ => c0 * F0 s + c1 * F1 s + c2 * F2 s + c3 * F3 s) r
      = c0 * iteratedDeriv n F0 r + c1 * iteratedDeriv n F1 r
        + c2 * iteratedDeriv n F2 r + c3 * iteratedDeriv n F3 r := by
  have m0 : ContDiffAt ℝ (↑n) (fun s : ℝ => c0 * F0 s) r :=
    (contDiffAt_const (c := c0)).mul h0
  have m1 : ContDiffAt ℝ (↑n) (fun s : ℝ => c1 * F1 s) r :=
    (contDiffAt_const (c := c1)).mul h1
  have m2 : ContDiffAt ℝ (↑n) (fun s : ℝ => c2 * F2 s) r :=
    (contDiffAt_const (c := c2)).mul h2
  have m3 : ContDiffAt ℝ (↑n) (fun s : ℝ => c3 * F3 s) r :=
    (contDiffAt_const (c := c3)).mul h3
  have e0 := iteratedDeriv_const_mul (c := c0) (f := F0) (n := n) (x := r) h0
  have e1 := iteratedDeriv_const_mul (c := c1) (f := F1) (n := n) (x := r) h1
  have e2 := iteratedDeriv_const_mul (c := c2) (f := F2) (n := n) (x := r) h2
  have e3 := iteratedDeriv_const_mul (c := c3) (f := F3) (n := n) (x := r) h3
  have cdA : ContDiffAt ℝ (↑n) (fun s : ℝ => c0 * F0 s + c1 * F1 s + c2 * F2 s) r :=
    (m0.add m1).add m2
  have cdB : ContDiffAt ℝ (↑n) (fun s : ℝ => c0 * F0 s + c1 * F1 s) r := m0.add m1
  have s1 : (fun s : ℝ => c0 * F0 s + c1 * F1 s + c2 * F2 s + c3 * F3 s)
      = (fun s : ℝ => c0 * F0 s + c1 * F1 s + c2 * F2 s) + (fun s : ℝ => c3 * F3 s) := rfl
  have s2 : (fun s : ℝ => c0 * F0 s + c1 * F1 s + c2 * F2 s)
      = (fun s : ℝ => c0 * F0 s + c1 * F1 s) + (fun s : ℝ => c2 * F2 s) := rfl
  have s3 : (fun s : ℝ => c0 * F0 s + c1 * F1 s)
      = (fun s : ℝ => c0 * F0 s) + (fun s : ℝ => c1 * F1 s) := rfl
  rw [s1, iteratedDeriv_add cdA m3, s2, iteratedDeriv_add cdB m2, s3,
    iteratedDeriv_add m0 m1, e0, e1, e2, e3]

/-! ## The target -/

/-- The `r`-seminorms of the explicit `high` part `highPart` of the CKMRV layer are bounded, with
moderate growth in `τ` on `𝒟`.  The content is: `psi1` is smooth with bounded derivatives, so
each of the four explicit factors `λ·psi1 λ·e^{-λ}`, `psi1 λ·(λ+1)e^{-λ}`, `μ·psi1 μ·e^{-μ}`,
`psi1 μ·(μ+1)e^{-μ}` (with `λ = πr²`, `μ = πr² - 2π`) times `|r|^k` has bounded `l`-th derivative on
`ℝ`; the `τ`-dependence enters only through the four constants `G i j τ`. -/
theorem highPart_seminorm (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ)
    (hG : ∀ i j : Fin 2, Work.Kernels.ModerateGrowthOn Work.Asymptotics.DomainD (G i j)) :
    ∀ k l : ℕ, ∃ c N : ℝ, 0 ≤ c ∧ ∀ (τ : UpperHalfPlane) (r : ℝ),
      τ ∈ Work.Asymptotics.DomainD →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => Work.Asymptotics.highPart G τ s) r‖
        ≤ c * (Work.Kernels.scale τ) ^ N := by
  intro k l
  obtain ⟨α0, N0, hα0, hN0, hb0⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale DomainD (G 0 0)).mp (hG 0 0)
  obtain ⟨α1, N1, hα1, hN1, hb1⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale DomainD (G 0 1)).mp (hG 0 1)
  obtain ⟨α2, N2, hα2, hN2, hb2⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale DomainD (G 1 0)).mp (hG 1 0)
  obtain ⟨α3, N3, hα3, hN3, hb3⟩ :=
    (Work.Kernels.moderateGrowthOn_iff_scale DomainD (G 1 1)).mp (hG 1 1)
  obtain ⟨A0, hA0, hbA0⟩ := highAmp0_grow (l + 1)
  obtain ⟨A1, hA1, hbA1⟩ := highAmp1_grow (l + 1)
  obtain ⟨B0, hB0, hbB0⟩ := seminorm_highFac highAmp0 0 k l A0 1 hA0 highAmp0_contDiff hbA0
  obtain ⟨B1, hB1, hbB1⟩ := seminorm_highFac highAmp1 0 k l A1 1 hA1 highAmp1_contDiff hbA1
  obtain ⟨B2, hB2, hbB2⟩ :=
    seminorm_highFac highAmp0 (2 * Real.pi) k l A0 1 hA0 highAmp0_contDiff hbA0
  obtain ⟨B3, hB3, hbB3⟩ :=
    seminorm_highFac highAmp1 (2 * Real.pi) k l A1 1 hA1 highAmp1_contDiff hbA1
  set E : ℝ := Real.exp (2 * Real.pi) with hE
  have hE0 : 0 ≤ E := Real.exp_nonneg _
  refine ⟨α0 * B0 + α1 * B1 + E * α2 * B2 + E * α3 * B3, max (max N0 N1) (max N2 N3),
    by positivity, fun τ r hτ => ?_⟩
  have hS1 : 1 ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  -- the four coefficient bounds
  have hc0 : ‖G 0 0 τ‖ ≤ α0 * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3) :=
    le_trans (hb0 τ hτ)
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hS1 (le_trans (le_max_left _ _) (le_max_left _ _)))
        hα0)
  have hc1 : ‖Complex.I * G 0 1 τ‖ ≤ α1 * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3) := by
    rw [norm_mul, Complex.norm_I, one_mul]
    exact le_trans (hb1 τ hτ)
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hS1 (le_trans (le_max_right _ _) (le_max_left _ _)))
        hα1)
  have hc2 : ‖Complex.exp ((2 * Real.pi : ℝ) : ℂ) * G 1 0 τ‖
      ≤ (E * α2) * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3) := by
    rw [norm_mul, Complex.norm_exp_ofReal]
    have h := hb2 τ hτ
    have hN : N2 ≤ max (max N0 N1) (max N2 N3) := le_trans (le_max_left _ _) (le_max_right _ _)
    calc Real.exp (2 * Real.pi) * ‖G 1 0 τ‖
        ≤ Real.exp (2 * Real.pi) * (α2 * (Work.Kernels.scale τ) ^ N2) :=
          mul_le_mul_of_nonneg_left h hE0
      _ = (E * α2) * (Work.Kernels.scale τ) ^ N2 := by rw [hE]; ring
      _ ≤ (E * α2) * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hS1 hN) (by positivity)
  have hc3 : ‖Complex.exp ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * G 1 1 τ)‖
      ≤ (E * α3) * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3) := by
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal, Complex.norm_I, one_mul]
    have h := hb3 τ hτ
    have hN : N3 ≤ max (max N0 N1) (max N2 N3) :=
      le_trans (le_max_right N2 N3) (le_max_right (max N0 N1) (max N2 N3))
    calc Real.exp (2 * Real.pi) * ‖G 1 1 τ‖
        ≤ Real.exp (2 * Real.pi) * (α3 * (Work.Kernels.scale τ) ^ N3) :=
          mul_le_mul_of_nonneg_left h hE0
      _ = (E * α3) * (Work.Kernels.scale τ) ^ N3 := by rw [hE]; ring
      _ ≤ (E * α3) * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hS1 hN) (by positivity)
  -- the decomposition of `highPart` as a function of `r`
  have hfun : (fun s : ℝ => highPart G τ s)
      = fun s : ℝ => G 0 0 τ * highFac highAmp0 0 s
          + (Complex.I * G 0 1 τ) * highFac highAmp1 0 s
          + (Complex.exp ((2 * Real.pi : ℝ) : ℂ) * G 1 0 τ) * highFac highAmp0 (2 * Real.pi) s
          + (Complex.exp ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * G 1 1 τ))
              * highFac highAmp1 (2 * Real.pi) s :=
    funext fun s => highPart_decomp G τ s
  have hcd0 : ContDiffAt ℝ (↑l) (highFac highAmp0 0) r :=
    (highFac_contDiff highAmp0 0 highAmp0_contDiff).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hcd1 : ContDiffAt ℝ (↑l) (highFac highAmp1 0) r :=
    (highFac_contDiff highAmp1 0 highAmp1_contDiff).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hcd2 : ContDiffAt ℝ (↑l) (highFac highAmp0 (2 * Real.pi)) r :=
    (highFac_contDiff highAmp0 (2 * Real.pi) highAmp0_contDiff).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hcd3 : ContDiffAt ℝ (↑l) (highFac highAmp1 (2 * Real.pi)) r :=
    (highFac_contDiff highAmp1 (2 * Real.pi) highAmp1_contDiff).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
  rw [hfun, iteratedDeriv_four (G 0 0 τ) (Complex.I * G 0 1 τ)
    (Complex.exp ((2 * Real.pi : ℝ) : ℂ) * G 1 0 τ)
    (Complex.exp ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * G 1 1 τ))
    (highFac highAmp0 0) (highFac highAmp1 0) (highFac highAmp0 (2 * Real.pi))
    (highFac highAmp1 (2 * Real.pi)) l r hcd0 hcd1 hcd2 hcd3]
  -- bound the four terms and sum
  have e0 := hbB0 r
  have e1 := hbB1 r
  have e2 := hbB2 r
  have e3 := hbB3 r
  have hbnd0 : |r| ^ k * ‖(G 0 0 τ) * iteratedDeriv l (highFac highAmp0 0) r‖
      ≤ α0 * B0 * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3) := by
    rw [norm_mul]
    calc |r| ^ k * (‖G 0 0 τ‖ * ‖iteratedDeriv l (highFac highAmp0 0) r‖)
        = ‖G 0 0 τ‖ * (|r| ^ k * ‖iteratedDeriv l (highFac highAmp0 0) r‖) := by ring
      _ ≤ (α0 * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3)) * B0 :=
          mul_le_mul hc0 e0 (by positivity) (by positivity)
      _ = α0 * B0 * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3) := by ring
  have hbnd1 : |r| ^ k * ‖(Complex.I * G 0 1 τ) * iteratedDeriv l (highFac highAmp1 0) r‖
      ≤ α1 * B1 * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3) := by
    rw [norm_mul]
    calc |r| ^ k * (‖Complex.I * G 0 1 τ‖ * ‖iteratedDeriv l (highFac highAmp1 0) r‖)
        = ‖Complex.I * G 0 1 τ‖ * (|r| ^ k * ‖iteratedDeriv l (highFac highAmp1 0) r‖) := by ring
      _ ≤ (α1 * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3)) * B1 :=
          mul_le_mul hc1 e1 (by positivity) (by positivity)
      _ = α1 * B1 * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3) := by ring
  have hbnd2 : |r| ^ k * ‖(Complex.exp ((2 * Real.pi : ℝ) : ℂ) * G 1 0 τ)
        * iteratedDeriv l (highFac highAmp0 (2 * Real.pi)) r‖
      ≤ E * α2 * B2 * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3) := by
    rw [norm_mul]
    calc |r| ^ k * (‖Complex.exp ((2 * Real.pi : ℝ) : ℂ) * G 1 0 τ‖
          * ‖iteratedDeriv l (highFac highAmp0 (2 * Real.pi)) r‖)
        = ‖Complex.exp ((2 * Real.pi : ℝ) : ℂ) * G 1 0 τ‖
          * (|r| ^ k * ‖iteratedDeriv l (highFac highAmp0 (2 * Real.pi)) r‖) := by ring
      _ ≤ (E * α2 * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3)) * B2 :=
          mul_le_mul hc2 e2 (by positivity) (by positivity)
      _ = E * α2 * B2 * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3) := by ring
  have hbnd3 : |r| ^ k * ‖(Complex.exp ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * G 1 1 τ))
        * iteratedDeriv l (highFac highAmp1 (2 * Real.pi)) r‖
      ≤ E * α3 * B3 * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3) := by
    rw [norm_mul]
    calc |r| ^ k * (‖Complex.exp ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * G 1 1 τ)‖
          * ‖iteratedDeriv l (highFac highAmp1 (2 * Real.pi)) r‖)
        = ‖Complex.exp ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * G 1 1 τ)‖
          * (|r| ^ k * ‖iteratedDeriv l (highFac highAmp1 (2 * Real.pi)) r‖) := by ring
      _ ≤ (E * α3 * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3)) * B3 :=
          mul_le_mul hc3 e3 (by positivity) (by positivity)
      _ = E * α3 * B3 * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3) := by ring
  calc |r| ^ k * ‖G 0 0 τ * iteratedDeriv l (highFac highAmp0 0) r
          + (Complex.I * G 0 1 τ) * iteratedDeriv l (highFac highAmp1 0) r
          + (Complex.exp ((2 * Real.pi : ℝ) : ℂ) * G 1 0 τ)
              * iteratedDeriv l (highFac highAmp0 (2 * Real.pi)) r
          + (Complex.exp ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * G 1 1 τ))
              * iteratedDeriv l (highFac highAmp1 (2 * Real.pi)) r‖
      ≤ |r| ^ k * (‖G 0 0 τ * iteratedDeriv l (highFac highAmp0 0) r‖
          + ‖(Complex.I * G 0 1 τ) * iteratedDeriv l (highFac highAmp1 0) r‖
          + ‖(Complex.exp ((2 * Real.pi : ℝ) : ℂ) * G 1 0 τ)
              * iteratedDeriv l (highFac highAmp0 (2 * Real.pi)) r‖
          + ‖(Complex.exp ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * G 1 1 τ))
              * iteratedDeriv l (highFac highAmp1 (2 * Real.pi)) r‖) :=
        mul_le_mul_of_nonneg_left
          (norm_four_add_le (G 0 0 τ * iteratedDeriv l (highFac highAmp0 0) r)
            ((Complex.I * G 0 1 τ) * iteratedDeriv l (highFac highAmp1 0) r)
            ((Complex.exp ((2 * Real.pi : ℝ) : ℂ) * G 1 0 τ)
              * iteratedDeriv l (highFac highAmp0 (2 * Real.pi)) r)
            ((Complex.exp ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * G 1 1 τ))
              * iteratedDeriv l (highFac highAmp1 (2 * Real.pi)) r))
          (by positivity)
    _ = |r| ^ k * ‖G 0 0 τ * iteratedDeriv l (highFac highAmp0 0) r‖
          + |r| ^ k * ‖(Complex.I * G 0 1 τ) * iteratedDeriv l (highFac highAmp1 0) r‖
          + |r| ^ k * ‖(Complex.exp ((2 * Real.pi : ℝ) : ℂ) * G 1 0 τ)
              * iteratedDeriv l (highFac highAmp0 (2 * Real.pi)) r‖
          + |r| ^ k * ‖(Complex.exp ((2 * Real.pi : ℝ) : ℂ) * (Complex.I * G 1 1 τ))
              * iteratedDeriv l (highFac highAmp1 (2 * Real.pi)) r‖ := by ring
    _ ≤ α0 * B0 * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3)
          + α1 * B1 * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3)
          + E * α2 * B2 * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3)
          + E * α3 * B3 * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3) :=
        add_le_add (add_le_add (add_le_add hbnd0 hbnd1) hbnd2) hbnd3
    _ = (α0 * B0 + α1 * B1 + E * α2 * B2 + E * α3 * B3)
          * (Work.Kernels.scale τ) ^ max (max N0 N1) (max N2 N3) := by ring

end Work.Asymptotics
