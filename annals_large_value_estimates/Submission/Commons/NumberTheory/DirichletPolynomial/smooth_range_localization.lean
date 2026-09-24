import Mathlib.Analysis.Complex.ExponentialBounds
import Submission.Commons.Analysis.Fourier.fejer_window_localization_majorant

open Finset
open scoped BigOperators

set_option maxHeartbeats 1600000

namespace Commons.NumberTheory.DirichletPolynomial

noncomputable section

open Commons.Analysis.Fourier

def tent (W x : ℝ) : ℝ := 2 * max 0 (1 - |x| / (2 * W))
def EE (θ z : ℝ) : ℂ := Complex.exp (↑(θ * z) * Complex.I)

lemma tent_eq {W : ℝ} (hW : 0 < W) (x : ℝ) : tent W x = 2 * tri (x / (2 * W)) := by
  unfold tent tri; rw [max_comm, abs_div, abs_of_pos (by linarith : (0:ℝ) < 2*W)]

lemma EE_add (θ a b : ℝ) : EE θ a * EE θ b = EE θ (a + b) := by
  unfold EE; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma EE_conj (θ z : ℝ) : (starRingEnd ℂ) (EE θ z) = EE θ (-z) := by
  unfold EE; rw [← Complex.exp_conj]; congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

lemma EEsincos (θ z : ℝ) : EE θ z = ↑(Real.cos (θ*z)) + ↑(Real.sin (θ*z)) * Complex.I := by
  unfold EE; rw [Complex.exp_ofReal_mul_I]

lemma tri_cos_nonneg {R : ℕ} (t : Fin R → ℝ) (β T : ℝ) (hT : 0 < T) :
    0 ≤ ∑ i : Fin R, ∑ j : Fin R, tri ((t i - t j) / T) * Real.cos (β * (t i - t j)) := by
  have h := fejer_expansion_identity_re (g := fun y : ℝ => Real.sinc (Real.pi * y)^2)
      integrable_sinc_pi_sq (ĝ := tri) (fun s => integral_sinc_pi_sq_mul_exp s) T t
      (fun i => Complex.exp (Complex.I * ((β * t i : ℝ) : ℂ)))
  have hkey : ∀ i j : Fin R,
      (Complex.exp (Complex.I * ((β * t i : ℝ) : ℂ)) * (starRingEnd ℂ)
        (Complex.exp (Complex.I * ((β * t j : ℝ) : ℂ)))).re = Real.cos (β * (t i - t j)) := by
    intro i j
    have h1 : (starRingEnd ℂ) (Complex.exp (Complex.I * ((β * t j : ℝ) : ℂ)))
        = Complex.exp (-(Complex.I * ((β * t j : ℝ) : ℂ))) := by
      rw [← Complex.exp_conj]; congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring
    rw [h1, ← Complex.exp_add]
    have h2 : Complex.I * ((β * t i : ℝ) : ℂ) + -(Complex.I * ((β * t j : ℝ) : ℂ))
        = ((β * (t i - t j) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [h2, Complex.exp_ofReal_mul_I, Complex.add_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.cos_ofReal_re, Complex.sin_ofReal_im]
    ring
  have hsum : (∑ i : Fin R, ∑ j : Fin R, tri ((t i - t j) / T) * Real.cos (β * (t i - t j)))
      = (∑ i : Fin R, ∑ j : Fin R, tri ((t i - t j) / T) *
          (Complex.exp (Complex.I * ((β * t i : ℝ) : ℂ)) * (starRingEnd ℂ)
            (Complex.exp (Complex.I * ((β * t j : ℝ) : ℂ)))).re) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; rw [hkey i j]
  rw [hsum, h]
  exact MeasureTheory.integral_nonneg (fun y => by positivity)

lemma tent_cos_nonneg {R : ℕ} (t : Fin R → ℝ) (W : ℝ) (hW : 0 < W) (β : ℝ) :
    0 ≤ ∑ i : Fin R, ∑ j : Fin R, tent W (t i - t j) * Real.cos (β * (t i - t j)) := by
  have hfac : (∑ i, ∑ j, tent W (t i - t j) * Real.cos (β * (t i - t j)))
      = 2 * (∑ i, ∑ j, tri ((t i - t j) / (2*W)) * Real.cos (β * (t i - t j))) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
    rw [tent_eq hW]; ring
  rw [hfac]
  have := tri_cos_nonneg t β (2*W) (by linarith)
  linarith

lemma odd_kernel_zero {R : ℕ} (φ f : ℝ → ℝ) (hφ : ∀ x, φ (-x) = φ x) (hf : ∀ x, f (-x) = -f x)
    (t : Fin R → ℝ) :
    ∑ i : Fin R, ∑ j : Fin R, φ (t i - t j) * f (t i - t j) = 0 := by
  have hg : ∀ i j : Fin R, φ (t i - t j) * f (t i - t j) = -(φ (t j - t i) * f (t j - t i)) := by
    intro i j
    have h1 : t j - t i = -(t i - t j) := by ring
    rw [h1, hφ, hf]; ring
  have hA : (∑ i, ∑ j, φ (t j - t i) * f (t j - t i)) = (∑ i, ∑ j, φ (t i - t j) * f (t i - t j)) := by
    rw [Finset.sum_comm]
  have key : (∑ i, ∑ j, φ (t i - t j) * f (t i - t j))
      = - (∑ i, ∑ j, φ (t i - t j) * f (t i - t j)) := by
    conv_lhs => rw [← hA]
    have hg' : ∀ i j : Fin R, φ (t j - t i) * f (t j - t i) = -(φ (t i - t j) * f (t i - t j)) := by
      intro i j; have := hg i j; linarith
    rw [show (∑ i, ∑ j, φ (t j - t i) * f (t j - t i))
        = ∑ i, ∑ j, -(φ (t i - t j) * f (t i - t j)) from by
      apply Finset.sum_congr rfl; intro i _
      apply Finset.sum_congr rfl; intro j _; exact hg' i j]
    simp_rw [Finset.sum_neg_distrib]
  linarith [key]

lemma tent_even (W x : ℝ) : tent W (-x) = tent W x := by unfold tent; rw [abs_neg]

/-- The tent-weighted cosine kernel of a Dirichlet sum: for `n,m ≥ 1`, the "complex kernel"
is real and nonnegative. -/
lemma tent_kernel_nonneg {R : ℕ} (t : Fin R → ℝ) (W : ℝ) (hW : 0 < W) (un um : ℝ) :
    (∑ i : Fin R, ∑ j : Fin R, tent W (t i - t j) * EE (t i - t j) (un - um)).re
      = ∑ i : Fin R, ∑ j : Fin R, tent W (t i - t j) * Real.cos ((un - um) * (t i - t j)) := by
  have him : (∑ i : Fin R, ∑ j : Fin R, tent W (t i - t j) * Real.sin ((un - um) * (t i - t j))) = 0 :=
    odd_kernel_zero (tent W) (fun x => Real.sin ((un - um)*x)) (tent_even W)
      (fun x => by rw [show (un - um)*(-x) = -((un - um)*x) from by ring, Real.sin_neg]) t
  have hre : ∀ i j : Fin R, (tent W (t i - t j) * EE (t i - t j) (un - um)).re
      = tent W (t i - t j) * Real.cos ((un - um) * (t i - t j)) := by
    intro i j
    rw [EEsincos]
    rw [show (t i - t j) * (un - um) = (un - um) * (t i - t j) from by ring]
    rw [show tent W (t i - t j) * (↑(Real.cos ((un - um) * (t i - t j)))
          + ↑(Real.sin ((un - um) * (t i - t j))) * Complex.I)
        = ↑(tent W (t i - t j) * Real.cos ((un - um) * (t i - t j)))
          + ↑(tent W (t i - t j) * Real.sin ((un - um) * (t i - t j))) * Complex.I from by push_cast; ring]
    rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.ofReal_re, Complex.I_re, Complex.I_im]
    ring
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl; intro j _
  exact hre i j


lemma normSq_sum_EE (c : ℕ → ℂ) (S : Finset ℕ) (θ : ℝ) :
    ‖∑ n ∈ S, c n * EE θ (Real.log n)‖^2
    = (∑ n ∈ S, ∑ m ∈ S, c n * (starRingEnd ℂ) (c m) * EE θ (Real.log n - Real.log m)).re := by
  have hzc : ∀ z : ℂ, ‖z‖^2 = (z * (starRingEnd ℂ) z).re := by
    intro z; rw [Complex.mul_conj, Complex.ofReal_re, ← Complex.normSq_eq_norm_sq]
  have hterm : ∀ n m : ℕ,
      c n * EE θ (Real.log n) * ((starRingEnd ℂ) (c m) * (starRingEnd ℂ) (EE θ (Real.log m)))
      = c n * (starRingEnd ℂ) (c m) * EE θ (Real.log n - Real.log m) := by
    intro n m
    rw [EE_conj θ (Real.log m)]
    rw [show c n * EE θ (Real.log n) * ((starRingEnd ℂ) (c m) * EE θ (-Real.log m))
        = c n * (starRingEnd ℂ) (c m) * (EE θ (Real.log n) * EE θ (-Real.log m)) by ring]
    rw [EE_add θ (Real.log n) (-Real.log m)]
    rw [show Real.log n + -Real.log m = Real.log n - Real.log m from by ring]
  have expand : (∑ n ∈ S, c n * EE θ (Real.log n))
        * (starRingEnd ℂ) (∑ n ∈ S, c n * EE θ (Real.log n))
      = ∑ n ∈ S, ∑ m ∈ S, c n * (starRingEnd ℂ) (c m) * EE θ (Real.log n - Real.log m) := by
    rw [map_sum]
    simp only [map_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl; intro n _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro m _
    exact hterm n m
  rw [hzc, expand]

/-- The tent-weighted kernel `Kl` is nonnegative. -/
lemma Kl_nonneg {R : ℕ} (t : Fin R → ℝ) (W : ℝ) (hW : 0 < W) (a b : ℝ) :
    0 ≤ ∑ i : Fin R, ∑ j : Fin R, tent W (t i - t j) * Real.cos ((a - b) * (t i - t j)) :=
  tent_cos_nonneg t W hW (a - b)


open MeasureTheory Real
open scoped FourierTransform

theorem dirichlet_coefficient_majorant :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 / 4 → ∀ (Δ : ℝ), 0 < Δ →
    ∀ (S : Finset ℕ), (∀ n ∈ S, 1 ≤ n) → ∀ (c : ℕ → ℝ), ∀ (a : ℕ → ℂ), (∀ n, ‖a n‖ ≤ c n) →
    ∀ (R : ℕ) (t : Fin R → ℝ), (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
    (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ Δ then
        ‖∑ n ∈ S,
          a n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0))
    ≤ C / ε * (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ 4 * ε * Δ then
        ‖∑ n ∈ S,
          (c n : ℂ) * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0)) := by
  refine ⟨8, by norm_num, ?_⟩
  intro ε hε hε4 Δ hΔ S hS c a ha R t hsep
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hTpos : (0:ℝ) < 4 * Δ := by positivity
  have hc_nonneg : ∀ n, 0 ≤ c n := fun n => (norm_nonneg (a n)).trans (ha n)
  set L : ℕ → ℝ := fun n => Real.log n with hL
  set ph : ℕ → ℕ → Fin R → ℂ := fun n m i => Complex.exp (↑((L n - L m) * (t i)) * Complex.I) with hph
  set q : ℕ → Fin R → Fin R → ℂ := fun n i j => Complex.exp (↑(L n * (t i - t j)) * Complex.I) with hq
  set zp : ℕ → Fin R → Fin R → ℂ := fun n i j => q n i j / (Real.sqrt (n:ℝ):ℂ) with hzp
  set A : Fin R → Fin R → ℂ := fun i j => ∑ n ∈ S, a n * zp n i j with hA
  set B : Fin R → Fin R → ℂ := fun i j => ∑ n ∈ S, (c n : ℂ) * zp n i j with hB
  set Zf : ℕ → ℕ → ℝ → ℂ := fun n m y => ∑ i : Fin R,
      ph n m i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / (4 * Δ))) * Complex.I) with hZf
  set Vf : ℝ → ℝ := fun y => ∑ n ∈ S, ∑ m ∈ S,
      (c n * c m) / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ)) * ‖Zf n m y‖ ^ 2 with hVf
  set wf : ℕ → ℕ → ℂ := fun n m =>
      (a n * (starRingEnd ℂ) (a m)) / ((Real.sqrt (n:ℝ):ℂ) * (Real.sqrt (m:ℝ):ℂ)) with hwf
  set wc : ℕ → ℕ → ℝ := fun n m =>
      (c n * c m) / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ)) with hwc
  set Uf : ℝ → ℂ := fun y => ∑ n ∈ S, ∑ m ∈ S,
      wf n m * ((‖Zf n m y‖ ^ 2 : ℝ) : ℂ) with hUf
  set Qr : ℝ := ∑ i : Fin R, ∑ j : Fin R,
      (Real.sinc (Real.pi * ((t i - t j) / (4 * Δ)))) ^ 2 * ‖A i j‖ ^ 2 with hQ
  have hQnn : 0 ≤ Qr := by
    rw [hQ]
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have htri_nonneg : ∀ y : ℝ, 0 ≤ tri y := by
    intro y; rw [show tri y = max (1 - |y|) 0 from rfl]; exact le_max_right _ _
  have hph1 : ∀ (n m : ℕ) (i : Fin R), ‖ph n m i‖ = 1 := by
    intro n m i
    rw [hph]
    exact Complex.norm_exp_ofReal_mul_I _
  have hexp1 : ∀ (y : ℝ) (i : Fin R),
      ‖Complex.exp (↑(-(2 * Real.pi * y * (t i) / (4 * Δ))) * Complex.I)‖ = 1 :=
    fun y i => Complex.norm_exp_ofReal_mul_I _
  have hZbdd : ∀ (n m : ℕ) (y : ℝ), ‖Zf n m y‖ ≤ R := by
    intro n m y
    rw [hZf]
    calc ‖∑ i : Fin R, ph n m i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / (4 * Δ))) * Complex.I)‖
        ≤ ∑ i : Fin R, ‖ph n m i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / (4 * Δ))) * Complex.I)‖ :=
          norm_sum_le _ _
      _ = ∑ i : Fin R, (1:ℝ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_mul, hph1 n m i, hexp1 y i, one_mul]
      _ = R := by simp
  have hZcont : ∀ n m : ℕ, Continuous (fun y : ℝ => Zf n m y) := by
    intro n m
    show Continuous (fun y : ℝ => ∑ i : Fin R,
      ph n m i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / (4 * Δ))) * Complex.I))
    refine continuous_finset_sum _ fun i _ => ?_
    exact continuous_const.mul (by fun_prop)
  have hVcont : Continuous (fun y : ℝ => Vf y) := by
    show Continuous (fun y : ℝ => ∑ n ∈ S, ∑ m ∈ S,
      (c n * c m) / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ)) * ‖Zf n m y‖ ^ 2)
    refine continuous_finset_sum _ fun n hn => continuous_finset_sum _ fun m hm => ?_
    exact ((hZcont n m).norm.pow 2).const_mul _
  have hUcont : Continuous (fun y : ℝ => Uf y) := by
    show Continuous (fun y : ℝ => ∑ n ∈ S, ∑ m ∈ S,
      wf n m * ((‖Zf n m y‖ ^ 2 : ℝ) : ℂ))
    refine continuous_finset_sum _ fun n hn => continuous_finset_sum _ fun m hm => ?_
    exact ((Complex.continuous_ofReal.comp ((hZcont n m).norm.pow 2))).const_mul _
  have hVnn : ∀ y : ℝ, 0 ≤ Vf y := by
    intro y
    rw [hVf]
    refine Finset.sum_nonneg fun n _ => Finset.sum_nonneg fun m _ => ?_
    exact mul_nonneg (div_nonneg (mul_nonneg (hc_nonneg n) (hc_nonneg m))
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))) (sq_nonneg _)
  set M : ℝ := (R:ℝ) ^ 2 * (∑ n ∈ S, c n / Real.sqrt (n:ℝ)) ^ 2 with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]; positivity
  have hVbdd : ∀ y : ℝ, Vf y ≤ M := by
    intro y
    rw [hVf, hMdef]
    have hterm : ∀ n ∈ S, ∀ m ∈ S,
        (c n * c m) / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ)) * ‖Zf n m y‖ ^ 2
        ≤ (R:ℝ) ^ 2 * ((c n / Real.sqrt (n:ℝ)) * (c m / Real.sqrt (m:ℝ))) := by
      intro n hn m hm
      have hs1 : 0 ≤ Real.sqrt (n:ℝ) := Real.sqrt_nonneg _
      have hs2 : 0 ≤ Real.sqrt (m:ℝ) := Real.sqrt_nonneg _
      have h1 : ‖Zf n m y‖ ^ 2 ≤ (R:ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hZbdd n m y) 2
      have h2 : (c n * c m) / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ))
          = (c n / Real.sqrt (n:ℝ)) * (c m / Real.sqrt (m:ℝ)) := by ring
      have h3 : 0 ≤ (c n / Real.sqrt (n:ℝ)) * (c m / Real.sqrt (m:ℝ)) :=
        mul_nonneg (div_nonneg (hc_nonneg n) hs1) (div_nonneg (hc_nonneg m) hs2)
      rw [h2]
      nlinarith [h1, h3, mul_nonneg h3 (sq_nonneg ‖Zf n m y‖)]
    calc ∑ n ∈ S, ∑ m ∈ S,
          (c n * c m) / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ)) * ‖Zf n m y‖ ^ 2
        ≤ ∑ n ∈ S, ∑ m ∈ S, (R:ℝ) ^ 2 * ((c n / Real.sqrt (n:ℝ)) * (c m / Real.sqrt (m:ℝ))) :=
          Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => hterm n hn m hm
      _ = (R:ℝ) ^ 2 * (∑ n ∈ S, c n / Real.sqrt (n:ℝ)) ^ 2 := by
          have h1 : (∑ n ∈ S, ∑ m ∈ S, (c n / Real.sqrt (n:ℝ)) * (c m / Real.sqrt (m:ℝ)))
              = (∑ n ∈ S, c n / Real.sqrt (n:ℝ)) ^ 2 := by
            rw [pow_two, Finset.sum_mul_sum]
          rw [← h1, Finset.mul_sum]
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [Finset.mul_sum]
  have hsinc_le_one : ∀ u : ℝ, Real.sinc u ^ 2 ≤ 1 := by
    intro u
    have h1 : |Real.sinc u| ≤ 1 := abs_sinc_le_one u
    have h2 : Real.sinc u ^ 2 = |Real.sinc u| ^ 2 := (sq_abs _).symm
    rw [h2]
    nlinarith [h1, abs_nonneg (Real.sinc u)]
  have hexp_eq : ∀ (n : ℕ) (τ : ℝ),
      Complex.exp (↑(τ * Real.log n) * Complex.I) = Complex.exp (↑(L n * τ) * Complex.I) := by
    intro n τ
    rw [hL]
    congr 1
    push_cast
    ring
  have hAeq : ∀ i j : Fin R,
      (∑ n ∈ S, a n * (n:ℂ) ^ (Complex.I * ((t i - t j : ℝ):ℂ)) / (Real.sqrt (n:ℝ):ℂ)) = A i j := by
    intro i j
    rw [hA]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := hS n hn
    rw [mul_div_assoc, cpow_I_mul_of_one_le hn1 (t i - t j),
      hexp_eq n (t i - t j), hzp, hq]
  have hBeq : ∀ i j : Fin R,
      (∑ n ∈ S, (c n : ℂ) * (n:ℂ) ^ (Complex.I * ((t i - t j : ℝ):ℂ)) / (Real.sqrt (n:ℝ):ℂ)) = B i j := by
    intro i j
    rw [hB]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hn1 : 1 ≤ n := hS n hn
    rw [mul_div_assoc, cpow_I_mul_of_one_le hn1 (t i - t j),
      hexp_eq n (t i - t j), hzp, hq]
  have hstepA : (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ Δ then
        ‖∑ n ∈ S, a n * (n:ℂ) ^ (Complex.I * ((t i - t j : ℝ):ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖ ^ 2
       else 0)) ≤ 2 * Qr := by
    have h1 : (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ Δ then
          ‖∑ n ∈ S, a n * (n:ℂ) ^ (Complex.I * ((t i - t j : ℝ):ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖ ^ 2
         else 0))
        = ∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ Δ then ‖A i j‖ ^ 2 else 0) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hAeq i j]
    rw [h1, hQ]
    calc ∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ Δ then ‖A i j‖ ^ 2 else 0)
        ≤ ∑ i : Fin R, ∑ j : Fin R,
            2 * ((Real.sinc (Real.pi * ((t i - t j) / (4 * Δ)))) ^ 2 * ‖A i j‖ ^ 2) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          by_cases h : |t i - t j| ≤ Δ
          · rw [if_pos h]
            have habs : |(t i - t j) / (4 * Δ)| ≤ 1 / 4 := by
              rw [abs_div, abs_of_pos hTpos, div_le_iff₀ hTpos]
              nlinarith
            have hs := sinc_pi_sq_lower_bound habs
            nlinarith [sq_nonneg ‖A i j‖]
          · rw [if_neg h]
            positivity
      _ = 2 * ∑ i : Fin R, ∑ j : Fin R,
            (Real.sinc (Real.pi * ((t i - t j) / (4 * Δ)))) ^ 2 * ‖A i j‖ ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
  have hczp : ∀ (m : ℕ) (i j : Fin R),
      (starRingEnd ℂ) (zp m i j) = (starRingEnd ℂ) (q m i j) / (Real.sqrt (m:ℝ):ℂ) := by
    intro m i j
    rw [hzp, map_div₀]
    congr 1
    exact Complex.conj_ofReal _
  have hkey : ∀ (n m : ℕ) (i j : Fin R),
      q n i j * (starRingEnd ℂ) (q m i j) = ph n m i * (starRingEnd ℂ) (ph n m j) := by
    intro n m i j
    simp only [hq, hph, star_exp_ofReal_mul_I, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hAA : ∀ i j : Fin R, A i j * (starRingEnd ℂ) (A i j)
      = ∑ n ∈ S, ∑ m ∈ S, wf n m * (ph n m i * (starRingEnd ℂ) (ph n m j)) := by
    intro i j
    simp only [hA]
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, hczp m i j, hzp]
    rw [show (a n * (q n i j / (Real.sqrt (n:ℝ):ℂ)))
          * ((starRingEnd ℂ) (a m) * ((starRingEnd ℂ) (q m i j) / (Real.sqrt (m:ℝ):ℂ)))
        = ((a n * (starRingEnd ℂ) (a m)) / ((Real.sqrt (n:ℝ):ℂ) * (Real.sqrt (m:ℝ):ℂ)))
          * (q n i j * (starRingEnd ℂ) (q m i j)) from by ring,
      hkey n m i j]
  have hnormA : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
    intro z
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  have hQc : (Qr : ℂ) = ∑ i : Fin R, ∑ j : Fin R,
      ((Real.sinc (Real.pi * ((t i - t j) / (4 * Δ))) ^ 2 : ℝ) : ℂ)
        * (A i j * (starRingEnd ℂ) (A i j)) := by
    rw [hQ, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.ofReal_mul, hnormA]
  have hQ2 : (Qr : ℂ) = ∑ n ∈ S, ∑ m ∈ S, wf n m *
      (∑ i : Fin R, ∑ j : Fin R, ((Real.sinc (Real.pi * ((t i - t j) / (4 * Δ))) ^ 2 : ℝ) : ℂ)
        * (ph n m i * (starRingEnd ℂ) (ph n m j))) := by
    rw [hQc]
    have hnorm : (∑ i : Fin R, ∑ j : Fin R,
          ((Real.sinc (Real.pi * ((t i - t j) / (4 * Δ))) ^ 2 : ℝ) : ℂ)
            * (A i j * (starRingEnd ℂ) (A i j)))
        = ∑ i : Fin R, ∑ j : Fin R, ∑ n ∈ S, ∑ m ∈ S, wf n m *
            (((Real.sinc (Real.pi * ((t i - t j) / (4 * Δ))) ^ 2 : ℝ) : ℂ)
              * (ph n m i * (starRingEnd ℂ) (ph n m j))) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hAA i j, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    rw [hnorm, sum4_comm]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
  have hident : ∀ n m : ℕ,
      (∑ i : Fin R, ∑ j : Fin R, ((Real.sinc (Real.pi * ((t i - t j) / (4 * Δ))) ^ 2 : ℝ) : ℂ)
          * (ph n m i * (starRingEnd ℂ) (ph n m j)))
        = ∫ y : ℝ, (tri y : ℂ) * ((‖Zf n m y‖ ^ 2 : ℝ) : ℂ) :=
    fun n m => fejer_expansion_identity tri_integrable
      (Ĝ := fun s : ℝ => ((Real.sinc (Real.pi * s) ^ 2 : ℝ) : ℂ))
      (fun s => integral_tri_mul_exp s) (4 * Δ) t (ph n m)
  have hQ3 : (Qr : ℂ) = ∑ n ∈ S, ∑ m ∈ S, wf n m *
      ∫ y : ℝ, (tri y : ℂ) * ((‖Zf n m y‖ ^ 2 : ℝ) : ℂ) := by
    rw [hQ2]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    rw [hident n m]
  have hstepB : (Qr : ℂ) = ∫ y : ℝ, (tri y : ℂ) * Uf y := by
    rw [hQ3]
    refine sum_mul_integral_eq_integral_sum wf (fun n m y => ((‖Zf n m y‖ ^ 2 : ℝ) : ℂ)) S S
      (g := fun y : ℝ => (tri y : ℂ)) tri_integrable.ofReal ?_
    intro n hn m hm
    refine Integrable.mono' (tri_integrable.const_mul ((R:ℝ)^2))
      (((Complex.continuous_ofReal.comp tri_continuous).aestronglyMeasurable).mul
        ((Complex.continuous_ofReal.comp ((hZcont n m).norm.pow 2)).aestronglyMeasurable)) ?_
    filter_upwards with y
    rw [norm_mul, norm_ofReal_of_nonneg (htri_nonneg y), norm_ofReal_of_nonneg (sq_nonneg _)]
    have hb := hZbdd n m y
    have hb2 : ‖Zf n m y‖ ^ 2 ≤ (R:ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    nlinarith [htri_nonneg y, norm_nonneg (Zf n m y)]
  have hUnorm : ∀ y : ℝ, ‖Uf y‖ ≤ Vf y := by
    intro y
    rw [hUf, hVf]
    calc ‖∑ n ∈ S, ∑ m ∈ S, wf n m * ((‖Zf n m y‖ ^ 2 : ℝ) : ℂ)‖
        ≤ ∑ n ∈ S, ‖∑ m ∈ S, wf n m * ((‖Zf n m y‖ ^ 2 : ℝ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ S, ∑ m ∈ S, ‖wf n m * ((‖Zf n m y‖ ^ 2 : ℝ) : ℂ)‖ :=
          Finset.sum_le_sum fun n _ => norm_sum_le _ _
      _ ≤ ∑ n ∈ S, ∑ m ∈ S,
            (c n * c m) / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ)) * ‖Zf n m y‖ ^ 2 := by
          refine Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun m hm => ?_
          rw [norm_mul, norm_ofReal_of_nonneg (sq_nonneg _)]
          have hn1 : 1 ≤ n := hS n hn
          have hm1 : 1 ≤ m := hS m hm
          have hsn : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos_of_pos (by exact_mod_cast hn1)
          have hsm : 0 < Real.sqrt (m:ℝ) := Real.sqrt_pos_of_pos (by exact_mod_cast hm1)
          have hwn : ‖wf n m‖ = (‖a n‖ * ‖a m‖) / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ)) := by
            rw [hwf, norm_div, norm_mul, Complex.norm_conj]
            congr 1
            rw [norm_mul, norm_ofReal_of_nonneg (Real.sqrt_nonneg _),
              norm_ofReal_of_nonneg (Real.sqrt_nonneg _)]
          rw [hwn]
          have h1 : ‖a n‖ * ‖a m‖ ≤ c n * c m :=
            mul_le_mul (ha n) (ha m) (norm_nonneg _) (hc_nonneg n)
          have h2 : (0:ℝ) < Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ) := mul_pos hsn hsm
          have h3 : ‖a n‖ * ‖a m‖ / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ))
              ≤ c n * c m / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ)) :=
            div_le_div_of_nonneg_right h1 h2.le
          nlinarith [h3, sq_nonneg ‖Zf n m y‖]
  have hstepC : Qr ≤ ∫ y : ℝ, tri y * Vf y := by
    have h1 : Qr = ‖(Qr : ℂ)‖ := by
      rw [show ‖(Qr : ℂ)‖ = |Qr| from RCLike.norm_ofReal Qr, abs_of_nonneg hQnn]
    rw [h1, hstepB]
    have hint1 : Integrable (fun y : ℝ => tri y * ‖Uf y‖) := by
      refine Integrable.mono' (tri_integrable.const_mul M)
        (tri_continuous.aestronglyMeasurable.mul hUcont.norm.aestronglyMeasurable) ?_
      filter_upwards with y
      show ‖tri y * ‖Uf y‖‖ ≤ M * tri y
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (htri_nonneg y) (norm_nonneg _))]
      nlinarith [htri_nonneg y, hUnorm y, hVbdd y, hMnn]
    have hint2 : Integrable (fun y : ℝ => tri y * Vf y) := by
      refine Integrable.mono' (tri_integrable.const_mul M)
        (tri_continuous.aestronglyMeasurable.mul hVcont.aestronglyMeasurable) ?_
      filter_upwards with y
      show ‖tri y * Vf y‖ ≤ M * tri y
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (htri_nonneg y) (hVnn y))]
      nlinarith [htri_nonneg y, hVbdd y, hMnn]
    calc ‖∫ y : ℝ, (tri y : ℂ) * Uf y‖
        ≤ ∫ y : ℝ, ‖(tri y : ℂ) * Uf y‖ := norm_integral_le_integral_norm _
      _ = ∫ y : ℝ, tri y * ‖Uf y‖ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          show ‖(tri y : ℂ) * Uf y‖ = tri y * ‖Uf y‖
          rw [norm_mul, norm_ofReal_of_nonneg (htri_nonneg y)]
      _ ≤ ∫ y : ℝ, tri y * Vf y := by
          refine integral_mono hint1 hint2 ?_
          intro y
          exact mul_le_mul_of_nonneg_left (hUnorm y) (htri_nonneg y)
  have hstepD : (∫ y : ℝ, tri y * Vf y) ≤ 2 * ∫ y : ℝ, Real.sinc (Real.pi * (ε * y)) ^ 2 * Vf y := by
    have hpoint : ∀ y : ℝ, tri y ≤ 2 * Real.sinc (Real.pi * (ε * y)) ^ 2 := by
      intro y
      rcases le_or_gt |y| 1 with hy | hy
      · have h1 : |ε * y| ≤ 1 / 4 := by
          rw [abs_mul, abs_of_pos hε]
          calc ε * |y| ≤ (1 / 4) * 1 := mul_le_mul hε4 hy (abs_nonneg y) (by norm_num)
            _ = 1 / 4 := by norm_num
        have hs := sinc_pi_sq_lower_bound h1
        have ht := tri_eq_one_sub hy
        rw [ht]
        linarith [abs_nonneg y, hs]
      · rw [tri_eq_zero_of_one_le_abs hy.le]
        positivity
    have hint1 : Integrable (fun y : ℝ => tri y * Vf y) := by
      refine Integrable.mono' (tri_integrable.const_mul M)
        (tri_continuous.aestronglyMeasurable.mul hVcont.aestronglyMeasurable) ?_
      filter_upwards with y
      show ‖tri y * Vf y‖ ≤ M * tri y
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (htri_nonneg y) (hVnn y))]
      nlinarith [htri_nonneg y, hVbdd y, hMnn]
    have hint2 : Integrable (fun y : ℝ => (2 * Real.sinc (Real.pi * (ε * y)) ^ 2) * Vf y) := by
      have h2 : Integrable (fun y : ℝ =>
          2 * Real.sinc (Real.pi * (ε * y)) ^ 2 * M) :=
        ((integrable_sinc_pi_sq.comp_mul_left' hε.ne').const_mul 2).mul_const M
      refine Integrable.mono' h2 ((by fun_prop : Continuous (fun y : ℝ =>
          Real.sinc (Real.pi * (ε * y)) ^ 2)).const_mul _ |>.mul hVcont).aestronglyMeasurable ?_
      filter_upwards with y
      show ‖(2 * Real.sinc (Real.pi * (ε * y)) ^ 2) * Vf y‖ ≤ 2 * Real.sinc (Real.pi * (ε * y)) ^ 2 * M
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _)) (hVnn y))]
      have hs := hsinc_le_one (Real.pi * (ε * y))
      have hsnn : 0 ≤ Real.sinc (Real.pi * (ε * y)) ^ 2 := sq_nonneg _
      nlinarith [hVbdd y, hVnn y, hs, hMnn]
    calc ∫ y : ℝ, tri y * Vf y
        ≤ ∫ y : ℝ, (2 * Real.sinc (Real.pi * (ε * y)) ^ 2) * Vf y := by
          refine integral_mono hint1 hint2 ?_
          intro y
          have h := hpoint y
          nlinarith [hVnn y]
      _ = 2 * ∫ y : ℝ, Real.sinc (Real.pi * (ε * y)) ^ 2 * Vf y := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          show (2 * Real.sinc (Real.pi * (ε * y)) ^ 2) * Vf y
            = 2 * (Real.sinc (Real.pi * (ε * y)) ^ 2 * Vf y)
          ring
  have hstepE : (∫ y : ℝ, Real.sinc (Real.pi * (ε * y)) ^ 2 * Vf y)
      = (1 / ε) * ∫ y : ℝ, Real.sinc (Real.pi * y) ^ 2 * Vf (y / ε) := by
    have h := Measure.integral_comp_mul_left (fun u : ℝ => Real.sinc (Real.pi * u) ^ 2 * Vf (u / ε)) ε
    have hL : (∫ x : ℝ, Real.sinc (Real.pi * (ε * x)) ^ 2 * Vf ((ε * x) / ε))
        = (∫ x : ℝ, Real.sinc (Real.pi * (ε * x)) ^ 2 * Vf x) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show Real.sinc (Real.pi * (ε * x)) ^ 2 * Vf ((ε * x) / ε)
        = Real.sinc (Real.pi * (ε * x)) ^ 2 * Vf x
      rw [mul_div_cancel_left₀ x hεne]
    rw [hL] at h
    rw [h, abs_of_pos (inv_pos.mpr hε), smul_eq_mul, inv_eq_one_div]
  have hstepF : (∫ y : ℝ, Real.sinc (Real.pi * y) ^ 2 * Vf (y / ε))
      ≤ ∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ 4 * ε * Δ then ‖B i j‖ ^ 2 else 0) := by
    have harg : ∀ (y : ℝ) (i : Fin R),
        -(2 * Real.pi * (y / ε) * (t i) / (4 * Δ))
          = -(2 * Real.pi * y * (t i) / (ε * (4 * Δ))) := by
      intro y i
      ring_nf
    have hZdiv : ∀ (n m : ℕ) (y : ℝ), Zf n m (y / ε)
        = ∑ i : Fin R, ph n m i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / (ε * (4 * Δ)))) * Complex.I) := by
      intro n m y
      show (∑ i : Fin R, ph n m i * Complex.exp (↑(-(2 * Real.pi * (y / ε) * (t i) / (4 * Δ))) * Complex.I))
          = ∑ i : Fin R, ph n m i * Complex.exp (↑(-(2 * Real.pi * y * (t i) / (ε * (4 * Δ)))) * Complex.I)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [harg y i]
    have hintF : ∀ n ∈ S, ∀ m ∈ S,
        Integrable (fun y : ℝ => Real.sinc (Real.pi * y) ^ 2 * ‖Zf n m (y / ε)‖ ^ 2) := by
      intro n hn m hm
      refine Integrable.mono' (integrable_sinc_pi_sq.const_mul ((R:ℝ) ^ 2))
        (((by fun_prop : Continuous (fun y : ℝ => Real.sinc (Real.pi * y) ^ 2)).mul
          (((hZcont n m).comp (by fun_prop : Continuous fun y : ℝ => y / ε)).norm.pow 2)).aestronglyMeasurable) ?_
      filter_upwards with y
      show ‖Real.sinc (Real.pi * y) ^ 2 * ‖Zf n m (y / ε)‖ ^ 2‖ ≤ (R:ℝ) ^ 2 * Real.sinc (Real.pi * y) ^ 2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
      have hb := hZbdd n m (y / ε)
      have hb2 : ‖Zf n m (y / ε)‖ ^ 2 ≤ (R:ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      have hs := hsinc_le_one (Real.pi * y)
      nlinarith [sq_nonneg (Real.sinc (Real.pi * y)), sq_nonneg ‖Zf n m (y / ε)‖]
    have ha := sum_mul_integral_eq_integral_sum_real wc (fun n m y => ‖Zf n m (y / ε)‖ ^ 2) S S
      (g := fun y : ℝ => Real.sinc (Real.pi * y) ^ 2) integrable_sinc_pi_sq hintF
    rw [← ha]
    have hident2 : ∀ n m : ℕ,
        (∫ y : ℝ, Real.sinc (Real.pi * y) ^ 2 * ‖Zf n m (y / ε)‖ ^ 2)
          = ∑ i : Fin R, ∑ j : Fin R, tri ((t i - t j) / (ε * (4 * Δ)))
              * (ph n m i * (starRingEnd ℂ) (ph n m j)).re := by
      intro n m
      have h := fejer_expansion_identity_re integrable_sinc_pi_sq
        (ĝ := tri) (fun s => integral_sinc_pi_sq_mul_exp s) (ε * (4 * Δ)) t (ph n m)
      rw [h]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      show Real.sinc (Real.pi * y) ^ 2 * ‖Zf n m (y / ε)‖ ^ 2
        = Real.sinc (Real.pi * y) ^ 2 * ‖∑ i : Fin R, ph n m i
            * Complex.exp (↑(-(2 * Real.pi * y * (t i) / (ε * (4 * Δ)))) * Complex.I)‖ ^ 2
      rw [hZdiv n m y]
    have hG : ∀ i j : Fin R,
        (∑ n ∈ S, ∑ m ∈ S, wc n m * (ph n m i * (starRingEnd ℂ) (ph n m j)).re) = ‖B i j‖ ^ 2 := by
      intro i j
      have h1 : (B i j * (starRingEnd ℂ) (B i j)).re
          = ∑ n ∈ S, ∑ m ∈ S, wc n m * (ph n m i * (starRingEnd ℂ) (ph n m j)).re := by
        simp only [hB]
        rw [map_sum, Finset.sum_mul_sum]
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [map_mul, hczp m i j, hzp, Complex.conj_ofReal]
        rw [show ((c n : ℂ) * (q n i j / (Real.sqrt (n:ℝ):ℂ))
              * ((c m : ℂ) * ((starRingEnd ℂ) (q m i j) / (Real.sqrt (m:ℝ):ℂ))))
            = (((c n * c m) / (Real.sqrt (n:ℝ) * Real.sqrt (m:ℝ)) : ℝ) : ℂ)
              * (q n i j * (starRingEnd ℂ) (q m i j)) from by push_cast; ring,
          hkey n m i j, Complex.re_ofReal_mul]
      have h2 : (B i j * (starRingEnd ℂ) (B i j)).re = ‖B i j‖ ^ 2 := by
        rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
      rw [← h2, h1]
    have hswap3 : (∑ n ∈ S, ∑ m ∈ S, wc n m * (∑ i : Fin R, ∑ j : Fin R,
          tri ((t i - t j) / (ε * (4 * Δ))) * (ph n m i * (starRingEnd ℂ) (ph n m j)).re))
        = ∑ i : Fin R, ∑ j : Fin R, tri ((t i - t j) / (ε * (4 * Δ))) *
            (∑ n ∈ S, ∑ m ∈ S, wc n m * (ph n m i * (starRingEnd ℂ) (ph n m j)).re) := by
      have e1 : (∑ n ∈ S, ∑ m ∈ S, wc n m * (∑ i : Fin R, ∑ j : Fin R,
            tri ((t i - t j) / (ε * (4 * Δ))) * (ph n m i * (starRingEnd ℂ) (ph n m j)).re))
          = ∑ n ∈ S, ∑ m ∈ S, ∑ i : Fin R, ∑ j : Fin R,
              wc n m * (tri ((t i - t j) / (ε * (4 * Δ)))
                * (ph n m i * (starRingEnd ℂ) (ph n m j)).re) := by
        refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
      rw [e1, ← sum4_comm S S (fun (i : Fin R) (j : Fin R) (n : ℕ) (m : ℕ) =>
        wc n m * (tri ((t i - t j) / (ε * (4 * Δ)))
          * (ph n m i * (starRingEnd ℂ) (ph n m j)).re))]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    have hmid : (∑ n ∈ S, ∑ m ∈ S, wc n m *
          ∫ y : ℝ, Real.sinc (Real.pi * y) ^ 2 * ‖Zf n m (y / ε)‖ ^ 2)
        = ∑ i : Fin R, ∑ j : Fin R, tri ((t i - t j) / (ε * (4 * Δ))) * ‖B i j‖ ^ 2 := by
      calc ∑ n ∈ S, ∑ m ∈ S, wc n m * ∫ y : ℝ, Real.sinc (Real.pi * y) ^ 2 * ‖Zf n m (y / ε)‖ ^ 2
          = ∑ n ∈ S, ∑ m ∈ S, wc n m * (∑ i : Fin R, ∑ j : Fin R,
              tri ((t i - t j) / (ε * (4 * Δ))) * (ph n m i * (starRingEnd ℂ) (ph n m j)).re) := by
            refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
            rw [hident2 n m]
        _ = ∑ i : Fin R, ∑ j : Fin R, tri ((t i - t j) / (ε * (4 * Δ))) *
              (∑ n ∈ S, ∑ m ∈ S, wc n m * (ph n m i * (starRingEnd ℂ) (ph n m j)).re) := hswap3
        _ = ∑ i : Fin R, ∑ j : Fin R, tri ((t i - t j) / (ε * (4 * Δ))) * ‖B i j‖ ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [hG i j]
    rw [hmid]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    by_cases h : |t i - t j| ≤ 4 * ε * Δ
    · rw [if_pos h]
      have h1 : tri ((t i - t j) / (ε * (4 * Δ))) ≤ 1 := by
        rw [show tri ((t i - t j) / (ε * (4 * Δ)))
            = max (1 - |(t i - t j) / (ε * (4 * Δ))|) 0 from rfl]
        exact max_le (by linarith [abs_nonneg ((t i - t j) / (ε * (4 * Δ)))]) (by norm_num)
      nlinarith [sq_nonneg ‖B i j‖]
    · rw [if_neg h]
      have h1 : tri ((t i - t j) / (ε * (4 * Δ))) = 0 := by
        apply tri_eq_zero_of_one_le_abs
        rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < ε * (4 * Δ)), le_div_iff₀ (by positivity)]
        nlinarith [not_le.mp h]
      rw [h1, zero_mul]
  have hRHSeq : (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ 4 * ε * Δ then
        ‖∑ n ∈ S, (c n : ℂ) * (n:ℂ) ^ (Complex.I * ((t i - t j : ℝ):ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖ ^ 2
       else 0))
      = ∑ i : Fin R, ∑ j : Fin R, (if |t i - t j| ≤ 4 * ε * Δ then ‖B i j‖ ^ 2 else 0) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hBeq i j]
  have hRHSnn : 0 ≤ ∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ 4 * ε * Δ then ‖B i j‖ ^ 2 else 0) := by
    refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
    split_ifs
    · exact sq_nonneg _
    · exact le_refl 0
  rw [hRHSeq]
  calc (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ Δ then
        ‖∑ n ∈ S, a n * (n:ℂ) ^ (Complex.I * ((t i - t j : ℝ):ℂ)) / (Real.sqrt (n:ℝ):ℂ)‖ ^ 2
       else 0))
      ≤ 2 * Qr := hstepA
    _ ≤ 2 * (∫ y : ℝ, tri y * Vf y) := by linarith
    _ ≤ 2 * (2 * ∫ y : ℝ, Real.sinc (Real.pi * (ε * y)) ^ 2 * Vf y) := by linarith
    _ = 4 * (∫ y : ℝ, Real.sinc (Real.pi * (ε * y)) ^ 2 * Vf y) := by ring
    _ = 4 * ((1 / ε) * ∫ y : ℝ, Real.sinc (Real.pi * y) ^ 2 * Vf (y / ε)) := by rw [hstepE]
    _ = (4 / ε) * (∫ y : ℝ, Real.sinc (Real.pi * y) ^ 2 * Vf (y / ε)) := by ring
    _ ≤ (4 / ε) * (∑ i : Fin R, ∑ j : Fin R,
          (if |t i - t j| ≤ 4 * ε * Δ then ‖B i j‖ ^ 2 else 0)) :=
        mul_le_mul_of_nonneg_left hstepF (by positivity)
    _ ≤ (8 / ε) * (∑ i : Fin R, ∑ j : Fin R,
          (if |t i - t j| ≤ 4 * ε * Δ then ‖B i j‖ ^ 2 else 0)) := by
        refine mul_le_mul_of_nonneg_right ?_ hRHSnn
        exact div_le_div_of_nonneg_right (by norm_num) hε.le


/-- **Target lemma.** -/
theorem smooth_range_localization :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℕ), 1 ≤ A → A ≤ B →
    ∀ (u : ℕ → ℂ), (∀ n, ‖u n‖ ≤ 1) →
    ∀ (R : ℕ) (t : Fin R → ℝ), (∀ i j, i ≠ j → 1 ≤ |t i - t j|) → ∀ (W : ℝ), 1 ≤ W →
    ∀ (a b : ℕ), A ≤ a → a ≤ b → b ≤ B →
    (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ W then
        ‖∑ n ∈ Finset.Icc a b, u n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ))‖ ^ 2
       else 0))
    ≤ C * (Real.log ((B : ℝ) + 2)) ^ 2 *
      (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ W then
          ‖∑ n ∈ Finset.Icc A B, (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ))‖ ^ 2
         else 0)) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := dirichlet_coefficient_majorant
  refine ⟨4 * C₀, by positivity, ?_⟩
  intro A B hA1 hAB u hu R t hsep W hW a b hAa hab hbB
  have hWpos : (0:ℝ) < W := lt_of_lt_of_le one_pos hW
  have hS : ∀ n ∈ Finset.Icc A B, 1 ≤ n := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    omega
  have hsub : Finset.Icc a b ⊆ Finset.Icc A B := Finset.Icc_subset_Icc hAa hbB
  set aa : ℕ → ℂ := fun n => if n ∈ Finset.Icc a b then u n * (Real.sqrt (n:ℝ):ℂ) else 0 with haa
  set cc : ℕ → ℝ := fun n => Real.sqrt (n:ℝ) with hcc
  have hauc : ∀ n, ‖aa n‖ ≤ cc n := by
    intro n
    rw [haa, hcc]
    simp only []
    by_cases hn : n ∈ Finset.Icc a b
    · rw [if_pos hn, norm_mul, Complex.norm_of_nonneg (Real.sqrt_nonneg _)]
      nlinarith [hu n, Real.sqrt_nonneg (n:ℝ)]
    · rw [if_neg hn, norm_zero]
      exact Real.sqrt_nonneg _
  have hkey := hC₀ (1/4) (by norm_num) (by norm_num) W hWpos (Finset.Icc A B) hS cc aa hauc R t hsep
  have hLinner : ∀ d : ℝ,
      (∑ n ∈ Finset.Icc A B, aa n * (n:ℂ)^(Complex.I*((d:ℝ):ℂ)) / (Real.sqrt (n:ℝ):ℂ))
        = ∑ n ∈ Finset.Icc a b, u n * (n:ℂ)^(Complex.I*((d:ℝ):ℂ)) := by
    intro d
    rw [haa]
    simp only []
    rw [show (∑ n ∈ Finset.Icc A B,
          (if n ∈ Finset.Icc a b then u n * (Real.sqrt (n:ℝ):ℂ) else 0)
            * (n:ℂ)^(Complex.I*((d:ℝ):ℂ)) / (Real.sqrt (n:ℝ):ℂ))
        = ∑ n ∈ Finset.Icc A B,
          (if n ∈ Finset.Icc a b then u n * (n:ℂ)^(Complex.I*((d:ℝ):ℂ)) else 0) from by
        refine Finset.sum_congr rfl (fun n _ => ?_)
        by_cases hn : n ∈ Finset.Icc a b
        · rw [if_pos hn, if_pos hn]
          have hs : (Real.sqrt (n:ℝ):ℂ) ≠ 0 := by
            rw [Complex.ofReal_ne_zero]
            exact ne_of_gt (Real.sqrt_pos_of_pos (by
              rw [Finset.mem_Icc] at hn; exact_mod_cast (by omega : 1 ≤ n)))
          rw [mul_assoc, mul_div_assoc, mul_div_cancel_left₀ _ hs]
        · rw [if_neg hn, if_neg hn, zero_mul, zero_div]]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
  have hRinner : ∀ d : ℝ,
      (∑ n ∈ Finset.Icc A B, (cc n : ℂ) * (n:ℂ)^(Complex.I*((d:ℝ):ℂ)) / (Real.sqrt (n:ℝ):ℂ))
        = ∑ n ∈ Finset.Icc A B, (n:ℂ)^(Complex.I*((d:ℝ):ℂ)) := by
    intro d
    rw [hcc]
    simp only []
    refine Finset.sum_congr rfl (fun n hn => ?_)
    have hn1 : 1 ≤ n := hS n hn
    have hs : (Real.sqrt (n:ℝ):ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact ne_of_gt (Real.sqrt_pos_of_pos (by exact_mod_cast hn1))
    rw [mul_div_cancel_left₀ _ hs]
  have hLHS_eq : (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ W then
          ‖∑ n ∈ Finset.Icc a b, u n * (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))‖^2 else 0))
      = ∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ W then
          ‖∑ n ∈ Finset.Icc A B, aa n * (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))
              / (Real.sqrt (n:ℝ):ℂ)‖^2 else 0) := by
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hd : |t i - t j| ≤ W
    · rw [if_pos hd, if_pos hd, hLinner (t i - t j)]
    · rw [if_neg hd, if_neg hd]
  have hSR_eq : (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ 4 * (1/4:ℝ) * W then
          ‖∑ n ∈ Finset.Icc A B, (cc n : ℂ) * (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))
              / (Real.sqrt (n:ℝ):ℂ)‖^2 else 0))
      = ∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ W then
          ‖∑ n ∈ Finset.Icc A B, (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))‖^2 else 0) := by
    have h4 : 4 * (1/4:ℝ) * W = W := by ring
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    by_cases hd : |t i - t j| ≤ 4 * (1/4:ℝ) * W
    · rw [if_pos hd, if_pos (by rwa [h4] at hd), hRinner (t i - t j)]
    · rw [if_neg hd, if_neg (by rwa [h4] at hd)]
  have hRHSnn : 0 ≤ ∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ W then
          ‖∑ n ∈ Finset.Icc A B, (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))‖^2 else 0) := by
    refine Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => ?_))
    by_cases hd : |t i - t j| ≤ W
    · rw [if_pos hd]; positivity
    · rw [if_neg hd]
  have hlog : (1:ℝ) ≤ Real.log ((B:ℝ) + 2) := by
    have h3 : (1:ℝ) < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 3)]
      exact Real.exp_one_lt_three
    have hB2 : (3:ℝ) ≤ (B:ℝ) + 2 := by
      have : (1:ℝ) ≤ (B:ℝ) := by exact_mod_cast (le_trans hA1 hAB)
      linarith
    have := Real.log_le_log (by norm_num : (0:ℝ) < 3) hB2
    linarith
  have hlogsq : (1:ℝ) ≤ (Real.log ((B:ℝ)+2))^2 := by nlinarith [hlog]
  have hfin : 4 * C₀ * (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ W then
          ‖∑ n ∈ Finset.Icc A B, (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))‖^2 else 0))
      ≤ 4 * C₀ * (Real.log ((B:ℝ)+2))^2 * (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ W then
          ‖∑ n ∈ Finset.Icc A B, (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))‖^2 else 0)) := by
    have hstep : (∑ i : Fin R, ∑ j : Fin R,
          (if |t i - t j| ≤ W then
            ‖∑ n ∈ Finset.Icc A B, (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))‖^2 else 0))
        ≤ (Real.log ((B:ℝ)+2))^2 * (∑ i : Fin R, ∑ j : Fin R,
          (if |t i - t j| ≤ W then
            ‖∑ n ∈ Finset.Icc A B, (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))‖^2 else 0)) := by
      calc (∑ i : Fin R, ∑ j : Fin R,
            (if |t i - t j| ≤ W then
              ‖∑ n ∈ Finset.Icc A B, (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))‖^2 else 0))
          = 1 * (∑ i : Fin R, ∑ j : Fin R,
            (if |t i - t j| ≤ W then
              ‖∑ n ∈ Finset.Icc A B, (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))‖^2 else 0)) := by ring
        _ ≤ (Real.log ((B:ℝ)+2))^2 * (∑ i : Fin R, ∑ j : Fin R,
            (if |t i - t j| ≤ W then
              ‖∑ n ∈ Finset.Icc A B, (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))‖^2 else 0)) :=
              mul_le_mul_of_nonneg_right hlogsq hRHSnn
    nlinarith [hstep, hC₀pos,
      mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hC₀pos.le) hRHSnn]
  have hkey2 : (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ W then
          ‖∑ n ∈ Finset.Icc A B, aa n * (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))
              / (Real.sqrt (n:ℝ):ℂ)‖^2 else 0))
      ≤ 4 * C₀ * (∑ i : Fin R, ∑ j : Fin R,
          (if |t i - t j| ≤ W then
            ‖∑ n ∈ Finset.Icc A B, (n:ℂ)^(Complex.I*((t i - t j:ℝ):ℂ))‖^2 else 0)) := by
    have h := hkey
    rw [hSR_eq] at h
    have hc : C₀ / (1/4:ℝ) = 4 * C₀ := by ring
    rw [hc] at h
    exact h
  rw [hLHS_eq]
  exact le_trans hkey2 hfin


end

end Commons.NumberTheory.DirichletPolynomial