import Mathlib
import Submission.Commons.Analysis.ExponentialSums.second_derivative_test
import Submission.Commons.NumberTheory.DirichletPolynomial.aliasing_exp_sum_small

open Complex
open scoped BigOperators ComplexConjugate

set_option autoImplicit false

namespace Commons.NumberTheory.DirichletPolynomial

noncomputable section

/-!
# Both aliasing regimes for `∑_{n=N}^{2N} n^{iδ} − ∫_N^{2N} x^{iδ} dx`

The two auxiliary lemmas `aliasing_exp_sum_small` and `aliasing_exp_sum_large`
both live in the commons, but they define auxiliary lemmas with colliding names
(`deriv_phi`, `contDiffOn_phi`), so they cannot be imported into the same module.
We therefore import `aliasing_exp_sum_small` (small-`δ` regime) and reproduce the
large-`δ` machinery verbatim inside the nested namespace `AliasLarge`, where the
names no longer collide.  The final theorem glues the two regimes with a single
constant.
-/

namespace AliasLarge

lemma cpow_I_eq_conj_exp (x : ℝ) (hx : 0 < x) (δ : ℝ) :
    (x : ℂ) ^ (Complex.I * (δ : ℂ)) =
      conj (Complex.exp
        (((2 * Real.pi * (-(δ / (2 * Real.pi)) * Real.log x) : ℝ) : ℂ) * Complex.I)) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [Complex.cpow_def_of_ne_zero hx0, ← Complex.exp_conj]
  congr 1
  rw [← Complex.ofReal_log hx.le]
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  field_simp

/-- Reindex a `ℤ`-interval sum as a `ℕ`-interval sum with the canonical cast. -/
lemma sum_Icc_int_eq_nat (f : ℤ → ℂ) (a b : ℕ) :
    (∑ m ∈ Finset.Icc (a : ℤ) (b : ℤ), f m) = ∑ n ∈ Finset.Icc a b, f (n : ℤ) := by
  refine Finset.sum_bij' (fun m _ => m.toNat) (fun n _ => (n : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    rw [Finset.mem_Icc] at hm ⊢
    obtain ⟨h1, h2⟩ := hm
    have h0 : (0 : ℤ) ≤ m := by
      have : (0 : ℤ) ≤ (a : ℤ) := by exact_mod_cast Nat.zero_le a
      linarith
    have hcast : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg h0
    constructor
    · exact_mod_cast (show (a : ℤ) ≤ (m.toNat : ℤ) by rw [hcast]; exact h1)
    · exact_mod_cast (show (m.toNat : ℤ) ≤ (b : ℤ) by rw [hcast]; exact h2)
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact_mod_cast hn
  · intro m hm
    rw [Finset.mem_Icc] at hm
    have h0 : (0 : ℤ) ≤ m := by
      have : (0 : ℤ) ≤ (a : ℤ) := by exact_mod_cast Nat.zero_le a
      linarith [hm.1]
    exact Int.toNat_of_nonneg h0
  · intro n hn
    exact Int.toNat_natCast n
  · intro m hm
    rw [Finset.mem_Icc] at hm
    have h0 : (0 : ℤ) ≤ m := by
      have : (0 : ℤ) ≤ (a : ℤ) := by exact_mod_cast Nat.zero_le a
      linarith [hm.1]
    rw [Int.toNat_of_nonneg h0]

/-! ## Bound on the integral part -/

/-- `‖∫_N^{2N} x^{iδ} dx‖ ≤ 3√δ` for `δ ≥ N ≥ 1`. -/
lemma norm_integral_cpow_le (N : ℕ) (δ : ℝ) (hN : (1 : ℝ) ≤ N) (hδ : (N : ℝ) ≤ δ) :
    ‖(∫ x in (N : ℝ)..(2 * (N : ℝ)), (x : ℂ) ^ (Complex.I * (δ : ℂ)))‖
      ≤ 3 * Real.sqrt δ := by
  have hNr : (0 : ℝ) < (N : ℝ) := by linarith
  have hδpos : (0 : ℝ) < δ := by linarith
  have hrre : (-1 : ℝ) < (Complex.I * (δ : ℂ)).re := by simp
  rw [integral_cpow (a := (N : ℝ)) (b := 2 * (N : ℝ)) (r := Complex.I * (δ : ℂ)) (Or.inl hrre)]
  have hnorm (a : ℝ) (ha : 0 < a) : ‖(a : ℂ) ^ (Complex.I * (δ : ℂ) + 1)‖ = a := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ha]
    have hre : (Complex.I * (δ : ℂ) + 1).re = 1 := by
      simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, Real.rpow_one]
  have hnum : ‖(((2 * (N : ℝ) : ℝ)) : ℂ) ^ (Complex.I * (δ : ℂ) + 1)
      - ((((N : ℝ) : ℝ)) : ℂ) ^ (Complex.I * (δ : ℂ) + 1)‖ ≤ 3 * (N : ℝ) := by
    calc ‖(((2 * (N : ℝ) : ℝ)) : ℂ) ^ (Complex.I * (δ : ℂ) + 1)
            - ((((N : ℝ) : ℝ)) : ℂ) ^ (Complex.I * (δ : ℂ) + 1)‖
        ≤ ‖(((2 * (N : ℝ) : ℝ)) : ℂ) ^ (Complex.I * (δ : ℂ) + 1)‖
            + ‖(((((N : ℝ) : ℝ)) : ℂ) ^ (Complex.I * (δ : ℂ) + 1))‖ := norm_sub_le _ _
      _ = 2 * (N : ℝ) + (N : ℝ) := by
          rw [hnorm (2 * (N : ℝ)) (by linarith), hnorm (N : ℝ) hNr]
      _ = 3 * (N : ℝ) := by ring
  have hden : δ ≤ ‖Complex.I * (δ : ℂ) + 1‖ := by
    have him : (Complex.I * (δ : ℂ) + 1).im = δ := by
      simp [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im]
    calc δ = |δ| := (abs_of_nonneg hδpos.le).symm
      _ = |(Complex.I * (δ : ℂ) + 1).im| := by rw [him]
      _ ≤ ‖Complex.I * (δ : ℂ) + 1‖ := Complex.abs_im_le_norm _
  have hstep : ‖((((2 * (N : ℝ) : ℝ)) : ℂ) ^ (Complex.I * (δ : ℂ) + 1)
        - ((((N : ℝ) : ℝ)) : ℂ) ^ (Complex.I * (δ : ℂ) + 1)) / (Complex.I * (δ : ℂ) + 1)‖
      ≤ 3 := by
    rw [norm_div]
    refine (div_le_div₀ (by positivity) hnum hδpos hden).trans ?_
    rw [div_le_iff₀ hδpos]
    linarith
  refine hstep.trans ?_
  have : (1 : ℝ) ≤ Real.sqrt δ := Real.one_le_sqrt.mpr (by linarith)
  linarith

/-! ## Derivative of the convex phase -/

lemma deriv_phi (δ : ℝ) :
    deriv (fun x : ℝ => -(δ / (2 * Real.pi)) * Real.log x)
      = fun x => -(δ / (2 * Real.pi)) * x⁻¹ := by
  rw [deriv_const_mul_field' (v := Real.log), Real.deriv_log']

lemma deriv_deriv_phi (δ : ℝ) {x : ℝ} (hx : x ≠ 0) :
    deriv (deriv (fun x : ℝ => -(δ / (2 * Real.pi)) * Real.log x)) x
      = δ / (2 * Real.pi * x ^ 2) := by
  rw [deriv_phi]
  have h2 : HasDerivAt (fun y : ℝ => -(δ / (2 * Real.pi)) * y⁻¹)
      (-(δ / (2 * Real.pi)) * (-(x ^ 2)⁻¹)) x :=
    (hasDerivAt_inv hx).const_mul _
  rw [h2.deriv]
  field_simp

lemma contDiffOn_phi (δ : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    ContDiffOn ℝ 2 (fun x : ℝ => -(δ / (2 * Real.pi)) * Real.log x)
      (Set.Icc ((N : ℤ) : ℝ) (((N : ℤ) : ℝ) + (N : ℝ))) := by
  have hsub : Set.Icc ((N : ℤ) : ℝ) (((N : ℤ) : ℝ) + (N : ℝ)) ⊆ {0}ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have h1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hcast : ((N : ℤ) : ℝ) = (N : ℝ) := by push_cast; ring
    have hxN : ((N : ℤ) : ℝ) ≤ x := hx.1
    rw [hcast] at hxN
    exact (by linarith : (0 : ℝ) < x).ne'
  exact contDiffOn_const.mul (Real.contDiffOn_log.mono hsub)

/-- Second-derivative control for the convex phase `φ(x) = -(δ/2π) log x` on `(N, 2N)`,
with `r = δ/(8πN²)` and `B = 4`. -/
lemma sdt_pp (δ : ℝ) (N : ℕ) (hN : 1 ≤ N) (hδ : (N : ℝ) ≤ δ) :
    ∀ x ∈ Set.Ioo ((N : ℤ) : ℝ) (((N : ℤ) : ℝ) + (N : ℝ)),
      δ / (8 * Real.pi * (N : ℝ) ^ 2)
        ≤ deriv (deriv (fun x : ℝ => -(δ / (2 * Real.pi)) * Real.log x)) x ∧
      deriv (deriv (fun x : ℝ => -(δ / (2 * Real.pi)) * Real.log x)) x
        ≤ 4 * (δ / (8 * Real.pi * (N : ℝ) ^ 2)) := by
  intro x hx
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hcast : ((N : ℤ) : ℝ) = (N : ℝ) := by push_cast; ring
  have hx1 : (N : ℝ) < x := by have h := hx.1; rw [hcast] at h; exact h
  have hx2 : x < 2 * (N : ℝ) := by
    have h := hx.2
    rw [hcast] at h
    have : (N : ℝ) + (N : ℝ) = 2 * (N : ℝ) := by ring
    linarith [h, this]
  have hxpos : (0 : ℝ) < x := by linarith
  rw [deriv_deriv_phi δ (ne_of_gt hxpos)]
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  constructor
  · have hd : (0 : ℝ) < 2 * Real.pi * x ^ 2 := by positivity
    have hdb : 2 * Real.pi * x ^ 2 ≤ 8 * Real.pi * (N : ℝ) ^ 2 := by
      have hx2' : x ^ 2 ≤ (2 * (N : ℝ)) ^ 2 := by
        exact pow_le_pow_left₀ hxpos.le hx2.le 2
      nlinarith [hx2', hpi]
    have hdelta : (0 : ℝ) ≤ δ := by linarith
    exact div_le_div₀ hdelta le_rfl hd hdb
  · rw [show 4 * (δ / (8 * Real.pi * (N : ℝ) ^ 2)) = δ / (2 * Real.pi * (N : ℝ) ^ 2) by
      field_simp; ring]
    have hd : (0 : ℝ) < 2 * Real.pi * (N : ℝ) ^ 2 := by positivity
    have hdb : 2 * Real.pi * (N : ℝ) ^ 2 ≤ 2 * Real.pi * x ^ 2 := by
      have hx1' : (N : ℝ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hNpos.le hx1.le 2
      nlinarith [hx1', hpi]
    have hdelta : (0 : ℝ) ≤ δ := by linarith
    exact div_le_div₀ hdelta le_rfl hd hdb

lemma le_of_sq_le_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  have := (sq_le_sq.mp h)
  rwa [abs_of_nonneg ha, abs_of_nonneg hb] at this

/-! ## Bound on the sum part -/

/-- If `C0` satisfies the second-derivative test with `B = 4`, then for `δ ≥ N ≥ 1`,
`‖∑_{n=N}^{2N} n^{iδ}‖ ≤ (1 + 11 C0) √δ`. -/
lemma norm_sum_cpow_le (C0 : ℝ) (hC0 : 0 ≤ C0)
    (hsdt : ∀ {a : ℤ} {M : ℕ}, 1 ≤ M → ∀ (f : ℝ → ℝ) {r : ℝ}, 0 < r →
      ContDiffOn ℝ 2 f (Set.Icc ((a : ℤ) : ℝ) (((a : ℤ) : ℝ) + (M : ℝ))) →
      (∀ x ∈ Set.Ioo ((a : ℤ) : ℝ) (((a : ℤ) : ℝ) + (M : ℝ)),
          r ≤ deriv (deriv f) x ∧ deriv (deriv f) x ≤ 4 * r) →
      ‖∑ n ∈ Finset.Icc (a + 1) (a + (M : ℤ)),
          Complex.exp (((2 * Real.pi * f (n : ℝ) : ℝ) : ℂ) * Complex.I)‖
        ≤ C0 * ((M : ℝ) * Real.sqrt r + 1 / Real.sqrt r))
    (N : ℕ) (hN : 1 ≤ N) (δ : ℝ) (hδ : (N : ℝ) ≤ δ) :
    ‖∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ (Complex.I * (δ : ℂ))‖
      ≤ (1 + 11 * C0) * Real.sqrt δ := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hδpos : (0 : ℝ) < δ := by linarith
  set rr : ℝ := δ / (8 * Real.pi * (N : ℝ) ^ 2) with hrr
  have hrpos : 0 < rr := by rw [hrr]; positivity
  have hcd : ContDiffOn ℝ 2 (fun x : ℝ => -(δ / (2 * Real.pi)) * Real.log x)
      (Set.Icc ((N : ℤ) : ℝ) (((N : ℤ) : ℝ) + (N : ℝ))) := contDiffOn_phi δ N hN
  have hpp := sdt_pp δ N hN hδ
  have hs := hsdt (a := (N : ℤ)) (M := N) hN (fun x : ℝ => -(δ / (2 * Real.pi)) * Real.log x)
    hrpos hcd hpp
  -- Key identity: target sum = conj of the ℤ-indexed exponential sum.
  have hkey : (∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ (Complex.I * (δ : ℂ)))
      = conj (∑ m ∈ Finset.Icc (N : ℤ) (2 * (N : ℤ)),
          Complex.exp (((2 * Real.pi * (-(δ / (2 * Real.pi)) * Real.log (m : ℝ)) : ℝ) : ℂ)
            * Complex.I)) := by
    rw [map_sum]
    have h2N : (2 * (N : ℤ) : ℤ) = ((2 * N : ℕ) : ℤ) := by push_cast; ring
    rw [h2N]
    rw [sum_Icc_int_eq_nat
      (fun m : ℤ => conj (Complex.exp
        (((2 * Real.pi * (-(δ / (2 * Real.pi)) * Real.log (m : ℝ)) : ℝ) : ℂ) * Complex.I)))
      N (2 * N)]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℕ) ≤ n := by omega
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    rw [show ((n : ℤ) : ℝ) = (n : ℝ) from Int.cast_natCast n]
    have h := cpow_I_eq_conj_exp (n : ℝ) hnpos δ
    simpa using h
  -- Split the ℤ-sum into the `m = N` term plus the tail.
  have hsplit : (∑ m ∈ Finset.Icc (N : ℤ) (2 * (N : ℤ)),
        Complex.exp (((2 * Real.pi * (-(δ / (2 * Real.pi)) * Real.log (m : ℝ)) : ℝ) : ℂ)
          * Complex.I))
      = Complex.exp (((2 * Real.pi * (-(δ / (2 * Real.pi)) * Real.log (N : ℝ)) : ℝ) : ℂ)
          * Complex.I)
        + ∑ m ∈ Finset.Icc ((N : ℤ) + 1) (2 * (N : ℤ)),
            Complex.exp (((2 * Real.pi * (-(δ / (2 * Real.pi)) * Real.log (m : ℝ)) : ℝ) : ℂ)
              * Complex.I) := by
    have hNm : (N : ℤ) ∉ Finset.Icc ((N : ℤ) + 1) (2 * (N : ℤ)) := by
      simp only [Finset.mem_Icc, not_and, not_le]
      intro h
      omega
    have hins : Finset.Icc (N : ℤ) (2 * (N : ℤ))
        = insert (N : ℤ) (Finset.Icc ((N : ℤ) + 1) (2 * (N : ℤ))) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        rcases eq_or_lt_of_le h1 with h | h
        · exact Or.inl h.symm
        · exact Or.inr ⟨h, h2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨le_rfl, by omega⟩
        · exact ⟨by omega, h2⟩
    rw [hins, Finset.sum_insert hNm]
    simp only [Int.cast_natCast]
  -- Align `2*(N:ℤ)` with `(N:ℤ) + (N:ℤ)` for `hs`.
  have htail : (∑ m ∈ Finset.Icc ((N : ℤ) + 1) (2 * (N : ℤ)),
        Complex.exp (((2 * Real.pi * (-(δ / (2 * Real.pi)) * Real.log (m : ℝ)) : ℝ) : ℂ)
          * Complex.I))
      = ∑ m ∈ Finset.Icc ((N : ℤ) + 1) ((N : ℤ) + (N : ℤ)),
        Complex.exp (((2 * Real.pi * (-(δ / (2 * Real.pi)) * Real.log (m : ℝ)) : ℝ) : ℂ)
          * Complex.I) := by
    congr 1
    ring
  have hGN : ‖Complex.exp (((2 * Real.pi * (-(δ / (2 * Real.pi)) * Real.log (N : ℝ)) : ℝ) : ℂ)
      * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp_ofReal_mul_I]
  -- Numerical bound: N√rr + 1/√rr ≤ 11√δ.
  have hnum1 : (N : ℝ) * Real.sqrt rr ≤ Real.sqrt δ := by
    apply le_of_sq_le_sq (by positivity) (Real.sqrt_nonneg _)
    rw [mul_pow, Real.sq_sqrt hrpos.le]
    have hsq : (N : ℝ) ^ 2 * rr = δ / (8 * Real.pi) := by
      rw [hrr]; field_simp
    rw [hsq, Real.sq_sqrt hδpos.le]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [Real.pi_gt_three, hδpos]
  have hnum2 : 1 / Real.sqrt rr ≤ 10 * Real.sqrt δ := by
    apply le_of_sq_le_sq (by positivity) (by positivity)
    rw [one_div, inv_pow, Real.sq_sqrt hrpos.le]
    have hsq : rr⁻¹ = 8 * Real.pi * (N : ℝ) ^ 2 / δ := by
      rw [hrr]; field_simp
    rw [hsq, mul_pow, Real.sq_sqrt hδpos.le]
    rw [div_le_iff₀ hδpos]
    have hNsq : (N : ℝ) ^ 2 ≤ δ ^ 2 := by
      have := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (N : ℝ)) hδ 2
      simpa using this
    nlinarith [Real.pi_lt_four, hNsq, hNpos, hδpos]
  calc ‖∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ (Complex.I * (δ : ℂ))‖
      = ‖∑ m ∈ Finset.Icc (N : ℤ) (2 * (N : ℤ)),
          Complex.exp (((2 * Real.pi * (-(δ / (2 * Real.pi)) * Real.log (m : ℝ)) : ℝ) : ℂ)
            * Complex.I)‖ := by rw [hkey, norm_conj]
    _ = ‖Complex.exp (((2 * Real.pi * (-(δ / (2 * Real.pi)) * Real.log (N : ℝ)) : ℝ) : ℂ) * Complex.I)
          + ∑ m ∈ Finset.Icc ((N : ℤ) + 1) (2 * (N : ℤ)),
              Complex.exp (((2 * Real.pi * (-(δ / (2 * Real.pi)) * Real.log (m : ℝ)) : ℝ) : ℂ)
                * Complex.I)‖ := by rw [hsplit]
    _ ≤ ‖Complex.exp (((2 * Real.pi * (-(δ / (2 * Real.pi)) * Real.log (N : ℝ)) : ℝ) : ℂ) * Complex.I)‖
          + ‖∑ m ∈ Finset.Icc ((N : ℤ) + 1) (2 * (N : ℤ)),
              Complex.exp (((2 * Real.pi * (-(δ / (2 * Real.pi)) * Real.log (m : ℝ)) : ℝ) : ℂ)
                * Complex.I)‖ := norm_add_le _ _
    _ = 1 + ‖∑ m ∈ Finset.Icc ((N : ℤ) + 1) (2 * (N : ℤ)),
              Complex.exp (((2 * Real.pi * (-(δ / (2 * Real.pi)) * Real.log (m : ℝ)) : ℝ) : ℂ)
                * Complex.I)‖ := by rw [hGN]
    _ ≤ 1 + C0 * ((N : ℝ) * Real.sqrt rr + 1 / Real.sqrt rr) := by
        rw [htail]
        linarith [hs]
    _ ≤ (1 + 11 * C0) * Real.sqrt δ := by
        have : (N : ℝ) * Real.sqrt rr + 1 / Real.sqrt rr ≤ 11 * Real.sqrt δ := by
          linarith [hnum1, hnum2]
        have hsqrt1 : (1 : ℝ) ≤ Real.sqrt δ := Real.one_le_sqrt.mpr (by linarith)
        nlinarith [hC0, hsqrt1]

/-! ## Main theorem -/

theorem aliasing_exp_sum_large :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ δ : ℝ, (N : ℝ) ≤ δ →
      ‖(∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ (Complex.I * (δ : ℂ))) -
        (∫ x in (N : ℝ)..(2 * (N : ℝ)), (x : ℂ) ^ (Complex.I * (δ : ℂ)))‖ ≤
      C * Real.sqrt δ := by
  obtain ⟨C0, hC0pos, hsdt⟩ :=
    Commons.Analysis.ExponentialSums.second_derivative_test (B := 4) (by norm_num)
  refine ⟨4 + 11 * C0, by linarith, ?_⟩
  intro N hN δ hδ
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  calc ‖(∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ (Complex.I * (δ : ℂ))) -
        (∫ x in (N : ℝ)..(2 * (N : ℝ)), (x : ℂ) ^ (Complex.I * (δ : ℂ)))‖
      ≤ ‖∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ (Complex.I * (δ : ℂ))‖
          + ‖(∫ x in (N : ℝ)..(2 * (N : ℝ)), (x : ℂ) ^ (Complex.I * (δ : ℂ)))‖ := norm_sub_le _ _
    _ ≤ (1 + 11 * C0) * Real.sqrt δ + 3 * Real.sqrt δ :=
        add_le_add (norm_sum_cpow_le C0 hC0pos.le hsdt N hN δ hδ)
          (norm_integral_cpow_le N δ hN1 hδ)
    _ = (4 + 11 * C0) * Real.sqrt δ := by ring


end AliasLarge

/-- Both aliasing regimes for `∑_{n=N}^{2N} n^{iδ} − ∫_N^{2N} x^{iδ} dx` at once:
the small-`δ` regime (`|δ| ≤ N`, bound `C(1 + |δ|/N)`) and the large-`δ`
regime (`δ ≥ N`, bound `C√δ`), with a single constant, obtained by combining
`aliasing_exp_sum_small` and `AliasLarge.aliasing_exp_sum_large`. -/
theorem aliasing_exp_sum_both :
    ∃ C : ℝ, 0 < C ∧
      (∀ (N : ℕ), 1 ≤ N → ∀ δ : ℝ, |δ| ≤ (N : ℝ) →
        ‖(∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ (Complex.I * (δ : ℂ))) -
          (∫ x in (N : ℝ)..(2 * (N : ℝ)), (x : ℂ) ^ (Complex.I * (δ : ℂ)))‖
            ≤ C * (1 + |δ| / (N : ℝ))) ∧
      (∀ (N : ℕ), 1 ≤ N → ∀ δ : ℝ, (N : ℝ) ≤ δ →
        ‖(∑ n ∈ Finset.Icc N (2 * N), (n : ℂ) ^ (Complex.I * (δ : ℂ))) -
          (∫ x in (N : ℝ)..(2 * (N : ℝ)), (x : ℂ) ^ (Complex.I * (δ : ℂ)))‖
            ≤ C * Real.sqrt δ) := by
  obtain ⟨C₁, hC₁, hsmall⟩ := aliasing_exp_sum_small
  obtain ⟨C₂, hC₂, hlarge⟩ := AliasLarge.aliasing_exp_sum_large
  refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁ (le_max_left C₁ C₂), ?_, ?_⟩
  · intro N hN δ hδ
    refine le_trans (hsmall N hN δ hδ) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (by positivity)
  · intro N hN δ hδ
    refine le_trans (hlarge N hN δ hδ) ?_
    exact mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (Real.sqrt_nonneg δ)

end

end Commons.NumberTheory.DirichletPolynomial
