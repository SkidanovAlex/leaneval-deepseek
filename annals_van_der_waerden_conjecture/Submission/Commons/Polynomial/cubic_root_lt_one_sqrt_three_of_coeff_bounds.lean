import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.IntervalCases

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

open Polynomial

namespace Commons.Polynomial

lemma cubic_root_lt_one_sqrt_three_aeval_cubic_eq {a b c : ℤ} {w : ℂ}
    (h : Polynomial.aeval w (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)) = 0) :
    w ^ 3 + (a : ℂ) * w ^ 2 + (b : ℂ) * w + (c : ℂ) = 0 := by
  rw [Polynomial.aeval_def] at h
  norm_num [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C] at h
  rw [← Polynomial.C_eq_intCast (n := a), ← Polynomial.C_eq_intCast (n := b), ← Polynomial.C_eq_intCast (n := c)] at h
  rw [Polynomial.eval₂_C, Polynomial.eval₂_C, Polynomial.eval₂_C] at h
  norm_num at h
  simpa using h

lemma cubic_root_lt_one_sqrt_three_real_im_zero_abs_lt_one {r : ℂ} (hre : r.im = 0) (hn : ‖r‖ < 1) :
    |r.re| < 1 := by
  have h := hn
  rw [Complex.norm_def] at h
  simp [Complex.normSq_apply, hre] at h
  rw [← pow_two] at h
  rw [Real.sqrt_sq_eq_abs] at h
  simpa using h

lemma cubic_root_lt_one_sqrt_three_complex_root_normSq_lt_three {z : ℂ} (hn : ‖z‖ < Real.sqrt 3) :
    z.re ^ 2 + z.im ^ 2 < 3 := by
  have hsq : ‖z‖ ^ 2 < (Real.sqrt 3) ^ 2 := (sq_lt_sq₀ (norm_nonneg z) (Real.sqrt_nonneg 3)).2 hn
  have h3 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  rw [← Complex.normSq_eq_norm_sq] at hsq
  rw [Complex.normSq_apply] at hsq
  rw [h3] at hsq
  simpa [pow_two] using hsq

lemma cubic_root_lt_one_sqrt_three_cubic_eval_re {a b c : ℤ} (u v : ℝ) :
    (((u + v * Complex.I : ℂ) ^ 3 + (a : ℂ) * (u + v * Complex.I : ℂ) ^ 2 +
        (b : ℂ) * (u + v * Complex.I : ℂ) + (c : ℂ)).re =
      u ^ 3 - 3 * u * v ^ 2 + (a : ℝ) * (u ^ 2 - v ^ 2) + (b : ℝ) * u + (c : ℝ)) := by
  ring_nf
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, ← Complex.ofReal_pow, Complex.I_sq]
  norm_num
  simp only [← Complex.ofReal_pow, Complex.ofReal_im, Complex.ofReal_re]
  ring_nf

lemma cubic_root_lt_one_sqrt_three_cubic_eval_im {a b c : ℤ} (u v : ℝ) :
    (((u + v * Complex.I : ℂ) ^ 3 + (a : ℂ) * (u + v * Complex.I : ℂ) ^ 2 +
        (b : ℂ) * (u + v * Complex.I : ℂ) + (c : ℂ)).im =
      v * (3 * u ^ 2 - v ^ 2 + 2 * (a : ℝ) * u + (b : ℝ))) := by
  ring_nf
  simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, ← Complex.ofReal_pow, Complex.I_sq]
  norm_num
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  ring_nf

lemma cubic_root_lt_one_sqrt_three_cubic_monic {a b c : ℤ} :
    (Polynomial.X ^ 3 + Polynomial.C (a : ℂ) * Polynomial.X ^ 2 +
      Polynomial.C (b : ℂ) * Polynomial.X + Polynomial.C (c : ℂ)).Monic := by
  rw [show Polynomial.X ^ 3 + Polynomial.C (a : ℂ) * Polynomial.X ^ 2 +
      Polynomial.C (b : ℂ) * Polynomial.X + Polynomial.C (c : ℂ) =
      Polynomial.X ^ 3 + (Polynomial.C (a : ℂ) * Polynomial.X ^ 2 +
      Polynomial.C (b : ℂ) * Polynomial.X + Polynomial.C (c : ℂ)) by ring]
  apply Polynomial.monic_X_pow_add
  compute_degree!

lemma cubic_root_lt_one_sqrt_three_cubic_natDegree {a b c : ℤ} :
    (Polynomial.X ^ 3 + Polynomial.C (a : ℂ) * Polynomial.X ^ 2 +
      Polynomial.C (b : ℂ) * Polynomial.X + Polynomial.C (c : ℂ)).natDegree = 3 := by
  compute_degree!

lemma cubic_root_lt_one_sqrt_three_cubic_ne_zero {a b c : ℤ} :
    (Polynomial.X ^ 3 + Polynomial.C (a : ℂ) * Polynomial.X ^ 2 +
      Polynomial.C (b : ℂ) * Polynomial.X + Polynomial.C (c : ℂ)) ≠ 0 := by
  intro h
  have hd := congrArg Polynomial.natDegree h
  rw [cubic_root_lt_one_sqrt_three_cubic_natDegree] at hd
  norm_num at hd

lemma cubic_root_lt_one_sqrt_three_cubic_coeff_two {a b c : ℤ} :
    (Polynomial.X ^ 3 + Polynomial.C (a : ℂ) * Polynomial.X ^ 2 +
      Polynomial.C (b : ℂ) * Polynomial.X + Polynomial.C (c : ℂ)).coeff 2 = (a : ℂ) := by
  have hb1 : ((b : Polynomial ℂ).coeff 1) = 0 := by
    change (Polynomial.C (b : ℂ)).coeff 1 = 0
    rw [Polynomial.coeff_C]
    norm_num
  have hc2 : ((c : Polynomial ℂ).coeff 2) = 0 := by
    change (Polynomial.C (c : ℂ)).coeff 2 = 0
    rw [Polynomial.coeff_C]
    norm_num
  norm_num [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_X_pow, hb1, hc2]

lemma cubic_root_lt_one_sqrt_three_cubic_coeff_one {a b c : ℤ} :
    (Polynomial.X ^ 3 + Polynomial.C (a : ℂ) * Polynomial.X ^ 2 +
      Polynomial.C (b : ℂ) * Polynomial.X + Polynomial.C (c : ℂ)).coeff 1 = (b : ℂ) := by
  have hc1 : ((c : Polynomial ℂ).coeff 1) = 0 := by
    change (Polynomial.C (c : ℂ)).coeff 1 = 0
    rw [Polynomial.coeff_C]
    norm_num
  norm_num [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_X_pow, hc1]

lemma cubic_root_lt_one_sqrt_three_cubic_coeff_zero {a b c : ℤ} :
    (Polynomial.X ^ 3 + Polynomial.C (a : ℂ) * Polynomial.X ^ 2 +
      Polynomial.C (b : ℂ) * Polynomial.X + Polynomial.C (c : ℂ)).coeff 0 = (c : ℂ) := by
  norm_num [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
    Polynomial.coeff_X_pow]

lemma cubic_root_lt_one_sqrt_three_triple_coeff_two (r z : ℂ) :
    (((X - C r) * (X - C (star z)) * (X - C z) : Polynomial ℂ).coeff 2) = -(r + star z + z) := by
  rw [Polynomial.coeff_mul_X_sub_C (p := (X - C r) * (X - C (star z))) (r := z) (a := 1)]
  have hq1 : ((X - C r) * (X - C (star z)) : Polynomial ℂ).coeff 1 = -(star z) - r := by
    rw [Polynomial.coeff_X_sub_C_mul (p := X - C (star z)) (r := r) (a := 0)]
    simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
  have hq2 : ((X - C r) * (X - C (star z)) : Polynomial ℂ).coeff 2 = 1 := by
    rw [Polynomial.coeff_X_sub_C_mul (p := X - C (star z)) (r := r) (a := 1)]
    simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
  rw [hq1, hq2]
  ring

lemma cubic_root_lt_one_sqrt_three_triple_coeff_one (r z : ℂ) :
    (((X - C r) * (X - C (star z)) * (X - C z) : Polynomial ℂ).coeff 1) =
      r * star z + r * z + star z * z := by
  rw [Polynomial.coeff_mul_X_sub_C (p := (X - C r) * (X - C (star z))) (r := z) (a := 0)]
  have hq0 : ((X - C r) * (X - C (star z)) : Polynomial ℂ).coeff 0 = r * star z := by
    simp [Polynomial.coeff_mul, Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
  have hq1 : ((X - C r) * (X - C (star z)) : Polynomial ℂ).coeff 1 = -(star z) - r := by
    rw [Polynomial.coeff_X_sub_C_mul (p := X - C (star z)) (r := r) (a := 0)]
    simp [Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]
  rw [hq0, hq1]
  ring

lemma cubic_root_lt_one_sqrt_three_triple_coeff_zero (r z : ℂ) :
    (((X - C r) * (X - C (star z)) * (X - C z) : Polynomial ℂ).coeff 0) =
      - (r * star z * z) := by
  simp [Polynomial.coeff_mul, Polynomial.coeff_sub, Polynomial.coeff_X, Polynomial.coeff_C]

lemma cubic_root_lt_one_sqrt_three_roots_prod_three {r z : ℂ} (hr_im : r.im = 0) (hz_im : z.im ≠ 0) :
    ((({r, star z, z} : Finset ℂ).val.map (fun x => X - C x)).prod) =
      (X - C r) * (X - C (star z)) * (X - C z) := by
  have hz_ne_conj : z ≠ star z := by
    intro h
    have hh := congrArg Complex.im h
    simp at hh
    have hz0 : z.im = 0 := by linarith
    exact hz_im hz0
  have hr_ne_z : r ≠ z := by
    intro h
    have hh := congrArg Complex.im h
    simp [hr_im] at hh
    exact hz_im hh.symm
  have hr_ne_conj : r ≠ star z := by
    intro h
    have hh := congrArg Complex.im h
    simp [hr_im] at hh
    exact hz_im hh
  rw [Finset.insert_val, Finset.insert_val]
  rw [Multiset.ndinsert_of_notMem, Multiset.ndinsert_of_notMem]
  · simp [Multiset.map_cons, Multiset.prod_cons]
    ring
  · simpa [Multiset.mem_singleton, eq_comm] using hz_ne_conj
  · simpa [Multiset.mem_cons, Multiset.mem_singleton] using ⟨hr_ne_conj, hr_ne_z⟩

lemma cubic_root_lt_one_sqrt_three_card_three {r z : ℂ} (hr_im : r.im = 0) (hz_im : z.im ≠ 0) :
    ({r, star z, z} : Finset ℂ).card = 3 := by
  have hz_ne_conj : z ≠ star z := by
    intro h
    have hh := congrArg Complex.im h
    simp at hh
    have hz0 : z.im = 0 := by linarith
    exact hz_im hz0
  have hr_ne_z : r ≠ z := by
    intro h
    have hh := congrArg Complex.im h
    simp [hr_im] at hh
    exact hz_im hh.symm
  have hr_ne_conj : r ≠ star z := by
    intro h
    have hh := congrArg Complex.im h
    simp [hr_im] at hh
    exact hz_im hh
  refine Finset.card_eq_three.2 ⟨r, star z, z, hr_ne_conj, hr_ne_z, hz_ne_conj.symm, ?_⟩
  rfl

lemma cubic_root_lt_one_sqrt_three_roots_vieta_complex {a b c : ℤ} {r z : ℂ}
    (hr : r ^ 3 + (a : ℂ) * r ^ 2 + (b : ℂ) * r + (c : ℂ) = 0)
    (hz : z ^ 3 + (a : ℂ) * z ^ 2 + (b : ℂ) * z + (c : ℂ) = 0)
    (hr_im : r.im = 0) (hz_im : z.im ≠ 0) :
    r + z + star z = -(a : ℂ) ∧
    r * star z + r * z + star z * z = (b : ℂ) ∧
    r * star z * z = -(c : ℂ) := by
  let P : Polynomial ℂ := Polynomial.X ^ 3 + Polynomial.C (a : ℂ) * Polynomial.X ^ 2 +
      Polynomial.C (b : ℂ) * Polynomial.X + Polynomial.C (c : ℂ)
  have hPnat : P.natDegree = 3 := by
    simpa [P] using cubic_root_lt_one_sqrt_three_cubic_natDegree
  have hrP : P.eval r = 0 := by simpa [P] using hr
  have hzP : P.eval z = 0 := by simpa [P] using hz
  have hzstarP : P.eval (star z) = 0 := by
    have hstar : star (P.eval z) = P.eval (star z) := by
      simp [P]
    rw [← hstar, hzP]
    simp
  have hdistinct := cubic_root_lt_one_sqrt_three_card_three (r := r) (z := z) hr_im hz_im
  have hroots : P.roots = ({r, star z, z} : Finset ℂ).val := by
    apply Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl
      · exact hrP
      · exact hzstarP
      · exact hzP
    · have hcard : P.natDegree ≤ ({r, star z, z} : Finset ℂ).card := by
        rw [hPnat, hdistinct]
      exact hcard
    · exact cubic_root_lt_one_sqrt_three_cubic_ne_zero
  have hsplit : P.Splits := by
    rw [Polynomial.splits_iff_card_roots]
    rw [hroots]
    rw [Finset.card_val, hdistinct, hPnat]
  have hprod : P = (P.roots.map (fun x => X - C x)).prod :=
    hsplit.eq_prod_roots_of_monic (by simpa [P] using cubic_root_lt_one_sqrt_three_cubic_monic)
  have hprod3 : (P.roots.map (fun x => X - C x)).prod = (X - C r) * (X - C (star z)) * (X - C z) := by
    rw [hroots]
    exact cubic_root_lt_one_sqrt_three_roots_prod_three hr_im hz_im
  have hcoeff2 := congrArg (fun p : Polynomial ℂ => p.coeff 2) hprod
  rw [hprod3] at hcoeff2
  rw [cubic_root_lt_one_sqrt_three_cubic_coeff_two, cubic_root_lt_one_sqrt_three_triple_coeff_two] at hcoeff2
  have hsum : r + z + star z = -(a : ℂ) := by
    rw [hcoeff2]
    ring
  have hcoeff1 := congrArg (fun p : Polynomial ℂ => p.coeff 1) hprod
  rw [hprod3] at hcoeff1
  rw [cubic_root_lt_one_sqrt_three_cubic_coeff_one, cubic_root_lt_one_sqrt_three_triple_coeff_one] at hcoeff1
  have hpair : r * star z + r * z + star z * z = (b : ℂ) := hcoeff1.symm
  have hcoeff0 := congrArg (fun p : Polynomial ℂ => p.coeff 0) hprod
  rw [hprod3] at hcoeff0
  rw [cubic_root_lt_one_sqrt_three_cubic_coeff_zero, cubic_root_lt_one_sqrt_three_triple_coeff_zero] at hcoeff0
  have hprodroots : r * star z * z = -(c : ℂ) := by
    rw [hcoeff0]
    ring
  exact ⟨hsum, hpair, hprodroots⟩

lemma cubic_root_lt_one_sqrt_three_vieta_complex_to_real {a b c : ℤ} {r z : ℂ}
    (hr_im : r.im = 0)
    (hsum : r + z + star z = -(a : ℂ))
    (hpair : r * star z + r * z + star z * z = (b : ℂ))
    (hprod : r * star z * z = -(c : ℂ)) :
    r.re + 2 * z.re = -(a : ℝ) ∧
    (b : ℝ) = 2 * r.re * z.re + (z.re ^ 2 + z.im ^ 2) ∧
    (c : ℝ) = - r.re * (z.re ^ 2 + z.im ^ 2) := by
  have hr_eq : r = (r.re : ℂ) := by
    apply Complex.ext <;> simp [hr_im]
  have hz_sum : z + star z = (2 * z.re : ℂ) := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, ← Complex.ofReal_pow] <;> ring
  have hz_mul : star z * z = (z.re ^ 2 + z.im ^ 2 : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im, ← Complex.ofReal_pow] <;> ring
  have hsum_real : r.re + 2 * z.re = -(a : ℝ) := by
    have hsum' : (r.re : ℂ) + (z + star z) = -(a : ℂ) := by
      rw [← hr_eq]
      simpa [add_assoc] using hsum
    rw [hz_sum] at hsum'
    have hsumr := congrArg Complex.re hsum'
    norm_num [Complex.ofReal_re, Complex.add_re, ← Complex.ofReal_pow] at hsumr
    linarith
  have hb_real : (b : ℝ) = 2 * r.re * z.re + (z.re ^ 2 + z.im ^ 2) := by
    have hpair' : (r.re : ℂ) * (2 * z.re : ℂ) + (z.re ^ 2 + z.im ^ 2 : ℂ) = (b : ℂ) := by
      rw [← hr_eq, ← hz_sum, ← hz_mul]
      ring_nf
      simpa [add_comm, add_left_comm, mul_comm] using hpair
    have hpairr := congrArg Complex.re hpair'
    norm_num [Complex.ofReal_re, Complex.add_re, Complex.mul_re, ← Complex.ofReal_pow] at hpairr
    ring_nf at hpairr ⊢
    exact hpairr.symm
  have hc_real : (c : ℝ) = - r.re * (z.re ^ 2 + z.im ^ 2) := by
    have hprod' : (r.re : ℂ) * (z.re ^ 2 + z.im ^ 2 : ℂ) = -(c : ℂ) := by
      rw [← hr_eq, ← hz_mul]
      simpa [mul_assoc] using hprod
    have hprodr := congrArg Complex.re hprod'
    norm_num [Complex.ofReal_re, Complex.add_re, Complex.mul_re, ← Complex.ofReal_pow] at hprodr
    linarith
  exact ⟨hsum_real, hb_real, hc_real⟩

lemma cubic_root_lt_one_sqrt_three_core {a b c : ℤ} {x u v : ℝ}
    (ha : |a| ≤ 4) (hbnd : |b| ≤ 6)
    (hc : c = -2 ∨ c = -1 ∨ c = 1 ∨ c = 2)
    (hx1 : -1 < x) (hx2 : x < 1)
    (hs : u ^ 2 + v ^ 2 < 3) (hv : v ≠ 0)
    (hsum : x + 2 * u = -(a : ℝ))
    (hb : (b : ℝ) = 2 * x * u + (u ^ 2 + v ^ 2))
    (hcprod : (c : ℝ) = -x * (u ^ 2 + v ^ 2)) :
    (a, b, c) ∈ [(-2,0,2), (-2,1,1), (-2,1,2), (-2,2,1), (-2,3,-1), (-1,0,1), (-1,1,1), (-1,1,2), (-1,2,-1), (-1,2,1), (-1,3,-2), (-1,3,-1), (0,1,-1), (0,1,1), (0,2,-2), (0,2,-1), (0,2,1), (0,2,2), (1,0,-1), (1,1,-2), (1,1,-1), (1,2,-1), (1,2,1), (1,3,1), (1,3,2), (2,0,-2), (2,1,-2), (2,1,-1), (2,2,-1), (2,3,1)] := by
  have hvp : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  have hspos : 0 < u ^ 2 + v ^ 2 := by nlinarith [sq_pos_of_ne_zero hv, sq_nonneg u]
  rcases hc with rfl | rfl | rfl | rfl
  all_goals
    have h1 : -4 ≤ a := (abs_le.mp ha).1
    have h2 : a ≤ 4 := (abs_le.mp ha).2
    interval_cases a using h1, h2
    all_goals
      have h3 : -6 ≤ b := (abs_le.mp hbnd).1
      have h4 : b ≤ 6 := (abs_le.mp hbnd).2
      interval_cases b using h3, h4
  all_goals
    norm_num at hsum hb hcprod
    first | decide | nlinarith [sq_nonneg x, sq_nonneg u, sq_nonneg v, hvp, hs]

theorem cubic_root_lt_one_sqrt_three_of_coeff_bounds {a b c : ℤ}
    (ha : |a| ≤ 4) (hb : |b| ≤ 6)
    (hc : c = -2 ∨ c = -1 ∨ c = 1 ∨ c = 2)
    (hroot : ∃ r z : ℂ, r.im = 0 ∧ z.im ≠ 0 ∧
      Polynomial.aeval (r : ℂ) (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)) = 0 ∧
      Polynomial.aeval (z : ℂ) (Polynomial.X ^ 3 + Polynomial.C (a : ℚ) * Polynomial.X ^ 2 +
        Polynomial.C (b : ℚ) * Polynomial.X + Polynomial.C (c : ℚ)) = 0 ∧
      ‖r‖ < 1 ∧ ‖z‖ < Real.sqrt 3) :
    (a, b, c) ∈ [(-2,0,2), (-2,1,1), (-2,1,2), (-2,2,1), (-2,3,-1), (-1,0,1), (-1,1,1), (-1,1,2), (-1,2,-1), (-1,2,1), (-1,3,-2), (-1,3,-1), (0,1,-1), (0,1,1), (0,2,-2), (0,2,-1), (0,2,1), (0,2,2), (1,0,-1), (1,1,-2), (1,1,-1), (1,2,-1), (1,2,1), (1,3,1), (1,3,2), (2,0,-2), (2,1,-2), (2,1,-1), (2,2,-1), (2,3,1)] := by
  rcases hroot with ⟨r, z, hr_im, hz_im, hr_eval, hz_eval, hr_norm, hz_norm⟩
  have hr_eval_c : r ^ 3 + (a : ℂ) * r ^ 2 + (b : ℂ) * r + (c : ℂ) = 0 :=
    cubic_root_lt_one_sqrt_three_aeval_cubic_eq hr_eval
  have hz_eval_c : z ^ 3 + (a : ℂ) * z ^ 2 + (b : ℂ) * z + (c : ℂ) = 0 :=
    cubic_root_lt_one_sqrt_three_aeval_cubic_eq hz_eval
  have hr_rep : r = (r.re : ℂ) := by
    apply Complex.ext <;> simp [hr_im]
  have hz_rep : z = (z.re + z.im * Complex.I : ℂ) := (Complex.re_add_im z).symm
  have hr_real : r.re ^ 3 + (a : ℝ) * r.re ^ 2 + (b : ℝ) * r.re + (c : ℝ) = 0 := by
    have h := hr_eval_c
    rw [hr_rep] at h
    have hre := congrArg Complex.re h
    norm_num [Complex.ofReal_re, Complex.add_re, Complex.mul_re, ← Complex.ofReal_pow] at hre
    ring_nf at hre ⊢
    exact hre
  have hz_copy := hz_eval_c
  rw [hz_rep] at hz_copy
  have hz_re0 := congrArg Complex.re hz_copy
  have hz_im0 := congrArg Complex.im hz_copy
  have hzr : z.re ^ 3 - 3 * z.re * z.im ^ 2 + (a : ℝ) * (z.re ^ 2 - z.im ^ 2) +
      (b : ℝ) * z.re + (c : ℝ) = 0 := by
    rw [cubic_root_lt_one_sqrt_three_cubic_eval_re] at hz_re0
    exact hz_re0
  have hzi_full : z.im * (3 * z.re ^ 2 - z.im ^ 2 + 2 * (a : ℝ) * z.re + (b : ℝ)) = 0 := by
    rw [cubic_root_lt_one_sqrt_three_cubic_eval_im] at hz_im0
    exact hz_im0
  have hzi : 3 * z.re ^ 2 - z.im ^ 2 + 2 * (a : ℝ) * z.re + (b : ℝ) = 0 := by
    exact (mul_eq_zero.mp hzi_full).resolve_left hz_im
  have hx_abs : |r.re| < 1 := cubic_root_lt_one_sqrt_three_real_im_zero_abs_lt_one hr_im hr_norm
  have hx1 : -1 < r.re := (abs_lt.mp hx_abs).1
  have hx2 : r.re < 1 := (abs_lt.mp hx_abs).2
  have hs : z.re ^ 2 + z.im ^ 2 < 3 := cubic_root_lt_one_sqrt_three_complex_root_normSq_lt_three hz_norm
  have hvieta := cubic_root_lt_one_sqrt_three_roots_vieta_complex hr_eval_c hz_eval_c hr_im hz_im
  rcases hvieta with ⟨hsumc, hpairc, hprodc⟩
  have hvreal := cubic_root_lt_one_sqrt_three_vieta_complex_to_real hr_im hsumc hpairc hprodc
  rcases hvreal with ⟨hsum_real, hb_real, hc_real⟩
  exact cubic_root_lt_one_sqrt_three_core ha hb hc hx1 hx2 hs hz_im hsum_real hb_real hc_real

end Commons.Polynomial