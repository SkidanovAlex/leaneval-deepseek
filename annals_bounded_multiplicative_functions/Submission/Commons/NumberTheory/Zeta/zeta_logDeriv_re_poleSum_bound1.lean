import Mathlib
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth
import Submission.Commons.NumberTheory.Zeta.zeta_strip_polyGrowth_neg
import Submission.Commons.NumberTheory.Zeta.zeta_norm_le_const_of_three_le_re
import Submission.Commons.NumberTheory.Zeta.zeta_lower_re_two
import Submission.Commons.NumberTheory.Zeta.zetaZeroBall
import Submission.Commons.NumberTheory.Zeta.zeta1_logDeriv_pole_removal
import Submission.Commons.NumberTheory.Linnik.goodRadius_pair
import Submission.Commons.Analysis.Complex.logDeriv_sub_divisor_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex Filter Metric Set Function
open scoped Real Topology BigOperators

set_option maxHeartbeats 0

noncomputable section

namespace Commons.NumberTheory.Zeta

/-!
# `zeta_logDeriv_re_poleSum_bound1`

There exist `C > 0` and `H ≥ 2` such that, whenever `β + i·t` (`|t| ≥ H`,
`1/2 ≤ β < 1`) is a zero of the Riemann zeta function, then for every `0 < x ≤ 1/2`
the real part of `−ζ′/ζ(1 + x + i·t)` is bounded above by
`−1/(x + (1 − β)) + C·(log(|t|+3) + 1)`.

**Proof.** Work with the entire completion `riemannZeta₁(s) = (s−1)·ζ(s)`.  Fix
`|t| ≥ 5`, centre `c = 2+i·t`, evaluation point `s₀ = (1+x)+i·t` and zero
`ρ₀ = β+i·t` (`2−β ≤ 3/2`, `1−x ≤ 1`).

1. Choose a "good" radius `R` with `max(4−4x, 4−2β) < R ≤ 4` avoiding the finitely
   many radii of the zeros of `riemannZeta₁` (both `R` and `R/2`); the circles
   `|w−c| = R` and `|w−c| = R/2` are then zero-free.
2. `|ζ₁(c)| ≥ κ|t|` (lower bound of `ζ` on `Re = 2`) and `‖ζ₁(w)‖ ≤ Cg·(|t|+7)¹⁵`
   on `|w−c| ≤ 4` (published strip bounds), so `|ζ₁(w)/ζ₁(c)| ≤ A` on the circle
   with `log A = O(log(|t|+6)+1)`.
3. The generic Borel–Carathéodory bound `Commons.Analysis.Complex.logDeriv_sub_divisor_le`
   (zeros inside `|w−c| ≤ R/2` factored out; the tail handled by the maximum modulus
   principle) gives, at `s₀`:

       ‖ζ₁′/ζ₁(s₀) − ∑_{u ∈ zeros, |u−c| ≤ R/2} d(u)/(s₀−u)‖ ≤ 4·log A/(R·(1−2·(1/4))²).

4. Real parts: every zero `u` has `Re u ≤ 1 < Re s₀`, so `Re(1/(s₀−u)) ≥ 0`; keeping
   only the term of `ρ₀` (divisor ≥ 1) and using `Re(1/(s₀−ρ₀)) = 1/(x+1−β)`:

       Re(−ζ₁′/ζ₁)(s₀) ≤ −1/(x+1−β) + O(log(|t|+6)+1).

   Finally `−ζ′/ζ = −ζ₁′/ζ₁ + 1/(s−1)` and `Re(1/(s₀−1)) ≤ 1` give the result.
-/


-- =========== copied basic helpers =============

private lemma norm_ofReal_coe (t : ℝ) : ‖(t : ℂ)‖ = |t| := RCLike.norm_ofReal t
private lemma zeta1_eq_sub_mul (w : ℂ) (hw : w ≠ 1) :
    riemannZeta₁ w = (w - 1) * riemannZeta w := by
  have hz : riemannZeta w = (w - 1)⁻¹ * riemannZeta₁ w := riemannZeta_eq_inv_sub_mul hw
  calc
    riemannZeta₁ w = (w - 1) * ((w - 1)⁻¹ * riemannZeta₁ w) := by
      rw [← mul_assoc, mul_inv_cancel₀ (sub_ne_zero.mpr hw), one_mul]
    _ = (w - 1) * riemannZeta w := by rw [hz]

private lemma zeta1_ne_zero_fun : riemannZeta₁ ≠ 0 := by
  intro hz
  have h2 : riemannZeta₁ (1 : ℂ) = 0 := congrFun hz (1 : ℂ)
  exact zero_ne_one (h2.symm.trans riemannZeta₁_one)

private lemma zeta1_analytic_closedBall (c : ℂ) (R : ℝ) :
    AnalyticOnNhd ℂ riemannZeta₁ (Metric.closedBall c R) := by
  intro w hw
  exact differentiable_riemannZeta₁.analyticAt w

private lemma zeta1_ne_zero_of_re_ge_two {w : ℂ} (hw : (2 : ℝ) ≤ w.re) : riemannZeta₁ w ≠ 0 := by
  have hw1 : w ≠ 1 := by
    intro h
    have hre : w.re = (1 : ℂ).re := congrArg Complex.re h
    simp at hre
    linarith
  have hz : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re (s := w) (by linarith)
  intro h₁
  have hprod : (w - 1) * riemannZeta w = 0 := by
    rwa [zeta1_eq_sub_mul w hw1] at h₁
  exact hz ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hw1))

private lemma zeta1_zero_re_le_one {u : ℂ} (hu : riemannZeta₁ u = 0) : u.re ≤ 1 := by
  by_contra hnot
  have hgt : 1 < u.re := by linarith
  have hu1 : u ≠ 1 := by
    intro h
    have hre : u.re = (1 : ℂ).re := congrArg Complex.re h
    simp at hre
    linarith
  have hz : riemannZeta u ≠ 0 := riemannZeta_ne_zero_of_one_le_re (s := u) (le_of_lt hgt)
  rw [zeta1_eq_sub_mul u hu1] at hu
  exact hz ((mul_eq_zero.mp hu).resolve_left (sub_ne_zero.mpr hu1))

private lemma divisor_pos_of_zero {U : Set ℂ} {u : ℂ}
    (hfan : AnalyticOnNhd ℂ riemannZeta₁ U) (hu : u ∈ U) (hfz : riemannZeta₁ u = 0) :
    (1 : ℤ) ≤ MeromorphicOn.divisor riemannZeta₁ U u := by
  have hd_ne : MeromorphicOn.divisor riemannZeta₁ U u ≠ 0 :=
    Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero differentiable_riemannZeta₁
      zeta1_ne_zero_fun hu hfz
  have hd_nonneg : (0 : ℤ) ≤ MeromorphicOn.divisor riemannZeta₁ U u :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfan u
  omega

private lemma divisor_ne_zero_implies_zero {U : Set ℂ} {u : ℂ}
    (hfan : AnalyticOnNhd ℂ riemannZeta₁ U) (hu : u ∈ U)
    (hd : (MeromorphicOn.divisor riemannZeta₁ U u : ℤ) ≠ 0) : riemannZeta₁ u = 0 := by
  by_contra h
  have hord : meromorphicOrderAt riemannZeta₁ u = (0 : WithTop ℤ) :=
    Commons.Analysis.Complex.meromorphicOrderAt_eq_zero_of_ne_zero (hfan u hu) h
  have hd' : (MeromorphicOn.divisor riemannZeta₁ U u : ℤ) = 0 := by
    rw [MeromorphicOn.divisor_apply (hfan.meromorphicOn) hu]
    rw [hord]
    rfl
  exact hd hd'

private lemma zeta1_growth_disk4 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ t : ℝ, 5 ≤ |t| →
      ∀ w : ℂ, ‖w - ((2 : ℂ) + Complex.I * (t : ℂ))‖ ≤ 4 →
        ‖riemannZeta₁ w‖ ≤ C₀ * (|t| + 7) ^ 15 := by
  rcases Commons.NumberTheory.Zeta.zeta_strip_polyGrowth with ⟨C1, hC1pos, hC1spec⟩
  rcases Commons.NumberTheory.Zeta.zeta_strip_polyGrowth_neg with ⟨C2, hC2pos, hC2spec⟩
  rcases Commons.NumberTheory.Zeta.zeta_norm_le_const_of_three_le_re with ⟨C3, hC3pos, hC3spec⟩
  let M : ℝ := max C1 (max C2 C3)
  let C₀ : ℝ := max 1 M
  have hC0pos : 0 < C₀ := by dsimp [C₀]; positivity
  have hC1le : C1 ≤ M := by dsimp [M]; exact le_max_left C1 (max C2 C3)
  have hC2le : C2 ≤ M := by dsimp [M]; exact le_trans (le_max_left C2 C3) (le_max_right C1 (max C2 C3))
  have hC3le : C3 ≤ M := by dsimp [M]; exact le_trans (le_max_right C2 C3) (le_max_right C1 (max C2 C3))
  have hMle : M ≤ C₀ := by dsimp [C₀]; exact le_max_right 1 M
  refine ⟨C₀, hC0pos, ?_⟩
  intro t ht w hw
  let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  have hwc : ‖w - c‖ ≤ 4 := by simpa [c] using hw
  have hw_re_abs : |w.re - 2| ≤ 4 := by
    have h2 : |w.re - 2| ≤ ‖w - c‖ := by simpa [c] using (Complex.abs_re_le_norm (w - c))
    exact le_trans h2 hwc
  have hIm_ge : (1 : ℝ) ≤ |w.im| := by
    have h2 : |w.im - t| ≤ ‖w - c‖ := by simpa [c] using (Complex.abs_im_le_norm (w - c))
    have htri : |t| ≤ |w.im - t| + |w.im| := by
      calc
        |t| = |(w.im - t) - w.im| := by
          have heq : (w.im - t) - w.im = -t := by ring
          rw [heq, abs_neg]
        _ ≤ |w.im - t| + |w.im| := by simpa [sub_eq_add_neg, abs_neg] using (abs_add_le (w.im - t) (-w.im))
    have h3 : |w.im - t| ≤ 4 := le_trans h2 hwc
    linarith
  have hIm_le : |w.im| ≤ |t| + 4 := by
    have h2 : |w.im - t| ≤ ‖w - c‖ := by simpa [c] using (Complex.abs_im_le_norm (w - c))
    have htri : |w.im| ≤ |w.im - t| + |t| := by
      calc
        |w.im| = |(w.im - t) + t| := by congr 1; ring
        _ ≤ |w.im - t| + |t| := abs_add_le (w.im - t) t
    have h3 : |w.im - t| ≤ 4 := le_trans h2 hwc
    linarith
  have hw1 : w ≠ 1 := by
    intro hw1'
    have hlen : |t| ≤ ‖(1 : ℂ) - c‖ := by
      have hneg : (1 : ℂ) - c = -((1 : ℂ) + Complex.I * (t : ℂ)) := by
        simp [c]
        ring
      have h := Complex.abs_im_le_norm ((1 : ℂ) + Complex.I * (t : ℂ))
      have him : ((1 : ℂ) + Complex.I * (t : ℂ)).im = t := by
        rw [Complex.add_im, Complex.mul_im]
        norm_num
      rw [him] at h
      rw [hneg, norm_neg]
      exact h
    have hbig : |t| ≤ ‖w - c‖ := by
      rw [hw1']
      exact hlen
    linarith
  have hw_sub : ‖w - 1‖ ≤ ‖w - c‖ + ‖c - 1‖ := by
    calc
      ‖w - 1‖ = ‖(w - c) + (c - 1)‖ := by congr 1; ring
      _ ≤ ‖w - c‖ + ‖c - 1‖ := norm_add_le (w - c) (c - 1)
  have hc1_le : ‖c - 1‖ ≤ |t| + 1 := by
    have hc1' : c - 1 = (1 : ℂ) + Complex.I * (t : ℂ) := by
      simp [c]
      ring
    calc
      ‖c - 1‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.I * (t : ℂ)‖ := by
        rw [hc1']
        simpa using (norm_add_le ((1 : ℂ)) (Complex.I * (t : ℂ)))
      _ ≤ |t| + 1 := by
        rw [norm_mul, Complex.norm_I, norm_ofReal_coe]
        norm_num
        linarith
      _ = |t| + 1 := by rfl
  have hw_norm_le : ‖w - 1‖ ≤ |t| + 7 := by
    calc
      ‖w - 1‖ ≤ ‖w - c‖ + ‖c - 1‖ := hw_sub
      _ ≤ 4 + (|t| + 1) := by linarith
      _ ≤ |t| + 7 := by linarith
  let σ : ℝ := w.re
  have hσ_lo : -2 ≤ σ := by
    have h := (abs_le.mp hw_re_abs).1
    dsimp [σ]
    linarith
  have hσ_hi : σ ≤ 6 := by
    have h := (abs_le.mp hw_re_abs).2
    dsimp [σ]
    linarith
  have hw_coord : w = (σ : ℂ) + Complex.I * (w.im : ℂ) := by
    apply Complex.ext
    · simp [σ]
    · simp
  have hzeta_le : ‖riemannZeta w‖ ≤ M * (|t| + 7) ^ 12 := by
    by_cases hA : σ ≤ -1
    · have hb := hC2spec σ w.im hσ_lo hA hIm_ge
      have hb' : ‖riemannZeta w‖ ≤ C2 * (|w.im| + 3) ^ 12 := by
        rw [← hw_coord] at hb
        exact hb
      have hIm7 : |w.im| + 3 ≤ |t| + 7 := by linarith
      have hpow : (|w.im| + 3) ^ 12 ≤ (|t| + 7) ^ 12 := by
        exact pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ |w.im| + 3) hIm7 12
      calc
        ‖riemannZeta w‖ ≤ C2 * (|w.im| + 3) ^ 12 := hb'
        _ ≤ C2 * (|t| + 7) ^ 12 := mul_le_mul_of_nonneg_left hpow (le_of_lt hC2pos)
        _ ≤ M * (|t| + 7) ^ 12 := mul_le_mul_of_nonneg_right hC2le (by positivity)
    · by_cases hB : σ ≤ 3
      · have hσm1 : -1 ≤ σ := by linarith
        have hb := hC1spec σ w.im hσm1 hB hIm_ge
        have hb' : ‖riemannZeta w‖ ≤ C1 * (|w.im| + 3) ^ 4 := by
          rw [← hw_coord] at hb
          exact hb
        have hIm7 : |w.im| + 3 ≤ |t| + 7 := by linarith
        have hone : (1 : ℝ) ≤ |w.im| + 3 := by linarith
        have hpow : (|w.im| + 3) ^ 4 ≤ (|t| + 7) ^ 12 := by
          have h4le12 : (|w.im| + 3) ^ 4 ≤ (|w.im| + 3) ^ 12 := pow_le_pow_right₀ hone (by omega : (4 : ℕ) ≤ 12)
          exact le_trans h4le12 (pow_le_pow_left₀ (by positivity) hIm7 12)
        calc
          ‖riemannZeta w‖ ≤ C1 * (|w.im| + 3) ^ 4 := hb'
          _ ≤ C1 * (|t| + 7) ^ 12 := mul_le_mul_of_nonneg_left hpow (le_of_lt hC1pos)
          _ ≤ M * (|t| + 7) ^ 12 := mul_le_mul_of_nonneg_right hC1le (by positivity)
      · have hσge3 : 3 ≤ σ := by linarith
        have hb := hC3spec w hσge3
        have hpow1 : (1 : ℝ) ≤ (|t| + 7) ^ 12 := by
          exact one_le_pow₀ (by linarith : (1 : ℝ) ≤ |t| + 7)
        calc
          ‖riemannZeta w‖ ≤ C3 := hb
          _ ≤ C3 * (|t| + 7) ^ 12 := le_mul_of_one_le_right (le_of_lt hC3pos) hpow1
          _ ≤ M * (|t| + 7) ^ 12 := mul_le_mul_of_nonneg_right hC3le (by positivity)
  have hz1 : riemannZeta₁ w = (w - 1) * riemannZeta w := zeta1_eq_sub_mul w hw1
  calc
    ‖riemannZeta₁ w‖ = ‖(w - 1) * riemannZeta w‖ := by rw [hz1]
    _ ≤ ‖w - 1‖ * ‖riemannZeta w‖ := norm_mul_le _ _
    _ ≤ (|t| + 7) * (M * (|t| + 7) ^ 12) :=
      mul_le_mul hw_norm_le hzeta_le (norm_nonneg _) (by positivity : (0 : ℝ) ≤ |t| + 7)
    _ = M * (|t| + 7) ^ 13 := by ring
    _ ≤ M * (|t| + 7) ^ 15 := by
      have hpow : (|t| + 7) ^ 13 ≤ (|t| + 7) ^ 15 := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ |t| + 7) (by omega : (13 : ℕ) ≤ 15)
      exact mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ M)
    _ ≤ C₀ * (|t| + 7) ^ 15 := by
      exact mul_le_mul_of_nonneg_right hMle (by positivity : (0 : ℝ) ≤ (|t| + 7) ^ 15)

private lemma exists_good_R (t β x : ℝ) (ht : 5 ≤ |t|) (hβ0 : 1 / 2 ≤ β) (hβ1 : β < 1)
    (hx0 : 0 < x) (hx12 : x ≤ 1 / 2) :
    ∃ R : ℝ, max (4 - 4 * x) (4 - 2 * β) < R ∧ R ≤ 4 ∧
      (∀ w : ℂ, ‖w - ((2 : ℂ) + Complex.I * (t : ℂ))‖ = R → riemannZeta₁ w ≠ 0) ∧
      (∀ w : ℂ, ‖w - ((2 : ℂ) + Complex.I * (t : ℂ))‖ = R / 2 → riemannZeta₁ w ≠ 0) := by
  let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  have hc_norm_le : ‖c‖ ≤ |t| + 2 := by
    have h1 := norm_add_le ((2 : ℂ)) (Complex.I * (t : ℂ))
    have hI : ‖(Complex.I : ℂ)‖ = 1 := Complex.norm_I
    have ht' : ‖(t : ℂ)‖ = |t| := norm_ofReal_coe t
    calc
      ‖c‖ ≤ ‖(2 : ℂ)‖ + ‖Complex.I * (t : ℂ)‖ := by simpa [c] using h1
      _ ≤ 2 + |t| := by
        rw [norm_mul, hI, ht']
        norm_num
      _ = |t| + 2 := by ring
  rcases Commons.NumberTheory.Zeta.zetaZeroBall (4 + ‖c‖) (by positivity) with ⟨Z, hZ⟩
  let Bad : Set ℝ := (fun u : ℂ => ‖u - c‖) '' (Z : Set ℂ)
  have hBad_fin : Bad.Finite := Z.finite_toSet.image (fun u : ℂ => ‖u - c‖)
  let Bad2 : Set ℝ := (fun r : ℝ => 2 * r) '' Bad
  have hBad2_fin : Bad2.Finite := hBad_fin.image (fun r : ℝ => 2 * r)
  let E : Set ℝ := Bad ∪ Bad2
  have hE_fin : E.Finite := hBad_fin.union hBad2_fin
  have ha_lt : max (4 - 4 * x) (4 - 2 * β) < 4 := by
    have hx : 4 - 4 * x < 4 := by nlinarith
    have hb : 4 - 2 * β < 4 := by nlinarith
    exact max_lt hx hb
  rcases Commons.NumberTheory.Linnik.exists_notMem_Ioc_of_finite (S := E) hE_fin ha_lt with
    ⟨R, hRa, hR4, hRnotE⟩
  have hRnotBad : R ∉ Bad := by
    intro hb
    exact hRnotE (Or.inl hb)
  have hRnotBad2 : R ∉ Bad2 := by
    intro hb
    exact hRnotE (Or.inr hb)
  refine ⟨R, hRa, hR4, ?_, ?_⟩
  · intro w hw
    intro hwz
    have hwZ : w ∈ Z := by
      rw [hZ]
      constructor
      · have hw_norm : ‖w‖ ≤ ‖w - c‖ + ‖c‖ := by
          calc
            ‖w‖ = ‖(w - c) + c‖ := by congr 1; ring
            _ ≤ ‖w - c‖ + ‖c‖ := norm_add_le (w - c) c
        rw [mem_closedBall, dist_zero_right]
        nlinarith [hw, hc_norm_le]
      · exact hwz
    have hr_in : ‖w - c‖ ∈ Bad := by
      refine Set.mem_image_of_mem _ hwZ
    have hRinBad : R ∈ Bad := by
      rw [← hw]
      exact hr_in
    exact hRnotBad hRinBad
  · intro w hw
    intro hwz
    have hwZ : w ∈ Z := by
      rw [hZ]
      constructor
      · have hw_norm : ‖w‖ ≤ ‖w - c‖ + ‖c‖ := by
          calc
            ‖w‖ = ‖(w - c) + c‖ := by congr 1; ring
            _ ≤ ‖w - c‖ + ‖c‖ := norm_add_le (w - c) c
        rw [mem_closedBall, dist_zero_right]
        have hR2le4 : R / 2 ≤ 4 := by linarith
        nlinarith [hw, hc_norm_le]
      · exact hwz
    have hr2_in : ‖w - c‖ ∈ Bad := by
      exact Set.mem_image_of_mem _ hwZ
    have hR_half : R / 2 = ‖w - c‖ := by linarith
    have hr2_inE : R ∈ Bad2 := by
      refine ⟨R / 2, ?_, ?_⟩
      · rw [hR_half]
        exact hr2_in
      · ring
    exact hRnotBad2 hr2_inE

/-! ## Geometry of `s₀`, `ρ₀`, `c` -/

private lemma dist_s₀_c (t x : ℝ) : ‖((((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)) -
    ((2 : ℂ) + Complex.I * (t : ℂ))‖ = |1 - x| := by
  have h : ((((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)) - ((2 : ℂ) + Complex.I * (t : ℂ))
      = ((1 + x - 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  calc
    ‖((((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)) - ((2 : ℂ) + Complex.I * (t : ℂ))‖
        = ‖(((1 + x - 2 : ℝ) : ℂ))‖ := by rw [h]
    _ = |1 + x - 2| := by rw [norm_ofReal_coe]
    _ = |1 - x| := by
      have hxy : 1 + x - 2 = -(1 - x) := by ring
      rw [hxy, abs_neg]

private lemma dist_rho_c (t β : ℝ) : ‖(((β : ℂ) + (t : ℂ) * Complex.I)) -
    ((2 : ℂ) + Complex.I * (t : ℂ))‖ = |β - 2| := by
  have h : (((β : ℂ) + (t : ℂ) * Complex.I)) - ((2 : ℂ) + Complex.I * (t : ℂ))
      = ((β - 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  rw [h]
  rw [norm_ofReal_coe]

/-! ## finsum real-part lemmas -/

private lemma re_coe_mul (n : ℤ) (z : ℂ) : (((n : ℤ) : ℂ) * z).re = (n : ℝ) * z.re := by
  rw [Complex.mul_re]
  have h1 : ((n : ℤ) : ℂ).re = (n : ℝ) := by simp
  have h2 : ((n : ℤ) : ℂ).im = 0 := by simp
  rw [h1, h2]
  ring


private lemma finsum_re_eq {d : ℂ → ℤ} (hfin : (Function.support d).Finite) (g : ℂ → ℂ) :
    (∑ᶠ u, ((d u : ℤ) : ℂ) * g u).re = ∑ᶠ u, ((d u : ℤ) : ℝ) * (g u).re := by
  classical
  let S : Finset ℂ := hfin.toFinset
  have hsub_term : Function.support (fun u : ℂ => ((d u : ℤ) : ℂ) * g u) ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    have hd : d u ≠ 0 := by
      intro hd0
      have hterm : ((d u : ℤ) : ℂ) * g u = 0 := by simp [hd0]
      exact hu hterm
    exact hfin.mem_toFinset.mpr hd
  have hsub_re : Function.support (fun u : ℂ => ((d u : ℤ) : ℝ) * (g u).re) ⊆ (S : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    have hd : d u ≠ 0 := by
      intro hd0
      have hterm : ((d u : ℤ) : ℝ) * (g u).re = 0 := by simp [hd0]
      exact hu hterm
    exact hfin.mem_toFinset.mpr hd
  rw [finsum_eq_sum_of_support_subset (f := fun u : ℂ => ((d u : ℤ) : ℂ) * g u) (s := S) hsub_term]
  rw [finsum_eq_sum_of_support_subset (f := fun u : ℂ => ((d u : ℤ) : ℝ) * (g u).re) (s := S) hsub_re]
  -- real part of a finite sum
  have hre : (∑ u ∈ S, ((d u : ℤ) : ℂ) * g u).re = ∑ u ∈ S, (((d u : ℤ) : ℂ) * g u).re := by
    refine Finset.induction_on S ?base ?step
    · simp
    · intro a S' ha ih
      rw [Finset.sum_insert ha, Complex.add_re, Finset.sum_insert ha, ih]
  rw [hre]
  apply Finset.sum_congr rfl
  intro u hu
  rw [re_coe_mul]

/-- real part of `d·z` for real `d`. -/
private lemma re_inv_sub_nonneg {u : ℂ} (hu : u.re ≤ 1) (s₀ : ℂ) (hs₀ : 1 < s₀.re) :
    0 ≤ (1 / (s₀ - u)).re := by
  have hne : s₀ - u ≠ 0 := by
    intro h
    have hre : s₀.re - u.re = 0 := by
      have hc := congrArg Complex.re h
      simpa using hc
    linarith
  have hre : (1 / (s₀ - u)).re = (s₀ - u).re / Complex.normSq (s₀ - u) := by
    calc
      (1 / (s₀ - u)).re = ((s₀ - u)⁻¹).re := by simp [one_div]
      _ = (s₀ - u).re / Complex.normSq (s₀ - u) := by
        rw [Complex.inv_def]
        rw [Complex.mul_re]
        rw [Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re]
        simp
        ring
  rw [hre]
  have hnormSq_pos : 0 < Complex.normSq (s₀ - u) := by
    rw [Complex.normSq_pos]
    exact hne
  have hnum : 0 ≤ (s₀ - u).re := by
    have hsre : (s₀ - u).re = s₀.re - u.re := by simp
    rw [hsre]
    linarith
  exact div_nonneg hnum (le_of_lt hnormSq_pos)

private lemma pole_term_re (β t x : ℝ) :
    (1 / ((((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I) - ((β : ℂ) + (t : ℂ) * Complex.I))).re
      = 1 / (x + (1 - β)) := by
  let a : ℝ := 1 + x - β
  have hdiff : ((((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I) - ((β : ℂ) + (t : ℂ) * Complex.I))
      = (a : ℂ) := by
    apply Complex.ext <;> simp [a] <;> ring
  calc
    (1 / ((((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I) - ((β : ℂ) + (t : ℂ) * Complex.I))).re
        = (1 / (a : ℂ)).re := by rw [hdiff]
    _ = (a⁻¹ : ℝ) := by
      rw [one_div, ← Complex.ofReal_inv]
      simp
    _ = 1 / a := by rw [inv_eq_one_div]
    _ = 1 / (x + (1 - β)) := by congr 1; dsimp [a]; ring

/-! ## Main analytic bound for `ζ₁` (before converting to `ζ`) -/

/-! ## log absorption -/

private lemma log_bound_aux (a : ℝ) (ha : 0 < a) :
    ∃ C₂ : ℝ, 0 < C₂ ∧ ∀ t : ℝ, (1 : ℝ) ≤ |t| →
      Real.log (1 + a * (|t| + 7) ^ 15) ≤ C₂ * (Real.log (|t| + 6) + 1) := by
  let B : ℝ := Real.log (1 + a) + 15 * Real.log 2
  let C₂ : ℝ := B + 15
  have hB0 : 0 ≤ B := by
    dsimp [B]
    have h1 : 0 ≤ Real.log (1 + a) := Real.log_nonneg (by linarith)
    have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    nlinarith
  have hC2pos : 0 < C₂ := by dsimp [C₂]; linarith
  refine ⟨C₂, hC2pos, ?_⟩
  intro t ht
  let M : ℝ := |t| + 7
  let L : ℝ := Real.log (|t| + 6)
  have hM : (1 : ℝ) ≤ M := by dsimp [M]; linarith
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hpos1 : 0 < 1 + a := by positivity
  have h1 : Real.log (1 + a * M ^ 15) ≤ Real.log ((1 + a) * M ^ 15) := by
    have hle : 1 + a * M ^ 15 ≤ (1 + a) * M ^ 15 := by
      have hone : (1 : ℝ) ≤ M ^ 15 := one_le_pow₀ hM
      nlinarith [ha, hone]
    exact Real.log_le_log (by positivity) hle
  have h2 : Real.log ((1 + a) * M ^ 15) = Real.log (1 + a) + Real.log (M ^ 15) := by
    rw [Real.log_mul (ne_of_gt hpos1) (ne_of_gt (pow_pos hMpos 15))]
  have h3 : Real.log (M ^ 15) = 15 * Real.log M := by
    rw [Real.log_pow]
    norm_num
  have hM6 : M ≤ 2 * (|t| + 6) := by
    dsimp [M]
    nlinarith
  have hlogM : Real.log M ≤ Real.log 2 + L := by
    have hpos2 : 0 < 2 * (|t| + 6) := by positivity
    have hlog := Real.log_le_log hMpos hM6
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : |t| + 6 ≠ 0)] at hlog
    linarith
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  calc
    Real.log (1 + a * (|t| + 7) ^ 15) = Real.log (1 + a * M ^ 15) := by rfl
    _ ≤ Real.log ((1 + a) * M ^ 15) := h1
    _ = Real.log (1 + a) + 15 * Real.log M := by rw [h2, h3]
    _ ≤ Real.log (1 + a) + 15 * (Real.log 2 + L) := by nlinarith
    _ ≤ C₂ * (L + 1) := by
      dsimp [C₂, B]
      nlinarith [hL0]

/-- `‖c − 1‖ ≥ |t|` for `c = 2 + it`. -/
private lemma c_sub_one_norm_ge (t : ℝ) : |t| ≤ ‖(((2 : ℂ) + Complex.I * (t : ℂ)) - 1)‖ := by
  have h := Complex.abs_im_le_norm (((2 : ℂ) + Complex.I * (t : ℂ)) - 1)
  have him : (((2 : ℂ) + Complex.I * (t : ℂ)) - 1).im = t := by simp
  rw [him] at h
  exact h

private lemma s₀_geom (t x : ℝ) (hx0 : 0 < x) (hx12 : x ≤ 1 / 2) :
    ‖((((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)) - ((2 : ℂ) + Complex.I * (t : ℂ))‖ ≤ 1 := by
  rw [dist_s₀_c, abs_of_nonneg (by linarith)]
  linarith

private lemma Finset_sum_re (Z : Finset ℂ) (g : ℂ → ℂ) :
    (∑ u ∈ Z, g u).re = ∑ u ∈ Z, (g u).re := by
  classical
  refine Finset.induction_on Z ?base ?step
  · simp
  · intro a Z' ha ih
    rw [Finset.sum_insert ha, Complex.add_re, Finset.sum_insert ha, ih]

private lemma divisor_support_mem {U : Set ℂ} {u : ℂ}
    (h : (MeromorphicOn.divisor riemannZeta₁ U u : ℤ) ≠ 0) : u ∈ U := by
  by_contra hnot
  have hd : (MeromorphicOn.divisor riemannZeta₁ U u : ℤ) = 0 := by
    rw [MeromorphicOn.divisor_def]
    simp [hnot]
  exact h hd

theorem zeta1_pole_bound :
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ t β x : ℝ, 5 ≤ |t| → 1 / 2 ≤ β → β < 1 →
      riemannZeta (((β : ℂ) + (t : ℂ) * Complex.I)) = 0 → 0 < x → x ≤ 1 / 2 →
      (-deriv riemannZeta₁ ((((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)) /
          riemannZeta₁ ((((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I))).re ≤
        -(1 / (x + (1 - β))) + C1 * (Real.log (|t| + 6) + 1) := by
  rcases zeta1_growth_disk4 with ⟨Cg, hCgpos, hGrowth⟩
  rcases Commons.NumberTheory.Zeta.zeta_lower_re_two with ⟨κ, hκpos, hκspec⟩
  rcases log_bound_aux (Cg / κ) (by positivity) with ⟨C₂, hC2pos, hC2spec⟩
  let C1 : ℝ := 8 * C₂ + 2
  have hC1pos : 0 < C1 := by dsimp [C1]; positivity
  refine ⟨C1, hC1pos, ?_⟩
  intro t β x ht hβ0 hβ1 hzero hx0 hx12
  let c : ℂ := (2 : ℂ) + Complex.I * (t : ℂ)
  let s₀ : ℂ := (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)
  let ρ₀ : ℂ := ((β : ℂ) + (t : ℂ) * Complex.I)
  let L : ℝ := Real.log (|t| + 6) + 1
  have hLge1 : (1 : ℝ) ≤ L := by
    dsimp [L]
    have hlog : 0 ≤ Real.log (|t| + 6) := Real.log_nonneg (by linarith)
    linarith
  rcases exists_good_R t β x ht hβ0 hβ1 hx0 hx12 with ⟨R, hRa, hR4, hRcirc, hRcirc2⟩
  have hR_ge4x : (4 - 4 * x) < R := lt_of_le_of_lt (le_max_left (4 - 4 * x) (4 - 2 * β)) hRa
  have hR_ge2b : (4 - 2 * β) < R := lt_of_le_of_lt (le_max_right (4 - 4 * x) (4 - 2 * β)) hRa
  have hRpos : 0 < R := by
    have hb : (2 : ℝ) < 4 - 2 * β := by nlinarith
    linarith
  have hs₀R : ‖s₀ - c‖ ≤ (1 / 4) * R := by
    have hdist := dist_s₀_c t x
    rw [hdist, abs_of_nonneg]
    · nlinarith
    · linarith
  have hρ₀R : ‖ρ₀ - c‖ ≤ R / 2 := by
    have hdist := dist_rho_c t β
    have hβ2 : β - 2 ≤ 0 := by linarith
    rw [hdist, abs_of_nonpos hβ2]
    nlinarith
  have hρ₀ball : ρ₀ ∈ Metric.closedBall c (R / 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hρ₀R
  have hζ1c : riemannZeta₁ c ≠ 0 := by
    apply zeta1_ne_zero_of_re_ge_two
    simp [c]
  have hζ1s₀ : riemannZeta₁ s₀ ≠ 0 := by
    intro hz
    have hs₀1 : s₀ ≠ 1 := by
      intro h
      have hre : s₀.re = (1 : ℂ).re := congrArg Complex.re h
      dsimp [s₀] at hre
      simp at hre
      linarith
    have hzζ : riemannZeta s₀ ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re (s := s₀)
      dsimp [s₀]
      simp
      linarith
    have hfac := zeta1_eq_sub_mul s₀ hs₀1
    have hprod : (s₀ - 1) * riemannZeta s₀ = 0 := by rwa [hfac] at hz
    exact hzζ ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hs₀1))
  have hζ1rho₀ : riemannZeta₁ ρ₀ = 0 := by
    have hρ₀nz : ρ₀ ≠ 1 := by
      intro h
      have hre : ρ₀.re = (1 : ℂ).re := congrArg Complex.re h
      dsimp [ρ₀] at hre
      simp at hre
      linarith
    have hfac := zeta1_eq_sub_mul ρ₀ hρ₀nz
    rw [hfac]
    dsimp [ρ₀]
    rw [hzero]
    ring
  have hclow : κ * |t| ≤ ‖riemannZeta₁ c‖ := by
    have hc1 : c ≠ 1 := by
      intro h
      have hre : c.re = (1 : ℂ).re := congrArg Complex.re h
      simp [c] at hre
    have hfac := zeta1_eq_sub_mul c hc1
    have him_le : |t| ≤ ‖c - 1‖ := by
      have h := Complex.abs_im_le_norm (c - 1)
      have him : (c - 1).im = t := by simp [c]
      rw [him] at h
      exact h
    have hzlow : κ ≤ ‖riemannZeta c‖ := by
      have h := hκspec t
      simpa [c] using h
    calc
      κ * |t| ≤ ‖riemannZeta c‖ * ‖c - 1‖ := by
        exact mul_le_mul hzlow him_le (abs_nonneg t) (norm_nonneg (riemannZeta c))
      _ = ‖(c - 1) * riemannZeta c‖ := by rw [norm_mul]; ring
      _ = ‖riemannZeta₁ c‖ := by rw [hfac]
  let M : ℝ := |t| + 7
  let A : ℝ := 1 + (Cg / κ) * M ^ 15
  have hA1 : (1 : ℝ) ≤ A := by
    dsimp [A]
    have hnn : 0 ≤ (Cg / κ) * M ^ 15 := by positivity
    linarith
  have hA0 : 0 ≤ A := by linarith
  have hlogA : Real.log A ≤ C₂ * (Real.log (|t| + 6) + 1) := by
    have hspec := hC2spec t (by linarith)
    dsimp [A, M]
    have hle : 1 + (Cg / κ) * (|t| + 7) ^ 15 ≤ 1 + (Cg / κ) * (|t| + 7) ^ 15 := le_rfl
    -- hspec: log (1 + (Cg/κ)(|t|+7)^15) ≤ C₂(log(|t|+6)+1)
    have hAeq : A = 1 + (Cg / κ) * M ^ 15 := rfl
    rw [show Real.log A = Real.log (1 + (Cg / κ) * M ^ 15) by rw [hAeq]]
    exact hspec
  have hAb : ∀ w : ℂ, ‖w - c‖ = R → ‖riemannZeta₁ w‖ ≤ A * ‖riemannZeta₁ c‖ := by
    intro w hw
    have hw4 : ‖w - c‖ ≤ 4 := by rw [hw]; exact hR4
    have hgw := hGrowth t ht w hw4
    have hAκ : Cg * M ^ 15 ≤ A * (κ * |t|) := by
      calc
        Cg * M ^ 15 ≤ (κ * |t|) * ((Cg / κ) * M ^ 15) := by
          have h1 : (κ * |t|) * ((Cg / κ) * M ^ 15) = Cg * M ^ 15 * |t| := by
            field_simp [ne_of_gt hκpos]
          rw [h1]
          have hCgn : 0 ≤ Cg * M ^ 15 := by positivity
          exact le_mul_of_one_le_right hCgn (by linarith : (1 : ℝ) ≤ |t|)
        _ ≤ (1 + (Cg / κ) * M ^ 15) * (κ * |t|) := by
          have hκt : 0 ≤ κ * |t| := by positivity
          nlinarith
        _ = A * (κ * |t|) := by rfl
    have hle1 : A * (κ * |t|) ≤ A * ‖riemannZeta₁ c‖ := by
      exact mul_le_mul_of_nonneg_left hclow hA0
    calc
      ‖riemannZeta₁ w‖ ≤ Cg * M ^ 15 := hgw
      _ ≤ A * (κ * |t|) := hAκ
      _ ≤ A * ‖riemannZeta₁ c‖ := hle1
  have hα : (1 / 4 : ℝ) < 1 / 2 := by norm_num
  have hα0 : 0 ≤ (1 / 4 : ℝ) := by norm_num
  have hb := Commons.Analysis.Complex.logDeriv_sub_divisor_le (f := riemannZeta₁) (c := c) (R := R)
    (A := A) (α := 1 / 4) hRpos hA1 hα0 hα (zeta1_analytic_closedBall c R) hζ1c hRcirc hRcirc2 hAb
    (s := s₀) hs₀R hζ1s₀
  let d : ℂ → ℤ := MeromorphicOn.divisor riemannZeta₁ (Metric.closedBall c (R / 2))
  have hfan : AnalyticOnNhd ℂ riemannZeta₁ (Metric.closedBall c (R / 2)) := zeta1_analytic_closedBall c (R / 2)
  have hdsupp : (Function.support d).Finite := by
    dsimp [d]
    exact MeromorphicOn.divisor_support_finite_of_subset (f := riemannZeta₁)
      (U := Metric.closedBall c (R / 2)) (V := Metric.closedBall c (R / 2))
      hfan.meromorphicOn (isCompact_closedBall c (R / 2)) (by intro z hz; exact hz)
  let Z0 : Finset ℂ := hdsupp.toFinset
  have hZ0_mem : ∀ u : ℂ, u ∈ Z0 ↔ d u ≠ 0 := by
    intro u
    exact hdsupp.mem_toFinset
  have hZ0rho₀ : ρ₀ ∈ Z0 := by
    rw [hZ0_mem]
    have hd_ne : d ρ₀ ≠ 0 := by
      dsimp [d]
      exact Commons.NumberTheory.Linnik.divisor_ne_zero_of_apply_eq_zero differentiable_riemannZeta₁
        zeta1_ne_zero_fun hρ₀ball hζ1rho₀
    exact hd_ne
  have hd_nonneg : ∀ u : ℂ, (0 : ℤ) ≤ d u := by
    intro u
    dsimp [d]
    exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfan u
  have hterm_support : Function.support (fun u : ℂ => ((d u : ℤ) : ℂ) * (1 / (s₀ - u))) ⊆ (Z0 : Set ℂ) := by
    intro u hu
    rw [Function.mem_support] at hu
    have hd : d u ≠ 0 := by
      intro hd0
      have hterm : ((d u : ℤ) : ℂ) * (1 / (s₀ - u)) = 0 := by simp [hd0]
      exact hu hterm
    exact (hZ0_mem u).mpr hd
  have hS_fin : (∑ᶠ u : ℂ, ((d u : ℤ) : ℂ) * (1 / (s₀ - u))) =
      ∑ u ∈ Z0, ((d u : ℤ) : ℂ) * (1 / (s₀ - u)) := by
    rw [finsum_eq_sum_of_support_subset (f := fun u : ℂ => ((d u : ℤ) : ℂ) * (1 / (s₀ - u))) (s := Z0) hterm_support]
  -- hb rewritten to finite sums
  rw [hS_fin] at hb
  have hb' : ‖logDeriv riemannZeta₁ s₀ - (∑ u ∈ Z0, ((d u : ℤ) : ℂ) * (1 / (s₀ - u)))‖ ≤
      4 * Real.log A / (R * (1 - 2 * (1 / 4)) ^ 2) := hb
  have hs₀re : 1 < s₀.re := by
    dsimp [s₀]
    simp
    linarith
  have hZ0_sub : ∀ u : ℂ, u ∈ Z0 → u ∈ Metric.closedBall c (R / 2) := by
    intro u hu
    have hdne : d u ≠ 0 := (hZ0_mem u).mp hu
    dsimp [d] at hdne
    exact divisor_support_mem hdne
  have hu_zeta1 : ∀ u : ℂ, u ∈ Z0 → riemannZeta₁ u = 0 := by
    intro u hu
    have hdne : d u ≠ 0 := (hZ0_mem u).mp hu
    dsimp [d] at hdne
    exact divisor_ne_zero_implies_zero hfan (hZ0_sub u hu) hdne
  have hu_re : ∀ u : ℂ, u ∈ Z0 → u.re ≤ 1 := by
    intro u hu
    exact zeta1_zero_re_le_one (hu_zeta1 u hu)
  let Su : ℂ := ∑ u ∈ Z0, (((d u : ℤ) : ℂ) * (1 / (s₀ - u)))
  have hReZ : Su.re = ∑ u ∈ Z0, ((d u : ℤ) : ℝ) * (1 / (s₀ - u)).re := by
    change ((∑ u ∈ Z0, (((d u : ℤ) : ℂ) * (1 / (s₀ - u))))).re = ∑ u ∈ Z0, ((d u : ℤ) : ℝ) * (1 / (s₀ - u)).re
    rw [Finset_sum_re]
    apply Finset.sum_congr rfl
    intro u hu
    rw [re_coe_mul]
  have hterm_ge : ∀ u : ℂ, u ∈ Z0 → 0 ≤ ((d u : ℤ) : ℝ) * (1 / (s₀ - u)).re := by
    intro u hu
    have hd0 : (0 : ℝ) ≤ (d u : ℤ) := by
      have hz0 : (0 : ℤ) ≤ d u := hd_nonneg u
      exact_mod_cast hz0
    have hrinv : 0 ≤ (1 / (s₀ - u)).re := by
      apply re_inv_sub_nonneg
      · exact hu_re u hu
      · exact hs₀re
    exact mul_nonneg hd0 hrinv
  have hterm_rho₀ : 1 / (x + (1 - β)) ≤ ((d ρ₀ : ℤ) : ℝ) * (1 / (s₀ - ρ₀)).re := by
    have hd1z : (1 : ℤ) ≤ d ρ₀ := by
      dsimp [d]
      exact divisor_pos_of_zero hfan hρ₀ball hζ1rho₀
    have hd1 : (1 : ℝ) ≤ (d ρ₀ : ℤ) := by exact_mod_cast hd1z
    have hRinv : 0 ≤ (1 / (s₀ - ρ₀)).re := by
      apply re_inv_sub_nonneg
      · exact zeta1_zero_re_le_one hζ1rho₀
      · exact hs₀re
    have hval : (1 / (s₀ - ρ₀)).re = 1 / (x + (1 - β)) := by
      dsimp [s₀, ρ₀]
      exact pole_term_re β t x
    rw [hval]
    nlinarith
  have hReSum_ge : 1 / (x + (1 - β)) ≤ Su.re := by
    rw [hReZ]
    exact le_trans hterm_rho₀ (Finset.single_le_sum hterm_ge hZ0rho₀)
  let Lc : ℂ := logDeriv riemannZeta₁ s₀
  have hL_def : Lc = deriv riemannZeta₁ s₀ / riemannZeta₁ s₀ := by
    dsimp [Lc]
    rw [logDeriv_apply]
  have htail : ‖Lc - Su‖ ≤ 4 * Real.log A / (R * (1 - 2 * (1 / 4)) ^ 2) := by
    simpa [Lc, Su] using hb'
  have hstep1 : (-Lc).re ≤ -Su.re + ‖Lc - Su‖ := by
    have hsplit : Lc = Su + (Lc - Su) := by ring
    have hstep1a : (-Lc).re = (-Su + -(Lc - Su)).re := by
      congr 1
      rw [hsplit]
      ring
    have h1 : (-Lc).re = -(Su.re) + (-(Lc - Su)).re := by
      calc
        (-Lc).re = (-Su + -(Lc - Su)).re := hstep1a
        _ = (-Su).re + (-(Lc - Su)).re := by simp
        _ = -(Su.re) + (-(Lc - Su)).re := by simp
    rw [h1]
    have hle : (-(Lc - Su)).re ≤ ‖Lc - Su‖ := by
      have habs : (-(Lc - Su)).re ≤ |(Lc - Su).re| := by
        rw [Complex.neg_re]
        exact neg_le_abs ((Lc - Su).re)
      exact le_trans habs (Complex.abs_re_le_norm (Lc - Su))
    linarith
  have hstep2 : -Su.re ≤ -(1 / (x + (1 - β))) := by linarith [hReSum_ge]
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hstep3 : 4 * Real.log A / (R * (1 - 2 * (1 / 4)) ^ 2) ≤ 8 * Real.log A := by
    have h16 : 4 * Real.log A / (R * (1 - 2 * (1 / 4)) ^ 2) ≤ 16 * Real.log A / R := by
      norm_num
      field_simp [hRpos.ne']
      nlinarith
    have hdiv : 16 * Real.log A / R ≤ 8 * Real.log A := by
      rw [div_le_iff₀ hRpos]
      nlinarith
    exact le_trans h16 hdiv
  have hlogA_bound : 8 * Real.log A ≤ 8 * (C₂ * L) := by
    have hle : Real.log A ≤ C₂ * L := by
      dsimp [L]
      exact hlogA
    nlinarith [hC2pos]
  have hfin1 : (-Lc).re ≤ -(1 / (x + (1 - β))) + 8 * (C₂ * L) := by
    have hE := htail
    nlinarith [hstep1, hE, hstep2, hstep3, hlogA_bound]
  have hC1_ge : 8 * (C₂ * L) ≤ C1 * L := by
    dsimp [C1]
    nlinarith [hLge1, hC2pos]
  have hfin2 : (-Lc).re ≤ -(1 / (x + (1 - β))) + C1 * L := by
    nlinarith [hfin1, hC1_ge]
  have hLneg : (-deriv riemannZeta₁ s₀ / riemannZeta₁ s₀) = -Lc := by
    have hring : -deriv riemannZeta₁ s₀ / riemannZeta₁ s₀ = -(deriv riemannZeta₁ s₀ / riemannZeta₁ s₀) := by ring
    rw [hring, ← hL_def]
  have hgoal : (-deriv riemannZeta₁ s₀ / riemannZeta₁ s₀).re ≤ -(1 / (x + (1 - β))) + C1 * (Real.log (|t| + 6) + 1) := by
    rw [hLneg]
    dsimp [L]
    exact hfin2
  exact hgoal


/-! ## Final theorem for ζ -/

/-- identity `ζ′/ζ = ζ₁′/ζ₁ − (s−1)⁻¹` for `s ≠ 1` (as real parts of the negatives). -/
private lemma logDeriv_inv_shift (c s : ℂ) (hs : s ≠ c) :
    logDeriv (fun w : ℂ => (w - c)⁻¹) s = - (s - c)⁻¹ := by
  rw [logDeriv_apply]
  have hd : HasDerivAt (fun w : ℂ => w - c) 1 s := by
    simpa using ((hasDerivAt_id s).sub_const c)
  have hinv := hd.inv (sub_ne_zero.mpr hs)
  have hder : deriv (fun w : ℂ => (w - c)⁻¹) s = -1 / (s - c) ^ 2 := hinv.deriv
  calc
    deriv (fun w : ℂ => (w - c)⁻¹) s / (fun w : ℂ => (w - c)⁻¹) s
        = (-1 / (s - c) ^ 2) / ((s - c)⁻¹) := by rw [hder]
    _ = - (s - c)⁻¹ := by
      field_simp [sub_ne_zero.mpr hs]

/-- identity `ζ′/ζ = ζ₁′/ζ₁ − (s−1)⁻¹` for `s ≠ 1` (written with `deriv`). -/
private lemma zeta1_logDeriv_sub_deriv (s : ℂ) (hs : s ≠ 1) (hz1 : riemannZeta₁ s ≠ 0) :
    deriv riemannZeta s / riemannZeta s = deriv riemannZeta₁ s / riemannZeta₁ s - (s - 1)⁻¹ := by
  let P : ℂ → ℂ := fun w : ℂ => (w - 1)⁻¹
  have hfac : (fun w : ℂ => riemannZeta w) =ᶠ[𝓝 s] fun w : ℂ => P w * riemannZeta₁ w := by
    filter_upwards [eventually_ne_nhds hs] with w hw
    dsimp [P]
    exact riemannZeta_eq_inv_sub_mul hw
  have hPne : P s ≠ 0 := by
    dsimp [P]
    exact inv_ne_zero (sub_ne_zero.mpr hs)
  have hdP : DifferentiableAt ℂ P s := by
    dsimp [P]
    exact ((hasDerivAt_id s).sub_const (1 : ℂ)).inv (sub_ne_zero.mpr hs) |>.differentiableAt
  have hz1diff : DifferentiableAt ℂ riemannZeta₁ s := by fun_prop
  have hL1 : logDeriv P s = - (s - 1)⁻¹ := by
    dsimp [P]
    exact logDeriv_inv_shift (1 : ℂ) s hs
  have hL2 : logDeriv (fun w : ℂ => P w * riemannZeta₁ w) s = logDeriv P s + logDeriv riemannZeta₁ s := by
    exact logDeriv_mul s hPne hz1 hdP hz1diff
  have hlog1 : logDeriv riemannZeta s = logDeriv (fun w : ℂ => P w * riemannZeta₁ w) s := by
    have hc : logDeriv riemannZeta =ᶠ[𝓝 s] logDeriv (fun w : ℂ => P w * riemannZeta₁ w) :=
      (logDeriv_congr_nhds hfac)
    exact hc.eq_of_nhds
  calc
    deriv riemannZeta s / riemannZeta s = logDeriv riemannZeta s := (logDeriv_apply riemannZeta s).symm
    _ = logDeriv (fun w : ℂ => P w * riemannZeta₁ w) s := hlog1
    _ = logDeriv P s + logDeriv riemannZeta₁ s := hL2
    _ = - (s - 1)⁻¹ + deriv riemannZeta₁ s / riemannZeta₁ s := by
      rw [hL1]
      rw [logDeriv_apply riemannZeta₁ s]
    _ = deriv riemannZeta₁ s / riemannZeta₁ s - (s - 1)⁻¹ := by ring

theorem zeta_logDeriv_re_poleSum_bound1 :
    ∃ C : ℝ, 0 < C ∧ ∃ H : ℝ, (2 : ℝ) ≤ H ∧
      ∀ t : ℝ, H ≤ |t| → ∀ β : ℝ, (1 / 2 : ℝ) ≤ β → β < 1 →
        riemannZeta (((β : ℂ) + (t : ℂ) * Complex.I)) = 0 →
        ∀ x : ℝ, 0 < x → x ≤ 1 / 2 →
        (-deriv riemannZeta ((((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)) /
            riemannZeta ((((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I))).re ≤
          - (1 / (x + (1 - β))) + C * (Real.log (|t| + 3) + 1) := by
  rcases zeta1_pole_bound with ⟨C1, hC1pos, hC1spec⟩
  let C : ℝ := C1 * (1 + Real.log 3) + 2
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hCpos : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hCpos, (5 : ℝ), by norm_num, ?_⟩
  intro t ht β hβ0 hβ1 hzero x hx0 hx12
  let s₀ : ℂ := (((1 + x : ℝ) : ℂ) + (t : ℂ) * Complex.I)
  have hb := hC1spec t β x (by linarith) hβ0 hβ1 hzero hx0 hx12
  have hs₀1 : s₀ ≠ 1 := by
    intro h
    have hre : s₀.re = (1 : ℂ).re := congrArg Complex.re h
    dsimp [s₀] at hre
    simp at hre
    linarith
  have hζ1s₀ : riemannZeta₁ s₀ ≠ 0 := by
    intro hz
    have hzζ : riemannZeta s₀ ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re (s := s₀)
      dsimp [s₀]
      simp
      linarith
    have hfac := zeta1_eq_sub_mul s₀ hs₀1
    have hprod : (s₀ - 1) * riemannZeta s₀ = 0 := by rwa [hfac] at hz
    exact hzζ ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hs₀1))
  have hmain := zeta1_logDeriv_sub_deriv s₀ hs₀1 hζ1s₀
  have hrel : (-deriv riemannZeta s₀ / riemannZeta s₀).re =
      (-deriv riemannZeta₁ s₀ / riemannZeta₁ s₀).re + (1 / (s₀ - 1)).re := by
    have hparse : -deriv riemannZeta s₀ / riemannZeta s₀ = -(deriv riemannZeta s₀ / riemannZeta s₀) := by ring
    have hparse1 : -deriv riemannZeta₁ s₀ / riemannZeta₁ s₀ = -(deriv riemannZeta₁ s₀ / riemannZeta₁ s₀) := by ring
    calc
      (-deriv riemannZeta s₀ / riemannZeta s₀).re
          = (-(deriv riemannZeta s₀ / riemannZeta s₀)).re := by rw [hparse]
      _ = (-(deriv riemannZeta₁ s₀ / riemannZeta₁ s₀ - (s₀ - 1)⁻¹)).re := by rw [hmain]
      _ = (-(deriv riemannZeta₁ s₀ / riemannZeta₁ s₀)).re + ((s₀ - 1)⁻¹).re := by
        have hnegadd : -(deriv riemannZeta₁ s₀ / riemannZeta₁ s₀ - (s₀ - 1)⁻¹)
            = -(deriv riemannZeta₁ s₀ / riemannZeta₁ s₀) + (s₀ - 1)⁻¹ := by ring
        rw [hnegadd]
        simp
      _ = (-deriv riemannZeta₁ s₀ / riemannZeta₁ s₀).re + (1 / (s₀ - 1)).re := by
        rw [hparse1, one_div]
  have hrel1 : (1 / (s₀ - 1)).re ≤ 1 := by
    have h1 : (1 / (s₀ - 1)).re ≤ ‖(1 / (s₀ - 1))‖ := by
      exact le_trans (le_abs_self ((1 / (s₀ - 1)).re)) (Complex.abs_re_le_norm (1 / (s₀ - 1)))
    have hn : ‖s₀ - 1‖ ≥ 1 := by
      have him := Complex.abs_im_le_norm (s₀ - 1)
      have htm : (s₀ - 1).im = t := by dsimp [s₀]; simp
      rw [htm] at him
      have hle : 1 ≤ |t| := by linarith
      linarith
    have h2 : ‖(1 / (s₀ - 1))‖ ≤ 1 := by
      rw [one_div, norm_inv]
      exact inv_le_one_of_one_le₀ hn
    linarith
  have hlog6 : Real.log (|t| + 6) + 1 ≤ (1 + Real.log 3) * (Real.log (|t| + 3) + 1) := by
    have hpos1 : 0 < |t| + 6 := by linarith
    have hle : |t| + 6 ≤ 3 * (|t| + 3) := by nlinarith
    have hlog := Real.log_le_log hpos1 hle
    have hlog3 : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith)
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by linarith : |t| + 3 ≠ 0)] at hlog
    nlinarith [hlog3]
  have hL3ge1 : (1 : ℝ) ≤ Real.log (|t| + 3) + 1 := by
    have hlog : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith)
    linarith
  have hmain2 : (-deriv riemannZeta₁ s₀ / riemannZeta₁ s₀).re ≤
      -(1 / (x + (1 - β))) + C1 * (Real.log (|t| + 6) + 1) := by
    simpa [s₀] using hb
  have h2' : C1 * (Real.log (|t| + 6) + 1) + 1 ≤ C * (Real.log (|t| + 3) + 1) := by
    have h1 : C1 * (Real.log (|t| + 6) + 1) ≤ C1 * ((1 + Real.log 3) * (Real.log (|t| + 3) + 1)) :=
      mul_le_mul_of_nonneg_left hlog6 (le_of_lt hC1pos)
    dsimp [C]
    nlinarith [h1, hL3ge1]
  calc
    (-deriv riemannZeta s₀ / riemannZeta s₀).re
        ≤ -(1 / (x + (1 - β))) + C1 * (Real.log (|t| + 6) + 1) + 1 := by
      rw [hrel]
      have hr := hrel1
      nlinarith [hmain2]
    _ = -(1 / (x + (1 - β))) + (C1 * (Real.log (|t| + 6) + 1) + 1) := by ring
    _ ≤ -(1 / (x + (1 - β))) + C * (Real.log (|t| + 3) + 1) := by nlinarith [h2']

end Commons.NumberTheory.Zeta
