/-
# The C²-bounds for the §6 spike profile at the arithmetic modulus `q`

This module proves `Work.KMTAreas.A7.spike_profile_bounds_q`: there are constants `C, A ≥ 0` such
that for every `N ≥ 1`, every pair of scales `k₁,k₂`, every `q ≥ 1` with `q • β₁ = q • β₂ = 0` the
real profile

  `spikeProfile P N k₁ k₂ q β₁ β₂ (x₁,x₂) = φ_N(x₁) φ̃_N(x₂) M₀ P N q β₁ β₂ x₁ x₂`

is `C⁴`, supported in the rectangle dictated by the two bumps, bounded by
`C q 2^{A (k₁+k₂)} / N`, and has the three second-derivative bounds of the §6 single-scale
estimate (the two one-sided ones and the mixed one), each gaining the corresponding power of the
support radius.

The bookkeeping argument is the one of `KMTAreas/A7/spikeProfile_bounds.lean`
(`spikeProfile_estimates`); here it is assembled with concrete ingredients:

* the uniform-in-`N,k` `C²`-bounds for the bumps (`varphitildeN_deriv_unif`, and `varphiN` is
  `varphitildeN 1`);
* the uniform mixed-derivative bound for `M₀` (`M0_iteratedDeriv_bound`);
* the Schwarz/Clairaut exchange of the two double derivatives (`spike_dp_comm_two`, proved here
  from the `C²`-symmetry of the second Fréchet derivative);
* the elementary `2`-power arithmetic (`spike_xz_arith`).
-/
import Mathlib
import Submission.Work.KMTAreas.A7.spikeDefs
import Submission.Work.KMTAreas.A7.M0_iteratedDeriv_bound
import Submission.Work.KMTAreas.A7.varphitildeN_deriv_unif
import Submission.Work.KMTAreas.A7.spikeToolbox
import Submission.Work.KMTPlan.A6.symD_period_contDiff
import Submission.Work.KMTPlan.A6.SymToolbox_dp1_one_contDiff
import Submission.Work.KMTPlan.A6.SymToolbox_dp2_one_contDiff

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas.A7

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTPlan.A6

noncomputable section

/-! ## Exchange of the two double derivatives (Schwarz/Clairaut) -/

/-- The derivative of the slice `t ↦ (t,c)` is the constant vector `(1,0)`. -/
private lemma deriv_slice_left (c x : ℝ) :
    deriv (fun t : ℝ => (t, c)) x = ((1 : ℝ), (0 : ℝ)) :=
  ((hasDerivAt_id x).prodMk (hasDerivAt_const x c)).deriv

/-- The derivative of the slice `s ↦ (c,s)` is the constant vector `(0,1)`. -/
private lemma deriv_slice_right (c y : ℝ) :
    deriv (fun s : ℝ => (c, s)) y = ((0 : ℝ), (1 : ℝ)) :=
  ((hasDerivAt_const y c).prodMk (hasDerivAt_id y)).deriv

/-- The Fréchet derivative of a two-variable function in the first coordinate is the derivative of
the corresponding slice. -/
private lemma fderiv_fst_eq_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : ℝ × ℝ → F) (x y : ℝ) (hG : DifferentiableAt ℝ G (x, y)) :
    fderiv ℝ G (x, y) ((1 : ℝ), (0 : ℝ)) = deriv (fun t : ℝ => G (t, y)) x := by
  have hslice : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x :=
    (hasFDerivAt_prodMk_left x y).differentiableAt
  have h := fderiv_comp_deriv (l := G) (f := fun t : ℝ => (t, y)) (x := x) hG hslice
  rw [deriv_slice_left y x] at h
  have heq : (G ∘ fun t : ℝ => (t, y)) = fun t : ℝ => G (t, y) := rfl
  rw [heq] at h
  exact h.symm

/-- The Fréchet derivative of a two-variable function in the second coordinate is the derivative
of the corresponding slice. -/
private lemma fderiv_snd_eq_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (G : ℝ × ℝ → F) (x y : ℝ) (hG : DifferentiableAt ℝ G (x, y)) :
    fderiv ℝ G (x, y) ((0 : ℝ), (1 : ℝ)) = deriv (fun s : ℝ => G (x, s)) y := by
  have hslice : DifferentiableAt ℝ (fun s : ℝ => (x, s)) y :=
    (hasFDerivAt_prodMk_right x y).differentiableAt
  have h := fderiv_comp_deriv (l := G) (f := fun s : ℝ => (x, s)) (x := y) hG hslice
  rw [deriv_slice_right x y] at h
  have heq : (G ∘ fun s : ℝ => (x, s)) = fun s : ℝ => G (x, s) := rfl
  rw [heq] at h
  exact h.symm

/-- Evaluating the derivative of a `(ℝ × ℝ →L[ℝ] ℂ)`-valued function commutes with `deriv`. -/
private lemma deriv_clm_apply_const (c : ℝ → ((ℝ × ℝ) →L[ℝ] ℂ)) (e : ℝ × ℝ) (y : ℝ)
    (hc : DifferentiableAt ℝ c y) :
    (deriv c y) e = deriv (fun s : ℝ => c s e) y := by
  have hd : DifferentiableAt ℝ (fun _ : ℝ => e) y := differentiableAt_const e
  have h := deriv_clm_apply (c := c) (u := fun _ : ℝ => e) hc hd
  simpa using h.symm

/-- **Schwarz/Clairaut for the §6 two-variable partials.**  If `H` is `C²` as a function on
`ℝ × ℝ`, then the two mixed second partial derivatives agree. -/
private lemma dp1_dp2_swap (H : ℝ → ℝ → ℂ)
    (hH : ContDiff ℝ 2 (fun p : ℝ × ℝ => H p.1 p.2)) :
    dp1 1 (dp2 1 H) = dp2 1 (dp1 1 H) := by
  funext x y
  set Ψ : ℝ × ℝ → ℂ := fun p => H p.1 p.2 with hΨdef
  have hHΨ : ContDiff ℝ 2 Ψ := hH
  have hdiffΨ : ∀ z : ℝ × ℝ, DifferentiableAt ℝ Ψ z :=
    fun z => (hHΨ.differentiable (by simp)).differentiableAt
  have hfderiv : ContDiff ℝ 1 (fderiv ℝ Ψ) := hHΨ.fderiv_right (m := 1) (by norm_num)
  have hdiffθ : DifferentiableAt ℝ (fderiv ℝ Ψ) (x, y) :=
    (hfderiv.differentiable (by simp)).differentiableAt
  have hsymm : fderiv ℝ (fderiv ℝ Ψ) (x, y) ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ))
      = fderiv ℝ (fderiv ℝ Ψ) (x, y) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) :=
    (hHΨ.contDiffAt.isSymmSndFDerivAt (by simp)).eq _ _
  have hsliceA : ∀ u v : ℝ, fderiv ℝ Ψ (u, v) ((1 : ℝ), (0 : ℝ)) = dp1 1 H u v := by
    intro u v
    rw [fderiv_fst_eq_deriv Ψ u v (hdiffΨ (u, v))]
    simp only [hΨdef, dp1, iteratedDeriv_one]
  have hsliceB : ∀ u v : ℝ, fderiv ℝ Ψ (u, v) ((0 : ℝ), (1 : ℝ)) = dp2 1 H u v := by
    intro u v
    rw [fderiv_snd_eq_deriv Ψ u v (hdiffΨ (u, v))]
    simp only [hΨdef, dp2, iteratedDeriv_one]
  have hleft : fderiv ℝ (fderiv ℝ Ψ) (x, y) ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ))
      = dp2 1 (dp1 1 H) x y := by
    rw [fderiv_snd_eq_deriv (fderiv ℝ Ψ) x y hdiffθ]
    have hc : DifferentiableAt ℝ (fun s : ℝ => fderiv ℝ Ψ (x, s)) y :=
      hdiffθ.comp y ((differentiableAt_const x).prodMk differentiableAt_id)
    rw [deriv_clm_apply_const (c := fun s : ℝ => fderiv ℝ Ψ (x, s)) ((1 : ℝ), (0 : ℝ)) y hc]
    have hfun : (fun s : ℝ => fderiv ℝ Ψ (x, s) ((1 : ℝ), (0 : ℝ)))
        = fun s : ℝ => dp1 1 H x s := funext fun s => hsliceA x s
    rw [hfun]
    simp only [dp2, iteratedDeriv_one]
  have hright : fderiv ℝ (fderiv ℝ Ψ) (x, y) ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))
      = dp1 1 (dp2 1 H) x y := by
    rw [fderiv_fst_eq_deriv (fderiv ℝ Ψ) x y hdiffθ]
    have hc : DifferentiableAt ℝ (fun t : ℝ => fderiv ℝ Ψ (t, y)) x :=
      hdiffθ.comp x (differentiableAt_id.prodMk (differentiableAt_const y))
    rw [deriv_clm_apply_const (c := fun t : ℝ => fderiv ℝ Ψ (t, y)) ((0 : ℝ), (1 : ℝ)) x hc]
    have hfun : (fun t : ℝ => fderiv ℝ Ψ (t, y) ((0 : ℝ), (1 : ℝ)))
        = fun t : ℝ => dp2 1 H t y := funext fun t => hsliceB t y
    rw [hfun]
    simp only [dp1, iteratedDeriv_one]
  rw [← hleft, ← hright]
  exact hsymm.symm

/-- `dp1 (n+1) = dp1 1 ∘ dp1 n`. -/
private lemma dp1_succ_eq (n : ℕ) (H : ℝ → ℝ → ℂ) : dp1 (n + 1) H = dp1 1 (dp1 n H) := by
  funext x y
  simp only [dp1, iteratedDeriv_one]
  rw [iteratedDeriv_succ]

/-- `dp2 (n+1) = dp2 1 ∘ dp2 n`. -/
private lemma dp2_succ_eq (n : ℕ) (H : ℝ → ℝ → ℂ) : dp2 (n + 1) H = dp2 1 (dp2 n H) := by
  funext x y
  simp only [dp2, iteratedDeriv_one]
  rw [iteratedDeriv_succ]

/-- `dp1 2 = dp1 1 ∘ dp1 1`. -/
private lemma dp1_two_eq (H : ℝ → ℝ → ℂ) : dp1 2 H = dp1 1 (dp1 1 H) := dp1_succ_eq 1 H

/-- `dp2 2 = dp2 1 ∘ dp2 1`. -/
private lemma dp2_two_eq (H : ℝ → ℝ → ℂ) : dp2 2 H = dp2 1 (dp2 1 H) := dp2_succ_eq 1 H

/-- **The exchange of the two double derivatives.**  For a `C⁴` function `g` on `ℝ × ℝ` the
iterated mixed derivative `∂₂²∂₁² g` equals `∂₁²∂₂² g = dp 2 2 g`. -/
private lemma spike_dp_comm_two (g : ℝ → ℝ → ℂ)
    (hg : ContDiff ℝ 4 (fun p : ℝ × ℝ => g p.1 p.2)) :
    dp2 2 (dp1 2 g) = dp 2 2 g := by
  have hsm4 : ContDiff ℝ 4 (fun p : ℝ × ℝ => g p.1 p.2) := hg
  have hAg : ContDiff ℝ 3 (fun p : ℝ × ℝ => dp1 1 g p.1 p.2) :=
    SymToolbox_dp1_one_contDiff g 3 hsm4
  have hBg : ContDiff ℝ 3 (fun p : ℝ × ℝ => dp2 1 g p.1 p.2) :=
    SymToolbox_dp2_one_contDiff g 3 hsm4
  have hABg : ContDiff ℝ 2 (fun p : ℝ × ℝ => dp1 1 (dp2 1 g) p.1 p.2) :=
    SymToolbox_dp1_one_contDiff (dp2 1 g) 2 hBg
  have hAg2 : ContDiff ℝ 2 (fun p : ℝ × ℝ => dp1 1 g p.1 p.2) := hAg.of_le (by norm_num)
  have hBg2 : ContDiff ℝ 2 (fun p : ℝ × ℝ => dp2 1 g p.1 p.2) := hBg.of_le (by norm_num)
  have hg2 : ContDiff ℝ 2 (fun p : ℝ × ℝ => g p.1 p.2) := hsm4.of_le (by norm_num)
  -- the four Clairaut exchanges, read off the operator word `A A B B`
  have e1 : dp1 1 (dp2 1 (dp1 1 g)) = dp2 1 (dp1 1 (dp1 1 g)) := dp1_dp2_swap (dp1 1 g) hAg2
  have e2 : dp1 1 (dp2 1 g) = dp2 1 (dp1 1 g) := dp1_dp2_swap g hg2
  have e3 : dp1 1 (dp2 1 (dp1 1 (dp2 1 g))) = dp2 1 (dp1 1 (dp1 1 (dp2 1 g))) :=
    dp1_dp2_swap (dp1 1 (dp2 1 g)) hABg
  have e4 : dp1 1 (dp2 1 (dp2 1 g)) = dp2 1 (dp1 1 (dp2 1 g)) := dp1_dp2_swap (dp2 1 g) hBg2
  -- the four bubble-sort steps turning the word `A A B B` into `B B A A`
  have s1 : dp2 1 (dp2 1 (dp1 1 (dp1 1 g))) = dp2 1 (dp1 1 (dp2 1 (dp1 1 g))) :=
    (congrArg (dp2 1) e1).symm
  have s2 : dp2 1 (dp1 1 (dp2 1 (dp1 1 g))) = dp2 1 (dp1 1 (dp1 1 (dp2 1 g))) :=
    (congrArg (fun X : ℝ → ℝ → ℂ => dp2 1 (dp1 1 X)) e2).symm
  have s3 : dp2 1 (dp1 1 (dp1 1 (dp2 1 g))) = dp1 1 (dp2 1 (dp1 1 (dp2 1 g))) := e3.symm
  have s4 : dp1 1 (dp2 1 (dp1 1 (dp2 1 g))) = dp1 1 (dp1 1 (dp2 1 (dp2 1 g))) :=
    (congrArg (dp1 1) e4).symm
  have key : dp2 1 (dp2 1 (dp1 1 (dp1 1 g))) = dp1 1 (dp1 1 (dp2 1 (dp2 1 g))) :=
    s1.trans (s2.trans (s3.trans s4))
  have key' : dp2 2 (dp1 2 g) = dp1 2 (dp2 2 g) := by
    rw [dp2_two_eq (dp1 2 g), dp1_two_eq g, dp1_two_eq (dp2 2 g), dp2_two_eq g]
    exact key
  exact key'

/-! ## The elementary `2`-power arithmetic -/

/-- `2^p · 2^q · 2^r = 2^{p+q+r}` for real exponents. -/
private lemma two_rpow_mul_three (p q r : ℝ) :
    (2:ℝ)^p * (2:ℝ)^q * (2:ℝ)^r = (2:ℝ)^(p+q+r) := by
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2),
    add_assoc]

/-- The `2`-power arithmetic of the `M₀`-derivative bound: `XZ^{A_M} u^a v^b` is absorbed by
`4 · 2^{2d} · (2+2^d+1)^{A_M} · 2^{(A_M d + 2d+2)(k₁+k₂)}`. -/
private lemma spike_xz_arith (d k₁ k₂ a b : ℕ) (hd : 1 ≤ d) {A_M u v : ℝ} (hA_M : 0 ≤ A_M)
    (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hu2 : u ≤ (2:ℝ)^(k₁+1)) (hv2 : v ≤ (2:ℝ)^(d*(k₂+1)))
    (ha : a ≤ 2) (hb : b ≤ 2) :
    ((2:ℝ)^(k₁+1) + (2:ℝ)^(d*(k₂+1)) + 1)^A_M * u^a * v^b
      ≤ 4 * (2 + (2:ℝ)^d + 1)^A_M * (2:ℝ)^(2*d)
          * (2:ℝ)^((A_M*d + 2*d + 2) * ((k₁:ℝ)+(k₂:ℝ))) := by
  set G : ℝ := 2 + (2:ℝ)^d + 1 with hGdef
  have hGpos : 0 < G := by rw [hGdef]; positivity
  have hXZnn : (0:ℝ) ≤ (2:ℝ)^(k₁+1) + (2:ℝ)^(d*(k₂+1)) + 1 := by positivity
  have hXZle : (2:ℝ)^(k₁+1) + (2:ℝ)^(d*(k₂+1)) + 1 ≤ G * (2:ℝ)^(d*(k₁+k₂)) := by
    rw [hGdef]
    have h1 : (2:ℝ)^(k₁+1) ≤ 2 * (2:ℝ)^(d*(k₁+k₂)) := by
      rw [pow_succ]
      have hle : (2:ℝ)^k₁ ≤ (2:ℝ)^(d*(k₁+k₂)) := by
        apply pow_le_pow_right₀ (by norm_num)
        calc k₁ ≤ 1 * k₁ := by simp
          _ ≤ d * k₁ := Nat.mul_le_mul_right k₁ hd
          _ ≤ d * (k₁ + k₂) := Nat.mul_le_mul_left d (Nat.le_add_right k₁ k₂)
      calc (2:ℝ)^k₁ * 2 ≤ (2:ℝ)^(d*(k₁+k₂)) * 2 :=
            mul_le_mul_of_nonneg_right hle (by norm_num)
        _ = 2 * (2:ℝ)^(d*(k₁+k₂)) := by ring
    have h2 : (2:ℝ)^(d*(k₂+1)) ≤ (2:ℝ)^d * (2:ℝ)^(d*(k₁+k₂)) := by
      rw [Nat.mul_succ, pow_add]
      have hle : (2:ℝ)^(d*k₂) ≤ (2:ℝ)^(d*(k₁+k₂)) := by
        apply pow_le_pow_right₀ (by norm_num)
        exact Nat.mul_le_mul_left d (Nat.le_add_left k₂ k₁)
      calc (2:ℝ)^(d*k₂) * (2:ℝ)^d ≤ (2:ℝ)^(d*(k₁+k₂)) * (2:ℝ)^d :=
            mul_le_mul_of_nonneg_right hle (by positivity)
        _ = (2:ℝ)^d * (2:ℝ)^(d*(k₁+k₂)) := by ring
    have h3 : (1:ℝ) ≤ (2:ℝ)^(d*(k₁+k₂)) := one_le_pow₀ (by norm_num)
    nlinarith [h1, h2, h3]
  have hXZpow : ((2:ℝ)^(k₁+1) + (2:ℝ)^(d*(k₂+1)) + 1)^A_M
      ≤ G^A_M * (2:ℝ)^(A_M * ((d*(k₁+k₂) : ℕ) : ℝ)) := by
    calc ((2:ℝ)^(k₁+1) + (2:ℝ)^(d*(k₂+1)) + 1)^A_M
        ≤ (G * (2:ℝ)^(d*(k₁+k₂)))^A_M := Real.rpow_le_rpow hXZnn hXZle hA_M
      _ = G^A_M * ((2:ℝ)^(d*(k₁+k₂)))^A_M := Real.mul_rpow hGpos.le (by positivity)
      _ = G^A_M * (2:ℝ)^(A_M * ((d*(k₁+k₂) : ℕ) : ℝ)) := by
            rw [← Real.rpow_natCast (2:ℝ) (d*(k₁+k₂)),
              ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
            rw [mul_comm (((d*(k₁+k₂) : ℕ) : ℝ)) A_M]
  have hup : u^a ≤ 4 * (2:ℝ)^(2*k₁) := by
    have h1 : u^a ≤ ((2:ℝ)^(k₁+1))^a := pow_le_pow_left₀ hu hu2 a
    have h2 : ((2:ℝ)^(k₁+1))^a = (2:ℝ)^((k₁+1)*a) := by rw [pow_mul]
    have h3 : (k₁+1)*a ≤ (k₁+1)*2 := Nat.mul_le_mul_left _ ha
    have h4 : (2:ℝ)^((k₁+1)*a) ≤ (2:ℝ)^((k₁+1)*2) := pow_le_pow_right₀ (by norm_num) h3
    have h5 : (2:ℝ)^((k₁+1)*2) = 4 * (2:ℝ)^(2*k₁) := by
      have h6 : (k₁+1)*2 = 2*k₁ + 2 := by ring
      rw [h6, pow_add]
      ring
    calc u^a ≤ ((2:ℝ)^(k₁+1))^a := h1
      _ = (2:ℝ)^((k₁+1)*a) := h2
      _ ≤ (2:ℝ)^((k₁+1)*2) := h4
      _ = 4 * (2:ℝ)^(2*k₁) := h5
  have hvp : v^b ≤ (2:ℝ)^(2*d) * (2:ℝ)^(2*d*k₂) := by
    have h1 : v^b ≤ ((2:ℝ)^(d*(k₂+1)))^b := pow_le_pow_left₀ hv hv2 b
    have h2 : ((2:ℝ)^(d*(k₂+1)))^b = (2:ℝ)^((d*(k₂+1))*b) := by rw [← pow_mul]
    have h3 : (d*(k₂+1))*b ≤ (d*(k₂+1))*2 := Nat.mul_le_mul_left _ hb
    have h4 : (2:ℝ)^((d*(k₂+1))*b) ≤ (2:ℝ)^((d*(k₂+1))*2) := pow_le_pow_right₀ (by norm_num) h3
    have h5 : (2:ℝ)^((d*(k₂+1))*2) = (2:ℝ)^(2*d) * (2:ℝ)^(2*d*k₂) := by
      have h6 : (d*(k₂+1))*2 = 2*d + 2*d*k₂ := by ring
      rw [h6, pow_add]
    calc v^b ≤ ((2:ℝ)^(d*(k₂+1)))^b := h1
      _ = (2:ℝ)^((d*(k₂+1))*b) := h2
      _ ≤ (2:ℝ)^((d*(k₂+1))*2) := h4
      _ = (2:ℝ)^(2*d) * (2:ℝ)^(2*d*k₂) := h5
  -- rewrite the two finite bounds with real exponents
  have hupR : u^a ≤ 4 * (2:ℝ)^((2*k₁ : ℕ) : ℝ) := by
    rw [Real.rpow_natCast]; exact hup
  have hvpR : v^b ≤ (2:ℝ)^((2*d : ℕ) : ℝ) * (2:ℝ)^((2*d*k₂ : ℕ) : ℝ) := by
    rw [Real.rpow_natCast, Real.rpow_natCast]; exact hvp
  -- the exponent comparison
  have hexp : A_M * ((d*(k₁+k₂) : ℕ) : ℝ) + ((2*k₁ : ℕ) : ℝ) + ((2*d*k₂ : ℕ) : ℝ)
      ≤ (A_M*↑d + 2*↑d + 2) * (↑k₁ + ↑k₂) := by
    have hdR : (1:ℝ) ≤ d := by exact_mod_cast hd
    have hk1 : (0:ℝ) ≤ k₁ := Nat.cast_nonneg _
    have hk2 : (0:ℝ) ≤ k₂ := Nat.cast_nonneg _
    have hkey : (A_M*↑d + 2*↑d + 2) * (↑k₁ + ↑k₂)
        - (A_M * ((d*(k₁+k₂) : ℕ) : ℝ) + ((2*k₁ : ℕ) : ℝ) + ((2*d*k₂ : ℕ) : ℝ))
        = 2*↑d*↑k₁ + 2*↑k₂ := by push_cast; ring
    nlinarith [hkey, hdR, hk1, hk2]
  have hcomb : (2:ℝ)^(A_M * ((d*(k₁+k₂) : ℕ) : ℝ)) * (2:ℝ)^((2*k₁ : ℕ) : ℝ)
        * (2:ℝ)^((2*d*k₂ : ℕ) : ℝ)
      ≤ (2:ℝ)^((A_M*↑d + 2*↑d + 2) * (↑k₁ + ↑k₂)) := by
    rw [two_rpow_mul_three]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hexp
  have hb1 : ((2:ℝ)^(k₁+1) + (2:ℝ)^(d*(k₂+1)) + 1)^A_M * u^a
      ≤ (G^A_M * (2:ℝ)^(A_M * ((d*(k₁+k₂) : ℕ) : ℝ))) * (4 * (2:ℝ)^((2*k₁ : ℕ) : ℝ)) :=
    mul_le_mul hXZpow hupR (by positivity) (by positivity)
  calc ((2:ℝ)^(k₁+1) + (2:ℝ)^(d*(k₂+1)) + 1)^A_M * u^a * v^b
      = (((2:ℝ)^(k₁+1) + (2:ℝ)^(d*(k₂+1)) + 1)^A_M * u^a) * v^b := rfl
    _ ≤ ((G^A_M * (2:ℝ)^(A_M * ((d*(k₁+k₂) : ℕ) : ℝ))) * (4 * (2:ℝ)^((2*k₁ : ℕ) : ℝ)))
          * ((2:ℝ)^((2*d : ℕ) : ℝ) * (2:ℝ)^((2*d*k₂ : ℕ) : ℝ)) :=
        mul_le_mul hb1 hvpR (by positivity) (by positivity)
    _ = 4 * (2:ℝ)^((2*d : ℕ) : ℝ) * G^A_M
          * ((2:ℝ)^(A_M * ((d*(k₁+k₂) : ℕ) : ℝ)) * (2:ℝ)^((2*k₁ : ℕ) : ℝ)
              * (2:ℝ)^((2*d*k₂ : ℕ) : ℝ)) := by ring
    _ ≤ 4 * (2:ℝ)^((2*d : ℕ) : ℝ) * G^A_M
          * (2:ℝ)^((A_M*↑d + 2*↑d + 2) * (↑k₁ + ↑k₂)) :=
        mul_le_mul_of_nonneg_left hcomb (by positivity)
    _ = 4 * (2 + (2:ℝ)^d + 1)^A_M * (2:ℝ)^(2*d)
          * (2:ℝ)^((A_M*↑d + 2*↑d + 2) * (↑k₁ + ↑k₂)) := by
        rw [← hGdef, Real.rpow_natCast]
        ring

private lemma two_rpow_mono {a b : ℝ} (h : a ≤ b) : (2 : ℝ) ^ a ≤ (2 : ℝ) ^ b :=
  (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr h

private lemma spikeXZ_le (P : Polynomial ℤ) (hd1 : 1 ≤ P.natDegree) (k₁ k₂ : ℕ) :
    (2 : ℝ) ^ (k₁ + 1) + (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) + 1
      ≤ (2 + (2 : ℝ) ^ P.natDegree + 1) * (2 : ℝ) ^ (P.natDegree * (k₁ + k₂)) := by
  have h1 : (2 : ℝ) ^ (k₁ + 1) ≤ 2 * (2 : ℝ) ^ (P.natDegree * (k₁ + k₂)) := by
    rw [pow_succ]
    calc (2 : ℝ) ^ k₁ * 2 ≤ (2 : ℝ) ^ (P.natDegree * (k₁ + k₂)) * 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
          refine pow_le_pow_right₀ (by norm_num) ?_
          have hka : k₁ ≤ P.natDegree * k₁ := Nat.le_mul_of_pos_left k₁ (by omega)
          have hkb : 0 ≤ P.natDegree * k₂ := Nat.zero_le _
          have hkeq : P.natDegree * (k₁ + k₂) = P.natDegree * k₁ + P.natDegree * k₂ := by ring
          omega
      _ = 2 * (2 : ℝ) ^ (P.natDegree * (k₁ + k₂)) := by ring
  have h2 : (2 : ℝ) ^ (P.natDegree * (k₂ + 1))
      ≤ (2 : ℝ) ^ P.natDegree * (2 : ℝ) ^ (P.natDegree * (k₁ + k₂)) := by
    rw [Nat.mul_succ, pow_add]
    calc (2 : ℝ) ^ (P.natDegree * k₂) * (2 : ℝ) ^ P.natDegree
        ≤ (2 : ℝ) ^ (P.natDegree * (k₁ + k₂)) * (2 : ℝ) ^ P.natDegree := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ P.natDegree)
          refine pow_le_pow_right₀ (by norm_num) ?_
          exact Nat.mul_le_mul_left _ (Nat.le_add_left _ _)
      _ = (2 : ℝ) ^ P.natDegree * (2 : ℝ) ^ (P.natDegree * (k₁ + k₂)) := by ring
  have h3 : (1 : ℝ) ≤ 1 * (2 : ℝ) ^ (P.natDegree * (k₁ + k₂)) := by
    have h : (1 : ℝ) ≤ (2 : ℝ) ^ (P.natDegree * (k₁ + k₂)) := by
      rw [← Real.rpow_natCast (2 : ℝ) (P.natDegree * (k₁ + k₂))]
      exact Real.one_le_rpow (by norm_num) (by positivity)
    linarith
  linarith [h1, h2, h3]

private theorem spikeProfile_estimates (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree)
    {Cφ Cψ : ℝ} (hCφ : 0 < Cφ) (hCψ : 0 < Cψ)
    (hφb : ∀ (N k j : ℕ), j ≤ 2 → ∀ x : ℝ,
      ‖iteratedDeriv j (varphiN N k) x‖
        ≤ Cφ / (2 : ℝ) ^ ((j : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))))
    (hψb : ∀ (N k j : ℕ), j ≤ 2 → ∀ x : ℝ,
      ‖iteratedDeriv j (varphitildeN P.natDegree N k) x‖
        ≤ Cψ / (2 : ℝ) ^ ((j : ℝ) * ((P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))))
    (hswap : ∀ (g : ℝ → ℝ → ℂ), ContDiff ℝ 4 (fun p : ℝ × ℝ => g p.1 p.2) → ∀ x y : ℝ,
      dp2 2 (dp1 2 g) x y = dp 2 2 g x y)
    (harith : ∀ (d k₁ k₂ a b : ℕ), 1 ≤ d → ∀ {A_M u v : ℝ}, 0 ≤ A_M → 0 ≤ u → 0 ≤ v →
      u ≤ (2 : ℝ) ^ (k₁ + 1) → v ≤ (2 : ℝ) ^ (d * (k₂ + 1)) → a ≤ 2 → b ≤ 2 →
      ((2 : ℝ) ^ (k₁ + 1) + (2 : ℝ) ^ (d * (k₂ + 1)) + 1) ^ A_M * u ^ a * v ^ b
        ≤ 4 * (2 + (2 : ℝ) ^ d + 1) ^ A_M * (2 : ℝ) ^ (2 * d)
            * (2 : ℝ) ^ ((A_M * d + 2 * d + 2) * ((k₁ : ℝ) + (k₂ : ℝ)))) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ (N k₁ k₂ q : ℕ) (β₁ β₂ : Work.Analysis.IonescuWainger.Circle),
        1 ≤ N → 1 ≤ q → q • β₁ = 0 → q • β₂ = 0 →
        ContDiff ℝ 4 (fun p : ℝ × ℝ => spikeProfile P N k₁ k₂ q β₁ β₂ p.1 p.2) ∧
        (∀ x₁ x₂ : ℝ, spikeProfile P N k₁ k₂ q β₁ β₂ x₁ x₂ ≠ 0 →
          |x₁| ≤ (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) ∧
          |x₂| ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) ∧
        (∀ x₁ x₂ : ℝ, ‖spikeProfile P N k₁ k₂ q β₁ β₂ x₁ x₂‖
          ≤ C * (q : ℝ) * (2 : ℝ) ^ (A * ((k₁ : ℝ) + (k₂ : ℝ))) / (N : ℝ)) ∧
        (∀ x₁ x₂ : ℝ, ‖iteratedDeriv 2 (fun y : ℝ => spikeProfile P N k₁ k₂ q β₁ β₂ y x₂) x₁‖
          ≤ C * (q : ℝ) * (2 : ℝ) ^ (A * ((k₁ : ℝ) + (k₂ : ℝ))) / (N : ℝ)
              / ((2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) ^ 2) ∧
        (∀ x₁ x₂ : ℝ, ‖iteratedDeriv 2 (fun y : ℝ => spikeProfile P N k₁ k₂ q β₁ β₂ x₁ y) x₂‖
          ≤ C * (q : ℝ) * (2 : ℝ) ^ (A * ((k₁ : ℝ) + (k₂ : ℝ))) / (N : ℝ)
              / ((2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) ^ 2) ∧
        (∀ x₁ x₂ : ℝ, ‖iteratedDeriv 2 (fun y : ℝ => iteratedDeriv 2 (fun z : ℝ =>
            spikeProfile P N k₁ k₂ q β₁ β₂ z y) x₁) x₂‖
          ≤ C * (q : ℝ) * (2 : ℝ) ^ (A * ((k₁ : ℝ) + (k₂ : ℝ))) / (N : ℝ)
              / (((2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) ^ 2
                * ((2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) ^ 2)) := by
  obtain ⟨C_M, A_M, hC_M, hA_M, hM0⟩ := M0_iteratedDeriv_bound P hdeg
  have hd1 : 1 ≤ P.natDegree := by omega
  set G : ℝ := 2 + (2 : ℝ) ^ P.natDegree + 1 with hGdef
  have hGpos : 0 < G := by rw [hGdef]; positivity
  set Cs : ℝ := 256 * Cφ * Cψ * C_M * G ^ A_M * (2 : ℝ) ^ (2 * P.natDegree) with hCsdef
  have hCspos : 0 < Cs := by rw [hCsdef]; positivity
  have hAnn : 0 ≤ A_M * (P.natDegree : ℝ) + 2 * (P.natDegree : ℝ) + 2 := by
    have h1 : (0 : ℝ) ≤ (P.natDegree : ℝ) := Nat.cast_nonneg _
    nlinarith [hA_M]
  refine ⟨16 * Cs, A_M * (P.natDegree : ℝ) + 2 * (P.natDegree : ℝ) + 2, by positivity, hAnn, ?_⟩
  intro N k₁ k₂ q β₁ β₂ hN hq hβ₁ hβ₂
  set w₁ : ℝ := (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) with hw₁def
  set w₂ : ℝ := (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) with hw₂def
  have hw₁pos : 0 < w₁ := by rw [hw₁def]; positivity
  have hw₂pos : 0 < w₂ := by rw [hw₂def]; positivity
  set XZ : ℝ := (2 : ℝ) ^ (k₁ + 1) + (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) + 1 with hXZdef
  have hXZnn : 0 ≤ XZ := by rw [hXZdef]; positivity
  have hXZpos : 0 < XZ := by rw [hXZdef]; positivity
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hqnn : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  set E : ℝ := (A_M * (P.natDegree : ℝ) + 2 * (P.natDegree : ℝ) + 2) * ((k₁ : ℝ) + (k₂ : ℝ)) with hEdef
  have hw₁pow : ∀ j : ℕ, w₁ ^ j = (2 : ℝ) ^ ((j : ℝ) * ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := by
    intro j
    rw [hw₁def, ← Real.rpow_natCast ((2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) j,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hw₂pow : ∀ j : ℕ, w₂ ^ j
      = (2 : ℝ) ^ ((j : ℝ) * ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) := by
    intro j
    rw [hw₂def, ← Real.rpow_natCast ((2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) j,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hsuppφ : ∀ (j : ℕ) (x : ℝ), iteratedDeriv j (varphiN N k₁) x ≠ 0 → |x| ≤ w₁ := by
    intro j x hx
    by_contra hlt
    have hlt' : (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) < |x| := by
      rw [hw₁def] at hlt
      exact not_le.mp hlt
    exact hx (SpikeToolbox.iteratedDeriv_varphiN_eq_zero_of_radius N k₁ j hlt')
  have hsuppψ : ∀ (j : ℕ) (x : ℝ), iteratedDeriv j (varphitildeN P.natDegree N k₂) x ≠ 0 → |x| ≤ w₂ := by
    intro j x hx
    by_contra hlt
    have hlt' : (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) < |x| := by
      rw [hw₂def] at hlt
      exact not_le.mp hlt
    exact hx (SpikeToolbox.iteratedDeriv_varphitildeN_eq_zero_of_radius P.natDegree N k₂ j hd1 hlt')
  have hfreq₁ : ∀ {x : ℝ}, |x| ≤ w₁ → |x| ≤ (2 : ℝ) ^ (k₁ + 1) / (N : ℝ) := by
    intro x hx
    have h : |x| ≤ (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by
      rwa [hw₁def] at hx
    exact SpikeToolbox.le_pow_div_of_abs_le hN h
  have hfreq₂ : ∀ {x : ℝ}, |x| ≤ w₂ → |x| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree := by
    intro x hx
    have h : |x| ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := by
      rwa [hw₂def] at hx
    exact SpikeToolbox.le_pow_div_pow_of_abs_le hN h
  have hMb : ∀ (j₁ j₂ : ℕ), j₁ ≤ 2 → j₂ ≤ 2 → ∀ ξ₁ ξ₂ : ℝ,
      |ξ₁| ≤ (2 : ℝ) ^ (k₁ + 1) / (N : ℝ) →
      |ξ₂| ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) / (N : ℝ) ^ P.natDegree →
      ‖dp j₁ j₂ (fun a b => M0 P N q β₁ β₂ a b) ξ₁ ξ₂‖
        ≤ C_M * XZ ^ A_M * (q : ℝ) * ((N : ℝ) ^ j₁ * (N : ℝ) ^ (P.natDegree * j₂)) / (N : ℝ) := by
    intro j₁ j₂ hj₁ hj₂ ξ₁ ξ₂ hξ₁ hξ₂
    have h := hM0 N q (k₁ + 1) (k₂ + 1) β₁ β₂ ξ₁ ξ₂ j₁ j₂ hN hq hβ₁ hβ₂ hj₁ hj₂ hξ₁ hξ₂
    rw [hXZdef]
    simpa [dp, dp1, dp2] using h
  have hXZpow : XZ ^ A_M ≤ G ^ A_M * (2 : ℝ) ^ (A_M * ((P.natDegree : ℝ) * ((k₁ : ℝ) + (k₂ : ℝ)))) := by
    have hle := spikeXZ_le P hd1 k₁ k₂
    calc XZ ^ A_M ≤ (G * (2 : ℝ) ^ (P.natDegree * (k₁ + k₂))) ^ A_M := by
          refine Real.rpow_le_rpow hXZnn ?_ hA_M
          rw [hXZdef]
          exact hle
      _ = G ^ A_M * ((2 : ℝ) ^ (P.natDegree * (k₁ + k₂))) ^ A_M :=
          Real.mul_rpow hGpos.le (by positivity)
      _ = G ^ A_M * (2 : ℝ) ^ (A_M * ((P.natDegree : ℝ) * ((k₁ : ℝ) + (k₂ : ℝ)))) := by
          rw [← Real.rpow_natCast (2 : ℝ) (P.natDegree * (k₁ + k₂)),
            ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
          congr 1
          push_cast
          ring_nf
  have hXZ_E : XZ ^ A_M ≤ G ^ A_M * (2 : ℝ) ^ E := by
    refine hXZpow.trans (mul_le_mul_of_nonneg_left ?_ (le_of_lt (by positivity : (0 : ℝ) < G ^ A_M)))
    refine two_rpow_mono ?_
    rw [hEdef]
    have hkk : (0 : ℝ) ≤ (k₁ : ℝ) + (k₂ : ℝ) := by positivity
    have hdR : (0 : ℝ) ≤ (P.natDegree : ℝ) := Nat.cast_nonneg _
    nlinarith [hA_M, hkk, hdR]
  -- the support radius in the `X/N` normalisation
  have hNw₁ : (N : ℝ) * w₁ ≤ (2 : ℝ) ^ (k₁ + 1) := by
    have h : |w₁| ≤ (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := by
      rw [abs_of_pos hw₁pos, hw₁def]
    have h2 := SpikeToolbox.le_pow_div_of_abs_le hN h
    rw [le_div_iff₀ hNpos] at h2
    rw [abs_of_pos hw₁pos] at h2
    linarith [h2]
  have hNw₂ : ((N : ℝ) ^ P.natDegree) * w₂ ≤ (2 : ℝ) ^ (P.natDegree * (k₂ + 1)) := by
    have h : |w₂| ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := by
      rw [abs_of_pos hw₂pos, hw₂def]
    have h2 := SpikeToolbox.le_pow_div_pow_of_abs_le hN h
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) ^ P.natDegree)] at h2
    rw [abs_of_pos hw₂pos] at h2
    linarith [h2]
  -- smoothness of the profile
  have hcd4 : ContDiff ℝ 4 (fun p : ℝ × ℝ => spikeProfile P N k₁ k₂ q β₁ β₂ p.1 p.2) := by
    have h1 : ContDiff ℝ 4 (fun p : ℝ × ℝ => varphiN N k₁ p.1) :=
      (Work.KMTPlan.A6.contDiff4_varphiN N k₁).comp contDiff_fst
    have h2 : ContDiff ℝ 4 (fun p : ℝ × ℝ => varphitildeN P.natDegree N k₂ p.2) :=
      (Work.KMTPlan.A6.contDiff4_varphitildeN P.natDegree N k₂).comp contDiff_snd
    have h3 : ContDiff ℝ 4 (fun p : ℝ × ℝ => M0 P N q β₁ β₂ p.1 p.2) :=
      Work.KMTPlan.A6.contDiff4_M0 P N q β₁ β₂
    simpa only [spikeProfile] using (h1.mul h2).mul h3
  -- the general `dp` estimate
  have hgen : ∀ (j₁ j₂ : ℕ), j₁ ≤ 2 → j₂ ≤ 2 → ∀ x₁ x₂ : ℝ,
      ‖dp j₁ j₂ (fun a b => spikeProfile P N k₁ k₂ q β₁ β₂ a b) x₁ x₂‖
        ≤ 16 * Cs * (q : ℝ) * (2 : ℝ) ^ E / ((N : ℝ) * (w₁ ^ j₁ * w₂ ^ j₂)) := by
    intro j₁ j₂ hj₁ hj₂ x₁ x₂
    have hσ : (fun a b => spikeProfile P N k₁ k₂ q β₁ β₂ a b)
        = fun a b => M0 P N q β₁ β₂ a b * varphiN N k₁ a * varphitildeN P.natDegree N k₂ b := by
      funext a b
      simp only [spikeProfile]
      ring
    rw [hσ]
    have hexp := SpikeToolbox.dp_finset_sum_mul_three (S := ({()} : Finset Unit))
        (F := fun _ : Unit => fun a b => M0 P N q β₁ β₂ a b)
        (φ := fun _ : Unit => varphiN N k₁)
        (ψ := fun _ : Unit => varphitildeN P.natDegree N k₂)
        j₁ j₂ hj₁ hj₂ x₂ x₁
        (fun k hk a => SpikeToolbox.M0_contDiff_two_snd P N q β₁ β₂ a)
        (fun k hk i₂ hi₂ => by
          have hfun : (fun a : ℝ => iteratedDeriv i₂ (fun b : ℝ => M0 P N q β₁ β₂ a b) x₂)
              = fun a : ℝ => M0deriv P N q β₁ β₂ a x₂ 0 i₂ := by
            funext a
            rw [SpikeToolbox.iteratedDeriv_M0_snd P N q β₁ β₂ a i₂]
          rw [hfun]
          exact SpikeToolbox.M0deriv_contDiff_two_fst P N q β₁ β₂ x₂ 0 i₂)
        (fun k hk => contDiff_varphiN N k₁)
        (fun k hk => contDiff_varphitildeN P.natDegree N k₂)
    simp only [Finset.sum_singleton, Finset.mem_singleton] at hexp
    rw [hexp]
    have hYnn : (0 : ℝ) ≤ Cs * (q : ℝ) * (2 : ℝ) ^ E / ((N : ℝ) * (w₁ ^ j₁ * w₂ ^ j₂)) := by positivity
    have hterm : ∀ (i₂ : ℕ), i₂ ∈ Finset.range (j₂ + 1) → ∀ (i₁ : ℕ), i₁ ∈ Finset.range (j₁ + 1) →
        ‖(↑(j₂.choose i₂) * ↑(j₁.choose i₁) : ℂ) * iteratedDeriv i₁ (varphiN N k₁) x₁
          * iteratedDeriv (j₁ - i₁) (fun a => iteratedDeriv i₂ (fun b => M0 P N q β₁ β₂ a b) x₂) x₁
          * iteratedDeriv (j₂ - i₂) (varphitildeN P.natDegree N k₂) x₂‖
          ≤ Cs * (q : ℝ) * (2 : ℝ) ^ E / ((N : ℝ) * (w₁ ^ j₁ * w₂ ^ j₂)) := by
      intro i₂ hi₂ i₁ hi₁
      have hi₁' : i₁ ≤ j₁ := by have := Finset.mem_range.mp hi₁; omega
      have hi₂' : i₂ ≤ j₂ := by have := Finset.mem_range.mp hi₂; omega
      by_cases hz₁ : iteratedDeriv i₁ (varphiN N k₁) x₁ = 0
      · have hzero : ‖(↑(j₂.choose i₂) * ↑(j₁.choose i₁) : ℂ) * iteratedDeriv i₁ (varphiN N k₁) x₁
            * iteratedDeriv (j₁ - i₁) (fun a => iteratedDeriv i₂ (fun b => M0 P N q β₁ β₂ a b) x₂) x₁
            * iteratedDeriv (j₂ - i₂) (varphitildeN P.natDegree N k₂) x₂‖ = 0 := by
          rw [hz₁]
          simp
        rw [hzero]
        exact hYnn
      by_cases hz₂ : iteratedDeriv (j₂ - i₂) (varphitildeN P.natDegree N k₂) x₂ = 0
      · have hzero : ‖(↑(j₂.choose i₂) * ↑(j₁.choose i₁) : ℂ) * iteratedDeriv i₁ (varphiN N k₁) x₁
            * iteratedDeriv (j₁ - i₁) (fun a => iteratedDeriv i₂ (fun b => M0 P N q β₁ β₂ a b) x₂) x₁
            * iteratedDeriv (j₂ - i₂) (varphitildeN P.natDegree N k₂) x₂‖ = 0 := by
          rw [hz₂]
          simp
        rw [hzero]
        exact hYnn
      have hφx : ‖iteratedDeriv i₁ (varphiN N k₁) x₁‖ ≤ Cφ / w₁ ^ i₁ := by
        rw [hw₁pow i₁]
        exact hφb N k₁ i₁ (le_trans hi₁' hj₁) x₁
      have hψx : ‖iteratedDeriv (j₂ - i₂) (varphitildeN P.natDegree N k₂) x₂‖ ≤ Cψ / w₂ ^ (j₂ - i₂) := by
        rw [hw₂pow (j₂ - i₂)]
        exact hψb N k₂ (j₂ - i₂) (by omega) x₂
      have hMx : ‖iteratedDeriv (j₁ - i₁)
            (fun a => iteratedDeriv i₂ (fun b => M0 P N q β₁ β₂ a b) x₂) x₁‖
          ≤ C_M * XZ ^ A_M * (q : ℝ) * ((N : ℝ) ^ (j₁ - i₁) * (N : ℝ) ^ (P.natDegree * i₂)) / (N : ℝ) := by
        have hMz : iteratedDeriv (j₁ - i₁)
              (fun a => iteratedDeriv i₂ (fun b => M0 P N q β₁ β₂ a b) x₂) x₁
            = dp (j₁ - i₁) i₂ (fun a b => M0 P N q β₁ β₂ a b) x₁ x₂ := rfl
        rw [hMz]
        exact hMb (j₁ - i₁) i₂ (by omega) (by omega) x₁ x₂
          (hfreq₁ (hsuppφ i₁ x₁ hz₁)) (hfreq₂ (hsuppψ (j₂ - i₂) x₂ hz₂))
      have hbin : ‖(↑(j₂.choose i₂) * ↑(j₁.choose i₁) : ℂ)‖ ≤ 16 := by
        rw [norm_mul, Complex.norm_natCast, Complex.norm_natCast]
        have h1' : ((j₂.choose i₂ : ℕ) : ℝ) ≤ 4 := SpikeToolbox.choose_le_four hj₂
        have h2' : ((j₁.choose i₁ : ℕ) : ℝ) ≤ 4 := SpikeToolbox.choose_le_four hj₁
        nlinarith [Nat.cast_nonneg (α := ℝ) (j₂.choose i₂), Nat.cast_nonneg (α := ℝ) (j₁.choose i₁)]
      have hstep1 : ‖(↑(j₂.choose i₂) * ↑(j₁.choose i₁) : ℂ) * iteratedDeriv i₁ (varphiN N k₁) x₁
            * iteratedDeriv (j₁ - i₁) (fun a => iteratedDeriv i₂ (fun b => M0 P N q β₁ β₂ a b) x₂) x₁
            * iteratedDeriv (j₂ - i₂) (varphitildeN P.natDegree N k₂) x₂‖
          ≤ 16 * (Cφ / w₁ ^ i₁) * (C_M * XZ ^ A_M * (q : ℝ)
              * ((N : ℝ) ^ (j₁ - i₁) * (N : ℝ) ^ (P.natDegree * i₂)) / (N : ℝ))
            * (Cψ / w₂ ^ (j₂ - i₂)) := by
        rw [norm_mul, norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul (mul_le_mul hbin hφx (norm_nonneg _)
          (by norm_num : (0 : ℝ) ≤ 16)) hMx (norm_nonneg _)
            (by positivity : (0 : ℝ) ≤ 16 * (Cφ / w₁ ^ i₁))) hψx (norm_nonneg _)
          (by positivity : (0 : ℝ) ≤ 16 * (Cφ / w₁ ^ i₁) * (C_M * XZ ^ A_M * (q : ℝ)
              * ((N : ℝ) ^ (j₁ - i₁) * (N : ℝ) ^ (P.natDegree * i₂)) / (N : ℝ)))
      have hcore : XZ ^ A_M * ((N : ℝ) * w₁) ^ (j₁ - i₁) * (((N : ℝ) ^ P.natDegree) * w₂) ^ i₂
          ≤ 4 * G ^ A_M * (2 : ℝ) ^ (2 * P.natDegree) * (2 : ℝ) ^ E := by
        have h := harith P.natDegree k₁ k₂ (j₁ - i₁) i₂ hd1 (A_M := A_M) (u := (N : ℝ) * w₁)
          (v := ((N : ℝ) ^ P.natDegree) * w₂) hA_M
          (by positivity : (0 : ℝ) ≤ (N : ℝ) * w₁)
          (by positivity : (0 : ℝ) ≤ ((N : ℝ) ^ P.natDegree) * w₂)
          hNw₁ hNw₂ (by omega) (by omega)
        rw [hXZdef, hGdef, hEdef]
        exact h
      have hcore16 : 16 * Cφ * Cψ * C_M * XZ ^ A_M * ((N : ℝ) * w₁) ^ (j₁ - i₁)
            * (((N : ℝ) ^ P.natDegree) * w₂) ^ i₂ ≤ Cs * (2 : ℝ) ^ E := by
        have h := mul_le_mul_of_nonneg_left hcore (by positivity : (0 : ℝ) ≤ 16 * Cφ * Cψ * C_M)
        rw [hCsdef]
        nlinarith [h, hCφ.le, hCψ.le, hC_M.le, (by positivity : (0 : ℝ) ≤ G ^ A_M),
          (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * P.natDegree)),
          (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ E)]
      have hgoal : 16 * (Cφ / w₁ ^ i₁) * (C_M * XZ ^ A_M * (q : ℝ)
              * ((N : ℝ) ^ (j₁ - i₁) * (N : ℝ) ^ (P.natDegree * i₂)) / (N : ℝ))
            * (Cψ / w₂ ^ (j₂ - i₂))
          ≤ Cs * (q : ℝ) * (2 : ℝ) ^ E / ((N : ℝ) * (w₁ ^ j₁ * w₂ ^ j₂)) := by
        have hDpos : (0 : ℝ) < (N : ℝ) * (w₁ ^ j₁ * w₂ ^ j₂) := by positivity
        refine le_of_mul_le_mul_right ?_ hDpos
        have hR : (Cs * (q : ℝ) * (2 : ℝ) ^ E / ((N : ℝ) * (w₁ ^ j₁ * w₂ ^ j₂)))
            * ((N : ℝ) * (w₁ ^ j₁ * w₂ ^ j₂)) = Cs * (q : ℝ) * (2 : ℝ) ^ E := by
          rw [div_mul_cancel₀]
          positivity
        rw [hR]
        have hL : 16 * (Cφ / w₁ ^ i₁) * (C_M * XZ ^ A_M * (q : ℝ)
                * ((N : ℝ) ^ (j₁ - i₁) * (N : ℝ) ^ (P.natDegree * i₂)) / (N : ℝ))
              * (Cψ / w₂ ^ (j₂ - i₂)) * ((N : ℝ) * (w₁ ^ j₁ * w₂ ^ j₂))
            = 16 * Cφ * Cψ * C_M * XZ ^ A_M * (q : ℝ) * ((N : ℝ) * w₁) ^ (j₁ - i₁)
              * (((N : ℝ) ^ P.natDegree) * w₂) ^ i₂ := by
          have hsplit₁ : w₁ ^ j₁ = w₁ ^ (j₁ - i₁) * w₁ ^ i₁ := by
            rw [← pow_add, Nat.sub_add_cancel hi₁']
          have hsplit₂ : w₂ ^ j₂ = w₂ ^ (j₂ - i₂) * w₂ ^ i₂ := by
            rw [← pow_add, Nat.sub_add_cancel hi₂']
          have hw₁ne : w₁ ^ i₁ ≠ 0 := pow_ne_zero _ (ne_of_gt hw₁pos)
          have hw₂ne : w₂ ^ (j₂ - i₂) ≠ 0 := pow_ne_zero _ (ne_of_gt hw₂pos)
          have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
          rw [hsplit₁, hsplit₂, mul_pow, mul_pow, pow_mul]
          first
           | (field_simp; ring)
           | field_simp
        rw [hL]
        have h := mul_le_mul_of_nonneg_right hcore16 hqnn
        linarith [h]
      exact hstep1.trans hgoal
    have hsum1 : ‖∑ i₂ ∈ Finset.range (j₂ + 1), ∑ i₁ ∈ Finset.range (j₁ + 1),
          (↑(j₂.choose i₂) * ↑(j₁.choose i₁) : ℂ) * iteratedDeriv i₁ (varphiN N k₁) x₁
            * iteratedDeriv (j₁ - i₁) (fun a => iteratedDeriv i₂ (fun b => M0 P N q β₁ β₂ a b) x₂) x₁
            * iteratedDeriv (j₂ - i₂) (varphitildeN P.natDegree N k₂) x₂‖
        ≤ ((j₂ + 1) * (j₁ + 1) : ℕ) • (Cs * (q : ℝ) * (2 : ℝ) ^ E / ((N : ℝ) * (w₁ ^ j₁ * w₂ ^ j₂))) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i₂ ∈ Finset.range (j₂ + 1), ‖∑ i₁ ∈ Finset.range (j₁ + 1),
              (↑(j₂.choose i₂) * ↑(j₁.choose i₁) : ℂ) * iteratedDeriv i₁ (varphiN N k₁) x₁
                * iteratedDeriv (j₁ - i₁) (fun a => iteratedDeriv i₂ (fun b => M0 P N q β₁ β₂ a b) x₂) x₁
                * iteratedDeriv (j₂ - i₂) (varphitildeN P.natDegree N k₂) x₂‖
          ≤ ∑ _i₂ ∈ Finset.range (j₂ + 1),
              ∑ _i₁ ∈ Finset.range (j₁ + 1),
              (Cs * (q : ℝ) * (2 : ℝ) ^ E / ((N : ℝ) * (w₁ ^ j₁ * w₂ ^ j₂))) :=
            Finset.sum_le_sum (fun i₂ hi₂ => (norm_sum_le _ _).trans
              (Finset.sum_le_sum (fun i₁ hi₁ => hterm i₂ hi₂ i₁ hi₁)))
        _ = ((j₂ + 1) * (j₁ + 1) : ℕ) • (Cs * (q : ℝ) * (2 : ℝ) ^ E / ((N : ℝ) * (w₁ ^ j₁ * w₂ ^ j₂))) := by
            rw [Finset.sum_const, Finset.card_range]
            rw [Finset.sum_const, Finset.card_range]
            simp only [nsmul_eq_mul]
            push_cast
            ring
    have hsum2 : ((j₂ + 1) * (j₁ + 1) : ℕ) • (Cs * (q : ℝ) * (2 : ℝ) ^ E / ((N : ℝ) * (w₁ ^ j₁ * w₂ ^ j₂)))
        ≤ 16 * Cs * (q : ℝ) * (2 : ℝ) ^ E / ((N : ℝ) * (w₁ ^ j₁ * w₂ ^ j₂)) := by
      rw [nsmul_eq_mul]
      have hcardR : (((j₂ + 1) * (j₁ + 1) : ℕ) : ℝ) ≤ 16 := by
        have hj₁3 : j₁ + 1 ≤ 3 := by omega
        have hj₂3 : j₂ + 1 ≤ 3 := by omega
        have h16 : (j₂ + 1) * (j₁ + 1) ≤ 16 := by
          calc (j₂ + 1) * (j₁ + 1) ≤ 3 * 3 := Nat.mul_le_mul hj₂3 hj₁3
            _ = 9 := by norm_num
            _ ≤ 16 := by norm_num
        exact_mod_cast h16
      refine le_trans (mul_le_mul_of_nonneg_right hcardR hYnn) (le_of_eq ?_)
      rw [← mul_div_assoc]
      ring
    exact hsum1.trans hsum2
  refine ⟨hcd4, ?_, ?_, ?_, ?_, ?_⟩
  · intro x₁ x₂ hne
    have h1 : varphiN N k₁ x₁ ≠ 0 := by
      intro h0
      exact hne (by simp only [spikeProfile, h0, zero_mul])
    have h2 : varphitildeN P.natDegree N k₂ x₂ ≠ 0 := by
      intro h0
      exact hne (by simp only [spikeProfile, h0, mul_zero, zero_mul])
    exact ⟨varphiN_support N k₁ x₁ h1, SpikeToolbox.varphitildeN_ne_zero_abs_le P.natDegree N k₂ hd1 h2⟩
  · intro x₁ x₂
    by_cases h1 : varphiN N k₁ x₁ = 0
    · rw [spikeProfile, h1, zero_mul, zero_mul, norm_zero]
      have : (0 : ℝ) ≤ 16 * Cs * (q : ℝ) * (2 : ℝ) ^ E / (N : ℝ) := by positivity
      exact this
    by_cases h2 : varphitildeN P.natDegree N k₂ x₂ = 0
    · rw [spikeProfile, h2, mul_zero, zero_mul, norm_zero]
      have : (0 : ℝ) ≤ 16 * Cs * (q : ℝ) * (2 : ℝ) ^ E / (N : ℝ) := by positivity
      exact this
    have hφ0 : ‖varphiN N k₁ x₁‖ ≤ Cφ := by
      have h := hφb N k₁ 0 (by norm_num) x₁
      rw [iteratedDeriv_zero] at h
      simpa using h
    have hψ0 : ‖varphitildeN P.natDegree N k₂ x₂‖ ≤ Cψ := by
      have h := hψb N k₂ 0 (by norm_num) x₂
      rw [iteratedDeriv_zero] at h
      simpa using h
    have hs1 : |x₁| ≤ (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) := varphiN_support N k₁ x₁ h1
    have hs2 : |x₂| ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) :=
      SpikeToolbox.varphitildeN_ne_zero_abs_le P.natDegree N k₂ hd1 h2
    have hM00 : ‖M0 P N q β₁ β₂ x₁ x₂‖ ≤ C_M * XZ ^ A_M * (q : ℝ) / (N : ℝ) := by
      have h := hMb 0 0 (by norm_num) (by norm_num) x₁ x₂ (hfreq₁ hs1) (hfreq₂ hs2)
      have h' : (N : ℝ) ^ (0 : ℕ) * (N : ℝ) ^ (P.natDegree * 0) = 1 := by simp
      simpa [dp, dp1, dp2, iteratedDeriv_zero, h'] using h
    have hstep : ‖spikeProfile P N k₁ k₂ q β₁ β₂ x₁ x₂‖
        ≤ Cφ * Cψ * (C_M * XZ ^ A_M * (q : ℝ) / (N : ℝ)) := by
      calc ‖spikeProfile P N k₁ k₂ q β₁ β₂ x₁ x₂‖
          = ‖varphiN N k₁ x₁‖ * ‖varphitildeN P.natDegree N k₂ x₂‖ * ‖M0 P N q β₁ β₂ x₁ x₂‖ := by
              rw [spikeProfile, norm_mul, norm_mul]
        _ ≤ Cφ * Cψ * (C_M * XZ ^ A_M * (q : ℝ) / (N : ℝ)) := by
              refine mul_le_mul (mul_le_mul hφ0 hψ0 (norm_nonneg _) hCφ.le) hM00 (norm_nonneg _)
                (by positivity)
    refine hstep.trans ?_
    have h1' : Cφ * Cψ * C_M * XZ ^ A_M ≤ 16 * Cs * (2 : ℝ) ^ E := by
      have h2 : Cφ * Cψ * C_M * XZ ^ A_M ≤ Cφ * Cψ * C_M * (G ^ A_M * (2 : ℝ) ^ E) :=
        mul_le_mul_of_nonneg_left hXZ_E (by positivity)
      have h3 : Cφ * Cψ * C_M * (G ^ A_M * (2 : ℝ) ^ E) ≤ Cs * (2 : ℝ) ^ E := by
        rw [hCsdef]
        have hZ : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * P.natDegree) := by
          rw [← Real.rpow_natCast (2 : ℝ) (2 * P.natDegree)]
          exact Real.one_le_rpow (by norm_num) (by positivity)
        nlinarith [hZ, mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hCφ.le hCψ.le) hC_M.le)
          (le_of_lt (by positivity : (0 : ℝ) < G ^ A_M))) (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ E)]
      have h4 : Cs * (2 : ℝ) ^ E ≤ 16 * Cs * (2 : ℝ) ^ E := by
        have h0 : (0 : ℝ) ≤ Cs * (2 : ℝ) ^ E := mul_nonneg hCspos.le (by positivity)
        nlinarith [h0]
      linarith [h2, h3, h4]
    calc Cφ * Cψ * (C_M * XZ ^ A_M * (q : ℝ) / (N : ℝ))
        = (Cφ * Cψ * C_M * XZ ^ A_M) * ((q : ℝ) / (N : ℝ)) := by ring
      _ ≤ (16 * Cs * (2 : ℝ) ^ E) * ((q : ℝ) / (N : ℝ)) :=
          mul_le_mul_of_nonneg_right h1' (by positivity)
      _ = 16 * Cs * (q : ℝ) * (2 : ℝ) ^ E / (N : ℝ) := by ring
  · intro x₁ x₂
    have h := hgen 2 0 (by norm_num) (by norm_num) x₁ x₂
    have heq : dp 2 0 (fun a b => spikeProfile P N k₁ k₂ q β₁ β₂ a b) x₁ x₂
        = iteratedDeriv 2 (fun y : ℝ => spikeProfile P N k₁ k₂ q β₁ β₂ y x₂) x₁ := by
      simp only [dp, dp1, dp2, iteratedDeriv_zero]
    rw [heq] at h
    simp only [pow_zero, mul_one, one_mul] at h
    refine h.trans (le_of_eq ?_)
    rw [div_div]
  · intro x₁ x₂
    have h := hgen 0 2 (by norm_num) (by norm_num) x₁ x₂
    have heq : dp 0 2 (fun a b => spikeProfile P N k₁ k₂ q β₁ β₂ a b) x₁ x₂
        = iteratedDeriv 2 (fun y : ℝ => spikeProfile P N k₁ k₂ q β₁ β₂ x₁ y) x₂ := by
      simp only [dp, dp1, dp2, iteratedDeriv_zero]
    rw [heq] at h
    simp only [pow_zero, mul_one, one_mul] at h
    refine h.trans (le_of_eq ?_)
    rw [div_div]
  · intro x₁ x₂
    have h := hgen 2 2 (by norm_num) (by norm_num) x₁ x₂
    have heq : dp 2 2 (fun a b => spikeProfile P N k₁ k₂ q β₁ β₂ a b) x₁ x₂
        = iteratedDeriv 2 (fun y : ℝ => iteratedDeriv 2 (fun z : ℝ =>
            spikeProfile P N k₁ k₂ q β₁ β₂ z y) x₁) x₂ := by
      change dp 2 2 (fun a b => spikeProfile P N k₁ k₂ q β₁ β₂ a b) x₁ x₂
        = dp2 2 (dp1 2 (fun a b => spikeProfile P N k₁ k₂ q β₁ β₂ a b)) x₁ x₂
      exact (hswap _ hcd4 x₁ x₂).symm
    rw [← heq]
    refine h.trans (le_of_eq ?_)
    rw [div_div]
/-! ## The uniform bump bound for `φ_N` -/

/-- `φ_N` at the scale `k` is `φ̃_N` with `d = 1`. -/
private lemma varphiN_eq_varphitildeN_one (N k : ℕ) : varphiN N k = varphitildeN 1 N k := by
  unfold varphiN varphitildeN
  by_cases hk : k = 0 <;> simp [hk]

/-- The derivative bound for `φ_N`, uniform in `N` and `k`. -/
private lemma varphiN_deriv_bound_uniform :
    ∃ C : ℝ, 0 < C ∧ ∀ (N k j : ℕ), j ≤ 2 → ∀ x : ℝ,
      ‖iteratedDeriv j (varphiN N k) x‖
        ≤ C / (2 : ℝ) ^ ((j : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := by
  obtain ⟨C, hCpos, hC⟩ := varphitildeN_deriv_unif 1 le_rfl
  refine ⟨C, hCpos, fun N k j hj x => ?_⟩
  rw [varphiN_eq_varphitildeN_one]
  simpa using hC N k j hj x

/-! ## The target -/

theorem spike_profile_bounds_q (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) :
    ∃ C A : ℝ, 0 < C ∧ 0 ≤ A ∧
      ∀ (N k₁ k₂ q : ℕ) (β₁ β₂ : Work.Analysis.IonescuWainger.Circle),
        1 ≤ N → 1 ≤ q → q • β₁ = 0 → q • β₂ = 0 →
        ContDiff ℝ 4 (fun p : ℝ × ℝ => Work.KMTAreas.A7.spikeProfile P N k₁ k₂ q β₁ β₂ p.1 p.2) ∧
        (∀ x₁ x₂ : ℝ, Work.KMTAreas.A7.spikeProfile P N k₁ k₂ q β₁ β₂ x₁ x₂ ≠ 0 →
          |x₁| ≤ (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) ∧
          |x₂| ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) ∧
        (∀ x₁ x₂ : ℝ, ‖Work.KMTAreas.A7.spikeProfile P N k₁ k₂ q β₁ β₂ x₁ x₂‖
          ≤ C * (q : ℝ) * (2 : ℝ) ^ (A * ((k₁ : ℝ) + (k₂ : ℝ))) / (N : ℝ)) ∧
        (∀ x₁ x₂ : ℝ, ‖iteratedDeriv 2 (fun y : ℝ => Work.KMTAreas.A7.spikeProfile P N k₁ k₂ q β₁ β₂ y x₂) x₁‖
          ≤ C * (q : ℝ) * (2 : ℝ) ^ (A * ((k₁ : ℝ) + (k₂ : ℝ))) / (N : ℝ)
              / ((2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) ^ 2) ∧
        (∀ x₁ x₂ : ℝ, ‖iteratedDeriv 2 (fun y : ℝ => Work.KMTAreas.A7.spikeProfile P N k₁ k₂ q β₁ β₂ x₁ y) x₂‖
          ≤ C * (q : ℝ) * (2 : ℝ) ^ (A * ((k₁ : ℝ) + (k₂ : ℝ))) / (N : ℝ)
              / ((2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) ^ 2) ∧
        (∀ x₁ x₂ : ℝ, ‖iteratedDeriv 2 (fun y : ℝ => iteratedDeriv 2 (fun z : ℝ =>
            Work.KMTAreas.A7.spikeProfile P N k₁ k₂ q β₁ β₂ z y) x₁) x₂‖
          ≤ C * (q : ℝ) * (2 : ℝ) ^ (A * ((k₁ : ℝ) + (k₂ : ℝ))) / (N : ℝ)
              / (((2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) ^ 2
                * ((2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))) ^ 2)) := by
  obtain ⟨Cφ, hCφpos, hφb⟩ := varphiN_deriv_bound_uniform
  obtain ⟨Cψ, hCψpos, hψb⟩ := varphitildeN_deriv_unif P.natDegree (by omega)
  exact spikeProfile_estimates P hdeg hCφpos hCψpos hφb hψb
    (fun g hg x y => congrFun (congrFun (spike_dp_comm_two g hg) x) y)
    (fun d k₁ k₂ a b hd {A_M u v} hA_M hu hv hu2 hv2 ha hb =>
      spike_xz_arith d k₁ k₂ a b hd hA_M hu hv hu2 hv2 ha hb)

end

end Work.KMTAreas.A7
