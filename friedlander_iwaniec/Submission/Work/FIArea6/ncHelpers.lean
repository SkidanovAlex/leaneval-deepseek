/-
# `Submission.Work.FIArea6.ncHelpers` — the elementary vocabulary of the coprimality removal

Helpers for `Work.FIArea6.noncoprime_mass_le` (the coprimality removal of (16.4)):

* `ncKb` — the radius of the Gaussian box that contains every `z` with `|z|² ≤ 2N`;
* `ncBox` — the polar box with the (5.8) small-prime condition, i.e. the outer summation index
  of `Work.FIArea6.ncPairCount`;
* `ncGset` — the candidate common divisors `g` of a non-coprime pair, `Pz < |g|² ≤ 2N`;
* the elementary arithmetical facts (`θ ≤ 1`, `log N ≥ 1/4`, `(|g|², 4d) = 1` for a common
  divisor `g` of a (5.8)-free `z`, the box/counting estimates).
-/
import Mathlib
import Submission.Work.FIArea6.S16UDefs
import Submission.Work.FIArea4.polarBox_card_le
import Submission.Work.FIArea6.ncGaussAlg

set_option autoImplicit false

namespace Work.FIArea6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The numerical parameters -/

/-- `θ = (log x)^{-A'} ≤ 1`. -/
lemma ncTheta_le_one (Pa : Work.FITop.Params) : Pa.θ ≤ 1 := by
  have hpx : (0:ℝ) < (Pa.x : ℝ) := by
    have : (3:ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith
  have hx1 : (1:ℝ) ≤ Real.log (Pa.x : ℝ) := by
    rw [Real.le_log_iff_exp_le (y := (Pa.x:ℝ)) hpx]
    have : (3:ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith [Real.exp_one_lt_d9]
  have hA'0 : (0:ℝ) ≤ Pa.A' := by
    have h2 : (0:ℝ) ≤ 2 * Pa.A + (2:ℝ)^(20:ℕ) := by have := Pa.hA; positivity
    linarith [Pa.hA']
  rw [Pa.hθ]
  calc (Real.log (Pa.x:ℝ)) ^ (-Pa.A') = ((Real.log (Pa.x:ℝ)) ^ Pa.A')⁻¹ :=
        Real.rpow_neg (le_trans zero_le_one hx1) _
    _ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_rpow hx1 hA'0)

/-- `1/4 ≤ log N` (from `N > x^{1/4}` and `log x ≥ 1`). -/
lemma ncLogN_ge (Pa : Work.FITop.Params) : (1:ℝ)/4 ≤ Real.log Pa.N := by
  have hpx : (0:ℝ) < (Pa.x : ℝ) := by
    have : (3:ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith
  have hx1 : (1:ℝ) ≤ (Pa.x : ℝ) := by
    have : (3:ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith
  have hle : (Pa.x:ℝ) ^ ((1:ℝ)/4) ≤ Pa.N :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith [Pa.hη])) Pa.hNlo.le
  have h1 : Real.log ((Pa.x:ℝ) ^ ((1:ℝ)/4)) ≤ Real.log Pa.N :=
    Real.log_le_log (Real.rpow_pos_of_pos hpx _) hle
  rw [Real.log_rpow hpx] at h1
  have hlog3 : (1:ℝ) ≤ Real.log (Pa.x:ℝ) := by
    rw [Real.le_log_iff_exp_le (y := (Pa.x:ℝ)) hpx]
    have : (3:ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith [Real.exp_one_lt_d9]
  have h4 : Real.log (Pa.x:ℝ)/4 = (1:ℝ)/4 * Real.log (Pa.x:ℝ) := by ring
  linarith [h1, h4]

/-! ## 2. Gaussian integers of norm `≤ r` live in the box `ncKb` -/

/-- The radius of the Gaussian box containing every `z` with `|z|² ≤ 2N`. -/
def ncKb (Pa : Work.FITop.Params) : ℤ := (⌈Real.sqrt (2 * Pa.N)⌉₊ : ℤ)

/-- `(|z|² : ℤ) = (Re z)² + (Im z)²`. -/
lemma ncGnorm_coords (z : GaussianInt) :
    ((Work.FIPlan.gnorm z : ℕ) : ℤ) = z.re ^ 2 + z.im ^ 2 := by
  have hnorm : z.norm = z.re ^ 2 + z.im ^ 2 := by rw [Zsqrtd.norm_def]; ring
  rw [Work.FIPlan.gnorm, hnorm, Int.natAbs_of_nonneg (by positivity)]

lemma ncMem_gBox (Pa : Work.FITop.Params) {z : GaussianInt} {r : ℝ}
    (hr : ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ r) (hr2 : r ≤ 2 * Pa.N) :
    z ∈ Work.FIPlan.gBox (ncKb Pa) := by
  have hKb : (ncKb Pa : ℝ) = (⌈Real.sqrt (2 * Pa.N)⌉₊ : ℝ) := by simp [ncKb]
  have hle : Real.sqrt (2 * Pa.N) ≤ (ncKb Pa : ℝ) := by
    rw [hKb]; exact Nat.le_ceil _
  have hgn : ∀ w : ℤ, (w = z.re ∨ w = z.im) → |(w:ℝ)| ≤ (ncKb Pa : ℝ) := by
    intro w hw
    have h1 : ((w:ℝ))^2 ≤ ((Work.FIPlan.gnorm z : ℕ) : ℝ) := by
      have hcoords := ncGnorm_coords z
      rcases hw with rfl | rfl
      · have h3 : z.re ^ 2 ≤ (Work.FIPlan.gnorm z : ℤ) := by
          rw [hcoords]; nlinarith [sq_nonneg z.im]
        exact_mod_cast h3
      · have h3 : z.im ^ 2 ≤ (Work.FIPlan.gnorm z : ℤ) := by
          rw [hcoords]; nlinarith [sq_nonneg z.re]
        exact_mod_cast h3
    calc |(w:ℝ)| = Real.sqrt ((w:ℝ)^2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt r := Real.sqrt_le_sqrt (le_trans h1 hr)
      _ ≤ Real.sqrt (2 * Pa.N) := Real.sqrt_le_sqrt hr2
      _ ≤ (ncKb Pa : ℝ) := hle
  rw [Work.FIPlan.gBox, Finset.mem_image]
  refine ⟨(z.re, z.im), Finset.mem_product.mpr ⟨?_, ?_⟩, by cases z; rfl⟩
  · rw [Finset.mem_Icc]
    have h := hgn z.re (Or.inl rfl)
    rw [abs_le] at h
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  · rw [Finset.mem_Icc]
    have h := hgn z.im (Or.inr rfl)
    rw [abs_le] at h
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- A divisor `a` of `|z|²` is coprime to `4d` when `z` is free of primes `≤ Pz ≥ 4d` (5.8). -/
lemma ncCoprime_of_dvd {Pa : Work.FITop.Params} {z : GaussianInt} {a d : ℕ}
    (hz : Work.FITop3.NoSmallPrimes Pa z) (ha : a ∣ Work.FIPlan.gnorm z)
    (hd : 1 ≤ d) (hP : 4 * d ≤ Pa.Pz) :
    Nat.Coprime a (4 * d) := by
  apply Nat.coprime_of_dvd'
  intro k hk hka hk4d
  exfalso
  have hk_le : k ≤ Pa.Pz := le_trans (Nat.le_of_dvd (by omega) hk4d) (by omega)
  exact hz k hk hk_le (dvd_trans hka ha)

/-! ## 3. The polar box (5.14) with the small-prime condition -/

/-- The outer summation index of `ncPairCount`: the polar box with `(z, Π) = 1` (5.8). -/
def ncBox (Pa : Work.FITop.Params) (φ : ℝ) : Finset GaussianInt :=
  (Work.FITop.boxN Pa).filter
    (fun z => Work.FITop3.InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z)

lemma ncBox_spec {Pa : Work.FITop.Params} {φ : ℝ} {z : GaussianInt} (hz : z ∈ ncBox Pa φ) :
    Work.FITop3.InPolarBox Pa φ z ∧ Work.FITop3.NoSmallPrimes Pa z :=
  (Finset.mem_filter.mp hz).2

/-- Every element of the polar box has `|z|² ≤ 2N`. -/
lemma ncBox_gnorm_le (Pa : Work.FITop.Params) (φ : ℝ) {z : GaussianInt}
    (hz : z ∈ ncBox Pa φ) :
    ((Work.FIPlan.gnorm z : ℕ) : ℝ) ≤ 2 * Pa.N := by
  obtain ⟨hpol, -⟩ := ncBox_spec hz
  obtain ⟨-, hNlo, hNhi, -, -⟩ := hpol
  have hN0 : (0:ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hθ := ncTheta_le_one Pa
  have h2 : (1 + Pa.θ) * Pa.N ≤ 2 * Pa.N := by
    apply mul_le_mul_of_nonneg_right _ hN0; linarith
  linarith

/-- The candidate common divisors: `Pz < |g|² ≤ 2N`, inside the box `ncKb`. -/
def ncGset (Pa : Work.FITop.Params) : Finset GaussianInt :=
  (Work.FIPlan.gBox (ncKb Pa)).filter
    (fun g => (Pa.Pz : ℝ) < ((Work.FIPlan.gnorm g : ℕ) : ℝ)
      ∧ ((Work.FIPlan.gnorm g : ℕ) : ℝ) ≤ 2 * Pa.N)

lemma ncGset_spec {Pa : Work.FITop.Params} {g : GaussianInt} (hg : g ∈ ncGset Pa) :
    (Pa.Pz : ℝ) < ((Work.FIPlan.gnorm g : ℕ) : ℝ) ∧
      ((Work.FIPlan.gnorm g : ℕ) : ℝ) ≤ 2 * Pa.N :=
  (Finset.mem_filter.mp hg).2

lemma ncGset_ne_zero {Pa : Work.FITop.Params} {g : GaussianInt} (hg : g ∈ ncGset Pa) :
    g ≠ 0 := by
  intro h0
  rw [h0] at hg
  have h1 : ((Work.FIPlan.gnorm (0 : GaussianInt) : ℕ) : ℝ) = 0 := by
    simp [Work.FIPlan.gnorm, Zsqrtd.norm_zero]
  have h2 := (ncGset_spec hg).1
  rw [h1] at h2
  have : (0:ℝ) < (Pa.Pz : ℝ) := by
    have := Pa.hP2; exact_mod_cast (by omega : 0 < Pa.Pz)
  linarith

lemma ncGset_one_le {Pa : Work.FITop.Params} {g : GaussianInt} (hg : g ∈ ncGset Pa) :
    (1:ℝ) ≤ ((Work.FIPlan.gnorm g : ℕ) : ℝ) := by
  have h := (ncGset_spec hg).1
  have : (0:ℝ) < (Pa.Pz : ℝ) := by
    have := Pa.hP2; exact_mod_cast (by omega : 0 < Pa.Pz)
  have h1 : (0:ℝ) < ((Work.FIPlan.gnorm g : ℕ) : ℝ) := by linarith
  have h2 : (0:ℕ) < Work.FIPlan.gnorm g := by exact_mod_cast h1
  exact_mod_cast (by omega : 1 ≤ Work.FIPlan.gnorm g)

/-- The number of Gaussian integers of norm `≤ r` is at most `(2√r + 1)²`. -/
lemma ncCardGn_le (r : ℝ) :
    (((Work.FIPlan.gBox (⌈Real.sqrt r⌉₊ : ℤ)).filter
      (fun u => ((Work.FIPlan.gnorm u : ℕ) : ℝ) ≤ r)).card : ℝ)
      ≤ (2 * Real.sqrt r + 1) ^ 2 := by
  rcases le_or_gt 0 r with hr | hr
  · refine Work.FIArea4.card_le_of_dist_le
      ((Work.FIPlan.gBox (⌈Real.sqrt r⌉₊ : ℤ)).filter
        (fun u => ((Work.FIPlan.gnorm u : ℕ) : ℝ) ≤ r))
      (0 : ℂ) (Real.sqrt_nonneg r) ?_
    intro z hz
    rw [sub_zero, Work.FIArea4.norm_toComplex_eq_sqrt_gnorm]
    exact Real.sqrt_le_sqrt (Finset.mem_filter.mp hz).2
  · have hemp : ((Work.FIPlan.gBox (⌈Real.sqrt r⌉₊ : ℤ)).filter
        (fun u => ((Work.FIPlan.gnorm u : ℕ) : ℝ) ≤ r)) = ∅ := by
      refine Finset.filter_false_of_mem ?_
      intro u _ h
      have h2 : (0:ℝ) ≤ ((Work.FIPlan.gnorm u : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hzero : (((Work.FIPlan.gBox (⌈Real.sqrt r⌉₊ : ℤ)).filter
        (fun u => ((Work.FIPlan.gnorm u : ℕ) : ℝ) ≤ r)).card : ℝ) = 0 := by
      rw [hemp, Finset.card_empty, Nat.cast_zero]
    rw [hzero]
    nlinarith [Real.sqrt_nonneg r]

/-! ## 4. The exponential parameter bounds of the endgame -/

/-- An explicit lower bound for `e^{2·10⁶}` against the constants of the endgame. -/
lemma ncExp_big : 12288 + 10240 * Real.exp 500000 + 13188 * Real.exp 1000000
    ≤ Real.exp 2000000 := by
  have h1 : (1000000:ℝ) ≤ Real.exp 1000000 := by
    have h := Real.add_one_le_exp 1000000; linarith
  have h4 : Real.exp 500000 ≤ Real.exp 1000000 := Real.exp_le_exp.mpr (by norm_num)
  have h3 : Real.exp 1000000 * Real.exp 1000000 = Real.exp 2000000 := by
    have h : (2000000:ℝ) = 1000000 + 1000000 := by norm_num
    rw [h, Real.exp_add]
  nlinarith [h1, h3, h4, Real.exp_pos 500000, Real.exp_pos 1000000]

end

end Work.FIArea6
