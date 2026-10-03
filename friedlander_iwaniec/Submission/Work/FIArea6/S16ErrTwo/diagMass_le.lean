import Mathlib
import Submission.Work.FIArea6.S16ErrTwo.Defs
import Submission.Work.FIArea6.card_dvd_delta_fiber_near_le
import Submission.Work.FIArea6.S16_beta_mass6
import Submission.Work.FIArea7.isCoprime_coords_of_squarefree_gnorm

set_option autoImplicit false

open Finset
open scoped BigOperators

namespace Work.FIArea6.S16ErrTwo

attribute [local instance] Classical.propDecidable

noncomputable section

lemma gnorm_eq_coords (z : GaussianInt) :
    Work.FIPlan.gnorm z = z.re.natAbs ^ 2 + z.im.natAbs ^ 2 := by
  unfold Work.FIPlan.gnorm
  have h : z.norm = z.re ^ 2 + z.im ^ 2 := by
    rw [Zsqrtd.norm_def]; ring
  rw [h, Int.natAbs_add_of_nonneg (by positivity) (by positivity), Int.natAbs_pow, Int.natAbs_pow]

lemma Delta_coord' (z1 z2 : GaussianInt) :
    Work.FIPlan.Delta z1 z2 = z1.re * z2.im - z1.im * z2.re := by
  rw [Work.FIPlan.Delta, Zsqrtd.im_mul, Zsqrtd.im_star, Zsqrtd.re_star]; ring

lemma exists_scale_of_delta_eq_zero {z1 z2 : GaussianInt} (hcop : IsCoprime z1.re z1.im)
    (hΔ : Work.FIPlan.Delta z1 z2 = 0) :
    ∃ t : ℤ, z2.re = t * z1.re ∧ z2.im = t * z1.im := by
  obtain ⟨x, y, hxy⟩ := hcop
  rw [Delta_coord'] at hΔ
  refine ⟨x * z2.re + y * z2.im, ?_, ?_⟩
  · linear_combination -(z2.re : ℤ) * hxy - (y : ℤ) * hΔ
  · linear_combination -(z2.im : ℤ) * hxy + (x : ℤ) * hΔ

lemma gnorm_scale_nat (t : ℤ) {z1 z2 : GaussianInt}
    (hre : z2.re = t * z1.re) (him : z2.im = t * z1.im) :
    Work.FIPlan.gnorm z2 = t.natAbs ^ 2 * Work.FIPlan.gnorm z1 := by
  rw [gnorm_eq_coords, gnorm_eq_coords, hre, him, Int.natAbs_mul, Int.natAbs_mul]
  ring

lemma mem_boxN_coords {Pa : Work.FITop.Params} {z : GaussianInt} (hz : z ∈ Work.FITop.boxN Pa) :
    -Work.FITop.radN Pa ≤ z.re ∧ z.re ≤ Work.FITop.radN Pa ∧
    -Work.FITop.radN Pa ≤ z.im ∧ z.im ≤ Work.FITop.radN Pa := by
  rw [Work.FITop.boxN, Work.FIPlan.gBox] at hz
  obtain ⟨p, hp, hfa⟩ := Finset.mem_image.mp hz
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  rw [Finset.mem_Icc] at hp1 hp2
  have hre : z.re = p.1 := by
    have h := congrArg (fun w : GaussianInt => w.re) hfa
    simpa using h.symm
  have him : z.im = p.2 := by
    have h := congrArg (fun w : GaussianInt => w.im) hfa
    simpa using h.symm
  exact ⟨by rw [hre]; exact hp1.1, by rw [hre]; exact hp1.2,
         by rw [him]; exact hp2.1, by rw [him]; exact hp2.2⟩

lemma gnorm_le_two_radN_sq {Pa : Work.FITop.Params} {z : GaussianInt}
    (hz : z ∈ Work.FITop.boxN Pa) :
    (Work.FIPlan.gnorm z : ℝ) ≤ 2 * ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ) ^ 2 := by
  obtain ⟨hr1, hr2, hi1, hi2⟩ := mem_boxN_coords hz
  have habsre : |z.re| ≤ Work.FITop.radN Pa := abs_le.mpr ⟨hr1, hr2⟩
  have habsim : |z.im| ≤ Work.FITop.radN Pa := abs_le.mpr ⟨hi1, hi2⟩
  have hre_nat : z.re.natAbs ≤ (⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) := by
    have h1 : (z.re.natAbs : ℤ) = |z.re| := Int.natCast_natAbs z.re
    have h2 : (z.re.natAbs : ℤ) ≤ Work.FITop.radN Pa := by rw [h1]; exact habsre
    have h3 : (z.re.natAbs : ℤ) ≤ ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℤ) := by
      simpa [Work.FITop.radN] using h2
    exact_mod_cast h3
  have him_nat : z.im.natAbs ≤ (⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) := by
    have h1 : (z.im.natAbs : ℤ) = |z.im| := Int.natCast_natAbs z.im
    have h2 : (z.im.natAbs : ℤ) ≤ Work.FITop.radN Pa := by rw [h1]; exact habsim
    have h3 : (z.im.natAbs : ℤ) ≤ ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℤ) := by
      simpa [Work.FITop.radN] using h2
    exact_mod_cast h3
  have hnat : Work.FIPlan.gnorm z
      ≤ 2 * (⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) ^ 2 := by
    rw [gnorm_eq_coords]
    have e1 : z.re.natAbs ^ 2 ≤ (⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) ^ 2 :=
      pow_le_pow_left₀ (Nat.zero_le _) hre_nat 2
    have e2 : z.im.natAbs ^ 2 ≤ (⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) ^ 2 :=
      pow_le_pow_left₀ (Nat.zero_le _) him_nat 2
    calc z.re.natAbs ^ 2 + z.im.natAbs ^ 2
        ≤ (⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) ^ 2 + (⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) ^ 2 :=
          add_le_add e1 e2
      _ = 2 * (⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) ^ 2 := by ring
  exact_mod_cast hnat

theorem card_delta_zero_boxN_le (Pa : Work.FITop.Params) {z1 : GaussianInt}
    (hgN : Pa.N < (Work.FIPlan.gnorm z1 : ℝ))
    (hcop : IsCoprime z1.re z1.im) :
    ((Work.FITop.boxN Pa).filter (fun z2 => Work.FIPlan.Delta z1 z2 = 0)).card ≤ 9 := by
  have hN1 : (1:ℝ) ≤ Pa.N := Pa.hN1
  have hgnorm1pos : (0:ℝ) < (Work.FIPlan.gnorm z1 : ℝ) := by linarith
  have hgnorm0 : Work.FIPlan.gnorm (0 : GaussianInt) = 0 := by
    rw [gnorm_eq_coords]; simp
  have hz1ne : z1 ≠ 0 := by
    intro h0
    rw [h0, hgnorm0] at hgN
    push_cast at hgN
    linarith
  have hsqrtN1 : (1:ℝ) ≤ Real.sqrt Pa.N := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hN1
  have hsqrt4 : Real.sqrt (4 * Pa.N) = 2 * Real.sqrt Pa.N := by
    rw [show (4:ℝ) * Pa.N = 2 ^ 2 * Pa.N by norm_num,
        Real.sqrt_mul (show (0:ℝ) ≤ 2 ^ 2 by norm_num),
        Real.sqrt_sq (show (0:ℝ) ≤ 2 by norm_num)]
  have hRbound : ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ) ≤ 3 * Real.sqrt Pa.N := by
    have h1 : ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ) < Real.sqrt (4 * Pa.N) + 1 :=
      Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
    rw [hsqrt4] at h1 ⊢
    linarith
  have hRnn : (0:ℝ) ≤ ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ) := by positivity
  have hRsq : ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ) ^ 2 ≤ 9 * Pa.N := by
    have h1 := pow_le_pow_left₀ hRnn hRbound 2
    have h2 : (3 * Real.sqrt Pa.N) ^ 2 = 9 * Pa.N := by
      rw [mul_pow, Real.sq_sqrt (by linarith : (0:ℝ) ≤ Pa.N)]; ring
    rwa [h2] at h1
  set g : ℤ → GaussianInt := fun t => (⟨t * z1.re, t * z1.im⟩ : GaussianInt) with hg
  have hinj : Set.InjOn g ↑(Finset.Icc (-4) 4) := by
    intro a _ b _ hab
    have h1 : a * z1.re = b * z1.re := by
      have := congrArg (fun w : GaussianInt => w.re) hab; simpa [hg] using this
    have h2 : a * z1.im = b * z1.im := by
      have := congrArg (fun w : GaussianInt => w.im) hab; simpa [hg] using this
    have h1z : (a - b) * z1.re = 0 := by nlinarith [h1]
    have h2z : (a - b) * z1.im = 0 := by nlinarith [h2]
    have hab0 : a - b = 0 := by
      rcases mul_eq_zero.mp h1z with h | h
      · exact h
      · rcases mul_eq_zero.mp h2z with h2 | h2
        · exact h2
        · exact absurd (Zsqrtd.ext h h2) hz1ne
    exact sub_eq_zero.mp hab0
  have hsub : (Work.FITop.boxN Pa).filter (fun z2 => Work.FIPlan.Delta z1 z2 = 0)
      ⊆ (Finset.Icc (-4) 4).image g := by
    intro z2 hz2
    rw [Finset.mem_filter] at hz2
    obtain ⟨hz2box, hΔ⟩ := hz2
    obtain ⟨t, htr, hti⟩ := exists_scale_of_delta_eq_zero hcop hΔ
    have hgz2 : Work.FIPlan.gnorm z2 = t.natAbs ^ 2 * Work.FIPlan.gnorm z1 :=
      gnorm_scale_nat t htr hti
    have hle : (Work.FIPlan.gnorm z2 : ℝ)
        ≤ 2 * ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ) ^ 2 :=
      gnorm_le_two_radN_sq hz2box
    have h2 : ((Work.FIPlan.gnorm z2 : ℕ) : ℝ)
        = ((t.natAbs : ℕ) : ℝ) ^ 2 * (Work.FIPlan.gnorm z1 : ℝ) := by
      rw [hgz2, Nat.cast_mul, Nat.cast_pow]
    have hprodR : ((t.natAbs : ℕ) : ℝ) ^ 2 * (Work.FIPlan.gnorm z1 : ℝ)
        ≤ 2 * ((⌈Real.sqrt (4 * Pa.N)⌉₊ : ℕ) : ℝ) ^ 2 := by
      rw [← h2]; exact gnorm_le_two_radN_sq hz2box
    have hleR : ((t.natAbs : ℕ) : ℝ) ^ 2 * (Work.FIPlan.gnorm z1 : ℝ) ≤ 18 * Pa.N := by
      linarith [hprodR, hRsq]
    have htnsq : t.natAbs ^ 2 < 25 := by
      by_contra hcon
      have hcon' : 25 ≤ t.natAbs ^ 2 := by omega
      have h1 : (25 : ℝ) * (Work.FIPlan.gnorm z1 : ℝ)
          ≤ ((t.natAbs : ℕ) : ℝ) ^ 2 * (Work.FIPlan.gnorm z1 : ℝ) := by
        have : (25 : ℝ) ≤ ((t.natAbs : ℕ) : ℝ) ^ 2 := by exact_mod_cast hcon'
        exact mul_le_mul_of_nonneg_right this (by positivity)
      nlinarith [h1, hleR, hgN, hgnorm1pos]
    have htabs : |t| ≤ 4 := by
      have h5 : t.natAbs < 5 := by
        have hsq : t.natAbs ^ 2 < 5 ^ 2 := by simpa using htnsq
        exact lt_of_pow_lt_pow_left' 2 hsq
      have h1 : t.natAbs ≤ 4 := by omega
      have h2 : ((t.natAbs : ℕ) : ℤ) ≤ 4 := by exact_mod_cast h1
      rwa [Int.natCast_natAbs] at h2
    rw [Finset.mem_image]
    refine ⟨t, Finset.mem_Icc.mpr (abs_le.mp htabs), ?_⟩
    apply Zsqrtd.ext
    · simpa [hg] using htr.symm
    · simpa [hg] using hti.symm
  calc ((Work.FITop.boxN Pa).filter (fun z2 => Work.FIPlan.Delta z1 z2 = 0)).card
      ≤ ((Finset.Icc (-4) 4).image g).card := Finset.card_le_card hsub
    _ = (Finset.Icc (-4) 4).card := Finset.card_image_of_injOn hinj
    _ = 9 := by
      have h : ((Finset.Icc (-4:ℤ) 4).card : ℤ) = 9 := by
        rw [Int.card_Icc_of_le (-4) 4 (by norm_num : (-4:ℤ) ≤ 4 + 1)]
        norm_num
      exact_mod_cast h

lemma diagMass_generic_le (B : Finset GaussianInt) (a : GaussianInt → ℝ)
    (hcard : ∀ z1, a z1 ≠ 0 →
      (((B.filter (fun z2 => Work.FIPlan.Delta z1 z2 = 0)).card : ℕ) : ℝ) ≤ 9)
    (hcard' : ∀ z2, a z2 ≠ 0 →
      (((B.filter (fun z1 => Work.FIPlan.Delta z1 z2 = 0)).card : ℕ) : ℝ) ≤ 9) :
    (∑ z1 ∈ B, ∑ z2 ∈ B, (if Work.FIPlan.Delta z1 z2 = 0 then a z1 * a z2 else 0))
      ≤ 9 * (∑ z ∈ B, a z ^ 2) := by
  have key : ∀ z1 z2, (if Work.FIPlan.Delta z1 z2 = 0 then a z1 * a z2 else 0)
      ≤ (if Work.FIPlan.Delta z1 z2 = 0 then a z1 ^ 2 / 2 else 0)
        + (if Work.FIPlan.Delta z1 z2 = 0 then a z2 ^ 2 / 2 else 0) := by
    intro z1 z2
    by_cases h : Work.FIPlan.Delta z1 z2 = 0
    · rw [if_pos h, if_pos h, if_pos h]; nlinarith [sq_nonneg (a z1 - a z2)]
    · rw [if_neg h, if_neg h, if_neg h]; simp
  have hT1 : (∑ z1 ∈ B, ∑ z2 ∈ B,
        (if Work.FIPlan.Delta z1 z2 = 0 then a z1 ^ 2 / 2 else 0))
      ≤ 9/2 * (∑ z ∈ B, a z ^ 2) := by
    have step : ∀ z1, (∑ z2 ∈ B, (if Work.FIPlan.Delta z1 z2 = 0 then a z1 ^ 2 / 2 else 0))
        = ((B.filter (fun z2 => Work.FIPlan.Delta z1 z2 = 0)).card : ℝ) * (a z1 ^ 2 / 2) := by
      intro z1
      rw [← Finset.sum_filter]
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun z1 _ => step z1)]
    calc ∑ z1 ∈ B, ((B.filter (fun z2 => Work.FIPlan.Delta z1 z2 = 0)).card : ℝ) * (a z1 ^ 2 / 2)
        ≤ ∑ z1 ∈ B, 9 * (a z1 ^ 2 / 2) := by
          apply Finset.sum_le_sum
          intro z1 _
          by_cases h : a z1 = 0
          · simp [h]
          · exact mul_le_mul_of_nonneg_right (hcard z1 h) (by positivity)
      _ = 9 * (∑ z1 ∈ B, a z1 ^ 2 / 2) := by rw [← Finset.mul_sum]
      _ = 9 * ((∑ z1 ∈ B, a z1 ^ 2) / 2) := by rw [← Finset.sum_div]
      _ = 9/2 * (∑ z1 ∈ B, a z1 ^ 2) := by ring
  have hT2 : (∑ z1 ∈ B, ∑ z2 ∈ B,
        (if Work.FIPlan.Delta z1 z2 = 0 then a z2 ^ 2 / 2 else 0))
      ≤ 9/2 * (∑ z ∈ B, a z ^ 2) := by
    rw [Finset.sum_comm]
    have step : ∀ z2, (∑ z1 ∈ B, (if Work.FIPlan.Delta z1 z2 = 0 then a z2 ^ 2 / 2 else 0))
        = ((B.filter (fun z1 => Work.FIPlan.Delta z1 z2 = 0)).card : ℝ) * (a z2 ^ 2 / 2) := by
      intro z2
      rw [← Finset.sum_filter]
      rw [Finset.sum_const]
      simp [nsmul_eq_mul]
    rw [Finset.sum_congr rfl (fun z2 _ => step z2)]
    calc ∑ z2 ∈ B, ((B.filter (fun z1 => Work.FIPlan.Delta z1 z2 = 0)).card : ℝ) * (a z2 ^ 2 / 2)
        ≤ ∑ z2 ∈ B, 9 * (a z2 ^ 2 / 2) := by
          apply Finset.sum_le_sum
          intro z2 _
          by_cases h : a z2 = 0
          · simp [h]
          · exact mul_le_mul_of_nonneg_right (hcard' z2 h) (by positivity)
      _ = 9 * (∑ z2 ∈ B, a z2 ^ 2 / 2) := by rw [← Finset.mul_sum]
      _ = 9 * ((∑ z2 ∈ B, a z2 ^ 2) / 2) := by rw [← Finset.sum_div]
      _ = 9/2 * (∑ z2 ∈ B, a z2 ^ 2) := by ring
  calc (∑ z1 ∈ B, ∑ z2 ∈ B, (if Work.FIPlan.Delta z1 z2 = 0 then a z1 * a z2 else 0))
      ≤ ∑ z1 ∈ B, ∑ z2 ∈ B, ((if Work.FIPlan.Delta z1 z2 = 0 then a z1 ^ 2 / 2 else 0)
            + (if Work.FIPlan.Delta z1 z2 = 0 then a z2 ^ 2 / 2 else 0)) := by
        apply Finset.sum_le_sum; intro z1 _
        apply Finset.sum_le_sum; intro z2 _
        exact key z1 z2
    _ = (∑ z1 ∈ B, ∑ z2 ∈ B, (if Work.FIPlan.Delta z1 z2 = 0 then a z1 ^ 2 / 2 else 0))
        + (∑ z1 ∈ B, ∑ z2 ∈ B, (if Work.FIPlan.Delta z1 z2 = 0 then a z2 ^ 2 / 2 else 0)) := by
        simp only [Finset.sum_add_distrib]
    _ ≤ 9/2 * (∑ z ∈ B, a z ^ 2) + 9/2 * (∑ z ∈ B, a z ^ 2) := add_le_add hT1 hT2
    _ = 9 * (∑ z ∈ B, a z ^ 2) := by ring

/-- **The diagonal mass of §16.** For a round-6 coefficient, the pairs of the box with
`Δ(z₁,z₂) = 0` carry at most a constant times the square mass:

`diagMass β ≤ C (Σ_{z ∈ boxN} ‖βz‖²)`.

*Route.*  On the support `gnorm z = z.re² + z.im²` is squarefree (`IsBetaCoeff6` carries the Möbius
factor, so `z ∈ supp β → Squarefree (gnorm z)`; then `gcd z.re z.im = 1`).  For `z₁ ∈ supp β`,
`Δ(z₁,z′) = z₁.re·z′.im − z₁.im·z′.re = 0` with `gcd z₁.re z₁.im = 1` forces `z′ = t·z₁` with
`t ∈ ℤ` (Bezout), and `z′ ∈ boxN` forces `|t| ≤ 4` since `N < gnorm z₁` and
`gnorm z′ = t²·gnorm z₁ ≤ 2·radN²`; hence `#{z′ ∈ boxN : Δ(z₁,z′) = 0} ≤ 9`.  AM–GM over the
symmetric condition `Δ(z₁,z₂) = 0` (`Work.FIArea6.Delta_eq_neg`) then gives the claim, with `C = 9`. -/
theorem diagMass_le :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Pa : Work.FITop.Params) (φ : ℝ) (z0 : GaussianInt) (β : GaussianInt → ℂ),
      Work.FITop4.IsBetaCoeff6 Pa φ z0 β →
      diagMass Pa β
        ≤ C * (∑ z ∈ Work.FITop.boxN Pa, ‖β z‖ ^ (2 : ℕ)) := by
  refine ⟨9, by norm_num, ?_⟩
  intro Pa φ z0 β hβ
  have hcard : ∀ z1 : GaussianInt, ‖β z1‖ ≠ 0 →
      (((Work.FITop.boxN Pa).filter (fun z2 => Work.FIPlan.Delta z1 z2 = 0)).card : ℝ) ≤ 9 := by
    intro z1 hz
    have hz' : β z1 ≠ 0 := by intro h0; exact hz (by simp [h0])
    have hpol := Work.FITop4.IsBetaCoeff6.support hβ hz'
    have hgN : Pa.N < (Work.FIPlan.gnorm z1 : ℝ) := hpol.2.1
    have hsf := Work.FITop4.IsBetaCoeff6.squarefree_gnorm hβ hz'
    have hcop := Work.FIArea7.isCoprime_coords_of_squarefree_gnorm hsf
    exact_mod_cast card_delta_zero_boxN_le Pa hgN hcop
  have hcard' : ∀ z2 : GaussianInt, ‖β z2‖ ≠ 0 →
      (((Work.FITop.boxN Pa).filter (fun z1 => Work.FIPlan.Delta z1 z2 = 0)).card : ℝ) ≤ 9 := by
    intro z2 hz
    have hz' : β z2 ≠ 0 := by intro h0; exact hz (by simp [h0])
    have hpol := Work.FITop4.IsBetaCoeff6.support hβ hz'
    have hgN : Pa.N < (Work.FIPlan.gnorm z2 : ℝ) := hpol.2.1
    have hsf := Work.FITop4.IsBetaCoeff6.squarefree_gnorm hβ hz'
    have hcop := Work.FIArea7.isCoprime_coords_of_squarefree_gnorm hsf
    have h := card_delta_zero_boxN_le Pa hgN hcop
    have heq : (Work.FITop.boxN Pa).filter (fun z1 => Work.FIPlan.Delta z1 z2 = 0)
        = (Work.FITop.boxN Pa).filter (fun w => Work.FIPlan.Delta z2 w = 0) := by
      apply Finset.filter_congr
      intro w _
      rw [Work.FIArea6.Delta_eq_neg]
      simp
    rw [heq]
    exact_mod_cast h
  have hmain := diagMass_generic_le (Work.FITop.boxN Pa) (fun z => ‖β z‖) hcard hcard'
  simpa [diagMass] using hmain

end

end Work.FIArea6.S16ErrTwo
