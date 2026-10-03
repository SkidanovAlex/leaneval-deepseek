import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.large_sieve_sq_neg_one
import Submission.Commons.NumberTheory.FriedlanderIwaniec.rho_le_two_pow_omega
import Submission.Commons.NumberTheory.Moebius.sum_moebius_divisors
import Submission.Commons.Data.Nat.card_divisors_le_const_mul_rpow
import Submission.Commons.NumberTheory.DivisorSum.sum_divisor_count_div_le
import Submission.Commons.NumberTheory.FriedlanderIwaniec.reduced_linear_form_uniform

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.FriedlanderIwaniec

open Finset
open Commons.Analysis.ExponentialSums

/-- Decomposition of a pair `(d, l)`, `d > 0`, `l > 0`, along the squarefree part of
`gcd d l ^ 2`: there are a squarefree `ρ`, a positive `σ` and `d₀, l₀` with
`d = ρ σ ^ 2 d₀`, `l = ρ σ l₀`, `gcd ρ d₀ = 1`, `gcd d₀ l₀ = 1` and
`gcd d (l ^ 2) = ρ σ ^ 2`. -/
theorem exists_sqfree_sq_decomp (d l : ℕ) (hd : 0 < d) (hl : 0 < l) :
    ∃ ρ σ d₀ l₀ : ℕ, Squarefree ρ ∧ 0 < σ ∧ d = ρ * σ^2 * d₀ ∧ l = ρ * σ * l₀ ∧
      Nat.gcd ρ d₀ = 1 ∧ Nat.gcd d₀ l₀ = 1 ∧ Nat.gcd d (l^2) = ρ * σ^2 := by
  classical
  obtain ⟨a, b, hba, hsq⟩ := Nat.sq_mul_squarefree (Nat.gcd d (l^2))
  set ρ : ℕ := a with hρdef
  set σ : ℕ := b with hσdef
  have hg : ρ * σ^2 = Nat.gcd d (l^2) := by rw [← hba]; ring
  have hgpos : 0 < Nat.gcd d (l^2) := Nat.gcd_pos_of_pos_left _ hd
  have hσpos : 0 < σ := by
    rcases Nat.eq_zero_or_pos σ with h | h
    · rw [h] at hg; simp at hg; omega
    · exact h
  have hρpos : 0 < ρ := by
    rcases Nat.eq_zero_or_pos ρ with h | h
    · rw [h, zero_mul] at hg; omega
    · exact h
  have hρne : ρ ≠ 0 := hρpos.ne'
  have hσne : σ ≠ 0 := hσpos.ne'
  have hlne : l ≠ 0 := hl.ne'
  -- ρ * σ ∣ l
  have hkey : ∀ p : ℕ, (ρ * σ).factorization p ≤ l.factorization p := by
    intro p
    have h1 : ρ.factorization p + (σ^2).factorization p
        = (Nat.gcd d (l^2)).factorization p := by
      have h := congrArg (fun m : ℕ => m.factorization p) hg
      rwa [Nat.factorization_mul hρne (pow_ne_zero 2 hσne)] at h
    rw [Nat.factorization_pow] at h1
    simp only [Finsupp.smul_apply, smul_eq_mul] at h1
    have hgdvd : Nat.gcd d (l^2) ∣ l^2 := Nat.gcd_dvd_right _ _
    have h2 : (Nat.gcd d (l^2)).factorization p ≤ (l^2).factorization p :=
      (Nat.factorization_le_iff_dvd hgpos.ne' (pow_ne_zero 2 hlne)).mpr hgdvd p
    rw [Nat.factorization_pow] at h2
    simp only [Finsupp.smul_apply, smul_eq_mul] at h2
    have h3 : ρ.factorization p ≤ 1 := Squarefree.natFactorization_le_one p hsq
    rw [Nat.factorization_mul hρne hσne]
    simp only [Finsupp.add_apply]
    omega
  have hρσdvd : ρ * σ ∣ l :=
    (Nat.factorization_le_iff_dvd (mul_ne_zero hρne hσne) hlne).mp hkey
  have hgdd : Nat.gcd d (l^2) ∣ d := Nat.gcd_dvd_left _ _
  set d₀ : ℕ := d / Nat.gcd d (l^2) with hd₀def
  set l₀ : ℕ := l / (ρ * σ) with hl₀def
  have hd_eq : d = ρ * σ^2 * d₀ := by
    have h : ρ * σ^2 * (d / (ρ * σ^2)) = d := Nat.mul_div_cancel' (hg.symm ▸ hgdd)
    rw [hd₀def, ← hg]
    exact h.symm
  have hl_eq : l = ρ * σ * l₀ := by
    have h := Nat.mul_div_cancel' hρσdvd
    rw [hl₀def]
    exact h.symm
  have hgcdid : Nat.gcd d (l^2) = ρ * σ^2 * Nat.gcd d₀ (ρ * l₀^2) := by
    rw [hd_eq, hl_eq]
    have h1 : (ρ * σ * l₀)^2 = ρ * σ^2 * (ρ * l₀^2) := by ring
    rw [h1]
    have h2 : ρ * σ^2 * d₀ = ρ * σ^2 * d₀ := rfl
    rw [h2, Nat.gcd_mul_left]
  have hg1 : Nat.gcd d₀ (ρ * l₀^2) = 1 := by
    have h : ρ * σ^2 * Nat.gcd d₀ (ρ * l₀^2) = ρ * σ^2 := by
      have h' := hgcdid.symm
      rw [← hg] at h'
      exact h'
    have h2 : ρ * σ^2 * Nat.gcd d₀ (ρ * l₀^2) = ρ * σ^2 * 1 := by rw [mul_one]; exact h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h2
  have hρd : Nat.gcd ρ d₀ = 1 := by
    have hdiv : Nat.gcd ρ d₀ ∣ Nat.gcd d₀ (ρ * l₀^2) := by
      refine Nat.dvd_gcd (Nat.gcd_dvd_right ρ d₀) ?_
      exact (Nat.gcd_dvd_left ρ d₀).trans (dvd_mul_right ρ (l₀^2))
    rw [hg1] at hdiv
    exact Nat.dvd_one.mp hdiv
  have hdl : Nat.gcd d₀ l₀ = 1 := by
    have hdiv : Nat.gcd d₀ l₀ ∣ Nat.gcd d₀ (ρ * l₀^2) := by
      refine Nat.dvd_gcd (Nat.gcd_dvd_left d₀ l₀) ?_
      have hl0dvd : l₀ ∣ ρ * l₀^2 := ⟨ρ * l₀, by ring⟩
      exact (Nat.gcd_dvd_right d₀ l₀).trans hl0dvd
    rw [hg1] at hdiv
    exact Nat.dvd_one.mp hdiv
  exact ⟨ρ, σ, d₀, l₀, hsq, hσpos, hd_eq, hl_eq, hρd, hdl, hg.symm⟩

/-- Every root `ν` of `ν ^ 2 + l ^ 2 ≡ 0 (mod d)` is divisible by `ρ σ`. -/
private lemma rho_sigma_dvd_of_dvd (d l ρ σ d₀ l₀ ν : ℕ) (hρ : Squarefree ρ) (hσ : 0 < σ)
    (hd : d = ρ * σ^2 * d₀) (hl : l = ρ * σ * l₀) (hν : d ∣ ν^2 + l^2) : ρ * σ ∣ ν := by
  rcases Nat.eq_zero_or_pos ν with h | h
  · rw [h]; exact dvd_zero _
  have hρpos : 0 < ρ := Nat.pos_of_ne_zero hρ.ne_zero
  have hρne : ρ ≠ 0 := hρ.ne_zero
  have hσne : σ ≠ 0 := hσ.ne'
  have h1 : ρ * σ^2 ∣ l^2 := ⟨ρ * l₀^2, by rw [hl]; ring⟩
  have hdvd : ρ * σ^2 ∣ ν^2 + l^2 :=
    (dvd_mul_right (ρ * σ^2) d₀).trans (hd ▸ hν)
  have h2 : ρ * σ^2 ∣ ν^2 := (Nat.dvd_add_iff_left h1).mpr hdvd
  have hkey : ∀ p : ℕ, (ρ * σ).factorization p ≤ ν.factorization p := by
    intro p
    have hA : ρ.factorization p + 2 * σ.factorization p ≤ 2 * ν.factorization p := by
      have h := (Nat.factorization_le_iff_dvd (by positivity) (pow_ne_zero 2 h.ne')).mpr h2 p
      simp only [Nat.factorization_mul hρne (pow_ne_zero 2 hσne), Nat.factorization_pow,
        Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h
      exact h
    have h3 : ρ.factorization p ≤ 1 := Squarefree.natFactorization_le_one p hρ
    rw [Nat.factorization_mul hρne hσne]
    simp only [Finsupp.add_apply]
    omega
  exact (Nat.factorization_le_iff_dvd (mul_ne_zero hρne hσne) h.ne').mp hkey

/-- Reduction of the congruence `ν ^ 2 + l ^ 2 ≡ 0 (mod d)` for `ν = ρ σ m`. -/
private lemma dvd_iff_dvd_reduced (d l ρ σ d₀ l₀ m : ℕ) (hρ : 0 < ρ) (hσ : 0 < σ)
    (hd : d = ρ * σ^2 * d₀) (hl : l = ρ * σ * l₀) (hcop : Nat.Coprime d₀ ρ) :
    d ∣ (ρ * σ * m)^2 + l^2 ↔ d₀ ∣ m^2 + l₀^2 := by
  have h1 : (ρ * σ * m)^2 + l^2 = ρ * σ^2 * (ρ * (m^2 + l₀^2)) := by rw [hl]; ring
  rw [hd, h1]
  constructor
  · intro h
    have h' : d₀ ∣ ρ * (m^2 + l₀^2) := Nat.dvd_of_mul_dvd_mul_left (by positivity) h
    exact hcop.dvd_of_dvd_mul_left h'
  · intro h
    exact mul_dvd_mul_left (ρ * σ^2) (dvd_mul_of_dvd_right h ρ)


/-- Reindexing the roots of `ν ^ 2 + l ^ 2 ≡ 0 (mod d)` as `ρ σ m` with
`m < σ d₀` and `d₀ ∣ m ^ 2 + l₀ ^ 2`. -/
private lemma roots_eq_image (d l ρ σ d₀ l₀ : ℕ) (hd0 : 0 < d) (hρ : Squarefree ρ) (hσ : 0 < σ)
    (hd : d = ρ * σ^2 * d₀) (hl : l = ρ * σ * l₀) (hcopρ : Nat.Coprime d₀ ρ) :
    (Finset.range d).filter (fun ν : ℕ => d ∣ ν^2 + l^2)
      = ((Finset.range (σ * d₀)).filter (fun m : ℕ => d₀ ∣ m^2 + l₀^2)).image
          (fun m => ρ * σ * m) := by
  have hρpos : 0 < ρ := Nat.pos_of_ne_zero hρ.ne_zero
  have hd₀pos : 0 < d₀ := by
    have hmul : 0 < d₀ * (ρ * σ^2) := by
      rw [mul_comm d₀ (ρ * σ^2), ← hd]
      exact hd0
    exact Nat.pos_of_mul_pos_right hmul
  have hσd₀ : 0 < σ * d₀ := Nat.mul_pos hσ hd₀pos
  apply Finset.ext
  intro ν
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hνd, hdiv⟩
    obtain ⟨m, hm⟩ := rho_sigma_dvd_of_dvd d l ρ σ d₀ l₀ ν hρ hσ hd hl hdiv
    refine ⟨m, ⟨?_, ?_⟩, hm.symm⟩
    · rw [hm, hd] at hνd
      -- ρ σ m < ρ σ ^2 d₀
      exact lt_of_mul_lt_mul_left (by
        calc ρ * σ * m < ρ * σ ^2 * d₀ := hνd
          _ = ρ * σ * (σ * d₀) := by ring) (by positivity)
    · rw [hm] at hdiv
      exact (dvd_iff_dvd_reduced d l ρ σ d₀ l₀ m hρpos hσ hd hl hcopρ).mp hdiv
  · rintro ⟨m, ⟨hmrange, hmdiv⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · -- ρ σ m < d
      have : ρ * σ * m < ρ * σ * (σ * d₀) :=
        mul_lt_mul_of_pos_left hmrange (by positivity)
      calc ρ * σ * m < ρ * σ * (σ * d₀) := this
        _ = d := by rw [hd]; ring
    · exact (dvd_iff_dvd_reduced d l ρ σ d₀ l₀ m hρpos hσ hd hl hcopρ).mpr hmdiv


/-- `(d * c + r) % (σ * d) = d * (c % σ) + r` for `r < d`, `σ > 0`. -/
private lemma mul_add_mod (d c r σ : ℕ) (hd : 0 < d) (hσ : 0 < σ) (hr : r < d) :
    (d * c + r) % (σ * d) = d * (c % σ) + r := by
  have hmod : (d * c + r) ≡ d * (c % σ) + r [MOD σ * d] := by
    have h1 : c ≡ c % σ [MOD σ] := (Nat.mod_modEq c σ).symm
    have h2 : d * c ≡ d * (c % σ) [MOD d * σ] := h1.mul_left' d
    rw [Nat.mul_comm d σ] at h2
    exact h2.add_right r
  have hlt : d * (c % σ) + r < σ * d := by
    have h1 : c % σ < σ := Nat.mod_lt _ hσ
    calc d * (c % σ) + r < d * (c % σ) + d := by omega
      _ = d * (c % σ + 1) := by ring
      _ ≤ d * σ := Nat.mul_le_mul_left d (by omega)
      _ = σ * d := by ring
  refine Nat.ModEq.eq_of_lt_of_lt ?_ (Nat.mod_lt _ (Nat.mul_pos hσ hd)) hlt
  exact (Nat.mod_modEq (d * c + r) (σ * d)).trans hmod

/-- Lifting a congruence `A ≡ m [MOD d₀]` with `m < σ d₀` to the modulus `σ d₀`. -/
private lemma exists_lift (d₀ σ A m : ℕ) (hd₀ : 0 < d₀) (hσ : 0 < σ) (hm : m < σ * d₀)
    (h : A ≡ m [MOD d₀]) : ∃ j < σ, (A + d₀ * j) % (σ * d₀) = m := by
  set j : ℕ := (m / d₀ + σ - (A / d₀) % σ) % σ with hjdef
  have hjlt : j < σ := Nat.mod_lt _ hσ
  refine ⟨j, hjlt, ?_⟩
  have hAj : (A / d₀ + j) % σ = m / d₀ := by
    have hj1 : j ≡ m / d₀ + σ - (A / d₀) % σ [MOD σ] := by
      rw [hjdef]; exact Nat.mod_modEq _ σ
    have hA1 : A / d₀ ≡ (A / d₀) % σ [MOD σ] := (Nat.mod_modEq _ σ).symm
    have hsum := hA1.add hj1
    have hxx : (A / d₀) % σ + (m / d₀ + σ - (A / d₀) % σ) = m / d₀ + σ := by
      have hx : (A / d₀) % σ ≤ m / d₀ + σ :=
        le_trans (Nat.le_of_lt (Nat.mod_lt _ hσ)) (Nat.le_add_left σ (m / d₀))
      rw [Nat.add_sub_of_le hx]
    rw [hxx] at hsum
    have h2 : m / d₀ + σ ≡ m / d₀ [MOD σ] :=
      Nat.add_modulus_modEq_iff.mpr (Nat.ModEq.refl (m / d₀))
    refine Nat.ModEq.eq_of_lt_of_lt ?_ (Nat.mod_lt _ hσ)
      (Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hm))
    exact (Nat.mod_modEq (A / d₀ + j) σ).trans (hsum.trans h2)
  have hA' : A + d₀ * j = d₀ * (A / d₀ + j) + m % d₀ := by
    have hAd : d₀ * (A / d₀) + m % d₀ = A := by
      rw [← h]
      exact Nat.div_add_mod A d₀
    calc A + d₀ * j = (d₀ * (A / d₀) + m % d₀) + d₀ * j := by rw [hAd]
      _ = d₀ * (A / d₀ + j) + m % d₀ := by ring
  rw [hA', mul_add_mod d₀ (A / d₀ + j) (m % d₀) σ hd₀ hσ (Nat.mod_lt m hd₀), hAj]
  exact Nat.div_add_mod m d₀


/-- The set of `m < σ d₀` with `m ^ 2 + l₀ ^ 2 ≡ 0 (mod d₀)` is parametrised by the
roots `μ` of `μ ^ 2 + 1 ≡ 0 (mod d₀)` and a lift `j < σ`. -/
private lemma param_eq_reduced (d₀ l₀ σ : ℕ) (hσ : 0 < σ) (hcop : Nat.Coprime d₀ l₀) :
    (Finset.range (σ * d₀)).filter (fun m : ℕ => d₀ ∣ m^2 + l₀^2)
      = (((Finset.range d₀).filter (fun μ : ℕ => d₀ ∣ μ^2 + 1)).product (Finset.range σ)).image
          (fun p : ℕ × ℕ => (l₀ * p.1 + d₀ * p.2) % (σ * d₀)) := by
  rcases Nat.eq_zero_or_pos d₀ with hd₀ | hd₀
  · subst hd₀
    ext m
    simp
  have hσd₀ : 0 < σ * d₀ := Nat.mul_pos hσ hd₀
  apply Finset.ext
  intro m
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨hmrange, hmdiv⟩
    haveI : NeZero d₀ := ⟨hd₀.ne'⟩
    set U : (ZMod d₀)ˣ := ZMod.unitOfCoprime l₀ hcop.symm with hU
    set u : ℕ := ((U⁻¹ : (ZMod d₀)ˣ) : ZMod d₀).val with hu
    have hcoe : ((U : (ZMod d₀)ˣ) : ZMod d₀) = (l₀ : ZMod d₀) := by
      rw [hU]; exact ZMod.coe_unitOfCoprime l₀ hcop.symm
    have hu1 : (u : ZMod d₀) * (l₀ : ZMod d₀) = 1 := by
      have h2 : (u : ZMod d₀) = ((U⁻¹ : (ZMod d₀)ˣ) : ZMod d₀) := by
        rw [hu]; exact ZMod.natCast_zmod_val _
      rw [h2, ← hcoe]
      exact Units.inv_mul U
    have hm1 : (m : ZMod d₀)^2 + (l₀ : ZMod d₀)^2 = 0 := by
      have h : (((m^2 + l₀^2 : ℕ)) : ZMod d₀) = 0 := by
        simpa using (ZMod.natCast_eq_natCast_iff (m^2 + l₀^2) 0 d₀).mpr
          (Nat.modEq_zero_iff_dvd.mpr hmdiv)
      simpa using h
    have hm2 : (m : ZMod d₀)^2 = -((l₀ : ZMod d₀)^2) := eq_neg_of_add_eq_zero_left hm1
    set μ : ℕ := (m * u) % d₀ with hμdef
    have hμlt : μ < d₀ := Nat.mod_lt _ hd₀
    have hμval : (μ : ZMod d₀) = (m : ZMod d₀) * (u : ZMod d₀) := by
      rw [hμdef, ZMod.natCast_mod]
      push_cast
      ring
    have hμsq : (μ : ZMod d₀)^2 + 1 = 0 := by
      rw [hμval]
      calc ((m : ZMod d₀) * (u : ZMod d₀))^2 + 1
          = (m : ZMod d₀)^2 * (u : ZMod d₀)^2 + 1 := by ring
        _ = -((l₀ : ZMod d₀)^2) * (u : ZMod d₀)^2 + 1 := by rw [hm2]
        _ = -(((u : ZMod d₀) * (l₀ : ZMod d₀))^2) + 1 := by ring
        _ = 0 := by rw [hu1]; ring
    have hμdiv : d₀ ∣ μ^2 + 1 := by
      apply Nat.modEq_zero_iff_dvd.mp
      exact (ZMod.natCast_eq_natCast_iff (μ^2 + 1) 0 d₀).mp (by simpa using hμsq)
    have hμeq : (l₀ * μ : ℕ) ≡ m [MOD d₀] := by
      refine (ZMod.natCast_eq_natCast_iff (l₀ * μ) m d₀).mp ?_
      push_cast
      rw [hμval]
      calc (l₀ : ZMod d₀) * ((m : ZMod d₀) * (u : ZMod d₀))
          = (m : ZMod d₀) * ((u : ZMod d₀) * (l₀ : ZMod d₀)) := by ring
        _ = (m : ZMod d₀) := by rw [hu1, mul_one]
    obtain ⟨j, hjlt, hj⟩ := exists_lift d₀ σ (l₀ * μ) m hd₀ hσ hmrange hμeq
    exact ⟨(μ, j), Finset.mem_product.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hμlt, hμdiv⟩,
        Finset.mem_range.mpr hjlt⟩, hj⟩
  · rintro ⟨⟨μ, j⟩, hp, hval⟩
    obtain ⟨hμ, hj⟩ := Finset.mem_product.mp hp
    obtain ⟨hμlt, hμdiv⟩ := Finset.mem_filter.mp hμ
    have hjlt : j < σ := Finset.mem_range.mp hj
    refine ⟨?_, ?_⟩
    · rw [← hval]
      exact Nat.mod_lt _ hσd₀
    · have hm1 : m ≡ l₀ * μ + d₀ * j [MOD d₀] := by
        rw [← hval]
        exact (Nat.mod_modEq _ (σ * d₀)).of_dvd (dvd_mul_left d₀ σ)
      have hm2 : m^2 ≡ (l₀ * μ)^2 [MOD d₀] := by
        have hA : m^2 ≡ (l₀ * μ + d₀ * j)^2 [MOD d₀] := hm1.pow 2
        have hB : (l₀ * μ + d₀ * j)^2 ≡ (l₀ * μ)^2 [MOD d₀] := by
          have h : l₀ * μ + d₀ * j ≡ l₀ * μ [MOD d₀] := by
            have := (Nat.ModEq.refl (l₀ * μ)).add
              (Nat.modEq_zero_iff_dvd.mpr (dvd_mul_right d₀ j))
            simpa using this
          exact h.pow 2
        exact hA.trans hB
      have hm3 : (l₀ * μ)^2 + l₀^2 ≡ 0 [MOD d₀] := by
        have h : μ^2 + 1 ≡ 0 [MOD d₀] := Nat.modEq_zero_iff_dvd.mpr hμdiv
        have h2 : (l₀^2) * (μ^2 + 1) ≡ (l₀^2) * 0 [MOD d₀] := h.mul_left (l₀^2)
        have h3 : (l₀^2) * (μ^2 + 1) = (l₀ * μ)^2 + l₀^2 := by ring
        rw [h3] at h2
        simpa using h2
      have hfin : m^2 + l₀^2 ≡ 0 [MOD d₀] :=
        (hm2.add (Nat.ModEq.refl (l₀^2))).trans hm3
      exact Nat.modEq_zero_iff_dvd.mp hfin


/-- `ch` is multiplicative. -/
private lemma chAdd (x y : ℝ) : ch (x + y) = ch x * ch y := by
  unfold Commons.Analysis.ExponentialSums.ch
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `ch` of an integer is `1`. -/
private lemma chInt (n : ℤ) : ch (n : ℝ) = 1 := by
  unfold Commons.Analysis.ExponentialSums.ch
  have h : (((2 * Real.pi * (n : ℝ) : ℝ)) : ℂ) * Complex.I
      = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h]
  exact Complex.exp_int_mul_two_pi_mul_I n

/-- `ch` is periodic with period `1`. -/
private lemma chPeriod (x : ℝ) (n : ℤ) : ch (x + (n : ℝ)) = ch x := by
  rw [chAdd, chInt, mul_one]

/-- If `ch x = 1` then `x` is an integer. -/
private lemma chEqOne (x : ℝ) (h : ch x = 1) : ∃ n : ℤ, (n : ℝ) = x := by
  unfold Commons.Analysis.ExponentialSums.ch at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨n, ?_⟩
  have h2 : (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)
      = (((n : ℂ) * (2 * (Real.pi : ℂ))) * Complex.I) := by
    rw [hn]; ring
  have h3 : ((2 * Real.pi * x : ℝ) : ℂ) = ((n : ℂ) * (2 * (Real.pi : ℂ))) :=
    mul_right_cancel₀ Complex.I_ne_zero h2
  have h4 : (2 * Real.pi * x : ℝ) = (n : ℝ) * (2 * Real.pi) := by
    exact_mod_cast h3
  have h5 : (2 * Real.pi) * x = (2 * Real.pi) * (n : ℝ) := by
    rw [h4]; ring
  exact (mul_left_cancel₀ (ne_of_gt (by positivity : (0:ℝ) < 2 * Real.pi)) h5).symm

/-- The sum of the `σ`-th roots of unity: `∑_{j < σ} ch (j k / σ) = σ` if `σ ∣ k`, else `0`. -/
private lemma sum_ch_div (k σ : ℕ) (hσ : 0 < σ) :
    (∑ j ∈ Finset.range σ, ch ((j:ℝ) * (k:ℝ) / (σ:ℝ)))
      = if σ ∣ k then (σ : ℂ) else 0 := by
  have hpow : ∀ j : ℕ, ch ((j:ℝ) * (k:ℝ) / (σ:ℝ)) = (ch ((k:ℝ)/(σ:ℝ)))^j := by
    intro j
    rw [show (j:ℝ) * (k:ℝ) / (σ:ℝ) = (j:ℝ) * ((k:ℝ)/(σ:ℝ)) by ring]
    exact Commons.Analysis.ExponentialSums.ch_nat_mul ((k:ℝ)/(σ:ℝ)) j
  rw [Finset.sum_congr rfl (fun j _ => hpow j)]
  by_cases hk : σ ∣ k
  · rw [if_pos hk]
    obtain ⟨k', hk'⟩ := hk
    have hzeta : ch ((k:ℝ)/(σ:ℝ)) = 1 := by
      have h1 : (k:ℝ)/(σ:ℝ) = (k':ℝ) := by
        rw [hk']; push_cast; field_simp
      rw [h1]
      simpa using chInt (k' : ℤ)
    rw [hzeta]
    simp
  · rw [if_neg hk]
    have hzeta : ch ((k:ℝ)/(σ:ℝ)) ≠ 1 := by
      intro h1
      obtain ⟨n, hn⟩ := chEqOne _ h1
      have h3 : (k:ℝ) = (n:ℝ) * (σ:ℝ) := by
        have hh := hn
        field_simp at hh
        linarith [hh]
      have hm0 : 0 ≤ n := by
        by_contra hcon
        have hlt : (n:ℝ) < 0 := by exact_mod_cast (not_le.mp hcon)
        have hk0 : (0:ℝ) ≤ (k:ℝ) := by positivity
        have hs0 : (0:ℝ) < (σ:ℝ) := by positivity
        nlinarith [h3, hlt, hs0, hk0]
      refine hk ⟨n.toNat, ?_⟩
      have h4 : (k:ℝ) = (σ:ℝ) * ((n.toNat : ℕ) : ℝ) := by
        rw [← Int.toNat_of_nonneg hm0] at h3
        rw [mul_comm] at h3
        exact h3
      exact_mod_cast h4
    have hgeom : (∑ j ∈ Finset.range σ, (ch ((k:ℝ)/(σ:ℝ)))^j)
        * (ch ((k:ℝ)/(σ:ℝ)) - 1) = 0 := by
      rw [geom_sum_mul]
      have hpow2 : (ch ((k:ℝ)/(σ:ℝ)))^σ = ch ((σ:ℝ) * ((k:ℝ)/(σ:ℝ))) := by
        rw [← Commons.Analysis.ExponentialSums.ch_nat_mul ((k:ℝ)/(σ:ℝ)) σ]
      rw [hpow2]
      have hdiv : (σ:ℝ) * ((k:ℝ)/(σ:ℝ)) = (k:ℝ) := by
        field_simp
      rw [hdiv]
      have h6 : (k:ℝ) = ((k:ℤ):ℝ) := by push_cast; ring
      rw [h6, chInt, sub_self]
    rcases mul_eq_zero.mp hgeom with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h) hzeta


/-- The parametrisation of the reduced roots is injective. -/
private lemma param_inj (d₀ l₀ σ : ℕ) (hσ : 0 < σ) (hcop : Nat.Coprime d₀ l₀) :
    ∀ p ∈ ((Finset.range d₀).filter (fun μ : ℕ => d₀ ∣ μ^2 + 1)).product (Finset.range σ),
      ∀ q ∈ ((Finset.range d₀).filter (fun μ : ℕ => d₀ ∣ μ^2 + 1)).product (Finset.range σ),
      (l₀ * p.1 + d₀ * p.2) % (σ * d₀) = (l₀ * q.1 + d₀ * q.2) % (σ * d₀) → p = q := by
  rintro p hp q hq h
  rcases Nat.eq_zero_or_pos d₀ with hd₀ | hd₀
  · subst hd₀
    simp at hp
  obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
  obtain ⟨hq1, hq2⟩ := Finset.mem_product.mp hq
  have hp1' : p.1 < d₀ := Finset.mem_range.mp (Finset.mem_filter.mp hp1).1
  have hq1' : q.1 < d₀ := Finset.mem_range.mp (Finset.mem_filter.mp hq1).1
  have hp2' : p.2 < σ := Finset.mem_range.mp hp2
  have hq2' : q.2 < σ := Finset.mem_range.mp hq2
  have hmod0 : (l₀ * p.1 + d₀ * p.2) ≡ (l₀ * q.1 + d₀ * q.2) [MOD σ * d₀] := h
  have hmod : (l₀ * p.1 + d₀ * p.2) ≡ (l₀ * q.1 + d₀ * q.2) [MOD d₀] :=
    Nat.ModEq.of_dvd (dvd_mul_left d₀ σ) hmod0
  have h2 : d₀ * p.2 ≡ d₀ * q.2 [MOD d₀] := by
    rw [Nat.ModEq]
    simp
  have h1 : l₀ * p.1 ≡ l₀ * q.1 [MOD d₀] := (Nat.ModEq.add_iff_right h2).mp hmod
  have h3 : p.1 ≡ q.1 [MOD d₀] := by
    have h4 := Nat.ModEq.cancel_left_div_gcd hd₀ h1
    rwa [Nat.coprime_iff_gcd_eq_one.mp hcop, Nat.div_one] at h4
  have hp1eq : p.1 = q.1 := Nat.ModEq.eq_of_lt_of_lt h3 hp1' hq1'
  have hmod2 : d₀ * p.2 ≡ d₀ * q.2 [MOD σ * d₀] := by
    have h5 : l₀ * p.1 + d₀ * p.2 ≡ l₀ * p.1 + d₀ * q.2 [MOD σ * d₀] := by
      rw [← hp1eq] at hmod0
      exact hmod0
    exact Nat.ModEq.add_left_cancel' (l₀ * p.1) h5
  have h4 : p.2 ≡ q.2 [MOD σ] := by
    have h5 : d₀ * p.2 ≡ d₀ * q.2 [MOD d₀ * σ] := by rwa [Nat.mul_comm d₀ σ]
    exact Nat.ModEq.mul_left_cancel' hd₀.ne' h5
  have hp2eq : p.2 = q.2 := Nat.ModEq.eq_of_lt_of_lt h4 hp2' hq2'
  exact Prod.ext hp1eq hp2eq


/-- `ch` of `x - n` for a natural number `n`. -/
private lemma chSubNat (x : ℝ) (n : ℕ) : ch (x - (n:ℝ)) = ch x := by
  have h : ((-(n:ℤ) : ℤ) : ℝ) = -((n:ℝ)) := by push_cast; ring
  rw [show x - (n:ℝ) = x + ((-(n:ℤ) : ℤ) : ℝ) by rw [h]; ring]
  exact chPeriod x (-(n:ℤ))

/-- The argument `ρ σ m k / d` simplifies to `m k / (σ d₀)` when `d = ρ σ ^ 2 d₀`. -/
private lemma ch_arg_mul (d ρ σ d₀ m k : ℕ) (hρ : 0 < ρ) (hσ : 0 < σ) (hd₀ : 0 < d₀)
    (hd : d = ρ * σ^2 * d₀) :
    ch (((ρ * σ * m : ℕ) : ℝ) * (k : ℝ) / (d : ℝ))
      = ch (((m : ℝ) * (k : ℝ)) / (((σ * d₀ : ℕ)) : ℝ)) := by
  congr 1
  rw [hd]
  push_cast
  field_simp

/-- Reduction of `(l₀ μ + d₀ j) % (σ d₀)` modulo `σ d₀` in the argument of `ch`. -/
private lemma ch_arg_mod (σ d₀ l₀ μ j k : ℕ) (hσ : 0 < σ) (hd₀ : 0 < d₀) :
    ch (((((l₀ * μ + d₀ * j) % (σ * d₀)) : ℕ) : ℝ) * (k : ℝ) / (((σ * d₀ : ℕ)) : ℝ))
      = ch (((l₀ : ℝ) * (μ : ℝ) * (k : ℝ) / (((σ * d₀ : ℕ)) : ℝ))
              + ((j : ℝ) * (k : ℝ) / (σ : ℝ))) := by
  have hσd₀ : ((σ : ℝ) * (d₀ : ℝ)) ≠ 0 := by positivity
  have hX : ((((l₀ * μ + d₀ * j) % (σ * d₀)) : ℕ) : ℝ)
      = (((l₀ * μ + d₀ * j : ℕ)) : ℝ)
        - ((σ : ℝ) * (d₀ : ℝ)) * (((l₀ * μ + d₀ * j) / (σ * d₀) : ℕ) : ℝ) := by
    have h := Nat.div_add_mod (l₀ * μ + d₀ * j) (σ * d₀)
    have h' : ((((σ * d₀) * ((l₀ * μ + d₀ * j) / (σ * d₀))
        + (l₀ * μ + d₀ * j) % (σ * d₀) : ℕ)) : ℝ) = (((l₀ * μ + d₀ * j : ℕ)) : ℝ) := by
      rw [h]
    push_cast at h' ⊢
    linarith [h']
  have hsplit : (((((l₀ * μ + d₀ * j) % (σ * d₀)) : ℕ) : ℝ) * (k : ℝ) / (((σ * d₀ : ℕ)) : ℝ))
      = (((l₀ * μ + d₀ * j : ℕ) : ℝ) * (k : ℝ) / (((σ * d₀ : ℕ)) : ℝ))
        - ((((l₀ * μ + d₀ * j) / (σ * d₀) * k : ℕ)) : ℝ) := by
    rw [hX]
    push_cast
    field_simp
  rw [hsplit, chSubNat]
  congr 1
  push_cast
  field_simp

/-- For `σ ∣ k` the argument `l₀ μ k / (σ d₀)` simplifies to `μ (k / σ) l₀ / d₀`. -/
private lemma ch_arg_final (σ d₀ l₀ μ k : ℕ) (hσ : 0 < σ) (hd₀ : 0 < d₀) (hk : σ ∣ k) :
    ch (((l₀ : ℝ) * (μ : ℝ) * (k : ℝ) / (((σ * d₀ : ℕ)) : ℝ)))
      = ch (((μ : ℝ) * ((k : ℝ) / (σ : ℝ)) * (l₀ : ℝ)) / ((d₀ : ℝ))) := by
  have hcast : ((k : ℝ) / (σ : ℝ)) = (((k / σ : ℕ)) : ℝ) :=
    (Nat.cast_div hk (by positivity : (σ : ℝ) ≠ 0)).symm
  obtain ⟨k', hk'⟩ := hk
  have hdiv : (k / σ) = k' := by rw [hk', Nat.mul_div_cancel_left k' hσ]
  rw [hcast, hdiv, hk']
  congr 1
  push_cast
  field_simp


/-- **The linear form of `ρ(k, l, d)` in terms of the roots of `-1` modulo `d₀`.** -/
private lemma sum_roots_sq_add_sq_eq (d l ρ σ d₀ l₀ k : ℕ) (hd0 : 0 < d) (hρ : Squarefree ρ)
    (hσ : 0 < σ) (hd : d = ρ * σ^2 * d₀) (hl : l = ρ * σ * l₀)
    (hcopρ : Nat.Coprime d₀ ρ) (hcop : Nat.Coprime d₀ l₀) :
    (∑ ν ∈ (Finset.range d).filter (fun ν : ℕ => d ∣ ν^2 + l^2),
        ch ((ν:ℝ) * (k:ℝ) / (d:ℝ)))
      = if σ ∣ k then (σ : ℂ) * ∑ μ ∈ (Finset.range d₀).filter (fun μ : ℕ => d₀ ∣ μ^2 + 1),
            ch ((μ:ℝ) * ((k/σ):ℝ) * ((l₀:ℝ)) / (d₀:ℝ)) else 0 := by
  have hρpos : 0 < ρ := Nat.pos_of_ne_zero hρ.ne_zero
  have hd₀pos : 0 < d₀ := by
    have hmul : 0 < d₀ * (ρ * σ^2) := by rw [mul_comm d₀ (ρ * σ^2), ← hd]; exact hd0
    exact Nat.pos_of_mul_pos_right hmul
  set M : Finset ℕ := (Finset.range (σ * d₀)).filter (fun m : ℕ => d₀ ∣ m^2 + l₀^2) with hM
  set R : Finset ℕ := (Finset.range d₀).filter (fun μ : ℕ => d₀ ∣ μ^2 + 1) with hR
  have hA : (∑ ν ∈ (Finset.range d).filter (fun ν : ℕ => d ∣ ν^2 + l^2),
        ch ((ν:ℝ) * (k:ℝ) / (d:ℝ)))
      = ∑ m ∈ M, ch (((ρ * σ * m : ℕ) : ℝ) * (k:ℝ) / (d:ℝ)) := by
    rw [roots_eq_image d l ρ σ d₀ l₀ hd0 hρ hσ hd hl hcopρ, hM]
    refine Finset.sum_image ?_
    intro a _ b _ hab
    exact Nat.mul_left_cancel (by positivity : 0 < ρ * σ) hab
  rw [hA]
  rw [Finset.sum_congr rfl (fun m _ => ch_arg_mul d ρ σ d₀ m k hρpos hσ hd₀pos hd)]
  have hMC : M = (R.product (Finset.range σ)).image
      (fun p : ℕ × ℕ => (l₀ * p.1 + d₀ * p.2) % (σ * d₀)) := by
    rw [hM, hR]
    exact param_eq_reduced d₀ l₀ σ hσ hcop
  rw [hMC]
  rw [Finset.sum_image (fun p hp q hq h => param_inj d₀ l₀ σ hσ hcop p hp q hq h)]
  rw [show (∑ x ∈ R.product (Finset.range σ),
        ch ((((l₀ * x.1 + d₀ * x.2) % (σ * d₀)) : ℕ) * (k:ℝ) / (((σ * d₀ : ℕ)) : ℝ)))
      = ∑ μ ∈ R, ∑ j ∈ Finset.range σ,
        ch ((((l₀ * μ + d₀ * j) % (σ * d₀)) : ℕ) * (k:ℝ) / (((σ * d₀ : ℕ)) : ℝ))
      from Finset.sum_product R (Finset.range σ) _]
  have hE : ∀ μ ∈ R, ∀ j ∈ Finset.range σ,
      ch (((((l₀ * μ + d₀ * j) % (σ * d₀)) : ℕ) : ℝ) * (k : ℝ) / (((σ * d₀ : ℕ)) : ℝ))
        = ch (((l₀ : ℝ) * (μ : ℝ) * (k : ℝ) / (((σ * d₀ : ℕ)) : ℝ)))
            * ch (((j:ℝ) * (k:ℝ) / (σ:ℝ))) := by
    intro μ _ j _
    rw [ch_arg_mod σ d₀ l₀ μ j k hσ hd₀pos, chAdd]
  rw [Finset.sum_congr rfl (fun μ hμ => Finset.sum_congr rfl (fun j hj => hE μ hμ j hj))]
  have hF : ∀ μ ∈ R,
      (∑ j ∈ Finset.range σ, ch (((l₀ : ℝ) * (μ : ℝ) * (k : ℝ)
            / (((σ * d₀ : ℕ)) : ℝ))) * ch (((j:ℝ) * (k:ℝ) / (σ:ℝ))))
        = ch (((l₀ : ℝ) * (μ : ℝ) * (k : ℝ) / (((σ * d₀ : ℕ)) : ℝ)))
            * (if σ ∣ k then (σ:ℂ) else 0) := by
    intro μ _
    rw [← Finset.mul_sum, sum_ch_div k σ hσ]
  rw [Finset.sum_congr rfl (fun μ hμ => hF μ hμ)]
  by_cases hk : σ ∣ k
  · have hstep : ∀ μ ∈ R, ch (((l₀ : ℝ) * (μ : ℝ) * (k : ℝ) / (((σ * d₀ : ℕ)) : ℝ)))
          * (σ : ℂ) = (σ : ℂ) * ch (((μ : ℝ) * ((k : ℝ) / (σ : ℝ)) * (l₀ : ℝ)) / ((d₀ : ℝ))) := by
      intro μ _
      rw [ch_arg_final σ d₀ l₀ μ k hσ hd₀pos hk, mul_comm]
    simp only [if_pos hk]
    rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  · simp only [if_neg hk]
    simp


/-- A squarefree `ρ` with `ρ * σ ^ 2 ∣ l ^ 2` divides `ρ * σ` into `l`. -/
private lemma sqfree_mul_dvd_of_dvd_sq (ρ σ l : ℕ) (hρ : Squarefree ρ) (hσ : 0 < σ)
    (h : ρ * σ^2 ∣ l^2) : ρ * σ ∣ l := by
  rcases Nat.eq_zero_or_pos l with hl | hl
  · rw [hl]; exact dvd_zero _
  have hρne : ρ ≠ 0 := hρ.ne_zero
  have hσne : σ ≠ 0 := hσ.ne'
  have hkey : ∀ p : ℕ, (ρ * σ).factorization p ≤ l.factorization p := by
    intro p
    have hA : ρ.factorization p + 2 * σ.factorization p ≤ 2 * l.factorization p := by
      have hh := (Nat.factorization_le_iff_dvd (by positivity) (pow_ne_zero 2 hl.ne')).mpr h p
      simp only [Nat.factorization_mul hρne (pow_ne_zero 2 hσne), Nat.factorization_pow,
        Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hh
      exact hh
    have h3 : ρ.factorization p ≤ 1 := Squarefree.natFactorization_le_one p hρ
    rw [Nat.factorization_mul hρne hσne]
    simp only [Finsupp.add_apply]
    omega
  exact (Nat.factorization_le_iff_dvd (mul_ne_zero hρne hσne) hl.ne').mp hkey

/-- If `gcd d (l ^ 2) = ρ * σ ^ 2`, `d = ρ * σ ^ 2 * d₀` and `l = ρ * σ * l₀` with `ρ`
squarefree, then the reduced data is coprime. -/
private lemma gcd_reduced_coprime (d l ρ σ d₀ l₀ : ℕ) (hρ : Squarefree ρ) (hσ : 0 < σ)
    (hd : d = ρ * σ^2 * d₀) (hl : l = ρ * σ * l₀) (hg : Nat.gcd d (l^2) = ρ * σ^2) :
    Nat.gcd ρ d₀ = 1 ∧ Nat.gcd d₀ l₀ = 1 := by
  have hgcdid : Nat.gcd d (l^2) = ρ * σ^2 * Nat.gcd d₀ (ρ * l₀^2) := by
    rw [hd, hl]
    have h1 : (ρ * σ * l₀)^2 = ρ * σ^2 * (ρ * l₀^2) := by ring
    rw [h1]
    rw [show ρ * σ^2 * d₀ = ρ * σ^2 * d₀ from rfl, Nat.gcd_mul_left]
  have hg1 : Nat.gcd d₀ (ρ * l₀^2) = 1 := by
    have h : ρ * σ^2 * Nat.gcd d₀ (ρ * l₀^2) = ρ * σ^2 := by
      have h' := hgcdid.symm
      rw [hg] at h'
      exact h'
    have h2 : ρ * σ^2 * Nat.gcd d₀ (ρ * l₀^2) = ρ * σ^2 * 1 := by rw [mul_one]; exact h
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (Nat.pos_of_ne_zero hρ.ne_zero) (pow_pos hσ 2)) h2
  constructor
  · have hdiv : Nat.gcd ρ d₀ ∣ Nat.gcd d₀ (ρ * l₀^2) := by
      refine Nat.dvd_gcd (Nat.gcd_dvd_right ρ d₀) ?_
      exact (Nat.gcd_dvd_left ρ d₀).trans (dvd_mul_right ρ (l₀^2))
    rw [hg1] at hdiv
    exact Nat.dvd_one.mp hdiv
  · have hdiv : Nat.gcd d₀ l₀ ∣ Nat.gcd d₀ (ρ * l₀^2) := by
      refine Nat.dvd_gcd (Nat.gcd_dvd_left d₀ l₀) ?_
      have hl0dvd : l₀ ∣ ρ * l₀^2 := ⟨ρ * l₀, by ring⟩
      exact (Nat.gcd_dvd_right d₀ l₀).trans hl0dvd
    rw [hg1] at hdiv
    exact Nat.dvd_one.mp hdiv

/-- The `(ρ, σ, d₀, l₀)` reduction data of a pair `(d, l)`. -/
structure Decomp (d l : ℕ) where
  ρ : ℕ
  σ : ℕ
  d₀ : ℕ
  l₀ : ℕ
  hρ : Squarefree ρ
  hσ : 0 < σ
  hd : d = ρ * σ^2 * d₀
  hl : l = ρ * σ * l₀
  hρd : Nat.gcd ρ d₀ = 1
  hdl : Nat.gcd d₀ l₀ = 1
  hg : Nat.gcd d (l^2) = ρ * σ^2

/-- The (non-canonical but fixed) reduction data of `(d, l)`. -/
noncomputable def decompOf (d l : ℕ) (hd : 0 < d) (hl : 0 < l) : Decomp d l :=
  Classical.choice (show Nonempty (Decomp d l) from
    let ⟨ρ, σ, d₀, l₀, hρ, hσ, hd', hl', hρd, hdl, hg⟩ := exists_sqfree_sq_decomp d l hd hl
    ⟨⟨ρ, σ, d₀, l₀, hρ, hσ, hd', hl', hρd, hdl, hg⟩⟩)


/-- Uniqueness of the decomposition `g = ρ σ ^ 2` with `ρ` squarefree and `σ > 0`. -/
private lemma sqfree_sq_unique {ρ σ ρ' σ' : ℕ} (hρ : Squarefree ρ) (hρ' : Squarefree ρ')
    (hσ : 0 < σ) (hσ' : 0 < σ') (h : ρ * σ^2 = ρ' * σ'^2) : ρ = ρ' ∧ σ = σ' := by
  have hρne : ρ ≠ 0 := hρ.ne_zero
  have hρne' : ρ' ≠ 0 := hρ'.ne_zero
  have hσne : σ ≠ 0 := hσ.ne'
  have hσne' : σ' ≠ 0 := hσ'.ne'
  have hfac : ∀ p : ℕ, ρ.factorization p = ρ'.factorization p ∧ σ.factorization p = σ'.factorization p := by
    intro p
    have h1 : ρ.factorization p + 2 * σ.factorization p
        = ρ'.factorization p + 2 * σ'.factorization p := by
      have hh := congrArg (fun m : ℕ => m.factorization p) h
      simp only [Nat.factorization_mul hρne (pow_ne_zero 2 hσne),
        Nat.factorization_mul hρne' (pow_ne_zero 2 hσne'),
        Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hh
      linarith [hh]
    have h2 : ρ.factorization p ≤ 1 := Squarefree.natFactorization_le_one p hρ
    have h3 : ρ'.factorization p ≤ 1 := Squarefree.natFactorization_le_one p hρ'
    omega
  constructor
  · exact Nat.eq_of_factorization_eq hρne hρne' (fun p => (hfac p).1)
  · exact Nat.eq_of_factorization_eq hσne hσne' (fun p => (hfac p).2)

/-- Reindexing a sum over the multiples of `σ` in `Icc 1 K` by `k = σ k₀`. -/
private lemma sum_dvd_reindex (K σ : ℕ) (hσ : 0 < σ) (f : ℕ → ℂ) :
    (∑ k ∈ Finset.Icc 1 K, (if σ ∣ k then f (k / σ) else 0))
      = ∑ k₀ ∈ Finset.Icc 1 (K / σ), f k₀ := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij' (fun k _ => k / σ) (fun k₀ _ => σ * k₀) ?_ ?_ ?_ ?_ ?_
  · intro k hk
    obtain ⟨hkI, hkdvd⟩ := Finset.mem_filter.mp hk
    simp only [Finset.mem_Icc] at hkI ⊢
    constructor
    · have hle : 1 * σ ≤ k := by simpa using Nat.le_of_dvd (by omega : 0 < k) hkdvd
      exact Nat.le_div_iff_mul_le hσ |>.mpr hle
    · exact Nat.div_le_div_right hkI.2
  · intro k₀ hk₀
    simp only [Finset.mem_Icc] at hk₀ ⊢
    have h1 : 1 ≤ σ * k₀ := Nat.mul_pos hσ (by omega)
    have h2' : k₀ * σ ≤ K := Nat.le_div_iff_mul_le hσ |>.mp hk₀.2
    have h2 : σ * k₀ ≤ K := by rwa [mul_comm σ k₀]
    exact Finset.mem_filter.mpr ⟨by simp only [Finset.mem_Icc]; omega, ⟨k₀, rfl⟩⟩
  · intro k hk
    obtain ⟨hkI, hkdvd⟩ := Finset.mem_filter.mp hk
    obtain ⟨k₀, hk₀⟩ := hkdvd
    simp only [hk₀, Nat.mul_div_cancel_left _ hσ]
  · intro k₀ _
    exact Nat.mul_div_cancel_left k₀ hσ
  · intro k hk
    rfl


/-! ## The assembly: pointwise reduction of `ρ(k,l,d)` to one class

Write `g = gcd d (l ^ 2) = ρ σ ^ 2` with `ρ` squarefree (`Nat.sq_mul_squarefree`,
uniqueness in `sqfree_sq_unique`), `d = ρ σ ^ 2 d₀`, `l = ρ σ l₀`.  By
`sum_roots_sq_add_sq_eq` the inner sum `∑_{ν²+l²≡0(d)} e(νk/d)` collapses to `σ` times a sum
over the roots of `-1` modulo `d₀`, supported on the multiples `σ ∣ k`.  -/

/-- The inner exponential sum `∑_{ν : ν ^ 2 + l ^ 2 ≡ 0 (mod d)} e(ν k / d)`. -/
private noncomputable def rhoRoot (d k l : ℕ) : ℂ :=
  ∑ ν ∈ (Finset.range d).filter (fun ν : ℕ => (ν^2 + l^2) % d = 0),
    Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * (k:ℝ) / (d:ℝ))

/-- The reduced inner sum `∑_{μ : μ ^ 2 ≡ -1 (mod d)} e(μ k l / d)`. -/
private noncomputable def oneClass (d k l : ℕ) : ℂ :=
  ∑ μ ∈ (Finset.range d).filter (fun μ : ℕ => d ∣ μ^2 + 1),
    Commons.Analysis.ExponentialSums.ch ((μ:ℝ) * ((k*l : ℕ):ℝ) / (d:ℝ))

/-- The identity relating `gcd d (l ^ 2)` to the reduced data `d = ρ σ ^ 2 d₀`, `l = ρ σ l₀`. -/
private lemma gcd_mul_gcd_eq (ρ σ d₀ l₀ : ℕ) :
    Nat.gcd (ρ*σ^2*d₀) ((ρ*σ*l₀)^2) = ρ*σ^2*Nat.gcd d₀ (ρ*l₀^2) := by
  have h1 : (ρ*σ*l₀)^2 = ρ*σ^2*(ρ*l₀^2) := by ring
  rw [h1, Nat.gcd_mul_left]

/-- **Pointwise reduction.**  For a pair `(d,l)` with reduced data
`d = ρ σ ^ 2 d₀`, `l = ρ σ l₀`, the `k`-sum of `ξ k l ρ(k,l,d)` is `σ` times a sum
over the roots of `-1` modulo `d₀`, restricted to multiples of `σ`. -/
private lemma sum_k_rhoRoot_eq (d l K ρ σ d₀ l₀ : ℕ) (hd : 0 < d)
    (hρ : Squarefree ρ) (hσ : 0 < σ) (hd' : d = ρ*σ^2*d₀) (hl' : l = ρ*σ*l₀)
    (hρd : Nat.gcd ρ d₀ = 1) (hdl : Nat.gcd d₀ l₀ = 1) (ξ : ℕ → ℕ → ℂ) :
    (∑ k ∈ Finset.Icc 1 K, ξ k l * rhoRoot d k l)
      = (σ:ℂ) * ∑ k₀ ∈ Finset.Icc 1 (K/σ), ξ (σ*k₀) l * oneClass d₀ k₀ l₀ := by
  classical
  have hfil : (Finset.range d).filter (fun ν : ℕ => (ν^2 + l^2) % d = 0)
      = (Finset.range d).filter (fun ν : ℕ => d ∣ ν^2 + l^2) := by
    refine Finset.filter_congr ?_
    intro ν _
    exact (Nat.dvd_iff_mod_eq_zero).symm
  have hcopρ : Nat.Coprime d₀ ρ := Nat.coprime_comm.mpr hρd
  have hcop : Nat.Coprime d₀ l₀ := hdl
  have hkey : ∀ k : ℕ, rhoRoot d k l
      = if σ ∣ k then (σ:ℂ) * oneClass d₀ (k/σ) l₀ else 0 := by
    intro k
    unfold rhoRoot
    rw [hfil]
    rw [sum_roots_sq_add_sq_eq d l ρ σ d₀ l₀ k hd hρ hσ hd' hl' hcopρ hcop]
    by_cases hk : σ ∣ k
    · rw [if_pos hk, if_pos hk]
      congr 1
      refine Finset.sum_congr rfl (fun μ _ => ?_)
      congr 1
      push_cast
      rw [Nat.cast_div hk (by positivity : (σ:ℝ) ≠ 0)]
      ring
    · rw [if_neg hk, if_neg hk]
  have step1 : (∑ k ∈ Finset.Icc 1 K, ξ k l * rhoRoot d k l)
      = ∑ k ∈ Finset.Icc 1 K,
          ξ k l * (if σ ∣ k then (σ:ℂ) * oneClass d₀ (k/σ) l₀ else 0) :=
    Finset.sum_congr rfl (fun k _ => by rw [hkey k])
  have step2 : ∀ k : ℕ, ξ k l * (if σ ∣ k then (σ:ℂ) * oneClass d₀ (k/σ) l₀ else 0)
      = (σ:ℂ) * (if σ ∣ k then ξ k l * oneClass d₀ (k/σ) l₀ else 0) := by
    intro k
    by_cases hk : σ ∣ k
    · rw [if_pos hk, if_pos hk]; ring
    · rw [if_neg hk, if_neg hk]; ring
  have step3 : (∑ k ∈ Finset.Icc 1 K,
        (if σ ∣ k then ξ k l * oneClass d₀ (k/σ) l₀ else 0))
      = ∑ k ∈ Finset.Icc 1 K,
        (if σ ∣ k then (fun k₀ => ξ (σ*k₀) l * oneClass d₀ k₀ l₀) (k/σ) else 0) :=
    Finset.sum_congr rfl (fun k _ => by
      by_cases hk : σ ∣ k
      · rw [if_pos hk, if_pos hk]
        simp only [Nat.mul_div_cancel' hk]
      · rw [if_neg hk, if_neg hk])
  calc (∑ k ∈ Finset.Icc 1 K, ξ k l * rhoRoot d k l)
      = ∑ k ∈ Finset.Icc 1 K,
          ξ k l * (if σ ∣ k then (σ:ℂ) * oneClass d₀ (k/σ) l₀ else 0) := step1
    _ = ∑ k ∈ Finset.Icc 1 K,
          (σ:ℂ) * (if σ ∣ k then ξ k l * oneClass d₀ (k/σ) l₀ else 0) :=
        Finset.sum_congr rfl (fun k _ => step2 k)
    _ = (σ:ℂ) * ∑ k ∈ Finset.Icc 1 K,
          (if σ ∣ k then ξ k l * oneClass d₀ (k/σ) l₀ else 0) := by rw [Finset.mul_sum]
    _ = (σ:ℂ) * ∑ k₀ ∈ Finset.Icc 1 (K/σ), ξ (σ*k₀) l * oneClass d₀ k₀ l₀ := by
        congr 1
        rw [step3, sum_dvd_reindex K σ hσ (fun k₀ => ξ (σ*k₀) l * oneClass d₀ k₀ l₀)]

/-- Coprimality of the reduced data: `gcd ρ d₀ = gcd d₀ l₀ = 1` gives `gcd d₀ (ρ l₀ ^ 2) = 1`. -/
private lemma gcd_d0_rho_l0_sq (ρ d₀ l₀ : ℕ) (hρd : Nat.gcd ρ d₀ = 1)
    (hdl : Nat.gcd d₀ l₀ = 1) : Nat.gcd d₀ (ρ*l₀^2) = 1 :=
  (Nat.coprime_comm.mpr hρd).mul_right ((show Nat.Coprime d₀ l₀ from hdl).pow_right 2)

/-- The fibre of `l ∈ [1,L]` with `gcd d (l ^ 2) = ρ σ ^ 2` is the image of the
`l₀ ∈ [1, L/(ρσ)]` coprime to `d₀ = d/(ρ σ ^ 2)` under `l₀ ↦ ρ σ l₀`. -/
private lemma fibre_reindex (d L ρ σ : ℕ) (hd : 0 < d) (hρ : Squarefree ρ) (hσ : 0 < σ)
    (hdvd : ρ * σ^2 ∣ d) (hcop : Nat.gcd ρ (d/(ρ*σ^2)) = 1) :
    (Finset.Icc 1 L).filter (fun l => Nat.gcd d (l^2) = ρ*σ^2)
      = ((Finset.Icc 1 (L/(ρ*σ))).filter (fun l₀ => Nat.gcd l₀ (d/(ρ*σ^2)) = 1)).image
          (fun l₀ => ρ*σ*l₀) := by
  have hprod : ρ*σ^2*(d/(ρ*σ^2)) = d := Nat.mul_div_cancel' hdvd
  have hρpos : 0 < ρ := Nat.pos_of_ne_zero hρ.ne_zero
  have hρσ2pos : 0 < ρ*σ^2 := Nat.mul_pos hρpos (pow_pos hσ 2)
  have hρσpos : 0 < ρ*σ := Nat.mul_pos hρpos hσ
  ext l
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
  constructor
  · rintro ⟨⟨hl1, hlL⟩, hgcd⟩
    have hdiv : ρ*σ^2 ∣ l^2 := hgcd ▸ Nat.gcd_dvd_right d (l^2)
    obtain ⟨u, hu⟩ := sqfree_mul_dvd_of_dvd_sq ρ σ l hρ hσ hdiv
    have hkey : Nat.gcd d (l^2) = ρ*σ^2*Nat.gcd (d/(ρ*σ^2)) (ρ*u^2) := by
      have h0 := gcd_mul_gcd_eq ρ σ (d/(ρ*σ^2)) u
      rw [hprod] at h0
      rw [← hu] at h0
      exact h0
    have h2 : Nat.gcd (d/(ρ*σ^2)) (ρ*u^2) = 1 := by
      have h3 : ρ*σ^2*Nat.gcd (d/(ρ*σ^2)) (ρ*u^2) = ρ*σ^2*1 := by
        rw [mul_one, ← hkey]; exact hgcd
      exact Nat.eq_of_mul_eq_mul_left hρσ2pos h3
    have hu1 : 1 ≤ u := by
      rcases Nat.eq_zero_or_pos u with h | h
      · rw [h, mul_zero] at hu; omega
      · exact h
    have huL : u * (ρ*σ) ≤ L := by
      have hh : ρ*σ*u ≤ L := by rw [← hu]; exact hlL
      calc u * (ρ*σ) = ρ*σ*u := by ring
        _ ≤ L := hh
    have hcpu : Nat.gcd u (d/(ρ*σ^2)) = 1 := by
      refine Nat.dvd_one.mp ?_
      have h4 : Nat.gcd u (d/(ρ*σ^2)) ∣ Nat.gcd (d/(ρ*σ^2)) (ρ*u^2) :=
        Nat.dvd_gcd (Nat.gcd_dvd_right u (d/(ρ*σ^2)))
          ((Nat.gcd_dvd_left u (d/(ρ*σ^2))).trans
            ((dvd_mul_right u u).trans ⟨ρ, by ring⟩))
      rwa [h2] at h4
    exact ⟨u, ⟨⟨hu1, (Nat.le_div_iff_mul_le hρσpos).mpr huL⟩, hcpu⟩, hu.symm⟩
  · rintro ⟨u, ⟨⟨hu1, huL⟩, hcpu⟩, rfl⟩
    have huL' : u * (ρ*σ) ≤ L := (Nat.le_div_iff_mul_le hρσpos).mp huL
    have hρσu : ρ*σ*u ≤ L := by
      calc ρ*σ*u = u*(ρ*σ) := by ring
        _ ≤ L := huL'
    refine ⟨⟨by have hpos := Nat.mul_pos hρσpos (by omega : 0 < u); omega, hρσu⟩, ?_⟩
    have h2 : Nat.gcd (d/(ρ*σ^2)) (ρ*u^2) = 1 :=
      gcd_d0_rho_l0_sq ρ (d/(ρ*σ^2)) u hcop (by rw [Nat.gcd_comm]; exact hcpu)
    rw [← hprod, gcd_mul_gcd_eq ρ σ (d/(ρ*σ^2)) u, h2, mul_one]

/-- **Fibre computation.**  The contribution of the class `gcd d (l ^ 2) = ρ σ ^ 2` to the
`l`-sum is, after reindexing `l = ρ σ l₀`, exactly the one-class sum over the
`l₀ ∈ [1, L/(ρσ)]` coprime to `d₀ = d/(ρσ ^ 2)`, multiplied by `σ`. -/
private lemma fibre_sum_eq (d L ρ σ K : ℕ) (hd : 0 < d) (hρ : Squarefree ρ) (hσ : 0 < σ)
    (hdvd : ρ * σ^2 ∣ d) (ξ : ℕ → ℕ → ℂ) :
    (∑ l ∈ Finset.Icc 1 L, (if Nat.gcd d (l^2) = ρ*σ^2 then
        ∑ k ∈ Finset.Icc 1 K, ξ k l * rhoRoot d k l else 0))
      = (if Nat.gcd ρ (d/(ρ*σ^2)) = 1 then
          (σ:ℂ) * ∑ l₀ ∈ Finset.Icc 1 (L/(ρ*σ)),
            (if Nat.gcd l₀ (d/(ρ*σ^2)) = 1 then
              ∑ k₀ ∈ Finset.Icc 1 (K/σ), ξ (σ*k₀) (ρ*σ*l₀) * oneClass (d/(ρ*σ^2)) k₀ l₀
              else 0)
        else 0) := by
  classical
  have hprod : ρ*σ^2*(d/(ρ*σ^2)) = d := Nat.mul_div_cancel' hdvd
  have hρpos : 0 < ρ := Nat.pos_of_ne_zero hρ.ne_zero
  have hρσ2pos : 0 < ρ*σ^2 := Nat.mul_pos hρpos (pow_pos hσ 2)
  have hρσpos : 0 < ρ*σ := Nat.mul_pos hρpos hσ
  by_cases hcop : Nat.gcd ρ (d/(ρ*σ^2)) = 1
  · conv_rhs => rw [if_pos hcop]
    simp only [← Finset.sum_filter]
    rw [fibre_reindex d L ρ σ hd hρ hσ hdvd hcop]
    rw [Finset.sum_image (fun a _ b _ hab => Nat.mul_left_cancel hρσpos hab)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l₀ hl₀ => ?_)
    obtain ⟨_, hcpu⟩ := Finset.mem_filter.mp hl₀
    exact sum_k_rhoRoot_eq d (ρ*σ*l₀) K ρ σ (d/(ρ*σ^2)) l₀ hd hρ hσ hprod.symm rfl hcop
      (by rw [Nat.gcd_comm]; exact hcpu) ξ
  · conv_rhs => rw [if_neg hcop]
    refine Finset.sum_eq_zero (fun l hl => ?_)
    by_cases hc : Nat.gcd d (l^2) = ρ*σ^2
    · rw [if_pos hc]
      exfalso
      have hdiv : ρ*σ^2 ∣ l^2 := hc ▸ Nat.gcd_dvd_right d (l^2)
      obtain ⟨u, hu⟩ := sqfree_mul_dvd_of_dvd_sq ρ σ l hρ hσ hdiv
      have hkey : Nat.gcd d (l^2) = ρ*σ^2*Nat.gcd (d/(ρ*σ^2)) (ρ*u^2) := by
        have h0 := gcd_mul_gcd_eq ρ σ (d/(ρ*σ^2)) u
        rw [hprod] at h0
        rw [← hu] at h0
        exact h0
      have h2 : Nat.gcd (d/(ρ*σ^2)) (ρ*u^2) = 1 := by
        have h3 : ρ*σ^2*Nat.gcd (d/(ρ*σ^2)) (ρ*u^2) = ρ*σ^2*1 := by
          rw [mul_one, ← hkey]; exact hc
        exact Nat.eq_of_mul_eq_mul_left hρσ2pos h3
      have h3 : Nat.gcd (d/(ρ*σ^2)) ρ = 1 := by
        refine Nat.dvd_one.mp ?_
        have h4 : Nat.gcd (d/(ρ*σ^2)) ρ ∣ Nat.gcd (d/(ρ*σ^2)) (ρ*u^2) :=
          Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
            ((Nat.gcd_dvd_right _ _).trans (dvd_mul_right ρ (u^2)))
        rwa [h2] at h4
      exact hcop (by rw [Nat.gcd_comm]; exact h3)
    · rw [if_neg hc]
/-- The one-class linear form: the `k,l` double sum of `ξ k l` against the roots of `-1`,
restricted to the `l` coprime to the modulus. -/
private noncomputable def ocSum (d K L : ℕ) (ξ : ℕ → ℕ → ℂ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L,
    (if Nat.gcd l d = 1 then ξ k l * oneClass d k l else 0)

/-- The same form with the order of summation exchanged. -/
private lemma ocSum_eq_swapped (d K L : ℕ) (ξ : ℕ → ℕ → ℂ) :
    ocSum d K L ξ
      = ∑ l ∈ Finset.Icc 1 L, (if Nat.gcd l d = 1 then
          ∑ k ∈ Finset.Icc 1 K, ξ k l * oneClass d k l else 0) := by
  unfold ocSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.sum_ite_irrel (Nat.gcd l d = 1) (Finset.Icc 1 K)
      (fun k => ξ k l * oneClass d k l) (fun _ => 0)]
  simp

/-- The one-class estimate, as a `Prop` in the constants `C` and `η`. -/
private def OneClassBound (C η : ℝ) : Prop :=
  ∀ (D K L : ℕ), 1 ≤ D → 1 ≤ K → 1 ≤ L → ∀ ξ : ℕ → ℕ → ℂ,
    (∑ d ∈ Finset.Icc 1 D, ‖ocSum d K L ξ‖)
      ≤ C * Real.sqrt ((D:ℝ) * ((D:ℝ) + (K:ℝ)*(L:ℝ))) * (((D:ℝ)*(K:ℝ)*(L:ℝ))^η)
          * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2)

/-- The one-class estimate in the degenerate cases `D = 0`, `K = 0`, `L = 0`, where both sides
vanish. -/
private lemma oneClassBound_all {C η : ℝ} (hη : 0 < η) (hC : OneClassBound C η)
    (D K L : ℕ) (ξ : ℕ → ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 D, ‖ocSum d K L ξ‖)
      ≤ C * Real.sqrt ((D:ℝ) * ((D:ℝ) + (K:ℝ)*(L:ℝ))) * (((D:ℝ)*(K:ℝ)*(L:ℝ))^η)
          * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2) := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    simp [ocSum, Real.zero_rpow hη.ne']
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    simp [ocSum, Real.zero_rpow hη.ne']
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    simp [ocSum, Real.zero_rpow hη.ne']
  · exact hC D K L hD hK hL ξ

/-- The fibre `gcd d (l ^ 2) = ρ σ ^ 2` is empty when `ρ σ ^ 2 ∤ d`. -/
private lemma fibre_empty_of_not_dvd (d L ρ σ : ℕ) (hd : 0 < d) (hdvd : ¬ ρ*σ^2 ∣ d) :
    (Finset.Icc 1 L).filter (fun l => Nat.gcd d (l^2) = ρ*σ^2) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro l _ hc
  exact hdvd (hc ▸ Nat.gcd_dvd_left d (l^2))

/-- The fibre `gcd d (l ^ 2) = ρ σ ^ 2` is empty when `gcd ρ d₀ ≠ 1`. -/
private lemma fibre_empty_of_not_coprime (d L ρ σ : ℕ) (hd : 0 < d) (hρ : Squarefree ρ)
    (hσ : 0 < σ) (hdvd : ρ*σ^2 ∣ d) (hcop : Nat.gcd ρ (d/(ρ*σ^2)) ≠ 1) :
    (Finset.Icc 1 L).filter (fun l => Nat.gcd d (l^2) = ρ*σ^2) = ∅ := by
  rw [Finset.filter_eq_empty_iff]
  intro l _ hc
  have hprod : ρ*σ^2*(d/(ρ*σ^2)) = d := Nat.mul_div_cancel' hdvd
  have hρpos : 0 < ρ := Nat.pos_of_ne_zero hρ.ne_zero
  have hρσ2pos : 0 < ρ*σ^2 := Nat.mul_pos hρpos (pow_pos hσ 2)
  have hdiv : ρ*σ^2 ∣ l^2 := hc ▸ Nat.gcd_dvd_right d (l^2)
  obtain ⟨u, hu⟩ := sqfree_mul_dvd_of_dvd_sq ρ σ l hρ hσ hdiv
  have hkey : Nat.gcd d (l^2) = ρ*σ^2*Nat.gcd (d/(ρ*σ^2)) (ρ*u^2) := by
    have h0 := gcd_mul_gcd_eq ρ σ (d/(ρ*σ^2)) u
    rw [hprod] at h0
    rw [← hu] at h0
    exact h0
  have h2 : Nat.gcd (d/(ρ*σ^2)) (ρ*u^2) = 1 := by
    have h3 : ρ*σ^2*Nat.gcd (d/(ρ*σ^2)) (ρ*u^2) = ρ*σ^2*1 := by
      rw [mul_one, ← hkey]; exact hc
    exact Nat.eq_of_mul_eq_mul_left hρσ2pos h3
  have h3 : Nat.gcd (d/(ρ*σ^2)) ρ = 1 := by
    refine Nat.dvd_one.mp ?_
    have h4 : Nat.gcd (d/(ρ*σ^2)) ρ ∣ Nat.gcd (d/(ρ*σ^2)) (ρ*u^2) :=
      Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
        ((Nat.gcd_dvd_right _ _).trans (dvd_mul_right ρ (u^2)))
    rwa [h2] at h4
  exact hcop (by rw [Nat.gcd_comm]; exact h3)

/-- A fibre sum over an empty fibre vanishes. -/
private lemma sum_fibre_eq_zero (d L ρ σ K : ℕ)
    (hempty : (Finset.Icc 1 L).filter (fun l => Nat.gcd d (l^2) = ρ*σ^2) = ∅)
    (ξ : ℕ → ℕ → ℂ) :
    (∑ l ∈ Finset.Icc 1 L, (if Nat.gcd d (l^2) = ρ*σ^2 then
        ∑ k ∈ Finset.Icc 1 K, ξ k l * rhoRoot d k l else 0)) = 0 := by
  rw [← Finset.sum_filter, hempty, Finset.sum_empty]

/-- Norm bound for the contribution of one fibre class: bounding the fibre sum by the
one-class sum at the reduced modulus. -/
private lemma fibre_norm_le (d L ρ σ K : ℕ) (hd : 0 < d) (hρ : Squarefree ρ) (hσ : 0 < σ)
    (ξ : ℕ → ℕ → ℂ) :
    ‖∑ l ∈ Finset.Icc 1 L, (if Nat.gcd d (l^2) = ρ*σ^2 then
        ∑ k ∈ Finset.Icc 1 K, ξ k l * rhoRoot d k l else 0)‖
      ≤ (if ρ*σ^2 ∣ d then (σ:ℝ) * ‖∑ l₀ ∈ Finset.Icc 1 (L/(ρ*σ)),
            (if Nat.gcd l₀ (d/(ρ*σ^2)) = 1 then
              ∑ k₀ ∈ Finset.Icc 1 (K/σ), ξ (σ*k₀) (ρ*σ*l₀) * oneClass (d/(ρ*σ^2)) k₀ l₀
              else 0)‖ else 0) := by
  by_cases hdvd : ρ*σ^2 ∣ d
  · rw [if_pos hdvd]
    by_cases hcop : Nat.gcd ρ (d/(ρ*σ^2)) = 1
    · rw [fibre_sum_eq d L ρ σ K hd hρ hσ hdvd ξ]
      conv_lhs => rw [if_pos hcop]
      rw [norm_mul, Complex.norm_natCast]
    · rw [fibre_sum_eq d L ρ σ K hd hρ hσ hdvd ξ]
      conv_lhs => rw [if_neg hcop]
      rw [norm_zero]
      positivity
  · rw [if_neg hdvd]
    rw [sum_fibre_eq_zero d L ρ σ K (fibre_empty_of_not_dvd d L ρ σ hd hdvd) ξ, norm_zero]
/-- **Splitting into fibre classes.**  The `l`-sum is the sum over the pairs `(ρ,σ)` of the
contribution of the fibre `gcd d (l ^ 2) = ρ σ ^ 2`; the pairs range over
`[1,D] × [1,D]` with `ρ` squarefree. -/
private lemma partition_identity (d L D K : ℕ) (ξ : ℕ → ℕ → ℂ) (hd : 0 < d) (hdD : d ≤ D) :
    (∑ l ∈ Finset.Icc 1 L, ∑ k ∈ Finset.Icc 1 K, ξ k l * rhoRoot d k l)
      = ∑ p ∈ (((Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D))).filter (fun p : ℕ × ℕ => Squarefree p.1),
          ∑ l ∈ Finset.Icc 1 L, (if Nat.gcd d (l^2) = p.1*p.2^2 then
            ∑ k ∈ Finset.Icc 1 K, ξ k l * rhoRoot d k l else 0) := by
  classical
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l hl => ?_)
  have hl0 : 0 < l := by have := (Finset.mem_Icc.mp hl).1; omega
  have hdec := decompOf d l hd hl0
  set g : ℕ := Nat.gcd d (l^2) with hg
  have hgρσ : g = hdec.ρ * hdec.σ^2 := by rw [hg]; exact hdec.hg
  have hρ1 : 1 ≤ hdec.ρ := Nat.one_le_iff_ne_zero.mpr hdec.hρ.ne_zero
  have hσ1 : 1 ≤ hdec.σ := hdec.hσ
  have hgD : hdec.ρ * hdec.σ^2 ≤ D := by
    rw [← hgρσ]; exact (Nat.le_of_dvd hd (Nat.gcd_dvd_left d (l^2))).trans hdD
  have hρD : hdec.ρ ≤ D :=
    le_trans (Nat.le_mul_of_pos_right (m := hdec.σ^2) hdec.ρ (pow_pos hdec.hσ 2)) hgD
  have hσD : hdec.σ ≤ D := by
    have hσsq : hdec.σ ≤ hdec.σ^2 := by
      rw [pow_two]; exact Nat.le_mul_of_pos_right hdec.σ hdec.hσ
    have h2 : hdec.σ^2 ≤ hdec.ρ * hdec.σ^2 :=
      Nat.le_mul_of_pos_left (hdec.σ^2) (Nat.pos_of_ne_zero hdec.hρ.ne_zero)
    omega
  have hmem : (hdec.ρ, hdec.σ) ∈
      (((Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D))).filter (fun p : ℕ × ℕ => Squarefree p.1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨hρ1, hρD⟩, Finset.mem_Icc.mpr ⟨hσ1, hσD⟩⟩, hdec.hρ⟩
  have huniq : ∀ p ∈ (((Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D))).filter
        (fun p : ℕ × ℕ => Squarefree p.1), g = p.1 * p.2^2 → p = (hdec.ρ, hdec.σ) := by
    intro p hp hpcond
    have hsq : Squarefree p.1 := (Finset.mem_filter.mp hp).2
    have hp2 : 0 < p.2 := by
      have h := (Finset.mem_Icc.mp (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).2).1
      omega
    have heq : p.1 * p.2^2 = hdec.ρ * hdec.σ^2 := by rw [← hpcond, hgρσ]
    obtain ⟨h1, h2⟩ := sqfree_sq_unique hsq hdec.hρ hp2 hdec.hσ heq
    exact Prod.ext h1 h2
  have hsingle : ((((Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D))).filter
      (fun p : ℕ × ℕ => Squarefree p.1)).filter (fun p => g = p.1 * p.2^2)
      = {(hdec.ρ, hdec.σ)} := by
    rw [Finset.eq_singleton_iff_unique_mem]
    refine ⟨?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨hmem, hgρσ⟩
    · intro p hp
      exact huniq p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2
  rw [← Finset.sum_filter, hsingle, Finset.sum_singleton]
/-- The multiples of `ρ σ ^ 2` in `[1,D]`, divided by `ρ σ ^ 2`, are exactly `[1, D/(ρ σ ^ 2)]`. -/
private lemma image_div_Icc (D a : ℕ) (ha : 0 < a) :
    ((Finset.Icc 1 D).filter (fun d => a ∣ d)).image (fun d => d/a) = Finset.Icc 1 (D/a) := by
  ext m
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨d, ⟨⟨hd1, hdD⟩, hdvd⟩, rfl⟩
    constructor
    · have h : a * (d/a) = d := Nat.mul_div_cancel' hdvd
      nlinarith [hd1, ha, h]
    · rw [Nat.le_div_iff_mul_le ha]
      calc (d/a) * a = a * (d/a) := by ring
        _ = d := Nat.mul_div_cancel' hdvd
        _ ≤ D := hdD
  · rintro ⟨hm1, hmD⟩
    refine ⟨a*m, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · have := Nat.mul_pos ha (by omega : 0 < m); omega
    · rw [Nat.le_div_iff_mul_le ha] at hmD
      calc a*m = m*a := by ring
        _ ≤ D := hmD
    · exact dvd_mul_right a m
    · exact Nat.mul_div_cancel_left m ha

/-- `√(a / b ^ 2) = √a / b` for `b > 0`. -/
private lemma sqrt_div_sq (a b : ℝ) (hb : 0 < b) : Real.sqrt (a / b^2) = Real.sqrt a / b := by
  rw [Real.sqrt_div' a (by positivity : (0:ℝ) ≤ b^2), Real.sqrt_sq (le_of_lt hb)]

/-- Restricting the coefficient range does not increase the `ℓ²` norm. -/
private lemma xi_norm_le (K L σ ρ : ℕ) (hρ : 0 < ρ) (hσ : 0 < σ) (ξ : ℕ → ℕ → ℂ) :
    Real.sqrt (∑ k ∈ Finset.Icc 1 (K/σ), ∑ l ∈ Finset.Icc 1 (L/(ρ*σ)), ‖ξ (σ*k) (ρ*σ*l)‖^2)
      ≤ Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2) := by
  have hρσpos : 0 < ρ*σ := Nat.mul_pos hρ hσ
  have hinner : ∀ k ∈ Finset.Icc 1 K,
      ∑ l ∈ Finset.Icc 1 (L/(ρ*σ)), ‖ξ k (ρ*σ*l)‖^2 ≤ ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2 := by
    intro k _
    have himg : ((Finset.Icc 1 (L/(ρ*σ))).image (fun l => ρ*σ*l)) ⊆ Finset.Icc 1 L := by
      intro m hm
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hm
      simp only [Finset.mem_Icc] at hl ⊢
      constructor
      · have := Nat.mul_pos hρσpos (by omega : 0 < l); omega
      · calc ρ*σ*l = l*(ρ*σ) := by ring
          _ ≤ (L/(ρ*σ))*(ρ*σ) := Nat.mul_le_mul_right _ hl.2
          _ = ρ*σ*(L/(ρ*σ)) := by ring
          _ ≤ L := Nat.mul_div_le L (ρ*σ)
    calc ∑ l ∈ Finset.Icc 1 (L/(ρ*σ)), ‖ξ k (ρ*σ*l)‖^2
        = ∑ m ∈ (Finset.Icc 1 (L/(ρ*σ))).image (fun l => ρ*σ*l), ‖ξ k m‖^2 := by
          rw [Finset.sum_image (fun a _ b _ hab => Nat.mul_left_cancel hρσpos hab)]
      _ ≤ ∑ m ∈ Finset.Icc 1 L, ‖ξ k m‖^2 :=
          Finset.sum_le_sum_of_subset_of_nonneg himg (fun i _ _ => sq_nonneg _)
  have hσmem : ∀ k ∈ Finset.Icc 1 (K/σ), σ*k ∈ Finset.Icc 1 K := by
    intro k hk
    simp only [Finset.mem_Icc] at hk ⊢
    constructor
    · have := Nat.mul_pos hσ (by omega : 0 < k); omega
    · calc σ*k = k*σ := by ring
        _ ≤ (K/σ)*σ := Nat.mul_le_mul_right _ hk.2
        _ = σ*(K/σ) := by ring
        _ ≤ K := Nat.mul_div_le K σ
  have houter : ((Finset.Icc 1 (K/σ)).image (fun k => σ*k)) ⊆ Finset.Icc 1 K := by
    intro m hm
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
    exact hσmem k hk
  calc Real.sqrt (∑ k ∈ Finset.Icc 1 (K/σ), ∑ l ∈ Finset.Icc 1 (L/(ρ*σ)), ‖ξ (σ*k) (ρ*σ*l)‖^2)
      ≤ Real.sqrt (∑ k ∈ Finset.Icc 1 (K/σ), ∑ l ∈ Finset.Icc 1 L, ‖ξ (σ*k) l‖^2) :=
        Real.sqrt_le_sqrt (Finset.sum_le_sum (fun k hk => hinner (σ*k) (hσmem k hk)))
    _ ≤ Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2) := by
        refine Real.sqrt_le_sqrt ?_
        calc ∑ k ∈ Finset.Icc 1 (K/σ), ∑ l ∈ Finset.Icc 1 L, ‖ξ (σ*k) l‖^2
            = ∑ m ∈ (Finset.Icc 1 (K/σ)).image (fun k => σ*k),
                ∑ l ∈ Finset.Icc 1 L, ‖ξ m l‖^2 := by
              rw [Finset.sum_image (fun a _ b _ hab => Nat.mul_left_cancel hσ hab)]
          _ ≤ ∑ m ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ m l‖^2 :=
              Finset.sum_le_sum_of_subset_of_nonneg houter
                (fun i _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))

/-- **The total contribution of one class `(ρ,σ)`.**  Summing the fibre bound over the moduli
`d ∈ [1,D]` and applying the one-class estimate. -/
private lemma fibre_total_le {C₀ η : ℝ} (hC₀nn : 0 ≤ C₀) (hη : 0 < η) (hC₀ : OneClassBound C₀ η)
    (D K L : ℕ) (hD : 1 ≤ D) (hK : 1 ≤ K) (hL : 1 ≤ L) (ξ : ℕ → ℕ → ℂ)
    (ρ σ : ℕ) (hρ : Squarefree ρ) (hσ : 0 < σ) :
    (∑ d ∈ Finset.Icc 1 D, ‖∑ l ∈ Finset.Icc 1 L, (if Nat.gcd d (l^2) = ρ*σ^2 then
        ∑ k ∈ Finset.Icc 1 K, ξ k l * rhoRoot d k l else 0)‖)
      ≤ C₀ * (((D:ℝ)*(K:ℝ)*(L:ℝ))^η)
          * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2)
          * (Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) / ((ρ:ℝ)*(σ:ℝ))) := by
  classical
  have hρpos : 0 < ρ := Nat.pos_of_ne_zero hρ.ne_zero
  have hρR : (0:ℝ) < ρ := by exact_mod_cast hρpos
  have hσR : (0:ℝ) < σ := by exact_mod_cast hσ
  have hρσR : (0:ℝ) < (ρ:ℝ)*(σ:ℝ) := mul_pos hρR hσR
  have hρσ2R : (0:ℝ) < (ρ:ℝ)*(σ:ℝ)^2 := mul_pos hρR (pow_pos hσR 2)
  set DD : ℝ := ((D/((ρ*σ^2)) : ℕ) : ℝ) with hDD
  set KK : ℝ := ((K/σ : ℕ) : ℝ) with hKK
  set LL : ℝ := ((L/((ρ*σ)) : ℕ) : ℝ) with hLL
  -- pointwise bound
  have hstep1 : ∀ d ∈ Finset.Icc 1 D,
      ‖∑ l ∈ Finset.Icc 1 L, (if Nat.gcd d (l^2) = ρ*σ^2 then
        ∑ k ∈ Finset.Icc 1 K, ξ k l * rhoRoot d k l else 0)‖
      ≤ (if ρ*σ^2 ∣ d then (σ:ℝ) * ‖ocSum (d/(ρ*σ^2)) (K/σ) (L/(ρ*σ))
            (fun k₀ l₀ => ξ (σ*k₀) (ρ*σ*l₀))‖ else 0) := by
    intro d hdmem
    have hd : 0 < d := by have := (Finset.mem_Icc.mp hdmem).1; omega
    have h := fibre_norm_le d L ρ σ K hd hρ hσ ξ
    rw [← ocSum_eq_swapped (d/(ρ*σ^2)) (K/σ) (L/(ρ*σ))
      (fun k₀ l₀ => ξ (σ*k₀) (ρ*σ*l₀))] at h
    exact h
  -- reindexing the d-sum
  have hinj : Set.InjOn (fun d : ℕ => d/(ρ*σ^2))
      ↑((Finset.Icc 1 D).filter (fun d => ρ*σ^2 ∣ d)) := by
    intro a ha b hb hab
    obtain ⟨_, hadvd⟩ := Finset.mem_filter.mp ha
    obtain ⟨_, hbdvd⟩ := Finset.mem_filter.mp hb
    have hab' : a/(ρ*σ^2) = b/(ρ*σ^2) := hab
    calc a = ρ*σ^2 * (a/(ρ*σ^2)) := (Nat.mul_div_cancel' hadvd).symm
      _ = ρ*σ^2 * (b/(ρ*σ^2)) := by rw [hab']
      _ = b := Nat.mul_div_cancel' hbdvd
  have hsum_σ : (∑ m ∈ ((Finset.Icc 1 D).filter (fun d => ρ*σ^2 ∣ d)).image (fun d => d/(ρ*σ^2)),
          (σ:ℝ) * ‖ocSum m (K/σ) (L/(ρ*σ)) (fun k₀ l₀ => ξ (σ*k₀) (ρ*σ*l₀))‖)
      = ∑ m ∈ Finset.Icc 1 (D/(ρ*σ^2)),
          (σ:ℝ) * ‖ocSum m (K/σ) (L/(ρ*σ)) (fun k₀ l₀ => ξ (σ*k₀) (ρ*σ*l₀))‖ := by
    rw [image_div_Icc D (ρ*σ^2) (by positivity)]
  have hstep2 : (∑ d ∈ Finset.Icc 1 D, (if ρ*σ^2 ∣ d then (σ:ℝ) *
        ‖ocSum (d/(ρ*σ^2)) (K/σ) (L/(ρ*σ)) (fun k₀ l₀ => ξ (σ*k₀) (ρ*σ*l₀))‖ else 0))
      = (σ:ℝ) * ∑ m ∈ Finset.Icc 1 (D/(ρ*σ^2)),
          ‖ocSum m (K/σ) (L/(ρ*σ)) (fun k₀ l₀ => ξ (σ*k₀) (ρ*σ*l₀))‖ := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_filter]
    rw [← Finset.sum_image (f := fun m => (σ:ℝ) * ‖ocSum m (K/σ) (L/(ρ*σ))
          (fun k₀ l₀ => ξ (σ*k₀) (ρ*σ*l₀))‖)
          (s := (Finset.Icc 1 D).filter (fun d => ρ*σ^2 ∣ d))
          (g := fun d => d/(ρ*σ^2)) hinj]
    rw [hsum_σ]
  -- the one-class estimate
  have hstep3 : (σ:ℝ) * ∑ m ∈ Finset.Icc 1 (D/(ρ*σ^2)),
        ‖ocSum m (K/σ) (L/(ρ*σ)) (fun k₀ l₀ => ξ (σ*k₀) (ρ*σ*l₀))‖
      ≤ (σ:ℝ) * (C₀ * Real.sqrt (DD * (DD + KK*LL)) * ((DD*KK*LL)^η)
          * Real.sqrt (∑ k ∈ Finset.Icc 1 (K/σ), ∑ l ∈ Finset.Icc 1 (L/(ρ*σ)),
              ‖ξ (σ*k) (ρ*σ*l)‖^2)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact oneClassBound_all hη hC₀ (D/(ρ*σ^2)) (K/σ) (L/(ρ*σ))
      (fun k₀ l₀ => ξ (σ*k₀) (ρ*σ*l₀))
  -- bounds for the reduced ranges
  have hDDle : DD ≤ (D:ℝ)/((ρ:ℝ)*(σ:ℝ)^2) := by
    rw [hDD]
    calc ((D/((ρ*σ^2)) : ℕ) : ℝ) ≤ (D:ℝ)/(((ρ*σ^2) : ℕ) : ℝ) := Nat.cast_div_le
      _ = (D:ℝ)/((ρ:ℝ)*(σ:ℝ)^2) := by push_cast; ring
  have hKKle : KK ≤ (K:ℝ)/(σ:ℝ) := by
    rw [hKK]
    calc ((K/σ : ℕ) : ℝ) ≤ (K:ℝ)/((σ:ℕ):ℝ) := Nat.cast_div_le
      _ = (K:ℝ)/(σ:ℝ) := rfl
  have hLLle : LL ≤ (L:ℝ)/((ρ:ℝ)*(σ:ℝ)) := by
    rw [hLL]
    calc ((L/((ρ*σ)) : ℕ) : ℝ) ≤ (L:ℝ)/(((ρ*σ) : ℕ) : ℝ) := Nat.cast_div_le
      _ = (L:ℝ)/((ρ:ℝ)*(σ:ℝ)) := by push_cast; ring
  have hDDnn : 0 ≤ DD := by rw [hDD]; positivity
  have hKKnn : 0 ≤ KK := by rw [hKK]; positivity
  have hLLnn : 0 ≤ LL := by rw [hLL]; positivity
  have hsum : DD + KK*LL ≤ ((D:ℝ)+((K:ℝ)*(L:ℝ)))/((ρ:ℝ)*(σ:ℝ)^2) := by
    have hKL : KK*LL ≤ ((K:ℝ)*(L:ℝ))/((ρ:ℝ)*(σ:ℝ)^2) := by
      have h := mul_le_mul hKKle hLLle hLLnn (by positivity : (0:ℝ) ≤ (K:ℝ)/(σ:ℝ))
      have h2 : ((K:ℝ)/(σ:ℝ)) * ((L:ℝ)/((ρ:ℝ)*(σ:ℝ))) = ((K:ℝ)*(L:ℝ))/((ρ:ℝ)*(σ:ℝ)^2) := by
        rw [div_mul_div_comm]
        field_simp
      calc KK*LL ≤ ((K:ℝ)/(σ:ℝ)) * ((L:ℝ)/((ρ:ℝ)*(σ:ℝ))) := h
        _ = ((K:ℝ)*(L:ℝ))/((ρ:ℝ)*(σ:ℝ)^2) := h2
    have h3 : ((D:ℝ)/((ρ:ℝ)*(σ:ℝ)^2)) + ((K:ℝ)*(L:ℝ))/((ρ:ℝ)*(σ:ℝ)^2)
        = ((D:ℝ)+((K:ℝ)*(L:ℝ)))/((ρ:ℝ)*(σ:ℝ)^2) := by rw [← add_div]
    calc DD + KK*LL ≤ (D:ℝ)/((ρ:ℝ)*(σ:ℝ)^2) + ((K:ℝ)*(L:ℝ))/((ρ:ℝ)*(σ:ℝ)^2) :=
          add_le_add hDDle hKL
      _ = ((D:ℝ)+((K:ℝ)*(L:ℝ)))/((ρ:ℝ)*(σ:ℝ)^2) := h3
  have hprod : DD * (DD + KK*LL) ≤ ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ)))/((ρ:ℝ)*(σ:ℝ)^2)^2 := by
    have h1 : DD * (DD+KK*LL)
        ≤ ((D:ℝ)/((ρ:ℝ)*(σ:ℝ)^2)) * (((D:ℝ)+((K:ℝ)*(L:ℝ)))/((ρ:ℝ)*(σ:ℝ)^2)) :=
      mul_le_mul hDDle hsum (by positivity) (by positivity)
    have h2 : ((D:ℝ)/((ρ:ℝ)*(σ:ℝ)^2)) * (((D:ℝ)+((K:ℝ)*(L:ℝ)))/((ρ:ℝ)*(σ:ℝ)^2))
        = ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ)))/((ρ:ℝ)*(σ:ℝ)^2)^2 := by
      rw [div_mul_div_comm]; ring
    exact h1.trans (le_of_eq h2)
  have hsqrt1 : (σ:ℝ) * Real.sqrt (DD * (DD + KK*LL))
      ≤ Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) / ((ρ:ℝ)*(σ:ℝ)) := by
    have h2 : Real.sqrt (DD * (DD + KK*LL))
        ≤ Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) / ((ρ:ℝ)*(σ:ℝ)^2) := by
      calc Real.sqrt (DD * (DD + KK*LL))
          ≤ Real.sqrt (((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ)))/((ρ:ℝ)*(σ:ℝ)^2)^2) := Real.sqrt_le_sqrt hprod
        _ = Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) / ((ρ:ℝ)*(σ:ℝ)^2) :=
            sqrt_div_sq _ _ hρσ2R
    have h3 : (σ:ℝ) * (Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) / ((ρ:ℝ)*(σ:ℝ)^2))
        = Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) / ((ρ:ℝ)*(σ:ℝ)) := by
      field_simp
    calc (σ:ℝ) * Real.sqrt (DD * (DD + KK*LL))
        ≤ (σ:ℝ) * (Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) / ((ρ:ℝ)*(σ:ℝ)^2)) :=
          mul_le_mul_of_nonneg_left h2 (le_of_lt hσR)
      _ = Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) / ((ρ:ℝ)*(σ:ℝ)) := h3
  have hDDK : DD ≤ (D:ℝ) := by rw [hDD]; exact_mod_cast Nat.div_le_self D (ρ*σ^2)
  have hKKK : KK ≤ (K:ℝ) := by rw [hKK]; exact_mod_cast Nat.div_le_self K σ
  have hLLL : LL ≤ (L:ℝ) := by rw [hLL]; exact_mod_cast Nat.div_le_self L (ρ*σ)
  have hWnn : (0:ℝ) ≤ (D:ℝ)*(K:ℝ)*(L:ℝ) := by positivity
  have hDDKL : (DD*KK*LL)^η ≤ ((D:ℝ)*(K:ℝ)*(L:ℝ))^η := by
    refine Real.rpow_le_rpow (by positivity) ?_ (le_of_lt hη)
    calc DD*KK*LL ≤ ((D:ℝ)*(K:ℝ))*(L:ℝ) :=
          mul_le_mul (mul_le_mul hDDK hKKK hKKnn (by positivity)) hLLL hLLnn (by positivity)
      _ = (D:ℝ)*(K:ℝ)*(L:ℝ) := by ring
  calc (∑ d ∈ Finset.Icc 1 D, ‖∑ l ∈ Finset.Icc 1 L, (if Nat.gcd d (l^2) = ρ*σ^2 then
        ∑ k ∈ Finset.Icc 1 K, ξ k l * rhoRoot d k l else 0)‖)
      ≤ ∑ d ∈ Finset.Icc 1 D, (if ρ*σ^2 ∣ d then (σ:ℝ) * ‖ocSum (d/(ρ*σ^2)) (K/σ) (L/(ρ*σ))
            (fun k₀ l₀ => ξ (σ*k₀) (ρ*σ*l₀))‖ else 0) := Finset.sum_le_sum hstep1
    _ = (σ:ℝ) * ∑ m ∈ Finset.Icc 1 (D/(ρ*σ^2)),
          ‖ocSum m (K/σ) (L/(ρ*σ)) (fun k₀ l₀ => ξ (σ*k₀) (ρ*σ*l₀))‖ := hstep2
    _ ≤ (σ:ℝ) * (C₀ * Real.sqrt (DD * (DD + KK*LL)) * ((DD*KK*LL)^η)
          * Real.sqrt (∑ k ∈ Finset.Icc 1 (K/σ), ∑ l ∈ Finset.Icc 1 (L/(ρ*σ)),
              ‖ξ (σ*k) (ρ*σ*l)‖^2)) := hstep3
    _ ≤ C₀ * (((D:ℝ)*(K:ℝ)*(L:ℝ))^η)
          * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2)
          * (Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) / ((ρ:ℝ)*(σ:ℝ))) := by
        have hA := xi_norm_le K L σ ρ hρpos hσ ξ
        have hBnn : 0 ≤ Real.sqrt (DD * (DD + KK*LL)) := Real.sqrt_nonneg _
        have hσB : 0 ≤ (σ:ℝ) * Real.sqrt (DD * (DD + KK*LL)) :=
          mul_nonneg (le_of_lt hσR) hBnn
        have hinner1 : C₀ * ((DD*KK*LL)^η)
              * Real.sqrt (∑ k ∈ Finset.Icc 1 (K/σ), ∑ l ∈ Finset.Icc 1 (L/(ρ*σ)),
                  ‖ξ (σ*k) (ρ*σ*l)‖^2)
            ≤ C₀ * (((D:ℝ)*(K:ℝ)*(L:ℝ))^η)
              * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hDDKL hC₀nn) hA (Real.sqrt_nonneg _)
            (by positivity)
        calc (σ:ℝ) * (C₀ * Real.sqrt (DD * (DD + KK*LL)) * ((DD*KK*LL)^η) * Real.sqrt (∑ k ∈ Finset.Icc 1 (K/σ), ∑ l ∈ Finset.Icc 1 (L/(ρ*σ)), ‖ξ (σ*k) (ρ*σ*l)‖^2)) = (C₀ * ((DD*KK*LL)^η) * Real.sqrt (∑ k ∈ Finset.Icc 1 (K/σ), ∑ l ∈ Finset.Icc 1 (L/(ρ*σ)), ‖ξ (σ*k) (ρ*σ*l)‖^2)) * ((σ:ℝ) * Real.sqrt (DD * (DD + KK*LL))) := by ring
          _ ≤ (C₀ * (((D:ℝ)*(K:ℝ)*(L:ℝ))^η)
                * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2))
              * (Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) / ((ρ:ℝ)*(σ:ℝ))) :=
              mul_le_mul hinner1 hsqrt1 hσB (by positivity)
          _ = C₀ * (((D:ℝ)*(K:ℝ)*(L:ℝ))^η)
              * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2)
              * (Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) / ((ρ:ℝ)*(σ:ℝ))) := by ring

/-- `√(a (a + b)) ≤ a + √(a b)` for `a, b ≥ 0`. -/
private lemma sqrt_mul_self_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a*(a+b)) ≤ a + Real.sqrt (a*b) := by
  rw [Real.sqrt_le_left (by positivity)]
  have h2 := Real.sq_sqrt (mul_nonneg ha hb)
  have h3 : 0 ≤ Real.sqrt (a*b) := Real.sqrt_nonneg _
  nlinarith [h2, h3, ha, hb, mul_nonneg ha hb, sq_nonneg (Real.sqrt (a*b)), sq_nonneg a]

/-- `(1 + log n) ^ 4 ≤ C n ^ (η/2)` for `η > 0`, `n ≥ 1`. -/
private lemma log_rpow_bound (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → (1 + Real.log (n:ℝ))^4 ≤ C * (n:ℝ)^(η/2) := by
  set s : ℝ := η/8 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  refine ⟨(1 + 1/s)^4 + 1, by positivity, fun n hn => ?_⟩
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hlog : 1 + Real.log (n:ℝ) ≤ (1 + 1/s) * (n:ℝ)^s := by
    have h := Real.log_le_rpow_div (x := (n:ℝ)) (by positivity) hs0
    have hpow : (1:ℝ) ≤ (n:ℝ)^s := Real.one_le_rpow hn1 (le_of_lt hs0)
    calc 1 + Real.log (n:ℝ) ≤ 1 + (n:ℝ)^s / s := by linarith [h]
      _ = 1 + (1/s) * (n:ℝ)^s := by ring
      _ ≤ (n:ℝ)^s + (1/s) * (n:ℝ)^s := by
          have := add_le_add_right hpow ((1/s) * (n:ℝ)^s)
          linarith
      _ = (1 + 1/s) * (n:ℝ)^s := by ring
  have hnn : 0 ≤ 1 + Real.log (n:ℝ) := by
    have := Real.log_nonneg hn1; linarith
  have h4 : (1 + Real.log (n:ℝ))^4 ≤ ((1 + 1/s) * (n:ℝ)^s)^4 := pow_le_pow_left₀ hnn hlog 4
  have hpow4 : ((1 + 1/s) * (n:ℝ)^s)^4 = (1 + 1/s)^4 * (n:ℝ)^(η/2) := by
    rw [mul_pow, ← Real.rpow_natCast ((n:ℝ)^s) 4,
      ← Real.rpow_mul (by positivity : (0:ℝ) ≤ (n:ℝ))]
    congr 1
    push_cast
    rw [hs]
    ring
  rw [hpow4] at h4
  refine h4.trans ?_
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by positivity) _)

/-- `∑_{n ≤ D} 1/n ≤ (1 + log D) ^ 2`. -/
private lemma harmonic_inv_le (D : ℕ) (hD : 1 ≤ D) :
    (∑ n ∈ Finset.Icc 1 D, (1:ℝ)/(n:ℝ)) ≤ (1 + Real.log D)^2 := by
  refine le_trans ?_ (Commons.NumberTheory.DivisorSum.sum_divisor_count_div_le D hD)
  refine Finset.sum_le_sum (fun n hn => ?_)
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hcard : (1:ℝ) ≤ ((Nat.divisors n).card : ℝ) := by
    have h1 : 1 ≤ (Nat.divisors n).card :=
      Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩⟩
    exact_mod_cast h1
  have hnpos : (0:ℝ) ≤ (n:ℝ) := by positivity
  exact div_le_div_of_nonneg_right hcard hnpos

/-- `∑_{p ∈ Bset} 1/(p₁ p₂) ≤ (1 + log D) ^ 4`. -/
private lemma Bset_inv_sum_le (D : ℕ) (hD : 1 ≤ D) :
    (∑ p ∈ (((Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D))).filter (fun p : ℕ × ℕ => Squarefree p.1),
        (1:ℝ)/((p.1:ℝ)*(p.2:ℝ)))
      ≤ (1 + Real.log D)^4 := by
  have h1 : (∑ p ∈ (((Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D))).filter
        (fun p : ℕ × ℕ => Squarefree p.1), (1:ℝ)/((p.1:ℝ)*(p.2:ℝ)))
      ≤ ∑ p ∈ ((Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D)), (1:ℝ)/((p.1:ℝ)*(p.2:ℝ)) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun p _ _ => by positivity)
  have h2 : (∑ p ∈ ((Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D)), (1:ℝ)/((p.1:ℝ)*(p.2:ℝ)))
      = (∑ a ∈ Finset.Icc 1 D, (1:ℝ)/(a:ℝ)) * (∑ b ∈ Finset.Icc 1 D, (1:ℝ)/(b:ℝ)) := by
    rw [Finset.sum_product]
    have hL : (∑ x ∈ Finset.Icc 1 D, ∑ y ∈ Finset.Icc 1 D,
          (1:ℝ) / ((((x,y):ℕ×ℕ).1:ℝ) * (((x,y):ℕ×ℕ).2:ℝ)))
        = ∑ x ∈ Finset.Icc 1 D, ∑ y ∈ Finset.Icc 1 D, (1:ℝ)/(x:ℝ) * ((1:ℝ)/(y:ℝ)) := by
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
      simp only [Prod.fst, Prod.snd, one_div, ← mul_inv]
    rw [hL, ← Finset.sum_mul_sum]
  have h3 : (∑ a ∈ Finset.Icc 1 D, (1:ℝ)/(a:ℝ)) * (∑ b ∈ Finset.Icc 1 D, (1:ℝ)/(b:ℝ))
      ≤ (1 + Real.log D)^2 * (1 + Real.log D)^2 :=
    mul_le_mul (harmonic_inv_le D hD) (harmonic_inv_le D hD) (by positivity) (by positivity)
  calc (∑ p ∈ (((Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D))).filter
        (fun p : ℕ × ℕ => Squarefree p.1), (1:ℝ)/((p.1:ℝ)*(p.2:ℝ)))
      ≤ ∑ p ∈ ((Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D)), (1:ℝ)/((p.1:ℝ)*(p.2:ℝ)) := h1
    _ = (∑ a ∈ Finset.Icc 1 D, (1:ℝ)/(a:ℝ)) * (∑ b ∈ Finset.Icc 1 D, (1:ℝ)/(b:ℝ)) := h2
    _ ≤ (1 + Real.log D)^2 * (1 + Real.log D)^2 := h3
    _ = (1 + Real.log D)^4 := by ring
/-- **Assembly.**  Summing the one-class bounds over the fibre classes `(p₁,p₂)`. -/
private lemma assembly_bound {C₀ Cl η eps : ℝ} (hC₀nn : 0 ≤ C₀) (hClpos : 0 < Cl)
    (hηpos : 0 < η) (hC₀ : OneClassBound C₀ η)
    (hCl : ∀ n : ℕ, 1 ≤ n → (1 + Real.log (n:ℝ))^4 ≤ Cl * (n:ℝ)^(η/2))
    (heps : 3*η/2 ≤ eps)
    (D K L : ℕ) (hD : 1 ≤ D) (hK : 1 ≤ K) (hL : 1 ≤ L) (ξ : ℕ → ℕ → ℂ) :
    (∑ d ∈ Finset.Icc 1 D, ‖∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L,
        ξ k l * rhoRoot d k l‖)
      ≤ C₀ * Cl * ((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*(L:ℝ)))
          * (((D:ℝ)*(K:ℝ)*(L:ℝ))^eps)
          * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2) := by
  classical
  set Bs : Finset (ℕ × ℕ) :=
    ((Finset.Icc 1 D) ×ˢ (Finset.Icc 1 D)).filter (fun p : ℕ × ℕ => Squarefree p.1) with hBs
  have hW1 : (1:ℝ) ≤ (D:ℝ)*(K:ℝ)*(L:ℝ) := by
    have h1 : (1:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
    have h2 : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
    have h3 : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
    have h4 : (0:ℝ) ≤ (D:ℝ) := by linarith
    have h5 : (0:ℝ) ≤ (L:ℝ) := by linarith
    have h6 : (0:ℝ) ≤ (D:ℝ)*(K:ℝ) := by positivity
    calc (1:ℝ) = 1*1*1 := by norm_num
      _ ≤ (D:ℝ)*(K:ℝ)*(L:ℝ) :=
          mul_le_mul (mul_le_mul h1 h2 (by norm_num) h4) h3 (by norm_num) h6
  have hAnc : (0:ℝ) ≤ Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2) :=
    Real.sqrt_nonneg _
  -- Step 1: triangle inequality over the fibre classes
  have hpt : ∀ d ∈ Finset.Icc 1 D,
      ‖∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ξ k l * rhoRoot d k l‖
      ≤ ∑ p ∈ Bs, ‖∑ l ∈ Finset.Icc 1 L, (if Nat.gcd d (l^2) = p.1*p.2^2 then
            ∑ k ∈ Finset.Icc 1 K, ξ k l * rhoRoot d k l else 0)‖ := by
    intro d hdmem
    have hdD : d ≤ D := (Finset.mem_Icc.mp hdmem).2
    have hdpos : 0 < d := by have := (Finset.mem_Icc.mp hdmem).1; omega
    have hpart := partition_identity d L D K ξ hdpos hdD
    rw [hBs.symm] at hpart
    calc ‖∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ξ k l * rhoRoot d k l‖
        = ‖∑ l ∈ Finset.Icc 1 L, ∑ k ∈ Finset.Icc 1 K, ξ k l * rhoRoot d k l‖ := by
          rw [Finset.sum_comm]
      _ = ‖∑ p ∈ Bs, ∑ l ∈ Finset.Icc 1 L, (if Nat.gcd d (l^2) = p.1*p.2^2 then
            ∑ k ∈ Finset.Icc 1 K, ξ k l * rhoRoot d k l else 0)‖ := by rw [hpart]
      _ ≤ ∑ p ∈ Bs, ‖∑ l ∈ Finset.Icc 1 L, (if Nat.gcd d (l^2) = p.1*p.2^2 then
            ∑ k ∈ Finset.Icc 1 K, ξ k l * rhoRoot d k l else 0)‖ := norm_sum_le _ _
  -- Step 2: the one-class bound for each class
  have hp : ∀ p ∈ Bs, (∑ d ∈ Finset.Icc 1 D, ‖∑ l ∈ Finset.Icc 1 L,
        (if Nat.gcd d (l^2) = p.1*p.2^2 then
          ∑ k ∈ Finset.Icc 1 K, ξ k l * rhoRoot d k l else 0)‖)
      ≤ C₀ * (((D:ℝ)*(K:ℝ)*(L:ℝ))^η)
          * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2)
          * (Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) / ((p.1:ℝ)*(p.2:ℝ))) := by
    intro p hpB
    rw [hBs] at hpB
    obtain ⟨hpmem, hpsq⟩ := Finset.mem_filter.mp hpB
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpmem
    have hp2pos : 0 < p.2 := by have := (Finset.mem_Icc.mp hp2).1; omega
    exact fibre_total_le hC₀nn hηpos hC₀ D K L hD hK hL ξ p.1 p.2 hpsq hp2pos
  -- Step 3: summing over the classes
  have hsum1 : (∑ p ∈ Bs, (∑ d ∈ Finset.Icc 1 D, ‖∑ l ∈ Finset.Icc 1 L,
        (if Nat.gcd d (l^2) = p.1*p.2^2 then
          ∑ k ∈ Finset.Icc 1 K, ξ k l * rhoRoot d k l else 0)‖))
      ≤ C₀ * (((D:ℝ)*(K:ℝ)*(L:ℝ))^η)
          * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2)
          * (Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ)))
              * (∑ p ∈ Bs, (1:ℝ)/((p.1:ℝ)*(p.2:ℝ)))) := by
    calc (∑ p ∈ Bs, (∑ d ∈ Finset.Icc 1 D, ‖∑ l ∈ Finset.Icc 1 L,
        (if Nat.gcd d (l^2) = p.1*p.2^2 then
          ∑ k ∈ Finset.Icc 1 K, ξ k l * rhoRoot d k l else 0)‖))
        ≤ ∑ p ∈ Bs, C₀ * (((D:ℝ)*(K:ℝ)*(L:ℝ))^η)
            * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2)
            * (Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) / ((p.1:ℝ)*(p.2:ℝ))) :=
          Finset.sum_le_sum hp
      _ = C₀ * (((D:ℝ)*(K:ℝ)*(L:ℝ))^η)
            * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2)
            * (Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ)))
                * (∑ p ∈ Bs, (1:ℝ)/((p.1:ℝ)*(p.2:ℝ)))) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl (fun p _ => ?_)
          ring
  -- Step 4: the harmonic bound
  have hBsle : (∑ p ∈ Bs, (1:ℝ)/((p.1:ℝ)*(p.2:ℝ))) ≤ (1 + Real.log D)^4 := by
    have h := Bset_inv_sum_le D hD
    rw [hBs.symm] at h
    exact h
  -- Step 5: the log absorption and the exponent comparison
  have hXle : Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ)))
      ≤ (D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*(L:ℝ)) := by
    have h := sqrt_mul_self_add_le (D:ℝ) ((K:ℝ)*(L:ℝ)) (by positivity) (by positivity)
    rwa [show (D:ℝ)*((K:ℝ)*(L:ℝ)) = (D:ℝ)*(K:ℝ)*(L:ℝ) from by ring] at h
  have hClog : (1 + Real.log (D:ℝ))^4 ≤ Cl * ((D:ℝ)*(K:ℝ)*(L:ℝ))^(η/2) := by
    have h := hCl D hD
    have hKL1 : (1:ℝ) ≤ (K:ℝ)*(L:ℝ) := by
      have h2 : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK
      have h3 : (1:ℝ) ≤ (L:ℝ) := by exact_mod_cast hL
      nlinarith
    have hDpos : (0:ℝ) < D := by exact_mod_cast (by omega : 0 < D)
    have hDle : (D:ℝ) ≤ (D:ℝ)*(K:ℝ)*(L:ℝ) := by nlinarith
    calc (1 + Real.log (D:ℝ))^4 ≤ Cl * (D:ℝ)^(η/2) := h
      _ ≤ Cl * ((D:ℝ)*(K:ℝ)*(L:ℝ))^(η/2) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_of_lt hDpos) hDle (by positivity))
            (le_of_lt hClpos)
  have hcomb : C₀ * (((D:ℝ)*(K:ℝ)*(L:ℝ))^η)
        * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2)
        * (Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) * (1 + Real.log D)^4)
      ≤ C₀ * Cl * ((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*(L:ℝ)))
          * (((D:ℝ)*(K:ℝ)*(L:ℝ))^eps)
          * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2) := by
    set W : ℝ := (D:ℝ)*(K:ℝ)*(L:ℝ) with hW
    set A : ℝ := Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2) with hA
    have hWpos : (0:ℝ) < W := by rw [hW]; positivity
    have hAnn : 0 ≤ A := by rw [hA]; exact Real.sqrt_nonneg _
    have hlog' : W^η * (1 + Real.log (D:ℝ))^4 ≤ Cl * W^(3*η/2) := by
      have h2 : W^η * W^(η/2) = W^(3*η/2) := by
        rw [← Real.rpow_add (by rw [hW]; positivity)]
        congr 1; ring
      calc W^η * (1 + Real.log (D:ℝ))^4 ≤ W^η * (Cl * W^(η/2)) :=
            mul_le_mul_of_nonneg_left hClog (by rw [hW]; positivity)
        _ = Cl * (W^η * W^(η/2)) := by ring
        _ = Cl * W^(3*η/2) := by rw [h2]
    have hX : Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) ≤ (D:ℝ) + Real.sqrt W := by
      rw [hW]; exact hXle
    have hstep1 : C₀ * W^η * A * Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) * (1 + Real.log D)^4
        ≤ C₀ * W^η * A * ((D:ℝ) + Real.sqrt W) * (1 + Real.log D)^4 := by
      have hnn : 0 ≤ C₀ * W^η * A * (1 + Real.log D)^4 := by positivity
      calc C₀ * W^η * A * Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) * (1 + Real.log D)^4
          = (C₀ * W^η * A * (1 + Real.log D)^4) * Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) := by ring
        _ ≤ (C₀ * W^η * A * (1 + Real.log D)^4) * ((D:ℝ) + Real.sqrt W) :=
            mul_le_mul_of_nonneg_left hX hnn
        _ = C₀ * W^η * A * ((D:ℝ) + Real.sqrt W) * (1 + Real.log D)^4 := by ring
    have hstep2 : C₀ * W^η * A * ((D:ℝ) + Real.sqrt W) * (1 + Real.log D)^4
        ≤ C₀ * A * ((D:ℝ) + Real.sqrt W) * (Cl * W^(3*η/2)) := by
      calc C₀ * W^η * A * ((D:ℝ) + Real.sqrt W) * (1 + Real.log D)^4
          = (C₀ * A * ((D:ℝ) + Real.sqrt W)) * (W^η * (1 + Real.log D)^4) := by ring
        _ ≤ (C₀ * A * ((D:ℝ) + Real.sqrt W)) * (Cl * W^(3*η/2)) := by
            refine mul_le_mul_of_nonneg_left hlog' ?_
            exact mul_nonneg (mul_nonneg hC₀nn hAnn) (by positivity)
        _ = C₀ * A * ((D:ℝ) + Real.sqrt W) * (Cl * W^(3*η/2)) := by ring
    have hstep3 : C₀ * A * ((D:ℝ) + Real.sqrt W) * (Cl * W^(3*η/2))
        ≤ C₀ * Cl * ((D:ℝ) + Real.sqrt W) * W^eps * A := by
      have hpowe : W^(3*η/2) ≤ W^eps :=
        Real.rpow_le_rpow_of_exponent_le (by rw [hW]; exact hW1) heps
      calc C₀ * A * ((D:ℝ) + Real.sqrt W) * (Cl * W^(3*η/2))
          = C₀ * Cl * ((D:ℝ) + Real.sqrt W) * (W^(3*η/2) * A) := by ring
        _ ≤ C₀ * Cl * ((D:ℝ) + Real.sqrt W) * (W^eps * A) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right hpowe hAnn
        _ = C₀ * Cl * ((D:ℝ) + Real.sqrt W) * W^eps * A := by ring
    calc C₀ * (((D:ℝ)*(K:ℝ)*(L:ℝ))^η)
          * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2)
          * (Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) * (1 + Real.log D)^4)
        = C₀ * W^η * A * Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) * (1 + Real.log D)^4 := by
          rw [hW, hA]; ring
      _ ≤ C₀ * W^η * A * ((D:ℝ) + Real.sqrt W) * (1 + Real.log D)^4 := hstep1
      _ ≤ C₀ * A * ((D:ℝ) + Real.sqrt W) * (Cl * W^(3*η/2)) := hstep2
      _ ≤ C₀ * Cl * ((D:ℝ) + Real.sqrt W) * W^eps * A := hstep3
      _ = C₀ * Cl * ((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*(L:ℝ)))
          * (((D:ℝ)*(K:ℝ)*(L:ℝ))^eps)
          * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2) := by
          rw [hW, hA]
  -- combine
  calc (∑ d ∈ Finset.Icc 1 D, ‖∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L,
        ξ k l * rhoRoot d k l‖)
      ≤ ∑ p ∈ Bs, ∑ d ∈ Finset.Icc 1 D, ‖∑ l ∈ Finset.Icc 1 L,
          (if Nat.gcd d (l^2) = p.1*p.2^2 then
            ∑ k ∈ Finset.Icc 1 K, ξ k l * rhoRoot d k l else 0)‖ :=
        (Finset.sum_le_sum hpt).trans Finset.sum_comm.le
    _ ≤ C₀ * (((D:ℝ)*(K:ℝ)*(L:ℝ))^η)
          * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2)
          * (Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ)))
              * (∑ p ∈ Bs, (1:ℝ)/((p.1:ℝ)*(p.2:ℝ)))) := hsum1
    _ ≤ C₀ * (((D:ℝ)*(K:ℝ)*(L:ℝ))^η)
          * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2)
          * (Real.sqrt ((D:ℝ)*((D:ℝ)+(K:ℝ)*(L:ℝ))) * (1 + Real.log D)^4) := by
        have hnn : 0 ≤ C₀ * (((D:ℝ)*(K:ℝ)*(L:ℝ))^η)
            * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2) := by positivity
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hBsle (Real.sqrt_nonneg _)) hnn
    _ ≤ C₀ * Cl * ((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*(L:ℝ)))
          * (((D:ℝ)*(K:ℝ)*(L:ℝ))^eps)
          * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2) := hcomb
/-- **Friedlander–Iwaniec, Lemma 3.3.**  The linear form in `ρ(k,l;d)` is bounded by
`(D + √(DKL))(DKL)^ε ‖ξ‖`, uniformly in `D,K,L`. -/
theorem linear_form_rho_bound_uniform (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D K L : ℕ), 1 ≤ D → 1 ≤ K → 1 ≤ L → ∀ ξ : ℕ → ℕ → ℂ,
      (∑ d ∈ Finset.Icc 1 D, ‖∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L,
          ξ k l * ∑ ν ∈ (Finset.range d).filter (fun ν : ℕ => (ν^2 + l^2) % d = 0),
            Commons.Analysis.ExponentialSums.ch ((ν:ℝ) * (k:ℝ) / d)‖)
        ≤ C * ((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*(L:ℝ))) * ((D:ℝ)*(K:ℝ)*(L:ℝ))^eps
            * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2) := by
  have hηpos : 0 < eps/4 := by linarith
  obtain ⟨C₀, hC₀pos, hC₀⟩ :=
    Commons.NumberTheory.FriedlanderIwaniec.reduced_linear_form_uniform (eps/4) hηpos
  have hOC : OneClassBound C₀ (eps/4) := fun D K L hD hK hL ξ => by
    simpa only [OneClassBound, ocSum, oneClass, Nat.cast_mul] using hC₀ D K L hD hK hL ξ
  obtain ⟨Cl, hClpos, hCl⟩ := log_rpow_bound (eps/4) hηpos
  refine ⟨C₀ * Cl + 1, by positivity, ?_⟩
  intro D K L hD hK hL ξ
  have hmain := assembly_bound (le_of_lt hC₀pos) hClpos hηpos hOC hCl
    (by linarith : 3*(eps/4)/2 ≤ eps) D K L hD hK hL ξ
  have h2 : C₀ * Cl * ((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*(L:ℝ)))
        * (((D:ℝ)*(K:ℝ)*(L:ℝ))^eps)
        * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2)
      ≤ (C₀ * Cl + 1) * ((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*(L:ℝ)))
        * (((D:ℝ)*(K:ℝ)*(L:ℝ))^eps)
        * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2) := by
    have h1 : C₀ * Cl ≤ C₀ * Cl + 1 := by linarith
    have hnn : (0:ℝ) ≤ ((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*(L:ℝ)))
        * (((D:ℝ)*(K:ℝ)*(L:ℝ))^eps)
        * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2) := by
      positivity
    calc C₀ * Cl * ((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*(L:ℝ)))
          * (((D:ℝ)*(K:ℝ)*(L:ℝ))^eps)
          * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2)
        = (C₀ * Cl) * (((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*(L:ℝ)))
            * (((D:ℝ)*(K:ℝ)*(L:ℝ))^eps)
            * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2)) := by ring
      _ ≤ (C₀ * Cl + 1) * (((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*(L:ℝ)))
            * (((D:ℝ)*(K:ℝ)*(L:ℝ))^eps)
            * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2)) :=
          mul_le_mul_of_nonneg_right h1 hnn
      _ = (C₀ * Cl + 1) * ((D:ℝ) + Real.sqrt ((D:ℝ)*(K:ℝ)*(L:ℝ)))
          * (((D:ℝ)*(K:ℝ)*(L:ℝ))^eps)
          * Real.sqrt (∑ k ∈ Finset.Icc 1 K, ∑ l ∈ Finset.Icc 1 L, ‖ξ k l‖^2) := by ring
  exact hmain.trans h2

end Commons.NumberTheory.FriedlanderIwaniec
