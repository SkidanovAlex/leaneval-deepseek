/-
# `Submission.Work.FIArea7.reflection_pair_betaPrime_general` — the reflection identity in the
twisted coefficient `β'`, *without* the sign hypothesis `0 < r₁r₂`

`Work.FIArea7.reflection_pair_betaPrime` proves the pair identity of *FI* §17 under the paper's
hypothesis (17.4) `0 < r₁r₂` (the points `z₁, z₂` lying in the same half-plane).  The frozen
area-7 sums run over polar boxes (`Work.FIPlan.PolarBox`, (5.12)) with an arbitrary phase `φ`, so
a pair in one box may well have `r₁r₂ < 0`; the missing case is restored here by the explicit
sign `Work.FIArea7.reflSign z₁ z₂ = sign(r₁)·sign(Δ(z₁,z₂))` (see `NOTES.md` §11bis/§11ter).

Concretely, the *arithmetic core* of Lemma 17.1 in the opposite-sign case is: with
`u_i = |r_i|` (so `u₁ + u₂ ≡ 0 (mod 4)` when `r₁ ≡ r₂ (mod 4)` have opposite signs),
`Δ = u₁s₂ + u₂s₁`,

  `J(-(u₁u₂) | |Δ|)·χ₂(u₁u₂)^{ν₂(|Δ|)} = sign(Δ)·(s₁|u₁)(s₂|u₂)`

(`Work.FIArea7.kronCore_neg`), the companion of `Work.FIArea7.kronCore`; the 2-adic correction is
`Work.FIArea7.kronEight_neg` (the companion of `Work.FIArea7.kronEight`).
-/
import Mathlib
import Submission.Work.FIArea7.ReflectAlg
import Submission.Work.FIArea7.jacobiSym_reflection_mod4
import Submission.Work.FIArea7.KronTwo
import Submission.Work.FIArea7.FIsymbols
import Submission.Work.FIArea7.reflBook
import Submission.Work.FIArea7.kronCore_neg
import Submission.Work.FIArea7.kronEight_neg

namespace Work.FIArea7

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. Two elementary facts about `χ₂ = kronTwo` -/

/-- `χ₂(-a) = χ₂(a)` (`-1` lies in the kernel of `χ₈`). -/
lemma kronTwo_neg (a : ℤ) : kronTwo (-a) = kronTwo a := by
  have h : (-a : ℤ) = (-1) * a := by ring
  rw [h, kronTwo_mul]
  norm_num [kronTwo]

/-- `|z|² = r² + s²` as an integer (coordinate form of `gnorm`). -/
lemma gnorm_int_coord (z : GaussianInt) : (Work.FIPlan.gnorm z : ℤ) = z.re ^ 2 + z.im ^ 2 :=
  gnorm_int' z

/-! ## 2. The core identity, general sign -/

/-- **The arithmetic core of *FI* Lemma 17.1 without a sign hypothesis on `r₁r₂`.**

  `(Re(z̄₁z₂) | |Δ|)·(|z₁|² | |Δ|) = (χ₂(Re(z̄₁z₂))χ₂(|z₁|²))^{ν₂(|Δ|)}·reflSign(z₁,z₂)·(s₁/|r₁|)(s₂/|r₂|)`

where the correction `reflSign(z₁,z₂)` is `1` when `0 < r₁r₂` and `sign(r₁)sign(Δ(z₁,z₂))`
otherwise.  This is the `mod 4` form of Lemma 17.1 valid for *ordered* pairs of the frozen
area-7 boxes (both signs of `r₁r₂` and of `Δ`). -/
theorem jacobiSym_reflection_mod4_general {z1 z2 : GaussianInt}
    (hP1 : Work.FIPlan.IsPrimary z1) (hP2 : Work.FIPlan.IsPrimary z2)
    (hs1 : Squarefree (Work.FIPlan.gnorm z1)) (hs2 : Squarefree (Work.FIPlan.gnorm z2))
    (hc : IsCoprime z1 z2)
    (hcc : IsCoprime ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ))
    (h4r : z1.re ≡ z2.re [ZMOD 4]) (h4i : z1.im ≡ z2.im [ZMOD 4])
    (hr1 : z1.re ≠ 0) (hr2 : z2.re ≠ 0) (hD : 0 < Work.FIPlan.absDelta z1 z2) :
    jacobiSym (z1.re * z2.re + z1.im * z2.im) (Work.FIPlan.absDelta z1 z2)
        * jacobiSym ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) (Work.FIPlan.absDelta z1 z2)
      = (Work.FIArea7.kronTwo (z1.re * z2.re + z1.im * z2.im)
          * Work.FIArea7.kronTwo ((Work.FIPlan.gnorm z1 : ℕ) : ℤ))
          ^ ((Work.FIPlan.absDelta z1 z2).factorization 2)
        * Work.FIArea7.reflSign z1 z2
        * (jacobiSym z1.im z1.re.natAbs * jacobiSym z2.im z2.re.natAbs) := by
  rcases lt_trichotomy (z1.re * z2.re) 0 with hneg | hzero | hpos
  · -- **Case II**: `r₁r₂ < 0`  (the sign the frozen area-7 boxes may carry)
    obtain ⟨hr1odd, hs1even, _⟩ := hP1
    obtain ⟨hr2odd, hs2even, _⟩ := hP2
    have hcop1 : (z1.re.natAbs).Coprime (z1.im.natAbs) := coprime_coords_of_sqfree' hs1
    have hcop2 : (z2.re.natAbs).Coprime (z2.im.natAbs) := coprime_coords_of_sqfree' hs2
    have hsigns : (0 < z1.re ∧ z2.re < 0) ∨ (z1.re < 0 ∧ 0 < z2.re) := by
      rcases lt_trichotomy z1.re 0 with h | h | h
      · rcases lt_trichotomy z2.re 0 with h2 | h2 | h2
        · exact absurd (mul_pos_of_neg_of_neg h h2) (by linarith)
        · exact absurd h2 hr2
        · exact Or.inr ⟨h, h2⟩
      · exact absurd h hr1
      · rcases lt_trichotomy z2.re 0 with h2 | h2 | h2
        · exact Or.inl ⟨h, h2⟩
        · exact absurd h2 hr2
        · exact absurd (mul_pos h h2) (by linarith)
    -- the coordinates, the common divisor `g = (|r₁|,|r₂|)` and the reduced parts
    set a1 : ℕ := z1.re.natAbs with ha1
    set a2 : ℕ := z2.re.natAbs with ha2
    have ha1ne : a1 ≠ 0 := by rw [ha1]; exact Int.natAbs_ne_zero.mpr hr1
    have ha2ne : a2 ≠ 0 := by rw [ha2]; exact Int.natAbs_ne_zero.mpr hr2
    have hodd1 : Odd a1 := by rw [ha1]; exact hr1odd.natAbs
    have hodd2 : Odd a2 := by rw [ha2]; exact hr2odd.natAbs
    set g : ℕ := a1.gcd a2 with hg
    have hgd1 : g ∣ a1 := by rw [hg]; exact Nat.gcd_dvd_left _ _
    have hgd2 : g ∣ a2 := by rw [hg]; exact Nat.gcd_dvd_right _ _
    have hgpos : 0 < g := Nat.pos_of_dvd_of_pos hgd1 (Nat.pos_of_ne_zero ha1ne)
    have hgne : g ≠ 0 := hgpos.ne'
    set w1 : ℕ := a1 / g with hw1
    set w2 : ℕ := a2 / g with hw2
    have hgw1 : g * w1 = a1 := by rw [hw1]; exact Nat.mul_div_cancel' hgd1
    have hgw2 : g * w2 = a2 := by rw [hw2]; exact Nat.mul_div_cancel' hgd2
    have hoddw1 : Odd w1 := (Nat.odd_mul.mp (by rw [hgw1]; exact hodd1)).2
    have hoddw2 : Odd w2 := (Nat.odd_mul.mp (by rw [hgw2]; exact hodd2)).2
    have hoddg : Odd g := (Nat.odd_mul.mp (by rw [hgw1]; exact hodd1)).1
    have hwd1 : w1 ∣ a1 := ⟨g, by rw [mul_comm, hgw1]⟩
    have hwd2 : w2 ∣ a2 := ⟨g, by rw [mul_comm, hgw2]⟩
    have hw12 : w1.Coprime w2 := by rw [hw1, hw2, hg]; exact Nat.coprime_div_gcd_div_gcd hgpos
    have hgs1 : g.Coprime z1.im.natAbs := hcop1.coprime_dvd_left hgd1
    have hgs2 : g.Coprime z2.im.natAbs := hcop2.coprime_dvd_left hgd2
    have hws1 : w1.Coprime z1.im.natAbs := hcop1.coprime_dvd_left hwd1
    have hws2 : w2.Coprime z2.im.natAbs := hcop2.coprime_dvd_left hwd2
    have ha1c : (a1 : ℤ) = (g : ℤ) * (w1 : ℤ) := by rw [← hgw1]; push_cast; ring
    have ha2c : (a2 : ℤ) = (g : ℤ) * (w2 : ℤ) := by rw [← hgw2]; push_cast; ring
    have hgposZ : (0 : ℤ) < (g : ℤ) := by exact_mod_cast hgpos
    -- the two signs
    have hr1a : 0 < z1.re → (a1 : ℤ) = z1.re := fun h => by
      rw [ha1]; exact Int.natAbs_of_nonneg (le_of_lt h)
    have hr1b : z1.re < 0 → (a1 : ℤ) = -z1.re := fun h => by
      rw [ha1]; exact natAbs_of_nonpos' (le_of_lt h)
    have hr2a : 0 < z2.re → (a2 : ℤ) = z2.re := fun h => by
      rw [ha2]; exact Int.natAbs_of_nonneg (le_of_lt h)
    have hr2b : z2.re < 0 → (a2 : ℤ) = -z2.re := fun h => by
      rw [ha2]; exact natAbs_of_nonpos' (le_of_lt h)
    have hr1a' : 0 < z1.re → z1.re = (a1 : ℤ) := fun h => (hr1a h).symm
    have hr1b' : z1.re < 0 → z1.re = -(a1 : ℤ) := fun h => by rw [hr1b h]; ring
    have hr2a' : 0 < z2.re → z2.re = (a2 : ℤ) := fun h => (hr2a h).symm
    have hr2b' : z2.re < 0 → z2.re = -(a2 : ℤ) := fun h => by rw [hr2b h]; ring
    have hprod : (a1 : ℤ) * (a2 : ℤ) = -(z1.re * z2.re) := by
      rcases hsigns with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hr1a h1, hr2b h2]; ring
      · rw [hr1b h1, hr2a h2]; ring
    -- the product `Re(z̄₁z₂) = r₁r₂ + s₁s₂` is `-(g²w₁w₂ - s₁s₂)`
    have hA : z1.re * z2.re + z1.im * z2.im = -((g : ℤ) ^ 2 * (w1 : ℤ) * (w2 : ℤ) - z1.im * z2.im) := by
      have h := hprod
      rw [ha1c, ha2c] at h
      have h2 : (g : ℤ) * (w1 : ℤ) * ((g : ℤ) * (w2 : ℤ)) = (g : ℤ) ^ 2 * (w1 : ℤ) * (w2 : ℤ) := by ring
      rw [h2] at h
      linarith
    -- `|z₁|² = g²w₁² + s₁²`
    have hN1 : ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) = (g : ℤ) ^ 2 * (w1 : ℤ) ^ 2 + z1.im ^ 2 := by
      have hz1sq : z1.re ^ 2 = ((g : ℤ) * (w1 : ℤ)) ^ 2 := by
        rcases hsigns with ⟨h1, _⟩ | ⟨h1, _⟩
        · rw [hr1a' h1, ha1c]
        · rw [hr1b' h1, show (-(a1 : ℤ)) ^ 2 = ((a1 : ℤ)) ^ 2 by ring, ha1c]
      rw [gnorm_int_coord, hz1sq]; ring
    -- the determinant `Δ(z₁,z₂) = ±g·(w₁s₂ + w₂s₁)` and `|Δ| = g·D₂`
    have hDz1 : Work.FIPlan.absDelta z1 z2 = (z1.re * z2.im - z2.re * z1.im).natAbs := by
      rw [Work.FIPlan.absDelta, Work.FIPlan.Delta, im_mul, Zsqrtd.re_star, Zsqrtd.im_star]
      congr 1; ring
    have hDabs : Work.FIPlan.absDelta z1 z2 = ((a1 : ℤ) * z2.im + (a2 : ℤ) * z1.im).natAbs := by
      rw [hDz1]
      rcases hsigns with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hr1a' h1, hr2b' h2]; congr 1; ring
      · rw [hr1b' h1, hr2a' h2]
        rw [show -(a1 : ℤ) * z2.im - (a2 : ℤ) * z1.im
            = -((a1 : ℤ) * z2.im + (a2 : ℤ) * z1.im) by ring, Int.natAbs_neg]
    set Δ2 : ℤ := (w1 : ℤ) * z2.im + (w2 : ℤ) * z1.im with hΔ2
    set D2 : ℕ := Δ2.natAbs with hD2
    have hDsplit : Work.FIPlan.absDelta z1 z2 = g * D2 := by
      rw [hDabs, hD2, hΔ2]
      have h' : (a1 : ℤ) * z2.im + (a2 : ℤ) * z1.im
          = (g : ℤ) * ((w1 : ℤ) * z2.im + (w2 : ℤ) * z1.im) := by
        rw [ha1c, ha2c]; ring
      rw [h', Int.natAbs_mul, Int.natAbs_natCast]
    have hD2pos : 0 < D2 := by
      rcases Nat.eq_zero_or_pos D2 with h | h
      · rw [hDsplit, h, mul_zero] at hD; omega
      · exact h
    have hD2ne : Δ2 ≠ 0 := by
      intro hc; rw [hD2, hc] at hD2pos; simp at hD2pos
    have hΔ2ne : (w1 : ℤ) * z2.im + (w2 : ℤ) * z1.im ≠ 0 := fun h => hD2ne (by rw [hΔ2]; exact h)
    -- the congruence `w₁ + w₂ ≡ 0 (mod 4)` descends from `r₁ ≡ r₂ (mod 4)`
    have h4a : (a1 : ℤ) + (a2 : ℤ) ≡ 0 [ZMOD 4] := by
      rcases hsigns with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hr : z1.re ≡ z2.re [ZMOD 4] := h4r
        rw [hr1a' h1, hr2b' h2] at hr
        simpa using hr.add_right (a2 : ℤ)
      · have hr : z1.re ≡ z2.re [ZMOD 4] := h4r
        rw [hr1b' h1, hr2a' h2] at hr
        simpa using (hr.add_left (a1 : ℤ)).symm
    have h4w : (w1 : ℤ) + (w2 : ℤ) ≡ 0 [ZMOD 4] := by
      have hab : (a1 : ℤ) + (a2 : ℤ) = (g : ℤ) * ((w1 : ℤ) + (w2 : ℤ)) := by
        rw [ha1c, ha2c]; ring
      rw [hab] at h4a
      have hgg : IsCoprime (4 : ℤ) (g : ℤ) := by
        rw [Int.isCoprime_iff_gcd_eq_one]
        have h4cop : Nat.Coprime 4 g := by
          have := Nat.Coprime.pow_left (n := 2) (m := 2) (k := g)
            (Nat.coprime_two_left.mpr hoddg)
          simpa using this
        have hgcd : Int.gcd (4 : ℤ) (g : ℤ) = Nat.gcd 4 g := by
          rw [Int.gcd_eq_natAbs]; norm_num
        rw [hgcd, Nat.coprime_iff_gcd_eq_one.mp h4cop]
      have hdvd : (4 : ℤ) ∣ (g : ℤ) * (0 - ((w1 : ℤ) + (w2 : ℤ))) := by
        have h1 : (4 : ℤ) ∣ (g : ℤ) * ((w1 : ℤ) + (w2 : ℤ)) := by
          have h := Int.modEq_iff_dvd.mp h4a
          rw [zero_sub] at h
          exact dvd_neg.mp h
        have h2 : (4 : ℤ) ∣ -((g : ℤ) * ((w1 : ℤ) + (w2 : ℤ))) := dvd_neg.mpr h1
        rwa [show -((g : ℤ) * ((w1 : ℤ) + (w2 : ℤ)))
              = (g : ℤ) * (0 - ((w1 : ℤ) + (w2 : ℤ))) by ring] at h2
      exact Int.modEq_iff_dvd.mpr (hgg.dvd_of_dvd_mul_left hdvd)
    -- coprimality of `|z₁|²` and `|w₁s₂ + w₂s₁|`
    have hcc' : Nat.Coprime (Work.FIPlan.gnorm z1) (Work.FIPlan.absDelta z1 z2) := by
      have h := Int.isCoprime_iff_gcd_eq_one.mp hcc
      rw [Int.gcd_eq_natAbs] at h
      rw [Nat.coprime_iff_gcd_eq_one]
      simpa using h
    have hNabs : (((g : ℤ) ^ 2 * (w1 : ℤ) ^ 2 + (-z1.im) ^ 2).natAbs) = Work.FIPlan.gnorm z1 := by
      rw [neg_sq, ← hN1, Int.natAbs_natCast]
    have hMod2 : (((w1 : ℤ) * z2.im - (w2 : ℤ) * (-z1.im)).natAbs) = D2 := by
      rw [hD2, hΔ2]; congr 1; ring
    have hB' : ((((g : ℤ) ^ 2 * (w1 : ℤ) ^ 2 + (-z1.im) ^ 2).natAbs)).Coprime
        (((w1 : ℤ) * z2.im - (w2 : ℤ) * (-z1.im)).natAbs) := by
      have h3 : D2 ∣ Work.FIPlan.absDelta z1 z2 := ⟨g, by rw [hDsplit, mul_comm]⟩
      rw [hNabs, hMod2]
      exact hcc'.coprime_dvd_right h3
    have hD' : (w1 : ℤ) * z2.im - (w2 : ℤ) * (-z1.im) ≠ 0 := by
      rw [show (w1 : ℤ) * z2.im - (w2 : ℤ) * (-z1.im) = Δ2 by rw [hΔ2]; ring]
      exact hD2ne
    -- **the reflSign identification**: in the opposite-sign case
    -- `reflSign z₁ z₂ = sign(w₁s₂ + w₂s₁)`
    have hDform : Work.FIPlan.Delta z1 z2 = z1.re * z2.im - z1.im * z2.re := by
      rw [Work.FIPlan.Delta, im_mul, Zsqrtd.re_star, Zsqrtd.im_star]; ring
    have hrefl : Work.FIArea7.reflSign z1 z2
        = (if 0 < (w1 : ℤ) * z2.im + (w2 : ℤ) * z1.im then (1 : ℤ) else -1) := by
      rw [Work.FIArea7.reflSign, if_neg (by linarith : ¬ (0 < z1.re * z2.re)), hDform]
      rcases hsigns with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hrel : z1.re * z2.im - z1.im * z2.re = (g : ℤ) * Δ2 := by
          rw [hΔ2, hr1a' h1, hr2b' h2, ha1c, ha2c]; ring
        rw [hrel]
        have hiff : ((0 < z1.re ∧ 0 < (g : ℤ) * Δ2) ∨ (z1.re < 0 ∧ (g : ℤ) * Δ2 < 0)) ↔ 0 < Δ2 := by
          constructor
          · rintro (⟨_, hh⟩ | ⟨hh, _⟩)
            · rwa [mul_pos_iff_of_pos_left hgposZ] at hh
            · exact absurd hh (by linarith)
          · intro hh
            exact Or.inl ⟨h1, (mul_pos_iff_of_pos_left hgposZ).mpr hh⟩
        by_cases hΔ : 0 < Δ2
        · rw [if_pos hΔ, if_pos (hiff.mpr hΔ)]
        · rw [if_neg hΔ, if_neg (fun h => hΔ (hiff.mp h))]
      · have hrel : z1.re * z2.im - z1.im * z2.re = -((g : ℤ) * Δ2) := by
          rw [hΔ2, hr1b' h1, hr2a' h2, ha1c, ha2c]; ring
        rw [hrel]
        have hiff : ((0 < z1.re ∧ 0 < -((g : ℤ) * Δ2)) ∨ (z1.re < 0 ∧ -((g : ℤ) * Δ2) < 0)) ↔ 0 < Δ2 := by
          constructor
          · rintro (⟨hh, _⟩ | ⟨_, hh⟩)
            · exact absurd hh (by linarith)
            · rw [neg_lt_zero, mul_pos_iff_of_pos_left hgposZ] at hh; exact hh
          · intro hh
            exact Or.inr ⟨h1, by rw [neg_lt_zero, mul_pos_iff_of_pos_left hgposZ]; exact hh⟩
        by_cases hΔ : 0 < Δ2
        · rw [if_pos hΔ, if_pos (hiff.mpr hΔ)]
        · rw [if_neg hΔ, if_neg (fun h => hΔ (hiff.mp h))]
    -- the exponent `ν₂(|Δ|) = ν₂(D₂)` (`g` is odd)
    have hfac : (Work.FIPlan.absDelta z1 z2).factorization 2 = D2.factorization 2 := by
      rw [hDsplit]
      have h2g : ¬ (2 : ℕ) ∣ g := by
        rw [← even_iff_two_dvd]; exact (Nat.not_even_iff_odd.mpr hoddg)
      rw [Nat.factorization_mul hgne hD2pos.ne', Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd h2g, zero_add]
    -- **(A)** `Work.FIArea7.reflBook` with the substitution `s₁ ↦ -s₁`:
    have hmain : jacobiSym (-(z1.re * z2.re + z1.im * z2.im)) (Work.FIPlan.absDelta z1 z2)
          * jacobiSym ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) (Work.FIPlan.absDelta z1 z2)
        = jacobiSym (-(z1.im * z2.im)) g * jacobiSym (((w1 * w2 : ℕ) : ℤ)) D2 := by
      have hrb := reflBook (g := g) (u1 := w1) (u2 := w2) (s1 := -z1.im) (s2 := z2.im)
        hgpos hoddw1 hoddw2 hw12 (by simpa using hgs1) (by simpa using hws1) hB' hD'
      rw [show (g : ℤ) ^ 2 * (w1 : ℤ) * (w2 : ℤ) + (-z1.im) * z2.im
              = -(z1.re * z2.re + z1.im * z2.im) from by rw [hA]; ring,
          show g * (((w1 : ℤ) * z2.im - (w2 : ℤ) * (-z1.im)).natAbs)
              = Work.FIPlan.absDelta z1 z2 from by rw [hMod2, ← hDsplit],
          show ((((g : ℤ) ^ 2 * (w1 : ℤ) ^ 2 + (-z1.im) ^ 2).natAbs : ℕ) : ℤ)
              = ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) from by rw [hNabs],
          show (-z1.im) * z2.im = -(z1.im * z2.im) from by ring,
          hMod2] at hrb
      exact hrb
    -- **(B)** the `J(-1, |Δ|)` factor
    have hminus : jacobiSym (z1.re * z2.re + z1.im * z2.im) (Work.FIPlan.absDelta z1 z2)
        = jacobiSym (-1) (Work.FIPlan.absDelta z1 z2)
          * jacobiSym (-(z1.re * z2.re + z1.im * z2.im)) (Work.FIPlan.absDelta z1 z2) := by
      have h := jacobiSym.mul_left (-1 : ℤ) (-(z1.re * z2.re + z1.im * z2.im))
        (Work.FIPlan.absDelta z1 z2)
      rw [show (-1 : ℤ) * (-(z1.re * z2.re + z1.im * z2.im))
            = z1.re * z2.re + z1.im * z2.im by ring] at h
      exact h
    have hJ1D : jacobiSym (-1) (Work.FIPlan.absDelta z1 z2) = jacobiSym (-1) g * jacobiSym (-1) D2 := by
      rw [hDsplit, jacobiSym.mul_right' (-1) hgne hD2pos.ne']
    have hJs : jacobiSym (-(z1.im * z2.im)) g
        = jacobiSym (-1) g * (jacobiSym z1.im g * jacobiSym z2.im g) := by
      rw [show -(z1.im * z2.im) = (-1) * z1.im * z2.im by ring, jacobiSym.mul_left,
        jacobiSym.mul_left]
      ring
    -- **(C)** `kronCore_neg`
    have hxodd : Odd (((w1 * w2 : ℕ) : ℤ)) := by
      obtain ⟨k, hk⟩ := hoddw1.mul hoddw2
      exact ⟨(k : ℤ), by rw [hk]; push_cast; ring⟩
    have hT2 : Work.FIArea7.kronTwo (((w1 * w2 : ℕ) : ℤ)) ^ (D2.factorization 2)
        * Work.FIArea7.kronTwo (((w1 * w2 : ℕ) : ℤ)) ^ (D2.factorization 2) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, Work.FIArea7.kronTwo_sq_of_odd hxodd, one_pow]
    have hkc : jacobiSym (-(((w1 * w2 : ℕ) : ℤ))) D2
        = (if 0 < (w1 : ℤ) * z2.im + (w2 : ℤ) * z1.im then (1 : ℤ) else -1)
          * (jacobiSym z1.im w1 * jacobiSym z2.im w2)
          * Work.FIArea7.kronTwo (((w1 * w2 : ℕ) : ℤ)) ^ (D2.factorization 2) := by
      have hKC := kronCore_neg hoddw1 hoddw2 hw12 hws1 hws2 h4w hΔ2ne
      calc jacobiSym (-(((w1 * w2 : ℕ) : ℤ))) D2
          = jacobiSym (-(((w1 * w2 : ℕ) : ℤ))) D2
            * (Work.FIArea7.kronTwo (((w1 * w2 : ℕ) : ℤ)) ^ (D2.factorization 2)
               * Work.FIArea7.kronTwo (((w1 * w2 : ℕ) : ℤ)) ^ (D2.factorization 2)) := by
            rw [hT2, mul_one]
        _ = (jacobiSym (-(((w1 * w2 : ℕ) : ℤ))) D2
              * Work.FIArea7.kronTwo (((w1 * w2 : ℕ) : ℤ)) ^ (D2.factorization 2))
            * Work.FIArea7.kronTwo (((w1 * w2 : ℕ) : ℤ)) ^ (D2.factorization 2) := by ring
        _ = ((if 0 < (w1 : ℤ) * z2.im + (w2 : ℤ) * z1.im then (1 : ℤ) else -1)
              * (jacobiSym z1.im w1 * jacobiSym z2.im w2))
            * Work.FIArea7.kronTwo (((w1 * w2 : ℕ) : ℤ)) ^ (D2.factorization 2) := by rw [hKC]
        _ = (if 0 < (w1 : ℤ) * z2.im + (w2 : ℤ) * z1.im then (1 : ℤ) else -1)
            * (jacobiSym z1.im w1 * jacobiSym z2.im w2)
            * Work.FIArea7.kronTwo (((w1 * w2 : ℕ) : ℤ)) ^ (D2.factorization 2) := by ring
    have hJw : jacobiSym (((w1 * w2 : ℕ) : ℤ)) D2
        = jacobiSym (-1) D2
          * ((if 0 < (w1 : ℤ) * z2.im + (w2 : ℤ) * z1.im then (1 : ℤ) else -1)
              * (jacobiSym z1.im w1 * jacobiSym z2.im w2)
              * Work.FIArea7.kronTwo (((w1 * w2 : ℕ) : ℤ)) ^ (D2.factorization 2)) := by
      have h := jacobiSym.mul_left (-1 : ℤ) (-(((w1 * w2 : ℕ) : ℤ))) D2
      rw [show (-1 : ℤ) * (-(((w1 * w2 : ℕ) : ℤ))) = (((w1 * w2 : ℕ) : ℤ)) by ring] at h
      rw [h, hkc]
    -- **(D)** the two cofactor symbols split at `aᵢ = g·wᵢ`
    have hw1ne : w1 ≠ 0 := fun h => ha1ne (by rw [← hgw1, h, mul_zero])
    have hw2ne : w2 ≠ 0 := fun h => ha2ne (by rw [← hgw2, h, mul_zero])
    have hs1a : jacobiSym z1.im a1 = jacobiSym z1.im g * jacobiSym z1.im w1 := by
      rw [← hgw1]; exact jacobiSym.mul_right' z1.im hgne hw1ne
    have hs2a : jacobiSym z2.im a2 = jacobiSym z2.im g * jacobiSym z2.im w2 := by
      rw [← hgw2]; exact jacobiSym.mul_right' z2.im hgne hw2ne
    have hL : jacobiSym (z1.re * z2.re + z1.im * z2.im) (Work.FIPlan.absDelta z1 z2)
          * jacobiSym ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) (Work.FIPlan.absDelta z1 z2)
        = (if 0 < (w1 : ℤ) * z2.im + (w2 : ℤ) * z1.im then (1 : ℤ) else -1)
          * Work.FIArea7.kronTwo (((w1 * w2 : ℕ) : ℤ)) ^ (D2.factorization 2)
          * (jacobiSym z1.im a1 * jacobiSym z2.im a2) := by
      rw [hminus, mul_assoc, hmain, hJ1D, hJs, hJw, hs1a, hs2a]
      have hJ1g : jacobiSym (-1) g = 1 ∨ jacobiSym (-1) g = -1 :=
        jacobiSym.eq_one_or_neg_one (by rw [Int.gcd_eq_natAbs]; norm_num)
      have hJ1D2 : jacobiSym (-1) D2 = 1 ∨ jacobiSym (-1) D2 = -1 :=
        jacobiSym.eq_one_or_neg_one (by rw [Int.gcd_eq_natAbs]; norm_num)
      rcases hJ1g with h1 | h1 <;> rcases hJ1D2 with h2 | h2 <;> rw [h1, h2] <;> ring
    -- **(E)** the right-hand side of the goal
    have hkron : Work.FIArea7.kronTwo (z1.re * z2.re + z1.im * z2.im)
          * Work.FIArea7.kronTwo ((Work.FIPlan.gnorm z1 : ℕ) : ℤ)
        = Work.FIArea7.kronTwo (((w1 * w2 : ℕ) : ℤ)) := by
      have h1 : Work.FIArea7.kronTwo (z1.re * z2.re + z1.im * z2.im)
          = Work.FIArea7.kronTwo ((g : ℤ) ^ 2 * (w1 : ℤ) * (w2 : ℤ) - z1.im * z2.im) := by
        rw [hA, kronTwo_neg]
      have h2 : Work.FIArea7.kronTwo ((Work.FIPlan.gnorm z1 : ℕ) : ℤ)
          = Work.FIArea7.kronTwo ((g : ℤ) ^ 2 * (w1 : ℤ) ^ 2 + z1.im ^ 2) := by rw [hN1]
      have h3 := kronEight_neg hoddg hoddw1 hoddw2 hs1even hs2even h4w h4i
      rw [h1, h2, h3,
        show ((w1 : ℤ) * (w2 : ℤ)) = (((w1 * w2 : ℕ) : ℤ)) by push_cast; ring]
    have hR : (Work.FIArea7.kronTwo (z1.re * z2.re + z1.im * z2.im)
            * Work.FIArea7.kronTwo ((Work.FIPlan.gnorm z1 : ℕ) : ℤ))
          ^ ((Work.FIPlan.absDelta z1 z2).factorization 2)
          * Work.FIArea7.reflSign z1 z2
          * (jacobiSym z1.im a1 * jacobiSym z2.im a2)
        = (if 0 < (w1 : ℤ) * z2.im + (w2 : ℤ) * z1.im then (1 : ℤ) else -1)
          * Work.FIArea7.kronTwo (((w1 * w2 : ℕ) : ℤ)) ^ (D2.factorization 2)
          * (jacobiSym z1.im a1 * jacobiSym z2.im a2) := by
      rw [hkron, hrefl, hfac]
      ring
    rw [hL, hR]
  · exfalso
    rcases mul_eq_zero.mp hzero with h | h
    · exact hr1 h
    · exact hr2 h
  · -- **Case I**: `0 < r₁r₂`: the paper's case (`Work.FIArea7.jacobiSym_reflection_mod4`)
    have hrefl : Work.FIArea7.reflSign z1 z2 = 1 := by
      rw [Work.FIArea7.reflSign]; exact if_pos hpos
    rw [hrefl, mul_one]
    exact jacobiSym_reflection_mod4 hP1 hP2 hs1 hs2 hc hcc h4r h4i hpos hD


theorem reflection_pair_betaPrime_general (z1 z2 : GaussianInt) (β : GaussianInt → ℂ)
    (hP1 : Work.FIPlan.IsPrimary z1) (hP2 : Work.FIPlan.IsPrimary z2)
    (hs1 : Squarefree (Work.FIPlan.gnorm z1)) (hs2 : Squarefree (Work.FIPlan.gnorm z2))
    (hc : IsCoprime z1 z2)
    (hcc : IsCoprime ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) ((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ))
    (h4r : z1.re ≡ z2.re [ZMOD 4]) (h4i : z1.im ≡ z2.im [ZMOD 4])
    (hr1 : z1.re ≠ 0) (hr2 : z2.re ≠ 0) (hD : 0 < Work.FIPlan.absDelta z1 z2) :
    (jacobiSym (z1.re * z2.re + z1.im * z2.im) (Work.FIPlan.absDelta z1 z2) : ℂ)
        * β z1 * star (β z2)
      = (((Work.FIArea7.kronTwo (z1.re * z2.re + z1.im * z2.im)
             * Work.FIArea7.kronTwo ((Work.FIPlan.gnorm z1 : ℕ) : ℤ))
           ^ ((Work.FIPlan.absDelta z1 z2).factorization 2) : ℤ) : ℂ)
        * (Work.FIArea7.reflSign z1 z2 : ℂ)
        * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
        * (jacobiSym ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) (Work.FIPlan.absDelta z1 z2) : ℂ)
        * (Work.FIArea7.betaPrime β z1 * star (Work.FIArea7.betaPrime β z2)) := by
  have hcore := jacobiSym_reflection_mod4_general hP1 hP2 hs1 hs2 hc hcc h4r h4i hr1 hr2 hD
  have hgcd : (((Work.FIPlan.gnorm z1 : ℕ) : ℤ)).gcd (((Work.FIPlan.absDelta z1 z2 : ℕ) : ℤ))
      = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcc
  have hBsq : jacobiSym ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) (Work.FIPlan.absDelta z1 z2) ^ 2 = 1 :=
    jacobiSym.sq_one hgcd
  -- **(1)** solve the core identity for the single symbol `J(Re(z̄₁z₂) | |Δ|)`
  have hcore2 : jacobiSym (z1.re * z2.re + z1.im * z2.im) (Work.FIPlan.absDelta z1 z2)
      = (((Work.FIArea7.kronTwo (z1.re * z2.re + z1.im * z2.im)
             * Work.FIArea7.kronTwo ((Work.FIPlan.gnorm z1 : ℕ) : ℤ))
           ^ ((Work.FIPlan.absDelta z1 z2).factorization 2) : ℤ)
        * Work.FIArea7.reflSign z1 z2
        * (jacobiSym ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) (Work.FIPlan.absDelta z1 z2))
        * (jacobiSym z1.im z1.re.natAbs * jacobiSym z2.im z2.re.natAbs)) := by
    have hsq : jacobiSym ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) (Work.FIPlan.absDelta z1 z2)
        * jacobiSym ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) (Work.FIPlan.absDelta z1 z2) = 1 := by
      rw [← sq]; exact hBsq
    calc jacobiSym (z1.re * z2.re + z1.im * z2.im) (Work.FIPlan.absDelta z1 z2)
        = jacobiSym (z1.re * z2.re + z1.im * z2.im) (Work.FIPlan.absDelta z1 z2)
            * (jacobiSym ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) (Work.FIPlan.absDelta z1 z2)
              * jacobiSym ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) (Work.FIPlan.absDelta z1 z2)) := by
          rw [hsq, mul_one]
      _ = (jacobiSym (z1.re * z2.re + z1.im * z2.im) (Work.FIPlan.absDelta z1 z2)
            * jacobiSym ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) (Work.FIPlan.absDelta z1 z2))
          * jacobiSym ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) (Work.FIPlan.absDelta z1 z2) := by ring
      _ = (((Work.FIArea7.kronTwo (z1.re * z2.re + z1.im * z2.im)
              * Work.FIArea7.kronTwo ((Work.FIPlan.gnorm z1 : ℕ) : ℤ))
            ^ ((Work.FIPlan.absDelta z1 z2).factorization 2) : ℤ)
          * Work.FIArea7.reflSign z1 z2
          * (jacobiSym z1.im z1.re.natAbs * jacobiSym z2.im z2.re.natAbs))
          * jacobiSym ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) (Work.FIPlan.absDelta z1 z2) := by
          rw [hcore]
      _ = (((Work.FIArea7.kronTwo (z1.re * z2.re + z1.im * z2.im)
              * Work.FIArea7.kronTwo ((Work.FIPlan.gnorm z1 : ℕ) : ℤ))
            ^ ((Work.FIPlan.absDelta z1 z2).factorization 2) : ℤ)
          * Work.FIArea7.reflSign z1 z2
          * (jacobiSym ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) (Work.FIPlan.absDelta z1 z2))
          * (jacobiSym z1.im z1.re.natAbs * jacobiSym z2.im z2.re.natAbs)) := by ring
  -- **(2)** the Jacobi–Kubota bookkeeping `β'_z = [z]β_z` (`ReflectAlg.jksym_mul_star`)
  have hbp : Work.FIArea7.betaPrime β z1 * star (Work.FIArea7.betaPrime β z2)
      = Complex.I ^ (((z1.re - 1) / 2 : ℤ) - ((z2.re - 1) / 2 : ℤ))
        * (Work.FIArea7.JKCoeff z1 * Work.FIArea7.JKCoeff z2) * (β z1 * star (β z2)) := by
    rw [Work.FIArea7.betaPrime, Work.FIArea7.betaPrime, star_mul]
    rw [show Work.FIArea7.JKSym z1 * β z1 * (star (β z2) * star (Work.FIArea7.JKSym z2))
        = (Work.FIArea7.JKSym z1 * star (Work.FIArea7.JKSym z2)) * (β z1 * star (β z2))
        by ring]
    rw [Work.FIArea7.jksym_mul_star]
  -- **(3)** the two powers of `i` are inverse to each other
  have hIprod : Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
      * Complex.I ^ (((z1.re - 1) / 2 : ℤ) - ((z2.re - 1) / 2 : ℤ)) = 1 := by
    rw [← zpow_add₀ Complex.I_ne_zero]
    have hz : (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
        + (((z1.re - 1) / 2 : ℤ) - ((z2.re - 1) / 2 : ℤ)) = 0 := by ring
    rw [hz, zpow_zero]
  have hexp : (Work.FIArea7.JKCoeff z1 * Work.FIArea7.JKCoeff z2) * (β z1 * star (β z2))
      = Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
        * (Work.FIArea7.betaPrime β z1 * star (Work.FIArea7.betaPrime β z2)) := by
    calc (Work.FIArea7.JKCoeff z1 * Work.FIArea7.JKCoeff z2) * (β z1 * star (β z2))
        = (Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
            * Complex.I ^ (((z1.re - 1) / 2 : ℤ) - ((z2.re - 1) / 2 : ℤ)))
          * ((Work.FIArea7.JKCoeff z1 * Work.FIArea7.JKCoeff z2) * (β z1 * star (β z2))) := by
          rw [hIprod, one_mul]
      _ = Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
          * (Complex.I ^ (((z1.re - 1) / 2 : ℤ) - ((z2.re - 1) / 2 : ℤ))
            * ((Work.FIArea7.JKCoeff z1 * Work.FIArea7.JKCoeff z2) * (β z1 * star (β z2)))) := by
          ring_nf
      _ = Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
          * (Work.FIArea7.betaPrime β z1 * star (Work.FIArea7.betaPrime β z2)) := by
          rw [hbp]
          ring_nf
  have hJK2 : ((jacobiSym z1.im z1.re.natAbs : ℤ) : ℂ) * ((jacobiSym z2.im z2.re.natAbs : ℤ) : ℂ)
        * (β z1 * star (β z2))
      = Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ))
        * (Work.FIArea7.betaPrime β z1 * star (Work.FIArea7.betaPrime β z2)) :=
    hexp
  calc (jacobiSym (z1.re * z2.re + z1.im * z2.im) (Work.FIPlan.absDelta z1 z2) : ℂ) * β z1 * star (β z2)
      = ((Work.FIArea7.kronTwo (z1.re * z2.re + z1.im * z2.im) : ℂ) * (Work.FIArea7.kronTwo ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) : ℂ)) ^ ((Work.FIPlan.absDelta z1 z2).factorization 2) * ((Work.FIArea7.reflSign z1 z2 : ℤ) : ℂ) * ((jacobiSym ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) (Work.FIPlan.absDelta z1 z2) : ℤ) : ℂ) * (((jacobiSym z1.im z1.re.natAbs : ℤ) : ℂ) * ((jacobiSym z2.im z2.re.natAbs : ℤ) : ℂ) * (β z1 * star (β z2))) := by
        rw [hcore2]
        push_cast
        ring
      _ = ((Work.FIArea7.kronTwo (z1.re * z2.re + z1.im * z2.im) : ℂ) * (Work.FIArea7.kronTwo ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) : ℂ)) ^ ((Work.FIPlan.absDelta z1 z2).factorization 2) * ((Work.FIArea7.reflSign z1 z2 : ℤ) : ℂ) * ((jacobiSym ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) (Work.FIPlan.absDelta z1 z2) : ℤ) : ℂ) * (Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ)) * (Work.FIArea7.betaPrime β z1 * star (Work.FIArea7.betaPrime β z2))) := by
        rw [hJK2]
      _ = ((((Work.FIArea7.kronTwo (z1.re * z2.re + z1.im * z2.im) * Work.FIArea7.kronTwo ((Work.FIPlan.gnorm z1 : ℕ) : ℤ)) ^ ((Work.FIPlan.absDelta z1 z2).factorization 2) : ℤ) : ℂ) * (Work.FIArea7.reflSign z1 z2 : ℂ) * Complex.I ^ (((z2.re - 1) / 2 : ℤ) - ((z1.re - 1) / 2 : ℤ)) * (jacobiSym ((Work.FIPlan.gnorm z1 : ℕ) : ℤ) (Work.FIPlan.absDelta z1 z2) : ℂ) * (Work.FIArea7.betaPrime β z1 * star (Work.FIArea7.betaPrime β z2))) := by
        push_cast
        ring

end Work.FIArea7
