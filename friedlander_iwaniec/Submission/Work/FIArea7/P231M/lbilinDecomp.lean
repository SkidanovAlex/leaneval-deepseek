import Mathlib
import Submission.Work.FIArea7.P231Defs

namespace Work.FIArea7.P231

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## A general gcd-reindexing identity

For any `G : ℕ → ℕ → ℂ`,
`∑_{m ≤ M} ∑_{n ≤ N} G m n = ∑_{g ≤ min M N} ∑_{a ≤ M/g} ∑_{b ≤ N/g, (a,b)=1} G (ga) (gb)`,
obtained by grouping the pairs `(m,n)` according to `g = gcd m n`. -/

private def ASet (M N : ℕ) : Finset (ℕ × ℕ) := (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 N)

private def BSet (M N : ℕ) : Finset (Σ _ : ℕ, ℕ × ℕ) :=
  (Finset.Icc 1 (min M N)).sigma
    (fun g => (Finset.Icc 1 (M / g)) ×ˢ (Finset.Icc 1 (N / g)))

private def gcdTau (p : ℕ × ℕ) : (Σ _ : ℕ, ℕ × ℕ) :=
  ⟨Nat.gcd p.1 p.2, (p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2)⟩

private def bsummand (G : ℕ → ℕ → ℂ) : (Σ _ : ℕ, ℕ × ℕ) → ℂ :=
  fun q => if Nat.Coprime q.2.1 q.2.2 then G (q.1 * q.2.1) (q.1 * q.2.2) else 0

private lemma bsummand_gcdTau {G : ℕ → ℕ → ℂ} {p : ℕ × ℕ}
    (hgpos : 0 < Nat.gcd p.1 p.2) : bsummand G (gcdTau p) = G p.1 p.2 := by
  have hc : Nat.Coprime (p.1 / Nat.gcd p.1 p.2) (p.2 / Nat.gcd p.1 p.2) :=
    Nat.coprime_div_gcd_div_gcd hgpos
  have hm1 : Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) = p.1 :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left p.1 p.2)
  have hm2 : Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2) = p.2 :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right p.1 p.2)
  have hbs : bsummand G (gcdTau p)
      = (if Nat.Coprime (p.1 / Nat.gcd p.1 p.2) (p.2 / Nat.gcd p.1 p.2)
          then G (Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2))
                 (Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2)) else 0) := rfl
  simp only [hbs, if_pos hc, hm1, hm2]

private lemma sum_gcd_decomp {M N : ℕ} (G : ℕ → ℕ → ℂ) :
    (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N, G m n)
      = ∑ g ∈ Finset.Icc 1 (min M N),
          ∑ a ∈ Finset.Icc 1 (M / g), ∑ b ∈ Finset.Icc 1 (N / g),
            (if Nat.Coprime a b then G (g * a) (g * b) else 0) := by
  classical
  have hval : ∑ p ∈ ASet M N, G p.1 p.2 = ∑ p ∈ ASet M N, bsummand G (gcdTau p) := by
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [ASet, Finset.mem_product] at hp
    obtain ⟨hp1, _⟩ := hp
    rw [Finset.mem_Icc] at hp1
    obtain ⟨hp1a, _⟩ := hp1
    exact (bsummand_gcdTau (Nat.gcd_pos_of_pos_left p.2 (by omega))).symm
  have hφinj : Set.InjOn gcdTau ↑(ASet M N) := by
    intro p _ p' _ heq
    have h1 : Nat.gcd p.1 p.2 = Nat.gcd p'.1 p'.2 := by
      have := congrArg Sigma.fst heq
      simpa only [gcdTau] using this
    have h2 : (p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2)
        = (p'.1 / Nat.gcd p'.1 p'.2, p'.2 / Nat.gcd p'.1 p'.2) := by
      have := congrArg Sigma.snd heq
      simpa only [gcdTau] using this
    have h2a : p.1 / Nat.gcd p.1 p.2 = p'.1 / Nat.gcd p'.1 p'.2 := congrArg Prod.fst h2
    have h2b : p.2 / Nat.gcd p.1 p.2 = p'.2 / Nat.gcd p'.1 p'.2 := congrArg Prod.snd h2
    have e1 : p.1 = p'.1 := by
      calc p.1 = Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) :=
            (Nat.mul_div_cancel' (Nat.gcd_dvd_left p.1 p.2)).symm
        _ = Nat.gcd p'.1 p'.2 * (p'.1 / Nat.gcd p'.1 p'.2) := by rw [h2a, h1]
        _ = p'.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left p'.1 p'.2)
    have e2 : p.2 = p'.2 := by
      calc p.2 = Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2) :=
            (Nat.mul_div_cancel' (Nat.gcd_dvd_right p.1 p.2)).symm
        _ = Nat.gcd p'.1 p'.2 * (p'.2 / Nat.gcd p'.1 p'.2) := by rw [h2b, h1]
        _ = p'.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right p'.1 p'.2)
    exact Prod.ext e1 e2
  have hmaps : (ASet M N).image gcdTau ⊆ BSet M N := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    rw [ASet, Finset.mem_product] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [Finset.mem_Icc] at hp1 hp2
    obtain ⟨hp1a, hp1b⟩ := hp1
    obtain ⟨hp2a, hp2b⟩ := hp2
    have hp1pos : 0 < p.1 := by omega
    have hp2pos : 0 < p.2 := by omega
    have hgpos : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left p.2 hp1pos
    have hgle1 : Nat.gcd p.1 p.2 ≤ p.1 := Nat.gcd_le_left p.2 hp1pos
    have hgle2 : Nat.gcd p.1 p.2 ≤ p.2 := Nat.gcd_le_right p.1 hp2pos
    rw [BSet, Finset.mem_sigma]
    constructor
    · rw [Finset.mem_Icc]
      exact ⟨hgpos, le_min (le_trans hgle1 hp1b) (le_trans hgle2 hp2b)⟩
    · rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      exact ⟨⟨Nat.div_pos hgle1 hgpos, Nat.div_le_div_right hp1b⟩,
             ⟨Nat.div_pos hgle2 hgpos, Nat.div_le_div_right hp2b⟩⟩
  have hpos : ∀ q ∈ BSet M N, bsummand G q ≠ 0 → q ∈ (ASet M N).image gcdTau := by
    rintro ⟨g', p'⟩ hqB hne
    obtain ⟨a', b'⟩ := p'
    rw [BSet, Finset.mem_sigma] at hqB
    obtain ⟨hgB, hpmem⟩ := hqB
    rw [Finset.mem_Icc] at hgB
    obtain ⟨hg1raw, _⟩ := hgB
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hpmem
    obtain ⟨⟨ha1raw, ha2raw⟩, ⟨hb1raw, hb2raw⟩⟩ := hpmem
    have hg1 : 1 ≤ g' := hg1raw
    have ha1 : 1 ≤ a' := ha1raw
    have hb1 : 1 ≤ b' := hb1raw
    have ha2 : a' ≤ M / g' := ha2raw
    have hb2 : b' ≤ N / g' := hb2raw
    have hgpos : 0 < g' := hg1
    have hcop : Nat.Coprime a' b' := by
      by_contra hc
      exact hne (by simp only [bsummand]; exact if_neg hc)
    have hgcd : Nat.gcd (g' * a') (g' * b') = g' := by
      rw [Nat.gcd_mul_left, hcop.gcd_eq_one, Nat.mul_one]
    refine Finset.mem_image.mpr ⟨(g' * a', g' * b'), ?_, ?_⟩
    · rw [ASet, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
      refine ⟨⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩,
              ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩⟩
      · have h := (Nat.le_div_iff_mul_le hgpos).mp ha2
        rwa [Nat.mul_comm] at h
      · have h := (Nat.le_div_iff_mul_le hgpos).mp hb2
        rwa [Nat.mul_comm] at h
    · simp only [gcdTau, hgcd, Nat.mul_div_right a' hgpos, Nat.mul_div_right b' hgpos]
  have hzero : ∀ q ∈ BSet M N, q ∉ (ASet M N).image gcdTau → bsummand G q = 0 := by
    intro q hqB hqnot
    by_contra hne
    exact hqnot (hpos q hqB hne)
  have hR : (∑ q ∈ BSet M N, bsummand G q)
      = ∑ g ∈ Finset.Icc 1 (min M N),
          ∑ a ∈ Finset.Icc 1 (M / g), ∑ b ∈ Finset.Icc 1 (N / g),
            (if Nat.Coprime a b then G (g * a) (g * b) else 0) := by
    rw [BSet, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_product]
    rfl
  calc (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 N, G m n)
      = ∑ p ∈ ASet M N, G p.1 p.2 :=
          (Finset.sum_product (Finset.Icc 1 M) (Finset.Icc 1 N)
            (fun p : ℕ × ℕ => G p.1 p.2)).symm
    _ = ∑ p ∈ ASet M N, bsummand G (gcdTau p) := hval
    _ = ∑ q ∈ (ASet M N).image gcdTau, bsummand G q := (Finset.sum_image hφinj).symm
    _ = ∑ q ∈ BSet M N, bsummand G q := Finset.sum_subset hmaps hzero
    _ = _ := hR

/-- **(23.5)–(23.7)**: the unrestricted bilinear form `L(M,N)` decomposes over the common divisor
`g = gcd(m,n)` into restricted forms `L*(M/g, N/g)` with dilated coefficients. -/
lemma LBilin_gcd_decomp (M N c : ℕ) (psi : GaussianInt → ℂ) (α β : ℕ → ℂ) :
    LBilin M N c psi α β
      = ∑ g ∈ Finset.Icc 1 (min M N),
          ∑ a ∈ Finset.Icc 1 (M / g), ∑ b ∈ Finset.Icc 1 (N / g),
            (if Nat.Coprime a b then
              α (g * a) * β (g * b) * quadEigen psi (c * g ^ 2 * a * b) else 0) := by
  simp only [LBilin]
  rw [sum_gcd_decomp (G := fun m n => α m * β n * quadEigen psi (c * m * n))]
  refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  by_cases hc : Nat.Coprime a b
  · rw [if_pos hc, if_pos hc]
    rw [show c * (g * a) * (g * b) = c * g ^ 2 * a * b from by ring]
  · rw [if_neg hc, if_neg hc]

theorem lbilinDecomp (M N c : ℕ) (psi : GaussianInt → ℂ) (α β : ℕ → ℂ) :
    Work.FIArea7.LBilin M N c psi α β
      = ∑ g ∈ Finset.Icc 1 (min M N),
          Work.FIArea7.LBilinStar (M / g) (N / g) (c * g ^ 2) psi
            (fun a => α (g * a)) (fun b => β (g * b)) := by
  rw [LBilin_gcd_decomp]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [LBilinStar]

end

end Work.FIArea7.P231
