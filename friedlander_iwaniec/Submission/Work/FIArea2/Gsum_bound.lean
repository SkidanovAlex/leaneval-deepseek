import Mathlib
import Submission.Work.FIArea2.G8Defs
import Submission.Work.FIArea2.ramanujan_setup
import Submission.Work.FIArea2.ramanujan_primepow
import Submission.Work.FIArea2.TsumDefs
import Submission.Work.FIArea2.Tsum_mul
import Submission.Work.FIArea2.Tsum_prime_pow_odd
import Submission.Work.FIArea2.Tsum_prime_pow_two
import Submission.Work.FIArea2.Tsum_prime_pow_of_cases
import Submission.Work.FIArea2.Gsum_assembly
import Submission.Work.FIArea2.Gsum_eq_Tsum
import Submission.Work.FIArea2.gcdDelta_eq_gcd
import Submission.Work.FIArea2.exists_residue_data

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

open scoped BigOperators

/-- **Lemma 8.1 of FI** ((8.5)), *with the §6 standing hypotheses that make it true*.  For
`z₁, z₂` with `(z₁,z₂) = 1`, both primitive (`(zⱼ,z̄ⱼ) = 1`) and `Δ = Im(z̄₁z₂) ≠ 0`, and all
`h₁,h₂ : ℤ`,

  `‖G(h₁,h₂)‖ ≤ 4·τ(Δ)³·(Λ,Δ)/|Δ|`,   `Λ = z₁h₁² − z₂h₂²`,

where `G(h₁,h₂)` is (6.10) (`Work.FIArea2.Gsum` in `Submission.Work.FIArea2.G8Defs`), the sum over
the solution pairs of (6.4)/(6.5) normalised by `|Δ|⁻¹`, and `(Λ,Δ)` (`Work.FIArea2.gcdDelta`) is
the largest `d ∣ |Δ|` dividing both the real and the imaginary part of `Λ` — the quantity used in
§9 ("`Λ(r₁,r₂) ≡ Λ(s₁,s₂) ≡ 0 (mod d)`").  The hypotheses are exactly those of the application:
§5–§6 deduce `(z₁,z̄₁) = (z₂,z̄₂) = 1` from the support of `β` (squarefree `|z|²`, see
`Work.FIArea2.isCoprime_star_of_squarefree_odd_gnorm`) and `(z₁,z₂) = 1` from (5.26); §9 uses the
bound only on such pairs.  At `h₁ = h₂ = 0` it says `G₀ ≤ 4τ(Δ)³`, i.e. (8.6), since `Λ = 0` gives
`(Λ,Δ) = |Δ|`.  (Without the coprimality/primitivity hypotheses the statement is **false**: for
`z₁ = 1`, `z₂ = p²i`, `h₁ = h₂ = p²` one has `G = p = 109 > 108 = 4·τ(Δ)³(Λ,Δ)/|Δ|`.)

Route (§8): (8.1) `Δ = Δ₁Δ₂²`; the restructuring (8.3) of the sum over the solution set into
`|Δ|⁻¹Σ_{b₁d₁=|Δ₁|, b₂d₂=Δ₂, (d₁,b₂)=1, d₂|(h₁,h₂)} d₂² Σ_ω R((h₁+ωh₂)d₂^{-1}; b₁b₂²)` with
`ω² ≡ z₂/z₁ (mod b₁b₂²)`; the Ramanujan-sum bound `|R(h;b)| ≤ (h,b)`
(`Work.FIArea2.ramanujan_sum_bound`) and `n(z;b) ≤ 4τ(b)` for the number of `ω` (this is where
coprimality and primitivity are used: `z₂/z₁` is a *unit* modulo `|Δ|`); then
`(h₁+ωh₂, b₁b₂²) ∣ z₁h₁² − z₂h₂²`, because `ω²z₁ ≡ z₂` gives `(ωh₂)²z₁ ≡ z₂h₂²`. -/
theorem Gsum_bound (z1 z2 : GaussianInt)
    (hcop : IsCoprime z1 z2) (hp1 : IsCoprime z1 (star z1)) (hp2 : IsCoprime z2 (star z2))
    (hD : Work.FIPlan.absDelta z1 z2 ≠ 0) (h1 h2 : ℤ) :
    ‖Work.FIArea2.Gsum z1 z2 h1 h2‖
      ≤ 4 * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
          * (Work.FIArea2.gcdDelta z1 z2 h1 h2 : ℝ) / (Work.FIPlan.absDelta z1 z2 : ℝ) := by
  haveI : NeZero (Work.FIPlan.absDelta z1 z2) := ⟨hD⟩
  -- the residue `a = z₂/z₁ (mod |Δ|)` and its coprimality
  obtain ⟨a, hni, _hre, ha, hacop⟩ := exists_residue_data z1 z2 hcop hp1 hp2 hD
  have haunit : IsUnit ((a : ℤ) : ZMod (Work.FIPlan.absDelta z1 z2)) := by
    rw [Int.cast_natCast]
    exact (ZMod.isUnit_iff_coprime a (Work.FIPlan.absDelta z1 z2)).mpr hacop
  -- the two inputs of the assembly
  have hloc : ∀ (p : ℕ), p.Prime → ∀ (ν : ℕ) [NeZero (p ^ ν)], 1 ≤ ν → ∀ (a h1 h2 : ℤ),
      IsUnit (a : ZMod (p ^ ν)) →
      ‖Tsum (p ^ ν) a h1 h2‖
        ≤ ((ν : ℝ) + 1) ^ 3 * (Nat.gcd (p ^ ν) ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ) :=
    fun p hp ν inst hν a h1 h2 ha =>
      @Tsum_prime_pow_of_cases
        (fun ν hν a h1 h2 ha => Tsum_prime_pow_two ν hν a h1 h2 ha)
        (fun p hp hodd ν hν inst a h1 h2 ha => @Tsum_prime_pow_odd p hp hodd ν hν inst a h1 h2 ha)
        p hp ν hν inst a h1 h2 ha
  have hmul : ∀ {m n : ℕ} [NeZero m] [NeZero n], Nat.Coprime m n → ∀ (c1 c2 : ℤ),
      (c1 : ZMod m) * (n : ZMod m) = 1 → (c2 : ZMod n) * (m : ZMod n) = 1 → ∀ (a h1 h2 : ℤ),
      Tsum (m * n) a h1 h2
        = Tsum m a (h1 * c1) (h2 * c1) * Tsum n a (h1 * c2) (h2 * c2) :=
    fun {m n} _ _ hmn c1 c2 hc1 hc2 a h1 h2 => Tsum_mul hmn c1 c2 hc1 hc2 a h1 h2
  have hT := gsumAsm_Tsum_bound hloc hmul (Work.FIPlan.absDelta z1 z2) (a : ℤ) h1 h2 haunit
  have hG := Gsum_eq_Tsum z1 z2 (a : ℤ) hni ha h1 h2
  have hgcd := gcdDelta_eq_gcd z1 z2 (a : ℤ) h1 h2 hD hni ha
  rw [hG, hgcd]
  have hnpos : (0 : ℝ) < (Work.FIPlan.absDelta z1 z2 : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hD
  calc ‖(((Work.FIPlan.absDelta z1 z2 : ℝ))⁻¹ : ℂ)
        * Tsum (Work.FIPlan.absDelta z1 z2) (a : ℤ) h1 h2‖
      = (Work.FIPlan.absDelta z1 z2 : ℝ)⁻¹
          * ‖Tsum (Work.FIPlan.absDelta z1 z2) (a : ℤ) h1 h2‖ := by
        rw [norm_mul]
        congr 1
        simp [hnpos.le]
    _ ≤ (Work.FIPlan.absDelta z1 z2 : ℝ)⁻¹
          * (4 * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
              * (Nat.gcd (Work.FIPlan.absDelta z1 z2)
                  ((h1 ^ 2 - (a : ℤ) * h2 ^ 2).natAbs) : ℝ)) :=
        mul_le_mul_of_nonneg_left hT (by positivity)
    _ = 4 * (((Work.FIPlan.absDelta z1 z2).divisors.card : ℝ) ^ 3)
          * (Nat.gcd (Work.FIPlan.absDelta z1 z2)
              ((h1 ^ 2 - (a : ℤ) * h2 ^ 2).natAbs) : ℝ) / (Work.FIPlan.absDelta z1 z2 : ℝ) := by
        rw [div_eq_inv_mul]



end Work.FIArea2
