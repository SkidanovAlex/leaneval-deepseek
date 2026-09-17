import Mathlib.Algebra.Lie.UniversalEnveloping

set_option linter.style.haveILetI false

namespace Commons.Algebra.Lie.Sl2

/-- **Commutation of `E` with powers of `F` in an associative `R`-algebra.**

Let `E F H` be elements of an associative `R`-algebra satisfying the two "`𝔰𝔩₂`-like" relations
`E * F = F * E + H` and `H * F = F * H - 2 • F`.  Then for every natural number `n`,
$E F^{n+1} = F^{n+1} E + (n+1)\bigl(F^{n}(H - n)\bigr).$
This is the shifted form (no truncated subtraction in the exponent) of the classical `𝔰𝔩₂`
commutation relation; the accompanying lemma `uea_mul_pow` is its universal enveloping algebra
specialisation.

The proof is a direct induction: multiplying the induction hypothesis on the right by `F`,
using `E F = F E + H` to expand `E F` and `H F = F H - 2 F` to commute `H` past the remaining
`F`'s. -/
theorem uea_mul_pow_aux {R A : Type*} [CommRing R] [Ring A] [Algebra R A]
    (E F H : A) (hEF : E * F = F * E + H) (hHF : H * F = F * H - (2 : R) • F) :
    ∀ n : ℕ, E * F ^ (n+1) = F ^ (n+1) * E
      + ((n+1 : ℕ) : R) • (F ^ n * (H - (n : R) • 1)) := by
  intro n
  induction n with
  | zero =>
    simpa using hEF
  | succ n ih =>
    have hinner : (H - (n : R) • (1:A)) * F = F * H - ((n+2 : ℕ) : R) • F := by
      rw [sub_mul, smul_mul_assoc, one_mul, hHF, sub_sub, ← add_smul]
      rw [show ((2:R) + (n:R)) = ((n+2:ℕ):R) by push_cast; ring]
    have hT : ((n+1 : ℕ) : R) • ((F^n * (H - (n : R) • 1)) * F)
        = ((n+1 : ℕ) : R) • (F^(n+1) * H - ((n+2:ℕ):R) • F^(n+1)) := by
      rw [mul_assoc, hinner, mul_sub, mul_smul_comm, ← mul_assoc, ← pow_succ]
    have hscal : F^(n+1) * H + ((n+1:ℕ):R) • (F^(n+1) * H - ((n+2:ℕ):R) • F^(n+1))
        = ((n+2:ℕ):R) • (F^(n+1) * H - ((n+1:ℕ):R) • F^(n+1)) := by
      rw [smul_sub, smul_smul, smul_sub, smul_smul]
      rw [← add_sub_assoc]
      nth_rewrite 1 [← one_smul R (F^(n+1) * H)]
      rw [← add_smul]
      rw [show (1:R) + ↑(n+1) = ↑(n+2) by push_cast; ring]
      rw [show (↑(n+1) : R) * ↑(n+2) = ↑(n+2) * ↑(n+1) by ring]
    have step1 : E * F ^ (n+1+1) = (E * F ^ (n+1)) * F := by
      rw [pow_succ, ← mul_assoc]
    rw [step1, ih]
    rw [add_mul, smul_mul_assoc, mul_assoc, hEF, mul_add, ← mul_assoc, ← pow_succ, hT]
    rw [add_assoc, hscal]
    rw [mul_sub, mul_smul_comm, mul_one]

/-- **The `𝔰𝔩₂` commutation relation in the universal enveloping algebra.**

Let `e f h : L` be elements of a Lie algebra `L` over a commutative ring `R` satisfying
`⁅e, f⁆ = h` and `⁅h, f⁆ = -2 f` (so that `(h, e, f)` behaves like a half of an `𝔰𝔩₂`-triple).
Writing `E = ι e`, `F = ι f`, `H = ι h` for their images in the universal enveloping algebra, one
has for every `n : ℕ`
$E F^n = F^n E + n \cdot F^{n-1}\bigl(H - (n-1)\bigr).$
Only the two relations above are used (in particular `⁅h, e⁆ = 2e` is *not* needed). -/
theorem uea_mul_pow {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (e f h : L) (hef : ⁅e, f⁆ = h) (hhf : ⁅h, f⁆ = -(2 : R) • f) (n : ℕ) : UniversalEnvelopingAlgebra.ι R e * (UniversalEnvelopingAlgebra.ι R f) ^ n = (UniversalEnvelopingAlgebra.ι R f) ^ n * UniversalEnvelopingAlgebra.ι R e + (n : R) • ((UniversalEnvelopingAlgebra.ι R f) ^ (n - 1) * (UniversalEnvelopingAlgebra.ι R h - ((n - 1 : ℕ) : R) • 1)) := by
  letI : LieRing (UniversalEnvelopingAlgebra R L) := LieRing.ofAssociativeRing
  have hEF : UniversalEnvelopingAlgebra.ι R e * UniversalEnvelopingAlgebra.ι R f
      = UniversalEnvelopingAlgebra.ι R f * UniversalEnvelopingAlgebra.ι R e
        + UniversalEnvelopingAlgebra.ι R h := by
    have h1 : ⁅UniversalEnvelopingAlgebra.ι R e, UniversalEnvelopingAlgebra.ι R f⁆
        = UniversalEnvelopingAlgebra.ι R h := by
      rw [← LieHom.map_lie (UniversalEnvelopingAlgebra.ι R) e f, hef]
    rw [LieRing.of_associative_ring_bracket] at h1
    exact sub_eq_iff_eq_add'.mp h1
  have hHF : UniversalEnvelopingAlgebra.ι R h * UniversalEnvelopingAlgebra.ι R f
      = UniversalEnvelopingAlgebra.ι R f * UniversalEnvelopingAlgebra.ι R h
        - (2 : R) • UniversalEnvelopingAlgebra.ι R f := by
    have h1 : ⁅UniversalEnvelopingAlgebra.ι R h, UniversalEnvelopingAlgebra.ι R f⁆
        = -(2 : R) • UniversalEnvelopingAlgebra.ι R f := by
      rw [← LieHom.map_lie (UniversalEnvelopingAlgebra.ι R) h f, hhf]
      simp
    rw [LieRing.of_associative_ring_bracket] at h1
    have h2 := sub_eq_iff_eq_add'.mp h1
    rw [neg_smul, ← sub_eq_add_neg] at h2
    exact h2
  rcases n with _ | m
  · simp
  · have h := uea_mul_pow_aux (UniversalEnvelopingAlgebra.ι R e) (UniversalEnvelopingAlgebra.ι R f)
        (UniversalEnvelopingAlgebra.ι R h) hEF hHF m
    simpa [Nat.add_sub_cancel] using h

end Commons.Algebra.Lie.Sl2