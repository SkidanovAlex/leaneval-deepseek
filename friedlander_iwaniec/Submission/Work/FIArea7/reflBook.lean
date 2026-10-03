import Mathlib
import Submission.Work.FIArea7.KronTwoAux
import Submission.Work.FIArea7.KronTwo

namespace Work.FIArea7

/-- The coprimality behind the bookkeeping of `reflBook`: for odd `u₁` coprime to `u₂` and to `s₁`,

  `(u₁, u₁s₂ − u₂s₁) = 1`.

(Indeed `u₁s₂ − u₂s₁ ≡ −u₂s₁ (mod u₁)` and both `u₂` and `s₁` are coprime to `u₁`.)  In the
form used below: `Int.gcd u₁ (u₁s₂ − u₂s₁) = 1`. -/
lemma gcd_u1_diff_u2_mul_s1 {u1 u2 : ℕ} {s1 s2 : ℤ} (h12 : u1.Coprime u2)
    (hu1s1 : u1.Coprime s1.natAbs) :
    (u1 : ℤ).gcd ((u1 : ℤ) * s2 - (u2 : ℤ) * s1) = 1 := by
  have hmod : ((u1 : ℤ) * s2 - (u2 : ℤ) * s1) % (u1 : ℤ)
      = (-((u2 : ℤ) * s1)) % (u1 : ℤ) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    have h : (u1 : ℤ) * s2 - (u2 : ℤ) * s1 - -((u2 : ℤ) * s1) = (u1 : ℤ) * s2 := by ring
    rw [h, Int.mul_emod_right]
  calc (u1 : ℤ).gcd ((u1 : ℤ) * s2 - (u2 : ℤ) * s1)
      = (((u1 : ℤ) * s2 - (u2 : ℤ) * s1) % (u1 : ℤ)).gcd (u1 : ℤ) := by
        rw [Int.gcd_comm, ← Int.gcd_emod]
    _ = ((-((u2 : ℤ) * s1)) % (u1 : ℤ)).gcd (u1 : ℤ) := by rw [hmod]
    _ = (-((u2 : ℤ) * s1)).gcd (u1 : ℤ) := by rw [Int.gcd_emod]
    _ = ((u2 : ℤ) * s1).gcd (u1 : ℤ) := by
        rw [Int.gcd_eq_natAbs, Int.gcd_eq_natAbs, Int.natAbs_neg]
    _ = (u1 : ℤ).gcd ((u2 : ℤ) * s1) := by rw [Int.gcd_comm]
    _ = 1 := by
        rw [Int.gcd_eq_natAbs, Int.natAbs_natCast, Int.natAbs_mul, Int.natAbs_natCast]
        exact h12.mul_right hu1s1

/-- **The Jacobi bookkeeping of the reflection `(z₂/z₁||Δ|) = (|z₁|²||Δ|)·(Re(z̄₁z₂)||Δ|)`.**
Writing `rᵢ = g·uᵢ` with `g = (r₁,r₂) > 0` (so `|Δ| = g·|u₁s₂ − u₂s₁|`,
`Re(z̄₁z₂) = g²u₁u₂ + s₁s₂`, `|z₁|² = g²u₁² + s₁²`), the product of the two Jacobi symbols with
modulus `|Δ|` splits into the symbol of `s₁s₂` to modulus `g` times the symbol of `u₁u₂` to
modulus `|u₁s₂ − u₂s₁|`.  The two ingredients are `g²u₁²+s₁² ≡ s₁² (mod g)` (and `(g,s₁)=1`, so
the symbol of `|z₁|²` to modulus `g` is `1`) and `(g²u₁u₂+s₁s₂)·u₁² ≡ u₁u₂·(g²u₁²+s₁²) (mod
u₁s₂−u₂s₁)` together with `(u₁² ||u₁s₂−u₂s₁|) = 1` (which needs `(u₁,u₂) = (u₁,s₁) = 1`) and
`(|z₁|², |u₁s₂−u₂s₁|) = 1`. -/
theorem reflBook {g u1 u2 : ℕ} {s1 s2 : ℤ}
    (hg : 0 < g) (hu1 : Odd u1) (hu2 : Odd u2)
    (h12 : u1.Coprime u2) (hgs1 : g.Coprime s1.natAbs)
    (hu1s1 : u1.Coprime s1.natAbs)
    (hB : (((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2).natAbs).Coprime
        (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs))
    (hD : (u1 : ℤ) * s2 - (u2 : ℤ) * s1 ≠ 0) :
    jacobiSym ((g : ℤ) ^ 2 * (u1 : ℤ) * (u2 : ℤ) + s1 * s2)
        (g * (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs))
      * jacobiSym ((((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2).natAbs : ℕ) : ℤ)
        (g * (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs))
      = jacobiSym (s1 * s2) g
        * jacobiSym (((u1 * u2 : ℕ) : ℤ)) (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs) := by
  -- the modulus `|Δ| = g·|u₁s₂ − u₂s₁|` is nonzero: split it
  have hDne : ((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs ≠ 0 := (Int.natAbs_pos.mpr hD).ne'
  -- `|z₁|² = g²u₁² + s₁²` is the nonnegative integer it is the `natAbs` of
  have hBcast : ((((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2).natAbs : ℕ) : ℤ)
      = (g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2 := Int.natAbs_of_nonneg (by positivity)
  rw [jacobiSym.mul_right' _ hg.ne' hDne, jacobiSym.mul_right' _ hg.ne' hDne, hBcast]
  -- `g²u₁u₂ + s₁s₂ ≡ s₁s₂ (mod g)`
  have hAg : jacobiSym ((g : ℤ) ^ 2 * (u1 : ℤ) * (u2 : ℤ) + s1 * s2) g
      = jacobiSym (s1 * s2) g := by
    have h : ((g : ℤ) ^ 2 * (u1 : ℤ) * (u2 : ℤ) + s1 * s2) ≡ s1 * s2 [ZMOD (g : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      exact ⟨-((g : ℤ) * (u1 : ℤ) * (u2 : ℤ)), by ring⟩
    exact jacobiSym.mod_left' h
  -- `g²u₁² + s₁² ≡ s₁² (mod g)` and `(g, s₁) = 1`, so the `g`-symbol of `|z₁|²` is `1`
  have hBg : jacobiSym ((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2) g = 1 := by
    have hm : ((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2) ≡ s1 ^ 2 [ZMOD (g : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      exact ⟨-((g : ℤ) * (u1 : ℤ) ^ 2), by ring⟩
    rw [jacobiSym.mod_left' hm]
    have hsq : s1 ^ 2 = ((s1.natAbs : ℤ)) ^ 2 := by
      rw [pow_two, pow_two, ← Nat.cast_mul, Int.natAbs_mul_self]
    rw [hsq]
    have hg1 : ((s1.natAbs : ℤ)).gcd (g : ℤ) = 1 := by
      simp only [Int.gcd_eq_natAbs, Int.natAbs_natCast]
      exact hgs1.symm
    rw [jacobiSym.sq_one' hg1]
  -- `(g²u₁u₂+s₁s₂)·u₁² ≡ u₁u₂·(g²u₁²+s₁²) (mod u₁s₂−u₂s₁)`, with `(u₁², |u₁s₂−u₂s₁|) = 1`
  have hAD : jacobiSym ((g : ℤ) ^ 2 * (u1 : ℤ) * (u2 : ℤ) + s1 * s2)
        (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs)
      = jacobiSym (((u1 * u2 : ℕ) : ℤ)) (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs)
        * jacobiSym ((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2)
            (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs) := by
    have hmC : ((g : ℤ) ^ 2 * (u1 : ℤ) * (u2 : ℤ) + s1 * s2) * (u1 : ℤ) ^ 2
        ≡ ((u1 : ℤ) * (u2 : ℤ)) * ((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2)
          [ZMOD ((((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs : ℕ) : ℤ)] := by
      rw [Int.modEq_iff_dvd]
      have h : ((u1 : ℤ) * (u2 : ℤ)) * ((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2)
          - ((g : ℤ) ^ 2 * (u1 : ℤ) * (u2 : ℤ) + s1 * s2) * (u1 : ℤ) ^ 2
          = -(s1 * u1) * ((u1 : ℤ) * s2 - (u2 : ℤ) * s1) := by ring
      rw [h]
      exact dvd_mul_of_dvd_right
        ((Int.natAbs_dvd (a := (u1 : ℤ) * s2 - (u2 : ℤ) * s1)
          (b := (u1 : ℤ) * s2 - (u2 : ℤ) * s1)).mpr dvd_rfl) _
    have hsq2 : jacobiSym ((u1 : ℤ) ^ 2) (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs) = 1 := by
      have hg1 : (u1 : ℤ).gcd ((((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs : ℕ) : ℤ) = 1 := by
        simpa only [Int.gcd_eq_natAbs, Int.natAbs_natCast] using
          gcd_u1_diff_u2_mul_s1 (s2 := s2) h12 hu1s1
      exact jacobiSym.sq_one' hg1
    calc jacobiSym ((g : ℤ) ^ 2 * (u1 : ℤ) * (u2 : ℤ) + s1 * s2)
          (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs)
        = jacobiSym ((g : ℤ) ^ 2 * (u1 : ℤ) * (u2 : ℤ) + s1 * s2)
              (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs)
            * jacobiSym ((u1 : ℤ) ^ 2) (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs) := by
          rw [hsq2, mul_one]
      _ = jacobiSym (((g : ℤ) ^ 2 * (u1 : ℤ) * (u2 : ℤ) + s1 * s2) * (u1 : ℤ) ^ 2)
            (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs) :=
          (jacobiSym.mul_left _ _ _).symm
      _ = jacobiSym (((u1 : ℤ) * (u2 : ℤ)) * ((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2))
            (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs) := jacobiSym.mod_left' hmC
      _ = jacobiSym ((u1 : ℤ) * (u2 : ℤ)) (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs)
            * jacobiSym ((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2)
              (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs) := jacobiSym.mul_left _ _ _
      _ = jacobiSym (((u1 * u2 : ℕ) : ℤ)) (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs)
            * jacobiSym ((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2)
              (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs) := by rw [Nat.cast_mul]
  -- `(|z₁|², |u₁s₂−u₂s₁|) = 1`, so the square of the `|u₁s₂−u₂s₁|`-symbol of `|z₁|²` is `1`
  have hBD : jacobiSym ((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2)
        (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs)
      * jacobiSym ((g : ℤ) ^ 2 * (u1 : ℤ) ^ 2 + s1 ^ 2)
        (((u1 : ℤ) * s2 - (u2 : ℤ) * s1).natAbs) = 1 := by
    rw [← sq]
    exact jacobiSym.sq_one (by
      simpa only [Int.gcd_eq_natAbs, Int.natAbs_natCast] using hB)
  rw [hAg, hBg, hAD, one_mul, mul_assoc, mul_assoc, hBD, mul_one]

end Work.FIArea7
