import Mathlib

namespace Work.Peluse.LadderA

/-- Product of powers of a single base `γ ∈ (0,1]`, exponents `(n:ℝ)*s`, `(n:ℝ)*hB` and `1`. -/
private lemma gamma_prod_eq {γ : ℝ} (hγ : 0 < γ) (s hB : ℝ) (n : ℕ) :
    γ ^ (1 + (n:ℝ) * (s + hB)) = γ * γ ^ ((n:ℝ) * s) * γ ^ ((n:ℝ) * hB) := by
  have e : (1:ℝ) + (n:ℝ) * (s + hB) = (1 + (n:ℝ) * s) + (n:ℝ) * hB := by ring
  rw [e, Real.rpow_add hγ, Real.rpow_add hγ, Real.rpow_one]

/-- The bookkeeping inequality without its constant prefactor: for `0 < c`, `0 < γ, γ' ≤ 1` and
exponents `s, hB` with `1 + n*(s+hB) ≤ K` and `hB ≤ K`,
`c^(s+hB) · (γγ')^K ≤ γ · (c γ^n)^s · (c γ^n γ')^hB`. -/
private lemma key_aux {c γ γ' s hB : ℝ} {n K : ℕ}
    (hc : 0 < c) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hγ' : 0 < γ') (hγ'1 : γ' ≤ 1)
    (hK1 : 1 + (n:ℝ) * (s + hB) ≤ (K:ℝ)) (hK2 : hB ≤ (K:ℝ)) :
    c ^ (s + hB) * (γ * γ') ^ K ≤ γ * (c * γ ^ n) ^ s * (c * γ ^ n * γ') ^ hB := by
  have hγK : γ ^ (K:ℝ) ≤ γ ^ (1 + (n:ℝ) * (s + hB)) :=
    Real.rpow_le_rpow_of_exponent_ge hγ hγ1 hK1
  have hγ'K : γ' ^ (K:ℝ) ≤ γ' ^ hB :=
    Real.rpow_le_rpow_of_exponent_ge hγ' hγ'1 hK2
  have hcore : γ ^ (K:ℝ) * γ' ^ (K:ℝ) ≤ γ ^ (1 + (n:ℝ) * (s + hB)) * γ' ^ hB :=
    mul_le_mul hγK hγ'K (Real.rpow_nonneg hγ'.le _) (Real.rpow_nonneg hγ.le _)
  have hL : c ^ (s + hB) * (γ * γ') ^ K = c ^ (s + hB) * (γ ^ (K:ℝ) * γ' ^ (K:ℝ)) := by
    rw [← Real.rpow_natCast (γ * γ') K, Real.mul_rpow hγ.le hγ'.le]
  have hR : γ * (c * γ ^ n) ^ s * (c * γ ^ n * γ') ^ hB
      = c ^ (s + hB) * (γ ^ (1 + (n:ℝ) * (s + hB)) * γ' ^ hB) := by
    rw [Real.mul_rpow hc.le (pow_nonneg hγ.le n),
        Real.mul_rpow (mul_nonneg hc.le (pow_nonneg hγ.le n)) hγ'.le,
        Real.mul_rpow hc.le (pow_nonneg hγ.le n),
        ← Real.rpow_natCast γ n, ← Real.rpow_mul hγ.le (n:ℝ) s,
        ← Real.rpow_mul hγ.le (n:ℝ) hB,
        Real.rpow_add hc, gamma_prod_eq hγ s hB n]
    ring
  rw [hL, hR]
  exact mul_le_mul_of_nonneg_left hcore (Real.rpow_nonneg hc.le _)

theorem mainBookkeep {γ γ' c₁ C' : ℝ} {Kbig Kb Khc m tbig lev : ℕ}
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hγ'0 : 0 < γ') (hγ'1 : γ' ≤ 1)
    (hc₁ : 0 < c₁) (hC' : 0 < C')
    (h1 : 1 + (2 : ℝ) ^ m * (1 + (Khc : ℝ) * (2 : ℝ) ^ tbig) / (2 : ℝ) ^ lev ≤ (Kbig : ℝ))
    (h2 : (Khc : ℝ) * (2 : ℝ) ^ tbig / (2 : ℝ) ^ lev ≤ (Kbig : ℝ)) :
    (1 / (2 * ((Kb : ℝ) + 1))) * c₁ ^ ((1 + (Khc : ℝ) * (2 : ℝ) ^ tbig) / (2 : ℝ) ^ lev) *
        ((1 : ℝ) / 2) ^ (2 ^ tbig) * (C') ^ ((2 : ℝ) ^ tbig / (2 : ℝ) ^ lev) *
        (γ * γ') ^ Kbig
      ≤ (γ / (2 * ((Kb : ℝ) + 1))) *
        ((c₁ * γ ^ (2 ^ m)) ^ (1 / (2 : ℝ) ^ lev) * ((1 : ℝ) / 2) ^ (2 ^ tbig) *
          (C') ^ ((2 : ℝ) ^ tbig / (2 : ℝ) ^ lev) *
          (c₁ * γ ^ (2 ^ m) * γ') ^ ((Khc : ℝ) * (2 : ℝ) ^ tbig / (2 : ℝ) ^ lev)) := by
  -- split the exponent of `c₁` on the left as `1/2^lev + Khc*2^tbig/2^lev`
  have hA : (1 + (Khc : ℝ) * (2 : ℝ) ^ tbig) / (2 : ℝ) ^ lev
      = 1 / (2 : ℝ) ^ lev + (Khc : ℝ) * (2 : ℝ) ^ tbig / (2 : ℝ) ^ lev := by ring
  have hA2 : (2 : ℝ) ^ m * (1 + (Khc : ℝ) * (2 : ℝ) ^ tbig) / (2 : ℝ) ^ lev
      = (2 : ℝ) ^ m * (1 / (2 : ℝ) ^ lev + (Khc : ℝ) * (2 : ℝ) ^ tbig / (2 : ℝ) ^ lev) := by ring
  have hcast : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ m := by push_cast; ring
  -- the first hypothesis in the shape keyed to `key_aux`
  have h1' : 1 + ((2 ^ m : ℕ) : ℝ) * (1 / (2 : ℝ) ^ lev + (Khc : ℝ) * (2 : ℝ) ^ tbig / (2 : ℝ) ^ lev)
      ≤ (Kbig : ℝ) := by
    have h := h1
    rw [hA2] at h
    rwa [← hcast] at h
  -- the core inequality
  have hkey : c₁ ^ ((1 + (Khc : ℝ) * (2 : ℝ) ^ tbig) / (2 : ℝ) ^ lev) * (γ * γ') ^ Kbig
      ≤ γ * (c₁ * γ ^ (2 ^ m)) ^ (1 / (2 : ℝ) ^ lev)
        * (c₁ * γ ^ (2 ^ m) * γ') ^ ((Khc : ℝ) * (2 : ℝ) ^ tbig / (2 : ℝ) ^ lev) := by
    have h := key_aux (n := 2 ^ m) (K := Kbig) (s := 1 / (2 : ℝ) ^ lev)
                (hB := (Khc : ℝ) * (2 : ℝ) ^ tbig / (2 : ℝ) ^ lev)
                hc₁ hγ0 hγ1 hγ'0 hγ'1 h1' h2
    rw [← hA] at h
    exact h
  -- the common positive prefactor
  have hP : 0 < (1 / (2 * ((Kb : ℝ) + 1))) * ((1 : ℝ) / 2) ^ (2 ^ tbig)
      * (C') ^ ((2 : ℝ) ^ tbig / (2 : ℝ) ^ lev) := by positivity
  have hmain := mul_le_mul_of_nonneg_left hkey hP.le
  have e1 : (1 / (2 * ((Kb : ℝ) + 1))) * c₁ ^ ((1 + (Khc : ℝ) * (2 : ℝ) ^ tbig) / (2 : ℝ) ^ lev) *
        ((1 : ℝ) / 2) ^ (2 ^ tbig) * (C') ^ ((2 : ℝ) ^ tbig / (2 : ℝ) ^ lev) *
        (γ * γ') ^ Kbig
      = ((1 / (2 * ((Kb : ℝ) + 1))) * ((1 : ℝ) / 2) ^ (2 ^ tbig)
          * (C') ^ ((2 : ℝ) ^ tbig / (2 : ℝ) ^ lev)) *
        (c₁ ^ ((1 + (Khc : ℝ) * (2 : ℝ) ^ tbig) / (2 : ℝ) ^ lev) * (γ * γ') ^ Kbig) := by ring
  have e2 : (γ / (2 * ((Kb : ℝ) + 1))) *
        ((c₁ * γ ^ (2 ^ m)) ^ (1 / (2 : ℝ) ^ lev) * ((1 : ℝ) / 2) ^ (2 ^ tbig) *
          (C') ^ ((2 : ℝ) ^ tbig / (2 : ℝ) ^ lev) *
          (c₁ * γ ^ (2 ^ m) * γ') ^ ((Khc : ℝ) * (2 : ℝ) ^ tbig / (2 : ℝ) ^ lev))
      = ((1 / (2 * ((Kb : ℝ) + 1))) * ((1 : ℝ) / 2) ^ (2 ^ tbig)
          * (C') ^ ((2 : ℝ) ^ tbig / (2 : ℝ) ^ lev)) *
        (γ * (c₁ * γ ^ (2 ^ m)) ^ (1 / (2 : ℝ) ^ lev)
          * (c₁ * γ ^ (2 ^ m) * γ') ^ ((Khc : ℝ) * (2 : ℝ) ^ tbig / (2 : ℝ) ^ lev)) := by ring
  rw [e1, e2]
  exact hmain

end Work.Peluse.LadderA
