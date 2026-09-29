import Mathlib
import Submission.Work.TMC16Core.Basic.nnDist

/-!
# Dirichlet's grid lemma for the distance to the nearest integer (`nn`)

`Work.Core.exists_nn_le`: for `p, q` coprime integers with `q ≥ 1` and any real `θ`,
some `k ∈ {1, …, q}` satisfies

  `nn (θ + k · p/q) ≤ 1/(2q)`,

where `nn` is the distance to the nearest integer.

**Mathematics.**  Multiplication by `p` permutes the residues modulo `q` (`p` is a unit
mod `q`, since `gcd p q = 1`).  Hence, writing `A = round (-qθ)` so that `|qθ + A| ≤ 1/2`,
there is `k ∈ {1, …, q}` and `m : ℤ` with `k p = A + m q`; therefore

  `θ + k p/q = (qθ + A)/q + m`,

and since `nn` is unchanged by translation by an integer,

  `nn (θ + k p/q) = nn ((qθ + A)/q) ≤ |qθ + A| / q ≤ 1/(2q)`.

The only input that is not immediate is the arithmetic fact, which is proved here as
`Work.Core.mul_mod_exists` (a Bézout/CRT statement, usable on its own).
-/

namespace Work.Core

open Work.TMC16Core.Basic

/-- **Bezout/CRT, explicit form.**  If `p : ℤ` is coprime to `q : ℕ`, `q > 0`, then every
integer `A` is congruent modulo `q` to `k * p` for some `k ∈ {1, …, q}`; equivalently
`k * p = A + m * q` for a suitable `m : ℤ`.

(The representative is chosen in `{1, …, q}` rather than `{0, …, q-1}`: it is
`((k₀ - 1) mod q) + 1`, which also covers the residue `0`.) -/
lemma mul_mod_exists (p : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime p.natAbs q) (A : ℤ) :
    ∃ k ∈ Finset.Icc 1 q, ∃ m : ℤ, (k : ℤ) * p = A + m * (q : ℤ) := by
  have hqZ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hqne : (q : ℤ) ≠ 0 := ne_of_gt hqZ
  -- Bezout: `gcd p q = 1`, hence `p * gcdA + q * gcdB = 1`.
  have hgcd : Int.gcd p (q : ℤ) = 1 := by
    rw [Int.gcd_eq_natAbs]
    simpa using hcop.gcd_eq_one
  have hbez : p * p.gcdA (q : ℤ) + (q : ℤ) * p.gcdB (q : ℤ) = 1 := by
    have h := Int.gcd_eq_gcd_ab p (q : ℤ)
    rw [hgcd] at h
    norm_num at h
    exact h.symm
  -- A first solution `k0 * p = A + m0 * q`, namely `k0 = A * gcdA`, `m0 = -(A * gcdB)`.
  set k0 : ℤ := A * p.gcdA (q : ℤ) with hk0
  -- Reduce `k0` modulo `q` into the interval `{1, …, q}`.
  set s : ℤ := (k0 - 1) % (q : ℤ) with hs
  have hs0 : 0 ≤ s := by rw [hs]; exact Int.emod_nonneg _ hqne
  have hsq : s < (q : ℤ) := by rw [hs]; exact Int.emod_lt_of_pos _ hqZ
  set K : ℤ := s + 1 with hK
  have hK1 : 1 ≤ K := by rw [hK]; omega
  have hKq : K ≤ (q : ℤ) := by rw [hK]; omega
  have hKnat : ((K.toNat : ℕ) : ℤ) = K := Int.toNat_of_nonneg (by omega)
  have hKmem : K.toNat ∈ Finset.Icc 1 q := by
    rw [Finset.mem_Icc]
    constructor
    · have : (1 : ℤ) ≤ (K.toNat : ℤ) := by rw [hKnat]; exact hK1
      exact_mod_cast this
    · have : (K.toNat : ℤ) ≤ (q : ℤ) := by rw [hKnat]; exact hKq
      exact_mod_cast this
  have hdvd : (q : ℤ) ∣ K * p - A := by
    have hk0eq : k0 * p = A + (-(A * p.gcdB (q : ℤ))) * (q : ℤ) := by
      rw [hk0]
      have h1 : p.gcdA (q : ℤ) * p = 1 - (q : ℤ) * p.gcdB (q : ℤ) := by
        have h2 : p * p.gcdA (q : ℤ) = p.gcdA (q : ℤ) * p := mul_comm _ _
        linarith [hbez, h2]
      rw [mul_assoc, h1]
      ring
    -- `q ∣ K - k0` because `K = ((k0 - 1) mod q) + 1`.
    have h1 : (q : ℤ) ∣ K - k0 := by
      refine ⟨-((k0 - 1) / (q : ℤ)), ?_⟩
      have h := Int.mul_ediv_add_emod (k0 - 1) (q : ℤ)
      rw [← hs] at h
      rw [hK]
      linarith [h]
    -- `q ∣ k0 * p - A`.
    have h2 : (q : ℤ) ∣ k0 * p - A := ⟨-(A * p.gcdB (q : ℤ)), by linarith [hk0eq]⟩
    have h3 : K * p - A = (K - k0) * p + (k0 * p - A) := by ring
    rw [h3]
    exact dvd_add (h1.mul_right p) h2
  obtain ⟨m, hm⟩ := hdvd
  exact ⟨K.toNat, hKmem, m, by rw [hKnat]; linarith⟩

theorem exists_nn_le (p : ℤ) (q : ℕ) (hq : 0 < q) (hcop : Nat.Coprime p.natAbs q) (θ : ℝ) :
    ∃ k ∈ Finset.Icc 1 q,
      Work.TMC16Core.Basic.nn (θ + (k : ℝ) * ((p : ℝ) / (q : ℝ))) ≤ 1 / (2 * (q : ℝ)) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  -- `A = round (-qθ)` is within `1/2` of `-qθ`, and `k p = A + m q` for a suitable `k`.
  obtain ⟨k, hk, m, hm⟩ := mul_mod_exists p q hq hcop (round (-(θ * (q : ℝ))))
  refine ⟨k, hk, ?_⟩
  have hkR : (k : ℝ) * (p : ℝ) =
      ((round (-(θ * (q : ℝ))) : ℤ) : ℝ) + (m : ℝ) * (q : ℝ) := by
    exact_mod_cast hm
  have hkey : θ + (k : ℝ) * ((p : ℝ) / (q : ℝ)) =
      ((θ * (q : ℝ) + ((round (-(θ * (q : ℝ))) : ℤ) : ℝ)) / (q : ℝ)) + (m : ℝ) := by
    field_simp
    linarith [hkR]
  rw [hkey, nn_add_intCast]
  have hbound : |θ * (q : ℝ) + ((round (-(θ * (q : ℝ))) : ℤ) : ℝ)| ≤ 1 / 2 := by
    have h := abs_sub_round (-(θ * (q : ℝ)))
    rw [show θ * (q : ℝ) + ((round (-(θ * (q : ℝ))) : ℤ) : ℝ)
          = -(-(θ * (q : ℝ)) - ((round (-(θ * (q : ℝ))) : ℤ) : ℝ)) by ring, abs_neg]
    exact h
  calc nn ((θ * (q : ℝ) + ((round (-(θ * (q : ℝ))) : ℤ) : ℝ)) / (q : ℝ))
      ≤ |(θ * (q : ℝ) + ((round (-(θ * (q : ℝ))) : ℤ) : ℝ)) / (q : ℝ)| := nn_le_abs _
    _ = |θ * (q : ℝ) + ((round (-(θ * (q : ℝ))) : ℤ) : ℝ)| / (q : ℝ) := by
        rw [abs_div, abs_of_pos hqR]
    _ ≤ (1 / 2) / (q : ℝ) := div_le_div_of_nonneg_right hbound hqR.le
    _ = 1 / (2 * (q : ℝ)) := by rw [div_div]

end Work.Core
