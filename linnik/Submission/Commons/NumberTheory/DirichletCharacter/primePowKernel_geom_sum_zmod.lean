import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.primePowSubgroup_quadratic_sum_bound

namespace Commons.NumberTheory.DirichletCharacter

open scoped BigOperators

/-- The vanishing of the reduction of `d : ZMod (p ^ e)` modulo `p` is equivalent to
`p` dividing the canonical representative `d.val`. -/
private lemma zmod_castHom_zmod_eq_zero_iff (p e : ℕ) [Fact p.Prime]
    (h : p ∣ p ^ e) (d : ZMod (p ^ e)) :
    (ZMod.castHom h (ZMod p) d = 0) ↔ p ∣ d.val := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]


/-- **Kernel orthogonality over a full range `p ^ n`.**

Let `p` be a prime, `e ≥ 2`, and `χ` a Dirichlet character modulo `p ^ e` which is non-trivial
on the top kernel element `1 + p ^ (e-1)`; set `ζ = χ (1 + p ^ (e-1))`, a primitive `p`-th root
of unity.  Then for `n ≥ 1` and any `d : ZMod (p ^ e)`,
`∑_{t < p^n} χ (1 + p^(e-1) * (t * d))` equals `p^n` when the reduction of `d` modulo `p`
vanishes, and `0` otherwise.

The existing commons lemma `Commons.NumberTheory.DirichletCharacter.primePowKernel_sum_orthogonality`
is the case `n = 1` written with an integer multiplier; this is the version for arbitrary powers
`p ^ n` with `d : ZMod (p ^ e)`.  A short proof: write `d = (d.val : ZMod (p^e))`, use
`primePowKernel_char_pow` to see that each term equals `ζ ^ (t * d.val)`, and evaluate the
geometric sum (whose length `p ^ n` is a multiple of `p`). -/
theorem primePowKernel_geom_sum_zmod (p e : ℕ) [Fact p.Prime] (he : 2 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e))
    (htop : χ ((((1 + p ^ (e - 1) : ℕ)) : ZMod (p ^ e))) ≠ 1)
    (d : ZMod (p ^ e)) (n : ℕ) (hn : 1 ≤ n) :
    ∑ t ∈ Finset.range (p ^ n),
        χ (1 + (((p ^ (e - 1) : ℕ)) : ZMod (p ^ e)) * ((t : ZMod (p ^ e)) * d))
      = if (ZMod.castHom (by simpa using pow_dvd_pow p (show 1 ≤ e by omega)) (ZMod p) d = 0)
          then ((p ^ n : ℕ) : ℂ) else 0 := by
  set ζ : ℂ := χ ((((1 + p ^ (e - 1) : ℕ)) : ZMod (p ^ e))) with hζdef
  set z : ℂ := ζ ^ d.val with hzdef
  have hζne : ζ ≠ 1 := by rw [hζdef]; exact htop
  have hζp : ζ ^ p = 1 := by
    rw [hζdef, ← primePowKernel_char_pow p e he χ p]
    have hcast : (((1 + (p : ℤ) ^ (e - 1) * ((p : ℕ) : ℤ) : ℤ)) : ZMod (p ^ e)) = 1 := by
      have h1 : (1 + (p : ℤ) ^ (e - 1) * ((p : ℕ) : ℤ)) = (1 : ℤ) + (p : ℤ) ^ e := by
        rw [show e = (e - 1) + 1 by omega, pow_succ]
        push_cast
        ring
      rw [h1, Int.cast_add, Int.cast_one]
      have hpz : (((p : ℤ) ^ e : ℤ) : ZMod (p ^ e)) = 0 := by
        rw [show (((p : ℤ) ^ e : ℤ)) = (↑(p ^ e) : ℤ) by push_cast; ring]
        rw [Int.cast_natCast, ZMod.natCast_self]
      rw [hpz, add_zero]
    rw [hcast, map_one]
  have hterm : ∀ t : ℕ,
      χ (1 + (((p ^ (e - 1) : ℕ)) : ZMod (p ^ e)) * ((t : ZMod (p ^ e)) * d)) = z ^ t := by
    intro t
    have hdcast : ((d.val : ℕ) : ZMod (p ^ e)) = d := ZMod.natCast_zmod_val d
    have h1 : ((t : ZMod (p ^ e)) * d) = ((t * d.val : ℕ) : ZMod (p ^ e)) := by
      conv_lhs => rw [← hdcast]
      push_cast
      ring
    rw [h1]
    have h2 : (1 : ZMod (p ^ e)) + (((p ^ (e - 1) : ℕ)) : ZMod (p ^ e))
          * ((t * d.val : ℕ) : ZMod (p ^ e))
        = (((1 + (p : ℤ) ^ (e - 1) * ((t * d.val : ℕ) : ℤ) : ℤ)) : ZMod (p ^ e)) := by
      push_cast; ring
    rw [h2, primePowKernel_char_pow p e he χ (t * d.val), ← hζdef]
    rw [pow_mul', hzdef]
  rw [Finset.sum_congr rfl (fun t _ => hterm t)]
  have hcond : ∀ (h : p ∣ p ^ e), (ZMod.castHom h (ZMod p) d = 0) ↔ p ∣ d.val :=
    fun h => zmod_castHom_zmod_eq_zero_iff p e h d
  by_cases hp : p ∣ d.val
  · have hz1 : z = 1 := by
      obtain ⟨c, hc⟩ := hp
      rw [hzdef, hc, pow_mul, hζp, one_pow]
    rw [hz1, if_pos ((hcond _).mpr hp)]
    simp
  · have hzne : z ≠ 1 := by
      intro h
      have h1 : orderOf ζ ∣ d.val := by
        rw [hzdef] at h
        exact orderOf_dvd_iff_pow_eq_one.mpr h
      have h2 : orderOf ζ ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hζp
      have hord : orderOf ζ = p := by
        rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp h2 with h' | h'
        · exact absurd (orderOf_eq_one_iff.mp h') hζne
        · exact h'
      rw [hord] at h1
      exact hp h1
    rw [if_neg (fun h => hp ((hcond _).mp h))]
    have hn1 : p ^ n = p * p ^ (n - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hn]
      rw [pow_succ']
    have hzpow : z ^ (p ^ n) = 1 := by
      have hexp : d.val * p ^ n = p * (d.val * p ^ (n - 1)) := by rw [hn1]; ring
      calc z ^ (p ^ n) = (ζ ^ d.val) ^ (p ^ n) := by rw [hzdef]
        _ = ζ ^ (d.val * p ^ n) := (pow_mul ζ d.val (p ^ n)).symm
        _ = ζ ^ (p * (d.val * p ^ (n - 1))) := by rw [hexp]
        _ = (ζ ^ p) ^ (d.val * p ^ (n - 1)) := pow_mul ζ p _
        _ = 1 := by rw [hζp, one_pow]
    have hgeom : (∑ t ∈ Finset.range (p ^ n), z ^ t) * (1 - z) = 0 := by
      rw [geom_sum_mul_neg, hzpow, sub_self]
    rcases mul_eq_zero.mp hgeom with h | h
    · exact h
    · exact absurd (sub_eq_zero.mp h).symm hzne


end Commons.NumberTheory.DirichletCharacter
