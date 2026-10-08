import Mathlib
import Submission.Work.Hering.HardCore.EndgameDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The endgame algebra for the abelian case of the hard core of Hering's theorem

This file proves `Work.Hering.HardCore.endgame_algebra`.  The setting is the module
`C_m = Ω_m(C) ≅ (ℤ/2^m)³` of the proof of Peterfalvi I, Chapter IV §3, Proposition 2, in the
basis `(c₁,c₂,c₃)`: `SMat m` is the matrix of the action of `s` and `TMat m k k₂ k₃` that of
the action of `t`, with parameters `k, k₂, k₃` as in the source (see `EndgameDefs`).

The hypotheses are
* `hk : k = 2u+1` (i.e. `k` is odd),
* `h91 : k₂ + k·k₃ ≡ 1 mod 2^{m-1}` (relation (9.1) of the source),
* `hT : t` has order two,
* `hA : (st)⁴ = 1`.

The conclusion is that `c₁` lies in the image of `(st)² + 1`.

The proof is an explicit computation.  Writing `A = TMat * SMat` and `F = A²`, we show

  `F = !![1, σ, 1 + 2·m₀; 0, ⋆, b·σ; 0, ⋆, 2ρ·b' - 1]`

where `σ = 2k₂ + 2k₃(1-k)`, `ρ = 2k₂+k₃-1`, `b = 2k₂(1-k)-1`, `b' = 2k₂+2k₃-1` and
`m₀ = (1-k)(1+k₂) + k₃(1-k)² - 1`.  From `hA` (i.e. `F² = 1`) we read off the (0,2)-entry of
`F² - 1`, which gives `2ρ·V = 0` for the odd (hence invertible) element
`V = (1+2m₀)b' + 2ρb`; since odd elements of `ZMod (2^m)` are units (we invert them explicitly
via the geometric series `∑_{i<m} (1-V)^i`) this forces `2ρ = 0`, and then `σ = 0` and
`F₂₂ = -1`.  Finally `x = ![1-m₀, 0, 1]` satisfies `(F+1)x = c₁`.

(Note that the hypotheses `hk` and `hT` are not used by the argument: `hT` is in fact a formal
consequence of `h91`, and the computation only needs `h91` and `hA`.)
-/

namespace Work.Hering.HardCore

open Matrix

/-- In `ZMod (2^m)` the class of `2^m` is `0`. -/
lemma two_pow_modulus_eq_zero (m : ℕ) : ((2 : ZMod (2^m))^m) = 0 := by
  rw [show (2 : ZMod (2^m)) = ((2 : ℕ) : ZMod (2^m)) from rfl, ← Nat.cast_pow]
  exact ZMod.natCast_self _

/-- In `ZMod (2^m)`, `2^j = 0` for all `j ≥ m`. -/
lemma two_pow_eq_zero_of_le {m j : ℕ} (h : m ≤ j) : ((2 : ZMod (2^m))^j) = 0 := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add, two_pow_modulus_eq_zero m, zero_mul]

theorem endgame_algebra (m : ℕ) (hm : 2 ≤ m) (k k2 k3 : ZMod (2^m))
    (hk : ∃ u : ZMod (2^m), k = 2*u + 1)
    (h91 : ∃ t : ZMod (2^m), k2 + k * k3 - 1 = 2 ^ (m - 1) * t)
    (hT : TMat m k k2 k3 * TMat m k k2 k3 = 1)
    (hA : (TMat m k k2 k3 * SMat m) ^ 4 = 1) :
    ∃ x : Fin 3 → ZMod (2^m),
      Matrix.mulVec ((TMat m k k2 k3 * SMat m) ^ 2 + 1) x = Pi.single 0 1 := by
  obtain ⟨t, ht⟩ := h91
  -- the parameter `s = 2^(m-1) t` of the congruence (9.1), and the relations it satisfies
  have hs2 : (2 : ZMod (2^m)) * (2^(m-1) * t) = 0 := by
    rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ m),
      two_pow_modulus_eq_zero, zero_mul]
  have hss : (2^(m-1)*t) * (2^(m-1)*t) = 0 := by
    have h2 : ((2 : ZMod (2^m))^(m-1))^2 = 0 := by
      rw [← pow_mul, two_pow_eq_zero_of_le (by omega : m ≤ (m-1)*2)]
    calc (2^(m-1)*t) * (2^(m-1)*t) = ((2^(m-1))^2) * (t*t) := by ring
      _ = 0 := by rw [h2, zero_mul]
  have hrel : k * k3 = 1 - k2 + 2^(m-1)*t := by linear_combination ht
  -- ## Step 1: the matrix `A = TMat * SMat`
  have hAmat : TMat m k k2 k3 * SMat m
      = !![(1 : ZMod (2^m)), 1, 1-k; 0, 2*k2-1, 2*k2*(1-k)-1; 0, 2*k3, 2*k3-2*(k*k3)+1] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [TMat, SMat, Matrix.mul_apply, Fin.sum_univ_three] <;>
      ring
  -- ## Step 2: the square `F = A²`
  have hF : (TMat m k k2 k3 * SMat m)^2
      = !![(1 : ZMod (2^m)), 2*k2 + 2*k3*(1-k), 1 + 2*((1-k)*(1+k2) + k3*(1-k)^2 - 1);
           0, (2*k2-1)*(2*k2-1) + (2*k2*(1-k)-1)*(2*k3),
             (2*k2*(1-k)-1)*(2*k2 + 2*k3*(1-k));
           0, (2*k3)*(2*k2 + 2*k3*(1-k)), 2*(2*k2+k3-1)*(2*k2+2*k3-1) - 1] := by
    rw [pow_two, hAmat]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
      (try ring) <;>
      linear_combination
        (-4*k2 - 4*(2*k2+2*k3-1) + 4*(k*k3-(1-k2+2^(m-1)*t)) + 8*(2^(m-1)*t)) * hrel
        + (-2*k2 - 2*(2*k2+2*k3-1)) * hs2 + 4 * hss
  -- ## Step 3: `σ = 2ρ`
  have hσ : 2*k2 + 2*k3*(1-k) = 2*(2*k2+k3-1) := by
    linear_combination (-2 : ZMod (2^m)) * hrel - hs2
  -- ## Step 4: the `(0,2)`-entry of `F² - 1`
  have h020 : (1 + 2*((1-k)*(1+k2) + k3*(1-k)^2 - 1))
      + (2*k2 + 2*k3*(1-k)) * ((2*k2*(1-k)-1)*(2*k2 + 2*k3*(1-k)))
      + (1 + 2*((1-k)*(1+k2) + k3*(1-k)^2 - 1)) * (2*(2*k2+k3-1)*(2*k2+2*k3-1) - 1) = 0 := by
    have h := hA
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add] at h
    have h2 : (((TMat m k k2 k3 * SMat m)^2 * (TMat m k k2 k3 * SMat m)^2) 0 2) = 0 := by
      rw [h]
      simp
    rw [Matrix.mul_apply, Fin.sum_univ_three, hF] at h2
    simpa using h2
  rw [hσ] at h020
  -- ## Step 5: `2ρ · V = 0` with `V` odd
  have hkey : (2*(2*k2+k3-1)) * ((1 + 2*((1-k)*(1+k2) + k3*(1-k)^2 - 1))*(2*k2+2*k3-1)
      + 2*(2*k2+k3-1)*(2*k2*(1-k)-1)) = 0 := by
    linear_combination h020
  -- ## Step 6: inverting the odd element `V`
  set Z : ZMod (2^m) := k2 + k3 + ((1-k)*(1+k2) + k3*(1-k)^2 - 1)*(2*k2+2*k3-1)
      + (2*k2+k3-1)*(2*k2*(1-k)-1) with hZ
  have hVZ : (1 + 2*((1-k)*(1+k2) + k3*(1-k)^2 - 1))*(2*k2+2*k3-1)
      + 2*(2*k2+k3-1)*(2*k2*(1-k)-1) = -(1 - 2*Z) := by
    rw [hZ]; ring
  have hVkey : (2*(2*k2+k3-1)) * (1 - 2*Z) = 0 := by
    have h := hkey
    rw [hVZ] at h
    linear_combination (-1) * h
  have hgeom : (1 - 2*Z) * (∑ i ∈ Finset.range m, (2*Z)^i) = 1 := by
    rw [mul_comm, geom_sum_mul_neg, mul_pow, two_pow_modulus_eq_zero, zero_mul, sub_zero]
  have h2ρ : 2*(2*k2+k3-1) = 0 := by
    have h1 : (2*(2*k2+k3-1)) * ((1 - 2*Z) * (∑ i ∈ Finset.range m, (2*Z)^i)) = 0 := by
      rw [← mul_assoc, hVkey, zero_mul]
    rwa [hgeom, mul_one] at h1
  -- ## Step 7: the entries of `F + 1`
  have hσ0 : 2*k2 + 2*k3*(1-k) = 0 := by rw [hσ, h2ρ]
  have h12 : (2*k2*(1-k)-1)*(2*k2 + 2*k3*(1-k)) = 0 := by rw [hσ0, mul_zero]
  have h22 : 2*(2*k2+k3-1)*(2*k2+2*k3-1) - 1 = -1 := by
    rw [show 2*(2*k2+k3-1)*(2*k2+2*k3-1) = (2*(2*k2+k3-1))*(2*k2+2*k3-1) by ring,
      h2ρ, zero_mul, zero_sub]
  -- ## Step 8: the vector `x`
  refine ⟨![1 - (1-k)*(1+k2) - k3*(1-k)^2, 0, 1], ?_⟩
  rw [hF, h12, h22, hσ0]
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Pi.single_eq_same,
      Pi.single_eq_of_ne] <;>
    ring

end Work.Hering.HardCore
