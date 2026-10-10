import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5

open Polynomial

/-- In a field of characteristic `5`, `0 < n < 5` forces `((n : ℕ) : 𝕜) ≠ 0`. -/
private lemma natCast_ne_zero_of_lt {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] {n : ℕ} (h0 : 0 < n)
    (h5 : n < 5) : ((n : ℕ) : 𝕜) ≠ 0 := by
  intro h
  have hdvd := (CharP.cast_eq_zero_iff 𝕜 5 n).mp h
  have hle := Nat.le_of_dvd h0 hdvd
  omega

/-- `G = (X³ + X) - m·((cX + d)³ + (cX + d))` in `𝕜[X]`, char `5`, `c ≠ 0`, `m ∈ {2,3,-2,-3}`.

Route (pure polynomial algebra).  Expanding,
`G = (1 - m*c^3) * X^3 + (-(3*m*c^2*d)) * X^2 + (1 - 3*m*c*d^2 - m*c) * X + (-(m*d^3 + m*d))`,
from which `G.natDegree ≤ 3`.  If `G.natDegree = 0` then all three coefficients of `X^3`, `X^2`,
`X` vanish, so `m*c^3 = 1`, `3*m*c^2*d = 0`, `m*c*(3*d^2 + 1) = 1`.  Since `3 ≠ 0`, `m ≠ 0`
(`m ∈ {2,3,-2,-3}` in char `5`) and `c ≠ 0`, the second gives `d = 0`, so `c^2 = 3*d^2 + 1 = 1`
and `m*c = m*c^3 = 1`; dividing gives `m^2 = 1`.  But `m = ±2` gives `m^2 = 4 ≠ 1` and `m = ±3`
gives `m^2 = 9 = 4 ≠ 1` in char `5`, a contradiction.  (To get `m ≠ 1` from `m^2 = 1`:
`c^2 = 1` gives `c = 1 ∨ c = -1`, and `m*c = 1` gives `m = ±1`, contradicting `m^2 ≠ 1`.)

Useful arithmetic facts in `CharP 𝕜 5`: `(2:𝕜) ≠ 0`, `(3:𝕜) ≠ 0`,
`((3:ℕ):𝕜) = (2:𝕜) + 1`, `((4:ℕ):𝕜) = (3:𝕜) + 1`, and from
`CharP.cast_eq_zero_iff 𝕜 5 n : ((n:ℕ):𝕜) = 0 ↔ 5 ∣ n` one gets `(2:𝕜) ≠ 1`, `(3:𝕜) ≠ 1`,
`(2:𝕜) ≠ -1`, `(3:𝕜) ≠ -1` (e.g. from `h : (2:𝕜) = 1` deduce `(1:𝕜) = 0` via
`(2:𝕜) - 1 = 1` and `CharP.cast_eq_zero_iff 𝕜 5 1`).  Proving the expansion: `ring`-normalize
`(C c * X + C d)^3` first (with `C c`, `C d`, `X` as atoms) and then rewrite with `map_add`,
`map_mul`, `map_pow`, `Polynomial.C_pow`-style lemmas, or prove
`p^3 + p = (C c)^3 * X^3 + 3*(C c)^2*(C d) * X^2 + ...` by `ring` and go on from there. -/
theorem asG_natDegree {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (m c d : 𝕜) (hc : c ≠ 0)
    (hm : m = 2 ∨ m = 3 ∨ m = -2 ∨ m = -3) :
    let G : Polynomial 𝕜 := (Polynomial.X ^ 3 + Polynomial.X) -
      Polynomial.C m * ((Polynomial.C c * Polynomial.X + Polynomial.C d) ^ 3
        + (Polynomial.C c * Polynomial.X + Polynomial.C d))
    G.natDegree = 1 ∨ G.natDegree = 2 ∨ G.natDegree = 3 := by
  -- arithmetic facts in characteristic `5`
  have h2 : (2 : 𝕜) ≠ 0 := natCast_ne_zero_of_lt (n := 2) (by norm_num) (by norm_num)
  have h3 : (3 : 𝕜) ≠ 0 := natCast_ne_zero_of_lt (n := 3) (by norm_num) (by norm_num)
  have h4nz : (4 : 𝕜) ≠ 0 := natCast_ne_zero_of_lt (n := 4) (by norm_num) (by norm_num)
  have h22 : (2 : 𝕜) ^ 2 ≠ 1 := by
    intro hh
    apply h3
    rw [← (by ring : (2 : 𝕜) ^ 2 - 1 = (3 : 𝕜)), hh, sub_self]
  have h33 : (3 : 𝕜) ^ 2 ≠ 1 := by
    intro hh
    have hprod : (2 : 𝕜) * (4 : 𝕜) = 0 := by
      rw [← (by ring : (3 : 𝕜) ^ 2 - 1 = (2 : 𝕜) * (4 : 𝕜)), hh, sub_self]
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd h h2
    · exact absurd h h4nz
  have hm0 : m ≠ 0 := by
    rcases hm with h | h | h | h <;> rw [h]
    · exact h2
    · exact h3
    · exact neg_ne_zero.mpr h2
    · exact neg_ne_zero.mpr h3
  have hm2 : m ^ 2 ≠ 1 := by
    rcases hm with h | h | h | h
    · rw [h]; exact h22
    · rw [h]; exact h33
    · rw [h]; rw [show (-2 : 𝕜) ^ 2 = (2 : 𝕜) ^ 2 by ring]; exact h22
    · rw [h]; rw [show (-3 : 𝕜) ^ 2 = (3 : 𝕜) ^ 2 by ring]; exact h33
  let E : Polynomial 𝕜 := (Polynomial.X ^ 3 + Polynomial.X) -
      Polynomial.C m * ((Polynomial.C c * Polynomial.X + Polynomial.C d) ^ 3
        + (Polynomial.C c * Polynomial.X + Polynomial.C d))
  change E.natDegree = 1 ∨ E.natDegree = 2 ∨ E.natDegree = 3
  have hEE : E = (Polynomial.X ^ 3 + Polynomial.X) -
      Polynomial.C m * ((Polynomial.C c * Polynomial.X + Polynomial.C d) ^ 3
        + (Polynomial.C c * Polynomial.X + Polynomial.C d)) := rfl
  -- the expansion, first in "atom" form with `C m`, `C c`, `C d` as atoms,
  have hbase : ((Polynomial.X ^ 3 + Polynomial.X) -
        Polynomial.C m * ((Polynomial.C c * Polynomial.X + Polynomial.C d) ^ 3
          + (Polynomial.C c * Polynomial.X + Polynomial.C d)) : Polynomial 𝕜)
      = (1 - Polynomial.C m * (Polynomial.C c) ^ 3) * Polynomial.X ^ 3
        - (3 * Polynomial.C m * (Polynomial.C c) ^ 2 * Polynomial.C d) * Polynomial.X ^ 2
        + (1 - Polynomial.C m * (3 * (Polynomial.C c) * (Polynomial.C d) ^ 2 + Polynomial.C c))
            * Polynomial.X
        - Polynomial.C m * ((Polynomial.C d) ^ 3 + Polynomial.C d) := by
    first | refl_ring1 | ring
  -- and then in explicit scalar form.
  have hCform : (Polynomial.C (1 - m * c ^ 3) * Polynomial.X ^ 3
        + Polynomial.C (-(3 * m * c ^ 2 * d)) * Polynomial.X ^ 2
        + Polynomial.C (1 - 3 * m * c * d ^ 2 - m * c) * Polynomial.X
        + Polynomial.C (-(m * d ^ 3 + m * d)) : Polynomial 𝕜)
      = (1 - Polynomial.C m * (Polynomial.C c) ^ 3) * Polynomial.X ^ 3
        - (3 * Polynomial.C m * (Polynomial.C c) ^ 2 * Polynomial.C d) * Polynomial.X ^ 2
        + (1 - Polynomial.C m * (3 * (Polynomial.C c) * (Polynomial.C d) ^ 2 + Polynomial.C c))
            * Polynomial.X
        - Polynomial.C m * ((Polynomial.C d) ^ 3 + Polynomial.C d) := by
    simp only [map_sub, map_mul, map_pow, map_neg, map_add, map_one, map_ofNat]
    first | refl_ring1 | ring
  have hexp : E = Polynomial.C (1 - m * c ^ 3) * Polynomial.X ^ 3
        + Polynomial.C (-(3 * m * c ^ 2 * d)) * Polynomial.X ^ 2
        + Polynomial.C (1 - 3 * m * c * d ^ 2 - m * c) * Polynomial.X
        + Polynomial.C (-(m * d ^ 3 + m * d)) := by
    rw [hEE, hbase, ← hCform]
  have hcoeff3 : E.coeff 3 = 1 - m * c ^ 3 := by
    rw [hexp]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C]
    norm_num
  have hcoeff2 : E.coeff 2 = -(3 * m * c ^ 2 * d) := by
    rw [hexp]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C]
    norm_num
  have hcoeff1 : E.coeff 1 = 1 - 3 * m * c * d ^ 2 - m * c := by
    rw [hexp]
    simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C_mul_X,
      Polynomial.coeff_C]
    norm_num
  have hdeg : E.natDegree ≤ 3 := by
    rw [hexp]
    compute_degree
  -- `E` is not a constant
  have hne : E.natDegree ≠ 0 := by
    intro h0
    have h1 : 1 - m * c ^ 3 = 0 := by
      have := Polynomial.coeff_eq_zero_of_natDegree_lt (p := E) (n := 3) (by rw [h0]; norm_num)
      rwa [hcoeff3] at this
    have h2' : -(3 * m * c ^ 2 * d) = 0 := by
      have := Polynomial.coeff_eq_zero_of_natDegree_lt (p := E) (n := 2) (by rw [h0]; norm_num)
      rwa [hcoeff2] at this
    have h1' : 1 - 3 * m * c * d ^ 2 - m * c = 0 := by
      have := Polynomial.coeff_eq_zero_of_natDegree_lt (p := E) (n := 1) (by rw [h0]; norm_num)
      rwa [hcoeff1] at this
    have hmc3 : m * c ^ 3 = 1 := (sub_eq_zero.mp h1).symm
    have hd0 : d = 0 := by
      have hb : 3 * m * c ^ 2 * d = 0 := neg_eq_zero.mp h2'
      rcases mul_eq_zero.mp hb with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · exact absurd h h3
          · exact absurd h hm0
        · exact absurd h (pow_ne_zero 2 hc)
      · exact h
    have hmc : m * c = 1 := by
      rw [hd0] at h1'
      have hh : 1 - m * c = 0 := by simpa using h1'
      exact (sub_eq_zero.mp hh).symm
    have hc2 : c ^ 2 = 1 := by
      have hmul : m * c * (c ^ 2 - 1) = 0 := by
        have hz : m * c ^ 3 - m * c = 0 := by rw [hmc3, hmc, sub_self]
        have heq : m * c ^ 3 - m * c = m * c * (c ^ 2 - 1) := by ring
        rw [← heq]
        exact hz
      have hmcne : m * c ≠ 0 := by rw [hmc]; exact one_ne_zero
      rcases mul_eq_zero.mp hmul with h | h
      · exact absurd h hmcne
      · exact sub_eq_zero.mp h
    have hm2eq : m ^ 2 = 1 := by
      have h1 : (m * c) ^ 2 = 1 := by rw [hmc]; norm_num
      have h2 : m ^ 2 * c ^ 2 = (m * c) ^ 2 := by ring
      calc m ^ 2 = m ^ 2 * c ^ 2 := by rw [hc2, mul_one]
        _ = (m * c) ^ 2 := h2
        _ = 1 := h1
    exact hm2 hm2eq
  omega

end Work.MotV5
