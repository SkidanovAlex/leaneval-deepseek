import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Q8

/-- For three pairwise distinct indices `a b c` of `Fin 3` the total sum is the sum of the three
terms (in any order). -/
lemma step7a_sum_univ_three {M : Type*} [AddCommMonoid M] (f : Fin 3 → M)
    {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∑ i, f i = f a + f b + f c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp_all [Fin.sum_univ_three] <;> abel

/-- The purely numerical (scalar) core of step (7)(a): three complex numbers tied by the sign `e`
(`e p = e q`), a nonzero divisibility variable `x`, and the equation system
`1 + ∑ eᵢxᵢ = 0`, `∑ eᵢzᵢ = 0`, `∑ eᵢzᵢ²/xᵢ = 0` (with `z p ≠ 0`) are contradictory. -/
lemma step7a_scalar_core {ep eq ek Xp Xq Xk Zp Zq Zk : ℂ}
    (hep : ep = eq) (hxp : Xp = Xq) (hzp : Zp = Zq)
    (hEp : ep * ep = 1) (hEk : ek * ek = 1)
    (hXp : Xp ≠ 0) (_hXq : Xq ≠ 0) (hXk : Xk ≠ 0)
    (hZp : Zp ≠ 0)
    (s1 : 1 + (ep * Xp + eq * Xq + ek * Xk) = 0)
    (s2 : ep * Zp + eq * Zq + ek * Zk = 0)
    (s3 : ep * Zp^2 / Xp + eq * Zq^2 / Xq + ek * Zk^2 / Xk = 0) : False := by
  simp only [← hep, ← hxp, ← hzp] at s1 s2 s3
  -- `h2` forces `e k z k = -2 e p z p`
  have hzk : ek * Zk = -2 * (ep * Zp) := by linear_combination s2
  -- squaring and using `eᵢ² = 1` yields `z k ^ 2 = 4 z p ^ 2`
  have hzksq : Zk^2 = 4 * Zp^2 := by
    linear_combination (ek*Zk - 2*ep*Zp)*hzk - Zk^2*hEk + 4*Zp^2*hEp
  have hZpnz : Zp^2 ≠ 0 := pow_ne_zero 2 hZp
  -- substituting into `h3` kills the `e k z k ^ 2 / x k` term
  have s3b : 2*ep*Zp^2/Xp + 4*ek*Zp^2/Xk = 0 := by
    linear_combination s3 - (ek/Xk)*hzksq
  -- cancel the now common factor `z p ^ 2 ≠ 0`
  have s3c : 2*ep/Xp + 4*ek/Xk = 0 := by
    have h : Zp^2 * (2*ep/Xp + 4*ek/Xk) = 0 := by linear_combination s3b
    exact (mul_eq_zero.mp h).resolve_left hZpnz
  -- clear denominators: `2 e p x k + 4 e k x p = 0`
  have hpoly : 2*ep*Xk + 4*ek*Xp = 0 := by
    have h1 : Xp * Xk * (2*ep/Xp + 4*ek/Xk) = 0 := by rw [s3c, mul_zero]
    have hexp : Xp * Xk * (2*ep/Xp + 4*ek/Xk) = 2*ep*Xk + 4*ek*Xp := by field_simp
    rwa [hexp] at h1
  have hkey1 : ep*Xk = -2*ek*Xp := by linear_combination (1/2)*hpoly
  -- multiply by `e k` and use `e k ^ 2 = 1` and `e p ^ 2 = 1`
  have hkey : ek*Xk = -2*ep*Xp := by
    linear_combination (ep*ek)*hkey1 - (2*ep*Xp)*hEk - (ek*Xk)*hEp
  -- `h1` then reads `1 = 0`
  have h10 : (1:ℂ) = 0 := by linear_combination s1 - hkey
  exact one_ne_zero h10

/-- The numerical contradiction in step (7)(a) of Glauberman's `Q₈` argument: if two of the
three indices `p ≠ q` carry the same sign `e`, the same `x`, and the same `z`, then the three
equations `1 + ∑ eᵢxᵢ = 0`, `∑ eᵢzᵢ = 0`, `∑ eᵢzᵢ²/xᵢ = 0` together with `Re zᵢ > 0` and
`xᵢ ≠ 0` are contradictory.

Proof sketch: `h2` gives `e k z k = -2 e p z p` for the third index `k`, whence `z k ^ 2 = 4 z p ^ 2`;
`h3` then gives `2 e p / x p + 4 e k / x k = 0` after cancelling `z p ^ 2 ≠ 0` and `2 e p / x p`
multiplied by `e k` gives `e k x k = -2 e p x p`; finally `h1` reads `1 + 2 e p x p + e k x k = 0`. -/
theorem step7a_numeric {e x z : Fin 3 → ℂ} (he : ∀ i, e i = 1 ∨ e i = -1)
    (hx : ∀ i, x i ≠ 0) (hz : ∀ i, 0 < (z i).re)
    (h1 : 1 + ∑ i, e i * x i = 0)
    (h2 : ∑ i, e i * z i = 0)
    (h3 : ∑ i, e i * z i ^ 2 / x i = 0)
    {p q : Fin 3} (hpq : p ≠ q) (hep : e p = e q) (hxp : x p = x q)
    (hzp : z p = z q) : False := by
  -- the third index, distinct from both `p` and `q`
  obtain ⟨k, hkp, hkq⟩ : ∃ k : Fin 3, k ≠ p ∧ k ≠ q := by
    fin_cases p <;> fin_cases q <;> simp_all <;> decide
  -- split each of the three sums into its `p`, `q`, `k` terms
  rw [step7a_sum_univ_three (fun i => e i * x i) hpq hkp.symm hkq.symm] at h1
  rw [step7a_sum_univ_three (fun i => e i * z i) hpq hkp.symm hkq.symm] at h2
  rw [step7a_sum_univ_three (fun i => e i * z i ^ 2 / x i) hpq hkp.symm hkq.symm] at h3
  have hEp : e p * e p = 1 := by rcases he p with hh | hh <;> rw [hh] <;> ring
  have hEk : e k * e k = 1 := by rcases he k with hh | hh <;> rw [hh] <;> ring
  have hZp : z p ≠ 0 := by intro hz0; have := hz p; rw [hz0] at this; simp at this
  exact step7a_scalar_core hep hxp hzp hEp hEk (hx p) (hx q) (hx k) hZp h1 h2 h3

end Work.BrauerSuzuki.Q8
