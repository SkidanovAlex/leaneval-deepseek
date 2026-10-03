import Mathlib
import Submission.Work.FIArea2.TsumDefs
import Submission.Work.FIArea2.Tsum_odd_defs
import Submission.Work.FIArea2.Tsum_eq_uvSum
import Submission.Work.FIArea2.uvSum_eq_ramSum
import Submission.Work.FIArea2.ramSum_bound
import Submission.Work.FIArea2.Tsum_nonsquare_bound
import Submission.Work.FIArea2.exists_sqrt_data

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- **The odd-prime case of the local estimate of *FI* Lemma 8.1.**  For `p` an odd prime, `ν ≥ 1`,
`a` a unit modulo `p^ν` and all `h₁, h₂ : ℤ`,

  `‖T(p^ν, a, h₁, h₂)‖ ≤ (ν+1)³ · (p^ν, h₁² - a h₂²)`.

Route (brute-force verified for all odd `p^ν ≤ 3^5` and all units `a`, `h₁,h₂` modulo `p^ν`):

* If `a` is a **square** modulo `p` (equivalently modulo `p^ν`, by Hensel — see
  `Work.FIArea2.henselSqDvdAux`, `Work.FIArea2.sqRoots_card`), pick `ρ` with `ρ² ≡ a (mod p^ν)`
  and put `α = (h₂ - h₁ρ⁻¹)/2`, `β = (h₂ + h₁ρ⁻¹)/2` in `ZMod (p^ν)` (`2` and `ρ` are units).
  Since `y²-ax² = (y-ρx)(y+ρx)`, the map `(x,y) ↦ (u,v) = (y-ρx, y+ρx)` is a bijection from the
  solution set onto `{(u,v) : uv = 0}`, and `xh₁+yh₂ = uα + vβ`; so `T` becomes the sum of
  `E((uα+vβ)/p^ν)` over `uv = 0`.  Decomposing `uv = 0` by the `p`-adic order of `u` and of `v`
  (each element of `ZMod (p^ν)` is `0` or `p^i` times a unit modulo `p^{ν-i}`) splits this sum as
  `T = ∑_{k+l ≤ ν} R(α;p^k)·R(β;p^l)`, where `R(·;b)` is the Ramanujan sum (`Work.FIArea2.ram`),
  because the terms with `u` of order `i` insert the Ramanujan sums `R(α;p^{ν-i})`.

  Evaluating with the exact prime-power values `R(c;p^m) = p^m[p^m|c] - p^{m-1}[p^{m-1}|c]`
  (`Work.FIArea2.ramanujan_primepow`), and writing `s`, `t` for the `p`-adic valuations of `α`, `β`
  capped at `ν` (`s = ν` when `α = 0` in `ZMod (p^ν)`, etc.), gives **exactly**
  `T = 0` if `s+t ≤ ν-2`, `T = -p^{ν-1}` if `s+t = ν-1`, and
  `T = p^{ν-1}((s+t+1-ν)(p-1) - 1)` if `s+t ≥ ν`; since `αβ = -(h₁²-ah₂²)/(4a)` and `4a` is a
  unit, `min(ν, s+t) = min(ν, (h₁²-ah₂², p^ν))`, so in every case
  `|T| ≤ (ν+1)³ (h₁²-ah₂², p^ν)`.  (In particular `T` is *not* always `0` when the valuation is
  `< ν`: `p = 3, ν = 2, a = 1, h₁ = 1, h₂ = 2` gives `T = -3`, where the valuation is `1 = ν-1`.)
* If `a` is a **non-square** modulo `p`, every solution has `p^{⌈ν/2⌉} | x` and `p^{⌈ν/2⌉} | y`
  (if `p ∤ x` then `y/x` would be a square root of `a` mod `p`), so
  `T = p^{2⌊ν/2⌋}·[p^{⌊ν/2⌋}|h₁]·[p^{⌊ν/2⌋}|h₂]`, and the bound follows because
  `p^{⌊ν/2⌋} | h₁, h₂` implies `2⌊ν/2⌋ ≤ (h₁²-ah₂², p^ν)`. -/
theorem Tsum_prime_pow_odd (p : ℕ) (hp : p.Prime) (hodd : Odd p) (ν : ℕ) (hν : 1 ≤ ν)
    [NeZero (p ^ ν)] (a h1 h2 : ℤ) (ha : IsUnit (a : ZMod (p ^ ν))) :
    ‖Tsum (p ^ ν) a h1 h2‖
      ≤ ((ν : ℝ) + 1) ^ 3 * (Nat.gcd (p ^ ν) ((h1 ^ 2 - a * h2 ^ 2).natAbs) : ℝ) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- `p ∤ 4a`  (in particular `p ∤ a`)
  have hp_a : ¬ (p : ℤ) ∣ a := by
    have hcop : IsCoprime ((p : ℤ) ^ ν) a := by
      have h := (ZMod.coe_int_isUnit_iff_isCoprime a (p ^ ν)).mp ha
      simpa using h
    have hnat : Nat.Coprime (p ^ ν) a.natAbs := by
      have h := (Int.isCoprime_iff_nat_coprime).mp hcop
      simpa using h
    intro hd
    have hdvd : p ∣ a.natAbs := by
      have h := (Int.natAbs_dvd_natAbs (a := (p : ℤ)) (b := a)).mpr hd
      simpa using h
    have h1 : p ∣ Nat.gcd (p ^ ν) a.natAbs :=
      Nat.dvd_gcd (dvd_pow_self p (by omega)) hdvd
    rw [hnat] at h1
    have h2 : p ≤ 1 := Nat.le_of_dvd (by norm_num) h1
    have h3 : 2 ≤ p := hp.two_le
    omega
  -- `2` is a unit modulo `p^ν` (as `p` is odd)
  have h2u : IsUnit (2 : ZMod (p ^ ν)) := by
    refine (ZMod.isUnit_natCast_iff_not_dvd_pow hp hν).mpr ?_
    intro hd
    have hp1 : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    have hp2 : 2 ≤ p := hp.two_le
    have hp3 : p = 2 := by omega
    rw [hp3] at hodd
    exact (by decide : ¬ Odd 2) hodd
  by_cases hsq : IsSquare ((a : ZMod p))
  · -- **the square case**: substitute `(x,y) ↦ (y - ρx, y + ρx)` and decompose by `p`-adic order
    obtain ⟨ρ, ρ', α, β, hρ, hρ', hα, hβ, hrel⟩ :=
      exists_sqrt_data hp hodd hν a h1 h2 ha hsq
    have hT1 := Tsum_eq_uvSum hp hν a h1 h2 ρ ρ' α β ha h2u hρ hρ' hα hβ
    have hT2 := uvSum_eq_ramSum (p := p) (ν := ν) hp hν α β
    rw [hT1, hT2]
    -- the relation `4aαβ = -(h₁² - a h₂²)` in the form required by `ramSum_bound`
    have hrel' : (4 : ZMod (p ^ ν)) * (a : ZMod (p ^ ν)) * α * β
        = ((-(h1 ^ 2 - a * h2 ^ 2) : ℤ) : ZMod (p ^ ν)) := by
      rw [hrel]
      push_cast
      ring
    have hbound := ramSum_bound hp hν a hp_a α β (-(h1 ^ 2 - a * h2 ^ 2)) hrel'
    rw [Int.natAbs_neg] at hbound
    refine le_trans ?_ hbound
    -- bound the norm of the Ramanujan sum by the sum of the norms of its terms
    refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
    by_cases hk : p ^ (ν - k) ∣ α.val <;> simp [hk]
  · -- **the non-square case**
    exact Tsum_nonsquare_bound hp hodd hν a h1 h2 ha hsq

end

end Work.FIArea2
