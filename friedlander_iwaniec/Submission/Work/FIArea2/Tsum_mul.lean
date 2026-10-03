import Mathlib
import Submission.Work.FIArea2.TsumDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

open Finset
open scoped BigOperators

/-!
# CRT multiplicativity of the reduced sum `T` (FI (8.2))

This file proves `Tsum_mul`, the multiplicativity of the reduced sum `T(n,a,h₁,h₂)` under
the Chinese remainder theorem.  The proof reindexes the double sum over `ZMod (m*n)` by the
CRT ring equivalence `ZMod (m*n) ≃+* ZMod m × ZMod n`, observes that the solution condition
`y² ≡ a x²` holds iff it holds componentwise, and factors the additive character
`e((xh₁+yh₂)/(mn))` as `e(x₁c₁h₁/m)·e(x₂c₂h₂/n)` using `c₁n ≡ 1 (mod m)`, `c₂m ≡ 1 (mod n)`.
-/

/-- First component of the Chinese remainder isomorphism: reduction modulo `m`. -/
lemma crt_fst {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m*n)] (h : Nat.Coprime m n)
    (x : ZMod (m*n)) : (ZMod.chineseRemainder h x).1 = (ZMod.cast x : ZMod m) := by
  unfold ZMod.chineseRemainder; simp

/-- Second component of the Chinese remainder isomorphism: reduction modulo `n`. -/
lemma crt_snd {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m*n)] (h : Nat.Coprime m n)
    (x : ZMod (m*n)) : (ZMod.chineseRemainder h x).2 = (ZMod.cast x : ZMod n) := by
  unfold ZMod.chineseRemainder; simp

/-- The CRT inverse of a pair reduces to the pair's first component modulo `m`. -/
lemma cast_symm_fst {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m*n)] (h : Nat.Coprime m n)
    (p : ZMod m × ZMod n) :
    (ZMod.cast ((ZMod.chineseRemainder h).symm p) : ZMod m) = p.1 := by
  rw [← crt_fst h _, RingEquiv.apply_symm_apply]

/-- The CRT inverse of a pair reduces to the pair's second component modulo `n`. -/
lemma cast_symm_snd {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m*n)] (h : Nat.Coprime m n)
    (p : ZMod m × ZMod n) :
    (ZMod.cast ((ZMod.chineseRemainder h).symm p) : ZMod n) = p.2 := by
  rw [← crt_snd h _, RingEquiv.apply_symm_apply]

/-- **The basic CRT congruence.**  For `x : ZMod (m*n)`, coprime `m, n`, and integers `c₁, c₂`
with `c₁ n ≡ 1 (mod m)`, `c₂ m ≡ 1 (mod n)`,

  `m*n ∣ x.val - n c₁ (x mod m).val - m c₂ (x mod n).val`.

Equivalently, `x.val/(mn) ≡ c₁ (x mod m).val/m + c₂ (x mod n).val/n (mod 1)`. -/
lemma dvd_Dx {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m*n)] (h : Nat.Coprime m n)
    (c1 c2 : ℤ) (hc1 : (c1 : ZMod m) * (n : ZMod m) = 1)
    (hc2 : (c2 : ZMod n) * (m : ZMod n) = 1) (x : ZMod (m*n)) :
    ((m*n : ℕ) : ℤ) ∣ (x.val : ℤ) - (n:ℤ)*c1*((ZMod.cast x : ZMod m).val : ℤ)
      - (m:ℤ)*c2*((ZMod.cast x : ZMod n).val : ℤ) := by
  have hA : (m:ℤ) ∣ (x.val : ℤ) - ((ZMod.cast x : ZMod m).val : ℤ) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub ((ZMod.cast x : ZMod m).val) (x.val) m]
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.cast_eq_val]
  have hB : (m:ℤ) ∣ (n:ℤ)*c1*((ZMod.cast x : ZMod m).val : ℤ) - ((ZMod.cast x : ZMod m).val : ℤ) := by
    have hc1' : ((c1 * n : ℤ) : ZMod m) = 1 := by push_cast; exact hc1
    have hB0 : (m:ℤ) ∣ 1 - c1*n := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub (c1*n) 1 m]; simpa using hc1'
    obtain ⟨q, hq⟩ := hB0
    exact ⟨-(q*((ZMod.cast x : ZMod m).val : ℤ)),
      by linear_combination (-((ZMod.cast x : ZMod m).val : ℤ)) * hq⟩
  have hC : (n:ℤ) ∣ (x.val : ℤ) - ((ZMod.cast x : ZMod n).val : ℤ) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub ((ZMod.cast x : ZMod n).val) (x.val) n]
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val, ZMod.cast_eq_val]
  have hD : (n:ℤ) ∣ (m:ℤ)*c2*((ZMod.cast x : ZMod n).val : ℤ) - ((ZMod.cast x : ZMod n).val : ℤ) := by
    have hc2' : ((c2 * m : ℤ) : ZMod n) = 1 := by push_cast; exact hc2
    have hD0 : (n:ℤ) ∣ 1 - c2*m := by
      rw [← ZMod.intCast_eq_intCast_iff_dvd_sub (c2*m) 1 n]; simpa using hc2'
    obtain ⟨q, hq⟩ := hD0
    exact ⟨-(q*((ZMod.cast x : ZMod n).val : ℤ)),
      by linear_combination (-((ZMod.cast x : ZMod n).val : ℤ)) * hq⟩
  have hm : (m:ℤ) ∣ (x.val : ℤ) - (n:ℤ)*c1*((ZMod.cast x : ZMod m).val : ℤ)
      - (m:ℤ)*c2*((ZMod.cast x : ZMod n).val : ℤ) := by
    obtain ⟨a, ha⟩ := hA; obtain ⟨b, hb⟩ := hB
    exact ⟨a - b - c2*((ZMod.cast x : ZMod n).val : ℤ), by linear_combination ha - hb⟩
  have hn : (n:ℤ) ∣ (x.val : ℤ) - (n:ℤ)*c1*((ZMod.cast x : ZMod m).val : ℤ)
      - (m:ℤ)*c2*((ZMod.cast x : ZMod n).val : ℤ) := by
    obtain ⟨a, ha⟩ := hC; obtain ⟨b, hb⟩ := hD
    exact ⟨a - b - c1*((ZMod.cast x : ZMod m).val : ℤ), by linear_combination ha - hb⟩
  have := (h.isCoprime).mul_dvd hm hn
  simpa [Nat.cast_mul] using this

/-- **Factorisation of the additive character.**  For `x : ZMod (m*n)` and coprime `m, n`,
`e(x.val h/(mn)) = e((x mod m).val (hc₁)/m) · e((x mod n).val (hc₂)/n)`. -/
lemma E_crt {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m*n)] (h : Nat.Coprime m n)
    (c1 c2 : ℤ) (hc1 : (c1 : ZMod m) * (n : ZMod m) = 1)
    (hc2 : (c2 : ZMod n) * (m : ZMod n) = 1) (h1 : ℤ) (x : ZMod (m*n)) :
    E ((((x.val : ℤ) * h1 : ℤ) : ℝ) / ((m*n : ℕ) : ℝ))
      = E (((((ZMod.cast x : ZMod m).val : ℤ) * (h1*c1) : ℤ) : ℝ) / ((m:ℕ):ℝ))
        * E (((((ZMod.cast x : ZMod n).val : ℤ) * (h1*c2) : ℤ) : ℝ) / ((n:ℕ):ℝ)) := by
  obtain ⟨k, hk⟩ := dvd_Dx h c1 c2 hc1 hc2 x
  have hm0 : ((m:ℕ):ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne m)
  have hn0 : ((n:ℕ):ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne n)
  have hmn0 : ((m*n:ℕ):ℝ) ≠ 0 := by rw [Nat.cast_mul]; exact mul_ne_zero hm0 hn0
  set U : ℝ := (((x.val : ℤ) * h1 : ℤ) : ℝ) / ((m*n : ℕ) : ℝ) with hU
  set V1 : ℝ := (((((ZMod.cast x : ZMod m).val : ℤ) * (h1*c1) : ℤ) : ℝ) / ((m:ℕ):ℝ)) with hV1
  set V2 : ℝ := (((((ZMod.cast x : ZMod n).val : ℤ) * (h1*c2) : ℤ) : ℝ) / ((n:ℕ):ℝ)) with hV2
  change E U = E V1 * E V2
  rw [← E_add]
  have key : U - (V1 + V2) = ((k*h1 : ℤ) : ℝ) := by
    rw [hU, hV1, hV2]
    rw [show (((x.val : ℤ) * h1 : ℤ) : ℝ) / ((m*n : ℕ) : ℝ)
        - (((((ZMod.cast x : ZMod m).val : ℤ) * (h1*c1) : ℤ) : ℝ) / ((m:ℕ):ℝ)
           + ((((ZMod.cast x : ZMod n).val : ℤ) * (h1*c2) : ℤ) : ℝ) / ((n:ℕ):ℝ))
       = ((h1*((x.val:ℤ) - (n:ℤ)*c1*((ZMod.cast x : ZMod m).val:ℤ)
            - (m:ℤ)*c2*((ZMod.cast x : ZMod n).val:ℤ)) : ℤ) : ℝ) / ((m*n:ℕ):ℝ) from by
        field_simp; push_cast; ring]
    rw [hk]
    push_cast
    field_simp
  rw [← sub_add_cancel U (V1+V2), E_add, key, E_int (k*h1), one_mul]

/-- **Componentwise character factorisation in CRT coordinates.**  With `p, q : ZMod m × ZMod n`
corresponding to `x = e⁻¹ p`, `y = e⁻¹ q`, the character `e((x.val h₁ + y.val h₂)/(mn))` factors
into its `m`-part and `n`-part, the moduli scaling by `c₁` and `c₂` respectively. -/
lemma E_split {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m*n)] (hmn : Nat.Coprime m n)
    (c1 c2 : ℤ) (hc1 : (c1 : ZMod m) * (n : ZMod m) = 1)
    (hc2 : (c2 : ZMod n) * (m : ZMod n) = 1) (h1 h2 : ℤ) (p q : ZMod m × ZMod n) :
    E ((((((ZMod.chineseRemainder hmn).symm p).val : ℤ) * h1
          + (((ZMod.chineseRemainder hmn).symm q).val : ℤ) * h2 : ℤ) : ℝ) / ((m*n : ℕ) : ℝ))
      = E ((((p.1.val : ℤ) * (h1*c1) + (q.1.val : ℤ) * (h2*c1) : ℤ) : ℝ) / ((m:ℕ):ℝ))
        * E ((((p.2.val : ℤ) * (h1*c2) + (q.2.val : ℤ) * (h2*c2) : ℤ) : ℝ) / ((n:ℕ):ℝ)) := by
  set x := (ZMod.chineseRemainder hmn).symm p with hx
  set y := (ZMod.chineseRemainder hmn).symm q with hy
  have hx1 : (ZMod.cast x : ZMod m) = p.1 := by rw [hx, cast_symm_fst]
  have hx2 : (ZMod.cast x : ZMod n) = p.2 := by rw [hx, cast_symm_snd]
  have hy1 : (ZMod.cast y : ZMod m) = q.1 := by rw [hy, cast_symm_fst]
  have hy2 : (ZMod.cast y : ZMod n) = q.2 := by rw [hy, cast_symm_snd]
  have hEcx := E_crt hmn c1 c2 hc1 hc2 h1 x
  have hEcy := E_crt hmn c1 c2 hc1 hc2 h2 y
  rw [hx1, hx2] at hEcx
  rw [hy1, hy2] at hEcy
  have hu : ((((x.val : ℤ) * h1 + (y.val : ℤ) * h2 : ℤ) : ℝ) / ((m*n : ℕ) : ℝ))
      = ((((x.val : ℤ) * h1 : ℤ) : ℝ) / ((m*n : ℕ) : ℝ))
        + ((((y.val : ℤ) * h2 : ℤ) : ℝ) / ((m*n : ℕ) : ℝ)) := by push_cast; ring
  rw [hu, E_add, hEcx, hEcy]
  rw [show ((((p.1.val : ℤ) * (h1*c1) + (q.1.val : ℤ) * (h2*c1) : ℤ) : ℝ) / ((m:ℕ):ℝ))
        = ((((p.1.val : ℤ) * (h1*c1) : ℤ) : ℝ) / ((m:ℕ):ℝ))
          + ((((q.1.val : ℤ) * (h2*c1) : ℤ) : ℝ) / ((m:ℕ):ℝ)) from by push_cast; ring,
      E_add,
      show ((((p.2.val : ℤ) * (h1*c2) + (q.2.val : ℤ) * (h2*c2) : ℤ) : ℝ) / ((n:ℕ):ℝ))
        = ((((p.2.val : ℤ) * (h1*c2) : ℤ) : ℝ) / ((n:ℕ):ℝ))
          + ((((q.2.val : ℤ) * (h2*c2) : ℤ) : ℝ) / ((n:ℕ):ℝ)) from by push_cast; ring,
      E_add]
  ring

/-- **Equivalence of the solution conditions under CRT.**  `y² ≡ a x² (mod mn)` holds iff it
holds modulo `m` and modulo `n`. -/
lemma cond_crt {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m*n)] (h : Nat.Coprime m n)
    (a : ℤ) (p q : ZMod m × ZMod n) :
    ((ZMod.chineseRemainder h).symm q)^2 = (a : ZMod (m*n)) * ((ZMod.chineseRemainder h).symm p)^2
      ↔ q.1^2 = (a:ZMod m)*p.1^2 ∧ q.2^2 = (a:ZMod n)*p.2^2 := by
  rw [show ((ZMod.chineseRemainder h).symm q)^2 = (a : ZMod (m*n)) * ((ZMod.chineseRemainder h).symm p)^2
        ↔ (ZMod.chineseRemainder h) (((ZMod.chineseRemainder h).symm q)^2)
            = (ZMod.chineseRemainder h) ((a : ZMod (m*n)) * ((ZMod.chineseRemainder h).symm p)^2)
      from (ZMod.chineseRemainder h).injective.eq_iff.symm]
  simp only [map_pow, map_mul, map_intCast, RingEquiv.apply_symm_apply]
  rw [Prod.ext_iff]
  simp

/-- **The CRT-transported summand is a product.**  Combining the componentwise condition and
the factorisation of the character, the summand of `T(mn,a,h₁,h₂)` in CRT coordinates is the
product of the `m`-summand (with parameters `h₁c₁, h₂c₁`) and the `n`-summand (with `h₁c₂, h₂c₂`). -/
lemma summand_crt {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m*n)] (hmn : Nat.Coprime m n)
    (c1 c2 : ℤ) (hc1 : (c1 : ZMod m) * (n : ZMod m) = 1)
    (hc2 : (c2 : ZMod n) * (m : ZMod n) = 1) (a h1 h2 : ℤ) (p q : ZMod m × ZMod n) :
    (if ((ZMod.chineseRemainder hmn).symm q)^2 = (a : ZMod (m*n)) * ((ZMod.chineseRemainder hmn).symm p)^2
       then E ((((((ZMod.chineseRemainder hmn).symm p).val : ℤ) * h1
                 + (((ZMod.chineseRemainder hmn).symm q).val : ℤ) * h2 : ℤ) : ℝ) / ((m*n : ℕ) : ℝ))
       else 0)
    = (if q.1^2 = (a:ZMod m)*p.1^2
        then E ((((p.1.val : ℤ)*(h1*c1) + (q.1.val : ℤ)*(h2*c1) : ℤ) : ℝ) / ((m:ℕ):ℝ)) else 0)
      * (if q.2^2 = (a:ZMod n)*p.2^2
        then E ((((p.2.val : ℤ)*(h1*c2) + (q.2.val : ℤ)*(h2*c2) : ℤ) : ℝ) / ((n:ℕ):ℝ)) else 0) := by
  by_cases hcond : q.1^2 = (a:ZMod m)*p.1^2 ∧ q.2^2 = (a:ZMod n)*p.2^2
  · have hc : ((ZMod.chineseRemainder hmn).symm q)^2
        = (a : ZMod (m*n)) * ((ZMod.chineseRemainder hmn).symm p)^2 :=
      (cond_crt hmn a p q).mpr hcond
    rw [if_pos hc, if_pos hcond.1, if_pos hcond.2]
    exact E_split hmn c1 c2 hc1 hc2 h1 h2 p q
  · have hc : ¬ (((ZMod.chineseRemainder hmn).symm q)^2
        = (a : ZMod (m*n)) * ((ZMod.chineseRemainder hmn).symm p)^2) :=
      fun hh => hcond ((cond_crt hmn a p q).mp hh)
    rw [if_neg hc]
    rcases not_and_or.mp hcond with hh | hh
    · rw [if_neg hh, zero_mul]
    · rw [if_neg hh, mul_zero]

/-- **Four-fold sum factorisation.**  `∑_{a,b,c,d} f a c · g b d = (∑_{a,c} f a c)·(∑_{b,d} g b d)`. -/
lemma sum_four_factor {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → γ → ℂ) (g : β → δ → ℂ) :
    (∑ a : α, ∑ b : β, ∑ c : γ, ∑ d : δ, f a c * g b d)
      = (∑ a, ∑ c, f a c) * (∑ b, ∑ d, g b d) := by
  rw [Finset.sum_mul_sum (s := Finset.univ) (t := Finset.univ)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_mul_sum (s := Finset.univ) (t := Finset.univ)]

/-- **CRT multiplicativity of the reduced sum `T`.**  For coprime moduli `m, n`, integers `c₁, c₂`
representing the inverses of `n` modulo `m` and of `m` modulo `n` (`c₁·n ≡ 1 (mod m)`,
`c₂·m ≡ 1 (mod n)`), and any `a, h₁, h₂ : ℤ`,

  `T(mn, a, h₁, h₂) = T(m, a, h₁c₁, h₂c₁) · T(n, a, h₁c₂, h₂c₂)`.

This is the step that lets the estimate for `T` be reduced to prime powers.

Route: the CRT (`ZMod (m*n) ≃+* ZMod m × ZMod n`, or the explicit map
`x ↦ (x.val : ZMod m, x.val : ZMod n)`); the solution condition `y² = a x²` in `ZMod (m*n)` holds iff
it holds componentwise; and the character identity
`e(xH/(mn)) = e(x₁c₁H/m)·e(x₂c₂H/n)` for `x ↔ (x₁,x₂)`, which follows from
`x ≡ x₁·(n c₁) + x₂·(m c₂) (mod mn)` together with `c₁n ≡ 1 (mod m)`, `c₂m ≡ 1 (mod n)`.
With the canonical representatives used in `Tsum` one has `(x.val : ZMod m) = x₁.val`. -/
theorem Tsum_mul {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)] (hmn : Nat.Coprime m n)
    (c1 c2 : ℤ) (hc1 : (c1 : ZMod m) * (n : ZMod m) = 1) (hc2 : (c2 : ZMod n) * (m : ZMod n) = 1)
    (a h1 h2 : ℤ) :
    Tsum (m * n) a h1 h2
      = Tsum m a (h1 * c1) (h2 * c1) * Tsum n a (h1 * c2) (h2 * c2) := by
  let fA : ZMod (m*n) → ZMod (m*n) → ℂ := fun x y =>
    if y ^ 2 = (a : ZMod (m*n)) * x ^ 2 then
      E (((((x.val : ℤ) * h1 + (y.val : ℤ) * h2 : ℤ) : ℝ) / ((m*n : ℕ) : ℝ))) else 0
  let g1 : ZMod m → ZMod m → ℂ := fun x y =>
    if y ^ 2 = (a : ZMod m) * x ^ 2 then
      E (((((x.val : ℤ) * (h1*c1) + (y.val : ℤ) * (h2*c1) : ℤ) : ℝ) / ((m : ℕ) : ℝ))) else 0
  let g2 : ZMod n → ZMod n → ℂ := fun x y =>
    if y ^ 2 = (a : ZMod n) * x ^ 2 then
      E (((((x.val : ℤ) * (h1*c2) + (y.val : ℤ) * (h2*c2) : ℤ) : ℝ) / ((n : ℕ) : ℝ))) else 0
  change (∑ x : ZMod (m*n), ∑ y : ZMod (m*n), fA x y)
      = (∑ x : ZMod m, ∑ y : ZMod m, g1 x y) * (∑ x : ZMod n, ∑ y : ZMod n, g2 x y)
  rw [Fintype.sum_equiv (ZMod.chineseRemainder hmn)
        (fun x : ZMod (m*n) => ∑ y : ZMod (m*n), fA x y)
        (fun p : ZMod m × ZMod n => ∑ y : ZMod (m*n), fA ((ZMod.chineseRemainder hmn).symm p) y)
        (fun x => by simp [RingEquiv.symm_apply_apply])]
  rw [show (∑ p : ZMod m × ZMod n, ∑ y : ZMod (m*n),
              fA ((ZMod.chineseRemainder hmn).symm p) y)
        = ∑ p : ZMod m × ZMod n, ∑ q : ZMod m × ZMod n,
            fA ((ZMod.chineseRemainder hmn).symm p) ((ZMod.chineseRemainder hmn).symm q) from by
      apply Finset.sum_congr rfl; intro p _
      rw [Fintype.sum_equiv (ZMod.chineseRemainder hmn)
            (fun y : ZMod (m*n) => fA ((ZMod.chineseRemainder hmn).symm p) y)
            (fun q : ZMod m × ZMod n =>
              fA ((ZMod.chineseRemainder hmn).symm p) ((ZMod.chineseRemainder hmn).symm q))
            (fun y => by simp [RingEquiv.symm_apply_apply])]]
  rw [show (∑ p : ZMod m × ZMod n, ∑ q : ZMod m × ZMod n,
              fA ((ZMod.chineseRemainder hmn).symm p) ((ZMod.chineseRemainder hmn).symm q))
        = ∑ p : ZMod m × ZMod n, ∑ q : ZMod m × ZMod n, g1 p.1 q.1 * g2 p.2 q.2 from by
      apply Finset.sum_congr rfl; intro p _
      apply Finset.sum_congr rfl; intro q _
      exact summand_crt hmn c1 c2 hc1 hc2 a h1 h2 p q]
  rw [show (∑ p : ZMod m × ZMod n, ∑ q : ZMod m × ZMod n, g1 p.1 q.1 * g2 p.2 q.2)
        = (∑ x : ZMod m, ∑ y : ZMod m, g1 x y) * (∑ x : ZMod n, ∑ y : ZMod n, g2 x y) from by
      simp only [Fintype.sum_prod_type]
      exact sum_four_factor g1 g2]

end Work.FIArea2
