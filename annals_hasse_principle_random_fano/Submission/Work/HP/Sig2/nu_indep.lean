import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Sig2.VeroMon
import Submission.Work.HP.Lat.detLAux
import Submission.Work.HP.Sig2.veronese_proportional
import Submission.Work.HP.Sig2.eq_pm_of_prim_prop

/-!
# `ν_{d,n}(x)` and `ν_{d,n}(y)` are `ℤ`-linearly independent for primitive `x ≠ ±y`

If `x, y : ℤ^{n+1}` are primitive (`IsPrim`, i.e. `gcd` of the coordinates is `1`) and
`x ≠ y`, `x ≠ -y`, then the Veronese images `ν_{d,n}(x)` and `ν_{d,n}(y)` are linearly
independent over `ℤ` (for `d ≥ 2`).

The proof is by contradiction.  A non-trivial integer relation
`a · ν(x) + b · ν(y) = 0` with `a, b ≠ 0` becomes the rational proportionality
`ν(x) = λ · ν(y)` with `λ = -b/a ≠ 0`; the injectivity of `ν_{d,n}` on rays over a field
(`veronese_proportional`) turns this into `x = μ · y` over `ℚ`, and primitivity of the
integer vectors forces `μ = ±1` (`eq_pm_of_prim_prop`), contradicting `x ≠ ±y`.
-/

set_option autoImplicit false

namespace Work.HP.Sig2

open Finset MvPolynomial

/-- Two primitive integer vectors which are not equal up to sign have linearly independent
Veronese images. -/
theorem nu_indep (d n : ℕ) (hd : 2 ≤ d) (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (hxy : x ≠ y) (hxy' : x ≠ -y) :
    LinearIndependent ℤ ![veronese d n x, veronese d n y] := by
  have hd1 : 1 ≤ d := by omega
  have hx0 : x ≠ 0 := isPrim_ne_zero hx
  have hy0 : y ≠ 0 := isPrim_ne_zero hy
  have hnx : veronese d n x ≠ 0 := veronese_ne_zero d n hd1 hx0
  have hny : veronese d n y ≠ 0 := veronese_ne_zero d n hd1 hy0
  -- `c • z = 0 → c = 0` for a nonzero integer vector `z`
  have hsmul : ∀ (c : ℤ) (z : Mon d n → ℤ), z ≠ 0 → c • z = 0 → c = 0 := by
    intro c z hz hcz
    by_contra hc
    obtain ⟨m, hm⟩ := Function.ne_iff.mp hz
    simp only [Pi.zero_apply] at hm
    have h1 := congrFun hcz m
    rw [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact hc h
    · exact hm h
  rw [LinearIndependent.pair_iff]
  intro a b hab
  -- both coefficients nonzero is impossible
  have hcontra : ¬ (a ≠ 0 ∧ b ≠ 0) := by
    rintro ⟨ha, hb⟩
    set lam : ℚ := -((b : ℚ)) / (a : ℚ) with hlamdef
    have haq : (a : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
    have hbq : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb
    have hlam : lam ≠ 0 := by
      rw [hlamdef]
      exact div_ne_zero (neg_ne_zero.mpr hbq) haq
    have hyq : (fun i => (y i : ℚ)) ≠ 0 := by
      intro h0
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hy0
      simp only [Pi.zero_apply] at hi
      have h1 : (y i : ℚ) = 0 := by
        have := congrFun h0 i; simpa using this
      exact hi (Int.cast_eq_zero.mp h1)
    -- the rational proportionality `ν(x) = lam * ν(y)`
    have hmrel : ∀ m : Mon d n,
        veronese d n (fun i => (x i : ℚ)) m = lam * veronese d n (fun i => (y i : ℚ)) m := by
      intro m
      have hmn := congrFun hab m
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
        smul_eq_mul] at hmn
      rw [veronese_intCast, veronese_intCast]
      have hcast : (a : ℚ) * ((veronese d n x m : ℤ) : ℚ)
          + (b : ℚ) * ((veronese d n y m : ℤ) : ℚ) = 0 := by
        have := congrArg (fun z : ℤ => (z : ℚ)) hmn
        push_cast at this
        exact this
      rw [hlamdef, div_mul_eq_mul_div, eq_div_iff haq]
      linear_combination hcast
    obtain ⟨mu, hmu⟩ := veronese_proportional d n hd1 (fun i => (x i : ℚ))
      (fun i => (y i : ℚ)) hyq hlam hmrel
    rcases eq_pm_of_prim_prop x y hx hy mu hmu with h | h
    · exact hxy h
    · exact hxy' h
  constructor
  · by_contra ha
    have hb : b = 0 := by
      by_contra hb
      exact hcontra ⟨ha, hb⟩
    rw [hb, zero_smul, add_zero] at hab
    exact ha (hsmul a (veronese d n x) hnx hab)
  · by_contra hb
    have ha : a = 0 := by
      by_contra ha
      exact hcontra ⟨ha, hb⟩
    rw [ha, zero_smul, zero_add] at hab
    exact hb (hsmul b (veronese d n y) hny hab)

end Work.HP.Sig2
