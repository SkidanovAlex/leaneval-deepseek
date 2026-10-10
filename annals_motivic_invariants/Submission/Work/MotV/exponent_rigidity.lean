import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotV.ExpRigDefs
import Submission.Work.MotV.val_aeval_natTrailingDegree
import Submission.Work.MotV.val_aeval_shift
import Submission.Work.MotV.aeval_num_denom_symm
import Submission.Work.MotV.not_fifth_pow_of_exp_value
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false

open scoped WithZero
open Polynomial WithZero Multiplicative

namespace Work.MotV
noncomputable section

/-! ## Auxiliary lemmas for the exponent count (node V4)

These are the pieces of the argument of `Work.MotV.exponent_rigidity` proper: the behaviour of a
valuation on `ℤ`-powers and on the element `h * (α h)^k`, and the local count of `ord_0 (β h)`
for an arbitrary `𝕜`-automorphism `β` of `𝕜(t)`. -/

/-- A valuation commutes with `ℤ`-powers. -/
theorem val_zpow {F : Type*} [Field F] (v : Valuation F ℤᵐ⁰) (x : F) (k : ℤ) :
    v (x ^ k) = (v x) ^ k := by
  cases k with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast, map_pow, zpow_natCast]
  | negSucc n => simp only [zpow_negSucc, Valuation.map_inv, map_pow]

/-- The value of `hT 𝕜 * (α (hT 𝕜)) ^ k` at a valuation `v` with `v (hT 𝕜) = exp (-m)` and
`v (α (hT 𝕜)) = exp (-m')` is `exp (-(m + k * m'))`. -/
theorem val_g (𝕜 : Type*) [Field 𝕜] (α : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜) (k : ℤ)
    (v : Valuation (RatFunc 𝕜) ℤᵐ⁰) (m m' : ℤ)
    (h : v (hT 𝕜) = exp (-m)) (h' : v (α (hT 𝕜)) = exp (-m')) :
    v (hT 𝕜 * (α (hT 𝕜)) ^ k) = exp (-(m + k * m')) := by
  rw [map_mul, val_zpow, h, h', ← WithZero.exp_zsmul, ← WithZero.exp_add]
  congr 1
  rw [zsmul_eq_mul, Int.cast_id]
  first | refl_ring1 | ring

/-- **The local count.**  For any `𝕜`-automorphism `β` of `𝕜(t)`, the value of `h = t(t-1)` at the
`t`-adic valuation `vT 𝕜` is `exp (-c)` with `c ∈ {-2, 0, 1}`: `β h` has a double pole at `t = 0`
(`c = -2`), is a unit there (`c = 0`), or has a simple zero there (`c = 1`).

Write `X = U(a)/V(a)` with `a = β X`, `U = (β.symm X).num`, `V = (β.symm X).denom` (the `aeval`
form of `RatFunc.num_div_denom`); `h = a(a-1)`, so it suffices to control `vT 𝕜 a` and
`vT 𝕜 (a - 1)`.  If `a` has a pole at `t = 0` (resp. a zero), the valuation of `U(a)` is
`(vT 𝕜 a) ^ natDegree U` (resp. `(vT 𝕜 a) ^ natTrailingDegree U`, the mirror of Mathlib's
`Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X`); comparing with
the `t`-adic valuation of `X` (which is `exp (-1)`) pins the value: the logarithm of `vT 𝕜 a`
divides `1`.  If `a` is a unit at `t = 0`, then either `a - 1` is a unit (giving `c = 0`), or
`a` takes the value `1` at `t = 0`, and the shifted form of the same computation (applied to the
polynomials shifted by `X + 1`) gives `vT 𝕜 (a - 1) = exp (-1)`. -/
theorem vT_bound (𝕜 : Type*) [Field 𝕜] (β : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜) :
    ∃ c : ℤ, (c = -2 ∨ c = 0 ∨ c = 1) ∧ vT 𝕜 (β (hT 𝕜)) = exp (-c) := by
  haveI htriv : (vT 𝕜).IsTrivialOn 𝕜 := (trivOn_iff_isTrivialOn (vT 𝕜)).mp (vT_trivOn 𝕜)
  set a : RatFunc 𝕜 := β RatFunc.X with ha
  set U : Polynomial 𝕜 := (β.symm RatFunc.X).num with hU
  set V : Polynomial 𝕜 := (β.symm RatFunc.X).denom with hV
  have hX1 : (β.symm RatFunc.X) ≠ 0 := by
    intro h
    exact RatFunc.X_ne_zero (β.symm.injective (by rw [h, map_zero]))
  have ha0 : a ≠ 0 := by
    rw [ha]
    intro h
    exact RatFunc.X_ne_zero (β.injective (by rw [h, map_zero]))
  have hU0 : U ≠ 0 := by
    rw [hU]
    exact RatFunc.num_ne_zero hX1
  have hV0 : V ≠ 0 := by
    rw [hV]
    exact RatFunc.denom_ne_zero _
  have hrel : RatFunc.X * (V.aeval a) = U.aeval a := by
    rw [hV, hU, ha]
    exact aeval_num_denom_symm 𝕜 β
  have hxa : vT 𝕜 a ≠ 0 := (Valuation.ne_zero_iff (vT 𝕜)).mpr ha0
  have hneg1 : vT 𝕜 (-1 : RatFunc 𝕜) = 1 := by
    have h : (-1 : RatFunc 𝕜) = algebraMap 𝕜 (RatFunc 𝕜) (-1) := by simp
    rw [h, vT_trivOn 𝕜 (-1) (by norm_num)]
  have hβh : β (hT 𝕜) = a * (a - 1) := by
    rw [hT, map_mul, map_sub, map_one, ha]
  -- the log computation: `exp (-1) * x ^ n = x ^ m` and `x ≠ 0` force `(m - n) * log x = -1`
  have hlogeq : ∀ (x : ℤᵐ⁰) (n m : ℕ), x ≠ 0 → exp (-1 : ℤ) * x ^ n = x ^ m →
      ((m : ℤ) - n) * x.log = -1 := by
    intro x n m hx h
    have h1 := congrArg WithZero.log h
    rw [WithZero.log_mul (exp_ne_zero) (pow_ne_zero _ hx), WithZero.log_exp,
      WithZero.log_pow, WithZero.log_pow, nsmul_eq_mul, nsmul_eq_mul] at h1
    linarith
  have hlogneg : ∀ (x : ℤᵐ⁰) (n m : ℕ), x ≠ 0 → exp (-1 : ℤ) * x ^ n = x ^ m →
      x.log < 0 → x.log = -1 := by
    intro x n m hx h hlt
    have h' : x.log * ((m : ℤ) - n) = -1 := by
      rw [mul_comm]; exact hlogeq x n m hx h
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one h' with h1 | h1 <;> omega
  have hlogpos : ∀ (x : ℤᵐ⁰) (n m : ℕ), x ≠ 0 → exp (-1 : ℤ) * x ^ n = x ^ m →
      0 < x.log → x.log = 1 := by
    intro x n m hx h hlt
    have h' : x.log * ((m : ℤ) - n) = -1 := by
      rw [mul_comm]; exact hlogeq x n m hx h
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one h' with h1 | h1 <;> omega
  rcases lt_trichotomy (vT 𝕜 a) 1 with hlt | heq | hgt
  · -- Case B: `a` vanishes at `t = 0`
    have hzU := val_aeval_natTrailingDegree (v := vT 𝕜) hlt hU0
    have hzV := val_aeval_natTrailingDegree (v := vT 𝕜) hlt hV0
    have hkey : exp (-1 : ℤ) * (vT 𝕜 a) ^ V.natTrailingDegree
        = (vT 𝕜 a) ^ U.natTrailingDegree := by
      have h := congrArg (vT 𝕜) hrel
      rw [map_mul] at h
      rw [vT_X, hzV, hzU] at h
      exact h
    have hlneg : (vT 𝕜 a).log < 0 := by
      rw [← WithZero.exp_lt_exp, WithZero.exp_log hxa, WithZero.exp_zero]
      exact hlt
    have hLval : (vT 𝕜 a).log = -1 := hlogneg _ _ _ hxa hkey hlneg
    have ha1 : vT 𝕜 a = exp (-1 : ℤ) := by rw [← WithZero.exp_log hxa, hLval]
    have ha1m : vT 𝕜 (a - 1) = 1 := by
      have hlt' : vT 𝕜 a < vT 𝕜 (-1 : RatFunc 𝕜) := by rw [hneg1]; exact hlt
      have h := Valuation.map_add_eq_of_lt_left (vT 𝕜) hlt'
      rw [hneg1] at h
      simpa [sub_eq_add_neg, add_comm] using h
    refine ⟨1, Or.inr (Or.inr rfl), ?_⟩
    rw [hβh, map_mul, ha1, ha1m, mul_one]
  · -- Case C: `a` is a unit at `t = 0`
    have ha1m_ne : a - 1 ≠ 0 := by
      intro h
      have h1 : β RatFunc.X - 1 = 0 := by rw [← ha]; exact h
      have h1' : β RatFunc.X = (1 : RatFunc 𝕜) := sub_eq_zero.mp h1
      have h2 : β (RatFunc.X - 1) = 0 := by
        rw [map_sub, map_one, h1', sub_self]
      have h3 : (RatFunc.X - 1 : RatFunc 𝕜) = 0 :=
        β.injective (by rw [h2, map_zero])
      have h4 : vT 𝕜 (RatFunc.X - 1) = 0 := by rw [h3, map_zero]
      rw [vT_X_sub_one] at h4
      exact one_ne_zero h4
    have hxw : vT 𝕜 (a - 1) ≠ 0 := (Valuation.ne_zero_iff (vT 𝕜)).mpr ha1m_ne
    rcases lt_trichotomy (vT 𝕜 (a - 1)) 1 with h2lt | h2eq | h2gt
    · -- `a - 1` vanishes at `t = 0`: shifted form of the computation, giving `exp (-1)`
      have hshU := val_aeval_shift (v := vT 𝕜) (a := a) (c := (1 : 𝕜))
        (by simpa using h2lt) (p := U) hU0
      have hshV := val_aeval_shift (v := vT 𝕜) (a := a) (c := (1 : 𝕜))
        (by simpa using h2lt) (p := V) hV0
      have hshU' : vT 𝕜 (U.aeval a)
          = (vT 𝕜 (a - 1)) ^ (U.comp (Polynomial.X + Polynomial.C (1 : 𝕜))).natTrailingDegree := by
        simpa using hshU
      have hshV' : vT 𝕜 (V.aeval a)
          = (vT 𝕜 (a - 1)) ^ (V.comp (Polynomial.X + Polynomial.C (1 : 𝕜))).natTrailingDegree := by
        simpa using hshV
      have hkey : exp (-1 : ℤ)
            * (vT 𝕜 (a - 1)) ^ (V.comp (Polynomial.X + Polynomial.C (1 : 𝕜))).natTrailingDegree
          = (vT 𝕜 (a - 1)) ^ (U.comp (Polynomial.X + Polynomial.C (1 : 𝕜))).natTrailingDegree := by
        have h := congrArg (vT 𝕜) hrel
        rw [map_mul, vT_X, hshV', hshU'] at h
        exact h
      have hlneg : (vT 𝕜 (a - 1)).log < 0 := by
        rw [← WithZero.exp_lt_exp, WithZero.exp_log hxw, WithZero.exp_zero]
        exact h2lt
      have hLval : (vT 𝕜 (a - 1)).log = -1 := hlogneg _ _ _ hxw hkey hlneg
      have hval : vT 𝕜 (a - 1) = exp (-1 : ℤ) := by
        rw [← WithZero.exp_log hxw, hLval]
      refine ⟨1, Or.inr (Or.inr rfl), ?_⟩
      rw [hβh, map_mul, heq, hval, one_mul]
    · -- `a - 1` is a unit at `t = 0`
      refine ⟨0, Or.inr (Or.inl rfl), ?_⟩
      rw [hβh, map_mul, heq, h2eq, mul_one, neg_zero, WithZero.exp_zero]
    · -- impossible: `a - 1` cannot have a pole while `a` is a unit
      exfalso
      have h : vT 𝕜 (1 + (a - 1)) = vT 𝕜 (a - 1) :=
        Valuation.map_add_eq_of_lt_right (vT 𝕜) (by rw [map_one]; exact h2gt)
      rw [show (1 : RatFunc 𝕜) + (a - 1) = a by ring, heq] at h
      rw [h] at h2gt
      exact absurd h2gt (lt_irrefl _)
  · -- Case A: `a` has a pole at `t = 0`
    have hpU := Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
      (v := vT 𝕜) a hgt hU0
    have hpV := Polynomial.valuation_aeval_eq_valuation_X_pow_natDegree_of_one_lt_valuation_X
      (v := vT 𝕜) a hgt hV0
    have hkey : exp (-1 : ℤ) * (vT 𝕜 a) ^ V.natDegree = (vT 𝕜 a) ^ U.natDegree := by
      have h := congrArg (vT 𝕜) hrel
      rw [map_mul] at h
      rw [vT_X, hpV, hpU] at h
      exact h
    have hlpos : 0 < (vT 𝕜 a).log := by
      rw [← WithZero.exp_lt_exp, WithZero.exp_log hxa, WithZero.exp_zero]
      exact hgt
    have hLval : (vT 𝕜 a).log = 1 := hlogpos _ _ _ hxa hkey hlpos
    have ha1 : vT 𝕜 a = exp (1 : ℤ) := by rw [← WithZero.exp_log hxa, hLval]
    have ha1m : vT 𝕜 (a - 1) = exp (1 : ℤ) := by
      have hlt' : vT 𝕜 (-1 : RatFunc 𝕜) < vT 𝕜 a := by rw [hneg1]; exact hgt
      have h := Valuation.map_add_eq_of_lt_left (vT 𝕜) hlt'
      rw [ha1] at h
      rwa [sub_eq_add_neg]
    refine ⟨-2, Or.inl rfl, ?_⟩
    rw [hβh, map_mul, ha1, ha1m, ← WithZero.exp_add]
    norm_num

/-- Node V4: the exponent count.  For an arbitrary `𝕜`-automorphism `α` of `𝕜(t)` and
`k ∈ {2,3,-2,-3}`, the element `h * (α h)^k` of `𝕜(t)`, `h = hT 𝕜 = t(t-1)`, is *not*
fifth-power valued.  True over every field, including imperfect ones and any characteristic; sharp
for `k = -1` with `α = id`, where it fails.

Route.  A valuation `w` of `𝕜(t)` trivial on `𝕜` that has value group `ℤ` is `ord_p` for a unique
rational place `p`, and `ord_0 h = 1`, `ord_1 h = 1`, `ord_∞ h = -2`; for a Möbius `α`,
`ord_p (α h) = ord_{α(p)} h`, so this is one of `{1, 1, -2}`.  Since `h * (α h)^k` is
fifth-power valued only if `ord_p (h) + k * ord_{α(p)}(h) ≡ 0 (mod 5)` for *every* `p`, it suffices
to exhibit one `p` where this fails:
* `k = 2` and `k = -3` have `k ≡ 2`: at `p = 0`, `1 + 2 * c ≡ 0` forces `c ≡ 2`, which is not in
  `{1, 1, -2} ≡ {1, 1, 3}`; so `p = 0` witnesses.
* `k = 3` and `k = -2` have `k ≡ 3`: at `p = 0`, `1 + 3 * c ≡ 0` forces `c ≡ 3`, i.e.
  `α(0) = ∞`; at `p = 1`, `1 + 3 * c' ≡ 0` again forces `c' ≡ 3`, i.e. `α(1) = ∞`.
  Both cannot hold (`α` injective), so one of `p = 0, 1` witnesses.
(Do NOT try to use the place `∞` alone: for `k ≡ 2` and `α(∞) ∈ {0,1}` one has
`-2 + k * ord_{α(∞)} h ≡ 0`, e.g. `α(t) = 1/t`, `k = 2`, where `h * (α h)^2 = (t-1)^3/t^3`.)
Use `ord_0` as the `HeightOneSpectrum` valuation of `Polynomial 𝕜` at `X`, `ord_1` as the one at
`X - 1`, `ord_∞` as `inftyValuation`; the only structural input is the classification of the
`ℤᵐ⁰`-valued valuations of `𝕜(t)` trivial on `𝕜` (a polynomial argument in `w t`).

Implementation.  We use `vT 𝕜 = ord_0`.  For every automorphism `β`, `vT 𝕜 (β h) = exp (-c)` with
`c ∈ {-2,0,1}` (`vT_bound`).  For `k ≡ 2 (5)` the place `t = 0` alone witnesses: the value of
`h * (α h)^k = 1 + k * c` is never divisible by `5`.  For `k ≡ 3 (5)` the only failing case at
`t = 0` is `c = -2` (i.e. `α` has a pole at `t = 0`); then the composite valuation
`v = vT 𝕜 ∘ α` witnesses instead, since `v (h * (α h)^k) = -c - k * c'` with
`c' ∈ {-2,0,1}` for `α²` (this is where the independence of the argument from `β` is used). -/
theorem exponent_rigidity (𝕜 : Type*) [Field 𝕜] (α : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜) (k : ℤ)
    (hk : k = 2 ∨ k = 3 ∨ k = -2 ∨ k = -3) :
    ¬ FifthPowerValued 𝕜 (hT 𝕜 * (α (hT 𝕜)) ^ k) := by
  intro hFP
  obtain ⟨c, hcmem, hc⟩ := vT_bound 𝕜 α
  -- `finish` closes a case given a witness valuation with the values of `hT 𝕜` and `α (hT 𝕜)`
  have finish : ∀ (v : Valuation (RatFunc 𝕜) ℤᵐ⁰), TrivOn 𝕜 v → ∀ m m' : ℤ,
      v (hT 𝕜) = exp (-m) → v (α (hT 𝕜)) = exp (-m') →
      (¬ (5 : ℤ) ∣ (m + k * m')) → False := by
    intro v hv m m' h h' hm
    have hval := val_g 𝕜 α k v m m' h h'
    refine (not_fifth_pow_of_exp_value v hval ?_) (hFP v hv)
    intro h5
    exact hm (by rwa [dvd_neg] at h5)
  rcases hk with rfl | rfl | rfl | rfl
  · -- `k = 2`
    refine finish (vT 𝕜) (vT_trivOn 𝕜) 1 c (by rw [vT_hT]) hc ?_
    rcases hcmem with h | h | h <;> subst h <;> norm_num
  · -- `k = 3`
    by_cases hc2 : c = -2
    · obtain ⟨c', hc'mem, hc'⟩ := vT_bound 𝕜 (α * α)
      have hv : TrivOn 𝕜 (Valuation.comap (α : RatFunc 𝕜 →+* RatFunc 𝕜) (vT 𝕜)) := by
        intro x hx
        rw [Valuation.comap_apply]
        change (vT 𝕜) (α ((algebraMap 𝕜 (RatFunc 𝕜)) x)) = 1
        rw [AlgEquiv.commutes α x]
        exact vT_trivOn 𝕜 x hx
      have h1 : (Valuation.comap (α : RatFunc 𝕜 →+* RatFunc 𝕜) (vT 𝕜)) (hT 𝕜) = exp (-c) := by
        rw [Valuation.comap_apply]
        exact hc
      have h2 : (Valuation.comap (α : RatFunc 𝕜 →+* RatFunc 𝕜) (vT 𝕜)) (α (hT 𝕜))
          = exp (-c') := by
        rw [Valuation.comap_apply]
        change (vT 𝕜) ((α * α) (hT 𝕜)) = exp (-c')
        exact hc'
      refine finish _ hv c c' h1 h2 ?_
      rcases hc'mem with h | h | h <;> subst h <;> rw [hc2] <;> norm_num
    · refine finish (vT 𝕜) (vT_trivOn 𝕜) 1 c (by rw [vT_hT]) hc ?_
      rcases hcmem with h | h | h
      · exact absurd h hc2
      · subst h; norm_num
      · subst h; norm_num
  · -- `k = -2`
    by_cases hc2 : c = -2
    · obtain ⟨c', hc'mem, hc'⟩ := vT_bound 𝕜 (α * α)
      have hv : TrivOn 𝕜 (Valuation.comap (α : RatFunc 𝕜 →+* RatFunc 𝕜) (vT 𝕜)) := by
        intro x hx
        rw [Valuation.comap_apply]
        change (vT 𝕜) (α ((algebraMap 𝕜 (RatFunc 𝕜)) x)) = 1
        rw [AlgEquiv.commutes α x]
        exact vT_trivOn 𝕜 x hx
      have h1 : (Valuation.comap (α : RatFunc 𝕜 →+* RatFunc 𝕜) (vT 𝕜)) (hT 𝕜) = exp (-c) := by
        rw [Valuation.comap_apply]
        exact hc
      have h2 : (Valuation.comap (α : RatFunc 𝕜 →+* RatFunc 𝕜) (vT 𝕜)) (α (hT 𝕜))
          = exp (-c') := by
        rw [Valuation.comap_apply]
        change (vT 𝕜) ((α * α) (hT 𝕜)) = exp (-c')
        exact hc'
      refine finish _ hv c c' h1 h2 ?_
      rcases hc'mem with h | h | h <;> subst h <;> rw [hc2] <;> norm_num
    · refine finish (vT 𝕜) (vT_trivOn 𝕜) 1 c (by rw [vT_hT]) hc ?_
      rcases hcmem with h | h | h
      · exact absurd h hc2
      · subst h; norm_num
      · subst h; norm_num
  · -- `k = -3`
    refine finish (vT 𝕜) (vT_trivOn 𝕜) 1 c (by rw [vT_hT]) hc ?_
    rcases hcmem with h | h | h <;> subst h <;> norm_num

end
end Work.MotV

set_option linter.dupNamespace false

namespace Work.MotV

namespace Work.MotV

/-- The same statement as `Work.MotV.exponent_rigidity`, under the doubly nested namespace of the
original file, kept so that the name `Work.MotV.Work.MotV.exponent_rigidity` also resolves. -/
theorem exponent_rigidity (𝕜 : Type*) [Field 𝕜] (α : RatFunc 𝕜 ≃ₐ[𝕜] RatFunc 𝕜) (k : ℤ)
    (hk : k = 2 ∨ k = 3 ∨ k = -2 ∨ k = -3) :
    ¬ FifthPowerValued 𝕜 (hT 𝕜 * (α (hT 𝕜)) ^ k) :=
  _root_.Work.MotV.exponent_rigidity 𝕜 α k hk

end Work.MotV

end Work.MotV
