import Mathlib
import Submission.Work.MotV5.ordOfPlace_api
import Submission.Work.MotV5.affPlace_deriv_bound
import Submission.Work.MotV.PlaceDefs
import Submission.Work.MotV.ordPlaceCommon
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

/-!
Route.  This is a statement about a discrete valuation ring, and everything needed is already
proven in the workspace:

* `Work.MotV5.OrdAPI.ordOfPlace_mul`, `ordOfPlace_inv`, `ordOfPlace_nonneg_iff`,
  `ordOfPlace_of_mem` (`Submission.Work.MotV5.ordOfPlace_api`,
  `Submission.Work.MotV5.ordOfPlace_helpers`) give the order calculus at a rational place;
* `Work.MotV5.ordOfPlace_mul_zpow` and `Work.MotV5.ordOfPlace_unit_mul_zpow`
  (`Submission.Work.MotV5.affPlace_deriv_bound`) give, for `π : ↥S` irreducible and `w : ↥S`,
  `w ≠ 0`, `k : ℤ`: `ordOfPlace E S hS ((w : Func E) * (π : Func E) ^ k)
     = ordOfPlace E S hS (w : Func E) + k`.

Proof sketch.  `letI : IsDiscreteValuationRing ↥S := hS.1.choose`, put
`fS : ↥S := ⟨f, hf⟩` and `dS : ↥S := ⟨D f, hmem S hS f hf⟩`; then
`ordOfPlace E S hS f = (avNat fS : ℤ)` and `ordOfPlace E S hS (D f) = (avNat dS : ℤ)`
(`Work.MotV.ordPlace_eq_of_mem`, `Work.MotV.ordOfPlace_eq_ordPlace`, or
`Work.MotV5.OrdAPI.ordOfPlace_of_mem`); note `f ≠ 0` (else `D f = 0`).

* If `avNat fS = 0` then the left side is `-1` and the right side is `≥ 0` because `D f ∈ S`
  (`ordOfPlace_nonneg_of_mem`).
* Otherwise `n := avNat fS ≥ 1`.  Pick `π : ↥S` irreducible
  (`IsDiscreteValuationRing.exists_irreducible`) and use
  `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible` to write `fS = u * π ^ n` with `u : ↥Sˣ`;
  then `ordOfPlace E S hS f = n` (`ordOfPlace_unit_mul_zpow` with `k = n`).
  In `Func E`, `algebraMap fS = algebraMap u * (algebraMap π) ^ n`; applying `Derivation.leibniz`
  and `Derivation.leibniz_pow` (`D ((algebraMap π)^n) = n • ((algebraMap π)^(n-1) • D (algebraMap π))`,
  with `•` the multiplication of `Func E`) gives
    `D f = algebraMap (π ^ (n - 1) * z)`  with  `z := u * (n * dπ) + π * du`,
  where `dπ := ⟨D (algebraMap π), hmem S hS _ (algebraMap π).2⟩` and
  `du := ⟨D (algebraMap u), hmem S hS _ (algebraMap u).2⟩` (prove the equality with `Subtype.ext`
  and `ring`).  Since `D f ≠ 0` and `Func E` is a domain, `z ≠ 0`.  Hence, by
  `ordOfPlace_mul_zpow` (with `w := z`, `k := (n - 1 : ℤ)`, which needs `z ≠ 0`) and
  `ordOfPlace_nonneg_of_mem` for `z`, `ordOfPlace E S hS (D f) = ordOfPlace E S hS (algebraMap z) + (n - 1) ≥ n - 1`,
  which is the claim.
-/
theorem derivBoundMem {N : Type*} [Field N] (E : WeierstrassCurve N)
    (D : Derivation N (Work.MotC2.Func E) (Work.MotC2.Func E))
    (hmem : ∀ (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S)
      (f : Work.MotC2.Func E), f ∈ S → D f ∈ S)
    (S : Subalgebra N (Work.MotC2.Func E)) (hS : Work.MotC2.IsRatPlace E S)
    {f : Work.MotC2.Func E} (hf : f ∈ S) (hDf : D f ≠ 0) :
    Work.MotV.ordOfPlace E S hS f - 1 ≤ Work.MotV.ordOfPlace E S hS (D f) := by
  letI : IsDiscreteValuationRing ↥S := hS.1.choose
  have hDfmem : D f ∈ S := hmem S hS f hf
  let fS : ↥S := ⟨f, hf⟩
  let dS : ↥S := ⟨D f, hDfmem⟩
  -- The order of `f` is the `avNat` of `f` viewed in `↥S`.
  have hordf : Work.MotV.ordOfPlace E S hS f = ((Work.MotV.avNat fS : ℕ) : ℤ) := by
    rw [Work.MotV.ordOfPlace_eq_ordPlace, Work.MotV.ordPlace_eq_of_mem E S hS f hf]
  rcases Nat.eq_zero_or_pos (Work.MotV.avNat fS) with hn0 | hnpos
  · -- `f` is a unit of the place: its order is `0` and `D f` is regular.
    rw [hordf, hn0, Nat.cast_zero]
    have h := Work.MotV5.ordOfPlace_nonneg_of_mem E S hS hDfmem
    linarith
  · -- `f` vanishes to order `n ≥ 1` at the place.
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible ↥S
    have hfS0 : fS ≠ 0 := by
      intro h
      rw [h, Work.MotV.avNat_zero] at hnpos
      exact absurd hnpos (lt_irrefl 0)
    obtain ⟨n, u, hgu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hfS0 hπ
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exfalso
        have hz : Work.MotV.avNat fS = 0 := by
          rw [hgu, h, pow_zero, mul_one]
          exact Work.MotV.avNat_eq_zero_of_unit u
        omega
      · exact h
    have hfcoe : f = ((u : ↥S) : Work.MotC2.Func E) *
        (((π : ↥S) : Work.MotC2.Func E)) ^ n := by
      rw [show f = (fS : Work.MotC2.Func E) from rfl, hgu, Subalgebra.coe_mul,
        Subalgebra.coe_pow]
    have hordf_n : Work.MotV.ordOfPlace E S hS f = (n : ℤ) := by
      rw [hfcoe]
      simpa using Work.MotV5.ordOfPlace_unit_mul_zpow E S hS π hπ u (n : ℤ)
    -- The regular correction `z` with `D f = π ^ (n - 1) * z`.
    let dπ : ↥S := ⟨D ((π : ↥S) : Work.MotC2.Func E), hmem S hS _ π.2⟩
    let du : ↥S := ⟨D ((u : ↥S) : Work.MotC2.Func E), hmem S hS _ (u : ↥S).2⟩
    let z : ↥S := u * ((n : ↥S) * dπ) + π * du
    have hdS : dS = π ^ (n - 1) * z := by
      apply Subtype.ext
      change D f = ((π ^ (n - 1) * z : ↥S) : Work.MotC2.Func E)
      rw [hfcoe, Derivation.leibniz, Derivation.leibniz_pow]
      simp only [smul_eq_mul, nsmul_eq_mul]
      rw [show (((π : ↥S) : Work.MotC2.Func E)) ^ n
          = (((π : ↥S) : Work.MotC2.Func E)) ^ (n - 1) *
            ((π : ↥S) : Work.MotC2.Func E) from by
        rw [← pow_succ, Nat.sub_add_cancel hn1]]
      simp only [z, dπ, du, Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_pow]
      push_cast
      first | refl_ring1 | ring
    have hDf_eq : D f = (z : Work.MotC2.Func E) *
        ((π : ↥S) : Work.MotC2.Func E) ^ ((n - 1 : ℕ) : ℤ) := by
      have h1 : (dS : Work.MotC2.Func E) = (z : Work.MotC2.Func E) *
          ((π : ↥S) : Work.MotC2.Func E) ^ ((n - 1 : ℕ) : ℤ) := by
        rw [hdS, Subalgebra.coe_mul, Subalgebra.coe_pow, zpow_natCast, mul_comm]
      simpa using h1
    have hz : z ≠ 0 := by
      intro hz0
      exact hDf (by rw [hDf_eq, hz0, Subalgebra.coe_zero, zero_mul])
    rw [hordf_n, hDf_eq,
      Work.MotV5.ordOfPlace_mul_zpow E S hS π hπ z hz ((n - 1 : ℕ) : ℤ)]
    have hzmem : 0 ≤ Work.MotV.ordOfPlace E S hS (z : Work.MotC2.Func E) :=
      Work.MotV5.ordOfPlace_nonneg_of_mem E S hS z.2
    have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
    linarith

end Work.MotV
