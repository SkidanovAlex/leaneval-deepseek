import Mathlib
import Submission.NK.Chebotarev.CommonSqrtInCyclotomic
import Submission.NK.Chebotarev.exists_sq_eq_ratCast_in_cyclotomic_of_dvd
import Submission.NK.Chebotarev.nonempty_commonSqrtInCyclotomic_ulift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Square roots of a finite family of rationals inside one cyclotomic field

`NK.Chebotarev.SqrtInCyclotomic` (and `NK.Chebotarev.ExistsSqrtInCyclotomic`) record a
cyclotomic field containing a square root of a *single* rational.  For the multiquadratic case of
Kronecker–Weber we need the simultaneous statement: one cyclotomic field containing square roots of
**all** members of a finite family `d : Fin r → ℚ`.

The construction is completely explicit.  Write `d i = (d i).num / (d i).den` and put

`N = 8 * ∏ i, max 1 ((d i).num * (d i).den).natAbs`.

Every prime dividing `(d i).num * (d i).den` (for every `i`) then divides `N`; since `8 ∣ N`, the
field `ℚ(ζ_N)` contains `√(-1)`, `√2`, and `√p` for each odd prime `p ∣ N` (quadratic Gauss sum),
hence `√((d i).num * (d i).den)` and finally `√(d i) = √((d i).num * (d i).den) / (d i).den`
(`NK.Chebotarev.exists_sq_eq_ratCast_in_cyclotomic_of_dvd`).

The result is first proved at universe level `0` for `F = CyclotomicField N ℚ` and then transported
to an arbitrary universe along `ULift`
(`NK.Chebotarev.nonempty_commonSqrtInCyclotomic_ulift`), exactly as in
`NK.Chebotarev.ExistsSqrtInCyclotomic`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

namespace NK.Chebotarev

/-- **Universe level `0` form.**  A single cyclotomic field `ℚ(ζ_N)` of a suitable explicit level
`N` contains square roots of all the rationals `d i`.

For `d i ≠ 0` the root of `d i` is obtained from
`NK.Chebotarev.exists_sq_eq_ratCast_in_cyclotomic_of_dvd`; the only point to check is that every
prime dividing `(d i).num * (d i).den` divides `8 * ∏ i, max 1 ((d i).num * (d i).den).natAbs`,
which holds because `(d i).num * (d i).den ≠ 0` and `max 1 x = x` for `x ≠ 0`.  For `d i = 0` we
simply take the root `0`. -/
theorem nonempty_commonSqrtInCyclotomic_zero (r : ℕ) (d : Fin r → ℚ) :
    Nonempty (CommonSqrtInCyclotomic.{0} r d) := by
  classical
  let N : ℕ := 8 * ∏ i : Fin r, max 1 (((d i).num * ((d i).den : ℤ)).natAbs)
  have hprod : 0 < ∏ i : Fin r, max 1 (((d i).num * ((d i).den : ℤ)).natAbs) :=
    Finset.prod_pos fun i _ => lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)
  have hNpos : 0 < N := Nat.mul_pos (by norm_num) hprod
  haveI : NeZero N := ⟨hNpos.ne'⟩
  have h8 : 8 ∣ N := ⟨∏ i : Fin r, max 1 (((d i).num * ((d i).den : ℤ)).natAbs), rfl⟩
  haveI : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  have hroot : ∀ i : Fin r, ∃ x : CyclotomicField N ℚ,
      x ^ 2 = algebraMap ℚ (CyclotomicField N ℚ) (d i) := by
    intro i
    rcases eq_or_ne (d i) 0 with h0 | hne
    · -- `d i = 0`: the root is `0`
      refine ⟨0, ?_⟩
      rw [h0, map_zero]
      simp
    · -- `d i ≠ 0`: every prime of `(d i).num * (d i).den` divides `N`
      refine exists_sq_eq_ratCast_in_cyclotomic_of_dvd N h8 (d i) ?_
      intro p hp hpm
      have hmi : (d i).num * ((d i).den : ℤ) ≠ 0 := by
        refine mul_ne_zero ?_ ?_
        · intro hnum0
          have h := Rat.num_div_den (d i)
          rw [hnum0] at h
          exact hne (by simpa using h.symm)
        · exact Int.natCast_ne_zero.mpr (d i).pos.ne'
      have hle : 1 ≤ ((d i).num * ((d i).den : ℤ)).natAbs :=
        Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hmi)
      have hdvd : max 1 ((d i).num * ((d i).den : ℤ)).natAbs ∣
          ∏ j : Fin r, max 1 (((d j).num * ((d j).den : ℤ)).natAbs) :=
        Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
      rw [max_eq_right hle] at hdvd
      exact dvd_mul_of_dvd_right (dvd_trans hpm hdvd) 8
  exact ⟨{ n := N, hn := hNpos, F := CyclotomicField N ℚ,
            s := fun i => Classical.choose (hroot i),
            s_sq := fun i => Classical.choose_spec (hroot i) }⟩

theorem exists_common_sqrt (r : ℕ) (d : Fin r → ℚ) :
    Nonempty (NK.Chebotarev.CommonSqrtInCyclotomic.{u} r d) := by
  exact nonempty_commonSqrtInCyclotomic_ulift r d (nonempty_commonSqrtInCyclotomic_zero r d)

end NK.Chebotarev
