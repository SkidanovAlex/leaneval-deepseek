import Mathlib
import Submission.Work.TorsorExistence.ArtinSchreier.Irreducible
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `w` of Artin–Schreier type of degree `< 5` over `F` lies in `F`

Let `F` be a field of characteristic `5`, `Ω` an `F`-algebra which is a field, `c : F`, and
`w : Ω` with `w ^ 5 - w = c`.  If `w` is a root of a *nonzero* polynomial `Q ∈ F[X]` of degree
`≤ 4`, then `w` already lies in the image of `F`.

The point is that `X ^ 5 - X - a` is either split or irreducible over a field of
characteristic `5`; here this is used in the following form:

* If `c = b ^ 5 - b` for some `b : F`, then `w - b` satisfies `y ^ 5 = y`, hence `w - b` is one of
  `0,1,2,3,4` (see `pow_five_eq_self_exists`), so `w ∈ F`.
* Otherwise `X ^ 5 - X - C c` is irreducible
  (`irreducible_X_pow_five_sub_X_sub_C`), and `minpoly F w` divides both it and `Q`.  Since an
  irreducible polynomial has no non-unit proper divisors, `minpoly F w` is associated to a degree
  `5` polynomial, contradicting `minpoly F w ∣ Q` with `Q ≠ 0` and `natDegree Q ≤ 4`.

Both ingredients are taken from `Submission.Work.TorsorExistence.ArtinSchreier`.
-/

namespace Work.MotV5

open Polynomial

theorem as_minpoly_four {F Ω : Type} [Field F] [CharP F 5] [Field Ω]
    [Algebra F Ω] (w : Ω) (c : F) (hw : w ^ 5 - w = algebraMap F Ω c) (Q : Polynomial F)
    (hQ0 : Q ≠ 0) (hQdeg : Q.natDegree ≤ 4) (hQw : Polynomial.aeval w Q = 0) :
    w ∈ Set.range (algebraMap F Ω) := by
  have h5Ω : (5 : Ω) = 0 := by
    have h := congrArg (algebraMap F Ω) (CharP.cast_eq_zero F 5)
    simp only [map_zero] at h
    rw [map_natCast] at h
    exact h
  by_cases hc : ∃ b : F, b ^ 5 - b = c
  · -- `c` is in the image of `℘ : b ↦ b ^ 5 - b`, so `w - b` is a fifth root of itself.
    obtain ⟨b, hb⟩ := hc
    have hkey : (w - algebraMap F Ω b) ^ 5 - (w - algebraMap F Ω b) = 0 := by
      rw [Work.TorsorExistence.ArtinSchreier.sub_pow_five h5Ω, ← map_pow]
      rw [show (w ^ 5 - algebraMap F Ω (b ^ 5)) - (w - algebraMap F Ω b)
            = (w ^ 5 - w) - (algebraMap F Ω (b ^ 5) - algebraMap F Ω b) from by ring]
      rw [hw, ← map_sub, hb, sub_self]
    have hy : (w - algebraMap F Ω b) ^ 5 = (w - algebraMap F Ω b) := sub_eq_zero.mp hkey
    obtain ⟨i, _, hi⟩ :=
      Work.TorsorExistence.ArtinSchreier.pow_five_eq_self_exists h5Ω
        (w - algebraMap F Ω b) hy
    refine ⟨b + (i : F), ?_⟩
    rw [map_add, map_natCast, ← hi]
    first | refl_ring1 | ring
  · -- `X ^ 5 - X - c` is irreducible, forcing `minpoly F w` to have degree `5`.
    have hirr : Irreducible (X ^ 5 - X - C c : Polynomial F) :=
      Work.TorsorExistence.ArtinSchreier.irreducible_X_pow_five_sub_X_sub_C c hc
    have hfw : Polynomial.aeval w (X ^ 5 - X - C c : Polynomial F) = 0 := by
      simp only [map_sub, map_pow, aeval_X, aeval_C]
      rw [hw, sub_self]
    have hmf : minpoly F w ∣ (X ^ 5 - X - C c : Polynomial F) := minpoly.dvd F w hfw
    have hmQ : minpoly F w ∣ Q := minpoly.dvd F w hQw
    have hmd : (minpoly F w).natDegree ≤ 4 :=
      le_trans (Polynomial.natDegree_le_of_dvd hmQ hQ0) hQdeg
    have hm0 : minpoly F w ≠ 0 := fun h0 => hQ0 (by
      obtain ⟨r, hr⟩ := hmQ
      rw [h0, zero_mul] at hr
      exact hr)
    have hfdeg : (X ^ 5 - X - C c : Polynomial F).natDegree = 5 := by
      have h : (X ^ 5 - X - C c : Polynomial F) = (X ^ 5 - C c) - X := by ring
      rw [h, Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
      · exact Polynomial.natDegree_X_pow_sub_C
      · rw [Polynomial.natDegree_X, Polynomial.natDegree_X_pow_sub_C]; norm_num
    rcases (Irreducible.dvd_iff hirr).mp hmf with hunit | hassoc
    · -- `minpoly F w` is a unit, hence `aeval w (minpoly F w) = 0` is a unit of `Ω`.
      exfalso
      have h := hunit.map (Polynomial.aeval w)
      rw [minpoly.aeval F w] at h
      exact not_isUnit_zero h
    · -- `minpoly F w` is associated to `X ^ 5 - X - C c`, of degree `5`.
      exfalso
      have hle := Polynomial.natDegree_le_of_dvd hassoc.dvd hm0
      rw [hfdeg] at hle
      omega

end Work.MotV5
