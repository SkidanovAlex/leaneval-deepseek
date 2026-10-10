import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.ClassBCD.RatFunc.irreducible_X_pow_sub_X_sub_C
import Submission.Work.MotV5.CensusAux.fAS_notMem_pe
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.irreducible_sdualAS2_quintic`

The target ruling quintic of the AS chart

`C a * X ^ 5 - X ^ 4 + 1   (a = fAS 𝕜 = t ^ 3 + t)`

is irreducible over `RatFunc 𝕜` in characteristic `5`.

## The argument

The reversal (`Polynomial.reverse`) of `C a * X ^ 5 - X ^ 4 + 1` is the Artin–Schreier polynomial
`X ^ 5 - X + C a`, which is irreducible by `Work.ClassBCD.RatFunc.irreducible_X_pow_sub_X_sub_C`
as soon as `a` is not of the shape `b ^ 5 - b`; here `-a ∉ ℘(F)` is exactly
`Work.MotV5.CensusAux.fAS_notMem_pe`.  Reversal transfers irreducibility in the direction we need
(the whole point being that reversal is a ring-theoretic `X ↦ X⁻¹`, which is defined on
polynomials of nonzero constant coefficient), which is `irreducible_reverse` below.
-/

set_option linter.style.haveILetI false

namespace Work.MotAS

open Polynomial

/-- If `p.reverse` is a unit and `p` has nonzero constant coefficient, then `p` is a unit
(a unit of `F[X]` is a nonzero constant). -/
theorem isUnit_of_isUnit_reverse {F : Type*} [Field F] {p : F[X]} (h0 : p.coeff 0 ≠ 0)
    (hu : IsUnit p.reverse) : IsUnit p := by
  have hd : p.natDegree = 0 := by
    have h := Polynomial.natDegree_eq_zero_of_isUnit hu
    rw [reverse_natDegree, natTrailingDegree_eq_zero.mpr (Or.inr h0), tsub_zero] at h
    exact h
  rw [eq_C_of_natDegree_eq_zero hd]
  exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr h0)

/-- **Reversal transfers irreducibility.**  If `p` has nonzero constant coefficient (so that the
reciprocal polynomial `p.reverse` captures the whole of `p`) and `p` is irreducible, then so is
`p.reverse`. -/
theorem irreducible_reverse {F : Type*} [Field F] (p : F[X]) (h0 : p.coeff 0 ≠ 0)
    (hp : Irreducible p) : Irreducible p.reverse := by
  have htd : p.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr h0)
  have hN : p.reverse.natDegree = p.natDegree := by
    rw [reverse_natDegree, htd, tsub_zero]
  have hrr : p.reverse.reverse = p := by
    show reflect p.reverse.natDegree p.reverse = p
    rw [hN]
    exact reflect_reflect
  have hpne : p ≠ 0 := fun h => h0 (by rw [h, coeff_zero])
  refine ⟨?_, ?_⟩
  · intro hu
    have hd : p.natDegree = 0 := by
      have h := Polynomial.natDegree_eq_zero_of_isUnit hu
      rw [hN] at h
      exact h
    exact hp.1 (by rw [eq_C_of_natDegree_eq_zero hd]
                   exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr h0))
  · intro g h hgh
    have hcoeff : g.coeff 0 * h.coeff 0 = p.leadingCoeff := by
      have h1 := congrArg (fun q : F[X] => q.coeff 0) hgh
      rw [coeff_zero_reverse] at h1
      rw [h1]
      simp [coeff_mul]
    have hne : g.coeff 0 * h.coeff 0 ≠ 0 := by
      rw [hcoeff]
      exact leadingCoeff_ne_zero.mpr hpne
    have hpg : p = g.reverse * h.reverse := by
      rw [← hrr, hgh, reverse_mul_of_domain]
    rcases hp.isUnit_or_isUnit hpg with hu | hu
    · exact Or.inl (isUnit_of_isUnit_reverse (fun hz => hne (by rw [hz, zero_mul])) hu)
    · exact Or.inr (isUnit_of_isUnit_reverse (fun hz => hne (by rw [hz, mul_zero])) hu)

/-- **The Artin–Schreier quintic in reciprocal form.**  For a field `F` of characteristic `5` and
`a : F` with `b ^ 5 - b ≠ -a` for every `b`, the quintic `C a * X ^ 5 - X ^ 4 + 1` is irreducible
over `F`. -/
theorem irreducible_quintic (F : Type) [Field F] [CharP F 5] (a : F)
    (ha : ∀ b : F, b ^ 5 - b ≠ -a) :
    Irreducible ((Polynomial.C a : Polynomial F) * Polynomial.X ^ 5 - Polynomial.X ^ 4 + 1) := by
  haveI hprime : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have ha0 : a ≠ 0 := by
    intro h0
    refine ha 0 ?_
    rw [h0]
    norm_num
  have hQ : Irreducible ((Polynomial.X : Polynomial F) ^ 5 - Polynomial.X + Polynomial.C a) := by
    have h := Work.ClassBCD.RatFunc.irreducible_X_pow_sub_X_sub_C F 5 (-a) ha
    simpa using h
  have hrev : ((Polynomial.X : Polynomial F) ^ 5 - Polynomial.X + Polynomial.C a).reverse
      = Polynomial.C a * Polynomial.X ^ 5 - Polynomial.X ^ 4 + 1 := by
    have hrev1 : ((Polynomial.X : Polynomial F) ^ 5 - Polynomial.X + Polynomial.C a).reverse
        = Polynomial.C a * Polynomial.X ^ ((Polynomial.X : Polynomial F) ^ 5 - Polynomial.X).natDegree
          + ((Polynomial.X : Polynomial F) ^ 5 - Polynomial.X).reverse := by
      rw [show ((Polynomial.X : Polynomial F) ^ 5 - Polynomial.X + Polynomial.C a)
          = Polynomial.C a + ((Polynomial.X : Polynomial F) ^ 5 - Polynomial.X) from by ring]
      rw [reverse_C_add]
    rw [hrev1]
    have h1 : ((Polynomial.X : Polynomial F) ^ 5 - Polynomial.X).natDegree = 5 := by
      rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [natDegree_X, natDegree_X_pow]; norm_num),
        natDegree_X_pow]
    rw [h1]
    have h2 : ((Polynomial.X : Polynomial F) ^ 5 - Polynomial.X)
        = Polynomial.X * ((Polynomial.X : Polynomial F) ^ 4 - 1) := by ring
    rw [h2, reverse_X_mul]
    have h3 : ((Polynomial.X : Polynomial F) ^ 4 - 1)
        = (Polynomial.X : Polynomial F) ^ 4 + Polynomial.C (-1) := by
      rw [map_neg, map_one]; ring
    rw [h3, reverse_add_C]
    have h4 : ((Polynomial.X : Polynomial F) ^ 4).natDegree = 4 := natDegree_X_pow 4
    rw [h4]
    have h5 : (Polynomial.X ^ 4 : Polynomial F).reverse = 1 := by
      rw [show (Polynomial.X ^ 4 : Polynomial F) = 1 * Polynomial.X ^ 4 from by ring,
        reverse_mul_X_pow,
        show (1 : Polynomial F) = Polynomial.C 1 from (map_one Polynomial.C).symm, reverse_C]
    rw [h5]
    rw [map_neg, map_one]
    first | refl_ring1 | ring
  rw [← hrev]
  exact irreducible_reverse _ (by simpa using ha0) hQ

theorem irreducible_sdualAS2_quintic (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] :
    Irreducible ((Polynomial.C (Work.MotV.fAS 𝕜) : Polynomial (RatFunc 𝕜)) * Polynomial.X ^ 5
      - Polynomial.X ^ 4 + 1) := by
  refine irreducible_quintic (RatFunc 𝕜) (Work.MotV.fAS 𝕜) ?_
  intro b hb
  refine (Work.MotV5.CensusAux.fAS_notMem_pe 𝕜) ⟨-b, ?_⟩
  calc (-b) ^ 5 - (-b) = -(b ^ 5 - b) := by ring
    _ = -(-(Work.MotV.fAS 𝕜)) := by rw [hb]
    _ = Work.MotV.fAS 𝕜 := by ring

end Work.MotAS
