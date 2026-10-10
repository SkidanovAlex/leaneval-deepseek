import Mathlib.FieldTheory.KummerExtension
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Order.Star.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

/-!
# A finite Galois extension of a local field with degree divisible by a fixed power of `p`

This generalises `Work.SSGRoute.PTCore.exists_galois_degree_p_dvd_of_uniformizer` from `p` to
`p ^ N`.  Let `F` be a field of characteristic zero equipped with a valuation
`w : F → WithZero (Multiplicative ℤ)` and let `π` be a uniformizer, i.e. `w π = exp (-1)`.
Then there is a finite Galois extension `E` of `F` (an intermediate field of the algebraic
closure) with `p ^ N ∣ [E : F]`.

The construction is the splitting field of `X ^ (p ^ N) - π`; the norm/valuation computation
`N(α) ^ (p^N) = π ^ [E : F]` gives `p^N • log (w (N α)) = [E : F] • (-1)`, hence `p^N ∣ [E : F]`.
-/

namespace Work.SSGRoute.PTembedding

open Polynomial

/-- Arithmetic: if `m • k = e • (-1)` in `ℤ`, then `m ∣ e`. -/
private lemma dvd_of_pow_nsmul_eq_neg {m e : ℕ} {k : ℤ} (h : m • k = e • (-1 : ℤ)) : m ∣ e := by
  have h' : (m : ℤ) * k = -(e : ℤ) := by simpa [nsmul_eq_mul] using h
  refine Int.ofNat_dvd.mp ⟨-k, ?_⟩
  rw [mul_neg, h', neg_neg]

/-- **A finite Galois extension of degree divisible by `p ^ N`, from a uniformizer.**
Let `F` be a field of characteristic zero equipped with a valuation `w` with values in
`ℤᵐ⁰ = WithZero (Multiplicative ℤ)`, and let `π` be a uniformizer, i.e. `w π = exp (-1)`.
Then there is a finite Galois extension `E` of `F` (an intermediate field of the algebraic
closure) with `p ^ N ∣ [E : F]`. -/
theorem exists_galois_degree_pow_dvd_of_uniformizer (p N : ℕ) [Fact p.Prime] {F : Type*} [Field F]
    [CharZero F] (w : Valuation F (WithZero (Multiplicative ℤ))) (π : F)
    (hπ : w π = WithZero.exp (-1)) :
    ∃ E : IntermediateField F (AlgebraicClosure F),
      FiniteDimensional F ↥E ∧ IsGalois F ↥E ∧ p ^ N ∣ Module.finrank F ↥E := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hnpos : 0 < p ^ N := pow_pos hp.pos N
  have hnne : ((p ^ N : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero N hp.ne_zero)
  have hπne : π ≠ 0 := (Valuation.ne_zero_iff w).mp (by rw [hπ]; exact WithZero.exp_ne_zero)
  let E : IntermediateField F (AlgebraicClosure F) :=
    IntermediateField.adjoin F ((X ^ (p ^ N) - C π).rootSet (AlgebraicClosure F))
  haveI hsplit : Polynomial.IsSplittingField F ↥E (X ^ (p ^ N) - C π) :=
    IntermediateField.adjoin_rootSet_isSplittingField (p := X ^ (p ^ N) - C π) (IsAlgClosed.splits _)
  haveI hfin : FiniteDimensional F ↥E :=
    Polynomial.IsSplittingField.finiteDimensional ↥E (X ^ (p ^ N) - C π)
  have hsep : (X ^ (p ^ N) - C π).Separable := separable_X_pow_sub_C π hnne hπne
  haveI hgal : IsGalois F ↥E :=
    IsGalois.of_separable_splitting_field (p := X ^ (p ^ N) - C π) hsep
  haveI : Module.Free F ↥E := Module.Free.of_divisionRing F ↥E
  haveI : NeZero (p ^ N) := ⟨hnpos.ne'⟩
  let α : ↥E := rootOfSplitsXPowSubC (n := p ^ N) hnpos π ↥E
  have hα : α ^ (p ^ N) = algebraMap F ↥E π := rootOfSplitsXPowSubC_pow (n := p ^ N) π ↥E
  have hnorm : ((Algebra.norm F) α) ^ (p ^ N) = π ^ Module.finrank F ↥E := by
    rw [← map_pow, hα, Algebra.norm_algebraMap]
  have hw : (w ((Algebra.norm F) α)) ^ (p ^ N) = (w π) ^ Module.finrank F ↥E := by
    simpa using congrArg w hnorm
  rw [hπ] at hw
  have hlog : (p ^ N) • WithZero.log (w ((Algebra.norm F) α)) =
      Module.finrank F ↥E • (-1 : ℤ) := by
    have h := congrArg WithZero.log hw
    simpa only [WithZero.log_pow, WithZero.log_exp] using h
  exact ⟨E, hfin, hgal, dvd_of_pow_nsmul_eq_neg hlog⟩

end Work.SSGRoute.PTembedding
