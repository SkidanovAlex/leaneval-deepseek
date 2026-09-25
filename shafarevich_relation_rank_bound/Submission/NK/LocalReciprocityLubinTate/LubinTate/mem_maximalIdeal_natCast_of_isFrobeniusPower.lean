import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.Series

/-!
# The Frobenius power `q` lies in the maximal ideal

Let `F` be a nonarchimedean local field with ring of integers `𝒪[F]`.  Suppose `π ∈ 𝒪[F]` and
`q ≥ 2` satisfy `IsFrobeniusPower π q`, i.e. there is a prime `p` with
`CharP (𝒪[F] ⧸ (π)) p` and `q = p ^ k`.

Then `q ∈ 𝔪[F]`.  Indeed:

* `(π) ≠ ⊤`: if `(π)` were the whole ring the quotient `𝒪[F] ⧸ (π)` would be the zero ring, and
  `CharP R p` would force `p ∣ 1`, contradicting primality of `p`;
* `q ∈ (π)`: the residue characteristic `p` of `𝒪[F] ⧸ (π)` is `0` there, hence so is
  `q = p ^ k` (`k ≥ 1`, since `q ≥ 2`);
* a proper ideal of a local ring is contained in the maximal ideal, which is the set of nonunits.

This is the third coefficient-ring condition of the Lubin–Tate construction: in
`NK.LocalReciprocityLubinTate.LubinTate.Integers` the Lubin–Tate series `πX + X^q` is built with
`q = #𝓀[F]`, and the reduction-theoretic arguments (`NK.LocalReciprocityLubinTate.ModPi`) need
`q ∈ 𝔪[F]`.
-/

set_option linter.style.haveILetI false

universe u

namespace NK.LocalReciprocityLubinTate.LubinTate

/-- **If `IsFrobeniusPower π q` holds with `q ≥ 2` then `q` lies in the maximal ideal of the ring of
integers.**  Equivalently: a natural number `≥ 2` that is the cardinality of the residue ring
`𝒪[F] ⧸ (π)` (which holds when the residue ring has a prime characteristic and `q` is a power of it)
is a non-unit of `𝒪[F]`. -/
theorem mem_maximalIdeal_natCast_of_isFrobeniusPower (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (π : (↥(ValuativeRel.valuation F).integer)) (q : ℕ) (hq : 2 ≤ q)
    (h : NK.LocalReciprocityLubinTate.IsFrobeniusPower π q) :
    (q : ↥(ValuativeRel.valuation F).integer) ∈
      IsLocalRing.maximalIdeal ↥(ValuativeRel.valuation F).integer := by
  obtain ⟨p, hp, hchar, k, hk⟩ := h
  haveI : CharP (↥(ValuativeRel.valuation F).integer ⧸ Ideal.span {π}) p := hchar
  -- `q = p ^ k` with `k ≥ 1`, since `q ≥ 2`.
  have hk1 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    omega
  -- The residue characteristic `p` of `𝒪[F] ⧸ (π)` vanishes there, hence so does `q = p ^ k`.
  have hq0 : (q : ↥(ValuativeRel.valuation F).integer ⧸ Ideal.span {π}) = 0 := by
    rw [hk, Nat.cast_pow, CharP.cast_eq_zero, zero_pow hk1]
  -- Therefore `q ∈ (π)`.
  have hqmem : (q : ↥(ValuativeRel.valuation F).integer) ∈ Ideal.span {π} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [map_natCast (Ideal.Quotient.mk (Ideal.span {π})) q]
    exact hq0
  -- `(π)` is a proper ideal: otherwise the quotient would be the zero ring, where `CharP R p`
  -- would give `p ∣ 1`.
  have hne_top : Ideal.span {π} ≠ ⊤ := by
    intro htop
    haveI : Subsingleton (↥(ValuativeRel.valuation F).integer ⧸ Ideal.span {π}) :=
      Ideal.Quotient.subsingleton_iff.mpr htop
    have h1 : (1 : ↥(ValuativeRel.valuation F).integer ⧸ Ideal.span {π}) = 0 :=
      Subsingleton.elim _ _
    refine hp.not_dvd_one ?_
    have h1' : ((1 : ℕ) : ↥(ValuativeRel.valuation F).integer ⧸ Ideal.span {π}) = 0 := by
      simpa using h1
    exact (CharP.cast_eq_zero_iff _ p 1).mp h1'
  -- In a local ring the maximal ideal is the set of nonunits, and a proper ideal contains no unit.
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  exact hne_top (Ideal.eq_top_of_isUnit_mem _ hqmem hunit)

end NK.LocalReciprocityLubinTate.LubinTate
