import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.place_basics
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open _root_.SSGRoute
open scoped Pointwise

/-!
# `T¹`-places are stable under conjugation

The set `T¹ = Ram(K/ℚ) ∪ {p}` really is a set of *primes of ℚ*: whether a place `A` of `ℚ̄` lies in
`T¹` depends only on the prime of `ℚ` below `A`, i.e. on the `G_ℚ`-orbit of `A`.  Consequently
`IsT1Place p K` is invariant under the conjugation action of `G_ℚ = ℚ̄ ≃ₐ[ℚ] ℚ̄` on the places of
`ℚ̄`.

Both ingredients are bookkeeping about that action:

* finiteness (`IsFinPlace`) and ramification (`IsRamifiedIn`, which uses that `K.fixingSubgroup` is
  normal because `K/ℚ` is normal) are conjugation invariant — these are
  `isFinPlace_smul_iff` and `isRamifiedIn_conj` of `place_basics`;
* the condition `A.valuation (p : ℚ̄) < 1` only involves the rational number `p`, which is fixed by
  every `σ ∈ G_ℚ`, so it too is conjugation invariant.
-/

section Places

variable {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]

/-- The valuation of a translated place at a translated element: `(g • A).valuation (g • x) < 1`
if and only if `A.valuation x < 1`.  (The version `smul_valuation_lt_one` of `place_basics` is the
special case `x ∈ A`; here `x` is arbitrary, which we need for the rational number `p`, that in
general need not be integral at `A`.) -/
theorem valuation_lt_one_smul_iff (g : Ω ≃ₐ[k] Ω) (A : ValuationSubring Ω) (x : Ω) :
    (g • A).valuation (g • x) < 1 ↔ A.valuation x < 1 := by
  by_cases hx : x ∈ A
  · exact smul_valuation_lt_one g A x hx
  · have hgx : g • x ∉ g • A :=
      fun hh => hx (ValuationSubring.smul_mem_pointwise_smul_iff.mp hh)
    refine iff_of_false (fun hlt => hgx ?_) (fun hlt => hx ?_)
    · exact ValuationSubring.mem_of_valuation_le_one (g • A) (g • x) (le_of_lt hlt)
    · exact ValuationSubring.mem_of_valuation_le_one A x (le_of_lt hlt)

end Places

/-- For a normal extension `K/ℚ` of `ℚ̄`, the fixing subgroup `G_K = K.fixingSubgroup` is normal in
`G_ℚ`.  It is the kernel of the restriction `G_ℚ →* Gal(K/ℚ)` (`restrictNormalHom_ker`), and
kernels of group homomorphisms are normal. -/
theorem fixingSubgroup_normal_of_normal (K : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K] :
    K.fixingSubgroup.Normal := by
  have hker : (AlgEquiv.restrictNormalHom ↥K).ker = K.fixingSubgroup :=
    @IntermediateField.restrictNormalHom_ker ℚ SSGRoute.QBar _ _ _ K ‹Normal ℚ ↥K›
  rw [← hker]
  exact MonoidHom.normal_ker _

/-- `T¹`-places over a normal number field `K` are stable under conjugation of the place. -/
theorem isT1Place_of_isConjPlace (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K]
    {A₀ A : ValuationSubring SSGRoute.QBar} (h : SSGRoute.IsConjPlace ℚ A₀ A)
    (hA₀ : SSGRoute.IsT1Place p K A₀) : SSGRoute.IsT1Place p K A := by
  obtain ⟨σ, hσ⟩ := h
  rw [← hσ]
  obtain ⟨hfin, hv | hram⟩ := hA₀
  · refine ⟨(isFinPlace_smul_iff A₀ σ).mpr hfin, Or.inl ?_⟩
    have hp : σ • (p : SSGRoute.QBar) = (p : SSGRoute.QBar) := by
      rw [AlgEquiv.smul_def, map_natCast]
    have key := valuation_lt_one_smul_iff σ A₀ (p : SSGRoute.QBar)
    rw [hp] at key
    exact key.mpr hv
  · refine ⟨(isFinPlace_smul_iff A₀ σ).mpr hfin, Or.inr ?_⟩
    exact (isRamifiedIn_conj K (fixingSubgroup_normal_of_normal K) A₀ σ).mpr hram

end Work.SSGRoute
