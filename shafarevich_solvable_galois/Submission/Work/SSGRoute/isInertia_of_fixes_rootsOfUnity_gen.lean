import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.RamificationGroup
import Submission.Work.SSGRoute.charP_residueField_isFinPlace
import Submission.Work.SSGRoute.isUnit_natCast_of_not_dvd_resCharAt
import Submission.Work.SSGRoute.residueField_residue_pow_eq_one_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Fixing the prime-to-`p` roots of unity forces inertia (general number field)

Let `k` be a number field, `Ω` an algebraic closure of `k`, `A` a finite place of `Ω` over `k`
(`SSGRoute.IsFinPlace k A`: the restriction of `A` to `k` is a proper valuation subring) and
`p` the residue characteristic of `A`, i.e. the characteristic of its residue field
(`hchar : CharP (IsLocalRing.ResidueField ↥A) p`, which by
`Work.SSGRoute.charP_residueField_isFinPlace` is `resCharAt (primeOf A hA)`).

This file proves `Work.SSGRoute.isInertia_of_fixes_rootsOfUnity_gen`: an element `σ` of the
decomposition group `D_A` of `A` which fixes every root of unity of `Ω` of order prime to `p`
lies in the inertia group `I_A = {σ ∈ D_A : σ acts trivially on the residue field of A}`.

The argument is the general-number-field form of `Work.SSGRoute.isInertia_fixesRoots_clean`
(the case `k = ℚ`, `Ω = ℚ̄`):

* the residue field `κ` of `A` is the algebraic closure `𝔽̄_p` of `𝔽_p`, so every element of `κˣ`
  is a root of unity of order prime to `p` (`Work.SSGRoute.residueField_residue_pow_eq_one_gen`);
* the integers prime to `p` are units of `↥A`
  (`Work.SSGRoute.isUnit_natCast_iff_not_dvd_resCharAt`), so reduction modulo the maximal ideal is
  injective on the `N`-torsion of `↥A` for such `N` (`NK.ResidueFrob.residue_injective_on_torsion`);
* a primitive `N`-th root of unity `ζ` of `Ω` (`NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed`)
  lies in `↥A` (`NK.TameStructureDeep.Tame.mem_valuationSubring_of_isPrimitiveRoot`), reduces to a
  primitive `N`-th root of unity of `κ` (`NK.ResidueFrob.isPrimitiveRoot_residue`), and is fixed by
  `σ` (the hypothesis `hfix`); since every `N`-th root of unity of `κ` is a power of this one, `σ`
  acts trivially on the residue field.  The valuation inequality `A.valuation (σ x - x) < 1` for
  `x ∈ A` is the translation of this residue-triviality
  (`ValuationSubring.valuation_lt_one_iff`).
-/

namespace Work.SSGRoute

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

theorem isInertia_of_fixes_rootsOfUnity_gen
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (p : ℕ)
    (hchar : CharP (IsLocalRing.ResidueField ↥A) p)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ SSGRoute.decomp k A)
    (hfix : ∀ (n : ℕ), ¬ p ∣ n → ∀ ζ : Ω, IsPrimitiveRoot ζ n → σ ζ = ζ) :
    SSGRoute.IsInertia k A σ := by
  -- `Ω` is an algebraic closure of the number field `k`, hence of characteristic `0` and
  -- separably closed.
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI : IsSepClosure k Ω := IsSepClosure.of_isAlgClosure_of_perfectField k Ω
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed k
  -- Every element of the residue field of `A` is `0` or a root of unity of order prime to `p`.
  have hres : ∀ a : ↥A, IsLocalRing.residue ↥A a = 0 ∨
      ∃ N : ℕ, 0 < N ∧ ¬ p ∣ N ∧ (IsLocalRing.residue ↥A a) ^ N = 1 :=
    fun a => residueField_residue_pow_eq_one_gen k Ω A hA p hchar a
  -- `p` is the residue characteristic of the prime of `k` below `A`, ...
  have hpchar : NK.TameStructureDeep.Tame.resCharAt (Submission.NeukirchUchida.primeOf A hA) = p :=
    CharP.eq _ (charP_residueField_isFinPlace k Ω A hA) hchar
  -- ... so every natural number prime to `p` is a unit of the valuation ring `↥A`.
  have hunit : ∀ n : ℕ, ¬ p ∣ n → IsUnit (n : ↥A) := by
    intro n hn
    rw [← hpchar] at hn
    exact (isUnit_natCast_iff_not_dvd_resCharAt k Ω A hA n).mpr hn
  refine ⟨hσ, ?_⟩
  intro x hx
  -- `σ` acts on the valuation ring `↥A` through its image in the decomposition group.
  let g : ↥(A.decompositionSubgroup k) := ⟨σ, hσ⟩
  -- `σ` acts trivially on the residue field of `A`.
  have hfixres : ∀ b : ↥A, IsLocalRing.residue ↥A (g • b) = IsLocalRing.residue ↥A b := by
    intro b
    rw [IsLocalRing.ResidueField.residue_smul]
    rcases hres b with h0 | ⟨N, hNpos, hNp, hNpow⟩
    · rw [h0, smul_zero]
    · -- a primitive `N`-th root of unity `ζ₀` of `Ω`, and its residue in `↥A`
      haveI : NeZero N := ⟨hNpos.ne'⟩
      haveI : NeZero (N : Ω) := ⟨Nat.cast_ne_zero.mpr hNpos.ne'⟩
      obtain ⟨ζ₀, hζ₀⟩ :=
        NK.LocalAnabelian.exists_isPrimitiveRoot_of_isSepClosed (K := Ω) (n := N)
      have hζ₀mem : ζ₀ ∈ A :=
        NK.TameStructureDeep.Tame.mem_valuationSubring_of_isPrimitiveRoot A hζ₀ hNpos.ne'
      let ζ₀A : ↥A := ⟨ζ₀, hζ₀mem⟩
      have hζ₀A : IsPrimitiveRoot ζ₀A N :=
        (IsPrimitiveRoot.coe_submonoidClass_iff (N := A) (ζ := ζ₀A)).mp hζ₀
      have hunitN : IsUnit (N : ↥A) := hunit N hNp
      have hη : IsPrimitiveRoot (IsLocalRing.residue ↥A ζ₀A) N :=
        NK.ResidueFrob.isPrimitiveRoot_residue hζ₀A
          (fun w hw hres' => NK.ResidueFrob.residue_injective_on_torsion hunitN hw hres')
      -- the residue of `b` is a power of the residue of `ζ₀A`
      obtain ⟨j, -, hj⟩ := hη.eq_pow_of_pow_eq_one hNpow
      -- `σ` fixes `ζ₀`, hence its residue
      have hgζ : g • ζ₀A = ζ₀A := by
        apply Subtype.ext
        rw [NK.Ramification.coe_smul]
        exact hfix N hNp ζ₀ hζ₀
      rw [← hj]
      calc (MulSemiringAction.toRingEquiv ↥(A.decompositionSubgroup k)
              (IsLocalRing.ResidueField ↥A)) g ((IsLocalRing.residue ↥A) ζ₀A ^ j)
          = (MulSemiringAction.toRingEquiv ↥(A.decompositionSubgroup k)
              (IsLocalRing.ResidueField ↥A)) g ((IsLocalRing.residue ↥A) ζ₀A) ^ j := by
            rw [map_pow]
        _ = ((IsLocalRing.residue ↥A) (g • ζ₀A)) ^ j := by
            rw [MulSemiringAction.toRingEquiv_apply_apply,
              ← IsLocalRing.ResidueField.residue_smul ↥(A.decompositionSubgroup k) g ζ₀A]
        _ = ((IsLocalRing.residue ↥A) ζ₀A) ^ j := by rw [hgζ]
  -- residue-triviality on `↥A` is the valuation inequality defining `I_A`
  let w : ↥A := g • (⟨x, hx⟩ : ↥A) - ⟨x, hx⟩
  have hmem : w ∈ IsLocalRing.maximalIdeal ↥A := by
    change g • (⟨x, hx⟩ : ↥A) - ⟨x, hx⟩ ∈ IsLocalRing.maximalIdeal ↥A
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hfixres, sub_self]
  have hlt : A.valuation (w : Ω) < 1 :=
    (ValuationSubring.valuation_lt_one_iff A w).mp hmem
  simpa [w, NK.Ramification.coe_smul] using hlt

end Work.SSGRoute
