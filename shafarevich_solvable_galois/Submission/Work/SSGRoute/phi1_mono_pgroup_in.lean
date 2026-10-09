import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.phi1_mono_base
import Submission.Work.SSGRoute.phi1_mono_step_in_clean
import Submission.Work.SSGRoute.natCard_cokernel_lt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester): read `DESIGN_FIX.md` §1 and the docstrings of
`phi1_mono_step_in` (E5s) and `phi1_mono_pgroup` (the lane's helper base).

# E5Ω `phi1_mono_pgroup_in` — dévissage: `φ¹` is injective for `p`-groups, levels inside `Ω`

If `Gal(K/k)` is a `p`-group and `μ_p ⊆ k`, then `φ¹` is injective on `Ext¹_G(M, C_K)` for every
finite `p`-torsion `Gal(K/k)`-module `M`, tested on the finite Galois levels `K ≤ L ≤ Ω` of a fixed
algebraically closed `Ω ⊇ K` (`PhiOneVanishesIn Ω`).

**Proof.** Strong induction on `Nat.card M`.  For `M = 0` the `Ext` group is a subsingleton
(`Rep.isZero_iff`); for `M ≠ 0`, the `p`-group `Gal(K/k)` has a non-zero fixed vector, giving a
short exact sequence `0 → 𝔽_p → M → M₂ → 0` (`exists_trivial_sub_shortExact`) with
`Nat.card M₂ < Nat.card M` (`natCard_cokernel_lt`), and E5s (`phi1_mono_step_in`) with the
induction hypothesis at `M₂` finishes.

The old, type-indexed `Work.SSGRoute.phi1_mono_pgroup` follows by instantiating the
type-quantifier at `↥L` (`phiOneVanishes_to_In`). -/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

private theorem phi1_mono_pgroup_in_aux (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower k K Ω]
    (ζ : k) (hζ : IsPrimitiveRoot ζ p) (hG : IsPGroup p (K ≃ₐ[k] K)) :
    ∀ (n : ℕ) (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M], Nat.card M = n →
      (∀ m : M, p • m = 0) →
      ∀ (x : Abelian.Ext M (classesK k K) 1), PhiOneVanishesIn Ω x → x = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M _ hcard hM x hx
    by_cases hsub : Subsingleton M
    · -- `M` is a zero object, so `Ext¹(M, C_K)` is a subsingleton
      have hz : CategoryTheory.Limits.IsZero M := (Rep.isZero_iff Coeff (K ≃ₐ[k] K) M).mpr hsub
      have hid : (𝟙 M : M ⟶ M) = 0 := (CategoryTheory.Limits.IsZero.iff_id_eq_zero M).mp hz
      have heq : x = (Abelian.Ext.mk₀ (𝟙 M)).comp x (zero_add 1) :=
        (Abelian.Ext.mk₀_id_comp x).symm
      rw [heq, hid, Abelian.Ext.mk₀_zero]
      exact Abelian.Ext.zero_comp M 0 x 1 (zero_add 1)
    · haveI : Nontrivial M := not_subsingleton_iff_nontrivial.mp hsub
      obtain ⟨M₂, i, π, hcond, hS, hFin₂, hp₂⟩ :=
        exists_trivial_sub_shortExact (G := K ≃ₐ[k] K) p hG M hM ‹Nontrivial M›
      -- the short exact sequence `0 → 𝔽_p → M → M₂ → 0`, its cardinality bookkeeping and E5s
      have hcard₁ : Nat.card (Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p)) = p := by
        rw [Nat.card_eq_fintype_card, ZMod.card]
      have hlt : Nat.card (ShortComplex.mk i π hcond).X₃ <
          Nat.card (ShortComplex.mk i π hcond).X₂ :=
        natCard_cokernel_lt hS hcard₁
      have hIH : ∀ z : Abelian.Ext (ShortComplex.mk i π hcond).X₃ (classesK k K) 1,
          PhiOneVanishesIn Ω z → z = 0 := by
        intro z hz
        refine ih (Nat.card (ShortComplex.mk i π hcond).X₃) ?_ (ShortComplex.mk i π hcond).X₃
          rfl hp₂ z hz
        rw [← hcard]
        exact hlt
      exact phi1_mono_step_in_in p k K Ω ζ hζ (ShortComplex.mk i π hcond) hS (Iso.refl _) hIH x hx

/-- **E5Ω.** Dévissage: if `Gal(K/k)` is a `p`-group and `μ_p ⊆ k`, then `φ¹` is injective on
`Ext¹_G(M, C_K)` for every finite `p`-torsion `Gal(K/k)`-module `M`, tested on the levels of a
fixed algebraic closure `Ω ⊇ K` (strong induction on `|M|` along `0 → 𝔽_p → M → M₂ → 0`, with
the step `Work.SSGRoute.phi1_mono_step_in`). -/
theorem phi1_mono_pgroup_in (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K] (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : k) (hζ : IsPrimitiveRoot ζ p) (hG : IsPGroup p (K ≃ₐ[k] K))
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (x : Abelian.Ext M (classesK k K) 1) (hx : PhiOneVanishesIn Ω x) : x = 0 :=
  phi1_mono_pgroup_in_aux p k K Ω ζ hζ hG (Nat.card M) M rfl hM x hx

end Work.SSGRoute
