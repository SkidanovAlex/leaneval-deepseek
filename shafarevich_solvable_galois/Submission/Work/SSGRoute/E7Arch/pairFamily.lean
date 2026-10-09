/-
# The archimedean (real-place) half of `G1` as a *family* in the coefficient module

`Work.SSGRoute.local_tate_duality_archimedean` proves local Tate duality at an involution `c`
(`c ^ 2 = 1`, the real-place case): there is a pairing on `H¹(⟨c⟩, M) × H¹(⟨c⟩, M^∨(1))` with
clauses (1),(2) (additivity), (3) (zero on a coboundary) and (4) (perfectness), *for a single
coefficient module* `M`; and `Work.SSGRoute.archPair_nondegenerate` reproves the perfectness clauses
for the *explicit* pairing `Ach.archPair`.

The consumers (`Work.SSGRoute.PTembedding.localTatePairing_canonical` = node `E7`,
`Work.SSGRoute.canonical_localPairing_with_reciprocity` = node `G1`, consumed by
`Work.SSGRoute.coker_obstruction`) need more: a *single* family `pair M H a b` over **all** finite
`𝔽_p[Gal(K/k)]`-modules `M`, satisfying the clauses (1)–(4) at every local group **and** the
naturality clause (5) `pair M₂ H (f ∘ a) b = pair M H a (f' ∘ b)` in the coefficient module (`f`
equivariant, `f'` the transpose of `f ⊗ id_T`).  Clause (5) is what makes the obstruction class
universal: it is the `hnat` slot of `H1Pair.glueable_of_inputs` and the identity used by
`H1Pair.transfer_sum_eq_zero`, so a per-module `∃` does not suffice.

This file supplies exactly that at the involution groups:

* `pairArchFamily` — the family `M ↦ (H ↦ archPair …)` cut down to the involution groups (it is `0`
  off them, where its values are never used);
* `cup_*` — clauses (1)–(3) and (5) for the explicit `archPair`, recomputed from its formula as in
  the proof of `local_tate_duality_archimedean`;
* `pairArchFamily_pairClauses` — the bundle (1)–(4) for the family, in the shape of the `hloc`
  hypothesis of `Work.SSGRoute.pt_selmer_relaxed` (`H1Pair.PairClauses`), with perfectness from
  `archPair_nondegenerate`;
* `pairArchFamily_naturality` — clause (5) at the involution groups.

Clause (6) (orthogonality at an unramified place) is a finite-place clause and does not apply here;
reciprocity (clause (7)) is not a consequence of the clauses and remains a separate input.
-/
import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.LTDArch.Defs
import Submission.Work.SSGRoute.LTDArch.AuxLemmas
import Submission.Work.SSGRoute.local_tate_duality_archimedean
import Submission.Work.SSGRoute.archPair_nondegenerate
import Submission.Work.SSGRoute.H1Pair.Clauses
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open SSGRoute
open scoped TensorProduct

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.SSGRoute.E7Arch

attribute [local instance] Classical.propDecidable

/-- **`T` is fixed by `Gal(Ω/k)` when `p = 2`** (a primitive second root of unity is `-1`). -/
theorem tTrivial_of_eq_two     (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) (hp : p = 2) (σ : Ω ≃ₐ[k] Ω) (t : T) :
    SSGRoute.res k K σ • t = t := by
  have hfix : σ • ζ = ζ := by
    have h2 : ζ = -1 := by
      have hpow : ζ ^ 2 = 1 := by rw [← hp]; exact hζ.pow_eq_one
      have hne : ζ ≠ 1 := hζ.ne_one (by have := (Fact.out : p.Prime).two_le; omega)
      have hmul : (ζ - 1) * (ζ + 1) = 0 := by linear_combination hpow
      rcases mul_eq_zero.mp hmul with h | h
      · exact absurd (sub_eq_zero.mp h) hne
      · exact eq_neg_of_add_eq_zero_left h
    rw [h2]
    simp
  have h := hT.2 σ 1 (by rw [hfix, pow_one]) t
  simpa using h
/-- Clause (1): `archPair` is additive in its first variable. -/
theorem cup_add_left     (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) {M : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (c : Ω ≃ₐ[k] Ω) (a a' : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)) :
    Ach.archPair p (Ω ≃ₐ[k] Ω) M T hT.1 c (a + a') b =
      Ach.archPair p (Ω ≃ₐ[k] Ω) M T hT.1 c a b +
        Ach.archPair p (Ω ≃ₐ[k] Ω) M T hT.1 c a' b := by
  by_cases hp2 : p = 2
  · rw [Ach.archPair_apply_of_eq_two (h := hT.1) p (Ω ≃ₐ[k] Ω) M T hp2 c (a + a') b,
      Ach.archPair_apply_of_eq_two (h := hT.1) p (Ω ≃ₐ[k] Ω) M T hp2 c a b,
      Ach.archPair_apply_of_eq_two (h := hT.1) p (Ω ≃ₐ[k] Ω) M T hp2 c a' b]
    simp only [Pi.add_apply, TensorProduct.add_tmul, map_add]
  · rw [Ach.archPair_apply_of_ne_two (h := hT.1) p (Ω ≃ₐ[k] Ω) M T hp2 c (a + a') b,
      Ach.archPair_apply_of_ne_two (h := hT.1) p (Ω ≃ₐ[k] Ω) M T hp2 c a b,
      Ach.archPair_apply_of_ne_two (h := hT.1) p (Ω ≃ₐ[k] Ω) M T hp2 c a' b, add_zero]
/-- Clause (2): `archPair` is additive in its second variable. -/
theorem cup_add_right     (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) {M : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (c : Ω ≃ₐ[k] Ω) (a : (Ω ≃ₐ[k] Ω) → M)
    (b b' : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)) :
    Ach.archPair p (Ω ≃ₐ[k] Ω) M T hT.1 c a (b + b') =
      Ach.archPair p (Ω ≃ₐ[k] Ω) M T hT.1 c a b +
        Ach.archPair p (Ω ≃ₐ[k] Ω) M T hT.1 c a b' := by
  by_cases hp2 : p = 2
  · rw [Ach.archPair_apply_of_eq_two (h := hT.1) p (Ω ≃ₐ[k] Ω) M T hp2 c a (b + b'),
      Ach.archPair_apply_of_eq_two (h := hT.1) p (Ω ≃ₐ[k] Ω) M T hp2 c a b,
      Ach.archPair_apply_of_eq_two (h := hT.1) p (Ω ≃ₐ[k] Ω) M T hp2 c a b']
    simp only [Pi.add_apply, LinearMap.add_apply]
  · rw [Ach.archPair_apply_of_ne_two (h := hT.1) p (Ω ≃ₐ[k] Ω) M T hp2 c a (b + b'),
      Ach.archPair_apply_of_ne_two (h := hT.1) p (Ω ≃ₐ[k] Ω) M T hp2 c a b,
      Ach.archPair_apply_of_ne_two (h := hT.1) p (Ω ≃ₐ[k] Ω) M T hp2 c a b', add_zero]
/-- Clause (3), first variable: `archPair` vanishes on a coboundary. -/
theorem cup_coboundary_left     (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) {M : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1)
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧
      SSGRoute.IsLocConstOn (Subgroup.zpowers c) b)
    (hab : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) a) :
    Ach.archPair p (Ω ≃ₐ[k] Ω) M T hT.1 c a b = 0 := by
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨-, m, hm⟩ := (Ach.isCoboundaryOn_zpowers_iff (SSGRoute.res k K) c hc a).mp hab
    obtain ⟨-, hbc⟩ := (Ach.isCocycleOn_zpowers_iff (SSGRoute.res k K) c hc b).mp hb.1
    have hσinv : (SSGRoute.res k K c)⁻¹ = SSGRoute.res k K c :=
      inv_eq_of_mul_eq_one_right (by rw [← map_mul, ← pow_two, hc, map_one])
    have hψzero : (ArchAux.onePlus (p := 2) (SSGRoute.res k K c)).dualMap (b c) = 0 := by
      rw [ArchAux.dualMap_onePlus (SSGRoute.res k K c) hσinv, add_comm]
      exact hbc
    rw [Ach.archPair_apply_of_eq_two (h := hT.1) 2 (Ω ≃ₐ[k] Ω) M T rfl c a b]
    have hkey : a c = SSGRoute.res k K c • m + m := by
      rw [hm, Ach.sub_eq_add_of_eq_two 2 rfl]
    have hsmul : (SSGRoute.res k K c • m) ⊗ₜ[ZMod 2] Ach.t0 2 T hT.1 =
        SSGRoute.res k K c • (m ⊗ₜ[ZMod 2] Ach.t0 2 T hT.1) := by
      rw [show SSGRoute.res k K c • (m ⊗ₜ[ZMod 2] Ach.t0 2 T hT.1) =
          (SSGRoute.res k K c • m) ⊗ₜ[ZMod 2] (SSGRoute.res k K c • Ach.t0 2 T hT.1) from rfl,
        tTrivial_of_eq_two 2 k Ω K ζ hζ hζK T hT rfl c (Ach.t0 2 T hT.1)]
    have h2 : a c ⊗ₜ[ZMod 2] Ach.t0 2 T hT.1 =
        ArchAux.onePlus (p := 2) (SSGRoute.res k K c) (m ⊗ₜ[ZMod 2] Ach.t0 2 T hT.1) := by
      rw [hkey, ArchAux.onePlus_apply, TensorProduct.add_tmul, ← hsmul, add_comm]
    rw [h2, ← LinearMap.dualMap_apply, hψzero, LinearMap.zero_apply]
  · rw [Ach.archPair_apply_of_ne_two (h := hT.1) p (Ω ≃ₐ[k] Ω) M T hp2 c a b]
/-- Clause (3), second variable: `archPair` vanishes on a coboundary. -/
theorem cup_coboundary_right     (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) {M : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1)
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a ∧
      SSGRoute.IsLocConstOn (Subgroup.zpowers c) a)
    (hbb : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b) :
    Ach.archPair p (Ω ≃ₐ[k] Ω) M T hT.1 c a b = 0 := by
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨-, ψ₀, hψ₀⟩ := (Ach.isCoboundaryOn_zpowers_iff (SSGRoute.res k K) c hc b).mp hbb
    obtain ⟨-, hac⟩ := (Ach.isCocycleOn_zpowers_iff (SSGRoute.res k K) c hc a).mp ha.1
    have hσinv : (SSGRoute.res k K c)⁻¹ = SSGRoute.res k K c :=
      inv_eq_of_mul_eq_one_right (by rw [← map_mul, ← pow_two, hc, map_one])
    rw [Ach.archPair_apply_of_eq_two (h := hT.1) 2 (Ω ≃ₐ[k] Ω) M T rfl c a b]
    have hbc : b c = SSGRoute.res k K c • ψ₀ + ψ₀ := by
      rw [hψ₀, Ach.sub_eq_add_of_eq_two 2 rfl]
    have hsmul : (SSGRoute.res k K c • a c) ⊗ₜ[ZMod 2] Ach.t0 2 T hT.1 =
        SSGRoute.res k K c • (a c ⊗ₜ[ZMod 2] Ach.t0 2 T hT.1) := by
      rw [show SSGRoute.res k K c • (a c ⊗ₜ[ZMod 2] Ach.t0 2 T hT.1) =
          (SSGRoute.res k K c • a c) ⊗ₜ[ZMod 2] (SSGRoute.res k K c • Ach.t0 2 T hT.1) from rfl,
        tTrivial_of_eq_two 2 k Ω K ζ hζ hζK T hT rfl c (Ach.t0 2 T hT.1)]
    have hx : SSGRoute.res k K c • (a c ⊗ₜ[ZMod 2] Ach.t0 2 T hT.1) +
        (a c ⊗ₜ[ZMod 2] Ach.t0 2 T hT.1) = 0 := by
      rw [← hsmul, ← TensorProduct.add_tmul, add_comm, hac, TensorProduct.zero_tmul]
    rw [hbc, LinearMap.add_apply, ArchAux.dualSMul_apply_of_inv_eq_self _ hσinv, ← map_add, hx,
      map_zero]
  · rw [Ach.archPair_apply_of_ne_two (h := hT.1) p (Ω ≃ₐ[k] Ω) M T hp2 c a b]
/-- Clause (5): naturality of `archPair` in the coefficient module. -/
theorem cup_naturality     (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) {M : Type} [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (M₂ : Type) [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂]
    (c : Ω ≃ₐ[k] Ω)
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
    (f' : SSGRoute.DualMod p (M₂ ⊗[ZMod p] T) →ₗ[ZMod p] SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hff' : ∀ (φ : SSGRoute.DualMod p (M₂ ⊗[ZMod p] T)) (e : M) (t : T),
      f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M₂ ⊗[ZMod p] T)) :
    Ach.archPair p (Ω ≃ₐ[k] Ω) M₂ T hT.1 c (fun σ => f (a σ)) b =
      Ach.archPair p (Ω ≃ₐ[k] Ω) M T hT.1 c a (fun σ => f' (b σ)) := by
  by_cases hp2 : p = 2
  · rw [Ach.archPair_apply_of_eq_two (h := hT.1) p (Ω ≃ₐ[k] Ω) M₂ T hp2 c (fun σ => f (a σ)) b,
      Ach.archPair_apply_of_eq_two (h := hT.1) p (Ω ≃ₐ[k] Ω) M T hp2 c a (fun σ => f' (b σ))]
    exact (hff' (b c) (a c) (Ach.t0 p T hT.1)).symm
  · rw [Ach.archPair_apply_of_ne_two (h := hT.1) p (Ω ≃ₐ[k] Ω) M₂ T hp2 c (fun σ => f (a σ)) b,
      Ach.archPair_apply_of_ne_two (h := hT.1) p (Ω ≃ₐ[k] Ω) M T hp2 c a (fun σ => f' (b σ))]
/-- **The archimedean family of local pairings**: at a subgroup generated by an involution it is
the explicit pairing `Ach.archPair`, and `0` off those subgroups (where it is never used).  The
generator is chosen once and for all by `Classical.choose`, so that the family is a single canonical
object, as the clauses (and reciprocity) require. -/
noncomputable def pairArchFamily     (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) :
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → M) →
        ((Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)) → ZMod p :=
  fun M _ _ _ _ _ H a b =>
    if h : ∃ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 ∧ H = Subgroup.zpowers c then
      Ach.archPair p (Ω ≃ₐ[k] Ω) M T hT.1 (Classical.choose h) a b else 0

/-- The chosen generator of `⟨c⟩`: an involution generating the same cyclic subgroup. -/
noncomputable def genArch     (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) : Ω ≃ₐ[k] Ω :=
  Classical.choose (show ∃ c' : Ω ≃ₐ[k] Ω, c' ^ 2 = 1 ∧ Subgroup.zpowers c = Subgroup.zpowers c'
    from ⟨c, hc, rfl⟩)

theorem genArch_spec     (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) :
    (genArch p k Ω K ζ hζ hζK T hT c hc) ^ 2 = 1 ∧
      Subgroup.zpowers (genArch p k Ω K ζ hζ hζK T hT c hc) = Subgroup.zpowers c := by
  rw [genArch]
  obtain ⟨h1, h2⟩ := Classical.choose_spec (show ∃ c' : Ω ≃ₐ[k] Ω, c' ^ 2 = 1 ∧
    Subgroup.zpowers c = Subgroup.zpowers c' from ⟨c, hc, rfl⟩)
  exact ⟨h1, h2.symm⟩

theorem genArch_sq     (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) :
    (genArch p k Ω K ζ hζ hζK T hT c hc) ^ 2 = 1 := (genArch_spec p k Ω K ζ hζ hζK T hT c hc).1

theorem zpowers_genArch     (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ) (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) :
    Subgroup.zpowers (genArch p k Ω K ζ hζ hζK T hT c hc) = Subgroup.zpowers c :=
  (genArch_spec p k Ω K ζ hζ hζK T hT c hc).2

/-- **The value of the family at `⟨c⟩`**: it is `archPair` at the chosen generator. -/
theorem pairArchFamily_zpowers_apply     (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) (a : (Ω ≃ₐ[k] Ω) → M)
    (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)) :
    pairArchFamily p k Ω K ζ hζ hζK T hT M (Subgroup.zpowers c) a b =
      Ach.archPair p (Ω ≃ₐ[k] Ω) M T hT.1 (genArch p k Ω K ζ hζ hζK T hT c hc) a b := by
  unfold pairArchFamily
  split_ifs with h
  · rw [show h = (show ∃ c' : Ω ≃ₐ[k] Ω, c' ^ 2 = 1 ∧
        Subgroup.zpowers c = Subgroup.zpowers c' from ⟨c, hc, rfl⟩) from Subsingleton.elim _ _]
    simp only [genArch]
  · exact absurd (show ∃ c' : Ω ≃ₐ[k] Ω, c' ^ 2 = 1 ∧ Subgroup.zpowers c = Subgroup.zpowers c'
      from ⟨c, hc, rfl⟩) h
/-- Clause (1) at `⟨c⟩` for the family. -/
theorem pairArchFamily_add_left     (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1)
    (a a' : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)) :
    pairArchFamily p k Ω K ζ hζ hζK T hT M (Subgroup.zpowers c) (a + a') b =
      pairArchFamily p k Ω K ζ hζ hζK T hT M (Subgroup.zpowers c) a b +
        pairArchFamily p k Ω K ζ hζ hζK T hT M (Subgroup.zpowers c) a' b := by
  rw [pairArchFamily_zpowers_apply p k Ω K ζ hζ hζK T hT M c hc (a + a') b,
    pairArchFamily_zpowers_apply p k Ω K ζ hζ hζK T hT M c hc a b,
    pairArchFamily_zpowers_apply p k Ω K ζ hζ hζK T hT M c hc a' b]
  exact cup_add_left p k Ω K ζ hζ hζK T hT (genArch p k Ω K ζ hζ hζK T hT c hc) a a' b

/-- Clause (2) at `⟨c⟩` for the family. -/
theorem pairArchFamily_add_right     (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1)
    (a : (Ω ≃ₐ[k] Ω) → M) (b b' : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T)) :
    pairArchFamily p k Ω K ζ hζ hζK T hT M (Subgroup.zpowers c) a (b + b') =
      pairArchFamily p k Ω K ζ hζ hζK T hT M (Subgroup.zpowers c) a b +
        pairArchFamily p k Ω K ζ hζ hζK T hT M (Subgroup.zpowers c) a b' := by
  rw [pairArchFamily_zpowers_apply p k Ω K ζ hζ hζK T hT M c hc a (b + b'),
    pairArchFamily_zpowers_apply p k Ω K ζ hζ hζK T hT M c hc a b,
    pairArchFamily_zpowers_apply p k Ω K ζ hζ hζK T hT M c hc a b']
  exact cup_add_right p k Ω K ζ hζ hζK T hT (genArch p k Ω K ζ hζ hζK T hT c hc) a b b'

/-- Clause (3) in the first variable at `⟨c⟩` for the family. -/
theorem pairArchFamily_coboundary_left     (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1)
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧
      SSGRoute.IsLocConstOn (Subgroup.zpowers c) b)
    (hab : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) a) :
    pairArchFamily p k Ω K ζ hζ hζK T hT M (Subgroup.zpowers c) a b = 0 := by
  rw [pairArchFamily_zpowers_apply p k Ω K ζ hζ hζK T hT M c hc a b]
  exact cup_coboundary_left p k Ω K ζ hζ hζK T hT (genArch p k Ω K ζ hζ hζK T hT c hc) (genArch_sq p k Ω K ζ hζ hζK T hT c hc) a b
    ((zpowers_genArch p k Ω K ζ hζ hζK T hT c hc).symm ▸ hb) ((zpowers_genArch p k Ω K ζ hζ hζK T hT c hc).symm ▸ hab)

/-- Clause (3) in the second variable at `⟨c⟩` for the family. -/
theorem pairArchFamily_coboundary_right     (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1)
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a ∧
      SSGRoute.IsLocConstOn (Subgroup.zpowers c) a)
    (hbb : SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b) :
    pairArchFamily p k Ω K ζ hζ hζK T hT M (Subgroup.zpowers c) a b = 0 := by
  rw [pairArchFamily_zpowers_apply p k Ω K ζ hζ hζK T hT M c hc a b]
  exact cup_coboundary_right p k Ω K ζ hζ hζK T hT (genArch p k Ω K ζ hζ hζK T hT c hc) (genArch_sq p k Ω K ζ hζ hζK T hT c hc) a b
    ((zpowers_genArch p k Ω K ζ hζ hζK T hT c hc).symm ▸ ha) ((zpowers_genArch p k Ω K ζ hζ hζK T hT c hc).symm ▸ hbb)

/-- Clause (4), first variable, at `⟨c⟩` for the family. -/
theorem pairArchFamily_perfect_left     (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) (a : (Ω ≃ₐ[k] Ω) → M)
    (ha : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a ∧
      SSGRoute.IsLocConstOn (Subgroup.zpowers c) a)
    (hzero : ∀ b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧
        SSGRoute.IsLocConstOn (Subgroup.zpowers c) b) →
      pairArchFamily p k Ω K ζ hζ hζK T hT M (Subgroup.zpowers c) a b = 0) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) a :=
  zpowers_genArch p k Ω K ζ hζ hζK T hT c hc ▸
    (archPair_nondegenerate (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK) (E := M) (T := T) (hT := hT) (c := genArch p k Ω K ζ hζ hζK T hT c hc) (hc := genArch_sq p k Ω K ζ hζ hζK T hT c hc)).1 a
      ((zpowers_genArch p k Ω K ζ hζ hζK T hT c hc).symm ▸ ha)
      (fun b hb => by
        rw [← pairArchFamily_zpowers_apply p k Ω K ζ hζ hζK T hT M c hc a b]
        exact hzero b (zpowers_genArch p k Ω K ζ hζ hζK T hT c hc ▸ hb))

/-- Clause (4), second variable, at `⟨c⟩` for the family. -/
theorem pairArchFamily_perfect_right     (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1)
    (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧
      SSGRoute.IsLocConstOn (Subgroup.zpowers c) b)
    (hzero : ∀ a : (Ω ≃ₐ[k] Ω) → M,
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a ∧
        SSGRoute.IsLocConstOn (Subgroup.zpowers c) a) →
      pairArchFamily p k Ω K ζ hζ hζK T hT M (Subgroup.zpowers c) a b = 0) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b :=
  zpowers_genArch p k Ω K ζ hζ hζK T hT c hc ▸
    (archPair_nondegenerate (p := p) (k := k) (Ω := Ω) (K := K) (ζ := ζ) (hζ := hζ) (hζK := hζK) (E := M) (T := T) (hT := hT) (c := genArch p k Ω K ζ hζ hζK T hT c hc) (hc := genArch_sq p k Ω K ζ hζ hζK T hT c hc)).2 b
      ((zpowers_genArch p k Ω K ζ hζ hζK T hT c hc).symm ▸ hb)
      (fun a ha => by
        rw [← pairArchFamily_zpowers_apply p k Ω K ζ hζ hζK T hT M c hc a b]
        exact hzero a (zpowers_genArch p k Ω K ζ hζ hζK T hT c hc ▸ ha))

/-- **Clauses (1)–(4) of the archimedean family at `⟨c⟩`**, in the shape of the `hloc` hypothesis of
`Work.SSGRoute.pt_selmer_relaxed`. -/
theorem pairArchFamily_pairClauses     (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) :
    H1Pair.PairClauses p K T M
      (fun a b => pairArchFamily p k Ω K ζ hζ hζK T hT M (Subgroup.zpowers c) a b) (Subgroup.zpowers c) :=
  ⟨fun a a' b _ _ _ => pairArchFamily_add_left p k Ω K ζ hζ hζK T hT M c hc a a' b,
    fun a b b' _ _ _ => pairArchFamily_add_right p k Ω K ζ hζ hζK T hT M c hc a b b',
    fun a b ha hb h => h.elim
      (fun hab => pairArchFamily_coboundary_left p k Ω K ζ hζ hζK T hT M c hc a b hb hab)
      (fun hbb => pairArchFamily_coboundary_right p k Ω K ζ hζ hζK T hT M c hc a b ha hbb),
    fun a ha hzero => pairArchFamily_perfect_left p k Ω K ζ hζ hζK T hT M c hc a ha hzero,
    fun b hb hzero => pairArchFamily_perfect_right p k Ω K ζ hζ hζK T hT M c hc b hb hzero⟩

/-- **Naturality (clause (5)) for the archimedean family at `⟨c⟩`.** -/
theorem pairArchFamily_naturality     (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M M₂ : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    [AddCommGroup M₂] [Module (ZMod p) M₂] [DistribMulAction (K ≃ₐ[k] K) M₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M₂] [Finite M₂]
    (f : M →ₗ[ZMod p] M₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : M), f (g • e) = g • f e)
    (f' : SSGRoute.DualMod p (M₂ ⊗[ZMod p] T) →ₗ[ZMod p] SSGRoute.DualMod p (M ⊗[ZMod p] T))
    (hff' : ∀ (φ : SSGRoute.DualMod p (M₂ ⊗[ZMod p] T)) (e : M) (t : T),
      f' φ (e ⊗ₜ[ZMod p] t) = φ (f e ⊗ₜ[ZMod p] t))
    (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → SSGRoute.DualMod p (M₂ ⊗[ZMod p] T))
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) :
    pairArchFamily p k Ω K ζ hζ hζK T hT M₂ (Subgroup.zpowers c) (fun σ => f (a σ)) b =
      pairArchFamily p k Ω K ζ hζ hζK T hT M (Subgroup.zpowers c) a (fun σ => f' (b σ)) := by
  rw [pairArchFamily_zpowers_apply p k Ω K ζ hζ hζK T hT M₂ c hc (fun σ => f (a σ)) b,
    pairArchFamily_zpowers_apply p k Ω K ζ hζ hζK T hT M c hc a (fun σ => f' (b σ))]
  exact cup_naturality p k Ω K ζ hζ hζK T hT M₂ (genArch p k Ω K ζ hζ hζK T hT c hc) f hf f' hff' a b

end Work.SSGRoute.E7Arch
