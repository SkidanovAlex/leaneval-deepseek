import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.PT.pt_canonical_aux
import Submission.Work.SSGRoute.PT.pt_selmer_counting
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The counting step of the Poitou–Tate argument

`Work.SSGRoute.PT.pt_canonical_relaxed` is assembled from three independent pieces:

* clauses (1) and (2) of its conclusion — the canonical local pairing, requested separately as
  `SSGRoute/PT/pt_canonical_pairing`;
* the Poitou–Tate counting identity `|V| · |W| = |∏_{S ∪ C} H¹|`, requested separately as
  `SSGRoute/PT/pt_selmer_counting_identity`;
* the *counting step* proved here, which converts those two into clause (3) (realizability).

The counting step is pure linear algebra over `𝔽_p`.  Let `β` be the pairing induced on the
products `P`, `Q` of local `H¹`-groups by the local pairings, let `V ≤ P` be the image of the
relaxed Selmer group and `W ≤ Q` the image of the relaxed dual Selmer group.  Reciprocity gives
`V ⊆ W^⊥` (`Work.SSGRoute.PT.pt_orthogonality_of_realizable`), the counting identity gives
`|V| · |W| = |P|`, and the non-degeneracy clauses (1d)/(1e) make `β` non-degenerate in both
variables.  Then `W^⊥ = V`: an element of `P` orthogonal to `W` is realizable.

This file proves the abstract statement (`wbot_le_of_natCard`); the concrete identification of
`P`, `Q`, `V`, `W` and `β` with the statements of the sibling nodes is the *assembly*
(`pt_realization_of_pairing_and_counting`).
-/

open scoped TensorProduct Pointwise BigOperators
open Classical

set_option linter.style.haveILetI false

namespace Work.SSGRoute.PT

noncomputable section

/-! ## The abstract counting lemma -/

/-- **The counting step.**  Let `β : P → Q → 𝔽_p` be a pairing, non-degenerate in both
variables.  Let `V ≤ P`, `W ≤ Q` with `V ⊆ W^⊥` and `|V| · |W| = |P|`.  Then `W^⊥ ≤ V`.

In dimensions: on the one hand `dim V ≤ dim W^⊥ = dim P − dim (dual annihilator of W)`, and
`dim (dual annihilator of W) = dim Q − dim W = dim P − dim W`; the counting identity
`dim P = dim V + dim W` therefore forces equality. -/
theorem wbot_le_of_natCard {p : ℕ} [Fact p.Prime] {P Q : Type*}
    [AddCommGroup P] [Module (ZMod p) P] [Finite P]
    [AddCommGroup Q] [Module (ZMod p) Q] [Finite Q]
    (β : P →ₗ[ZMod p] Q →ₗ[ZMod p] ZMod p)
    (hndL : ∀ x : P, (∀ y : Q, β x y = 0) → x = 0)
    (hndR : ∀ y : Q, (∀ x : P, β x y = 0) → y = 0)
    (V : Submodule (ZMod p) P) (W : Submodule (ZMod p) Q)
    (hVW : ∀ x ∈ V, ∀ y : W, β x y = 0)
    (hcard : Nat.card V * Nat.card W = Nat.card P) :
    ∀ x : P, (∀ y : W, β x y = 0) → x ∈ V := by
  classical
  haveI hPf : Module.Finite (ZMod p) P := Module.Finite.of_finite
  haveI hQf : Module.Finite (ZMod p) Q := Module.Finite.of_finite
  haveI hVf : Module.Finite (ZMod p) V := Module.Finite.of_finite
  haveI hWf : Module.Finite (ZMod p) W := Module.Finite.of_finite
  -- the two injections given by the two non-degeneracy clauses
  have hinjΦ : Function.Injective β := by
    intro x y hxy
    have hz : β (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h0 : ∀ z : Q, β (x - y) z = 0 := fun z => by rw [hz]; rfl
    have h1 : x - y = 0 := hndL (x - y) h0
    rwa [sub_eq_zero] at h1
  have hinjΨ : Function.Injective (LinearMap.flip β) := by
    intro x y hxy
    have hz : LinearMap.flip β (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have h0 : ∀ z : P, β z (x - y) = 0 := by
      intro z
      have h1 := congrArg (fun (f : P →ₗ[ZMod p] ZMod p) => f z) hz
      simpa using h1
    have h1 : x - y = 0 := hndR (x - y) h0
    rwa [sub_eq_zero] at h1
  have hPQ : Module.finrank (ZMod p) P = Module.finrank (ZMod p) Q := by
    have h1 : Module.finrank (ZMod p) P ≤ Module.finrank (ZMod p) Q := by
      have h := LinearMap.finrank_le_finrank_of_injective (R := ZMod p)
        (M := P) (M' := Module.Dual (ZMod p) Q) hinjΦ
      rwa [Subspace.dual_finrank_eq] at h
    have h2 : Module.finrank (ZMod p) Q ≤ Module.finrank (ZMod p) P := by
      have h := LinearMap.finrank_le_finrank_of_injective (R := ZMod p)
        (M := Q) (M' := Module.Dual (ZMod p) P) hinjΨ
      rwa [Subspace.dual_finrank_eq] at h
    omega
  -- the counting identity in dimensions
  have hdim : Module.finrank (ZMod p) P
      = Module.finrank (ZMod p) V + Module.finrank (ZMod p) W := by
    have hV : Nat.card V = p ^ Module.finrank (ZMod p) V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    have hW : Nat.card W = p ^ Module.finrank (ZMod p) W := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    have hP : Nat.card P = p ^ Module.finrank (ZMod p) P := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
    rw [hV, hW, hP, ← pow_add] at hcard
    exact (Nat.pow_right_injective (Fact.out (p := p.Prime)).two_le hcard).symm
  -- `W^⊥` is the preimage of the dual annihilator of `W`
  have hWbot : ∀ x : P, (∀ y : W, β x y = 0) ↔
      x ∈ (Submodule.dualAnnihilator W).comap β := by
    intro x
    rw [Submodule.mem_comap, Submodule.mem_dualAnnihilator]
    exact ⟨fun h y hy => h ⟨y, hy⟩, fun h y => h y.1 y.2⟩
  -- the finrank of the dual annihilator
  have hann : Module.finrank (ZMod p) (Submodule.dualAnnihilator W)
      = Module.finrank (ZMod p) Q - Module.finrank (ZMod p) W := by
    have := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    omega
  -- the preimage of the annihilator is an equivalence, so has the same dimension
  have hPQ' : Module.finrank (ZMod p) P
      = Module.finrank (ZMod p) (Module.Dual (ZMod p) Q) := by
    rw [Subspace.dual_finrank_eq]; exact hPQ
  have hcomap : Module.finrank (ZMod p) ((Submodule.dualAnnihilator W).comap β)
      = Module.finrank (ZMod p) (Submodule.dualAnnihilator W) := by
    let f : ((Submodule.dualAnnihilator W).comap β) →ₗ[ZMod p]
        Submodule.dualAnnihilator W :=
      { toFun := fun x => ⟨β x.1, x.2⟩
        map_add' := fun x y => by ext; simp
        map_smul' := fun c x => by ext; simp }
    have hf : Function.Bijective f := by
      refine ⟨?_, ?_⟩
      · intro x y hxy
        have h1 : β x.1 = β y.1 := congrArg Subtype.val hxy
        exact Subtype.ext (hinjΦ h1)
      · rintro ⟨φ, hφ⟩
        obtain ⟨x, rfl⟩ := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hPQ').mp
          hinjΦ φ
        exact ⟨⟨x, by rw [Submodule.mem_comap]; exact hφ⟩, Subtype.ext rfl⟩
    exact LinearEquiv.finrank_eq (LinearEquiv.ofBijective f hf)
  have hker : Module.finrank (ZMod p) ((Submodule.dualAnnihilator W).comap β)
      = Module.finrank (ZMod p) V := by
    rw [hcomap, hann]
    omega
  -- `V` and `W^⊥` have the same dimension, so they are equal
  have hle : V ≤ (Submodule.dualAnnihilator W).comap β := by
    intro x hx
    rw [← hWbot x]
    exact hVW x hx
  have hEq : V = (Submodule.dualAnnihilator W).comap β :=
    Submodule.eq_of_le_of_finrank_eq hle hker.symm
  intro x hx
  rw [hEq, ← hWbot x]
  exact hx

end

end Work.SSGRoute.PT

namespace Work.SSGRoute.PT

noncomputable section

/-! ## The local pairing on `H¹` induced by the axioms -/

section LocalPairing

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- A chosen representative of a local `H¹`-class, as a locally constant cocycle. -/
def locRepr (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (y : H1loc p k Ω K M H) : (Ω ≃ₐ[k] Ω) → M :=
  Classical.choose (toClass_surjective p k Ω K M H y)

theorem toClass_locRepr (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (y : H1loc p k Ω K M H) :
    toClass p k Ω K M H (locRepr p k Ω K M H y) = y :=
  (Classical.choose_spec (toClass_surjective p k Ω K M H y)).2

theorem mem_locRepr (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (y : H1loc p k Ω K M H) :
    locRepr p k Ω K M H y ∈ lcCocycles p k Ω K M H :=
  (Classical.choose_spec (toClass_surjective p k Ω K M H y)).1

/-- `toClass` of a difference of locally constant cocycles. -/
theorem toClass_sub (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) {f g : (Ω ≃ₐ[k] Ω) → M}
    (hf : f ∈ lcCocycles p k Ω K M H) (hg : g ∈ lcCocycles p k Ω K M H) :
    toClass p k Ω K M H (f - g) = toClass p k Ω K M H f - toClass p k Ω K M H g := by
  have hfg : f - g ∈ lcCocycles p k Ω K M H := Submodule.sub_mem _ hf hg
  have h1 : toClass p k Ω K M H (f - g) + toClass p k Ω K M H g = toClass p k Ω K M H f := by
    rw [← toClass_add p k Ω K M H hfg hg]
    congr 1
    ext σ
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  exact eq_sub_of_add_eq h1

/-- **Two locally constant cocycles with the same class differ by a coboundary.** -/
theorem sub_mem_coboundaries_of_toClass_eq (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) {f g : (Ω ≃ₐ[k] Ω) → M}
    (hf : f ∈ lcCocycles p k Ω K M H) (hg : g ∈ lcCocycles p k Ω K M H)
    (heq : toClass p k Ω K M H f = toClass p k Ω K M H g) :
    f - g ∈ coboundaries p k Ω K M H := by
  have hsubc : f - g ∈ lcCocycles p k Ω K M H := Submodule.sub_mem _ hf hg
  rw [← toClass_eq_zero_iff p k Ω K M H hsubc, toClass_sub p k Ω K M H hf hg, heq, sub_self]

/-- **The local pairing on `H¹`.**  The local axioms (additivity in each variable on locally
constant cocycles, vanishing on coboundaries, non-degeneracy on both sides) make `pair H` descend
to a bilinear pairing `H¹(H, M) × H¹(H, M') → 𝔽_p` which is non-degenerate in each variable. -/
theorem exists_pairing_on_H1loc (M M' : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    [AddCommGroup M'] [Module (ZMod p) M'] [DistribMulAction (K ≃ₐ[k] K) M']
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M']
    (H : Subgroup (Ω ≃ₐ[k] Ω))
    (pair : ((Ω ≃ₐ[k] Ω) → M) → ((Ω ≃ₐ[k] Ω) → M') → ZMod p)
    (haddL : ∀ (a a' : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → M'),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a' ∧ SSGRoute.IsLocConstOn H a') →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
      pair (a + a') b = pair a b + pair a' b)
    (haddR : ∀ (a : (Ω ≃ₐ[k] Ω) → M) (b b' : (Ω ≃ₐ[k] Ω) → M'),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b' ∧ SSGRoute.IsLocConstOn H b') →
      pair a (b + b') = pair a b + pair a b')
    (hvanishL : ∀ (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → M'),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a → pair a b = 0)
    (hvanishR : ∀ (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → M'),
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b → pair a b = 0)
    (hndL : ∀ a : (Ω ≃ₐ[k] Ω) → M,
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
      (∀ b : (Ω ≃ₐ[k] Ω) → M',
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        pair a b = 0) →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H a)
    (hndR : ∀ b : (Ω ≃ₐ[k] Ω) → M',
      (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
      (∀ a : (Ω ≃ₐ[k] Ω) → M,
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        pair a b = 0) →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) H b) :
    ∃ B : H1loc p k Ω K M H →ₗ[ZMod p] H1loc p k Ω K M' H →ₗ[ZMod p] ZMod p,
      (∀ (a : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → M'),
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H a ∧ SSGRoute.IsLocConstOn H a) →
        (SSGRoute.IsCocycleOn (SSGRoute.res k K) H b ∧ SSGRoute.IsLocConstOn H b) →
        B (toClass p k Ω K M H a) (toClass p k Ω K M' H b) = pair a b) ∧
      (∀ x : H1loc p k Ω K M H, (∀ y : H1loc p k Ω K M' H, B x y = 0) → x = 0) ∧
      (∀ y : H1loc p k Ω K M' H, (∀ x : H1loc p k Ω K M H, B x y = 0) → y = 0) := by
  classical
  -- the pairing depends only on the classes
  have hcongL : ∀ (f f' : (Ω ≃ₐ[k] Ω) → M) (b : (Ω ≃ₐ[k] Ω) → M'),
      f ∈ lcCocycles p k Ω K M H → f' ∈ lcCocycles p k Ω K M H →
      b ∈ lcCocycles p k Ω K M' H →
      toClass p k Ω K M H f = toClass p k Ω K M H f' → pair f b = pair f' b := by
    intro f f' b hf hf' hb heq
    have hsubc : (fun σ => f σ - f' σ) ∈ lcCocycles p k Ω K M H := Submodule.sub_mem _ hf hf'
    have hsub : (fun σ => f σ - f' σ) ∈ coboundaries p k Ω K M H :=
      sub_mem_coboundaries_of_toClass_eq p k Ω K M H hf hf' heq
    have hsplit : f = f' + (fun σ => f σ - f' σ) := by
      ext σ; simp only [Pi.add_apply]; abel
    rw [hsplit, haddL f' (fun σ => f σ - f' σ) b hf' hsubc hb,
      hvanishL (fun σ => f σ - f' σ) b hsubc hb hsub, add_zero]
  have hcongR : ∀ (a : (Ω ≃ₐ[k] Ω) → M) (f f' : (Ω ≃ₐ[k] Ω) → M'),
      a ∈ lcCocycles p k Ω K M H → f ∈ lcCocycles p k Ω K M' H →
      f' ∈ lcCocycles p k Ω K M' H →
      toClass p k Ω K M' H f = toClass p k Ω K M' H f' → pair a f = pair a f' := by
    intro a f f' ha hf hf' heq
    have hsubc : (fun σ => f σ - f' σ) ∈ lcCocycles p k Ω K M' H := Submodule.sub_mem _ hf hf'
    have hsub : (fun σ => f σ - f' σ) ∈ coboundaries p k Ω K M' H :=
      sub_mem_coboundaries_of_toClass_eq p k Ω K M' H hf hf' heq
    have hsplit : f = f' + (fun σ => f σ - f' σ) := by
      ext σ; simp only [Pi.add_apply]; abel
    rw [hsplit, haddR a f' (fun σ => f σ - f' σ) ha hf' hsubc,
      hvanishR a (fun σ => f σ - f' σ) ha hsubc hsub, add_zero]
  -- additivity of the descended pairing on representatives
  have hadd1 : ∀ (x x' : H1loc p k Ω K M H) (y : H1loc p k Ω K M' H),
      pair (locRepr p k Ω K M H (x + x')) (locRepr p k Ω K M' H y)
        = pair (locRepr p k Ω K M H x) (locRepr p k Ω K M' H y)
          + pair (locRepr p k Ω K M H x') (locRepr p k Ω K M' H y) := by
    intro x x' y
    have hx : locRepr p k Ω K M H x ∈ lcCocycles p k Ω K M H := mem_locRepr p k Ω K M H x
    have hx' : locRepr p k Ω K M H x' ∈ lcCocycles p k Ω K M H := mem_locRepr p k Ω K M H x'
    have hy : locRepr p k Ω K M' H y ∈ lcCocycles p k Ω K M' H := mem_locRepr p k Ω K M' H y
    have hsum : toClass p k Ω K M H (locRepr p k Ω K M H (x + x'))
        = toClass p k Ω K M H (locRepr p k Ω K M H x + locRepr p k Ω K M H x') := by
      simp only [toClass_add p k Ω K M H hx hx', toClass_locRepr]
    rw [hcongL _ _ _ (mem_locRepr p k Ω K M H (x + x')) (add_mem hx hx') hy hsum,
      haddL (locRepr p k Ω K M H x) (locRepr p k Ω K M H x') (locRepr p k Ω K M' H y) hx hx' hy]
  have hadd2 : ∀ (x : H1loc p k Ω K M H) (y y' : H1loc p k Ω K M' H),
      pair (locRepr p k Ω K M H x) (locRepr p k Ω K M' H (y + y'))
        = pair (locRepr p k Ω K M H x) (locRepr p k Ω K M' H y)
          + pair (locRepr p k Ω K M H x) (locRepr p k Ω K M' H y') := by
    intro x y y'
    have hx : locRepr p k Ω K M H x ∈ lcCocycles p k Ω K M H := mem_locRepr p k Ω K M H x
    have hy : locRepr p k Ω K M' H y ∈ lcCocycles p k Ω K M' H := mem_locRepr p k Ω K M' H y
    have hy' : locRepr p k Ω K M' H y' ∈ lcCocycles p k Ω K M' H := mem_locRepr p k Ω K M' H y'
    have hsum : toClass p k Ω K M' H (locRepr p k Ω K M' H (y + y'))
        = toClass p k Ω K M' H (locRepr p k Ω K M' H y + locRepr p k Ω K M' H y') := by
      simp only [toClass_add p k Ω K M' H hy hy', toClass_locRepr]
    rw [hcongR _ _ _ hx (mem_locRepr p k Ω K M' H (y + y')) (add_mem hy hy') hsum,
      haddR (locRepr p k Ω K M H x) (locRepr p k Ω K M' H y) (locRepr p k Ω K M' H y') hx hy hy']
  -- the additive map in the first variable
  let innerAdd : ∀ (_ : H1loc p k Ω K M H), H1loc p k Ω K M' H →+ ZMod p :=
    fun x => AddMonoidHom.mk' (fun y => pair (locRepr p k Ω K M H x) (locRepr p k Ω K M' H y))
      (fun y y' => hadd2 x y y')
  have hinner : ∀ x x' : H1loc p k Ω K M H, innerAdd (x + x') = innerAdd x + innerAdd x' := by
    intro x x'
    ext y
    exact hadd1 x x' y
  let F : H1loc p k Ω K M H →+ (H1loc p k Ω K M' H →ₗ[ZMod p] ZMod p) :=
    AddMonoidHom.mk' (fun x => AddMonoidHom.toZModLinearMap p (innerAdd x))
      (fun x x' => by
        rw [hinner x x']
        ext y
        rfl)
  let B : H1loc p k Ω K M H →ₗ[ZMod p] H1loc p k Ω K M' H →ₗ[ZMod p] ZMod p :=
    AddMonoidHom.toZModLinearMap p F
  have hB : ∀ (x : H1loc p k Ω K M H) (y : H1loc p k Ω K M' H),
      B x y = pair (locRepr p k Ω K M H x) (locRepr p k Ω K M' H y) := fun x y => rfl
  refine ⟨B, ?_, ?_, ?_⟩
  · -- defining property on locally constant cocycles
    intro a b ha hb
    have h1 := hcongL a (locRepr p k Ω K M H (toClass p k Ω K M H a)) b ha
      (mem_locRepr p k Ω K M H _) hb (toClass_locRepr p k Ω K M H (toClass p k Ω K M H a)).symm
    have h2 := hcongR (locRepr p k Ω K M H (toClass p k Ω K M H a)) b
      (locRepr p k Ω K M' H (toClass p k Ω K M' H b)) (mem_locRepr p k Ω K M H _) hb
      (mem_locRepr p k Ω K M' H _)
      (toClass_locRepr p k Ω K M' H (toClass p k Ω K M' H b)).symm
    rw [hB, h1, h2]
  · -- non-degeneracy in the first variable
    intro x hx
    have key : ∀ b : (Ω ≃ₐ[k] Ω) → M',
        b ∈ lcCocycles p k Ω K M' H → pair (locRepr p k Ω K M H x) b = 0 := by
      intro b hb
      rw [hcongR (locRepr p k Ω K M H x) b (locRepr p k Ω K M' H (toClass p k Ω K M' H b))
          (mem_locRepr p k Ω K M H x) hb (mem_locRepr p k Ω K M' H _)
          (toClass_locRepr p k Ω K M' H (toClass p k Ω K M' H b)).symm,
        ← hB x (toClass p k Ω K M' H b), hx (toClass p k Ω K M' H b)]
    have hrep : locRepr p k Ω K M H x ∈ coboundaries p k Ω K M H :=
      hndL _ (mem_locRepr p k Ω K M H x) key
    rw [← toClass_locRepr p k Ω K M H x,
      (toClass_eq_zero_iff p k Ω K M H (mem_locRepr p k Ω K M H x)).mpr hrep]
  · -- non-degeneracy in the second variable
    intro y hy
    have key : ∀ a : (Ω ≃ₐ[k] Ω) → M,
        a ∈ lcCocycles p k Ω K M H → pair a (locRepr p k Ω K M' H y) = 0 := by
      intro a ha
      rw [hcongL a (locRepr p k Ω K M H (toClass p k Ω K M H a)) (locRepr p k Ω K M' H y) ha
          (mem_locRepr p k Ω K M H _) (mem_locRepr p k Ω K M' H y)
          (toClass_locRepr p k Ω K M H (toClass p k Ω K M H a)).symm,
        ← hB (toClass p k Ω K M H a) y, hy (toClass p k Ω K M H a)]
    have hrep : locRepr p k Ω K M' H y ∈ coboundaries p k Ω K M' H :=
      hndR _ (mem_locRepr p k Ω K M' H y) key
    rw [← toClass_locRepr p k Ω K M' H y,
      (toClass_eq_zero_iff p k Ω K M' H (mem_locRepr p k Ω K M' H y)).mpr hrep]

end LocalPairing



/-! ## The relaxed Selmer modules and their local class maps -/

section SelmerClasses

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))

omit hKN in
/-- The **relaxed primal Selmer module** of `M`: global locally constant cocycles of `M` that
vanish on inertia at every finite place outside `S` which is not split in `N`. -/
noncomputable def primalSelmer : Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → M) where
  carrier := {ε | SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ ε ∧
    SSGRoute.IsLocConstOn ⊤ ε ∧
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → ε σ = 0}
  zero_mem' := ⟨fun g _ h _ => by simp, ⟨⊤, isOpen_univ, fun _ _ _ _ _ => rfl⟩,
    fun B _ _ _ σ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3⟩ ⟨hg1, hg2, hg3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a ha b hb
      simp only [Pi.add_apply, hf1 a ha b hb, hg1 a ha b hb, smul_add]
      abel
    · obtain ⟨U, hUo, hU⟩ := hf2
      obtain ⟨V, hVo, hV⟩ := hg2
      refine ⟨U ⊓ V, ?_, ?_⟩
      · rw [Subgroup.coe_inf]; exact hUo.inter hVo
      · intro a ha u hu huH
        simp only [Pi.add_apply, hU a ha u (Subgroup.mem_inf.mp hu).1 huH,
          hV a ha u (Subgroup.mem_inf.mp hu).2 huH]
    · intro B hB hBconj hBsplit σ hσ
      simp only [Pi.add_apply, hf3 B hB hBconj hBsplit σ hσ, hg3 B hB hBconj hBsplit σ hσ,
        add_zero]
  smul_mem' := by
    rintro r f ⟨hf1, hf2, hf3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro a ha b hb
      simp only [Pi.smul_apply, hf1 a ha b hb, smul_add]
      rw [smul_comm (SSGRoute.res k K a) r (f b)]
    · obtain ⟨U, hUo, hU⟩ := hf2
      exact ⟨U, hUo, fun a ha u hu huH => by simp only [Pi.smul_apply, hU a ha u hu huH]⟩
    · intro B hB hBconj hBsplit σ hσ
      simp only [Pi.smul_apply, hf3 B hB hBconj hBsplit σ hσ, smul_zero]

omit hKN in
/-- The **local class map**: the tuple of local `H¹`-classes of a global cochain. -/
noncomputable def primalClassMap (ε : (Ω ≃ₐ[k] Ω) → M) : primalClasses p k Ω K M S C :=
  (fun A => toClass p k Ω K M (SSGRoute.decomp k A.1) ε,
    fun c => toClass p k Ω K M (Subgroup.zpowers c.1) ε)

/-- **The classes realized by the relaxed Selmer module are exactly the realizable classes.** -/
theorem mem_image_primalClassMap_iff (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (x : primalClasses p k Ω K M S C) :
    x ∈ primalClassMap p k Ω K M S C ''
        (primalSelmer p k Ω K N M S : Set ((Ω ≃ₐ[k] Ω) → M)) ↔
      IsRealizableClass p k Ω K N hKN M S C x := by
  constructor
  · rintro ⟨ε, hε, rfl⟩
    obtain ⟨hε1, hε2, hε3⟩ := hε
    refine ⟨(fun _ => ε), (fun _ => ε), ε, rfl, hε1, hε2, ?_, ?_, hε3⟩
    · intro A _
      exact ⟨0, fun σ _ => by simp⟩
    · intro c _
      exact ⟨0, fun σ _ => by simp⟩
  · rintro ⟨α, β, ε, hclass, hε1, hε2, hεα, hεβ, hεram⟩
    refine ⟨ε, ⟨hε1, hε2, hεram⟩, ?_⟩
    -- the two components of `primalClassMap ε` and of `x`
    have hcomp1 : ∀ A : {A // A ∈ S},
        toClass p k Ω K M (SSGRoute.decomp k A.1) (α A.1) = x.1 A := by
      intro A
      have h := congrArg (fun z : primalClasses p k Ω K M S C => z.1 A) hclass
      simpa [primalClassOf] using h
    have hcomp2 : ∀ c : {c // c ∈ C},
        toClass p k Ω K M (Subgroup.zpowers c.1) (β c.1) = x.2 c := by
      intro c
      have h := congrArg (fun z : primalClasses p k Ω K M S C => z.2 c) hclass
      simpa [primalClassOf] using h
    refine Prod.ext ?_ ?_
    · funext A
      show toClass p k Ω K M (SSGRoute.decomp k A.1) ε = x.1 A
      have hεc : ε ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A.1) :=
        ⟨isCocycleOn_mono (SSGRoute.res k K) le_top hε1,
          isLocConstOn_mono le_top hε2⟩
      have hdiff : (ε - α A.1) ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A.1) :=
        coboundaries_le_lcCocycles p k Ω K M (SSGRoute.decomp k A.1) (hεα A.1 A.2)
      have hαc : α A.1 ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A.1) := by
        have h := Submodule.sub_mem (lcCocycles p k Ω K M (SSGRoute.decomp k A.1)) hεc hdiff
        have heq : ε - (ε - α A.1) = α A.1 := by
          ext σ; simp only [Pi.sub_apply]; abel
        rwa [heq] at h
      have h0 : toClass p k Ω K M (SSGRoute.decomp k A.1) (ε - α A.1) = 0 :=
        (toClass_eq_zero_iff p k Ω K M (SSGRoute.decomp k A.1) hdiff).mpr (hεα A.1 A.2)
      rw [toClass_sub p k Ω K M (SSGRoute.decomp k A.1) hεc hαc] at h0
      have : toClass p k Ω K M (SSGRoute.decomp k A.1) ε
          = toClass p k Ω K M (SSGRoute.decomp k A.1) (α A.1) := sub_eq_zero.mp h0
      rw [this, hcomp1 A]
    · funext c
      show toClass p k Ω K M (Subgroup.zpowers c.1) ε = x.2 c
      have hεc : ε ∈ lcCocycles p k Ω K M (Subgroup.zpowers c.1) :=
        ⟨isCocycleOn_mono (SSGRoute.res k K) le_top hε1,
          isLocConstOn_mono le_top hε2⟩
      have hdiff : (ε - β c.1) ∈ lcCocycles p k Ω K M (Subgroup.zpowers c.1) :=
        coboundaries_le_lcCocycles p k Ω K M (Subgroup.zpowers c.1) (hεβ c.1 c.2)
      have hβc : β c.1 ∈ lcCocycles p k Ω K M (Subgroup.zpowers c.1) := by
        have h := Submodule.sub_mem (lcCocycles p k Ω K M (Subgroup.zpowers c.1)) hεc hdiff
        have heq : ε - (ε - β c.1) = β c.1 := by
          ext σ; simp only [Pi.sub_apply]; abel
        rwa [heq] at h
      have h0 : toClass p k Ω K M (Subgroup.zpowers c.1) (ε - β c.1) = 0 :=
        (toClass_eq_zero_iff p k Ω K M (Subgroup.zpowers c.1) hdiff).mpr (hεβ c.1 c.2)
      rw [toClass_sub p k Ω K M (Subgroup.zpowers c.1) hεc hβc] at h0
      have : toClass p k Ω K M (Subgroup.zpowers c.1) ε
          = toClass p k Ω K M (Subgroup.zpowers c.1) (β c.1) := sub_eq_zero.mp h0
      rw [this, hcomp2 c]

section DualSelmer

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))

omit hKN in
/-- The **relaxed dual Selmer module** of `M' = DualMod p (M ⊗ T)`: global locally constant
cocycles that are coboundaries on the decomposition group of every finite place split in `N`
outside `S`, and vanish on inertia at every finite place outside `S` that is not split in `N`. -/
noncomputable def dualSelmer :
    Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) where
  carrier := {b | SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b ∧ SSGRoute.IsLocConstOn ⊤ b ∧
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
      SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k B) b) ∧
    (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → b σ = 0)}
  zero_mem' := ⟨fun g _ h _ => by simp, ⟨⊤, isOpen_univ, fun _ _ _ _ _ => rfl⟩,
    fun B _ _ _ => ⟨0, fun σ _ => by simp⟩, fun B _ _ _ σ _ => rfl⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3, hf4⟩ ⟨hg1, hg2, hg3, hg4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a ha b hb
      simp only [Pi.add_apply, hf1 a ha b hb, hg1 a ha b hb, smul_add]
      abel
    · obtain ⟨U, hUo, hU⟩ := hf2
      obtain ⟨V, hVo, hV⟩ := hg2
      refine ⟨U ⊓ V, ?_, ?_⟩
      · rw [Subgroup.coe_inf]; exact hUo.inter hVo
      · intro a ha u hu huH
        simp only [Pi.add_apply, hU a ha u (Subgroup.mem_inf.mp hu).1 huH,
          hV a ha u (Subgroup.mem_inf.mp hu).2 huH]
    · intro B hB hBconj hBsplit
      obtain ⟨m, hm⟩ := hf3 B hB hBconj hBsplit
      obtain ⟨m', hm'⟩ := hg3 B hB hBconj hBsplit
      refine ⟨m + m', fun σ hσ => ?_⟩
      simp only [Pi.add_apply, hm σ hσ, hm' σ hσ, smul_add]
      abel
    · intro B hB hBconj hBsplit σ hσ
      simp only [Pi.add_apply, hf4 B hB hBconj hBsplit σ hσ, hg4 B hB hBconj hBsplit σ hσ,
        add_zero]
  smul_mem' := by
    rintro r f ⟨hf1, hf2, hf3, hf4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a ha b hb
      simp only [Pi.smul_apply, hf1 a ha b hb, smul_add]
      rw [smul_comm (SSGRoute.res k K a) r (f b)]
    · obtain ⟨U, hUo, hU⟩ := hf2
      exact ⟨U, hUo, fun a ha u hu huH => by simp only [Pi.smul_apply, hU a ha u hu huH]⟩
    · intro B hB hBconj hBsplit
      obtain ⟨m, hm⟩ := hf3 B hB hBconj hBsplit
      refine ⟨r • m, fun σ hσ => ?_⟩
      simp only [Pi.smul_apply, hm σ hσ, smul_sub]
      rw [smul_comm (SSGRoute.res k K σ) r m]
    · intro B hB hBconj hBsplit σ hσ
      simp only [Pi.smul_apply, hf4 B hB hBconj hBsplit σ hσ, smul_zero]

omit hKN in
/-- The **local class map** of the dual Selmer module. -/
noncomputable def dualClassMap (b : (Ω ≃ₐ[k] Ω) →
    Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :
    primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C :=
  (fun A => toClass p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
      (SSGRoute.decomp k A.1) b,
    fun c => toClass p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
      (Subgroup.zpowers c.1) b)

/-- **The dual Selmer classes are exactly the image of the dual class map.** -/
theorem mem_image_dualClassMap_iff
    (x : primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C) :
    x ∈ dualClassMap p k Ω K T M S C ''
        (dualSelmer p k Ω K N T M S :
          Set ((Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))) ↔
      IsDualSelmerClass p k Ω K N hKN T M S C x := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    exact ⟨b, rfl, hb1, hb2, hb3, hb4⟩
  · rintro ⟨b, hclass, hb1, hb2, hb3, hb4⟩
    refine ⟨b, ⟨hb1, hb2, hb3, hb4⟩, ?_⟩
    have hcomp1 : ∀ A : {A // A ∈ S},
        toClass p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (SSGRoute.decomp k A.1) b = x.1 A := by
      intro A
      have h := congrArg (fun z : primalClasses p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C => z.1 A) hclass
      simpa [primalClassOf] using h
    have hcomp2 : ∀ c : {c // c ∈ C},
        toClass p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (Subgroup.zpowers c.1) b = x.2 c := by
      intro c
      have h := congrArg (fun z : primalClasses p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C => z.2 c) hclass
      simpa [primalClassOf] using h
    refine Prod.ext ?_ ?_
    · funext A
      exact hcomp1 A
    · funext c
      exact hcomp2 c



end DualSelmer

/-! ## Linearity of `toClass` and of the local class maps -/

section ClassMapLinear

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]

/-- `toClass` on the locally constant cocycles, as an additive map. -/
noncomputable def toClassAddHom (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    lcCocycles p k Ω K M H →+ H1loc p k Ω K M H :=
  AddMonoidHom.mk' (fun f => toClass p k Ω K M H f.1)
    (fun f g => toClass_add p k Ω K M H f.2 g.2)

/-- **`𝔽_p`-linearity of `toClass`**. -/
theorem toClass_smul (H : Subgroup (Ω ≃ₐ[k] Ω)) (r : ZMod p) {f : (Ω ≃ₐ[k] Ω) → M}
    (hf : f ∈ lcCocycles p k Ω K M H) :
    toClass p k Ω K M H (r • f) = r • toClass p k Ω K M H f := by
  have h := (AddMonoidHom.toZModLinearMap p (toClassAddHom p k Ω K M H)).map_smul r ⟨f, hf⟩
  simpa [toClassAddHom] using h

end ClassMapLinear




/-! ## An additive map between `𝔽_p`-modules is `𝔽_p`-linear -/

section AddHomSmul

/-- **Additivity implies `𝔽_p`-linearity** for `ZMod n`-modules.  Stated without any `→ₗ` type, so
that it can be used where instance search over `ZMod n` is expensive or ambiguous. -/
theorem addHom_smul {n : ℕ} {A B : Type} [AddCommGroup A] [AddCommGroup B]
    [Module (ZMod n) A] [Module (ZMod n) B] (f : A →+ B) (c : ZMod n) (a : A) :
    f (c • a) = c • f a :=
  (AddMonoidHom.toZModLinearMap n f).map_smul c a

end AddHomSmul





/-! ## The product pairing on the local class spaces -/

section ProductPairingFun

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))

local instance : AddCommGroup (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : DistribMulAction (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance
local instance : SMulCommClass (K ≃ₐ[k] K) (ZMod p) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance

/-- **The product of the local pairings**, as a plain function of the two local class spaces: the
sum over one place per prime of `S` and one involution per class in `C`.  It is additive in each
variable (`productFormFun_add_left`, `productFormFun_add_right`), which is what
`wbot_le_of_additive` needs. -/
noncomputable def productFormFun
    (B : ∀ H : Subgroup (Ω ≃ₐ[k] Ω), H1loc p k Ω K M H →ₗ[ZMod p]
      H1loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) H →ₗ[ZMod p] ZMod p) :
    primalClasses p k Ω K M S C →
      primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C →
        ZMod p :=
  fun x y => (∑ A ∈ S.attach, B (SSGRoute.decomp k A.1) (x.1 A) (y.1 A))
    + (∑ c ∈ C.attach, B (Subgroup.zpowers c.1) (x.2 c) (y.2 c))

theorem productFormFun_add_left
    (B : ∀ H : Subgroup (Ω ≃ₐ[k] Ω), H1loc p k Ω K M H →ₗ[ZMod p]
      H1loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) H →ₗ[ZMod p] ZMod p)
    (x x' : primalClasses p k Ω K M S C)
    (y : primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C) :
    productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S) (C := C) B (x + x') y
      = productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S) (C := C) B x y + productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S) (C := C) B x' y := by
  classical
  have h1 : (∑ A ∈ S.attach, B (SSGRoute.decomp k A.1) ((x + x').1 A) (y.1 A))
      = (∑ A ∈ S.attach, B (SSGRoute.decomp k A.1) (x.1 A) (y.1 A))
        + (∑ A ∈ S.attach, B (SSGRoute.decomp k A.1) (x'.1 A) (y.1 A)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun A _ => by
      show ((B (SSGRoute.decomp k A.1)) (x.1 A + x'.1 A)) (y.1 A)
        = ((B (SSGRoute.decomp k A.1)) (x.1 A)) (y.1 A)
          + ((B (SSGRoute.decomp k A.1)) (x'.1 A)) (y.1 A)
      exact congrArg (fun (f : H1loc p k Ω K (Work.SSGRoute.DualMod p
          (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A.1) →ₗ[ZMod p] ZMod p) => f (y.1 A))
        (map_add (B (SSGRoute.decomp k A.1)) (x.1 A) (x'.1 A)))
  have h2 : (∑ c ∈ C.attach, B (Subgroup.zpowers c.1) ((x + x').2 c) (y.2 c))
      = (∑ c ∈ C.attach, B (Subgroup.zpowers c.1) (x.2 c) (y.2 c))
        + (∑ c ∈ C.attach, B (Subgroup.zpowers c.1) (x'.2 c) (y.2 c)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun c _ => by
      show ((B (Subgroup.zpowers c.1)) (x.2 c + x'.2 c)) (y.2 c)
        = ((B (Subgroup.zpowers c.1)) (x.2 c)) (y.2 c)
          + ((B (Subgroup.zpowers c.1)) (x'.2 c)) (y.2 c)
      exact congrArg (fun (f : H1loc p k Ω K (Work.SSGRoute.DualMod p
          (TensorProduct (ZMod p) M T)) (Subgroup.zpowers c.1) →ₗ[ZMod p] ZMod p) => f (y.2 c))
        (map_add (B (Subgroup.zpowers c.1)) (x.2 c) (x'.2 c)))
  simp only [productFormFun]
  rw [h1, h2]
  abel

theorem productFormFun_add_right
    (B : ∀ H : Subgroup (Ω ≃ₐ[k] Ω), H1loc p k Ω K M H →ₗ[ZMod p]
      H1loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) H →ₗ[ZMod p] ZMod p)
    (x : primalClasses p k Ω K M S C)
    (y y' : primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C) :
    productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S) (C := C) B x (y + y')
      = productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S) (C := C) B x y + productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S) (C := C) B x y' := by
  classical
  have h1 : (∑ A ∈ S.attach, B (SSGRoute.decomp k A.1) (x.1 A) ((y + y').1 A))
      = (∑ A ∈ S.attach, B (SSGRoute.decomp k A.1) (x.1 A) (y.1 A))
        + (∑ A ∈ S.attach, B (SSGRoute.decomp k A.1) (x.1 A) (y'.1 A)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun A _ => by
      show ((B (SSGRoute.decomp k A.1)) (x.1 A)) (y.1 A + y'.1 A)
        = ((B (SSGRoute.decomp k A.1)) (x.1 A)) (y.1 A)
          + ((B (SSGRoute.decomp k A.1)) (x.1 A)) (y'.1 A)
      exact map_add ((B (SSGRoute.decomp k A.1)) (x.1 A)) (y.1 A) (y'.1 A))
  have h2 : (∑ c ∈ C.attach, B (Subgroup.zpowers c.1) (x.2 c) ((y + y').2 c))
      = (∑ c ∈ C.attach, B (Subgroup.zpowers c.1) (x.2 c) (y.2 c))
        + (∑ c ∈ C.attach, B (Subgroup.zpowers c.1) (x.2 c) (y'.2 c)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun c _ => by
      show ((B (Subgroup.zpowers c.1)) (x.2 c)) (y.2 c + y'.2 c)
        = ((B (Subgroup.zpowers c.1)) (x.2 c)) (y.2 c)
          + ((B (Subgroup.zpowers c.1)) (x.2 c)) (y'.2 c)
      exact map_add ((B (Subgroup.zpowers c.1)) (x.2 c)) (y.2 c) (y'.2 c))
  simp only [productFormFun]
  rw [h1, h2]
  abel

theorem productFormFun_ndR
    (B : ∀ H : Subgroup (Ω ≃ₐ[k] Ω), H1loc p k Ω K M H →ₗ[ZMod p]
      H1loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) H →ₗ[ZMod p] ZMod p)
    (hndR : ∀ A ∈ S, ∀ y : H1loc p k Ω K (Work.SSGRoute.DualMod p
        (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A),
      (∀ x : H1loc p k Ω K M (SSGRoute.decomp k A),
        B (SSGRoute.decomp k A) x y = 0) → y = 0)
    (hndRc : ∀ c ∈ C, ∀ y : H1loc p k Ω K (Work.SSGRoute.DualMod p
        (TensorProduct (ZMod p) M T)) (Subgroup.zpowers c),
      (∀ x : H1loc p k Ω K M (Subgroup.zpowers c),
        B (Subgroup.zpowers c) x y = 0) → y = 0)
    (y : primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C)
    (hy : ∀ x : primalClasses p k Ω K M S C,
      productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S) (C := C)
        B x y = 0) :
    y = 0 := by
  classical
  refine Prod.ext ?_ ?_
  · funext A
    refine hndR A.1 A.2 (y.1 A) (fun v => ?_)
    have hS : (∑ A' ∈ S.attach, B (SSGRoute.decomp k A'.1)
        ((Function.update (0 : ∀ a : {a // a ∈ S}, H1loc p k Ω K M
            (SSGRoute.decomp k a.1)) A v) A') (y.1 A'))
        = B (SSGRoute.decomp k A.1) v (y.1 A) := by
      rw [Finset.sum_eq_single A]
      · rw [show (Function.update (0 : ∀ a : {a // a ∈ S}, H1loc p k Ω K M
            (SSGRoute.decomp k a.1)) A v) A = v from
          Function.update_self A v (0 : ∀ a : {a // a ∈ S}, H1loc p k Ω K M
            (SSGRoute.decomp k a.1))]
      · intro A' _ hA'
        rw [show (Function.update (0 : ∀ a : {a // a ∈ S}, H1loc p k Ω K M
              (SSGRoute.decomp k a.1)) A v) A' = 0 from
            Function.update_of_ne hA' v (0 : ∀ a : {a // a ∈ S}, H1loc p k Ω K M
              (SSGRoute.decomp k a.1)),
          map_zero, LinearMap.zero_apply]
      · intro h
        exact absurd (Finset.mem_attach _ A) h
    have hC : (∑ c ∈ C.attach, B (Subgroup.zpowers c.1)
        ((0 : ∀ c : {c // c ∈ C}, H1loc p k Ω K M (Subgroup.zpowers c.1)) c) (y.2 c)) = 0 := by
      refine Finset.sum_eq_zero (fun c _ => ?_)
      simp only [Pi.zero_apply, map_zero, LinearMap.zero_apply]
    have hx := hy ⟨Function.update (0 : ∀ a : {a // a ∈ S}, H1loc p k Ω K M
      (SSGRoute.decomp k a.1)) A v, 0⟩
    simp only [productFormFun] at hx
    rw [hS, hC, add_zero] at hx
    exact hx
  · funext A
    refine hndRc A.1 A.2 (y.2 A) (fun v => ?_)
    have hS : (∑ A' ∈ S.attach, B (SSGRoute.decomp k A'.1)
        ((0 : ∀ a : {a // a ∈ S}, H1loc p k Ω K M (SSGRoute.decomp k a.1)) A')
        (y.1 A')) = 0 := by
      refine Finset.sum_eq_zero (fun A' _ => ?_)
      simp only [Pi.zero_apply, map_zero, LinearMap.zero_apply]
    have hC : (∑ c ∈ C.attach, B (Subgroup.zpowers c.1)
        ((Function.update (0 : ∀ c' : {c' // c' ∈ C}, H1loc p k Ω K M
            (Subgroup.zpowers c'.1)) A v) c) (y.2 c))
        = B (Subgroup.zpowers A.1) v (y.2 A) := by
      rw [Finset.sum_eq_single A]
      · rw [show (Function.update (0 : ∀ c' : {c' // c' ∈ C}, H1loc p k Ω K M
            (Subgroup.zpowers c'.1)) A v) A = v from
          Function.update_self A v (0 : ∀ c' : {c' // c' ∈ C}, H1loc p k Ω K M
            (Subgroup.zpowers c'.1))]
      · intro c _ hc
        rw [show (Function.update (0 : ∀ c' : {c' // c' ∈ C}, H1loc p k Ω K M
              (Subgroup.zpowers c'.1)) A v) c = 0 from
            Function.update_of_ne hc v (0 : ∀ c' : {c' // c' ∈ C}, H1loc p k Ω K M
              (Subgroup.zpowers c'.1)),
          map_zero, LinearMap.zero_apply]
      · intro h
        exact absurd (Finset.mem_attach _ A) h
    have hx := hy ⟨0, Function.update (0 : ∀ c' : {c' // c' ∈ C}, H1loc p k Ω K M
      (Subgroup.zpowers c'.1)) A v⟩
    simp only [productFormFun] at hx
    rw [hS, hC, zero_add] at hx
    exact hx

theorem productFormFun_ndL
    (B : ∀ H : Subgroup (Ω ≃ₐ[k] Ω), H1loc p k Ω K M H →ₗ[ZMod p]
      H1loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) H →ₗ[ZMod p] ZMod p)
    (hndL : ∀ A ∈ S, ∀ x : H1loc p k Ω K M (SSGRoute.decomp k A),
      (∀ y : H1loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (SSGRoute.decomp k A), B (SSGRoute.decomp k A) x y = 0) → x = 0)
    (hndLc : ∀ c ∈ C, ∀ x : H1loc p k Ω K M (Subgroup.zpowers c),
      (∀ y : H1loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
        (Subgroup.zpowers c), B (Subgroup.zpowers c) x y = 0) → x = 0)
    (x : primalClasses p k Ω K M S C)
    (hx : ∀ y : primalClasses p k Ω K (Work.SSGRoute.DualMod p
      (TensorProduct (ZMod p) M T)) S C,
      productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S) (C := C)
        B x y = 0) :
    x = 0 := by
  classical
  refine Prod.ext ?_ ?_
  · funext A
    refine hndL A.1 A.2 (x.1 A) (fun v => ?_)
    have hS : (∑ A' ∈ S.attach, B (SSGRoute.decomp k A'.1) (x.1 A')
        ((Function.update (0 : ∀ a : {a // a ∈ S}, H1loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
            (SSGRoute.decomp k a.1)) A v) A'))
        = B (SSGRoute.decomp k A.1) (x.1 A) v := by
      rw [Finset.sum_eq_single A]
      · rw [show (Function.update (0 : ∀ a : {a // a ∈ S}, H1loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
            (SSGRoute.decomp k a.1)) A v) A = v from
          Function.update_self A v (0 : ∀ a : {a // a ∈ S}, H1loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
            (SSGRoute.decomp k a.1))]
      · intro A' _ hA'
        rw [show (Function.update (0 : ∀ a : {a // a ∈ S}, H1loc p k Ω K
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
              (SSGRoute.decomp k a.1)) A v) A' = 0 from
            Function.update_of_ne hA' v (0 : ∀ a : {a // a ∈ S}, H1loc p k Ω K
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
              (SSGRoute.decomp k a.1)),
          map_zero]
      · intro h
        exact absurd (Finset.mem_attach _ A) h
    have hC : (∑ c ∈ C.attach, B (Subgroup.zpowers c.1) (x.2 c)
        ((0 : ∀ c : {c // c ∈ C}, H1loc p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (Subgroup.zpowers c.1)) c)) = 0 := by
      refine Finset.sum_eq_zero (fun c _ => ?_)
      simp only [Pi.zero_apply, map_zero]
    have hxy := hx ⟨Function.update (0 : ∀ a : {a // a ∈ S}, H1loc p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
      (SSGRoute.decomp k a.1)) A v, 0⟩
    simp only [productFormFun] at hxy
    rw [hS, hC, add_zero] at hxy
    exact hxy
  · funext A
    refine hndLc A.1 A.2 (x.2 A) (fun v => ?_)
    have hS : (∑ A' ∈ S.attach, B (SSGRoute.decomp k A'.1) (x.1 A')
        ((0 : ∀ a : {a // a ∈ S}, H1loc p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (SSGRoute.decomp k a.1)) A')) = 0 := by
      refine Finset.sum_eq_zero (fun A' _ => ?_)
      simp only [Pi.zero_apply, map_zero]
    have hC : (∑ c ∈ C.attach, B (Subgroup.zpowers c.1) (x.2 c)
        ((Function.update (0 : ∀ c' : {c' // c' ∈ C}, H1loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
            (Subgroup.zpowers c'.1)) A v) c))
        = B (Subgroup.zpowers A.1) (x.2 A) v := by
      rw [Finset.sum_eq_single A]
      · rw [show (Function.update (0 : ∀ c' : {c' // c' ∈ C}, H1loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
            (Subgroup.zpowers c'.1)) A v) A = v from
          Function.update_self A v (0 : ∀ c' : {c' // c' ∈ C}, H1loc p k Ω K
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
            (Subgroup.zpowers c'.1))]
      · intro c _ hc
        rw [show (Function.update (0 : ∀ c' : {c' // c' ∈ C}, H1loc p k Ω K
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
              (Subgroup.zpowers c'.1)) A v) c = 0 from
            Function.update_of_ne hc v (0 : ∀ c' : {c' // c' ∈ C}, H1loc p k Ω K
              (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
              (Subgroup.zpowers c'.1)),
          map_zero]
      · intro h
        exact absurd (Finset.mem_attach _ A) h
    have hxy := hx ⟨0, Function.update (0 : ∀ c' : {c' // c' ∈ C}, H1loc p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
      (Subgroup.zpowers c'.1)) A v⟩
    simp only [productFormFun] at hxy
    rw [hS, hC, zero_add] at hxy
    exact hxy

end ProductPairingFun


section DualClassSet

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))

-- the coefficient module `M' = DualMod p (M ⊗ T)` is pinned as a local instance so that the
-- (deep) instance search for its `Module` structure does not have to be repeated
local instance : AddCommGroup (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : DistribMulAction (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance
local instance : SMulCommClass (K ≃ₐ[k] K) (ZMod p) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance

omit hKN in
theorem isCocycleOn_of_mem_dualSelmer
    {b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)}
    (h : b ∈ dualSelmer p k Ω K N T M S) (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    b ∈ lcCocycles p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) H :=
  ⟨isCocycleOn_mono (SSGRoute.res k K) le_top h.1, isLocConstOn_mono le_top h.2.1⟩

omit hKN in
/-- The local class map of the relaxed dual Selmer module, as an `𝔽_p`-linear map. -/
noncomputable def dualClassMapLin :
    dualSelmer p k Ω K N T M S →ₗ[ZMod p]
      primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C :=
  { toFun := fun b => dualClassMap (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      (S := S) (C := C) b.1
    map_add' := fun b b' => by
      refine Prod.ext ?_ ?_
      · funext A
        exact toClass_add p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (SSGRoute.decomp k A.1)
          (isCocycleOn_of_mem_dualSelmer p k Ω K N T M S b.2 _)
          (isCocycleOn_of_mem_dualSelmer p k Ω K N T M S b'.2 _)
      · funext c
        exact toClass_add p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (Subgroup.zpowers c.1)
          (isCocycleOn_of_mem_dualSelmer p k Ω K N T M S b.2 _)
          (isCocycleOn_of_mem_dualSelmer p k Ω K N T M S b'.2 _)
    map_smul' := fun r b => by
      refine Prod.ext ?_ ?_
      · funext A
        exact toClass_smul p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (SSGRoute.decomp k A.1) r
          (isCocycleOn_of_mem_dualSelmer p k Ω K N T M S b.2 _)
      · funext c
        exact toClass_smul p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (Subgroup.zpowers c.1) r
          (isCocycleOn_of_mem_dualSelmer p k Ω K N T M S b.2 _) }

omit hKN in
/-- The **dual Selmer class module** `W`. -/
noncomputable def dualClassSet :
    Submodule (ZMod p) (primalClasses p k Ω K (Work.SSGRoute.DualMod p
      (TensorProduct (ZMod p) M T)) S C) :=
  (dualClassMapLin p k Ω K N T M S C).range

/-- The dual Selmer class module is exactly the set of dual Selmer classes. -/
theorem mem_dualClassSet_iff
    (y : primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C) :
    y ∈ dualClassSet p k Ω K N T M S C ↔ IsDualSelmerClass p k Ω K N hKN T M S C y := by
  constructor
  · intro hy
    obtain ⟨b, hb⟩ := LinearMap.mem_range.mp hy
    exact (mem_image_dualClassMap_iff p k Ω K N hKN T M S C y).mp ⟨b.1, b.2, hb⟩
  · intro hy
    obtain ⟨b, hb, hcls⟩ := (mem_image_dualClassMap_iff p k Ω K N hKN T M S C y).mpr hy
    exact LinearMap.mem_range.mpr ⟨⟨b, hb⟩, hcls⟩

/-- The cardinality form used by the counting identity. -/
theorem natCard_dualClassSet :
    Nat.card (dualClassSet p k Ω K N T M S C) =
      Nat.card {y : primalClasses p k Ω K (Work.SSGRoute.DualMod p
          (TensorProduct (ZMod p) M T)) S C //
        IsDualSelmerClass p k Ω K N hKN T M S C y} :=
  Nat.card_congr (Equiv.subtypeEquivRight
    (fun y => (mem_dualClassSet_iff p k Ω K N hKN T M S C y)))

end DualClassSet

section ClassSet

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))

omit hKN in
theorem isCocycleOn_of_mem_primalSelmer {ε : (Ω ≃ₐ[k] Ω) → M}
    (h : ε ∈ primalSelmer (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M) (S := S))
    (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    ε ∈ lcCocycles p k Ω K M H :=
  ⟨isCocycleOn_mono (SSGRoute.res k K) le_top h.1, isLocConstOn_mono le_top h.2.1⟩

omit hKN in
/-- The local class map of the relaxed primal Selmer module, as an `𝔽_p`-linear map. -/
noncomputable def primalClassMapLin :
    primalSelmer (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M) (S := S) →ₗ[ZMod p]
      primalClasses p k Ω K M S C :=
  { toFun := fun ε => primalClassMap (p := p) (k := k) (Ω := Ω) (K := K) (M := M) (S := S)
      (C := C) ε.1
    map_add' := fun ε ε' => by
      refine Prod.ext ?_ ?_
      · funext A
        exact toClass_add p k Ω K M (SSGRoute.decomp k A.1)
          (isCocycleOn_of_mem_primalSelmer (p := p) (k := k) (Ω := Ω) (K := K) (N := N)
            (M := M) (S := S) ε.2 _)
          (isCocycleOn_of_mem_primalSelmer (p := p) (k := k) (Ω := Ω) (K := K) (N := N)
            (M := M) (S := S) ε'.2 _)
      · funext c
        exact toClass_add p k Ω K M (Subgroup.zpowers c.1)
          (isCocycleOn_of_mem_primalSelmer (p := p) (k := k) (Ω := Ω) (K := K) (N := N)
            (M := M) (S := S) ε.2 _)
          (isCocycleOn_of_mem_primalSelmer (p := p) (k := k) (Ω := Ω) (K := K) (N := N)
            (M := M) (S := S) ε'.2 _)
    map_smul' := fun r ε => by
      refine Prod.ext ?_ ?_
      · funext A
        exact toClass_smul p k Ω K M (SSGRoute.decomp k A.1) r
          (isCocycleOn_of_mem_primalSelmer (p := p) (k := k) (Ω := Ω) (K := K) (N := N)
            (M := M) (S := S) ε.2 _)
      · funext c
        exact toClass_smul p k Ω K M (Subgroup.zpowers c.1) r
          (isCocycleOn_of_mem_primalSelmer (p := p) (k := k) (Ω := Ω) (K := K) (N := N)
            (M := M) (S := S) ε.2 _) }

omit hKN in
/-- The **realizable class module** `V`: the image of the relaxed primal Selmer module in the
local class space. -/
noncomputable def primalClassSet : Submodule (ZMod p) (primalClasses p k Ω K M S C) :=
  (primalClassMapLin (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M) (S := S)
    (C := C)).range

/-- The realizable class module is exactly the set of realizable classes. -/
theorem mem_primalClassSet_iff (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (x : primalClasses p k Ω K M S C) :
    x ∈ primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M) (S := S)
        (C := C) ↔
      IsRealizableClass p k Ω K N hKN M S C x := by
  constructor
  · intro hx
    obtain ⟨ε, hε⟩ := LinearMap.mem_range.mp hx
    exact (mem_image_primalClassMap_iff p k Ω K N hKN M S C hCinv x).mp ⟨ε.1, ε.2, hε⟩
  · intro hx
    obtain ⟨ε, hε, hcls⟩ :=
      (mem_image_primalClassMap_iff p k Ω K N hKN M S C hCinv x).mpr hx
    exact LinearMap.mem_range.mpr ⟨⟨ε, hε⟩, hcls⟩

/-- The cardinality form used by the counting identity. -/
theorem natCard_primalClassSet (hCinv : ∀ c ∈ C, c ^ 2 = 1) :
    Nat.card (primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M) (S := S)
        (C := C)) =
      Nat.card {x : primalClasses p k Ω K M S C //
        IsRealizableClass p k Ω K N hKN M S C x} :=
  Nat.card_congr (Equiv.subtypeEquivRight
    (fun x => (mem_primalClassSet_iff p k Ω K N hKN M S C hCinv x)))

end ClassSet

section ClassMapPairing

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))

local instance : AddCommGroup (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : DistribMulAction (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance
local instance : SMulCommClass (K ≃ₐ[k] K) (ZMod p) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance

/-- **The product pairing on the local class maps** is the sum of the local pairings of the two
global cocycles.  This is the form in which reciprocity (`pt_orthogonality_of_realizable`) is
applied: with `pair` the local pairings, `hB` their defining property on classes. -/
theorem productFormFun_classMap
    (B : ∀ H : Subgroup (Ω ≃ₐ[k] Ω), H1loc p k Ω K M H →ₗ[ZMod p]
      H1loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) H →ₗ[ZMod p] ZMod p)
    (pair : ∀ H : Subgroup (Ω ≃ₐ[k] Ω), ((Ω ≃ₐ[k] Ω) → M) → ((Ω ≃ₐ[k] Ω) →
      Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hB : ∀ (H : Subgroup (Ω ≃ₐ[k] Ω)) (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      a ∈ lcCocycles p k Ω K M H → b ∈ lcCocycles p k Ω K
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) H →
      B H (toClass p k Ω K M H a)
        (toClass p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) H b)
        = pair H a b)
    (ε : (Ω ≃ₐ[k] Ω) → M) (hε : ε ∈ primalSelmer p k Ω K N M S)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : b ∈ dualSelmer p k Ω K N T M S) :
    productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S) (C := C) B
        (primalClassMap p k Ω K M S C ε) (dualClassMap p k Ω K T M S C b)
      = (∑ A ∈ S.attach, pair (SSGRoute.decomp k A.1) ε b)
        + (∑ c ∈ C.attach, pair (Subgroup.zpowers c.1) ε b) := by
  classical
  simp only [productFormFun, primalClassMap, dualClassMap]
  congr 1
  · exact Finset.sum_congr rfl (fun A _ => hB (SSGRoute.decomp k A.1) ε b
      (isCocycleOn_of_mem_primalSelmer p k Ω K N M S hε _)
      (isCocycleOn_of_mem_dualSelmer p k Ω K N T M S hb _))
  · exact Finset.sum_congr rfl (fun c _ => hB (Subgroup.zpowers c.1) ε b
      (isCocycleOn_of_mem_primalSelmer p k Ω K N M S hε _)
      (isCocycleOn_of_mem_dualSelmer p k Ω K N T M S hb _))


/-- **The product pairing on the local class maps**, in the form in which the two sides are only
known at the places of `S` and the involutions of `C` (the only groups at which the local axioms
are available). -/
theorem productFormFun_classMap'
    (B : ∀ H : Subgroup (Ω ≃ₐ[k] Ω), H1loc p k Ω K M H →ₗ[ZMod p]
      H1loc p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) H →ₗ[ZMod p] ZMod p)
    (pair : ∀ H : Subgroup (Ω ≃ₐ[k] Ω), ((Ω ≃ₐ[k] Ω) → M) → ((Ω ≃ₐ[k] Ω) →
      Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) → ZMod p)
    (hB : ∀ A ∈ S, ∀ (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      a ∈ lcCocycles p k Ω K M (SSGRoute.decomp k A) → b ∈ lcCocycles p k Ω K
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (SSGRoute.decomp k A) →
      B (SSGRoute.decomp k A) (toClass p k Ω K M (SSGRoute.decomp k A) a)
        (toClass p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (SSGRoute.decomp k A) b)
        = pair (SSGRoute.decomp k A) a b)
    (hBc : ∀ c ∈ C, ∀ (a : (Ω ≃ₐ[k] Ω) → M)
        (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)),
      a ∈ lcCocycles p k Ω K M (Subgroup.zpowers c) → b ∈ lcCocycles p k Ω K
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) (Subgroup.zpowers c) →
      B (Subgroup.zpowers c) (toClass p k Ω K M (Subgroup.zpowers c) a)
        (toClass p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
          (Subgroup.zpowers c) b)
        = pair (Subgroup.zpowers c) a b)
    (ε : (Ω ≃ₐ[k] Ω) → M) (hε : ε ∈ primalSelmer p k Ω K N M S)
    (b : (Ω ≃ₐ[k] Ω) → Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))
    (hb : b ∈ dualSelmer p k Ω K N T M S) :
    productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S) (C := C) B
        (primalClassMap p k Ω K M S C ε) (dualClassMap p k Ω K T M S C b)
      = (∑ A ∈ S.attach, pair (SSGRoute.decomp k A.1) ε b)
        + (∑ c ∈ C.attach, pair (Subgroup.zpowers c.1) ε b) := by
  classical
  simp only [productFormFun, primalClassMap, dualClassMap]
  congr 1
  · exact Finset.sum_congr rfl (fun A _ => hB A.1 A.2 ε b
      (isCocycleOn_of_mem_primalSelmer p k Ω K N M S hε _)
      (isCocycleOn_of_mem_dualSelmer p k Ω K N T M S hb _))
  · exact Finset.sum_congr rfl (fun c _ => hBc c.1 c.2 ε b
      (isCocycleOn_of_mem_primalSelmer p k Ω K N M S hε _)
      (isCocycleOn_of_mem_dualSelmer p k Ω K N T M S hb _))


end ClassMapPairing

section CountingSubmodules

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))

local instance : AddCommGroup (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
  inferInstance
local instance : DistribMulAction (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance
local instance : SMulCommClass (K ≃ₐ[k] K) (ZMod p) (Work.SSGRoute.DualMod p
    (TensorProduct (ZMod p) M T)) := inferInstance

/-- **The Poitou–Tate counting identity in the submodule form** used by `wbot_le_of_additive`:
`|V| · |W| = |∏_{S ∪ C} H¹|`. -/
theorem natCard_counting (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hcount : Nat.card {x : primalClasses p k Ω K M S C //
        IsRealizableClass p k Ω K N hKN M S C x} *
      Nat.card {y : primalClasses p k Ω K (Work.SSGRoute.DualMod p
          (TensorProduct (ZMod p) M T)) S C //
        IsDualSelmerClass p k Ω K N hKN T M S C y} =
      Nat.card (primalClasses p k Ω K M S C)) :
    Nat.card (primalClassSet p k Ω K N M S C) *
        Nat.card (dualClassSet p k Ω K N T M S C) =
      Nat.card (primalClasses p k Ω K M S C) := by
  rw [natCard_primalClassSet p k Ω K N hKN M S C hCinv,
    natCard_dualClassSet p k Ω K N hKN T M S C]
  exact hcount

end CountingSubmodules


end SelmerClasses


/-! ## Finiteness of the local `H¹` at an involution -/

section ZpowersFinite

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- **The local `H¹` at the subgroup generated by an involution is finite.**  For `c ^ 2 = 1` the
group `⟨c⟩` has at most two elements, a locally constant cocycle on it is determined by its value
at `c` (which lies in `ker (1 + c)`), and coboundaries are parametrised by `M`; hence
`H¹(⟨c⟩, M) ≅ ker (1 + c) / (1 − c)M` is finite when `M` is. -/
theorem finite_H1loc_zpowers (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc : c ^ 2 = 1) :
    Finite (H1loc p k Ω K M (Subgroup.zpowers c)) := by
  classical
  rcases eq_or_ne c 1 with rfl | hc1
  · have : Subsingleton (H1loc p k Ω K M (Subgroup.zpowers (1 : Ω ≃ₐ[k] Ω))) := by
      refine ⟨fun a b => ?_⟩
      have key : ∀ y : H1loc p k Ω K M (Subgroup.zpowers (1 : Ω ≃ₐ[k] Ω)), y = 0 := by
        intro y
        obtain ⟨f, hfmem, hfy⟩ :=
          toClass_surjective p k Ω K M (Subgroup.zpowers (1 : Ω ≃ₐ[k] Ω)) y
        have hcoc := (Ach.isCocycleOn_zpowers_iff (SSGRoute.res k K) 1 (by simp) f).mp hfmem.1
        have hcob : f ∈ coboundaries p k Ω K M (Subgroup.zpowers (1 : Ω ≃ₐ[k] Ω)) := by
          refine ⟨0, fun g hg => ?_⟩
          have hg1 : g = 1 := by
            rcases Ach.mem_zpowers_eq_one_or (1 : Ω ≃ₐ[k] Ω) (by simp) hg with h | h
            · exact h
            · exact h
          rw [hg1, hcoc.1, map_one, one_smul, sub_self]
        rw [← hfy, (toClass_eq_zero_iff p k Ω K M _ hfmem).mpr hcob]
      exact (key a).trans (key b).symm
    exact Finite.of_subsingleton
  · refine Finite.of_surjective
      (fun m : {m : M // m + SSGRoute.res k K c • m = 0} =>
        toClass p k Ω K M (Subgroup.zpowers c) (fun σ => if σ = c then m.1 else 0)) ?_
    intro y
    obtain ⟨f, hfmem, hfy⟩ := toClass_surjective p k Ω K M (Subgroup.zpowers c) y
    have hcoc := (Ach.isCocycleOn_zpowers_iff (SSGRoute.res k K) c hc f).mp hfmem.1
    have hmem : (fun σ : Ω ≃ₐ[k] Ω => if σ = c then f c else 0) ∈
        lcCocycles p k Ω K M (Subgroup.zpowers c) := by
      refine ⟨(Ach.isCocycleOn_zpowers_iff (SSGRoute.res k K) c hc _).mpr ⟨?_, ?_⟩,
        isLocConstOn_zpowers c hc _⟩
      · rw [if_neg (fun h : (1 : Ω ≃ₐ[k] Ω) = c => hc1 h.symm)]
      · rw [if_pos rfl]
        exact hcoc.2
    refine ⟨⟨f c, hcoc.2⟩, ?_⟩
    have hsubmem : (fun σ : Ω ≃ₐ[k] Ω => (if σ = c then f c else 0) - f σ) ∈
        lcCocycles p k Ω K M (Subgroup.zpowers c) := Submodule.sub_mem _ hmem hfmem
    have hsub : (fun σ : Ω ≃ₐ[k] Ω => (if σ = c then f c else 0) - f σ) ∈
        coboundaries p k Ω K M (Subgroup.zpowers c) := by
      refine ⟨0, fun g hg => ?_⟩
      rcases Ach.mem_zpowers_eq_one_or c hc hg with h1 | hcg
      · rw [h1]
        have hif : (if (1 : Ω ≃ₐ[k] Ω) = c then f c else 0) = 0 :=
          if_neg (fun h => hc1 h.symm)
        show (if (1 : Ω ≃ₐ[k] Ω) = c then f c else 0) - f 1
          = (SSGRoute.res k K) 1 • 0 - 0
        rw [hif, hcoc.1, sub_zero, map_one, one_smul, sub_self]
      · rw [hcg]
        show (if c = c then f c else 0) - f c = (SSGRoute.res k K) c • 0 - 0
        rw [if_pos rfl, sub_self, smul_zero, sub_self]
    have hsame : toClass p k Ω K M (Subgroup.zpowers c)
          (fun σ : Ω ≃ₐ[k] Ω => if σ = c then f c else 0)
        = toClass p k Ω K M (Subgroup.zpowers c) f := by
      have hsplit : (fun σ : Ω ≃ₐ[k] Ω => if σ = c then f c else 0)
          = f + (fun σ : Ω ≃ₐ[k] Ω => (if σ = c then f c else 0) - f σ) := by
        ext σ
        simp only [Pi.add_apply]
        abel
      rw [hsplit, toClass_add p k Ω K M _ hfmem hsubmem,
        (toClass_eq_zero_iff p k Ω K M _ hsubmem).mpr hsub, add_zero]
    exact hsame.trans hfy

/-! ## Finiteness of the local class spaces -/

section ClassesFinite

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]

/-- **The local class space `primalClasses` is finite**, given finiteness of each of the local
`H¹`-groups involved.  This is the hypothesis under which the Poitou–Tate counting identity
`Work.SSGRoute.PT.pt_selmer_counting_identity` is a statement about genuine cardinalities; the
finiteness of the local groups themselves is `Work.SSGRoute.PT.finite_H1loc_zpowers` (involutions)
and the arithmetic input `Submission.Work.SSGRoute.finite_localField_homs` (finite places). -/
theorem finite_primalClasses (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (S : Finset (ValuationSubring Ω)) (C : Finset (Ω ≃ₐ[k] Ω))
    (hS : ∀ A ∈ S, Finite (H1loc p k Ω K M (SSGRoute.decomp k A)))
    (hC : ∀ c ∈ C, Finite (H1loc p k Ω K M (Subgroup.zpowers c))) :
    Finite (primalClasses p k Ω K M S C) := by
  haveI : ∀ A : {A // A ∈ S}, Finite (H1loc p k Ω K M (SSGRoute.decomp k A.1)) :=
    fun A => hS A.1 A.2
  haveI : ∀ c : {c // c ∈ C}, Finite (H1loc p k Ω K M (Subgroup.zpowers c.1)) :=
    fun c => hC c.1 c.2
  exact inferInstance

end ClassesFinite

end ZpowersFinite


/-- **The counting step, for a pairing that is only known to be *additive* in each variable.**
This is the form in which the product pairing of local Tate pairings is available: bilinearity
over `𝔽_p` is then automatic (an additive map between `𝔽_p`-modules is `𝔽_p`-linear), and the
reduction goes through `wbot_le_of_natCard`. -/
theorem wbot_le_of_additive {p : ℕ} [Fact p.Prime] {P Q : Type*}
    [AddCommGroup P] [Module (ZMod p) P] [Finite P]
    [AddCommGroup Q] [Module (ZMod p) Q] [Finite Q]
    (β : P → Q → ZMod p)
    (haddL : ∀ x x' y, β (x + x') y = β x y + β x' y)
    (haddR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hndL : ∀ x : P, (∀ y : Q, β x y = 0) → x = 0)
    (hndR : ∀ y : Q, (∀ x : P, β x y = 0) → y = 0)
    (V : Submodule (ZMod p) P) (W : Submodule (ZMod p) Q)
    (hVW : ∀ x ∈ V, ∀ y : W, β x y = 0)
    (hcard : Nat.card V * Nat.card W = Nat.card P) :
    ∀ x : P, (∀ y : W, β x y = 0) → x ∈ V := by
  haveI hPfin : Module.Finite (ZMod p) P := Module.Finite.of_finite
  haveI hQfin : Module.Finite (ZMod p) Q := Module.Finite.of_finite
  let inner : ∀ (_ : P), Q →+ ZMod p :=
    fun x => AddMonoidHom.mk' (β x) (fun y y' => haddR x y y')
  have hinner : ∀ x x' : P, inner (x + x') = inner x + inner x' := by
    intro x x'
    ext y
    exact haddL x x' y
  let F : P →+ (Q →ₗ[ZMod p] ZMod p) :=
    AddMonoidHom.mk' (fun x => AddMonoidHom.toZModLinearMap p (inner x))
      (fun x x' => by
        rw [hinner x x']
        ext y
        rfl)
  let βlin : P →ₗ[ZMod p] Q →ₗ[ZMod p] ZMod p := AddMonoidHom.toZModLinearMap p F
  have hβ : ∀ x y, βlin x y = β x y := fun x y => rfl
  have hndL' : ∀ x : P, (∀ y : Q, βlin x y = 0) → x = 0 := by
    intro x hx
    exact hndL x (fun y => by rw [← hβ]; exact hx y)
  have hndR' : ∀ y : Q, (∀ x : P, βlin x y = 0) → y = 0 := by
    intro y hy
    exact hndR y (fun x => by rw [← hβ]; exact hy x)
  have hVW' : ∀ x ∈ V, ∀ y : W, βlin x y = 0 := by
    intro x hx y
    rw [hβ]
    exact hVW x hx y
  exact wbot_le_of_natCard βlin hndL' hndR' V W hVW' hcard


end

end Work.SSGRoute.PT
