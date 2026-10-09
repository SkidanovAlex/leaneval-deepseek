import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.DualMod.Main
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.PT.pt_selmer_counting
import Submission.Work.SSGRoute.PT.pt_counting_assembly
import Submission.Work.SSGRoute.PT.pt_canonical_aux
import Submission.Work.SSGRoute.PT.pt_canonical_assembly
import Submission.Work.SSGRoute.PT.pt_reciprocal_set
import Submission.Work.SSGRoute.PT.converseRepr
import Submission.Work.SSGRoute.PT.finite_primalClasses_general
import Submission.Work.SSGRoute.PT.finite_dualMod_tensor
import Submission.Work.SSGRoute.PT.pt_counting_identity_aux
import Submission.Work.SSGRoute.EulerSymm.kummerUDSideConditions
import Submission.Work.SSGRoute.PT.canonical_localPairing_reciprocity_converse
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Poitou–Tate counting identity: the proof, and its single remaining input

This file holds `Work.SSGRoute.PT.pt_selmer_counting_identity` — the counting identity
`|V| · |W| = |P|` that `Work.SSGRoute.PT.natCard_counting` takes as its hypothesis `hcount`, that
`Work.SSGRoute.PT.pt_canonical_relaxed` consumes as its clause (3), and that
`Work.SSGRoute.PT.pt_counting_identity_h1` states behind the abbreviation
`Work.SSGRoute.PT.CountingIdentity` (`PT/pt_counting_identity_h1.lean`); the two forms are the
*same proposition* (`CountingIdentity` is that `Nat.card` equation by definition).

`V` is the set of realizable classes (the image of the relaxed primal Selmer group in the product
`P = ∏_{S ∪ C} H¹` of the local `H¹`'s), `W` the set of relaxed dual Selmer classes.  Given a
perfect pairing `β : P × P' → 𝔽_p` and the *proved* inclusion `V ⊆ W^⊥`
(`CountAux.primalClassSet_orthogonal_dualClassSet`), the identity is equivalent (via
`natCard_annihilator_mul`) to the *middle exactness* `V = W^⊥` of the Poitou–Tate sequence —
Schmidt–Wingberg's Lemma 10, i.e. Milne, *Arithmetic Duality Theorems*, I.4.10 (b) at `r = 1`, in
the relaxed form.

## State (2026-10-07, measured): the proof is complete modulo the single node `G1⁺`

The theorem **has no `sorry`** and is proved by the five steps below.  Its axiom set is
`[propext, sorryAx, Classical.choice, Quot.sound]`, and the *only* declaration on its proof path
carrying `sorryAx` is the node

  **`Work.SSGRoute.PT.canonical_localPairing_reciprocity_converse`** (`G1⁺`,
  `PT/canonical_localPairing_reciprocity_converse.lean`),

i.e. the canonical local Tate pairing with its local axioms (1)–(5), the reciprocity law (7) and
the *converse* clause (8) — which is the middle exactness `W^⊥ ⊆ V` in representative form.  Every
other input was checked to be `[propext, Classical.choice, Quot.sound]` (see
`PT/pt_counting_identity_aux.lean`, `PT/converseRepr.lean`, `PT/pt_canonical_assembly.lean`,
`PT/pt_counting_assembly.lean`, `PT/finite_primalClasses_general.lean`,
`PT/finite_dualMod_tensor.lean`, `EulerSymm/kummerUDSideConditions.lean`).

`G1⁺` is in turn rooted in the E1aClean leaf `E1aClean.localDictionary_natural_family_arch` (via
the definable local dictionary `g1FinHalf`/`finZB`; `g1FinHalf`'s *definition* mentions the leaf's
statement, so every declaration whose type mentions it reports `sorryAx`).  **When that leaf lands,
this file becomes axiom-clean with no further work.**

## The proof (five steps)

1. **`G1⁺`**: `obtain ⟨pair, hmain, hrec7, hconv8full⟩ := canonical_localPairing_reciprocity_converse …`;
   `hloc : LocalAxioms …` from clauses (1)–(4), `hrec : Recip …` from clause (7), and
   `hconv8 : ConverseRepr …` from clause (8).
2. **The two halves of `V = W^⊥`**: `hconv_of_converse` (`PT/converseRepr.lean`, clause (8)
   gives `W^⊥ ⊆ V`) and `CountAux.primalClassSet_orthogonal_dualClassSet`
   (`PT/pt_counting_identity_aux.lean`, the proved reciprocity `V ⊆ W^⊥`, i.e.
   `pt_orthogonality_of_realizable` through `productFormFun_primalClassOf`).
3. **Finiteness** of both local class spaces: `finite_primalClasses_general` at `M` and at
   `M' = DualMod p (M ⊗ T)` (`finite_dualMod_tensor` + `EulerSymm.finite_of_isCyclotomicDual`).
4. **The product form** `β = productFormFun (localPairingFun … pair hloc)`, additive in each
   variable (`productFormFun_add_left/right`) and non-degenerate in each
   (`productFormFun_ndL/ndR` from `localPairingFun_ndL/ndR`); the annihilator identity is applied
   in its *additive* form `CountAux.natCard_annihilator_mul_additive`.
5. **The counting step**: `Nat.card` conversion (`natCard_primalClassSet`, `natCard_dualClassSet`)
   plus `Nat.card_congr (Equiv.subtypeEquivRight hiff)` and the annihilator cardinality.

Two Lean-side points that cost time and are worth remembering:

* the two *linear-algebra* lemmas now live in the much lighter module
  `PT/pt_counting_identity_aux.lean` (this module imports them), so that they can be used without
  dragging in the `G1⁺` closure;
* the instance search for `Module (ZMod p) (primalClasses …)` does **not** terminate when it is
  left to the elaborator at an application site: the application of
  `CountAux.natCard_annihilator_mul_additive` therefore supplies *every* instance argument
  explicitly, with a type ascription making the goal type concrete (the pattern recorded at
  `PT/pt_canonical_assembly.lean`'s `counting_step_concrete`).  A local `letI` pin of the same
  instance instead produces a non-definitional diamond.

## Superseded material (kept for the record, no longer on the path)

The earlier sessions reduced this node to the *value formula* of the class formation and to the
middle exactness in the `Ext` vocabulary (`PT/NOTE_count_residual_value_formula.md`, the `hVF`
assembly, the E9 route through `pt_sha2_core`); the lead's re-pointing then made the node's
residual exactly `G1⁺`, which is the route implemented here.  The filed
`Work.SSGRoute.PTembedding.localGlobal_annihilator` is *false as stated* (it quantifies over an
arbitrary local family `pair`, so with `pair = 0` a non-zero functional killing `Ш¹` would have to
vanish) and must not be used.
-/


open scoped TensorProduct Pointwise
open Classical

set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

namespace Work.SSGRoute.PT

/-! The two linear-algebra lemmas `natCard_annihilator_mul` and
`CountAux.natCard_annihilator_mul_additive` now live in the (much lighter) module
`Submission/Work/SSGRoute/PT/pt_counting_identity_aux.lean`, which this module imports. -/

/-- **The Poitou–Tate counting identity for the relaxed Selmer groups** (the Euler-characteristic
half of the `H¹`-part of the nine-term sequence).

Let `k` be a number field, `Ω` an algebraic closure, `K ⊆ N` finite Galois over `k`, `ζ` a primitive
`p`-th root of unity in `K`, `T` the cyclotomic dual of `μ_p` over `Gal(K/k)`, `M` a finite
`𝔽_p[Gal(K/k)]`-module and `M' = DualMod p (M ⊗ T) = M^∨(1)` its Tate dual.  Let `S` be one place
per prime, containing the primes over `p` and those ramified in `N`, and `C` one involution per real
place.  With `primalClasses` the product of the local `H¹`-spaces at `S ∪ C`, `IsRealizableClass`
the set of classes realized by a global cocycle unramified outside `S ∪ cs(N)` and
`IsDualSelmerClass` the relaxed dual Selmer classes (locally trivial at the finite places splitting
completely in `N` and outside `S`; unramified at the other finite places outside `S`), one has

`|{x | IsRealizableClass x}| · |{y | IsDualSelmerClass y}| = |primalClasses|`.

In dimensions this is `dim V + dim W = dim ∏_{S ∪ C} H¹`, the Euler characteristic of the Selmer
complex (Milne, *Arithmetic Duality Theorems* I.4.10; Neukirch–Schmidt–Wingberg 8.6.8).  It is
`hcount`, the hypothesis of `Work.SSGRoute.PT.natCard_counting`.  It requires the local duality
dimension equality `dim H¹(D_A, M) = dim H¹(D_A, M')` at every place of `S ∪ C` — which is
`Work.SSGRoute.local_tate_duality_finite` together with the identification `M' = M^∨(1)` given by
`hT` — the finiteness of the global Selmer groups (Hasse/Bauer descent `sha1_descentHom`), and the
`Ext`-core exactness segment (`Work.SSGRoute.PT.Exactness`, `h1ImageLeKernel`, `h1KernelLeImage`). -/
theorem pt_selmer_counting_identity (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (C : Finset (Ω ≃ₐ[k] Ω)) (hCinv : ∀ c ∈ C, c ^ 2 = 1)
    (hC : ∀ c : Ω ≃ₐ[k] Ω, c ^ 2 = 1 → c ≠ 1 → ∃ c₀ ∈ C, ∃ σ : Ω ≃ₐ[k] Ω, c = σ * c₀ * σ⁻¹)
    (hCdisj : ∀ c ∈ C, ∀ c' ∈ C, (∃ σ : Ω ≃ₐ[k] Ω, c' = σ * c * σ⁻¹) → c = c') :
    Nat.card {x : Work.SSGRoute.PT.primalClasses p k Ω K M S C //
        Work.SSGRoute.PT.IsRealizableClass p k Ω K N hKN M S C x} *
      Nat.card {y : Work.SSGRoute.PT.primalClasses p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C //
        Work.SSGRoute.PT.IsDualSelmerClass p k Ω K N hKN T M S C y} =
      Nat.card (Work.SSGRoute.PT.primalClasses p k Ω K M S C) := by
  classical
  -- the `ZMod p`-module instances of the Tate dual `M^∨(1) = DualMod p (M ⊗ T)` (pinned as in
  -- `PT/converseRepr.lean`, so that the product space on the dual side is a `ZMod p`-module)
  letI : AddCommGroup (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) := inferInstance
  letI : Module (ZMod p) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) := inferInstance
  letI : DistribMulAction (K ≃ₐ[k] K)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) := inferInstance
  letI : SMulCommClass (K ≃ₐ[k] K) (ZMod p)
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) := inferInstance
  haveI hTfin : Finite T :=
    Work.SSGRoute.EulerSymm.finite_of_isCyclotomicDual p k Ω K ζ T hT
  -- ## 1. the canonical local pairing with its local axioms, reciprocity and converse (`G1⁺`)
  obtain ⟨pair, hmain, hrec7, hconv8full⟩ :=
    canonical_localPairing_reciprocity_converse p k Ω K ζ hζ hζK T hT
  have hloc : ∀ H : Subgroup (Ω ≃ₐ[k] Ω), IsLocalGroup k Ω H →
      LocalAxioms (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (pair M) H := by
    intro H hH
    obtain ⟨c1, c2, c3, c4, c5⟩ := hmain M H hH
    exact ⟨c1, c2, c3, c4, c5.1⟩
  have hrec : Recip (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (pair M) := hrec7 M
  have hconv8 : ConverseRepr p k Ω K N hKN T M S C (pair M) :=
    fun α β hα hβ hsum =>
      hconv8full M N hKN S hSfin hSdisj hSram C hCinv hC hCdisj α β hα hβ hsum
  -- ## 2. the two halves of the annihilator identity `V = W^⊥`
  have hconv := hconv_of_converse (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (hKN := hKN)
    (T := T) (M := M) (S := S) (C := C) (pair M) hloc hSfin hCinv hconv8
  have hrecip := CountAux.primalClassSet_orthogonal_dualClassSet (p := p) (k := k) (Ω := Ω)
    (K := K) (N := N) (T := T) (M := M) (S := S) (C := C)
    hKN hSfin hSdisj hSram hCinv hC hCdisj (pair M) hloc hrec
  -- ## 3. finiteness of the two local class spaces
  haveI hQDfin : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) :=
    finite_dualMod_tensor p M T
  haveI hPfin : Finite (primalClasses p k Ω K M S C) :=
    finite_primalClasses_general p k Ω K M S hSfin C hCinv
  haveI hQfin : Finite (primalClasses p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C) :=
    finite_primalClasses_general p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S hSfin C hCinv
  -- ## 4. the product form of the local pairings and its two non-degeneracies
  let β : primalClasses p k Ω K M S C →
      primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C →
        ZMod p :=
    productFormFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (S := S) (C := C)
      (localPairingFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (pair M) hloc)
  have haddL : ∀ x x' y, β (x + x') y = β x y + β x' y := fun x x' y =>
    productFormFun_add_left (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      (S := S) (C := C)
      (localPairingFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (pair M) hloc)
      x x' y
  have haddR : ∀ x y y', β x (y + y') = β x y + β x y' := fun x y y' =>
    productFormFun_add_right (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      (S := S) (C := C)
      (localPairingFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (pair M) hloc)
      x y y'
  have hndL : ∀ x : primalClasses p k Ω K M S C, (∀ y, β x y = 0) → x = 0 := by
    intro x hx
    exact productFormFun_ndL (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      (S := S) (C := C)
      (localPairingFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (pair M) hloc)
      (fun A hA => localPairingFun_ndL (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
        (pair M) hloc (Or.inl ⟨A, hSfin A hA, rfl⟩))
      (fun c hc => localPairingFun_ndL (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
        (pair M) hloc (Or.inr ⟨c, hCinv c hc, rfl⟩))
      x hx
  have hndR : ∀ y : primalClasses p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C,
      (∀ x, β x y = 0) → y = 0 := by
    intro y hy
    exact productFormFun_ndR (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
      (S := S) (C := C)
      (localPairingFun (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M) (pair M) hloc)
      (fun A hA => localPairingFun_ndR (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
        (pair M) hloc (Or.inl ⟨A, hSfin A hA, rfl⟩))
      (fun c hc => localPairingFun_ndR (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (M := M)
        (pair M) hloc (Or.inr ⟨c, hCinv c hc, rfl⟩))
      y hy
  -- ## 5. `V = W^⊥`, hence the counting identity
  have hiff : ∀ x : primalClasses p k Ω K M S C,
      (∀ y ∈ dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M)
          (S := S) (C := C), β x y = 0) ↔
        x ∈ primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M) (S := S)
          (C := C) :=
    fun x => ⟨fun h => hconv x h, fun hx y hy => hrecip x hx y hy⟩
  -- Every instance argument is supplied explicitly: as recorded at
  -- `PT/pt_canonical_assembly.lean`'s `counting_step_concrete`, the search for
  -- `Module (ZMod p) (primalClasses …)` does not terminate when it is left to the elaborator at an
  -- application site (it succeeds once the goal type is concrete, as in the ascriptions below).
  have hcard := @CountAux.natCard_annihilator_mul_additive p (inferInstance : Fact p.Prime)
    (primalClasses p k Ω K M S C)
    (primalClasses p k Ω K (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C)
    (inferInstance : AddCommGroup (primalClasses p k Ω K M S C))
    (inferInstance : Module (ZMod p) (primalClasses p k Ω K M S C))
    (inferInstance : Finite (primalClasses p k Ω K M S C))
    (inferInstance : AddCommGroup (primalClasses p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C))
    (inferInstance : Module (ZMod p) (primalClasses p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C))
    (inferInstance : Finite (primalClasses p k Ω K
      (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C))
    β haddL haddR hndL hndR
    (dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M) (S := S)
      (C := C))
  calc Nat.card {x : Work.SSGRoute.PT.primalClasses p k Ω K M S C //
        Work.SSGRoute.PT.IsRealizableClass p k Ω K N hKN M S C x} *
      Nat.card {y : Work.SSGRoute.PT.primalClasses p k Ω K
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)) S C //
        Work.SSGRoute.PT.IsDualSelmerClass p k Ω K N hKN T M S C y}
      = Nat.card (primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (M := M)
            (S := S) (C := C)) *
          Nat.card (dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M)
            (S := S) (C := C)) := by
        rw [(natCard_primalClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (hKN := hKN)
              (M := M) (S := S) (C := C) hCinv).symm,
            (natCard_dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (hKN := hKN)
              (T := T) (M := M) (S := S) (C := C)).symm]
    _ = Nat.card {x : Work.SSGRoute.PT.primalClasses p k Ω K M S C //
          ∀ y ∈ dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M)
              (S := S) (C := C), β x y = 0} *
          Nat.card (dualClassSet (p := p) (k := k) (Ω := Ω) (K := K) (N := N) (T := T) (M := M)
            (S := S) (C := C)) := by
        rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x => hiff x))]
    _ = Nat.card (Work.SSGRoute.PT.primalClasses p k Ω K M S C) := hcard

/-!
## The reduction, and the exact residual input

Given a pairing `β : P × P' → 𝔽_p` (additive, non-degenerate in both variables) together with the
annihilator identity `hann : (∀ y ∈ W, β x y = 0) ↔ x ∈ V` and `|P| = |P'|`, the target follows by
`natCard_annihilator_mul` composed with `natCard_primalClassSet` / `natCard_dualClassSet`
(`PT/pt_counting_assembly.lean`) and `Nat.card_congr (Equiv.subtypeEquivRight hann)`.

Three of those four ingredients are proved: the pairing (from the local pairings at `S ∪ C` by
`Work.SSGRoute.PT.productFormFun`, `…_ndL/ndR`, `exists_pairing_on_H1loc`), the inclusion
`V ⊆ W^⊥` (`Work.SSGRoute.PT.pt_orthogonality_of_realizable`, reciprocity) and the cardinality
lemma `natCard_annihilator_mul` of this file.  The instance obstruction recorded earlier (`Prod.instModule`
on the dual side versus the abstract `[Module (ZMod p) Q]`) is handled by the predicate-level step
`Work.SSGRoute.PT.wbot_le_of_additive` / `Work.SSGRoute.PT.counting_step_concrete`
(`PT/pt_canonical_assembly.lean`, proved), which is the instance-free form of the same argument.

What is *not* proved — and is the whole arithmetic content of this file — is the converse
inclusion `W^⊥ ⊆ V` for the canonical pairing, i.e. the middle exactness of the Poitou–Tate
sequence.  Note that `counting_step_concrete` goes the *other* way (it derives the realizability
clause from `hcount`); it does not give `hcount`.

`Work.SSGRoute.PT.pt_counting_identity_h1` (`PT/pt_counting_identity_h1.lean`) states the same
proposition in the `CountingIdentity` wrapper; a proof of either closes both.
-/

end Work.SSGRoute.PT


