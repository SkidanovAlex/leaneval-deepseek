import Mathlib
import Submission.Work.SSGRoute.PTCore.zloc_places
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `X¹_S` and `X²_S`: Milne's *unramified-outside-`S`, trivial-on-`S`* Tate–Shafarevich groups

This is item (1) of the bridge design of `PTCore/STATUS_pt_pairing_left_inj_s7.md` §12.

The place-set family of §9 (`Sha1On T = Z1locOn T ⧸ B¹`, conditions imposed at the places of `T`
for the *full* `G_k`) is **not** the family that a limit argument can iterate: for a finite `T` its
members are infinite, because `H¹_cont(G_k, M)` is infinite and `Sha1On T` is the kernel of a map
from it to a finite group.  The family with finite members is Milne's (*Arithmetic Duality
Theorems*, §4):

`X¹_S = ker(H¹(G_S,M) → ∏_{v∈S} H¹(K_v,M))`

— classes that are **unramified outside `S`** and **trivial at `S`** — finite for finite `S` by
Milne's Corollary 4.15.  This file provides its two ingredients in the workspace's vocabulary:

* `Z1unr S` / `Z2unr S`: the locally constant `1`-cocycles (resp. `2`-cocycles) of `M` that vanish
  on the inertia subgroup of every finite place **outside** `S` — the cochain-level form of
  "unramified outside `S`";
* `X1 S` / `X2 S`: the quotient of `Z1unr S ⊓ Z1locOn S` (resp. `Z2unr S ⊓ Z2locOn S`) by the
  global coboundaries, i.e. the group of classes unramified outside `S` and trivial at the places
  of `S` (and at the involutions).

With `S = Set.univ` the unramified condition is vacuous and `X1 univ` is the workspace's `Sha1`; as
`S` grows the family shrinks, with `⋂_{S finite} X1 S = Ш¹` — the statement handed to the fleet as
item (3) of §12.

## The place conditions are *conjugacy-based* (§27 of the status file)

A place set represented by a `Finset` can only ever cover the finitely many places above a given
prime **up to conjugacy**: `IsFinPlace`, `IsRamifiedIn`, `IsInertia` and the valuation at `p` are
all invariant under `G_k`-conjugation, and there are infinitely many places of `Ω` above each prime
of `k` (they form a single `G_k`-orbit).  So the condition "unramified outside `S`" must read

  `(∀ A ∈ S, ¬ IsConjPlace k A B) → a` vanishes on the inertia subgroup of `B`

and *not* the literal `B ∉ S`: with literal membership, "unramified outside `S`" would demand
vanishing on the inertia of the infinitely many places above each prime outside the finite `S`, and
the inclusion `Z¹_loc ≤ Z1unr S` of the corrected item (3) — the `⊇` half of `Ш¹ ≤ X¹_S` — would be
vacuous as soon as `K/k` ramifies (see `PTCore/STATUS_pt_pairing_left_inj_s7.md` §27).  The
conjugacy idiom used here is the one already used by the counting lane
(`PT.primalSelmer`, `IsRealizableClass`, `PT.pt_counting_identity_h1`'s `hSram`) and by
`exists_finset_ramifiedPlaces`/`places_of_primes_gen` in `ZSplit/`.

**Caveat recorded for the prover of (3).**  The identity `⋂_{S finite} X1 S = Ш¹` is *not* the
cochain-level identity `⋂_S (Z1unr S ⊓ Z1locOn S) = Z1loc`: the latter is **false**, because a
non-zero global coboundary `a = (σ ↦ σ • m - m)` with `m ∉ M^{I_B}` lies in `Z1loc` (it is a global
coboundary, hence a coboundary on every `D_A`) but not in `Z1unr S` for any `S` not meeting the
conjugacy class of `B`.  The identity must therefore be taken at the level of *classes* (the
coboundaries are killed in `X1 S`), i.e. one has to show that the natural map `Ш¹ → X1 S` is a
bijection onto the intersection, or equivalently that the two subquotients coincide.
-/

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000

namespace Work.SSGRoute.PTCore

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
  (K : IntermediateField k Ω) [Normal k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]

/-- **`Z¹_unr S`**: the locally constant `1`-cocycles unramified outside the finite places of `S`.

This is "`H¹(G_S,M)` at the cochain level": a cocycle of the full group `G_k` that vanishes on the
inertia subgroup of every finite place **whose conjugacy class does not meet `S`** — the place-set
condition is conjugacy-based, as it must be for a finite `S` (`S` names one place per prime of
`k`, and the places above a given prime are a single `G_k`-orbit). -/
def Z1unr (S : Finset (ValuationSubring Ω)) : Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → M) where
  carrier := {a | SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a ∧ SSGRoute.IsLocConstOn ⊤ a ∧
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
      ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0}
  zero_mem' := ⟨isCocycleOn_zero, isLocConstOn_zero, fun _ _ _ _ _ => rfl⟩
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    exact ⟨isCocycleOn_add ha1 hb1, isLocConstOn_add ha2 hb2,
      fun B hB hBc σ hσ => by
        rw [Pi.add_apply, ha3 B hB hBc σ hσ, hb3 B hB hBc σ hσ, add_zero]⟩
  smul_mem' := by
    rintro c a ⟨ha1, ha2, ha3⟩
    exact ⟨isCocycleOn_smul ha1 c, isLocConstOn_smul ha2 c,
      fun B hB hBc σ hσ => by
        rw [Pi.smul_apply, ha3 B hB hBc σ hσ, smul_zero]⟩

/-- **`Z²_unr S`**: the locally constant `2`-cocycles unramified outside the finite places of `S`
(again with the conjugacy-based place condition). -/
def Z2unr (S : Finset (ValuationSubring Ω)) :
    Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M) where
  carrier := {c | SSGRoute.IsCocycle2 (SSGRoute.res k K) c ∧ SSGRoute.IsLocConst2 c ∧
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
      ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ →
        ∀ τ : Ω ≃ₐ[k] Ω, c σ τ = 0}
  zero_mem' := ⟨isCocycle2_zero, isLocConst2_zero, fun _ _ _ _ _ _ => rfl⟩
  add_mem' := by
    rintro a b ⟨ha1, ha2, ha3⟩ ⟨hb1, hb2, hb3⟩
    exact ⟨isCocycle2_add ha1 hb1, isLocConst2_add ha2 hb2,
      fun B hB hBc σ hσ τ => by
        simp only [Pi.add_apply, ha3 B hB hBc σ hσ τ, hb3 B hB hBc σ hσ τ, add_zero]⟩
  smul_mem' := by
    rintro c a ⟨ha1, ha2, ha3⟩
    exact ⟨isCocycle2_smul ha1 c, isLocConst2_smul ha2 c,
      fun B hB hBc σ hσ τ => by
        simp only [Pi.smul_apply, ha3 B hB hBc σ hσ τ, smul_zero]⟩

variable {p k Ω K M}

@[simp] theorem mem_Z1unr {S : Finset (ValuationSubring Ω)} {a : (Ω ≃ₐ[k] Ω) → M} :
    a ∈ Z1unr p k Ω K M S ↔
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a ∧ SSGRoute.IsLocConstOn ⊤ a ∧
      ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0 := Iff.rfl

@[simp] theorem mem_Z2unr {S : Finset (ValuationSubring Ω)}
    {c : (Ω ≃ₐ[k] Ω) → (Ω ≃ₐ[k] Ω) → M} :
    c ∈ Z2unr p k Ω K M S ↔
      SSGRoute.IsCocycle2 (SSGRoute.res k K) c ∧ SSGRoute.IsLocConst2 c ∧
      ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
        ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ →
          ∀ τ : Ω ≃ₐ[k] Ω, c σ τ = 0 := Iff.rfl

variable (p k Ω K M)

/-- **`Z1unr` is monotone in `S`**: prescribing more places (i.e. allowing more conjugacy classes of
places to be ramified) weakens the unramified-outside condition. -/
theorem Z1unr_monotone : Monotone (Z1unr p k Ω K M) := by
  intro S T hST a ha
  refine ⟨ha.1, ha.2.1, ?_⟩
  intro B hB hBT σ hσ
  exact ha.2.2 B hB (fun A hA => hBT A (hST hA)) σ hσ

/-- **`Z2unr` is monotone in `S`.** -/
theorem Z2unr_monotone : Monotone (Z2unr p k Ω K M) := by
  intro S T hST c hc
  refine ⟨hc.1, hc.2.1, ?_⟩
  intro B hB hBT σ hσ τ
  exact hc.2.2 B hB (fun A hA => hBT A (hST hA)) σ hσ τ

/-- **`X¹_S`** (Milne, *ADT* §4), as a `Submodule` of the ambient `1`-cochains: the cocycles that
are **unramified outside `S`** and **trivial at the places of `S`** (and at the involutions) —
i.e. `Z1unr S ⊓ Z1locOn S`.  Its quotient by the global coboundaries is the group `X¹_S` of Milne's
nine-term sequence; with `S = Finset.univ` the unramified-outside condition is vacuous and this
submodule is `Z1loc` (see `PTCore/STATUS_pt_pairing_left_inj_s7.md` §12), so the quotient is the
workspace's `Ш¹`. -/
theorem X1_submodule_characterisation (S : Finset (ValuationSubring Ω))
    (a : (Ω ≃ₐ[k] Ω) → M) :
    (a ∈ Z1unr p k Ω K M S ∧ a ∈ Z1locOn p k Ω K M (↑S : Set (ValuationSubring Ω))) ↔
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ a ∧ SSGRoute.IsLocConstOn ⊤ a ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
          (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
          ∀ σ : Ω ≃ₐ[k] Ω, SSGRoute.IsInertia k B σ → a σ = 0) ∧
      (∀ A : ValuationSubring Ω, A ∈ S → SSGRoute.IsFinPlace k A →
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) a) ∧
      (∀ σ : Ω ≃ₐ[k] Ω, σ ^ 2 = 1 →
          SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers σ) a) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨h1, h2, h3⟩, -, -, h6, h7⟩
    exact ⟨h1, h2, h3, h6, h7⟩
  · rintro ⟨h1, h2, h3, h6, h7⟩
    exact ⟨⟨h1, h2, h3⟩, h1, h2, h6, h7⟩

end Work.SSGRoute.PTCore
