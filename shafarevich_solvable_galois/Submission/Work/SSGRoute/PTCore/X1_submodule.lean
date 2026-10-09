import Mathlib
import Submission.Work.SSGRoute.PTCore.zloc_places
import Submission.Work.SSGRoute.PTCore.X1_unramified
import Submission.Work.SSGRoute.PTCore.Z1loc_le_Z1unr_of_ramified_subset
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `X¹_S` as a submodule of the single ambient `H¹_cont(G_k,M)`

Item (1)/(3) of the bridge design (`PTCore/STATUS_pt_pairing_left_inj_s7.md` §§12–14, §20, §22):
Milne's (*Arithmetic Duality Theorems* §4) group

`X¹_S = ker(H¹(G_S,M) → ∏_{v∈S} H¹(K_v,M))`

consists of the classes of `M` that are **unramified outside `S`** and **trivial at `S`**.  It is
realised here as a *submodule of the single ambient group*

`H1cont p k Ω K M := ↥(lcCocycles p k Ω K M ⊤) ⧸ (B1top).comap (lcCocycles ⊤).subtype`

— the workspace's `H¹_cont(G_k,M)` — rather than as a quotient of a *varying* cochain module.  This
is what §13/§14 require: the cochain-level intersection `⋂_S (Z1unr S ⊓ Z1locOn S)` is **not**
`Z1loc` (the witness is the global coboundary `σ ↦ σ • m − m` with `m ∉ M^{I_B}`, which lies in
`Z1loc` but in no `Z1unr S` with `B ∉ S`), so the intersection has to be taken after dividing out
the coboundaries.

**Lean engineering note.**  `X1 S` must be written as `Submodule.map`/`Submodule.comap` over
`↥(lcCocycles ⊤)`; the direct `⊓` of two submodules of the *function space* `(Ω ≃ₐ[k] Ω) → M` does
not elaborate here (instance synthesis fails or times out on that module structure), which is why
`X1_unramified.lean` phrases `X1_submodule_characterisation` with the two memberships side by side.
-/

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.PTCore

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]

/-- **The ambient `H¹_cont(G_k,M)`**: locally constant `1`-cocycles for `res k K` modulo the global
coboundaries. -/
abbrev H1cont : Type :=
  ↥(lcCocycles p k Ω K M ⊤) ⧸
    (B1top p k Ω K M).comap (lcCocycles p k Ω K M ⊤).subtype

/-- **`X¹_S`**: the classes unramified outside `S` and trivial at the places of `S`, as a submodule
of the ambient `H1cont`. -/
noncomputable def X1 (S : Finset (ValuationSubring Ω)) : Submodule (ZMod p) (H1cont p k Ω K M) :=
  Submodule.map (Submodule.mkQ ((B1top p k Ω K M).comap (lcCocycles p k Ω K M ⊤).subtype))
    (Submodule.comap (lcCocycles p k Ω K M ⊤).subtype (Z1unr p k Ω K M S) ⊓
      Submodule.comap (lcCocycles p k Ω K M ⊤).subtype
        (Z1locOn p k Ω K M (↑S : Set (ValuationSubring Ω))))

/-- **The `⊇` half of `Ш¹ ≤ X¹_S`**, in representative form: for `S` covering every finite place at
which `K/k` is ramified (up to conjugacy — `S` names one place per conjugacy class, and the places
above a prime of `k` form a single `G_k`-orbit, so a `Finset` cannot do better), the class in the
ambient `H¹_cont` of any locally trivial cocycle lies in `X1 S`.  This is the assembly of `X1 S`'s
definition with the delegated `Z1loc_le_Z1unr_of_ramified_subset`. -/
theorem mem_X1_of_mem_Z1loc [IsAlgClosure k Ω] (S : Finset (ValuationSubring Ω))
    (hS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      SSGRoute.IsRamifiedIn k K B → ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (a : ↥(Z1loc p k Ω K M)) :
    Submodule.Quotient.mk
        (⟨(a : (Ω ≃ₐ[k] Ω) → M), a.2.1, a.2.2.1⟩ : ↥(lcCocycles p k Ω K M ⊤)) ∈
      X1 p k Ω K M S := by
  refine Submodule.mem_map.mpr ⟨⟨(a : (Ω ≃ₐ[k] Ω) → M), a.2.1, a.2.2.1⟩, ?_, rfl⟩
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · exact Submodule.mem_comap.mpr
      (Z1loc_le_Z1unr_of_ramified_subset p k Ω K M S hS a.2)
  · exact Submodule.mem_comap.mpr
      ⟨a.2.1, a.2.2.1, fun A _ hA => a.2.2.2.1 A hA, a.2.2.2.2⟩

end Work.SSGRoute.PTCore
