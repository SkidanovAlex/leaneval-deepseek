import Mathlib
import Submission.Work.StemsB.SerreExact
import Submission.Work.StemsB.Fibrations
import Submission.Work.Cohomology.relChainsMapOf_comp

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The comparison maps of the Serre exactness assembly

For the cellular proof of the Serre exact sequence in the stable range we need three maps of pairs,
all on relative singular chains:

* `pairMapOf g γ₀ b₀ hbase` — the map `(Γ, {γ₀}) → (B, {b₀})` induced by `g : Γ → B`;
* `pullbackPairMap g p γ₀ b₀ hbase` — the map `(X, q⁻¹{γ₀}) → (E, p⁻¹{b₀})` induced by the second
  projection of the pullback `X = Γ ×_B E`;
* `stagePairMap g p γ₀` — the map `(X, q⁻¹{γ₀}) → (Γ, {γ₀})` induced by the first projection.

Their relation (the pullback square `p ∘ pullbackSnd = g ∘ pullbackFst`) is
`pullbackPairMap ≫ relPairMap = stagePairMap ≫ pairMapOf`, so the three comparison theorems
compose into the isomorphism of the target statement.
-/

open scoped Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.CWModel

noncomputable section

variable {Γ B E : Type} [TopologicalSpace Γ] [TopologicalSpace B] [TopologicalSpace E]

/-- **The pair map `(Γ, {γ₀}) → (B, {b₀})`** induced by a map `g` with `g γ₀ = b₀`, on relative
singular chains. -/
def pairMapOf (g : C(Γ, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀) :
    Work.Cohomology.relChains (TopCat.of Γ) ({γ₀} : Set Γ) ⟶
      Work.Cohomology.relChains (TopCat.of B) ({b₀} : Set B) :=
  Work.Cohomology.relChainsMapOf (TopCat.of Γ) (TopCat.of B) {γ₀} {b₀} (TopCat.ofHom g)
    (TopCat.ofHom ⟨fun _ => ⟨b₀, rfl⟩, continuous_const⟩)
    (by
      ext x
      exact (congrArg g x.2).trans hbase)

/-- **The pair map `(Γ ×_B E, q⁻¹{γ₀}) → (E, p⁻¹{b₀})`** induced by the second projection of the
pullback, on relative singular chains. -/
def pullbackPairMap (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀) :
    Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback g p))
        ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ⟶
      Work.Cohomology.relChains (TopCat.of E) (p ⁻¹' ({b₀} : Set B)) :=
  Work.Cohomology.relChainsMapOf _ _ _ _
    (TopCat.ofHom (Work.StemsB.pullbackSnd g p))
    (TopCat.ofHom ⟨
      (fun x : ↥((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) =>
        ⟨Work.StemsB.pullbackSnd g p x.1, by
          have hx : x.1.1.1 = γ₀ := x.2
          calc p (x.1.1.2) = g (x.1.1.1) := x.1.2.symm
            _ = g γ₀ := by rw [hx]
            _ = b₀ := hbase⟩),
      Continuous.subtype_mk
        ((Work.StemsB.pullbackSnd g p).continuous.comp continuous_subtype_val)
        (fun x => by
          have hx : x.1.1.1 = γ₀ := x.2
          calc p (x.1.1.2) = g (x.1.1.1) := x.1.2.symm
            _ = g γ₀ := by rw [hx]
            _ = b₀ := hbase)⟩)
    (by ext x; rfl)

/-- **The pair map `(Γ ×_B E, q⁻¹{γ₀}) → (Γ, {γ₀})`** induced by the first projection of the
pullback, on relative singular chains. -/
def stagePairMap (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) :
    Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback g p))
        ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ⟶
      Work.Cohomology.relChains (TopCat.of Γ) ({γ₀} : Set Γ) :=
  Work.Cohomology.relChainsMapOf _ _ _ _
    (TopCat.ofHom (Work.StemsB.pullbackFst g p))
    (TopCat.ofHom ⟨fun x => ⟨Work.StemsB.pullbackFst g p x.1, x.2⟩,
      Continuous.subtype_mk
        ((Work.StemsB.pullbackFst g p).continuous.comp continuous_subtype_val)
        (fun x => x.2)⟩)
    (by ext x; rfl)

end

end Work.Serre.CWModel
