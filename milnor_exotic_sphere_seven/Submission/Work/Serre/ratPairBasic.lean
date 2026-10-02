import Mathlib
import Submission.Work.Serre.E3aDefs
import Submission.Work.Serre.csrGlue
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.OneCell.RatMap
import Submission.Work.StemsB.RelChainsR
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.CWModel.Maps

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The rational comparison maps of the Serre pair comparison in the stable range

Over `ℚ`, the vocabulary of the cellular proof of the Serre exact sequence in the stable range:

* `relPairMapRat` — the map of pairs `(E, p⁻¹{b₀}) → (B, {b₀})` on relative rational chains;
* `pairMapOfRat`, `stagePairMapRat`, `pullbackPairMapRat` — the three comparison maps of the
  CW-model machinery (the `ℚ` counterparts of `Work.Serre.CWModel.pairMapOf`, `stagePairMap`,
  `pullbackPairMap`);
* `RatCellStepSharp` — the sharp rational cell step: the single geometric input of the cellular
  induction (delegated as `Work.Serre.cellStepSharp`, `Submission/Work/Serre/cellStepSharp.lean`);
* `RatFibreTransport` — the transport of the fibre's rational connectivity along a path in the base
  (`ℚ`-counterpart of `Work.Serre.SPC.FibreTransport`);
* `RatCellStep` — the cell step turned into the exact shape the tower induction consumes.
-/

open scoped Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

variable {E B Γ : Type} [TopologicalSpace E] [TopologicalSpace B] [TopologicalSpace Γ]

/-! ## The comparison maps of a pair -/

/-- **The map of pairs `(E, p⁻¹{b₀}) → (B, {b₀})`** on relative rational chains. -/
def relPairMapRat (p : C(E, B)) (b₀ : B) :
    Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' {b₀}) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B) :=
  relChainsRPairMap (p ⁻¹' {b₀}) ({b₀} : Set B) p (fun _ hx => hx)

/-- **The pair map `(Γ, {γ₀}) → (B, {b₀})`** on relative rational chains. -/
def pairMapOfRat (g : C(Γ, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀) :
    Work.StemsB.relChainsR ℚ (TopCat.of Γ) ({γ₀} : Set Γ) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B) :=
  relChainsRPairMap ({γ₀} : Set Γ) ({b₀} : Set B) g
    (fun x hx => by simpa [show x = γ₀ from hx] using hbase)

/-- **The pair map `(Γ ×_B E, q⁻¹{γ₀}) → (Γ, {γ₀})`** on relative rational chains. -/
def stagePairMapRat (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) :
    Work.StemsB.relChainsR ℚ (TopCat.of (Work.StemsB.Pullback g p))
        ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of Γ) ({γ₀} : Set Γ) :=
  relChainsRPairMap _ _ (Work.StemsB.pullbackFst g p) (fun _ hx => hx)

/-- **The pair map `(Γ ×_B E, q⁻¹{γ₀}) → (E, p⁻¹{b₀})`** on relative rational chains. -/
def pullbackPairMapRat (g : C(Γ, B)) (p : C(E, B)) (γ₀ : Γ) (b₀ : B) (hbase : g γ₀ = b₀) :
    Work.StemsB.relChainsR ℚ (TopCat.of (Work.StemsB.Pullback g p))
        ((Work.StemsB.pullbackFst g p) ⁻¹' ({γ₀} : Set Γ)) ⟶
      Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' ({b₀} : Set B)) :=
  relChainsRPairMap _ _ (Work.StemsB.pullbackSnd g p)
    (fun x hx => by
      have hx' : (Work.StemsB.pullbackFst g p) x = γ₀ := hx
      show p x.1.2 = b₀
      calc p x.1.2 = g ((Work.StemsB.pullbackFst g p) x) := x.2.symm
        _ = g γ₀ := by rw [hx']
        _ = b₀ := hbase)

/-- The pullback square identity `p ∘ pullbackSnd = g ∘ pullbackFst`, as an equality of continuous
maps. -/
theorem pullbackSnd_comp_eq (g : C(Γ, B)) (p : C(E, B)) :
    p.comp (Work.StemsB.pullbackSnd g p) = g.comp (Work.StemsB.pullbackFst g p) := by
  ext x
  exact x.2.symm

/-! ## The geometric inputs -/

/-- **The sharp rational cell step.**  For an attachment `Γ' = attachCells n Γ ι f` (cells of
dimension `n + 2`) and a Serre fibration `q : X → Γ'` whose fibres are rationally acyclic below `φ`
and rationally connected, the map of relative rational chain complexes
`Work.Serre.cellStepMap n ι f q : C_*(X, q⁻¹Γ; ℚ) ⟶ C_*(Γ', Γ; ℚ)` is an isomorphism on homology in
degrees `< (n+2) + φ` and surjective in degree `(n+2) + φ`.

This is the `ℚ`-counterpart of `Work.Serre.SPC.CellStepHyp` (which is the `ℤ` sharp cell step), and
it is the single geometric input of the cellular induction: everything else in the proof of
`Work.Serre.ratSerrePairComparison` is formal. -/
def RatCellStepSharp : Prop :=
  ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (φ : ℕ)
    (hfib : ∀ y : Work.RatHurewicz.attachCells n Y ι f, ∀ j : ℕ, 0 < j → j < φ →
      CategoryTheory.Limits.IsZero ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q y))).homology j))
    (h0 : ∀ y : Work.RatHurewicz.attachCells n Y ι f,
      Nonempty ((Work.Cohomology.singularChains ℚ
        (TopCat.of (Work.StemsB.fibre q y))).homology 0 ≅ ModuleCat.of ℚ ℚ)),
    (∀ i : ℕ, i < (n + 2) + φ → CategoryTheory.IsIso
      (HomologicalComplex.homologyMap (Work.Serre.cellStepMap n ι f q) i)) ∧
    Function.Surjective (HomologicalComplex.homologyMap (Work.Serre.cellStepMap n ι f q)
      ((n + 2) + φ)).hom

/-- **Transport of the fibre connectivity of a Serre fibration along a path in the base**, over
`ℚ`: the `ℚ`-counterpart of `Work.Serre.SPC.FibreTransport`. -/
def RatFibreTransport : Prop :=
  ∀ {X Γ : Type} [TopologicalSpace X] [TopologicalSpace Γ] (q : C(X, Γ))
    (hq : Work.StemsB.IsSerreFibration q) (φ : ℕ) (x₀ x₁ : Γ) (γ : C(unitInterval, Γ))
    (hγ0 : γ 0 = x₀) (hγ1 : γ 1 = x₁),
    (∀ j : ℕ, 0 < j → j < φ → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℚ (TopCat.of (Work.StemsB.fibre q x₀))).homology j)) →
    Nonempty ((Work.Cohomology.singularChains ℚ (TopCat.of (Work.StemsB.fibre q x₀))).homology 0
      ≅ ModuleCat.of ℚ ℚ) →
    (∀ j : ℕ, 0 < j → j < φ → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℚ (TopCat.of (Work.StemsB.fibre q x₁))).homology j)) ∧
    Nonempty ((Work.Cohomology.singularChains ℚ (TopCat.of (Work.StemsB.fibre q x₁))).homology 0
      ≅ ModuleCat.of ℚ ℚ)

/-- **The fibre-connectivity of a Serre fibration over a path connected base is independent of the
base point**, over `ℚ` (consequence of `RatFibreTransport` and path connectedness). -/
theorem ratFibreConnectivity_of_pathConnected (htr : RatFibreTransport)
    {X Γ : Type} [TopologicalSpace X] [TopologicalSpace Γ] (q : C(X, Γ))
    (hq : Work.StemsB.IsSerreFibration q) [PathConnectedSpace Γ] (x₀ x₁ : Γ) (φ : ℕ)
    (h₁ : ∀ j : ℕ, 0 < j → j < φ → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℚ (TopCat.of (Work.StemsB.fibre q x₀))).homology j))
    (h₁0 : Nonempty ((Work.Cohomology.singularChains ℚ
      (TopCat.of (Work.StemsB.fibre q x₀))).homology 0 ≅ ModuleCat.of ℚ ℚ)) :
    (∀ j : ℕ, 0 < j → j < φ → CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularChains ℚ (TopCat.of (Work.StemsB.fibre q x₁))).homology j)) ∧
    Nonempty ((Work.Cohomology.singularChains ℚ
      (TopCat.of (Work.StemsB.fibre q x₁))).homology 0 ≅ ModuleCat.of ℚ ℚ) := by
  obtain ⟨P⟩ := PathConnectedSpace.joined x₀ x₁
  exact htr q hq φ x₀ x₁ P.toContinuousMap P.source P.target h₁ h₁0

end

end Work.Serre
