import Mathlib
import Submission.Work.Serre.C1Cyl
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Serre.CsrSharp.cellStepSharpIso
import Submission.Work.Serre.DiscPair.lesSplitPair
import Submission.Work.Serre.DiscPair.cylPairCofibre
import Submission.Work.Serre.DiscPair.cellStepPairKernel
import Submission.Work.Serre.DiscPair.cellStepVanishing
import Submission.Work.Serre.DiscPair.centreConePair
import Submission.Work.Serre.DiscPair.centreConePairZero

/-!
# The disc-pair cell step

`Work.Serre.DiscPair.discCellStep`, assembled from four independent pieces:

* `cylPairCofibre` — `H_m(cyl q, S) ≅ coker(φ_m) × ker(φ_{m-1})` for the mapping-cylinder pair of a
  map of pairs;
* `cellStepPairKernel` — the sharp cell step with naturality: the pair map is surjective in degrees
  `≥ n+2` and its kernel is the direct sum of the reduced homologies of the fibres;
* `cellStepVanishing` — the relative groups vanish below the cell dimension;
* `centreConePair`, `centreConePairZero` — the pair over a cell centre is the cone on the fibre.

The two index regimes are `m > D` (everything is controlled by the cell step) and `m = D` (both
sides vanish).
-/

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits
open scoped Topology

noncomputable section

/-- A product with a zero ℚ-module is the other factor. -/
def prodIsoOfIsZero {X Y : ModuleCat ℚ} (hX : IsZero X) :
    ModuleCat.of ℚ (↥X × ↥Y) ≅ Y := by
  haveI : Subsingleton ↥X := ModuleCat.subsingleton_of_isZero hX
  exact (LinearEquiv.ofBijective (LinearMap.snd ℚ ↥X ↥Y)
    ⟨fun a b h => by
      ext
      · exact Subsingleton.elim _ _
      · exact h,
     fun y => ⟨(0, y), rfl⟩⟩).toModuleIso

/-- A product of zero ℚ-modules is a zero ℚ-module. -/
theorem isZero_prod {X Y : ModuleCat ℚ} (hX : IsZero X) (hY : IsZero Y) :
    IsZero (ModuleCat.of ℚ (↥X × ↥Y)) := by
  haveI : Subsingleton ↥X := ModuleCat.subsingleton_of_isZero hX
  haveI : Subsingleton ↥Y := ModuleCat.subsingleton_of_isZero hY
  exact ModuleCat.isZero_iff_subsingleton.mpr
    ⟨fun a b => by ext <;> exact Subsingleton.elim _ _⟩

/-- The kernel of a morphism whose source is a zero module is a zero module. -/
theorem isZero_kernel_of_isZero_src {X Y : ModuleCat ℚ} (f : X ⟶ Y) (hX : IsZero X) :
    IsZero (kernel f) := by
  haveI : Subsingleton ↥X := ModuleCat.subsingleton_of_isZero hX
  refine IsZero.of_iso (Y := ModuleCat.of ℚ ↥(ModuleCat.Hom.hom f).ker)
    (ModuleCat.isZero_iff_subsingleton.mpr ⟨fun a b => ?_⟩) (ModuleCat.kernelIsoKer f)
  exact Subtype.ext (Subsingleton.elim _ _)

/-- A direct sum of subsingleton ℚ-modules is a subsingleton. -/
theorem subsingleton_directSum {ι : Type} {M : ι → ModuleCat ℚ}
    (h : ∀ i, Subsingleton ↥(M i)) :
    Subsingleton (DirectSum ι (fun i => ↥(M i))) := by
  refine ⟨fun a b => ?_⟩
  apply DirectSum.ext
  intro i
  exact Subsingleton.elim _ _

/-- A direct sum of zero ℚ-modules is a zero ℚ-module. -/
theorem isZero_directSum {ι : Type} {M : ι → ModuleCat ℚ} (h : ∀ i, IsZero (M i)) :
    IsZero (ModuleCat.of ℚ (DirectSum ι (fun i => ↥(M i)))) :=
  ModuleCat.isZero_iff_subsingleton.mpr
    (subsingleton_directSum (fun i => ModuleCat.subsingleton_of_isZero (h i)))

/-- An isomorphism of direct sums induced by a family of isomorphisms. -/
def directSumIso {ι : Type} {M N : ι → ModuleCat ℚ} (e : ∀ i, M i ≅ N i) :
    ModuleCat.of ℚ (DirectSum ι (fun i => ↥(M i))) ≅
      ModuleCat.of ℚ (DirectSum ι (fun i => ↥(N i))) := by
  classical
  exact (ModuleCat.coprodIsoDirectSum M).symm ≪≫ CategoryTheory.Limits.Sigma.mapIso e ≪≫
    ModuleCat.coprodIsoDirectSum N

end

theorem discCellStep (D : ℕ) (hD : 2 ≤ D) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (hne : ∀ i : ι, Nonempty (Work.StemsB.fibre q (Work.Serre.csrCentre (D - 2) Γ ι f i)))
    (m : ℕ) (hmD : D ≤ m) :
    Nonempty (((Work.StemsB.relChainsR ℚ (TopCat.of (Work.Serre.cyl q))
        ((Work.Serre.cylRetract q) ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f) ∪
          Set.range (Work.Serre.cylIncl q))).homology m) ≅
      ModuleCat.of ℚ (DirectSum ι (fun i => ↥((Work.StemsB.relChainsR ℚ
        (TopCat.of ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D-2) Γ ι f i}))
        {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}).homology (m - D))))) := by
  classical
  have hb : ∀ i : ι, Work.StemsB.fibre q (Work.Serre.csrCentre (D-2) Γ ι f i) :=
    fun i => Classical.choice (hne i)
  -- the pair map and its values
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (q ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f))
        (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f)) q (fun _ hx => hx)) m).hom :=
    (cellStepPairKernel (D-2) Γ ι f q hq hne hb m (by omega)).1
  haveI : Epi (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (q ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f))
        (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f)) q (fun _ hx => hx)) m) :=
    (ModuleCat.epi_iff_surjective _).mpr hsurj
  have hz : IsZero (cokernel (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (q ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f))
        (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f)) q (fun _ hx => hx)) m)) :=
    Limits.isZero_cokernel_of_epi _
  obtain ⟨e1⟩ := cylPairCofibre D Γ ι f q hq m (by omega)
  rcases eq_or_lt_of_le hmD with hEq | hLt
  · -- `m = D`: both sides are zero
    subst hEq
    have hvan := (cellStepVanishing (D-2) Γ ι f q hq (D-1) (by omega) (by omega)).1
    have hzk : IsZero (kernel (HomologicalComplex.homologyMap
        (Work.Serre.relChainsRPairMap (q ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f))
          (Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f)) q (fun _ hx => hx)) (D-1))) :=
      isZero_kernel_of_isZero_src _ hvan
    have hL : IsZero (((Work.StemsB.relChainsR ℚ (TopCat.of (Work.Serre.cyl q))
        ((Work.Serre.cylRetract q) ⁻¹' Set.range (Work.RatHurewicz.attachIncl (D-2) Γ ι f) ∪
          Set.range (Work.Serre.cylIncl q))).homology D)) :=
      (isZero_prod hz hzk).of_iso e1
    have hR : IsZero (ModuleCat.of ℚ (DirectSum ι (fun i => ↥((Work.StemsB.relChainsR ℚ
        (TopCat.of ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D-2) Γ ι f i}))
        {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}).homology (D - D))))) := by
      rw [Nat.sub_self]
      exact isZero_directSum (fun i => centreConePairZero D hD Γ ι f q hq hne i)
    exact ⟨hL.iso hR⟩
  · -- `D < m`
    have hk' : (D-2) + 2 ≤ m - 1 := by omega
    obtain ⟨-, ⟨e2⟩⟩ := cellStepPairKernel (D-2) Γ ι f q hq hne hb (m-1) hk'
    have hidx : (m - 1) - ((D-2)+2) = m - D - 1 := by omega
    have hk1 : 1 ≤ m - D := by omega
    -- per-cell isomorphisms
    have e3 : ∀ i : ι, (Work.StemsB.relChainsR ℚ
        (TopCat.of (Work.StemsB.fibre q (Work.Serre.csrCentre (D-2) Γ ι f i)))
        {hb i}).homology ((m-D)-1) ≅ (Work.StemsB.relChainsR ℚ
        (TopCat.of ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D-2) Γ ι f i}))
        {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}).homology (m - D) :=
      fun i => (centreConePair D Γ ι f q hq i (hb i) (m-D) hk1).some.symm
    have hmid : Nonempty (ModuleCat.of ℚ (DirectSum ι (fun i => ↥((Work.StemsB.relChainsR ℚ
        (TopCat.of (Work.StemsB.fibre q (Work.Serre.csrCentre (D-2) Γ ι f i)))
        {hb i}).homology ((m-1) - ((D-2)+2)))))
        ≅ ModuleCat.of ℚ (DirectSum ι (fun i => ↥((Work.StemsB.relChainsR ℚ
        (TopCat.of ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D-2) Γ ι f i}))
        {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}).homology (m - D))))) := by
      rw [hidx]
      exact ⟨directSumIso e3⟩
    obtain ⟨e4⟩ := hmid
    exact ⟨e1 ≪≫ prodIsoOfIsZero hz ≪≫ e2 ≪≫ e4⟩

end Work.Serre.DiscPair
