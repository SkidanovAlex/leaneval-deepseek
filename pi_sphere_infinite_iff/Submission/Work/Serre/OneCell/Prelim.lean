import Mathlib
import Submission.Work.StemsB.RelChainsR
import Submission.Work.Serre.Engine
import Submission.Work.Serre.OneCell.RatAdditivity
import Submission.Work.Serre.OneCell.RatMap
import Submission.Work.Serre.OneCell.AbsComparison
import Submission.Work.Serre.pathConnectedSpace_of_ratAcyclic
import Submission.Work.Serre.ratH_zero_of_pathConnected
import Submission.Work.Serre.periodicity_of_pairComparison
import Submission.Work.Serre.CellStep.sigmaHomeo

set_option synthInstance.maxHeartbeats 400000


/-!
# Preliminaries for the local model of the `1`-cell step

Generic tools:

* transport of rational homology along a homeomorphism, and of the vanishing of a homology module;
* the base change `ℤ → ℚ` of the vanishing of a *relative* homology module;
* the identification of the fibre over a point of `W` inside `q⁻¹W` with the fibre of `q`;
* `H_k` of a nonempty subsingleton space vanishes in positive degrees;
* `H_0 ≅ ℚ` forces path connectedness.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.OneCell

open Work.Serre

noncomputable section

/-! ## Transport along homeomorphisms -/

/-- A homeomorphism induces an isomorphism on rational homology in every degree. -/
theorem isIso_ratHomologyMap_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (k : ℕ) : IsIso (ratHomologyMap (e : C(X, Y)) k) := by
  haveI : IsIso (TopCat.ofHom (e : C(X, Y))) := by
    rw [show TopCat.ofHom (e : C(X, Y)) = (TopCat.isoOfHomeo e).hom from rfl]
    infer_instance
  exact Work.Serre.OneCell.isIso_homologyMap_chainMap_of_isIso (TopCat.ofHom (e : C(X, Y))) k

/-- Homeomorphic spaces have isomorphic rational homology in every degree. -/
theorem nonempty_ratH_iso_of_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (k : ℕ) : Nonempty (ratH (TopCat.of X) k ≅ ratH (TopCat.of Y) k) := by
  haveI := isIso_ratHomologyMap_homeo e k
  exact ⟨asIso (ratHomologyMap (e : C(X, Y)) k)⟩

/-- Vanishing of rational homology transfers across a homeomorphism. -/
theorem isZero_ratH_of_homeo {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (k : ℕ) (h : IsZero (ratH (TopCat.of Y) k)) :
    IsZero (ratH (TopCat.of X) k) := by
  haveI := isIso_ratHomologyMap_homeo e k
  exact IsZero.of_iso h (asIso (ratHomologyMap (e : C(X, Y)) k))

/-! ## Base change `ℤ → ℚ` of a vanishing relative homology -/

/-- The rational relative homology of a pair vanishes whenever the integral one does. -/
theorem isZero_ppRelH_of_isZero_relChains (X : TopCat) (A : Set X) (k : ℕ)
    (h : IsZero ((Work.Cohomology.relChains X A).homology k)) : IsZero (ppRelH X A k) := by
  obtain ⟨α⟩ := pp_relH_baseChange X A k
  exact IsZero.of_iso
    (CategoryTheory.Functor.map_isZero Work.StemsB.IntRatF h) α

/-! ## The restriction of a map to the preimage of a set -/

/-- The restriction of `q` to `q ⁻¹' W`, regarded as a map onto the subspace `W`. -/
def restrictTo {E Z : Type} [TopologicalSpace E] [TopologicalSpace Z] (q : C(E, Z)) (W : Set Z) :
    C(↥(q ⁻¹' W), ↥W) :=
  ⟨fun x => ⟨q x.1, x.2⟩, (q.continuous.comp continuous_subtype_val).subtype_mk _⟩

@[simp] theorem restrictTo_apply {E Z : Type} [TopologicalSpace E] [TopologicalSpace Z]
    (q : C(E, Z)) (W : Set Z) (x : ↥(q ⁻¹' W)) :
    ((restrictTo q W x : ↥W) : Z) = q x.1 := rfl

/-- The sub-pair subtype `{x : ↥S | (x : X) ∈ T}` is the subspace `↥T`, when `T ⊆ S`. -/
noncomputable def homeoSubtypeSubtype {X : Type} [TopologicalSpace X] {S T : Set X}
    (hTS : T ⊆ S) : ↥{x : ↥S | (x : X) ∈ T} ≃ₜ ↥T where
  toFun x := ⟨x.1.1, x.2⟩
  invFun y := ⟨⟨y.1, hTS y.2⟩, y.2⟩
  left_inv x := rfl
  right_inv y := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

@[simp] theorem homeoSubtypeSubtype_apply {X : Type} [TopologicalSpace X] {S T : Set X}
    (hTS : T ⊆ S) (x : ↥{x : ↥S | (x : X) ∈ T}) :
    ((homeoSubtypeSubtype hTS x : ↥T) : X) = x.1.1 := rfl

/-! ## The fibre over a point of `W` inside `q ⁻¹' W` -/

/-- The points of `q⁻¹W` lying over a fixed `z ∈ W` form a space homeomorphic to the fibre of `q`
at `z`. -/
noncomputable def homeoSubFibre {E Z : Type} [TopologicalSpace E] [TopologicalSpace Z]
    (q : C(E, Z)) {W : Set Z} {z : Z} (hz : z ∈ W) :
    ↥{x : ↥(q ⁻¹' W) | q x.1 = z} ≃ₜ Work.StemsB.fibre q z where
  toFun x := ⟨x.1.1, x.2⟩
  invFun y := ⟨⟨y.1, by show q y.1 ∈ W; rw [y.2]; exact hz⟩, y.2⟩
  left_inv x := by rfl
  right_inv y := by rfl
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Vanishing in positive degrees of the homology of a nonempty subsingleton space. -/
theorem isZero_ratH_subsingleton {X : Type} [TopologicalSpace X] {S : Set X}
    (hS : S.Subsingleton) (hne : S.Nonempty) (k : ℕ) (hk : 0 < k) :
    IsZero (ratH (TopCat.of ↥S) k) := by
  haveI : Nonempty ↥S := ⟨⟨hne.some, hne.some_mem⟩⟩
  haveI : Subsingleton ↥S := ⟨fun a b => Subtype.ext (hS a.2 b.2)⟩
  exact Work.Serre.OneCell.isZero_ratH_of_homeo
    (e := { toFun := fun _ => PUnit.unit, invFun := fun _ => ⟨hne.some, hne.some_mem⟩,
            left_inv := fun a => Subtype.ext (hS hne.some_mem a.2),
            right_inv := fun _ => Subsingleton.elim _ _,
            continuous_toFun := continuous_const, continuous_invFun := continuous_const })
    k (Work.Cohomology.homologyContractible_ring ℚ k hk)

end

end Work.Serre.OneCell
