import Mathlib
import Submission.Work.Smooth.OneManifold.Defs

/-!
# Elementary properties of locally Euclidean subsets, and the weakness of `IsLocalArc`

This file contains

* the basic API of `Work.Smooth.OneManifold.IsLocallyEuclidean` (transport along homeomorphisms,
  restriction to open subsets, restriction to subsets of the surface);
* `isLocalArc_range_of_injective_continuous`: the range of an injective continuous map `ℝ → ℝ³` is
  `Work.Smooth.Morse.IsLocalArc` for *every* surface, because the definition of `IsLocalArc`
  permits the neighbourhood `U = Set.univ`.  This is the formal record that `IsLocalArc` is strictly
  weaker than `IsLocallyEuclidean`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Smooth.OneManifold

noncomputable section

/-! ## Basic API -/

/-- **A set which is open in the carrier is open in a subset of the carrier.** -/
theorem isOpenInSet_of_isOpenInCarrier {ψ : Submission.Diffeo} {Z W : Set R3}
    (hZ : Z ⊆ (Work.Smooth.Morse.torus ψ).carrier)
    (hW : Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ) W) :
    IsOpenInSet Z W := by
  set φ : Z → (Work.Smooth.Morse.torus ψ).carrier := fun y => ⟨(y : R3), hZ y.2⟩ with hφdef
  have hφ : Continuous φ := Continuous.subtype_mk continuous_subtype_val fun y => hZ y.2
  have hpre : IsOpen (φ ⁻¹' (Subtype.val ⁻¹' W :
      Set (Work.Smooth.Morse.torus ψ).carrier)) := hW.preimage hφ
  show IsOpen (Subtype.val ⁻¹' W : Set Z)
  rw [show (Subtype.val ⁻¹' W : Set Z) = φ ⁻¹' (Subtype.val ⁻¹' W :
      Set (Work.Smooth.Morse.torus ψ).carrier) from by
    ext y
    exact Iff.rfl]
  exact hpre

/-- The same, with the open set intersected with `Z`. -/
theorem isOpenInSet_inter_of_isOpenInCarrier {ψ : Submission.Diffeo} {Z W : Set R3}
    (hZ : Z ⊆ (Work.Smooth.Morse.torus ψ).carrier)
    (hW : Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ) W) :
    IsOpenInSet Z (W ∩ Z) := by
  have h := isOpenInSet_of_isOpenInCarrier hZ hW
  show IsOpen (Subtype.val ⁻¹' (W ∩ Z) : Set Z)
  rw [show (Subtype.val ⁻¹' (W ∩ Z) : Set Z) = Subtype.val ⁻¹' W from by
    ext y
    exact ⟨fun h => h.1, fun h => ⟨h, y.2⟩⟩]
  exact h

/-- **Being locally Euclidean is a topological property.** -/
theorem isLocallyArc_of_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (h : Work.Smooth.SphereJordan.IsLocallyArc X) :
    Work.Smooth.SphereJordan.IsLocallyArc Y := by
  intro y
  obtain ⟨c⟩ := h (e.symm y)
  refine ⟨{ V := e '' c.V
            isOpen_V := e.isOpenMap c.V c.isOpen_V
            mem_V := ⟨e.symm y, c.mem_V, by simp⟩
            homeo := c.homeo.trans (Homeomorph.image e c.V)
            homeo_zero := ?_ }⟩
  apply Subtype.ext
  show e ((c.homeo 0 : c.V) : X) = y
  rw [show ((c.homeo 0 : c.V) : X) = e.symm y from congrArg Subtype.val c.homeo_zero]
  simp

/-- **The restriction of a locally Euclidean set to a relatively open subset.** -/
theorem IsLocallyEuclidean.of_subset {Z C : Set R3} (hCsub : C ⊆ Z)
    (hCopen : IsOpenInSet Z C) (h : IsLocallyEuclidean Z) : IsLocallyEuclidean C := by
  have h1 : Work.Smooth.SphereJordan.IsLocallyArc ↥{y : Z | (y : R3) ∈ C} :=
    Work.Smooth.SphereJordan.LocalArc.isLocallyArcIsOpen (X := Z) h hCopen
  exact isLocallyArc_of_homeomorph
    (Work.Smooth.SphereJordan.LocalArc.subtypeSubtypeHomeomorph hCsub).symm h1

/-- **An open subset of a locally Euclidean set is locally Euclidean.** -/
theorem IsLocallyEuclidean.of_isOpenIn {Z V : Set R3} (hVsub : V ⊆ Z)
    (hV : IsOpenInSet Z V) (h : IsLocallyEuclidean Z) : IsLocallyEuclidean V :=
  h.of_subset hVsub hV


/-- **Congruence for local Euclidean-ness along an equality of sets.** -/
theorem isLocallyEuclidean_of_eq {Z Z' : Set R3} (h : Z = Z') (hZ : IsLocallyEuclidean Z) :
    IsLocallyEuclidean Z' :=
  isLocallyArc_of_homeomorph (Homeomorph.setCongr h) hZ

/-! ## The weakness of `Work.Smooth.Morse.IsLocalArc` -/

/-- **Every injective continuous image of an open set of `ℝ` is `IsLocalArc`.**

Take `U = Set.univ`, which is open in the surface (`isOpenInCarrier_univ`), and `I = Set.univ`:
every point `x` of `Z = Set.range γ` is `γ s₀` for some `s₀`, and the map `γ` itself is the
required arc.  In particular the hypothesis `Work.Smooth.Morse.IsLocalArc ψ Z` does not force `Z`
to lie in the surface `F = torus ψ`, nor to be locally Euclidean. -/
theorem isLocalArc_range_of_injective_continuous (ψ : Submission.Diffeo) {γ : ℝ → R3}
    (hcont : Continuous γ) (hinj : Function.Injective γ) :
    Work.Smooth.Morse.IsLocalArc ψ (Set.range γ) := by
  rintro x ⟨s₀, rfl⟩
  refine ⟨Set.univ, Work.SurgeryInvariance.isOpenInCarrier_univ _, Set.mem_univ _, Set.univ, s₀, γ,
    isOpen_univ, Set.mem_univ _, hcont.continuousOn, rfl, hinj.injOn, ?_, ?_⟩
  · rintro s _
    exact ⟨s, rfl⟩
  · rintro y ⟨s, rfl⟩ _
    exact ⟨s, Set.mem_univ _, rfl⟩

end

end Work.Smooth.OneManifold
