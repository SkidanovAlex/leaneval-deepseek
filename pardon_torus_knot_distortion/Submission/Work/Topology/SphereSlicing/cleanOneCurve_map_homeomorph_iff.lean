import Mathlib
import Submission.Work.Topology.SphereSlicing.Defs

/-!
# `CleanOneCurve` is invariant under an ambient homeomorphism

`Work.Topology.SphereSlicing.CleanOneCurve P` is Pardon's single cut-and-paste of the second
innermost argument, stated on the local model `Work.Topology.SphereSlicing.SliceDisc P` of an
embedded disc in `ℝ³` whose boundary is a simple closed curve of `F = P.carrier` and whose
interior meets `F` only in inessential curves.

The cut-and-paste is a purely topological operation, so it is insensitive to the ambient
homeomorphism: a homeomorphism `ψ` of `ℝ³` carries the standard torus to
`ParamTorus.mapHomeomorph ψ` and the discs bounded by its loops to the discs bounded by the
images of those loops.  Here we make that transport explicit —

* `SliceDisc.push ψ` pushes a slice disc of the standard torus forward along `ψ` to a slice disc
  of `ParamTorus.mapHomeomorph ψ`;
* `SliceDisc.pull ψ` pulls a slice disc of `ParamTorus.mapHomeomorph ψ` back to the standard
  torus;

both preserve the boundary curve (up to `ClosedCurve.mapHomeomorph` / `ClosedCurve.mapHomeomorphInv`,
which are mutually inverse) and the number `Fintype.card D.ι` of intersection curves exactly.
The transport produces the equivalence

`CleanOneCurve (ParamTorus.mapHomeomorph ψ) ↔ CleanOneCurve standard`,

which is what lets the classical input of Pardon's Lemma 4.2 be stated for the standard torus
alone and transported to the tori `ψ(F)` of the challenge.

All the point-set input used here (`ClosedCurve.mapHomeomorph` and its inverse, the
transport of `IsSimple`, `IsEssential`, `Set.range` and of membership in the carrier) is already
proved in `Submission.Work.CoreTopology`; only the disc-level reassembly is new.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.SphereSlicing

noncomputable section

/-! ## The range of a pulled-back curve -/

/-- The range of the pull-back of a curve along `ψ` is the image under `ψ.symm` of its range. -/
theorem range_mapHomeomorphInv (ψ : R3 ≃ₜ R3)
    (γ : ClosedCurve (ParamTorus.mapHomeomorph ψ)) :
    Set.range (ClosedCurve.mapHomeomorphInv ψ γ).γ = ψ.symm '' Set.range γ.γ :=
  Set.range_comp (⇑ψ.symm) γ.γ

/-! ## Transporting the embedded disc -/

/-- The image of an embedded disc of `ℝ³` under the homeomorphism `ψ`. -/
def pushDisc (ψ : R3 ≃ₜ R3) (e : C(Disc, R3)) : C(Disc, R3) :=
  (homeomorphCMap ψ).comp e

@[simp] theorem pushDisc_apply (ψ : R3 ≃ₜ R3) (e : C(Disc, R3)) (z : Disc) :
    pushDisc ψ e z = ψ (e z) := rfl

/-- The range of the pushed-forward disc is the image of its range. -/
theorem range_pushDisc (ψ : R3 ≃ₜ R3) (e : C(Disc, R3)) :
    Set.range (pushDisc ψ e) = ψ '' Set.range e :=
  Set.range_comp (⇑(homeomorphCMap ψ)) (⇑e)

/-- The image of an embedded disc of `ℝ³` under the inverse of the homeomorphism `ψ`. -/
def pullDisc (ψ : R3 ≃ₜ R3) (e : C(Disc, R3)) : C(Disc, R3) :=
  (homeomorphCMap ψ.symm).comp e

@[simp] theorem pullDisc_apply (ψ : R3 ≃ₜ R3) (e : C(Disc, R3)) (z : Disc) :
    pullDisc ψ e z = ψ.symm (e z) := rfl

/-- The range of the pulled-back disc is the image of its range. -/
theorem range_pullDisc (ψ : R3 ≃ₜ R3) (e : C(Disc, R3)) :
    Set.range (pullDisc ψ e) = ψ.symm '' Set.range e :=
  Set.range_comp (⇑(homeomorphCMap ψ.symm)) (⇑e)

/-! ## Pushing a slice disc forward -/

/-- **Pushing a slice disc of the standard torus forward along `ψ`.**  Every field of
`SliceDisc standard` transports along the homeomorphism `ψ` of `ℝ³`: curves to their images,
the disc to its image, and `IsSimple`, `IsEssential`, disjointness of ranges, containment of
ranges and the covering condition are preserved (using that `ψ` is a bijection carrying
`standard.carrier` onto the carrier of `ParamTorus.mapHomeomorph ψ`). -/
def SliceDisc.push (ψ : R3 ≃ₜ R3) (D : SliceDisc standard) :
    SliceDisc (ParamTorus.mapHomeomorph ψ) where
  α := ClosedCurve.mapHomeomorph ψ D.α
  simple := (ClosedCurve.isSimple_mapHomeomorph_iff ψ D.α).mpr D.simple
  e := pushDisc ψ D.e
  inj := fun z w h => D.inj (ψ.injective h)
  boundary := fun θ => by
    show ψ (D.e (circlePoint θ)) = (ClosedCurve.mapHomeomorph ψ D.α).γ θ
    rw [D.boundary θ]
    rfl
  ι := D.ι
  fintype := D.fintype
  curves := fun i => ClosedCurve.mapHomeomorph ψ (D.curves i)
  curves_simple := fun i =>
    (ClosedCurve.isSimple_mapHomeomorph_iff ψ (D.curves i)).mpr (D.curves_simple i)
  curves_inessential := fun i h =>
    D.curves_inessential i ((ClosedCurve.isEssential_mapHomeomorph_iff ψ (D.curves i)).mp h)
  curves_disjoint := fun i j hij => by
    show Disjoint (Set.range (ClosedCurve.mapHomeomorph ψ (D.curves i)).γ)
      (Set.range (ClosedCurve.mapHomeomorph ψ (D.curves j)).γ)
    rw [ClosedCurve.range_mapHomeomorph, ClosedCurve.range_mapHomeomorph]
    exact Set.disjoint_image_of_injective ψ.injective (D.curves_disjoint hij)
  curves_subset := fun i => by
    show Set.range (ClosedCurve.mapHomeomorph ψ (D.curves i)).γ ⊆ Set.range (pushDisc ψ D.e)
    rw [ClosedCurve.range_mapHomeomorph, range_pushDisc]
    exact Set.image_mono (D.curves_subset i)
  covers := fun z hz hmem => by
    have hmem' : D.e z ∈ standard.carrier := by
      have h := hmem
      rw [pushDisc_apply, mem_carrier_mapHomeomorph_iff] at h
      exact h
    obtain ⟨i, hi⟩ := D.covers z hz hmem'
    refine ⟨i, ?_⟩
    show pushDisc ψ D.e z ∈ Set.range (ClosedCurve.mapHomeomorph ψ (D.curves i)).γ
    rw [pushDisc_apply, ClosedCurve.range_mapHomeomorph]
    exact ⟨D.e z, hi, rfl⟩

@[simp] theorem SliceDisc.push_α (ψ : R3 ≃ₜ R3) (D : SliceDisc standard) :
    (SliceDisc.push ψ D).α = ClosedCurve.mapHomeomorph ψ D.α := rfl

@[simp] theorem SliceDisc.push_card (ψ : R3 ≃ₜ R3) (D : SliceDisc standard) :
    Fintype.card (SliceDisc.push ψ D).ι = Fintype.card D.ι := rfl

/-! ## Pulling a slice disc back -/

/-- **Pulling a slice disc of `ParamTorus.mapHomeomorph ψ` back to the standard torus.**  This is
`SliceDisc.push ψ.symm` with the curves read as `ClosedCurve.mapHomeomorphInv ψ` on the standard
torus rather than as `ClosedCurve.mapHomeomorph ψ.symm` on the (carrier-equal) torus
`ParamTorus.mapHomeomorph ψ.symm`. -/
def SliceDisc.pull (ψ : R3 ≃ₜ R3) (D : SliceDisc (ParamTorus.mapHomeomorph ψ)) :
    SliceDisc standard where
  α := ClosedCurve.mapHomeomorphInv ψ D.α
  simple := (ClosedCurve.isSimple_mapHomeomorphInv_iff ψ D.α).mpr D.simple
  e := pullDisc ψ D.e
  inj := fun z w h => D.inj (ψ.symm.injective h)
  boundary := fun θ => by
    show ψ.symm (D.e (circlePoint θ)) = (ClosedCurve.mapHomeomorphInv ψ D.α).γ θ
    rw [D.boundary θ]
    rfl
  ι := D.ι
  fintype := D.fintype
  curves := fun i => ClosedCurve.mapHomeomorphInv ψ (D.curves i)
  curves_simple := fun i =>
    (ClosedCurve.isSimple_mapHomeomorphInv_iff ψ (D.curves i)).mpr (D.curves_simple i)
  curves_inessential := fun i h =>
    D.curves_inessential i ((ClosedCurve.isEssential_mapHomeomorphInv_iff ψ (D.curves i)).mp h)
  curves_disjoint := fun i j hij => by
    show Disjoint (Set.range (ClosedCurve.mapHomeomorphInv ψ (D.curves i)).γ)
      (Set.range (ClosedCurve.mapHomeomorphInv ψ (D.curves j)).γ)
    rw [range_mapHomeomorphInv, range_mapHomeomorphInv]
    exact Set.disjoint_image_of_injective ψ.symm.injective (D.curves_disjoint hij)
  curves_subset := fun i => by
    show Set.range (ClosedCurve.mapHomeomorphInv ψ (D.curves i)).γ ⊆ Set.range (pullDisc ψ D.e)
    rw [range_mapHomeomorphInv, range_pullDisc]
    exact Set.image_mono (D.curves_subset i)
  covers := fun z hz hmem => by
    have hmem' : D.e z ∈ (ParamTorus.mapHomeomorph ψ).carrier :=
      (mem_carrier_mapHomeomorph_iff' ψ (D.e z)).mpr (by simpa using hmem)
    obtain ⟨i, hi⟩ := D.covers z hz hmem'
    refine ⟨i, ?_⟩
    show pullDisc ψ D.e z ∈ Set.range (ClosedCurve.mapHomeomorphInv ψ (D.curves i)).γ
    rw [pullDisc_apply, range_mapHomeomorphInv]
    exact ⟨D.e z, hi, rfl⟩

@[simp] theorem SliceDisc.pull_α (ψ : R3 ≃ₜ R3)
    (D : SliceDisc (ParamTorus.mapHomeomorph ψ)) :
    (SliceDisc.pull ψ D).α = ClosedCurve.mapHomeomorphInv ψ D.α := rfl

@[simp] theorem SliceDisc.pull_card (ψ : R3 ≃ₜ R3)
    (D : SliceDisc (ParamTorus.mapHomeomorph ψ)) :
    Fintype.card (SliceDisc.pull ψ D).ι = Fintype.card D.ι := rfl

/-! ## Invariance of `CleanOneCurve` -/

/-- **The cut-and-paste of Pardon's second innermost argument is invariant under an ambient
homeomorphism of `ℝ³`.**  `SliceDisc.push` and `SliceDisc.pull` are inverse transports
preserving the boundary curve and the number of intersection curves, so a strictly decreasing
replacement of a slice disc on one torus is a strictly decreasing replacement on the other. -/
theorem cleanOneCurve_map_homeomorph_iff (φ : LeanEval.KnotTheory.PardonDistortion.R3 ≃ₜ
      LeanEval.KnotTheory.PardonDistortion.R3) :
    Work.Topology.SphereSlicing.CleanOneCurve (Work.CoreTopology.ParamTorus.mapHomeomorph φ) ↔
      Work.Topology.SphereSlicing.CleanOneCurve Work.CoreTopology.standard := by
  constructor
  · intro h D hD
    have hDφ : 0 < Fintype.card (SliceDisc.push φ D).ι := by
      rw [SliceDisc.push_card]; exact hD
    obtain ⟨E, hEα, hEcard⟩ := h (SliceDisc.push φ D) hDφ
    refine ⟨SliceDisc.pull φ E, ?_, ?_⟩
    · rw [SliceDisc.pull_α, hEα, SliceDisc.push_α]
      exact ClosedCurve.mapHomeomorphInv_mapHomeomorph φ D.α
    · calc Fintype.card (SliceDisc.pull φ E).ι = Fintype.card E.ι := SliceDisc.pull_card φ E
        _ < Fintype.card (SliceDisc.push φ D).ι := hEcard
        _ = Fintype.card D.ι := SliceDisc.push_card φ D
  · intro h D hD
    have hD0 : 0 < Fintype.card (SliceDisc.pull φ D).ι := by
      rw [SliceDisc.pull_card]; exact hD
    obtain ⟨E, hEα, hEcard⟩ := h (SliceDisc.pull φ D) hD0
    refine ⟨SliceDisc.push φ E, ?_, ?_⟩
    · rw [SliceDisc.push_α, hEα, SliceDisc.pull_α]
      exact ClosedCurve.mapHomeomorph_mapHomeomorphInv φ D.α
    · calc Fintype.card (SliceDisc.push φ E).ι = Fintype.card E.ι := SliceDisc.push_card φ E
        _ < Fintype.card (SliceDisc.pull φ D).ι := hEcard
        _ = Fintype.card D.ι := SliceDisc.pull_card φ D

end

end Work.Topology.SphereSlicing
