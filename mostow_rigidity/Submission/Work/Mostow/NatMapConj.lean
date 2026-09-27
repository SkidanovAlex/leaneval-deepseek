import Mathlib
import Submission.Work.Mostow.BCGDefs
import Submission.Work.Mostow.NatMeasure

/-!
# `NatMapConj` — conjugation equivariance of the BCG natural map

For a boundary bijection `φ` of `Sph n` (continuous, hence a homeomorphism) and
`g h : PO n 1`, the conjugated boundary map `ξ ↦ h⁻¹ • φ (g • ξ)` is again a continuous
bijection of `Sph n`, and the natural map of the conjugated map is the conjugate of the
natural map:

`natMap (bd h⁻¹ ∘ φ ∘ bd g) u = h⁻¹ • natMap φ (g • u)`.

This is exactly the equivariance clause `NatMapEquivProp` of the natural map, but with the
boundary map *post-composed/pre-composed by group elements* rather than assuming an
equivariance hypothesis on `φ`; it is the form in which the equivariance is needed when the
map `φ` is produced by the boundary extension of a quasi-isometry (Morse lemma) whose
equivariance only holds up to bounded error, and one has to correct it by an element of
`PO n 1`.

## Proof
* `bd k` is a continuous bijection of `Sph n` for every `k : PO n 1` (from `POActionProp`:
  `bd 1 = id` on the sphere and `bd (kq) = bd k ∘ bd q`);
* the measure chain `(visual n u).map (bd h⁻¹ ∘ φ ∘ bd g)
  = (((visual n u).map (bd g)).map φ).map (bd h⁻¹) = ((visual n (g • u)).map φ).map (bd h⁻¹)`
  (using `VisualProp`'s equivariance and `AEMeasurable.map_map_of_aemeasurable`);
* `BaryProp`'s equivariance `bar (ν.map (bd k)) = k • bar ν` finishes it.
The side conditions that `BaryProp` requires of `ν = (visual n (g • u)).map φ` are supplied by
the shared helper `natMeasure_good` (`Submission/Work/Mostow/NatMeasure.lean`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

variable {n : ℕ}

/-- The boundary action of `k` carries the sphere into itself. -/
lemma bd_mapsTo_Sph (hA : POActionProp n) (k : PO n 1) : Set.MapsTo (bd k) (Sph n) (Sph n) := by
  obtain ⟨-, -, -, -, -, -, -, h, -, -, -, -⟩ := hA
  exact h k

/-- The boundary action of `k` is injective on the sphere (`bd (k⁻¹) ∘ bd k = bd 1 = id`). -/
lemma bd_injOn_Sph (hA : POActionProp n) (k : PO n 1) : Set.InjOn (bd k) (Sph n) := by
  obtain ⟨-, -, -, -, -, -, -, -, hOne, hComp, -, -⟩ := hA
  intro ξ hξ η hη h
  calc ξ = bd (1 : PO n 1) ξ := (hOne ξ hξ).symm
    _ = bd (k⁻¹ * k) ξ := by rw [inv_mul_cancel]
    _ = bd k⁻¹ (bd k ξ) := hComp k⁻¹ k ξ hξ
    _ = bd k⁻¹ (bd k η) := by rw [h]
    _ = bd (k⁻¹ * k) η := (hComp k⁻¹ k η hη).symm
    _ = bd (1 : PO n 1) η := by rw [inv_mul_cancel]
    _ = η := hOne η hη

/-- The boundary action of `k` is onto the sphere. -/
lemma bd_surjOn_Sph (hA : POActionProp n) (k : PO n 1) : Set.SurjOn (bd k) (Sph n) (Sph n) := by
  obtain ⟨-, -, -, -, -, -, -, hMap, hOne, hComp, -, -⟩ := hA
  intro η hη
  exact ⟨bd k⁻¹ η, hMap k⁻¹ η hη, by
    calc bd k (bd k⁻¹ η) = bd (k * k⁻¹) η := (hComp k k⁻¹ η hη).symm
      _ = bd (1 : PO n 1) η := by rw [mul_inv_cancel]
      _ = η := hOne η hη⟩

/-- The boundary action of `k` is a bijection of the sphere onto itself. -/
lemma bd_bijOn_Sph (hA : POActionProp n) (k : PO n 1) : Set.BijOn (bd k) (Sph n) (Sph n) :=
  ⟨bd_mapsTo_Sph hA k, bd_injOn_Sph hA k, bd_surjOn_Sph hA k⟩

/-- The boundary action of `k` is continuous on the sphere. -/
lemma bd_contOn_Sph (hA : POActionProp n) (k : PO n 1) : ContinuousOn (bd k) (Sph n) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, h, -⟩ := hA
  exact h k

/-- The boundary action of `k` is measurable. -/
lemma bd_measurableOfProp (hA : POActionProp n) (k : PO n 1) : Measurable (bd k) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h⟩ := hA
  exact h k

theorem NatMapConj (n : ℕ) (hA : Submission.Mostow.POActionProp n) (hV : Submission.Mostow.VisualProp n)
    (hB : Submission.Mostow.BaryProp n) (φ : Submission.Mostow.E n → Submission.Mostow.E n)
    (hbij : Set.BijOn φ (Submission.Mostow.Sph n) (Submission.Mostow.Sph n))
    (hcont : ContinuousOn φ (Submission.Mostow.Sph n)) (g h : LeanEval.Geometry.MostowRigidity.PO n 1) :
    Set.BijOn (fun ξ => Submission.Mostow.bd h⁻¹ (φ (Submission.Mostow.bd g ξ)))
        (Submission.Mostow.Sph n) (Submission.Mostow.Sph n) ∧
    ContinuousOn (fun ξ => Submission.Mostow.bd h⁻¹ (φ (Submission.Mostow.bd g ξ)))
        (Submission.Mostow.Sph n) ∧
    ∀ u : Submission.Mostow.E n,
      Submission.Mostow.natMap (fun ξ => Submission.Mostow.bd h⁻¹ (φ (Submission.Mostow.bd g ξ))) u
        = h⁻¹ • Submission.Mostow.natMap φ (g • u) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ((bd_bijOn_Sph hA h⁻¹).comp hbij).comp (bd_bijOn_Sph hA g)
  · have hinner : ContinuousOn (fun ξ => φ (bd g ξ)) (Sph n) :=
      hcont.comp (bd_contOn_Sph hA g) (bd_mapsTo_Sph hA g)
    exact (bd_contOn_Sph hA h⁻¹).comp hinner (hbij.1.comp (bd_mapsTo_Sph hA g))
  · intro u
    have hgood := natMeasure_good n hV φ hbij hcont (g • u)
    have hmapg : (visual n u).map (bd g) = visual n (g • u) := (hV u).2.2.2.2 g
    have haeφg : AEMeasurable φ ((visual n u).map (bd g)) := by rw [hmapg]; exact hgood.2.2.2
    have haeφbdg : AEMeasurable (φ ∘ bd g) (visual n u) :=
      AEMeasurable.comp_aemeasurable haeφg (bd_measurableOfProp hA g).aemeasurable
    have key : (visual n u).map (fun ξ => bd h⁻¹ (φ (bd g ξ)))
        = ((visual n (g • u)).map φ).map (bd h⁻¹) := by
      calc (visual n u).map (fun ξ => bd h⁻¹ (φ (bd g ξ)))
          = (visual n u).map ((bd h⁻¹) ∘ (φ ∘ bd g)) := rfl
        _ = ((visual n u).map (φ ∘ bd g)).map (bd h⁻¹) :=
              (AEMeasurable.map_map_of_aemeasurable
                (bd_measurableOfProp hA h⁻¹).aemeasurable haeφbdg).symm
        _ = (((visual n u).map (bd g)).map φ).map (bd h⁻¹) := by
              rw [AEMeasurable.map_map_of_aemeasurable haeφg (bd_measurableOfProp hA g).aemeasurable]
        _ = ((visual n (g • u)).map φ).map (bd h⁻¹) := by rw [hmapg]
    change bar ((visual n u).map (fun ξ => bd h⁻¹ (φ (bd g ξ))))
        = h⁻¹ • bar ((visual n (g • u)).map φ)
    rw [key]
    exact (hB ((visual n (g • u)).map φ) hgood.1 hgood.2.1 hgood.2.2.1).2.2 h⁻¹

end Work.Mostow
