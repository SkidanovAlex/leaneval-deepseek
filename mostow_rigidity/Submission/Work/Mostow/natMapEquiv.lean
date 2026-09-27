import Mathlib
import Submission.Mostow.Interfaces
import Submission.Work.Mostow.NatMeasure

/-! Guidance from the project lead (the requester):

# Area N1 — natMapEquiv : NatMapEquivProp n   (lead's design; short area)

natMap φ u = bar ((visual n u).map φ). Given φ bijective and continuous on Sph with φ ∘ bd g = bd h ∘ φ on Sph.
Chain (all measures live on Sph, so a.e.-equalities on Sph suffice):
 (visual (g•u)).map φ = ((visual u).map (bd g)).map φ          [VisualProp]
                      = (visual u).map (φ ∘ bd g)               [`Measure.map_map` / AEMeasurable version]
                      = (visual u).map (bd h ∘ φ)               [`Measure.map_congr`: equal on Sph, visual u (Sphᶜ) = 0]
                      = ((visual u).map φ).map (bd h)
 bar of it = h • bar ((visual u).map φ)                          [BaryProp equivariance]
Side conditions for BaryProp on ν = (visual u).map φ: probability (φ AEMeasurable: φ agrees a.e. with the measurable
`Set.piecewise (Sph n) φ 0`-type modification, ContinuousOn on the closed set Sph ⇒ measurable restriction);
ν(Sphᶜ) = 0 (φ maps Sph into Sph); no atoms (φ injective on Sph ⇒ φ⁻¹{ξ} ∩ Sph has ≤ 1 point, visual has no atoms).
Write one helper lemma `natMeasure_good` (these three facts) — natMapJac and natMapSurj need the same; put it at
`Submission/Work/Mostow/NatMeasure.lean`-style shared path and say so in your report.
-/

/-!
## Implementation notes (Work.Mostow.natMapEquiv)

The three BaryProp side conditions for `ν = (visual n u).map φ` and the a.e.-measurability of `φ`
are proved once, for arbitrary `φ` a continuous bijection of `Sph n`, in the shared module
`Submission/Work/Mostow/NatMeasure.lean` as `Work.Mostow.natMeasure_good`
(this is the helper the N2/N3 areas are meant to reuse).

The measure chain is then:
* `VisualProp` gives `(visual n u).map (bd g) = visual n (g • u)`;
* `AEMeasurable.map_map_of_aemeasurable` twice, with `Measurable (bd g)` from `POActionProp`,
  and `AEMeasurable φ` of the relevant visual measure (transported across the above identity,
  since `g • u` is again a point of `E n`, so the helper applies at `g • u`);
* in the middle, `Measure.map_congr` using the a.e.-equality `φ ∘ bd g =ᵐ bd h ∘ φ`, which follows
  from the hypothesis on `Sph n` and `visual n u (Sph n)ᶜ = 0`.
Finally `BaryProp`'s equivariance clause (`bar (ν.map (bd h)) = h • bar ν`) applied to `ν` gives
`natMap φ (g • u) = h • natMap φ u` definitionally.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

theorem natMapEquiv (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (hV : VisualProp n) (hB : BaryProp n) : NatMapEquivProp n := by
  intro φ hbij hcont g h hcomm u
  -- the last two clauses of `POActionProp`: `bd` is continuous on the sphere and measurable
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hbdmeas⟩ := hA
  -- `visual n u` is carried by `Sph n`, so the hypothesis only has to hold on `Sph n`
  have hmem : ∀ᵐ x ∂(visual n u), x ∈ Sph n := by
    rw [ae_iff]
    simpa only [Set.compl_def] using (hV u).2.1
  have hcongr : (φ ∘ bd g) =ᵐ[visual n u] (bd h ∘ φ) := by
    filter_upwards [hmem] with x hx
    exact hcomm x hx
  -- the side conditions on `ν = (visual n u).map φ`, and a.e.-measurability of `φ`
  have hgood := natMeasure_good n hV φ hbij hcont u
  have haeφ : AEMeasurable φ (visual n u) := hgood.2.2.2
  have haegu : AEMeasurable φ (visual n (g • u)) :=
    (natMeasure_good n hV φ hbij hcont (g • u)).2.2.2
  have hmap : (visual n u).map (bd g) = visual n (g • u) := (hV u).2.2.2.2 g
  have haebdg : AEMeasurable φ ((visual n u).map (bd g)) := by rw [hmap]; exact haegu
  -- the measure chain
  have key : (visual n (g • u)).map φ = ((visual n u).map φ).map (bd h) := by
    rw [← hmap]
    rw [AEMeasurable.map_map_of_aemeasurable haebdg (hbdmeas g).aemeasurable]
    rw [Measure.map_congr hcongr]
    rw [AEMeasurable.map_map_of_aemeasurable (hbdmeas h).aemeasurable haeφ]
  show bar ((visual n (g • u)).map φ) = h • bar ((visual n u).map φ)
  rw [key]
  exact (hB ((visual n u).map φ) hgood.1 hgood.2.1 hgood.2.2.1).2.2 h

end Work.Mostow
