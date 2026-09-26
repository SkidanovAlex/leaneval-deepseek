import Mathlib
import Submission.Work.Drive.Final.dentedRegion_frontier
import Submission.Work.Drive.Final.dentRegion_union_strip
import Submission.Work.Drive.Final.noJumpBelow_of_region
import Submission.Work.Drive.EpsFormSphere.bigComponent_compl_inessentialCurves
import Submission.Work.BoxShrink.PinchOff.windingSpan_sdiff_range_eq_of_not_isEssential

/-!
# The no-jump step at an event of the tilted sweep

(The `(L)` field of `Work.Drive.Final.TiltedSweepMono` at an *exceptional* level — the lead's
`noJumpBelow_of_goodData`, `Submission/Work/Drive/Final/NOTES_LEAD_grazes_L.md`.)

At an exceptional level `lamstar = ℓ D.centre` of the tilted sweep (the level of an event `p` of the
sweep height, resolved by the dent datum `D` of `Work.Drive.Final.DentDatum`), the no-jump clause

  `Work.Drive.Mono.NoJumpBelowAt P s c σ u v h ℓ lamstar`

follows from **three** geometric inputs and nothing else:

1. the *union-form genericity* `hgen`: every point of the surface in the closed box and the closed
   slab whose level is `lamstar` lies in the closure of the dented region `Ω` or on the family
   `⋃ cs`;
2. the **clopen clause** and `W Ω = ⊥` for the dented region `Ω`;
3. a supply of an essential closed curve `ζ` of the surface avoiding `closure Ω`, the family `⋃ cs`
   and the trace of the dent's support ball `carrier ∩ closedBall D.centre D.r`;
4. *nothing else*: the **error-set strip clause** — the only other geometric input of
   `Work.Drive.Final.noJumpBelow_of_region_avoiding` — is **derived**, unconditionally, from the
   dent datum by `Work.Drive.Final.dentRegion_union_strip` (proved).

The region is the correct one of the design (lead's item 0),

  `Ω = P.carrier ∩ interior (D.deform '' tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))`,

i.e. the points of the surface inside the *interior* of the image of the level's removed set under
the dent — **not** `D.dentStep 1 (X λ*)`, which is the image of the region and lies off the surface.

## The supply of `ζ`

`Work.Drive.Final.exists_essential_avoiding_of_not_span_bot` below is the reduction used by the
consumer: `ζ` exists as soon as the region `P.carrier ∖ (⋃ cs ∪ E)` has non-vanishing winding span
(and the clopen clause with `W Ω = ⊥` hold).  The only geometric fact behind it is the point-set
argument of `Work.Drive.Final.noJumpBelow_of_region`: an essential curve of the surface which avoids
the trace `⋃ cs` never meets `closure Ω` — because `closure Ω ∩ (carrier ∖ ⋃ cs) = Ω` and `W Ω = ⊥`
(so a curve of `carrier ∖ ⋃ cs` entering `Ω` would be inessential).

`Work.Drive.Final.exists_essential_avoiding_of_bot_clopen` is the companion with a *disc* error set:
a `DiscRegion` containing `E` whose **boundary circle** avoids the trace.  It uses the peel
`Work.Drive.BoxShrink.PinchOff.windingSpan_le_sdiff_carrier_of_discRegion`, whose only hypothesis on
the ambient region is that it contains that boundary circle.

The stripping of the trace curves from the whole carrier (`W (carrier ∖ ⋃ cs) = ⊤`, by
`Work.Drive.BoxShrink.PinchOff.windingSpan_sdiff_iUnion_range_eq_of_not_isEssential`) is what makes
both statements available without any counting hypothesis: the counting enters only through the
**inessentiality** of the curves `cs`.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped Topology

namespace Work.Drive.Final

noncomputable section

/-! ## An essential curve off the trace never meets the closure of the level region -/

/-- **The point-set core of the no-jump argument.**  Let `Ω` be a region of the surface with the
*clopen* property `closure Ω ∩ (carrier ∖ T) = Ω` w.r.t. a family of closed curves with trace `T`,
and with `W Ω = ⊥`.  Then **every** essential closed curve of the surface whose image avoids `T`
also avoids `closure Ω`.

Proof: on the surface, the image of the curve is preconnected and covered by the ambient open set `B`
of `Ω` and the open set `(closure Ω)ᶜ`; these meet only inside `Ω ⊆ closure Ω`, so the image lies in
one of them.  If it lay in `B` it would lie in `Ω` (inside the carrier), hence carry vanishing
winding span, contradicting essentiality.  Hence it lies outside `closure Ω`. -/
theorem not_mem_closure_of_essential_of_subset_sdiff_trace {P : Work.CoreTopology.ParamTorus}
    {Ω : Set R3} {n : ℕ} {cs : Fin n → Work.CoreTopology.ClosedCurve P}
    (hΩc : Ω ⊆ P.carrier) (hΩopen : Work.SurgeryInvariance.IsOpenInCarrier P Ω)
    (hcl : closure Ω ∩ (P.carrier \ ⋃ i, Set.range (cs i).γ) = Ω)
    (hbot : Work.SurgeryInvariance.WindingSpan P Ω = ⊥)
    (ζ : Work.CoreTopology.ClosedCurve P) (hζ : Work.CoreTopology.IsEssential P ζ)
    (hsub : Set.range ζ.γ ⊆ P.carrier \ ⋃ i, Set.range (cs i).γ) :
    ∀ t : ℝ, ζ.γ t ∉ closure Ω := by
  classical
  obtain ⟨B, hBopen, hBeq⟩ := (isOpen_induced_iff (f := (Subtype.val : P.carrier → R3))
    (s := (Subtype.val ⁻¹' Ω))).mp hΩopen
  have hmemB : ∀ z : R3, z ∈ Ω ↔ z ∈ P.carrier ∧ z ∈ B := by
    intro z
    constructor
    · intro hz
      refine ⟨hΩc hz, ?_⟩
      have h1 : (⟨z, hΩc hz⟩ : P.carrier) ∈ Subtype.val ⁻¹' Ω := hz
      rw [← hBeq] at h1
      exact h1
    · rintro ⟨hzc, hzB⟩
      have h1 : (⟨z, hzc⟩ : P.carrier) ∈ Subtype.val ⁻¹' B := hzB
      rw [hBeq] at h1
      exact h1
  have hSpre : IsPreconnected (Set.range ζ.γ) := by
    rw [Work.CoreTopology.ClosedCurve.range_eq_image P ζ]
    exact isPreconnected_Ico.image ζ.γ ζ.cont.continuousOn
  have hcarrier : Set.range ζ.γ ⊆ P.carrier := fun z ⟨t, ht⟩ => ht ▸ ζ.mem t
  have hSU : Set.range ζ.γ ⊆ B ∪ (closure Ω)ᶜ := by
    intro z hz
    by_cases hzB : z ∈ B
    · exact Or.inl hzB
    · refine Or.inr (fun hzcl => hzB ?_)
      have h1 : z ∈ closure Ω ∩ (P.carrier \ ⋃ i, Set.range (cs i).γ) := ⟨hzcl, hsub hz⟩
      rw [hcl] at h1
      exact (hmemB z).mp h1 |>.2
  have hSZdis : Set.range ζ.γ ∩ (B ∩ (closure Ω)ᶜ) = ∅ := by
    rw [← Set.not_nonempty_iff_eq_empty]
    rintro ⟨z, hzS, hzB, hzV⟩
    have hzcar : z ∈ P.carrier := hcarrier hzS
    have hzΩ : z ∈ Ω := (hmemB z).mpr ⟨hzcar, hzB⟩
    exact hzV (subset_closure hzΩ)
  have hSdisjClosure : Disjoint (Set.range ζ.γ) (closure Ω) := by
    by_cases hSU0 : (Set.range ζ.γ ∩ B).Nonempty
    · exfalso
      have hSV0 : Set.range ζ.γ ∩ (closure Ω)ᶜ = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        intro hne
        have h1 : (Set.range ζ.γ ∩ (B ∩ (closure Ω)ᶜ)).Nonempty :=
          hSpre B (closure Ω)ᶜ hBopen isClosed_closure.isOpen_compl hSU hSU0 hne
        rw [hSZdis] at h1
        exact Set.not_nonempty_empty h1
      have hSsubB : Set.range ζ.γ ⊆ B := by
        intro z hz
        rcases hSU hz with h | h
        · exact h
        · have h2 : (Set.range ζ.γ ∩ (closure Ω)ᶜ).Nonempty := ⟨z, hz, h⟩
          rw [hSV0] at h2
          exact absurd h2 Set.not_nonempty_empty
      have hSsubΩ : Set.range ζ.γ ⊆ Ω := by
        intro z hz
        exact (hmemB z).mpr ⟨hcarrier hz, hSsubB hz⟩
      have hWne : Work.SurgeryInvariance.WindingSpan P (Set.range ζ.γ) ≠ ⊥ :=
        (Work.SurgeryInvariance.windingSpan_ne_bot_iff P _).mpr ⟨ζ, hζ, fun t => ⟨t, rfl⟩⟩
      have hle : Work.SurgeryInvariance.WindingSpan P (Set.range ζ.γ) ≤
          Work.SurgeryInvariance.WindingSpan P Ω :=
        Work.SurgeryInvariance.WindingSpan_mono P hSsubΩ
      rw [hbot] at hle
      exact hWne (le_bot_iff.mp hle)
    · rw [Set.disjoint_left]
      intro z hzrange hzcl
      rcases hSU hzrange with h | h
      · have h2 : (Set.range ζ.γ ∩ B).Nonempty := ⟨z, hzrange, h⟩
        rw [Set.not_nonempty_iff_eq_empty.mp hSU0] at h2
        exact Set.not_nonempty_empty h2
      · exact h hzcl
  intro t ht
  exact (Set.disjoint_left.mp hSdisjClosure) ⟨t, rfl⟩ ht

/-- **The supply of the essential loop from a non-vanishing span of the complement.** -/
theorem exists_essential_avoiding_of_not_span_bot {P : Work.CoreTopology.ParamTorus}
    {Ω : Set R3} {n : ℕ} {cs : Fin n → Work.CoreTopology.ClosedCurve P}
    (hΩc : Ω ⊆ P.carrier) (hΩopen : Work.SurgeryInvariance.IsOpenInCarrier P Ω)
    (hcl : closure Ω ∩ (P.carrier \ ⋃ i, Set.range (cs i).γ) = Ω)
    (hbot : Work.SurgeryInvariance.WindingSpan P Ω = ⊥)
    (E : Set R3)
    (hW : Work.SurgeryInvariance.WindingSpan P
      (P.carrier \ ((⋃ i, Set.range (cs i).γ) ∪ E)) ≠ ⊥) :
    ∃ ζ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P ζ ∧
      (∀ t : ℝ, ζ.γ t ∉ closure Ω) ∧ (∀ t : ℝ, ζ.γ t ∉ ⋃ i, Set.range (cs i).γ) ∧
      (∀ t : ℝ, ζ.γ t ∉ E) := by
  classical
  obtain ⟨ζ, hζ, hζmem⟩ :=
    (Work.SurgeryInvariance.windingSpan_ne_bot_iff P
      (P.carrier \ ((⋃ i, Set.range (cs i).γ) ∪ E))).mp hW
  have hsub : Set.range ζ.γ ⊆ P.carrier \ ⋃ i, Set.range (cs i).γ := by
    rintro z ⟨t, ht⟩
    have h := hζmem t
    rw [ht] at h
    exact ⟨h.1, fun hh => h.2 (Or.inl hh)⟩
  refine ⟨ζ, hζ, not_mem_closure_of_essential_of_subset_sdiff_trace hΩc hΩopen hcl hbot ζ hζ
    hsub, ?_, ?_⟩
  · intro t h
    exact (hζmem t).2 (Or.inl h)
  · intro t h
    exact (hζmem t).2 (Or.inr h)

/-- **The supply of the essential loop from a disc error set.**  If a `DiscRegion` of the surface
contains `E` and has its **boundary circle** off the trace, then an essential loop avoiding
`closure Ω`, the trace and `E` exists: peel the trace off the whole carrier
(`W (carrier ∖ trace) = ⊤`), peel the disc
(`Work.Drive.BoxShrink.PinchOff.windingSpan_le_sdiff_carrier_of_discRegion`), and take an essential
curve of what remains.

Note that the disc may meet the trace inside its carrier (`D.carrier ∩ T ≠ ∅` is allowed); only
`D.boundary` has to avoid it. -/
theorem exists_essential_avoiding_of_bot_clopen {P : Work.CoreTopology.ParamTorus}
    {Ω : Set R3} {n : ℕ} {cs : Fin n → Work.CoreTopology.ClosedCurve P}
    (hΩc : Ω ⊆ P.carrier) (hΩopen : Work.SurgeryInvariance.IsOpenInCarrier P Ω)
    (hsimple : ∀ i, Work.CoreTopology.IsSimple P (cs i))
    (hess : ∀ i, ¬ Work.CoreTopology.IsEssential P (cs i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ))
    (hcl : closure Ω ∩ (P.carrier \ ⋃ i, Set.range (cs i).γ) = Ω)
    (hbot : Work.SurgeryInvariance.WindingSpan P Ω = ⊥)
    (D : Work.SurgeryInvariance.DiscRegion P) (E : Set R3) (hED : E ⊆ D.carrier)
    (hDbdy : D.boundary ⊆ P.carrier \ ⋃ i, Set.range (cs i).γ) :
    ∃ ζ : Work.CoreTopology.ClosedCurve P, Work.CoreTopology.IsEssential P ζ ∧
      (∀ t : ℝ, ζ.γ t ∉ closure Ω) ∧ (∀ t : ℝ, ζ.γ t ∉ ⋃ i, Set.range (cs i).γ) ∧
      (∀ t : ℝ, ζ.γ t ∉ E) := by
  classical
  set T : Set R3 := ⋃ i, Set.range (cs i).γ with hT
  have hTclosed : IsClosed T := by
    rw [hT]
    exact Work.Drive.EpsFormSphere.isClosed_iUnion_range_closedCurve cs
  have hcarrierOpen : Work.SurgeryInvariance.IsOpenInCarrier P P.carrier := by
    rw [Work.SurgeryInvariance.IsOpenInCarrier]
    have h : (Subtype.val ⁻¹' P.carrier : Set P.carrier) = Set.univ := by ext x; simp
    rw [h]
    exact isOpen_univ
  have hXopen : Work.SurgeryInvariance.IsOpenInCarrier P (P.carrier \ T) :=
    Work.BoxShrink.PinchOff.isOpenInCarrier_sdiff_of_isClosed hcarrierOpen hTclosed
  have hWT : Work.SurgeryInvariance.WindingSpan P (P.carrier \ T) = ⊤ := by
    have hpeel := Work.BoxShrink.PinchOff.windingSpan_sdiff_iUnion_range_eq_of_not_isEssential
      (P := P) (X := P.carrier) (γ := cs) hcarrierOpen hsimple hess hdisj
      (fun i t => (cs i).mem t)
    rw [hT, ← hpeel]
    exact Work.SurgeryInvariance.WindingSpan.carrier_eq_top P
  have hsub : D.boundary ⊆ P.carrier \ T := by rw [hT]; exact hDbdy
  have hle := Work.BoxShrink.PinchOff.windingSpan_le_sdiff_carrier_of_discRegion
    (P := P) D hXopen hsub
  have hWfin : Work.SurgeryInvariance.WindingSpan P ((P.carrier \ T) \ D.carrier) = ⊤ :=
    le_antisymm le_top (by rw [← hWT]; exact hle)
  obtain ⟨ζ, hζess, hζmem⟩ :=
    (Work.SurgeryInvariance.windingSpan_ne_bot_iff P ((P.carrier \ T) \ D.carrier)).mp
      (by rw [hWfin]; exact top_ne_bot)
  have hsubC : Set.range ζ.γ ⊆ P.carrier \ T := by
    rintro z ⟨t, ht⟩
    rw [← ht]
    exact (hζmem t).1
  exact ⟨ζ, hζess,
    not_mem_closure_of_essential_of_subset_sdiff_trace hΩc hΩopen hcl hbot
      ζ hζess hsubC,
    fun t h => (hζmem t).1.2 (by rw [hT]; exact h),
    fun t h => (hζmem t).2 (hED h)⟩

/-! ## The no-jump step at an event -/

/-- **The no-jump step at an event, from the dent datum.**  See the module docstring: the strip
clause is derived, so the only hypotheses besides the datum are the union-form genericity `hgen` and
the essential loop `ζ` avoiding `closure Ω ∪ ⋃ cs ∪ E`. -/
theorem noJumpBelowAt_of_dentData
    {ψ : Submission.Diffeo} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ}
    {ℓ : R3 →L[ℝ] ℝ} {lamstar : ℝ} (D : DentDatum ψ s c σ u v h R ℓ)
    (hlam : ℓ D.centre = lamstar)
    {n : ℕ} {cs : Fin n → Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ)}
    (hgen : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ closure (Submission.PBox s c σ) →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = lamstar →
      z ∈ closure (eventDentedRegion ψ s c σ u v h R ℓ D) ∪ ⋃ i, Set.range (cs i).γ)
    (ζ : Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ))
    (hζ : Work.CoreTopology.IsEssential (Work.Drive.EpsSphere.torusOf ψ) ζ)
    (hζΩ : ∀ t, ζ.γ t ∉ closure (eventDentedRegion ψ s c σ u v h R ℓ D))
    (hζT : ∀ t, ζ.γ t ∉ ⋃ i, Set.range (cs i).γ)
    (hζE : ∀ t, ζ.γ t ∉ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        Metric.closedBall D.centre D.r) :
    Work.Drive.Mono.NoJumpBelowAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lamstar := by
  intro _hbot
  refine Work.Drive.Final.noJumpBelow_of_region_avoiding
    (P := Work.Drive.EpsSphere.torusOf ψ) (s := s) (c := c) (σ := σ) (u := u) (v := v)
    (h := h) (ℓ := ℓ) (lamstar := lamstar)
    (Ω := eventDentedRegion ψ s c σ u v h R ℓ D)
    (E := (Work.Drive.EpsSphere.torusOf ψ).carrier ∩ Metric.closedBall D.centre D.r)
    (cs := cs) (ζ := ζ) hζ hζΩ hζT hζE hgen ?_
  intro mu _hmu
  rw [← hlam]
  exact dentRegion_union_strip (P := Work.Drive.EpsSphere.torusOf ψ) D

/-! ## The bundled residual of the `(L)` package at an event -/

/-- **The residual of the `(L)` package at an event**: the four geometric inputs of
`Work.Drive.Final.noJumpBelowAt_of_dentData`, gathered into one `Prop`.  In words:

* **(trace)** the trace `carrier ∩ frontier (D.deform '' tiltedLevelRemoved … (ℓ D.centre))` is the
  union of the ranges of finitely many pairwise disjoint simple closed curves of the surface, each
  **inessential** in it;
* **(clopen)** that family is in clopen position w.r.t. the dented region `Ω`;
* **(span)** `W Ω = ⊥`;
* **(generic)** the union-form genericity at the event's level, with `Ω` and the trace on the right;
* **(loop)** an essential closed curve `ζ` of the surface avoiding `closure Ω`, the trace, and the
  trace `carrier ∩ closedBall D.centre D.r` of the dent's support ball.

The *tameness* half of (trace) is already a theorem
(`Work.Drive.Final.dentedTraceCurves`, needing compactness — free, by
`Work.Drive.Final.isCompact_frontier_deform_removed` — and local Euclideanity, i.e. the stratified
transversality of the wall, the slab faces and the box sphere); the error-set strip clause is
derived (`Work.Drive.Final.dentRegion_union_strip`); and (loop) is supplied by
`Work.Drive.Final.exists_essential_avoiding_of_not_span_bot` as soon as
`W (carrier ∖ (⋃ cs ∪ E)) ≠ ⊥` (with the clopen clause and `W Ω = ⊥`). -/
def DentResolved {ψ : Submission.Diffeo} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3}
    {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} (D : DentDatum ψ s c σ u v h R ℓ) : Prop :=
  ∃ (n : ℕ) (cs : Fin n → Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ))
    (ζ : Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ)),
    (∀ i, Work.CoreTopology.IsSimple (Work.Drive.EpsSphere.torusOf ψ) (cs i)) ∧
    (∀ i, ¬ Work.CoreTopology.IsEssential (Work.Drive.EpsSphere.torusOf ψ) (cs i)) ∧
    (∀ i j : Fin n, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ)) ∧
    (closure (eventDentedRegion ψ s c σ u v h R ℓ D) ∩
        ((Work.Drive.EpsSphere.torusOf ψ).carrier \ ⋃ i, Set.range (cs i).γ) =
      eventDentedRegion ψ s c σ u v h R ℓ D) ∧
    (Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (eventDentedRegion ψ s c σ u v h R ℓ D) = ⊥) ∧
    (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ closure (Submission.PBox s c σ) →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = ℓ D.centre →
      z ∈ closure (eventDentedRegion ψ s c σ u v h R ℓ D) ∪ ⋃ i, Set.range (cs i).γ) ∧
    Work.CoreTopology.IsEssential (Work.Drive.EpsSphere.torusOf ψ) ζ ∧
    (∀ t : ℝ, ζ.γ t ∉ closure (eventDentedRegion ψ s c σ u v h R ℓ D)) ∧
    (∀ t : ℝ, ζ.γ t ∉ ⋃ i, Set.range (cs i).γ) ∧
    (∀ t : ℝ, ζ.γ t ∉ (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      Metric.closedBall D.centre D.r)

/-- **The no-jump step at an event, from the bundled residual.** -/
theorem noJumpBelowAt_of_dentResolved
    {ψ : Submission.Diffeo} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ}
    {ℓ : R3 →L[ℝ] ℝ} {lamstar : ℝ} {D : DentDatum ψ s c σ u v h R ℓ}
    (hlam : ℓ D.centre = lamstar) (hres : DentResolved D) :
    Work.Drive.Mono.NoJumpBelowAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lamstar := by
  obtain ⟨n, cs, ζ, _hsimple, _hess, _hdisj, _hcl, _hbot, hgen, hζ, hζΩ, hζT, hζE⟩ := hres
  exact noJumpBelowAt_of_dentData D hlam
    (fun z hz hzP hzs hzl => hgen z hz hzP hzs (by rw [hzl, hlam])) ζ hζ hζΩ hζT hζE

/-- **The residual with the loop clause replaced by a span condition on the complement.**  This is
the reduction the `(L)` package should be attacked through: everything is geometric except the
single inequality `W (carrier ∖ (trace ∪ support ball)) ≠ ⊥`. -/
theorem dentResolved_of_hgen_span
    {ψ : Submission.Diffeo} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ}
    {ℓ : R3 →L[ℝ] ℝ} (D : DentDatum ψ s c σ u v h R ℓ)
    {n : ℕ} {cs : Fin n → Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ)}
    (hsimple : ∀ i, Work.CoreTopology.IsSimple (Work.Drive.EpsSphere.torusOf ψ) (cs i))
    (hess : ∀ i, ¬ Work.CoreTopology.IsEssential (Work.Drive.EpsSphere.torusOf ψ) (cs i))
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ))
    (hcl : closure (eventDentedRegion ψ s c σ u v h R ℓ D) ∩
        ((Work.Drive.EpsSphere.torusOf ψ).carrier \ ⋃ i, Set.range (cs i).γ) =
      eventDentedRegion ψ s c σ u v h R ℓ D)
    (hbot : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (eventDentedRegion ψ s c σ u v h R ℓ D) = ⊥)
    (hgen : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ closure (Submission.PBox s c σ) →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h → ℓ z = ℓ D.centre →
      z ∈ closure (eventDentedRegion ψ s c σ u v h R ℓ D) ∪ ⋃ i, Set.range (cs i).γ)
    (hW : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
      ((Work.Drive.EpsSphere.torusOf ψ).carrier \
        ((⋃ i, Set.range (cs i).γ) ∪
          ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ Metric.closedBall D.centre D.r))) ≠ ⊥) :
    DentResolved D := by
  obtain ⟨ζ, hζ, hζΩ, hζT, hζE⟩ :=
    exists_essential_avoiding_of_not_span_bot (P := Work.Drive.EpsSphere.torusOf ψ)
      (Ω := eventDentedRegion ψ s c σ u v h R ℓ D)
      (eventDentedRegion_subset_carrier D) (isOpenInCarrier_eventDentedRegion D)
      hcl hbot _ hW
  exact ⟨n, cs, ζ, hsimple, hess, hdisj, hcl, hbot, hgen, hζ, hζΩ, hζT, hζE⟩

end

end Work.Drive.Final
