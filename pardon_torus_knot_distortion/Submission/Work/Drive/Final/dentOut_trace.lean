import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Final.dentDeform_homeomorph
import Submission.Work.EpsW.countsWd
import Submission.Work.EpsW.exists_family_of_isCompact_of_isLocallyEuclidean
import Submission.Work.InnermostDisk.sphereSlicing_of_isEmbeddedSphere_of_traceCurves
import Submission.Work.CoreTopology.isClosed_carrier

/-!
# L4c: the inessentiality of the trace of the *deformed* level

(Project lead, `Final/NOTES_LEAD_L4_L1.md` §4, L4c.)  The `cs` family of the residual
`Work.Drive.Final.DentOutResolved` must consist of **inessential** curves covering the trace

  `carrier ∩ frontier (D.deform ⁻¹' tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))`.

Pardon's counting supplies the inessentiality of the trace of the *undeformed* level: the level
frontier is covered by embedded spheres (`Work.Drive.Final.SphereCoverAt`, carried by the bundle
`Work.Drive.Final.GoodSweepData3`), and each sphere carries no essential loop by Pardon's Lemma 2
(`Work.EpsW.trace_inessential_of_slicing_of_countsWd`) applied to its own slicing and the level
count.

This module transports that statement along the dent:

* `Work.Drive.Final.dentDeform_eq_self_of_le` — the deformation is the identity outside its ball;
* `Work.Drive.Final.frontier_preimage_homeomorph` / `isEmbeddedSphere_preimage` — a homeomorphism of
  `ℝ³` commutes with `frontier` and preserves embedded spheres;
* `Work.Drive.Final.knot_inter_dentDeform_preimage` — a knot avoiding the ball has the same
  intersection with a set as with its preimage under the dent (this is what makes the *count* at the
  deformed level equal to the count at the undeformed one);
* `Work.Drive.Final.not_containsEssentialLoop_iUnion_of_carrier_disjoint` — a set covered by finitely
  many *carrier-disjoint* closed sets, none of which contains an essential loop, contains none;
* `Work.Drive.Final.not_containsEssentialLoop_of_isEmbeddedSphere` — Pardon's Lemma 2 for one
  embedded sphere, in the shape consumed here;
* **`Work.Drive.Final.dentOut_trace_noEssential_of_sphereCover`** — L4c: given the sphere cover of
  the undeformed level, the level count, and the *tameness of the pulled-back spheres* (L4b), no
  essential loop lies in the frontier of the deformed removed set.

The tameness hypotheses (`htame`) are exactly the content of L4b; everything else here is proved.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped Topology

namespace Work.Drive.Final

noncomputable section

/-! ## The deformation off its ball -/

/-- **The dent deformation is the identity outside its closed ball** (`χ` vanishes beyond
radius `1`). -/
theorem dentDeform_eq_self_of_le {χ : ℝ → ℝ} {centre d : R3} {r a' : ℝ}
    (hr : 0 < r) (hχ : ∀ t : ℝ, 1 ≤ t → χ t = 0) {z : R3} (hz : r ≤ ‖z - centre‖) :
    dentDeform χ centre d r a' z = z := by
  rw [dentDeform]
  have h1 : 1 ≤ ‖z - centre‖ / r := (one_le_div hr).mpr hz
  rw [hχ _ h1, mul_zero, zero_smul, add_zero]

/-! ## Transport along a homeomorphism of `ℝ³` -/

/-- **A homeomorphism of `ℝ³` commutes with `frontier`.** -/
theorem frontier_preimage_homeomorph (Φ : R3 ≃ₜ R3) (A : Set R3) :
    frontier (Φ ⁻¹' A) = Φ ⁻¹' frontier A := by
  rw [frontier, frontier, ← Φ.preimage_closure A, ← Φ.preimage_interior A, Set.preimage_sdiff]

/-- **The pullback of an embedded sphere under a homeomorphism of `ℝ³` is an embedded sphere.** -/
theorem isEmbeddedSphere_preimage (Φ : R3 ≃ₜ R3) {S : Set R3}
    (hS : Work.InnermostDisk.IsEmbeddedSphere S) :
    Work.InnermostDisk.IsEmbeddedSphere (Φ ⁻¹' S) := by
  obtain ⟨e, hinj, hrange⟩ := hS
  refine ⟨⟨fun x => Φ.symm (e x), Φ.continuous_symm.comp e.continuous⟩, ?_, ?_⟩
  · intro x y hxy
    exact hinj (Φ.symm.injective hxy)
  · ext z
    constructor
    · rintro ⟨x, hx⟩
      have hexS : e x ∈ S := by rw [← hrange]; exact ⟨x, rfl⟩
      rw [← hx]
      simpa using hexS
    · intro hz
      have hz' : Φ z ∈ Set.range e := by rw [hrange]; exact hz
      obtain ⟨x, hx⟩ := hz'
      refine ⟨x, ?_⟩
      show Φ.symm (e x) = z
      rw [hx, Φ.symm_apply_apply]

/-- **An embedded sphere is closed** (it is the image of a compact space under a continuous map). -/
theorem isClosed_of_isEmbeddedSphere {S : Set R3}
    (hS : Work.InnermostDisk.IsEmbeddedSphere S) : IsClosed S := by
  obtain ⟨e, -, hrange⟩ := hS
  rw [← hrange]
  exact (isCompact_range e.continuous).isClosed

/-- **A knot avoiding the ball of the dent meets a set and its preimage in the same parameters.** -/
theorem knot_inter_dentDeform_preimage {χ : ℝ → ℝ} {centre d : R3} {r a' : ℝ} (hr : 0 < r)
    (hχ : ∀ t : ℝ, 1 ≤ t → χ t = 0) {K : Knot}
    (havoid : ∀ t : ℝ, r ≤ ‖K.curve t - centre‖) (S : Set R3) :
    Set.range K.curve ∩ (dentDeform χ centre d r a' ⁻¹' S) = Set.range K.curve ∩ S := by
  ext z
  constructor
  · rintro ⟨hz, hzS⟩
    obtain ⟨t, rfl⟩ := hz
    rw [Set.mem_preimage, dentDeform_eq_self_of_le hr hχ (havoid t)] at hzS
    exact ⟨⟨t, rfl⟩, hzS⟩
  · rintro ⟨hz, hzS⟩
    obtain ⟨t, rfl⟩ := hz
    exact ⟨⟨t, rfl⟩, by rw [Set.mem_preimage, dentDeform_eq_self_of_le hr hχ (havoid t)]; exact hzS⟩

/-! ## Pardon's Lemma 2 at one embedded sphere -/

/-- **A set covered by finitely many carrier-disjoint closed pieces, none of which contains an
essential loop, contains no essential loop.**  (The connected compact image of a closed curve
contained in the union lies in one piece by `exists_subset_of_preconnected_iUnion`.) -/
theorem not_containsEssentialLoop_iUnion_of_carrier_disjoint {P : Work.CoreTopology.ParamTorus}
    {ι : Type} [Fintype ι] {F : ι → Set R3} (hclosed : ∀ i, IsClosed (F i))
    (hdisj : Pairwise fun i j => Disjoint (F i ∩ P.carrier) (F j ∩ P.carrier))
    (hno : ∀ i, ¬ P.ContainsEssentialLoop (F i)) :
    ¬ P.ContainsEssentialLoop (⋃ i, F i) := by
  rintro ⟨γ, hess, hγ⟩
  have hsub : Set.range γ.γ ⊆ ⋃ i : ι, (F i ∩ P.carrier) := by
    rintro x ⟨t, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hγ t)
    exact Set.mem_iUnion.mpr ⟨i, hi, γ.mem t⟩
  obtain ⟨i, hi⟩ := Work.InnermostDisk.exists_subset_of_preconnected_iUnion
    (isPreconnected_range γ.cont) ⟨γ.γ 0, ⟨0, rfl⟩⟩ (fun i => F i ∩ P.carrier)
    (fun i => (hclosed i).inter (Work.CoreTopology.isClosed_carrier P)) hdisj hsub
  exact hno i ⟨γ, hess, fun t => (hi ⟨t, rfl⟩).1⟩

/-- **Pardon's Lemma 2 for one embedded sphere.**  If `S` is an embedded sphere whose trace on the
surface is a compact `1`-manifold and whose knot count is below `min p q`, then `S` carries no
essential loop of the surface. -/
theorem not_containsEssentialLoop_of_isEmbeddedSphere
    {S : Set R3} (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) {ψ : Submission.Diffeo} {K : Knot}
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    (hsph : Work.InnermostDisk.IsEmbeddedSphere S)
    (hcomp : IsCompact (S ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier))
    (hloc : Work.Smooth.OneManifold.IsLocallyEuclidean
      (S ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier))
    (hcount : (Set.range K.curve ∩ S).encard < (Nat.min p q : ℕ∞)) :
    ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop S := by
  obtain ⟨n, cs, hsimple, hdisj, hcover⟩ :=
    Work.EpsW.exists_family_of_isCompact_of_isLocallyEuclidean
      (P := Work.Drive.EpsSphere.torusOf ψ)
      (Z := S ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)
      Set.inter_subset_right hcomp hloc
  obtain ⟨Sl⟩ := Work.InnermostDisk.sphereSlicing_of_isEmbeddedSphere_of_traceCurves hsph n cs
    hsimple hdisj hcover
  exact Work.EpsW.trace_inessential_of_slicing_of_countsWd p q hp hq hc ψ K himg Sl hcl hcount

/-! ## L4c -/

/-- **L4c: the trace of the deformed level carries no essential loop.**

Let `Ss` be a cover of the frontier of the *undeformed* level's removed set by pairwise disjoint
embedded spheres (`Work.Drive.Final.SphereCoverAt`, carried by `GoodSweepData3`), and let the level
count at `ℓ D.centre` be below `min p q`.  Assume the *pulled-back* spheres
`D.deform ⁻¹' Ss i` have compact and locally Euclidean trace on the surface (L4b), the traces of two
distinct pulled-back spheres on the surface are disjoint (which holds in particular if the `Ss i` are
pairwise disjoint as sets — note that the bundle's `SphereCoverAt` currently only provides
disjointness of the traces on the *undeformed* surface, which does **not** suffice here), and the dent
is small (`|a'| κ < r`, so `D.deform` is a homeomorphism).  Then no essential loop of the surface lies
in the frontier of the deformed removed set — so every curve of `DentOutResolved`'s family which
*lies on* that trace is inessential. -/
theorem dentOut_trace_noEssential_of_sphereCover
    {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : R3 →L[ℝ] ℝ} {U : Set R3} (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U) (ha' : |D.a'| * D.κ < D.r)
    {m : ℕ} {Ss : Fin m → Set R3}
    (hsph : ∀ i, Work.InnermostDisk.IsEmbeddedSphere (Ss i))
    (hdisj : ∀ i j : Fin m, i ≠ j → Disjoint ((D.deform ⁻¹' Ss i) ∩
      (Work.Drive.EpsSphere.torusOf ψ).carrier)
      ((D.deform ⁻¹' Ss j) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier))
    (hfront : frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) =
      ⋃ i, Ss i)
    (hcount : (Set.range K.curve ∩
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))).encard <
      (Nat.min p q : ℕ∞))
    (htame : ∀ i : Fin m,
      IsCompact ((D.deform ⁻¹' Ss i) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        ((D.deform ⁻¹' Ss i) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)) :
    ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop
        (frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))) := by
  classical
  obtain ⟨Φ, hΦ⟩ := dentDeform_homeomorph D.κ_pos D.r_pos (le_of_eq D.d_norm) D.χ_diff
    D.χ_deriv_bound ha'
  have hdeform : D.deform = ⇑Φ := by
    funext z
    exact (hΦ z).symm
  -- the frontier of the deformed removed set is the pulled-back sphere cover
  have hfront' : frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ
      (ℓ D.centre)) = ⋃ i, Φ ⁻¹' Ss i := by
    rw [hdeform, frontier_preimage_homeomorph, hfront, Set.preimage_iUnion]
  -- the count at the pulled-back spheres
  have hcount' : ∀ i : Fin m, (Set.range K.curve ∩ (Φ ⁻¹' Ss i)).encard < (Nat.min p q : ℕ∞) := by
    intro i
    have h1 : Set.range K.curve ∩ (Φ ⁻¹' Ss i) = Set.range K.curve ∩ Ss i := by
      rw [← hdeform]
      exact knot_inter_dentDeform_preimage D.r_pos D.χ_eq_zero D.knotAvoids (Ss i)
    rw [h1]
    refine lt_of_le_of_lt (Set.encard_le_encard (Set.inter_subset_inter_right _ ?_)) hcount
    rw [hfront]
    exact Set.subset_iUnion _ i
  -- the tameness of the pulled-back spheres
  have htame' : ∀ i : Fin m,
      IsCompact ((Φ ⁻¹' Ss i) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        ((Φ ⁻¹' Ss i) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) := by
    intro i
    rw [← hdeform]
    exact htame i
  -- no essential loop in any pulled-back sphere
  have hno : ∀ i : Fin m, ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop (Φ ⁻¹' Ss i) :=
    fun i => not_containsEssentialLoop_of_isEmbeddedSphere p q hp hq hc himg hcl
      (isEmbeddedSphere_preimage Φ (hsph i)) (htame' i).1 (htame' i).2 (hcount' i)
  rw [hfront']
  exact not_containsEssentialLoop_iUnion_of_carrier_disjoint
    (F := fun i => Φ ⁻¹' Ss i)
    (fun i => isClosed_of_isEmbeddedSphere (isEmbeddedSphere_preimage Φ (hsph i)))
    (fun i j hij => by
      rw [← hdeform]
      exact hdisj i j hij)
    hno


/-! ## A family of curves from a trace with no essential loop -/

/-- **A compact locally Euclidean trace with no essential loop is the union of the ranges of finitely
many pairwise disjoint simple inessential closed curves** of the surface.  This is
`Work.EpsW.exists_family_of_isCompact_of_isLocallyEuclidean` (which produces the family, simple and
pairwise disjoint) combined with the fact that a curve of the family, being a curve of `P` inside the
trace, cannot be essential. -/
theorem exists_family_of_not_containsEssentialLoop {P : Work.CoreTopology.ParamTorus}
    {Z : Set R3} (hZc : Z ⊆ P.carrier) (hcomp : IsCompact Z)
    (hloc : Work.Smooth.OneManifold.IsLocallyEuclidean Z)
    (hno : ¬ P.ContainsEssentialLoop Z) :
    ∃ (n : ℕ) (cs : Fin n → Work.CoreTopology.ClosedCurve P),
      (∀ i, Work.CoreTopology.IsSimple P (cs i)) ∧
      (∀ i, ¬ Work.CoreTopology.IsEssential P (cs i)) ∧
      (∀ i j : Fin n, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ)) ∧
      Z = ⋃ i, Set.range (cs i).γ := by
  obtain ⟨n, cs, hsimple, hdisj, hcover⟩ :=
    Work.EpsW.exists_family_of_isCompact_of_isLocallyEuclidean (P := P) hZc hcomp hloc
  refine ⟨n, cs, hsimple, ?_, hdisj, hcover⟩
  intro i hess
  exact hno ⟨cs i, hess, fun t => by rw [hcover]; exact Set.mem_iUnion.mpr ⟨i, ⟨t, rfl⟩⟩⟩


/-! ## L4b as a named residual -/

/-- **L4b, the one remaining input of the `(L)` package at an event**: the pulled-back spheres of the
sphere cover of the level's frontier have compact and locally Euclidean trace on the surface.

Note that this is *not* a consequence of the other bundle clauses: in the *core* of the dent the
trace is the regular level set `{ℓ = λ* − a' ℓ d}` and is a `1`-manifold, but in the *annulus* where
`0 < χ < 1` the trace is `carrier ∩ {ℓ ∘ D.deform = λ*}`, and the differential
`∇(ℓ ∘ D.deform)(z) = ∇ℓ(z) + β(z)(z − centre)` can be normal to the surface.  See
`AUDIT_pardon_unconditional.md` §31.6. -/
def DentOutTraceTame {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U) {m : ℕ} (Ss : Fin m → Set R3) : Prop :=
  ∀ i : Fin m,
    IsCompact ((D.deform ⁻¹' Ss i) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) ∧
    Work.Smooth.OneManifold.IsLocallyEuclidean
      ((D.deform ⁻¹' Ss i) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)


/-! ## The residual of the `(L)` package at an event, with the counting data included -/

/-- **The trace data of the `(L)` package at every event**: at each event there is a dent datum,
small enough that its ball is inessential (`D.r < 1/4`, so that any subset of the ball has vanishing
winding span by `Work.CoreTopology.not_containsEssentialLoop_closedBall_of_lt_one`), with a cover
`Ss` of the *undeformed* level frontier by embedded spheres whose **pulled-back traces on the surface
are pairwise disjoint** and **tame** (`Work.Drive.Final.DentOutTraceTame`, i.e. L4b).

The datum also carries `D.r < 1 / 4` (so that the ball of the dent is inessential) and
`|D.a'| κ < D.r` (so that `D.deform` is a homeomorphism, `Work.Drive.Final.dentDeform_homeomorph`).

The two genuinely geometric clauses are the *pullback disjointness* (see `AUDIT` §31.7: the bundle's
`SphereCoverAt` only gives disjointness of the traces on the undeformed surface, which does not
survive the pullback) and the tameness `DentOutTraceTame` (L4b, `AUDIT` §31.6).  Everything else of
the `(L)` package is proved: the inessentiality of the trace curves follows from the level count
(`Work.Drive.Final.exists_dentOut_trace_family`), the span `W Ω₁ = ⊥` from the gates and Pardon's
dichotomy (`Work.Drive.Final.windingSpan_dentOutRegion_eq_bot`), the genericity `hgen` from L6b
(`Work.Drive.Final.dentOut_hgen`), and the assembly from
`Work.Drive.Final.dentOutResolvedCond_of_families`. -/
def EventTraceData (ψ : Submission.Diffeo) (K : Knot) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (u : ℝ) (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) : Prop :=
  ∀ p : ℝ × ℝ, IsAnyEvent ψ s c σ u v h ℓ p → ∀ U : Set R3,
    U ∈ nhds (Work.BoxShrink.Pinch.par ψ p) →
    ∃ D : AnyDentDatum ψ K s c σ u v h R ℓ U, D.p = p ∧ D.r < 1 / 4 ∧
      |D.a'| * D.κ < D.r ∧
    ∃ (m : ℕ) (Ss : Fin m → Set R3),
      (∀ i, Work.InnermostDisk.IsEmbeddedSphere (Ss i)) ∧
      frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) = ⋃ i, Ss i ∧
      (∀ i j : Fin m, i ≠ j → Disjoint ((D.deform ⁻¹' Ss i) ∩
        (Work.Drive.EpsSphere.torusOf ψ).carrier)
        ((D.deform ⁻¹' Ss j) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)) ∧
      DentOutTraceTame D Ss

end

end Work.Drive.Final
