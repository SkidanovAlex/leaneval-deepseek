import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Final.dentOut_resolved
import Submission.Work.Drive.Final.mem_closure_dentOutRegion_of_mem_PBox_of_fderiv_ne
import Submission.Work.Topology.SphereSlicing.isOpen_PBox

/-!
# L6b: the union-form genericity at an event of the tilted sweep

(Project lead, `Final/NOTES_LEAD_L4_L1.md` §4, L6b; `AUDIT_pardon_unconditional.md` §30.7.)

The no-jump argument at the event level `lam* = ℓ D.centre` (`Work.Drive.Final.noJumpBelow_of_region`)
needs the *union-form genericity*: every point `z` of the surface in the closed box and the closed
slab at level `lam*` lies in `closure Ω₁` or in the union of the trace curves.

This module proves the geometric half of that statement:

* `Work.Drive.Final.dentOut_centre_mem` — the centre of the dent itself is an interior point of
  `Ω₁` as soon as the event is an `IsEvent` or an `IsFaceEvent` (at an `IsEvent` the level functional
  at the image of the centre is `lam* + a'·ℓ d > lam*`; the slab is preserved by the deformation, so
  the centre is strictly inside the removed set *and* its image);
* `Work.Drive.Final.dentOut_hgen_of_goodData3` — the genericity clause: such a `z` is either in
  `closure Ω₁`, or it lies on the box sphere (`boxNorm c σ z = s`), in which case it is covered by the
  box-sphere trace curves which L6b adjoins to the family (`SphereCoverAt`'s sphere `{boxNorm = s}`,
  see `AUDIT` §30.7 item 1).

The proof of the genericity clause is the pointwise core
`Work.Drive.Final.mem_closure_dentOutRegion_of_mem_PBox_of_fderiv_ne`: a level point of the surface
in the *open* box at which the sweep height is regular lies in `closure Ω₁`.  The only points left
are those where the sweep height is critical: they are `IsEvent`s, and the clause "one event per
level" of `GoodSweepData3` identifies them with the event point of the dent, which is in `Ω₁` (or, in
the corner case, on the box sphere).
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped Topology

namespace Work.Drive.Final

noncomputable section

variable {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)}
  {ℓ : R3 →L[ℝ] ℝ} {U : Set R3} {exc : Finset ℝ} {lam0 lam1 : ℝ}

/-- The deformation of a dent is continuous. -/
theorem continuous_anyDentDatum_deform (D : AnyDentDatum ψ K s c σ u v h R ℓ U) :
    Continuous D.deform := by
  have h1 : Continuous fun z : R3 => D.χ (‖z - D.centre‖ / D.r) :=
    D.χ_cont.comp ((continuous_norm.comp (continuous_id.sub continuous_const)).div_const D.r)
  unfold AnyDentDatum.deform dentDeform
  exact continuous_id.add ((continuous_const.mul h1).smul continuous_const)

/-- **The centre of the dent is an interior point of `Ω₁`** when the event is an `IsEvent` or an
`IsFaceEvent`.

At the centre the deformation is the translation by `a' • d` (the cutoff equals `1` there), so the
image of the centre has level `lam* + a'·ℓ d > lam*` while lying in the box (the box is preserved
near the centre, `box_pres`) and on the same side of the slab (`d ⟂ v`).  Hence the image is an
*interior* point of the removed set, and its preimage — the centre — is an interior point of the
preimage of the removed set. -/
theorem dentOut_centre_mem (D : AnyDentDatum ψ K s c σ u v h R ℓ U)
    (hev : IsEvent ψ s c σ u v h ℓ D.p ∨ IsFaceEvent ψ s c σ u v h ℓ D.p) :
    D.centre ∈ dentOutRegion ψ s c σ u v h R ℓ D := by
  have hbox : D.centre ∈ Submission.PBox s c σ := by
    rw [D.centre_eq]
    rcases hev with hev | hev
    · exact hev.1
    · exact hev.1
  -- the image of the centre is in the box, and strictly above the level
  have hψbox : D.deform D.centre ∈ Submission.PBox s c σ := by
    have hbp := (D.box_pres D.centre (by simp [sub_self, norm_zero, le_of_lt D.r_pos])).mp hbox
    simpa only [AnyDentDatum.deform] using hbp
  have hlevel : ℓ D.centre < ℓ (D.deform D.centre) := by
    have h1 : ℓ (D.deform D.centre) =
        ℓ D.centre + (D.a' * D.χ 0) * ℓ D.d := by
      simp only [AnyDentDatum.deform, dentDeform, D.centre_eq, sub_self, norm_zero, zero_div,
        D.χ_zero_apply, mul_one]
      rw [map_add, map_smul, smul_eq_mul]
    rw [h1, D.χ_zero_apply, mul_one]
    have := mul_pos D.a'_pos D.push_pos
    linarith
  -- the removed set contains a neighbourhood of the image of the centre
  have hRsub : Submission.PBox s c σ ∩ {y : R3 | ℓ D.centre < ℓ y} ⊆
      Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre) := by
    rintro y ⟨hy1, hy2⟩
    refine ⟨hy1, fun hc => ?_⟩
    have hlt : ℓ y < ℓ D.centre := hc.2
    exact absurd hlt (not_lt.mpr (le_of_lt hy2))
  have hmem : D.deform D.centre ∈ interior
      (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) :=
    interior_maximal hRsub
      (Work.Topology.SphereSlicing.isOpen_PBox s c σ |>.inter
        (isOpen_lt continuous_const ℓ.continuous)) ⟨hψbox, hlevel⟩
  -- pull back to the preimage
  have hpre : D.centre ∈ interior (D.deform ⁻¹'
      Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) := by
    refine interior_maximal (Set.preimage_mono interior_subset)
      (isOpen_interior.preimage (continuous_anyDentDatum_deform D)) ?_
    exact hmem
  exact ⟨by rw [D.centre_eq]; exact Work.BoxShrink.Pinch.par_mem_carrier ψ D.p, hpre⟩

/-- **L6b, the geometric form.**  At a `GoodSweepData3` datum and any `AnyDentDatum`, every point of
the surface in the closed box, in the closed slab and on the level `ℓ D.centre` lies in
`closure Ω₁` or on the box sphere. -/
theorem dentOut_hgen_geometric
    (hG : GoodSweepData3 ψ K s c σ u v h R ℓ exc lam0 lam1)
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U)
    {z : R3} (hzc : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzbox : z ∈ closure (Submission.PBox s c σ))
    (hzslab : |slabFn c u v z| ≤ h) (hzℓ : ℓ z = ℓ D.centre) :
    z ∈ closure (dentOutRegion ψ s c σ u v h R ℓ D) ∨ Submission.boxNorm c σ z = s := by
  classical
  by_cases hboxsph : Submission.boxNorm c σ z = s
  · exact Or.inr hboxsph
  -- `z` is in the open box
  have hcoord : ∀ i : Fin 3, |z (σ i) - c (σ i)| / Submission.boxSide i ≤ s := by
    intro i
    rw [div_le_iff₀ (Submission.boxSide_pos i)]
    simpa [mul_comm] using Work.Drive.Final.abs_coord_le_of_mem_closure_PBox hzbox i
  have hboxnorm_le : Submission.boxNorm c σ z ≤ s := by
    rw [Submission.boxNorm]
    exact max_le (max_le (hcoord 0) (hcoord 1)) (hcoord 2)
  have hzPBox : z ∈ Submission.PBox s c σ :=
    (Submission.mem_PBox_iff s c σ z).mpr (lt_of_le_of_ne hboxnorm_le hboxsph)
  -- a parameter of `z`
  obtain ⟨pp, hpp⟩ : ∃ q : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ q = z := by
    obtain ⟨x, y, hxy⟩ := (Work.CoreTopology.ParamTorus.mem_carrier_iff _ z).mp hzc
    exact ⟨(x, y), hxy⟩
  by_cases hder : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) pp = 0
  · -- `pp` is an event; "one event per level" identifies it with the event of the dent
    obtain ⟨-, -, -, -, -, -, -, -, hone, -⟩ := hG
    have hppEv : IsAnyEvent ψ s c σ u v h ℓ pp := by
      refine Or.inl ⟨?_, ?_, hder⟩
      · rw [hpp]; exact hzPBox
      · simpa [Work.Drive.EpsForm.tiltedSlabClosed, slabFn_apply, hpp] using hzslab
    have hlevel : ℓ (Work.BoxShrink.Pinch.par ψ pp) = ℓ (Work.BoxShrink.Pinch.par ψ D.p) := by
      rw [hpp, hzℓ, D.centre_eq]
    have huniq := hone pp D.p hppEv D.isEvent hlevel
    have hzcentre : z = D.centre := by rw [← hpp, huniq, D.centre_eq]
    rcases D.isEvent with hev | hev | hev
    · -- an interior event: the centre is in `Ω₁` outright
      rw [hzcentre]
      exact Or.inl (subset_closure (dentOut_centre_mem D (Or.inl hev)))
    · rw [hzcentre]
      exact Or.inl (subset_closure (dentOut_centre_mem D (Or.inr hev)))
    · -- a corner event: the centre is on the box sphere
      exact absurd (hboxsph (by rw [hzcentre, D.centre_eq]; exact hev.2.1)) (not_false)
  · exact Or.inl (Work.Drive.Final.mem_closure_dentOutRegion_of_mem_PBox_of_fderiv_ne D hzc hzPBox
      hzℓ hpp hder)


/-! ## The box-sphere trace family, from `TransverseSphere` and the counting -/

/-- **The transverse-sphere family of the box sphere, with the inessentiality of the counting.**
`Work.Topology.SphereSlicing.TransverseSphere P S` (a clause of `Work.Drive.Mono.BoxGen`, hence of
`GoodSweepData2` and of the bundle) already gives a family of pairwise disjoint simple curves of `P`
lying on `S` and covering `S ∩ P.carrier`.  If moreover `S` carries no essential loop of `P` (for the
box sphere: `Work.EpsW.sphereTrace_inessential_of_countsWd`, from the crux's count `hS`), then each
curve of the family is *inessential* — which is what the no-jump argument consumes. -/
theorem exists_family_of_transverseSphere_of_not_containsEssentialLoop
    {P : Work.CoreTopology.ParamTorus} {S : Set R3}
    (htrans : Work.Topology.SphereSlicing.TransverseSphere P S)
    (hno : ¬ P.ContainsEssentialLoop S) :
    ∃ (ι : Type) (_ : Fintype ι) (cs : ι → Work.CoreTopology.ClosedCurve P),
      (∀ i, Work.CoreTopology.IsSimple P (cs i)) ∧
      (∀ i, ¬ Work.CoreTopology.IsEssential P (cs i)) ∧
      (Pairwise fun i j => Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ)) ∧
      (∀ (i : ι) (t : ℝ), (cs i).γ t ∈ S) ∧
      (∀ z : R3, z ∈ S → z ∈ P.carrier → ∃ i : ι, z ∈ Set.range (cs i).γ) := by
  obtain ⟨ι, hfin, cs, hsimple, hdisj, hmem, hcov⟩ := htrans
  refine ⟨ι, hfin, cs, hsimple, ?_, hdisj, hmem, hcov⟩
  intro i hess
  exact hno ⟨cs i, hess, fun t => hmem i t⟩

/-- **L6b in the form the no-jump argument consumes**: a level point of the surface in the closed box
lies in `closure Ω₁` or on the box sphere, and the box-sphere points are covered by any family which
covers the box sphere. -/
theorem dentOut_hgen
    (hG : GoodSweepData3 ψ K s c σ u v h R ℓ exc lam0 lam1)
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U)
    {ι : Type} {cs : ι → Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ)}
    (hboxcover : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      Submission.boxNorm c σ z = s → ∃ i : ι, z ∈ Set.range (cs i).γ)
    {z : R3} (hzc : z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hzbox : z ∈ closure (Submission.PBox s c σ))
    (hzslab : |slabFn c u v z| ≤ h) (hzℓ : ℓ z = ℓ D.centre) :
    z ∈ closure (dentOutRegion ψ s c σ u v h R ℓ D) ∪ ⋃ i, Set.range (cs i).γ := by
  rcases dentOut_hgen_geometric hG D hzc hzbox hzslab hzℓ with h | h
  · exact Or.inl h
  · obtain ⟨i, hi⟩ := hboxcover z hzc h
    exact Or.inr (Set.mem_iUnion.mpr ⟨i, hi⟩)


/-! ## The box-sphere family at a crux configuration -/

/-- **The box-sphere trace family at a crux configuration.**  From `BoxGen`'s transversality of the
box sphere (`Work.Topology.SphereSlicing.TransverseSphere`), Pardon's Lemma 2 at the box sphere
(`Work.EpsW.sphereTrace_inessential_of_countsWd`, using the crux's box count `hS`) produces a family of
pairwise disjoint simple **inessential** curves of the surface lying on the box sphere and covering
its trace.  This is the family which L6b adjoins to the trace curves of the deformed level. -/
theorem exists_family_of_boxSphere
    {ψ : Submission.Diffeo} {K : Knot} {s : ℝ} (hs : 0 < s) {c : R3} {σ : Equiv.Perm (Fin 3)}
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ)) {d : ℝ} (hd : 0 ≤ d)
    (hbound : Work.Sweep.IsDistortionBound K d)
    (hsmall : Submission.countConst * d < (Nat.min p q : ℝ))
    (hslice : Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
      {y : R3 | Submission.boxNorm c σ y = s})
    (hS : ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
      ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)))
    (htrans : Work.Topology.SphereSlicing.TransverseSphere (Work.Drive.EpsSphere.torusOf ψ)
      {y : R3 | Submission.boxNorm c σ y = s}) :
    ∃ (n : ℕ) (cs : Fin n → Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ)),
      (∀ i, Work.CoreTopology.IsSimple (Work.Drive.EpsSphere.torusOf ψ) (cs i)) ∧
      (∀ i, ¬ Work.CoreTopology.IsEssential (Work.Drive.EpsSphere.torusOf ψ) (cs i)) ∧
      (∀ i j : Fin n, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ)) ∧
      (∀ (i : Fin n) (t : ℝ), (cs i).γ t ∈
        {y : R3 | Submission.boxNorm c σ y = s}) ∧
      (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
        Submission.boxNorm c σ z = s → ∃ (i : Fin n) (t : ℝ), (cs i).γ t = z) := by
  have hno : ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop
      (Work.BoxShrink.Core.sphereSet c σ s) :=
    Work.EpsW.sphereTrace_inessential_of_countsWd p q hp hq hc ψ K hd himg hsmall hs c σ hslice hcl
      (by simpa only [Work.BoxShrink.Core.sphereSet, Set.mem_ofPred_eq] using hS)
  obtain ⟨ι, hfin, cs, hsimple, hess, hdisj, hmem, hcov⟩ :=
    exists_family_of_transverseSphere_of_not_containsEssentialLoop htrans hno
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun k => cs (e.symm k), ?_, ?_, ?_, ?_, ?_⟩
  · intro k; exact hsimple _
  · intro k; exact hess _
  · intro k l hkl
    exact hdisj (fun h => hkl (e.symm.injective h))
  · intro k t; exact hmem _ t
  · intro z hz hzs
    obtain ⟨i, hi⟩ := hcov z hzs hz
    obtain ⟨t, ht⟩ := hi
    exact ⟨e i, t, by simpa using ht⟩

end

end Work.Drive.Final
