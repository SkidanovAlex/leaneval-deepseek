import Submission.Work.Topology.SphereSlicing.Defs
import Submission.Work.Topology.SphereSlicing.Slice.Base
import Submission.Work.Topology.SphereSlicing.Slice.Reduce
import Submission.Work.Topology.SphereSlicing.cleansDiscs_of_cleanOneCurve
import Submission.Work.Topology.SphereSlicing.frontier_PBox
import Submission.Work.Topology.SphereSlicing.isEmbeddedSphere_BoxSphere
import Submission.Work.Topology.SphereSlicing.encard_range_inter_le_encard_param
import Submission.Work.Topology.SphereSlicing.Transport
import Submission.Work.CoreTopology.IntersectionNumberDiffeomorphic

/-!
# Assembly: Pardon's Lemma 4.2 at the boundary of Pardon's box

This is the file a caller should import.  It combines

* the classical slicing datum `Work.Topology.SphereSlicing.SliceData P S`, whose reduction to
  Pardon's `Work.InnermostDisk.SphereSlicing P S` is proved in
  `Work.Topology.SphereSlicing.Slice.Reduce`;
* the single cut-and-paste `Work.Topology.SphereSlicing.CleanOneCurve P`, whose reduction to
  `Work.InnermostDisk.CleansDiscs P` is proved in `Work.Topology.SphereSlicing.Clean.Reduce`
  and `cleansDiscs_of_cleanOneCurve`;
* the explicit homeomorphism `∂PBox s c σ ≃ₜ S²` and the resulting `IsEmbeddedSphere` of the box
  boundary (`homeomorph_BoxSphere`, `isEmbeddedSphere_BoxSphere`);
* the two classical *inputs* `SliceInput P` and `ClassicalInput P`, which package those data as
  hypotheses over all spheres in general position;

and delivers Pardon's Lemma 4.2 — a sphere meeting the curve `β` in fewer than `I(F, β)` points
contains no essential loop of the torus — in the following forms, in decreasing order of how much
of the classical input they demand:

* `Work.Topology.SphereSlicing.mustbeinessential_of_sliceData` — from the slicing datum
  `SliceData P S` at the *given* sphere and the cut-and-paste.  This is the sharpest form: nothing
  is assumed about spheres other than `S`, and `S` need not even be an embedded sphere;
* `Work.Topology.SphereSlicing.mustbeinessential_of_classicalInput` — from the global classical
  inputs `SliceInput P` and `CleanOneCurve P` plus transversality of `S`;
* `Work.Topology.SphereSlicing.mustbeinessential_BoxSphere` — the same at the boundary
  `∂PBox s c σ = BoxSphere s c σ` of Pardon's box;
* `Work.Topology.SphereSlicing.mustbeinessentialBox_of_classicalInput` — the same for the tori of
  the challenge, `F = ψ(F_standard)` and `β = ψ((p,q)-curve)`, with `I(F, β) = min p q` supplied
  unconditionally by `Work.CoreTopology.pardonsI_standard_mapHomeomorph` and with the intersection
  count taken in the *parameter* form `# {t ∈ [0, 2π) | boxNorm c σ (K.curve t) = s}` in which
  Pardon's sweep produces it.  This is the statement that `Work.BoxBubble.mustbeinessentialBox`
  needs, up to two hypotheses: the classical input at `ψ(F_standard)` and the transversality of
  the box boundary with it;
* `Work.Topology.SphereSlicing.mustbeinessentialBox_of_classicalInput_standard` — the same with the
  classical input in its normal form `ClassicalInput standard`, since the classical input is
  invariant under ambient homeomorphisms (`classicalInput_map_homeomorph_iff`).  A verbatim copy of
  the statement of `Work.BoxBubble.mustbeinessentialBox` is discharged by this theorem after adding
  exactly the two hypotheses above;
* `Work.Topology.SphereSlicing.mustbeinessentialBox_of_meetingAtMost` — the same from Pardon's
  strong `hclean` form `Work.InnermostDisk.CleansInSphereMeetingAtMost`.

The `ContainsEssentialLoop` forms (`not_containsEssentialLoop_BoxSphere`,
`le_pardonsI_of_containsEssentialLoop_BoxSphere`) are the vocabulary in which the sweep and the
double bubble of Pardon's argument read Pardon's Lemma off; the contrapositive
`le_pardonsI_of_containsEssentialLoop_BoxSphere` is the counting step itself.  For users of the
existing `Work.InnermostDisk` chapter, `Work.Topology.SphereSlicing.GeneralPosition` contains the
repaired global inputs (`SphereSlicingInputOnGeneralPosition`, `PardonPLInputOnGeneralPosition`) —
the originals quantify over all embedded spheres, which is too much.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology
open Work.InnermostDisk

namespace Work.Topology.SphereSlicing

noncomputable section

/-! ## Counting intersections through a parameter set -/

/-- The range of a `2π`-periodic map is the image of the fundamental interval `[0, 2π)` (the
general form, for an arbitrary periodic curve rather than a `ClosedCurve`, needed to count the
intersections of a knot curve with a box boundary through its parameter set). -/
theorem range_periodic_eq_image_Ico {f : ℝ → R3} (hf : Function.Periodic f (2 * Real.pi)) :
    Set.range f = f '' Set.Ico 0 (2 * Real.pi) := by
  refine Set.Subset.antisymm ?_ (Set.image_subset_range _ _)
  rintro y ⟨t, rfl⟩
  obtain ⟨k, hk, -⟩ := existsUnique_sub_zsmul_mem_Ico (a := 2 * Real.pi) (by positivity) t 0
  refine ⟨t - k • (2 * Real.pi), by simpa using hk, ?_⟩
  conv_rhs => rw [← sub_add_cancel t (k • (2 * Real.pi))]
  exact (Function.Periodic.zsmul hf k (t - k • (2 * Real.pi))).symm

/-- **Counting intersections through the parameter set.**  For a `2π`-periodic curve `f`, the
number of points of `range f ∩ T` is at most the number of parameters `t ∈ [0, 2π)` with
`f t ∈ T`.  This is how the intersection count `#(β ∩ ∂PBox)` produced by Pardon's sweep, which
is a count of parameters, bounds the cardinality `#(range β ∩ ∂PBox)` used by Pardon's Lemma. -/
theorem encard_range_inter_le_encard_param_of_periodic {f : ℝ → R3}
    (hf : Function.Periodic f (2 * Real.pi)) (T : Set R3) :
    Set.encard (Set.range f ∩ T) ≤
      Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ f t ∈ T} := by
  have hS : Set.range f ∩ T = f '' (Set.Ico 0 (2 * Real.pi) ∩ f ⁻¹' T) := by
    rw [range_periodic_eq_image_Ico hf]
    ext y
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hyT⟩
      exact ⟨t, ⟨ht, hyT⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hyT⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩, hyT⟩
  rw [hS]
  exact Set.encard_image_le f (Set.Ico 0 (2 * Real.pi) ∩ f ⁻¹' T)

/-! ## Pardon's Lemma from the slicing datum at the given sphere -/

/-- The two innermost-disc inputs combine: the slicing datum at `S` gives Pardon's first input
(`InnermostDiscInput`), and the single cut-and-paste gives the second (`CleansDiscs`). -/
theorem cleansInSphere_of_sliceData {P : ParamTorus} {S : Set R3} (h : SliceData P S)
    (hCl : CleanOneCurve P) : CleansInSphere P S :=
  cleansInSphere_of_inputs (innermostDiscInput_of_sliceData h) (cleansDiscs_of_cleanOneCurve hCl)

/-- **Pardon's Lemma 4.2 from the slicing datum at `S`.**  If `S` is sliced by `F` (`SliceData`),
if a single cut-and-paste is available (`CleanOneCurve`), and if `S` meets `β` in fewer than
`I(F, β)` points, then every closed curve of `F` whose image lies in `S` is inessential in `F`.

Nothing is assumed about spheres other than `S`; in particular `S` need not be an embedded sphere,
only sliced by `F`. -/
theorem mustbeinessential_of_sliceData (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    (h : SliceData P S) (hCl : CleanOneCurve P)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α :=
  mustbeinessential_of_inputs P β S (innermostDiscInput_of_sliceData h)
    (cleansDiscs_of_cleanOneCurve hCl) hSβ

/-- **Pardon's Lemma 4.2 from the slicing datum at `S`, in the "no essential loop" form.** -/
theorem not_containsEssentialLoop_of_sliceData (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    (h : SliceData P S) (hCl : CleanOneCurve P)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) :
    ¬ P.ContainsEssentialLoop S :=
  fun ⟨γ, hess, hmem⟩ => mustbeinessential_of_sliceData P β S h hCl hSβ γ hmem hess

/-- **The contrapositive**, unconditional in the slicing datum: if such a sphere contains an
essential loop of `F`, then it meets `β` in at least `I(F, β)` points. -/
theorem le_pardonsI_of_containsEssentialLoop_of_sliceData (P : ParamTorus) (β : ClosedCurve P)
    (S : Set R3) (h : SliceData P S) (hCl : CleanOneCurve P)
    (hU : P.ContainsEssentialLoop S) :
    pardonsI P β ≤ Set.encard (Set.range β.γ ∩ S) :=
  le_of_not_gt fun hlt => not_containsEssentialLoop_of_sliceData P β S h hCl hlt hU

/-- **Pardon's Lemma 4.2 in Pardon's own component form**, from the slicing datum at `S`: if the
finitely many curves `c i` of `F` all lie in `S` and `S` meets `β` in fewer than `I(F, β)` points,
then each of them is inessential in `F` ("every curve in `S ∩ F` is inessential in `F`"). -/
theorem not_isEssential_components_of_sliceData (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    {ι : Type} [Fintype ι] (c : ι → ClosedCurve P) (h : SliceData P S) (hCl : CleanOneCurve P)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β)
    (hcS : ∀ i : ι, ∀ t : ℝ, (c i).γ t ∈ S) : ∀ i : ι, ¬ IsEssential P (c i) :=
  fun i => mustbeinessential_of_sliceData P β S h hCl hSβ (c i) (hcS i)

/-! ## Pardon's Lemma from the global classical input -/

/-- **Pardon's Lemma 4.2 from the global classical input.**  Here `SliceInput P` slices every
embedded sphere *in general position with respect to `F`*, so the sphere `S` of the statement is
required to be in general position as well (`hT`). -/
theorem mustbeinessential_of_classicalInput (P : ParamTorus) (β : ClosedCurve P) (S : Set R3)
    (hS : IsEmbeddedSphere S) (hT : TransverseSphere P S) (h : ClassicalInput P)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α :=
  mustbeinessential_of_sliceData P β S (h.1 S hS hT).some h.2 hSβ

/-- The same, in the "no essential loop" form. -/
theorem not_containsEssentialLoop_of_classicalInput (P : ParamTorus) (β : ClosedCurve P)
    (S : Set R3) (hS : IsEmbeddedSphere S) (hT : TransverseSphere P S) (h : ClassicalInput P)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) :
    ¬ P.ContainsEssentialLoop S :=
  not_containsEssentialLoop_of_sliceData P β S (h.1 S hS hT).some h.2 hSβ

/-! ## The box boundary -/

/-- **Pardon's Lemma 4.2 at the boundary of Pardon's box**, from the slicing datum at that sphere.
The box boundary `∂PBox s c σ = BoxSphere s c σ` is a genuine embedded `S²`
(`isEmbeddedSphere_BoxSphere`), so it is exactly the kind of sphere Pardon's Lemma is about; but
the statement below needs only `SliceData P (BoxSphere s c σ)`, which is where the transversality
of the box with `F` and the Jordan–Schoenflies content live. -/
theorem mustbeinessential_BoxSphere (P : ParamTorus) (β : ClosedCurve P) {s : ℝ} (hs : 0 < s)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (h : SliceData P (BoxSphere s c σ))
    (hCl : CleanOneCurve P)
    (hβ : Set.encard (Set.range β.γ ∩ BoxSphere s c σ) < pardonsI P β) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ BoxSphere s c σ) → ¬ IsEssential P α :=
  mustbeinessential_of_sliceData P β (BoxSphere s c σ) h hCl hβ

/-- **Pardon's Lemma 4.2 at the box boundary, in the "no essential loop" form** — the form the
double bubble of Pardon's argument consumes. -/
theorem not_containsEssentialLoop_BoxSphere_data (P : ParamTorus) (β : ClosedCurve P) {s : ℝ}
    (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3)) (h : SliceData P (BoxSphere s c σ))
    (hCl : CleanOneCurve P)
    (hβ : Set.encard (Set.range β.γ ∩ BoxSphere s c σ) < pardonsI P β) :
    ¬ P.ContainsEssentialLoop (BoxSphere s c σ) :=
  not_containsEssentialLoop_of_sliceData P β (BoxSphere s c σ) h hCl hβ

/-- **The contrapositive at the box boundary**: a box boundary containing an essential loop of the
torus meets `β` in at least `I(F, β)` points.  This is the counting step of Pardon's argument. -/
theorem le_pardonsI_of_containsEssentialLoop_BoxSphere (P : ParamTorus) (β : ClosedCurve P)
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (h : SliceData P (BoxSphere s c σ)) (hCl : CleanOneCurve P)
    (hU : P.ContainsEssentialLoop (BoxSphere s c σ)) :
    pardonsI P β ≤ Set.encard (Set.range β.γ ∩ BoxSphere s c σ) :=
  le_of_not_gt fun hlt => not_containsEssentialLoop_BoxSphere_data P β hs c σ h hCl hlt hU

/-- **Pardon's Lemma 4.2 at the box boundary, from the global classical input** (the slicing
hypothesis is discharged through `SliceInput` at the box boundary, which needs the box boundary to
be in general position with respect to `F`). -/
theorem mustbeinessential_BoxSphere_of_classicalInput (P : ParamTorus) (β : ClosedCurve P)
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hT : TransverseSphere P (BoxSphere s c σ)) (h : ClassicalInput P)
    (hβ : Set.encard (Set.range β.γ ∩ BoxSphere s c σ) < pardonsI P β) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ BoxSphere s c σ) → ¬ IsEssential P α :=
  mustbeinessential_of_classicalInput P β (BoxSphere s c σ)
    (isEmbeddedSphere_BoxSphere hs c σ) hT h hβ

/-- **The slicing of the box boundary**, from the slicing input and transversality. -/
theorem nonempty_sphereSlicing_BoxSphere {P : ParamTorus} (h : SliceInput P) {s : ℝ} (hs : 0 < s)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (hT : TransverseSphere P (BoxSphere s c σ)) :
    Nonempty (SphereSlicing P (BoxSphere s c σ)) :=
  nonempty_sphereSlicing_of_sliceInput h (isEmbeddedSphere_BoxSphere hs c σ) hT

/-- **Pardon's first innermost input at the box boundary**, from the slicing input and
transversality. -/
theorem innermostDiscInput_BoxSphere {P : ParamTorus} (h : SliceInput P) {s : ℝ} (hs : 0 < s)
    (c : R3) (σ : Equiv.Perm (Fin 3)) (hT : TransverseSphere P (BoxSphere s c σ)) :
    InnermostDiscInput P (BoxSphere s c σ) :=
  innermostDiscInput_of_sliceInput h (isEmbeddedSphere_BoxSphere hs c σ) hT

/-! ## The `hclean` form, through `Work.CoreTopology.mustbeinessential` -/

/-- **Pardon's Lemma 4.2 at the box boundary through `Work.CoreTopology.mustbeinessential`**, from
the *strong* form of the cleaning hypothesis `Work.InnermostDisk.CleansInSphereMeetingAtMost`
(which is exactly the `hclean` of that theorem, see
`Work.InnermostDisk.hclean_of_cleansInSphereMeetingAtMost`).  This is the form requested for a
formalizer who establishes the comparison of intersection counts with `β`; the weaker
`CleansInSphere` form of this chapter is what Pardon's argument actually produces. -/
theorem mustbeinessential_BoxSphere_meetingAtMost (P : ParamTorus) (β : ClosedCurve P) {s : ℝ}
    (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (h : CleansInSphereMeetingAtMost P β (BoxSphere s c σ))
    (hβ : Set.encard (Set.range β.γ ∩ BoxSphere s c σ) < pardonsI P β) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ BoxSphere s c σ) → ¬ IsEssential P α :=
  mustbeinessential_via_core P β (BoxSphere s c σ) h hβ

/-! ## The box-specific forms of the innermost input, and the box far from the surface -/

/-- **Pardon's first innermost input at the box boundary, from a slicing datum at it.** -/
theorem innermostDiscInput_BoxSphere_of_sliceData {P : ParamTorus} {s : ℝ} (c : R3)
    (σ : Equiv.Perm (Fin 3)) (h : SliceData P (BoxSphere s c σ)) :
    InnermostDiscInput P (BoxSphere s c σ) :=
  innermostDiscInput_of_sliceData h

/-- The cutting-and-pasting step at the box boundary. -/
theorem cleansInSphere_BoxSphere_of_sliceData {P : ParamTorus} {s : ℝ} (c : R3)
    (σ : Equiv.Perm (Fin 3)) (h : SliceData P (BoxSphere s c σ)) (hCl : CleanOneCurve P) :
    CleansInSphere P (BoxSphere s c σ) :=
  cleansInSphere_of_sliceData h hCl

/-- **A box that does not meet the surface: no essential loop on its boundary** — unconditionally,
with no classical input and no transversality hypothesis.  (`BoxSphere s c σ = frontier (PBox s c σ)`
for `0 < s`, so it suffices that the *closed* box avoids `F`.) -/
theorem not_containsEssentialLoop_BoxSphere_of_disjoint {P : ParamTorus} {s : ℝ} (hs : 0 < s)
    (c : R3) (σ : Equiv.Perm (Fin 3))
    (h : ∀ y : R3, y ∈ closure (Submission.PBox s c σ) → y ∉ P.carrier) :
    ¬ P.ContainsEssentialLoop (BoxSphere s c σ) := by
  refine not_containsEssentialLoop_of_disjoint fun x hx hxc => h x ?_ hxc
  exact frontier_subset_closure (by rw [frontier_PBox hs c σ]; exact hx)

/-! ## The form needed by `Work.BoxBubble.mustbeinessentialBox` -/

/-- **Pardon's Lemma 4.2 at the box boundary for the tori of the challenge**, with the
intersection count in the parameter form produced by Pardon's sweep.

Let `ψ` be a homeomorphism of `ℝ³`, `F = ψ(F_standard)` the image of the standard torus,
`β = ψ(β_{p,q})` the image of the standard `(p,q)`-curve (with `p, q > 0` coprime, so that
`I(F, β) = min p q`), and `K` a knot whose image is that of `β`.  If the box boundary
`∂PBox s c σ` meets `K` — counted through the parameters `t ∈ [0, 2π)` of `K.curve` — in strictly
fewer than `min p q` points, then it contains no essential loop of `F`.

The hypotheses are the slicing datum at the box boundary (transversality of the box with `F` and
the Jordan–Schoenflies content) and the single cut-and-paste.  This is the statement that
`Work.BoxBubble.mustbeinessentialBox` needs. -/
theorem mustbeinessentialBox_of_sliceData (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : R3 ≃ₜ R3) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (ClosedCurve.mapHomeomorph ψ (standardCurve p q)).γ)
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (h : SliceData (ParamTorus.mapHomeomorph ψ) (BoxSphere s c σ))
    (hCl : CleanOneCurve (ParamTorus.mapHomeomorph ψ))
    (hcount : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} < (Nat.min p q : ℕ∞)) :
    ¬ (ParamTorus.mapHomeomorph ψ).ContainsEssentialLoop (BoxSphere s c σ) := by
  refine not_containsEssentialLoop_BoxSphere_data (ParamTorus.mapHomeomorph ψ)
    (ClosedCurve.mapHomeomorph ψ (standardCurve p q)) hs c σ h hCl ?_
  rw [pardonsI_standard_mapHomeomorph p q hp hq hc ψ]
  refine lt_of_le_of_lt ?_ hcount
  calc Set.encard (Set.range (ClosedCurve.mapHomeomorph ψ (standardCurve p q)).γ ∩
        BoxSphere s c σ)
      = Set.encard (Set.range K.curve ∩ BoxSphere s c σ) := by rw [← himg]
    _ ≤ Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ BoxSphere s c σ} :=
        encard_range_inter_le_encard_param_of_periodic K.periodic (BoxSphere s c σ)
    _ = Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
          Submission.boxNorm c σ (K.curve t) = s} :=
        congrArg Set.encard (by
          ext t
          simp only [Set.mem_setOf_eq, mem_BoxSphere])

/-- **The form needed by `Work.BoxBubble.mustbeinessentialBox`, from the global classical input
and transversality of the box boundary.** -/
theorem mustbeinessentialBox_of_classicalInput (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : R3 ≃ₜ R3) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (ClosedCurve.mapHomeomorph ψ (standardCurve p q)).γ)
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hT : TransverseSphere (ParamTorus.mapHomeomorph ψ) (BoxSphere s c σ))
    (h : ClassicalInput (ParamTorus.mapHomeomorph ψ))
    (hcount : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} < (Nat.min p q : ℕ∞)) :
    ¬ (ParamTorus.mapHomeomorph ψ).ContainsEssentialLoop (BoxSphere s c σ) :=
  mustbeinessentialBox_of_sliceData p q hp hq hc ψ K himg hs c σ
    (h.1 (BoxSphere s c σ) (isEmbeddedSphere_BoxSphere hs c σ) hT).some h.2 hcount

/-- **The form needed by `Work.BoxBubble.mustbeinessentialBox`, from the classical input at the
*standard* torus.**  Because the classical input is an invariant of the ambient homeomorphism
class (`classicalInput_map_homeomorph_iff`), it suffices to prove it once, for the standard torus
of revolution; the statement below takes it in that normal form. -/
theorem mustbeinessentialBox_of_classicalInput_standard (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : R3 ≃ₜ R3) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (ClosedCurve.mapHomeomorph ψ (standardCurve p q)).γ)
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (hT : TransverseSphere (ParamTorus.mapHomeomorph ψ) (BoxSphere s c σ))
    (h : ClassicalInput standard)
    (hcount : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} < (Nat.min p q : ℕ∞)) :
    ¬ (ParamTorus.mapHomeomorph ψ).ContainsEssentialLoop (BoxSphere s c σ) :=
  mustbeinessentialBox_of_classicalInput p q hp hq hc ψ K himg hs c σ hT
    ((classicalInput_map_homeomorph_iff ψ).mpr h) hcount

/-! ## Unconditional consistency checks

Pardon's Lemma as assembled above is conditional on the classical input.  The following instances
are *unconditional*, so that the conclusions are seen not to be vacuous:

* a region disjoint from `F` contains no essential loop (`not_containsEssentialLoop_of_disjoint`);
* a region contained in a *chart* of the parametrisation (a set carrying a continuous section of
  `P.psi`) contains no essential loop at all, so Pardon's Lemma holds there with no hypothesis
  whatsoever.
-/

/-- **Pardon's Lemma for a region lying in a chart of the parametrisation** — unconditionally.
Such a region contains no essential loop of `F` (`Work.InnermostDisk.not_isEssential_of_section`),
so the *geometric* hypothesis of the Lemma is satisfied vacuously and no classical input is
needed. -/
theorem mustbeinessential_of_subset_section (P : ParamTorus) (β : ClosedCurve P) (S s : Set R3)
    (σ : C(s, ℝ × ℝ)) (hσ : ∀ x : s, P.psi (σ x).1 (σ x).2 = (x : R3)) (hS : S ⊆ s)
    (hSβ : Set.encard (Set.range β.γ ∩ S) < pardonsI P β) :
    ∀ α : ClosedCurve P, (∀ t : ℝ, α.γ t ∈ S) → ¬ IsEssential P α :=
  mustbeinessential_of_cleansInSphere P β S (cleansInSphere_of_subset_section σ hσ hS) hSβ

/-- **The challenge form of Pardon's Lemma 4.2 at the box boundary, from the `hclean` hypothesis**:
same conclusion and same intersection count as `mustbeinessentialBox_of_sliceData`, but the geometric
hypothesis is the strong cleaning form `CleansInSphereMeetingAtMost` at the box boundary. -/
theorem mustbeinessentialBox_of_meetingAtMost (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (ψ : R3 ≃ₜ R3) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (ClosedCurve.mapHomeomorph ψ (standardCurve p q)).γ)
    {s : ℝ} (hs : 0 < s) (c : R3) (σ : Equiv.Perm (Fin 3))
    (h : CleansInSphereMeetingAtMost (ParamTorus.mapHomeomorph ψ)
      (ClosedCurve.mapHomeomorph ψ (standardCurve p q)) (BoxSphere s c σ))
    (hcount : Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
        Submission.boxNorm c σ (K.curve t) = s} < (Nat.min p q : ℕ∞)) :
    ¬ (ParamTorus.mapHomeomorph ψ).ContainsEssentialLoop (BoxSphere s c σ) := by
  intro hU
  obtain ⟨γ, hess, hmem⟩ := hU
  have hβ : Set.encard (Set.range (ClosedCurve.mapHomeomorph ψ
      (standardCurve p q)).γ ∩ BoxSphere s c σ) <
      pardonsI (ParamTorus.mapHomeomorph ψ) (ClosedCurve.mapHomeomorph ψ (standardCurve p q)) := by
    rw [pardonsI_standard_mapHomeomorph p q hp hq hc ψ]
    refine lt_of_le_of_lt ?_ hcount
    calc Set.encard (Set.range (ClosedCurve.mapHomeomorph ψ (standardCurve p q)).γ ∩
          BoxSphere s c σ)
        = Set.encard (Set.range K.curve ∩ BoxSphere s c σ) := by rw [← himg]
      _ ≤ Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧ K.curve t ∈ BoxSphere s c σ} :=
          encard_range_inter_le_encard_param_of_periodic K.periodic (BoxSphere s c σ)
      _ = Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
            Submission.boxNorm c σ (K.curve t) = s} :=
          congrArg Set.encard (by
            ext t
            simp only [Set.mem_setOf_eq, mem_BoxSphere])
  exact mustbeinessential_BoxSphere_meetingAtMost (ParamTorus.mapHomeomorph ψ)
    (ClosedCurve.mapHomeomorph ψ (standardCurve p q)) hs c σ h hβ γ hmem hess

end

end Work.Topology.SphereSlicing
