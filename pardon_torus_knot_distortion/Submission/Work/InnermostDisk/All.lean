import Submission.Work.InnermostDisk.Defs
import Submission.Work.InnermostDisk.Reduction
import Submission.Work.InnermostDisk.Clean
import Submission.Work.InnermostDisk.Instances
import Submission.Work.InnermostDisk.Packaging
import Submission.Work.InnermostDisk.Slicing
import Submission.Work.InnermostDisk.CoreInterface
import Submission.Work.InnermostDisk.WindingAPI
import Submission.Work.InnermostDisk.polarCoord_surjective
import Submission.Work.InnermostDisk.exp_eq_exp_mul_I_exists_int
import Submission.Work.InnermostDisk.descend_continuousMap
import Submission.Work.InnermostDisk.not_isEssential_of_section
import Submission.Work.InnermostDisk.not_isEssential_of_const
import Submission.Work.InnermostDisk.not_isEssential_of_comp
import Submission.Work.InnermostDisk.not_isEssential_of_range_subset_isSimple
import Submission.Work.InnermostDisk.not_isEssential_of_range_subset_covered
import Submission.Work.InnermostDisk.isEssential_iff_hasWinding
import Submission.Work.InnermostDisk.homotopic_iff_homotopicClosed
import Submission.Work.InnermostDisk.isEssential_iff_of_homotopic
import Submission.Work.InnermostDisk.not_isEssential_iff_homotopic_const
import Submission.Work.InnermostDisk.not_isEssential_of_boundsDiscInSurface
import Submission.Work.InnermostDisk.boundsDiscInSurface_of_not_isEssential
import Submission.Work.InnermostDisk.isEmbeddedSphere_sphere
import Submission.Work.InnermostDisk.isEmbeddedSphere_image_homeomorph
import Submission.Work.InnermostDisk.exists_section_nhds
import Submission.Work.InnermostDisk.exists_ball_not_isEssential

/-!
# Pardon's innermost-disc arguments

This is the entry point of the `Work.InnermostDisk` chapter: importing it gives everything.
It formalises the two cut-and-paste steps of Pardon's Lemma 4.2 ("mustbeinessential",
*On the distortion of knots on embedded surfaces*, Ann. of Math. **174** (2011), 637–646), the
geometric content that `Submission/Work/CoreTopology/MustBeInessential.lean` left as the explicit
hypothesis `hclean`.

## What is proved, and what is assumed

Pardon's proof is a three-step argument.  Step 3 (the counting contradiction) and all the
plumbing between the steps are **proved here**, sorry-free.  Steps 1 and 2 are classical
topological facts about a PL embedded sphere in `ℝ³` which Mathlib does not have (Jordan–Schoenflies
in `S²`, PL transversality, ball-boundedness of embedded 2-spheres, isotopy extension); they are
kept as the two explicit hypotheses

* `Work.InnermostDisk.InnermostDiscInput P S` — *step 1, innermost in the sphere*: if `S` contains
  an essential loop of `F`, some essential simple loop `α ⊆ S` bounds a disc inside `S` whose
  interior meets `F` only in inessential curves (a `Work.InnermostDisk.InnermostDisc`);
* `Work.InnermostDisk.CleansDiscs P` — *step 2, innermost in the surface*: an innermost disc can be
  replaced, keeping its boundary, by an embedded disc whose interior misses `F`.

The latter is in turn reduced to the single cut-and-paste operation
`Work.InnermostDisk.RemovesOneCurve P` (proved in `Clean.lean`), and both together are packaged as
the single classical statement `Work.InnermostDisk.PardonSphereInput P`.

## Main results

* `Work.InnermostDisk.mustbeinessential_of_PLInput` — **Pardon's Lemma 4.2 from the complete PL
  input** `Work.InnermostDisk.PardonPLInput P`, namely (i) a PL slicing of every embedded sphere
  by the components of `S ∩ F`, each bounded by a disc inside the sphere and nested
  (`Work.InnermostDisk.SphereSlicing`), and (ii) the cut-and-paste step `CleansDiscs P`.
  The innermost *selection* of step 1 is proved
  (`Work.InnermostDisk.SphereSlicing.exists_min_essential`,
  `Work.InnermostDisk.SphereSlicing.innermostDiscInput_of_slicing`).
* `Work.InnermostDisk.mustbeinessential_of_inputs` — **Pardon's Lemma 4.2** from the two inputs:
  if `#(β ∩ S) < I(F, β)` then every closed curve of `F` contained in `S` is inessential.
  Variants: `mustbeinessential_of_cleansInSphere` (from the abstract geometric input),
  `mustbeinessential_core_of_inputs` (with `I` kept abstract),
  `mustbeinessential_of_pardonSphereInput` (from the single packaged input),
  `mustbeinessential_of_removesOneCurve` (from one cut-and-paste),
  `mustbeinessential_via_core` (through the existing `Work.CoreTopology.mustbeinessential`).
* `Work.InnermostDisk.le_pardonsI_of_inputs`, `not_containsEssentialLoop_of_inputs`,
  `not_containsEssentialLoop_standardCurve_of_inputs` (for the standard `(p,q)` curve, with
  `I(F,β) = min p q`): the contrapositive forms.
* `Work.InnermostDisk.not_boundsDiskInComplement_of_mem_sphere` — the counting step alone,
  unconditional: no compressing loop fits inside a sphere meeting `β` too rarely.
* The passage from Pardon's literal conclusion ("every *component* of `S ∩ F` is inessential")
  to the formal one ("every closed curve of `F` whose image lies in `S` is inessential"):
  `Work.InnermostDisk.not_isEssential_of_range_subset_isSimple` (a loop lying in the image of an
  inessential *simple* curve is inessential) and
  `Work.InnermostDisk.not_isEssential_of_range_subset_covered` (a loop lying in a finite union of
  pairwise disjoint inessential simple curves is inessential).
* `Work.InnermostDisk.mustbeinessential_of_subset_section`,
  `Work.InnermostDisk.mustbeinessential_of_emptySlice` — unconditional instances.
* The chart lemma `not_isEssential_of_section`, the local charts of the standard torus
  (`exists_section_nhds`, `exists_ball_not_isEssential`), and the bridge between the winding-vector
  notion of essentiality and Pardon's "bounds a disc in the surface" / null-homotopy
  (`isEssential_iff_hasWinding`, `not_isEssential_iff_homotopic_const`,
  `not_isEssential_of_boundsDiscInSurface`, `boundsDiscInSurface_of_not_isEssential`).

See `Submission/Work/InnermostDisk/README.md` for the full account.
-/

namespace Work.InnermostDisk

end Work.InnermostDisk
