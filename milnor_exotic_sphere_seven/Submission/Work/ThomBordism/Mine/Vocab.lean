import Mathlib
import Submission.Work.Tubular.Defs
import Submission.Work.Tubular.Global
import Submission.Work.Tubular.LocalDegree
import Submission.Work.PTGeometric.HOFDefs
import Submission.Work.Orient.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-!
# Vocabulary for the punctured-zero-section lemma

`ν = NormalTotal E` is the normal total space of an embedding `E : V ↪ ℝ^{8+k}` of a closed
oriented smooth `8`-manifold `V`, `Z = range (zeroSectionNormal E)` is the zero section and
`D = NormalDiscSub E ε` the closed `ε`-disc bundle of `ν`.

This file records the small dictionary used by `Work.ThomBordism.relCohomology_zeroSection_punct`:

* `Mine.zeroSecDisc E hε x` — the zero-section point `0_x` as a point of `D`;
* `Mine.zeroSecSet E hε` — the zero section of the disc bundle, as a subset of `D`;
* `Mine.discIncl E ε` — the inclusion `D ↪ ν` of the disc bundle (as a map of spaces);
* `Mine.discIncl_not_mem_point` — it sends the complement of `{0_x}` (inside `D`) into the
  complement of `{0_x}` (inside `ν`), the compatibility needed by `HOF.RelHmapOf`.
-/

namespace Work.ThomBordism.Mine

noncomputable section

open Work.ThomBordism.PontryaginThom (EmbeddingData)

variable {V : Work.ThomBordism.Man8} {k : ℕ}

/-- **The zero-section point `0_x` inside the disc bundle** of radius `ε`. -/
abbrev zeroSecDisc {E : EmbeddingData V (8 + k)} {ε : ℝ} (hε : 0 < ε) (x : V.pt) :
    Work.Tubular.NormalDiscSub E ε :=
  ⟨Work.Tubular.zeroSectionNormal E x, by
    rw [Work.Tubular.mem_normalClosedDiscSet]
    simpa [Work.Tubular.normalNorm] using hε.le⟩

theorem zeroSecDisc_apply {E : EmbeddingData V (8 + k)} {ε : ℝ} (hε : 0 < ε) (x : V.pt) :
    ((zeroSecDisc (E := E) hε x : Work.Tubular.NormalDiscSub E ε) : Work.Tubular.NormalTotal E)
      = Work.Tubular.zeroSectionNormal E x := rfl

theorem continuous_zeroSecDisc {E : EmbeddingData V (8 + k)} {ε : ℝ} (hε : 0 < ε) :
    Continuous (zeroSecDisc (E := E) hε) :=
  Continuous.subtype_mk (Work.Tubular.zeroSectionNormal E).continuous _

/-- **The zero section of the disc bundle**, as a subset of the disc bundle. -/
abbrev zeroSecSet {E : EmbeddingData V (8 + k)} {ε : ℝ} (hε : 0 < ε) :
    Set (Work.Tubular.NormalDiscSub E ε) :=
  Set.range (zeroSecDisc (E := E) hε)

theorem isCompact_zeroSecSet {E : EmbeddingData V (8 + k)} {ε : ℝ} (hε : 0 < ε) :
    IsCompact (zeroSecSet (E := E) hε) :=
  isCompact_range (continuous_zeroSecDisc (E := E) hε)

theorem mem_zeroSecSet {E : EmbeddingData V (8 + k)} {ε : ℝ} (hε : 0 < ε) (x : V.pt) :
    zeroSecDisc (E := E) hε x ∈ zeroSecSet (E := E) hε :=
  Set.mem_range_self _

/-- **The inclusion of the disc bundle into the normal total space.** -/
def discIncl (E : EmbeddingData V (8 + k)) (ε : ℝ) :
    TopCat.of (Work.Tubular.NormalDiscSub E ε) ⟶ TopCat.of (Work.Tubular.NormalTotal E) :=
  Work.Cohomology.subtypeIncl (TopCat.of (Work.Tubular.NormalTotal E))
    (Work.Tubular.normalClosedDiscSet E ε)

@[simp] theorem discIncl_apply (E : EmbeddingData V (8 + k)) (ε : ℝ)
    (q : Work.Tubular.NormalDiscSub E ε) :
    (discIncl E ε) q = (q : Work.Tubular.NormalTotal E) := rfl

/-- The disc-bundle inclusion sends the complement of `{0_x}` (inside the disc bundle) into the
complement of `{0_x}` (inside the normal total space). -/
theorem discIncl_not_mem_point (E : EmbeddingData V (8 + k)) {ε : ℝ} (C : Work.Tubular.TubeChart E ε)
    (x : V.pt) :
    ∀ q : Work.Tubular.NormalDiscSub E ε,
      q ∉ ({zeroSecDisc (E := E) C.eps_pos x} : Set (Work.Tubular.NormalDiscSub E ε)) →
      (discIncl E ε) q ∉ ({Work.Tubular.zeroSectionNormal E x} : Set (Work.Tubular.NormalTotal E)) := by
  intro q hq hcon
  apply hq
  apply Subtype.ext
  exact hcon

/-- The disc-bundle inclusion sends the complement of the zero section into the complement of the
zero section. -/
theorem discIncl_not_mem_zeroSec (E : EmbeddingData V (8 + k)) {ε : ℝ}
    (C : Work.Tubular.TubeChart E ε) :
    ∀ q : Work.Tubular.NormalDiscSub E ε,
      q ∉ zeroSecSet (E := E) C.eps_pos →
      (discIncl E ε) q ∉ Set.range (Work.Tubular.zeroSectionNormal E) := by
  intro q hq hcon
  apply hq
  obtain ⟨x', hx'⟩ := hcon
  exact ⟨x', Subtype.ext hx'⟩

end

end Work.ThomBordism.Mine
