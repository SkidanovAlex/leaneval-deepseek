import Mathlib
import Submission.Work.ShafarevichKoch.RelationBound

/-!
# `Work.ShafarevichKoch.hasProTwoPresentation_of_denseEmbedding`

**Transfer of a pro-`2` presentation along a dense embedding.**

`HasProTwoPresentation F d r` (`RelationBound.lean`) asks for a maximal unramified pro-`2`
extension `M/F` together with `d` elements `g_i ∈ Gal(M/F)` and `r` words `w_j` in `d` letters
such that the presentation map `FreeGroup (Fin d) →* Gal(M/F)`, `x_i ↦ g_i`, has kernel the normal
closure of the `w_j`, and the `g_i` generate `Gal(M/F)` topologically.

The point of this file is that this datum may be built *abstractly*: it suffices to exhibit an
arbitrary group `G`, a presentation of `G` by `d` generators and `r` relations, and an **injective**
homomorphism `ρ : G →* Gal(M/F)` whose image of the `d` generators is topologically dense.  Two
ingredients make the transfer work:

* injectivity of `ρ` keeps the kernel of the presentation map unchanged, because
  `FreeGroup.lift (ρ ∘ gen) = ρ.comp (FreeGroup.lift gen)` and
  `MonoidHom.ker_comp_of_injective`;
* density is carried verbatim, since the closure of the image family `ρ ∘ gen` is exactly the
  topological closure named in the hypothesis.

This is the form in which the classical Shafarevich--Koch presentation is produced: one first
identifies the abstract group `G` with a presentation, then embeds it densely in `Gal(M/F)`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- **Transfer of an abstract presentation to `G_∅` along a dense embedding.**

Let `G` be a group presented by `d` generators `gen` and `r` relators `w`, let `M` be a maximal
unramified pro-`2` extension of `F`, and let `ρ : G →* Gal(M/F)` be injective with the images of the
`gen_i` topologically generating `Gal(M/F)`.  Then `F` has a pro-`2` presentation by `d` generators
and `r` relators in the sense of `HasProTwoPresentation F d r`. -/
theorem hasProTwoPresentation_of_denseEmbedding {F : Type*} [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2) {d r : ℕ} {G : Type*} [Group G]
    (gen : Fin d → G)
    (hker : ∃ w : Fin r → FreeGroup (Fin d),
      MonoidHom.ker (FreeGroup.lift gen) = Subgroup.normalClosure (Set.range w))
    (ρ : G →* Work.ClassFieldTower.galoisGroup M) (hinj : Function.Injective ρ)
    (hdense : (Subgroup.closure (Set.range (fun i => ρ (gen i)))).topologicalClosure = ⊤) :
    Work.ShafarevichKoch.HasProTwoPresentation F d r := by
  classical
  obtain ⟨w, hw⟩ := hker
  refine ⟨M, fun i => ρ (gen i), w, ?_, hdense⟩
  -- The presentation map of the image family is `ρ` composed with the presentation map of `G`.
  have hlift : FreeGroup.lift (fun i => ρ (gen i)) = ρ.comp (FreeGroup.lift gen) := by
    refine FreeGroup.ext_hom _ _ (fun i => ?_)
    simp [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
  -- Injectivity of `ρ` makes the kernel of the composed map the kernel of `FreeGroup.lift gen`.
  rw [hlift, MonoidHom.ker_comp_of_injective (FreeGroup.lift gen) ρ hinj]
  exact hw

end Work.ShafarevichKoch
