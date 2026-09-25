import Mathlib
import Submission.Work.ShafarevichKoch.RelationBound
import Submission.Work.ShafarevichKoch.residuallyFiniteTwoGroup_presented

/-!
# `Work.ShafarevichKoch.exists_hasProTwoPresentation_of_finite`

Whenever the maximal unramified pro-`2` Galois group `G_∅ = Gal(M/F)` is *finite* as an abstract
group, the interface `Work.ShafarevichKoch.HasProTwoPresentation F d r` holds for suitable
`d r : ℕ`: a finite group is finitely presented, so we may take the naive presentation on a finite
generating set (all of `G_∅`) and the finite normal generating set of the kernel of the resulting
surjection `FreeGroup (Fin d) →* G_∅`.

This is the statement recorded (and used as a sanity check on the interface) in
`README.md` §9.9 of the Shafarevich--Koch chapter: the numerical relation *bound* `r ≤ d + d₂(O_F^×)`
is not a function of the usual invariants of `G_∅`, precisely because a finite `G_∅` satisfies the
interface with some `d, r` while the bound fails there (it would contradict the finite-`p`-group
Golod--Shafarevich inequality).

## Proof

`Group.IsFinitelyPresented` is an instance for finite groups, so
`Group.IsFinitelyPresented.out` supplies `d : ℕ` and a surjection `φ : FreeGroup (Fin d) →* G_∅`
whose kernel is the normal closure of a finite set `S`.  Writing `S` as the range of a map
`w : Fin r → FreeGroup (Fin d)` (`Set.Finite.fin_param`), and setting `g i := φ (FreeGroup.of i)`,
we have `FreeGroup.lift g = φ` (`FreeGroup.lift_unique`), so
`ker (FreeGroup.lift g) = normalClosure (Set.range w)` (clause `(P1)`), and the closure of the range
of `g` is `(FreeGroup.lift g).range = φ.range = ⊤` (`FreeGroup.range_lift_eq_closure`), whose
topological closure is `⊤` (clause `(P2)`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Classical

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-- **A finite maximal unramified pro-`2` group admits a pro-`2` presentation.**

If `G_∅ = Gal(M/F)` is finite (as an abstract group), then `HasProTwoPresentation F d r` holds for
some `d r : ℕ`: a finite group is finitely presented, and we present `G_∅` on the finite set of its
own elements. -/
theorem exists_hasProTwoPresentation_of_finite (F : Type*) [Field F] [NumberField F]
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} F 2)
    (hfin : Finite (Work.ClassFieldTower.galoisGroup M)) :
    ∃ d r : ℕ, Work.ShafarevichKoch.HasProTwoPresentation F d r := by
  classical
  haveI : Finite (Work.ClassFieldTower.galoisGroup M) := hfin
  obtain ⟨d, φ, hφ, hker⟩ :=
    Group.IsFinitelyPresented.out (G := Work.ClassFieldTower.galoisGroup M)
  obtain ⟨S, hSfin, hSclos⟩ := hker
  obtain ⟨r, w, _, hw⟩ := Set.Finite.fin_param hSfin
  let g : Fin d → Work.ClassFieldTower.galoisGroup M := fun i => φ (FreeGroup.of i)
  -- `FreeGroup.lift g` is the same homomorphism as `φ`.
  have hlift : FreeGroup.lift g = φ :=
    MonoidHom.ext (fun x => (FreeGroup.lift_unique φ (fun x => rfl)).symm)
  -- the `g i` generate `G_∅` topologically (they already generate it abstractly).
  have hclos : Subgroup.closure (Set.range g) = ⊤ := by
    rw [← FreeGroup.range_lift_eq_closure (f := g)]
    rw [hlift]
    exact MonoidHom.range_eq_top.mpr hφ
  refine ⟨d, r, M, g, w, ?_, ?_⟩
  · -- `(P1)`: the kernel of the presentation map is the normal closure of the relators.
    rw [hlift]
    rw [← hSclos, hw]
  · -- `(P2)`: the `g i` generate `G_∅` topologically.
    rw [hclos]
    exact le_antisymm le_top (Subgroup.le_topologicalClosure ⊤)

end Work.ShafarevichKoch
