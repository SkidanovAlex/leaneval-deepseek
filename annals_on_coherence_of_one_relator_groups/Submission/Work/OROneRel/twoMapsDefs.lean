import Mathlib
import Submission.Work.OROneRel.winGateDefs
import Submission.Work.OROneRel.winRho_winRoot

/-!
# The class map of the window vertex, as a homomorphism

The vertex of the `Z`-domain decomposition of `G = ⟨α | u ^ l⟩` is the subgroup
`winVertex Wt c lo hi u l` of `G`, presented by `⟨winBeta | winRoot ^ l⟩`
(`Submission/Work/OROneRel/winAssembly.lean`).  This file provides the *class map* `winTheta` whose
image that subgroup is:

  `winTheta : ⟨winBeta | winRoot ^ l⟩ →* ⟨α | u ^ l⟩`,

the map of presented groups induced by the class map `winRho` of the alphabet, which is well defined
because `winRho (winRoot ^ l) = u ^ l` (`Work.OROneRel.winRho_winRoot`).

It is the map denoted `θ` in the *two-maps construction* of
`Submission/Work/OROneRel/magnusStepCase2.lean` (session notes, item (E)): the pin is the statement
`mk (Wt j * τ ^ (-j)) ∈ winTheta.range` and the assembly of the residual then only has to show that
`winTheta` is *injective* (plank (A)) in order to identify the vertex with `⟨winBeta | winRoot^l⟩`.

## Main declarations

* `winThetaGen`, `winTheta`, `winTheta_of`, `winTheta_mk`, `winTheta_winRoot`
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- The generator map of the class map of the window vertex: a window generator goes to the class of
its loop class. -/
noncomputable def winThetaGen (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α)
    (l : ℕ) : Work.OROneRel.winBeta Wt c lo hi → PresentedGroup ({u ^ l} : Set (FreeGroup α)) :=
  fun e => PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Work.OROneRel.coverClassAt Wt c e.1)

/-- `FreeGroup.lift` of the generator map is the class map `winRho` followed by `mk`. -/
theorem lift_winThetaGen (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α)
    (l : ℕ) :
    FreeGroup.lift (winThetaGen Wt c lo hi u l) =
      (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))).comp
        (Work.OROneRel.winRho Wt c lo hi) := by
  refine FreeGroup.ext_hom _ _ (fun e => ?_)
  rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, winThetaGen, Work.OROneRel.winRho_of]

/-- **The class map of the window vertex.**  The map of presented groups
`⟨winBeta | winRoot ^ l⟩ →* ⟨α | u ^ l⟩` induced by the loop class map `winRho` of the window
alphabet; it is well defined because `winRho (winRoot ^ l) = u ^ l`. -/
noncomputable def winTheta (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α)
    (l : ℕ) (hW0 : Wt 0 = 1) (hcu : Work.OROneRel.cohom c u = 1)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi) :
    PresentedGroup ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
        Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))) →*
      PresentedGroup ({u ^ l} : Set (FreeGroup α)) :=
  PresentedGroup.toGroup (f := winThetaGen Wt c lo hi u l) (by
    intro r hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    rw [lift_winThetaGen, MonoidHom.comp_apply, map_pow,
      Work.OROneRel.winRho_winRoot Wt hW0 hcu lo hi hwin]
    exact PresentedGroup.one_of_mem (Set.mem_singleton _))

/-- The value of `winTheta` on a generator: the class of the loop class of the window edge. -/
@[simp] theorem winTheta_of (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α)
    (l : ℕ) (hW0 : Wt 0 = 1) (hcu : Work.OROneRel.cohom c u = 1)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (e : Work.OROneRel.winBeta Wt c lo hi) :
    winTheta Wt c lo hi u l hW0 hcu hwin (PresentedGroup.of e) =
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
        (Work.OROneRel.coverClassAt Wt c e.1) :=
  PresentedGroup.toGroup.of _

/-- The value of `winTheta` on the class of a word: the class of its loop class under `winRho`. -/
theorem winTheta_mk (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α)
    (l : ℕ) (hW0 : Wt 0 = 1) (hcu : Work.OROneRel.cohom c u = 1)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (w : FreeGroup (Work.OROneRel.winBeta Wt c lo hi)) :
    winTheta Wt c lo hi u l hW0 hcu hwin
        (PresentedGroup.mk ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
            Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))) w) =
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) (Work.OROneRel.winRho Wt c lo hi w) := by
  have h : (winTheta Wt c lo hi u l hW0 hcu hwin).comp
        (PresentedGroup.mk ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
          Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))) =
      (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))).comp
        (Work.OROneRel.winRho Wt c lo hi) := by
    refine FreeGroup.ext_hom _ _ (fun e => ?_)
    show winTheta Wt c lo hi u l hW0 hcu hwin (PresentedGroup.of e) =
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
        (Work.OROneRel.winRho Wt c lo hi (FreeGroup.of e))
    rw [winTheta_of, Work.OROneRel.winRho_of]
  exact congrArg (fun f : FreeGroup (Work.OROneRel.winBeta Wt c lo hi) →*
      PresentedGroup ({u ^ l} : Set (FreeGroup α)) => f w) h

/-- The value of `winTheta` on the class of the vertex root: the class of `u`. -/
theorem winTheta_winRoot (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α)
    (l : ℕ) (hW0 : Wt 0 = 1) (hcu : Work.OROneRel.cohom c u = 1)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi) :
    winTheta Wt c lo hi u l hW0 hcu hwin
        (PresentedGroup.mk ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
            Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))
          (Work.OROneRel.winRoot Wt c lo hi u)) =
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u := by
  rw [winTheta_mk, Work.OROneRel.winRho_winRoot Wt hW0 hcu lo hi hwin]

/-- **The range of the class map is the vertex.**  It is the image of the loop class map `winRho`
under `PresentedGroup.mk`, i.e. the subgroup `winVertex` of
`Submission/Work/OROneRel/winAssembly.lean`. -/
theorem winTheta_range (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α)
    (l : ℕ) (hW0 : Wt 0 = 1) (hcu : Work.OROneRel.cohom c u = 1)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi) :
    (winTheta Wt c lo hi u l hW0 hcu hwin).range =
      (Work.OROneRel.winRho Wt c lo hi).range.map
        (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨w, rfl⟩ := PresentedGroup.mk_surjective
      ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
        Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))) x
    exact ⟨Work.OROneRel.winRho Wt c lo hi w, ⟨w, rfl⟩, (winTheta_mk Wt c lo hi u l hW0 hcu hwin w).symm⟩
  · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
    exact ⟨PresentedGroup.mk
      ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
        Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))) w,
      winTheta_mk Wt c lo hi u l hW0 hcu hwin w⟩

end Work.OROneRel
