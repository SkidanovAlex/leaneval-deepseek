import Mathlib
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.winRho_winRoot
import Submission.Work.OROneRel.winFreiheitssatz_easy
import Submission.Work.OROneRel.presentedGroup_map_injective_of_preimage
import Submission.Work.OROneRel.exists_cover_root_data
import Submission.Work.OROneRel.magnus_step_root_no_eps_zero

/-!
# The assembly of the window decomposition into the `Z`-domain datum

This file reduces the residual of `Work.OROneRel.magnusStepCase2` to exactly two geometric
obligations, in the *correct* basis (the non-tree edges `E(D) ∖ T` of a window, with the tree-path
gauge; see `Submission/Work/OROneRel/NOTES_magnusStepCase2_crux.md`, Fact 4).

Let `β = winBeta Wt c lo hi`, `v = winRoot Wt c lo hi u` (the deleted walk word) and
`ρ = winRho Wt c lo hi : F β →* F α` (the class map), and let `G = ⟨α | u ^ l⟩`.

* `winVertex Wt c lo hi u l = ρ.range.map (PresentedGroup.mk {u ^ l}) ≤ G` is the vertex.
* The map `⟨β | v ^ l⟩ →* G` induced by `ρ` (which exists as soon as `ρ (v ^ l) = u ^ l`, i.e.
  `winRoot v = u` from `Work.OROneRel.winRho_winRoot`) has range `winVertex` and is injective as soon
  as the Freiheitssatz (A), `ρ x ∈ ⟪u ^ l⟫ → x ∈ ⟪v ^ l⟫`, holds; this is the obligation
  `Work.OROneRel.winFreiheitssatz`.
* `magnusDomainDatum_of_winData` below then produces the `Z`-domain datum
  `Work.OROneRel.MagnusDomainDatum u l` from
  * the telescoping identity (`winRho_winRoot`, proved),
  * (A) (`work.OROneRel.winFreiheitssatz`, delegated),
  * aperiodicity of `v` (`not_isProperPower_winRoot`, proved),
  * the norm bound (`winRootNormLt`, proved),
  * the splitting (B) over the vertex (`winVertexSplits`, delegated),
  * the trivial half of (A) (`winRoot_preimage_easy`, proved).

Hence the target follows from (A), (B) and the existence of the window/gauge/deck data.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-- **The vertex of the window decomposition** inside `G = ⟨α | u ^ l⟩`: the image of the alphabet
`β = E(D) ∖ T` under the class map `winRho`. -/
noncomputable def winVertex (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α)
    (l : ℕ) : Subgroup (PresentedGroup ({u ^ l} : Set (FreeGroup α))) :=
  (winRho Wt c lo hi).range.map (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)))

/-- **The `Z`-domain datum from the window data.**  Given a window `[lo,hi]` containing the walk of
`u`, a gauge `Wt` with `Wt 0 = 1`, a deck element `τ` of weight `1`, the aperiodicity and norm bounds
for the deleted walk word `v = winRoot Wt c lo hi u`, the Freiheitssatz (A) for the window basis, and
the splitting (B) over the vertex `winVertex Wt c lo hi u l`, the datum of the residual holds. -/
noncomputable def magnusDomainDatum_of_winData {α : Type u} (u : FreeGroup α) (l : ℕ)
    {c : α → ℤ} (hcu : Work.OROneRel.cohom c u = 1)
    (Wt : ℤ → FreeGroup α) (lo hi : ℤ) (τ : FreeGroup α)
    (hW0 : Wt 0 = 1)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (hτ : Work.OROneRel.cohom c τ = Multiplicative.ofAdd 1)
    (hppv : ¬ Work.OROneRel.IsProperPower (Work.OROneRel.winRoot Wt c lo hi u))
    (hnorm : Work.OROneRel.relatorNorm (Work.OROneRel.winRoot Wt c lo hi u) <
      Work.OROneRel.relatorNorm u)
    (hA : ∀ x : FreeGroup (Work.OROneRel.winBeta Wt c lo hi),
      Work.OROneRel.winRho Wt c lo hi x ∈
          Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) →
        x ∈ Subgroup.normalClosure
          ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
            Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))))
    (A B : Subgroup ↥(winVertex Wt c lo hi u l)) (φ : A ≃* B)
    (e : HNNExtension ↥(winVertex Wt c lo hi u l) A B φ ≃*
      PresentedGroup ({u ^ l} : Set (FreeGroup α)))
    (he_of : ∀ h : ↥(winVertex Wt c lo hi u l),
      e (HNNExtension.of h) =
        ((h : ↥(winVertex Wt c lo hi u l)) :
          PresentedGroup ({u ^ l} : Set (FreeGroup α))))
    (he_t : e HNNExtension.t = PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) :
    MagnusDomainDatum u l := by
  classical
  -- the telescoping identity and the preimage statement (A) together with its easy half
  have hv : Work.OROneRel.winRho Wt c lo hi (Work.OROneRel.winRoot Wt c lo hi u) = u :=
    Work.OROneRel.winRho_winRoot Wt hW0 hcu lo hi hwin
  have hpre : ∀ x : FreeGroup (Work.OROneRel.winBeta Wt c lo hi),
      Work.OROneRel.winRho Wt c lo hi x ∈
          Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) ↔
        x ∈ Subgroup.normalClosure
          ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
            Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))) :=
    fun x => ⟨hA x, fun hx => Work.OROneRel.winRoot_preimage_easy Wt hW0 hcu lo hi l hwin x hx⟩
  -- the injective map out of the vertex presentation (extracted by choice: the ambient goal is a
  -- `Type`, so a `Prop`-existential cannot be eliminated directly)
  have hex := Work.OROneRel.presentedGroup_map_injective_of_preimage
    (Work.OROneRel.winRho Wt c lo hi) (Work.OROneRel.winRoot Wt c lo hi u) u l hpre
  let Φ : PresentedGroup
        ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
          Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))) →*
      PresentedGroup ({u ^ l} : Set (FreeGroup α)) := Classical.choose hex
  have hΦinj : Function.Injective Φ := (Classical.choose_spec hex).1
  have hΦmk : ∀ x : FreeGroup (Work.OROneRel.winBeta Wt c lo hi),
      Φ (PresentedGroup.mk
        ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
          Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))) x)
        = PresentedGroup.mk ({u ^ l} : Set (FreeGroup α))
            (Work.OROneRel.winRho Wt c lo hi x) := (Classical.choose_spec hex).2
  -- its range is the vertex
  have hrange : Φ.range = winVertex Wt c lo hi u l := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨w, rfl⟩ :=
        PresentedGroup.mk_surjective
          ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
            Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))) x
      exact ⟨Work.OROneRel.winRho Wt c lo hi w, ⟨w, rfl⟩, (hΦmk w).symm⟩
    · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
      exact ⟨PresentedGroup.mk _ x, hΦmk x⟩
  -- the base isomorphism
  let iso : PresentedGroup
        ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
          Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))) ≃*
      ↥(winVertex Wt c lo hi u l) :=
    (MonoidHom.ofInjective hΦinj).trans (MulEquiv.subgroupCongr hrange)
  have hiso : ∀ x, ((iso x : ↥(winVertex Wt c lo hi u l)) :
      PresentedGroup ({u ^ l} : Set (FreeGroup α))) = Φ x := by
    intro x
    show Φ x = Φ x
    rfl
  have hroot : ((iso (PresentedGroup.mk
        ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
          Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))
        (Work.OROneRel.winRoot Wt c lo hi u)) : ↥(winVertex Wt c lo hi u l)) :
      PresentedGroup ({u ^ l} : Set (FreeGroup α))) =
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) u := by
    rw [hiso, hΦmk, hv]
  exact ⟨Work.OROneRel.winBeta Wt c lo hi, Work.OROneRel.winRoot Wt c lo hi u, hppv, hnorm,
    winVertex Wt c lo hi u l, PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ,
    ⟨A, B, φ, e, he_of, he_t⟩, iso, hroot⟩

end Work.OROneRel
