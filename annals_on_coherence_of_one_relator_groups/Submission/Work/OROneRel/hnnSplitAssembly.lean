import Mathlib
import Submission.Work.OROneRel.winAssembly
import Submission.Work.OROneRel.twoMapsDefs
import Submission.Work.OROneRel.hnnExtension_iso_of_baseMulEquiv
import Submission.Work.OROneRel.unionAmalgamDefs

/-!
# The HNN splitting of `⟨α | u ^ l⟩` over the window vertex, from an explicit inverse

The residual of `Work.OROneRel.magnusStepCase2` (`Submission/Work/OROneRel/magnusStepCase2.lean`,
the obligation `magnusStepCase2_domainDatum_letters`) is the `Z`-domain step of Linton, *One-relator
hierarchies*, arXiv 2202.11324: the splitting of `G = ⟨α | u ^ l⟩` over the fundamental group of a
window `D` of the `Z`-cover.  This file isolates the *algebraic* content of that splitting and
proves it, leaving the geometric content as an explicit list of hypotheses.

## The general principle

The comparison map of the splitting is

`Ψ := HNNExtension.lift θ t hψ : HNNExtension Hd A A ψ →* G`,

where `Hd = ⟨β | v ^ l⟩` is the vertex group, `θ : Hd →* G` is the class map of the window,
`A ≤ Hd` is an associated subgroup and `t = mk τ ∈ G` is the class of the deck element.  `Ψ` maps
`of h ↦ θ h` and `HNNExtension.t ↦ t`.

The point of the construction is that **an explicit inverse of `Ψ` on generators finishes the job**:

* if `Φ : G →* HNNExtension Hd A A ψ` satisfies `Φ (θ h) = of h` and `Φ t = HNNExtension.t`, then
  `Φ ∘ Ψ = id` by `HNNExtension.hom_ext`, so `Ψ` is injective; if moreover `G = ⟨θ(Hd), t⟩`
  (the *generation* plank), then `Ψ` is surjective and hence an isomorphism;
* the map `Φ` itself is produced by `PresentedGroup.toGroup` from a generator map `X : α → K` with
  `FreeGroup.lift X (u ^ l) = 1` (the *relation* condition, `hXu`), `FreeGroup.lift X τ = t`
  (the *tracking* condition, `hXτ`), and `FreeGroup.lift X (coverClassAt Wt c e) = of e` for the
  generators `e` of the vertex (the *coedge* condition, `hXβ`).

The three conditions on `X` are the exact translation of "the labelled walk of the window is
consistent with the `Hd`-structure of the cover"; in the `Z`-cover they are read off from the walk of
`u` (via `Work.OROneRel.walking_telescope`), which is why the residual is a statement about the walk
and not about topology.  The natural candidate, for a *pin* `Q : ℤ → Hd` with
`θ (Q j) = mk (Wt j * τ ^ (-j))`, is

`X x := t ^ (-i) * of (Q i)⁻¹ * Γ(x,i) * of (Q (i + c x)) * t ^ (i + c x)`

where `Γ(x,i) = of e` for a non-tree edge `e = (x,i)` of the window and `Γ(x,i) = 1` for a tree
edge; the *only* content of the pin is that this expression is independent of the chosen level `i`
(equivalently: it is the statement that the level factors `Wt j * τ ^ (-j)` lie in the vertex and
are consistent along the tree).

## Contents

* `hnnExtension_iso_of_explicit_inverse` -- the general principle (no window in sight);
* `magnusDomainDatum_of_windowInverse` -- the `Z`-domain datum of the residual from a window and an
  explicit inverse on generators, assembled through the *proved* `magnusDomainDatum_of_winData`.
-/

namespace Work.OROneRel

universe u

/-! ## 1. The general HNN principle -/

/-- **The HNN extension is generated, over `θ(H)`, by an element `s` which satisfies the
defining relations, as soon as an explicit inverse is exhibited on generators.**

Concretely: let `A ≤ H`, `ψ : A ≃* A`, and let `θ : H →* G` and `s : G` satisfy the HNN relation
`s * θ a = θ (ψ a) * s` for `a ∈ A`.  If `G = ⟨θ(H), s⟩` and there is a homomorphism
`Φ : G →* HNNExtension H A A ψ` with `Φ (θ h) = of h` and `Φ s = t`, then `G ≅ HNNExtension H A A ψ`
with the base and the stable letter pinned. -/
theorem hnnExtension_iso_of_explicit_inverse {H G : Type*} [Group H] [Group G]
    (A : Subgroup H) (ψ : A ≃* A) (θ : H →* G) (s : G)
    (hψ : ∀ a : A, s * θ (a : H) = θ ((ψ a : A) : H) * s)
    (hgen : θ.range ⊔ Subgroup.zpowers s = ⊤)
    (Φ : G →* HNNExtension H A A ψ)
    (hΦ_of : ∀ h : H, Φ (θ h) = HNNExtension.of h)
    (hΦ_t : Φ s = HNNExtension.t) :
    ∃ e : G ≃* HNNExtension H A A ψ,
      (∀ h : H, e (θ h) = HNNExtension.of h) ∧ e s = HNNExtension.t := by
  classical
  -- the comparison map
  set Ψ : HNNExtension H A A ψ →* G := HNNExtension.lift θ s hψ with hΨ
  have hΨ_of : ∀ h : H, Ψ (HNNExtension.of h) = θ h := fun h => HNNExtension.lift_of θ s hψ h
  have hΨ_t : Ψ HNNExtension.t = s := HNNExtension.lift_t θ s hψ
  -- `Φ` is a left inverse of `Ψ`
  have hΦΨ : ∀ x : HNNExtension H A A ψ, Φ (Ψ x) = x := by
    have hcomp : Φ.comp Ψ = MonoidHom.id (HNNExtension H A A ψ) := by
      refine HNNExtension.hom_ext ?_ ?_
      · refine MonoidHom.ext fun h => ?_
        show Φ (Ψ (HNNExtension.of h)) = HNNExtension.of h
        rw [hΨ_of h, hΦ_of h]
      · show Φ (Ψ HNNExtension.t) = HNNExtension.t
        rw [hΨ_t, hΦ_t]
    intro x
    have := congrArg (fun f : HNNExtension H A A ψ →* HNNExtension H A A ψ => f x) hcomp
    simpa using this
  -- `Ψ` is surjective, so `Φ` is injective and the two are mutually inverse
  have hsurjΨ : Function.Surjective Ψ := by
    rw [← MonoidHom.range_eq_top]
    refine le_antisymm le_top ?_
    rw [← hgen]
    refine sup_le ?_ ?_
    · rintro g ⟨h, rfl⟩
      exact ⟨HNNExtension.of h, hΨ_of h⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨HNNExtension.t, hΨ_t⟩
  have hinjΦ : Function.Injective Φ := by
    intro x y hxy
    have hx : Ψ (Φ x) = x := by
      obtain ⟨z, rfl⟩ := hsurjΨ x
      rw [hΦΨ z]
    have hy : Ψ (Φ y) = y := by
      obtain ⟨z, rfl⟩ := hsurjΨ y
      rw [hΦΨ z]
    rw [← hx, ← hy, hxy]
  have hbij : Function.Bijective Φ := ⟨hinjΦ, fun y => ⟨Ψ y, hΦΨ y⟩⟩
  exact ⟨MulEquiv.mk (Equiv.ofBijective Φ hbij) (fun x y => map_mul Φ x y), hΦ_of, hΦ_t⟩

/-! ## 2. The `Z`-domain datum from an explicit inverse on the window generators -/

section Window

variable {α : Type u}

/-- **The `Z`-domain datum of the residual case from an explicit inverse of the comparison map on
the generators of the window.**

`θ = winTheta Wt c lo hi u l hW0 hcu hwin : ⟨winBeta | winRoot ^ l⟩ →* ⟨α | u ^ l⟩` is the class
map of the window, `τ` a deck element, `A ≤ ⟨winBeta | winRoot ^ l⟩` an associated subgroup with
`ψ : A ≃* A` the conjugation, and `X : α → HNNExtension ↥A ↥A ψ` a generator map satisfying the
three conditions

* `hXu` : `FreeGroup.lift X (u ^ l) = 1` (the relator is killed, so that `X` induces a map
  `Φ : ⟨α | u ^ l⟩ →* HNNExtension …`),
* `hXτ` : `FreeGroup.lift X τ = HNNExtension.t` (the tracking of the deck element),
* `hXβ` : `FreeGroup.lift X (coverClassAt Wt c e) = HNNExtension.of (of e)` for every
  coedge `e` of the window (the coedge condition),

together with the *generation* plank `hgen : θ.range ⊔ zpowers (mk τ) = ⊤`, the *Freiheitssatz*
plank `hA` and the aperiodicity and norm bounds of the window root.  The conclusion is the
`Z`-domain datum, and hence (through the proved `magnus_step_root_no_eps_zero_of_domainDatum`) the
target. -/
noncomputable def magnusDomainDatum_of_windowInverse (u : FreeGroup α) (l : ℕ) {c : α → ℤ}
    (Wt : ℤ → FreeGroup α) (lo hi : ℤ) (τ : FreeGroup α)
    (hW0 : Wt 0 = 1) (hcu : Work.OROneRel.cohom c u = 1)
    (hτ : Work.OROneRel.cohom c τ = Multiplicative.ofAdd 1)
    (hwin : ∀ p ∈ Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u),
      Work.OROneRel.coverEdge p ∈ Work.OROneRel.winE c lo hi)
    (hppv : ¬ Work.OROneRel.IsProperPower (Work.OROneRel.winRoot Wt c lo hi u))
    (hnorm : Work.OROneRel.relatorNorm (Work.OROneRel.winRoot Wt c lo hi u) <
      Work.OROneRel.relatorNorm u)
    (hA : ∀ x : FreeGroup (Work.OROneRel.winBeta Wt c lo hi),
      Work.OROneRel.winRho Wt c lo hi x ∈
          Subgroup.normalClosure ({u ^ l} : Set (FreeGroup α)) →
        x ∈ Subgroup.normalClosure
          ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
            Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))))
    (hθ : Function.Injective (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin))
    (A : Subgroup (PresentedGroup
      ({Work.OROneRel.winRoot Wt c lo hi u ^ l} : Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))))
    (ψ : A ≃* A)
    (hψ : ∀ a : A,
      PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ *
          Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin
            (a : PresentedGroup
              ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
                Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))) =
        Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin
            (ψ a : PresentedGroup
              ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
                Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))) *
          PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ)
    (hgen : (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin).range ⊔
      Subgroup.zpowers (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) = ⊤)
    (X : α → HNNExtension (PresentedGroup
      ({Work.OROneRel.winRoot Wt c lo hi u ^ l} : Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))))
      A A ψ)
    (hXu : FreeGroup.lift X (u ^ l) = 1)
    (hXτ : FreeGroup.lift X τ = HNNExtension.t)
    (hXβ : ∀ e : Work.OROneRel.winBeta Wt c lo hi,
      FreeGroup.lift X (Work.OROneRel.coverClassAt Wt c e.1) =
        HNNExtension.of (PresentedGroup.of e)) :
    MagnusDomainDatum u l := by
  classical
  have hXu' : ∀ r ∈ ({u ^ l} : Set (FreeGroup α)), FreeGroup.lift X r = 1 := by
    intro r hr
    rw [Set.mem_singleton_iff] at hr
    subst hr
    exact hXu
  -- the goal is a `Type`, so the existential extraction has to happen in a `Prop`
  have hmain : Nonempty (MagnusDomainDatum u l) := by
    -- the explicit inverse `Φ` and the comparison map
    set Φ : PresentedGroup ({u ^ l} : Set (FreeGroup α)) →* HNNExtension (PresentedGroup
        ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
          Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))) A A ψ :=
      PresentedGroup.toGroup (f := X) hXu' with hΦ
    have hΦ_mk : ∀ w : FreeGroup α,
        Φ (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) w) = FreeGroup.lift X w := fun _ => rfl
    have hΦ_of : ∀ h : PresentedGroup
        ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
          Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))),
        Φ (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin h) = HNNExtension.of h := by
      have key : Φ.comp (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin) = HNNExtension.of := by
        refine PresentedGroup.ext (fun e => ?_)
        rw [MonoidHom.comp_apply, Work.OROneRel.winTheta_of, hΦ_mk, hXβ e]
      intro h
      exact congrArg (fun f : PresentedGroup
          ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
            Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))) →*
          HNNExtension (PresentedGroup
            ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
              Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi)))) A A ψ => f h) key
    obtain ⟨e, he_of, he_t⟩ := hnnExtension_iso_of_explicit_inverse A ψ
      (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin)
      (PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ) hψ hgen Φ hΦ_of
      (by rw [hΦ_mk]; exact hXτ)
    -- the vertex of the splitting, and the transported isomorphism
    have hrange : (Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin).range =
        Work.OROneRel.winVertex Wt c lo hi u l :=
      Work.OROneRel.winTheta_range Wt c lo hi u l hW0 hcu hwin
    let iso : PresentedGroup
        ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
          Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))) ≃*
        ↥(Work.OROneRel.winVertex Wt c lo hi u l) :=
      (MonoidHom.ofInjective hθ).trans (MulEquiv.subgroupCongr hrange)
    have hiso : ∀ h : PresentedGroup
        ({Work.OROneRel.winRoot Wt c lo hi u ^ l} :
          Set (FreeGroup (Work.OROneRel.winBeta Wt c lo hi))),
        ((iso h : ↥(Work.OROneRel.winVertex Wt c lo hi u l)) :
          PresentedGroup ({u ^ l} : Set (FreeGroup α))) =
        Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin h := fun _ => rfl
    obtain ⟨A', B', φ', E, -, -, hE_of, hE_t⟩ :=
      hnnExtension_iso_of_baseMulEquiv iso A A ψ
    refine ⟨magnusDomainDatum_of_winData u l hcu Wt lo hi τ hW0 hwin hτ hppv hnorm hA A' B' φ'
      (E.symm.trans e.symm) ?_ ?_⟩
    · intro h
      obtain ⟨g, rfl⟩ := MulEquiv.surjective iso h
      have h1 : E.symm (HNNExtension.of (iso g)) = HNNExtension.of g := by
        rw [← hE_of g, MulEquiv.symm_apply_apply]
      have h2 : e.symm (HNNExtension.of g) =
          Work.OROneRel.winTheta Wt c lo hi u l hW0 hcu hwin g := by
        rw [← he_of g, MulEquiv.symm_apply_apply]
      show e.symm (E.symm (HNNExtension.of (iso g))) =
        ((iso g : ↥(Work.OROneRel.winVertex Wt c lo hi u l)) :
          PresentedGroup ({u ^ l} : Set (FreeGroup α)))
      rw [h1, h2]
      exact (hiso g).symm
    · have h1 : E.symm HNNExtension.t = HNNExtension.t := by
        rw [← hE_t, MulEquiv.symm_apply_apply]
      have h2 : e.symm HNNExtension.t = PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ := by
        rw [← he_t, MulEquiv.symm_apply_apply]
      show e.symm (E.symm HNNExtension.t) = PresentedGroup.mk ({u ^ l} : Set (FreeGroup α)) τ
      rw [h1, h2]
  exact Classical.choice hmain

end Window

end Work.OROneRel
