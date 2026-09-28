import Mathlib
import Submission.Work.RatHurewicz.cellwiseNonvanishing
import Submission.Work.Serre.DiscPair.cylPreimageHomeoOpen
import Submission.Work.Serre.cupIso_of_ne_zero_of_thomCylAt
import Submission.Work.Serre.isSerreFibration_restrictFibre
import Submission.Work.RatHurewicz.discPairFibreRestriction_of_fibreVisible
import Submission.Work.StemsB.AToolsR

/-!
# The local cup isomorphism over a piece of the base, from `ThomCylAt` over that piece

`Work.RatHurewicz.cupBijective_cylPre` provides the local bijectivity of the mixed cup product over
the part of the mapping cylinder over a *weakly contractible* open set `V` of the base.  For the
pieces of the Mayer–Vietoris cover of the cellular step that are **not** contractible — the
thickening `Work.Serre.cellU f ρ` of the old part (where the induction hypothesis is available) and
the union of the punctured half-balls (where `ThomCylAt` is available from the seeds) — the local
input is not weak contractibility but the statement `Work.Serre.ThomCylAt r N (q|_V)` itself.

This file supplies that variant: for any open `V ⊆ Γ` with `PathConnectedSpace ↥V` and
`ThomCylAt r N (q|_V)`, any non-zero relative class `U ∈ H^{r+1}(cyl q, range (cylIncl q))` has the
bijective mixed cup product with its restriction over `V`.

The proof is verbatim that of `Work.RatHurewicz.cupBijective_cylPre`, with the local model
`Work.Serre.DiscPair.thomCylAt_of_nonzero_class` (which needs weak contractibility) replaced by
`Work.Serre.cupIso_of_ne_zero_of_thomCylAt` (which needs `ThomCylAt` and `r ≤ N`).
-/

namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

noncomputable section

set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

/-- **The cup map over the part of the cylinder over an open set on which `ThomCylAt` holds is
bijective.** -/
theorem cupBijective_cylPre_of_thomCylAt (r N : ℕ) (hr : 1 ≤ r) (hN : r ≤ N)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ)
    {X : Type} [TopologicalSpace X] (q : C(X, Γ))
    (hq : Work.StemsB.IsSerreFibration q)
    (hpc : ∀ γ : Γ, PathConnectedSpace (Work.StemsB.fibre q γ))
    (hvan : ∀ γ : Γ, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Γ, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r
      ≅ ModuleCat.of ℚ ℚ))
    (V : Set Γ) (hVopen : IsOpen V) (hVpc : PathConnectedSpace ↥V)
    (hTh : Work.Serre.ThomCylAt r N (Work.Serre.restrictFibre q V))
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Work.Serre.cylBot q))
    (hU : U ≠ 0) :
    ∀ m : ℕ, m + r + 1 ≤ N + 1 →
      Function.Bijective (fun x : Work.Thom.Coh ℚ m ↥(Work.Serre.cylPre q V) =>
        (Work.Thom.mixedCupC ℚ (Work.Serre.DiscPair.cylPreBot q V) m (r + 1)) x
          ((Work.Thom.relCohMap
            (⟨Subtype.val, continuous_subtype_val⟩ :
              C(↥(Work.Serre.cylPre q V), Work.Serre.cyl q))
            (Work.Serre.DiscPair.cylPreBot q V) (Work.Serre.cylBot q)
            (fun x hx => hx) ℚ (r + 1)).hom U)) := by
  classical
  haveI := hVpc
  intro m hm
  -- the homeomorphism between the two presentations of the cylinder over the piece
  obtain ⟨e, hbot, hret⟩ := Work.Serre.DiscPair.cylPreimageHomeoOpen q V hVopen
  -- the restriction of `U` to the piece
  let z' : Work.Thom.RelCoh ℚ (r + 1) ↥(Work.Serre.cylPre q V)
      (Work.Serre.DiscPair.cylPreBot q V) :=
    (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(Work.Serre.cylPre q V), Work.Serre.cyl q))
      (Work.Serre.DiscPair.cylPreBot q V) (Work.Serre.cylBot q)
      (fun x hx => hx) ℚ (r + 1)).hom U
  obtain ⟨b₀⟩ := (inferInstance : Nonempty ↥V)
  have hz' : z' ≠ 0 :=
    cellwiseNonvanishing r N hr hN hΓ q hq hpc hvan hgen V b₀.1 b₀.2 U hU
  -- the transport of the class to the cylinder of the restriction
  have he : ∀ y ∈ Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)),
      e y ∈ Work.Serre.DiscPair.cylPreBot q V :=
    fun y hy => (hbot y).mp hy
  have hIsoRgen : ∀ n : ℕ, CategoryTheory.IsIso (Work.Thom.relCohMap e
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)))
      (Work.Serre.DiscPair.cylPreBot q V) he ℚ n) :=
    fun n => Work.Thom.CapGlue.isIso_relComplexMap_homeomorph
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)))
      (Work.Serre.DiscPair.cylPreBot q V) e hbot ℚ n
  have hIsoR := hIsoRgen (r + 1)
  let z : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl (Work.Serre.restrictFibre q V))
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V))) :=
    (Work.Thom.relCohMap e (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)))
      (Work.Serre.DiscPair.cylPreBot q V) he ℚ (r + 1)).hom z'
  have hz : z ≠ 0 := by
    have hb : Function.Injective (Work.Thom.relCohMap e
        (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)))
        (Work.Serre.DiscPair.cylPreBot q V) he ℚ (r + 1)).hom :=
      ((CategoryTheory.ConcreteCategory.isIso_iff_bijective _).mp hIsoR).1
    exact fun h0 => hz' (hb (by simpa using h0))
  -- the cup isomorphism in the cylinder world, for the specific class
  have hcupW := Work.Serre.cupIso_of_ne_zero_of_thomCylAt r N hr hN
    (Work.Serre.restrictFibre q V) hTh z hz m hm
  -- the notation
  let eC : C(Work.Serre.cyl (Work.Serre.restrictFibre q V), ↥(Work.Serre.cylPre q V)) :=
    ⟨e.toFun, e.continuous_toFun⟩
  -- the naturality identity
  have hnat : ∀ x : ↥(Work.Thom.Coh ℚ m ↥(Work.Serre.cylPre q V)),
      (Work.Thom.relCohMap e (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)))
        (Work.Serre.DiscPair.cylPreBot q V) he ℚ (m + (r + 1))).hom
        ((Work.Thom.mixedCupC ℚ (Work.Serre.DiscPair.cylPreBot q V) m (r + 1)) x z')
      = (Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)))
          m (r + 1)) ((Work.Thom.CohMap eC ℚ m).hom x) z :=
    fun x => Work.StemsB.mixedCupC_pairNaturalR (R := ℚ) eC
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)))
      (Work.Serre.DiscPair.cylPreBot q V) he m (r + 1) x z'
  -- the bijectivity of the cylinder-world cup map, for the specific class
  have hbS : Function.Bijective (Work.Thom.CohMap
      (Work.Serre.cylRetract (Work.Serre.restrictFibre q V)) ℚ m).hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective
      (Work.Thom.CohMap (Work.Serre.cylRetract (Work.Serre.restrictFibre q V)) ℚ m)).mp
      (Work.RatHurewicz.Dfr.isIso_CohMap_cylRetract (Work.Serre.restrictFibre q V) m)
  have hcomp : Function.Bijective (fun y : ↥(Work.Thom.Coh ℚ m ↥V) =>
      (Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)))
        m (r + 1))
        ((Work.Thom.CohMap (Work.Serre.cylRetract (Work.Serre.restrictFibre q V)) ℚ m).hom y)
        z) :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective
      (ModuleCat.ofHom (((Work.Thom.mixedCupC ℚ
          (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V))) m (r + 1))).flip z ∘ₗ
        (Work.Thom.CohMap (Work.Serre.cylRetract (Work.Serre.restrictFibre q V)) ℚ m).hom))).mp
      hcupW
  have hbz : Function.Bijective (fun y : ↥(Work.Thom.Coh ℚ m
      (Work.Serre.cyl (Work.Serre.restrictFibre q V))) =>
      (Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)))
        m (r + 1)) y z) :=
    ⟨hcomp.1.of_comp_right hbS.2,
      (Function.Surjective.of_comp_iff
        (fun y : ↥(Work.Thom.Coh ℚ m (Work.Serre.cyl (Work.Serre.restrictFibre q V))) =>
          (Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)))
            m (r + 1)) y z) hbS.2).mp hcomp.2⟩
  -- the transport of the bijectivity from the cylinder world to the piece
  have hbR : Function.Bijective (Work.Thom.relCohMap e
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)))
      (Work.Serre.DiscPair.cylPreBot q V) he ℚ (m + (r + 1))).hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective
      (Work.Thom.relCohMap e (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)))
        (Work.Serre.DiscPair.cylPreBot q V) he ℚ (m + (r + 1)))).mp (hIsoRgen _)
  have hbC : Function.Bijective (Work.Thom.CohMap eC ℚ m).hom :=
    (CategoryTheory.ConcreteCategory.isIso_iff_bijective (Work.Thom.CohMap eC ℚ m)).mp
      (Work.RatHurewicz.Dfr.isIso_CohMap_homeo e m)
  refine ⟨fun a b hab => ?_, fun y => ?_⟩
  · have hab' : (Work.Thom.mixedCupC ℚ (Work.Serre.DiscPair.cylPreBot q V) m (r + 1)) a z'
        = (Work.Thom.mixedCupC ℚ (Work.Serre.DiscPair.cylPreBot q V) m (r + 1)) b z' := hab
    have h1 : (Work.Thom.mixedCupC ℚ
          (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V))) m (r + 1))
          ((Work.Thom.CohMap eC ℚ m).hom a) z
        = (Work.Thom.mixedCupC ℚ
          (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V))) m (r + 1))
          ((Work.Thom.CohMap eC ℚ m).hom b) z := by
      calc (Work.Thom.mixedCupC ℚ
            (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V))) m (r + 1))
            ((Work.Thom.CohMap eC ℚ m).hom a) z
          = (Work.Thom.relCohMap e (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)))
              (Work.Serre.DiscPair.cylPreBot q V) he ℚ (m + (r + 1))).hom
              ((Work.Thom.mixedCupC ℚ (Work.Serre.DiscPair.cylPreBot q V) m (r + 1)) a z') :=
            (hnat a).symm
        _ = (Work.Thom.relCohMap e (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)))
              (Work.Serre.DiscPair.cylPreBot q V) he ℚ (m + (r + 1))).hom
              ((Work.Thom.mixedCupC ℚ (Work.Serre.DiscPair.cylPreBot q V) m (r + 1)) b z') := by
            rw [hab']
        _ = (Work.Thom.mixedCupC ℚ
              (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V))) m (r + 1))
              ((Work.Thom.CohMap eC ℚ m).hom b) z := hnat b
    exact hbC.1 (hbz.1 h1)
  · obtain ⟨v, hv⟩ := hbz.2 ((Work.Thom.relCohMap e
      (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)))
      (Work.Serre.DiscPair.cylPreBot q V) he ℚ (m + (r + 1))).hom y)
    obtain ⟨x, hx⟩ := hbC.2 v
    refine ⟨x, hbR.1 ?_⟩
    calc (Work.Thom.relCohMap e (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)))
          (Work.Serre.DiscPair.cylPreBot q V) he ℚ (m + (r + 1))).hom
          ((Work.Thom.mixedCupC ℚ (Work.Serre.DiscPair.cylPreBot q V) m (r + 1)) x z')
        = (Work.Thom.mixedCupC ℚ
            (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V))) m (r + 1))
            ((Work.Thom.CohMap eC ℚ m).hom x) z := hnat x
      _ = (Work.Thom.mixedCupC ℚ
            (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V))) m (r + 1)) v z := by
          rw [hx]
      _ = (Work.Thom.relCohMap e (Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)))
            (Work.Serre.DiscPair.cylPreBot q V) he ℚ (m + (r + 1))).hom y := hv

end

end Work.RatHurewicz
