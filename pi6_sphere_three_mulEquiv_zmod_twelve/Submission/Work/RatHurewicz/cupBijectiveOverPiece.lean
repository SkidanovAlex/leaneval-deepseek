import Mathlib
import Submission.Work.RatHurewicz.cellwiseNonvanishing
import Submission.Work.Serre.DiscPair.cylPreimageHomeoOpen
import Submission.Work.Serre.DiscPair.thomCylAt_of_nonzero_class
import Submission.Work.Serre.CWModelThomAux
import Submission.Work.Serre.isSerreFibration_restrictFibre
import Submission.Work.Serre.DiscPair.pathConnectedSpace_preimage_of_isSerreFibration
import Submission.Work.RatHurewicz.discPairFibreRestriction_of_fibreVisible
import Submission.Work.StemsB.AToolsR
import Submission.Work.RatHurewicz.csrOpenBallContractible

namespace Work.RatHurewicz

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval

noncomputable section

set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The local cup isomorphism over a weakly contractible piece of the base

`Work.RatHurewicz.cupBijective_cylPre` is the *local* input of the Mayer--Vietoris gluing
(`Work.Serre.glueCupIso`) for the cellular step of the CW-model Thom case: over the part of the
mapping cylinder lying over a weakly contractible open set `V` of the base, the mixed cup product
with the *restriction of any non-zero relative class* is bijective in the range.

## Why this is the local input, and how it avoids the multiplicative local model

The two ingredients are

* `Work.RatHurewicz.cellwiseNonvanishing`: a non-zero relative class of a Serre fibration with
  rationally spherical fibres restricts to a non-zero class over `V` (this is the `IH`-free fibre
  non-vanishing `fibreNonvanishingFree` together with functoriality of `relCohMap`);
* `Work.Serre.DiscPair.thomCylAt_of_nonzero_class`: over a *weakly contractible* base **every**
  non-zero relative class of a spherical Serre fibration is a Thom class (its mixed cup product
  with the pullback along the cylinder retraction is an isomorphism).

Because the second statement is available for the *specific* transported class, no comparison with
a chosen "local model" class is needed: the scalar ambiguity in the local Thom class (which is what
makes the multiplicative cell comparison `TM(D)` hard) never has to be resolved.  The remaining
transports are the homeomorphism `Work.Serre.DiscPair.cylPreimageHomeoOpen` between the part of the
cylinder over `V` and the cylinder of the restriction `q|_V`, the naturality of the mixed cup
product along it (`Work.StemsB.mixedCupC_pairNaturalR`), and the fact that the pullback along a
homeomorphism and along the retraction of a mapping cylinder are isomorphisms
(`Work.RatHurewicz.Dfr.isIso_CohMap_homeo`, `..._cylRetract`).

`Work.RatHurewicz.csrOpenBallCupBijective` is the instance used by the cellular step: the pieces of
the Mayer--Vietoris cover are the open half-balls `csrOpenBall i` of the attached cells, which are
weakly contractible and path connected by `Work.RatHurewicz.csrOpenBallContractible`.
-/

/-- **The cup map over the part of the cylinder over a weakly contractible open set is bijective.**
For a Serre fibration `q : X → Γ` with path connected, rationally `S^r`-through-`N` fibres, an open
set `V ⊆ Γ` that is weakly contractible and path connected, and any non-zero relative class
`U ∈ H^{r+1}(cyl q, range (cylIncl q))`, the mixed cup product with the restriction of `U` to the
part over `V` is a bijection `H^m(↥(cylPre q V)) ≅ H^{m+r+1}(↥(cylPre q V), ↥(cylPre q V) ∩ A)` for
`m + r + 1 ≤ N + 1`. -/
theorem cupBijective_cylPre (r N : ℕ) (hr : 1 ≤ r)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ)
    {X : Type} [TopologicalSpace X] (q : C(X, Γ))
    (hq : Work.StemsB.IsSerreFibration q)
    (hpc : ∀ γ : Γ, PathConnectedSpace (Work.StemsB.fibre q γ))
    (hvan : ∀ γ : Γ, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Γ, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r
      ≅ ModuleCat.of ℚ ℚ))
    (V : Set Γ) (hVopen : IsOpen V) (b₀ : ↥V)
    (hVc : ∀ j : ℕ, Subsingleton (HomotopyGroup (Fin j) ↥V b₀))
    (hVpc : PathConnectedSpace ↥V)
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
  intro m hm
  have hrN : r ≤ N := by omega
  -- the restricted fibration over the piece
  have hp : Work.StemsB.IsSerreFibration (Work.Serre.restrictFibre q V) :=
    Work.Serre.isSerreFibration_restrictFibre q hq V
  -- the homeomorphism between the two presentations of the cylinder over the piece
  obtain ⟨e, hbot, hret⟩ := Work.Serre.DiscPair.cylPreimageHomeoOpen q V hVopen
  -- the fibre data
  have hfd : Work.Serre.CWThom.FibreData r N q := fun γ => ⟨hvan γ, hgen γ⟩
  have hfdV : Work.Serre.CWThom.FibreData r N (Work.Serre.restrictFibre q V) :=
    Work.Serre.CWThom.fibreData_restrictFibre hfd V
  -- path connectedness of the total space over the piece
  have hX : PathConnectedSpace ↥(q ⁻¹' V) :=
    Work.Serre.DiscPair.pathConnectedSpace_preimage_of_isSerreFibration q hq hVpc b₀.1 b₀.2
      (hpc b₀.1)
  -- path connectedness of the fibre of the restriction at `b₀`
  have hpcV : PathConnectedSpace (Work.StemsB.fibre (Work.Serre.restrictFibre q V) b₀) :=
    Work.Serre.CWThom.pathConnectedSpace_of_homeo
      (Work.Serre.CWThom.fibreHomeo_restrictFibre q V b₀).symm (hpc b₀.1)
  -- the restriction of `U` to the piece
  let z' : Work.Thom.RelCoh ℚ (r + 1) ↥(Work.Serre.cylPre q V)
      (Work.Serre.DiscPair.cylPreBot q V) :=
    (Work.Thom.relCohMap
      (⟨Subtype.val, continuous_subtype_val⟩ :
        C(↥(Work.Serre.cylPre q V), Work.Serre.cyl q))
      (Work.Serre.DiscPair.cylPreBot q V) (Work.Serre.cylBot q)
      (fun x hx => hx) ℚ (r + 1)).hom U
  have hz' : z' ≠ 0 :=
    cellwiseNonvanishing r N hr hrN hΓ q hq hpc hvan hgen V b₀.1 b₀.2 U hU
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
  have hcupW := Work.Serre.DiscPair.thomCylAt_of_nonzero_class
    (Work.Serre.restrictFibre q V) b₀ r N hr hp hVpc hVc hX hpcV
    (fun t ht htr htN => (hfdV b₀).1 t ht htr htN) (hfdV b₀).2 z hz m hm
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
        (Work.Thom.CohMap (Work.Serre.cylRetract (Work.Serre.restrictFibre q V)) ℚ m).hom))).mp hcupW
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
/-- **The cup map over the open half-ball of an attached cell.**  The cellular-step instance of
`Work.RatHurewicz.cupBijective_cylPre`: the open half-balls `csrOpenBall i` are weakly contractible
and path connected (`Work.RatHurewicz.csrOpenBallContractible`). -/
theorem csrOpenBallCupBijective (r N D : ℕ) (hr : 1 ≤ r)
    {Γ : Type} [TopologicalSpace Γ] (hΓ : PathConnectedSpace Γ) (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D - 2), Γ))
    {X : Type} [TopologicalSpace X] (q : C(X, Work.RatHurewicz.attachCells (D - 2) Γ ι f))
    (hq : Work.StemsB.IsSerreFibration q)
    (hpc : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      PathConnectedSpace (Work.StemsB.fibre q γ))
    (hvan : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Work.RatHurewicz.attachCells (D - 2) Γ ι f,
      Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r ≅ ModuleCat.of ℚ ℚ))
    (i : ι)
    (U : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Work.Serre.cylBot q))
    (hU : U ≠ 0) :
    ∀ m : ℕ, m + r + 1 ≤ N + 1 →
      Function.Bijective (fun x : Work.Thom.Coh ℚ m
          ↥(Work.Serre.cylPre q (Work.Serre.csrOpenBall (D - 2) Γ ι f i)) =>
        (Work.Thom.mixedCupC ℚ
          (Work.Serre.DiscPair.cylPreBot q (Work.Serre.csrOpenBall (D - 2) Γ ι f i)) m (r + 1)) x
          ((Work.Thom.relCohMap
            (⟨Subtype.val, continuous_subtype_val⟩ :
              C(↥(Work.Serre.cylPre q (Work.Serre.csrOpenBall (D - 2) Γ ι f i)), Work.Serre.cyl q))
            (Work.Serre.DiscPair.cylPreBot q (Work.Serre.csrOpenBall (D - 2) Γ ι f i))
            (Work.Serre.cylBot q) (fun x hx => hx) ℚ (r + 1)).hom U)) := by
  obtain ⟨b₀, hVc, hVpc⟩ := Work.RatHurewicz.csrOpenBallContractible (D - 2) Γ ι f i
  exact cupBijective_cylPre (r := r) (N := N) (hr := hr)
    (Γ := Work.RatHurewicz.attachCells (D - 2) Γ ι f)
    (hΓ := Work.Serre.CWModel.pathConnectedSpace_attachCells (D - 2) Γ ι f)
    (X := X) (q := q) (hq := hq) (hpc := hpc) (hvan := hvan) (hgen := hgen)
    (V := Work.Serre.csrOpenBall (D - 2) Γ ι f i)
    (hVopen := (Work.Serre.csrGeom (D - 2) Γ ι f).1 i)
    (b₀ := b₀) (hVc := hVc) (hVpc := hVpc) (U := U) (hU := hU)

end

end Work.RatHurewicz
