import Mathlib
import Submission.Work.Serre.DiscPair.fibreRestriction_of_contractible
import Submission.Work.Serre.DiscPair.cylPair_concentrated
import Submission.Work.Serre.relCoh_concentrated_of_ratAcyclic
import Submission.Work.Serre.DiscPair.cylPreimageRelChainsIso
import Submission.Work.Serre.DiscPair.ratH_of_contractible_base
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.Serre.DiscPair.pathConnectedSpace_preimage_of_isSerreFibration
import Submission.Work.Serre.isSerreFibration_restrictFibre
import Submission.Work.Serre.CWModelThomAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Concentration of the relative cohomology of the mapping cylinder over an open set

`Work.Serre.DiscPair.relCoh_preimage_concentrated`: let `q : C(X,B)` be a Serre fibration whose
fibres are path connected and rationally `S^r` in the range `≤ N` (`H_t(fibre;ℚ) = 0` for
`0 < t ≤ N`, `t ≠ r`, and `H_r(fibre;ℚ) ≅ ℚ`), and let `V ⊆ B` be an open *weakly contractible*
subset (path connected, all homotopy groups trivial).  Then the pair

  `((cylRetract q)⁻¹ V, (cylRetract q)⁻¹ V ∩ range (cylIncl q))`

of the mapping cylinder has vanishing rational relative cohomology in every degree `j ≤ N+1` with
`j ≠ r+1`.

Mathematically this is `Work.Serre.DiscPair.cylPair_concentrated` applied to the *restricted*
fibration `q|_V : q⁻¹V → V`:

* `V` is rationally acyclic, being path connected and weakly contractible
  (`ratAcyclic_of_weaklyContractible_base`);
* the total space `q⁻¹V` is path connected (path lifting, `pathConnectedSpace_preimage_…`) and,
  by Serre's theorem over a weakly contractible base (`ratH_of_contractible_base`), its rational
  homology is concentrated in degree `r` through degree `N`;
* the fibre data of `q|_V` is that of `q`, by the fibre homeomorphism
  `CWThom.fibreHomeo_restrictFibre` (`CWThom.fibreData_restrictFibre`).

The mapping cylinder of `q|_V` is the part of `cyl q` over the *open* set `V`: this is the
homeomorphism of pairs `cylPreHomeoOpen` below (the open companion of
`Work.Serre.DiscPair.cylPreimageHomeo`, which is stated for closed sets; it is reproved here
because the module `cylPreimageHomeoOpen` cannot be imported together with the current closure).
`Subsingleton` of relative cohomology transports along this homeomorphism of pairs
(`Work.Thom.relCohHomeomorph`).
-/

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-! ## The mapping cylinder of `q|_V` over an open set `V` -/

/-- **The mapping cylinder of `q|_V` is the part of the mapping cylinder of `q` over an open `V`**:
the map `cylPreimageLift q V` is a bijective quotient map, because the restriction of the quotient
map `cylMk q` to the *saturated open* set `cylPreSet q V = cylMk q ⁻¹' ((cylRetract q) ⁻¹' V)` is a
quotient map (`Topology.IsQuotientMap.restrictPreimage_isOpen`). -/
private def cylPreHomeoOpen {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (V : Set B) (hV : IsOpen V) :
    Work.Serre.cyl (Work.Serre.restrictFibre q V) ≃ₜ ↥((Work.Serre.cylRetract q) ⁻¹' V) :=
  (isHomeomorph_iff_isQuotientMap_injective.mpr
    ⟨isQuotientMap_cylPreimageLift q V
        (Topology.IsQuotientMap.restrictPreimage_isOpen (f := Work.Serre.cylMk q)
          isQuotientMap_quotient_mk' (hV.preimage (Work.Serre.cylRetract q).continuous)),
      cylPreimageLift_injective q V⟩).homeomorph (cylPreimageLift q V)

/-- The homeomorphism `cylPreHomeoOpen` matches the bottom copies of the two mapping cylinders. -/
private theorem cylPreHomeoOpen_range {B : Type} [TopologicalSpace B] {X : Type}
    [TopologicalSpace X] (q : C(X, B)) (V : Set B) (hV : IsOpen V)
    (y : Work.Serre.cyl (Work.Serre.restrictFibre q V)) :
    y ∈ Set.range (Work.Serre.cylIncl (Work.Serre.restrictFibre q V)) ↔
      ((cylPreHomeoOpen q V hV y : ↥((Work.Serre.cylRetract q) ⁻¹' V)) : Work.Serre.cyl q)
        ∈ Set.range (Work.Serre.cylIncl q) := by
  rw [show ((cylPreHomeoOpen q V hV y : ↥((Work.Serre.cylRetract q) ⁻¹' V)) : Work.Serre.cyl q)
      = (cylPreimageLift q V y : Work.Serre.cyl q) from rfl]
  exact (cylPreimageLift_range q V y).symm

/-! ## The main theorem -/

theorem relCoh_preimage_concentrated {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    (hq : Work.StemsB.IsSerreFibration q)
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre q b))
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) t))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b)) r ≅ ModuleCat.of ℚ ℚ))
    (V : Set B) (hV : IsOpen V) (hVpc : PathConnectedSpace ↥V)
    (hVc : ∀ (i : ℕ) (y : ↥V), Subsingleton (HomotopyGroup (Fin i) ↥V y)) :
    (∀ j : ℕ, j ≤ N + 1 → j ≠ r + 1 →
        CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j
          ↥((Work.Serre.cylRetract q) ⁻¹' V)
          {x : ↥((Work.Serre.cylRetract q) ⁻¹' V) |
            (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)})) := by
  classical
  -- The restricted fibration `q|_V : q⁻¹V → V`.
  let qV : C(↥(q ⁻¹' V), ↥V) := Work.Serre.restrictFibre q V
  have hSerrV : Work.StemsB.IsSerreFibration qV :=
    Work.Serre.isSerreFibration_restrictFibre q hq V
  -- The fibre data of `q|_V` is that of `q`.
  have hfd : Work.Serre.CWThom.FibreData r N qV :=
    Work.Serre.CWThom.fibreData_restrictFibre
      (fun b => ⟨fun t ht htr htN => hvan b t ht htr htN, hgen b⟩) V
  -- A base point of `V`, and the fibre of `q|_V` over it.
  obtain ⟨v₀⟩ := hVpc.nonempty
  have hpcV : PathConnectedSpace (Work.StemsB.fibre qV v₀) :=
    Work.Serre.CWThom.pathConnectedSpace_of_homeo
      (Work.Serre.CWThom.fibreHomeo_restrictFibre q V v₀).symm (hpc (v₀ : B))
  -- The total space is path connected (path lifting).
  have hXV : PathConnectedSpace ↥(q ⁻¹' V) :=
    pathConnectedSpace_preimage_of_isSerreFibration q hq hVpc (v₀ : B) v₀.2 (hpc (v₀ : B))
  -- The base is rationally acyclic, being weakly contractible.
  have hVacyc : Work.Serre.RatAcyclic ↥V :=
    ratAcyclic_of_weaklyContractible_base v₀ hVpc (fun i => hVc i v₀)
  -- The rational homology of the total space is concentrated in degree `r` (Serre).
  obtain ⟨hXvan, hXgen⟩ :=
    ratH_of_contractible_base qV v₀ r N hr hrN hSerrV hVpc (fun i => hVc i v₀) hXV hpcV
      (hfd v₀).1 (hfd v₀).2
  -- Hence the disc pair of `q|_V` is concentrated in degree `r+1`.
  obtain ⟨hconc, -⟩ := cylPair_concentrated qV r N hr hVacyc hXV hXvan hXgen
  -- The mapping cylinder of `q|_V` is the part of `cyl q` over the open set `V`.
  have hsub : ∀ j : ℕ, j ≤ N + 1 → j ≠ r + 1 →
      Subsingleton (Work.Thom.RelCoh ℚ j (Work.Serre.cyl qV)
        (Set.range (Work.Serre.cylIncl qV))) :=
    fun j hj hjne => ModuleCat.isZero_iff_subsingleton.mp (hconc j hj hjne)
  intro j hj hjne
  refine ModuleCat.isZero_iff_subsingleton.mpr ?_
  haveI := hsub j hj hjne
  obtain ⟨iso⟩ := Work.Thom.relCohHomeomorph
    (Set.range (Work.Serre.cylIncl qV))
    {x : ↥((Work.Serre.cylRetract q) ⁻¹' V) |
      (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}
    (cylPreHomeoOpen q V hV) (fun y => cylPreHomeoOpen_range q V hV y) ℚ j
  exact ⟨fun a b => iso.toLinearEquiv.injective (Subsingleton.elim _ _)⟩

end

end Work.Serre.DiscPair
