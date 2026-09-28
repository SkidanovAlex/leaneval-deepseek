import Mathlib
import Submission.Work.StemsB.FibreTransport
import Submission.Work.StemsB.FibreTrivial
import Submission.Work.Cohomology.MVCohomology
import Submission.Work.Cohomology.homotopyEquiv

/-!
# The cohomology of the fibres of a Hurewicz fibration over the ends of a path

`Submission/Work/StemsB/FibreTransport.lean` proves the *homological* statement: for a Hurewicz
fibration `p : E → B` and a path `γ : I → B`, the fibre homology `H_j(p⁻¹(γ 0))` and
`H_j(p⁻¹(γ 1))` are isomorphic for every `j`, so that the fibre homology does not depend on the
point of the (path connected) base.

This module proves the corresponding statement for singular **cohomology**, by the same chain of
steps:

* `H^j(p⁻¹(γ 0)) ≅ H^j(fibre of the pullback over 0)` — the two fibres are literally the same
  subspace, and the two inclusion maps are mutually inverse;
* `H^j(fibre of the pullback over 0) ≅ H^j(Pullback p γ)` — the pullback is a Hurewicz fibration
  over the contractible base `I`, so it is trivial over `0` (and over `1`), i.e. the fibre is a
  homotopy retract of the total space;
* `H^j(Pullback p γ) ≅ H^j(fibre of the pullback over 1)` — same, triviality over `1`;
* `H^j(fibre of the pullback over 1) ≅ H^j(p⁻¹(γ 1))`.

Each step is an isomorphism on singular cohomology induced by a map which is a homotopy
equivalence, by `Work.Cohomology.homotopyEquiv` (homotopy invariance of singular cohomology).  The
composite is the statement below, which is what makes the cohomological invariants of the fibre of a
Hurewicz fibration (in particular the Chern classes and Pontryagin classes of its vertical tangent
bundle) independent of the chosen point of a path connected base.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

namespace Work.StemsB

noncomputable section

/-- **The cohomology of the fibres of a Hurewicz fibration does not depend on the point of the base,
along a path.**  For `p : E → B` a Hurewicz fibration, `γ : I → B` a path and `j : ℕ`, the
`j`-th singular cohomology of the fibre over `γ 0` is isomorphic to that of the fibre over `γ 1`. -/
theorem nonempty_singularCohomology_iso_fibre_of_path {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (hp : IsHurewiczFibration p) (γ : C(unitInterval, B))
    (j : ℕ) :
    Nonempty ((Work.Cohomology.singularCohomology ℤ j (TopCat.of ↥(p ⁻¹' {γ 0}))) ≅
      (Work.Cohomology.singularCohomology ℤ j (TopCat.of ↥(p ⁻¹' {γ 1})))) := by
  -- Step 1: `p⁻¹(γ 0)` and the fibre of the pullback over `0` are the same subspace.
  haveI h1 : IsIso (Work.Cohomology.singularCohomologyMap ℤ
      (TopCat.of ↥(p ⁻¹' {γ 0})) (TopCat.of (fibre (pullbackSnd p γ) 0))
      (TopCat.ofHom (fibreZeroHomInv p γ)) j) :=
    Work.Cohomology.homotopyEquiv ℤ (TopCat.of ↥(p ⁻¹' {γ 0}))
      (TopCat.of (fibre (pullbackSnd p γ) 0)) (TopCat.ofHom (fibreZeroHomInv p γ))
      (TopCat.ofHom (fibreZeroHom p γ))
      (topCatHomotopyOf (X := TopCat.of ↥(p ⁻¹' {γ 0}))
        (Y := TopCat.of (fibre (pullbackSnd p γ) 0))
        (f := TopCat.ofHom (fibreZeroHomInv p γ)) (g := TopCat.ofHom (fibreZeroHom p γ))
        ⟨fun z => z.1, continuous_fst⟩ (fun _ => rfl) (fun x => by
          show x = fibreZeroHom p γ (fibreZeroHomInv p γ x)
          exact (fibreZeroHom_comp_inv p γ x).symm))
      (topCatHomotopyOf (X := TopCat.of (fibre (pullbackSnd p γ) 0))
        (Y := TopCat.of ↥(p ⁻¹' {γ 0})) (f := TopCat.ofHom (fibreZeroHom p γ))
        (g := TopCat.ofHom (fibreZeroHomInv p γ)) ⟨fun z => z.1, continuous_fst⟩
        (fun _ => rfl) (fun x => by
          show x = fibreZeroHomInv p γ (fibreZeroHom p γ x)
          exact (fibreZeroHomInv_comp p γ x).symm)) j
  -- Step 2: the fibre over `0` of the pullback is a deformation retract of the total space.
  haveI h2 : IsIso (Work.Cohomology.singularCohomologyMap ℤ
      (TopCat.of (fibre (pullbackSnd p γ) 0)) (TopCat.of (Pullback p γ))
      (TopCat.ofHom (fibreIncl (pullbackSnd p γ) 0)) j) :=
    Work.Cohomology.homotopyEquiv ℤ (TopCat.of (fibre (pullbackSnd p γ) 0))
      (TopCat.of (Pullback p γ)) (TopCat.ofHom (fibreIncl (pullbackSnd p γ) 0))
      (TopCat.ofHom (pzG p hp γ))
      (topCatHomotopyOf (X := TopCat.of (fibre (pullbackSnd p γ) 0))
        (Y := TopCat.of (Pullback p γ)) (f := TopCat.ofHom (fibreIncl (pullbackSnd p γ) 0))
        (g := TopCat.ofHom (pzG p hp γ)) (pzHfib p hp γ)
        (fun x => pzHfib_zero p hp γ x) (fun x => pzHfib_one p hp γ x))
      (topCatHomotopyOf (X := TopCat.of (Pullback p γ))
        (Y := TopCat.of (fibre (pullbackSnd p γ) 0)) (f := TopCat.ofHom (pzG p hp γ))
        (g := TopCat.ofHom (fibreIncl (pullbackSnd p γ) 0)) (pzH p hp γ)
        (fun x => pzH_zero p hp γ x) (fun x => pzH_one p hp γ x)) j
  -- Step 3: the fibre over `1` of the pullback is a deformation retract of the total space.
  haveI h3 : IsIso (Work.Cohomology.singularCohomologyMap ℤ
      (TopCat.of (Pullback p γ)) (TopCat.of (fibre (pullbackSnd p γ) 1))
      (TopCat.ofHom (poG p hp γ)) j) :=
    Work.Cohomology.homotopyEquiv ℤ (TopCat.of (Pullback p γ))
      (TopCat.of (fibre (pullbackSnd p γ) 1)) (TopCat.ofHom (poG p hp γ))
      (TopCat.ofHom (fibreIncl (pullbackSnd p γ) 1))
      (topCatHomotopyOf (X := TopCat.of (Pullback p γ))
        (Y := TopCat.of (fibre (pullbackSnd p γ) 1)) (f := TopCat.ofHom (poG p hp γ))
        (g := TopCat.ofHom (fibreIncl (pullbackSnd p γ) 1)) (poH p hp γ)
        (fun x => poH_zero p hp γ x) (fun x => poH_one p hp γ x))
      (topCatHomotopyOf (X := TopCat.of (fibre (pullbackSnd p γ) 1))
        (Y := TopCat.of (Pullback p γ)) (f := TopCat.ofHom (fibreIncl (pullbackSnd p γ) 1))
        (g := TopCat.ofHom (poG p hp γ)) (poHfib p hp γ)
        (fun x => poHfib_zero p hp γ x) (fun x => poHfib_one p hp γ x)) j
  -- Step 4: `p⁻¹(γ 1)` and the fibre of the pullback over `1` are the same subspace.
  haveI h4 : IsIso (Work.Cohomology.singularCohomologyMap ℤ
      (TopCat.of ↥(p ⁻¹' {γ 1})) (TopCat.of (fibre (pullbackSnd p γ) 1))
      (TopCat.ofHom (fibreOneHomInv p γ)) j) :=
    Work.Cohomology.homotopyEquiv ℤ (TopCat.of ↥(p ⁻¹' {γ 1}))
      (TopCat.of (fibre (pullbackSnd p γ) 1)) (TopCat.ofHom (fibreOneHomInv p γ))
      (TopCat.ofHom (fibreOneHom p γ))
      (topCatHomotopyOf (X := TopCat.of ↥(p ⁻¹' {γ 1}))
        (Y := TopCat.of (fibre (pullbackSnd p γ) 1))
        (f := TopCat.ofHom (fibreOneHomInv p γ)) (g := TopCat.ofHom (fibreOneHom p γ))
        ⟨fun z => z.1, continuous_fst⟩ (fun _ => rfl) (fun x => by
          show x = fibreOneHom p γ (fibreOneHomInv p γ x)
          exact (fibreOneHom_comp_inv p γ x).symm))
      (topCatHomotopyOf (X := TopCat.of (fibre (pullbackSnd p γ) 1))
        (Y := TopCat.of ↥(p ⁻¹' {γ 1})) (f := TopCat.ofHom (fibreOneHom p γ))
        (g := TopCat.ofHom (fibreOneHomInv p γ)) ⟨fun z => z.1, continuous_fst⟩
        (fun _ => rfl) (fun x => by
          show x = fibreOneHomInv p γ (fibreOneHom p γ x)
          exact (fibreOneHomInv_comp p γ x).symm)) j
  exact ⟨(asIso (Work.Cohomology.singularCohomologyMap ℤ
      (TopCat.of ↥(p ⁻¹' {γ 0})) (TopCat.of (fibre (pullbackSnd p γ) 0))
      (TopCat.ofHom (fibreZeroHomInv p γ)) j)).symm ≪≫
    (asIso (Work.Cohomology.singularCohomologyMap ℤ
      (TopCat.of (fibre (pullbackSnd p γ) 0)) (TopCat.of (Pullback p γ))
      (TopCat.ofHom (fibreIncl (pullbackSnd p γ) 0)) j)).symm ≪≫
    (asIso (Work.Cohomology.singularCohomologyMap ℤ
      (TopCat.of (Pullback p γ)) (TopCat.of (fibre (pullbackSnd p γ) 1))
      (TopCat.ofHom (poG p hp γ)) j)).symm ≪≫
    (asIso (Work.Cohomology.singularCohomologyMap ℤ
      (TopCat.of ↥(p ⁻¹' {γ 1})) (TopCat.of (fibre (pullbackSnd p γ) 1))
      (TopCat.ofHom (fibreOneHomInv p γ)) j))⟩

end

end Work.StemsB
