import Mathlib
import Submission.Work.StemsB.SerreExact
import Submission.Work.StemsB.HurewiczFibration
import Submission.Work.Serre.serreE2b
import Submission.Work.StemsB.serreExactSphereProp
import Submission.Work.StemsB.SerreSphereInfty
import Submission.Work.Serre.serreK2Int
import Submission.Work.RatHurewicz.Cofibre.AssemblyDefs
import Submission.Work.RatHurewicz.Cofibre.isIso_homologyMap_uMap
import Submission.Work.RatHurewicz.Cofibre.homologyMap_uMap_comp_relPairMap
import Submission.Work.RatHurewicz.Cofibre.isIso_homologyMap_psiMap
import Submission.Work.RatHurewicz.Cofibre.bijective_piMapN_cofibreCollapse
import Submission.Work.RatHurewicz.Cofibre.subsingleton_homology_zero_relChains

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped Topology unitInterval
open Work.RatHurewicz

namespace Work.RatHurewicz

/-- **The injectivity half of Serre's exact sequence in the stable range, in the connectivity regime `b = k`, `f = k+1`.** For a Hurewicz fibration `p : E → B` whose fibre `F = p ⁻¹' {p e₀}` is `k`-connected and whose base is a range model of `K(π_k, k)` up to degree `2k-1`, the map of pairs `(E, F) → (B, {p e₀})` is injective on homology in all degrees `i ≤ 2k-1`. -/
theorem fibrationPairMap_injective_stableRange {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsHurewiczFibration p) (e₀ : E) (k : ℕ) (hk : 2 ≤ k)
    (hmodel : ∀ j : ℕ, j ≤ 2 * k - 1 → j ≠ k →
      Subsingleton (HomotopyGroup (Fin j) B (p e₀)))
    (hconn : ∀ j : ℕ, j ≤ k → Subsingleton (HomotopyGroup (Fin j) (↥(p ⁻¹' {p e₀}))
      ⟨e₀, rfl⟩))
    (i : ℕ) (hi : i ≤ 2 * k - 1) :
    Function.Injective (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p (p e₀)) i).hom := by
  haveI : Nonempty E := ⟨e₀⟩
  haveI : Nonempty ↥(p ⁻¹' {p e₀}) := ⟨⟨e₀, rfl⟩⟩
  -- the base is path connected, by the range model hypothesis in degree `0`
  have hpcB : PathConnectedSpace B :=
    Work.Serre.pathConnectedSpace_of_subsingleton_pi0 B (p e₀)
      (hmodel 0 (by omega) (by omega))
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · -- degree `0`: the target `H₀(B, {p e₀})` is a subsingleton
    haveI hEpc : PathConnectedSpace ↥(TopCat.of E) :=
      Work.Cofibre.pathConnectedSpace_E_of_fibration p hp e₀ k hk hconn hmodel
    haveI h0 : Subsingleton ↥(HomologicalComplex.homology
        (Work.Cohomology.relChains (TopCat.of E) (p ⁻¹' {p e₀})) 0) :=
      Cofibre.subsingleton_homology_zero_relChains (TopCat.of E) (p ⁻¹' {p e₀})
    exact fun a b _ => Subsingleton.elim a b
  · have hi2k : i < 2 * k := by omega
    -- the `π`-data of the collapse `c : cofibre → B` in the range needed by `serreK2IntSharp`
    have hπ : ∀ j : ℕ, j < 2 * k → ∀ y : cofibre (setIncl (p ⁻¹' {p e₀})),
        Function.Bijective (Work.Serre.piMapN
          (cofibreCollapse (setIncl (p ⁻¹' {p e₀})) p (p e₀) (fun y => y.2)) j y) :=
      fun j hj y => Cofibre.bijective_piMapN_cofibreCollapse p hp e₀ k hk hmodel hconn j hj y
    have hcofibre : Nonempty (cofibre (setIncl (p ⁻¹' {p e₀}))) :=
      ⟨cofibreIncl (setIncl (p ⁻¹' {p e₀})) e₀⟩
    -- the square `u_* ≫ φ_* = exc_* ≫ ψ_*`
    have hsq := Cofibre.homologyMap_uMap_comp_relPairMap E B p e₀ i
    -- the three factors of `exc_* ≫ ψ_*` are isomorphisms
    haveI hu : IsIso (HomologicalComplex.homologyMap (Cofibre.uMap (p ⁻¹' {p e₀}) e₀) i) :=
      Cofibre.isIso_homologyMap_uMap E (p ⁻¹' {p e₀}) e₀ i
    haveI hex : IsIso (HomologicalComplex.homologyMap
        (Work.Cohomology.relChainsMap (TopCat.of (cofibre (setIncl (p ⁻¹' {p e₀}))))
          (cofibreU (setIncl (p ⁻¹' {p e₀}))) (cofibreV (setIncl (p ⁻¹' {p e₀})))) i) :=
      Work.Cohomology.excision_relChainsMap_isIso _ _ _
        (isOpen_cofibreU _) (isOpen_cofibreV _) (cofibreU_union_cofibreV _) i
    haveI hps : IsIso (HomologicalComplex.homologyMap (Cofibre.psiMap (setIncl (p ⁻¹' {p e₀}))
        (cofibreCollapse (setIncl (p ⁻¹' {p e₀})) p (p e₀) (fun y => y.2)) (p e₀)
        (Cofibre.cofibreCollapse_eq_of_mem_cofibreV (setIncl (p ⁻¹' {p e₀})) p (p e₀)
          (fun y => y.2))) i) :=
      Cofibre.isIso_homologyMap_psiMap (setIncl (p ⁻¹' {p e₀}))
        (cofibreCollapse (setIncl (p ⁻¹' {p e₀})) p (p e₀) (fun y => y.2)) (p e₀)
        (Cofibre.cofibreCollapse_eq_of_mem_cofibreV (setIncl (p ⁻¹' {p e₀})) p (p e₀) (fun y => y.2))
        hcofibre hpcB (2 * k) hπ i hi0 hi2k
    -- hence `φ_*` is an isomorphism (the composite `u_* ≫ φ_*` is, and `u_*` is)
    have hcomp : IsIso (HomologicalComplex.homologyMap (Cofibre.uMap (p ⁻¹' {p e₀}) e₀) i
        ≫ HomologicalComplex.homologyMap (Work.StemsB.relPairMap p (p e₀)) i) :=
      hsq.symm ▸ IsIso.comp_isIso' hex hps
    haveI : IsIso (HomologicalComplex.homologyMap (Cofibre.uMap (p ⁻¹' {p e₀}) e₀) i
        ≫ HomologicalComplex.homologyMap (Work.StemsB.relPairMap p (p e₀)) i) := hcomp
    haveI hφ : IsIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p (p e₀)) i) :=
      IsIso.of_isIso_comp_left (HomologicalComplex.homologyMap (Cofibre.uMap (p ⁻¹' {p e₀}) e₀) i)
        (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p (p e₀)) i)
    exact (ModuleCat.mono_iff_injective _).mp (IsIso.mono_of_iso _)

end Work.RatHurewicz
