import Mathlib
import Submission.Work.RatHurewicz.cupBijectiveOverPiece
import Submission.Work.Serre.DiscPair.cylPair_concentrated
import Submission.Work.Serre.DiscPair.relCoh_preimage_concentrated

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

/-- **The relative cohomology of the mapping cylinder over an open piece of the base is
concentrated in degree `r+1`, where it is a line.**

Let `q : C(X,Γ)` be a Serre fibration whose fibres are path connected and rationally `S^r` in the
range `≤ N` (`H_t(fibre;ℚ) = 0` for `0 < t ≤ N`, `t ≠ r`, and `H_r(fibre;ℚ) ≅ ℚ`), and let
`V ⊆ Γ` be an open, path connected, weakly contractible subset.  Then the pair

  `(cylPre q V, cylPreBot q V) = ((cylRetract q)⁻¹ V, {x | (x : cyl q) ∈ range (cylIncl q)})`

of the mapping cylinder has rational relative cohomology vanishing in every degree `j ≤ N+1` with
`j ≠ r+1`, and equal to `ℚ` in degree `r+1`.

The proof is `Work.Serre.DiscPair.cylPair_concentrated` applied to the restricted fibration
`q|_V : q⁻¹V → V`, transported across the homeomorphism of pairs
`Work.Serre.DiscPair.cylPreimageHomeoOpen` (the mapping cylinder of `q|_V` is the part of the
mapping cylinder of `q` over `V`).  Only the base point `b₀` is used in the hypotheses: `V` is
rationally acyclic by `Work.Serre.DiscPair.ratAcyclic_of_weaklyContractible_base`, and the rational
homology of `q⁻¹V` is computed by Serre's theorem over a weakly contractible base
(`Work.Serre.DiscPair.ratH_of_contractible_base`). -/
theorem relCoh_cylPre_concentrated {Γ : Type} [TopologicalSpace Γ] {X : Type} [TopologicalSpace X]
    (q : C(X, Γ)) (hq : Work.StemsB.IsSerreFibration q) (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    (hpc : ∀ γ : Γ, PathConnectedSpace (Work.StemsB.fibre q γ))
    (hvan : ∀ γ : Γ, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) t))
    (hgen : ∀ γ : Γ, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q γ)) r
      ≅ ModuleCat.of ℚ ℚ))
    (V : Set Γ) (hVopen : IsOpen V) (b₀ : ↥V)
    (hVc : ∀ j : ℕ, Subsingleton (HomotopyGroup (Fin j) ↥V b₀))
    (hVpc : PathConnectedSpace ↥V) :
    (∀ j : ℕ, j ≤ N + 1 → j ≠ r + 1 →
      CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j ↥(Work.Serre.cylPre q V)
        (Work.Serre.DiscPair.cylPreBot q V))) ∧
    Nonempty (Work.Thom.RelCoh ℚ (r + 1) ↥(Work.Serre.cylPre q V)
      (Work.Serre.DiscPair.cylPreBot q V) ≅ ModuleCat.of ℚ ℚ) := by
  classical
  -- The restricted fibration `q|_V : q⁻¹V → V`.
  let qV : C(↥(q ⁻¹' V), ↥V) := Work.Serre.restrictFibre q V
  have hSerrV : Work.StemsB.IsSerreFibration qV :=
    Work.Serre.isSerreFibration_restrictFibre q hq V
  -- The fibre data of `q|_V` is that of `q`.
  have hfd : Work.Serre.CWThom.FibreData r N qV :=
    Work.Serre.CWThom.fibreData_restrictFibre
      (fun b => ⟨fun t ht htr htN => hvan b t ht htr htN, hgen b⟩) V
  -- The fibre of `q|_V` over the base point `b₀` is path connected.
  have hpcV : PathConnectedSpace (Work.StemsB.fibre qV b₀) :=
    Work.Serre.CWThom.pathConnectedSpace_of_homeo
      (Work.Serre.CWThom.fibreHomeo_restrictFibre q V b₀).symm (hpc (b₀ : Γ))
  -- The total space of `q|_V` is path connected (path lifting).
  have hXV : PathConnectedSpace ↥(q ⁻¹' V) :=
    Work.Serre.DiscPair.pathConnectedSpace_preimage_of_isSerreFibration q hq hVpc (b₀ : Γ) b₀.2
      (hpc (b₀ : Γ))
  -- The base `V` is rationally acyclic, being weakly contractible.
  have hVacyc : Work.Serre.RatAcyclic ↥V :=
    Work.Serre.DiscPair.ratAcyclic_of_weaklyContractible_base b₀ hVpc (fun i => hVc i)
  -- The rational homology of `q⁻¹V` is concentrated in degree `r` (Serre).
  obtain ⟨hXvan, hXgen⟩ :=
    Work.Serre.DiscPair.ratH_of_contractible_base qV b₀ r N hr hrN hSerrV hVpc (fun i => hVc i)
      hXV hpcV (hfd b₀).1 (hfd b₀).2
  -- Hence the disc pair of `q|_V` is concentrated in degree `r+1`, where it is a line.
  obtain ⟨hconc, hline⟩ :=
    Work.Serre.DiscPair.cylPair_concentrated qV r N hr hVacyc hXV hXvan hXgen
  -- The mapping cylinder of `q|_V` is the part of `cyl q` over the open set `V`.
  obtain ⟨e, hbot, _⟩ := Work.Serre.DiscPair.cylPreimageHomeoOpen q V hVopen
  have hiso : ∀ n : ℕ, Nonempty (Work.Thom.RelCoh ℚ n ↥(Work.Serre.cylPre q V)
      (Work.Serre.DiscPair.cylPreBot q V) ≅ Work.Thom.RelCoh ℚ n (Work.Serre.cyl qV)
      (Set.range (Work.Serre.cylIncl qV))) :=
    fun n => Work.Thom.relCohHomeomorph (Set.range (Work.Serre.cylIncl qV))
      (Work.Serre.DiscPair.cylPreBot q V) e hbot ℚ n
  refine ⟨fun j hj hjne => ?_, ?_⟩
  · exact IsZero.of_iso (hconc j hj hjne) (hiso j).some
  · obtain ⟨iso⟩ := hiso (r + 1)
    exact ⟨iso ≪≫ hline.some⟩

end

end Work.Serre
