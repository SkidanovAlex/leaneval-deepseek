import Mathlib
import Submission.Work.Serre.RangeEMVanDefs
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.Serre.serreConnectedCover
import Submission.Work.Serre.serreAttachCompress
import Submission.Work.Serre.serreAttachKillPi
import Submission.Work.RatHurewicz.AttachCells
import Submission.Work.RatHurewicz.attachCells_extension
import Submission.Work.RatHurewicz.exists_killed_tower
import Submission.Work.RatHurewicz.compression_of_relPiVanishing
import Submission.Work.RatHurewicz.CompressRelToRelPi
import Submission.Work.RatHurewicz.AttachPush.CellInterior
import Submission.Work.Serre.serreE2b
import Submission.Work.Serre.serreE0Range
import Submission.Work.Serre.Engine
import Submission.Work.Serre.C1Pair
import Submission.Work.Serre.C1Rat
import Submission.Work.Serre.RangeOne.Comparison
import Submission.Work.Serre.RangeOne.Defs
import Submission.Work.Serre.RangeOne.rangeWhitehead
import Submission.Work.Serre.RangeOne.colimModel

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `RangeEMVanOne` — the `1`-type range form of C3

The target of this file, `Work.Serre.RangeEMVanOne`, is the range form of the acyclicity of
`K(A,1)` for torsion `A`: a connected space with torsion abelian `π₁` and vanishing `πᵢ`
(`2 ≤ i ≤ N`) has `H_t(-;ℚ) = 0` for `0 < t ≤ N-1`.  `SerreC3` provides the *genuine* statement
(models of `K(A,1)` with all higher homotopy groups vanishing) and `SerreC0` the existence of such
models; the content of this file is the **comparison of a range model with a genuine one**.

## The route

1. `Work.Serre.isIso_ratHomologyMap_of_piMapN_bijective` (the clean "range Whitehead"): a map which
   is a bijection on `πᵢ` for `i ≤ M` (at every base point) induces an isomorphism on rational
   homology in degrees `< M`.  It is the mapping-cylinder argument of `Work.Serre.cylRelPi`
   combined with the compression/`SerreE2b` comparison
   `Work.Serre.isIso_ratHomologyMap_setIncl_of_compressRel`.
2. `Work.Serre.RangeModelComparison N W w₀` (the comparison input): a *genuine* model of `K(π₁W,1)`
   receiving a map from `W` which is a `π`-isomorphism up to `N`.  It is obtained from the
   *infinite* truncation tower `Work.RatHurewicz.towerState` (which is defined for every stage
   `s : ℕ`) by passing to the **colimit**: the colimit has `π₁ ≅ π₁(W)` and vanishing higher
   homotopy groups (a cube into the colimit factors through a stage), and the map `W → colimit`
   is a `π`-isomorphism in every degree.
3. `SerreC3` applies to the genuine model of step 2 and gives its rational acyclicity; combining
   with step 1 yields `H_t(W;ℚ) = 0` in the range.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section



/-- **The range form of C3 follows from the comparison input and the genuine statement `C3`.** -/
theorem rangeEMVanOne_of_comparison (hC3 : SerreC3)
    (hcmp : ∀ (N : ℕ) (W : Type) [TopologicalSpace W] (w₀ : W),
      Subsingleton (HomotopyGroup (Fin 0) W w₀) →
      (∀ a b : HomotopyGroup (Fin 1) W w₀, a * b = b * a) →
      (∀ α : HomotopyGroup (Fin 1) W w₀, ∃ K : ℕ, 0 < K ∧ α ^ K = 1) →
      (∀ i : ℕ, 2 ≤ i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) W w₀)) →
      RangeModelComparison N W w₀) :
    RangeEMVanOne := by
  intro N W _ w₀ h0 hcomm htors hvan t ht htN
  have hN : 2 ≤ N := by omega
  haveI : Nonempty W := ⟨w₀⟩
  obtain ⟨Z, tZ, pt, f, hgen, hbij⟩ := hcmp N W w₀ h0 hcomm htors hvan
  rcases hgen with ⟨hne, hhigh⟩
  obtain ⟨e⟩ := hne
  letI : TopologicalSpace Z := tZ
  -- the additive commutative group structure required by `SerreC3`
  letI hGr : Group (HomotopyGroup (Fin 1) W w₀) := HomotopyGroup.group (Fin 1)
  letI : CommGroup (HomotopyGroup (Fin 1) W w₀) := { hGr with mul_comm := hcomm }
  have hIsEM : IsEMSpace (Additive (HomotopyGroup (Fin 1) W w₀)) 1 (by norm_num) Z pt :=
    ⟨⟨e⟩, hhigh⟩
  have htor : Work.RatHurewicz.IsTorsionGroupAdd (Additive (HomotopyGroup (Fin 1) W w₀)) := by
    intro a
    obtain ⟨K, hK, hK1⟩ := htors a
    exact ⟨K, hK, hK1⟩
  have hacyc : RatAcyclic Z := hC3 _ htor 1 (by norm_num) Z pt hIsEM
  have hiso : IsIso (ratHomologyMap f t) :=
    Work.Serre.RangeOne.rangeWhitehead W Z w₀ f N (fun i hi x => hbij i hi x) t (by omega)
  exact IsZero.of_iso (hacyc.isZero_ratH ht) (asIso (ratHomologyMap f t))


theorem serreRangeEMVanOne (hC0 : Work.Serre.SerreC0) (hC3 : Work.Serre.SerreC3) :
    Work.Serre.RangeEMVanOne :=
  rangeEMVanOne_of_comparison hC3
    (fun N W _ w₀ h0 hcomm htors hvan =>
      Work.Serre.RangeOne.colimModel N W w₀ h0 hcomm htors hvan)

end

end Work.Serre
