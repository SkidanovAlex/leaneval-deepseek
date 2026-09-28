import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.DiscPair.centreConePair
import Submission.Work.Serre.DiscPair.centreConePairZero
import Submission.Work.StemsB.RelCochainDualR
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.StemsB.Periodicity
import Submission.Work.RatHurewicz.Cofibre.subsingleton_homology_zero_relChains
import Submission.Work.RatHurewicz.Cofibre.isIso_beta_of_contractible_subspace
import Submission.Work.StemsB.WangCohRat
import Submission.Work.Serre.Csr.Base

namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-! ## Two elementary bridges -/

/-- The `ℚ`-dual of a zero module is zero. -/
theorem isZero_dual_rat {M : ModuleCat ℚ} (h : IsZero M) :
    IsZero (ModuleCat.of ℚ (↥M →ₗ[ℚ] ℚ)) :=
  ModuleCat.isZero_iff_subsingleton.mpr
    ⟨fun f g => LinearMap.ext fun x => by
      haveI : Subsingleton ↥M := ModuleCat.isZero_iff_subsingleton.mp h
      rw [Subsingleton.elim x 0]
      simp⟩

/-- **Vanishing of relative homology implies vanishing of relative cohomology** over `ℚ`, by the
two halves of the universal coefficient theorem (`Work.StemsB.relComplexIsoDualR` and
`Work.StemsB.fieldDualUCT`). -/
theorem isZero_relCoh_of_isZero_relH {X : Type} [TopologicalSpace X] (A : Set X) (n : ℕ)
    (h : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of X) A).homology n)) :
    IsZero (Work.Thom.RelCoh ℚ n X A) := by
  obtain ⟨e⟩ := Work.StemsB.relComplexIsoDualR ℚ (TopCat.of X) A
  obtain ⟨g⟩ := Work.StemsB.fieldDualUCT ℚ (Work.StemsB.relChainsR ℚ (TopCat.of X) A) n
  exact IsZero.of_iso (isZero_dual_rat h) ((HomologicalComplex.homologyMapIso e n).trans g)

/-! ## The reduced rational homology of a path connected space

For a path connected space `X` and a point `b : X`, the reduced homology `H̃_k(X;ℚ) = H_k(X,{b};ℚ)`
is `H_k(X;ℚ)` for `k ≥ 1` and `0` for `k = 0`.  The positive-degree statement is the rational
image of the integral comparison `β : H_k(X;ℤ) → H_k(X,{b};ℤ)` (an isomorphism as soon as `{b}` is
contractible), and the degree-`0` statement is the elementary fact that `H_0(X,{b}) = 0` for `X`
path connected. -/

/-- **The reduced rational `H_0` of a path connected space vanishes.** -/
theorem isZero_relChainsR_point_zero (X : Type) [TopologicalSpace X] [PathConnectedSpace X]
    (b : X) :
    IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of X) ({b} : Set X)).homology 0) :=
  Work.Serre.Csr.isZero_relChainsR_rat_of_isZero_int (TopCat.of X) ({b} : Set X) 0
    (ModuleCat.isZero_iff_subsingleton.mpr
      (Work.RatHurewicz.Cofibre.subsingleton_homology_zero_relChains
        (TopCat.of X) ({b} : Set X)))

/-- **The reduced rational homology of a path connected space in positive degrees.**  For `k ≠ 0`,
the relative group `H_k(X,{b};ℚ)` of a path connected space `X` is `H_k(X;ℚ)`: the inclusion
`{b} ↪ X` induces an isomorphism `β_k : H_k(X;ℤ) ≅ H_k(X,{b};ℤ)` because `{b}` is contractible
(`Work.RatHurewicz.Cofibre.isIso_beta_of_contractible_subspace`), and base change to `ℚ` preserves
isomorphisms and homology. -/
theorem isZero_relChainsR_point_of_isZero_ratH (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] (b : X) (k : ℕ) (hk : k ≠ 0)
    (h : IsZero (Work.Serre.ratH (TopCat.of X) k)) :
    IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of X) ({b} : Set X)).homology k) := by
  -- base change of the vanishing in degree `k`
  have hZ : IsZero (Work.StemsB.IntRatF.obj
      ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology k)) :=
    IsZero.of_iso h (Work.StemsB.homologyBaseChangeRat (TopCat.of X) k).symm
  -- the integral middle map of the pair sequence is an isomorphism
  haveI : IsIso (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π
        (Work.Cohomology.inclChains (TopCat.of X) ({b} : Set X))) k) :=
    Work.RatHurewicz.Cofibre.isIso_beta_of_contractible_subspace
      (TopCat.of X) ({b} : Set X) k hk
  -- hence so is its base change
  have h2 : IsZero (Work.StemsB.IntRatF.obj
      ((Work.Cohomology.relChains (TopCat.of X) ({b} : Set X)).homology k)) :=
    IsZero.of_iso hZ (Work.StemsB.IntRatF.mapIso (asIso (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.π
        (Work.Cohomology.inclChains (TopCat.of X) ({b} : Set X))) k))).symm
  obtain ⟨eR⟩ := Work.Serre.Csr.relChainsRHomologyIsoRat (TopCat.of X) ({b} : Set X) k
  exact IsZero.of_iso h2 eR

/-! ## The target -/

theorem isZero_conePairRelCoh (D : ℕ) (hD : 2 ≤ D) (Γ : Type) [TopologicalSpace Γ] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere (D-2), Γ)) {X : Type} [TopologicalSpace X]
    (q : C(X, Work.RatHurewicz.attachCells (D-2) Γ ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (r N : ℕ) (hr : 1 ≤ r) (i : ι)
    (hpc : PathConnectedSpace (Work.StemsB.fibre q (Work.Serre.csrCentre (D - 2) Γ ι f i)))
    (hvan : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N → CategoryTheory.Limits.IsZero
      (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q (Work.Serre.csrCentre (D - 2) Γ ι f i))) t))
    (hgen : Nonempty (Work.Serre.ratH
      (TopCat.of (Work.StemsB.fibre q (Work.Serre.csrCentre (D - 2) Γ ι f i))) r
      ≅ ModuleCat.of ℚ ℚ))
    (j : ℕ) (hj : j ≤ N + 1) (hjne : j ≠ r + 1) :
    CategoryTheory.Limits.IsZero (Work.Thom.RelCoh ℚ j
      ↥((Work.Serre.cylRetract q) ⁻¹' {Work.Serre.csrCentre (D - 2) Γ ι f i})
      {x | (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)}) := by
  classical
  haveI hpcF : PathConnectedSpace (Work.StemsB.fibre q (Work.Serre.csrCentre (D - 2) Γ ι f i)) :=
    hpc
  refine isZero_relCoh_of_isZero_relH _ j ?_
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · -- degree `0`: the cone is path connected and its base is nonempty
    subst h0
    haveI hpcP : PathConnectedSpace ↥((Work.Serre.cylRetract q) ⁻¹'
        {Work.Serre.csrCentre (D - 2) Γ ι f i}) :=
      pathConnectedSpace_cylPreimage q (Work.Serre.csrCentre (D - 2) Γ ι f i)
    obtain ⟨b⟩ := hpc.nonempty
    obtain ⟨x, hx⟩ := b
    haveI hneA : Nonempty {x : ↥((Work.Serre.cylRetract q) ⁻¹'
        {Work.Serre.csrCentre (D - 2) Γ ι f i}) |
        (x : Work.Serre.cyl q) ∈ Set.range (Work.Serre.cylIncl q)} :=
      nonempty_cylPreimageBase q (Work.Serre.csrCentre (D - 2) Γ ι f i) x hx
    exact Work.Serre.Csr.isZero_relChainsR_rat_of_isZero_int _ _ 0
      (ModuleCat.isZero_iff_subsingleton.mpr
        (Work.RatHurewicz.Cofibre.subsingleton_homology_zero_relChains _ _))
  · -- degree `≥ 1`: the cone pair is the reduced homology of the fibre, shifted
    obtain ⟨b⟩ := hpc.nonempty
    obtain ⟨e1⟩ := centreConePair D Γ ι f q hq i b j hpos
    refine IsZero.of_iso ?_ e1
    rcases Nat.eq_zero_or_pos (j - 1) with hk0 | hkpos
    · rw [hk0]
      exact isZero_relChainsR_point_zero
        (Work.StemsB.fibre q (Work.Serre.csrCentre (D - 2) Γ ι f i)) b
    · refine isZero_relChainsR_point_of_isZero_ratH _ b (j - 1) (by omega) ?_
      exact hvan (j - 1) (by omega) (by omega) (by omega)

end

end Work.Serre.DiscPair
