import Submission.Work.StemsB.WangHomology
import Submission.Work.StemsB.SerreSphereInfty
import Submission.Work.StemsB.SerreSphereAssembly

/-!
# The Wang sequence over the sphere, in homology

This file instantiates the abstract homological Wang sequence of `WangHomology.lean` for a map
`p : E → SphModel b`, with the pair `(E, E|_O)` given by the *outer* piece
`O = sphLoopOuter b`.  The two identifications are

* `γ : H_n(E|_O) ≅ H_n(F)`, `F = p ⁻¹' {∞}` — the fibrewise triviality over the contractible `O`
  (`nonempty_homologyIso_fibreTriv`), and
* `τ : H_k(E, E|_O) ≅ H_{k-b}(F)` — excision (`isIso_relChainsMap_excision`), the fibrewise
  triviality over the inner cube `G = sphLoopBig b` (`isIso_relMap`), the relative Künneth of the
  collar (`collarProdO_iso`) and the independence of `H_*` of the fibre from the base point
  (`FibreTransport.nonempty_homology_fibre_iso`).

All four ingredients are theorems of this directory, so — unlike the cohomological case
(`WangSphere.lean`), where the relative Künneth of the disc pair is still missing — the Wang
sequence over a sphere is **unconditional** in homology.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

namespace Work.StemsB

noncomputable section

instance subsingleton_zeroModZ : Subsingleton ↥zeroModZ :=
  ⟨fun f g => funext fun i => i.elim0⟩

/-- The base point of the outer piece. -/
def dOuter (b : ℕ) : ↥(sphLoopOuter b) :=
  ⟨OnePoint.infty, infty_subset_outer b rfl⟩

/-- `chainZ` vanishes at negative indices. -/
theorem chainZ_neg (X : TopCat) {j : ℤ} (h : j < 0) : chainZ X j = zeroModZ := by
  rcases j with k | k
  · exact absurd (Int.natCast_nonneg k) (not_le.mpr h)
  · rfl

/-- An isomorphism to `zeroModZ` from any zero object. -/
theorem nonempty_iso_zeroModZ_of_isZero {M : ModuleCat ℤ} (h : IsZero M) :
    Nonempty (M ≅ zeroModZ) :=
  ⟨{ hom := 0, inv := 0,
     hom_inv_id := by rw [zero_comp, ((IsZero.iff_id_eq_zero M).mp h).symm]
     inv_hom_id := by
       rw [zero_comp, ((IsZero.iff_id_eq_zero zeroModZ).mp
         (ModuleCat.isZero_of_subsingleton zeroModZ)).symm] }⟩

/-- **The identification `τ : H_k(E, E|_O) ≅ H_{k-b}(F)` of the homological Wang sequence over a
sphere**, `O = sphLoopOuter b` and `F = p ⁻¹' {∞}`. -/
noncomputable def wangTauSphere (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hp : IsHurewiczFibration p) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (k : ℕ) :
    (Work.Cohomology.relChains (TopCat.of E) (p ⁻¹' sphLoopOuter b)).homology k ≅
      chainZ (TopCat.of ↥(p ⁻¹' {OnePoint.infty})) ((k : ℤ) - (b : ℤ)) := by
  haveI hEx : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap (TopCat.of E)
      (p ⁻¹' sphLoopBig b) (p ⁻¹' sphLoopOuter b)) k) := isIso_relChainsMap_excision b p k
  haveI hTr : IsIso (HomologicalComplex.homologyMap
      (relMap p (sphLoopBig b) d_G (sphLoopOuter b) hT_G) k) :=
    isIso_relMap p (sphLoopBig b) d_G (sphLoopOuter b) hT_G k
  by_cases hk : k < b
  · -- below the dimension: both sides vanish
    haveI hCol : IsZero ((Work.Cohomology.relChains
        (TopCat.of (↥(sphLoopBig b) × ↥(p ⁻¹' {d_G.1})))
        (collarProdO b ↥(p ⁻¹' {d_G.1}))).homology k) := collarProdO_isZero b hb _ k hk
    haveI hSrc : IsZero ((Work.Cohomology.relChains (TopCat.of ↥(p ⁻¹' sphLoopBig b))
        {x : ↥(p ⁻¹' sphLoopBig b) | (x : E) ∈ p ⁻¹' sphLoopOuter b}).homology k) :=
      IsZero.of_iso hCol (asIso (HomologicalComplex.homologyMap
        (relMap p (sphLoopBig b) d_G (sphLoopOuter b) hT_G) k))
    haveI hTgt : IsZero ((Work.Cohomology.relChains (TopCat.of E)
        (p ⁻¹' sphLoopOuter b)).homology k) :=
      IsZero.of_iso hSrc (asIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap
        (TopCat.of E) (p ⁻¹' sphLoopBig b) (p ⁻¹' sphLoopOuter b)) k)).symm
    have hneg : ((k : ℤ) - (b : ℤ)) < 0 := by omega
    rw [chainZ_neg _ hneg]
    exact Classical.choice (nonempty_iso_zeroModZ_of_isZero hTgt)
  · -- above the dimension: excision, triviality, collar Künneth, transport of the fibre
    have hbk : b ≤ k := Nat.le_of_not_lt hk
    let eCol := Classical.choice (collarProdO_iso b hb ↥(p ⁻¹' {d_G.1}) (k - b))
    let P := Classical.choice (joined_infty_SphModel b hb d_G.1)
    let γp : C(unitInterval, SphModel b) := P.toContinuousMap
    have h0 : γp 0 = OnePoint.infty := P.source
    have h1 : γp 1 = d_G.1 := P.target
    let eFib0 := Classical.choice (nonempty_homology_fibre_iso p hp γp (k - b))
    have eFib : ((Work.Cohomology.singularChains ℤ
          (TopCat.of ↥(p ⁻¹' {d_G.1}))).homology (k - b)) ≅
        ((Work.Cohomology.singularChains ℤ
          (TopCat.of ↥(p ⁻¹' {OnePoint.infty}))).homology (k - b)) :=
      (eqToIso (congrArg (fun y => (Work.Cohomology.singularChains ℤ
          (TopCat.of ↥(p ⁻¹' {y}))).homology (k - b)) h1)).symm.trans
        (eFib0.symm.trans (eqToIso (congrArg (fun y => (Work.Cohomology.singularChains ℤ
          (TopCat.of ↥(p ⁻¹' {y}))).homology (k - b)) h0)))
    have hCast : ((k - b : ℕ) : ℤ) = (k : ℤ) - (b : ℤ) := Nat.cast_sub hbk
    exact (asIso (HomologicalComplex.homologyMap (Work.Cohomology.relChainsMap (TopCat.of E)
      (p ⁻¹' sphLoopBig b) (p ⁻¹' sphLoopOuter b)) k)).symm.trans
      ((asIso (HomologicalComplex.homologyMap
        (relMap p (sphLoopBig b) d_G (sphLoopOuter b) hT_G) k)).trans
      ((homologyCongr (C := Work.Cohomology.relChains
        (TopCat.of (↥(sphLoopBig b) × ↥(p ⁻¹' {d_G.1})))
        (collarProdO b ↥(p ⁻¹' {d_G.1})))
        (i := k) (j := (k - b) + b) (Nat.sub_add_cancel hbk).symm).trans
      (eCol.trans (eFib.trans (eqToIso (congrArg
        (chainZ (TopCat.of ↥(p ⁻¹' {OnePoint.infty}))) hCast))))))

/-! ## The Wang sequence over the sphere -/

/-- The map `γ : H_n(E|_O) ≅ H_n(F)` of the homological Wang sequence over the sphere. -/
noncomputable def wangGammaSphereHom (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    ∀ n : ℕ,
      (Work.Cohomology.singularChains ℤ (TopCat.of ↥(p ⁻¹' sphLoopOuter b))).homology n ≅
        chainZ (TopCat.of ↥(p ⁻¹' {OnePoint.infty})) n := fun n =>
  Classical.choice (nonempty_homologyIso_fibreTriv p (sphLoopOuter b) (dOuter b) hT_O (dOuter b)
    (sphLoopOuterContr b) (sphLoopOuterContr_zero b) (sphLoopOuterContr_one b) n)

/-- The common notation for the fibre of the Wang sequence over the sphere. -/
abbrev wangFsp (b : ℕ) {E : Type} [TopologicalSpace E] (p : C(E, SphModel b)) : TopCat :=
  TopCat.of ↥(p ⁻¹' {OnePoint.infty})

/-- **The Wang sequence over the sphere, in homology.**  For `p : E → SphModel b`, a fibrewise
triviality over both pieces of the two-disc decomposition, the sequence

  `H_{n+b}(E) → H_n(F) --θ--> H_{n+b-1}(F) → H_{n+b-1}(E) → H_{n-1}(F) → ⋯`

(with `F` the fibre over `∞`) is exact.  The three exactness statements below are the three spots of
the sequence. -/
theorem wangHomExactSphere₁ (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hp : IsHurewiczFibration p)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (n : ℕ) :
    Function.Exact
      (wangHomθ (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangFsp b p) b
        (wangGammaSphereHom b hb E p hT_O) (wangTauSphere b hb E p hp d_G hT_G) n)
      (wangHomα (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangFsp b p) b
        (wangGammaSphereHom b hb E p hT_O) n) :=
  wangHomExact₃ _ _ _ _ _ _ n

/-- The second exactness spot of the Wang sequence over the sphere. -/
theorem wangHomExactSphere₂ (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hp : IsHurewiczFibration p)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (n : ℕ) :
    Function.Exact
      (wangHomβ (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangFsp b p) b
        (wangTauSphere b hb E p hp d_G hT_G) (n + 1))
      (wangHomθ (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangFsp b p) b
        (wangGammaSphereHom b hb E p hT_O) (wangTauSphere b hb E p hp d_G hT_G) n) :=
  wangHomExact₂ _ _ _ _ _ _ n

/-- The third exactness spot of the Wang sequence over the sphere. -/
theorem wangHomExactSphere₃ (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hp : IsHurewiczFibration p)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (n : ℕ) :
    Function.Exact
      (wangHomα (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangFsp b p) b
        (wangGammaSphereHom b hb E p hT_O) n)
      (wangHomβ (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangFsp b p) b
        (wangTauSphere b hb E p hp d_G hT_G) n) :=
  wangHomExact₁ _ _ _ _ _ _ n

end

end Work.StemsB
