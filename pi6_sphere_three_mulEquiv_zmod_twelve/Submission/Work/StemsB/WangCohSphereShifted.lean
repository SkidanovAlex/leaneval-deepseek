import Submission.Work.StemsB.WangSequenceShifted
import Submission.Work.StemsB.cohomology_collar_iso
import Submission.Work.StemsB.nonempty_singularCohomology_iso_fibre_of_path
import Submission.Work.StemsB.SerreSphereInfty
import Submission.Work.StemsB.SerreSphereAssembly
import Submission.Work.StemsB.FibreTrivCohomology
import Submission.Work.StemsB.WangSphereHomology

/-!
# The Wang sequence over a sphere, in cohomology, unconditionally

This file instantiates the degree-shifted Wang sequence (`WangSequenceShifted.lean`) for a map
`p : E → SphModel b` and the pair `(E, E|_O)` given by the **outer** piece `O = sphLoopOuter b`.
Both identifications are now theorems:

* `γ : H^k(E|_O) ≅ H^k(F)` — the fibrewise triviality over the contractible `O`
  (`nonempty_singularCohomology_iso_fibreTriv`);
* `τ : H^{n+b}(E, E|_O) ≅ H^n(F)` — excision (`nonempty_relCohomology_iso_excision`), the fibrewise
  triviality over the inner cube `G = sphLoopBig b` (`nonempty_relCohomology_iso_of_relChains_quasiIso`
  applied to `relMap`), the **cohomological collar Künneth**
  (`Work.StemsB.cohomology_collar_iso : CollarCohomology`) and the independence of the cohomology of
  the fibre from the base point (`nonempty_singularCohomology_iso_fibre_of_path`).

Hence the Wang sequence over a sphere is a theorem, in cohomology as well as in homology: the only
hypotheses are the two fibrewise trivialities and `IsHurewiczFibration p` (the latter used by the
fibre transport).  For the path–loop fibration both trivialities are available, so this covers the
case the blueprint's applications use.
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

/-- The fibre of the Wang sequence over the sphere. -/
abbrev wangCohFsp (b : ℕ) {E : Type} [TopologicalSpace E] (p : C(E, SphModel b)) : TopCat :=
  TopCat.of ↥(p ⁻¹' {OnePoint.infty})

/-- The identification `γ` over the outer piece. -/
noncomputable def wangGammaSphereOuter (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) :
    ∀ k : ℕ, Work.Cohomology.singularCohomology ℤ k (TopCat.of (p ⁻¹' sphLoopOuter b)) ≅
      Work.Cohomology.singularCohomology ℤ k (wangCohFsp b p) := fun k =>
  Classical.choice (nonempty_singularCohomology_iso_fibreTriv p (sphLoopOuter b) (dOuter b) hT_O
    (dOuter b) (sphLoopOuterContr b) (sphLoopOuterContr_zero b) (sphLoopOuterContr_one b) k)

/-- The set on which the trivialisation over the inner cube lands, when the relative part is the
outer piece: it is the collar product. -/
theorem relB_eq_sphLoopCollarProd {E : Type} [TopologicalSpace E] (b : ℕ) (p : C(E, SphModel b))
    (d_G : ↥(sphLoopBig b)) :
    relB p (sphLoopBig b) d_G (sphLoopOuter b) = sphLoopCollarProd b ↥(p ⁻¹' {d_G.1}) := by
  ext y
  exact ⟨fun hy => ⟨hy, y.1.2⟩, fun hy => hy.1⟩

/-- **The identification `τ` of the Wang sequence over a sphere, in the shifted form**:
`H^{n+b}(E, E|_O) ≅ H^n(F)`, `O = sphLoopOuter b`, `F = p ⁻¹' {∞}`. -/
noncomputable def wangTauCohShift (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hp : IsHurewiczFibration p) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (n : ℕ) :
    (Work.Cohomology.relComplex ℤ (TopCat.of E) (p ⁻¹' sphLoopOuter b)).homology (n + b) ≅
      Work.Cohomology.singularCohomology ℤ n (wangCohFsp b p) := by
  -- 1. excision
  let e₁ := Classical.choice (nonempty_relCohomology_iso_excision (TopCat.of E) (p ⁻¹' sphLoopBig b)
    (p ⁻¹' sphLoopOuter b) (sphLoopBig_open b |>.preimage p.continuous)
    (sphLoopOuter_open b |>.preimage p.continuous)
    (by rw [← Set.preimage_union, Set.union_comm (sphLoopBig b) (sphLoopOuter b),
      sphLoopOuter_union_sphLoopBig, Set.preimage_univ]) (n + b))
  -- 2. the fibrewise triviality over the inner cube
  let e₂ := Classical.choice (nonempty_relCohomology_iso_of_relChains_quasiIso
    (relMap p (sphLoopBig b) d_G (sphLoopOuter b) hT_G)
    (fun k => isIso_relMap p (sphLoopBig b) d_G (sphLoopOuter b) hT_G k) (n + b))
  -- 3. the collar Künneth
  let e₃ := Classical.choice (cohomology_collar_iso b hb ↥(p ⁻¹' {d_G.1}) n)
  -- 4. the transport of the fibre
  let P := Classical.choice (joined_infty_SphModel b hb d_G.1)
  let γp : C(unitInterval, SphModel b) := P.toContinuousMap
  have h0 : γp 0 = OnePoint.infty := P.source
  have h1 : γp 1 = d_G.1 := P.target
  let e₄₀ := Classical.choice (nonempty_singularCohomology_iso_fibre_of_path p hp γp n)
  have e₄ : Work.Cohomology.singularCohomology ℤ n
        (TopCat.of ↥(p ⁻¹' {d_G.1})) ≅ Work.Cohomology.singularCohomology ℤ n (wangCohFsp b p) :=
    (eqToIso (congrArg (fun y => Work.Cohomology.singularCohomology ℤ n
        (TopCat.of ↥(p ⁻¹' {y}))) h1)).symm.trans
      (e₄₀.symm.trans (eqToIso (congrArg (fun y => Work.Cohomology.singularCohomology ℤ n
        (TopCat.of ↥(p ⁻¹' {y}))) h0)))
  -- the set change
  have hSet : (Work.Cohomology.relComplex ℤ
        (TopCat.of (↥(sphLoopBig b) × ↥(p ⁻¹' {d_G.1})))
        (relB p (sphLoopBig b) d_G (sphLoopOuter b))).homology (n + b) =
      (Work.Cohomology.relComplex ℤ (TopCat.of (↥(sphLoopBig b) × ↥(p ⁻¹' {d_G.1})))
        (sphLoopCollarProd b ↥(p ⁻¹' {d_G.1}))).homology (n + b) :=
    congrArg (fun S => (Work.Cohomology.relComplex ℤ
      (TopCat.of (↥(sphLoopBig b) × ↥(p ⁻¹' {d_G.1}))) S).homology (n + b))
      (relB_eq_sphLoopCollarProd b p d_G)
  exact e₁.trans (e₂.symm.trans ((eqToIso hSet).trans (e₃.trans e₄)))

/-- The identification `τ` at the shifted degree `n+1`. -/
noncomputable def wangTauCohShiftS (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hp : IsHurewiczFibration p) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (n : ℕ) :
    (Work.Cohomology.relComplex ℤ (TopCat.of E) (p ⁻¹' sphLoopOuter b)).homology (n + b + 1) ≅
      Work.Cohomology.singularCohomology ℤ (n + 1) (wangCohFsp b p) :=
  eqToIso (congrArg (fun t => (Work.Cohomology.relComplex ℤ (TopCat.of E)
      (p ⁻¹' sphLoopOuter b)).homology t) (show n + b + 1 = (n + 1) + b by omega)) ≪≫
    wangTauCohShift b hb E p hp d_G hT_G (n + 1)

/-! ## The Wang sequence over a sphere -/

/-- **Exactness of the Wang sequence over a sphere at `H^{n+b}(E)`**, in cohomology. -/
theorem wangCohShiftExactSphere₁ (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hp : IsHurewiczFibration p)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (n : ℕ) :
    Function.Exact
      (wangCohShiftβ (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangCohFsp b p) b
        (wangTauCohShift b hb E p hp d_G hT_G) n)
      (wangCohShiftα (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangCohFsp b p) b
        (wangGammaSphereOuter b hb E p hT_O) (n + b)) :=
  wangCohShiftExact₁ _ _ _ _ _ _ n

/-- **Exactness of the Wang sequence over a sphere at `H^{n+b}(F)`**, in cohomology. -/
theorem wangCohShiftExactSphere₂ (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hp : IsHurewiczFibration p)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (n : ℕ) :
    Function.Exact
      (wangCohShiftα (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangCohFsp b p) b
        (wangGammaSphereOuter b hb E p hT_O) (n + b))
      (wangCohShiftθ (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangCohFsp b p) b
        (wangGammaSphereOuter b hb E p hT_O) (wangTauCohShiftS b hb E p hp d_G hT_G) n) :=
  wangCohShiftExact₂ _ _ _ _ _ _ n

/-- **Exactness of the Wang sequence over a sphere at `H^{n+b+1}(E, E|_O)`**, in cohomology. -/
theorem wangCohShiftExactSphere₃ (b : ℕ) (hb : 1 ≤ b) (E : Type) [TopologicalSpace E]
    (p : C(E, SphModel b)) (hp : IsHurewiczFibration p)
    (hT_O : FibrewiseTrivial p (sphLoopOuter b) (dOuter b)) (d_G : ↥(sphLoopBig b))
    (hT_G : FibrewiseTrivial p (sphLoopBig b) d_G) (n : ℕ) :
    Function.Exact
      (wangCohShiftθ (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangCohFsp b p) b
        (wangGammaSphereOuter b hb E p hT_O) (wangTauCohShiftS b hb E p hp d_G hT_G) n)
      (wangCohShiftβS (TopCat.of E) (p ⁻¹' sphLoopOuter b) (wangCohFsp b p) b
        (wangTauCohShiftS b hb E p hp d_G hT_G) n) :=
  wangCohShiftExact₃ _ _ _ _ _ _ n

end

end Work.StemsB
