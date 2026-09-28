import Mathlib
import Submission.Work.Serre.E2dTools
import Submission.Work.StemsB.CubePairHomology

/-!
# The base case and the slab vanishings of the E2(d) induction

* `Work.Serre.E2dAt n` — the E2(d) statement in dimension `n` (the statement of
  `Work.Serre.SerreE2d` with the cube `Iⁿ` and its boundary);
* `Work.Serre.isZero_relChains_pbSub_slabU`, `..._slabV` — the acyclicity of the two slab pairs of
  the Mayer–Vietoris cover, obtained from the compression properties
  (`Work.Serre.compressRel_slabU`, `Work.Serre.compressRel_slabV`) by the engine;
* `Work.Serre.E2dAt 0` — the base case, where `I⁰` is a point and `∂I⁰ = ∅`.
-/

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Work.Serre

noncomputable section

/-- **The E2(d) statement in dimension `n`**: the relative homology of the pullback over the cube
pair `(Iⁿ, ∂Iⁿ)` is the homology of the fibre, shifted by `n`. -/
def E2dAt (n : ℕ) : Prop :=
  ∀ (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (hp : Work.StemsB.IsSerreFibration p) (τ : C(Work.Stems.Cubical.IC n, B))
    (d₀ : Work.Stems.Cubical.IC n) (k : ℕ),
    Nonempty (((Work.Cohomology.relChains (TopCat.of (Work.StemsB.Pullback p τ))
        (pbPre p τ (cubeBdryS n))).homology (k + n)) ≅
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p (τ d₀)))).homology k))

/-- **The acyclicity of the first slab pair** of the Mayer–Vietoris cover of the cube. -/
theorem isZero_relChains_pbSub_slabU (n : ℕ) {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (τ : C(Work.Stems.Cubical.IC (n+1), B)) (m : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(pbPre p τ (slabU n)))
      (pbSub p τ (slabU n) (slabU n ∩ cubeBdryS (n+1)))).homology m) :=
  isZero_relChains_preimage_of_base_compress (Work.StemsB.pullbackSnd p τ)
    (fun i => Work.StemsB.hasHLP_pullback p τ (hp i)) (slabU n ∩ cubeBdryS (n+1)) (slabU n)
    Set.inter_subset_left (compressRel_slabU n) m

/-- **The acyclicity of the second slab pair** of the Mayer–Vietoris cover of the cube. -/
theorem isZero_relChains_pbSub_slabV (n : ℕ) {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (τ : C(Work.Stems.Cubical.IC (n+1), B)) (m : ℕ) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(pbPre p τ (slabV n)))
      (pbSub p τ (slabV n) (slabV n ∩ cubeBdryS (n+1)))).homology m) :=
  isZero_relChains_preimage_of_base_compress (Work.StemsB.pullbackSnd p τ)
    (fun i => Work.StemsB.hasHLP_pullback p τ (hp i)) (slabV n ∩ cubeBdryS (n+1)) (slabV n)
    Set.inter_subset_left (compressRel_slabV n) m

/-- The unique point of the `0`-cube. -/
def ptZero : Work.Stems.Cubical.IC 0 := fun i => i.elim0

theorem subsingleton_IC_zero : Subsingleton (Work.Stems.Cubical.IC 0) :=
  ⟨fun a b => funext fun i => i.elim0⟩

/-- **The pullback over a point is the fibre.** -/
def pullbackPtHomeo {E B : Type} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (τ : C(Work.Stems.Cubical.IC 0, B)) :
    Work.StemsB.Pullback p τ ≃ₜ Work.StemsB.fibre p (τ ptZero) where
  toFun x := ⟨x.1.1, by rw [x.2, Subsingleton.elim x.1.2 ptZero]⟩
  invFun e := ⟨(e.1, ptZero), e.2⟩
  left_inv x := by
    refine Subtype.ext ?_
    refine Prod.ext rfl ?_
    exact (Subsingleton.elim x.1.2 ptZero).symm
  right_inv e := by
    refine Subtype.ext rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_fst.comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_subtype_val.prodMk continuous_const

/-- **The base case of the E2(d) induction**: `I⁰` is a point and `∂I⁰ = ∅`. -/
theorem e2dAt_zero : E2dAt 0 := by
  intro E B _ _ p hp τ d₀ k
  have hpt : τ d₀ = τ ptZero := congrArg τ (Subsingleton.elim d₀ ptZero)
  -- the pair is the pair `(τ^*E, ∅)`
  have hset : pbPre p τ (cubeBdryS 0) = (∅ : Set (Work.StemsB.Pullback p τ)) := by
    ext x
    simp [pbPre, cubeBdryS, Cube.boundary]
  obtain ⟨e₁⟩ := Work.StemsB.relChains_empty_iso (TopCat.of (Work.StemsB.Pullback p τ))
  -- the pullback over a point is the fibre
  have e₂ : Nonempty (((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.StemsB.Pullback p τ))).homology k) ≅
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre p (τ d₀)))).homology k)) :=
    ⟨(HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k).mapIso
      (((singularChainComplexFunctor (ModuleCat ℤ)).obj (ModuleCat.of ℤ ℤ)).mapIso
        ((TopCat.isoOfHomeo (pullbackPtHomeo p τ)).trans (eqToIso (congrArg
          (fun b => TopCat.of (Work.StemsB.fibre p b)) hpt.symm))))⟩
  obtain ⟨i₂⟩ := e₂
  refine ⟨(eqToIso (congrArg (fun S => (Work.Cohomology.relChains
      (TopCat.of (Work.StemsB.Pullback p τ)) S).homology (k + 0)) hset)) ≪≫
    (HomologicalComplex.homologyFunctor (ModuleCat ℤ) (ComplexShape.down ℕ) k).mapIso e₁ ≪≫ ?_⟩
  exact i₂

end

end Work.Serre
