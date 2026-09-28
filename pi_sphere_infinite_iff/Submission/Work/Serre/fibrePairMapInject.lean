import Mathlib
import Submission.Work.Serre.ThomCylDefs
import Submission.Work.StemsB.Fibrations
import Submission.Work.Serre.relKronEquiv
import Submission.Work.Serre.relKron_exists
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.ratPairBasic
import Submission.Work.Serre.ratPairComparisonOneBoundary
import Submission.Work.Serre.B1Rel.relKronMapR_natural
import Submission.Work.StemsB.RelDualNatural

/-!
# The relative edge map of a Serre fibration is injective in the transgression degree

Over a field, relative cohomology is the dual of relative homology: the Kronecker pairing

  `relKronMapR ℚ X A n : H^n(X,A;ℚ) → (H_n(X,A;ℚ) →ₗ[ℚ] ℚ)`

is injective (`Work.Serre.relKronMapRInjective`, the universal coefficient theorem over `ℚ`) and
natural in the pair (`Work.Serre.B1Rel.relKronMapR_natural`).  Hence, for a map of pairs
`(X,A) → (Y,B)` whose map of relative chain complexes is *surjective* on `n`-th rational homology,
the induced pullback `H^n(Y,B;ℚ) → H^n(X,A;ℚ)` is *injective*: if the pullback of a class `β`
vanishes, then `β` pairs trivially with every class in the image of the homology map, hence with
everything, hence `β = 0`.

This is the duality half of `Work.Serre.fibrePairMapInject`; the analytic half is the `b = 1` case
of the rational Serre pair comparison (`Work.Serre.ratPairComparisonOneBoundary`), i.e. the
surjectivity of `H_{1+f}(E, p⁻¹b;ℚ) → H_{1+f}(B,{b};ℚ)` for a Serre fibration whose fibres are
rationally acyclic below `f` and connected.
-/

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- **Naturality of the relative Kronecker pairing over `ℚ`** in the pair (the `Set.MapsTo` form),
quoted from `Work.Serre.B1Rel.relKronMapR_natural` for the convenience of the duality half below.
Pairing the pullback of a relative cohomology class of `(Y,B)` with a relative homology class of
`(X,A)` equals pairing the class with the image class; this is the `ℚ`-coefficient counterpart of the
integer statement `Work.Tubular.relKronH_natural`. -/
theorem relKronMapR_pair_natural {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (f : C(X, Y)) (hf : ∀ x ∈ A, f x ∈ B) (n : ℕ)
    (β : (Work.Cohomology.relComplex ℚ (TopCat.of Y) B).homology n)
    (c : (Work.StemsB.relChainsR ℚ (TopCat.of X) A).homology n) :
    (Work.Serre.relKronMapR ℚ (TopCat.of X) A n).hom
        ((HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap
          (X₁ := TopCat.of X) (X₂ := TopCat.of Y) ℚ A B
          (TopCat.ofHom f) hf) n).hom β) c
      = (Work.Serre.relKronMapR ℚ (TopCat.of Y) B n).hom β
          ((HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap A B f hf) n).hom c) :=
  Work.Serre.B1Rel.relKronMapR_natural A B f hf n β c

/-- **The duality half**: over `ℚ`, if the map of relative chain complexes induced by a map of
pairs is surjective on `n`-th homology, then the induced map of relative cohomology is injective in
degree `n`. -/
theorem relCohMap_injective_of_surjective_relHomology {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (f : C(X, Y)) (A : Set X) (B : Set Y) (hf : ∀ x ∈ A, f x ∈ B) (n : ℕ)
    (h : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap A B f hf) n).hom) :
    Function.Injective (Work.Thom.relCohMap f A B hf ℚ n).hom := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro β hβ
  rw [LinearMap.mem_ker] at hβ
  -- `β` pairs trivially with every class of `H_n(X,A;ℚ)`
  have hzero : (Work.Serre.relKronMapR ℚ (TopCat.of Y) B n).hom β = 0 := by
    apply LinearMap.ext
    intro c
    obtain ⟨z, rfl⟩ := h c
    rw [← relKronMapR_pair_natural A B f hf n β z]
    rw [show (HomologicalComplex.homologyMap (Work.Cohomology.relComplexMap (X₁ := TopCat.of X)
        (X₂ := TopCat.of Y) ℚ A B (TopCat.ofHom f) hf) n).hom β = 0 from hβ]
    simp
  -- the Kronecker pairing is injective
  exact Work.Serre.relKronMapRInjective (TopCat.of Y) B n (by rw [hzero]; simp)

end

/-- The relative edge map of a Serre fibration is injective in the "transgression" degree `r+1`:
`H^{r+1}(B,{b};ℚ) → H^{r+1}(E, p⁻¹{b};ℚ)`.  A review raised the Hopf bundle `S¹ → S³ → S²`
(`r = 1`) as a counterexample via the argument "a disc `D ⊂ S³` bounding the fibre has
`p(D) = {b}`, so `p_* = 0`" — that argument is wrong: for a Seifert surface `D` of the fibre one has
`p(D) = {[u:1] : u ∈ D̄} ∪ {[1:0]}`, not a point, and the relative class `[p(D)]` is `±` the generator
of `H_2(S²,{b})` (its pairing with a regular value `b'` is the linking number `lk(F_b,F_{b'}) = ±1`).
The `H_2(S³) = 0` computation that seems to force `p_* = 0` concerns the *absolute* group, where the
class is indeed `0`; the bounding 3-chain does not have its boundary in `{b}`, so it does not kill
the *relative* class. -/
theorem fibrePairMapInject (r N : ℕ) (hr : 1 ≤ r) (hrN : r ≤ N)
    {B : Type} [TopologicalSpace B] (hB : PathConnectedSpace B)
    {E : Type} [TopologicalSpace E] (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p)
    (hvan : ∀ b : B, ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) t))
    (hpc : ∀ b : B, PathConnectedSpace (Work.StemsB.fibre p b))
    (hgen : ∀ b : B, Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b)) r
      ≅ ModuleCat.of ℚ ℚ))
    (b : B) :
    Function.Injective (Work.Thom.relCohMap p (p ⁻¹' {b}) {b} (fun x hx => hx) ℚ (r + 1)).hom := by
  -- the analytic half: the pair map is surjective on relative rational homology in degree `r + 1`
  have hcore := Work.Serre.ratPairComparisonOneBoundary p hp b r hr hB (hpc b)
    (fun j hj hjl => hvan b j hj (by omega) (by omega))
  have hsurj : Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (p ⁻¹' {b}) ({b} : Set B) p (fun _ hx => hx))
      (r + 1)).hom := by
    rw [show r + 1 = 1 + r from by omega]
    exact hcore
  -- the duality half
  exact relCohMap_injective_of_surjective_relHomology p (p ⁻¹' {b}) {b} (fun x hx => hx)
    (r + 1) hsurj

end Work.Serre
