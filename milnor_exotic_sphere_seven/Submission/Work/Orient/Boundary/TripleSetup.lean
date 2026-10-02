import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.HalfRestrictIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The map of triples of the relative chain complexes, and naturality of `δ`

The bookkeeping shared by the proof of
`Work.Orient.Boundary.tripleConnectingMap_surjective_of_isRelFundClass` (Hatcher 3.43, second half):

* `tripleMap` — the morphism of short complexes `tripleShort W A₁ B₁ ⟶ tripleShort W A₂ B₂` induced
  by inclusions of sets `A₁ ⊆ A₂`, `B₁ ⊆ B₂` (the "map of triples");
* `tripleMap_delta_naturality` — the naturality square of the connecting homomorphism
  `HomologicalComplex.HomologySequence.δ_naturality`, which is what turns a statement about the
  connecting map of one triple into a statement about another;
* the sets `bdrySetW`, `bdryMinus`, `halfBallK`, `bigB`, `bigA` of the proof and their inclusions
  (`bigA_eq`: `A` is the complement of `K ∩ W° ∪ {y}`).

Everything here is sorry-free; the geometry lives in the companion files
`…isZero_halfBallInterior_union_point`, `…tripleMap_tau₁_injective`,
`…tripleMap_tau₃_surjective_of_isRelFundClass`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.Orient.Boundary

noncomputable section

/-! ## 1. The naturality of the connecting map of a "map of triples"

The two squares of the morphism of short complexes of a map of triples, then the morphism itself
and the naturality identity `δ_{S₁} ≫ H(τ₁) = H(τ₃) ≫ δ_{S₂}`. -/

/-- The inclusion of chains `C_*(A₁) → C_*(B)` depends only on the pair of sets. -/
theorem inclChainsSub_congr_h {X : TopCat} {A B : Set X} (h h' : A ⊆ B) :
    Work.Cohomology.inclChainsSub X A B h = Work.Cohomology.inclChainsSub X A B h' := by
  unfold Work.Cohomology.inclChainsSub
  have hcm : (⟨fun x : A => (⟨(x : X), h x.2⟩ : B),
      Continuous.subtype_mk (f := fun x : A => (x : X)) continuous_subtype_val (fun x => h x.2)⟩
      : C(A, B))
      = ⟨fun x : A => (⟨(x : X), h' x.2⟩ : B),
      Continuous.subtype_mk (f := fun x : A => (x : X)) continuous_subtype_val (fun x => h' x.2)⟩ :=
    ContinuousMap.ext (fun x => Subtype.ext rfl)
  rw [hcm]

/-- The compatibility of the inclusions of chains of a map of triples `A₁ ⊆ A₂`, `B₁ ⊆ B₂` with
`A₁ ⊆ B₁`, `A₂ ⊆ B₂`. -/
theorem tripleCompat {W : TopCat} {A₁ B₁ A₂ B₂ : Set W} (h₁ : A₁ ⊆ B₁) (h₂ : A₂ ⊆ B₂)
    (hA : A₁ ⊆ A₂) (hB : B₁ ⊆ B₂) :
    Work.Cohomology.inclChainsSub W A₁ B₁ h₁ ≫ Work.Cohomology.inclChainsSub W B₁ B₂ hB
      = Work.Cohomology.inclChainsSub W A₁ A₂ hA ≫ Work.Cohomology.inclChainsSub W A₂ B₂ h₂ := by
  rw [Work.Cohomology.inclChainsSub_comp', Work.Cohomology.inclChainsSub_comp']

/-- The first square of the morphism of triples. -/
theorem tripleMap_comm₁ (W : TopCat) {A₁ B₁ A₂ B₂ : Set W} (h₁ : A₁ ⊆ B₁) (h₂ : A₂ ⊆ B₂)
    (hA : A₁ ⊆ A₂) (hB : B₁ ⊆ B₂) :
    cokernel.map (Work.Cohomology.inclChainsSub W A₁ B₁ h₁)
        (Work.Cohomology.inclChainsSub W A₂ B₂ h₂) (Work.Cohomology.inclChainsSub W A₁ A₂ hA)
        (Work.Cohomology.inclChainsSub W B₁ B₂ hB) (tripleCompat h₁ h₂ hA hB)
      ≫ cokernel.map (Work.Cohomology.inclChainsSub W A₂ B₂ h₂) (Work.Cohomology.inclChains W A₂)
          (𝟙 (Work.Cohomology.singularChains ℤ (TopCat.of ↑A₂))) (Work.Cohomology.inclChains W B₂)
          (by rw [Category.id_comp]; exact Work.Cohomology.inclChainsSub_comp W A₂ B₂ h₂)
    = cokernel.map (Work.Cohomology.inclChainsSub W A₁ B₁ h₁) (Work.Cohomology.inclChains W A₁)
        (𝟙 (Work.Cohomology.singularChains ℤ (TopCat.of ↑A₁))) (Work.Cohomology.inclChains W B₁)
        (by rw [Category.id_comp]; exact Work.Cohomology.inclChainsSub_comp W A₁ B₁ h₁)
      ≫ Work.Cohomology.relCokerMap W A₁ A₂ hA := by
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChainsSub W A₁ B₁ h₁))).mp
  rw [← Category.assoc, Work.Cohomology.cokernel_π_map, Category.assoc,
    Work.Cohomology.cokernel_π_map, ← Category.assoc, Work.Cohomology.inclChainsSub_comp,
    ← Category.assoc, Work.Cohomology.cokernel_π_map, Category.assoc,
    Work.Cohomology.relCokerMap_comp_π]

/-- The second square of the morphism of triples. -/
theorem tripleMap_comm₂ (W : TopCat) {A₁ B₁ A₂ B₂ : Set W} (h₁ : A₁ ⊆ B₁) (h₂ : A₂ ⊆ B₂)
    (hA : A₁ ⊆ A₂) (hB : B₁ ⊆ B₂) :
    Work.Cohomology.relCokerMap W A₁ A₂ hA ≫ Work.Cohomology.relCokerMap W A₂ B₂ h₂
      = Work.Cohomology.relCokerMap W A₁ B₁ h₁ ≫ Work.Cohomology.relCokerMap W B₁ B₂ hB := by
  rw [Work.Cohomology.relCokerMap_comp, Work.Cohomology.relCokerMap_comp]

/-- **The morphism of short complexes of a "map of triples"** `(A₁ ⊆ B₁) → (A₂ ⊆ B₂)`: the identity
of `W` induces maps on the three relative chain complexes. -/
noncomputable def tripleMap (W : TopCat) {A₁ B₁ A₂ B₂ : Set W} (h₁ : A₁ ⊆ B₁) (h₂ : A₂ ⊆ B₂)
    (hA : A₁ ⊆ A₂) (hB : B₁ ⊆ B₂) :
    Work.Cohomology.tripleShort W A₁ B₁ h₁ ⟶ Work.Cohomology.tripleShort W A₂ B₂ h₂ :=
  CategoryTheory.ShortComplex.homMk
    (cokernel.map (Work.Cohomology.inclChainsSub W A₁ B₁ h₁)
      (Work.Cohomology.inclChainsSub W A₂ B₂ h₂) (Work.Cohomology.inclChainsSub W A₁ A₂ hA)
      (Work.Cohomology.inclChainsSub W B₁ B₂ hB) (tripleCompat h₁ h₂ hA hB))
    (Work.Cohomology.relCokerMap W A₁ A₂ hA) (Work.Cohomology.relCokerMap W B₁ B₂ hB)
    (by
      rw [Work.Cohomology.tripleShort_f, Work.Cohomology.tripleShort_f]
      exact tripleMap_comm₁ W h₁ h₂ hA hB)
    (by
      rw [Work.Cohomology.tripleShort_g, Work.Cohomology.tripleShort_g]
      exact tripleMap_comm₂ W h₁ h₂ hA hB)

/-- **Naturality of the connecting homomorphism** for a map of triples: the square
`δ_{S₁} ≫ H(τ₁) = H(τ₃) ≫ δ_{S₂}` commutes. -/
theorem tripleMap_delta_naturality (W : TopCat) {A₁ B₁ A₂ B₂ : Set W} (h₁ : A₁ ⊆ B₁)
    (h₂ : A₂ ⊆ B₂) (hA : A₁ ⊆ A₂) (hB : B₁ ⊆ B₂) (n : ℕ) :
    (Work.Cohomology.relChains_triple_shortExact W A₁ B₁ h₁).δ (n + 1) n
        (by simp [ComplexShape.down])
      ≫ HomologicalComplex.homologyMap (tripleMap W h₁ h₂ hA hB).τ₁ n
    = HomologicalComplex.homologyMap (tripleMap W h₁ h₂ hA hB).τ₃ (n + 1)
      ≫ (Work.Cohomology.relChains_triple_shortExact W A₂ B₂ h₂).δ (n + 1) n
        (by simp [ComplexShape.down]) :=
  HomologicalComplex.HomologySequence.δ_naturality (tripleMap W h₁ h₂ hA hB) _ _
    (n + 1) n (by simp [ComplexShape.down])



/-- The inclusions of the map of triples `(∂W∖{y}, ∂W) → (A, B')`. -/
abbrev bdrySetW (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W] : Set W :=
  (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W

abbrev bdryMinus (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) : Set W := bdrySetW n W \ {y}

abbrev halfBallK (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) : Set W :=
  Work.Orient.halfBallPiece (n + 1) W y r

/-- `B' = W ∖ P`, the complement of the interior part `P = K ∩ W°` of the half-ball.  Written as a
complement so that `W ∖ B' = P` is *definitional*: the localisation out of `B'` is then literally
the map of the pair `(W, W∖P)`. -/
abbrev bigB (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) : Set W :=
  ((halfBallK n W y r) ∩ (bdrySetW n W)ᶜ)ᶜ

abbrev bigA (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) : Set W := bigB n W y r \ {y}

theorem bdryMinus_sub_bdrySetW (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) : bdryMinus n W y ⊆ bdrySetW n W := fun z hz => hz.1

theorem bigA_sub_bigB (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) : bigA n W y r ⊆ bigB n W y r := Set.diff_subset

theorem bdrySetW_sub_bigB (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) : bdrySetW n W ⊆ bigB n W y r := by
  intro z hz
  simp only [bigB, Set.mem_compl_iff, Set.mem_inter_iff]
  exact fun h => h.2 hz

theorem bdryMinus_sub_bigA (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) : bdryMinus n W y ⊆ bigA n W y r := by
  intro z hz
  exact ⟨bdrySetW_sub_bigB n W y r hz.1, fun hzy => hz.2 hzy⟩


/-- **(III)** The connecting map `δ'` of the triple `A ⊆ B' ⊆ W` is **onto**: its image is the
kernel of `H_n(B',A) → H_n(W,A)`, and `H_n(W,A) = H_n(W, W∖(K∩W°∪{y})) = 0`. -/
theorem bigA_eq (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) :
    bigA n W y r = (((halfBallK n W y r) ∩ (bdrySetW n W)ᶜ) ∪ {y})ᶜ := by
  rw [bigA, bigB, Set.diff_eq, Set.compl_union]

/-- `B'` is the complement of the interior part `K ∩ W°` of the half-ball, definitionally. -/
theorem bigB_eq (n : ℕ) (W : TopCat) [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (y : W) (r : ℝ) :
    bigB n W y r = ((halfBallK n W y r) ∩ (bdrySetW n W)ᶜ)ᶜ := rfl

/-! ## Bridges to the `Work.Orient` copies of the restriction maps

`Work.Orient.relChainsIncl` (the ORIENT copy, whose `RelH`-excluded-set form is `Work.Orient.relPunct`
and which appears in the hypothesis `Work.Orient.IsRelFundClass`) and
`Work.Cohomology.relCokerMap` (the plumbing copy, which is the `τ₃` of `tripleMap`) are the same map;
and the ORIENT copies compose. -/

/-- **`relChainsIncl` is `relCokerMap`**: the two spellings of the map of relative chain complexes
`C_*(X,A) ⟶ C_*(X,B)` induced by `A ⊆ B`. -/
theorem relChainsIncl_eq_relCokerMap (X : TopCat) {A B : Set X} (h : A ⊆ B) :
    Work.Orient.relChainsIncl X h = Work.Cohomology.relCokerMap X A B h := by
  apply (cancel_epi (cokernel.π (Work.Cohomology.inclChains X A))).1
  rw [Work.Cohomology.relCokerMap_comp_π]
  unfold Work.Orient.relChainsIncl Work.Cohomology.relChainsMapOf
  rw [Work.Cohomology.cokernel_π_map, Work.Cohomology.chainMap_id', Category.id_comp]

/-- `relChainsIncl` depends only on the pair of sets (not on the proof of the inclusion). -/
theorem relChainsIncl_congr_h {X : TopCat} {A B : Set X} (h h' : A ⊆ B) :
    Work.Orient.relChainsIncl X h = Work.Orient.relChainsIncl X h' := by
  rw [relChainsIncl_eq_relCokerMap X h]

/-- Functoriality of `relChainsIncl`. -/
theorem relChainsIncl_comp {X : TopCat} {A B C : Set X} (h₁ : A ⊆ B) (h₂ : B ⊆ C) :
    Work.Orient.relChainsIncl X h₁ ≫ Work.Orient.relChainsIncl X h₂
      = Work.Orient.relChainsIncl X (h₁.trans h₂) := by
  rw [relChainsIncl_eq_relCokerMap X h₁, relChainsIncl_eq_relCokerMap X h₂,
    relChainsIncl_eq_relCokerMap X (h₁.trans h₂)]
  exact Work.Cohomology.relCokerMap_comp h₁ h₂

/-- `relPunct` is the `relChainsIncl` of the complementary inclusion, definitionally. -/
theorem relPunct_eq_relChainsIncl (W : TopCat) (B : Set W) (x : W) (hx : x ∉ B) :
    Work.Orient.relPunct W B x hx
      = Work.Orient.relChainsIncl W (A := B) (B := {y : W | y ≠ x})
          (fun y hy hyx => hx (hyx ▸ hy)) := rfl

end

end Work.Orient.Boundary
