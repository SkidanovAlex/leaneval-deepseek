import Mathlib
import Submission.Work.StemsB.BundlePullbackHomology

/-!
# The preimage of a subset under `evalOne` is the pullback over the inclusion

For Step I of the sphere-specific route (`CONTRACTS.md` §F1) one needs the *preimage*
`p⁻¹(D) = {γ : PathSpace X x₀ // (evalOne X x₀) γ ∈ D}` of a subset `D ⊆ X` under the evaluation
map `evalOne X x₀ : PathSpace X x₀ → X`, because the path–loop fibration is trivial over a disc
`D ⊆ Sⁿ`.  The preimage is the pullback `Work.StemsB.bundlePullback X x₀ ↥D (inclusion)` of the
fibration over the inclusion `↥D ↪ X` — that is the content of `evalOnePreimageHomeo` below — so
the triviality statement `Work.StemsB.bundlePullback_homotopyEquiv` and its homology form
`Work.StemsB.isZero_homology_bundlePullback_iff` apply to preimages of based-contractible subsets.

* `Work.StemsB.evalOnePreimage D` — the preimage of `D` under `evalOne X x₀`.
* `Work.StemsB.evalOnePreimageHomeo D` — the pullback over `↥D ↪ X` is homeomorphic to it.
* `Work.StemsB.isZero_homology_evalOnePreimage_iff` — for a based contraction `c` of `D` at `d₀`:
  `H_m(p⁻¹D;ℚ) = 0 ↔ H_m(Path x₀ d₀;ℚ) = 0`.
-/

open scoped Topology

namespace Work.StemsB

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-- The inclusion `↥D ↪ X` of a subset, as a continuous map. -/
def subtypeInclCM (D : Set X) : ContinuousMap ↥D X :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The preimage of `D` under `evalOne X x₀`, as a type. -/
def evalOnePreimage (D : Set X) : Type _ :=
  {γ : PathSpace X x₀ // (evalOne X x₀) γ ∈ D}

instance instTopologicalSpaceEvalOnePreimage (D : Set X) :
    TopologicalSpace (evalOnePreimage (x₀ := x₀) D) :=
  inferInstanceAs (TopologicalSpace {γ : PathSpace X x₀ // (evalOne X x₀) γ ∈ D})

@[simp]
theorem mem_evalOnePreimage {D : Set X} (q : evalOnePreimage (x₀ := x₀) D) :
    (evalOne X x₀) q.1 ∈ D := q.2

/-- **The preimage of `D` under `evalOne` is the pullback of the path–loop fibration over the
inclusion `↥D ↪ X`.** -/
def evalOnePreimageHomeo (D : Set X) :
    (bundlePullback X x₀ ↥D (subtypeInclCM D)) ≃ₜ (evalOnePreimage (x₀ := x₀) D) where
  toFun p := ⟨p.1.2, by have h := p.2; rw [h]; exact p.1.1.2⟩
  invFun q := ⟨(⟨(evalOne X x₀) q.1, q.2⟩, q.1), rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact p.2
    · rfl
  right_inv q := by
    apply Subtype.ext
    rfl
  continuous_toFun := by
    exact Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) _
  continuous_invFun := by
    refine Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _
    · exact Continuous.subtype_mk ((evalOne X x₀).continuous.comp continuous_subtype_val) _
    · exact continuous_subtype_val

/-- **The rational homology of `p⁻¹D` is that of the fibre over the point `d₀` of a based
contraction of `D`.**  This is the triviality of the path–loop fibration over a contractible base,
in exactly the shape Step I uses. -/
theorem isZero_homology_evalOnePreimage_iff (D : Set X) (d₀ : ↥D)
    (c : ContinuousMap (↥D × unitInterval) ↥D)
    (hc0 : ∀ u, c (u, 0) = u) (hc1 : ∀ u, c (u, 1) = d₀) (hcb : ∀ t, c (d₀, t) = d₀)
    (m : ℕ) :
    CategoryTheory.Limits.IsZero
        ((Work.Cohomology.singularChains ℚ
          (TopCat.of (evalOnePreimage (x₀ := x₀) D))).homology m) ↔
      CategoryTheory.Limits.IsZero
        ((Work.Cohomology.singularChains ℚ (TopCat.of (Path x₀ (d₀ : X)))).homology m) := by
  have hbridge :
      CategoryTheory.Limits.IsZero
          ((Work.Cohomology.singularChains ℚ
            (TopCat.of (evalOnePreimage (x₀ := x₀) D))).homology m) ↔
        CategoryTheory.Limits.IsZero
          ((Work.Cohomology.singularChains ℚ
            (TopCat.of (bundlePullback X x₀ ↥D (subtypeInclCM D)))).homology m) :=
    ⟨fun hh => isZero_homology_of_homotopyEquiv_ring ℚ
        (X := TopCat.of (bundlePullback X x₀ ↥D (subtypeInclCM D)))
        (Y := TopCat.of (evalOnePreimage (x₀ := x₀) D))
        (evalOnePreimageHomeo D).toHomotopyEquiv m hh,
      fun hh => isZero_homology_of_homotopyEquiv_ring ℚ
        (X := TopCat.of (evalOnePreimage (x₀ := x₀) D))
        (Y := TopCat.of (bundlePullback X x₀ ↥D (subtypeInclCM D)))
        (evalOnePreimageHomeo D).symm.toHomotopyEquiv m hh⟩
  exact hbridge.trans
    (isZero_homology_bundlePullback_iff X x₀ ↥D (subtypeInclCM D) d₀ c hc0 hc1 hcb m)

end

end Work.StemsB
