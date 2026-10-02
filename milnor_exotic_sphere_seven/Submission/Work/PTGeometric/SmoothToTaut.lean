import Submission.Work.PTGeometric.SmoothApprox
import Submission.Work.PTGeometric.grassmannianRetraction

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: G2 made concrete — the smoothed null-homotopy takes values in the total space

`Work.PTGeometric.smoothApproximation` (`SmoothApprox.lean`) smooths a continuous map which is
already smooth near the boundary.  In the Pontryagin–Thom construction the map in question is only
known *in ambient coordinates*: a pair `(P, v)` of a matrix-valued and a vector-valued map, where
`P` is close to a projection `Q` (the Gauss map of the pieces, which is what the collapse map
produces) and `v` lies in the image of `P` on the boundary.  The blueprint's step G2 then says: smooth
the pair, retract the matrix part with the retraction `r` of
`Work.PTGeometric.grassmannianRetraction` (which needs the smoothed matrix to be within `1/4` of a
projection — hence the closeness hypothesis), and re-project the vector part by the *new* projection:
`P' := r ∘ Pm`, `v' := P' ṽ`.  The result is a **smooth** map whose values lie in the total space of
the tautological bundle (a projection together with a vector of its image) and whose boundary values
are exactly those of the original map.

This is the smoothing half of the geometric construction, with the two ingredients proved in this
area: `smoothApproximation` (G2) and `grassmannianRetraction` (G1).  What remains for the null-bordism
is the transversality half G3 (`NormalAction.lean`) and the identification of the ends.

## Main result

* `Work.PTGeometric.smoothMap_into_tautTotal`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

/-- **G2, concretely: a smooth map into the total space of the tautological bundle with prescribed
boundary values.**

Let `M` be a compact `T2` smooth `(9+k)`-manifold with boundary, `P : M → ℝⁿ →L[ℝ] ℝⁿ` a continuous
operator-valued map which is within `1/8` of the set of orthogonal rank-`k` projections everywhere,
`v : M → ℝⁿ` a continuous vector-valued map with `P x (v x) = v x` for `x ∈ ∂M`, and assume that
`(P, v)` is `C^∞` on a neighbourhood of `∂M` and that on `∂M` the matrix part `P` is *already* an
orthogonal rank-`k` projection.  Then there are a `C^∞` map `P' : M → ℝⁿ →L[ℝ] ℝⁿ` and a `C^∞` map
`v' : M → ℝⁿ` such that

* `P' x` is an orthogonal rank-`k` projection and `P' x (v' x) = v' x` for every `x` — i.e. `x ↦ (P' x, v' x)`
  takes values in the total space of the tautological bundle (a projection together with a vector of
  its image);
* `P' = P` and `v' = v` on `∂M` — the boundary values are preserved exactly.

The construction is the blueprint's G2: smooth the pair with `smoothApproximation_normedSpace`,
retract the matrix part with the retraction of `grassmannianRetraction` (applicable because the
smoothed matrix is still within `1/4` of the projection `Q`), and re-project the vector part by the new
projection.  The closeness hypothesis is what the collapse map of the pieces supplies (the Gauss map of
`V ⊂ ℝⁿ` takes values in `Gr_k(ℝⁿ)`, and the smoothing error can be made arbitrarily small). -/
theorem smoothMap_into_tautTotal (n k : ℕ) (hk : k ≤ n) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M]
    (P : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : M → EuclideanSpace ℝ (Fin n))
    (hP : Continuous P) (hv : Continuous v)
    (V : Set M) (hVopen : IsOpen V) (hbd : (𝓡∂ ((8 + k) + 1)).boundary M ⊆ V)
    (hPV : ContMDiffOn (𝓡∂ ((8 + k) + 1))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞ P V)
    (hvV : ContMDiffOn (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ v V)
    (hclose : ∀ x : M, ∃ Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      ContinuousLinearMap.adjoint Q = Q ∧ Q * Q = Q ∧
        LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) Q = (k : ℝ) ∧ ‖P x - Q‖ < 1/8)
    (hbndProj : ∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary M,
      ContinuousLinearMap.adjoint (P x) = P x ∧ P x * P x = P x ∧
        LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (P x) = (k : ℝ))
    (hbndMem : ∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary M, P x (v x) = v x) :
    ∃ (P' : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (v' : M → EuclideanSpace ℝ (Fin n)),
      ContMDiff (𝓡∂ ((8 + k) + 1))
        (𝓘(ℝ, (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n)))
        ∞ (fun x => (P' x, v' x)) ∧
      (∀ x : M, ContinuousLinearMap.adjoint (P' x) = P' x ∧ P' x * P' x = P' x ∧
        LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (P' x) = (k : ℝ) ∧ P' x (v' x) = v' x) ∧
      (∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary M, P' x = P x ∧ v' x = v x) := by
  obtain ⟨U, r, hUopen, hGrU, hCont, hFix, hMaps, hball⟩ := grassmannianRetraction n k hk
  -- smooth the two components separately, keeping the boundary values
  obtain ⟨Pm, hPm_sm, hPm_eq, hPm_close⟩ :=
    smoothApproximation_normedSpace (k := k) M P hP V hVopen hbd hPV (1 / 8) (by norm_num)
  obtain ⟨vm, hvm_sm, hvm_eq, hvm_close⟩ :=
    smoothApproximation_normedSpace (k := k) M v hv V hVopen hbd hvV (1 / 8) (by norm_num)
  have hPm_U : ∀ x : M, Pm x ∈ U := by
    intro x
    obtain ⟨Q, hQ1, hQ2, hQ3, hQd⟩ := hclose x
    refine hball (Pm x) ⟨Q, hQ1, hQ2, hQ3, ?_⟩
    calc ‖Pm x - Q‖ = ‖(Pm x - P x) + (P x - Q)‖ := by abel_nf
      _ ≤ ‖Pm x - P x‖ + ‖P x - Q‖ := norm_add_le _ _
      _ < 1/8 + 1/8 := by linarith [hPm_close x, hQd]
      _ = 1/4 := by norm_num
  -- retract the matrix part and re-project the vector part
  have hP'_sm : ContMDiff (𝓡∂ ((8 + k) + 1))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
      (fun x : M => r (Pm x)) :=
    ContMDiffOn.comp_contMDiff hCont.contMDiffOn hPm_sm hPm_U
  have hv'_sm : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun x : M => r (Pm x) (vm x)) :=
    hP'_sm.clm_apply hvm_sm
  refine ⟨fun x => r (Pm x), fun x => r (Pm x) (vm x),
    ContMDiff.prodMk_space hP'_sm hv'_sm, ?_, ?_⟩
  · intro x
    obtain ⟨h1, h2, h3⟩ := hMaps (Pm x) (hPm_U x)
    exact ⟨h1, h2, h3, by rw [← ContinuousLinearMap.mul_apply, h2]⟩
  · intro x hx
    have hPmx : Pm x = P x := hPm_eq x hx
    have hvmx : vm x = v x := hvm_eq x hx
    obtain ⟨hb1, hb2, hb3⟩ := hbndProj x hx
    refine ⟨?_, ?_⟩
    · show r (Pm x) = P x
      rw [hPmx]
      exact hFix (P x) hb1 hb2 hb3
    · have hrP : r (P x) = P x := hFix (P x) hb1 hb2 hb3
      show r (Pm x) (vm x) = v x
      rw [hPmx, hvmx, hrP]
      exact hbndMem x hx

end

end Work.PTGeometric
