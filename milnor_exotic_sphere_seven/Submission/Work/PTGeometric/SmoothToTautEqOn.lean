import Submission.Work.PTGeometric.SmoothToTaut
import Submission.Work.PTGeometric.SmoothApprox

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# PTGEOMETRIC: G2 with the boundary values prescribed on a closed end only

`Work.PTGeometric.smoothMap_into_tautTotal` (`SmoothToTaut.lean`) smooths a continuous pair
`(P, v)` (matrix part, vector part) into the total space of the tautological bundle and keeps the
values on the **whole boundary** `∂M`.  The last mile of the Pontryagin–Thom construction needs the
same construction with a weaker requirement: the values must be kept on a **closed end** `S ⊆ ∂M`
(where the null-homotopy is the genuine collapse map and the preimage of the zero section is the
pieces), while on the rest of `∂M` the smoothed map is only required to be *close* to the original
one.

The two reasons this is the form needed are

* the null-homotopy `H : M → Th(γ_k)` is only known to be smooth into the manifold part `E` of the
  Thom space on a neighbourhood of the collapse end (the collapse map is smooth near the core,
  `Work.Tubular.normalCoord`), so G2's hypothesis "already `C^∞` on a neighbourhood of the boundary"
  cannot be met;
* the *values* of the smoothed map off `S` are irrelevant: the end preimage of the core is only read
  off on `S`, and the preimage in the interior is then made transverse by G3.

Everything else (the retraction `r` of the Grassmannian, the re-projection `v ↦ r (Pm) (ṽ)`) is
verbatim the proof of `smoothMap_into_tautTotal`.

## Main results

* `Work.PTGeometric.smoothApprox_eqOn_normedSpace`
* `Work.PTGeometric.smoothMap_into_tautTotal_eqOn`
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

/-- **G2 with the values prescribed on a closed end.**  A continuous map from a compact smooth
`(9+k)`-manifold with boundary into a normed space, which is `C^∞` on a neighbourhood of a closed
set `S`, can be smoothed while keeping its values on `S` **exactly** and being uniformly close to it.

This is Mathlib's `Continuous.exists_contMDiff_approx_and_eqOn` with the closed set `S`, exactly as in
`Work.PTGeometric.smoothApproximation` (which is the case `S = ∂M`). -/
theorem smoothApprox_eqOn_normedSpace {k : ℕ} (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : M → F) (hf : Continuous f) (S : Set M) (hS : IsClosed S)
    (V : Set M) (hVopen : IsOpen V) (hSV : S ⊆ V)
    (hfV : ContMDiffOn (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, F)) ∞ f V)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g : M → F,
      ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, F)) ∞ g ∧
      (∀ x ∈ S, g x = f x) ∧
      (∀ x : M, ‖g x - f x‖ < ε) := by
  obtain ⟨g, hg_approx, hg_eqOn, -⟩ :=
    hf.exists_contMDiff_approx_and_eqOn (𝓡∂ ((8 + k) + 1)) (⊤ : ℕ∞) continuous_const
      (fun _ => hε) hS (hVopen.mem_nhdsSet.mpr hSV) hfV
  exact ⟨fun x => g x, g.contMDiff, fun x hx => hg_eqOn hx,
    fun x => by simpa [dist_eq_norm] using hg_approx x⟩

/-- **G2, concretely, with the boundary values prescribed on a closed end `S`.**

Let `M` be a compact `T2` smooth `(9+k)`-manifold with boundary, `P : M → ℝⁿ →L[ℝ] ℝⁿ` a continuous
operator-valued map which is within `1/8` of the set of orthogonal rank-`k` projections everywhere,
`v : M → ℝⁿ` a continuous vector-valued map, and `S ⊆ M` a **closed** set such that

* `(P, v)` is `C^∞` on a neighbourhood of `S`,
* on `S`, the matrix part `P` is *already* an orthogonal rank-`k` projection and `P x (v x) = v x`.

Then there are `C^∞` maps `P' : M → ℝⁿ →L[ℝ] ℝⁿ` and `v' : M → ℝⁿ` with

* `P' x` an orthogonal rank-`k` projection and `P' x (v' x) = v' x` for every `x` (`(P', v')` takes
  values in the total space of the tautological bundle),
* `P' = P` and `v' = v` on `S`.

The proof is that of `smoothMap_into_tautTotal` with the closed set `S` in place of `∂M`. -/
theorem smoothMap_into_tautTotal_eqOn (n k : ℕ) (hk : k ≤ n) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M] [CompactSpace M] [T2Space M]
    (P : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (v : M → EuclideanSpace ℝ (Fin n))
    (hP : Continuous P) (hv : Continuous v)
    (S : Set M) (hSclosed : IsClosed S)
    (V : Set M) (hVopen : IsOpen V) (hSV : S ⊆ V)
    (hPV : ContMDiffOn (𝓡∂ ((8 + k) + 1))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞ P V)
    (hvV : ContMDiffOn (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ v V)
    (hclose : ∀ x : M, ∃ Q : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      ContinuousLinearMap.adjoint Q = Q ∧ Q * Q = Q ∧
        LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) Q = (k : ℝ) ∧ ‖P x - Q‖ < 1/8)
    (hSProj : ∀ x ∈ S, ContinuousLinearMap.adjoint (P x) = P x ∧ P x * P x = P x ∧
      LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (P x) = (k : ℝ))
    (hSMem : ∀ x ∈ S, P x (v x) = v x) :
    ∃ (P' : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (v' : M → EuclideanSpace ℝ (Fin n)),
      ContMDiff (𝓡∂ ((8 + k) + 1))
        (𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) P' ∧
      ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ((⊤ : ℕ∞) : WithTop ℕ∞) v' ∧
      ContMDiff (𝓡∂ ((8 + k) + 1))
        (𝓘(ℝ, (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) × EuclideanSpace ℝ (Fin n)))
        ∞ (fun x => (P' x, v' x)) ∧
      (∀ x : M, ContinuousLinearMap.adjoint (P' x) = P' x ∧ P' x * P' x = P' x ∧
        LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (P' x) = (k : ℝ) ∧ P' x (v' x) = v' x) ∧
      (∀ x ∈ S, P' x = P x ∧ v' x = v x) := by
  obtain ⟨U, r, hUopen, hGrU, hCont, hFix, hMaps, hball⟩ := grassmannianRetraction n k hk
  -- smooth the two components separately, keeping the values on `S`
  obtain ⟨Pm, hPm_sm, hPm_eq, hPm_close⟩ :=
    smoothApprox_eqOn_normedSpace (k := k) M P hP S hSclosed V hVopen hSV hPV (1 / 8) (by norm_num)
  obtain ⟨vm, hvm_sm, hvm_eq, hvm_close⟩ :=
    smoothApprox_eqOn_normedSpace (k := k) M v hv S hSclosed V hVopen hSV hvV (1 / 8) (by norm_num)
  have hPm_U : ∀ x : M, Pm x ∈ U := by
    intro x
    obtain ⟨Q, hQ1, hQ2, hQ3, hQd⟩ := hclose x
    refine hball (Pm x) ⟨Q, hQ1, hQ2, hQ3, ?_⟩
    calc ‖Pm x - Q‖ = ‖(Pm x - P x) + (P x - Q)‖ := by abel_nf
      _ ≤ ‖Pm x - P x‖ + ‖P x - Q‖ := norm_add_le _ _
      _ < 1/8 + 1/8 := by linarith [hPm_close x, hQd]
      _ = 1/4 := by norm_num
  have hP'_sm : ContMDiff (𝓡∂ ((8 + k) + 1))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞
      (fun x : M => r (Pm x)) :=
    ContMDiffOn.comp_contMDiff hCont.contMDiffOn hPm_sm hPm_U
  have hv'_sm : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun x : M => r (Pm x) (vm x)) :=
    hP'_sm.clm_apply hvm_sm
  refine ⟨fun x => r (Pm x), fun x => r (Pm x) (vm x), hP'_sm, hv'_sm,
    ContMDiff.prodMk_space hP'_sm hv'_sm, ?_, ?_⟩
  · intro x
    obtain ⟨h1, h2, h3⟩ := hMaps (Pm x) (hPm_U x)
    exact ⟨h1, h2, h3, by rw [← ContinuousLinearMap.mul_apply, h2]⟩
  · intro x hx
    have hPmx : Pm x = P x := hPm_eq x hx
    have hvmx : vm x = v x := hvm_eq x hx
    obtain ⟨hb1, hb2, hb3⟩ := hSProj x hx
    refine ⟨?_, ?_⟩
    · show r (Pm x) = P x
      rw [hPmx]
      exact hFix (P x) hb1 hb2 hb3
    · have hrP : r (P x) = P x := hFix (P x) hb1 hb2 hb3
      show r (Pm x) (vm x) = v x
      rw [hPmx, hvmx, hrP]
      exact hSMem x hx

end

end Work.PTGeometric
