import Mathlib
import Submission.Work.Surf.transfer_defs
import Submission.Work.Surf.zeros_finite_euc

/-!
# Persistence of the regularity of the zeros of a `C¹` self-map of the plane

`Work.Surf.Trans.zeros_regular_persist` says: if `F : 𝔼² → 𝔼²` is `C¹`, does not vanish on the
boundary `sqBdry` of the unit square, and has *surjective* derivative at every zero in `sqBox`, then
the same conclusion holds for every `C¹` map `G` which is `δ`-close to `F` in the sense
`‖G x - F x‖ < δ` **and** `‖fderiv ℝ G x - fderiv ℝ F x‖ < δ` for `x ∈ sqBox`, for some `δ > 0`.

The statement is a uniform (in `x`) stability statement for the condition "`fderiv` is surjective at
a zero", and is exactly the *regularity* half of the perturbation lemma
`Work.Surf.smooth_reduction` (the *counting* half is `Work.Surf.ncard_zeros_persist`).

## Proof

Everything is a compactness argument on the two compact sets

* `S = {x ∈ sqBox | fderiv ℝ F x is not surjective}` — a closed subset of the compact square.  A
  non-regular point of the square is not a zero of `F` (regularity of the zeros is exactly `hreg`),
  so `‖F‖` is bounded below by a positive constant `m` on `S`;
* `K = {x ∈ sqBox | ‖F x‖ ≤ m/2}` — a closed subset of the square.  On `K`, `fderiv ℝ F` is
  surjective, so the continuous function `x ↦ infDist (fderiv ℝ F x) B` (where `B` is the closed set
  of non-surjective continuous linear maps `𝔼² →L[ℝ] 𝔼²`) is strictly positive and hence bounded
  below by some `ε > 0` on `K`.

A `G` which is `δ`-close to `F` with `δ := min (m/2) ε / 2` therefore has all its zeros `x ∈ sqBox`
inside `K` (since `‖F x‖ = ‖F x - G x‖ ≤ ‖G x - F x‖ < δ < m/2`), and at such a point
`‖fderiv ℝ G x - fderiv ℝ F x‖ < δ < ε`, so `fderiv ℝ G x` is not in `B`: it is surjective.

`F`'s non-vanishing on the boundary `sqBdry` is not needed for the argument; it is part of the
interface of the request because that is the situation in which the lemma is applied.
-/

namespace Work.Surf.Trans

set_option linter.unusedVariables false

open Set Metric Filter
open scoped Topology

noncomputable section

/-- **Surjectivity is an open condition on continuous linear maps** into a finite-dimensional space
(the target is finite-dimensional; the domain is arbitrary).  A surjective `L₀` has a right inverse
`R'`; the maps `L` with `‖L.comp R' - 1‖ < 1` form a neighbourhood of `L₀`, and on it `L.comp R'` is
invertible, so `L` is surjective. -/
theorem isOpen_setOf_surjective_clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] :
    IsOpen {L : E →L[ℝ] F | Function.Surjective L} := by
  rw [isOpen_iff_mem_nhds]
  intro L₀ hL₀
  obtain ⟨R, hR⟩ := LinearMap.exists_rightInverse_of_surjective (L₀ : E →ₗ[ℝ] F)
    (LinearMap.range_eq_top.mpr hL₀)
  have hRcont : Continuous R := LinearMap.continuous_of_finiteDimensional R
  let R' : F →L[ℝ] E := ⟨R, hRcont⟩
  have hR'coe : (R' : F → E) = R := rfl
  have hR' : L₀.comp R' = ContinuousLinearMap.id ℝ F := by
    ext x
    rw [ContinuousLinearMap.comp_apply, hR'coe, ContinuousLinearMap.id_apply]
    exact DFunLike.congr_fun hR x
  have hcont : Continuous fun L : E →L[ℝ] F => L.comp R' := by
    have h1 : Continuous fun L : E →L[ℝ] F =>
        ((ContinuousLinearMap.compL ℝ F E F) L) R' :=
      (ContinuousLinearMap.compL ℝ F E F).continuous.clm_apply continuous_const
    simpa [ContinuousLinearMap.compL_apply] using h1
  have hnbhd : {L : E →L[ℝ] F | ‖L.comp R' - ContinuousLinearMap.id ℝ F‖ < 1} ∈ 𝓝 L₀ := by
    have hc : Continuous fun L : E →L[ℝ] F => ‖L.comp R' - ContinuousLinearMap.id ℝ F‖ :=
      (hcont.sub continuous_const).norm
    refine (isOpen_lt hc (continuous_const : Continuous fun _ : E →L[ℝ] F => (1 : ℝ))).mem_nhds ?_
    show ‖L₀.comp R' - ContinuousLinearMap.id ℝ F‖ < 1
    rw [hR', sub_self, norm_zero]
    norm_num
  refine Filter.mem_of_superset hnbhd ?_
  intro L hL
  have hunit : IsUnit (L.comp R') := by
    have hsplit : L.comp R' = ContinuousLinearMap.id ℝ F -
        (ContinuousLinearMap.id ℝ F - L.comp R') := by abel
    rw [hsplit]
    exact isUnit_one_sub_of_norm_lt_one (by simpa [norm_sub_rev] using hL)
  have hbij : Function.Bijective (L.comp R') :=
    ContinuousLinearMap.isUnit_iff_bijective.mp hunit
  intro y
  obtain ⟨x, hx⟩ := hbij.2 y
  exact ⟨R' x, hx⟩

/-- **The set of non-surjective continuous linear maps `𝔼² →L[ℝ] 𝔼²` is closed** (complement of the
open set of surjective maps), and it is non-trivial: it contains `0`. -/
lemma isClosed_setOf_not_surjective_clm :
    IsClosed {L : E2 →L[ℝ] E2 | ¬ Function.Surjective L} :=
  (isOpen_setOf_surjective_clm (E := E2) (F := E2)).isClosed_compl

lemma not_surjective_zero_clm : ¬ Function.Surjective (0 : E2 →L[ℝ] E2) := by
  intro hsurj
  obtain ⟨y, hy⟩ := hsurj e0
  have h0 : (e0 : E2) = 0 := by simpa using hy.symm
  have h1 : (e0 : E2) 0 = 1 := e0_apply_zero
  rw [h0] at h1
  simp at h1

theorem zeros_regular_persist (F : E2 → E2) (hF : ContDiff ℝ 1 F)
    (hbdry : ∀ x ∈ sqBdry, F x ≠ 0)
    (hreg : ∀ x ∈ sqBox, F x = 0 → Function.Surjective (fderiv ℝ F x)) :
    ∃ δ > 0, ∀ G : E2 → E2, ContDiff ℝ 1 G →
      (∀ x ∈ sqBox, ‖G x - F x‖ < δ) → (∀ x ∈ sqBox, ‖fderiv ℝ G x - fderiv ℝ F x‖ < δ) →
      ∀ x ∈ sqBox, G x = 0 → Function.Surjective (fderiv ℝ G x) := by
  classical
  have hfd : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hclosedB : IsClosed {L : E2 →L[ℝ] E2 | ¬ Function.Surjective L} :=
    isClosed_setOf_not_surjective_clm
  -- The set of non-regular points of `F` in the square, and the lower bound `m` for `‖F‖` on it.
  set S : Set E2 := {x | x ∈ sqBox ∧ ¬ Function.Surjective (fderiv ℝ F x)} with hSdef
  have hSclosed : IsClosed S := by
    rw [hSdef]
    exact isClosed_sqBox_euc.inter (hclosedB.preimage hfd)
  have hScpt : IsCompact S :=
    IsCompact.of_isClosed_subset isCompact_sqBox_euc hSclosed (fun x hx => hx.1)
  have hSpos : ∀ x ∈ S, 0 < ‖F x‖ := by
    intro x hx
    rw [norm_pos_iff]
    exact fun h0 => hx.2 (hreg x hx.1 h0)
  obtain ⟨m, hmpos, hmle⟩ :=
    exists_pos_le_of_isCompact_of_pos hF.continuous.norm hScpt hSpos
  -- On `K := {x ∈ sqBox | ‖F x‖ ≤ m/2}` the derivative of `F` is surjective.
  set K : Set E2 := {x | x ∈ sqBox ∧ ‖F x‖ ≤ m / 2} with hKdef
  have hKclosed : IsClosed K := by
    rw [hKdef]
    exact isClosed_sqBox_euc.inter (isClosed_le hF.continuous.norm continuous_const)
  have hKcpt : IsCompact K :=
    IsCompact.of_isClosed_subset isCompact_sqBox_euc hKclosed (fun x hx => hx.1)
  have hKsurj : ∀ x ∈ K, Function.Surjective (fderiv ℝ F x) := by
    intro x hx
    by_contra hbad
    have h1 : m ≤ ‖F x‖ := hmle x ⟨hx.1, hbad⟩
    have h2 : ‖F x‖ ≤ m / 2 := hx.2
    linarith
  -- Uniformity of the surjectivity on `K`, via the closed set `B` of non-surjective maps.
  set B : Set (E2 →L[ℝ] E2) := {L | ¬ Function.Surjective L} with hBdef
  have hBclosed : IsClosed B := hclosedB
  have hBne : B.Nonempty := ⟨0, not_surjective_zero_clm⟩
  have hinfcont : Continuous (fun x : E2 => Metric.infDist (fderiv ℝ F x) B) :=
    (Metric.continuous_infDist_pt B).comp hfd
  have hinfpos : ∀ x ∈ K, 0 < Metric.infDist (fderiv ℝ F x) B := by
    intro x hx
    exact (hBclosed.notMem_iff_infDist_pos hBne).mp (fun hmem => hmem (hKsurj x hx))
  obtain ⟨ε, hεpos, hεle⟩ :=
    exists_pos_le_of_isCompact_of_pos hinfcont hKcpt hinfpos
  have hBclaim : ∀ x ∈ K, ∀ N : E2 →L[ℝ] E2,
      ‖N - fderiv ℝ F x‖ < ε → Function.Surjective N := by
    intro x hx N hN
    by_contra hnb
    have h1 : ε ≤ Metric.infDist (fderiv ℝ F x) B := hεle x hx
    have hNB : N ∈ B := by rw [hBdef]; exact hnb
    have h2 : Metric.infDist (fderiv ℝ F x) B ≤ ‖N - fderiv ℝ F x‖ := by
      have h := Metric.infDist_le_dist_of_mem (x := fderiv ℝ F x) (s := B) (y := N) hNB
      rwa [dist_eq_norm, norm_sub_rev] at h
    linarith
  refine ⟨min (m / 2) ε / 2, ?_, ?_⟩
  · have : 0 < min (m / 2) ε := lt_min (by linarith) hεpos
    linarith
  intro G hG hG0 hG1 x hxbox hGx
  have hδm : min (m / 2) ε / 2 < m / 2 := by
    have h1 : min (m / 2) ε ≤ m / 2 := min_le_left _ _
    linarith
  have hδε : min (m / 2) ε / 2 < ε := by
    have h1 : min (m / 2) ε ≤ ε := min_le_right _ _
    linarith
  have hxK : x ∈ K := by
    refine ⟨hxbox, ?_⟩
    have h1 : ‖F x‖ = ‖G x - F x‖ := by simp [hGx]
    have h2 : ‖G x - F x‖ < min (m / 2) ε / 2 := hG0 x hxbox
    linarith
  exact hBclaim x hxK (fderiv ℝ G x) (by
    have h := hG1 x hxbox
    linarith)

end

end Work.Surf.Trans
