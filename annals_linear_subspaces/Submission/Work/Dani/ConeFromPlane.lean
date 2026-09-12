import Mathlib
import ChallengeDeps
import Submission.Work.Dani.LineConjunct1
import Submission.Work.Dani.EscapeGlue
import Submission.Work.ModelStar.ModelStarHeight

/-!
# From a rational-plane Dirichlet property to the §3 cone obligation

`Submission.LineConjunct1.conjunct1_of_obligations` reduces conjunct 1 of de Saxcé's Theorem 1 to
the cone obligation `ConeObligation l k W` at every `ℓ`-plane `W`.  This file supplies the two
pieces of plumbing that connect the *flow* (Prop 5 / Theorem 9) route to that obligation:

* **`cone_of_planeResidual_le`** — the transfer from the operator-norm distance
  `planeResidual V W ≤ δ` (which is what the interior-power/flow estimates produce, via the
  bridge `distSubspaces = planeResidual`) to the *whole-span cone condition*
  `∀ v ∈ V, ‖v − π_W v‖ ≤ ε‖π_W v‖` with aperture `ε = 2δ`;

* **`coneObligation_of_dirichlet_property`** — if for every `ε ∈ (0,1]` there is a rational
  `k`-plane with `d(v,W) ≤ ε/2` and `H(v) ≤ C ε^{−k(d−ℓ)/d}`, then `ConeObligation l k W` holds
  (converting the rational plane into its `ℤ`-basis family, whose wedge norm is the height).

Module `Submission.Work.Dani.ConeFromPlane`, namespace `Submission.ConeFromPlane`.
-/

noncomputable section

open LinearSubspaces Module Real
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.ConeFromPlane

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℤᵈ" => intPoints

/-- **The cone condition from a residual bound.**  If the maximal residual of unit vectors of `V`
against `W` is at most `δ ≤ 1/2`, then every vector of `V` lies in the cone of aperture `2δ`
around `W`. -/
theorem cone_of_planeResidual_le {V W : Submodule ℝ ℝᵈ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (h : Submission.ProjectionDistance.planeResidual V W ≤ δ) :
    ∀ u ∈ V, ‖u - (W.starProjection u : ℝᵈ)‖ ≤ (2 * δ) * ‖(W.starProjection u : ℝᵈ)‖ := by
  intro u hu
  by_cases hu0 : u = 0
  · subst hu0; simp
  have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  -- the unit vector `u/‖u‖` and its residual bound
  set u' : ℝᵈ := (‖u‖)⁻¹ • u with hu'def
  have hu'V : u' ∈ V := Submodule.smul_mem _ _ hu
  have hu'n : ‖u'‖ = 1 := by
    rw [hu'def, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn, inv_mul_cancel₀ hn.ne']
  have hres : ‖u' - (W.starProjection u' : ℝᵈ)‖ ≤ δ :=
    le_trans (le_csSup (Submission.EscapeGlue.bddAbove_residualSet V W)
      ⟨u', hu'V, hu'n, rfl⟩) h
  -- scale back
  have hsub : u - (W.starProjection u : ℝᵈ) = ‖u‖ • (u' - (W.starProjection u' : ℝᵈ)) := by
    rw [hu'def, smul_sub, map_smul, smul_smul, smul_smul, mul_inv_cancel₀ hn.ne', one_smul,
      one_smul]
  have hproj : (W.starProjection u : ℝᵈ) = ‖u‖ • (W.starProjection u' : ℝᵈ) := by
    rw [hu'def, map_smul, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  have h1 : ‖u - (W.starProjection u : ℝᵈ)‖ ≤ δ * ‖u‖ := by
    rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hn]
    have hle := mul_le_mul_of_nonneg_left hres hn.le
    linarith
  -- Pythagoras: `‖u‖² = ‖π_W u‖² + ‖u − π_W u‖²`
  have hpy : ‖(W.starProjection u : ℝᵈ)‖ ^ 2 + ‖u - (W.starProjection u : ℝᵈ)‖ ^ 2 = ‖u‖ ^ 2 := by
    have h2 := Submodule.norm_sq_eq_add_norm_sq_starProjection u W
    have h3 : ((Wᗮ).starProjection u : ℝᵈ) = u - (W.starProjection u : ℝᵈ) := by
      have h := congrFun (congrArg DFunLike.coe (Submodule.starProjection_orthogonal (𝕜 := ℝ) W)) u
      simp only [sub_apply, ContinuousLinearMap.id_apply] at h
      exact h
    rw [h3] at h2
    exact h2.symm
  -- hence `‖π_W u‖² ≥ (1 − δ²)‖u‖²`
  have h4 : (1 - δ ^ 2) * ‖u‖ ^ 2 ≤ ‖(W.starProjection u : ℝᵈ)‖ ^ 2 := by
    have h5 : ‖u - (W.starProjection u : ℝᵈ)‖ ^ 2 ≤ δ ^ 2 * ‖u‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) h1 2
      rwa [mul_pow] at this
    linarith [hpy, h5]
  have hδ2 : δ ^ 2 ≤ 1 / 4 := by nlinarith [hδ1]
  have h6 : (3 / 4 : ℝ) * ‖u‖ ^ 2 ≤ ‖(W.starProjection u : ℝᵈ)‖ ^ 2 := by
    nlinarith [h4, hδ2, sq_nonneg ‖u‖]
  have h7 : ‖u‖ ≤ 2 * ‖(W.starProjection u : ℝᵈ)‖ := by
    have hnn : 0 ≤ ‖(W.starProjection u : ℝᵈ)‖ := norm_nonneg _
    have := (sq_le_sq₀ (norm_nonneg u) (by linarith : (0:ℝ) ≤ 2 * ‖(W.starProjection u : ℝᵈ)‖))
    apply this.mp
    nlinarith [h6]
  calc ‖u - (W.starProjection u : ℝᵈ)‖ ≤ δ * ‖u‖ := h1
    _ ≤ δ * (2 * ‖(W.starProjection u : ℝᵈ)‖) := mul_le_mul_of_nonneg_left h7 hδ.le
    _ = (2 * δ) * ‖(W.starProjection u : ℝᵈ)‖ := by ring

/-- **From the rational-plane Dirichlet property to the cone obligation.** -/
theorem coneObligation_of_dirichlet_property {l k : ℕ} (hk1 : 1 ≤ k) (hkl : k ≤ l) (_hld : l < d)
    (W : Submodule ℝ ℝᵈ) (hW : Module.finrank ℝ W = l)
    {C : ℝ} (hC : 0 < C)
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ v : Submodule ℝ ℝᵈ, ∃ hv : IsRational v,
      Module.finrank ℝ v = k ∧ distSubspaces v W ≤ ε / 2 ∧
      height v hv ≤ C * ε ^ (-((k : ℝ) * ((d - l : ℕ) : ℝ)) / (d : ℝ))) :
    Submission.LineConjunct1.ConeObligation (d := d) l k W := by
  classical
  have hl0 : 0 < l := lt_of_lt_of_le (Nat.one_le_iff_ne_zero.mpr (by omega)) hkl
  refine ⟨C, hC, fun ε hε hε1 => ?_⟩
  obtain ⟨v, hv, hvk, hdist, hheight⟩ := h ε hε hε1
  set m : Fin k → ℝᵈ := fun i => Submission.Heights.cbFamily v hv (Fin.cast hvk.symm i) with hmdef
  have hmem : ∀ i, m i ∈ ℤᵈ := by
    intro i
    refine Submission.EscapeGlue.imageLattice_le_intPoints v ?_
    rw [← Submission.Heights.chosenBasis_span_lattice v hv]
    exact Submodule.subset_span ⟨Fin.cast hvk.symm i, rfl⟩
  have hZ : LinearIndependent ℤ m := by
    have h1 : LinearIndependent ℤ (Submission.Heights.cbFamily v hv) :=
      Submission.Heights.chosenBasis_linearIndependent v hv
    have h2 := h1.comp (Fin.cast hvk.symm) (Fin.cast_injective hvk.symm)
    simpa [hmdef, Function.comp_def] using h2
  have hspan : Submodule.span ℝ (Set.range m) = v := by
    have hrange : Set.range m = Set.range (Submission.Heights.cbFamily v hv) := by
      rw [hmdef, show (fun i : Fin k => Submission.Heights.cbFamily v hv (Fin.cast hvk.symm i))
          = Submission.Heights.cbFamily v hv ∘ (Fin.cast hvk.symm) from rfl, Set.range_comp]
      have hsurj : Function.Surjective (Fin.cast hvk.symm) :=
        fun j => ⟨Fin.cast hvk j, Fin.ext (by simp only [Fin.val_cast])⟩
      rw [Set.range_eq_univ.mpr hsurj, Set.image_univ]
    rw [hrange]
    exact Submission.EscapeGlue.span_range_cbFamily v hv
  have hwedge : ‖exteriorPower.ιMulti ℝ k m‖ = height v hv := by
    have hnorm : ‖exteriorPower.ιMulti ℝ k m‖ =
        ‖exteriorPower.ιMulti ℝ (Module.finrank ℝ v) (Submission.Heights.cbFamily v hv)‖ := by
      rw [← Submission.EscapeGlue.norm_iMulti_cast hvk (Submission.Heights.cbFamily v hv), hmdef]
    rw [hnorm]; rfl
  -- the cone condition
  have hvne : v ≠ ⊥ := by
    intro hbot; rw [hbot] at hvk; simp at hvk; omega
  have hWne : W ≠ ⊥ := by
    intro hbot; rw [hbot] at hW; simp at hW; omega
  have hfr : Module.finrank ℝ v ≤ Module.finrank ℝ W := by rw [hvk, hW]; exact hkl
  have hres : Submission.ProjectionDistance.planeResidual v W ≤ ε / 2 := by
    rw [← Submission.Bridge.distSubspaces_eq_planeResidual_of_le v W hfr hvne hWne]
    exact hdist
  refine ⟨m, hmem, hZ, ?_, ?_⟩
  · intro w hw
    rw [hspan] at hw
    have hcone := cone_of_planeResidual_le (V := v) (W := W) (δ := ε / 2)
      (by positivity) (by linarith [hε1]) hres w hw
    have h2 : 2 * (ε / 2) * ‖(W.starProjection w : ℝᵈ)‖ = ε * ‖(W.starProjection w : ℝᵈ)‖ := by
      ring
    rwa [h2] at hcone
  · rw [hwedge]; exact hheight

end Submission.ConeFromPlane

end
