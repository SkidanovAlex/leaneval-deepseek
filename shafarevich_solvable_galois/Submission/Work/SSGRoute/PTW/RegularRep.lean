import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The regular representation of a compact group on `L²`, and the averaging operator

Auxiliary file for `Work.SSGRoute.PTW.mem_all_open_index_p_iff_mem_closure_pthPowers`.

## STATE AND NEXT STEPS (2026, mid-development)

Goal of the whole subproject: prove, for a compact Hausdorff abelian group `Q` of exponent `p`,
`Work.SSGRoute.PTW.exists_open_index_p_notMem_of_compact_abelian_exponent_p`:
for `y ≠ 1` there is an open index-`p` subgroup avoiding `y`; then feed it into the target theorem
`Work.SSGRoute.PTW.mem_all_open_index_p_iff_mem_closure_pthPowers` (replacing the missing
`compact_abelian_exponent_p_totallyDisconnected`).

PLAN (mathematical argument, believed complete):
1. `H := Lp ℂ 2 μ`, `μ` = Haar probability on `Q`; `regRep : Q → H →L[ℂ] H` = regular rep.
2. `regRep y ≠ 1` for `y ≠ 1` (use an open `W ∋ 1` with `yW ∩ W = ∅` and `indicatorConstLp`).
3. Pick `ξ ≠ 0` with `regRep y ξ ≠ ξ`.
4. `A : H →L[ℂ] H`, `A := ∫ g, (rank-one operator η ↦ ⟪regRep g ξ, η⟫ • regRep g ξ) dμ(g)`.
   Facts needed: `A` is self-adjoint (`IsSymmetric`), `A` intertwines `regRep`
   (`A ∘ regRep h = regRep h ∘ A`, by change of variables `g ↦ h⁻¹g` + left invariance of `μ`),
   `A ≠ 0` (`⟨Aξ,ξ⟩ = ∫ ‖⟪regRep g ξ, ξ⟫‖² > 0`), and `A` is compact (`A` lies in the closed
   convex hull of the compact set of rank-one operators `{rank-one (regRep g ξ)}`, e.g. via
   `Convex.integral_mem` + `rankOneIsCompact` + closedness of the set of compact operators, or via
   approximations of the integral by simple functions).
5. Spectral theorem (Mathlib `Analysis/InnerProductSpace/Spectrum.lean`):
   `ContinuousLinearMap.eq_zero_of_forall_hasEigenvalue_eq_zero` gives `∃ μ ≠ 0` with
   `eigenspace A μ ≠ ⊥`, and `ContinuousLinearMap.finite_dimensional_eigenspace` gives
   `FiniteDimensional ℂ (eigenspace A μ)`; the eigenspaces are `regRep`-invariant (since `A`
   intertwines).
6. Interlude lemma to prove (`compact_selfAdjoint_range_le_iSup_eigenspace`):
   `A.range ≤ (⨆ μ ≠ 0, eigenspace A μ).topologicalClosure`.
   With `ξ ∈ closure (range A)` (from `A ≠ 0` and the eigenvalue at `λ ≠ 0`) one gets a finite
   dimensional invariant subspace `E` on which `regRep y ≠ 1`.
7. Interlude lemma to prove (`finiteDim_rep_exists_weight`): a nontrivial finite-dimensional unitary
   representation of an abelian group has a weight `χ : Q →* ℂˣ` with `χ y ≠ 1` and eigenvector `v`
   (minimal-dimensional invariant subspaces + Schur). `χ` is automatically continuous in finite
   dimension (via `⟪regRep · v, v⟫`).
8. `χ(Q) ⊆ μ_p` (exponent `p`), `χ` nontrivial ⟹ `[Q : ker χ] = p`; `ker χ` is closed hence open
   (`Subgroup.isOpen_of_isClosed_of_finiteIndex`) and avoids `y`.

Blocking technical issue (small but real): rewriting with the `DomMulAct` action and `smul_smul`
reports "typeclass instance problem is stuck: `Measure.IsMulLeftInvariant ?m`"; see the note above
`regRep_mul`.  The scalar identity `mk_mul`/`mk_inv_mul` is fine.

## Contents / roadmap

* `regRep` : the left regular representation of a compact group `Q` (with left-invariant
  probability measure `μ` on a compact Hausdorff group) on `Lp ℂ 2 μ`, as a continuous linear map.
  Facts: `regRep_mul_apply`, `regRep_one`, `norm_regRep_apply`, `regRep_injective/surjective`,
  `continuous_regRep_apply` (strong continuity, from `Lp.instContinuousSMulDomMulAct`).
* `rankOneIsCompact` : `η ↦ ⟪a,η⟫ • b` is a compact operator.
* NEXT: the averaging operator `A := ∫ g, rankOne (regRep g ξ)` and its properties
  (self-adjoint, intertwines `regRep`, nonzero, compact), then the spectral step, then the
  finite-dimensional representation weight lemma
  (`Work.SSGRoute.PTW.finiteDim_rep_exists_weight`, delegated), then the separation lemma
  `exists_open_index_p_notMem_of_compact_abelian_exponent_p` and finally the target theorem.
-/

namespace Work.SSGRoute.PTW

open MeasureTheory Filter Metric
open scoped Topology InnerProductSpace ENNReal

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]
  [T2Space Q] [MeasurableSpace Q] [BorelSpace Q] {μ : Measure Q}
  [Measure.IsMulLeftInvariant μ] [IsProbabilityMeasure μ] [IsLocallyFiniteMeasure μ]
  [μ.InnerRegularCompactLTTop]

/-- The left regular representation of `Q` on `L²(Q, μ)`, as a continuous linear map. -/
noncomputable def regRep (g : Q) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun ξ => (DomMulAct.mk g⁻¹) • ξ
      map_add' := fun ξ η => DomMulAct.smul_Lp_add _ _ _
      map_smul' := fun r ξ => smul_comm (DomMulAct.mk g⁻¹) r ξ }
    1 (fun ξ => by
      change ‖(DomMulAct.mk g⁻¹) • ξ‖ ≤ 1 * ‖ξ‖
      rw [DomMulAct.norm_smul_Lp, one_mul])

@[simp]
theorem regRep_apply (g : Q) (ξ : Lp ℂ 2 μ) :
    regRep g ξ = (DomMulAct.mk g⁻¹) • ξ := rfl

/-- The scalar identity `mk a * mk b = mk (b * a)` (definitional). -/
theorem mk_mul (a b : Q) : DomMulAct.mk a * DomMulAct.mk b = DomMulAct.mk (b * a) := rfl

/-- The scalar identity `mk ((g*h)⁻¹) = mk g⁻¹ * mk h⁻¹`. -/
theorem mk_inv_mul (g h : Q) :
    DomMulAct.mk ((g * h)⁻¹) = DomMulAct.mk g⁻¹ * DomMulAct.mk h⁻¹ := by
  rw [mul_inv_rev]
  exact (mk_mul g⁻¹ h⁻¹).symm

/-- The scalar identity `mk g⁻¹ • (mk h⁻¹ • ξ) = mk ((g*h)⁻¹) • ξ` for the `Lᵈᵐᵃ`-action on `L²`.
The type ascriptions are essential for instance resolution. -/
theorem smul_inv_mul (g h : Q) (ξ : Lp ℂ 2 μ) :
    (((DomMulAct.mk g⁻¹) • ((DomMulAct.mk h⁻¹) • ξ)) : Lp ℂ 2 μ) =
      (DomMulAct.mk (g * h)⁻¹) • ξ := by
  rw [smul_smul, mk_mul, mul_inv_rev]

theorem regRep_mul_apply (g h : Q) (ξ : Lp ℂ 2 μ) :
    regRep (g * h) ξ = regRep g (regRep h ξ) := by
  change ((DomMulAct.mk (g * h)⁻¹) • ξ : Lp ℂ 2 μ) =
    ((DomMulAct.mk g⁻¹) • ((DomMulAct.mk h⁻¹) • ξ) : Lp ℂ 2 μ)
  rw [smul_inv_mul]

theorem regRep_mul (g h : Q) :
    (regRep (μ := μ) (g * h)) = (regRep (μ := μ) g).comp (regRep (μ := μ) h) :=
  ContinuousLinearMap.ext fun ξ => regRep_mul_apply g h ξ

theorem regRep_one : regRep (1 : Q) = ContinuousLinearMap.id ℂ (Lp ℂ 2 μ) := by
  ext ξ
  simp [regRep_apply]

theorem norm_regRep_apply (g : Q) (ξ : Lp ℂ 2 μ) : ‖regRep g ξ‖ = ‖ξ‖ := by
  rw [regRep_apply, DomMulAct.norm_smul_Lp]

/-- Strong continuity of the regular representation at an arbitrary point.  Uses Mathlib's
`ContinuousSMul Qᵈᵐᵃ (Lp ℂ 2 μ)` instance (`MeasureTheory.Lp.instContinuousSMulDomMulAct`), which
needs `Fact ((2 : ℝ≥0∞) ≠ ∞)` — not found by typeclass search, hence the local instance. -/
theorem continuous_regRep_apply (ξ : Lp ℂ 2 μ) :
    Continuous fun g : Q => regRep (μ := μ) g ξ := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hfun : (fun g : Q => regRep (μ := μ) g ξ)
      = fun g : Q => ((DomMulAct.mk g⁻¹) • ξ : Lp ℂ 2 μ) := by
    funext g
    exact regRep_apply (μ := μ) g ξ
  rw [hfun]
  exact continuous_smul.comp
    ((DomMulAct.continuous_mk.comp continuous_inv).prodMk continuous_const)

theorem regRep_injective (g : Q) : Function.Injective (regRep (μ := μ) g) := by
  intro ξ η h
  have h1 : regRep (μ := μ) g⁻¹ (regRep (μ := μ) g ξ)
      = regRep (μ := μ) g⁻¹ (regRep (μ := μ) g η) := by rw [h]
  rw [← regRep_mul_apply, inv_mul_cancel, regRep_one] at h1
  simpa using h1

theorem regRep_surjective (g : Q) : Function.Surjective (regRep (μ := μ) g) :=
  fun η => ⟨regRep (μ := μ) g⁻¹ η, by
    rw [← regRep_mul_apply, mul_inv_cancel, regRep_one]
    rfl⟩

/-- The rank-one operator `η ↦ ⟪a, η⟫ • b` on `L²`. -/
noncomputable def rankOneOp (a b : Lp ℂ 2 μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun η => inner ℂ a η • b
      map_add' := by
        intro η η'
        rw [inner_add_right, add_smul]
      map_smul' := by
        intro r η
        rw [inner_smul_right, mul_smul, RingHom.id_apply] }
    (‖a‖ * ‖b‖) (fun η => by
      change ‖inner ℂ a η • b‖ ≤ ‖a‖ * ‖b‖ * ‖η‖
      rw [norm_smul]
      calc ‖inner ℂ a η‖ * ‖b‖ ≤ (‖a‖ * ‖η‖) * ‖b‖ :=
            mul_le_mul_of_nonneg_right (norm_inner_le_norm a η) (norm_nonneg b)
        _ = (‖a‖ * ‖b‖) * ‖η‖ := by ring)

@[simp]
theorem rankOneOp_apply (a b η : Lp ℂ 2 μ) : rankOneOp (μ := μ) a b η = inner ℂ a η • b := rfl

/-- The averaging operator `A = ∫ g, |regRep g ξ⟩⟨regRep g ξ| dμ(g)`, a compact self-adjoint
operator on `L²` commuting with the regular representation. -/
noncomputable def avgOp (ξ : Lp ℂ 2 μ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  ∫ g, rankOneOp (μ := μ) (regRep (μ := μ) g ξ) (regRep (μ := μ) g ξ) ∂μ

/-- The rank-one operator `η ↦ ⟪a, η⟫ • b` is a compact operator. -/
theorem rankOneIsCompact {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (a b : H) : IsCompactOperator (fun η : H => inner ℂ a η • b) := by
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  refine ⟨closedBall 0 1, closedBall_mem_nhds 0 one_pos,
    (fun c : ℂ => c • b) '' closedBall 0 ‖a‖, ?_, ?_⟩
  · exact (isCompact_closedBall (0 : ℂ) ‖a‖).image (continuous_id.smul continuous_const)
  · rintro y ⟨η, hη, rfl⟩
    refine ⟨inner ℂ a η, ?_, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    have hη' : ‖η‖ ≤ 1 := by simpa [dist_eq_norm] using hη
    exact (norm_inner_le_norm a η).trans (mul_le_of_le_one_right (norm_nonneg a) hη')

end Work.SSGRoute.PTW
