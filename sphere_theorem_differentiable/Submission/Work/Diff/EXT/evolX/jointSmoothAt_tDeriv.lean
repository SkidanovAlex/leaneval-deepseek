import Mathlib
import Submission.Work.Diff.EXT.contMDiffAt_mvfderiv_along_field

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Joint smoothness of the time derivative of a jointly smooth family

If `Φ : ℝ × M → ℝ` is jointly `C^∞` at `(t₀, x)` then so is `p ↦ ∂_t Φ (p.1, p.2)`, i.e. the
function `(t, y) ↦ deriv (fun s => Φ (s, y)) t`.

The proof is a chart reduction, exactly as in
`Work.Diff.EXT.contMDiffAt_mvfderiv_along_field` (the *spatial* derivative of a jointly smooth
family, along a smooth field): both hypotheses and conclusion are local, and in the chart at `x`
the statement becomes the pure model-space fact `derivSlice_jointSmooth` below, namely that the
`t`-derivative of a function which is `C^{k+1}` on `univ ×ˢ σ` is `C^k` on `univ ×ˢ σ`
(the chain rule with the affine map `s ↦ (s, ξ)` plus Mathlib's
`ContDiffWithinAt.fderivWithin_right_apply`).
-/

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set Filter

namespace Work.Diff.EXT.evolX

noncomputable section

/-- **Pointwise model-space identity.**  If `u : ℝ × E → F` is differentiable within `S` at `p`
and the affine slice `s ↦ (s, p.2)` maps `univ` into `S`, then the (global) derivative of the
slice `s ↦ u (s, p.2)` at `p.1` is `fderivWithin ℝ u S p` applied to `(1, 0)`. -/
lemma deriv_slice_eq_fderivWithin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℝ × E → F} {S : Set (ℝ × E)} {p : ℝ × E}
    (hS : ∀ s : ℝ, (s, p.2) ∈ S)
    (hd : DifferentiableWithinAt ℝ u S p) :
    deriv (fun s : ℝ => u (s, p.2)) p.1 = fderivWithin ℝ u S p (1, 0) := by
  have h1 : HasFDerivWithinAt u (fderivWithin ℝ u S p) S p := hd.hasFDerivWithinAt
  have h2at : HasFDerivAt (fun s : ℝ => ((s, (0 : E)) + ((0 : ℝ), p.2)))
      (ContinuousLinearMap.inl ℝ ℝ E) p.1 :=
    ((ContinuousLinearMap.inl ℝ ℝ E).hasFDerivAt).add_const ((0 : ℝ), p.2)
  have heq : (fun s : ℝ => (s, p.2)) = fun s : ℝ => ((s, (0 : E)) + ((0 : ℝ), p.2)) := by
    funext s; simp
  have h2at' : HasFDerivAt (fun s : ℝ => (s, p.2)) (ContinuousLinearMap.inl ℝ ℝ E) p.1 := by
    rw [heq]; exact h2at
  have h2 : HasFDerivWithinAt (fun s : ℝ => (s, p.2)) (ContinuousLinearMap.inl ℝ ℝ E)
      Set.univ p.1 :=
    h2at'.hasFDerivWithinAt
  have hcomp := h1.comp p.1 h2 (fun s _ => hS s)
  have hfd : fderivWithin ℝ (fun s : ℝ => u (s, p.2)) Set.univ p.1
      = (fderivWithin ℝ u S p).comp (ContinuousLinearMap.inl ℝ ℝ E) :=
    hcomp.fderivWithin uniqueDiffWithinAt_univ
  rw [← fderiv_apply_one_eq_deriv, ← fderivWithin_univ, hfd, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply]

/-- **The time-derivative of a jointly `C^{k+1}` family is jointly `C^k`** (model space). -/
lemma derivSlice_contDiffWithinAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : ℝ × E → F} {σ : Set E} {t₀ : ℝ} {ξ₀ : E} (k : ℕ)
    (hu : ContDiffWithinAt ℝ (((k + 1 : ℕ)) : WithTop ℕ∞) u (Set.univ ×ˢ σ) (t₀, ξ₀))
    (hσ : UniqueDiffOn ℝ σ) (hξ₀ : ξ₀ ∈ σ) :
    ContDiffWithinAt ℝ ((k : ℕ) : WithTop ℕ∞)
      (fun p : ℝ × E => deriv (fun s : ℝ => u (s, p.2)) p.1) (Set.univ ×ˢ σ) (t₀, ξ₀) := by
  have hSuniq : UniqueDiffOn ℝ (Set.univ ×ˢ σ) :=
    UniqueDiffOn.prod (s := (Set.univ : Set ℝ)) (t := σ) uniqueDiffOn_univ hσ
  have hmem : (t₀, ξ₀) ∈ (Set.univ ×ˢ σ) := by simp [hξ₀]
  have hbase : ContDiffWithinAt ℝ ((k : ℕ) : WithTop ℕ∞)
      (fun p : ℝ × E => fderivWithin ℝ u (Set.univ ×ˢ σ) p (1, 0)) (Set.univ ×ˢ σ)
      (t₀, ξ₀) := by
    refine ContDiffWithinAt.fderivWithin_right_apply (f := u)
      (k := fun _ : ℝ × E => (((1 : ℝ), (0 : E)))) hu (contDiffWithinAt_const) hSuniq ?_ hmem
    simp
  refine hbase.congr_of_eventuallyEq ?_ ?_
  · have hcont : ∀ᶠ p : ℝ × E in 𝓝[Set.univ ×ˢ σ] (t₀, ξ₀),
        ContDiffWithinAt ℝ (((k + 1 : ℕ)) : WithTop ℕ∞) u (Set.univ ×ˢ σ) p := by
      have h1 := hu.eventually (hn := by simp)
      rwa [Set.insert_eq_of_mem hmem] at h1
    filter_upwards [hcont, self_mem_nhdsWithin] with p hdiff hpS
    have hpσ : p.2 ∈ σ := hpS.2
    exact deriv_slice_eq_fderivWithin (fun s => by simp [hpσ])
      (hdiff.differentiableWithinAt (by simp))
  · exact deriv_slice_eq_fderivWithin (fun s => by simp [hξ₀])
      (hu.differentiableWithinAt (by simp))

/-- **Joint smoothness of the time derivative.**  If `Φ : ℝ × M → ℝ` is jointly `C^∞` at
`(t₀, x)` then `p ↦ deriv (fun s => Φ (s, p.2)) p.1` is jointly `C^∞` at `(t₀, x)`. -/
theorem jointSmoothAt_tDeriv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    {Φ : ℝ × M → ℝ} {t₀ : ℝ} {x : M}
    (hΦ : ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ)
      (⊤ : ℕ∞) Φ (t₀, x)) :
    ContMDiffAt ((modelWithCornersSelf ℝ ℝ).prod I) (modelWithCornersSelf ℝ ℝ) (⊤ : ℕ∞)
      (fun p : ℝ × M => deriv (fun s : ℝ => Φ (s, p.2)) p.1) (t₀, x) := by
  have hΦ' : JointSmoothAt I M Φ t₀ x := hΦ
  rw [contMDiffAt_infty]
  intro n
  have hfam : ContDiffWithinAt ℝ ((n : ℕ) : WithTop ℕ∞)
      (fun p : ℝ × E => deriv (fun s : ℝ => Φ (s, (extChartAt I x).symm p.2)) p.1)
      (Set.univ ×ˢ (extChartAt I x).target) (t₀, (extChartAt I x) x) :=
    derivSlice_contDiffWithinAt n
      (contDiffWithinAt_chart_family (I := I) (M := M) (F := ℝ) (n + 1) hΦ')
      (uniqueDiffOn_extChartAt_target (I := I) x)
      (mem_extChartAt_target x)
  have hcmd := hfam.contMDiffWithinAt
  have hTev : (Set.univ ×ˢ (extChartAt I x).target)
      =ᶠ[𝓝 (t₀, (extChartAt I x) x)] (Set.univ ×ˢ Set.range I) := by
    obtain ⟨u, hu, huT⟩ := (mem_nhdsWithin_iff_exists_mem_nhds_inter).1
      (extChartAt_target_mem_nhdsWithin (I := I) x)
    filter_upwards [prod_mem_nhds univ_mem hu] with p hp
    exact propext ⟨fun h => ⟨h.1, extChartAt_target_subset_range x h.2⟩,
      fun h => ⟨h.1, huT ⟨hp.2, h.2⟩⟩⟩
  have hbig := (contMDiffWithinAt_congr_set hTev).1 hcmd
  refine (contMDiffAt_iff_source (I := (𝓘(ℝ, ℝ)).prod I) (I' := 𝓘(ℝ, ℝ))
    (x := (t₀, x))).2 ?_
  rw [show ((fun p : ℝ × M => deriv (fun s : ℝ => Φ (s, p.2)) p.1)
        ∘ (extChartAt ((𝓘(ℝ, ℝ)).prod I) (t₀, x)).symm)
      = (fun p : ℝ × E => deriv (fun s : ℝ => Φ (s, (extChartAt I x).symm p.2)) p.1) from by
        rw [extChartAt_prod_symm t₀ x]; rfl,
    extChartAt_prod_apply t₀ x, range_prod_modelWithCorners]
  exact hbig

end

end Work.Diff.EXT.evolX
