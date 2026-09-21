import Mathlib

namespace Work.Analysis.Calculus

/-- For a function `φ : ℝ × ℝ → ℝ` which is `C^∞` on an open set `U`, the `k`-th derivative of
the section `v ↦ φ (q.1, v)` at `q.2` is the `k`-th iterated Fréchet derivative of `φ` at `q`
evaluated on the constant family `(0,1)`.

The proof composes `φ` with the affine embedding `v ↦ (q.1, v) = (q.1,0) + inr v`, using the
translation invariance of iterated Fréchet derivatives and the composition formula with a
continuous linear map on the right. -/
lemma iteratedDeriv_section_eq_iteratedFDeriv {φ : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hφ : ContDiffOn ℝ ⊤ φ U) (k : ℕ) {q : ℝ × ℝ} (hq : q ∈ U) :
    iteratedDeriv k (fun v : ℝ => φ (q.1, v)) q.2 =
      (iteratedFDeriv ℝ k φ q) (fun _ => (0, 1)) := by
  set s : Set (ℝ × ℝ) := (fun z : ℝ × ℝ => z + (q.1, 0)) ⁻¹' U with hs_def
  have hs_open : IsOpen s := hU.preimage (by continuity)
  have hψ : ContDiffOn ℝ ⊤ (fun z : ℝ × ℝ => φ (z + (q.1, 0))) s :=
    hφ.comp ((contDiff_id.add contDiff_const).contDiffOn.mono (Set.subset_univ s))
      (fun z hz => hz)
  have hq_in : (ContinuousLinearMap.inr ℝ ℝ ℝ q.2) ∈ s := by
    rw [hs_def, Set.mem_preimage]
    have : (ContinuousLinearMap.inr ℝ ℝ ℝ q.2) + (q.1, 0) = q := by
      ext <;> simp [ContinuousLinearMap.inr]
    rw [this]; exact hq
  have hσ : (fun v : ℝ => φ (q.1, v)) =
      (fun z : ℝ × ℝ => φ (z + (q.1, 0))) ∘ (ContinuousLinearMap.inr ℝ ℝ ℝ) := by
    funext v
    simp [ContinuousLinearMap.inr]
  have hinr_open : IsOpen ((ContinuousLinearMap.inr ℝ ℝ ℝ) ⁻¹' s) :=
    hs_open.preimage (by continuity)
  have hq2_in : q.2 ∈ (ContinuousLinearMap.inr ℝ ℝ ℝ) ⁻¹' s := hq_in
  rw [iteratedDeriv_eq_iteratedFDeriv]
  rw [hσ]
  rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
        (f := (fun z : ℝ × ℝ => φ (z + (q.1, 0))) ∘ (ContinuousLinearMap.inr ℝ ℝ ℝ))
        k hinr_open hq2_in]
  rw [ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ)
        (g := ContinuousLinearMap.inr ℝ ℝ ℝ) (f := fun z : ℝ × ℝ => φ (z + (q.1, 0)))
        (s := s) hψ hs_open.uniqueDiffOn hinr_open.uniqueDiffOn hq_in (i := k) le_top]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
        (f := fun z : ℝ × ℝ => φ (z + (q.1, 0))) k hs_open hq_in]
  rw [iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := φ) k (q.1, 0)
        (ContinuousLinearMap.inr ℝ ℝ ℝ q.2)]
  simp [ContinuousLinearMap.inr]

/-- **Parametric bound for iterated derivatives.**

If `F` is jointly `C^∞` on an open set `U ⊆ ℝ × ℝ`, then on any compact `K ⊆ U` the `k`-th
derivative in the second variable of the section `u ↦ F x u` is uniformly bounded. -/
theorem parametric_iteratedDeriv_bound {F : ℝ → ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ⊤ (fun q : ℝ × ℝ => F q.1 q.2) U)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) (k : ℕ) :
    ∃ C : ℝ, ∀ q ∈ K, |iteratedDeriv k (fun u : ℝ => F q.1 u) q.2| ≤ C := by
  have hcont : ContinuousOn (iteratedFDeriv ℝ k (fun q : ℝ × ℝ => F q.1 q.2)) U :=
    ContinuousOn.continuousOn_iteratedFDeriv (f := fun q : ℝ × ℝ => F q.1 q.2) hF hU le_top
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hcont.mono hKU)
  refine ⟨C, fun q hq => ?_⟩
  have hqU : q ∈ U := hKU hq
  have hid := iteratedDeriv_section_eq_iteratedFDeriv hU hF k hqU
  rw [hid, ← Real.norm_eq_abs]
  calc ‖(iteratedFDeriv ℝ k (fun q : ℝ × ℝ => F q.1 q.2) q) (fun _ => (0, 1))‖
      ≤ ‖iteratedFDeriv ℝ k (fun q : ℝ × ℝ => F q.1 q.2) q‖ *
          ∏ _i : Fin k, ‖((0:ℝ), 1)‖ :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ k (fun q : ℝ × ℝ => F q.1 q.2) q‖ := by simp
    _ ≤ C := hC q hq

end Work.Analysis.Calculus
