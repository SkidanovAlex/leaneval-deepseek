import Mathlib
import Submission.Work.Diff.STE.flat.coeffDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

theorem coeffA_deriv_bound {n : ℕ} {T tstar : ℝ} (htstarT : tstar < T)
    (u : ℝ → Work.Diff.STE.Flat.Torus n)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × (Fin n → ℝ) => u p.1 p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ))
    (huper : ∀ t ∈ Set.Ico (0:ℝ) T, Work.Diff.STE.Periodic1 (u t))
    (lam : ℝ) (hlam : 0 < lam)
    (hell : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x : Fin n → ℝ, ∀ ξ : Fin n → ℝ,
      lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j,
        Work.Diff.STE.Flat.reMat (u t x) i j * ξ i * ξ j) :
    ∃ K₁ : ℝ, 0 ≤ K₁ ∧ ∀ t ∈ Set.Ico (0:ℝ) tstar, ∀ (c d i : Fin n) (x : Fin n → ℝ),
      |Work.Diff.STE.pdR i (fun y => Work.Diff.STE.flat.coeffA u t y c d) x| ≤ K₁ := by
  -- The bound is a compactness statement: the derivative is continuous on the compact
  -- `[0,tstar] × [0,1]ⁿ` and all the functions involved are `1`-periodic in `x`.
  have hKcompact : IsCompact ((Set.Icc (0:ℝ) tstar) ×ˢ
      (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1))) :=
    isCompact_Icc.prod (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc))
  have hKsub : (Set.Icc (0:ℝ) tstar) ×ˢ (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1))
      ⊆ Set.Ico (0:ℝ) T ×ˢ Set.univ :=
    fun p hp => ⟨⟨hp.1.1, lt_of_le_of_lt hp.1.2 htstarT⟩, Set.mem_univ _⟩
  -- joint smoothness of the metric matrix, its determinant is nonzero by ellipticity
  have hmat : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => Work.Diff.STE.Flat.reMat (u p.1 p.2) i j) (Set.Ico (0:ℝ) T ×ˢ Set.univ) :=
    fun i j => contDiffOn_reMat_entry hu i j
  have hdet : ∀ t ∈ Set.Ico (0:ℝ) T, ∀ x, (Work.Diff.STE.Flat.reMat (u t x)).det ≠ 0 :=
    fun t ht x => det_ne_zero_of_quadratic hlam (hell t ht x)
  -- joint smoothness of the entries of `coeffA`
  have hA : ∀ c d, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => coeffA u p.1 p.2 c d) (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
    intro c d
    have h1 := contDiffOn_matrixInv_entry (M := fun t x => Work.Diff.STE.Flat.reMat (u t x)) hmat hdet c d
    have h2 := contDiffOn_matrixInv_entry (M := fun t x => Work.Diff.STE.Flat.reMat (u t x)) hmat hdet d c
    have heq : (fun p : ℝ × (Fin n → ℝ) => coeffA u p.1 p.2 c d)
        = fun p : ℝ × (Fin n → ℝ) =>
            (((Work.Diff.STE.Flat.reMat (u p.1 p.2))⁻¹) c d
              + ((Work.Diff.STE.Flat.reMat (u p.1 p.2))⁻¹) d c) / 2 := by
      funext p
      exact coeffA_apply u p.1 p.2 c d
    rw [heq]
    exact (h1.add h2).div_const 2
  -- joint smoothness of the (complexified) partial derivatives of the entries of `coeffA`
  have hpdC : ∀ c d i, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => pd i (fun y => ((coeffA u p.1 y c d : ℂ))) p.2)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
    intro c d i
    refine contDiffOn_pd_slice (F := fun t y => ((coeffA u t y c d : ℂ))) ?_ i
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn (hA c d)
  have hK1cont : ContinuousOn (fun q : ℝ × (Fin n → ℝ) =>
      ∑ c : Fin n, ∑ d : Fin n, ∑ i : Fin n,
        |(pd i (fun y => ((coeffA u q.1 y c d : ℂ))) q.2).re|)
      (Set.Ico (0:ℝ) T ×ˢ Set.univ) := by
    refine continuousOn_finsetSum _ (fun c _ => continuousOn_finsetSum _ (fun d _ =>
      continuousOn_finsetSum _ (fun i _ => ?_)))
    exact continuous_abs.comp_continuousOn
      (Complex.continuous_re.comp_continuousOn (hpdC c d i).continuousOn)
  obtain ⟨K₁₀, hK₁₀⟩ := hKcompact.exists_bound_of_continuousOn (hK1cont.mono hKsub)
  -- differentiability of the `x`-slices
  have hslice : ∀ t ∈ Set.Ico (0:ℝ) tstar, ∀ c d,
      Differentiable ℝ (fun y => coeffA u t y c d) := by
    intro t ht c d
    exact (contDiff_slice_of_contDiffOn_real (F := fun t y => coeffA u t y c d) (hA c d)
      ⟨ht.1, lt_trans ht.2 htstarT⟩).differentiable (by simp)
  refine ⟨max K₁₀ 0, le_max_right _ _, ?_⟩
  intro t ht c d i x
  -- the derivative is `1`-periodic in `x`
  have hper : Periodic1 (fun x => pdR i (fun y => coeffA u t y c d) x) := by
    intro j
    refine cm_periodicIn_pdR j i ?_ ?_
    · exact hslice t ht c d
    · intro z
      have h1 : u t (z + Pi.single j 1) = u t z :=
        huper t ⟨ht.1, lt_trans ht.2 htstarT⟩ j z
      show coeffA u t (z + Pi.single j 1) c d = coeffA u t z c d
      simp only [coeffA, symmInv, h1]
  -- it suffices to bound it on the closed unit cube
  have hcube : ∀ y ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1),
      |pdR i (fun y' => coeffA u t y' c d) y| ≤ K₁₀ := by
    intro y hy
    have hb := hK₁₀ (t, y) ⟨⟨ht.1, ht.2.le⟩, hy⟩
    rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun c' _ => Finset.sum_nonneg (fun d' _ =>
      Finset.sum_nonneg (fun i' _ => abs_nonneg _))))] at hb
    have hpd : |pdR i (fun y' => coeffA u t y' c d) y|
        = |(pd i (fun y' => ((coeffA u t y' c d : ℂ))) y).re| := by
      rw [ga_pd_ofReal i (fun y' => coeffA u t y' c d) y (hslice t ht c d).differentiableAt]
      simp
    rw [hpd]
    exact le_trans (abs_le_sum_three
      (fun c' d' i' => (pd i' (fun y' => ((coeffA u t y' c' d' : ℂ))) y).re) c d i) hb
  exact le_trans (abs_le_of_periodic1_of_cube hper hcube x) (le_max_left _ _)

end Work.Diff.STE.flat
