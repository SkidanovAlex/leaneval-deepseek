import Mathlib
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.EXT.splice_defs
import Submission.Work.Diff.GE.norms_defs
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.EXT.contMDiffAt_matrix_inv
import Submission.Work.Diff.EXT.chartRic_partial_jet
import Submission.Work.Diff.EXT.norm_iteratedFDeriv_pi_le_sum
import Submission.Work.Diff.EXT.norm_iteratedFDeriv_comp_le_of_contDiffAt
import Submission.Work.Diff.EXT.exists_bound_iteratedFDeriv_invEntry_of_isCompact

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.Diff.EXT

theorem gramInv_bounds_of_gram_bounds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (G : ℝ → Submission.Diff.SMet I M) (σ T : ℝ) (x₀ : M) (K : Set E)
    (hKt : K ⊆ (extChartAt I x₀).target) (hU : UniqueDiffOn ℝ K)
    (hG : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.GE.GramM G x₀ t
          (Work.Diff.EXT.pt (I := I) x₀ y') i j) y‖ ≤ C)
    (hbd : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      c ≤ (Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y)).det)
    (hsm : ∀ t ∈ Set.Ico σ T, ∀ (i j : Fin (Module.finrank ℝ E)),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun y' : E => Work.Diff.GE.GramM G x₀ t
        (Work.Diff.EXT.pt (I := I) x₀ y') i j) K) :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico σ T, ∀ y ∈ K,
      ∀ (i j : Fin (Module.finrank ℝ E)),
        ‖iteratedFDeriv ℝ k (fun y' : E => Work.Diff.GE.GramInv G x₀ t
          (Work.Diff.EXT.pt (I := I) x₀ y') i j) y‖ ≤ C := by
  classical
  -- Jet bounds for the Gram matrix entries, extracted from `hG`.
  choose Cf hCf using hG
  have hCf_nn : ∀ i : ℕ, 0 ≤ Cf i := fun i => (hCf i).1
  have hCf_bd : ∀ i : ℕ, ∀ t ∈ Set.Ico σ T, ∀ y ∈ K, ∀ (a b : Fin (Module.finrank ℝ E)),
      ‖iteratedFDeriv ℝ i (fun y' : E => Work.Diff.GE.GramM G x₀ t
        (Work.Diff.EXT.pt (I := I) x₀ y') a b) y‖ ≤ Cf i := fun i => (hCf i).2
  -- The lower bound for the determinant.
  obtain ⟨c, hcpos, hcdet⟩ := hbd
  intro k
  -- A common bound for the derivatives of all orders `≤ k`.
  set D0 : ℝ := ∑ i ∈ Finset.range (k + 1), Cf i with hD0
  have hD0nn : 0 ≤ D0 := by rw [hD0]; exact Finset.sum_nonneg (fun i _ => hCf_nn i)
  have hCf_le_D0 : ∀ i, i ≤ k → Cf i ≤ D0 := by
    intro i hi
    rw [hD0]
    exact Finset.single_le_sum (fun j _ => hCf_nn j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  /- `B` bounds the matrix norm of the Gram matrix; `D` is a common geometric bound for the jets
  of the Gram matrix. -/
  set B : ℝ := ∑ _ : Fin (Module.finrank ℝ E), ∑ _ : Fin (Module.finrank ℝ E), D0 with hB
  set D : ℝ := max 1 B with hD
  have hD1 : 1 ≤ D := le_max_left _ _
  have hDB : B ≤ D := le_max_right _ _
  have hDkey : ∀ s, 1 ≤ s → s ≤ k → B ≤ D ^ s := by
    intro s hs1 _
    calc B ≤ D := hDB
      _ = D ^ 1 := (pow_one D).symm
      _ ≤ D ^ s := pow_le_pow_right₀ hD1 hs1
  -- The compact set of invertible matrices through which the Gram matrix ranges.
  set Tset : Set (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :=
      {A | c ≤ (Matrix.of A).det ∧ ‖A‖ ≤ B} with hTset
  have hTset_compact : IsCompact Tset := by
    rw [hTset]
    have hclosed : IsClosed {A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ |
        c ≤ (Matrix.of A).det} :=
      isClosed_le continuous_const (Work.Diff.EXT.contDiff_matrix_det_pi.continuous)
    have hball : IsCompact (Metric.closedBall
        (0 : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) B) :=
      isCompact_closedBall 0 B
    convert hball.inter_left hclosed using 1
    ext A
    simp [Metric.mem_closedBall, dist_eq_norm]
  have hTset_sub : Tset ⊆ {A | (Matrix.of A).det ≠ 0} := by
    intro A hA
    exact ne_of_gt (lt_of_lt_of_le hcpos hA.1)
  -- Uniform jet bounds for the entries of the inverse matrix on `Tset`.
  obtain ⟨M, hMnn, hMbd⟩ :=
    Work.Diff.EXT.exists_bound_iteratedFDeriv_invEntry_of_isCompact
      (Module.finrank ℝ E) hTset_compact hTset_sub k
  refine ⟨max 0 ((Nat.factorial k : ℝ) * M * D ^ k), le_max_left _ _, ?_⟩
  intro t ht y hy i j
  -- Smoothness of the chart matrix at `y` (the chart matrix is genuinely smooth on the target).
  have hFm_smooth : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y' : E => fun a b : Fin (Module.finrank ℝ E) =>
        Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') a b) y :=
    (Work.Diff.EXT.contDiffAt_chartMatFun (I := I) (G t) x₀ (hKt hy)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun y' => by funext a b; rfl))
  -- Jet bounds for the matrix-valued Gram family, from the entrywise bounds.
  have hFm_bound : ∀ s, s ≤ k → ‖iteratedFDeriv ℝ s
      (fun y' : E => fun a b : Fin (Module.finrank ℝ E) =>
        Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') a b) y‖ ≤ B := by
    intro s hsk
    have hpi1 : ‖iteratedFDeriv ℝ s (fun y' : E => fun a b : Fin (Module.finrank ℝ E) =>
          Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') a b) y‖
        ≤ ∑ a, ‖iteratedFDeriv ℝ s (fun y' : E => fun b : Fin (Module.finrank ℝ E) =>
            Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') a b) y‖ :=
      Work.Diff.EXT.norm_iteratedFDeriv_pi_le_sum _ y s hFm_smooth
    refine hpi1.trans ?_
    refine Finset.sum_le_sum (fun a _ => ?_)
    have hpi2 : ‖iteratedFDeriv ℝ s (fun y' : E => fun b : Fin (Module.finrank ℝ E) =>
          Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') a b) y‖
        ≤ ∑ b, ‖iteratedFDeriv ℝ s (fun y' : E =>
            Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') a b) y‖ :=
      Work.Diff.EXT.norm_iteratedFDeriv_pi_le_sum _ y s ((contDiffAt_pi.mp hFm_smooth) a)
    refine hpi2.trans ?_
    refine Finset.sum_le_sum (fun b _ => ?_)
    refine (hCf_bd s t ht y hy a b).trans ?_
    exact hCf_le_D0 s hsk
  have hFm_mem : (fun a b : Fin (Module.finrank ℝ E) =>
      Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) a b) ∈ Tset := by
    refine ⟨hcdet t ht y hy, ?_⟩
    have h0 := hFm_bound 0 (Nat.zero_le k)
    rwa [norm_iteratedFDeriv_zero] at h0
  have hFm_jet : ∀ s, 1 ≤ s → s ≤ k → ‖iteratedFDeriv ℝ s
      (fun y' : E => fun a b : Fin (Module.finrank ℝ E) =>
        Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') a b) y‖ ≤ D ^ s :=
    fun s hs1 hsk => (hFm_bound s hsk).trans (hDkey s hs1 hsk)
  have hdet0 : (Matrix.of (fun a b : Fin (Module.finrank ℝ E) =>
      Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) a b)).det ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le hcpos (hcdet t ht y hy))
  have hg_smooth : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun A' : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ =>
        (Matrix.of A')⁻¹ i j)
      (fun a b : Fin (Module.finrank ℝ E) =>
        Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y) a b) :=
    (contDiffAt_pi.mp (contDiffAt_pi.mp (Work.Diff.EXT.contDiffAt_matrix_inv_pi _ hdet0) i)) j
  -- The quantitative chain rule.
  have hcomp := Work.Diff.EXT.norm_iteratedFDeriv_comp_le_of_contDiffAt
    (f := fun y' : E => fun a b : Fin (Module.finrank ℝ E) =>
      Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') a b)
    (g := fun A' : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ => (Matrix.of A')⁻¹ i j)
    hFm_smooth hg_smooth (fun s hs => hMbd _ hFm_mem i j s hs) hFm_jet
  -- `GramInv` is the inverse of the Gram matrix, entrywise.
  have hrw : (fun y' : E => Work.Diff.GE.GramInv G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') i j)
      = (fun A' : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ => (Matrix.of A')⁻¹ i j)
        ∘ (fun y' : E => fun a b : Fin (Module.finrank ℝ E) =>
            Work.Diff.GE.GramM G x₀ t (Work.Diff.EXT.pt (I := I) x₀ y') a b) := by
    funext y'
    rfl
  rw [hrw]
  exact hcomp.trans (le_max_right _ _)

end Work.Diff.EXT
