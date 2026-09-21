import Mathlib
import Submission.Work.OddVolterra.Smooth.Slice

/-!
# Smoothness of parametric interval integrals

If `F : ℝ × ℝ → ℝ` is `C^∞` on an open set `V` and the vertical segment
`{s₀} × [c, d]` is contained in `V`, then the parametric integral
`s ↦ ∫ t in c..d, F (s, t)` is `C^∞` at `s₀`.

The proof differentiates under the integral sign with
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`, using the uniform
bounds provided by compactness of the rectangle, and then bootstraps to all orders of
smoothness with `contDiffOn_succ_iff_deriv_of_isOpen`.
-/

namespace Work.OddVolterra.Smooth.Alt

open Set Filter MeasureTheory
open scoped Topology Interval

noncomputable section

/-- The tube around a vertical segment inside an open set. -/
lemma exists_tube {V : Set (ℝ × ℝ)} (hV : IsOpen V) {c d s₀ : ℝ}
    (hseg : ∀ t ∈ Set.uIcc c d, (s₀, t) ∈ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, |s - s₀| < δ → ∀ t ∈ Set.uIcc c d, (s, t) ∈ V := by
  have hK : IsCompact ({s₀} ×ˢ Set.uIcc c d : Set (ℝ × ℝ)) :=
    isCompact_singleton.prod isCompact_uIcc
  have hKW : ({s₀} ×ˢ Set.uIcc c d : Set (ℝ × ℝ)) ⊆ V := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    simp only [Set.mem_singleton_iff] at hs
    rw [hs]
    exact hseg t ht
  obtain ⟨δ, hδpos, hδ⟩ := hK.exists_cthickening_subset_open hV hKW
  refine ⟨δ, hδpos, fun s hs t ht => hδ (Metric.thickening_subset_cthickening δ _ ?_)⟩
  rw [Metric.mem_thickening_iff]
  refine ⟨(s₀, t), ⟨by simp, ht⟩, ?_⟩
  have hdist : dist (s, t) (s₀, t) = |s - s₀| := by
    rw [Prod.dist_eq]
    dsimp only
    rw [dist_self, max_eq_left dist_nonneg, Real.dist_eq]
  rw [hdist]
  exact hs

theorem contDiffAt_integral_of_contDiffOn {F : ℝ × ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F V) {c d s₀ : ℝ}
    (hseg : ∀ t ∈ Set.uIcc c d, (s₀, t) ∈ V) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun s => ∫ t in c..d, F (s, t)) s₀ := by
  obtain ⟨δ, hδpos, htube⟩ := exists_tube hV hseg
  have hδ2pos : 0 < δ / 2 := by linarith
  set B : Set ℝ := Ioo (s₀ - δ / 2) (s₀ + δ / 2) with hBdef
  have hBopen : IsOpen B := by rw [hBdef]; exact isOpen_Ioo
  have hs₀B : s₀ ∈ B := by
    rw [hBdef]
    exact ⟨by linarith, by linarith⟩
  have hBmem : ∀ s ∈ B, |s - s₀| < δ := by
    intro s hs
    rw [hBdef] at hs
    rw [abs_lt]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hmemV : ∀ s ∈ B, ∀ t ∈ Set.uIcc c d, (s, t) ∈ V :=
    fun s hs t ht => htube s (hBmem s hs) t ht
  have hRsub : (Set.Icc (s₀ - δ / 2) (s₀ + δ / 2) ×ˢ Set.uIcc c d : Set (ℝ × ℝ)) ⊆ V := by
    rintro ⟨s, t⟩ ⟨hs, ht⟩
    refine htube s ?_ t ht
    rw [abs_lt]
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hRcompact : IsCompact (Set.Icc (s₀ - δ / 2) (s₀ + δ / 2) ×ˢ Set.uIcc c d :
      Set (ℝ × ℝ)) := isCompact_Icc.prod isCompact_uIcc
  have hcontIter : ∀ k : ℕ, ContinuousOn ((pderiv1 V)^[k] F) V :=
    fun k => (contDiffOn_pderiv1Iter hV hF k).continuousOn
  -- differentiating under the integral sign
  have key : ∀ k : ℕ, ∀ s ∈ B,
      HasDerivAt (fun u => ∫ t in c..d, ((pderiv1 V)^[k] F) (u, t))
        (∫ t in c..d, ((pderiv1 V)^[k + 1] F) (s, t)) s := by
    intro k s hs
    obtain ⟨M, hM⟩ := hRcompact.exists_bound_of_continuousOn
      ((hcontIter (k + 1)).mono hRsub)
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := c) (b := d) (bound := fun _ => M)
      (F := fun x t => ((pderiv1 V)^[k] F) (x, t))
      (F' := fun x t => ((pderiv1 V)^[k + 1] F) (x, t))
      (x₀ := s) (s := B) (hBopen.mem_nhds hs) ?_ ?_ ?_ ?_ ?_ ?_).2
    · filter_upwards [hBopen.mem_nhds hs] with x hx
      exact ContinuousOn.aestronglyMeasurable (μ := volume)
        (fun t ht => (((hcontIter k).continuousAt
          (hV.mem_nhds (hmemV x hx t (uIoc_subset_uIcc ht)))).comp
            (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt)
        measurableSet_uIoc
    · exact ContinuousOn.intervalIntegrable (μ := volume)
        (fun t ht => (((hcontIter k).continuousAt
          (hV.mem_nhds (hmemV s hs t ht))).comp
            (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt)
    · exact ContinuousOn.aestronglyMeasurable (μ := volume)
        (fun t ht => (((hcontIter (k + 1)).continuousAt
          (hV.mem_nhds (hmemV s hs t (uIoc_subset_uIcc ht)))).comp
            (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt)
        measurableSet_uIoc
    · refine Eventually.of_forall (fun t ht x hx => ?_)
      exact hM (x, t) ⟨⟨le_of_lt hx.1, le_of_lt hx.2⟩, uIoc_subset_uIcc ht⟩
    · exact intervalIntegrable_const
    · refine Eventually.of_forall (fun t ht x hx => ?_)
      have hd1 := hasDerivAt_slice hV (contDiffOn_pderiv1Iter hV hF k)
        (hmemV x hx t (uIoc_subset_uIcc ht))
      have hstep : ((pderiv1 V)^[k + 1] F) (x, t) = pderiv1 V ((pderiv1 V)^[k] F) (x, t) := by
        rw [Function.iterate_succ_apply']
      rw [hstep]
      exact hd1
  have hcontG : ∀ k : ℕ, ContinuousOn (fun u => ∫ t in c..d, ((pderiv1 V)^[k] F) (u, t)) B :=
    fun k u hu => (key k u hu).differentiableAt.continuousAt.continuousWithinAt
  -- bootstrap to all orders
  have hCD : ∀ k j : ℕ, ContDiffOn ℝ ((k : ℕ) : ℕ∞)
      (fun u => ∫ t in c..d, ((pderiv1 V)^[j] F) (u, t)) B := by
    intro k
    induction k with
    | zero =>
      intro j
      exact contDiffOn_zero.mpr (hcontG j)
    | succ k ih =>
      intro j
      have hcast : (((k + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) = (((k : ℕ) : ℕ∞) : WithTop ℕ∞) + 1 := by
        simp only [Nat.cast_succ, WithTop.coe_add, WithTop.coe_one]
      rw [hcast, contDiffOn_succ_iff_deriv_of_isOpen hBopen]
      refine ⟨fun x hx => (key j x hx).differentiableAt.differentiableWithinAt, ?_, ?_⟩
      · intro htop
        exact absurd htop (by simp)
      · refine (ih (j + 1)).congr (fun x hx => ?_)
        exact (key j x hx).deriv
  have hfinal : ContDiffOn ℝ (⊤ : ℕ∞) (fun u => ∫ t in c..d, F (u, t)) B := by
    rw [contDiffOn_iff_forall_nat_le]
    intro m _
    simpa using hCD m 0
  exact hfinal.contDiffAt (hBopen.mem_nhds hs₀B)

end

end Work.OddVolterra.Smooth.Alt
