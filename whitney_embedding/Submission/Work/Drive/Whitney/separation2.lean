import Mathlib
import Submission.Work.Drive.Whitney.modelChart2

/-!
# The separation clause of the corrected model chart is automatic

`Work.Drive.Whitney.ModelChartData2` carries the *separation* clause `hsepδ`: the image of `f`
outside the two patches stays at distance `≥ δ` from the graph patch over the closure of the
finger's base region.  This module proves that this clause is **automatic** once the two-sheet
presentation is available: the two sets are compact and disjoint (`hclean`/`hsep` exclude every
coincidence), so their distance is positive.

This is the reduction that leaves the *two-sheet normal form* as the only geometric content of
`ModelChartDataAll2`. -/

namespace Work.Drive.Whitney

open scoped Manifold ContDiff
open Set Metric

set_option linter.unusedVariables false

/-- **The separation exists.**  Under the sheet presentation (`σ` maps `regσ` onto the graph of `c`,
the patch is inside `W`, and the patch avoids the partner double points `p₁, q₁`, while the tube `U₁`
contains them), the image of `f` outside the two patches is at positive distance `δ` from the graph
patch over `closure reg2`. -/
theorem exists_separation {n k : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (c : ℝ → ℝ) (hc : Continuous c)
    (Φ : EuclideanSpace ℝ (Fin (2 * n)) → Mdl k)
    (hΦc : Continuous fun y : M => Φ (f y))
    (Θ : Mdl k → EuclideanSpace ℝ (Fin (2 * n))) (hΘΦ : ∀ z, Θ (Φ z) = z)
    (regσ : Set (ℝ × EuclideanSpace ℝ (Fin k)))
    (σ : ℝ × EuclideanSpace ℝ (Fin k) → M)
    (hσ : ∀ p ∈ regσ, f (σ p) = Θ (p.1, c p.1, 0, p.2))
    (hregsub : closure (reg2 (k := k)) ⊆ regσ)
    (hW : σ '' regσ ⊆ W)
    (hpatch₁ : p₁ ∉ σ '' regσ) (hpatch₃ : q₁ ∉ σ '' regσ)
    (U₁ : Set M) (hU₁p₁ : p₁ ∈ U₁) (hU₁q₁ : q₁ ∈ U₁)
    (hU₁o : IsOpen U₁) (hWo : IsOpen (σ '' regσ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : M, y ∉ U₁ → y ∉ σ '' regσ →
      ∀ p ∈ closure (reg2 (k := k)), δ ≤ ‖Φ (f y) - (p.1, c p.1, 0, p.2)‖ := by
  classical
  set Y : Set M := (U₁ ∪ σ '' regσ)ᶜ with hYdef
  have hYclosed : IsClosed Y := (hU₁o.union hWo).isClosed_compl
  -- the graph patch is compact
  have hregc : reg2c (k := k) = Set.Icc (-(3 / 2) : ℝ) (3 / 2) ×ˢ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 := by
    ext p
    simp only [reg2c, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Icc, Metric.mem_closedBall,
      dist_zero_right]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨abs_le.mp h1, h2⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨abs_le.mpr ⟨h1, h2⟩, h3⟩
  have hKc : IsCompact (closure (reg2 (k := k))) := by
    rw [closure_reg2, hregc]
    exact (isCompact_Icc).prod (isCompact_closedBall _ _)
  -- the function whose minimum we take
  have hcont : Continuous fun z : M × (ℝ × EuclideanSpace ℝ (Fin k)) =>
      ‖Φ (f z.1) - (z.2.1, c z.2.1, 0, z.2.2)‖ := by
    refine Continuous.norm ?_
    refine (hΦc.comp continuous_fst).sub ?_
    refine Continuous.prodMk (continuous_fst.comp continuous_snd) ?_
    refine Continuous.prodMk ((hc.comp (continuous_fst.comp continuous_snd))) ?_
    exact Continuous.prodMk continuous_const (continuous_snd.comp continuous_snd)
  by_cases hne : Y.Nonempty
  swap
  · -- the set of admissible `y` is empty: any positive δ works
    refine ⟨1, one_pos, ?_⟩
    intro y hy₁ hy₂
    exact absurd ⟨y, by
      simp only [hYdef, Set.mem_compl_iff]
      exact not_or.mpr ⟨hy₁, hy₂⟩⟩ hne
  · have hK : IsCompact (Y ×ˢ closure (reg2 (k := k))) := hYclosed.isCompact.prod hKc
    have hKne : (Y ×ˢ closure (reg2 (k := k))).Nonempty :=
      hne.prod ⟨_, subset_closure mem_reg2_1⟩
    obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKne hcont.continuousOn
    have hz₀' : z₀.1 ∈ Y ∧ z₀.2 ∈ closure (reg2 (k := k)) := hz₀
    have hpos : 0 < ‖Φ (f z₀.1) - (z₀.2.1, c z₀.2.1, 0, z₀.2.2)‖ := by
      rw [norm_pos_iff]
      intro hzero
      have hz : Φ (f z₀.1) = (z₀.2.1, c z₀.2.1, 0, z₀.2.2) := sub_eq_zero.mp hzero
      have hmemY : z₀.1 ∈ Y := hz₀'.1
      simp only [hYdef, Set.mem_compl_iff, Set.mem_union, not_or] at hmemY
      obtain ⟨hyU₁, hyσ⟩ := hmemY
      have hpσ : z₀.2 ∈ regσ := hregsub hz₀'.2
      have hfy : f z₀.1 = f (σ z₀.2) := by
        rw [hσ z₀.2 hpσ, ← hz, hΘΦ]
      have hσW : σ z₀.2 ∈ W := hW ⟨z₀.2, hpσ, rfl⟩
      by_cases hyW : z₀.1 ∈ W
      · rcases hclean z₀.1 (σ z₀.2) hyW hσW hfy with h | h | h | h | h
        · exact hyσ ⟨z₀.2, hpσ, h.symm⟩
        · exact hyU₁ (h.1 ▸ hU₁p₁)
        · exact hpatch₁ ⟨z₀.2, hpσ, h.2⟩
        · exact hyU₁ (h.1 ▸ hU₁q₁)
        · exact hpatch₃ ⟨z₀.2, hpσ, h.2⟩
      · exact absurd hfy.symm (hsep (σ z₀.2) z₀.1 hσW hyW)
    refine ⟨_, hpos, ?_⟩
    intro y hy₁ hy₂ p hp
    have hyY : y ∈ Y := by
      simp only [hYdef, Set.mem_compl_iff]
      exact not_or.mpr ⟨hy₁, hy₂⟩
    exact hmin (show (y, p) ∈ Y ×ˢ closure (reg2 (k := k)) from ⟨hyY, hp⟩)

end Work.Drive.Whitney
