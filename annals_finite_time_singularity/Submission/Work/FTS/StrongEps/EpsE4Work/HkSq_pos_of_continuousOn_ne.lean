import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Work

/-- **A continuity/nonvanishing box.**  If `f` is continuous on the open quadrant and
`f z₀ θ₀ ≠ 0` at an interior point `(z₀,θ₀)` (`z₀ > 0`, `0 < θ₀ < π/2`), then there is a
nondegenerate rectangle `(a,b) × (c,d)`, contained in the open quadrant and containing
`(z₀,θ₀)`, on which `f` does not vanish.

This is the purely topological input of `HkSq_pos_of_continuousOn_ne`: the `i = 0` slot
`(f z θ · w z / sin(2θ)^{η/2})²` of `HkIntegrand` is then strictly positive on a set of
positive measure. -/
theorem exists_box_ne {f : ℝ → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {z₀ θ₀ : ℝ} (hz : 0 < z₀) (hθ : θ₀ ∈ Set.Ioo 0 (π / 2)) (hne : f z₀ θ₀ ≠ 0) :
    ∃ a b c d : ℝ, 0 < a ∧ a < z₀ ∧ z₀ < b ∧ 0 < c ∧ c < θ₀ ∧ θ₀ < d ∧ d < π / 2 ∧
      ∀ z ∈ Set.Ioo a b, ∀ θ ∈ Set.Ioo c d, f z θ ≠ 0 := by
  -- `f` is continuous at the interior point `(z₀,θ₀)`, hence `{f ≠ 0}` is a neighbourhood of it
  have hnhds : Set.Ioi (0 : ℝ) ×ˢ Set.Ioo 0 (π / 2) ∈ 𝓝 (z₀, θ₀) :=
    (isOpen_Ioi.prod isOpen_Ioo).mem_nhds ⟨hz, hθ⟩
  have hcAt : ContinuousAt (Function.uncurry f) (z₀, θ₀) := hcont.continuousAt hnhds
  have hmem0 : {y : ℝ | y ≠ 0} ∈ 𝓝 (Function.uncurry f (z₀, θ₀)) :=
    (isOpen_ne (x := (0 : ℝ))).mem_nhds hne
  have hnhds2 : {p : ℝ × ℝ | f p.1 p.2 ≠ 0} ∈ 𝓝 (z₀, θ₀) :=
    hcAt.preimage_mem_nhds hmem0
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.mp hnhds2
  have hθ1 : 0 < θ₀ := hθ.1
  have hθ2 : θ₀ < π / 2 := hθ.2
  -- the half-side of the box
  set η : ℝ := min (ε / 2) (min (z₀ / 2) (min (θ₀ / 2) ((π / 2 - θ₀) / 2))) with hηdef
  have hηpos : 0 < η := by
    rw [hηdef]
    exact lt_min (by linarith) (lt_min (by linarith)
      (lt_min (by linarith) (by linarith)))
  have hηε : η ≤ ε / 2 := by rw [hηdef]; exact min_le_left _ _
  have hηz : η ≤ z₀ / 2 := by
    rw [hηdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hηθ : η ≤ θ₀ / 2 := by
    rw [hηdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hηπ : η ≤ (π / 2 - θ₀) / 2 := by
    rw [hηdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  refine ⟨z₀ - η, z₀ + η, θ₀ - η, θ₀ + η, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, ?_⟩
  intro z hzab θ hθcd
  have hzlt : |z - z₀| < η := by
    rw [abs_lt]; constructor <;> linarith [hzab.1, hzab.2]
  have hθlt : |θ - θ₀| < η := by
    rw [abs_lt]; constructor <;> linarith [hθcd.1, hθcd.2]
  have hdist : dist (z, θ) (z₀, θ₀) < ε := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
    exact ⟨lt_of_lt_of_le hzlt (by linarith), lt_of_lt_of_le hθlt (by linarith)⟩
  exact hε (Metric.mem_ball.mpr hdist)

theorem HkSq_pos_of_continuousOn_ne {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hmem : Work.Spaces.HkMem α k f)
    (hcont : ContinuousOn (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    {z₀ θ₀ : ℝ} (hz : 0 < z₀) (hθ : θ₀ ∈ Set.Ioo 0 (π / 2)) (hne : f z₀ θ₀ ≠ 0) :
    0 < Work.Spaces.HkSq α k f := by
  obtain ⟨a, b, c, d, hab, haz, hzb, hcd, hct, htd, hdp, hnebox⟩ :=
    exists_box_ne hcont hz hθ hne
  have hab' : a < b := lt_trans haz hzb
  have hcd' : c < d := lt_trans hct htd
  have hcdIθ : Set.Ioo c d ⊆ Work.Spaces.Iθ := fun θ hθ' =>
    ⟨le_of_lt (lt_trans hcd hθ'.1), le_of_lt (lt_trans hθ'.2 hdp)⟩
  -- the `θ`-slices of the integrand are strictly positive on the box
  have hinner : ∀ z ∈ Set.Ioo a b,
      0 < ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z hzab
    have hz0 : 0 < z := lt_trans hab hzab.1
    have hzI : z ∈ Work.Spaces.Iz := by
      rw [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt hz0
    have hFint : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ) Work.Spaces.Iθ :=
      hmem.1 z hzI
    have hFint' : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ) (Set.Ioo c d) :=
      hFint.mono_set hcdIθ
    have hpos_on : ∀ θ ∈ Set.Ioo c d, 0 < Work.Spaces.HkIntegrand α k f z θ := by
      intro θ hθ'
      have hfne : f z θ ≠ 0 := hnebox z hzab θ hθ'
      have hsinpos : 0 < Real.sin (2 * θ) := by
        refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
        · linarith [hθ'.1, hcd, Real.pi_pos]
        · linarith [hθ'.2, hdp, Real.pi_pos]
      have hwpos : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
      have hfac : 0 < Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2) :=
        div_pos hwpos (Real.rpow_pos_of_pos hsinpos _)
      have hs : 0 < (Work.Spaces.DzIter 0 f z θ
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 :=
        sq_pos_of_ne_zero (mul_ne_zero hfne (ne_of_gt hfac))
      exact lt_of_lt_of_le hs (Work.Spaces.sq_le_HkIntegrand_z α k f z θ 0 (Nat.zero_le k))
    have hsupp : Set.Ioo c d ⊆ Function.support (fun θ => Work.Spaces.HkIntegrand α k f z θ) :=
      fun θ hθ' => ne_of_gt (hpos_on θ hθ')
    have hgt : 0 < ∫ θ in Set.Ioo c d, Work.Spaces.HkIntegrand α k f z θ := by
      rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ) hFint']
      refine lt_of_lt_of_le ?_ (MeasureTheory.measure_mono fun θ hθ' => ⟨hsupp hθ', hθ'⟩)
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hcd')
    refine lt_of_lt_of_le hgt (MeasureTheory.setIntegral_mono_set hFint ?_ ?_)
    · filter_upwards with θ
      exact Work.Spaces.HkIntegrand_nonneg α k f z θ
    · filter_upwards with θ hθ'
      exact hcdIθ hθ'
  -- hence the `z`-slice integral is strictly positive on the box
  have houter : 0 < ∫ z in Set.Ioo a b,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) := by
    have hintab : IntegrableOn (fun z =>
        ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) (Set.Ioo a b) :=
      hmem.2.mono_set (fun z hz' => by
        rw [Work.Spaces.Iz, Set.mem_Ici]; exact le_of_lt (lt_trans hab hz'.1))
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun z =>
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ) hintab]
    have hsupp : Set.Ioo a b ⊆
        Function.support (fun z => ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k f z θ) := fun z hz' => ne_of_gt (hinner z hz')
    refine lt_of_lt_of_le ?_ (MeasureTheory.measure_mono fun z hz' => ⟨hsupp hz', hz'⟩)
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab')
  rw [Work.Spaces.HkSq]
  refine lt_of_lt_of_le houter (MeasureTheory.setIntegral_mono_set hmem.2 ?_ ?_)
  · filter_upwards with z
    exact MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k f z θ
  · filter_upwards with z hz'
    rw [Work.Spaces.Iz, Set.mem_Ici]
    exact le_of_lt (lt_trans hab hz'.1)

end Work.FTS.StrongEps.EpsE4Work
