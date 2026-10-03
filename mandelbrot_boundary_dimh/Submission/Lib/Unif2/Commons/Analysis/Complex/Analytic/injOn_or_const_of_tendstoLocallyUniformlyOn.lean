import Mathlib
import Submission.Lib.Unif2.Commons.Analysis.Complex.Analytic.locallyUniformLimit_injective_or_const

namespace Commons.Analysis.Complex.Analytic

open Filter Metric Set
open scoped Topology

noncomputable section

theorem injOn_or_const_of_tendstoLocallyUniformlyOn {R : ℝ} (hR : 0 < R) {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀ n, ∀ z ∈ Metric.ball (0 : ℂ) R, AnalyticAt ℂ (f n) z)
    (hg : ∀ z ∈ Metric.ball (0 : ℂ) R, AnalyticAt ℂ g z)
    (hconv : TendstoLocallyUniformlyOn f g Filter.atTop (Metric.ball (0 : ℂ) R))
    (hinj : ∀ n, Set.InjOn (f n) (Metric.ball (0 : ℂ) R)) :
    Set.InjOn g (Metric.ball (0 : ℂ) R) ∨ ∃ c : ℂ, ∀ z ∈ Metric.ball (0 : ℂ) R, g z = c := by
  -- View the open ball as a `ℂ`-charted space, so that the general Hurwitz-type theorem
  -- `locallyUniformLimit_injective_or_const` applies verbatim.
  have hne : Nonempty (Metric.ball (0:ℂ) R) := ⟨0, by simp [Metric.mem_ball, hR]⟩
  letI : Nonempty (Metric.ball (0:ℂ) R) := hne
  haveI : ConnectedSpace (Metric.ball (0:ℂ) R) :=
    isConnected_iff_connectedSpace.mp
      ⟨⟨0, by simp [Metric.mem_ball, hR]⟩, (convex_ball (0:ℂ) R).isPreconnected⟩
  let h : Topology.IsOpenEmbedding (Subtype.val : (Metric.ball (0:ℂ) R) → ℂ) :=
    Metric.isOpen_ball.isOpenEmbedding_subtypeVal
  letI : ChartedSpace ℂ (Metric.ball (0:ℂ) R) := h.singletonChartedSpace
  let e : OpenPartialHomeomorph (Metric.ball (0:ℂ) R) ℂ := h.toOpenPartialHomeomorph Subtype.val
  have he_apply : ∀ y : (Metric.ball (0:ℂ) R), e y = y.val := by
    intro y; rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_apply]
  have he_target : e.target = Set.range (Subtype.val : (Metric.ball (0:ℂ) R) → ℂ) :=
    Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target Subtype.val h
  -- In the chart at `x` (which is the inclusion of the ball), analyticity is the same as
  -- analyticity on the ambient `ℂ`.
  have htrans : ∀ (F : ℂ → ℂ),
      (∀ z ∈ Metric.ball (0:ℂ) R, AnalyticAt ℂ F z) →
      ∀ x : Metric.ball (0:ℂ) R,
        AnalyticAt ℂ ((fun y : Metric.ball (0:ℂ) R => F y.val) ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) := by
    intro F hF x
    change AnalyticAt ℂ ((fun y : Metric.ball (0:ℂ) R => F y.val) ∘ e.symm) (e x)
    have hxsrc : x ∈ e.source := mem_chart_source ℂ x
    have heq : ((fun y : Metric.ball (0:ℂ) R => F y.val) ∘ e.symm) =ᶠ[𝓝 (e x)] F := by
      have hmem : e.target ∈ 𝓝 (e x) := e.open_target.mem_nhds (e.map_source hxsrc)
      filter_upwards [hmem] with z hz
      show F (e.symm z).val = F z
      have hz' : z ∈ Set.range (Subtype.val : (Metric.ball (0:ℂ) R) → ℂ) := by rwa [← he_target]
      rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_right_inv Subtype.val h hz']
    have hce : e x = (x : ℂ) := he_apply x
    rw [hce] at heq
    exact (hF (x:ℂ) x.2).congr heq.symm
  have hf' : ∀ (n : ℕ) (x : Metric.ball (0:ℂ) R),
      AnalyticAt ℂ ((fun y : Metric.ball (0:ℂ) R => f n y.val) ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) := fun n x => htrans (f n) (fun z hz => hf n z hz) x
  have hg' : ∀ (x : Metric.ball (0:ℂ) R),
      AnalyticAt ℂ ((fun y : Metric.ball (0:ℂ) R => g y.val) ∘ (chartAt ℂ x).symm)
        ((chartAt ℂ x) x) := fun x => htrans g (fun z hz => hg z hz) x
  have hconv' : TendstoLocallyUniformlyOn (fun n (x : Metric.ball (0:ℂ) R) => f n x.val)
      (fun x : Metric.ball (0:ℂ) R => g x.val) Filter.atTop Set.univ :=
    tendstoLocallyUniformlyOn_univ.mpr
      ((tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe).mp hconv)
  have hinj' : ∀ n, Function.Injective (fun x : Metric.ball (0:ℂ) R => f n x.val) :=
    fun n a b hab => Subtype.ext (hinj n a.2 b.2 hab)
  rcases locallyUniformLimit_injective_or_const hf' hg' hconv' hinj' with hcase | hcase
  · left
    intro a ha b hb hab
    have h2 : (⟨a, ha⟩ : Metric.ball (0:ℂ) R) = ⟨b, hb⟩ := by
      apply hcase
      simpa using hab
    exact congrArg Subtype.val h2
  · right
    obtain ⟨c, hc⟩ := hcase
    exact ⟨c, fun z hz => hc ⟨z, hz⟩⟩

end

end Commons.Analysis.Complex.Analytic
