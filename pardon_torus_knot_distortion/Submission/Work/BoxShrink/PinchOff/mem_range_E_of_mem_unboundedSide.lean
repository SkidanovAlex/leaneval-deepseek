import Mathlib
import Submission.Work.Smooth.Jordan.All
import Submission.Work.Smooth.SphereJordan.disc_complement_preconnected

namespace Work.BoxShrink.PinchOff

/-- **The outer disc parametrisation covers the unbounded side.**

`c` is a simple closed plane curve (with separation datum `h`), `E : 𝔻 → S²` is a continuous
injection whose boundary circle maps to `c`, which sends `u₀` to `∞`, and which sends the open
disc minus `u₀` into the unbounded side `h.U`.  Then every point of `h.U` is in the image of `E`.

This is the "clopen" argument: `E '' 𝔻` is compact, hence closed in the Riemann sphere, and it is
contained in `↑''U ∪ ↑''(range c.γ) ∪ {∞}`; since `h.U` is a non-empty preconnected open set
disjoint from `range c.γ`, the open set `S² \ E '' 𝔻` intersected with `↑''h.U` is clopen in the
preconnected set `↑''h.U`, and it is not all of it (the image of an interior point of the disc,
different from `u₀`, lies in `h.U`), so it is empty. -/
theorem mem_range_E_of_mem_unboundedSide
    {c : Work.Smooth.Jordan.PlaneCurve} (h : Work.Smooth.Jordan.PlaneSeparation c)
    {E : Work.Smooth.Jordan.Disc → OnePoint ℂ} (hE : Continuous E)
    (hEinj : Function.Injective E)
    (hEb : ∀ θ : ℝ, E (Work.Smooth.Jordan.circlePoint θ) = ((c.γ θ : ℂ) : OnePoint ℂ))
    {u₀ : Work.Smooth.Jordan.Disc} (hEu₀ : E u₀ = OnePoint.infty)
    (hEopen : ∀ w : Work.Smooth.Jordan.Disc, ‖(w : ℂ)‖ < 1 → w ≠ u₀ →
      ∃ z : ℂ, E w = (z : OnePoint ℂ) ∧ z ∈ h.U) :
    ∀ z : ℂ, z ∈ h.U → ∃ w : Work.Smooth.Jordan.Disc, E w = (z : OnePoint ℂ) := by
  -- The complement of `E '' 𝔻` in the Riemann sphere is preconnected
  -- (`Work.Smooth.SphereJordan.disc_complement_preconnected`); this is the input that makes the
  -- "clopen" argument work: the complement of `E '' 𝔻` splits into the open pieces
  -- `↑''h.V` and `↑''h.U ∩ (E '' 𝔻)ᶜ`.
  have hpre : IsPreconnected ((Set.range E)ᶜ) :=
    Work.Smooth.SphereJordan.disc_complement_preconnected (f := ⟨E, hE⟩) hEinj
  have hclosed : IsClosed (Set.range E) := (isCompact_range hE).isClosed
  -- No point of the bounded side lies in the image of `E`: an interior point of the disc has
  -- image in `h.U` (or is `∞`), and a boundary point has image on the curve.
  have hV_notMem : ∀ v : ℂ, v ∈ h.V → ((v : ℂ) : OnePoint ℂ) ∉ Set.range E := by
    intro v hvV hv
    obtain ⟨w, hw⟩ := hv
    have hwle : ‖(w : ℂ)‖ ≤ 1 := by
      have h1 := w.2
      rw [Metric.mem_closedBall, dist_zero_right] at h1
      exact h1
    rcases lt_or_eq_of_le hwle with hlt | heq
    · rcases eq_or_ne w u₀ with rfl | hne
      · rw [hEu₀] at hw
        exact (OnePoint.coe_ne_infty v) hw.symm
      · obtain ⟨z, hz, hzU⟩ := hEopen w hlt hne
        have hzv : z = v := OnePoint.coe_injective (hz.symm.trans hw)
        exact Set.disjoint_left.mp h.disjoint_UV (hzv ▸ hzU) hvV
    · obtain ⟨θ, hθ⟩ := Work.Smooth.Jordan.exists_circlePoint_eq w heq
      have hv_trace : v ∈ c.trace := by
        refine ⟨θ, ?_⟩
        exact OnePoint.coe_injective (by rw [← hw, ← hθ, hEb θ])
      have : v ∈ c.traceᶜ := by rw [← h.union_eq]; exact Or.inr hvV
      exact this hv_trace
  -- The two open pieces of the complement of `E '' 𝔻`.
  set A : Set (OnePoint ℂ) := OnePoint.some '' h.V with hA
  set B : Set (OnePoint ℂ) := OnePoint.some '' h.U ∩ (Set.range E)ᶜ with hB
  have hAopen : IsOpen A := by rw [hA]; exact OnePoint.isOpen_image_coe.mpr h.isOpen_V
  have hBopen : IsOpen B := by
    rw [hB]
    exact (OnePoint.isOpen_image_coe.mpr h.isOpen_U).inter hclosed.isOpen_compl
  -- `↑''h.U` and `A` are disjoint, and `B ⊆ ↑''h.U`, so `A` and `B` are disjoint.
  have hUdisjV : Disjoint (OnePoint.some '' h.U) A := by
    rw [hA]
    exact (Set.disjoint_image_iff OnePoint.coe_injective).mpr h.disjoint_UV
  have hdisj : Disjoint A B :=
    hUdisjV.symm.mono_right (by rw [hB]; exact Set.inter_subset_left)
  -- The two pieces cover the complement of `E '' 𝔻`.
  have hcover : (Set.range E)ᶜ ⊆ A ∪ B := by
    intro x hx
    rw [hA, hB]
    have hxne : x ≠ OnePoint.infty := by
      intro hxi
      exact hx ⟨u₀, by rw [hxi, hEu₀]⟩
    obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hxne
    have hznotrace : z ∉ c.trace := by
      rintro ⟨θ, hθ⟩
      exact hx ⟨Work.Smooth.Jordan.circlePoint θ, by rw [hEb θ, hθ]⟩
    have hzUV : z ∈ h.U ∪ h.V := by
      rw [h.union_eq]; exact hznotrace
    rcases hzUV with hzU | hzV
    · exact Or.inr ⟨⟨z, hzU, rfl⟩, hx⟩
    · exact Or.inl ⟨z, hzV, rfl⟩
  -- Preconnectedness forces the complement of `E '' 𝔻` onto one of the two pieces.
  rcases hpre.subset_or_subset hAopen hBopen hdisj hcover with hsub | hsub
  · -- it is not contained in `B`: the bounded side is non-empty and disjoint from `↑''h.U`
    intro z hzU
    by_contra hcon
    exact (Set.disjoint_left.mp hUdisjV ⟨z, hzU, rfl⟩) (hsub hcon)
  · exfalso
    obtain ⟨v, hvV⟩ := h.nonempty_V
    have hvs : ((v : ℂ) : OnePoint ℂ) ∈ (Set.range E)ᶜ := hV_notMem v hvV
    have hmemB : ((v : ℂ) : OnePoint ℂ) ∈ B := hsub hvs
    rw [hB] at hmemB
    exact (Set.disjoint_left.mp hUdisjV hmemB.1) ⟨v, hvV, rfl⟩

end Work.BoxShrink.PinchOff
