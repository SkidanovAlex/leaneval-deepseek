import Mathlib

open scoped ContDiff Topology

namespace Work.NN.Newton

theorem inverseSmooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {w : E → E} {s : Set E} (hs : IsOpen s)
    (hw : ∀ m : ℕ, ContDiffOn ℝ m w s)
    (hinv : ∀ x ∈ s, ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ w x)
    (hinj : Set.InjOn w s)
    {Ψ : E → E} {t : Set E} (ht : IsOpen t) (hts : ∀ y ∈ t, Ψ y ∈ s)
    (hwΨ : ∀ y ∈ t, w (Ψ y) = y) :
    ∀ m : ℕ, ContDiffOn ℝ m Ψ t := by
  have hw_top : ContDiffOn ℝ ∞ w s := contDiffOn_infty.mpr hw
  have key : ContDiffOn ℝ ∞ Ψ t := by
    rw [ht.contDiffOn_iff]
    intro y hy
    have hx : Ψ y ∈ s := hts y hy
    have hwx : w (Ψ y) = y := hwΨ y hy
    obtain ⟨e, he⟩ := hinv (Ψ y) hx
    have hf : ContDiffAt ℝ ∞ w (Ψ y) := hw_top.contDiffAt (hs.mem_nhds hx)
    have hn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
    have hf' : HasFDerivAt w (e : E →L[ℝ] E) (Ψ y) := by
      rw [he]
      exact (hf.differentiableAt hn).hasFDerivAt
    have hstrict : HasStrictFDerivAt w (e : E →L[ℝ] E) (Ψ y) := hf.hasStrictFDerivAt' hf' hn
    -- Ψ is a left inverse of w near `Ψ y`
    have hgl : ∀ᶠ z in 𝓝 (Ψ y), Ψ (w z) = z := by
      have h1 : ∀ᶠ z in 𝓝 (Ψ y), z ∈ s := hs.mem_nhds hx
      have h2 : ∀ᶠ z in 𝓝 (Ψ y), w z ∈ t :=
        hf.continuousAt.preimage_mem_nhds (ht.mem_nhds (by rw [hwx]; exact hy))
      filter_upwards [h1, h2] with z hz_s hz_t
      exact (hinj hz_s (hts (w z) hz_t) (hwΨ (w z) hz_t).symm).symm
    -- hence Ψ agrees near `y` with the local inverse given by the inverse function theorem
    have huniq : ∀ᶠ z in 𝓝 y, Ψ z = hstrict.localInverse w e (Ψ y) z := by
      have := hstrict.localInverse_unique hgl
      rwa [hwx] at this
    have hcd : ContDiffAt ℝ ∞ (hf.localInverse hf' hn) y := by
      have := hf.to_localInverse hf' hn
      rwa [hwx] at this
    exact hcd.congr_of_eventuallyEq huniq
  intro m
  exact (contDiffOn_infty.mp key) m

end Work.NN.Newton
