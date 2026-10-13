import Mathlib
import Submission.Work.WilE3.Taylor.Arc.fibre_card_le

namespace Work.WilE3.Taylor.Arc

/-- **A map ramified of order `a` at `0` is locally `a`-to-one.**

If `σ s - σ 0 = s ^ a • v s` with `v` analytic at `0`, `v 0 ≠ 0` and `a > 0`, then near `0`
every fibre of `σ` has at most `a` points: for every finite set `S` of points close enough
to `0` one has `S.card ≤ a * (S.image σ).card`.

The proof picks a coordinate `j₀` with `v 0 j₀ ≠ 0` and applies the scalar fibre bound
`fibre_card_le` to `z ↦ v z j₀`: each fibre `S.filter (σ · = c)` is a set of at most `a`
solutions of `z ^ a * v z j₀ = c j₀ - σ 0 j₀`, and the cardinals add up over the image. -/
theorem card_le_mul_card_image {k : ℕ} {σ : ℂ → Fin k → ℂ} {a : ℕ} (ha : 0 < a)
    {v : ℂ → Fin k → ℂ} (hv : AnalyticAt ℂ v 0) (hv0 : v 0 ≠ 0)
    (hram : ∀ s : ℂ, σ s - σ 0 = s ^ a • v s) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S : Finset ℂ, (∀ s ∈ S, ‖s‖ < δ) → S.card ≤ a * (S.image σ).card := by
  classical
  -- Some coordinate of `v 0` is nonzero (this also handles `k = 0`, where `v 0 ≠ 0` is absurd).
  obtain ⟨j₀, hj₀⟩ : ∃ j : Fin k, v 0 j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hv0 (funext h)
  have hvj : AnalyticAt ℂ (fun z => v z j₀) 0 :=
    ((ContinuousLinearMap.proj j₀ : (Fin k → ℂ) →L[ℂ] ℂ).analyticAt (v 0)).comp hv
  -- `σ` is at most `a`-to-`1` near `0`, tested on the `j₀`-th coordinate.
  obtain ⟨δ, hδ, hbound⟩ := fibre_card_le ha hvj hj₀
  refine ⟨δ, hδ, ?_⟩
  intro S hS
  -- Every fibre of `σ` inside `S` has at most `a` elements.
  have hfib : ∀ c ∈ S.image σ, (S.filter (fun s => σ s = c)).card ≤ a := by
    intro c _
    apply hbound (c j₀ - σ 0 j₀)
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hzS, hzc⟩ := hz
    refine ⟨hS z hzS, ?_⟩
    have h2 : z ^ a • v z = c - σ 0 := by rw [← hram z, hzc]
    have h3 := congr_fun h2 j₀
    simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] using h3
  -- Add the fibre counts over the image.
  calc S.card = ∑ c ∈ S.image σ, (S.filter (fun s => σ s = c)).card :=
        Finset.card_eq_sum_card_fiberwise (f := σ) (t := S.image σ)
          (fun x hx => Finset.mem_image_of_mem σ hx)
    _ ≤ ∑ _c ∈ S.image σ, a := Finset.sum_le_sum hfib
    _ = a * (S.image σ).card := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        simp

end Work.WilE3.Taylor.Arc
