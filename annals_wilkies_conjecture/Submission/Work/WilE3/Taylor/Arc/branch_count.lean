import Mathlib
import Submission.Work.WilE3.Taylor.Arc.fibre_card_le
import Submission.Work.WilE3.Frame.exists_card_solutions_simple_tendsto

namespace Work.WilE3.Taylor.Arc

/-- A punctured-neighbourhood `∀ᶠ` statement is an explicit `ε`-`δ` statement:  if
eventually in `𝓝[≠] 0` the predicate `P` holds, then for all small nonzero `ε` the predicate
holds.  (The converse is not needed.) -/
private lemma punctured_eventually_iff {P : ℂ → Prop}
    (h : ∀ᶠ ε in nhdsWithin (0 : ℂ) {0}ᶜ, P ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℂ, 0 < ‖ε‖ → ‖ε‖ < δ → P ε := by
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h
  obtain ⟨δ, hδ, hδp⟩ := h
  exact ⟨δ, hδ, fun ε h0 hlt => hδp (by simpa [dist_eq_norm] using hlt) (by simpa using h0)⟩

/-- **The number of branches is at least `m / a`.**

Let `g` be analytic at `0` with `g 0 = 0` of order `m`, and let `σ s = s ^ a • v s` with `v`
analytic at `0`, `v 0 ≠ 0`.  Then, for all sufficiently small `ε ≠ 0`, the `m` simple solutions
of `g = ε` near `0` map under `σ` onto a set `T` of at least `m / a` values:  indeed `σ` is at
most `a`-to-`1` near `0` (`fibre_card_le`, applied to a nonzero coordinate of `v 0`, which exists
because `v 0 ≠ 0`), while `g = ε` has exactly `m` simple solutions in a small disc
(`exists_card_solutions_simple_tendsto`), all of which tend to `0` as `ε → 0` and hence lie in
the region where `σ` is at most `a`-to-`1`. -/
theorem branch_count {k : ℕ} {σ : ℂ → Fin k → ℂ} {g : ℂ → ℂ} {a m : ℕ}
    (hσ : AnalyticAt ℂ σ 0) (hg : AnalyticAt ℂ g 0) (hg0 : g 0 = 0)
    (hm : analyticOrderAt g 0 = m) (ha : 0 < a)
    (hram : ∃ v : ℂ → Fin k → ℂ, AnalyticAt ℂ v 0 ∧ v 0 ≠ 0 ∧ ∀ s : ℂ, σ s = s ^ a • v s) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧ ∀ ε : ℂ, 0 < ‖ε‖ → ‖ε‖ < δ →
      ∃ T : Finset (Fin k → ℂ),
        (∀ y ∈ T, ∃ s : ℂ, ‖s‖ < r ∧ σ s = y ∧ g s = ε ∧ deriv g s ≠ 0) ∧
        m ≤ a * T.card := by
  classical
  obtain ⟨v, hv, hv0, hσv⟩ := hram
  -- Some coordinate of `v 0` is nonzero (this also rules out `k = 0`).
  obtain ⟨j₀, hj₀⟩ : ∃ j : Fin k, v 0 j ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hv0 (funext h)
  have hvj : AnalyticAt ℂ (fun z => v z j₀) 0 :=
    ((ContinuousLinearMap.proj j₀ : (Fin k → ℂ) →L[ℂ] ℂ).analyticAt (v 0)).comp hv
  -- `σ` is at most `a`-to-`1` near `0`.
  obtain ⟨δ', hδ', hbound⟩ := fibre_card_le ha hvj hj₀
  -- `g = ε` has exactly `m` simple solutions near `0`, all tending to `0`.
  obtain ⟨r₁, δ₁, hr₁, hδ₁, hcount, hconv⟩ :=
    Work.WilE3.Frame.exists_card_solutions_simple_tendsto hg hg0 m hm
  -- Shrink so that every solution in the disc of radius `r₁` is within `δ'` of `0`.
  have hsmall : ∃ δ₂ : ℝ, 0 < δ₂ ∧ ∀ ε : ℂ, 0 < ‖ε‖ → ‖ε‖ < δ₂ →
      ∀ z : ℂ, g z = ε → ‖z‖ < r₁ → ‖z‖ < δ' :=
    punctured_eventually_iff (by simpa only [sub_zero] using hconv δ' hδ')
  obtain ⟨δ₂, hδ₂, hδ₂prop⟩ := hsmall
  refine ⟨r₁, min δ₁ δ₂, hr₁, lt_min hδ₁ hδ₂, ?_⟩
  intro ε hε0 hεδ
  have hεδ₁ : ‖ε‖ < δ₁ := lt_of_lt_of_le hεδ (min_le_left _ _)
  have hεδ₂ : ‖ε‖ < δ₂ := lt_of_lt_of_le hεδ (min_le_right _ _)
  obtain ⟨S, hScard, hSsol, _hSall⟩ := hcount ε hε0 hεδ₁
  refine ⟨S.image σ, ?_, ?_⟩
  · -- every value of `T` is attained by a simple solution
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨s, hsS, rfl⟩ := hy
    obtain ⟨hgε, hsr, hder⟩ := hSsol s hsS
    exact ⟨s, by simpa using hsr, rfl, hgε, hder⟩
  · -- counting: the `m` solutions are distributed over the values of `T`, at most `a` per value
    have hcard : S.card = ∑ y ∈ S.image σ, (S.filter (fun z => σ z = y)).card :=
      Finset.card_eq_sum_card_fiberwise (f := σ) (t := S.image σ)
        (fun x hx => Finset.mem_image_of_mem σ hx)
    have hfib : ∀ y ∈ S.image σ, (S.filter (fun z => σ z = y)).card ≤ a := by
      intro y _hy
      apply hbound (y j₀)
      intro z hz
      rw [Finset.mem_filter] at hz
      obtain ⟨hzS, hzy⟩ := hz
      obtain ⟨hgz, hzr, _⟩ := hSsol z hzS
      refine ⟨hδ₂prop ε hε0 hεδ₂ z hgz (by simpa using hzr), ?_⟩
      have h2 : z ^ a • v z = y := by rw [← hσv z, hzy]
      simpa [Pi.smul_apply, smul_eq_mul] using congr_fun h2 j₀
    calc m = S.card := hScard.symm
      _ = ∑ y ∈ S.image σ, (S.filter (fun z => σ z = y)).card := hcard
      _ ≤ ∑ _y ∈ S.image σ, a := Finset.sum_le_sum hfib
      _ = a * (S.image σ).card := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
          simp

end Work.WilE3.Taylor.Arc
