import Mathlib

namespace Work.Drive

open scoped InnerProductSpace
open Filter MeasureTheory

/-- If `γ` is a global flow line of a continuous vector field `V` on a complete real inner
product space, and `γ t` converges as `t → -∞` to a point `x`, then `x` is an equilibrium:
`V x = 0`.

Proof: suppose `V x = v ≠ 0`.  Then `⟨V (γ t), v⟩` tends to `‖v‖² > 0` as `t → -∞`, so for
all `t ≤ T` we have `⟨V (γ t), v⟩ ≥ c` with `c = ‖v‖²/2 > 0`.  By the fundamental theorem of
calculus on the interval `[t, t+1]` (for `t ≤ T-1`),
`⟨γ (t+1), v⟩ - ⟨γ t, v⟩ = ∫_t^{t+1} ⟨V (γ u), v⟩ du ≥ c`,
so the difference `⟨γ (t+1), v⟩ - ⟨γ t, v⟩` is bounded below by `c > 0` for all sufficiently
negative `t`.  But convergence of `γ` at `-∞` forces this difference to tend to `0`.
Contradiction. -/
theorem flow_tendsto_atBot_eq_zero {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {V : E → E} (hV : Continuous V) {γ : ℝ → E}
    (hγ : ∀ t : ℝ, HasDerivAt γ (V (γ t)) t) {x : E}
    (hx : Filter.Tendsto γ Filter.atBot (nhds x)) :
    V x = 0 := by
  by_contra hne
  set v : E := V x with hv
  have hvne : v ≠ 0 := by rw [hv]; exact hne
  have hvv : 0 < ⟪v, v⟫_ℝ := by rw [real_inner_self_pos]; exact hvne
  set c : ℝ := ⟪v, v⟫_ℝ / 2 with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hγcont : Continuous γ := continuous_iff_continuousAt.mpr (fun t => (hγ t).continuousAt)
  have hVcont : Tendsto (fun t : ℝ => V (γ t)) atBot (nhds (V x)) :=
    hV.continuousAt.tendsto.comp hx
  have hf : Tendsto (fun t : ℝ => ⟪V (γ t), v⟫_ℝ) atBot (nhds ⟪v, v⟫_ℝ) := by
    have h1 := hVcont.inner (𝕜 := ℝ) (tendsto_const_nhds (x := v))
    simpa [← hv] using h1
  have hclt : c < ⟪v, v⟫_ℝ := by rw [hc]; linarith
  have hf_ev : ∀ᶠ t : ℝ in atBot, c < ⟪V (γ t), v⟫_ℝ := by
    have := hf.eventually (isOpen_Ioi.mem_nhds hclt)
    simpa using this
  obtain ⟨T, hT⟩ := Filter.eventually_atBot.1 (hf_ev.mono (fun t ht => le_of_lt ht))
  have hmain : ∀ t : ℝ, t ≤ T - 1 → c ≤ ⟪γ (t + 1), v⟫_ℝ - ⟪γ t, v⟫_ℝ := by
    intro t ht
    have hderiv : ∀ s ∈ Set.uIcc t (t + 1),
        HasDerivAt (fun u : ℝ => ⟪γ u, v⟫_ℝ) (⟪V (γ s), v⟫_ℝ) s := by
      intro s _
      have h := HasDerivAt.inner (𝕜 := ℝ) (hγ s) (hasDerivAt_const s v)
      simpa using h
    have hcont_int : Continuous (fun s : ℝ => ⟪V (γ s), v⟫_ℝ) :=
      (hV.comp hγcont).inner continuous_const
    have hint : IntervalIntegrable (fun s : ℝ => ⟪V (γ s), v⟫_ℝ) volume t (t + 1) :=
      hcont_int.intervalIntegrable t (t + 1)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hle : ∀ s ∈ Set.Icc t (t + 1), c ≤ ⟪V (γ s), v⟫_ℝ := by
      intro s hs
      have hsT : s ≤ T := by linarith [hs.2, ht]
      exact hT s hsT
    have hcint : (∫ u in t..(t + 1), c ∂volume) = c := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hmono := intervalIntegral.integral_mono_on (le_of_lt (lt_add_one t))
      intervalIntegrable_const hint hle
    rw [hcint, hFTC] at hmono
    exact hmono
  have hshift : Tendsto (fun t : ℝ => γ (t + 1)) atBot (nhds x) :=
    hx.comp (Filter.tendsto_atBot_add_const_right atBot 1 tendsto_id)
  have hconv : Tendsto (fun t : ℝ => ⟪γ (t + 1), v⟫_ℝ - ⟪γ t, v⟫_ℝ) atBot (nhds 0) := by
    have h1 := hshift.inner (𝕜 := ℝ) (tendsto_const_nhds (x := v))
    have h2 := hx.inner (𝕜 := ℝ) (tendsto_const_nhds (x := v))
    have h3 := h1.sub h2
    simpa using h3
  have hev1 : ∀ᶠ t : ℝ in atBot, ⟪γ (t + 1), v⟫_ℝ - ⟪γ t, v⟫_ℝ < c := by
    have hmem : Set.Iio c ∈ nhds (0 : ℝ) :=
      isOpen_Iio.mem_nhds (show (0 : ℝ) ∈ Set.Iio c from hcpos)
    have := hconv.eventually hmem
    simpa using this
  have hev2 : ∀ᶠ t : ℝ in atBot, c ≤ ⟪γ (t + 1), v⟫_ℝ - ⟪γ t, v⟫_ℝ :=
    Filter.eventually_atBot.2 ⟨T - 1, fun t ht => hmain t ht⟩
  obtain ⟨t, ht1, ht2⟩ := (hev1.and hev2).exists
  linarith

end Work.Drive
