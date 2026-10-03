import Mathlib
import Submission.Work.L62.chain

/-!
# `Work.L62.march_up_im_nonneg`: the marching direction forces the sign of `Im β`

Shishikura's Lemma 6.2 (lifted `ℂ/ℤ` model) produces, for `ĥ = R - β`, a backward chain of discs
`W j` with `ĥ '' W (j+1) = W j` marching to one end of the cylinder.  In the `s = 1` case the discs
march to the upper end.  This file proves that this forces `0 ≤ Im β`, in the form needed by the
§6 assembly.

The mechanism is the asymptotic `E w - w → 0` (`E = d.E = Φ ∘ φ`) at the upper end
(`ParabData.E_upper`): for `w` of large imaginary part,

`Im (d.E w - β) - Im w = (Im (d.E w) - Im w) - Im β ≈ - Im β`.

So if `Im β < 0`, the discs `W j` sit *below* the discs `W (j+1)`: every `w ∈ W (j+1)` has
`Im w ≤ Im (ĥ w) - ε` with `ε = -Im β / 2 > 0`, hence the "height caps" of the discs drop by `ε`
at each step, and the chain cannot march to `+∞`.  Concretely, if `R` bounds the heights of `W J`
and the asymptotic estimate holds above height `T`, then

`∀ K, ∀ w ∈ W (J+K), Im w ≤ max T (R - K ε)`,

which contradicts `IsChain.marching` (which says that all points of `W j`, `j ≥ J`, have
imaginary part `> T`) at index `J + N` for `N` large enough that `R - N ε < T`: the disc
`W (J+N)` is nonempty (`IsConnected`), so it has a point that is simultaneously `> T` and `≤ T`.
-/

namespace Work.L62

open MandelDim Set Filter Topology

noncomputable section

/-- A predicate is eventually true along `upperEnd` iff it holds for every point of sufficiently
large imaginary part. -/
lemma marchUp_eventually_upperEnd {P : ℂ → Prop} :
    (∀ᶠ w in MandelDim.upperEnd, P w) ↔ ∃ T : ℝ, ∀ w : ℂ, T ≤ w.im → P w := by
  rw [MandelDim.upperEnd, Filter.eventually_comap, Filter.eventually_atTop]
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨T, fun w hw => hT w.im hw w rfl⟩
  · rintro ⟨T, hT⟩
    exact ⟨T, fun t ht w hwt => hT w (hwt ▸ ht)⟩

theorem march_up_im_nonneg {g₀ : ℂ → ℂ} {D : Set ℂ} (d : ParabData g₀ D)
    {β : ℂ} {DR : Set ℂ} {ζa ζb : ℂ} {ρ C₀ C₁ C₁' : ℝ} {W : ℕ → Set ℂ}
    (h : Work.L62.IsChain d.E β DR ζa ζb ρ 1 C₀ C₁ C₁' W) : 0 ≤ β.im := by
  by_contra hcon
  have hβneg : β.im < 0 := not_le.mp hcon
  set ε : ℝ := -β.im / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hβim : β.im = -2 * ε := by rw [hεdef]; ring
  -- the upper-end asymptotic of `d.E`: `‖d.E w - w‖ < ε` for `Im w ≥ T`
  obtain ⟨T, hT⟩ : ∃ T : ℝ, ∀ w : ℂ, T ≤ w.im → ‖d.E w - w‖ < ε := by
    have h1 : ∀ᶠ w in MandelDim.upperEnd, ‖d.E w - w‖ < ε := by
      have h2 : ∀ᶠ w in MandelDim.upperEnd, dist (d.E w - w) 0 < ε := by
        simpa only [MandelDim.ParabData.E] using
          d.E_upper.eventually (Metric.ball_mem_nhds (0 : ℂ) hεpos)
      exact h2.mono fun w hw => by rwa [dist_zero_right] at hw
    rwa [marchUp_eventually_upperEnd] at h1
  -- `W J` lies above height `T`, and `R` bounds its heights
  obtain ⟨J, hJ⟩ := h.marching T
  obtain ⟨R, hR⟩ := (h.bounded J).1.exists_norm_le
  -- a step large enough that the cap `R - N ε` has dropped below `T`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, R - (N : ℝ) * ε < T := by
    obtain ⟨N, hN⟩ := exists_nat_gt ((R - T) / ε)
    refine ⟨N, ?_⟩
    have hlt : (R - T) / ε < (N : ℝ) := hN
    rw [div_lt_iff₀ hεpos] at hlt
    linarith
  -- the height caps drop by `ε` at every step of the chain
  have key : ∀ K : ℕ, ∀ w ∈ W (J + K), w.im ≤ max T (R - (K : ℝ) * ε) := by
    intro K
    induction K with
    | zero =>
        intro w hw
        simp only [Nat.cast_zero, zero_mul, sub_zero]
        exact le_trans (le_trans (Complex.im_le_norm w) (hR w hw)) (le_max_right _ _)
    | succ K ih =>
        intro w hw
        have hw' : w ∈ W ((J + K) + 1) := by rwa [← Nat.add_assoc] at hw
        have himage : d.E w - β ∈ W (J + K) := by
          rw [← (h.chain (J + K)).2.2]
          exact mem_image_of_mem _ hw'
        have hih := ih (d.E w - β) himage
        rw [Nat.cast_succ]
        by_cases hwT : w.im ≤ T
        · exact le_trans hwT (le_max_left _ _)
        · have hwT' : T < w.im := not_le.mp hwT
          have herr : ‖d.E w - w‖ < ε := hT w (le_of_lt hwT')
          have herr' : w.im - ε < (d.E w).im := by
            have h1 : |(d.E w - w).im| ≤ ‖d.E w - w‖ := Complex.abs_im_le_norm _
            rw [Complex.sub_im] at h1
            have h2 : |(d.E w).im - w.im| < ε := lt_of_le_of_lt h1 herr
            have h3 := (abs_lt.mp h2).1
            linarith
          have him : w.im < (d.E w - β).im - ε := by
            rw [Complex.sub_im, hβim]
            linarith
          have hstep : w.im ≤ max T (R - (K : ℝ) * ε) - ε := by linarith
          have hmono : max T (R - (K : ℝ) * ε) - ε ≤ max T (R - ((K : ℝ) + 1) * ε) := by
            have hA : R - ((K : ℝ) + 1) * ε = (R - (K : ℝ) * ε) - ε := by ring
            rw [hA]
            rcases le_total (R - (K : ℝ) * ε) T with hcase | hcase
            · rw [max_eq_left hcase]
              exact le_trans (by linarith : T - ε ≤ T) (le_max_left _ _)
            · rw [max_eq_right hcase]
              exact le_max_right _ _
          linarith
  -- contradiction: `W (J+N)` is nonempty but is both bounded above by `T` and eventually above `T`
  obtain ⟨w, hw⟩ := ((h.open_conn (J + N)).2).nonempty
  have hgt : T < w.im := by
    have h1 := hJ (J + N) (Nat.le_add_right J N) w hw
    simpa using h1
  have hle := key N w hw
  rw [max_eq_left (le_of_lt hN)] at hle
  linarith

end

end Work.L62
