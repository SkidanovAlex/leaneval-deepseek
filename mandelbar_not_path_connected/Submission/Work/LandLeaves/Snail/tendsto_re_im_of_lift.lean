import Mathlib
import Submission.Work.LandLeaves.Snail.exists_continuous_log_of_path

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The real and imaginary parts of a drifting logarithm

Let `L : ℝ → ℂ` be a continuous lift of `q` on `[0, ∞)`, i.e. `exp (L t) = q t` for `t ≥ 0`,
and suppose `q t → 0` while the unit drift `L (t+1) - L t` tends to `c` with `0 < c.im`.
Then the real part of `L` tends to `-∞` and the imaginary part to `+∞`.

The real part is immediate: `‖q t‖ = exp ((L t).re) → 0`.

For the imaginary part, the drift hypothesis gives a threshold `T` with
`Im (L (t+1) - L t) > d := c.im / 2` for all `t ≥ T`.  Hence, for `s ∈ [T, T+1]` and `n ∈ ℕ`,
`Im (L (s+n)) ≥ Im (L s) + n d`; since `Im ∘ L` is continuous on the compact interval
`[T, T+1]`, the term `Im (L s)` is bounded below by some `B`, and writing an arbitrary large
`t ≥ T` as `s + ⌊t - T⌋` with `s = t - ⌊t - T⌋ ∈ [T, T+1]` gives `Im (L t) ≥ B + d ⌊t - T⌋ → ∞`.
-/

open Filter
open scoped Topology

namespace Work.LandLeaves.Snail

theorem tendsto_re_im_of_lift {L : ℝ → ℂ} {q : ℝ → ℂ} {c : ℂ}
    (hLc : ContinuousOn L (Set.Ici 0)) (hL : ∀ t ∈ Set.Ici (0 : ℝ), Complex.exp (L t) = q t)
    (hlim : Filter.Tendsto q Filter.atTop (nhds 0))
    (hdrift : Filter.Tendsto (fun t : ℝ => L (t + 1) - L t) Filter.atTop (nhds c))
    (hc : 0 < c.im) :
    Filter.Tendsto (fun t : ℝ => (L t).re) Filter.atTop Filter.atBot ∧
      Filter.Tendsto (fun t : ℝ => (L t).im) Filter.atTop Filter.atTop := by
  constructor
  · -- The modulus of `q` is `exp (Re L)`.
    have hnorm : Tendsto (fun t : ℝ => ‖q t‖) atTop (nhds 0) := by
      simpa using hlim.norm
    have hexp : Tendsto (fun t : ℝ => Real.exp ((L t).re)) atTop (nhds 0) := by
      refine hnorm.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with t ht
      rw [← hL t ht, Complex.norm_exp]
    rw [Filter.tendsto_atBot]
    intro b
    filter_upwards [hexp.eventually (isOpen_Iio.mem_nhds (Real.exp_pos b))] with t ht
    exact le_of_lt ((Real.exp_lt_exp).1 ht)
  · -- Imaginary part.
    have him_drift : Tendsto (fun t : ℝ => (L (t + 1) - L t).im) atTop (nhds c.im) :=
      (Complex.continuous_im.tendsto c).comp hdrift
    set d : ℝ := c.im / 2 with hddef
    have hd : 0 < d := by linarith
    have hev : ∀ᶠ t in atTop, d < (L (t + 1) - L t).im := by
      have hlt : d < c.im := by linarith
      exact him_drift.eventually (isOpen_Ioi.mem_nhds hlt)
    obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 hev
    -- Shift the threshold into `[0, ∞)` so that `L` is continuous on the interval used below.
    set T : ℝ := max T₀ 0 with hTdef
    have hT0 : T₀ ≤ T := le_max_left _ _
    have hTnn : 0 ≤ T := le_max_right _ _
    have hdrift_ge : ∀ t : ℝ, T ≤ t → d < (L (t + 1) - L t).im :=
      fun t ht => hT₀ t (le_trans hT0 ht)
    have hycont : ContinuousOn (fun t : ℝ => (L t).im) (Set.Icc T (T+1)) :=
      Complex.continuous_im.comp_continuousOn (hLc.mono (fun x hx => le_trans hTnn hx.1))
    have hne : (Set.Icc T (T+1)).Nonempty := Set.nonempty_Icc.mpr (by linarith)
    -- `B := Im (L x₀)` is a lower bound for `Im ∘ L` on `[T, T+1]`.
    obtain ⟨x₀, _hx₀mem, hx₀min⟩ := isCompact_Icc.exists_isMinOn hne hycont
    have hx₀min' : ∀ s ∈ Set.Icc T (T+1), (L x₀).im ≤ (L s).im := fun s hs => hx₀min hs
    -- The growing lower bound `Im (L (s+n)) ≥ B + n d` for `s ∈ [T, T+1]`.
    have hmain : ∀ n : ℕ, ∀ s : ℝ, T ≤ s → s ≤ T + 1 →
        (L x₀).im + (n : ℝ) * d ≤ (L (s + (n : ℝ))).im := by
      intro n
      induction n with
      | zero =>
        intro s hs1 hs2
        have h := hx₀min' s ⟨hs1, hs2⟩
        simpa only [Nat.cast_zero, zero_mul, add_zero] using h
      | succ n ih =>
        intro s hs1 hs2
        have hge : T ≤ s + (n : ℝ) := by
          have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n; linarith
        have hstep := hdrift_ge (s + (n:ℝ)) hge
        have hstep' : d < (L (s + (n:ℝ) + 1)).im - (L (s + (n:ℝ))).im := by
          simpa [Complex.sub_im] using hstep
        have ih' := ih s hs1 hs2
        rw [show ((n+1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring]
        rw [show s + ((n:ℝ) + 1) = (s + (n:ℝ)) + 1 by ring]
        linarith
    rw [Filter.tendsto_atTop]
    intro M
    obtain ⟨n₀, hn₀⟩ := exists_nat_ge ((M - (L x₀).im) / d)
    have hn₀' : M ≤ (L x₀).im + (n₀:ℝ) * d := by
      have h1 := mul_le_mul_of_nonneg_right hn₀ (le_of_lt hd)
      have h2 : ((M - (L x₀).im) / d) * d = M - (L x₀).im := div_mul_cancel₀ _ (ne_of_gt hd)
      linarith
    filter_upwards [Filter.eventually_ge_atTop (T + (n₀:ℝ))] with t ht
    have htT : T ≤ t := by
      have hn : (0:ℝ) ≤ (n₀:ℝ) := Nat.cast_nonneg n₀; linarith
    have hsub : 0 ≤ t - T := by linarith
    -- Decompose `t = s + m` with `m = ⌊t - T⌋` and `s ∈ [T, T+1]`.
    set m : ℕ := Nat.floor (t - T) with hmdef
    have hmle : (m:ℝ) ≤ t - T := by rw [hmdef]; exact Nat.floor_le hsub
    have hmlt : t - T < (m:ℝ) + 1 := by rw [hmdef]; exact Nat.lt_floor_add_one (t - T)
    have hNle : (n₀:ℝ) ≤ t - T := by linarith
    have hmge : (n₀:ℝ) ≤ (m:ℝ) := by
      rw [hmdef]
      exact_mod_cast (Nat.le_floor (α := ℝ) (a := t - T) hNle)
    set s : ℝ := t - (m:ℝ) with hsdef
    have hs1 : T ≤ s := by rw [hsdef]; linarith
    have hs2 : s ≤ T + 1 := by rw [hsdef]; linarith
    have heq : s + (m:ℝ) = t := by rw [hsdef]; ring
    have hmain' := hmain m s hs1 hs2
    rw [heq] at hmain'
    have hb : (L x₀).im + (n₀:ℝ) * d ≤ (L x₀).im + (m:ℝ) * d := by
      have := mul_le_mul_of_nonneg_right hmge (le_of_lt hd); linarith
    linarith

end Work.LandLeaves.Snail
