/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# The Snail lemma in Milnor's form (ledger item 5)

`Work.LandLeaves.SnailLemmaMilnor` (file `SnailLemmaMilnor.lean`) is the classical **Snail
lemma** in the form in which the landing theory uses it -- Milnor, *Dynamics in one complex
variable*, 3rd ed., Lemma 16.2; also Buff--Raissy, *Introduction to Fatou components in
holomorphic dynamics*, Lemma 6.10:

> a holomorphic germ at a fixed point `z₀` which admits a continuous path `p : [0,∞) → U∖{z₀}`
> in a neighbourhood `U` of `z₀` with `g (p t) = p (t + 1)` for all `t ≥ 0` and `p t → z₀` has
> multiplier of modulus `< 1` or multiplier exactly `1`.

## Structure of the proof

Writing `λ = deriv g z₀`, the statement is `‖λ‖ < 1 ∨ λ = 1`.  The three cases are:

* `1 < ‖λ‖` (repelling): the local expansion `expansion_of_one_lt_norm_deriv` forces
  `‖g z - z₀‖ ≥ c ‖z - z₀‖` with `c > 1` near `z₀`, contradicting `p n → z₀`.
  This is `no_snail_of_one_lt_norm_deriv`.

* `‖λ‖ = 1` and `λ` is a *root of unity*, `λ ≠ 1`: put `h = g^q` (multiplier `1`).  The path is
  also a Snail path for `h`, and the *descent chart* `Z w = 1/(((r-1)c) w^(r-1))` of a germ
  `h w = w + c w^r + O(w^(r+1))` (`c ≠ 0`, `r ≥ 2`) linearises `h` up to `O(‖Z‖^(-1/(r-1)))`
  (`chart_descent_bound`).  Along the path this error is small and of one sign, so
  `Re (Z (p t)) → -∞` (`descentPath_re_tendsto_atBot`); consequently the *directions*
  `p t / ‖p t‖` eventually lie in the closed "petal" set `{d : Re (c d^(r-1)) ≤ 0}`, a proper
  closed subset of the unit circle.  On the other hand the set of limit directions
  (`directionLimitSet`) is compact, nonempty and preconnected
  (`directionLimitSet_compact`), lies in the unit circle, and is invariant under multiplication
  by `λ` (`directionLimitSet_invariant`, because `g w = λ w + O(w²)` rotates directions by
  `arg λ`).  A compact preconnected subset of the circle invariant under a nontrivial root of
  unity must be the whole circle (`eqSphereOfPreconnectedOfPowEqOne`), contradicting the petal
  condition.

* `‖λ‖ = 1` and `λ^q ≠ 1` for all `q ≥ 1`: this is the *path* form of the irrationally
  indifferent case, `Work.LandLeaves.Snail.no_snail_of_not_rootOfUnity_path`
  (`Submission/Work/LandLeaves/Snail/snailPathNotRootOfUnity.lean`), proved from the log-lift,
  the drift, the invariant region cut off by the snail path and the Cauchy /
  dominated-convergence endgame.  Note that the *orbit* form of the same case
  (`no_converging_orbit_of_multiplier_not_root_of_unity`) is the Snail principle itself and is
  **not** available: see `convergingOrbitLinearizable.lean` and
  `Snail/NOTES_no_snail_of_multiplier_not_root_of_unity.md`.  Only the path form is used here.
-/
import Mathlib
import Submission.Work.LandLeaves.SnailLemmaMilnor
import Submission.Work.LandLeaves.expansion_of_one_lt_norm_deriv
import Submission.Work.LandLeaves.chart_descent_bound
import Submission.Work.LandLeaves.descentPath_re_tendsto_atBot
import Submission.Work.LandLeaves.directionLimitSet_invariant
import Submission.Work.LandLeaves.existsLeadingQuantitative
import Submission.Work.LandLeaves.Snail.snailPathNotRootOfUnity
import Submission.Work.LandLeaves.snailDescentDefs
import Submission.Work.LandLeaves.directionLimitSet_compact
import Submission.Work.LandLeaves.directionLimitSet_subset_of_eventually
import Submission.Work.LandLeaves.eqSphereOfPreconnectedOfPowEqOne
import Submission.Work.LandLeaves.twist_tendsto_zero
import Submission.Work.LandLeaves.exists_unit_pow_pos

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology

namespace Work.LandLeaves

/-! ## Elementary preparations -/

/-- A complex number with `z ^ q = 1`, `q > 0`, has modulus one. -/
theorem norm_eq_one_of_pow_eq_one' {z : ℂ} {q : ℕ} (hq : 0 < q) (hz : z ^ q = 1) : ‖z‖ = 1 := by
  have h : ‖z‖ ^ q = 1 := by rw [← norm_pow, hz, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hq.ne').mp h

/-- The derivative of a germ shifted to the origin. -/
theorem deriv_shift_germ' {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀) :
    deriv (fun w : ℂ => g (w + z₀) - z₀) 0 = deriv g z₀ := by
  have h1 : HasDerivAt (fun w : ℂ => w + z₀) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).add_const z₀
  have h2 : HasDerivAt g (deriv g z₀) ((fun w : ℂ => w + z₀) 0) := by
    simpa using hg.differentiableAt.hasDerivAt
  have h3 : HasDerivAt (fun w : ℂ => g (w + z₀)) (deriv g z₀ * 1) 0 := h2.comp 0 h1
  have h4 : HasDerivAt (fun w : ℂ => g (w + z₀) - z₀) (deriv g z₀ * 1) 0 := h3.sub_const z₀
  rw [h4.deriv]; ring

/-- The descent chart `Z w = 1 / (((r:ℂ)-1) * c * w^(r-1))` (`c ≠ 0`, `r ≥ 2`, `w ≠ 0`) has
negative real part exactly where `(c * w^(r-1)).re` is negative. -/
theorem chart_re_neg_iff {c : ℂ} {r : ℕ} (hr : 2 ≤ r) (hc : c ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    (1 / (((r : ℂ) - 1) * c * w ^ (r - 1))).re < 0 ↔ (c * w ^ (r - 1)).re < 0 := by
  set A : ℂ := ((r : ℂ) - 1) * c * w ^ (r - 1) with hA
  have hrR : (0 : ℝ) < (r : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hAeq : A = (((r : ℝ) - 1 : ℝ) : ℂ) * (c * w ^ (r - 1)) := by
    rw [hA]; push_cast; ring
  have hAsign : A.re = ((r : ℝ) - 1) * (c * w ^ (r - 1)).re := by
    rw [hAeq, Complex.re_ofReal_mul]
  have hAne : A ≠ 0 := by
    rw [hAeq]
    refine mul_ne_zero ?_ (mul_ne_zero hc (pow_ne_zero _ hw))
    rw [Complex.ofReal_ne_zero]; linarith
  have hsq : 0 < Complex.normSq A := Complex.normSq_pos.mpr hAne
  have key : ∀ X : ℝ, ((r : ℝ) - 1) * X / Complex.normSq A < 0 ↔ X < 0 := by
    intro X
    rw [div_neg_iff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · linarith
      · by_contra hX
        have hX0 : 0 ≤ X := not_lt.mp hX
        have h2' : 0 ≤ ((r : ℝ) - 1) * X := mul_nonneg (le_of_lt hrR) hX0
        linarith
    · intro hX
      exact Or.inr ⟨mul_neg_of_pos_of_neg hrR hX, hsq⟩
  rw [one_div, Complex.inv_re, hAsign]
  exact key _

/-- The weak (non-strict) form of `chart_re_neg_iff`. -/
theorem chart_re_nonpos_iff {c : ℂ} {r : ℕ} (hr : 2 ≤ r) (hc : c ≠ 0) {w : ℂ} (hw : w ≠ 0) :
    (1 / (((r : ℂ) - 1) * c * w ^ (r - 1))).re ≤ 0 ↔ (c * w ^ (r - 1)).re ≤ 0 := by
  have h1 : (0 : ℝ) < (1 / (((r : ℂ) - 1) * c * w ^ (r - 1))).re
      ↔ 0 < (c * w ^ (r - 1)).re := by
    have hneg := chart_re_neg_iff (c := -c) hr (neg_ne_zero.mpr hc) hw
    rw [show (((r : ℂ) - 1) * (-c) * w ^ (r - 1))
        = -(((r : ℂ) - 1) * c * w ^ (r - 1)) by ring] at hneg
    rw [div_neg] at hneg
    rw [Complex.neg_re] at hneg
    rw [show ((-c) * w ^ (r - 1)) = -(c * w ^ (r - 1)) by ring, Complex.neg_re] at hneg
    rw [neg_lt_zero] at hneg
    simpa using hneg
  constructor
  · intro h
    by_contra hcon
    exact absurd (h1.mpr (lt_of_not_ge hcon)) (not_lt.mpr h)
  · intro h
    by_contra hcon
    exact absurd (h1.mp (lt_of_not_ge hcon)) (not_lt.mpr h)

/-- `Re (c * w^(r-1))` in terms of the direction `w / ‖w‖`. -/
theorem re_mul_pow_direction {c : ℂ} {r : ℕ} {w : ℂ} (hw : w ≠ 0) :
    (c * (w / ((‖w‖ : ℝ) : ℂ)) ^ (r - 1)).re = (c * w ^ (r - 1)).re / ‖w‖ ^ (r - 1) := by
  have hdiv : w / ((‖w‖ : ℝ) : ℂ) = (((‖w‖ : ℝ))⁻¹ : ℂ) * w := by
    rw [div_eq_inv_mul, ← Complex.ofReal_inv]
  have hpow : ((((‖w‖ : ℝ))⁻¹ : ℂ) * w) ^ (r - 1)
      = ((((‖w‖ : ℝ) ^ (r - 1))⁻¹ : ℝ) : ℂ) * w ^ (r - 1) := by
    rw [mul_pow, ← Complex.ofReal_inv, ← Complex.ofReal_pow, inv_pow]
  rw [hdiv, hpow, show c * (((((‖w‖ : ℝ) ^ (r - 1))⁻¹ : ℝ) : ℂ) * w ^ (r - 1))
        = ((((‖w‖ : ℝ) ^ (r - 1))⁻¹ : ℝ) : ℂ) * (c * w ^ (r - 1)) by ring,
    Complex.re_ofReal_mul, div_eq_mul_inv, mul_comm]

/-! ## The repelling case -/

/-- **Repelling fixed points carry no snail.**  If `‖deriv g z₀‖ > 1` then `g` is locally
expanding at `z₀`, so a forward orbit which converges to `z₀` cannot exist. -/
theorem no_snail_of_one_lt_norm_deriv {g : ℂ → ℂ} {z₀ : ℂ} {p : ℝ → ℂ}
    (hg : AnalyticAt ℂ g z₀) (hfix : g z₀ = z₀) (hlarge : 1 < ‖deriv g z₀‖)
    (hne : ∀ t ∈ Set.Ici (0 : ℝ), p t ≠ z₀)
    (hshift : ∀ t ∈ Set.Ici (0 : ℝ), g (p t) = p (t + 1))
    (hlim : Tendsto p atTop (𝓝 z₀)) : False := by
  obtain ⟨ε, hε, c, hc, hbound⟩ := expansion_of_one_lt_norm_deriv hg hlarge
  have hseq : Tendsto (fun n : ℕ => p (n : ℝ)) atTop (𝓝 z₀) :=
    hlim.comp tendsto_natCast_atTop_atTop
  rw [Metric.tendsto_nhds] at hseq
  have hev : ∀ᶠ n : ℕ in atTop, ‖p (n : ℝ) - z₀‖ < ε := by
    filter_upwards [hseq ε hε] with n hn
    simpa [dist_eq_norm] using hn
  rw [Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  have hstep : ∀ n : ℕ, N ≤ n → c * ‖p (n : ℝ) - z₀‖ ≤ ‖p ((n + 1 : ℕ) : ℝ) - z₀‖ := by
    intro n hn
    have hb := hbound (p (n : ℝ)) (hN n hn)
    rw [hfix] at hb
    have harg : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [harg, ← hshift (n : ℝ) (by simp)]
    exact hb
  have hgrowth : ∀ k : ℕ, c ^ k * ‖p (N : ℝ) - z₀‖ ≤ ‖p ((N + k : ℕ) : ℝ) - z₀‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have h2 := hstep (N + k) (Nat.le_add_right N k)
        calc c ^ (k + 1) * ‖p (N : ℝ) - z₀‖ = c * (c ^ k * ‖p (N : ℝ) - z₀‖) := by ring
          _ ≤ c * ‖p ((N + k : ℕ) : ℝ) - z₀‖ :=
                mul_le_mul_of_nonneg_left ih (le_of_lt (lt_trans zero_lt_one hc))
          _ ≤ ‖p ((N + k + 1 : ℕ) : ℝ) - z₀‖ := by simpa [Nat.add_assoc] using h2
  have hpos : 0 < ‖p (N : ℝ) - z₀‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hne (N : ℝ) (by simp)
  have hsmall : ∀ᶠ m : ℕ in atTop, ‖p (m : ℝ) - z₀‖ < ‖p (N : ℝ) - z₀‖ := by
    filter_upwards [hseq ‖p (N : ℝ) - z₀‖ hpos] with m hm
    simpa [dist_eq_norm] using hm
  rw [Filter.eventually_atTop] at hsmall
  obtain ⟨M, hM⟩ := hsmall
  set m := max M (N + 2) with hm
  have hmM : M ≤ m := le_max_left _ _
  have hmN : N + 2 ≤ m := le_max_right _ _
  have hle := hgrowth (m - N)
  have hmn : N + (m - N) = m := Nat.add_sub_of_le (le_trans (Nat.le_add_right N 2) hmN)
  rw [hmn] at hle
  have hc2 : 1 < c ^ (m - N) := by
    calc (1 : ℝ) < c := hc
      _ = c ^ 1 := (pow_one c).symm
      _ ≤ c ^ (m - N) := pow_le_pow_right₀ (le_of_lt hc) (by omega)
  have : ‖p (N : ℝ) - z₀‖ < c ^ (m - N) * ‖p (N : ℝ) - z₀‖ := by nlinarith
  have hlt := hM m hmM
  linarith [hle, this, hlt]

/-! ## The root-of-unity case (the analytic heart) -/

/-- **A primitive root of unity multiplier admits no snail.**  If `(deriv g z₀)^q = 1` with
`q > 1` and `deriv g z₀ ≠ 1`, then the descent chart forces the limit directions of the path into
the closed petal set, while the invariance under `deriv g z₀` forces them to be the whole circle.

Sketch.  Normalise `z₀ = 0` (`G w = g (w + z₀) - z₀`, `Q t = p t - z₀`), put `H = G^[q]`: then
`H` is tangent to the identity at `0` and `Q (t + q) = H (Q t)`.

* If `H` is the identity near `0`, then `Q (t + q) = Q t` for large `t`, so `Q t = lim_n Q (t+nq) = 0`,
  contradicting `Q t ≠ 0`.
* Otherwise `exists_leading_quantitative` writes `H w = w + c w^r + O(w^(r+1))` with `r ≥ 2`,
  `c ≠ 0`; applying `descentPath_re_tendsto_atBot` to `s ↦ Q (q s)` gives `Re (Z (Q t)) → -∞`, and
  by `chart_re_neg_iff` the directions of `Q` are eventually in the closed petal set `U`.
* `directionLimitSet_compact` makes the limit set `L` a compact preconnected subset of the circle;
  `L ⊆ U ≠ circle`; `directionLimitSet_invariant` (via `twist_tendsto_zero`) gives `λ L ⊆ L`; and
  `eqSphereOfPreconnectedOfPowEqOne` forces `L` to be the whole circle: contradiction. -/
theorem no_snail_of_rootOfUnity_multiplier {g : ℂ → ℂ} {z₀ : ℂ} {p : ℝ → ℂ} {q : ℕ}
    (hg : AnalyticAt ℂ g z₀) (hfix : g z₀ = z₀) (hq : 1 < q)
    (hroot : (deriv g z₀) ^ q = 1) (hne' : deriv g z₀ ≠ 1)
    (hp : ContinuousOn p (Set.Ici 0)) (hne : ∀ t ∈ Set.Ici (0 : ℝ), p t ≠ z₀)
    (hshift : ∀ t ∈ Set.Ici (0 : ℝ), g (p t) = p (t + 1))
    (hlim : Tendsto p atTop (𝓝 z₀)) : False := by
  have hlam1 : ‖deriv g z₀‖ = 1 := norm_eq_one_of_pow_eq_one' (by omega) hroot
  have hqpos : (0 : ℝ) < (q : ℝ) := by
    have h0 : (0 : ℕ) < q := by omega
    exact_mod_cast h0
  -- shift the fixed point to the origin
  set G : ℂ → ℂ := fun w => g (w + z₀) - z₀ with hGdef
  set Q : ℝ → ℂ := fun t => p t - z₀ with hQdef
  have hGan : AnalyticAt ℂ G 0 := by
    have h1 : AnalyticAt ℂ (fun w : ℂ => w + z₀) 0 := analyticAt_id.add analyticAt_const
    have h2 : AnalyticAt ℂ g ((fun w : ℂ => w + z₀) 0) := by simpa using hg
    have h3 : AnalyticAt ℂ (fun w : ℂ => g (w + z₀)) 0 := AnalyticAt.comp h2 h1
    have h4 : AnalyticAt ℂ (fun w : ℂ => g (w + z₀) - z₀) 0 := h3.sub analyticAt_const
    simpa [hGdef] using h4
  have hG0 : G 0 = 0 := by simp [hGdef, hfix]
  have hGderiv : deriv G 0 = deriv g z₀ := by rw [hGdef]; exact deriv_shift_germ' hg
  have hQc : ContinuousOn Q (Set.Ici 0) := by
    rw [hQdef]; exact hp.sub continuousOn_const
  have hQne : ∀ t ∈ Set.Ici (0 : ℝ), Q t ≠ 0 := by
    intro t ht h0
    simp only [hQdef, sub_eq_zero] at h0
    exact hne t ht h0
  have hQshift : ∀ t ∈ Set.Ici (0 : ℝ), Q (t + 1) = G (Q t) := by
    intro t ht
    simp only [hQdef, hGdef]
    have h1 : p t - z₀ + z₀ = p t := by ring
    rw [h1, hshift t ht]
  have hQlim : Tendsto Q atTop (𝓝 0) := by
    rw [hQdef]; simpa using hlim.sub_const z₀
  -- the `q`-th iterate
  have hGn0 : ∀ n : ℕ, (G^[n]) 0 = 0 := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply']; simp [ih, hG0]
  have hHan_all : ∀ n : ℕ, AnalyticAt ℂ (G^[n]) 0 := by
    intro n
    induction n with
    | zero => simpa using analyticAt_id
    | succ k ih =>
        have hsplit : G^[k + 1] = G ∘ G^[k] := by
          funext x; exact Function.iterate_succ_apply' G k x
        rw [hsplit]
        exact (by simpa [hGn0 k] using hGan : AnalyticAt ℂ G ((G^[k]) 0)).comp ih
  have hHan : AnalyticAt ℂ (G^[q]) 0 := hHan_all q
  have hH0 : (G^[q]) 0 = 0 := hGn0 q
  have hHderiv : deriv (G^[q]) 0 = 1 := by
    have hh := (HasDerivAt.iterate (0 : ℂ) (hGan.differentiableAt.hasDerivAt) hG0 q).deriv
    rw [hGderiv, hroot] at hh
    exact hh
  have hQshiftq : ∀ t ∈ Set.Ici (0 : ℝ), Q (t + (q : ℝ)) = (G^[q]) (Q t) := by
    intro t ht
    have hgen : ∀ n : ℕ, Q (t + (n : ℝ)) = (G^[n]) (Q t) := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
          have hk : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
          rw [hk]
          have h1 : t + ((k : ℝ) + 1) = (t + (k : ℝ)) + 1 := by ring
          rw [h1, hQshift (t + (k : ℝ)) (Set.mem_Ici.mpr (by
            have h2 := Set.mem_Ici.mp ht; linarith))]
          have hsplit : G^[k + 1] = G ∘ G^[k] := by
            funext x; exact Function.iterate_succ_apply' G k x
          rw [hsplit, Function.comp_apply, ← ih]
    exact hgen q
  by_cases hHid : (G^[q]) =ᶠ[𝓝 0] fun w => w
  · -- `G^[q]` is the identity near `0`: the path is eventually periodic, hence constantly `0`
    obtain ⟨ε, hε, hε'⟩ := Metric.eventually_nhds_iff.mp hHid
    have hev : ∀ᶠ t : ℝ in atTop, dist (Q t) 0 < ε := by
      filter_upwards [hQlim (Metric.ball_mem_nhds (0 : ℂ) hε)] with t ht
      exact ht
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hev
    obtain ⟨T₀, hT₀_ge, hT₀_nn⟩ : ∃ T₀ : ℝ, T ≤ T₀ ∧ (0 : ℝ) ≤ T₀ :=
      ⟨max T 0, le_max_left _ _, le_max_right _ _⟩
    have hper : ∀ n : ℕ, Q (T₀ + (n : ℝ) * (q : ℝ)) = Q T₀ := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
          have hk : (((k + 1 : ℕ)) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
          rw [hk]
          have h1 : T₀ + ((k : ℝ) + 1) * (q : ℝ) = (T₀ + (k : ℝ) * (q : ℝ)) + q := by ring
          rw [h1, hQshiftq (T₀ + (k : ℝ) * (q:ℝ)) (Set.mem_Ici.mpr (by positivity))]
          rw [hε' (by
            have h2 : T ≤ T₀ + (k:ℝ) * (q:ℝ) := by
              have h3 : (0:ℝ) ≤ (k:ℝ) * (q:ℝ) := by positivity
              linarith
            exact hT _ h2)]
          exact ih
    have hlim2 : Tendsto (fun n : ℕ => Q (T₀ + (n : ℝ) * (q:ℝ))) atTop (𝓝 0) := by
      refine hQlim.comp ?_
      rw [Filter.tendsto_atTop]
      intro b
      refine Filter.eventually_atTop.mpr ⟨max (Nat.ceil ((b - T₀) / (q:ℝ))) 0, fun n hn => ?_⟩
      have hn' : ((b - T₀) / (q:ℝ)) ≤ (n : ℝ) := by
        have h1 : ((b - T₀) / (q:ℝ)) ≤ (Nat.ceil ((b - T₀) / (q:ℝ)) : ℝ) := Nat.le_ceil _
        have h2 : (Nat.ceil ((b - T₀) / (q:ℝ)) : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast le_trans (le_max_left _ _) hn
        linarith
      have h3 : (b - T₀) ≤ (n : ℝ) * (q:ℝ) := by
        have h4 := mul_le_mul_of_nonneg_right hn' (le_of_lt hqpos)
        rwa [div_mul_cancel₀] at h4
        exact ne_of_gt hqpos
      linarith
    have hzero : Q T₀ = 0 := by
      have hconst : (fun n : ℕ => Q (T₀ + (n : ℝ) * (q:ℝ))) = fun _ => Q T₀ :=
        funext (fun n => by rw [hper n])
      rw [hconst] at hlim2
      exact (tendsto_nhds_unique hlim2 tendsto_const_nhds).symm
    exact hQne T₀ (Set.mem_Ici.mpr hT₀_nn) hzero
  · -- the descent chart
    obtain ⟨r, c, hr, hc, ρ, hρ, A, hA, happrox⟩ :=
      existsLeadingQuantitative hHan hH0 hHderiv hHid
    -- reparametrise the path: `Q' s = Q (q s)`
    set Q' : ℝ → ℂ := fun s => Q ((q : ℝ) * s) with hQ'def
    have hQ'c : ContinuousOn Q' (Set.Ici 0) := by
      rw [hQ'def]
      refine hQc.comp (continuous_const.mul continuous_id).continuousOn ?_
      intro s hs
      exact Set.mem_Ici.mpr (by have h := Set.mem_Ici.mp hs; positivity)
    have hQ'ne : ∀ s ∈ Set.Ici (0 : ℝ), Q' s ≠ 0 := by
      intro s hs
      rw [hQ'def]
      exact hQne _ (Set.mem_Ici.mpr (by have h := Set.mem_Ici.mp hs; positivity))
    have hQ'shift : ∀ s ∈ Set.Ici (0 : ℝ), Q' (s + 1) = (G^[q]) (Q' s) := by
      intro s hs
      have h1 : (q : ℝ) * (s + 1) = (q : ℝ) * s + (q : ℝ) := by ring
      simp only [hQ'def]
      rw [h1, hQshiftq _ (Set.mem_Ici.mpr (by have h := Set.mem_Ici.mp hs; positivity))]
    have hQ'lim : Tendsto Q' atTop (𝓝 0) := by
      rw [hQ'def]
      refine hQlim.comp ?_
      rw [Filter.tendsto_atTop]
      intro b
      refine Filter.eventually_atTop.mpr ⟨max (b / (q:ℝ)) 0, fun s hs => ?_⟩
      have hs' : b / (q:ℝ) ≤ s := le_trans (le_max_left _ _) hs
      have h1 : b ≤ s * (q:ℝ) := by
        have h2 := mul_le_mul_of_nonneg_right hs' (le_of_lt hqpos)
        rwa [div_mul_cancel₀] at h2
        exact ne_of_gt hqpos
      calc b ≤ s * (q:ℝ) := h1
        _ = (q:ℝ) * s := by ring
    have hZ := descentPath_re_tendsto_atBot hr hc ⟨ρ, hρ, A, hA, happrox⟩ hQ'c hQ'ne
      hQ'shift hQ'lim
    -- the directions of `Q'` are eventually in the closed petal set
    have hevQ' : ∀ᶠ s : ℝ in atTop, (c * (Q' s) ^ (r - 1)).re ≤ 0 := by
      have h1 : ∀ᶠ s : ℝ in atTop,
          (1 / (((r : ℂ) - 1) * c * (Q' s) ^ (r - 1))).re ≤ 0 :=
        (Filter.tendsto_atBot.mp hZ) 0
      filter_upwards [h1, Filter.eventually_ge_atTop (0 : ℝ)] with s hs hs0
      exact (chart_re_nonpos_iff hr hc (hQ'ne s (Set.mem_Ici.mpr hs0))).mp hs
    have hevQ : ∀ᶠ t : ℝ in atTop, (c * (Q t) ^ (r - 1)).re ≤ 0 := by
      obtain ⟨S, hS⟩ := Filter.eventually_atTop.mp hevQ'
      refine Filter.eventually_atTop.mpr ⟨(q : ℝ) * S, fun t ht => ?_⟩
      have ht' : S * (q:ℝ) ≤ t := by rw [mul_comm]; exact ht
      have hs : S ≤ t / (q : ℝ) := by
        rw [le_div_iff₀ hqpos]
        exact ht'
      have h1 := hS (t / (q:ℝ)) hs
      have h2 : (q : ℝ) * (t / (q:ℝ)) = t := by
        rw [mul_comm]; exact div_mul_cancel₀ t (ne_of_gt hqpos)
      have h3 : Q' (t / (q:ℝ)) = Q t := by
        show Q ((q:ℝ) * (t / (q:ℝ))) = Q t
        rw [h2]
      rwa [h3] at h1
    -- the limit set of the directions
    set L : Set ℂ := directionLimitSet Q with hLdef
    obtain ⟨hLcpt, hLne, hLpre, hLsph⟩ := directionLimitSet_compact hQc hQne
    have hLU : L ⊆ {d : ℂ | (c * d ^ (r - 1)).re ≤ 0} := by
      obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hevQ
      obtain ⟨T₀, hT₀_nn, hT₀_ge⟩ : ∃ T₀ : ℝ, (0:ℝ) ≤ T₀ ∧ T ≤ T₀ :=
        ⟨max T 0, le_max_right _ _, le_max_left _ _⟩
      refine directionLimitSet_subset_of_eventually (T := T₀)
        (isClosed_le (by fun_prop) continuous_const) ?_
      intro t ht
      change (c * (Q t / ((‖Q t‖ : ℝ) : ℂ)) ^ (r - 1)).re ≤ 0
      have h1 : (c * (Q t) ^ (r - 1)).re ≤ 0 := hT t (le_trans hT₀_ge ht)
      rw [re_mul_pow_direction (hQne t (Set.mem_Ici.mpr (le_trans hT₀_nn ht)))]
      have hb : (0:ℝ) < ‖Q t‖ ^ (r - 1) :=
        pow_pos (norm_pos_iff.mpr (hQne t (Set.mem_Ici.mpr (le_trans hT₀_nn ht)))) _
      exact div_nonpos_of_nonpos_of_nonneg h1 (le_of_lt hb)
    have hLne_sph : L ≠ Metric.sphere (0 : ℂ) 1 := by
      intro hEq
      obtain ⟨d, hd1, hd2⟩ := exists_unit_pow_pos (show 0 < r - 1 by omega) hc
      have hdmem : d ∈ Metric.sphere (0 : ℂ) 1 := by
        rw [Metric.mem_sphere, dist_eq_norm, sub_zero]; exact hd1
      have hh : (c * d ^ (r - 1)).re ≤ 0 := hLU (hEq.symm ▸ hdmem)
      exact absurd hd2 (not_lt.mpr hh)
    -- invariance of the limit set under multiplication by `deriv g z₀`
    have hGlittle : (fun z : ℂ => G z - deriv g z₀ * z) =o[𝓝 0] (fun z : ℂ => z) := by
      have h := hGan.differentiableAt.hasDerivAt.isLittleO
      rw [hG0, hGderiv] at h
      simpa [mul_comm] using h
    have htwist : Tendsto (fun t : ℝ => Q (t + 1) / ((‖Q (t + 1)‖ : ℝ) : ℂ)
        - deriv g z₀ * (Q t / ((‖Q t‖ : ℝ) : ℂ))) atTop (𝓝 0) := by
      have h := twist_tendsto_zero hlam1 hGlittle
      have hQt : Tendsto Q atTop (𝓝[≠] (0 : ℂ)) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨hQlim, Filter.eventually_atTop.mpr ⟨0, fun t ht =>
          hQne t (Set.mem_Ici.mpr ht)⟩⟩
      have h2 : Tendsto (fun t : ℝ => G (Q t) / ((‖G (Q t)‖ : ℝ) : ℂ)
          - deriv g z₀ * (Q t / ((‖Q t‖ : ℝ) : ℂ))) atTop (𝓝 0) := by
        have h3 := h.comp hQt
        simpa [Function.comp_def] using h3
      refine h2.congr' ?_
      filter_upwards [Filter.eventually_atTop.mpr ⟨0, fun t ht => ht⟩] with t ht
      rw [← hQshift t (Set.mem_Ici.mpr ht)]
    have hinv : ∀ d ∈ L, deriv g z₀ * d ∈ L :=
      directionLimitSet_invariant hQc hQne htwist
    exact hLne_sph (eqSphereOfPreconnectedOfPowEqOne hLcpt hLpre hLne hLsph hlam1
      (by omega) hroot hne' hinv)

/-! ## The irrationally indifferent case -/

/-- **A multiplier which is not a root of unity admits no snail** (the irrationally
indifferent case of the Snail lemma, in *path* form).

This is `Work.LandLeaves.Snail.no_snail_of_not_rootOfUnity_path`, transported from the germ form
at `0` (Milnor's Lemma 13.2 as used by Hubbard--Schleicher); see
`Snail/snailPathNotRootOfUnity.lean` and the module docstring there for the proof.  It replaces an
earlier proof of this lemma which passed through the *orbit* form
`no_converging_orbit_of_multiplier_not_root_of_unity` — a statement equivalent to the Snail
principle itself, hence not available. -/
theorem no_snail_of_multiplier_not_rootOfUnity {g : ℂ → ℂ} {z₀ : ℂ} {p : ℝ → ℂ}
    (hg : AnalyticAt ℂ g z₀) (hfix : g z₀ = z₀) (h1 : ‖deriv g z₀‖ = 1)
    (hnr : ∀ q : ℕ, 0 < q → (deriv g z₀) ^ q ≠ 1)
    (hp : ContinuousOn p (Set.Ici 0)) (hne : ∀ t ∈ Set.Ici (0 : ℝ), p t ≠ z₀)
    (hshift : ∀ t ∈ Set.Ici (0 : ℝ), g (p t) = p (t + 1))
    (hlim : Tendsto p atTop (𝓝 z₀)) : False := by
  exact Snail.no_snail_of_not_rootOfUnity_path hg hfix h1 hnr hp hne hshift hlim

/-! ## The neutral case and the target -/

/-- **Neutral non-parabolic case of the Snail lemma** (the analytic core): a germ at `z₀` with
`‖deriv g z₀‖ = 1` and `deriv g z₀ ≠ 1` admits no forward path in `U ∖ {z₀}` advancing by the
germ and converging to `z₀`. -/
theorem no_snail_of_norm_one_ne_one {g : ℂ → ℂ} {z₀ : ℂ} {p : ℝ → ℂ}
    (hg : AnalyticAt ℂ g z₀) (hfix : g z₀ = z₀) (h1 : ‖deriv g z₀‖ = 1)
    (hne' : deriv g z₀ ≠ 1)
    (hp : ContinuousOn p (Set.Ici 0))
    (hne : ∀ t ∈ Set.Ici (0 : ℝ), p t ≠ z₀)
    (hshift : ∀ t ∈ Set.Ici (0 : ℝ), g (p t) = p (t + 1))
    (hlim : Tendsto p atTop (𝓝 z₀)) : False := by
  by_cases hroot : ∃ q : ℕ, 0 < q ∧ (deriv g z₀) ^ q = 1
  · obtain ⟨q, hq, hq1⟩ := hroot
    have hq2 : 1 < q := by
      by_contra hcon
      have h1 : q = 1 := by omega
      rw [h1, pow_one] at hq1
      exact hne' hq1
    exact (no_snail_of_rootOfUnity_multiplier hg hfix hq2 hq1 hne' hp hne hshift hlim).elim
  · exact (no_snail_of_multiplier_not_rootOfUnity hg hfix h1
      (fun q hq hq1 => hroot ⟨q, hq, hq1⟩) hp hne hshift hlim).elim

/-- **The Snail lemma in Milnor's form.** -/
theorem snailLemmaMilnor : Work.LandLeaves.SnailLemmaMilnor := by
  intro g z₀ U p hg hfix _hU _hz₀ hp hmem hshift hlim
  have hne : ∀ t ∈ Set.Ici (0 : ℝ), p t ≠ z₀ := fun t ht => (hmem t ht).2
  rcases lt_trichotomy ‖deriv g z₀‖ 1 with hlt | heq | hgt
  · exact Or.inl hlt
  · by_cases hone : deriv g z₀ = 1
    · exact Or.inr hone
    · exact (no_snail_of_norm_one_ne_one hg hfix heq hone hp hne hshift hlim).elim
  · exact (no_snail_of_one_lt_norm_deriv hg hfix hgt hne hshift hlim).elim

end Work.LandLeaves
