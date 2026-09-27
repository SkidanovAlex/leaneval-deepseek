import Mathlib
import Submission.Work.Mostow.cuspDefs
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.boundedOrbitFixed
import Submission.Work.Mostow.kleinBD
import Submission.Work.Mostow.bdBallContinuousAt

/-!
# A fixed-point-free isometry of `ℍⁿ` fixes a point of the boundary sphere

`Work.Mostow.cruxFixedPoint`: for `n ≥ 2` and `g : PO n 1` without fixed point in `ℍⁿ` (and with
displacement bounded below by a positive constant — a hypothesis which is in fact not needed),
the boundary action `bd g` has a fixed point on `Sph n`.

The argument is elementary and geometric; no topological fixed-point theorem is used.  Write
`κ u = (tpart u)⁻¹ • u = u / tpart u` for the **Klein coordinate** of the chart point `u`: the
intersection of the ray through the hyperboloid lift `hlift u = (u, tpart u)` with the time-`1`
slice.  It lies in the open Euclidean unit ball, and the two structural facts we use are

* `κ` intertwines the interior action with the boundary action, `κ (g • u) = bd g (κ u)`
  (`Work.Mostow.kleinBD`) — this is the sheet lemma
  `hlift (g • u) = tsign (rep g) • (mat (rep g) *ᵥ hlift u)` read in the time-`1` slice;
* `bd g` is continuous at every point of the closed unit ball (`Work.Mostow.bdBallContinuousAt`).

Now put `u k = g ^ k • 0`, `z k = κ (u k) = κ ((g ^ k) • 0)`.  Since `g` has no fixed point the
orbit of `0` is unbounded (`Work.Mostow.boundedOrbitFixed`), so `a k = hdist 0 (u k)` tends to
infinity along a subsequence and, the closed ball being compact, the normalised points `z k` have
a convergent subsequence `z (M j) → z*`.  The cosh-kernel identity `cc u v = cosh (hdist u v)`
gives, for every `k`,

`⟪z (k+1), z k⟫ = 1 - cosh (a 1) / (cosh (a k) cosh (a (k+1)))`,

which tends to `1` because `cosh (a (M j)) → ∞`; combined with `z (k+1) = bd g (z k)` and the
continuity of `bd g` at `z*` this gives `⟪z*, bd g z*⟫ = 1`.  Finally `‖z*‖ ≤ 1` and
`‖bd g z*‖ ≤ 1` (the latter as the limit of the norms of the points `z (M j + 1)` of the closed
ball), so Cauchy–Schwarz

`1 = ⟪z*, bd g z*⟫ ≤ ‖z*‖ ‖bd g z*‖ ≤ 1`

is an equality throughout: `‖z*‖ = 1`, i.e. `z* ∈ Sph n`, and equality in Cauchy–Schwarz forces
`bd g z* = z*`.
-/

set_option maxHeartbeats 4000000

namespace Work.Mostow

open LeanEval.Geometry.MostowRigidity Submission.Mostow MeasureTheory
open Filter
open scoped Topology

noncomputable section

variable {n : ℕ}

/-- The **Klein (Beltrami) coordinate** of a chart point: `u ↦ u / tpart u`.  Equivalently, it is
the hyperboloid lift `hlift u = (u, tpart u)` normalised to time coordinate `1`; it lies in the
open Euclidean unit ball. -/
def klein (u : E n) : E n := (tpart u)⁻¹ • u

lemma norm_lt_tpart (u : E n) : ‖u‖ < tpart u := by
  have h : Real.sqrt (‖u‖ ^ 2) < Real.sqrt (1 + ‖u‖ ^ 2) :=
    Real.sqrt_lt_sqrt (sq_nonneg ‖u‖) (by linarith)
  rwa [Real.sqrt_sq (norm_nonneg u), ← tpart] at h

/-- The Klein coordinate of a chart point lies in the open unit ball. -/
lemma norm_klein_lt_one (u : E n) : ‖klein u‖ < 1 := by
  have htp := tpart_pos u
  have h1 : ‖klein u‖ = ‖u‖ / tpart u := by
    rw [klein, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos htp, div_eq_inv_mul]
  rw [h1, div_lt_one htp]
  exact norm_lt_tpart u

/-- Klein coordinates pair through the cosh-kernel:
`⟪u/tpart u, v/tpart v⟫ = 1 - cosh (hdist u v) / (cosh (hdist 0 u) cosh (hdist 0 v))`. -/
lemma kleinInner (u v : E n) :
    inner ℝ (klein u) (klein v)
      = 1 - Real.cosh (hdist u v) /
          (Real.cosh (hdist 0 u) * Real.cosh (hdist 0 v)) := by
  have hu : tpart u ≠ 0 := ne_of_gt (tpart_pos u)
  have hv : tpart v ≠ 0 := ne_of_gt (tpart_pos v)
  rw [klein, klein, real_inner_smul_left, real_inner_smul_right, cosh_hdist, cosh_hdist_zero,
    cosh_hdist_zero]
  field_simp
  ring

/-- `cosh` tends to infinity at `+∞`. -/
lemma tendsto_cosh_atTop : Tendsto (Real.cosh : ℝ → ℝ) atTop atTop := by
  have hexp : Tendsto (fun x : ℝ => Real.exp x / 2) atTop atTop := by
    have h : Tendsto (fun x : ℝ => (1 / 2 : ℝ) * Real.exp x) atTop atTop :=
      Filter.Tendsto.const_mul_atTop (by norm_num) Real.tendsto_exp_atTop
    simpa [div_eq_mul_inv, mul_comm] using h
  refine Filter.tendsto_atTop_mono (f := fun x : ℝ => Real.exp x / 2) (fun x => ?_) hexp
  rw [Real.cosh_eq]
  nlinarith [Real.exp_pos (-x)]

/-- The orbit of any point under a fixed-point-free isometry of `ℍⁿ` is unbounded: the
contrapositive of `Work.Mostow.boundedOrbitFixed`. -/
lemma orbitEscape (n : ℕ) (hn : 1 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (hne : ∀ u : E n, g • u ≠ u) (u₀ : E n) :
    ∀ R : ℝ, ∃ m : ℕ, R < hdist u₀ ((g ^ m) • u₀) := by
  intro R
  by_contra h
  push Not at h
  obtain ⟨u, hu⟩ := boundedOrbitFixed n hn hA hI g u₀ ⟨R, h⟩
  exact hne u hu

/-- **The limit computation.**  For a fixed-point-free isometry `g` of `ℍⁿ` there is a point `zs`
of the closed unit ball with `⟪zs, bd g zs⟫ = 1` (and with `‖bd g zs‖ ≤ 1`): the limit of the
Klein coordinates of an escaping orbit. -/
lemma kleinLimit (n : ℕ) (hn : 1 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (hne : ∀ u : E n, g • u ≠ u) :
    ∃ zs : E n, ‖zs‖ ≤ 1 ∧ ‖bd g zs‖ ≤ 1 ∧ inner ℝ zs (bd g zs) = 1 := by
  have hmul : ∀ (g h : PO n 1) (u : E n), (g * h) • u = g • (h • u) := hA.2.2.2.2.1
  have hisom : ∀ (g : PO n 1) (u v : E n), hdist (g • u) (g • v) = hdist u v :=
    hI.2.2.2.2.2.2.1
  -- the orbit escapes to infinity
  have hesc : ∀ R : ℝ, ∃ m : ℕ, R < hdist (0 : E n) ((g ^ m) • (0 : E n)) :=
    orbitEscape n hn hA hI g hne 0
  choose K hK using fun j : ℕ => hesc (j : ℝ)
  set u : ℕ → E n := fun k => (g ^ k) • (0 : E n) with hudef
  set a : ℕ → ℝ := fun k => hdist (0 : E n) (u k) with hadef
  have hKa : ∀ j : ℕ, (j : ℝ) < a (K j) := fun j => by simpa [hadef, hudef] using hK j
  have hKtend : Tendsto (fun j => a (K j)) atTop atTop :=
    Filter.tendsto_atTop_mono (f := fun j : ℕ => (j : ℝ)) (fun j => le_of_lt (hKa j))
      tendsto_natCast_atTop_atTop
  -- the Klein coordinates, and a convergent subsequence
  set z : ℕ → E n := fun k => klein (u k) with hzdef
  obtain ⟨zs, hzsmem, φ, hφmono, hφlim⟩ :=
    IsCompact.tendsto_subseq (isCompact_closedBall (0 : E n) 1)
      (x := fun j => z (K j))
      (fun j => by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (norm_klein_lt_one (u (K j))).le)
  set M : ℕ → ℕ := fun j => K (φ j) with hMdef
  have hMlim : Tendsto (fun j => z (M j)) atTop (𝓝 zs) := by
    simpa [hMdef, Function.comp_def] using hφlim
  have hMtend : Tendsto (fun j => a (M j)) atTop atTop := by
    have h := hKtend.comp hφmono.tendsto_atTop
    simpa [hMdef, Function.comp_def] using h
  have hzsle : ‖zs‖ ≤ 1 := by
    rw [Metric.mem_closedBall, dist_zero_right] at hzsmem; exact hzsmem
  have hbdcont_at : ContinuousAt (bd g) zs := bdBallContinuousAt n g zs hzsle
  -- the orbit step and the Klein intertwining
  have hstep : ∀ k : ℕ, u (k+1) = g • u k := by
    intro k
    have h1 : u (k+1) = (g * g ^ k) • (0 : E n) := by
      simp only [hudef]; rw [pow_succ']
    have h2 : u k = (g ^ k) • (0 : E n) := by simp [hudef]
    rw [h1, h2]
    exact hmul g (g ^ k) (0 : E n)
  have hzstep : ∀ k : ℕ, z (k+1) = bd g (z k) := by
    intro k
    simp only [hzdef]
    rw [hstep k]
    exact (kleinBD n g (u k)).symm
  -- consecutive orbit distances
  have hdist_step : ∀ k : ℕ, hdist (u k) (u (k+1)) = a 1 := by
    intro k
    have h2 : u (k+1) = (g ^ k) • (g • (0 : E n)) := by
      have h1 : u (k+1) = (g ^ (k+1)) • (0 : E n) := by simp [hudef]
      rw [h1, pow_succ, hmul]
    have h3 : u k = (g ^ k) • (0 : E n) := by simp [hudef]
    rw [h3, h2, hisom]
    simp [hadef, hudef]
  have hinner : ∀ k : ℕ, inner ℝ (z k) (z (k+1))
      = 1 - Real.cosh (a 1) / (Real.cosh (a k) * Real.cosh (a (k+1))) := by
    intro k
    have hk := kleinInner (u k) (u (k+1))
    rw [hdist_step k] at hk
    simpa [hzdef, hadef] using hk
  -- the limits
  have hden_tend : Tendsto (fun j => Real.cosh (a (M j)) * Real.cosh (a (M j + 1)))
      atTop atTop := by
    refine Filter.tendsto_atTop_mono (f := fun j => Real.cosh (a (M j))) (fun j => ?_)
      (tendsto_cosh_atTop.comp hMtend)
    have h1 := Real.one_le_cosh (a (M j + 1))
    nlinarith [Real.cosh_pos (a (M j))]
  have hquot_tend : Tendsto (fun j => Real.cosh (a 1) /
      (Real.cosh (a (M j)) * Real.cosh (a (M j + 1)))) atTop (𝓝 0) :=
    Filter.Tendsto.const_div_atTop hden_tend _
  have hprod_tend : Tendsto (fun j => 1 - Real.cosh (a 1) /
      (Real.cosh (a (M j)) * Real.cosh (a (M j + 1)))) atTop (𝓝 1) := by
    have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h := h1.sub hquot_tend
    simpa using h
  have hinner_tend : Tendsto (fun j => inner ℝ (z (M j)) (z (M j + 1))) atTop (𝓝 1) :=
    Filter.Tendsto.congr (fun j => (hinner (M j)).symm) hprod_tend
  have hshift_tend : Tendsto (fun j => z (M j + 1)) atTop (𝓝 (bd g zs)) := by
    have h1 : Tendsto (fun j => bd g (z (M j))) atTop (𝓝 (bd g zs)) :=
      hbdcont_at.tendsto.comp hMlim
    exact Filter.Tendsto.congr (fun j => (hzstep (M j)).symm) h1
  have hinner_lim : Tendsto (fun j => inner ℝ (z (M j)) (z (M j + 1))) atTop
      (𝓝 (inner ℝ zs (bd g zs))) := by
    have hpair : Tendsto (fun j => (z (M j), z (M j + 1))) atTop (𝓝 (zs, bd g zs)) := by
      rw [nhds_prod_eq]
      exact hMlim.prodMk hshift_tend
    exact (continuous_inner.tendsto (zs, bd g zs)).comp hpair
  have hkey : inner ℝ zs (bd g zs) = 1 := tendsto_nhds_unique hinner_lim hinner_tend
  have hnormw_tend : Tendsto (fun j => ‖z (M j + 1)‖) atTop (𝓝 ‖bd g zs‖) := by
    have h := (continuous_norm.tendsto (bd g zs)).comp hshift_tend
    simpa only [Function.comp_def] using h
  have hnormw_le : ‖bd g zs‖ ≤ 1 :=
    le_of_tendsto' hnormw_tend (fun j => by
      simp only [hzdef]
      exact (norm_klein_lt_one (u (M j + 1))).le)
  exact ⟨zs, hzsle, hnormw_le, hkey⟩

/-- **The crux**: a fixed-point-free isometry of `ℍⁿ` (`n ≥ 2`) whose displacement is bounded
below by a positive constant fixes a point of the boundary sphere. -/
theorem cruxFixedPoint (n : ℕ) (hn : 2 ≤ n) (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (hne : ∀ u : E n, g • u ≠ u)
    (hpos : ∃ δ : ℝ, 0 < δ ∧ ∀ u : E n, δ ≤ hdist u (g • u)) :
    ∃ ξ : E n, ξ ∈ Sph n ∧ bd g ξ = ξ := by
  obtain ⟨zs, hzsle, hwsle, hkey⟩ := kleinLimit n (by omega) hA hI g hne
  -- Cauchy-Schwarz forces `‖zs‖ = 1` and equality
  have hcs : inner ℝ zs (bd g zs) ≤ ‖zs‖ * ‖bd g zs‖ := real_inner_le_norm zs (bd g zs)
  have h1 : 1 ≤ ‖zs‖ * ‖bd g zs‖ := by rw [← hkey]; exact hcs
  have h2 : ‖zs‖ * ‖bd g zs‖ ≤ 1 := by
    calc ‖zs‖ * ‖bd g zs‖ ≤ 1 * 1 := mul_le_mul hzsle hwsle (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hmul_eq : ‖zs‖ * ‖bd g zs‖ = 1 := le_antisymm h2 h1
  have hnormzs : ‖zs‖ = 1 := by
    have h3 : ‖zs‖ * ‖bd g zs‖ ≤ ‖zs‖ * 1 :=
      mul_le_mul_of_nonneg_left hwsle (norm_nonneg zs)
    linarith
  have hnormw : ‖bd g zs‖ = 1 := by
    have h := hmul_eq
    rw [hnormzs, one_mul] at h
    exact h
  refine ⟨zs, ?_, ?_⟩
  · rw [mem_Sph_iff]; exact hnormzs
  · have heq : inner ℝ zs (bd g zs) = ‖zs‖ * ‖bd g zs‖ := by rw [hkey, hmul_eq]
    have h2' := inner_eq_norm_mul_iff.mp heq
    rw [hnormzs, hnormw] at h2'
    simpa using h2'.symm

end

end Work.Mostow
