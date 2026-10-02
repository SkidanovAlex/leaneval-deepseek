import Mathlib
import Submission.Work.LandLeaves.Snail.exists_continuous_log_of_path
import Submission.Work.LandLeaves.Snail.exists_drift_of_snail
import Submission.Work.LandLeaves.Snail.exists_local_lift_of_germ
import Submission.Work.LandLeaves.Snail.tendsto_deriv_zero_of_tendsto_on_sphere
import Submission.Work.LandLeaves.Snail.tendsto_re_im_of_lift
import Submission.Work.LandLeaves.Snail.per_of_germ_lift
import Submission.Work.LandLeaves.Snail.existsInvariantRegionCorrected
import Submission.Work.LandLeaves.Snail.false_of_invariant_region

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Snail lemma, non-root-of-unity germ form

`Work.LandLeaves.Snail.noSnailOfNotRootOfUnityClean` : a germ `f` at `0` with `f 0 = 0`,
`deriv f 0 = lam`, `‖lam‖ = 1` with `lam` **not** a root of unity admits no continuous forward
path `q : [0,∞) → ℂ∖{0}` with `f (q t) = q (t + 1)` and `q t → 0`.

This is the non-root-of-unity half of the classical **Snail lemma** (Milnor, *Dynamics in one
complex variable*, Lemma 13.2): a path `p → 0` with `f (p t) = p (t + 1)` forces `‖f'(0)‖ < 1`
or `f'(0) = 1`; with `‖lam‖ = 1` and `lam^n ≠ 1` this is impossible.

## Strategy (Milnor 13.2, but with a *dominated convergence* ending)

Writing `λ = deriv f 0`, lift the path to the log-plane by a continuous `L` with `exp ∘ L = q`
(`exists_continuous_log_of_path`) and lift the germ to a univalent `F` on a left half-plane with
`exp (F Z) = f (exp Z)`, `F Z - Z → log λ` (`exists_local_lift_of_germ`).  Correcting `F` by the
constant `log λ - c` (where `c` is the drift of the lifted path, `L (t+1) - L t → c`,
`exists_drift_of_snail`) gives `Fb` with `exp ∘ Fb = f ∘ exp`, `Fb Z - Z → c` and
`Fb (L t) = L (t+1)`.  Milnor's proof then exhibits an `Fb`-invariant spiral region `V₀`
(`existsInvariantRegionCorrected`) whose `exp` is a neighbourhood `V` of `0` that `f` carries into
itself, on which every orbit converges to `0`.

Instead of Milnor's Schwarz-lemma rigidity (the equality case of Schwarz–Pick, not available),
one argues directly: `f^[n] : V → V` is uniformly bounded and converges pointwise to `0` on the
circle `|z| = ρ/2 ⊆ V`; Cauchy's integral formula plus dominated convergence
(`tendsto_deriv_zero_of_tendsto_on_sphere`) give `deriv (f^[n]) 0 → 0`, while the chain rule gives
`deriv (f^[n]) 0 = λ^n`, `‖λ^n‖ = 1`.

The case `c.im < 0` is reduced to `c.im > 0` by conjugating: `z ↦ conj (f (conj z))` is again
holomorphic at `0` with multiplier `conj λ` and the conjugated lifted path has drift `conj c`
whose imaginary part is `- c.im > 0`.
-/

open Filter
open scoped Topology

namespace Work.LandLeaves.Snail

open Complex

lemma cleanZeroIterate {f : ℂ → ℂ} (hfix : f 0 = 0) : ∀ n : ℕ, (f^[n]) 0 = 0 := by
  intro n
  induction n with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', ih, hfix]

lemma cleanDiffAtIterate {f : ℂ → ℂ} (hf : DifferentiableAt ℂ f 0) (hfix : f 0 = 0) :
    ∀ n : ℕ, DifferentiableAt ℂ (f^[n]) 0 := by
  intro n
  induction n with
  | zero => simpa using differentiableAt_id
  | succ k ih =>
    change DifferentiableAt ℂ (f^[k] ∘ f) 0
    exact (by rw [hfix]; exact ih : DifferentiableAt ℂ (f^[k]) (f 0)).comp 0 hf

/-- The chain rule along a fixed point: `(f^[n])'(0) = (f'(0))^n`. -/
lemma cleanDerivIterateEq {f : ℂ → ℂ} {lam : ℂ}
    (hf : DifferentiableAt ℂ f 0) (hfix : f 0 = 0) (hder : deriv f 0 = lam) :
    ∀ n : ℕ, deriv (f^[n]) 0 = lam ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    change deriv ((f^[k]) ∘ f) 0 = lam ^ (k+1)
    rw [deriv_comp (𝕜 := ℂ) 0 (by rw [hfix]; exact cleanDiffAtIterate hf hfix k) hf, hfix, ih, hder]
    ring

/-- A non-zero element of `2πiℤ = exp ⁻¹' {1}` has norm at least `2π`. -/
private lemma two_pi_le_norm_int_mul {n : ℤ} (hn : n ≠ 0) :
    2 * Real.pi ≤ ‖(n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)‖ := by
  have h2 : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one]; norm_num
  rw [norm_mul, h2]
  have h1 : (1 : ℝ) ≤ ‖(n : ℂ)‖ := by
    rw [Complex.norm_intCast, ← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn
  calc 2 * Real.pi = 1 * (2 * Real.pi) := by ring
    _ ≤ ‖(n : ℂ)‖ * (2 * Real.pi) := by gcongr

/-- Conjugation preserves analyticity at the origin. -/
private lemma analyticAt_conj_conj {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    AnalyticAt ℂ (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) 0 := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt] at hf ⊢
  have hf' : ∀ᶠ y in nhds ((starRingEnd ℂ) (0 : ℂ)), DifferentiableAt ℂ f y := by
    simpa using hf
  have h2 : ∀ᶠ z in nhds (0 : ℂ), DifferentiableAt ℂ f ((starRingEnd ℂ) z) :=
    (Complex.continuous_conj.tendsto (0 : ℂ)).eventually hf'
  filter_upwards [h2] with z hz
  simpa [Function.comp_def] using hz.conj_conj

/-- The derivative of the conjugate-conjugate of a germ. -/
private lemma deriv_conj_conj_at {f : ℂ → ℂ} {x : ℂ} :
    deriv (fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z))) x
      = (starRingEnd ℂ) (deriv f ((starRingEnd ℂ) x)) := by
  have h := congrFun (deriv_conj_conj (𝕜 := ℂ) (f := f)) x
  simpa [Function.comp_def] using h

/-- **The core of the Snail lemma in the log-plane**, for a drift `c` with `0 < c.im`.

The hypotheses are the exact output of the lifting constructions: `c` is the drift of the lifted
path, `exp c = lam`, and `0 < c.im` (so that the spiral region exists). -/
theorem cleanCore {f : ℂ → ℂ} {lam c : ℂ} {q L : ℝ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hfix : f 0 = 0) (hder : deriv f 0 = lam)
    (h1 : ‖lam‖ = 1)
    (hcexp : Complex.exp c = lam) (hcim : 0 < c.im)
    (hqc : ContinuousOn q (Set.Ici 0)) (hqne : ∀ t ∈ Set.Ici (0 : ℝ), q t ≠ 0)
    (hshift : ∀ t ∈ Set.Ici (0 : ℝ), f (q t) = q (t + 1))
    (hlim : Filter.Tendsto q Filter.atTop (nhds 0))
    (hLc : ContinuousOn L (Set.Ici 0)) (hLexp : ∀ t ∈ Set.Ici 0, Complex.exp (L t) = q t)
    (hdrift : Filter.Tendsto (fun t : ℝ => L (t + 1) - L t) Filter.atTop (nhds c)) : False := by
  have hlam_ne : lam ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; exact one_ne_zero h1.symm
  have hc_re : c.re = 0 := by
    have h := congrArg (fun w : ℂ => ‖w‖) hcexp
    rw [Complex.norm_exp, h1] at h
    exact (Real.exp_eq_one_iff c.re).mp h
  obtain ⟨F, X₀, hFexp, hFdiff, hFinj, hFdrift⟩ :=
    exists_local_lift_of_germ hf hfix hder hlam_ne
  have hFper : ∀ Z : ℂ, Z.re < X₀ →
      F (Z + 2 * (Real.pi : ℂ) * I) = F Z + 2 * (Real.pi : ℂ) * I :=
    per_of_germ_lift hFdiff hFexp hFdrift
  -- a disc on which `f` is differentiable
  obtain ⟨rd, hrdpos, hrddiff⟩ : ∃ r > 0, DifferentiableOn ℂ f (Metric.ball (0 : ℂ) r) := by
    have h : ∀ᶠ w in nhds (0 : ℂ), DifferentiableAt ℂ f w :=
      Complex.analyticAt_iff_eventually_differentiableAt.mp hf
    rw [Metric.eventually_nhds_iff] at h
    obtain ⟨ε, hε, hh⟩ := h
    exact ⟨ε, hε, fun w hw =>
      (hh (by simpa [Metric.mem_ball, dist_eq_norm] using hw)).differentiableWithinAt⟩
  -- shrink the half-plane so that `exp` of it lands inside the differentiability disc of `f`
  set X : ℝ := min X₀ (Real.log (rd / 4)) with hXdef
  have hXle : X ≤ X₀ := min_le_left _ _
  have hXlog : X ≤ Real.log (rd / 4) := min_le_right _ _
  have hexpX_le : Real.exp X ≤ rd / 4 := by
    have h := Real.exp_le_exp.mpr hXlog
    rwa [Real.exp_log (by linarith)] at h
  -- the corrected lift `Fb = F - (log lam - c)`
  set k : ℂ := Complex.log lam - c with hk
  have hkexp : Complex.exp k = 1 := by
    rw [hk, Complex.exp_sub, Complex.exp_log hlam_ne, hcexp, div_self hlam_ne]
  set Fb : ℂ → ℂ := fun Z => F Z - k with hFbdef
  have hFb_exp : ∀ Z : ℂ, Z.re < X → Complex.exp (Fb Z) = f (Complex.exp Z) := by
    intro Z hZ
    have hZX : Z.re < X₀ := lt_of_lt_of_le hZ hXle
    rw [hFbdef, Complex.exp_sub, hFexp Z hZX, hkexp, div_one]
  have hFb_diff : DifferentiableOn ℂ Fb {Z : ℂ | Z.re < X} := by
    rw [hFbdef]
    exact (hFdiff.mono (fun Z hZ => lt_of_lt_of_le hZ hXle)).sub_const k
  have hFb_inj : Set.InjOn Fb {Z : ℂ | Z.re < X} := by
    rw [hFbdef]
    intro a ha b hb hab
    refine hFinj (lt_of_lt_of_le ha hXle) (lt_of_lt_of_le hb hXle) ?_
    have h := congrArg (fun w : ℂ => w + k) hab
    simpa using h
  have hFb_per : ∀ Z : ℂ, Z.re < X →
      Fb (Z + 2 * (Real.pi : ℂ) * I) = Fb Z + 2 * (Real.pi : ℂ) * I := by
    intro Z hZ
    have hZX : Z.re < X₀ := lt_of_lt_of_le hZ hXle
    have hstep : F (Z + 2 * (Real.pi : ℂ) * I) - k = F Z - k + 2 * (Real.pi : ℂ) * I := by
      rw [hFper Z hZX]; ring
    show F (Z + 2 * (Real.pi : ℂ) * I) - k = (F Z - k) + 2 * (Real.pi : ℂ) * I
    exact hstep
  have hFb_drift : Filter.Tendsto (fun Z : ℂ => Fb Z - Z)
      (Filter.comap Complex.re Filter.atBot) (nhds c) := by
    have h := hFdrift.sub_const k
    have hk' : Complex.log lam - k = c := by rw [hk]; ring
    rw [hk'] at h
    refine h.congr' (Filter.Eventually.of_forall (fun Z => ?_))
    rw [hFbdef]; ring
  -- the path data
  obtain ⟨hPre, hPim⟩ := tendsto_re_im_of_lift hLc hLexp hlim hdrift hcim
  obtain ⟨T₁, hT₁⟩ : ∃ T : ℝ, ∀ t : ℝ, T ≤ t → (L t).re < X := by
    rw [Filter.tendsto_atBot] at hPre
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (hPre (X - 1))
    exact ⟨T, fun t ht => lt_of_le_of_lt (hT t ht) (by linarith)⟩
  set T₀ : ℝ := max T₁ 0 with hT₀def
  have hT₀nn : 0 ≤ T₀ := le_max_right _ _
  have hT₁T₀ : T₁ ≤ T₀ := le_max_left _ _
  have hLT : ∀ t ∈ Set.Ici T₀, (L t).re < X := fun t ht => hT₁ t (le_trans hT₁T₀ ht)
  -- the difference `Fb (L t) - L (t+1)` takes values in `2πiℤ`
  have hDmem : ∀ t : ℝ, T₀ ≤ t → Fb (L t) - L (t + 1) ∈ (Complex.exp ⁻¹' {1}) := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans hT₀nn ht
    have ht10 : 0 ≤ t + 1 := by linarith
    rw [Set.mem_preimage, Set.mem_singleton_iff, Complex.exp_sub, hFb_exp (L t) (hLT t ht),
      hLexp t (by simpa using ht0), hLexp (t + 1) (by simpa using ht10),
      hshift t (by simpa using ht0)]
    exact div_self (hqne (t + 1) (by simpa using ht10))
  -- it is continuous and tends to `0`, hence eventually vanishes
  have hDcont : ContinuousOn (fun t : ℝ => Fb (L t) - L (t + 1)) (Set.Ici T₀) := by
    have h1 : ContinuousOn (fun t : ℝ => Fb (L t)) (Set.Ici T₀) :=
      hFb_diff.continuousOn.comp (hLc.mono (fun t ht => le_trans hT₀nn ht))
        (fun t ht => hLT t ht)
    have h2 : ContinuousOn (fun t : ℝ => L (t + 1)) (Set.Ici T₀) :=
      hLc.comp ((continuous_id.add continuous_const).continuousOn)
        (fun t ht => by simp only [Set.mem_Ici] at ht ⊢; linarith [ht])
    exact h1.sub h2
  have hDlim : Filter.Tendsto (fun t : ℝ => Fb (L t) - L (t + 1)) Filter.atTop (nhds 0) := by
    have hLre : Filter.Tendsto L Filter.atTop (Filter.comap Complex.re Filter.atBot) := by
      rw [Filter.tendsto_comap_iff]; exact hPre
    have h1 : Filter.Tendsto (fun t : ℝ => Fb (L t) - L t) Filter.atTop (nhds c) :=
      hFb_drift.comp hLre
    have h2 : Filter.Tendsto (fun t : ℝ => L (t + 1) - L t) Filter.atTop (nhds c) := hdrift
    have h3 : Filter.Tendsto (fun t : ℝ => (Fb (L t) - L t) - (L (t + 1) - L t)) Filter.atTop
        (nhds (c - c)) := h1.sub h2
    rw [sub_self] at h3
    refine h3.congr' (Filter.Eventually.of_forall (fun t => ?_))
    ring
  obtain ⟨T, hTmax, hTsmall⟩ : ∃ T : ℝ, T₀ ≤ T ∧
      ∀ t : ℝ, T ≤ t → ‖Fb (L t) - L (t + 1)‖ < 2 * Real.pi := by
    have hball : ∀ᶠ t in Filter.atTop,
        Fb (L t) - L (t + 1) ∈ Metric.ball (0 : ℂ) (2 * Real.pi) :=
      hDlim.eventually (Metric.ball_mem_nhds 0 (by positivity))
    obtain ⟨T', hT'⟩ := Filter.eventually_atTop.1 hball
    exact ⟨max T' T₀, le_max_right _ _, fun t ht => by
      have h := hT' t (le_trans (le_max_left _ _) ht)
      rwa [Metric.mem_ball, dist_zero_right] at h⟩
  have hPinv : ∀ t ∈ Set.Ici T, Fb (L t) = L (t + 1) := by
    intro t ht
    have hzero : Fb (L t) - L (t + 1) = 0 := by
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (hDmem t (le_trans hTmax ht))
      have hsmall := hTsmall t ht
      rw [hn] at hsmall ⊢
      have hn0 : n = 0 := by
        by_contra hn'
        have := two_pi_le_norm_int_mul hn'
        linarith
      rw [hn0, Int.cast_zero, zero_mul]
    exact sub_eq_zero.mp hzero
  -- the invariant spiral region
  obtain ⟨V₀, hV₀open, hV₀sub, hV₀maps, hV₀orb, ρ, hρpos, hρball⟩ :=
    existsInvariantRegionCorrected hc_re hcim hFb_diff hFb_inj hFb_per hFb_drift
      (hLc.mono (fun t ht => le_trans (le_trans hT₀nn hTmax) ht))
      (fun t ht => hLT t (le_trans hTmax ht)) hPre hPim hPinv
  -- its exponential is an invariant neighbourhood of `0`
  set V : Set ℂ := Complex.exp '' V₀ ∪ {0} with hVdef
  have hV_bound : ∀ z ∈ V, ‖z‖ ≤ Real.exp X := by
    intro z hz
    rcases hz with ⟨Z, hZ, rfl⟩ | hz0
    · rw [Complex.norm_exp]; exact Real.exp_le_exp.mpr (le_of_lt (hV₀sub hZ))
    · rw [Set.mem_singleton_iff] at hz0
      rw [hz0, norm_zero]; exact Real.exp_nonneg X
  have hV_ball : ∀ z ∈ V, z ∈ Metric.ball (0 : ℂ) rd := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖z‖ ≤ Real.exp X := hV_bound z hz
      _ ≤ rd / 4 := hexpX_le
      _ < rd := by linarith
  have hMapsTo : Set.MapsTo f V V := by
    intro z hz
    rcases hz with ⟨Z, hZ, rfl⟩ | hz0
    · rw [← hFb_exp Z (hV₀sub hZ)]
      exact Or.inl ⟨Fb Z, hV₀maps hZ, rfl⟩
    · rw [Set.mem_singleton_iff] at hz0
      rw [hz0, hfix]; exact Or.inr rfl
  have hfdiffV : DifferentiableOn ℂ f V := hrddiff.mono (fun z hz => hV_ball z hz)
  have hdiffV : ∀ n : ℕ, DifferentiableOn ℂ (f^[n]) V := by
    intro n
    induction n with
    | zero => simpa using (differentiableOn_id : DifferentiableOn ℂ (id : ℂ → ℂ) V)
    | succ k ih =>
      have hcomp : DifferentiableOn ℂ ((f^[k]) ∘ f) V :=
        DifferentiableOn.comp ih hfdiffV hMapsTo
      rwa [funext (fun x => Function.iterate_succ_apply f k x)]
  have hiter_exp : ∀ n : ℕ, ∀ Z ∈ V₀,
      (f^[n]) (Complex.exp Z) = Complex.exp ((Fb^[n]) Z) := by
    intro n
    induction n with
    | zero => intro Z _; simp
    | succ k ih =>
      intro Z hZ
      have hZk : (Fb^[k]) Z ∈ V₀ := Set.MapsTo.iterate hV₀maps k hZ
      rw [Function.iterate_succ_apply', ih Z hZ, ← hFb_exp ((Fb^[k]) Z) (hV₀sub hZk),
        Function.iterate_succ_apply']
  -- the circle of radius `ρ / 2` lies inside `V`
  set R : ℝ := ρ / 2 with hRdef
  have hRpos : 0 < R := by rw [hRdef]; linarith
  have hsphere_sub : Metric.sphere (0 : ℂ) R ⊆ V := by
    intro z hz
    refine hρball ?_
    rw [Metric.mem_ball, dist_zero_right, mem_sphere_zero_iff_norm.mp hz, hRdef]
    linarith
  have hclosed_sub : Metric.closedBall (0 : ℂ) R ⊆ V := by
    intro z hz
    refine hρball ?_
    rw [Metric.mem_ball, dist_zero_right]
    have hz' : ‖z‖ ≤ R := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hz
    rw [hRdef] at hz'
    linarith [hρpos]
  have hconv : ∀ z ∈ Metric.sphere (0 : ℂ) R,
      Filter.Tendsto (fun n : ℕ => (f^[n]) z) Filter.atTop (nhds 0) := by
    intro z hz
    have hzV : z ∈ V := hsphere_sub hz
    have hzne : z ≠ 0 := by
      intro h0
      have h := mem_sphere_zero_iff_norm.mp hz
      rw [h0, norm_zero] at h
      exact (ne_of_lt hRpos) h
    rcases hzV with ⟨Z, hZV, hZeq⟩ | hz0
    · have hnorm : ∀ n : ℕ, ‖(f^[n]) z‖ = Real.exp (((Fb^[n]) Z).re) := by
        intro n
        rw [← hZeq, hiter_exp n Z hZV, Complex.norm_exp]
      have hexp : Filter.Tendsto (fun n : ℕ => Real.exp (((Fb^[n]) Z).re)) Filter.atTop
          (nhds 0) := Real.tendsto_exp_atBot.comp (hV₀orb Z hZV)
      rw [tendsto_zero_iff_norm_tendsto_zero]
      exact hexp.congr' (Filter.Eventually.of_forall (fun n => (hnorm n).symm))
    · rw [Set.mem_singleton_iff] at hz0
      exact absurd hz0 hzne
  have hbdd : ∀ n, ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖(f^[n]) z‖ ≤ Real.exp X :=
    fun n z hz => hV_bound _ (Set.MapsTo.iterate hMapsTo n (hsphere_sub hz))
  have hdiffc : ∀ n : ℕ, DifferentiableOn ℂ (f^[n]) (Metric.closedBall (0 : ℂ) R) :=
    fun n => (hdiffV n).mono hclosed_sub
  have hderiv0 := tendsto_deriv_zero_of_tendsto_on_sphere (g := fun n => f^[n])
    (R := R) (M := Real.exp X) hRpos (Real.exp_nonneg X) hdiffc hbdd hconv
  -- but `deriv (f^[n]) 0 = lam ^ n` has norm `1`
  have hconst : ∀ n : ℕ, ‖deriv (f^[n]) 0‖ = 1 := by
    intro n
    rw [cleanDerivIterateEq hf.differentiableAt hfix hder n, norm_pow, h1, one_pow]
  have hlimnorm : Filter.Tendsto (fun n : ℕ => ‖deriv (f^[n]) 0‖) Filter.atTop (nhds 0) := by
    simpa using hderiv0.norm
  have hfun : (fun n : ℕ => ‖deriv (f^[n]) 0‖) = fun _ => (1 : ℝ) := funext hconst
  rw [hfun] at hlimnorm
  have h1c : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) := tendsto_const_nhds
  exact zero_ne_one (tendsto_nhds_unique hlimnorm h1c)

/-- **The Snail lemma, non-root-of-unity germ form.**

A germ `f` at `0` with `f 0 = 0`, `deriv f 0 = lam` of modulus `1` which is not a root of unity
admits no continuous path `q` avoiding `0` with `f (q t) = q (t + 1)` and `q t → 0`. -/
theorem noSnailOfNotRootOfUnityClean {f : ℂ → ℂ} {lam : ℂ}
    (hf : AnalyticAt ℂ f 0) (hfix : f 0 = 0) (hder : deriv f 0 = lam)
    (h1 : ‖lam‖ = 1) (hnr : ∀ q : ℕ, 0 < q → lam ^ q ≠ 1)
    {q : ℝ → ℂ} (hqc : ContinuousOn q (Set.Ici 0)) (hqne : ∀ t ∈ Set.Ici (0 : ℝ), q t ≠ 0)
    (hshift : ∀ t ∈ Set.Ici (0 : ℝ), f (q t) = q (t + 1))
    (hlim : Filter.Tendsto q Filter.atTop (nhds 0)) : False := by
  have hlam_ne : lam ≠ 0 := by
    intro h; rw [h, norm_zero] at h1; exact one_ne_zero h1.symm
  have hder_ne : deriv f 0 ≠ 0 := by rw [hder]; exact hlam_ne
  have hlam1 : lam ≠ 1 := fun h => hnr 1 (by norm_num) (by rw [h, one_pow])
  obtain ⟨L, hLc, hLexp⟩ := exists_continuous_log_of_path hqc hqne
  obtain ⟨c, hcexp, hdrift⟩ := exists_drift_of_snail hLc hLexp hf hfix hder_ne hqne hshift hlim
  have hcexp' : Complex.exp c = lam := by rw [hcexp, hder]
  have hc_re : c.re = 0 := by
    have h := congrArg (fun w : ℂ => ‖w‖) hcexp'
    rw [Complex.norm_exp, h1] at h
    exact (Real.exp_eq_one_iff c.re).mp h
  have hcim_ne : c.im ≠ 0 := by
    intro h
    have hc : c = 0 := by
      apply Complex.ext
      · simpa using hc_re
      · simpa using h
    rw [hc, Complex.exp_zero] at hcexp'
    exact hlam1 hcexp'.symm
  rcases lt_or_gt_of_ne hcim_ne with hneg | hpos
  · -- `c.im < 0`: conjugate everything, so that the drift has positive imaginary part
    set f' : ℂ → ℂ := fun z => (starRingEnd ℂ) (f ((starRingEnd ℂ) z)) with hf'def
    set q' : ℝ → ℂ := fun t => (starRingEnd ℂ) (q t) with hq'def
    set L' : ℝ → ℂ := fun t => (starRingEnd ℂ) (L t) with hL'def
    have hf'a : AnalyticAt ℂ f' 0 := by
      rw [hf'def]; exact analyticAt_conj_conj hf
    have hf'fix : f' 0 = 0 := by
      rw [hf'def]; simp [hfix]
    have hf'der : deriv f' 0 = (starRingEnd ℂ) lam := by
      rw [hf'def, deriv_conj_conj_at, map_zero, hder]
    have h1' : ‖(starRingEnd ℂ) lam‖ = 1 := by rw [Complex.norm_conj, h1]
    have hcexp'' : Complex.exp ((starRingEnd ℂ) c) = (starRingEnd ℂ) lam := by
      rw [Complex.exp_conj, hcexp']
    have hpos' : 0 < ((starRingEnd ℂ) c).im := by
      rw [Complex.conj_im]; linarith
    have hq'c : ContinuousOn q' (Set.Ici 0) := by
      rw [hq'def]; exact Complex.continuous_conj.comp_continuousOn hqc
    have hq'ne : ∀ t ∈ Set.Ici (0 : ℝ), q' t ≠ 0 := by
      intro t ht h
      rw [hq'def] at h
      exact hqne t ht (by
        have := congrArg (starRingEnd ℂ) h
        simpa using this)
    have hq'shift : ∀ t ∈ Set.Ici (0 : ℝ), f' (q' t) = q' (t + 1) := by
      intro t ht
      simp only [hf'def, hq'def]
      rw [Complex.conj_conj]
      exact congrArg (starRingEnd ℂ) (hshift t ht)
    have hq'lim : Filter.Tendsto q' Filter.atTop (nhds 0) := by
      have h := (Complex.continuous_conj.tendsto (0 : ℂ)).comp hlim
      simpa only [Function.comp_def, map_zero, hq'def] using h
    have hL'c : ContinuousOn L' (Set.Ici 0) := by
      rw [hL'def]; exact Complex.continuous_conj.comp_continuousOn hLc
    have hL'exp : ∀ t ∈ Set.Ici 0, Complex.exp (L' t) = q' t := by
      intro t ht
      simp only [hL'def, hq'def]
      rw [Complex.exp_conj]
      exact congrArg (starRingEnd ℂ) (hLexp t ht)
    have hdt' : Filter.Tendsto (fun t : ℝ => L' (t + 1) - L' t) Filter.atTop
        (nhds ((starRingEnd ℂ) c)) := by
      have h := (Complex.continuous_conj.tendsto c).comp hdrift
      refine h.congr' (Filter.Eventually.of_forall (fun t => ?_))
      simp only [hL'def, Function.comp_apply]
      exact map_sub (starRingEnd ℂ) (L (t + 1)) (L t)
    exact cleanCore hf'a hf'fix hf'der h1' hcexp'' hpos' hq'c hq'ne hq'shift hq'lim hL'c hL'exp hdt'
  · exact cleanCore hf hfix hder h1 hcexp' hpos hqc hqne hshift hlim hLc hLexp hdrift

end Work.LandLeaves.Snail
