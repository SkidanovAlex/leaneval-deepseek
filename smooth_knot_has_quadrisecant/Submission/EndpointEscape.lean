import Mathlib
import ChallengeDeps
import Submission.Helpers
import Submission.CollinearityMap
import Submission.Commons.Analysis.Calculus.tendsto_slope_of_contDiffAt
import Submission.QuadrisecantChord

open LeanEval.KnotTheory.Quadrisecant
open Filter
open scoped Real Topology

/-!
# Milestone-2 step (iii) — the endpoint-escape lemma

**Statement (endpoint escape).**  Let `r` be a smooth knot, `a₀ b₀ m₀` a
strict collinear triple whose chord direction `d₀ = r a₀ − r b₀` is *not*
parallel to the tangent `velocity a₀` at the endpoint `a₀`
(`cross3 d₀ (velocity a₀) ≠ 0`).  Then no sequence of strict trisecant data
`(aₙ, bₙ, mₙ)` — with `mₙ` strictly between `aₙ` and `bₙ` — can have
`aₙ → a₀`, `bₙ → b₀` while the middles `mₙ → a₀` run to the *endpoint*:
the normalised-limit argument forces `velocity a₀ = λ • d₀`, contradicting
the transversality.

This is the geometric content behind the local open-map structure of `O`:
under the transverse general position of `TrisecantTransverse.lean`, the
middle points of strict data whose classes stay near a class `c₀ ∈ O`
cannot degenerate toward an endpoint of `c₀`'s chord (which would place
their classes outside the local sheet image).

**Proof (normalised-limit argument).**  From the strict betweenness,
`r mₙ − r aₙ = tₙ (r bₙ − r aₙ)` with `tₙ ∈ (0,1)`.  Fix a coordinate
`i₀` with `(r a₀ − r b₀).ofLp i₀ ≠ 0`.  For every coordinate `k` the scalar
slope lemma (`Commons.Analysis.Calculus.tendsto_slope_of_contDiffAt`,
applied to the coordinate functions `t ↦ (r t).ofLp k`, which are C¹ by the
knot's smoothness) gives
`(r mₙ − r aₙ).ofLp k / (mₙ − aₙ) → (velocity a₀).ofLp k`.  But by the
factorisation the same quantity is `sₙ (r bₙ − r aₙ).ofLp k` with
`sₙ = tₙ/(mₙ − aₙ)`; from the `i₀`-coordinate equation the scalar `sₙ`
converges to `(velocity a₀).ofLp i₀ / (r a₀ − r b₀).ofLp i₀`, and then
every coordinate of `velocity a₀` equals that scalar times the
corresponding coordinate of `d₀` — so `velocity a₀ = λ • d₀` and the cross
product vanishes, contradicting `cross3 d₀ (velocity a₀) ≠ 0`.

Everything here is elementary and verified (no axioms, no `sorry`).
-/

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-! ## 1. Coordinate functions of the knot are C¹ with the expected slopes -/

/-- The coordinate projection `Space →L[ℝ] ℝ`. -/
def coordProj (i : Fin 3) : Space →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) i

/-- The coordinate projection evaluates as `.ofLp`. -/
lemma coordProj_apply (i : Fin 3) (z : Space) : coordProj i z = z.ofLp i := rfl

/-- A nonzero vector of the space has a nonzero coordinate. -/
lemma exists_ofLp_ne_zero_of_ne_zero {v : Space} (hv : v ≠ 0) : ∃ i : Fin 3, v.ofLp i ≠ 0 := by
  by_contra h
  push Not at h
  apply hv
  ext i
  simpa using h i

/-- The scalar coordinate functions of the knot are C¹ at every point. -/
lemma contDiffAt_coord {r : ℝ → Space} (h : IsSmoothKnot r) (t₀ : ℝ) (i : Fin 3) :
    ContDiffAt ℝ 1 (fun t : ℝ => (r t).ofLp i) t₀ := by
  have hc1 : ContDiffAt ℝ 1 r t₀ := ContDiffAt.of_le h.smooth.contDiffAt le_top
  have hP : ContDiff ℝ ⊤ (fun x : Space => x.ofLp i) := by
    exact ContinuousLinearMap.contDiff (coordProj i)
  have hL : ContDiffAt ℝ 1 (fun x : Space => x.ofLp i) (r t₀) := ContDiffAt.of_le hP.contDiffAt le_top
  convert (ContDiffAt.comp (x := t₀) hL hc1) using 1
  funext t
  rfl

/-- The derivative of the coordinate function is the coordinate of the
velocity. -/
lemma deriv_coord {r : ℝ → Space} (h : IsSmoothKnot r) (t₀ : ℝ) (i : Fin 3) :
    deriv (fun t : ℝ => (r t).ofLp i) t₀ = (velocity r t₀).ofLp i := by
  have hdd : DifferentiableAt ℝ r t₀ :=
    (ContDiff.of_le h.smooth le_top).differentiable_one.differentiableAt
  have hc : DifferentiableAt ℝ (fun _ : ℝ => (coordProj i : Space →L[ℝ] ℝ)) t₀ :=
    differentiableAt_const (c := (coordProj i : Space →L[ℝ] ℝ))
  have hmain := deriv_clm_apply (𝕜 := ℝ) (c := (fun _ : ℝ => (coordProj i : Space →L[ℝ] ℝ)))
    (u := r) hc hdd
  have hfun : (fun y : ℝ => ((fun _ : ℝ => (coordProj i : Space →L[ℝ] ℝ)) y) (r y)) =
      (fun t : ℝ => (r t).ofLp i) := by
    funext t
    rfl
  rw [hfun] at hmain
  rw [deriv_const] at hmain
  simp at hmain
  rw [velocity]
  simpa [coordProj] using hmain

/-! ## 2. The normalised-limit slope of each coordinate of the knot -/

/-- For a strict middle family `m n` between `a n` and `b n`, each coordinate
of the chord direction times the scalar `t n / (m n − a n)` converges to the
coordinate of the velocity (this is the coordinate slope lemma applied to
the equality `r (m n) − r (a n) = t n • (r (b n) − r (a n))`). -/
lemma coord_slope_eq_of_middle {r : ℝ → Space} (h : IsSmoothKnot r)
    {a₀ : ℝ} {a b m : ℕ → ℝ} {t : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 a₀)) (hm : Tendsto m atTop (𝓝 a₀))
    (hmna : ∀ n, m n ≠ a n)
    (hmid : ∀ n, r (m n) - r (a n) = t n • (r (b n) - r (a n)))
    (_ht : ∀ n, 0 < t n ∧ t n < 1) (i : Fin 3) :
    Tendsto (fun n : ℕ => t n * (r (b n) - r (a n)).ofLp i / (m n - a n))
      atTop (𝓝 ((velocity r a₀).ofLp i)) := by
  -- the slope of the i-coordinate of the knot over [a n, m n]
  have hslope : Tendsto (fun n : ℕ =>
      ((r (m n)).ofLp i - (r (a n)).ofLp i) / (m n - a n)) atTop
      (𝓝 (deriv (fun t : ℝ => (r t).ofLp i) a₀)) := by
    exact Commons.Analysis.Calculus.tendsto_slope_of_contDiffAt
      (contDiffAt_coord h a₀ i) hm ha (Eventually.of_forall hmna)
  -- the coordinate of the factorisation equality
  have hcoord : ∀ n, (r (m n)).ofLp i - (r (a n)).ofLp i = t n * (r (b n) - r (a n)).ofLp i := by
    intro n
    have hlin : (r (m n)).ofLp i - (r (a n)).ofLp i =
        (r (m n) - r (a n)).ofLp i := by
      -- projection of a difference is the difference of projections
      change coordProj i (r (m n)) - coordProj i (r (a n)) = coordProj i (r (m n) - r (a n))
      rw [← (coordProj i).map_sub]
    rw [hlin, hmid n]
    -- projection of a scalar multiple
    change coordProj i (t n • (r (b n) - r (a n))) = t n * (r (b n) - r (a n)).ofLp i
    rw [(coordProj i).map_smul]
    simp [coordProj_apply]
  have heq : (fun n : ℕ => ((r (m n)).ofLp i - (r (a n)).ofLp i) / (m n - a n)) =
      (fun n : ℕ => t n * (r (b n) - r (a n)).ofLp i / (m n - a n)) := by
    funext n
    rw [hcoord n]
  rw [deriv_coord h a₀ i] at hslope
  simpa [heq] using hslope

/-! ## 3. The endpoint-escape lemma -/

/-- The coordinate functions of the knot are continuous (each coordinate of
`r`, composed with the convergences of the parameter sequences). -/
lemma coord_tendsto_of_tendsto {r : ℝ → Space} (h : IsSmoothKnot r)
    {x₀ : ℝ} {x : ℕ → ℝ} (hx : Tendsto x atTop (𝓝 x₀)) (i : Fin 3) :
    Tendsto (fun n : ℕ => (r (x n)).ofLp i) atTop (𝓝 ((r x₀).ofLp i)) := by
  have hc : Continuous (fun t : ℝ => (r t).ofLp i) := by
    refine ((coordProj i).continuous.comp h.smooth.continuous).congr ?_
    intro t
    exact coordProj_apply i (r t)
  change Tendsto (((fun t : ℝ => (r t).ofLp i) ∘ x)) atTop (𝓝 ((r x₀).ofLp i))
  exact (hc.tendsto x₀).comp hx

/-- The coordinates of the chord differences `r (b n) − r (a n)` converge to
the coordinates of `r b₀ − r a₀`. -/
lemma chord_coord_tendsto {r : ℝ → Space} (h : IsSmoothKnot r)
    {a₀ b₀ : ℝ} {a b : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 a₀))
    (hb : Tendsto b atTop (𝓝 b₀)) (i : Fin 3) :
    Tendsto (fun n : ℕ => (r (b n) - r (a n)).ofLp i) atTop (𝓝 ((r b₀ - r a₀).ofLp i)) := by
  have hb1 : Tendsto (fun n : ℕ => (r (b n)).ofLp i) atTop (𝓝 ((r b₀).ofLp i)) :=
    coord_tendsto_of_tendsto h hb i
  have ha1 : Tendsto (fun n : ℕ => (r (a n)).ofLp i) atTop (𝓝 ((r a₀).ofLp i)) :=
    coord_tendsto_of_tendsto h ha i
  have hsub : Tendsto (fun n : ℕ => (r (b n)).ofLp i - (r (a n)).ofLp i) atTop
      (𝓝 ((r b₀).ofLp i - (r a₀).ofLp i)) := hb1.sub ha1
  have hfeq : (fun n : ℕ => (r (b n)).ofLp i - (r (a n)).ofLp i) =
      (fun n : ℕ => (r (b n) - r (a n)).ofLp i) := by
    funext n
    change coordProj i (r (b n)) - coordProj i (r (a n)) = coordProj i (r (b n) - r (a n))
    rw [← (coordProj i).map_sub]
  simpa [hfeq, coordProj_apply] using hsub

/-- **Endpoint escape (normalised-limit form).**  If strict middle data
`(a n, b n, m n)` with `a n → a₀`, `b n → b₀`, `m n → a₀` and `m n ≠ a n`
satisfies `r (m n) − r (a n) = t n • (r (b n) − r (a n))` with `0 < t n < 1`
for every `n`, then the chord direction at the limit is parallel to the
tangent at the endpoint: `cross3 (r b₀ − r a₀) (velocity r a₀) = 0`. -/
theorem middle_to_endpoint_cross_zero {r : ℝ → Space} (h : IsSmoothKnot r)
    {a₀ b₀ : ℝ} (hd : r b₀ - r a₀ ≠ 0)
    {a b m t : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀))
    (hm : Tendsto m atTop (𝓝 a₀))
    (hmna : ∀ n, m n ≠ a n)
    (hmid : ∀ n, r (m n) - r (a n) = t n • (r (b n) - r (a n)))
    (ht : ∀ n, 0 < t n ∧ t n < 1) :
    cross3 (r b₀ - r a₀) (velocity r a₀) = 0 := by
  let D : Space := r b₀ - r a₀
  rcases exists_ofLp_ne_zero_of_ne_zero hd with ⟨i₀, hD₀⟩
  have hdc : ∀ i : Fin 3, Tendsto (fun n : ℕ => (r (b n) - r (a n)).ofLp i) atTop
      (𝓝 (D.ofLp i)) := by
    intro i
    simpa [D] using chord_coord_tendsto h ha hb i
  have hsl : ∀ i : Fin 3, Tendsto
      (fun n : ℕ => t n * (r (b n) - r (a n)).ofLp i / (m n - a n)) atTop
      (𝓝 ((velocity r a₀).ofLp i)) := fun i =>
    coord_slope_eq_of_middle h ha hm hmna hmid ht i
  have hDne : ∀ᶠ n in atTop, (r (b n) - r (a n)).ofLp i₀ ≠ 0 := by
    have hc0 : 0 < |D.ofLp i₀| / 2 := div_pos (abs_pos.mpr hD₀) (by norm_num)
    have hcl : ∀ᶠ n in atTop,
        dist ((r (b n) - r (a n)).ofLp i₀) (D.ofLp i₀) < |D.ofLp i₀| / 2 :=
      (Metric.tendsto_nhds.mp (hdc i₀)) (|D.ofLp i₀| / 2) hc0
    filter_upwards [hcl] with n hn
    intro hz
    have hn' : dist (0 : ℝ) (D.ofLp i₀) < |D.ofLp i₀| / 2 := by
      simpa [hz] using hn
    have hlt : |D.ofLp i₀| < |D.ofLp i₀| / 2 := by
      simpa [Real.dist_eq] using hn'
    have hcpos : 0 < |D.ofLp i₀| := abs_pos.mpr hD₀
    linarith
  let s : ℕ → ℝ := fun n => t n / (m n - a n)
  have hseq : Tendsto s atTop (𝓝 (((velocity r a₀).ofLp i₀) / D.ofLp i₀)) := by
    have hdiv : Tendsto
        (fun n : ℕ => (t n * (r (b n) - r (a n)).ofLp i₀ / (m n - a n)) /
          (r (b n) - r (a n)).ofLp i₀) atTop
        (𝓝 (((velocity r a₀).ofLp i₀) / D.ofLp i₀)) :=
      (hsl i₀).div (hdc i₀) hD₀
    refine hdiv.congr' ?_
    have heq : ∀ᶠ n in atTop,
        s n = (t n * (r (b n) - r (a n)).ofLp i₀ / (m n - a n)) /
          (r (b n) - r (a n)).ofLp i₀ := by
      filter_upwards [hDne] with n hn
      have hn' : (r (b n)).ofLp i₀ - (r (a n)).ofLp i₀ ≠ 0 := by
        simpa [coordProj_apply, ← (coordProj i₀).map_sub] using hn
      dsimp [s]
      field_simp [hn', sub_ne_zero.mpr (hmna n)]
    filter_upwards [heq] with n hn
    exact hn.symm
  have hvec : ∀ i : Fin 3, (velocity r a₀).ofLp i =
      (((velocity r a₀).ofLp i₀) / D.ofLp i₀) * D.ofLp i := by
    intro i
    have hmul : Tendsto (fun n : ℕ => s n * (r (b n) - r (a n)).ofLp i) atTop
        (𝓝 ((((velocity r a₀).ofLp i₀) / D.ofLp i₀) * D.ofLp i)) :=
      hseq.mul (hdc i)
    have heqpoint : ∀ n : ℕ,
        t n * (r (b n) - r (a n)).ofLp i / (m n - a n) =
          s n * (r (b n) - r (a n)).ofLp i := by
      intro n
      change t n * (r (b n) - r (a n)).ofLp i / (m n - a n) =
        (t n / (m n - a n)) * (r (b n) - r (a n)).ofLp i
      field_simp [sub_ne_zero.mpr (hmna n)]
    have hsl' : Tendsto (fun n : ℕ => s n * (r (b n) - r (a n)).ofLp i) atTop
        (𝓝 ((velocity r a₀).ofLp i)) := by
      exact (hsl i).congr' (Eventually.of_forall heqpoint)
    exact tendsto_nhds_unique hsl' hmul
  have hpar : velocity r a₀ =
      (((velocity r a₀).ofLp i₀) / D.ofLp i₀) • D := by
    ext i
    have hsm : ((((velocity r a₀).ofLp i₀) / D.ofLp i₀) • D).ofLp i =
        (((velocity r a₀).ofLp i₀) / D.ofLp i₀) * D.ofLp i := by
      change coordProj i ((((velocity r a₀).ofLp i₀) / D.ofLp i₀) • D) =
          (((velocity r a₀).ofLp i₀) / D.ofLp i₀) * D.ofLp i
      rw [(coordProj i).map_smul]
      simp [coordProj_apply]
    rw [hsm]
    exact hvec i
  rw [hpar]
  exact cross3_collinear_zero D (((velocity r a₀).ofLp i₀) / D.ofLp i₀)

/-- Strict membership in an open segment gives the affine coefficient:
`z ∈ openSegment x y` means `z − x = t • (y − x)` for some `0 < t < 1`. -/
lemma mem_openSegment_smul_sub {x y z : Space} (h : z ∈ openSegment ℝ x y) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ z - x = t • (y - x) := by
  rcases h with ⟨a, b, ha, hb, hab, hz⟩
  refine ⟨b, hb, ?_, ?_⟩
  · linarith
  · calc
      z - x = (a • x + b • y) - x := by rw [← hz]
      _ = b • (y - x) := by
        have h1 : a • x + b • y = x + b • (y - x) :=
          smul_add_smul_eq_add_smul_sub (A := x) (B := y) (s := a) (t := b) hab
        rw [h1]
        abel

/-- **Endpoint escape.**  Under the transversality `cross3 (r a₀ − r b₀)
(velocity r a₀) ≠ 0` no strict middle family of a knot can have its chords
tend to the chord `{a₀,b₀}` while its middles tend to the endpoint `a₀`. -/
theorem no_middle_to_endpoint {r : ℝ → Space} (h : IsSmoothKnot r)
    {a₀ b₀ : ℝ} (hd : r a₀ - r b₀ ≠ 0)
    (htr : cross3 (r a₀ - r b₀) (velocity r a₀) ≠ 0)
    {a b m : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀))
    (hm : Tendsto m atTop (𝓝 a₀))
    (hmna : ∀ n, m n ≠ a n)
    (hmid : ∀ n, r (m n) ∈ openSegment ℝ (r (a n)) (r (b n))) : False := by
  have hd' : r b₀ - r a₀ ≠ 0 := by
    apply sub_ne_zero.mpr
    intro hba
    apply hd
    simpa [sub_eq_iff_eq_add] using hba.symm
  have ht_aux : ∀ n : ℕ, ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      r (m n) - r (a n) = t • (r (b n) - r (a n)) := fun n =>
    mem_openSegment_smul_sub (hmid n)
  let t : ℕ → ℝ := fun n => Classical.choose (ht_aux n)
  have ht₀ : ∀ n, 0 < t n ∧ t n < 1 := by
    intro n
    exact ⟨(Classical.choose_spec (ht_aux n)).1, (Classical.choose_spec (ht_aux n)).2.1⟩
  have hteq : ∀ n, r (m n) - r (a n) = t n • (r (b n) - r (a n)) := by
    intro n
    exact (Classical.choose_spec (ht_aux n)).2.2
  have hz := middle_to_endpoint_cross_zero h hd' ha hb hm hmna hteq ht₀
  have hneg : cross3 (r a₀ - r b₀) (velocity r a₀) = 0 := by
    have hstep : r a₀ - r b₀ = -(r b₀ - r a₀) := by abel
    rw [hstep, cross3_neg_left, hz]
    simp
  exact htr hneg

/-- **Endpoint escape at the second endpoint.**  Under the transversality
`cross3 (r a₀ − r b₀) (velocity r b₀) ≠ 0` no strict middle family can
have its chords tend to the chord `{a₀,b₀}` while its middles tend to the
*other* endpoint `b₀`.  (Mirror of `no_middle_to_endpoint` by swapping
the roles of the two chord endpoints: `openSegment` membership is
symmetric.) -/
theorem no_middle_to_endpoint_b {r : ℝ → Space} (h : IsSmoothKnot r)
    {a₀ b₀ : ℝ} (hd : r a₀ - r b₀ ≠ 0)
    (htr : cross3 (r a₀ - r b₀) (velocity r b₀) ≠ 0)
    {a b m : ℕ → ℝ}
    (ha : Tendsto a atTop (𝓝 a₀)) (hb : Tendsto b atTop (𝓝 b₀))
    (hm : Tendsto m atTop (𝓝 b₀))
    (hmnb : ∀ n, m n ≠ b n)
    (hmid : ∀ n, r (m n) ∈ openSegment ℝ (r (a n)) (r (b n))) : False := by
  have hd' : r b₀ - r a₀ ≠ 0 := by
    rw [← neg_sub]
    exact neg_ne_zero.mpr hd
  have htr' : cross3 (r b₀ - r a₀) (velocity r b₀) ≠ 0 := by
    intro hz
    apply htr
    have hstep : r a₀ - r b₀ = -(r b₀ - r a₀) := by abel
    rw [hstep, cross3_neg_left]
    simp [hz]
  have hmid' : ∀ n : ℕ, r (m n) ∈ openSegment ℝ (r (b n)) (r (a n)) := fun n => by
    rw [openSegment_symm]
    exact hmid n
  exact no_middle_to_endpoint h hd' htr' hb ha hm hmnb hmid'

