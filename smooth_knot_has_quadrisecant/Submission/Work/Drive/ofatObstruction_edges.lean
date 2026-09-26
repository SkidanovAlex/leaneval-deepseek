import Mathlib
import Submission.Work.Drive.oFatDefs
import Submission.Work.Drive.stripCrosscutAvoidingO_of_isClosed_finite_fibre
import Submission.Work.Drive.shortSecantsFree_of_noInflection
import Submission.Work.Drive.tangentChordLocallyFinite
import Submission.Work.Drive.knot_tangent_chord_bound

/-!
# The obstruction set `OFat ρ ∪ TC` is bounded away from the edges of the strip

The project lead's obstruction set `Work.Drive.OFatObstruction r ρ = OFatR r ρ ∪ TCset r` sits in
the period strip `ℝ × (0, period)` of secants.  For the sweep to be able to *avoid* it (brick (d) of
the Kuperberg–Pannwitz argument) it must not accumulate at the two boundary lines `y = 0` and
`y = period`; that is the content of the present lemma:

`∃ δ > 0, closure (OFatObstruction r ρ) ⊆ {q | δ ≤ q.2 ∧ q.2 ≤ period - δ}`.

Two independent inputs:

* `OFatR r ρ ⊆ liftedTrisecant r` (a *fat* middle is a middle), and the no-inflection theorem
  `Work.Drive.shortSecantsFree_of_noInflection` bounds `liftedTrisecant r` away from both edges;
* `TCset r` (the *tangent chords*: chords tangent at one endpoint) is itself bounded away from both
  edges, with a bound obtained from the second-order Taylor expansion of the chord against the
  tangent at an endpoint (`Work.Drive.norm_cross3_chord_bound`, a lemma of
  `tangentChordLocallyFinite`): for a chord of parameter length `h`,
  `cross3 (r (a+h) - r a) (r' a) ≈ (h²/2) · (r'' a × r' a)`, and `r'' a × r' a ≠ 0` by the
  no-inflection hypothesis.  Uniformity in the base point `a` is obtained from the uniform
  continuity of the two-variable map `(x,y) ↦ r'' x × r' y` on a compact fundamental box (both
  factors are `period`-periodic), which yields a *uniform* second-order error bound.

Since both `OFatR` and `TCset` are bounded away from the edges, so is their union's closure.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

section Helpers

/-- The cross product of the first two derivatives of a curve, as a function of the two parameters:
`(x, y) ↦ r'' x × r' y`.  `crossK r (a,a) = curvatureVector r a`. -/
def crossK (r : ℝ → Space) (q : ℝ × ℝ) : Space := cross3 (deriv (deriv r) q.1) (deriv r q.2)

lemma curvatureVector_eq_crossK (r : ℝ → Space) (a : ℝ) : curvatureVector r a = crossK r (a, a) :=
  rfl

/-- **A uniform separation of the tangent chords of an inflection-free knot from the diagonal.**
There is `δ > 0` such that for every `a : ℝ` and every `h ≠ 0` with `|h| < δ`, the chord joining
`r a` and `r (a + h)` is *not* parallel to the tangent at `a`.

This is the quantitative form of `Work.Drive.tangentChordBoundary_local`, made uniform in the base
point: `cross3 (r (a+h) - r a) (r' a)` expands to second order as `(h²/2) · (r'' a × r' a)`, and
`r'' a × r' a` is bounded below in norm on the compact fundamental domain. -/
lemma exists_tangent_cross_sep {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a h : ℝ, 0 < |h| → |h| < δ →
      cross3 (r (a + h) - r a) (deriv r a) ≠ 0 := by
  have hp : 0 < period := period_pos
  -- continuity of the first two derivatives
  have hc1 : Continuous (deriv r) := hr.smooth.continuous_deriv (by simp)
  have hsC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r := hr.smooth.of_le le_top
  have hc1S : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv r) := (contDiff_infty_iff_deriv.mp hsC).2
  have hc2 : Continuous (fun t : ℝ => deriv (deriv r) t) := hc1S.continuous_deriv (by simp)
  -- periodicity of the first two derivatives
  have hper1 : Function.Periodic (deriv r) period := periodic_deriv hr.periodic
  have hper2 : Function.Periodic (deriv (deriv r)) period := periodic_deriv hper1
  have hKcont : Continuous (crossK r) :=
    continuous_cross3_pair.comp ((hc2.comp continuous_fst).prodMk (hc1.comp continuous_snd))
  have hcvcont : Continuous (curvatureVector r) := by
    have h : Continuous (fun a : ℝ => cross3 (deriv (deriv r) a) (deriv r a)) :=
      continuous_cross3_pair.comp (hc2.prodMk hc1)
    exact h
  have hcvper : Function.Periodic (curvatureVector r) period := by
    intro a
    simp only [curvatureVector, hper2 a, hper1 a]
  -- a uniform positive lower bound `m` for `‖r'' a × r' a‖`
  obtain ⟨a₀, -, hmin⟩ := (isCompact_Icc (a := (0:ℝ)) (b := period)).exists_isMinOn
      ⟨0, Set.mem_Icc.mpr ⟨le_rfl, hp.le⟩⟩ hcvcont.norm.continuousOn
  set m : ℝ := ‖curvatureVector r a₀‖ with hmdef
  have hmpos : 0 < m := by
    rw [hmdef]; exact norm_pos_iff.mpr (curvatureVector_ne_zero hinfl a₀)
  have hmle : ∀ a : ℝ, m ≤ ‖curvatureVector r a‖ := by
    intro a
    have h1 : ‖curvatureVector r a‖ = ‖curvatureVector r (resid a)‖ := by
      rw [resid]
      exact congrArg Norm.norm ((hcvper.int_mul ⌊a / period⌋).sub_eq a).symm
    rw [h1, hmdef]
    exact hmin ⟨(resid_mem a).1, (resid_mem a).2.le⟩
  -- a uniform second-order modulus for `(x, y) ↦ r'' x × r' y` on the compact fundamental box
  set K : Set (ℝ × ℝ) := Set.Icc (-period) (2 * period) ×ˢ Set.Icc (-period) (2 * period)
    with hKdef
  have hKc : IsCompact K := by rw [hKdef]; exact isCompact_Icc.prod isCompact_Icc
  have huc : UniformContinuousOn (crossK r) K :=
    hKc.uniformContinuousOn_of_continuous hKcont.continuousOn
  obtain ⟨η, hηpos, hη⟩ := (Metric.uniformContinuousOn_iff.mp huc) (m / 8) (by linarith)
  set η' : ℝ := min η period with hη'def
  have hη'pos : 0 < η' := lt_min hηpos hp
  have hmod : ∀ x y s s' : ℝ, |s| < η' → |s'| < η' →
      ‖crossK r (x + s, y + s') - crossK r (x, y)‖ < m / 8 := by
    intro x y s s' hs hs'
    have hsη : |s| < η := lt_of_lt_of_le hs (min_le_left _ _)
    have hs'η : |s'| < η := lt_of_lt_of_le hs' (min_le_left _ _)
    have hsp : |s| < period := lt_of_lt_of_le hs (min_le_right _ _)
    have hs'p : |s'| < period := lt_of_lt_of_le hs' (min_le_right _ _)
    obtain ⟨hslo, hshi⟩ := abs_lt.mp hsp
    obtain ⟨hs'lo, hs'hi⟩ := abs_lt.mp hs'p
    -- reduce both coordinates to the fundamental domain, using periodicity in each slot
    have hxr : deriv (deriv r) (resid x) = deriv (deriv r) x := by
      rw [resid]; exact (hper2.int_mul ⌊x / period⌋).sub_eq x
    have hyr : deriv r (resid y) = deriv r y := by
      rw [resid]; exact (hper1.int_mul ⌊y / period⌋).sub_eq y
    have hxs : deriv (deriv r) (x + s) = deriv (deriv r) (resid x + s) := by
      have h1 : x + s = (resid x + s) + (⌊x / period⌋ : ℝ) * period := by rw [resid]; ring
      rw [h1]
      exact (hper2.int_mul ⌊x / period⌋) (resid x + s)
    have hys : deriv r (y + s') = deriv r (resid y + s') := by
      have h1 : y + s' = (resid y + s') + (⌊y / period⌋ : ℝ) * period := by rw [resid]; ring
      rw [h1]
      exact (hper1.int_mul ⌊y / period⌋) (resid y + s')
    have hK1 : (resid x + s, resid y + s') ∈ K := by
      rw [hKdef]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
        first
          | linarith [resid_nonneg x, (resid_mem x).2]
          | linarith [resid_nonneg y, (resid_mem y).2]
    have hK2 : (resid x, resid y) ∈ K := by
      rw [hKdef]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;>
        first
          | linarith [resid_nonneg x, (resid_mem x).2]
          | linarith [resid_nonneg y, (resid_mem y).2]
    have hdist : dist (resid x + s, resid y + s') (resid x, resid y) < η := by
      rw [Prod.dist_eq, max_lt_iff]
      exact ⟨by rw [Real.dist_eq, add_sub_cancel_left]; exact hsη,
             by rw [Real.dist_eq, add_sub_cancel_left]; exact hs'η⟩
    have hres := hη (resid x + s, resid y + s') hK1 (resid x, resid y) hK2 hdist
    rw [dist_eq_norm] at hres
    have e1 : crossK r (x + s, y + s') = crossK r (resid x + s, resid y + s') := by
      show cross3 (deriv (deriv r) (x + s)) (deriv r (y + s')) =
        cross3 (deriv (deriv r) (resid x + s)) (deriv r (resid y + s'))
      rw [hxs, hys]
    have e2 : crossK r (x, y) = crossK r (resid x, resid y) := by
      show cross3 (deriv (deriv r) x) (deriv r y) =
        cross3 (deriv (deriv r) (resid x)) (deriv r (resid y))
      rw [hxr, hyr]
    rw [e1, e2]
    exact hres
  -- the second-order Taylor bound of `tangentChordLocallyFinite`, with `a₀ := a`
  set δ₀ : ℝ := min 1 η' with hδ₀def
  have hδ₀pos : 0 < δ₀ := lt_min one_pos hη'pos
  have hδ₀η : δ₀ ≤ η' := by rw [hδ₀def]; exact min_le_right _ _
  refine ⟨δ₀ / 4, by linarith, ?_⟩
  intro a h hh0 hhδ
  have hhyp : ∀ q : ℝ × ℝ, dist q (a, a) < δ₀ →
      dist (cross3 (deriv (deriv r) q.1) (deriv r q.2)) (curvatureVector r a)
        < ‖curvatureVector r a‖ / 4 := by
    intro q hq
    rw [Prod.dist_eq, max_lt_iff] at hq
    have hq1 : |q.1 - a| < η' := by
      rw [Real.dist_eq] at hq
      exact lt_of_lt_of_le hq.1 hδ₀η
    have hq2 : |q.2 - a| < η' := by
      rw [Real.dist_eq] at hq
      exact lt_of_lt_of_le hq.2 hδ₀η
    have hm := hmod a a (q.1 - a) (q.2 - a) hq1 hq2
    have hm' : ‖crossK r (q.1, q.2) - crossK r (a, a)‖ < m / 8 := by
      have h2 := hm
      rw [add_sub_cancel, add_sub_cancel] at h2
      exact h2
    rw [show cross3 (deriv (deriv r) q.1) (deriv r q.2) = crossK r (q.1, q.2) from rfl,
      dist_eq_norm]
    exact lt_of_lt_of_le hm' (by linarith [hmle a])
  have hb := norm_cross3_chord_bound (r := r) hr (a := a) (a₀ := a) (h := h)
    (g₀ := curvatureVector r a) hδ₀pos hhyp
    (by rw [sub_self, abs_zero]; linarith) hhδ
  intro hzero
  set A : Space := cross3 (r (a + h) - r a) (deriv r a) with hAdef
  set B : Space := (h ^ 2 / 2) • curvatureVector r a with hBdef
  have hBnorm : ‖B‖ = (h ^ 2 / 2) * ‖curvatureVector r a‖ := by
    rw [hBdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hAB : ‖A - B‖ ≤ (‖curvatureVector r a‖ / 4) * h ^ 2 := by
    have := hb
    rw [hAdef, hBdef] at this
    rwa [sq_abs] at this
  have hkey : (h ^ 2 / 4) * m ≤ ‖A‖ := by
    have h1 := abs_norm_sub_norm_le A B
    rw [abs_le] at h1
    have h2 : ‖B‖ - ‖A - B‖ ≤ ‖A‖ := by linarith [h1.1]
    have h3 := hmle a
    nlinarith [h2, hAB, hBnorm, h3]
  have hpos : 0 < (h ^ 2 / 4) * m := by
    have hh : h ≠ 0 := abs_pos.mp hh0
    have : 0 < h ^ 2 := by positivity
    positivity
  have : 0 < ‖A‖ := lt_of_lt_of_le hpos hkey
  exact (norm_pos_iff.mp this) hzero

/-- The fat-middle obstruction set is contained in the lifted trisecant locus: a *fat* middle is a
middle. -/
lemma ofatR_subset_liftedTrisecant {r : ℝ → Space} (hr : IsSmoothKnot r) (ρ : ℝ) :
    OFatR r ρ ⊆ liftedTrisecant r := by
  rintro q ⟨h0, h1, u, hu1, hu2, hu3⟩
  refine mem_liftedTrisecant_iff.mpr ⟨h0, h1, ?_⟩
  rw [stripSecantClass_eq_mobiusCover]
  refine (HasMiddleOnClass_iff r (stripPair q h0 h1)).mpr ⟨(u : AddCircle period), ?_⟩
  show knotMap r (u : AddCircle period) ∈
    openSegment ℝ (knotMap r ((stripPair q h0 h1).1.1)) (knotMap r ((stripPair q h0 h1).1.2))
  simp only [stripPair]
  rw [knotMap_eq_r hr u, knotMap_eq_r hr q.1, knotMap_eq_r hr (q.1 + q.2)]
  exact hu3

/-- **The symmetric form**: the separation also holds for the tangency at the *far* endpoint of the
chord (apply the first form to the reversed chord `(a + h, -h)`). -/
lemma exists_tangent_cross_sep₂ {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a h : ℝ, 0 < |h| → |h| < δ →
      cross3 (r (a + h) - r a) (deriv r a) ≠ 0 ∧
      cross3 (r (a + h) - r a) (deriv r (a + h)) ≠ 0 := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_tangent_cross_sep hr hinfl
  refine ⟨δ, hδpos, fun a h hh0 hhδ => ⟨hδ a h hh0 hhδ, ?_⟩⟩
  have h1 : 0 < |(-h)| := by rwa [abs_neg]
  have h2 : |(-h)| < δ := by rwa [abs_neg]
  have hne := hδ (a + h) (-h) h1 h2
  rw [show a + h + -h = a by ring] at hne
  intro hzero
  refine hne ?_
  have hsym : r a - r (a + h) = -(r (a + h) - r a) := by rw [neg_sub]
  rw [hsym, cross3_neg_left, hzero, neg_zero]

/-- A band estimate propagates to the closure, the band being closed. -/
lemma closure_subset_band {A : Set (ℝ × ℝ)} {δ : ℝ}
    (hA : ∀ q ∈ A, δ ≤ q.2 ∧ q.2 ≤ period - δ) :
    ∀ q ∈ closure A, δ ≤ q.2 ∧ q.2 ≤ period - δ := by
  have hcl : IsClosed {q : ℝ × ℝ | δ ≤ q.2 ∧ q.2 ≤ period - δ} :=
    (isClosed_le continuous_const continuous_snd).inter
      (isClosed_le continuous_snd continuous_const)
  have hsub : closure A ⊆ {q : ℝ × ℝ | δ ≤ q.2 ∧ q.2 ≤ period - δ} :=
    calc closure A ⊆ closure {q : ℝ × ℝ | δ ≤ q.2 ∧ q.2 ≤ period - δ} :=
          closure_mono (fun p hp => hA p hp)
      _ = {q : ℝ × ℝ | δ ≤ q.2 ∧ q.2 ≤ period - δ} := IsClosed.closure_eq hcl
  exact fun q hq => hsub hq

/-- The set of tangent chords `Work.Drive.TCset r` is bounded away from both edges of the strip, by
`Work.Drive.exists_tangent_cross_sep` (the second-order expansion of the chord against the tangent at
an endpoint). -/
lemma tcSet_band {r : ℝ → Space} (hr : IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ ![deriv r t, deriv (deriv r) t]) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ TCset r, δ ≤ q.2 ∧ q.2 ≤ period - δ := by
  obtain ⟨δ, hδpos, hδ⟩ := exists_tangent_cross_sep₂ hr hinfl
  refine ⟨δ, hδpos, ?_⟩
  intro q hq
  obtain ⟨hq0, hq1, hcross⟩ := mem_TCset_iff.mp hq
  -- the chord is the same when the second endpoint is shifted by one period
  have hper1 : Function.Periodic (deriv r) period := periodic_deriv hr.periodic
  have hrp : r (q.1 + (q.2 - period)) = r (q.1 + q.2) := by
    have h := hr.periodic (q.1 + (q.2 - period))
    rw [show q.1 + (q.2 - period) + period = q.1 + q.2 by ring] at h
    exact h.symm
  have hvp : deriv r (q.1 + (q.2 - period)) = deriv r (q.1 + q.2) := by
    have h := hper1 (q.1 + (q.2 - period))
    rw [show q.1 + (q.2 - period) + period = q.1 + q.2 by ring] at h
    exact h.symm
  constructor
  · by_contra hcon
    have hcon' : q.2 < δ := not_le.mp hcon
    have hqpos : 0 < |q.2| := by rw [abs_of_pos hq0]; exact hq0
    have hqlt : |q.2| < δ := by rw [abs_of_pos hq0]; exact hcon'
    obtain ⟨hA', hB'⟩ := hδ q.1 q.2 hqpos hqlt
    rcases hcross with hA | hB
    · exact absurd (by simpa [velocity] using hA) hA'
    · exact absurd (by simpa [velocity] using hB) hB'
  · by_contra hcon
    have hcon' : period - q.2 < δ := by linarith [not_le.mp hcon]
    have hηpos : 0 < period - q.2 := by linarith
    have hηδ : period - q.2 < δ := hcon'
    have habs : |q.2 - period| = period - q.2 := by
      rw [abs_of_neg (by linarith)]; ring
    have h1 : 0 < |q.2 - period| := by rw [habs]; exact hηpos
    have h2 : |q.2 - period| < δ := by rw [habs]; exact hηδ
    obtain ⟨hA', hB'⟩ := hδ q.1 (q.2 - period) h1 h2
    rcases hcross with hA | hB
    · refine absurd ?_ hA'
      rw [hrp]
      simpa [velocity] using hA
    · refine absurd ?_ hB'
      rw [hrp, hvp]
      simpa [velocity] using hB

end Helpers

theorem ofatObstruction_edges
    {r : ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hr : LeanEval.KnotTheory.Quadrisecant.IsSmoothKnot r)
    (hinfl : ∀ t : ℝ, LinearIndependent ℝ
      ![deriv r t, deriv (deriv r) t])
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ q ∈ closure (Work.Drive.OFatObstruction r ρ),
        δ ≤ q.2 ∧ q.2 ≤ LeanEval.KnotTheory.Quadrisecant.period - δ := by
  -- the bound is uniform in `ρ`; the hypothesis `0 < ρ` is part of the statement but not used
  have _hρpos : 0 < ρ := hρ
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := shortSecantsFree_of_noInflection hr hinfl
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := tcSet_band hr hinfl
  set δ : ℝ := min δ₁ δ₂ with hδdef
  have hδpos : 0 < δ := lt_min hδ₁pos hδ₂pos
  refine ⟨δ, hδpos, ?_⟩
  have hδle₁ : δ ≤ δ₁ := by rw [hδdef]; exact min_le_left _ _
  have hδle₂ : δ ≤ δ₂ := by rw [hδdef]; exact min_le_right _ _
  intro q hq
  rw [OFatObstruction, closure_union] at hq
  rcases hq with hq | hq
  · have hmem : q ∈ closure (liftedTrisecant r) :=
      closure_mono (ofatR_subset_liftedTrisecant hr ρ) hq
    obtain ⟨h1, h2⟩ := closure_subset_band hδ₁ q hmem
    exact ⟨by linarith, by linarith⟩
  · obtain ⟨h1, h2⟩ := closure_subset_band hδ₂ q hq
    exact ⟨by linarith, by linarith⟩

end Work.Drive
