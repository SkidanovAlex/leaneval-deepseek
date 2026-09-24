import Mathlib
import Submission.Commons.Analysis.Complex.Harmonic.subharmonic_le_harmonic_of_le_on_sphere
import Submission.Commons.Analysis.Complex.Harmonic.circleAverage_ge_of_le_harmonic
import Submission.Commons.Analysis.Complex.Harmonic.subharmonic_le_harmonic_on_open
import Submission.Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic

namespace Commons.Analysis.Complex.Harmonic

/-- **Comparison criterion transported across a biholomorphism.**
Let `Ω, Ω' ⊆ ℂ` be open, `v` continuous on `Ω` with the circle mean-value inequality,
and let `T : Ω' → Ω` be a biholomorphism with inverse `S`.  Then the comparison criterion
for `v` on `Ω` transports to `v ∘ T` on `Ω'`: for every closed ball `Metric.closedBall p r`
inside `Ω'` and every `h` harmonic on `Metric.ball p r`, continuous on `Metric.closedBall p r`,
with `v (T z) ≤ h z` on the sphere, one has `v (T z) ≤ h z` on the whole ball.

The proof pulls `h` back to `H := h ∘ S` on the open set `T '' Metric.ball p r` and applies
the comparison criterion on an open set (`subharmonic_le_harmonic_on_open`) there. -/
theorem subharmonic_le_harmonic_comp_biholo {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω)
    {v : ℂ → ℝ} (hcont : ContinuousOn v Ω)
    (hMVP : ∀ p ∈ Ω, ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Ω →
      v p ≤ Real.circleAverage v p r)
    {T S : ℂ → ℂ} (hTmap : Set.MapsTo T Ω' Ω) (hSmap : Set.MapsTo S Ω Ω')
    (hTS : ∀ z ∈ Ω', S (T z) = z) (hST : ∀ w ∈ Ω, T (S w) = w)
    (hTcont : ContinuousOn T Ω') (hScont : ContinuousOn S Ω)
    (hTana : AnalyticOnNhd ℂ T Ω') (hSana : AnalyticOnNhd ℂ S Ω)
    {p : ℂ} {r : ℝ} (_hr : 0 < r) (hball : Metric.closedBall p r ⊆ Ω') {h : ℂ → ℝ}
    (hharm : InnerProductSpace.HarmonicOnNhd h (Metric.ball p r))
    (hcont_h : ContinuousOn h (Metric.closedBall p r))
    (hle : ∀ z ∈ Metric.sphere p r, v (T z) ≤ h z) :
    ∀ z ∈ Metric.ball p r, v (T z) ≤ h z := by
  have _ := hTana
  have _ := hSmap
  have hBΩ' : Metric.ball p r ⊆ Ω' := Metric.ball_subset_closedBall.trans hball
  -- The image of the ball under the biholomorphism.
  set Ω'' : Set ℂ := T '' Metric.ball p r with hΩ''def
  -- `Ω''` is the pullback of the ball along `S`, hence open.
  have hΩ''eq : Ω'' = Ω ∩ S ⁻¹' Metric.ball p r := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hTmap (hBΩ' hz), by
        show S (T z) ∈ Metric.ball p r
        rw [hTS z (hBΩ' hz)]
        exact hz⟩
    · rintro ⟨hwΩ, hwS⟩
      exact ⟨S w, hwS, hST w hwΩ⟩
  have hΩ''open : IsOpen Ω'' := by
    rw [hΩ''eq]
    exact hScont.isOpen_inter_preimage hΩ Metric.isOpen_ball
  have hΩ''conn : IsPreconnected Ω'' := by
    rw [hΩ''def]
    exact Metric.isPreconnected_ball.image T (hTcont.mono hBΩ')
  -- `T '' closedBall p r` is compact, hence closed and bounded.
  have hTcb_compact : IsCompact (T '' Metric.closedBall p r) :=
    (ProperSpace.isCompact_closedBall p r).image_of_continuousOn (hTcont.mono hball)
  have hΩ''bdd : Bornology.IsBounded Ω'' := by
    rw [hΩ''def]
    exact hTcb_compact.isBounded.subset (Set.image_mono Metric.ball_subset_closedBall)
  have hcl : closure Ω'' ⊆ T '' Metric.closedBall p r := by
    rw [hΩ''def]
    exact closure_minimal (Set.image_mono Metric.ball_subset_closedBall) hTcb_compact.isClosed
  have hclosure : closure Ω'' ⊆ Ω := by
    refine hcl.trans ?_
    rintro w ⟨y, hy, rfl⟩
    exact hTmap (hball hy)
  -- The pulled-back harmonic function `H = h ∘ S` on `Ω''`.
  set H : ℂ → ℝ := fun w => h (S w) with hHdef
  have hHharm : InnerProductSpace.HarmonicOnNhd H Ω'' := by
    intro w hw
    rw [hΩ''def] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    have hzΩ' : z ∈ Ω' := hBΩ' hz
    have hTzΩ : T z ∈ Ω := hTmap hzΩ'
    refine Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic
      (u := h) (f := S) (x := T z) (hSana (T z) hTzΩ) ?_
    rw [hTS z hzΩ']
    exact hharm z hz
  have hHcont : ContinuousOn H (closure Ω'') := by
    have hmap : Set.MapsTo S (closure Ω'') (Metric.closedBall p r) := by
      intro w hw
      obtain ⟨y, hy, hyw⟩ := hcl hw
      subst hyw
      rw [hTS y (hball hy)]
      exact hy
    have hScont' : ContinuousOn S (closure Ω'') := hScont.mono hclosure
    exact hcont_h.comp hScont' hmap
  -- On the "boundary" of `Ω''` the values of `v` are bounded by those of `H`.
  have hbd : ∀ z ∈ closure Ω'', z ∉ Ω'' → v z ≤ H z := by
    intro z hzcl hzn
    obtain ⟨y, hy, hyz⟩ := hcl hzcl
    subst hyz
    have hysph : y ∈ Metric.sphere p r := by
      have hycb : dist y p ≤ r := Metric.mem_closedBall.mp hy
      have hyball : ¬ dist y p < r := by
        intro hlt
        exact hzn ⟨y, Metric.mem_ball.mpr hlt, rfl⟩
      rw [Metric.mem_sphere]
      exact le_antisymm hycb (not_lt.mp hyball)
    have hHval : H (T y) = h y := by
      change h (S (T y)) = h y
      rw [hTS y (hball hy)]
    rw [hHval]
    exact hle y hysph
  -- Apply the comparison criterion on the open set `Ω''`.
  have hmain := subharmonic_le_harmonic_on_open (Ω := Ω) (Ω' := Ω'') hΩ hcont hMVP
    hΩ''open hΩ''conn hΩ''bdd hclosure hHharm hHcont hbd
  intro z hz
  have hz'' : T z ∈ Ω'' := by
    rw [hΩ''def]
    exact ⟨z, hz, rfl⟩
  calc v (T z) ≤ H (T z) := hmain (T z) hz''
    _ = h z := by
        change h (S (T z)) = h z
        rw [hTS z (hBΩ' hz)]

/-- **Subharmonicity is preserved by a biholomorphism.**  Let `Ω, Ω' ⊆ ℂ` be open, let
`v : ℂ → ℝ` be continuous on `Ω` and satisfy the circle mean-value inequality at every point
of `Ω`, and let `T : Ω' → Ω` be a biholomorphism (with inverse `S : Ω → Ω'`; the hypotheses
below say that `T, S` are mutually inverse bijections between `Ω'` and `Ω` which are
continuous and complex analytic).  Then `v ∘ T` is continuous on `Ω'` and satisfies the
circle mean-value inequality at every point of `Ω'`. -/
theorem circleMeanValue_ge_comp_biholo {Ω Ω' : Set ℂ} (hΩ : IsOpen Ω) (hΩ' : IsOpen Ω')
    {v : ℂ → ℝ} (hcont : ContinuousOn v Ω)
    (hMVP : ∀ p ∈ Ω, ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Ω →
      v p ≤ Real.circleAverage v p r)
    {T S : ℂ → ℂ} (hTmap : Set.MapsTo T Ω' Ω) (hSmap : Set.MapsTo S Ω Ω')
    (hTS : ∀ z ∈ Ω', S (T z) = z) (hST : ∀ w ∈ Ω, T (S w) = w)
    (hTcont : ContinuousOn T Ω') (hScont : ContinuousOn S Ω)
    (hTana : AnalyticOnNhd ℂ T Ω') (hSana : AnalyticOnNhd ℂ S Ω) :
    ContinuousOn (v ∘ T) Ω' ∧
      ∀ p ∈ Ω', ∀ r : ℝ, 0 < r → Metric.closedBall p r ⊆ Ω' →
        (v ∘ T) p ≤ Real.circleAverage (v ∘ T) p r := by
  constructor
  · exact hcont.comp hTcont hTmap
  · intro p hp r hr hball
    have hcompcont : ContinuousOn (v ∘ T) Ω' := hcont.comp hTcont hTmap
    refine circleAverage_ge_of_le_harmonic (Ω := Ω') hΩ' hcompcont ?_ hr hball
    intro p' r' hr' hball' h hharm hcont_h hle
    refine subharmonic_le_harmonic_comp_biholo (Ω := Ω) (Ω' := Ω') hΩ hcont hMVP
      hTmap hSmap hTS hST hTcont hScont hTana hSana hr' hball' hharm hcont_h ?_
    intro z hz
    exact hle z hz

end Commons.Analysis.Complex.Harmonic
