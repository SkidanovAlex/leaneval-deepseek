import Mathlib
import Submission.Work.Drive.sweepFamOf
import Submission.Work.Drive.chordSweepDefs

namespace Work.Drive

/-- **A pointwise local cone on a compact window is uniform (compactness).**  Let `Γ` be a
`period`-periodic family of loops.  Suppose at every point `(σ₀, t₀)` of the box
`[a,b] × [0,period]` there are a direction `n`, a radius `ε > 0` and a rate `c > 0` such that the
loop `Γ s` grows at least at rate `c` in the direction `n` over the `t`-window `[t₀-ε, t₀+ε]`,
uniformly for `s ∈ [σ₀-ε, σ₀+ε]`.  Then a *single* radius `ε > 0` and a *single* rate `c > 0` work
for the whole box — the direction `n` may still depend on `(σ, t₀)`, and the conclusion covers
*all* real `t₀` by periodicity (no continuity of `Γ` is needed).

Proof route for the prover: `period_pos : 0 < period` (so the box is nonempty as `a ≤ b`);
`[a,b] × [0,period]` is compact; cover it by the open boxes
`(σ₀-ε_p/2, σ₀+ε_p/2) × (t₀-ε_p/2, t₀+ε_p/2)` (`Metric.ball`), extract a finite subcover with
`IsCompact.elim_finite_subcover`, and take `ε := ½·min`, `c := min` of the finitely many data
(`Finset.inf'`/`Finset.min'`, nonempty since the box is nonempty).  For a general real `t₀`, take
`k : ℤ` with `t₀ - k·period ∈ [0,period]` (e.g. `k = ⌊t₀/period⌋`), apply the finite-cover
statement at `(σ, t₀ - k·period)` and shift `t₁, t₂` by `k·period`, using `hper`. -/
theorem uniformCone_of_localCone {Γ : ℝ → ℝ → LeanEval.KnotTheory.Quadrisecant.Space}
    (hper : ∀ s t : ℝ, Γ s (t + LeanEval.KnotTheory.Quadrisecant.period) = Γ s t)
    {a b : ℝ} (hab : a ≤ b)
    (hloc : ∀ σ₀ ∈ Set.Icc a b, ∀ t₀ ∈ Set.Icc (0 : ℝ) LeanEval.KnotTheory.Quadrisecant.period,
      ∃ (n : LeanEval.KnotTheory.Quadrisecant.Space) (ε c : ℝ), 0 < ε ∧ 0 < c ∧
      ∀ s ∈ Set.Icc (σ₀ - ε) (σ₀ + ε), ∀ t₁ t₂ : ℝ, t₀ - ε ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ t₀ + ε →
        c * (t₂ - t₁) ≤ inner ℝ n (Γ s t₂ - Γ s t₁)) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∀ σ ∈ Set.Icc a b, ∀ t₀ : ℝ,
      ∃ n : LeanEval.KnotTheory.Quadrisecant.Space, ∀ s ∈ Set.Icc (σ - ε) (σ + ε),
      ∀ t₁ t₂ : ℝ, t₀ - ε ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ t₀ + ε →
        c * (t₂ - t₁) ≤ inner ℝ n (Γ s t₂ - Γ s t₁) := by
  classical
  -- `period = 2π > 0`, so the box `[a,b] × [0,period]` is nonempty.
  have hperiod_pos : 0 < LeanEval.KnotTheory.Quadrisecant.period := by
    rw [LeanEval.KnotTheory.Quadrisecant.period]; positivity
  have hperne : LeanEval.KnotTheory.Quadrisecant.period ≠ 0 := ne_of_gt hperiod_pos
  let K : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc (0 : ℝ) LeanEval.KnotTheory.Quadrisecant.period
  -- The local data, viewed as a function of a point of the box.
  have hgood : ∀ i : K, ∃ (n : LeanEval.KnotTheory.Quadrisecant.Space) (ε c : ℝ),
      0 < ε ∧ 0 < c ∧
      ∀ s ∈ Set.Icc (i.1.1 - ε) (i.1.1 + ε), ∀ t₁ t₂ : ℝ, i.1.2 - ε ≤ t₁ → t₁ ≤ t₂ →
        t₂ ≤ i.1.2 + ε → c * (t₂ - t₁) ≤ inner ℝ n (Γ s t₂ - Γ s t₁) := by
    intro i
    exact hloc i.1.1 i.2.1 i.1.2 i.2.2
  choose nF εF cF hεF hcF hlocF using hgood
  -- The box is compact, and covered by the open boxes of half the local radii.
  have hKcomp : IsCompact K := isCompact_Icc.prod isCompact_Icc
  let U : K → Set (ℝ × ℝ) :=
    fun i => Metric.ball (i.1.1) (εF i / 2) ×ˢ Metric.ball (i.1.2) (εF i / 2)
  have hUopen : ∀ i : K, IsOpen (U i) := fun i => Metric.isOpen_ball.prod Metric.isOpen_ball
  have hcover : K ⊆ ⋃ i : K, U i := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⟨x, hx⟩, ?_⟩
    exact ⟨Metric.mem_ball_self (by have := hεF ⟨x, hx⟩; linarith),
           Metric.mem_ball_self (by have := hεF ⟨x, hx⟩; linarith)⟩
  obtain ⟨t, ht⟩ := hKcomp.elim_finite_subcover U hUopen hcover
  have hKne : K.Nonempty := ⟨(a, 0), ⟨⟨le_rfl, hab⟩, ⟨le_rfl, hperiod_pos.le⟩⟩⟩
  have htne : t.Nonempty := by
    obtain ⟨x, hx⟩ := hKne
    rcases Set.mem_iUnion₂.1 (ht hx) with ⟨j, hj, -⟩
    exact ⟨j, hj⟩
  -- The uniform radius and rate: the minima of the finitely many data.
  let ε₀ : ℝ := t.inf' htne (fun j => εF j / 2)
  let c₀ : ℝ := t.inf' htne cF
  have hε₀ : 0 < ε₀ := by
    change 0 < t.inf' htne (fun j => εF j / 2)
    rw [Finset.lt_inf'_iff]
    intro j _
    have := hεF j
    linarith
  have hc₀ : 0 < c₀ := by
    change 0 < t.inf' htne cF
    rw [Finset.lt_inf'_iff]
    exact fun j _ => hcF j
  have hεle : ∀ j ∈ t, ε₀ ≤ εF j / 2 := by
    intro j hj
    change t.inf' htne (fun j => εF j / 2) ≤ εF j / 2
    exact Finset.inf'_le (fun j => εF j / 2) hj
  have hcle : ∀ j ∈ t, c₀ ≤ cF j := by
    intro j hj
    change t.inf' htne cF ≤ cF j
    exact Finset.inf'_le cF hj
  refine ⟨ε₀, c₀, hε₀, hc₀, ?_⟩
  intro σ hσ t₀
  -- Integer periodicity, so that we may reduce `t₀` modulo `period`.
  have hshift : ∀ (s u : ℝ) (k : ℤ),
      Γ s (u + (k : ℝ) * LeanEval.KnotTheory.Quadrisecant.period) = Γ s u := by
    intro s u k
    exact (Function.Periodic.int_mul (fun x => hper s x) k) u
  -- Reduce `t₀` to the fundamental window `[0,period]`.
  set m : ℤ := ⌊t₀ / LeanEval.KnotTheory.Quadrisecant.period⌋ with hm
  set τ : ℝ := t₀ - (m : ℝ) * LeanEval.KnotTheory.Quadrisecant.period with hτ
  have hmfloor : (m : ℝ) ≤ t₀ / LeanEval.KnotTheory.Quadrisecant.period := by
    rw [hm]; exact Int.floor_le _
  have hmfloor' : t₀ / LeanEval.KnotTheory.Quadrisecant.period < (m : ℝ) + 1 := by
    rw [hm]; exact Int.lt_floor_add_one _
  have hτnonneg : 0 ≤ τ := by
    have hmul : (m : ℝ) * LeanEval.KnotTheory.Quadrisecant.period ≤ t₀ := by
      calc (m : ℝ) * LeanEval.KnotTheory.Quadrisecant.period
          ≤ (t₀ / LeanEval.KnotTheory.Quadrisecant.period)
              * LeanEval.KnotTheory.Quadrisecant.period :=
            mul_le_mul_of_nonneg_right hmfloor hperiod_pos.le
        _ = t₀ := div_mul_cancel₀ t₀ hperne
    rw [hτ]; linarith
  have hτlt : τ < LeanEval.KnotTheory.Quadrisecant.period := by
    have hmul : t₀ < ((m : ℝ) + 1) * LeanEval.KnotTheory.Quadrisecant.period := by
      have h := mul_lt_mul_of_pos_right hmfloor' hperiod_pos
      rwa [div_mul_cancel₀ t₀ hperne] at h
    have hexp : ((m : ℝ) + 1) * LeanEval.KnotTheory.Quadrisecant.period
        = (m : ℝ) * LeanEval.KnotTheory.Quadrisecant.period
          + LeanEval.KnotTheory.Quadrisecant.period := by ring
    rw [hτ]; linarith
  have hτmem : τ ∈ Set.Icc (0 : ℝ) LeanEval.KnotTheory.Quadrisecant.period :=
    ⟨hτnonneg, le_of_lt hτlt⟩
  -- Find the element of the finite cover whose box contains `(σ, τ)`.
  have hKmem : (σ, τ) ∈ K := ⟨hσ, hτmem⟩
  obtain ⟨j, hj, hxj⟩ := Set.mem_iUnion₂.1 (ht hKmem)
  have hxj' : (σ, τ) ∈ Metric.ball j.1.1 (εF j / 2) ×ˢ Metric.ball j.1.2 (εF j / 2) := hxj
  have hσball : σ ∈ Metric.ball j.1.1 (εF j / 2) := hxj'.1
  have hτball : τ ∈ Metric.ball j.1.2 (εF j / 2) := hxj'.2
  rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_lt] at hσball hτball
  obtain ⟨hσlo, hσhi⟩ := hσball
  obtain ⟨hτlo, hτhi⟩ := hτball
  refine ⟨nF j, ?_⟩
  intro s hs t₁ t₂ h1 h2 h3
  have hεlej := hεle j hj
  have hclej := hcle j hj
  -- The window at `σ` of the conclusion sits inside the local `s`-window of `j`.
  have hs' : s ∈ Set.Icc (j.1.1 - εF j) (j.1.1 + εF j) := by
    refine ⟨?_, ?_⟩
    · linarith [hs.1, hσlo]
    · linarith [hs.2, hσhi]
  -- The shifted `t`-window sits inside the local `t`-window of `j`.
  have hu1 : j.1.2 - εF j ≤ t₁ - (m : ℝ) * LeanEval.KnotTheory.Quadrisecant.period := by
    linarith [h1, hτlo, hεlej, hτ]
  have hu2 : t₁ - (m : ℝ) * LeanEval.KnotTheory.Quadrisecant.period
      ≤ t₂ - (m : ℝ) * LeanEval.KnotTheory.Quadrisecant.period := by linarith [h2]
  have hu3 : t₂ - (m : ℝ) * LeanEval.KnotTheory.Quadrisecant.period ≤ j.1.2 + εF j := by
    linarith [h3, hτhi, hεlej, hτ]
  have hlocj := hlocF j s hs' (t₁ - (m : ℝ) * LeanEval.KnotTheory.Quadrisecant.period)
      (t₂ - (m : ℝ) * LeanEval.KnotTheory.Quadrisecant.period) hu1 hu2 hu3
  -- Undo the shift using `period`-periodicity (for integer multiples).
  have e₁ : Γ s (t₁ - (m : ℝ) * LeanEval.KnotTheory.Quadrisecant.period) = Γ s t₁ := by
    have h := hshift s (t₁ - (m : ℝ) * LeanEval.KnotTheory.Quadrisecant.period) m
    have harg : (t₁ - (m : ℝ) * LeanEval.KnotTheory.Quadrisecant.period)
        + (m : ℝ) * LeanEval.KnotTheory.Quadrisecant.period = t₁ := by ring
    rw [harg] at h
    exact h.symm
  have e₂ : Γ s (t₂ - (m : ℝ) * LeanEval.KnotTheory.Quadrisecant.period) = Γ s t₂ := by
    have h := hshift s (t₂ - (m : ℝ) * LeanEval.KnotTheory.Quadrisecant.period) m
    have harg : (t₂ - (m : ℝ) * LeanEval.KnotTheory.Quadrisecant.period)
        + (m : ℝ) * LeanEval.KnotTheory.Quadrisecant.period = t₂ := by ring
    rw [harg] at h
    exact h.symm
  rw [e₁, e₂] at hlocj
  have harg2 : (t₂ - (m : ℝ) * LeanEval.KnotTheory.Quadrisecant.period)
      - (t₁ - (m : ℝ) * LeanEval.KnotTheory.Quadrisecant.period) = t₂ - t₁ := by ring
  rw [harg2] at hlocj
  have hmono : c₀ * (t₂ - t₁) ≤ cF j * (t₂ - t₁) :=
    mul_le_mul_of_nonneg_right hclej (by linarith)
  linarith

end Work.Drive
