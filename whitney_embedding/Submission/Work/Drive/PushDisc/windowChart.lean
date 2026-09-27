import Mathlib
import Submission.Work.Drive.PushDisc.asymAnchor
import Submission.Work.Drive.PushDisc.asymChart
import Submission.Work.Drive.PushDisc.asymAmplitudesSolid

/-!
# The repaired chart data of the Whitney disc, and the bridge to `AsymChartData`

**Status and relation to `asymChartDataOfWhitneyChartRepair.lean`.**  The file
`Submission/Work/Drive/PushDisc/asymChartDataOfWhitneyChartRepair.lean` contains the same structure and
the same bridge proof, but it **does not compile** any more: it was written against the model-side
definitions (`asymShift`, `asymDisc`, `isCompact_asymDisc`, `asymShift_close_anchor`) that lived in the
later-reverted `asymChartDataOfWhitneyChart.lean`.  Those definitions are reconstructed, with proofs,
in `Drive/PushDisc/asymAnchor.lean` (imported here), and this file re-creates the structure and the
bridge on top of them, with the estimate's interface adapted to `asymShift_close_anchor`.  This file
supersedes the repair file; do not import both.

## The interface

`Work.Drive.PushDisc.WhitneyChartWindowData n f W p₁ p₂ q₁ q₂` is the chart of the Whitney disc:

* global coordinates `Φ, Θ`;
* the **second sheet** is a graph over the `(x,v)`-window (`σ₂`, `h`), with a core height `c` that
  vanishes at `±1`, is positive between them and negative outside (the opposite-sign condition);
* the **geometric row** `hiso`: near the model disc `asymDisc k c` the image of `f` comes only from
  the plane `{y = 0, v = 0}` and from the finger.  This is the "no new intersections" content of the
  Whitney move, i.e. the cleanliness of the Whitney disc, transported into the chart.

Nothing else in the interface is geometric: the amplitudes, the height condition `havoid`, the `Oo`
rows and the swept row `hswept` are all *bookkeeping*, and `nonempty_asymChartData_of_windowData`
below performs it.

## Main results

* `Work.Drive.PushDisc.WhitneyChartWindowData` — the structure;
* `Work.Drive.PushDisc.nonempty_asymChartData_of_windowData` — the bridge to `AsymChartData`;
* `Work.Drive.PushDisc.WhitneyChartWindowAll` — the `∀`-configurations form;
* `Work.Drive.PushDisc.asymChartAll_of_windowChartAll` — the element-wise assembly.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff
open Set Metric

/-- **The isolation criterion on the model.**  A compact set inside an open set has a ball around it
inside the open set. -/
theorem exists_ball_subset_of_isCompact_subset_isOpen {E : Type*} [PseudoMetricSpace E]
    {A V : Set E} (hAc : IsCompact A) (hVo : IsOpen V) (hAV : A ⊆ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : E, (∃ a ∈ A, dist x a < δ) → x ∈ V := by
  obtain ⟨δ, hδ, hsub⟩ := hAc.exists_cthickening_subset_open hVo hAV
  refine ⟨δ, hδ, fun x hx => hsub ?_⟩
  rw [Metric.mem_cthickening_iff]
  obtain ⟨a, ha, hd⟩ := hx
  refine le_trans (Metric.infEDist_le_edist_of_mem ha) ?_
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal hd.le

/-- **The bridge from an anchor estimate to the swept row.** -/
theorem hswept_of_anchor_estimate {k : ℕ} {M : Type*}
    (Φ : EuclideanSpace ℝ (Fin (2 * (k + 1))) → Work.Drive.Whitney.Mdl k)
    (Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (hΦΘ : ∀ ξ : Work.Drive.Whitney.Mdl k, Φ (Θ ξ) = ξ)
    (f : M → EuclideanSpace ℝ (Fin (2 * (k + 1))))
    (U₁ W₀ : Set M) (V A : Set (Work.Drive.Whitney.Mdl k)) (ρ : ℝ)
    (hballV : ∀ ξ : Work.Drive.Whitney.Mdl k, (∃ a ∈ A, dist ξ a < ρ) → ξ ∈ V)
    (hiso : ∀ z : M, Φ (f z) ∈ V → z ∈ U₁ ∪ W₀)
    (hh : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k))
    (m l : ℝ → ℝ) (X' : ℝ)
    (hest : ∀ p ∈ asymReg k X', 2 * m p.1 * l (‖p.2‖ ^ 2) ≠ 0 →
      ∃ a ∈ A, dist (asymShift m l hh p) a < ρ)
    {p : ℝ × EuclideanSpace ℝ (Fin k)} (hp : p ∈ asymReg k X')
    (hs : 2 * m p.1 * l (‖p.2‖ ^ 2) ≠ 0) :
    ∀ z : M, f z = Θ (p.1, (hh p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2), (hh p).2, p.2) →
      z ∈ U₁ ∪ W₀ := by
  intro z hz
  refine hiso z ?_
  have hΦ : Φ (f z) = asymShift m l hh p := by
    rw [hz]
    exact hΦΘ _
  rw [hΦ]
  exact hballV _ (hest p hp hs)

/-- **The window selection.**  The core height `c` vanishes at `±1`, so the window of the amplitude
can be taken arbitrarily close to `1` while keeping `|c x| ≤ η/2` on the annulus `1 ≤ |x| ≤ X`. -/
theorem exists_window_close_core {c : ℝ → ℝ} (hc : Continuous c)
    (hcm : c (-1) = 0) (hc1 : c 1 = 0) {X' η : ℝ} (hX' : 1 < X') (hη : 0 < η) :
    ∃ X : ℝ, 1 < X ∧ X < X' ∧ X - 1 ≤ η / 2 ∧
      ∀ x : ℝ, 1 ≤ |x| → |x| ≤ X → |c x| ≤ η / 2 := by
  have hη2 : 0 < η / 2 := by linarith
  obtain ⟨δ₁, hδ₁, h₁⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x - 1| < δ → |c x| < η / 2 := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := (1 : ℝ))) (η / 2) hη2
    refine ⟨δ, hδ, fun x hx => ?_⟩
    have hx' : dist x (1 : ℝ) < δ := by rw [Real.dist_eq]; exact hx
    have h' := h hx'
    rw [Real.dist_eq, hc1, sub_zero] at h'
    exact h'
  obtain ⟨δ₂, hδ₂, h₂⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ x : ℝ, |x + 1| < δ → |c x| < η / 2 := by
    obtain ⟨δ, hδ, h⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x := (-1 : ℝ))) (η / 2) hη2
    refine ⟨δ, hδ, fun x hx => ?_⟩
    have hx' : dist x (-1 : ℝ) < δ := by rw [Real.dist_eq, sub_neg_eq_add]; exact hx
    have h' := h hx'
    rw [Real.dist_eq, hcm, sub_zero] at h'
    exact h'
  set e : ℝ := min δ₁ δ₂ with hedef
  have he : 0 < e := lt_min hδ₁ hδ₂
  have he₁ : e ≤ δ₁ := by rw [hedef]; exact min_le_left _ _
  have he₂ : e ≤ δ₂ := by rw [hedef]; exact min_le_right _ _
  set m0 : ℝ := min (min (1 + e) X') (1 + η / 2) with hm0def
  have hm0e : m0 ≤ 1 + e := by
    rw [hm0def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hm0X' : m0 ≤ X' := by
    rw [hm0def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hm0η : m0 ≤ 1 + η / 2 := by rw [hm0def]; exact min_le_right _ _
  have hm01 : 1 < m0 := by
    rw [hm0def]; exact lt_min (lt_min (by linarith) hX') (by linarith)
  refine ⟨(1 + m0) / 2, by linarith, by linarith, by linarith, ?_⟩
  intro x hx1 hxX
  have hxlt : |x| < 1 + e := by
    have h : (1 + m0) / 2 < 1 + e := by linarith
    linarith
  by_cases hx : 0 ≤ x
  · have hxabs : |x| = x := abs_of_nonneg hx
    have h : |x - 1| < δ₁ := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - 1)]
      have h2 : x < 1 + e := by rw [hxabs] at hxlt; exact hxlt
      linarith
    exact le_of_lt (h₁ x h)
  · have hx' : x < 0 := not_le.mp hx
    have hxabs : |x| = -x := abs_of_neg hx'
    have h : |x + 1| < δ₂ := by
      have h1' : x + 1 ≤ 0 := by linarith
      rw [abs_of_nonpos h1']
      have h2 : -x < 1 + e := by rw [← hxabs]; exact hxlt
      linarith
    exact le_of_lt (h₂ x h)

/-- **The repaired chart data of the Whitney disc.**  See the module docstring. -/
structure WhitneyChartWindowData (n : ℕ) {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M) where
  k : ℕ
  hk : n = k + 1
  /-- the half-width of the `(x,v)`-window -/
  X' : ℝ
  hX' : 1 < X'
  /-- the coordinates of the ambient space -/
  Φ : EuclideanSpace ℝ (Fin (2 * n)) → Work.Drive.Whitney.Mdl k
  Θ : Work.Drive.Whitney.Mdl k → EuclideanSpace ℝ (Fin (2 * n))
  hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ
  hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ
  hΘΦ : ∀ y : EuclideanSpace ℝ (Fin (2 * n)), Θ (Φ y) = y
  hΦΘ : ∀ ξ : Work.Drive.Whitney.Mdl k, Φ (Θ ξ) = ξ
  /-- the height of the second sheet over the `(x,v)`-window -/
  h : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k)
  hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (asymReg k X')
  /-- the parametrisation of the finger by the `(x,v)`-coordinates -/
  σ₂ : ℝ × EuclideanSpace ℝ (Fin k) → M
  hσ₂ : ∀ p ∈ asymReg k X', f (σ₂ p) = Θ (p.1, (h p).1, (h p).2, p.2)
  hp₂ : σ₂ ((-1 : ℝ), 0) = p₂
  hq₂ : σ₂ ((1 : ℝ), 0) = q₂
  hW₀o : ∀ X'' : ℝ, 1 < X'' → X'' ≤ X' → IsOpen (σ₂ '' asymReg k X'')
  hW₀W : σ₂ '' asymReg k X' ⊆ W
  /-- the height of the core of the finger -/
  c : ℝ → ℝ
  hcsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c
  hcore : ∀ x : ℝ, |x| < X' → h (x, 0) = (c x, 0)
  hlip : ∃ L : ℝ, 0 ≤ L ∧ ∀ p ∈ asymReg k X',
    ‖h p - (c p.1, 0)‖ ≤ L * ‖p.2‖
  hcm : c (-1) = 0
  hc1 : c 1 = 0
  hcpos : ∀ x : ℝ, |x| < 1 → 0 < c x
  hcneg : ∀ x : ℝ, 1 < |x| → |x| < X' → c x < 0
  hfrontier : ∀ X'' : ℝ, 1 < X'' → X'' ≤ X' →
    ∀ x ∈ frontier (σ₂ '' asymReg k X''),
      |(Φ (f x)).1| = X'' ∨ ‖(Φ (f x)).2.2.2‖ = 1
  /-- **the geometric row**: near the model disc the image of `f` comes only from the plane
  `{y = 0, v = 0}` and from the finger.  This is the "no new intersections" content of the Whitney
  move (the cleanliness of the Whitney disc). -/
  hiso : ∃ V : Set (Work.Drive.Whitney.Mdl k), IsOpen V ∧ asymDisc k c ⊆ V ∧
    ∀ z : M, Φ (f z) ∈ V →
      ((Φ (f z)).2.1 = 0 ∧ (Φ (f z)).2.2.2 = 0) ∨ z ∈ σ₂ '' asymReg k X'
  /-- the coordinates of the two double points on the first sheet -/
  hp₁c : f p₁ = Θ ((-1 : ℝ), 0, 0, 0)
  hq₁c : f q₁ = Θ ((1 : ℝ), 0, 0, 0)

/-- **The bridge.**  The rows of `WhitneyChartWindowData` produce the one-sided normal form
`AsymChartData`: the window `X` is chosen close to `1` (`exists_window_close_core`), the isolation
radius of the model disc gives the size `η` of the amplitude, `asymAmplitudesSolid` produces `m, l`,
`asymShift_close_anchor` places every moved value within `η/2 + L ε + ε` of the model disc, `hiso`
catches the preimages, and the remaining rows are those of the input. -/
theorem nonempty_asymChartData_of_windowData {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    {f : M → EuclideanSpace ℝ (Fin (2 * n))} {W : Set M} {p₁ p₂ q₁ q₂ : M}
    (E : WhitneyChartWindowData n f W p₁ p₂ q₁ q₂) :
    Nonempty (Work.Drive.PushDisc.AsymChartData n f W p₁ p₂ q₁ q₂) := by
  obtain ⟨k, hk, X', hX', Φ, Θ, hΦsm, hΘsm, hΘΦ, hΦΘ, h, hh, σ₂, hσ₂, hp₂, hq₂, hW₀o,
    hW₀W, c, hcsm, hcore, hlip, hcm, hc1, hcpos, hcneg, hfrontier, hiso, hp₁c, hq₁c⟩ := E
  subst hk
  obtain ⟨V, hVo, hAV, hisoV⟩ := hiso
  obtain ⟨L, hLnn, hLip⟩ := hlip
  -- the maximal tube: the preimage of the plane `{y = 0, v = 0}`
  set U₁ : Set M := {z : M | (Φ (f z)).2.1 = 0 ∧ (Φ (f z)).2.2.2 = 0} with hU₁def
  -- the anchor is compact, and the isolation radius of the anchor
  have hAc : IsCompact (asymDisc k c) := isCompact_asymDisc hcsm.continuous
  obtain ⟨δ, hδpos, hδball⟩ := exists_ball_subset_of_isCompact_subset_isOpen hAc hVo hAV
  -- the size of the amplitude and of the `v`-window
  set η : ℝ := δ / 4 with hηdef
  have hηpos : 0 < η := by rw [hηdef]; linarith
  set ε : ℝ := min (1 / 2) (δ / (8 * (L + 1))) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact lt_min (by norm_num) (by positivity)
  have hε2 : ε ≤ 1 / 2 := by rw [hεdef]; exact min_le_left _ _
  have hεsmall : 2 * L * ε + ε < 5 * δ / 8 := by
    have h1 : ε ≤ δ / (8 * (L + 1)) := by rw [hεdef]; exact min_le_right _ _
    have h2 : 0 < L + 1 := by linarith
    have h3 : ε * (2 * L + 1) ≤ δ / (8 * (L + 1)) * (2 * L + 1) :=
      mul_le_mul_of_nonneg_right h1 (by linarith)
    have h4 : δ / (8 * (L + 1)) * (2 * L + 1) ≤ δ / 4 := by
      have h7 : δ / (8 * (L + 1)) * (2 * (L + 1)) = δ / 4 := by
        have h8 : (8 : ℝ) * (L + 1) ≠ 0 := by positivity
        field_simp
        ring
      calc δ / (8 * (L + 1)) * (2 * L + 1)
          ≤ δ / (8 * (L + 1)) * (2 * (L + 1)) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = δ / 4 := h7
    have h5 : 2 * L * ε + ε = ε * (2 * L + 1) := by ring
    rw [h5]
    linarith
  -- the window
  obtain ⟨X, h1X, hXX', hXclose, hXsup⟩ := exists_window_close_core hcsm.continuous hcm hc1 hX' hηpos
  -- the two quantitative rows of the amplitude's hypothesis
  have hcη : ∀ x : ℝ, |x| ≤ X → -η / 2 ≤ c x := by
    intro x hx
    rcases lt_or_ge |x| 1 with hlt | hge
    · have h1 : 0 ≤ c x := le_of_lt (hcpos x hlt)
      linarith
    · have h2 : |c x| ≤ η / 2 := hXsup x hge hx
      have h3 : -|c x| ≤ c x := neg_abs_le _
      linarith
  have hcnegX : ∀ x : ℝ, 1 < |x| → |x| < X → c x < 0 :=
    fun x h1 h2 => hcneg x h1 (lt_trans h2 hXX')
  -- the amplitudes
  obtain ⟨m, l, hm, hl, hmnn, hlnn, hmzero, hl0, hl1, hlhalf, hlε, hmlt, hrow⟩ :=
    asymAmplitudesSolid hcsm h1X hηpos hεpos hε2 hcnegX hcη
  -- the Lipschitz rows in coordinates
  have hlip1 : ∀ q : ℝ × EuclideanSpace ℝ (Fin k), |q.1| < X → ‖q.2‖ < 1 →
      |(h q).1 - c q.1| ≤ L * ‖q.2‖ := by
    intro q hq1 hq2
    have hq : q ∈ asymReg k X' := ⟨lt_trans hq1 hXX', hq2⟩
    have hLq : ‖h q - (c q.1, 0)‖ ≤ L * ‖q.2‖ := hLip q hq
    have h2 : ‖(h q - (c q.1, 0)).1‖ ≤ L * ‖q.2‖ := le_trans (norm_fst_le _) hLq
    simpa using h2
  have hlip2 : ∀ q : ℝ × EuclideanSpace ℝ (Fin k), |q.1| < X → ‖q.2‖ < 1 →
      ‖(h q).2‖ ≤ L * ‖q.2‖ := by
    intro q hq1 hq2
    have hq : q ∈ asymReg k X' := ⟨lt_trans hq1 hXX', hq2⟩
    have hLq : ‖h q - (c q.1, 0)‖ ≤ L * ‖q.2‖ := hLip q hq
    have h2 : ‖(h q - (c q.1, 0)).2‖ ≤ L * ‖q.2‖ := le_trans (norm_snd_le _) hLq
    simpa using h2
  -- the anchor estimate at the isolation radius
  have hest : ∀ p ∈ asymReg k X', 2 * m p.1 * l (‖p.2‖ ^ 2) ≠ 0 →
      ∃ a ∈ asymDisc k c, dist (asymShift m l h p) a < δ := by
    intro p hp hs
    have hmne : m p.1 ≠ 0 := fun h0 => hs (by rw [h0]; ring)
    have hp1 : |p.1| < X := by
      by_contra hcon
      exact hmne (hmzero p.1 (not_lt.mp hcon))
    have hp2 : ‖p.2‖ < 1 := hp.2
    obtain ⟨η₀, hη₀, hη₀b⟩ := asymShift_close_anchor h1X hXclose hηpos hεpos hLnn hcm hc1
      (fun x hx => le_of_lt (hcpos x hx)) hcnegX hcη hmnn hlnn hl1 hmzero hlε hrow hlip1 hlip2
      hp1 hp2 hs
    refine ⟨η₀, hη₀, lt_of_le_of_lt hη₀b ?_⟩
    rw [hηdef] at hη₀b ⊢
    have hLεnn : 0 ≤ L * ε := mul_nonneg hLnn hεpos.le
    linarith
  -- the swept row, from the geometric row `hiso`
  have hswept : ∀ p ∈ asymReg k X', 2 * m p.1 * l (‖p.2‖ ^ 2) ≠ 0 → ∀ z : M,
      f z = Θ (p.1, (h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2), (h p).2, p.2) →
      z ∈ U₁ ∪ σ₂ '' asymReg k X' := by
    intro p hp hs z hz
    exact hswept_of_anchor_estimate Φ Θ hΦΘ f U₁ (σ₂ '' asymReg k X') V (asymDisc k c) δ
      hδball (fun z' hz' => by
        rcases hisoV z' hz' with h | h
        · left; rw [hU₁def]; exact h
        · right; exact h)
      h m l X' hest hp hs z hz
  -- the height condition on the core
  have havoid : ∀ x : ℝ, |x| < X' → (h (x, 0)).1 ≠ 2 * m x * l 0 := by
    intro x hx hcon
    have hcorex : (h (x, 0)).1 = c x := by rw [hcore x hx]
    rw [hcorex, hl0, mul_one] at hcon
    rcases lt_or_ge |x| X with hlt | hge
    · exact absurd hcon (ne_of_lt (hmlt x hlt))
    · have hmx : m x = 0 := hmzero x hge
      have hzero : c x = 0 := by
        have h2 : 2 * m x = 0 := by rw [hmx]; ring
        rw [h2] at hcon
        exact hcon
      have hlt : c x < 0 := hcneg x (lt_of_lt_of_le h1X hge) hx
      linarith
  -- the `Oo` rows
  have hfr : ∀ x ∈ frontier (σ₂ '' asymReg k X'),
      X < |(Φ (f x)).1| ∨ 1 / 2 < ‖(Φ (f x)).2.2.2‖ ^ 2 := by
    intro y hy
    rcases hfrontier X' hX' le_rfl y hy with h | h
    · left; rw [h]; exact hXX'
    · right; rw [h]; norm_num
  obtain ⟨Oo, hOo, hOfix, hOfront⟩ :=
    exists_asymOo_rows (k := k) f m l X X' hXX' hmzero hlhalf Φ Θ hΘΦ σ₂ hfr
  refine ⟨k, rfl, X, X', h1X, hXX', m, l, hm, hl, hmnn, hlnn, hmzero, hlhalf, ?_, U₁, Φ, Θ,
    hΦsm, hΘsm, hΘΦ, hΦΘ, h, hh, σ₂, hσ₂, hp₂, hq₂, hW₀o X' hX' le_rfl, hW₀W, Oo, hOo, hOfix,
    hOfront, ?_, hswept, havoid, hp₁c, hq₁c⟩
  · rw [hl0]; norm_num
  · intro z hz
    rw [hU₁def] at hz
    exact hz


/-- **The chart of the Whitney disc exists for every configuration of the target.**  This is the form
in which the general-position construction of the Whitney disc and its framing (where the
opposite-sign hypothesis `OppositeType` is spent) have to deliver the geometric input of the compact
`n ≥ 3` case; `asymChartAll_of_windowChartAll` below converts it into `AsymChartAll` and hence, by the
proved `hasPushSignedSmooth_of_asymChartAll`, into the target `Work.Drive.HasPushSignedSmooth`. -/
def WhitneyChartWindowAll (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] : Prop :=
  ∀ (hn : 3 ≤ n) (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ q₁ q₂ : M)
    (hW₁ : p₁ ∈ W) (hW₂ : p₂ ∈ W) (hW₃ : q₁ ∈ W) (hW₄ : q₂ ∈ W)
    (hp₁p₂ : p₁ ≠ p₂) (hq₁q₂ : q₁ ≠ q₂)
    (hp₁q₁ : p₁ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hp₂q₁ : p₂ ≠ q₁) (hp₂q₂ : p₂ ≠ q₂)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (htransP : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = ⊤)
    (htransQ : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂).range = ⊤)
    (γ₁ γ₂ : ℝ → M) (hγ₁ : Continuous γ₁) (hγ₂ : Continuous γ₂)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1))
    (hγ₁smooth : ContMDiff 𝓘(ℝ, ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂smooth : ContMDiff 𝓘(ℝ, ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (hγ₁imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv 𝓘(ℝ, ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₁ t))
    (hγ₂imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv 𝓘(ℝ, ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₂ t))
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hsign : Work.Whitney.OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂),
    Nonempty (WhitneyChartWindowData n f W p₁ p₂ q₁ q₂)

/-- **The `∀`-configurations assembly**: the chart of the Whitney disc for every configuration gives
the one-sided normal form for every configuration.  Element-wise this is
`nonempty_asymChartData_of_windowData`. -/
theorem asymChartAll_of_windowChartAll {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (h : WhitneyChartWindowAll n M) : Work.Drive.PushDisc.AsymChartAll n M := by
  intro hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂ hp₁q₁ hp₁q₂
    hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
    hγW₁ hγW₂ hγ₁inj hγ₂inj hγ₁smooth hγ₂smooth hγ₁imm hγ₂imm hγdisj hγend hsign
  obtain ⟨D⟩ := h hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂
    hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂ hp₁q₁ hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ
    γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hγW₁ hγW₂ hγ₁inj hγ₂inj hγ₁smooth hγ₂smooth hγ₁imm
    hγ₂imm hγdisj hγend hsign
  exact nonempty_asymChartData_of_windowData D

end Work.Drive.PushDisc
