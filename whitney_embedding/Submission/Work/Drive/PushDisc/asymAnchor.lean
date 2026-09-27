import Mathlib
import Submission.Work.Drive.Whitney.modelChart

/-!
# The model anchor of the asymmetric push: definitions and the displacement estimate

This module reconstructs (and proves) the model-side objects that the bridge
`WhitneyChartWindowData ⟹ AsymChartData` consumes:

* `Work.Drive.PushDisc.asymShift` — the model coordinates of the **moved** point of the shear
  `mpsi m l`: for a window point `p = (x, v)` of the second sheet, the sheet point
  `(x, (h p).1, (h p).2, p.2)` is pushed to
  `(x, (h p).1 - 2 * m x * l (‖v‖²), (h p).2, p.2)`;
* `Work.Drive.PushDisc.asymDisc` — the **model disc anchor**
  `{|x| ≤ 1, 0 ≤ y ≤ c x, u = 0, v = 0}`, with `isCompact_asymDisc` and
  `modelCorner_mem_asymDisc`;
* `Work.Drive.PushDisc.asymShift_close_anchor` — **the displacement estimate**: every *moved* window
  point is pushed to within `η/2 + L ε + ε` of the model disc, where `η` is the size of the
  amplitude's *height* window and `ε` the size of its *`v`*-window.  This is the quantitative core of
  the asymmetric push: it says that the moved sheet lands next to the model disc
  `{|x| ≤ 1, 0 ≤ y ≤ c x}`, and it is what makes the "swept" row of `AsymChartData` follow from the
  geometric isolation row.

Everything here is pure real analysis / point-set topology on the model space
`Mdl k = ℝ × ℝ × ℝ^k × ℝ^k`; no manifolds.

The definitions reproduce the names used by `Drive/PushDisc/asymChartDataOfWhitneyChartRepair.lean`
(whose bridge `nonempty_asymChartData_of_windowData` was complete but which no longer compiles: it was
written against the definitions that used to live in the later-reverted
`asymChartDataOfWhitneyChart.lean`).  The bridge is re-created, against these definitions, in
`Drive/PushDisc/windowChart.lean`.
-/

namespace Work.Drive.PushDisc

open scoped Manifold ContDiff
open Set Metric

noncomputable section

/-- **The model coordinates of the moved point of the shear.**  For a point `p = (x,v)` of the second
sheet's `(x,v)`-window whose sheet coordinates are `(x, (h p).1, (h p).2, p.2)`, the model shear
`mpsi m l` sends it to `asymShift m l h p`. -/
def asymShift {k : ℕ} (m l : ℝ → ℝ)
    (h : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k))
    (p : ℝ × EuclideanSpace ℝ (Fin k)) : Work.Drive.Whitney.Mdl k :=
  (p.1, (h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2), (h p).2, p.2)

theorem mpsi_asymShift {k : ℕ} {m l : ℝ → ℝ}
    {h : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k)}
    (p : ℝ × EuclideanSpace ℝ (Fin k)) :
    Work.Drive.Whitney.mpsi m l (p.1, (h p).1, (h p).2, p.2) = asymShift m l h p := rfl

theorem asymShift_fst {k : ℕ} {m l : ℝ → ℝ}
    {h : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k)}
    (p : ℝ × EuclideanSpace ℝ (Fin k)) : (asymShift m l h p).1 = p.1 := rfl

theorem asymShift_snd_fst {k : ℕ} {m l : ℝ → ℝ}
    {h : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k)}
    (p : ℝ × EuclideanSpace ℝ (Fin k)) :
    (asymShift m l h p).2.1 = (h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2) := rfl

theorem asymShift_snd_snd_fst {k : ℕ} {m l : ℝ → ℝ}
    {h : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k)}
    (p : ℝ × EuclideanSpace ℝ (Fin k)) : (asymShift m l h p).2.2.1 = (h p).2 := rfl

theorem asymShift_snd_snd_snd {k : ℕ} {m l : ℝ → ℝ}
    {h : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k)}
    (p : ℝ × EuclideanSpace ℝ (Fin k)) : (asymShift m l h p).2.2.2 = p.2 := rfl

/-- **The model disc anchor** `{|x| ≤ 1, 0 ≤ y ≤ c x, u = 0, v = 0}`. -/
def asymDisc (k : ℕ) (c : ℝ → ℝ) : Set (Work.Drive.Whitney.Mdl k) :=
  {ξ | |ξ.1| ≤ 1 ∧ 0 ≤ ξ.2.1 ∧ ξ.2.1 ≤ c ξ.1 ∧ ξ.2.2.1 = 0 ∧ ξ.2.2.2 = 0}

theorem mem_asymDisc {k : ℕ} {c : ℝ → ℝ} {ξ : Work.Drive.Whitney.Mdl k} :
    ξ ∈ asymDisc k c ↔
      |ξ.1| ≤ 1 ∧ 0 ≤ ξ.2.1 ∧ ξ.2.1 ≤ c ξ.1 ∧ ξ.2.2.1 = 0 ∧ ξ.2.2.2 = 0 :=
  Iff.rfl

/-- **The model disc is compact**, for a continuous core height. -/
theorem isCompact_asymDisc {k : ℕ} {c : ℝ → ℝ} (hc : Continuous c) :
    IsCompact (asymDisc k c) := by
  obtain ⟨C, hC⟩ := isCompact_Icc (a := (-1 : ℝ)) (b := 1) |>.exists_bound_of_continuousOn
    hc.continuousOn
  have hKc : IsCompact {q : ℝ × ℝ | |q.1| ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ c q.1} := by
    refine (Metric.isCompact_iff_isClosed_bounded).mpr ⟨?_, ?_⟩
    · have h1 : IsClosed {q : ℝ × ℝ | |q.1| ≤ 1} :=
        isClosed_le (continuous_abs.comp continuous_fst) continuous_const
      have h2 : IsClosed {q : ℝ × ℝ | 0 ≤ q.2} := isClosed_Ici.preimage continuous_snd
      have h3 : IsClosed {q : ℝ × ℝ | q.2 ≤ c q.1} :=
        isClosed_le continuous_snd (hc.comp continuous_fst)
      have heq : {q : ℝ × ℝ | |q.1| ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ c q.1}
          = {q : ℝ × ℝ | |q.1| ≤ 1} ∩ ({q : ℝ × ℝ | 0 ≤ q.2} ∩ {q : ℝ × ℝ | q.2 ≤ c q.1}) := by
        ext q; tauto
      rw [heq]; exact h1.inter (h2.inter h3)
    · have hsub : {q : ℝ × ℝ | |q.1| ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ c q.1}
          ⊆ Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) C := by
        rintro ⟨a, b⟩ ⟨ha, hb0, hbC⟩
        refine ⟨?_, ?_⟩
        · rw [Set.mem_Icc]; exact abs_le.mp ha
        · rw [Set.mem_Icc]
          refine ⟨hb0, le_trans hbC ?_⟩
          exact le_trans (le_abs_self _) (hC a (by rw [Set.mem_Icc]; exact abs_le.mp ha))
      exact (isCompact_Icc.prod isCompact_Icc).isBounded.subset hsub
  have himg : (fun q : ℝ × ℝ => ((q.1, q.2, 0, 0) : Work.Drive.Whitney.Mdl k)) ''
      {q : ℝ × ℝ | |q.1| ≤ 1 ∧ 0 ≤ q.2 ∧ q.2 ≤ c q.1} = asymDisc k c := by
    ext ξ
    constructor
    · rintro ⟨q, ⟨hq1, hq2, hq3⟩, rfl⟩
      exact ⟨hq1, hq2, hq3, rfl, rfl⟩
    · intro hξ
      exact ⟨(ξ.1, ξ.2.1), ⟨hξ.1, hξ.2.1, hξ.2.2.1⟩,
        Prod.ext rfl (Prod.ext rfl (Prod.ext hξ.2.2.2.1.symm hξ.2.2.2.2.symm))⟩
  rw [← himg]
  exact hKc.image (by fun_prop)

theorem modelCorner_mem_asymDisc {k : ℕ} {c : ℝ → ℝ} (hcm : c (-1) = 0) (hc1 : c 1 = 0) :
    ((-1 : ℝ), 0, 0, 0) ∈ asymDisc k c ∧ ((1 : ℝ), 0, 0, 0) ∈ asymDisc k c :=
  ⟨⟨by norm_num, le_refl 0, by norm_num [hcm], rfl, rfl⟩,
   ⟨by norm_num, le_refl 0, by norm_num [hc1], rfl, rfl⟩⟩

/-- **The distance on the model space in coordinates**: the product metric is the sup-metric. -/
theorem dist_mdl_le_same {k : ℕ} {ξ η : Work.Drive.Whitney.Mdl k} {B : ℝ}
    (h1 : |ξ.1 - η.1| ≤ B) (h2 : |ξ.2.1 - η.2.1| ≤ B)
    (h3 : ‖ξ.2.2.1 - η.2.2.1‖ ≤ B) (h4 : ‖ξ.2.2.2 - η.2.2.2‖ ≤ B) :
    dist ξ η ≤ B := by
  rw [Prod.dist_eq, Prod.dist_eq, Prod.dist_eq, Real.dist_eq, Real.dist_eq,
    dist_eq_norm, dist_eq_norm]
  exact max_le h1 (max_le h2 (max_le h3 h4))

/-- **The displacement estimate of the asymmetric push.**  Let `p` be a point of the `(x,v)`-window
(`|p.1| < X`, `‖p.2‖ < 1`) which is **moved** by the shear, i.e. `2 * m p.1 * l (‖p.2‖²) ≠ 0`.  Then
the pushed model point `asymShift m l h p` is within `η/2 + L ε + ε` of the model disc
`asymDisc k c`. -/
theorem asymShift_close_anchor {k : ℕ} {m l : ℝ → ℝ}
    {h : ℝ × EuclideanSpace ℝ (Fin k) → ℝ × EuclideanSpace ℝ (Fin k)} {c : ℝ → ℝ}
    {X η ε L : ℝ}
    (hX1 : 1 < X) (hXc : X - 1 ≤ η / 2) (hη : 0 < η) (hε : 0 < ε) (hL : 0 ≤ L)
    (hcm : c (-1) = 0) (hc1 : c 1 = 0)
    (hcpos : ∀ x : ℝ, |x| < 1 → 0 ≤ c x)
    (hcneg : ∀ x : ℝ, 1 < |x| → |x| < X → c x < 0)
    (hcη : ∀ x : ℝ, |x| ≤ X → -η / 2 ≤ c x)
    (hmnn : ∀ x, 0 ≤ m x) (hlnn : ∀ t, 0 ≤ l t) (hl1 : ∀ t, l t ≤ 1)
    (hmzero : ∀ x, X ≤ |x| → m x = 0)
    (hlε : ∀ t, ε ^ 2 ≤ t → l t = 0)
    (hrow : ∀ x, |x| < X → 2 * m x ≤ c x + η / 2)
    (hlip1 : ∀ q : ℝ × EuclideanSpace ℝ (Fin k), |q.1| < X → ‖q.2‖ < 1 →
      |(h q).1 - c q.1| ≤ L * ‖q.2‖)
    (hlip2 : ∀ q : ℝ × EuclideanSpace ℝ (Fin k), |q.1| < X → ‖q.2‖ < 1 →
      ‖(h q).2‖ ≤ L * ‖q.2‖)
    {p : ℝ × EuclideanSpace ℝ (Fin k)} (hp1 : |p.1| < X) (hp2 : ‖p.2‖ < 1)
    (hs : 2 * m p.1 * l (‖p.2‖ ^ 2) ≠ 0) :
    ∃ η₀ ∈ asymDisc k c, dist (asymShift m l h p) η₀ ≤ η / 2 + L * ε + ε := by
  have hlne : l (‖p.2‖ ^ 2) ≠ 0 := fun h0 => hs (by rw [h0, mul_zero])
  have hp2eps : ‖p.2‖ < ε := by
    have h1 : ¬ (ε ^ 2 ≤ ‖p.2‖ ^ 2) := fun hc => hlne (hlε _ hc)
    have h2 : ‖p.2‖ ^ 2 < ε ^ 2 := not_le.mp h1
    nlinarith [norm_nonneg p.2, hε]
  -- bounds on the shear's shift
  have hsnn : 0 ≤ 2 * m p.1 * l (‖p.2‖ ^ 2) :=
    mul_nonneg (mul_nonneg (by norm_num) (hmnn p.1)) (hlnn _)
  have hsle : 2 * m p.1 * l (‖p.2‖ ^ 2) ≤ c p.1 + η / 2 := by
    have h1 : 2 * m p.1 * l (‖p.2‖ ^ 2) ≤ 2 * m p.1 * 1 :=
      mul_le_mul_of_nonneg_left (hl1 _) (mul_nonneg (by norm_num) (hmnn p.1))
    have h2 : 2 * m p.1 ≤ c p.1 + η / 2 := hrow p.1 hp1
    linarith
  -- bounds on the sheet from its core
  have hyabs : |(h p).1 - c p.1| ≤ L * ‖p.2‖ := hlip1 p hp1 hp2
  have huabs : ‖(h p).2‖ ≤ L * ‖p.2‖ := hlip2 p hp1 hp2
  have hLε : L * ‖p.2‖ ≤ L * ε := mul_le_mul_of_nonneg_left hp2eps.le hL
  have hyhi : (h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2) ≤ c p.1 + L * ε := by
    have h1 : (h p).1 ≤ c p.1 + L * ‖p.2‖ := by
      have := (abs_le.mp hyabs).2; linarith
    linarith [hsnn, hLε]
  have hylo : -L * ε - η / 2 ≤ (h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2) := by
    have h1 : c p.1 - L * ‖p.2‖ ≤ (h p).1 := by
      have := (abs_le.mp hyabs).1; linarith
    linarith [hsle, hLε]
  have hup : ‖(h p).2‖ ≤ L * ε := le_trans huabs hLε
  -- the pushed point and its height
  have hshift : asymShift m l h p
      = (p.1, (h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2), (h p).2, p.2) := rfl
  have hc_of_abs_one : ∀ e : ℝ, |e| = 1 → c e = 0 := by
    intro e he
    rcases (abs_eq (show (0 : ℝ) ≤ 1 by norm_num)).mp he with h | h
    · rw [h, hc1]
    · rw [h, hcm]
  -- the target bound
  set B : ℝ := η / 2 + L * ε + ε with hBdef
  have hLεnn : 0 ≤ L * ε := mul_nonneg hL hε.le
  have hBnn : 0 ≤ B := by rw [hBdef]; linarith [hη, hLεnn, hε.le]
  have hub : L * ε ≤ B := by rw [hBdef]; linarith [hε.le]
  have hue : ε ≤ B := by rw [hBdef]; linarith [hLεnn]
  have hy2B : L * ε + η / 2 ≤ B := by rw [hBdef]; linarith [hε.le]
  have hp1close : |p.1| - 1 < η / 2 := by linarith
  rcases lt_or_ge ((h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2)) 0 with hyneg | hypos
  · -- the pushed height is negative: the anchor is at height `0`
    by_cases hx : |p.1| ≤ 1
    · -- and the source's `x` lies in the disc window
      have hc0 : 0 ≤ c p.1 := by
        rcases lt_or_eq_of_le hx with hlt | heq
        · exact hcpos p.1 hlt
        · exact le_of_eq (hc_of_abs_one p.1 heq).symm
      refine ⟨(p.1, 0, 0, 0), ⟨hx, le_refl 0, hc0, rfl, rfl⟩, ?_⟩
      have c1 : |p.1 - p.1| ≤ B := by rw [sub_self, abs_zero]; exact hBnn
      have c2 : |(h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2) - 0| ≤ B := by
        rw [sub_zero, abs_of_neg hyneg]; linarith [hylo]
      have c3 : ‖(h p).2‖ ≤ B := le_trans hup hub
      have c4 : ‖p.2‖ ≤ B := le_trans hp2eps.le hue
      refine dist_mdl_le_same ?_ ?_ ?_ ?_
      · simpa [asymShift] using c1
      · simpa [asymShift] using c2
      · simpa [asymShift] using c3
      · simpa [asymShift] using c4
    · -- and the source's `x` is outside the disc window: anchor at `(±1, 0, 0, 0)`
      have hbl : 1 < |p.1| := not_le.mp hx
      have hcp1neg : c p.1 < 0 := hcneg p.1 hbl hp1
      have hyb : |(h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2)| ≤ B := by
        rw [abs_le]
        exact ⟨by linarith [hylo], by linarith [hyhi, hcp1neg, hLεnn]⟩
      have hcomp : |p.1| - 1 ≤ η / 2 := le_of_lt hp1close
      have c3 : ‖(h p).2‖ ≤ B := le_trans hup hub
      have c4 : ‖p.2‖ ≤ B := le_trans hp2eps.le hue
      rcases lt_trichotomy p.1 0 with hneg | hzero | hpos
      · refine ⟨(-1, 0, 0, 0), ⟨by norm_num, le_refl 0, by norm_num [hcm], rfl, rfl⟩, ?_⟩
        have c1 : |p.1 + 1| ≤ B := by
          rw [abs_of_neg hneg] at hbl
          have h2 : -p.1 - 1 ≤ η / 2 := by
            have h3 := hcomp
            rw [abs_of_neg hneg] at h3
            linarith
          rw [abs_of_neg (by linarith)]
          rw [hBdef]; linarith
        refine dist_mdl_le_same ?_ ?_ ?_ ?_
        · simpa [asymShift] using c1
        · simpa [asymShift] using hyb
        · simpa [asymShift] using c3
        · simpa [asymShift] using c4
      · exact absurd hzero (by rw [hzero] at hbl; norm_num at hbl)
      · refine ⟨(1, 0, 0, 0), ⟨by norm_num, le_refl 0, by norm_num [hc1], rfl, rfl⟩, ?_⟩
        have c1 : |p.1 - 1| ≤ B := by
          rw [abs_of_pos hpos] at hbl
          have h2 : p.1 - 1 ≤ η / 2 := by
            have h3 := hcomp
            rw [abs_of_pos hpos] at h3
            linarith
          rw [abs_of_nonneg (by linarith)]
          rw [hBdef]; linarith
        refine dist_mdl_le_same ?_ ?_ ?_ ?_
        · simpa [asymShift] using c1
        · simpa [asymShift] using hyb
        · simpa [asymShift] using c3
        · simpa [asymShift] using c4
  · -- the pushed height is nonnegative
    by_cases hx : |p.1| ≤ 1
    · -- the source's `x` lies in the disc window: anchor at the clamped height
      have hc0 : 0 ≤ c p.1 := by
        rcases lt_or_eq_of_le hx with hlt | heq
        · exact hcpos p.1 hlt
        · exact le_of_eq (hc_of_abs_one p.1 heq).symm
      have c3 : ‖(h p).2‖ ≤ B := le_trans hup hub
      have c4 : ‖p.2‖ ≤ B := le_trans hp2eps.le hue
      by_cases hle : (h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2) ≤ c p.1
      · -- the pushed height is below the core: anchor at the pushed height
        refine ⟨(p.1, (h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2), 0, 0),
          ⟨hx, hypos, hle, rfl, rfl⟩, ?_⟩
        have c1 : |p.1 - p.1| ≤ B := by rw [sub_self, abs_zero]; exact hBnn
        have c2 : |(h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2)
            - ((h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2))| ≤ B := by
          rw [sub_self, abs_zero]; exact hBnn
        refine dist_mdl_le_same ?_ ?_ ?_ ?_
        · simpa [asymShift] using c1
        · simpa [asymShift] using c2
        · simpa [asymShift] using c3
        · simpa [asymShift] using c4
      · -- the pushed height is above the core: anchor at the core's height
        have hgt : c p.1 < (h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2) := not_le.mp hle
        refine ⟨(p.1, c p.1, 0, 0), ⟨hx, hc0, le_refl _, rfl, rfl⟩, ?_⟩
        have c1 : |p.1 - p.1| ≤ B := by rw [sub_self, abs_zero]; exact hBnn
        have c2 : |(h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2) - c p.1| ≤ B := by
          rw [abs_of_nonneg (by linarith)]
          rw [hBdef]; linarith [hyhi]
        refine dist_mdl_le_same ?_ ?_ ?_ ?_
        · simpa [asymShift] using c1
        · simpa [asymShift] using c2
        · simpa [asymShift] using c3
        · simpa [asymShift] using c4
    · -- the source's `x` is outside the disc window: anchor at `(±1, 0, 0, 0)`
      have hbl : 1 < |p.1| := not_le.mp hx
      have hcp1neg : c p.1 < 0 := hcneg p.1 hbl hp1
      have hyb : |(h p).1 - 2 * m p.1 * l (‖p.2‖ ^ 2)| ≤ B := by
        rw [abs_le]
        exact ⟨by linarith [hylo], by linarith [hyhi, hcp1neg, hLεnn]⟩
      have hcomp : |p.1| - 1 ≤ η / 2 := le_of_lt hp1close
      have c3 : ‖(h p).2‖ ≤ B := le_trans hup hub
      have c4 : ‖p.2‖ ≤ B := le_trans hp2eps.le hue
      rcases lt_trichotomy p.1 0 with hneg | hzero | hpos
      · refine ⟨(-1, 0, 0, 0), ⟨by norm_num, le_refl 0, by norm_num [hcm], rfl, rfl⟩, ?_⟩
        have c1 : |p.1 + 1| ≤ B := by
          rw [abs_of_neg hneg] at hbl
          have h2 : -p.1 - 1 ≤ η / 2 := by
            have h3 := hcomp
            rw [abs_of_neg hneg] at h3
            linarith
          rw [abs_of_neg (by linarith)]
          rw [hBdef]; linarith
        refine dist_mdl_le_same ?_ ?_ ?_ ?_
        · simpa [asymShift] using c1
        · simpa [asymShift] using hyb
        · simpa [asymShift] using c3
        · simpa [asymShift] using c4
      · exact absurd hzero (by rw [hzero] at hbl; norm_num at hbl)
      · refine ⟨(1, 0, 0, 0), ⟨by norm_num, le_refl 0, by norm_num [hc1], rfl, rfl⟩, ?_⟩
        have c1 : |p.1 - 1| ≤ B := by
          rw [abs_of_pos hpos] at hbl
          have h2 : p.1 - 1 ≤ η / 2 := by
            have h3 := hcomp
            rw [abs_of_pos hpos] at h3
            linarith
          rw [abs_of_nonneg (by linarith)]
          rw [hBdef]; linarith
        refine dist_mdl_le_same ?_ ?_ ?_ ?_
        · simpa [asymShift] using c1
        · simpa [asymShift] using hyb
        · simpa [asymShift] using c3
        · simpa [asymShift] using c4

end

end Work.Drive.PushDisc
