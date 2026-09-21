import Mathlib
import Submission.Work.OddVolterra.RowIdentity.Basic
import Submission.Work.OddVolterra.Existence.hquot_contDiff

namespace Work.OddVolterra.RowIdentity

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-- The frozen radicand factor attached to an endpoint function `z`:
`(z σ + H(u,σ)) · (L(σ, z σ) + L(u, z σ))`.  `Qy` is the case `z = y` and
`Qx` the case `z = -x`. -/
def Qend (h z : ℝ → ℝ) (u σ : ℝ) : ℝ :=
  (z σ + hquot h u σ) * (line h σ (z σ) + line h u (z σ))

/-- The closed region of `(u,σ)` on which positivity of `Qend` is known:
the triangle `a ≤ u ≤ σ ≤ 1` together with the diagonal segment
`[a - η, 1 + η]`. -/
def Ktri (a η : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | (a ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1) ∨
    (p.1 = p.2 ∧ a - η ≤ p.1 ∧ p.1 ≤ 1 + η)}

/-- `(u,σ) ↦ Qend h z u σ` is continuous at every point with positive second coordinate,
provided `h` is smooth and `z` is continuous on the positive half-line. -/
private lemma continuousAt_Qend {h z : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hz : ContinuousOn z (Set.Ioi 0)) {u σ : ℝ} (hσ : 0 < σ) :
    ContinuousAt (fun p : ℝ × ℝ => Qend h z p.1 p.2) (u, σ) := by
  have hq : Continuous (fun p : ℝ × ℝ => hquot h p.1 p.2) :=
    (Work.OddVolterra.Existence.hquot_contDiff hh).continuous
  have hzσ : ContinuousAt z σ := hz.continuousAt (isOpen_Ioi.mem_nhds hσ)
  have hz2 : ContinuousAt (fun p : ℝ × ℝ => z p.2) (u, σ) :=
    hzσ.comp continuous_snd.continuousAt
  have hA : ContinuousAt (fun p : ℝ × ℝ => z p.2 + hquot h p.1 p.2) (u, σ) :=
    hz2.add hq.continuousAt
  have hB : ContinuousAt (fun p : ℝ × ℝ => line h p.2 (z p.2) + line h p.1 (z p.2)) (u, σ) := by
    have h1 : ContinuousAt (fun p : ℝ × ℝ => line h p.2 (z p.2)) (u, σ) := by
      have : (fun p : ℝ × ℝ => line h p.2 (z p.2))
          = fun p : ℝ × ℝ => p.2 * z p.2 + h p.2 := rfl
      rw [this]
      exact (continuous_snd.continuousAt.mul hz2).add
        ((hh.continuous.comp continuous_snd).continuousAt)
    have h2 : ContinuousAt (fun p : ℝ × ℝ => line h p.1 (z p.2)) (u, σ) := by
      have : (fun p : ℝ × ℝ => line h p.1 (z p.2))
          = fun p : ℝ × ℝ => p.1 * z p.2 + h p.1 := rfl
      rw [this]
      exact (continuous_fst.continuousAt.mul hz2).add
        ((hh.continuous.comp continuous_fst).continuousAt)
    exact h1.add h2
  exact hA.mul hB

/-- **A diagonal window of positivity.**  If `Qend h z` is positive on the triangle
`a ≤ u ≤ σ ≤ 1`, then it is positive on `(t,t)` for all `t` in a two-sided
neighbourhood of `[a,1]`. -/
private lemma exists_diag_window {h z : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hz : ContinuousOn z (Set.Ioi 0)) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hpos : ∀ u σ : ℝ, a ≤ u → u ≤ σ → σ ≤ 1 → 0 < Qend h z u σ) :
    ∃ η > 0, η ≤ a / 2 ∧ ∀ t ∈ Set.Icc (a - η) (1 + η), 0 < Qend h z t t := by
  have hcontU : ContinuousOn (fun p : ℝ × ℝ => Qend h z p.1 p.2) {p : ℝ × ℝ | 0 < p.2} :=
    fun p hp => (continuousAt_Qend hh hz hp).continuousWithinAt
  have hdiag : ContinuousOn (fun t : ℝ => (t, t)) (Set.Ioi 0) := by fun_prop
  have hDcont : ContinuousOn (fun t : ℝ => Qend h z t t) (Set.Ioi 0) :=
    hcontU.comp hdiag (by intro t ht; exact ht)
  have hopen : IsOpen (Set.Ioi (0 : ℝ) ∩ (fun t : ℝ => Qend h z t t) ⁻¹' Set.Ioi 0) :=
    ContinuousOn.isOpen_inter_preimage hDcont isOpen_Ioi isOpen_Ioi
  have hsub : Set.Icc a 1 ⊆ Set.Ioi (0 : ℝ) ∩ (fun t : ℝ => Qend h z t t) ⁻¹' Set.Ioi 0 := by
    intro t ht
    exact ⟨lt_of_lt_of_le ha ht.1, hpos t t ht.1 le_rfl ht.2⟩
  obtain ⟨η₀, hη₀pos, hη₀⟩ := isCompact_Icc.exists_cthickening_subset_open hopen hsub
  have hminpos : 0 < min η₀ (a / 2) := lt_min hη₀pos (by linarith)
  refine ⟨min η₀ (a / 2) / 2, by linarith, by linarith [min_le_right η₀ (a / 2), ha], ?_⟩
  intro t ht
  have hmem : t ∈ Metric.thickening η₀ (Set.Icc a 1) := by
    rw [Metric.mem_thickening_iff]
    rcases le_or_gt t a with hta | hta
    · refine ⟨a, ⟨le_rfl, ha1⟩, ?_⟩
      rw [Real.dist_eq, abs_of_nonpos (by linarith : t - a ≤ 0)]
      linarith [ht.1, hminpos, min_le_left η₀ (a / 2)]
    rcases le_or_gt 1 t with h1t | h1t
    · refine ⟨1, ⟨ha1, le_rfl⟩, ?_⟩
      rw [Real.dist_eq, abs_of_nonneg (by linarith : (0:ℝ) ≤ t - 1)]
      linarith [ht.2, hminpos, min_le_left η₀ (a / 2)]
    · exact ⟨t, ⟨hta.le, h1t.le⟩, by rw [Real.dist_eq, sub_self, abs_zero]; exact hη₀pos⟩
  exact (hη₀ (Metric.thickening_subset_cthickening _ _ hmem)).2

/-- **Geometry of the rectangle.**  Every point of the rectangle of slopes
`(s - δ, s + δ) × (s - δ, 1 + δ)` is within distance `2δ` of the region `Ktri a η`,
as long as `δ ≤ η` and `δ ≤ (1-c)/2` and `s ∈ [a,c]`. -/
private lemma exists_mem_Ktri_dist {a c η δ : ℝ} (ha1 : a ≤ 1) (hc1 : c < 1) (hη : 0 < η)
    (hδη : δ ≤ η) (hδc : δ ≤ (1 - c) / 2) {s : ℝ} (hs : s ∈ Set.Icc a c)
    {q : ℝ × ℝ} (hq : q ∈ Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (1 + δ)) :
    ∃ t ∈ Ktri a η, dist q t < 2 * δ := by
  rw [Set.mem_prod, Set.mem_Ioo, Set.mem_Ioo] at hq
  obtain ⟨hu, hσ⟩ := hq
  have hq1_lt : q.1 < 1 := by linarith [hu.2, hs.2, hδc, hc1]
  rcases le_or_gt q.1 q.2 with hle | hlt
  · rcases le_or_gt q.2 1 with hσ1 | hσ1
    · have hmemK : (max q.1 a, max q.2 a) ∈ Ktri a η := by
        refine Or.inl ⟨le_max_right q.1 a, max_le_max hle le_rfl, max_le hσ1 ha1⟩
      refine ⟨(max q.1 a, max q.2 a), hmemK, ?_⟩
      · rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        refine max_lt ?_ ?_
        · rcases le_or_gt q.1 a with h | h
          · rw [max_eq_right h, abs_of_nonpos (by linarith : q.1 - a ≤ 0)]
            linarith [hu.1, hδη, hs.1]
          · rw [max_eq_left h.le, sub_self, abs_zero]
            linarith
        · rcases le_or_gt q.2 a with h | h
          · rw [max_eq_right h, abs_of_nonpos (by linarith : q.2 - a ≤ 0)]
            linarith [hσ.1, hδη, hs.1]
          · rw [max_eq_left h.le, sub_self, abs_zero]
            linarith
    · have hmemK : (max q.1 a, 1) ∈ Ktri a η := by
        exact Or.inl ⟨le_max_right q.1 a, max_le hq1_lt.le ha1, le_rfl⟩
      refine ⟨(max q.1 a, 1), hmemK, ?_⟩
      · rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
        refine max_lt ?_ ?_
        · rcases le_or_gt q.1 a with h | h
          · rw [max_eq_right h, abs_of_nonpos (by linarith : q.1 - a ≤ 0)]
            linarith [hu.1, hδη, hs.1]
          · rw [max_eq_left h.le, sub_self, abs_zero]
            linarith
        · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ q.2 - 1)]
          linarith [hσ.2]
  · have hmemK : (q.1, q.1) ∈ Ktri a η := by
      exact Or.inr ⟨rfl, by linarith [hu.1, hδη, hs.1], by linarith [hu.2, hs.2, hδc, hc1, hη]⟩
    refine ⟨(q.1, q.1), hmemK, ?_⟩
    · rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
      refine max_lt ?_ ?_
      · rw [sub_self, abs_zero]; linarith
      · rw [abs_of_nonpos (by linarith : q.2 - q.1 ≤ 0)]
        linarith [hu.2, hσ.1]

/-- **The rectangle lemma for a general endpoint function.**  If the frozen factor
`Qend h z` is positive on the triangle `a ≤ u ≤ σ ≤ 1`, then near every slope
`s ∈ [a,c]` it is positive on the whole rectangle `(s-δ, s+δ) × (s-δ, 1+δ)`. -/
lemma Qend_rect_pos (h z : ℝ → ℝ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hz : ContinuousOn z (Set.Ioi 0)) {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (hc1 : c < 1)
    (hpos : ∀ u σ : ℝ, a ≤ u → u ≤ σ → σ ≤ 1 → 0 < Qend h z u σ) :
    ∀ s ∈ Set.Icc a c, ∃ δ > 0, ∀ q : ℝ × ℝ,
      q ∈ Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (1 + δ) → 0 < Qend h z q.1 q.2 := by
  have ha1 : a ≤ 1 := le_of_lt (lt_of_le_of_lt hac hc1)
  obtain ⟨η, hηpos, hηle, hDpos⟩ := exists_diag_window hh hz ha ha1 hpos
  have hKclosed : IsClosed (Ktri a η) := by
    have h1 : IsClosed {p : ℝ × ℝ | a ≤ p.1} := isClosed_le continuous_const continuous_fst
    have h2 : IsClosed {p : ℝ × ℝ | p.1 ≤ p.2} := isClosed_le continuous_fst continuous_snd
    have h3 : IsClosed {p : ℝ × ℝ | p.2 ≤ 1} := isClosed_le continuous_snd continuous_const
    have h4 : IsClosed {p : ℝ × ℝ | p.1 = p.2} := isClosed_eq continuous_fst continuous_snd
    have h5 : IsClosed {p : ℝ × ℝ | a - η ≤ p.1} := isClosed_le continuous_const continuous_fst
    have h6 : IsClosed {p : ℝ × ℝ | p.1 ≤ 1 + η} := isClosed_le continuous_fst continuous_const
    have hEq : Ktri a η = ({p : ℝ × ℝ | a ≤ p.1} ∩ {p : ℝ × ℝ | p.1 ≤ p.2}
          ∩ {p : ℝ × ℝ | p.2 ≤ 1})
        ∪ ({p : ℝ × ℝ | p.1 = p.2} ∩ {p : ℝ × ℝ | a - η ≤ p.1}
          ∩ {p : ℝ × ℝ | p.1 ≤ 1 + η}) := by
      ext p
      unfold Ktri
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff]
      tauto
    rw [hEq]
    exact ((h1.inter h2).inter h3).union ((h4.inter h5).inter h6)
  have hKsub : Ktri a η ⊆ Set.Icc (a - η) (1 + η) ×ˢ Set.Icc (a - η) (1 + η) := by
    intro p hp
    rcases hp with ⟨h1, h2, h3⟩ | ⟨h4, h5, h6⟩
    · exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    · exact ⟨⟨h5, h6⟩, ⟨by linarith, by linarith⟩⟩
  have hKcpt : IsCompact (Ktri a η) :=
    (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hKclosed hKsub
  have hKO : Ktri a η ⊆ {r : ℝ × ℝ | 0 < r.2}
      ∩ (fun r : ℝ × ℝ => Qend h z r.1 r.2) ⁻¹' Set.Ioi 0 := by
    intro p hp
    rcases hp with ⟨h1, h2, h3⟩ | ⟨h4, h5, h6⟩
    · exact ⟨lt_of_lt_of_le ha (le_trans h1 h2), hpos p.1 p.2 h1 h2 h3⟩
    · refine ⟨?_, ?_⟩
      · have hp1 : 0 < p.1 := by linarith [h5, hηle, ha]
        show 0 < p.2
        rw [← h4]; exact hp1
      · have hd := hDpos p.1 ⟨h5, h6⟩
        show 0 < Qend h z p.1 p.2
        rw [← h4]; exact hd
  have hcontU : ContinuousOn (fun p : ℝ × ℝ => Qend h z p.1 p.2) {p : ℝ × ℝ | 0 < p.2} :=
    fun p hp => (continuousAt_Qend hh hz hp).continuousWithinAt
  have hopen : IsOpen ({p : ℝ × ℝ | 0 < p.2}
      ∩ (fun p : ℝ × ℝ => Qend h z p.1 p.2) ⁻¹' Set.Ioi 0) :=
    ContinuousOn.isOpen_inter_preimage hcontU (isOpen_lt continuous_const continuous_snd) isOpen_Ioi
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hKcpt.exists_cthickening_subset_open hopen hKO
  intro s hs
  have hδc : 0 < (1 - c) / 2 := by linarith
  set δ : ℝ := min (δ₀ / 2) (min η ((1 - c) / 2)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min (by linarith) (lt_min hηpos hδc)
  have hδη : δ ≤ η := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδc' : δ ≤ (1 - c) / 2 := by
    rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hδ2 : 2 * δ ≤ δ₀ := by
    have h : δ ≤ δ₀ / 2 := by rw [hδdef]; exact min_le_left _ _
    linarith
  refine ⟨δ, hδpos, fun q hq => ?_⟩
  obtain ⟨t, htK, hdist⟩ := exists_mem_Ktri_dist ha1 hc1 hηpos hδη hδc' hs hq
  exact (hδ₀ (Metric.cthickening_mono hδ2 _ (Metric.thickening_subset_cthickening _ _
    (Metric.mem_thickening_iff.mpr ⟨t, htK, hdist⟩)))).2

/-- **Strict positivity of the two frozen factors on a rectangle of slopes.**

The hypothesis `hKden` of the setup gives `Qy h y s σ > 0` and `Qx h x s σ > 0` for
`a ≤ s ≤ σ ≤ 1`; using the continuity of `(u,σ) ↦ Qy h y u σ` (built from `hquot`, the divided
difference of the smooth `h`, see `Submission.Work.Analysis.Calculus.contDiff_dslope`) this
spreads to a full rectangle `(s-δ, s+δ) × (s-δ, 1+δ)` around the diagonal near `s`: points below
the diagonal come from `hKden` plus continuity on the compact triangle `{a ≤ u ≤ σ ≤ 1}`, while
points above the diagonal lie within `2δ` of the diagonal segment `{(t,t) : t ∈ [a,1]}`, where
positivity follows from `hKden` on the diagonal (with `hquot h t t = deriv h t`, see
`Work.OddVolterra.hquot_self`) and continuity. -/
theorem Qy_Qx_rect_pos (H : Setup) {s : ℝ} (hs : s ∈ Set.Icc H.a H.c) :
    ∃ δ > 0, ∀ q : ℝ × ℝ, q ∈ Set.Ioo (s - δ) (s + δ) ×ˢ Set.Ioo (s - δ) (1 + δ) →
      0 < Qy H.h H.y q.1 q.2 ∧ 0 < Qx H.h H.x q.1 q.2 := by
  obtain ⟨δy, hδypos, hy⟩ := Qend_rect_pos H.h H.y H.hh H.hy.continuousOn H.ha H.hac H.hc1
    (fun u σ hu huσ hσ => (H.hKden u σ hu huσ hσ).1) s hs
  obtain ⟨δx, hδxpos, hx⟩ := Qend_rect_pos H.h (fun σ => -(H.x σ)) H.hh H.hx.neg.continuousOn
    H.ha H.hac H.hc1 (fun u σ hu huσ hσ => (H.hKden u σ hu huσ hσ).2) s hs
  refine ⟨min δy δx, lt_min hδypos hδxpos, fun q hq => ⟨?_, ?_⟩⟩
  · exact hy q (Set.prod_mono
      (Set.Ioo_subset_Ioo (by linarith [min_le_left δy δx] : s - δy ≤ s - min δy δx)
        (by linarith [min_le_left δy δx] : s + min δy δx ≤ s + δy))
      (Set.Ioo_subset_Ioo (by linarith [min_le_left δy δx] : s - δy ≤ s - min δy δx)
        (by linarith [min_le_left δy δx] : 1 + min δy δx ≤ 1 + δy)) hq)
  · exact hx q (Set.prod_mono
      (Set.Ioo_subset_Ioo (by linarith [min_le_right δy δx] : s - δx ≤ s - min δy δx)
        (by linarith [min_le_right δy δx] : s + min δy δx ≤ s + δx))
      (Set.Ioo_subset_Ioo (by linarith [min_le_right δy δx] : s - δx ≤ s - min δy δx)
        (by linarith [min_le_right δy δx] : 1 + min δy δx ≤ 1 + δx)) hq)

end

end Work.OddVolterra.RowIdentity
