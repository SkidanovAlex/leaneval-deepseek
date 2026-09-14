import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Commons.Analysis.Integral.setIntegral_le_sqrt_mul_sqrt
import Submission.Commons.Analysis.Integral.sum_norm_intervalIntegral_le

namespace Commons.Analysis.Calculus

open MeasureTheory Set Filter intervalIntegral
open scoped ENNReal Topology Interval

-- Auxiliary lemmas (kept in a private namespace so that this module does not clash with
-- the independently developed `..._of_differenceQuotient_bound` in the commons).
namespace ACDiffQuotAux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `‖x‖ₑ ^ 2 = ENNReal.ofReal (‖x‖ ^ 2)`. -/
lemma enorm_sq_eq_ofReal (x : E) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := by
  simp [enorm_eq_nnnorm, ENNReal.ofReal_pow (norm_nonneg x)]

/-- The hypothesis of the main theorem, applied to a subset of `Ioc a (b - s)`. -/
lemma lintegral_diffQuotient_le {f : ℝ → E} {a b M s : ℝ} (hs : s ∈ Ioo (0:ℝ) (b - a))
    (h : ∀ s ∈ Ioo (0:ℝ) (b - a),
      ∫⁻ t in Ioc a (b - s), ENNReal.ofReal (‖s⁻¹ • (f (t + s) - f t)‖ ^ 2)
        ≤ ENNReal.ofReal (M ^ 2))
    {S : Set ℝ} (hS : S ⊆ Ioc a (b - s)) :
    ∫⁻ t in S, ENNReal.ofReal (‖s⁻¹ • (f (t + s) - f t)‖ ^ 2) ≤ ENNReal.ofReal (M ^ 2) :=
  le_trans (lintegral_mono_set hS) (h s hs)

/-- Real-integral form of the bound on the difference quotients over a subset of `Ioc a (b - s)`.
-/
lemma integral_diffQuotient_sq_le {f : ℝ → E} {a b M s : ℝ} (hs : s ∈ Ioo (0:ℝ) (b - a))
    (h : ∀ s ∈ Ioo (0:ℝ) (b - a),
      ∫⁻ t in Ioc a (b - s), ENNReal.ofReal (‖s⁻¹ • (f (t + s) - f t)‖ ^ 2)
        ≤ ENNReal.ofReal (M ^ 2))
    {S : Set ℝ} (hS : S ⊆ Ioc a (b - s))
    (hint : IntegrableOn (fun t ↦ ‖s⁻¹ • (f (t + s) - f t)‖ ^ 2) S volume) :
    ∫ t in S, ‖s⁻¹ • (f (t + s) - f t)‖ ^ 2 ≤ M ^ 2 := by
  have h1 : ENNReal.ofReal (∫ t in S, ‖s⁻¹ • (f (t + s) - f t)‖ ^ 2)
      = ∫⁻ t in S, ENNReal.ofReal (‖s⁻¹ • (f (t + s) - f t)‖ ^ 2) := by
    have hA : (∫ t in S, ‖s⁻¹ • (f (t + s) - f t)‖ ^ 2)
        = ∫ t in S, ‖(fun t : ℝ => ‖s⁻¹ • (f (t + s) - f t)‖ ^ 2) t‖ :=
      integral_congr_ae (μ := volume.restrict S)
        (Eventually.of_forall fun t => (Real.norm_of_nonneg (sq_nonneg _)).symm)
    have hR : (∫⁻ t in S, ENNReal.ofReal (‖s⁻¹ • (f (t + s) - f t)‖ ^ 2))
        = ∫⁻ t in S, ‖(fun t : ℝ => ‖s⁻¹ • (f (t + s) - f t)‖ ^ 2) t‖ₑ :=
      lintegral_congr fun t => (Real.enorm_eq_ofReal (sq_nonneg _)).symm
    rw [hA, hR, ← ofReal_integral_norm_eq_lintegral_enorm (μ := volume.restrict S) hint]
  have h2 : ENNReal.ofReal (∫ t in S, ‖s⁻¹ • (f (t + s) - f t)‖ ^ 2) ≤ ENNReal.ofReal (M ^ 2) := by
    rw [h1]; exact lintegral_diffQuotient_le hs h hS
  exact (ENNReal.ofReal_le_ofReal_iff (sq_nonneg M)).mp h2

/-- The (scaled) primitive of the difference quotients of `f` with step `s`, based at `a`. -/
noncomputable def diffQuotPrim (f : ℝ → E) (a s t : ℝ) : E :=
  s⁻¹ • ∫ u in a..t, (f (u + s) - f u)

/-- The difference quotients of `f` with step `s`. -/
noncomputable def diffQuot (f : ℝ → E) (s : ℝ) : ℝ → E := fun t => s⁻¹ • (f (t + s) - f t)

/-- Increments of `diffQuotPrim` are interval integrals of the difference quotients. -/
lemma diffQuotPrim_sub {f : ℝ → E} {a b s x y : ℝ} (hcont : ContinuousOn f (Icc a b))
    (hs : 0 ≤ s) (hax : a ≤ x) (hxy : x ≤ y) (hy : y + s ≤ b) :
    diffQuotPrim f a s y - diffQuotPrim f a s x
      = ∫ u in x..y, diffQuot f s u := by
  have hcontΔ : ContinuousOn (fun u : ℝ => f (u + s) - f u) (Icc a y) := by
    have h1 : ContinuousOn (fun u : ℝ => f (u + s)) (Icc a y) := by
      refine hcont.comp ((continuous_id.add continuous_const).continuousOn) ?_
      intro u hu
      simp only [mem_Icc] at hu ⊢
      exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
    exact h1.sub (hcont.mono (by intro u hu; exact ⟨hu.1, by linarith [hu.2]⟩))
  have hint_ax : IntervalIntegrable (fun u : ℝ => f (u + s) - f u) volume a x :=
    (hcontΔ.mono (by intro u hu; exact ⟨hu.1, by linarith [hu.2]⟩)).intervalIntegrable_of_Icc hax
  have hint_xy : IntervalIntegrable (fun u : ℝ => f (u + s) - f u) volume x y :=
    (hcontΔ.mono (by intro u hu; exact ⟨by linarith [hu.1, hax], hu.2⟩)).intervalIntegrable_of_Icc hxy
  have hadd := intervalIntegral.integral_add_adjacent_intervals hint_ax hint_xy
  simp only [diffQuotPrim, diffQuot]
  rw [← smul_sub, ← hadd, add_sub_cancel_left, intervalIntegral.integral_smul]

/-- The key `L²`-type bound: for a family of pairwise disjoint intervals inside `[a, b - s]`, the
sum of the norms of the increments of the primitive of the difference quotients is at most
`M * √L`, where `L` is the total length of the family. -/
lemma sum_norm_diffQuotPrim_le {f : ℝ → E} {a b M s : ℝ} (hM : 0 ≤ M)
    (hcont : ContinuousOn f (Icc a b))
    (h : ∀ s ∈ Ioo (0:ℝ) (b - a),
      ∫⁻ t in Ioc a (b - s), ENNReal.ofReal (‖s⁻¹ • (f (t + s) - f t)‖ ^ 2)
        ≤ ENNReal.ofReal (M ^ 2))
    (hs : s ∈ Ioo (0:ℝ) (b - a)) {n : ℕ} {x y : ℕ → ℝ}
    (hxy : ∀ i < n, a ≤ x i ∧ x i ≤ y i ∧ y i ≤ b - s)
    (hdisj : Set.PairwiseDisjoint (Finset.range n) (fun i ↦ uIoc (x i) (y i))) :
    ∑ i ∈ Finset.range n, ‖diffQuotPrim f a s (y i) - diffQuotPrim f a s (x i)‖
      ≤ M * Real.sqrt (∑ i ∈ Finset.range n, (y i - x i)) := by
  have hs0 : 0 ≤ s := le_of_lt hs.1
  have hcontΔ : ContinuousOn (fun u : ℝ => f (u + s) - f u) (Icc a (b - s)) := by
    have h1 : ContinuousOn (fun u : ℝ => f (u + s)) (Icc a (b - s)) := by
      refine hcont.comp ((continuous_id.add continuous_const).continuousOn) ?_
      intro u hu
      simp only [mem_Icc] at hu ⊢
      exact ⟨by linarith [hu.1], by linarith [hu.2, hs.2]⟩
    exact h1.sub (hcont.mono (by intro u hu; exact ⟨hu.1, by linarith [hu.2, hs.2]⟩))
  -- the intervals are contained in `Ioc a (b - s)`
  have hIoc : ∀ i < n, uIoc (x i) (y i) ⊆ Ioc a (b - s) := by
    intro i hi t ht
    rw [mem_uIoc] at ht
    obtain ⟨ha, hxyi, hyb⟩ := hxy i hi
    rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨ha.trans_lt h1, h2.trans hyb⟩
    · exact absurd h1 (not_lt.mpr (le_trans h2 hxyi))
  have hEsub : (⋃ i ∈ Finset.range n, uIoc (x i) (y i)) ⊆ Ioc a (b - s) := by
    intro t ht
    simp only [mem_iUnion, mem_range, exists_prop] at ht
    obtain ⟨i, hi, hti⟩ := ht
    exact hIoc i (Finset.mem_range.mp hi) hti
  have hEsub' : (⋃ i ∈ Finset.range n, uIoc (x i) (y i)) ⊆ Icc a (b - s) :=
    fun t ht => ⟨(hEsub ht).1.le, (hEsub ht).2⟩
  have hnormcont : ContinuousOn (fun t : ℝ ↦ ‖diffQuot f s t‖ ^ 2) (Icc a (b - s)) :=
    (hcontΔ.const_smul s⁻¹).norm.pow 2
  have hint : IntegrableOn (fun t ↦ ‖diffQuot f s t‖ ^ 2)
      (⋃ i ∈ Finset.range n, uIoc (x i) (y i)) volume :=
    (hnormcont.integrableOn_compact isCompact_Icc).mono_set hEsub'
  have hK : ∫ t in (⋃ i ∈ Finset.range n, uIoc (x i) (y i)), ‖diffQuot f s t‖ ^ 2 ≤ M ^ 2 :=
    integral_diffQuotient_sq_le hs h hEsub hint
  have hmain := Commons.Analysis.Integral.sum_norm_intervalIntegral_le (fun u => diffQuot f s u)
    x y (fun i hi => (hxy i hi).2.1) hdisj hint (sq_nonneg M) hK
  have hterms : ∀ i ∈ Finset.range n,
      ‖diffQuotPrim f a s (y i) - diffQuotPrim f a s (x i)‖ = ‖∫ u in (x i)..(y i), diffQuot f s u‖ := by
    intro i hi
    obtain ⟨ha, hxyi, hyb⟩ := hxy i (Finset.mem_range.mp hi)
    rw [diffQuotPrim_sub hcont hs0 ha hxyi (by linarith [hyb, hs.2])]
  rw [Finset.sum_congr rfl hterms]
  calc ∑ i ∈ Finset.range n, ‖∫ u in (x i)..(y i), diffQuot f s u‖
      ≤ Real.sqrt (M ^ 2) * Real.sqrt (∑ i ∈ Finset.range n, (y i - x i)) := hmain
    _ = M * Real.sqrt (∑ i ∈ Finset.range n, (y i - x i)) := by rw [Real.sqrt_sq hM]

/-- Integrability of an interval integral of a function continuous on a bigger interval. -/
lemma intervalIntegrable_of_mem_Icc {f : ℝ → E} {a b p q : ℝ} (hcont : ContinuousOn f (Icc a b))
    (hp : p ∈ Icc a b) (hq : q ∈ Icc a b) : IntervalIntegrable f volume p q := by
  refine (hcont.mono ?_).intervalIntegrable
  intro x hx
  rw [mem_uIcc] at hx
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨le_trans hp.1 h1, le_trans h2 hq.2⟩
  · exact ⟨le_trans hq.1 h1, le_trans h2 hp.2⟩

/-- The primitive of the difference quotients is the average of `f` over the two windows. -/
lemma diffQuotPrim_eq_sub {f : ℝ → E} {a b s t : ℝ} (hcont : ContinuousOn f (Icc a b))
    (hs : 0 ≤ s) (hat : a ≤ t) (htb : t + s ≤ b) :
    diffQuotPrim f a s t = s⁻¹ • ((∫ u in t..t + s, f u) - ∫ u in a..a + s, f u) := by
  have has : a + s ∈ Icc a b := ⟨by linarith, by linarith⟩
  have hts : t + s ∈ Icc a b := ⟨by linarith, htb⟩
  have hcontΔ : ContinuousOn (fun u : ℝ => f (u + s) - f u) (Icc a t) := by
    have h1 : ContinuousOn (fun u : ℝ => f (u + s)) (Icc a t) := by
      refine hcont.comp ((continuous_id.add continuous_const).continuousOn) ?_
      intro u hu
      simp only [mem_Icc] at hu ⊢
      exact ⟨by linarith [hu.1], by linarith [hu.2, htb]⟩
    exact h1.sub (hcont.mono (by intro u hu; exact ⟨hu.1, by linarith [hu.2, htb]⟩))
  have hint1 : IntervalIntegrable (fun u : ℝ => f (u + s)) volume a t := by
    have h1 : ContinuousOn (fun u : ℝ => f (u + s)) (Icc a t) := by
      refine hcont.comp ((continuous_id.add continuous_const).continuousOn) ?_
      intro u hu
      simp only [mem_Icc] at hu ⊢
      exact ⟨by linarith [hu.1], by linarith [hu.2, htb]⟩
    exact h1.intervalIntegrable_of_Icc hat
  have hint2 : IntervalIntegrable (fun u : ℝ => f u) volume a t :=
    intervalIntegrable_of_mem_Icc hcont ⟨le_rfl, by linarith⟩ ⟨hat, by linarith⟩
  have hsub : (∫ u in a..t, (f (u + s) - f u)) = (∫ u in a..t, f (u + s)) - ∫ u in a..t, f u :=
    intervalIntegral.integral_sub hint1 hint2
  have hcomp : (∫ u in a..t, f (u + s)) = ∫ u in a + s..t + s, f u :=
    intervalIntegral.integral_comp_add_right f s
  have e1 : (∫ u in a..t, f u) = (∫ u in a..a + s, f u) + ∫ u in a + s..t, f u :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_of_mem_Icc hcont ⟨le_rfl, by linarith⟩ has)
      (intervalIntegrable_of_mem_Icc hcont has ⟨hat, by linarith⟩)).symm
  have e2 : (∫ u in a + s..t + s, f u) = (∫ u in a + s..t, f u) + ∫ u in t..t + s, f u :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_of_mem_Icc hcont has ⟨hat, by linarith⟩)
      (intervalIntegrable_of_mem_Icc hcont ⟨hat, by linarith⟩ hts)).symm
  rw [diffQuotPrim, hsub, hcomp, e1, e2]
  abel

/-- The primitive of the difference quotients converges uniformly to `f - f a` on any `[a, c]`
with `c < b`, as the step tends to `0` from above. -/
lemma tendsto_uniform_diffQuotPrim {f : ℝ → E} {a b c : ℝ} (hab : a ≤ b) (hac : a ≤ c)
    (hcb : c < b) (hcont : ContinuousOn f (Icc a b)) :
    ∀ ε > 0, ∃ s₀ > 0, ∀ s ∈ Ioo (0:ℝ) s₀, ∀ t ∈ Icc a c,
      ‖diffQuotPrim f a s t - (f t - f a)‖ < ε := by
  intro ε hε
  obtain ⟨δ, hδ0, hδ⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hcont) (ε/4) (by linarith)
  refine ⟨min δ (b - c), lt_min hδ0 (by linarith), ?_⟩
  intro s hs t ht
  obtain ⟨hs0, hsb⟩ := hs
  have hsd : s < δ := lt_of_lt_of_le hsb (min_le_left _ _)
  have hsc : s < b - c := lt_of_lt_of_le hsb (min_le_right _ _)
  rw [mem_Icc] at ht
  obtain ⟨hat, htc⟩ := ht
  have hts : t + s ≤ b := by linarith
  have hsle : 0 ≤ s := le_of_lt hs0
  have hIcc' : ∀ u ∈ Icc t (t + s), u ∈ Icc a b := by
    intro u hu
    rw [mem_Icc] at hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hIcc'' : ∀ u ∈ Icc a (a + s), u ∈ Icc a b := by
    intro u hu
    rw [mem_Icc] at hu
    exact ⟨hu.1, by linarith [hu.2]⟩
  -- estimate on each window
  have hwin : ∀ p : ℝ, p ∈ Icc a c → ‖∫ u in p..p + s, (f u - f p)‖ ≤ s * (ε/4) := by
    intro p hp
    have hpb : p + s ≤ b := by linarith [hp.2, hsc]
    have hpbc : p ∈ Icc a b := ⟨hp.1, by linarith [hp.2, hcb]⟩
    have hmem : ∀ u ∈ Icc p (p + s), u ∈ Icc a b := by
      intro u hu
      rw [mem_Icc] at hu
      exact ⟨le_trans hp.1 hu.1, le_trans hu.2 hpb⟩
    have hcont1 : IntervalIntegrable (fun u : ℝ => ‖f u - f p‖) volume p (p + s) := by
      have : ContinuousOn (fun u : ℝ => ‖f u - f p‖) (Icc p (p + s)) :=
        ((hcont.mono hmem).sub continuousOn_const).norm
      exact this.intervalIntegrable_of_Icc (by linarith)
    have hcont2 : IntervalIntegrable (fun _ : ℝ => ε/4) volume p (p + s) :=
      intervalIntegrable_const
    calc ‖∫ u in p..p + s, (f u - f p)‖
        ≤ ∫ u in p..p + s, ‖f u - f p‖ :=
          intervalIntegral.norm_integral_le_integral_norm (by linarith [hsle])
      _ ≤ ∫ u in p..p + s, (ε/4) := by
          refine intervalIntegral.integral_mono_on (by linarith [hsle]) hcont1 hcont2 ?_
          intro u hu
          rw [mem_Icc] at hu
          have hdist : dist u p < δ := by
            rw [Real.dist_eq, abs_lt]
            constructor
            · linarith [hu.1]
            · linarith [hu.2, hsd]
          have hlt : dist (f u) (f p) < ε / 4 := hδ u (hmem u hu) p hpbc hdist
          rw [dist_eq_norm] at hlt
          exact hlt.le
      _ = s * (ε/4) := by
          rw [intervalIntegral.integral_const]
          simp only [smul_eq_mul]
          ring
  -- combine
  rw [diffQuotPrim_eq_sub hcont hsle hat hts]
  have hbase : f t - f a = s⁻¹ • (s • f t - s • f a) := by
    rw [smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ (ne_of_gt hs0), one_smul, one_smul]
  have hAI : IntervalIntegrable (fun u : ℝ => f u) volume t (t + s) :=
    intervalIntegrable_of_mem_Icc hcont ⟨hat, by linarith⟩ ⟨by linarith, hts⟩
  have hBI : IntervalIntegrable (fun u : ℝ => f u) volume a (a + s) :=
    intervalIntegrable_of_mem_Icc hcont ⟨le_rfl, by linarith⟩ ⟨by linarith, by linarith⟩
  have hct : IntervalIntegrable (fun _ : ℝ => f t) volume t (t + s) := intervalIntegrable_const
  have hca : IntervalIntegrable (fun _ : ℝ => f a) volume a (a + s) := intervalIntegrable_const
  have hA : (∫ u in t..t + s, (f u - f t)) = (∫ u in t..t + s, f u) - s • f t := by
    rw [intervalIntegral.integral_sub hAI hct, intervalIntegral.integral_const]
    congr 1
    ring
  have hB : (∫ u in a..a + s, (f u - f a)) = (∫ u in a..a + s, f u) - s • f a := by
    rw [intervalIntegral.integral_sub hBI hca, intervalIntegral.integral_const]
    congr 1
    ring
  have hrewrite : s⁻¹ • ((∫ u in t..t + s, f u) - ∫ u in a..a + s, f u) - (f t - f a)
      = s⁻¹ • ((∫ u in t..t + s, (f u - f t)) - ∫ u in a..a + s, (f u - f a)) := by
    rw [hbase, hA, hB, ← smul_sub]
    congr 1
    abel
  rw [hrewrite]
  have hnorm : ‖s⁻¹ • ((∫ u in t..t + s, (f u - f t)) - ∫ u in a..a + s, (f u - f a))‖
      = s⁻¹ * ‖(∫ u in t..t + s, (f u - f t)) - ∫ u in a..a + s, (f u - f a)‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hsle)]
  rw [hnorm]
  have h1 := hwin t ⟨hat, htc⟩
  have h2 := hwin a ⟨le_rfl, hac⟩
  have h3 : ‖(∫ u in t..t + s, (f u - f t)) - ∫ u in a..a + s, (f u - f a)‖
      ≤ s * (ε/4) + s * (ε/4) :=
    le_trans (norm_sub_le _ _) (add_le_add h1 h2)
  calc s⁻¹ * ‖(∫ u in t..t + s, (f u - f t)) - ∫ u in a..a + s, (f u - f a)‖
      ≤ s⁻¹ * (s * (ε/4) + s * (ε/4)) :=
        mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr hsle)
    _ = ε/2 := by field_simp; ring
    _ < ε := by linarith

/-- For a family of pairwise disjoint intervals with right endpoints strictly below `b`, the sum of
the distances of the `f`-values is at most `M √L`, where `L` is the total length of the family. -/
lemma sum_dist_le_of_lt_b {f : ℝ → E} {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hcont : ContinuousOn f (Icc a b))
    (h : ∀ s ∈ Ioo (0:ℝ) (b - a),
      ∫⁻ t in Ioc a (b - s), ENNReal.ofReal (‖s⁻¹ • (f (t + s) - f t)‖ ^ 2)
        ≤ ENNReal.ofReal (M ^ 2))
    {n : ℕ} {x y : ℕ → ℝ} (hxy : ∀ i < n, a ≤ x i ∧ x i ≤ y i ∧ y i < b)
    (hdisj : Set.PairwiseDisjoint (Finset.range n) (fun i ↦ uIoc (x i) (y i))) :
    ∑ i ∈ Finset.range n, dist (f (x i)) (f (y i))
      ≤ M * Real.sqrt (∑ i ∈ Finset.range n, (y i - x i)) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  have hn' : (Finset.range n).Nonempty := ⟨0, Finset.mem_range.mpr hn⟩
  set Y := (Finset.range n).sup' hn' y with hYdef
  have hYb : Y < b :=
    Finset.sup'_mem (Set.Iio b)
      (fun p hp q hq => by rw [Set.mem_Iio] at hp hq ⊢; exact max_lt hp hq) _ hn' y
      (fun i hi => (hxy i (Finset.mem_range.mp hi)).2.2)
  have haY : a ≤ Y :=
    Finset.sup'_mem (Set.Ici a)
      (fun p hp q _ => by rw [Set.mem_Ici] at hp ⊢; exact le_trans hp (le_max_left p q)) _ hn' y
      (fun i hi => le_trans (hxy i (Finset.mem_range.mp hi)).1 (hxy i (Finset.mem_range.mp hi)).2.1)
  have hleY : ∀ i ∈ Finset.range n, y i ≤ Y := fun i hi => Finset.le_sup' y hi
  set c := (Y + b) / 2 with hcdef
  have hYc : Y < c := by rw [hcdef]; linarith
  have hcb : c < b := by rw [hcdef]; linarith
  have hac : a ≤ c := le_trans haY hYc.le
  refine le_of_forall_pos_le_add fun η hη => ?_
  have hη' : 0 < η / (2 * n + 1) := by positivity
  obtain ⟨s₀, hs₀, hs₀'⟩ := tendsto_uniform_diffQuotPrim hab hac hcb hcont (η / (2 * n + 1)) hη'
  set s := min s₀ (b - c) / 2 with hsdef
  have hminpos : 0 < min s₀ (b - c) := lt_min hs₀ (by linarith)
  have hs_pos : 0 < s := by rw [hsdef]; linarith [hminpos]
  have hs_lt_s₀ : s < s₀ := by
    rw [hsdef]
    linarith [min_le_left s₀ (b - c), hminpos]
  have hs_lt_bc : s < b - c := by
    rw [hsdef]
    linarith [min_le_right s₀ (b - c), hminpos]
  have hs_ba : s < b - a := lt_of_lt_of_le hs_lt_bc (by linarith)
  have hs_bs : ∀ i < n, y i ≤ b - s := fun i hi =>
    by linarith [hleY i (Finset.mem_range.mpr hi), hYc, hs_lt_bc]
  have hkey := sum_norm_diffQuotPrim_le (f := f) hM hcont h
    (s := s) ⟨hs_pos, hs_ba⟩ (fun i hi => ⟨(hxy i hi).1, (hxy i hi).2.1, hs_bs i hi⟩) hdisj
  have hper : ∀ i ∈ Finset.range n,
      dist (f (x i)) (f (y i)) ≤
        ‖diffQuotPrim f a s (y i) - diffQuotPrim f a s (x i)‖ + 2 * (η / (2 * n + 1)) := by
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    obtain ⟨hax, hxyi, _⟩ := hxy i hi'
    have hxc : x i ∈ Icc a c := ⟨hax, le_trans hxyi (le_trans (hleY i hi) hYc.le)⟩
    have hyc : y i ∈ Icc a c := ⟨le_trans hax hxyi, le_trans (hleY i hi) hYc.le⟩
    have h1 := hs₀' s ⟨hs_pos, hs_lt_s₀⟩ (x i) hxc
    have h2 := hs₀' s ⟨hs_pos, hs_lt_s₀⟩ (y i) hyc
    have he1 : dist (f (x i) - f a) (diffQuotPrim f a s (x i)) < η / (2 * n + 1) := by
      rw [dist_eq_norm, norm_sub_rev]; exact h1
    have he2 : dist (diffQuotPrim f a s (y i)) (f (y i) - f a) < η / (2 * n + 1) := by
      rw [dist_eq_norm]; exact h2
    have he3 : dist (diffQuotPrim f a s (x i)) (diffQuotPrim f a s (y i))
        = ‖diffQuotPrim f a s (y i) - diffQuotPrim f a s (x i)‖ := by
      rw [dist_eq_norm, norm_sub_rev]
    calc dist (f (x i)) (f (y i))
        = dist (f (x i) - f a) (f (y i) - f a) := by
          rw [dist_eq_norm, dist_eq_norm, sub_sub_sub_cancel_right]
      _ ≤ dist (f (x i) - f a) (diffQuotPrim f a s (x i))
            + dist (diffQuotPrim f a s (x i)) (diffQuotPrim f a s (y i))
            + dist (diffQuotPrim f a s (y i)) (f (y i) - f a) := by
          have hA := dist_triangle (f (x i) - f a) (diffQuotPrim f a s (x i)) (f (y i) - f a)
          have hB := dist_triangle (diffQuotPrim f a s (x i)) (diffQuotPrim f a s (y i))
            (f (y i) - f a)
          linarith
      _ ≤ η / (2 * n + 1) + ‖diffQuotPrim f a s (y i) - diffQuotPrim f a s (x i)‖
            + η / (2 * n + 1) := by
          rw [he3]
          linarith [he1, he2, dist_nonneg (x := diffQuotPrim f a s (x i))
            (y := diffQuotPrim f a s (y i))]
      _ = ‖diffQuotPrim f a s (y i) - diffQuotPrim f a s (x i)‖ + 2 * (η / (2 * n + 1)) := by
          ring
  calc ∑ i ∈ Finset.range n, dist (f (x i)) (f (y i))
      ≤ ∑ i ∈ Finset.range n,
          (‖diffQuotPrim f a s (y i) - diffQuotPrim f a s (x i)‖ + 2 * (η / (2 * n + 1))) :=
        Finset.sum_le_sum hper
    _ = (∑ i ∈ Finset.range n, ‖diffQuotPrim f a s (y i) - diffQuotPrim f a s (x i)‖)
          + n * (2 * (η / (2 * n + 1))) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ M * Real.sqrt (∑ i ∈ Finset.range n, (y i - x i)) + n * (2 * (η / (2 * n + 1))) := by
        linarith
    _ ≤ M * Real.sqrt (∑ i ∈ Finset.range n, (y i - x i)) + η := by
        have h2n : (0 : ℝ) < 2 * n + 1 := by positivity
        have hsmall : (n : ℝ) * (2 * (η / (2 * n + 1))) ≤ η := by
          rw [show (n : ℝ) * (2 * (η / (2 * n + 1))) = 2 * n * η / (2 * n + 1) by ring]
          rw [div_le_iff₀ h2n]
          nlinarith
        linarith

/-- Pointwise Hölder-type bound: `dist (f x) (f y) ≤ M √(y - x)` for `a ≤ x ≤ y ≤ b`. -/
lemma dist_le_sqrt {f : ℝ → E} {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hcont : ContinuousOn f (Icc a b))
    (h : ∀ s ∈ Ioo (0:ℝ) (b - a),
      ∫⁻ t in Ioc a (b - s), ENNReal.ofReal (‖s⁻¹ • (f (t + s) - f t)‖ ^ 2)
        ≤ ENNReal.ofReal (M ^ 2))
    {x y : ℝ} (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
    dist (f x) (f y) ≤ M * Real.sqrt (y - x) := by
  have hstrict : ∀ {p q : ℝ}, a ≤ p → p ≤ q → q < b →
      dist (f p) (f q) ≤ M * Real.sqrt (q - p) := by
    intro p q hap hpq hqb
    have hb1 := sum_dist_le_of_lt_b (f := f) hab hM hcont h (n := 1)
      (x := fun _ => p) (y := fun _ => q)
      (fun i hi => by
        exact ⟨hap, hpq, hqb⟩)
      (by
        intro i hi j hj hij
        rw [Finset.mem_coe, Finset.mem_range, Nat.lt_one_iff] at hi hj
        exact absurd (by rw [hi, hj]) hij)
    simpa using hb1
  rcases lt_or_ge y b with hyb' | hyb'
  · exact hstrict hax hxy hyb'
  have hy : y = b := le_antisymm hyb hyb'
  rw [hy] at hxy ⊢
  rcases eq_or_lt_of_le hxy with hxb | hxb
  · rw [hxb, dist_self, sub_self, Real.sqrt_zero, mul_zero]
  refine le_of_forall_pos_le_add fun η hη => ?_
  obtain ⟨δ, hδ0, hδ⟩ := Metric.continuousWithinAt_iff.mp
    (hcont.continuousWithinAt ⟨hab, le_rfl⟩) η hη
  set y' := (max x (b - δ/2) + b) / 2 with hy'def
  have hmaxb : max x (b - δ/2) < b := max_lt hxb (by linarith)
  have hy'b : y' < b := by rw [hy'def]; linarith
  have hxy' : x ≤ y' := by
    rw [hy'def]
    have := le_max_left x (b - δ/2)
    linarith
  have hay' : a ≤ y' := le_trans hax hxy'
  have hdyb : dist y' b < δ := by
    rw [Real.dist_eq, abs_of_nonpos (by linarith [hy'b])]
    rw [hy'def]
    have := le_max_right x (b - δ/2)
    linarith
  have hclose : dist (f y') (f b) < η := hδ ⟨hay', hy'b.le⟩ hdyb
  calc dist (f x) (f b) ≤ dist (f x) (f y') + dist (f y') (f b) := dist_triangle _ _ _
    _ ≤ M * Real.sqrt (y' - x) + η := add_le_add (hstrict hax hxy' hy'b) hclose.le
    _ ≤ M * Real.sqrt (b - x) + η := by
        have h1 : y' - x ≤ b - x := by linarith [hy'b]
        have h2 : Real.sqrt (y' - x) ≤ Real.sqrt (b - x) := Real.sqrt_le_sqrt h1
        nlinarith [Real.sqrt_nonneg (y' - x), Real.sqrt_nonneg (b - x)]

/-- In a pairwise disjoint family of nondegenerate half-open intervals, two intervals with the same
right endpoint coincide. -/
lemma eq_of_right_eq_of_lt {n : ℕ} {x y : ℕ → ℝ}
    (hdisj : Set.PairwiseDisjoint (Finset.range n) (fun i ↦ uIoc (x i) (y i)))
    {i j : ℕ} (hi : i < n) (hj : j < n) (hxi : x i < y i) (hxj : x j < y j)
    (heq : y i = y j) : i = j := by
  by_contra hij
  have hd : Disjoint (uIoc (x i) (y i)) (uIoc (x j) (y j)) :=
    hdisj (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj) hij
  set p := (max (x i) (x j) + y i) / 2 with hpdef
  have hmaxi : max (x i) (x j) ≤ y i := max_le hxi.le (by linarith [hxj, heq])
  have hmaxj : max (x i) (x j) ≤ y j := by
    rw [← heq]
    exact max_le hxi.le (by linarith [hxj, heq])
  have hp1 : p ∈ uIoc (x i) (y i) := by
    rw [uIoc_of_le hxi.le, mem_Ioc]
    have h1 := le_max_left (x i) (x j)
    exact ⟨by linarith [hpdef, h1, hxi], by linarith [hpdef, hmaxi]⟩
  have hp2 : p ∈ uIoc (x j) (y j) := by
    rw [uIoc_of_le hxj.le, mem_Ioc]
    have h1 := le_max_left (x i) (x j)
    have h2 := le_max_right (x i) (x j)
    exact ⟨by linarith [hpdef, h2, hxj, heq], by linarith [hpdef, hmaxj]⟩
  rw [disjoint_iff_inter_eq_empty] at hd
  have : p ∈ (∅ : Set ℝ) := by
    rw [← hd]
    exact ⟨hp1, hp2⟩
  exact this

/-- The bound for an arbitrary pairwise disjoint family of intervals inside `[a, b]`, up to the
small loss `2 M √τ`, where `τ > 0` is arbitrary (and may be taken arbitrarily small). -/
lemma sum_dist_le_full {f : ℝ → E} {a b M τ : ℝ} (hab : a ≤ b) (hab' : a < b) (hM : 0 ≤ M)
    (hcont : ContinuousOn f (Icc a b))
    (h : ∀ s ∈ Ioo (0:ℝ) (b - a),
      ∫⁻ t in Ioc a (b - s), ENNReal.ofReal (‖s⁻¹ • (f (t + s) - f t)‖ ^ 2)
        ≤ ENNReal.ofReal (M ^ 2))
    (hτ0 : 0 < τ) (hτba : τ ≤ b - a)
    {n : ℕ} {x y : ℕ → ℝ} (hxy : ∀ i < n, a ≤ x i ∧ x i ≤ y i ∧ y i ≤ b)
    (hdisj : Set.PairwiseDisjoint (Finset.range n) (fun i ↦ uIoc (x i) (y i))) :
    ∑ i ∈ Finset.range n, dist (f (x i)) (f (y i))
      ≤ M * Real.sqrt (∑ i ∈ Finset.range n, (y i - x i)) + 2 * (M * Real.sqrt τ) := by
  classical
  set x3 : ℕ → ℝ := fun i =>
    if y i = b ∧ x i = b then a else if y i = b then min (x i) (b - τ) else x i with hx3
  set y3 : ℕ → ℝ := fun i =>
    if y i = b ∧ x i = b then a else if y i = b then b - τ else y i with hy3
  have hx3v : ∀ i, x3 i = (if y i = b ∧ x i = b then a
      else if y i = b then min (x i) (b - τ) else x i) := fun i => by simp only [hx3]
  have hy3v : ∀ i, y3 i = (if y i = b ∧ x i = b then a
      else if y i = b then b - τ else y i) := fun i => by simp only [hy3]
  have hxy3 : ∀ i < n, a ≤ x3 i ∧ x3 i ≤ y3 i ∧ y3 i < b := by
    intro i hi
    obtain ⟨ha, hxyi, hyb⟩ := hxy i hi
    by_cases h1 : y i = b ∧ x i = b
    · have hx : x3 i = a := by rw [hx3v i, if_pos h1]
      have hy : y3 i = a := by rw [hy3v i, if_pos h1]
      rw [hx, hy]
      exact ⟨le_rfl, le_rfl, hab'⟩
    · by_cases h2 : y i = b
      · have hx : x3 i = min (x i) (b - τ) := by rw [hx3v i, if_neg h1, if_pos h2]
        have hy : y3 i = b - τ := by rw [hy3v i, if_neg h1, if_pos h2]
        rw [hx, hy]
        exact ⟨le_min ha (by linarith [hτba]), min_le_right _ _, by linarith [hτ0]⟩
      · have hx : x3 i = x i := by rw [hx3v i, if_neg h1, if_neg h2]
        have hy : y3 i = y i := by rw [hy3v i, if_neg h1, if_neg h2]
        rw [hx, hy]
        exact ⟨ha, hxyi, lt_of_le_of_ne hyb h2⟩
  have hdisj3 : Set.PairwiseDisjoint (Finset.range n) (fun i ↦ uIoc (x3 i) (y3 i)) := by
    intro i hi j hj hij
    refine Disjoint.mono ?_ ?_ (hdisj hi hj hij)
    · intro t ht
      obtain ⟨ha, hxyi, hyb⟩ := hxy i (Finset.mem_range.mp hi)
      change t ∈ uIoc (x3 i) (y3 i) at ht
      by_cases h1 : y i = b ∧ x i = b
      · have hx : x3 i = a := by rw [hx3v i, if_pos h1]
        have hy : y3 i = a := by rw [hy3v i, if_pos h1]
        rw [hx, hy] at ht
        exact absurd ht (by
          rw [uIoc_of_le le_rfl, mem_Ioc]
          intro hh
          linarith [hh.1, hh.2])
      · by_cases h2 : y i = b
        · have hx : x3 i = min (x i) (b - τ) := by rw [hx3v i, if_neg h1, if_pos h2]
          have hy : y3 i = b - τ := by rw [hy3v i, if_neg h1, if_pos h2]
          rw [hx, hy] at ht
          simp only [mem_uIoc] at ht ⊢
          rcases ht with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
          · rcases le_or_gt (x i) (b - τ) with hcase | hcase
            · rw [min_eq_left hcase] at h1'
              exact Or.inl ⟨h1', by rw [h2]; linarith [h2', hτ0.le]⟩
            · rw [min_eq_right hcase.le] at h1'
              exact absurd h1' (not_lt.mpr h2')
          · exact absurd h1' (not_lt.mpr (h2'.trans (min_le_right _ _)))
        · have hx : x3 i = x i := by rw [hx3v i, if_neg h1, if_neg h2]
          have hy : y3 i = y i := by rw [hy3v i, if_neg h1, if_neg h2]
          rw [hx, hy] at ht
          exact ht
    · intro t ht
      obtain ⟨ha, hxyj, hyb⟩ := hxy j (Finset.mem_range.mp hj)
      change t ∈ uIoc (x3 j) (y3 j) at ht
      by_cases h1 : y j = b ∧ x j = b
      · have hx : x3 j = a := by rw [hx3v j, if_pos h1]
        have hy : y3 j = a := by rw [hy3v j, if_pos h1]
        rw [hx, hy] at ht
        exact absurd ht (by
          rw [uIoc_of_le le_rfl, mem_Ioc]
          intro hh
          linarith [hh.1, hh.2])
      · by_cases h2 : y j = b
        · have hx : x3 j = min (x j) (b - τ) := by rw [hx3v j, if_neg h1, if_pos h2]
          have hy : y3 j = b - τ := by rw [hy3v j, if_neg h1, if_pos h2]
          rw [hx, hy] at ht
          simp only [mem_uIoc] at ht ⊢
          rcases ht with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
          · rcases le_or_gt (x j) (b - τ) with hcase | hcase
            · rw [min_eq_left hcase] at h1'
              exact Or.inl ⟨h1', by rw [h2]; linarith [h2', hτ0.le]⟩
            · rw [min_eq_right hcase.le] at h1'
              exact absurd h1' (not_lt.mpr h2')
          · exact absurd h1' (not_lt.mpr (h2'.trans (min_le_right _ _)))
        · have hx : x3 j = x j := by rw [hx3v j, if_neg h1, if_neg h2]
          have hy : y3 j = y j := by rw [hy3v j, if_neg h1, if_neg h2]
          rw [hx, hy] at ht
          exact ht
  have hkey := sum_dist_le_of_lt_b (f := f) hab hM hcont h (x := x3) (y := y3) hxy3 hdisj3
  have hlen3 : ∑ i ∈ Finset.range n, (y3 i - x3 i) ≤ ∑ i ∈ Finset.range n, (y i - x i) := by
    refine Finset.sum_le_sum fun i hi => ?_
    obtain ⟨ha, hxyi, hyb⟩ := hxy i (Finset.mem_range.mp hi)
    by_cases h1 : y i = b ∧ x i = b
    · have hx : x3 i = a := by rw [hx3v i, if_pos h1]
      have hy : y3 i = a := by rw [hy3v i, if_pos h1]
      rw [hx, hy, h1.1, h1.2]
      simp
    · by_cases h2 : y i = b
      · have hx : x3 i = min (x i) (b - τ) := by rw [hx3v i, if_neg h1, if_pos h2]
        have hy : y3 i = b - τ := by rw [hy3v i, if_neg h1, if_pos h2]
        rw [hx, hy]
        rcases le_or_gt (x i) (b - τ) with hcase | hcase
        · rw [min_eq_left hcase]; linarith [hτ0.le]
        · rw [min_eq_right hcase.le]; linarith [h2]
      · have hx : x3 i = x i := by rw [hx3v i, if_neg h1, if_neg h2]
        have hy : y3 i = y i := by rw [hy3v i, if_neg h1, if_neg h2]
        rw [hx, hy]
  have hper : ∀ i < n, dist (f (x i)) (f (y i)) ≤ dist (f (x3 i)) (f (y3 i))
      + (if x i < y i ∧ y i = b then 2 * (M * Real.sqrt τ) else 0) := by
    intro i hi
    obtain ⟨ha, hxyi, hyb⟩ := hxy i hi
    by_cases htop : x i < y i ∧ y i = b
    · rw [if_pos htop]
      have hnot : ¬ (y i = b ∧ x i = b) := by
        rintro ⟨h1, h2⟩
        rw [h1, h2] at htop
        exact absurd htop.1 (lt_irrefl b)
      have hx : x3 i = min (x i) (b - τ) := by rw [hx3v i, if_neg hnot, if_pos htop.2]
      have hy : y3 i = b - τ := by rw [hy3v i, if_neg hnot, if_pos htop.2]
      have hxib : x i ≤ b := by rw [← htop.2]; exact htop.1.le
      have e1 : dist (f (x i)) (f (x3 i)) ≤ M * Real.sqrt τ := by
        rw [hx]
        rcases le_or_gt (x i) (b - τ) with hcase | hcase
        · rw [min_eq_left hcase, dist_self]; positivity
        · rw [min_eq_right hcase.le]
          have hd := dist_le_sqrt (f := f) hab hM hcont h (x := b - τ) (y := x i)
            (by linarith [hτba]) hcase.le hxib
          rw [dist_comm] at hd
          refine hd.trans ?_
          have hle : x i - (b - τ) ≤ τ := by linarith
          have h2 := Real.sqrt_le_sqrt hle
          nlinarith [Real.sqrt_nonneg (x i - (b - τ)), Real.sqrt_nonneg τ]
      have e2 : dist (f (y3 i)) (f (y i)) ≤ M * Real.sqrt τ := by
        rw [hy, htop.2]
        have hd := dist_le_sqrt (f := f) hab hM hcont h (x := b - τ) (y := b)
          (by linarith [hτba]) (by linarith [hτ0]) le_rfl
        rwa [show b - (b - τ) = τ by ring] at hd
      calc dist (f (x i)) (f (y i))
          ≤ dist (f (x i)) (f (x3 i)) + dist (f (x3 i)) (f (y i)) :=
            dist_triangle _ _ _
        _ ≤ dist (f (x i)) (f (x3 i)) + (dist (f (x3 i)) (f (y3 i)) + dist (f (y3 i)) (f (y i))) := by
            have := dist_triangle (f (x3 i)) (f (y3 i)) (f (y i))
            linarith
        _ ≤ M * Real.sqrt τ + (dist (f (x3 i)) (f (y3 i)) + M * Real.sqrt τ) := by
            linarith
        _ = dist (f (x3 i)) (f (y3 i)) + 2 * (M * Real.sqrt τ) := by ring
    · rw [if_neg htop]
      by_cases hb : y i = b
      · have hxb : x i = b := by
          rcases lt_or_eq_of_le hxyi with h | h
          · exact absurd ⟨h, hb⟩ htop
          · exact h.trans hb
        have hcleaning : y i = b ∧ x i = b := ⟨hb, hxb⟩
        have hx : x3 i = a := by rw [hx3v i, if_pos hcleaning]
        have hy : y3 i = a := by rw [hy3v i, if_pos hcleaning]
        rw [hx, hy, hxb, hb, dist_self, dist_self]
        simp
      · have hx : x3 i = x i := by rw [hx3v i, if_neg (fun hh => hb hh.1), if_neg hb]
        have hy : y3 i = y i := by rw [hy3v i, if_neg (fun hh => hb hh.1), if_neg hb]
        rw [hx, hy]
        exact le_add_of_nonneg_right (by positivity)
  have hEsum : ∑ i ∈ Finset.range n, (if x i < y i ∧ y i = b then 2 * (M * Real.sqrt τ) else 0)
      ≤ 2 * (M * Real.sqrt τ) := by
    rw [← Finset.sum_filter (s := Finset.range n) (p := fun i => x i < y i ∧ y i = b)
      (f := fun _ => 2 * (M * Real.sqrt τ))]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.range n).filter (fun i => x i < y i ∧ y i = b)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      rw [Finset.mem_filter] at ha hb
      exact eq_of_right_eq_of_lt hdisj (Finset.mem_range.mp ha.1) (Finset.mem_range.mp hb.1)
        ha.2.1 hb.2.1 (by rw [ha.2.2, hb.2.2])
    have hcardR : (((Finset.range n).filter (fun i => x i < y i ∧ y i = b)).card : ℝ) ≤ 1 := by
      exact_mod_cast hcard
    have hc : (0:ℝ) ≤ 2 * (M * Real.sqrt τ) := by positivity
    nlinarith [hcardR, hc]
  calc ∑ i ∈ Finset.range n, dist (f (x i)) (f (y i))
      ≤ ∑ i ∈ Finset.range n, (dist (f (x3 i)) (f (y3 i))
          + (if x i < y i ∧ y i = b then 2 * (M * Real.sqrt τ) else 0)) :=
        Finset.sum_le_sum fun i hi => hper i (Finset.mem_range.mp hi)
    _ = (∑ i ∈ Finset.range n, dist (f (x3 i)) (f (y3 i)))
          + ∑ i ∈ Finset.range n, (if x i < y i ∧ y i = b then 2 * (M * Real.sqrt τ) else 0) :=
        Finset.sum_add_distrib
    _ ≤ M * Real.sqrt (∑ i ∈ Finset.range n, (y3 i - x3 i)) + 2 * (M * Real.sqrt τ) := by
        linarith [hkey, hEsum]
    _ ≤ M * Real.sqrt (∑ i ∈ Finset.range n, (y i - x i)) + 2 * (M * Real.sqrt τ) := by
        have h1 := Real.sqrt_le_sqrt hlen3
        have h2 := mul_le_mul_of_nonneg_left h1 hM
        linarith

/-- `uIoc (min p q) (max p q) = uIoc p q`. -/
lemma uIoc_min_max (p q : ℝ) : uIoc (min p q) (max p q) = uIoc p q := by
  rw [uIoc, uIoc]
  congr 1 <;> simp


end ACDiffQuotAux

open ACDiffQuotAux

theorem absolutelyContinuousOnInterval_and_deriv_bound_of_differenceQuotient {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {f : ℝ → E} {a b M : ℝ} (hab : a ≤ b) (hM : 0 ≤ M)
    (hcont : ContinuousOn f (Set.Icc a b))
    (h : ∀ s ∈ Set.Ioo (0:ℝ) (b - a),
      ∫⁻ t in Set.Ioc a (b - s), ENNReal.ofReal (‖s⁻¹ • (f (t + s) - f t)‖ ^ 2)
        ≤ ENNReal.ofReal (M ^ 2)) :
    AbsolutelyContinuousOnInterval f a b ∧
      ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (‖deriv f t‖ ^ 2) ≤ ENNReal.ofReal (M ^ 2) := by
  constructor
  · rcases hab.eq_or_lt with rfl | hab'
    · rw [absolutelyContinuousOnInterval_iff]
      intro ε hε
      refine ⟨1, one_pos, fun E hE _ => ?_⟩
      obtain ⟨hmem, -⟩ := hE
      have hzero : ∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        obtain ⟨h1, h2⟩ := hmem i hi
        rw [uIcc_self] at h1 h2
        rw [mem_singleton_iff] at h1 h2
        rw [h1, h2, dist_self]
      rw [hzero]
      exact hε
    · rw [absolutelyContinuousOnInterval_iff]
      intro ε hε
      have hc : 0 < M + 1 := by linarith
      have hcpos : (0:ℝ) < ε / (2 * (M + 1)) := by positivity
      have hcpos' : (0:ℝ) < ε / (4 * (M + 1)) := by positivity
      set δ := (ε / (2 * (M + 1))) ^ 2 with hδdef
      set τ := min ((b - a) / 2) ((ε / (4 * (M + 1))) ^ 2) with hτdef
      have hτ0 : 0 < τ := by
        rw [hτdef]; exact lt_min (by linarith) (by positivity)
      have hτba : τ ≤ b - a := by
        rw [hτdef]
        have := min_le_left ((b - a) / 2) ((ε / (4 * (M + 1))) ^ 2)
        linarith
      have hτsq : Real.sqrt τ ≤ ε / (4 * (M + 1)) := by
        rw [hτdef]
        calc Real.sqrt (min ((b - a) / 2) ((ε / (4 * (M + 1))) ^ 2))
            ≤ Real.sqrt ((ε / (4 * (M + 1))) ^ 2) := Real.sqrt_le_sqrt (min_le_right _ _)
          _ = ε / (4 * (M + 1)) := Real.sqrt_sq hcpos'.le
      have hδpos : 0 < δ := by rw [hδdef]; positivity
      refine ⟨δ, hδpos, fun E hE hlen => ?_⟩
      obtain ⟨hmem, hdisjE⟩ := hE
      set x : ℕ → ℝ := fun i => min (E.2 i).1 (E.2 i).2 with hxdef
      set y : ℕ → ℝ := fun i => max (E.2 i).1 (E.2 i).2 with hydef
      have hxy : ∀ i < E.1, a ≤ x i ∧ x i ≤ y i ∧ y i ≤ b := by
        intro i hi
        obtain ⟨h1, h2⟩ := hmem i (Finset.mem_range.mpr hi)
        rw [mem_uIcc] at h1 h2
        have hp : a ≤ (E.2 i).1 ∧ (E.2 i).1 ≤ b := by
          rcases h1 with ⟨h, h'⟩ | ⟨h, h'⟩
          · exact ⟨h, h'⟩
          · exact ⟨by linarith, by linarith⟩
        have hq : a ≤ (E.2 i).2 ∧ (E.2 i).2 ≤ b := by
          rcases h2 with ⟨h, h'⟩ | ⟨h, h'⟩
          · exact ⟨h, h'⟩
          · exact ⟨by linarith, by linarith⟩
        simp only [hxdef, hydef]
        exact ⟨le_min hp.1 hq.1, min_le_max, max_le hp.2 hq.2⟩
      have hdisj : Set.PairwiseDisjoint (Finset.range E.1) (fun i ↦ uIoc (x i) (y i)) := by
        intro i hi j hj hij
        have hd := hdisjE hi hj hij
        show Disjoint (uIoc (x i) (y i)) (uIoc (x j) (y j))
        simp only [hxdef, hydef]
        rwa [uIoc_min_max, uIoc_min_max]
      have hlen' : ∑ i ∈ Finset.range E.1, (y i - x i) < δ := by
        have hsum : ∑ i ∈ Finset.range E.1, (y i - x i)
            = ∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2 := by
          refine Finset.sum_congr rfl fun i hi => ?_
          simp only [hxdef, hydef]
          rw [Real.dist_eq, ← max_sub_min_eq_abs']
        rw [hsum]
        exact hlen
      have hkey := sum_dist_le_full (f := f) hab hab' hM hcont h hτ0 hτba hxy hdisj
      have hsum_eq : ∑ i ∈ Finset.range E.1, dist (f ((E.2 i).1)) (f ((E.2 i).2))
          = ∑ i ∈ Finset.range E.1, dist (f (x i)) (f (y i)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        simp only [hxdef, hydef]
        rcases le_total (E.2 i).1 (E.2 i).2 with hle | hle
        · rw [min_eq_left hle, max_eq_right hle]
        · rw [min_eq_right hle, max_eq_left hle, dist_comm]
      rw [hsum_eq]
      have hLnonneg : 0 ≤ ∑ i ∈ Finset.range E.1, (y i - x i) :=
        Finset.sum_nonneg fun i hi => sub_nonneg.mpr (hxy i (Finset.mem_range.mp hi)).2.1
      have hsqrt_lt : Real.sqrt (∑ i ∈ Finset.range E.1, (y i - x i)) < ε / (2 * (M + 1)) := by
        have h1 : Real.sqrt (∑ i ∈ Finset.range E.1, (y i - x i)) < Real.sqrt δ :=
          Real.sqrt_lt_sqrt hLnonneg hlen'
        rwa [hδdef, Real.sqrt_sq hcpos.le] at h1
      calc ∑ i ∈ Finset.range E.1, dist (f (x i)) (f (y i))
          ≤ M * Real.sqrt (∑ i ∈ Finset.range E.1, (y i - x i)) + 2 * (M * Real.sqrt τ) := hkey
        _ ≤ M * (ε / (2 * (M + 1))) + 2 * (M * (ε / (4 * (M + 1)))) := by
            have h1 : M * Real.sqrt (∑ i ∈ Finset.range E.1, (y i - x i))
                ≤ M * (ε / (2 * (M + 1))) := mul_le_mul_of_nonneg_left hsqrt_lt.le hM
            have h2 : 2 * (M * Real.sqrt τ) ≤ 2 * (M * (ε / (4 * (M + 1)))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hτsq hM) (by norm_num)
            linarith
        _ < ε := by
            have h3 : M * (ε / (2 * (M + 1))) + 2 * (M * (ε / (4 * (M + 1))))
                = M * ε / (M + 1) := by field_simp; ring
            rw [h3]
            have h4 : M * ε / (M + 1) < (M + 1) * ε / (M + 1) := by
              apply div_lt_div_of_pos_right _ hc
              nlinarith
            rwa [mul_div_cancel_left₀ _ (ne_of_gt hc)] at h4
  · -- the bound on the derivative
    rcases hab.eq_or_lt with hbeq | hab'
    · -- `a = b`: the lintegral vanishes
      rw [hbeq, Ioc_self, Measure.restrict_empty, lintegral_zero_measure]
      exact bot_le
    · classical
      -- an extension of `f` to all of `ℝ` which is continuous and agrees with `f` on `[a, b]`
      set G : ℝ → E := fun t => f (max a (min t b)) with hGdef
      have hGcont : Continuous G := by
        refine hcont.comp_continuous ?_ ?_
        · exact continuous_const.max (continuous_id.min continuous_const)
        · intro t
          simp only [mem_Icc]
          exact ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
      have hGeq : ∀ t ∈ Icc a b, G t = f t := by
        intro t ht
        rw [mem_Icc] at ht
        simp only [hGdef]
        rw [min_eq_left ht.2, max_eq_right ht.1]
      set s : ℕ → ℝ := fun n => 1 / (n + 1) with hsdef
      have hs_pos : ∀ n, 0 < s n := by
        intro n
        rw [hsdef]
        positivity
      have hs_tendsto : Tendsto s atTop (𝓝 0) := by
        rw [hsdef]
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      set Q : ℕ → ℝ → ℝ≥0∞ := fun n t => ‖slope G t (t + s n)‖ₑ ^ 2 with hQdef
      have hQmeas : ∀ n, Measurable (Q n) := by
        intro n
        have hcont1 : Continuous (fun t : ℝ => slope G t (t + s n)) := by
          simp only [slope, add_sub_cancel_left]
          exact ((hGcont.comp (continuous_id.add continuous_const)).sub hGcont).const_smul _
        have hcont2 : Continuous (fun t : ℝ => ‖slope G t (t + s n)‖ ^ 2) :=
          (continuous_norm.comp hcont1).pow 2
        rw [hQdef]
        simpa only [enorm_sq_eq_ofReal] using hcont2.measurable.ennreal_ofReal
      set H : ℕ → ℝ → ℝ≥0∞ :=
        fun n => (Ioc a (b - s n)).indicator (Q n) with hHdef
      have hHmeas : ∀ n, Measurable (H n) := by
        intro n
        rw [hHdef]
        exact (hQmeas n).indicator measurableSet_Ioc
      -- pointwise comparison at points of `(a, b)`
      have hpt : ∀ t ∈ Ioo a b, ‖deriv f t‖ₑ ^ 2 ≤ liminf (fun n => H n t) atTop := by
        intro t ht
        rw [mem_Ioo] at ht
        have hbt : 0 < b - t := by linarith
        have hevQ : ∀ᶠ n in atTop, H n t = Q n t := by
          filter_upwards [hs_tendsto.eventually (Iio_mem_nhds hbt)] with n hn
          rw [hHdef]
          exact Set.indicator_of_mem (by rw [mem_Ioc]; exact ⟨ht.1, by linarith⟩) _
        rw [Filter.liminf_congr hevQ]
        by_cases hd : DifferentiableAt ℝ f t
        · have hslope : Tendsto (fun n : ℕ => slope f t (t + s n)) atTop (𝓝 (deriv f t)) := by
            refine (hd.hasDerivAt.tendsto_slope).comp ?_
            rw [tendsto_nhdsWithin_iff]
            refine ⟨by simpa using tendsto_const_nhds.add hs_tendsto, ?_⟩
            filter_upwards with n
            exact ne_of_gt (by linarith [hs_pos n] : t < t + s n)
          have hQeq : ∀ᶠ n in atTop, Q n t = ‖slope f t (t + s n)‖ₑ ^ 2 := by
            filter_upwards [hs_tendsto.eventually (Iio_mem_nhds hbt)] with n hn
            have htIcc : t ∈ Icc a b := ⟨ht.1.le, ht.2.le⟩
            have htsIcc : t + s n ∈ Icc a b := ⟨by linarith [ht.1, hs_pos n], by linarith⟩
            rw [hQdef]
            simp only [slope, add_sub_cancel_left]
            rw [hGeq (t + s n) htsIcc, hGeq t htIcc]
          have hlim : liminf (fun n => Q n t) atTop = ‖deriv f t‖ₑ ^ 2 := by
            rw [Filter.liminf_congr hQeq]
            have hR : Tendsto (fun n : ℕ => ‖slope f t (t + s n)‖ ^ 2) atTop
                (𝓝 (‖deriv f t‖ ^ 2)) :=
              ((continuous_norm.tendsto (deriv f t)).comp hslope).pow 2
            have hfinal : Tendsto (fun n : ℕ => ‖slope f t (t + s n)‖ₑ ^ 2) atTop
                (𝓝 (‖deriv f t‖ₑ ^ 2)) := by
              simpa only [enorm_sq_eq_ofReal] using ENNReal.tendsto_ofReal hR
            exact hfinal.liminf_eq
          rw [hlim]
        · rw [deriv_zero_of_not_differentiableAt hd]
          simp
      -- the bound on the truncated difference quotients
      have hHbound : ∀ n, s n < b - a → ∫⁻ t in Ioc a b, H n t ≤ ENNReal.ofReal (M ^ 2) := by
        intro n hn
        have hsub : Ioc a (b - s n) ⊆ Ioc a b := by
          intro t ht
          rw [mem_Ioc] at ht ⊢
          exact ⟨ht.1, by linarith [ht.2, hs_pos n]⟩
        have h1 : ∫⁻ t in Ioc a b, H n t ≤ ∫⁻ t in Ioc a (b - s n), Q n t := by
          have heq1 : ∫⁻ t in Ioc a b, H n t = ∫⁻ t in Ioc a (b - s n), Q n t := by
            have hHn : H n = (Ioc a (b - s n)).indicator (Q n) := by simp only [hHdef]
            rw [hHn]
            rw [lintegral_indicator (μ := volume.restrict (Ioc a b)) measurableSet_Ioc]
            rw [← Measure.restrict_restrict_of_subset (μ := volume) hsub]
          rw [heq1]
        have hident : ∫⁻ t in Ioc a (b - s n), Q n t
            = ∫⁻ t in Ioc a (b - s n),
                ENNReal.ofReal (‖(s n)⁻¹ • (f (t + s n) - f t)‖ ^ 2) := by
          refine setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
          rw [mem_Ioc] at ht
          have htIcc : t ∈ Icc a b := ⟨ht.1.le, by linarith [ht.2, hn.le, hs_pos n]⟩
          have htsIcc : t + s n ∈ Icc a b := ⟨by linarith [ht.1, hs_pos n], by linarith [ht.2]⟩
          rw [hQdef]
          simp only [slope, add_sub_cancel_left]
          rw [hGeq (t + s n) htsIcc, hGeq t htIcc]
          exact enorm_sq_eq_ofReal _
        have h2 : ∫⁻ t in Ioc a b, H n t
            ≤ ∫⁻ t in Ioc a (b - s n),
                ENNReal.ofReal (‖(s n)⁻¹ • (f (t + s n) - f t)‖ ^ 2) := by
          rw [hident] at h1
          exact h1
        exact h2.trans (lintegral_diffQuotient_le ⟨hs_pos n, hn⟩ h (le_refl _))
      have hliminf : liminf (fun n => ∫⁻ t in Ioc a b, H n t) atTop ≤ ENNReal.ofReal (M ^ 2) := by
        refine Filter.liminf_le_of_frequently_le' ?_
        refine (Filter.Eventually.frequently ?_)
        filter_upwards [hs_tendsto.eventually (Iio_mem_nhds (by linarith : (0:ℝ) < b - a))]
          with n hn
        exact hHbound n hn
      have hfatou : ∫⁻ t in Ioc a b, liminf (fun n => H n t) atTop ≤ ENNReal.ofReal (M ^ 2) :=
        (lintegral_liminf_le hHmeas).trans hliminf
      have hmono : ∫⁻ t in Ioo a b, ‖deriv f t‖ₑ ^ 2
          ≤ ∫⁻ t in Ioo a b, liminf (fun n => H n t) atTop := by
        rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo]
        exact lintegral_mono fun t => by
          by_cases ht : t ∈ Ioo a b
          · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
            exact hpt t ht
          · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
      have hmono2 : ∫⁻ t in Ioo a b, liminf (fun n => H n t) atTop
          ≤ ∫⁻ t in Ioc a b, liminf (fun n => H n t) atTop :=
        lintegral_mono_set fun t ht => ⟨ht.1, ht.2.le⟩
      have hfin : ∫⁻ t in ({b} : Set ℝ), ‖deriv f t‖ₑ ^ 2 = 0 := by
        rw [lintegral_singleton, Real.volume_singleton, mul_zero]
      have hIoc_eq : ∫⁻ t in Ioc a b, (‖deriv f t‖ₑ ^ 2 : ℝ≥0∞)
          = ∫⁻ t in Ioo a b, ‖deriv f t‖ₑ ^ 2 := by
        have hset : (Ioc a b : Set ℝ) = Ioo a b ∪ ({b} : Set ℝ) := by
          ext t
          simp only [mem_Ioc, mem_union, mem_Ioo, mem_singleton_iff]
          constructor
          · intro h
            rcases eq_or_lt_of_le h.2 with hb | hb
            · exact Or.inr hb
            · exact Or.inl ⟨h.1, hb⟩
          · rintro (⟨h1, h2⟩ | rfl)
            · exact ⟨h1, h2.le⟩
            · exact ⟨hab', le_rfl⟩
        have hdisj : Disjoint (Ioo a b) ({b} : Set ℝ) := by
          rw [disjoint_iff_inter_eq_empty]
          ext t
          simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and, mem_Ioo,
            mem_singleton_iff]
          intro ht htb
          rw [htb] at ht
          exact absurd ht.2 (lt_irrefl b)
        rw [hset, lintegral_union (measurableSet_singleton b) hdisj, hfin]
        simp
      have hmain : ∫⁻ t in Ioc a b, ‖deriv f t‖ₑ ^ 2 ≤ ENNReal.ofReal (M ^ 2) :=
        hIoc_eq.trans_le ((hmono.trans hmono2).trans hfatou)
      simpa only [enorm_sq_eq_ofReal] using hmain

end Commons.Analysis.Calculus
