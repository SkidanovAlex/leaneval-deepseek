import Mathlib

/-!
# The zero set of `max f g` near a common regular zero is a local arc

Let `f g : ℝ × ℝ → ℝ` be `C¹` and let `p` be a common zero of `f` and `g` at which the map
`(f, g)` has an invertible derivative.  Then in a neighbourhood of `p` the set
`{q | max (f q) (g q) = 0}` is a topological arc through `p`: there is a continuous injective
parametrisation `ρ` of an interval through `p` whose image is exactly that zero set near `p`.

The proof is the inverse function theorem: `(f, g)` is a local homeomorphism at `p`, so the zero
set of `max (f, g)` is the preimage of the "corner" `{(x, y) | max x y = 0}` under the local
inverse.  The corner is parametrised explicitly by `cornerPt`.
-/

namespace Work.Smooth.BoxGeneric.LocalArc

/-- `max a b = 0` means that `a ≤ 0`, `b ≤ 0` and one of the two is zero. -/
private lemma max_eq_zero_iff {a b : ℝ} :
    max a b = 0 ↔ a ≤ 0 ∧ b ≤ 0 ∧ (a = 0 ∨ b = 0) := by
  constructor
  · intro h
    have ha : a ≤ 0 := le_trans (le_max_left a b) (le_of_eq h)
    have hb : b ≤ 0 := le_trans (le_max_right a b) (le_of_eq h)
    refine ⟨ha, hb, ?_⟩
    by_contra hc
    rw [not_or] at hc
    obtain ⟨ha', hb'⟩ := hc
    have hmax : max a b < 0 := max_lt (lt_of_le_of_ne ha ha') (lt_of_le_of_ne hb hb')
    rw [h] at hmax
    exact lt_irrefl 0 hmax
  · rintro ⟨ha, hb, h0 | h0⟩
    · rw [h0]; exact max_eq_left hb
    · rw [h0]; exact max_eq_right ha

/-- The "corner" `{(x, y) | max x y = 0}`, parametrised by `t ↦ (min (η t) 0, -max (η t) 0)`.
For `t ≤ 0` this is the point `(η t, 0)` on the negative `x`-axis and for `t ≥ 0` it is the point
`(0, -η t)` on the negative `y`-axis. -/
private def cornerPt (η : ℝ) (t : ℝ) : ℝ × ℝ := (η * min t 0, -(η * max t 0))

private lemma cornerPt_continuous (η : ℝ) : Continuous (cornerPt η) := by
  unfold cornerPt
  fun_prop

private lemma cornerPt_zero (η : ℝ) : cornerPt η 0 = 0 := by
  unfold cornerPt
  simp

private lemma cornerPt_injective (η : ℝ) (hη : 0 < η) : Function.Injective (cornerPt η) := by
  intro t1 t2 h
  have h1 : η * min t1 0 = η * min t2 0 := by
    have h' := congrArg Prod.fst h; simpa [cornerPt] using h'
  have h2 : -(η * max t1 0) = -(η * max t2 0) := by
    have h' := congrArg Prod.snd h; simpa [cornerPt] using h'
  have h1' : min t1 0 = min t2 0 := mul_left_cancel₀ (ne_of_gt hη) h1
  have h2' : max t1 0 = max t2 0 :=
    mul_left_cancel₀ (ne_of_gt hη) (neg_inj.mp h2)
  calc t1 = min t1 0 + max t1 0 := by have := min_add_max t1 0; linarith
    _ = min t2 0 + max t2 0 := by rw [h1', h2']
    _ = t2 := by have := min_add_max t2 0; linarith

private lemma cornerPt_norm_le (η : ℝ) (hη : 0 < η) (t : ℝ) :
    ‖cornerPt η t‖ ≤ η * |t| := by
  have h1 : |min t 0| ≤ |t| := by
    rcases le_total t 0 with h | h
    · simp only [min_eq_left h]; exact le_refl _
    · rw [min_eq_right h]; simp
  have h2 : |max t 0| ≤ |t| := by
    rcases le_total t 0 with h | h
    · rw [max_eq_right h]; simp
    · simp only [max_eq_left h]; exact le_refl _
  unfold cornerPt
  rw [Prod.norm_def]
  simp only [Real.norm_eq_abs, abs_mul, abs_neg]
  rw [abs_of_pos hη, max_le_iff]
  exact ⟨mul_le_mul_of_nonneg_left h1 hη.le, mul_le_mul_of_nonneg_left h2 hη.le⟩

private lemma cornerPt_max (η : ℝ) (hη : 0 < η) (t : ℝ) :
    max (η * min t 0) (-(η * max t 0)) = 0 := by
  rcases le_total t 0 with h | h
  · rw [min_eq_left h, max_eq_right h, mul_zero, neg_zero]
    exact max_eq_right (mul_nonpos_of_nonneg_of_nonpos hη.le h)
  · rw [min_eq_right h, max_eq_left h, mul_zero]
    exact max_eq_left (by nlinarith [mul_nonneg hη.le h])

theorem local_arc_of_max_of_isInvertible {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) {p : ℝ × ℝ} (hfp : f p = 0) (hgp : g p = 0) (hinv : ((fderiv ℝ f p).prod (fderiv ℝ g p)).IsInvertible) : ∃ ε : ℝ, 0 < ε ∧ ∃ ρ : ℝ → ℝ × ℝ, ρ 0 = p ∧ ContinuousOn ρ (Set.Ioo (-1 : ℝ) 1) ∧ Set.InjOn ρ (Set.Ioo (-1 : ℝ) 1) ∧ (∀ t ∈ Set.Ioo (-1 : ℝ) 1, max (f (ρ t)) (g (ρ t)) = 0) ∧ (∀ q : ℝ × ℝ, max (f q) (g q) = 0 → ‖q - p‖ < ε → ∃ t ∈ Set.Ioo (-1 : ℝ) 1, ρ t = q) := by
  obtain ⟨A, hA⟩ := hinv
  have hn : (1 : WithTop ℕ∞) ≠ 0 := by norm_num
  have hAstrict : HasStrictFDerivAt (fun q : ℝ × ℝ => (f q, g q)) (A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := by
    have h := ((hf.contDiffAt (x := p)).hasStrictFDerivAt hn).prodMk
      ((hg.contDiffAt (x := p)).hasStrictFDerivAt hn)
    rwa [← hA] at h
  let Φ := hAstrict.toOpenPartialHomeomorph (fun q : ℝ × ℝ => (f q, g q))
  have hp_source : p ∈ Φ.source := hAstrict.mem_toOpenPartialHomeomorph_source
  have h0_target : (fun q : ℝ × ℝ => (f q, g q)) p ∈ Φ.target :=
    hAstrict.image_mem_toOpenPartialHomeomorph_target
  have hΦp : (Φ : ℝ × ℝ → ℝ × ℝ) p = 0 := Prod.ext hfp hgp
  have h0 : (0 : ℝ × ℝ) ∈ Φ.target := by
    rw [← hΦp]
    exact h0_target
  obtain ⟨η, hηpos, hηsub⟩ := Metric.mem_nhds_iff.mp (Φ.open_target.mem_nhds h0)
  have hf_abs_cont : ContinuousAt (fun q : ℝ × ℝ => |f q|) p :=
    continuous_abs.continuousAt.comp hf.continuous.continuousAt
  have hg_abs_cont : ContinuousAt (fun q : ℝ × ℝ => |g q|) p :=
    continuous_abs.continuousAt.comp hg.continuous.continuousAt
  have hmem_f : (fun q : ℝ × ℝ => |f q|) ⁻¹' (Set.Iio η) ∈ nhds p :=
    hf_abs_cont.preimage_mem_nhds (isOpen_Iio.mem_nhds (by simpa [hfp] using hηpos))
  have hmem_g : (fun q : ℝ × ℝ => |g q|) ⁻¹' (Set.Iio η) ∈ nhds p :=
    hg_abs_cont.preimage_mem_nhds (isOpen_Iio.mem_nhds (by simpa [hgp] using hηpos))
  have hnhds : Φ.source ∩ {q : ℝ × ℝ | |f q| < η} ∩ {q : ℝ × ℝ | |g q| < η} ∈ nhds p :=
    Filter.inter_mem (Filter.inter_mem (Φ.open_source.mem_nhds hp_source) hmem_f) hmem_g
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp hnhds
  have hc_mem : ∀ t ∈ Set.Ioo (-1 : ℝ) 1, cornerPt η t ∈ Φ.target := by
    intro t ht
    apply hηsub
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    rw [Set.mem_Ioo] at ht
    have ht1 : |t| < 1 := abs_lt.mpr ht
    calc ‖cornerPt η t‖ ≤ η * |t| := cornerPt_norm_le η hηpos t
      _ < η * 1 := by nlinarith [hηpos, ht1]
      _ = η := mul_one η
  let ρ : ℝ → ℝ × ℝ := fun t => Φ.symm (cornerPt η t)
  refine ⟨ε, hεpos, ρ, ?_, ?_, ?_, ?_, ?_⟩
  · show Φ.symm (cornerPt η 0) = p
    rw [cornerPt_zero, ← hΦp]
    exact Φ.left_inv hp_source
  · show ContinuousOn (fun t : ℝ => Φ.symm (cornerPt η t)) (Set.Ioo (-1 : ℝ) 1)
    exact Φ.continuousOn_symm.comp (cornerPt_continuous η).continuousOn hc_mem
  · show Set.InjOn (fun t : ℝ => Φ.symm (cornerPt η t)) (Set.Ioo (-1 : ℝ) 1)
    intro t1 ht1 t2 ht2 h
    have h1 : cornerPt η t1 = cornerPt η t2 := by
      apply Φ.symm.injOn
      · show cornerPt η t1 ∈ (Φ.symm).source
        rw [OpenPartialHomeomorph.symm_source]; exact hc_mem t1 ht1
      · show cornerPt η t2 ∈ (Φ.symm).source
        rw [OpenPartialHomeomorph.symm_source]; exact hc_mem t2 ht2
      · exact h
    exact cornerPt_injective η hηpos h1
  · intro t ht
    have hct : cornerPt η t ∈ Φ.target := hc_mem t ht
    have happ : (f (ρ t), g (ρ t)) = cornerPt η t := Φ.right_inv hct
    have hf_eq : f (ρ t) = η * min t 0 := by
      have h' := congrArg Prod.fst happ
      simpa [cornerPt] using h'
    have hg_eq : g (ρ t) = -(η * max t 0) := by
      have h' := congrArg Prod.snd happ
      simpa [cornerPt] using h'
    rw [hf_eq, hg_eq]
    exact cornerPt_max η hηpos t
  · intro q hq hqε
    have hq_ball : q ∈ Metric.ball p ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      exact hqε
    obtain ⟨⟨hqsrc, hfq_lt⟩, hgq_lt⟩ := hεsub hq_ball
    simp only [Set.mem_ofPred_eq] at hfq_lt hgq_lt
    obtain ⟨hfq_nonpos, hgq_nonpos, hcase⟩ := max_eq_zero_iff.mp hq
    rcases hcase with hfq0 | hgq0
    · have hneg : -g q < η := by
        have h' := abs_of_nonpos hgq_nonpos
        rw [h'] at hgq_lt
        exact hgq_lt
      have ht_nonneg : 0 ≤ -(g q) / η := div_nonneg (by linarith) hηpos.le
      refine ⟨-(g q) / η, ?_, ?_⟩
      · rw [Set.mem_Ioo]
        refine ⟨by linarith, ?_⟩
        rw [div_lt_one hηpos]
        exact hneg
      · have hct : cornerPt η (-(g q) / η) = Φ q := by
          have h1 : η * min (-(g q) / η) 0 = f q := by
            rw [min_eq_right ht_nonneg, mul_zero, hfq0]
          have h2 : -(η * max (-(g q) / η) 0) = g q := by
            rw [max_eq_left ht_nonneg, mul_div_cancel₀ (-(g q)) (ne_of_gt hηpos), neg_neg]
          exact Prod.ext h1 h2
        show Φ.symm (cornerPt η (-(g q) / η)) = q
        rw [hct]
        exact Φ.left_inv hqsrc
    · have hpos : -η < f q := by
        have h' := abs_of_nonpos hfq_nonpos
        rw [h'] at hfq_lt
        linarith
      have ht_nonpos : f q / η ≤ 0 := div_nonpos_of_nonpos_of_nonneg hfq_nonpos hηpos.le
      refine ⟨f q / η, ?_, ?_⟩
      · rw [Set.mem_Ioo]
        refine ⟨?_, by linarith⟩
        rw [lt_div_iff₀ hηpos]
        linarith
      · have hct : cornerPt η (f q / η) = Φ q := by
          have h1 : η * min (f q / η) 0 = f q := by
            rw [min_eq_left ht_nonpos, mul_div_cancel₀ (f q) (ne_of_gt hηpos)]
          have h2 : -(η * max (f q / η) 0) = g q := by
            rw [max_eq_right ht_nonpos, mul_zero, neg_zero]
            exact hgq0.symm
          exact Prod.ext h1 h2
        show Φ.symm (cornerPt η (f q / η)) = q
        rw [hct]
        exact Φ.left_inv hqsrc

end Work.Smooth.BoxGeneric.LocalArc
