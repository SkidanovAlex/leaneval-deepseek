import Mathlib
import Submission.Work.Smooth.SphereJordan.Caratheodory.Jacobian

/-!
# The length–area principle (infrastructure)
-/

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ENNReal

namespace Work.Smooth.SphereJordan.Caratheodory

/-! ## Polar coordinates centred at a point -/

/-- **Polar coordinates around an arbitrary point.** -/
lemma lintegral_polar_comp (φ : ℂ → ℝ≥0∞) (ζ : ℂ) :
    (∫⁻ z, φ z) = ∫⁻ p in Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal p.1 * φ (ζ + Complex.polarCoord.symm p) := by
  have h1 : (∫⁻ p in Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        ENNReal.ofReal p.1 * φ (ζ + Complex.polarCoord.symm p)) = ∫⁻ p, φ (ζ + p) := by
    have h := Complex.lintegral_comp_polarCoord_symm (fun z : ℂ => φ (ζ + z))
    simp only [smul_eq_mul] at h
    convert h using 2 <;> rfl
  rw [h1]
  rw [show (∫⁻ p : ℂ, φ (ζ + p)) = ∫⁻ p, φ (p + ζ) from
    lintegral_congr fun p => by rw [add_comm]]
  exact (lintegral_add_right_eq_self φ ζ).symm

/-! ## Translation, periodicity and splitting of interval integrals -/

/-- Shifting the interval of integration. -/
lemma lintegral_Ioo_add_right (F : ℝ → ℝ≥0∞) (a b c : ℝ) :
    (∫⁻ θ in Set.Ioo (a + c) (b + c), F θ) = ∫⁻ θ in Set.Ioo a b, F (θ + c) := by
  rw [← lintegral_indicator measurableSet_Ioo, ← lintegral_indicator measurableSet_Ioo]
  have h : ∀ θ : ℝ, (Set.Ioo a b).indicator (fun θ => F (θ + c)) θ
      = (Set.Ioo (a + c) (b + c)).indicator F (θ + c) := by
    intro θ
    by_cases hθ : θ ∈ Set.Ioo a b
    · have hθ' : θ + c ∈ Set.Ioo (a + c) (b + c) := ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
      rw [Set.indicator_of_mem hθ, Set.indicator_of_mem hθ']
    · have hθ' : θ + c ∉ Set.Ioo (a + c) (b + c) := by
        intro hh; exact hθ ⟨by linarith [hh.1], by linarith [hh.2]⟩
      rw [Set.indicator_of_notMem hθ, Set.indicator_of_notMem hθ']
  rw [lintegral_congr h]
  exact (lintegral_add_right_eq_self _ c).symm

/-- A `2π`-periodic function has the same integral over the translate of an interval by `2π`. -/
lemma lintegral_Ioo_periodic (F : ℝ → ℝ≥0∞) (hF : ∀ θ, F (θ + 2 * Real.pi) = F θ) (a b : ℝ) :
    (∫⁻ θ in Set.Ioo (a + 2 * Real.pi) (b + 2 * Real.pi), F θ) = ∫⁻ θ in Set.Ioo a b, F θ := by
  rw [lintegral_Ioo_add_right F a b (2 * Real.pi)]
  exact lintegral_congr fun θ => hF θ

/-- Splitting an interval at an interior point. -/
lemma lintegral_Ioo_split (F : ℝ → ℝ≥0∞) {a b c : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    (∫⁻ θ in Set.Ioo a b, F θ) = (∫⁻ θ in Set.Ioo a c, F θ) + ∫⁻ θ in Set.Ioo c b, F θ := by
  have hdisj : Disjoint (Set.Ioo a c) (Set.Ioo c b) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx'.1 (not_lt.mpr hx.2.le)
  have hunion : Set.Ioo a c ∪ Set.Ioo c b = Set.Ioo a b \ {c} := by
    ext x; constructor
    · rintro (h | h)
      · exact ⟨⟨h.1, lt_of_lt_of_le h.2 hcb⟩, fun hx => absurd (hx ▸ h.2) (lt_irrefl c)⟩
      · exact ⟨⟨lt_of_le_of_lt hac h.1, h.2⟩, fun hx => absurd (hx ▸ h.1) (lt_irrefl c)⟩
    · rintro ⟨h, hc⟩
      rcases lt_trichotomy x c with h' | h' | h'
      · exact Or.inl ⟨h.1, h'⟩
      · exact absurd (Set.mem_singleton_iff.mpr h') hc
      · exact Or.inr ⟨h', h.2⟩
  have h1 : (∫⁻ θ in Set.Ioo a c ∪ Set.Ioo c b, F θ)
      = (∫⁻ θ in Set.Ioo a c, F θ) + ∫⁻ θ in Set.Ioo c b, F θ := by
    rw [Measure.restrict_union hdisj measurableSet_Ioo, lintegral_add_measure]
  have h2 : (∫⁻ θ in Set.Ioo a b \ {c}, F θ) = ∫⁻ θ in Set.Ioo a b, F θ := by
    rw [← lintegral_indicator (measurableSet_Ioo.diff (measurableSet_singleton c)),
      ← lintegral_indicator measurableSet_Ioo]
    refine lintegral_congr_ae ?_
    have hae : ∀ᶠ θ in MeasureTheory.ae (volume : Measure ℝ), θ ∉ ({c} : Set ℝ) := by
      rw [MeasureTheory.ae_iff]
      simpa using (measure_singleton (c : ℝ))
    filter_upwards [hae] with θ hθ
    by_cases h : θ ∈ Set.Ioo a b
    · have h1 : θ ∈ Set.Ioo a b \ {c} := ⟨h, hθ⟩
      rw [Set.indicator_of_mem h1, Set.indicator_of_mem h]
    · have h1 : θ ∉ Set.Ioo a b \ {c} := fun hh => h hh.1
      rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h]
  rw [← h1, hunion, h2]

/-- Shifting an interval by an integer multiple of `2π`. -/
lemma lintegral_Ioo_periodic_int (F : ℝ → ℝ≥0∞) (hF : ∀ θ, F (θ + 2 * Real.pi) = F θ)
    (m : ℤ) (a b : ℝ) :
    (∫⁻ θ in Set.Ioo (a + (m:ℝ) * (2 * Real.pi)) (b + (m:ℝ) * (2 * Real.pi)), F θ)
      = ∫⁻ θ in Set.Ioo a b, F θ := by
  rw [lintegral_Ioo_add_right F a b ((m:ℝ) * (2 * Real.pi))]
  refine lintegral_congr fun θ => ?_
  have hper : Function.Periodic F (2 * Real.pi) := fun x => hF x
  have h := hper.int_mul m θ
  simpa using h

/-- A `2π`-periodic function has the same integral over any interval of length `2π`. -/
lemma lintegral_Ioo_period_eq (F : ℝ → ℝ≥0∞) (hF : ∀ θ, F (θ + 2 * Real.pi) = F θ) (a : ℝ) :
    (∫⁻ θ in Set.Ioo a (a + 2 * Real.pi), F θ)
      = ∫⁻ θ in Set.Ioo (-Real.pi) Real.pi, F θ := by
  have h2π : (0:ℝ) < 2 * Real.pi := by positivity
  obtain ⟨m, hm1, hm2⟩ : ∃ m : ℤ, -Real.pi ≤ a - (m:ℝ) * (2*Real.pi) ∧
      a - (m:ℝ) * (2*Real.pi) < Real.pi := by
    refine ⟨⌊(a + Real.pi) / (2 * Real.pi)⌋, ?_, ?_⟩
    · have h := Int.floor_le ((a + Real.pi) / (2 * Real.pi))
      have h' : ((⌊(a + Real.pi) / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2*Real.pi) ≤ a + Real.pi := by
        have h2 := mul_le_mul_of_nonneg_right h (le_of_lt h2π)
        rwa [div_mul_cancel₀ _ (ne_of_gt h2π)] at h2
      linarith
    · have h := Int.lt_floor_add_one ((a + Real.pi) / (2 * Real.pi))
      have h' : a + Real.pi < (((⌊(a + Real.pi) / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1) * (2*Real.pi) := by
        have h2 := mul_lt_mul_of_pos_right h h2π
        rwa [div_mul_cancel₀ _ (ne_of_gt h2π)] at h2
      push_cast at h'
      linarith
  set b : ℝ := a - (m:ℝ) * (2*Real.pi) with hb
  rw [show a = b + (m:ℝ) * (2 * Real.pi) from by rw [hb]; ring,
    show b + (m:ℝ) * (2 * Real.pi) + 2 * Real.pi
      = (b + 2 * Real.pi) + (m:ℝ) * (2 * Real.pi) from by ring,
    lintegral_Ioo_periodic_int F hF m b (b + 2 * Real.pi)]
  rcases lt_or_eq_of_le hm1 with hlt | heq
  · have hb2 : b < Real.pi := hm2
    rw [lintegral_Ioo_split F (a := b) (b := b + 2 * Real.pi) (c := Real.pi)
        (by linarith) (by linarith),
      lintegral_Ioo_split F (a := -Real.pi) (b := Real.pi) (c := b)
        (by linarith) (by linarith)]
    have h3 : (∫⁻ θ in Set.Ioo Real.pi (b + 2 * Real.pi), F θ)
        = ∫⁻ θ in Set.Ioo (-Real.pi) b, F θ := by
      have h := lintegral_Ioo_add_right F (-Real.pi) b (2 * Real.pi)
      rw [show -Real.pi + 2 * Real.pi = Real.pi from by ring] at h
      rw [h]
      exact lintegral_congr fun θ => hF θ
    rw [h3]
    ring
  · rw [← heq, show -Real.pi + 2 * Real.pi = Real.pi from by ring]

/-- **The `L¹` version of the length–area principle.**  If the density `D` is integrable over a
neighbourhood of `0`, then there are arbitrarily small radii at which `r * D r` is small. -/
lemma exists_small_density {D : ℝ → ℝ≥0∞} {r₀ M : ℝ} (hr₀ : 0 < r₀) (hM : 0 < M)
    (hfin : ∫⁻ r in Set.Ioo (0:ℝ) r₀, D r < ⊤) :
    ∃ r ∈ Set.Ioo 0 r₀, ENNReal.ofReal r * D r ≤ ENNReal.ofReal M := by
  by_contra h
  push Not at h
  have hM2 : (0:ℝ) < M / 2 := by linarith
  have key : ∀ k : ℕ,
      ENNReal.ofReal (M / 2) ≤ ∫⁻ r in Set.Ioo (r₀ / 2^(k+1)) (r₀ / 2^k), D r := by
    intro k
    have hpow : (0:ℝ) < (2:ℝ)^k := by positivity
    have hge1 : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    have hpt : ∀ r ∈ Set.Ioo (r₀ / 2^(k+1)) (r₀ / 2^k),
        ENNReal.ofReal M * (ENNReal.ofReal r)⁻¹ ≤ D r := by
      intro r hr
      have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr.1.le
      have hrlt : r < r₀ := by
        have h2 : r₀ / 2^k ≤ r₀ := by
          rw [div_le_iff₀ hpow]
          nlinarith [hge1, hr₀]
        linarith [hr.2, h2]
      have h1 : ENNReal.ofReal M / ENNReal.ofReal r < D r := by
        rw [ENNReal.div_lt_iff (Or.inl (by positivity)) (Or.inl (by simp))]
        rw [mul_comm]
        exact h r ⟨hr0, hrlt⟩
      rw [ENNReal.div_eq_inv_mul, mul_comm] at h1
      exact h1.le
    have hpt2 : ∀ r ∈ Set.Ioo (r₀ / 2^(k+1)) (r₀ / 2^k),
        ENNReal.ofReal ((2:ℝ)^k / r₀) ≤ (ENNReal.ofReal r)⁻¹ := by
      intro r hr
      have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hr.1.le
      rw [show (2:ℝ)^k / r₀ = (r₀ / 2^k)⁻¹ from by rw [inv_div],
        ← ENNReal.ofReal_inv_of_pos hr0]
      refine ENNReal.ofReal_le_ofReal ?_
      exact (inv_le_inv₀ (by positivity : (0:ℝ) < r₀ / 2^k) hr0).mpr hr.2.le
    have hhalf : ENNReal.ofReal ((2:ℝ)^k / r₀) * ENNReal.ofReal (r₀ / 2^(k+1))
        = ENNReal.ofReal (1/2) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
      ring_nf
    calc ENNReal.ofReal (M / 2)
        = ENNReal.ofReal M * ENNReal.ofReal (1/2) := by
          rw [← ENNReal.ofReal_mul (le_of_lt hM)]; congr 1; ring
      _ = ENNReal.ofReal M * (ENNReal.ofReal ((2:ℝ)^k / r₀)
            * ENNReal.ofReal (r₀ / 2^(k+1))) := by rw [hhalf]
      _ = ENNReal.ofReal M * (ENNReal.ofReal ((2:ℝ)^k / r₀)
            * volume (Set.Ioo (r₀ / 2^(k+1)) (r₀ / 2^k))) := by
          congr 1
          rw [Real.volume_Ioo]
          congr 1
          ring
      _ = ENNReal.ofReal M * ∫⁻ r in Set.Ioo (r₀ / 2^(k+1)) (r₀ / 2^k),
            ENNReal.ofReal ((2:ℝ)^k / r₀) := by
          rw [lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ENNReal.ofReal M * ∫⁻ r in Set.Ioo (r₀ / 2^(k+1)) (r₀ / 2^k),
            (ENNReal.ofReal r)⁻¹ := by
          refine mul_le_mul' le_rfl ?_
          refine lintegral_mono_ae ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with r hr
          exact hpt2 r hr
      _ = ∫⁻ r in Set.Ioo (r₀ / 2^(k+1)) (r₀ / 2^k),
            ENNReal.ofReal M * (ENNReal.ofReal r)⁻¹ := by
          rw [lintegral_const_mul' (μ := volume.restrict (Set.Ioo (r₀ / 2^(k+1)) (r₀ / 2^k)))
            (ENNReal.ofReal M) _ (ENNReal.ofReal_ne_top)]
      _ ≤ ∫⁻ r in Set.Ioo (r₀ / 2^(k+1)) (r₀ / 2^k), D r := by
          refine lintegral_mono_ae ?_
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with r hr
          exact hpt r hr
  have hsum : ∀ N : ℕ,
      (N : ℝ≥0∞) * ENNReal.ofReal (M/2) ≤ ∫⁻ r in Set.Ioo (0:ℝ) r₀, D r := by
    intro N
    have hdisj : Set.PairwiseDisjoint (↑(Finset.range N) : Set ℕ)
        (fun k => Set.Ioo (r₀ / 2^(k+1)) (r₀ / 2^k)) := by
      intro i _ j _ hij
      rw [Function.onFun, Set.disjoint_left]
      intro x hx hx'
      simp only [Set.mem_Ioo] at hx hx'
      rcases lt_or_gt_of_ne hij with hlt | hlt
      · have hle : (2:ℝ)^(i+1) ≤ 2^j := pow_le_pow_right₀ (by norm_num) (by omega)
        have h1 : r₀ / 2^j ≤ r₀ / 2^(i+1) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hr₀)
          exact (inv_le_inv₀ (by positivity : (0:ℝ) < 2^j) (by positivity : (0:ℝ) < 2^(i+1))).mpr hle
        linarith [hx.1, hx'.2, h1]
      · have hle : (2:ℝ)^(j+1) ≤ 2^i := pow_le_pow_right₀ (by norm_num) (by omega)
        have h1 : r₀ / 2^i ≤ r₀ / 2^(j+1) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hr₀)
          exact (inv_le_inv₀ (by positivity : (0:ℝ) < 2^i) (by positivity : (0:ℝ) < 2^(j+1))).mpr hle
        linarith [hx'.1, hx.2, h1]
    have hb : (⋃ k ∈ Finset.range N, Set.Ioo (r₀ / 2^(k+1)) (r₀ / 2^k)) ⊆ Set.Ioo (0:ℝ) r₀ := by
      intro x hx
      simp only [Set.mem_iUnion, Finset.mem_range] at hx
      obtain ⟨k, _, hk1, hk2⟩ := hx
      refine ⟨?_, ?_⟩
      · have : 0 < r₀ / 2^(k+1) := by positivity
        linarith [hk1]
      · have h2 : r₀ / 2^k ≤ r₀ := by
          have hge1 : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
          rw [div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^k)]
          nlinarith [hge1, hr₀]
        linarith [hk2, h2]
    calc (N : ℝ≥0∞) * ENNReal.ofReal (M/2)
        = ∑ k ∈ Finset.range N, ENNReal.ofReal (M/2) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ k ∈ Finset.range N, ∫⁻ r in Set.Ioo (r₀ / 2^(k+1)) (r₀ / 2^k), D r :=
          Finset.sum_le_sum fun k _ => key k
      _ = ∫⁻ r in ⋃ k ∈ Finset.range N, Set.Ioo (r₀ / 2^(k+1)) (r₀ / 2^k), D r := by
          rw [lintegral_biUnion_finset hdisj (fun _ _ => measurableSet_Ioo)]
      _ ≤ ∫⁻ r in Set.Ioo (0:ℝ) r₀, D r :=
          lintegral_mono_set (Subset.rfl.trans hb)
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_of_lt hfin)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (n : ℝ≥0∞) < (N : ℝ≥0∞) * ENNReal.ofReal (M/2) := by
    have hc : (0:ℝ) < M/2 := hM2
    refine ⟨⌊(n:ℝ)/(M/2)⌋₊ + 1, ?_⟩
    have hlt : (n:ℝ) < (⌊(n:ℝ)/(M/2)⌋₊ + 1) * (M/2) := by
      have h4 : (n:ℝ)/(M/2) < (⌊(n:ℝ)/(M/2)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
      have h5 := mul_lt_mul_of_pos_right h4 hc
      rwa [div_mul_cancel₀ _ (ne_of_gt hc)] at h5
    calc (n : ℝ≥0∞) = ENNReal.ofReal (n:ℝ) := (ENNReal.ofReal_natCast n).symm
      _ < ENNReal.ofReal ((⌊(n:ℝ)/(M/2)⌋₊ + 1 : ℕ) * (M/2)) :=
          (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by push_cast; exact hlt)
      _ = ENNReal.ofReal ((⌊(n:ℝ)/(M/2)⌋₊ + 1 : ℕ) : ℝ) * ENNReal.ofReal (M/2) := by
          rw [ENNReal.ofReal_mul (by positivity)]
      _ = ((⌊(n:ℝ)/(M/2)⌋₊ + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (M/2) := by
          rw [← ENNReal.ofReal_natCast]
  exact absurd (lt_of_lt_of_le hN (hsum N)) (not_lt.mpr hn.le)

end Work.Smooth.SphereJordan.Caratheodory
