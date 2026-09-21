import Mathlib
import Submission.Work.OddRadon.Abel

/-!
# The right derivative of `c ↦ ∫₀^c γ s (c² - s²)^β ds` at the upper limit

`Work.OddCurve.LowSlope.abelTrans_diffQuot_integral_tendsto` identifies the one-sided limit
(`h → 0⁺`) of the difference-quotient integral

`∫ s in 0..c, γ s * (((c+h)² - s²)^β - (c² - s²)^β) / h`

with `2 β c · abelTrans (β-1) γ c = 2 β c ∫₀^c γ s (c² - s²)^(β-1) ds`,
for `γ` continuous and bounded on `(0, 2c)` and `β > 0`.

The mechanism is a dominated-convergence argument (`intervalIntegral.tendsto_integral_filter_of_dominated_convergence`)
applied to the family `h ↦ s ↦ γ s * ((((c+h)² - s²)^β - (c² - s²)^β)/h)`:

* pointwise (`h → 0⁺`, `s ∈ (0,c)`) the bracket converges to `β (c² - s²)^(β-1) · 2c` by the chain
  rule for `Real.rpow` at the positive base `c² - s²`;
* the family is dominated by `M * (β * (2 * (c² - s²)^(β-1) + K) * (3c))`, where `K` is any bound
  for `((c+h)² - s²)^(β-1)` (a constant when `β ≥ 1`, and `(c² - s²)^(β-1)` itself when `β < 1`);
  the singular weight `(c² - s²)^(β-1)` is interval integrable on `(0,c)` because `β - 1 > -1`.

## Auxiliary results

* `rpow_sub_rpow_le_mul_add` — the mean-value-type bound
  `B^β - A^β ≤ β (A^(β-1) + B^(β-1)) (B - A)` for `0 < A ≤ B`, `β > 0`;
* `intervalIntegrable_sq_sub_sq_rpow` — `s ↦ (c² - s²)^p` is interval integrable on `(0,c)` for
  `p > -1`, `c > 0`;
* `exists_diffQuot_rpow_bound` — the uniform domination bound;
* `tendsto_diffQuot_rpow_sq` — the pointwise limit.
-/

namespace Work.OddCurve.LowSlope

open MeasureTheory Filter
open scoped Interval Topology

/-- **A mean-value-type bound for `Real.rpow`.** For `0 < A ≤ B` and `β > 0`,
`B ^ β - A ^ β ≤ β * (A ^ (β - 1) + B ^ (β - 1)) * (B - A)`.

Proof: `B^β - A^β = ∫_A^B β u^(β-1) du`, and `u ↦ u^(β-1)` is monotone on `(0,∞)`; in either
regime its value is at most the sum of the two endpoint values. -/
lemma rpow_sub_rpow_le_mul_add {β A B : ℝ} (hβ : 0 < β) (hA : 0 < A) (hAB : A ≤ B) :
    B ^ β - A ^ β ≤ β * (A ^ (β - 1) + B ^ (β - 1)) * (B - A) := by
  have hcont : ContinuousOn (fun u : ℝ => u ^ (β - 1)) (Set.uIcc A B) := by
    refine continuousOn_id.rpow_const ?_
    intro u hu
    rw [Set.uIcc_of_le hAB, Set.mem_Icc] at hu
    exact Or.inl (ne_of_gt (lt_of_lt_of_le hA hu.1))
  have hint : IntervalIntegrable (fun u : ℝ => β * u ^ (β - 1)) volume A B :=
    hcont.intervalIntegrable.const_mul β
  have hderiv : ∀ u ∈ Set.uIcc A B, HasDerivAt (fun u : ℝ => u ^ β) (β * u ^ (β - 1)) u := by
    intro u hu
    rw [Set.uIcc_of_le hAB, Set.mem_Icc] at hu
    exact Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (lt_of_lt_of_le hA hu.1)))
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hmono : ∀ u ∈ Set.Icc A B, β * u ^ (β - 1) ≤ β * (A ^ (β - 1) + B ^ (β - 1)) := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hA hu.1
    have huB : u ^ (β - 1) ≤ A ^ (β - 1) + B ^ (β - 1) := by
      by_cases h1 : 1 ≤ β
      · have hle : u ^ (β - 1) ≤ B ^ (β - 1) :=
          Real.rpow_le_rpow hu0.le hu.2 (by linarith : 0 ≤ β - 1)
        linarith [Real.rpow_nonneg hA.le (β - 1)]
      · push Not at h1
        have hAu : A ^ (1 - β) ≤ u ^ (1 - β) := Real.rpow_le_rpow hA.le hu.1 (by linarith)
        have hmain : u ^ (β - 1) ≤ A ^ (β - 1) := by
          rw [show β - 1 = -(1 - β) by ring]
          rw [Real.rpow_neg (le_of_lt hu0) (1 - β), Real.rpow_neg hA.le (1 - β)]
          exact (inv_le_inv₀ (Real.rpow_pos_of_pos hu0 _) (Real.rpow_pos_of_pos hA _)).mpr hAu
        exact le_trans hmain (le_add_of_nonneg_right (Real.rpow_nonneg (le_trans hA.le hAB) _))
    exact mul_le_mul_of_nonneg_left huB hβ.le
  have h2 := intervalIntegral.integral_mono_on hAB hint intervalIntegrable_const hmono
  have hconst : (∫ u in A..B, β * (A ^ (β - 1) + B ^ (β - 1)))
      = β * (A ^ (β - 1) + B ^ (β - 1)) * (B - A) := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hFTC, hconst] at h2
  exact h2

/-- For `c > 0` and `p > -1` the (possibly singular) weight `s ↦ (c² - s²)^p` is interval
integrable on `(0,c)`: the singularity at the right endpoint is `(c-s)^p` up to a bounded factor. -/
lemma intervalIntegrable_sq_sub_sq_rpow {c p : ℝ} (hc : 0 < c) (hp : -1 < p) :
    IntervalIntegrable (fun s : ℝ => (c ^ 2 - s ^ 2) ^ p) volume (0 : ℝ) c := by
  have h1 : IntervalIntegrable (fun s : ℝ => (c - s) ^ p) volume (0 : ℝ) c := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := c) hp)
    have h2 := h.comp_sub_left c
    simpa [sub_zero] using h2.symm
  have h2 : ContinuousOn (fun s : ℝ => (c + s) ^ p) (Set.uIcc (0:ℝ) c) := by
    refine (continuous_const.add continuous_id).continuousOn.rpow_const ?_
    intro x hx
    rw [Set.uIcc_of_le hc.le, Set.mem_Icc] at hx
    exact Or.inl (ne_of_gt (by simp only [Pi.add_apply, id_eq]; linarith [hx.1, hc]))
  have h3 := h1.mul_continuousOn h2
  refine h3.congr ?_
  intro s hs
  rw [Set.uIoc_of_le hc.le, Set.mem_Ioc] at hs
  have hcs : 0 ≤ c - s := by linarith [hs.2]
  have hcs' : 0 ≤ c + s := by linarith [hs.1]
  show (c - s) ^ p * (c + s) ^ p = (c ^ 2 - s ^ 2) ^ p
  rw [← Real.mul_rpow hcs hcs']
  ring_nf

/-- **Uniform domination of the difference-quotient integrand.** There is a constant `K ≥ 0` such
that for `0 < h ≤ c`, `0 < s < c` and any `g` with `|g| ≤ M`,
`|g * ((((c+h)² - s²)^β - (c² - s²)^β)/h)| ≤ M * (β * (2 * (c² - s²)^(β-1) + K) * (3c))`. -/
lemma exists_diffQuot_rpow_bound {β M c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (h s g : ℝ), 0 < h → h ≤ c → s ∈ Set.Ioo 0 c → |g| ≤ M →
      |g * ((((c+h)^2 - s^2)^β - (c^2 - s^2)^β)/h)|
        ≤ M * (β * (2 * (c^2 - s^2)^(β-1) + K) * (3*c)) := by
  refine ⟨max 1 ((2*c)^(2*β-2)), le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro h s g hh0 hhc hs hg
  have hK : 0 ≤ max 1 ((2*c)^(2*β-2)) := le_trans zero_le_one (le_max_left _ _)
  have hA : 0 < c ^ 2 - s ^ 2 := by
    have h1 : 0 < c - s := by linarith [hs.2]
    have h2 : 0 < c + s := by linarith [hs.1, hc]
    nlinarith [mul_pos h1 h2]
  have hAle : c ^ 2 - s ^ 2 ≤ (c + h) ^ 2 - s ^ 2 := by
    nlinarith [hh0, hc, sq_nonneg h]
  have hdiff := rpow_sub_rpow_le_mul_add hβ hA hAle
  have hstep1 : (((c+h)^2 - s^2)^β - (c^2 - s^2)^β) / h
      ≤ β * ((c^2-s^2)^(β-1) + ((c+h)^2-s^2)^(β-1)) * (2*c+h) := by
    rw [div_le_iff₀ hh0]
    have hBA : (c+h)^2 - s^2 - (c^2 - s^2) = h*(2*c+h) := by ring
    calc (((c+h)^2 - s^2)^β - (c^2 - s^2)^β)
        ≤ β * ((c^2-s^2)^(β-1) + ((c+h)^2-s^2)^(β-1)) * ((c+h)^2 - s^2 - (c^2 - s^2)) := hdiff
      _ = β * ((c^2-s^2)^(β-1) + ((c+h)^2-s^2)^(β-1)) * (2*c+h) * h := by rw [hBA]; ring
  have hBK : ((c+h)^2-s^2)^(β-1) ≤ (c^2-s^2)^(β-1) + max 1 ((2*c)^(2*β-2)) := by
    by_cases h1 : 1 ≤ β
    · have hch : c + h ≤ 2*c := by linarith
      have hBle : (c+h)^2 - s^2 ≤ (2*c)^2 := by nlinarith [hch, hc, hh0, sq_nonneg s]
      have hle : ((c+h)^2-s^2)^(β-1) ≤ ((2*c)^2)^(β-1) :=
        Real.rpow_le_rpow (by linarith) hBle (by linarith)
      have heq : ((2*c)^2)^(β-1) = (2*c)^(2*β-2) := by
        rw [← Real.rpow_natCast (2*c) 2, ← Real.rpow_mul (by linarith : (0:ℝ) ≤ 2*c)]
        ring_nf
      rw [heq] at hle
      exact le_trans hle (le_trans (le_max_right _ _)
        (le_add_of_nonneg_left (Real.rpow_nonneg hA.le _)))
    · push Not at h1
      have hB0 : (0:ℝ) ≤ (c+h)^2 - s^2 := le_trans hA.le hAle
      have hAu : (c^2-s^2)^(1-β) ≤ ((c+h)^2-s^2)^(1-β) :=
        Real.rpow_le_rpow hA.le hAle (by linarith)
      have hmain : ((c+h)^2-s^2)^(β-1) ≤ (c^2-s^2)^(β-1) := by
        rw [show β - 1 = -(1-β) by ring]
        rw [Real.rpow_neg hB0 (1-β), Real.rpow_neg hA.le (1-β)]
        exact (inv_le_inv₀ (Real.rpow_pos_of_pos (by linarith) _)
          (Real.rpow_pos_of_pos hA _)).mpr hAu
      exact le_trans hmain (le_add_of_nonneg_right hK)
  have hq0 : 0 ≤ (((c+h)^2 - s^2)^β - (c^2 - s^2)^β) / h := by
    have h2 : (c^2-s^2)^β ≤ ((c+h)^2-s^2)^β := Real.rpow_le_rpow hA.le hAle hβ.le
    exact div_nonneg (by linarith) hh0.le
  have hsum : ((c^2-s^2)^(β-1) + ((c+h)^2-s^2)^(β-1))
      ≤ 2 * (c^2-s^2)^(β-1) + max 1 ((2*c)^(2*β-2)) := by linarith
  have hstep2 : β * ((c^2-s^2)^(β-1) + ((c+h)^2-s^2)^(β-1)) * (2*c+h)
      ≤ β * (2 * (c^2-s^2)^(β-1) + max 1 ((2*c)^(2*β-2))) * (3*c) := by
    have h1 : 0 ≤ β * (2 * (c^2-s^2)^(β-1) + max 1 ((2*c)^(2*β-2))) := by
      have h2 : 0 ≤ 2 * (c^2-s^2)^(β-1) + max 1 ((2*c)^(2*β-2)) := by
        linarith [Real.rpow_nonneg hA.le (β-1)]
      exact mul_nonneg hβ.le h2
    calc β * ((c^2-s^2)^(β-1) + ((c+h)^2-s^2)^(β-1)) * (2*c+h)
        ≤ β * (2 * (c^2-s^2)^(β-1) + max 1 ((2*c)^(2*β-2))) * (2*c+h) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hsum hβ.le
          · linarith
      _ ≤ β * (2 * (c^2-s^2)^(β-1) + max 1 ((2*c)^(2*β-2))) * (3*c) := by
          apply mul_le_mul_of_nonneg_left _ h1
          linarith
  rw [abs_mul, abs_of_nonneg hq0]
  exact mul_le_mul hg (le_trans hstep1 hstep2) hq0 (le_trans (abs_nonneg g) hg)

/-- **The pointwise difference-quotient limit.** For `0 ≤ s < c`,
`(((c+h)² - s²)^β - (c² - s²)^β)/h → β (c² - s²)^(β-1) · 2c` as `h → 0⁺`. -/
lemma tendsto_diffQuot_rpow_sq {β c s : ℝ} (hs : s < c) (hs0 : 0 ≤ s) :
    Tendsto (fun h : ℝ => (((c+h)^2 - s^2)^β - (c^2 - s^2)^β) / h)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (β * (c^2 - s^2)^(β-1) * (2*c))) := by
  have hpos : 0 < c^2 - s^2 := by nlinarith
  have hderiv : HasDerivAt (fun x : ℝ => (x^2 - s^2)^β)
      (β * (c^2 - s^2)^(β-1) * (2*c)) c := by
    have h1 : HasDerivAt (fun x : ℝ => x^2 - s^2) (2*c) c := by
      have h := ((hasDerivAt_id c).pow 2).sub_const (s^2)
      simpa using h
    have h2 : HasDerivAt (fun u : ℝ => u^β) (β * (c^2-s^2)^(β-1)) (c^2 - s^2) :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hpos))
    exact h2.comp c h1
  have hsub : Set.Ioi (0:ℝ) ⊆ ({0} : Set ℝ)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt hx
  have key := hderiv.tendsto_slope_zero.mono_left (nhdsWithin_mono (0:ℝ) hsub)
  simpa [div_eq_mul_inv, smul_eq_mul, mul_comm] using key

theorem abelTrans_diffQuot_integral_tendsto {β M c : ℝ} (hβ : 0 < β) (hc : 0 < c) {γ : ℝ → ℝ}
    (hγc : ContinuousOn γ (Set.Ioo (0 : ℝ) (2 * c)))
    (hγb : ∀ s ∈ Set.Ioo (0 : ℝ) (2 * c), |γ s| ≤ M) :
    Filter.Tendsto
      (fun h : ℝ => ∫ s in (0 : ℝ)..c,
        γ s * (((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) / h)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (2 * β * c * Work.OddRadon.abelTrans (β - 1) γ c)) := by
  obtain ⟨K, hK0, hbound⟩ := exists_diffQuot_rpow_bound hβ hc
  let bound : ℝ → ℝ := fun s => M * (β * (2 * (c ^ 2 - s ^ 2) ^ (β - 1) + K) * (3 * c))
  -- the point `s = c` is the only one where the domination at `h → 0⁺` may fail; drop it
  have hae : ∀ᵐ s ∂volume, s ∉ ({c} : Set ℝ) := compl_mem_ae_iff.mpr (measure_singleton c)
  -- eventually `h` lies in `(0, c]`
  have hev : ∀ᶠ h in nhdsWithin (0:ℝ) (Set.Ioi 0), h ∈ Set.Ioc 0 c := by
    rw [eventually_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds hc] with h hh hpos
    exact ⟨hpos, le_of_lt hh⟩
  have hBint : IntervalIntegrable bound volume (0:ℝ) c := by
    have h1 : IntervalIntegrable (fun s : ℝ => (c^2 - s^2)^(β-1)) volume (0:ℝ) c :=
      intervalIntegrable_sq_sub_sq_rpow hc (by linarith)
    have h2 : IntervalIntegrable (fun s : ℝ => 2 * (c^2 - s^2)^(β-1)) volume (0:ℝ) c :=
      h1.const_mul 2
    have h3 : IntervalIntegrable (fun s : ℝ => 2 * (c^2 - s^2)^(β-1) + K) volume (0:ℝ) c :=
      h2.add intervalIntegrable_const
    have h4 : IntervalIntegrable (fun s : ℝ => β * (2 * (c^2 - s^2)^(β-1) + K)) volume (0:ℝ) c :=
      h3.const_mul β
    have h5 : IntervalIntegrable
        (fun s : ℝ => β * (2 * (c^2 - s^2)^(β-1) + K) * (3*c)) volume (0:ℝ) c :=
      h4.mul_const (3*c)
    show IntervalIntegrable
      (fun s : ℝ => M * (β * (2 * (c^2 - s^2)^(β-1) + K) * (3*c))) volume (0:ℝ) c
    exact h5.const_mul M
  have hDCT : Tendsto (fun h : ℝ => ∫ s in (0:ℝ)..c,
        γ s * ((((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) / h))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ s in (0:ℝ)..c, γ s * (β * (c ^ 2 - s ^ 2) ^ (β - 1) * (2 * c)))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (a := (0:ℝ)) (b := c) (l := nhdsWithin (0:ℝ) (Set.Ioi 0))
      (F := fun h s => γ s * ((((c + h) ^ 2 - s ^ 2) ^ β - (c ^ 2 - s ^ 2) ^ β) / h))
      (f := fun s => γ s * (β * (c ^ 2 - s ^ 2) ^ (β - 1) * (2 * c))) bound ?_ ?_ hBint ?_
    · filter_upwards with h
      have hγmeas : AEStronglyMeasurable γ (volume.restrict (Set.uIoc (0:ℝ) c)) := by
        have hsub : Set.Ioc (0:ℝ) c ⊆ Set.Ioo (0:ℝ) (2*c) :=
          fun x hx => ⟨hx.1, by linarith [hx.2, hc]⟩
        have h' := (hγc.mono hsub).aestronglyMeasurable (μ := volume) measurableSet_Ioc
        simpa [Set.uIoc_of_le hc.le] using h'
      have h2 : AEStronglyMeasurable (fun s : ℝ => (((c+h)^2 - s^2)^β - (c^2-s^2)^β)/h)
          (volume.restrict (Set.uIoc (0:ℝ) c)) := by
        apply Measurable.aestronglyMeasurable
        fun_prop
      exact hγmeas.mul h2
    · filter_upwards [hev] with h hh
      filter_upwards [hae] with s hsne hsmem
      rw [Set.uIoc_of_le hc.le, Set.mem_Ioc] at hsmem
      have hsc : s ≠ c := fun hcontra => hsne (by simp [hcontra])
      have hs : s ∈ Set.Ioo 0 c := ⟨hsmem.1, lt_of_le_of_ne hsmem.2 hsc⟩
      have hgs : |γ s| ≤ M := hγb s ⟨hs.1, by linarith [hs.2, hc]⟩
      have hres := hbound h s (γ s) hh.1 hh.2 hs hgs
      simpa only [bound, Real.norm_eq_abs] using hres
    · filter_upwards [hae] with s hsne hsmem
      rw [Set.uIoc_of_le hc.le, Set.mem_Ioc] at hsmem
      have hsc : s ≠ c := fun hcontra => hsne (by simp [hcontra])
      have hs : s < c := lt_of_le_of_ne hsmem.2 hsc
      exact (tendsto_diffQuot_rpow_sq hs hsmem.1.le).const_mul (γ s)
  -- identify the limit with `2 β c · abelTrans (β-1) γ c`
  have hlim : (∫ s in (0:ℝ)..c, γ s * (β * (c ^ 2 - s ^ 2) ^ (β - 1) * (2 * c)))
      = 2 * β * c * Work.OddRadon.abelTrans (β - 1) γ c := by
    rw [Work.OddRadon.abelTrans, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    ring
  rw [hlim] at hDCT
  -- match the shape of the integrand (`a * b / h` vs `a * (b / h)`)
  refine hDCT.congr' (Eventually.of_forall (fun h => ?_))
  exact intervalIntegral.integral_congr (fun s _ => by rw [mul_div_assoc])

end Work.OddCurve.LowSlope
