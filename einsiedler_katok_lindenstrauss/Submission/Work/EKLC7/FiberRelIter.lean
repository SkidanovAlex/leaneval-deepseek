import Mathlib
import Submission.Work.EKLC7.Defs
import Submission.Work.EKLC7.FiberRel

/-!
# `Work.EKLC7.FiberRelIter`

The iterated (Fubini-free) form of `Work.EKLC7.FiberRel`: the commutator-translation relation
for the triple of leafwise measures of a Heisenberg configuration, stated as an iterated a.e.
statement `∀ᵐ x ∂νij, ∀ᵐ y ∂νjk, ...` rather than as an a.e. statement for the product measure.

The proof repeats the argument of `FiberRel` (the product-formula comparison of `TripleA` and
`TripleB` in root-group coordinates, then the transfer to `SL₃(ℝ)`), but discharges the
measure-determination step with `frit_tentDet` (a self-contained proof that the trapezoid test
functions determine a locally finite measure on `ℝ`), and finishes with the general Fubini-type
implication `Measure.ae_ae_of_ae_prod`.

Since `Work.EKLC7.tent` and `Work.EKLC7.tentFormula` have the same defining body, `frit_tentDet`
below is also a usable proof of the statement of `Work.EKLC7.TentDetermine` (the only difference
is the name under which the trapezoid is spelled): its axioms are exactly
`propext`, `Classical.choice`, `Quot.sound`.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.style.longLine false

noncomputable section

namespace Work.EKLC7

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

/-! ## Measure determination from the trapezoid test functions -/

theorem frit_tent_nonneg (a b : ℚ) (n : ℕ) (t : ℝ) : 0 ≤ tent a b n t := by
  simp only [tent]
  exact le_max_left _ _

theorem frit_tent_le_one (a b : ℚ) (n : ℕ) (t : ℝ) : tent a b n t ≤ 1 := by
  simp only [tent]
  exact max_le zero_le_one (min_le_left _ _)

theorem frit_tent_support {a b : ℚ} {n : ℕ} {t : ℝ} (ht : tent a b n t ≠ 0) :
    (a : ℝ) ≤ t ∧ t ≤ (b : ℝ) + 1 := by
  have hn : n ≠ 0 := by
    rintro rfl
    exact ht (by simp [tent])
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hX : 0 < (n : ℝ) * (t - (a : ℝ)) := by
    by_contra h
    have h' : (n : ℝ) * (t - (a : ℝ)) ≤ 0 := not_lt.mp h
    refine ht ?_
    simp only [tent]
    exact max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) h'))
  have hY : 0 < 1 + (n : ℝ) * ((b : ℝ) - t) := by
    by_contra h
    have h' : 1 + (n : ℝ) * ((b : ℝ) - t) ≤ 0 := not_lt.mp h
    refine ht ?_
    simp only [tent]
    exact max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) h'))
  have hta : (a : ℝ) < t := by
    by_contra h
    have h' : t - (a : ℝ) ≤ 0 := by linarith [not_lt.mp h]
    have := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hnpos) h'
    linarith
  constructor
  · exact le_of_lt hta
  · by_contra hcon
    have hge : (b : ℝ) + 1 < t := not_le.mp hcon
    have hbt : (b : ℝ) - t < -1 := by linarith
    have hm : (n : ℝ) * ((b : ℝ) - t) < (n : ℝ) * (-1) := mul_lt_mul_of_pos_left hbt hnpos
    nlinarith [hY, hm, hn1]

theorem frit_tentDet {γ δ : Measure ℝ} [IsFiniteMeasureOnCompacts γ]
    [IsFiniteMeasureOnCompacts δ]
    (h : ∀ (a b : ℚ) (n : ℕ), ∫ t, tent a b n t ∂γ = ∫ t, tent a b n t ∂δ) :
    γ = δ := by
  classical
  refine Measure.ext_of_Ioc γ δ ?_
  intro a b hab
  have hAex : ∀ n : ℕ, ∃ q : ℚ, a < (q : ℝ) ∧ (q : ℝ) < a + 1 / ((n : ℝ) + 1) := fun n => by
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show a < a + 1 / ((n : ℝ) + 1) by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith)
    exact ⟨q, h1, h2⟩
  have hBex : ∀ n : ℕ, ∃ q : ℚ, b < (q : ℝ) ∧ (q : ℝ) < b + 1 / ((n : ℝ) + 1) := fun n => by
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show b < b + 1 / ((n : ℝ) + 1) by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith)
    exact ⟨q, h1, h2⟩
  choose A hA1 hA2 using hAex
  choose B hB1 hB2 using hBex
  have hfrac : ∀ n : ℕ, (n : ℝ) * (1 / ((n : ℝ) + 1)) ≤ 1 := by
    intro n
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  have hpt : ∀ t : ℝ, Tendsto (fun n : ℕ => tent (A n) (B n) n t) atTop
      (𝓝 ((Set.Ioc a b).indicator (fun _ => (1 : ℝ)) t)) := by
    intro t
    by_cases hta : t ≤ a
    · have hzero : ∀ n : ℕ, tent (A n) (B n) n t = 0 := by
        intro n
        have hnonpos : (n : ℝ) * (t - (A n : ℝ)) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) (by linarith [hA1 n])
        simp only [tent]
        exact max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) hnonpos))
      have hind : (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) t = 0 :=
        Set.indicator_of_notMem (by simp only [Set.mem_Ioc]; exact fun hc => absurd hc.1 (not_lt.mpr hta)) _
      rw [hind]
      have hconst : (fun n : ℕ => tent (A n) (B n) n t) = fun _ => (0 : ℝ) := funext hzero
      rw [hconst]
      exact tendsto_const_nhds
    · have hta' : a < t := not_le.mp hta
      by_cases htb : t ≤ b
      · obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, (2 : ℝ) ≤ (n : ℝ) * (t - a) := by
          refine ⟨⌈2 / (t - a)⌉₊, fun n hn => ?_⟩
          have hpos : (0 : ℝ) < t - a := by linarith
          exact (div_le_iff₀ hpos).mp (le_trans (Nat.le_ceil _) (by exact_mod_cast hn))
        have hev : ∀ᶠ n in atTop, tent (A n) (B n) n t = 1 := by
          refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
          have h2n : (2 : ℝ) ≤ (n : ℝ) * (t - a) := hN n hn
          have hnpos : (0 : ℝ) < (n : ℝ) := by
            rcases Nat.eq_zero_or_pos n with h0 | h0
            · rw [h0] at h2n; norm_num at h2n
            · exact_mod_cast h0
          have hmul : (n : ℝ) * (t - a - 1 / ((n : ℝ) + 1)) < (n : ℝ) * (t - (A n : ℝ)) :=
            mul_lt_mul_of_pos_left (by linarith [hA2 n]) hnpos
          have hexp : (n : ℝ) * (t - a - 1 / ((n : ℝ) + 1))
              = (n : ℝ) * (t - a) - (n : ℝ) * (1 / ((n : ℝ) + 1)) := by ring
          have h1 : (1 : ℝ) ≤ (n : ℝ) * (t - (A n : ℝ)) := by
            nlinarith [hmul, hexp, hfrac n, h2n]
          have h2 : (0 : ℝ) ≤ (n : ℝ) * ((B n : ℝ) - t) :=
            mul_nonneg (Nat.cast_nonneg n) (by linarith [hB1 n])
          have hinner : (1 : ℝ) ≤ min ((n : ℝ) * (t - (A n : ℝ)))
              (1 + (n : ℝ) * ((B n : ℝ) - t)) := le_min h1 (by linarith)
          simp only [tent]
          rw [min_eq_left hinner]
          exact max_eq_right zero_le_one
        have hind : (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) t = 1 :=
          Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hta', htb⟩) _
        rw [hind]
        exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).congr'
          (hev.mono fun n hn => hn.symm)
      · have hbt : b < t := not_le.mp htb
        obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, (2 : ℝ) ≤ (n : ℝ) * (t - b) := by
          refine ⟨⌈2 / (t - b)⌉₊, fun n hn => ?_⟩
          have hpos : (0 : ℝ) < t - b := by linarith
          exact (div_le_iff₀ hpos).mp (le_trans (Nat.le_ceil _) (by exact_mod_cast hn))
        have hev : ∀ᶠ n in atTop, tent (A n) (B n) n t = 0 := by
          refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
          have h2n : (2 : ℝ) ≤ (n : ℝ) * (t - b) := hN n hn
          have hnpos : (0 : ℝ) < (n : ℝ) := by
            rcases Nat.eq_zero_or_pos n with h0 | h0
            · rw [h0] at h2n; norm_num at h2n
            · exact_mod_cast h0
          have hmul : (n : ℝ) * ((B n : ℝ) - t) < (n : ℝ) * (b - t + 1 / ((n : ℝ) + 1)) :=
            mul_lt_mul_of_pos_left (by linarith [hB2 n]) hnpos
          have hexp : (n : ℝ) * (b - t + 1 / ((n : ℝ) + 1))
              = (n : ℝ) * (b - t) + (n : ℝ) * (1 / ((n : ℝ) + 1)) := by ring
          have hneg : 1 + (n : ℝ) * ((B n : ℝ) - t) < 0 := by
            nlinarith [hmul, hexp, hfrac n, h2n]
          simp only [tent]
          exact max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) hneg.le))
        have hind : (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) t = 0 :=
          Set.indicator_of_notMem (by simp only [Set.mem_Ioc]; exact fun hc => absurd hc.2 (not_le.mpr hbt)) _
        rw [hind]
        exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
          (hev.mono fun n hn => hn.symm)
  have hb_meas : MeasurableSet (Set.Icc a (b + 2)) := measurableSet_Icc
  have hbγ : Integrable ((Set.Icc a (b + 2)).indicator (fun _ => (1 : ℝ))) γ := by
    rw [MeasureTheory.integrable_indicator_iff hb_meas]
    exact MeasureTheory.integrableOn_const (C := (1 : ℝ))
      (hs := (isCompact_Icc (a := a) (b := b + 2)).measure_lt_top.ne)
  have hbδ : Integrable ((Set.Icc a (b + 2)).indicator (fun _ => (1 : ℝ))) δ := by
    rw [MeasureTheory.integrable_indicator_iff hb_meas]
    exact MeasureTheory.integrableOn_const (C := (1 : ℝ))
      (hs := (isCompact_Icc (a := a) (b := b + 2)).measure_lt_top.ne)
  have hbnd : ∀ (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ], ∀ n : ℕ, ∀ᵐ t ∂μ,
      ‖tent (A n) (B n) n t‖ ≤ (Set.Icc a (b + 2)).indicator (fun _ => (1 : ℝ)) t := by
    intro μ _ n
    refine Filter.Eventually.of_forall fun t => ?_
    by_cases ht : tent (A n) (B n) n t = 0
    · rw [ht, norm_zero]
      by_cases hmem : t ∈ Set.Icc a (b + 2)
      · rw [Set.indicator_of_mem hmem]
        exact zero_le_one
      · rw [Set.indicator_of_notMem hmem]
    · obtain ⟨h1, h2⟩ := frit_tent_support ht
      have hmem : t ∈ Set.Icc a (b + 2) := by
        refine ⟨?_, ?_⟩
        · linarith [hA1 n, h1]
        · have hle1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]
            linarith
          linarith [hB2 n, h2, hle1]
      rw [Set.indicator_of_mem hmem, Real.norm_eq_abs,
        abs_of_nonneg (frit_tent_nonneg (A n) (B n) n t)]
      exact frit_tent_le_one (A n) (B n) n t
  have hlimγ : Tendsto (fun n : ℕ => ∫ t, tent (A n) (B n) n t ∂γ) atTop
      (𝓝 (γ.real (Set.Ioc a b))) := by
    have hmain := tendsto_integral_of_dominated_convergence (μ := γ)
      (F := fun (n : ℕ) (t : ℝ) => tent (A n) (B n) n t)
      (f := fun t : ℝ => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) t)
      ((Set.Icc a (b + 2)).indicator (fun _ => (1 : ℝ)))
      (fun n => (fr_continuous_tent (A n) (B n) n).aestronglyMeasurable) hbγ (hbnd γ)
      (Filter.Eventually.of_forall hpt)
    have hgoal : (∫ t, (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) t ∂γ) = γ.real (Set.Ioc a b) :=
      MeasureTheory.integral_indicator_one measurableSet_Ioc
    rw [hgoal] at hmain
    exact hmain
  have hlimδ : Tendsto (fun n : ℕ => ∫ t, tent (A n) (B n) n t ∂δ) atTop
      (𝓝 (δ.real (Set.Ioc a b))) := by
    have hmain := tendsto_integral_of_dominated_convergence (μ := δ)
      (F := fun (n : ℕ) (t : ℝ) => tent (A n) (B n) n t)
      (f := fun t : ℝ => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) t)
      ((Set.Icc a (b + 2)).indicator (fun _ => (1 : ℝ)))
      (fun n => (fr_continuous_tent (A n) (B n) n).aestronglyMeasurable) hbδ (hbnd δ)
      (Filter.Eventually.of_forall hpt)
    have hgoal : (∫ t, (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) t ∂δ) = δ.real (Set.Ioc a b) :=
      MeasureTheory.integral_indicator_one measurableSet_Ioc
    rw [hgoal] at hmain
    exact hmain
  have heq : γ.real (Set.Ioc a b) = δ.real (Set.Ioc a b) := by
    have hsame : (fun n : ℕ => ∫ t, tent (A n) (B n) n t ∂γ)
        = fun n : ℕ => ∫ t, tent (A n) (B n) n t ∂δ :=
      funext fun n => h (A n) (B n) n
    rw [hsame] at hlimγ
    exact tendsto_nhds_unique hlimγ hlimδ
  rw [Measure.real_def, Measure.real_def] at heq
  have hγfin : γ (Set.Ioc a b) ≠ ∞ :=
    ne_top_of_le_ne_top (isCompact_Icc (a := a) (b := b)).measure_lt_top.ne
      (measure_mono (fun x hx => ⟨le_of_lt hx.1, hx.2⟩))
  have hδfin : δ (Set.Ioc a b) ≠ ∞ :=
    ne_top_of_le_ne_top (isCompact_Icc (a := a) (b := b)).measure_lt_top.ne
      (measure_mono (fun x hx => ⟨le_of_lt hx.1, hx.2⟩))
  exact (ENNReal.toReal_eq_toReal_iff' hγfin hδfin).mp heq

theorem frit_fiber_of_integral {Ap Bp Cp : Measure ℝ}
    [IsFiniteMeasureOnCompacts Ap] [IsFiniteMeasureOnCompacts Bp] [IsFiniteMeasureOnCompacts Cp]
    {cA cB : ℝ} (hcA : 0 < cA) (hcB : 0 < cB)
    (hE : ∀ (F : CompactlySupportedContinuousMap (ℝ × ℝ) ℝ)
        (h : CompactlySupportedContinuousMap ℝ ℝ),
      cA * (∫ p, ∫ r, ∫ q, (F (p, r)) * (h (p * r + q)) ∂Cp ∂Bp ∂Ap)
        = cB * (∫ q, h q ∂Cp) * (∫ p, ∫ r, F (p, r) ∂Bp ∂Ap)) :
    ∀ᵐ z ∂(Ap.prod Bp), Cp.map (fun q => z.1 * z.2 + q) = ENNReal.ofReal (cB / cA) • Cp := by
  classical
  haveI : SFinite Ap := inferInstance
  haveI : SFinite Bp := inferInstance
  haveI : SFinite Cp := inferInstance
  haveI hfinAB : IsFiniteMeasureOnCompacts (Ap.prod Bp) := fr_isFiniteMeasureOnCompacts_prod
  have hlam : (0 : ℝ) < cB / cA := div_pos hcB hcA
  -- bumps localising to large boxes
  have hbump : ∀ n : ℕ, ∃ χ : CompactlySupportedContinuousMap (ℝ × ℝ) ℝ,
      (∀ z ∈ Set.Icc (-(n : ℝ)) (n : ℝ) ×ˢ Set.Icc (-(n : ℝ)) (n : ℝ), χ z = 1) ∧
      (∀ z, 0 ≤ χ z) ∧ (∀ z, χ z ≤ 1) := by
    intro n
    obtain ⟨f, hf1, -, hfs, hfr⟩ := exists_continuous_one_zero_of_isCompact
      (s := Set.Icc (-(n : ℝ)) (n : ℝ) ×ˢ Set.Icc (-(n : ℝ)) (n : ℝ)) (t := ∅)
      (isCompact_Icc.prod isCompact_Icc) isClosed_empty (Set.disjoint_empty _)
    exact ⟨⟨f, hfs⟩, hf1, fun z => (hfr z).1, fun z => (hfr z).2⟩
  choose χ hχ1 hχ0 hχle using hbump
  -- the a.e. statement for a single test function `h`
  have key : ∀ (n : ℕ) (h : CompactlySupportedContinuousMap ℝ ℝ), ∀ᵐ z ∂(Ap.prod Bp),
      χ n z * ((∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp)
        - (cB / cA) * (∫ q, (h : ℝ → ℝ) q ∂Cp)) = 0 := by
    intro n h
    obtain ⟨hΨmeas, hΨbdd⟩ := ShiftIntegralMeas h Cp
    obtain ⟨M, hM0, hM⟩ :=
      isCompact_exists_abs_bound_prod (tsupport (χ n)) (χ n).hasCompactSupport
    obtain ⟨C, hC⟩ := hΨbdd M
    set c : ℝ := (cB / cA) * (∫ q, (h : ℝ → ℝ) q ∂Cp) with hcdef
    set Φ : ℝ × ℝ → ℝ :=
      fun z => χ n z * ((∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c) with hΦdef
    have hΦmeas : Measurable Φ :=
      (map_continuous (χ n)).measurable.mul (hΨmeas.sub measurable_const)
    have hΦbdd : ∃ C', ∀ z, |Φ z| ≤ C' := by
      refine ⟨max (C + |c|) 0, fun z => ?_⟩
      by_cases hz : z ∈ tsupport (χ n)
      · obtain ⟨hz1, hz2⟩ := hM z hz
        have h1 : |χ n z| ≤ 1 := abs_le.mpr ⟨by linarith [hχ0 n z], hχle n z⟩
        have h3 : |∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp| ≤ C := hC z hz1 hz2
        have h2 : |(∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c| ≤ C + |c| := by
          have habs : |(∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c|
              ≤ |∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp| + |c| := by
            calc |(∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c|
                = |(∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) + (-c)| := by ring_nf
              _ ≤ |∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp| + |-c| := abs_add_le _ _
              _ = |∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp| + |c| := by rw [abs_neg]
          linarith
        rw [hΦdef]
        calc |χ n z * ((∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c)|
            = |χ n z| * |(∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c| := abs_mul _ _
          _ ≤ 1 * (C + |c|) := mul_le_mul h1 h2 (abs_nonneg _) (by linarith)
          _ ≤ max (C + |c|) 0 := by rw [one_mul]; exact le_max_left _ _
      · have hz0 : χ n z = 0 := image_eq_zero_of_notMem_tsupport hz
        rw [hΦdef]
        simp [hz0]
    refine SepL2 (Ap.prod Bp) Φ hΦmeas hΦbdd ?_
    intro F
    have hE' := hE (F * χ n) h
    have hIntFχ : Integrable (fun z : ℝ × ℝ => (F * χ n) z) (Ap.prod Bp) :=
      (map_continuous (F * χ n)).integrable_of_hasCompactSupport (F * χ n).hasCompactSupport
    obtain ⟨D, hD0, hD⟩ := isCompact_exists_abs_bound (Set.image F (tsupport F))
      (F.hasCompactSupport.image F.continuous)
    have hD' : ∀ z ∈ tsupport F, |F z| ≤ D := fun z hz => hD (F z) ⟨z, hz, rfl⟩
    have hIntFχΨ : Integrable
        (fun z : ℝ × ℝ => (F * χ n) z * (∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp))
        (Ap.prod Bp) := by
      refine fr_integrable_of_bound_compactSupport (C := D * C + 1) ?_ ?_ ?_
      · exact ((map_continuous (F * χ n)).measurable.mul hΨmeas).aestronglyMeasurable
      · rw [hasCompactSupport_def]
        refine IsCompact.of_isClosed_subset (F.hasCompactSupport.isCompact.inter
          (χ n).hasCompactSupport.isCompact) isClosed_closure ?_
        refine closure_minimal ?_ ((F.hasCompactSupport.isCompact.inter
          (χ n).hasCompactSupport.isCompact).isClosed)
        intro z hz
        simp only [Function.mem_support, ne_eq] at hz
        have h1 : (F * χ n) z ≠ 0 := fun h0 => hz (by rw [h0, zero_mul])
        have h2 : F z ≠ 0 := fun h0 =>
          h1 (by rw [CompactlySupportedContinuousMap.mul_apply, h0, zero_mul])
        have h3 : χ n z ≠ 0 := fun h0 =>
          h1 (by rw [CompactlySupportedContinuousMap.mul_apply, h0, mul_zero])
        exact ⟨subset_tsupport F h2, subset_tsupport (χ n) h3⟩
      · have hsubχ : tsupport (fun z : ℝ × ℝ => (F * χ n) z *
            (∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp)) ⊆ tsupport (χ n) := by
          refine closure_minimal ?_ ((χ n).hasCompactSupport.isCompact.isClosed)
          intro z hz
          simp only [Function.mem_support, ne_eq] at hz
          have h1 : (F * χ n) z ≠ 0 := fun h0 => hz (by rw [h0, zero_mul])
          exact subset_tsupport (χ n) (fun h0 =>
            h1 (by rw [CompactlySupportedContinuousMap.mul_apply, h0, mul_zero]))
        have hsubF : tsupport (fun z : ℝ × ℝ => (F * χ n) z *
            (∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp)) ⊆ tsupport F := by
          refine closure_minimal ?_ (F.hasCompactSupport.isCompact.isClosed)
          intro z hz
          simp only [Function.mem_support, ne_eq] at hz
          have h1 : (F * χ n) z ≠ 0 := fun h0 => hz (by rw [h0, zero_mul])
          exact subset_tsupport F (fun h0 =>
            h1 (by rw [CompactlySupportedContinuousMap.mul_apply, h0, zero_mul]))
        intro z hz
        obtain ⟨hz1, hz2⟩ := hM z (hsubχ hz)
        have hboundF : |F z| ≤ D := hD' z (hsubF hz)
        have hboundχ : |χ n z| ≤ 1 := abs_le.mpr ⟨by linarith [hχ0 n z], hχle n z⟩
        have hboundΨ : |∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp| ≤ C := hC z hz1 hz2
        have hboundFχ : |(F * χ n) z| ≤ D := by
          rw [CompactlySupportedContinuousMap.mul_apply, abs_mul]
          calc |F z| * |χ n z| ≤ D * 1 := mul_le_mul hboundF hboundχ (abs_nonneg _) hD0
            _ = D := mul_one D
        calc |(F * χ n) z * (∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp)|
            = |(F * χ n) z| * |∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp| := abs_mul _ _
          _ ≤ D * |∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp| :=
              mul_le_mul_of_nonneg_right hboundFχ (abs_nonneg _)
          _ ≤ D * C := mul_le_mul_of_nonneg_left hboundΨ hD0
          _ ≤ D * C + 1 := by linarith
    have hA2 : Integrable (fun z : ℝ × ℝ => (F * χ n) z * c) (Ap.prod Bp) := hIntFχ.mul_const c
    have step1 : ∫ z, F z * Φ z ∂(Ap.prod Bp)
        = ∫ z, (F * χ n) z * ((∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c)
            ∂(Ap.prod Bp) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show F z * (χ n z * ((∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c))
          = (F * χ n) z * ((∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c)
      rw [CompactlySupportedContinuousMap.mul_apply]
      ring
    rw [step1]
    have step2 : ∫ z, (F * χ n) z * ((∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c)
          ∂(Ap.prod Bp)
        = (∫ z, (F * χ n) z * (∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp)
              ∂(Ap.prod Bp))
          - (∫ z, (F * χ n) z * c ∂(Ap.prod Bp)) := by
      rw [show (fun z : ℝ × ℝ => (F * χ n) z *
            ((∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp) - c))
          = fun z : ℝ × ℝ => (F * χ n) z * (∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp)
              - (F * χ n) z * c from funext fun z => by ring,
        MeasureTheory.integral_sub hIntFχΨ hA2]
    rw [step2]
    have e1 : ∫ z, (F * χ n) z * (∫ q, (h : ℝ → ℝ) (z.1 * z.2 + q) ∂Cp)
          ∂(Ap.prod Bp)
        = ∫ p, ∫ r, ∫ q, ((F * χ n) (p, r)) * (h (p * r + q)) ∂Cp ∂Bp ∂Ap := by
      rw [MeasureTheory.integral_prod _ hIntFχΨ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
      exact (MeasureTheory.integral_const_mul _ _).symm
    have e2 : ∫ z, (F * χ n) z * c ∂(Ap.prod Bp)
        = c * (∫ p, ∫ r, ((F * χ n) (p, r)) ∂Bp ∂Ap) := by
      rw [MeasureTheory.integral_prod _ hA2]
      simp only [MeasureTheory.integral_mul_const]
      exact mul_comm _ _
    rw [e1, e2]
    have hmul : cA * (c * (∫ p, ∫ r, ((F * χ n) (p, r)) ∂Bp ∂Ap))
        = cB * (∫ q, h q ∂Cp) * (∫ p, ∫ r, ((F * χ n) (p, r)) ∂Bp ∂Ap) := by
      have hA0 : cA ≠ 0 := ne_of_gt hcA
      rw [hcdef]
      field_simp
    have hcancel : cA * (∫ p, ∫ r, ∫ q, ((F * χ n) (p, r)) * (h (p * r + q))
          ∂Cp ∂Bp ∂Ap)
        = cA * (c * (∫ p, ∫ r, ((F * χ n) (p, r)) ∂Bp ∂Ap)) := by
      rw [hE', hmul]
    exact sub_eq_zero.mpr (mul_left_cancel₀ (ne_of_gt hcA) hcancel)
  -- combine over the countable family of test functions
  have hcomb : ∀ᵐ z ∂(Ap.prod Bp), ∀ (i : ℕ × (ℚ × ℚ × ℕ)),
      χ i.1 z * ((∫ q, tent i.2.1 i.2.2.1 i.2.2.2 (z.1 * z.2 + q) ∂Cp)
        - (cB / cA) * (∫ q, tent i.2.1 i.2.2.1 i.2.2.2 q ∂Cp)) = 0 := by
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    exact key i.1 (fr_tentCC i.2.1 i.2.2.1 i.2.2.2)
  filter_upwards [hcomb] with z hz
  have hmain : ∀ (a b : ℚ) (n : ℕ),
      ∫ t, tent a b n t ∂(Cp.map (fun q => z.1 * z.2 + q))
        = ∫ t, tent a b n t ∂(ENNReal.ofReal (cB / cA) • Cp) := by
    intro a b n
    obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, χ n₀ z = 1 := by
      refine ⟨Nat.ceil (max |z.1| |z.2|) + 1, hχ1 _ z ?_⟩
      have h1 : |z.1| ≤ (Nat.ceil (max |z.1| |z.2|) : ℝ) :=
        le_trans (le_max_left _ _) (Nat.le_ceil _)
      have h2 : |z.2| ≤ (Nat.ceil (max |z.1| |z.2|) : ℝ) :=
        le_trans (le_max_right _ _) (Nat.le_ceil _)
      have e1 := abs_le.mp h1
      have e2 := abs_le.mp h2
      simp only [Set.mem_prod, Set.mem_Icc]
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> · push_cast; linarith [e1.1, e1.2, e2.1, e2.2]
    have hz0 := hz (n₀, (a, b, n))
    rw [hn₀, one_mul, sub_eq_zero] at hz0
    rw [MeasureTheory.integral_map
      (by fun_prop : AEMeasurable (fun q : ℝ => z.1 * z.2 + q) Cp)
      ((fr_continuous_tent a b n).aestronglyMeasurable)]
    rw [MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal hlam.le, smul_eq_mul]
    exact hz0
  haveI hγfin : IsFiniteMeasureOnCompacts (Cp.map (fun q => z.1 * z.2 + q)) := by
    refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply (by fun_prop : Measurable fun q : ℝ => z.1 * z.2 + q)
      hK.measurableSet]
    have heq : (fun q : ℝ => z.1 * z.2 + q) ⁻¹' K = (fun q : ℝ => q - z.1 * z.2) '' K := by
      ext q
      constructor
      · intro hq; exact ⟨z.1 * z.2 + q, hq, by ring⟩
      · rintro ⟨y, hy, rfl⟩; simpa using hy
    rw [heq]
    exact (hK.image (by fun_prop)).measure_lt_top
  haveI hδfin : IsFiniteMeasureOnCompacts (ENNReal.ofReal (cB / cA) • Cp) :=
    IsFiniteMeasureOnCompacts.smul Cp ENNReal.ofReal_ne_top
  exact frit_tentDet (γ := Cp.map (fun q => z.1 * z.2 + q))
    (δ := ENNReal.ofReal (cB / cA) • Cp) hmain


/-! ## The main theorem -/

theorem frit_fiberRel_prod :
    ∀ {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
      (νij νjk νik νN : MeasureTheory.Measure Work.EKLContract.SL3) (cA cB : ℝ),
      MeasureTheory.IsFiniteMeasureOnCompacts νij → MeasureTheory.IsFiniteMeasureOnCompacts νjk →
      MeasureTheory.IsFiniteMeasureOnCompacts νik →
      νij (Work.EKLContract.Uij hij)ᶜ = 0 → νjk (Work.EKLContract.Uij hjk)ᶜ = 0 →
      νik (Work.EKLContract.Uij hik)ᶜ = 0 →
      0 < cA → 0 < cB →
      Work.EKLC7.TripleA νN νij νjk νik cA → Work.EKLC7.TripleB νN νij νjk νik cB →
      ∀ᵐ z ∂(νij.prod νjk),
        (νik).map (fun g => g * Work.EKLC7.comm z.1 z.2)
          = ENNReal.ofReal (cB / cA) • νik := by
  intro i j k hij hjk hik νij νjk νik νN cA cB hfij hfjk hfik hcij hcjk hcik hcA hcB hA hB
  classical
  haveI : IsFiniteMeasureOnCompacts νij := hfij
  haveI : IsFiniteMeasureOnCompacts νjk := hfjk
  haveI : IsFiniteMeasureOnCompacts νik := hfik
  haveI : SFinite νij := inferInstance
  haveI : SFinite νjk := inferInstance
  haveI : SFinite νik := inferInstance
  -- parameter (root-group) measures
  set Ap : Measure ℝ := νij.map (fun g : SL3 => toMat g i j) with hApdef
  set Bp : Measure ℝ := νjk.map (fun g : SL3 => toMat g j k) with hBpdef
  set Cp : Measure ℝ := νik.map (fun g : SL3 => toMat g i k) with hCpdef
  haveI hApfin : IsFiniteMeasureOnCompacts Ap := by
    rw [hApdef]; exact isFiniteMeasureOnCompacts_map_entry hij hcij
  haveI hBpfin : IsFiniteMeasureOnCompacts Bp := by
    rw [hBpdef]; exact isFiniteMeasureOnCompacts_map_entry hjk hcjk
  haveI hCpfin : IsFiniteMeasureOnCompacts Cp := by
    rw [hCpdef]; exact isFiniteMeasureOnCompacts_map_entry hik hcik
  haveI : SFinite Ap := inferInstance
  haveI : SFinite Bp := inferInstance
  haveI : SFinite Cp := inferInstance
  haveI : SFinite (Bp.prod Cp) := inferInstance
  haveI : SFinite (Ap.prod Cp) := inferInstance
  have hAp : νij = Ap.map (fun s : ℝ => uij hij s) := by
    rw [hApdef]; exact measure_eq_map_uij_entry hij hcij
  have hBp : νjk = Bp.map (fun s : ℝ => uij hjk s) := by
    rw [hBpdef]; exact measure_eq_map_uij_entry hjk hcjk
  have hCp : νik = Cp.map (fun s : ℝ => uij hik s) := by
    rw [hCpdef]; exact measure_eq_map_uij_entry hik hcik
  -- Step 1: the two iterated integrals in coordinates
  have hE : ∀ (F : CompactlySupportedContinuousMap (ℝ × ℝ) ℝ)
      (h : CompactlySupportedContinuousMap ℝ ℝ),
      cA * (∫ p, ∫ r, ∫ q, (F (p, r)) * (h (p * r + q)) ∂Cp ∂Bp ∂Ap)
        = cB * (∫ q, h q ∂Cp) * (∫ p, ∫ r, F (p, r) ∂Bp ∂Ap) := by
    intro F h
    obtain ⟨f, hf⟩ := CoordTest hij hjk hik (fun z : ℝ × ℝ => F z) (fun t : ℝ => h t)
      F.continuous h.continuous F.hasCompactSupport h.hasCompactSupport
    have hAform : (∫ g₁, ∫ g₂, ∫ g₃, f (g₁ * g₂ * g₃) ∂νik ∂νjk ∂νij)
        = ∫ p, ∫ r, ∫ q, F (p, r) * h (p * r + q) ∂Cp ∂Bp ∂Ap := by
      rw [IterTrip (Work.EKLContract.Lemmas.horoUij_cont hij) (Work.EKLContract.Lemmas.horoUij_cont hjk) (Work.EKLContract.Lemmas.horoUij_cont hik)
        (continuous_heisA hij hjk hik) (prod_heisA hij hjk hik) (heisA_lex hij hjk hik)
        hAp hBp hCp f]
      rw [show (νij.prod (νjk.prod νik)).map
            (fun u : SL3 × SL3 × SL3 => u.1 * u.2.1 * u.2.2)
          = (Ap.prod (Bp.prod Cp)).map (heisA hij hjk hik) from
        rhoA_eq hij hjk hik hAp hBp hCp]
      rw [show (∫ g, f g ∂((Ap.prod (Bp.prod Cp)).map (heisA hij hjk hik)))
          = ∫ x : ℝ × ℝ × ℝ, f (heisA hij hjk hik x) ∂(Ap.prod (Bp.prod Cp)) from
        MeasureTheory.integral_map (continuous_heisA hij hjk hik).aemeasurable
          f.continuous.aestronglyMeasurable]
      rw [show (fun x : ℝ × ℝ × ℝ => f (heisA hij hjk hik x))
          = fun x => (fr_mkG F h) (shearA x) from funext fun x => by
            change f (heis hij hjk hik x.1 (x.1 * x.2.1 + x.2.2) x.2.1)
              = F (x.1, x.2.1) * h (x.1 * x.2.1 + x.2.2)
            exact hf _ _ _]
      rw [fubini_shearA (Ap := Ap) (Bp := Bp) (Cp := Cp) (fr_mkG F h)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
      rfl
    have hBform : (∫ g₁, ∫ g₂, ∫ g₃, f (g₁ * g₂ * g₃) ∂νik ∂νij ∂νjk)
        = ∫ r, ∫ p, ∫ q, F (p, r) * h q ∂Cp ∂Ap ∂Bp := by
      rw [IterTrip (Work.EKLContract.Lemmas.horoUij_cont hjk) (Work.EKLContract.Lemmas.horoUij_cont hij) (Work.EKLContract.Lemmas.horoUij_cont hik)
        (continuous_heisB hij hjk hik) (prod_heisB hij hjk hik) (heisB_lex hij hjk hik)
        hBp hAp hCp f]
      rw [show (νjk.prod (νij.prod νik)).map
            (fun u : SL3 × SL3 × SL3 => u.1 * u.2.1 * u.2.2)
          = (Bp.prod (Ap.prod Cp)).map (heisB hij hjk hik) from
        rhoB_eq hij hjk hik hAp hBp hCp]
      rw [show (∫ g, f g ∂((Bp.prod (Ap.prod Cp)).map (heisB hij hjk hik)))
          = ∫ x : ℝ × ℝ × ℝ, f (heisB hij hjk hik x) ∂(Bp.prod (Ap.prod Cp)) from
        MeasureTheory.integral_map (continuous_heisB hij hjk hik).aemeasurable
          f.continuous.aestronglyMeasurable]
      haveI : IsFiniteMeasureOnCompacts (Ap.prod Cp) :=
        fr_isFiniteMeasureOnCompacts_prod (μ := Ap) (ν := Cp)
      haveI : IsFiniteMeasureOnCompacts (Bp.prod (Ap.prod Cp)) :=
        fr_isFiniteMeasureOnCompacts_prod (μ := Bp) (ν := Ap.prod Cp)
      rw [MeasureTheory.integral_prod (fun x : ℝ × ℝ × ℝ => f (heisB hij hjk hik x))
        ((f.continuous.comp (continuous_heisB hij hjk hik)).integrable_of_hasCompactSupport
          (fr_hasCompactSupport_heisB f hij hjk hik))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
      show ∫ w : ℝ × ℝ, f (heisB hij hjk hik (r, w)) ∂(Ap.prod Cp)
          = ∫ p, ∫ q, F (p, r) * h q ∂Cp ∂Ap
      rw [MeasureTheory.integral_prod (fun w : ℝ × ℝ => f (heisB hij hjk hik (r, w)))
        ((f.continuous.comp ((continuous_heisB hij hjk hik).comp
            (continuous_const.prodMk continuous_id))).integrable_of_hasCompactSupport
          (fr_hasCompactSupport_heisB_snd f hij hjk hik r))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
      simp only [heisB]
      rw [hf]
    have hAB : cA * (∫ p, ∫ r, ∫ q, F (p, r) * h (p * r + q) ∂Cp ∂Bp ∂Ap)
        = cB * (∫ r, ∫ p, ∫ q, F (p, r) * h q ∂Cp ∂Ap ∂Bp) := by
      rw [← hAform, ← hBform]
      exact (hA f).symm.trans (hB f)
    have hBfac : (∫ r, ∫ p, ∫ q, F (p, r) * h q ∂Cp ∂Ap ∂Bp)
        = (∫ q, h q ∂Cp) * (∫ r, ∫ p, F (p, r) ∂Ap ∂Bp) := by
      have h1 : ∀ r : ℝ, (∫ p, ∫ q, F (p, r) * h q ∂Cp ∂Ap)
          = (∫ q, h q ∂Cp) * (∫ p, F (p, r) ∂Ap) := by
        intro r
        rw [show (∫ p, ∫ q, F (p, r) * h q ∂Cp ∂Ap)
            = ∫ p, F (p, r) * (∫ q, h q ∂Cp) ∂Ap from ?_,
          MeasureTheory.integral_mul_const]
        · ring
        · refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          exact MeasureTheory.integral_const_mul _ _
      rw [show (∫ r, ∫ p, ∫ q, F (p, r) * h q ∂Cp ∂Ap ∂Bp)
          = ∫ r, (∫ q, h q ∂Cp) * (∫ p, F (p, r) ∂Ap) ∂Bp from ?_,
        MeasureTheory.integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun r => h1 r)
    have hswap : (∫ r, ∫ p, F (p, r) ∂Ap ∂Bp) = ∫ p, ∫ r, F (p, r) ∂Bp ∂Ap := by
      haveI : IsFiniteMeasureOnCompacts (Ap.prod Bp) :=
        fr_isFiniteMeasureOnCompacts_prod (μ := Ap) (ν := Bp)
      have hIntF : Integrable (fun z : ℝ × ℝ => F z) (Ap.prod Bp) :=
        F.continuous.integrable_of_hasCompactSupport F.hasCompactSupport
      rw [← MeasureTheory.integral_prod_symm (fun z : ℝ × ℝ => F z) hIntF,
        MeasureTheory.integral_prod (fun z : ℝ × ℝ => F z) hIntF]
    rw [hAB, hBfac, hswap]
    ring
  -- Step 2: the a.e. fiber relation at the level of `ℝ`
  have hgood := frit_fiber_of_integral (Ap := Ap) (Bp := Bp) (Cp := Cp) hcA hcB hE
  -- Step 3: transfer to `SL₃(ℝ)`
  have hlam : (0 : ℝ) < cB / cA := div_pos hcB hcA
  set T : SL3 × SL3 → ℝ × ℝ := fun z => (toMat z.1 i j, toMat z.2 j k) with hTdef
  have hTmeas : Measurable T := by
    rw [hTdef]
    exact (((continuous_toMat_entry i j).comp continuous_fst).measurable).prodMk
      (((continuous_toMat_entry j k).comp continuous_snd).measurable)
  have hmapT : (νij.prod νjk).map T = Ap.prod Bp := by
    rw [hTdef, hApdef, hBpdef]
    exact (Measure.map_prod_map νij νjk (continuous_toMat_entry i j).measurable
      (continuous_toMat_entry j k).measurable).symm
  set Bad : Set (ℝ × ℝ) := ⋃ (a : ℚ × ℚ × ℕ),
    {y : ℝ × ℝ | ∫ q, tent a.1 a.2.1 a.2.2 (y.1 * y.2 + q) ∂Cp
      ≠ ∫ t, tent a.1 a.2.1 a.2.2 t ∂(ENNReal.ofReal (cB / cA) • Cp)} with hBad
  have hBadmeas : MeasurableSet Bad := by
    rw [hBad]
    refine MeasurableSet.iUnion fun a => ?_
    have hfm : Measurable (fun y : ℝ × ℝ =>
        ∫ q, tent a.1 a.2.1 a.2.2 (y.1 * y.2 + q) ∂Cp) :=
      (ShiftIntegralMeas (fr_tentCC a.1 a.2.1 a.2.2) Cp).1
    have : {y : ℝ × ℝ | ∫ q, tent a.1 a.2.1 a.2.2 (y.1 * y.2 + q) ∂Cp
        ≠ ∫ t, tent a.1 a.2.1 a.2.2 t ∂(ENNReal.ofReal (cB / cA) • Cp)}
        = (fun y : ℝ × ℝ => ∫ q, tent a.1 a.2.1 a.2.2 (y.1 * y.2 + q) ∂Cp) ⁻¹'
            ({∫ t, tent a.1 a.2.1 a.2.2 t ∂(ENNReal.ofReal (cB / cA) • Cp)}ᶜ) := rfl
    rw [this]
    exact hfm (measurableSet_singleton _).compl
  have hBadnull : (Ap.prod Bp) Bad = 0 := by
    rw [hBad]
    refine measure_iUnion_null fun a => ?_
    have hfl : ∀ᵐ y ∂(Ap.prod Bp),
        (∫ q, tent a.1 a.2.1 a.2.2 (y.1 * y.2 + q) ∂Cp)
          = ∫ t, tent a.1 a.2.1 a.2.2 t ∂(ENNReal.ofReal (cB / cA) • Cp) := by
      filter_upwards [hgood] with y hy
      rw [← MeasureTheory.integral_map
        (by fun_prop : AEMeasurable (fun q : ℝ => y.1 * y.2 + q) Cp)
        ((fr_continuous_tent a.1 a.2.1 a.2.2).aestronglyMeasurable), hy]
    exact MeasureTheory.ae_iff.mp hfl
  have hpre : (νij.prod νjk) (T ⁻¹' Bad) = 0 := by
    rw [← Measure.map_apply hTmeas hBadmeas, hmapT]
    exact hBadnull
  have hSnull : (νij.prod νjk) ((Uij hij ×ˢ Uij hjk)ᶜ) = 0 := by
    have hsub : ((Uij hij ×ˢ Uij hjk)ᶜ : Set (SL3 × SL3))
        ⊆ ((Uij hij : Set SL3)ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ (Uij hjk : Set SL3)ᶜ) := by
      intro z hz
      rw [Set.mem_compl_iff, Set.mem_prod, not_and_or] at hz
      rcases hz with h1 | h2
      · exact Set.mem_union_left _ (Set.mem_prod.mpr ⟨h1, Set.mem_univ _⟩)
      · exact Set.mem_union_right _ (Set.mem_prod.mpr ⟨Set.mem_univ _, h2⟩)
    refine measure_mono_null hsub ?_
    refine le_antisymm ?_ bot_le
    calc (νij.prod νjk) ((Uij hij : Set SL3)ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ (Uij hjk : Set SL3)ᶜ)
          ≤ (νij.prod νjk) ((Uij hij : Set SL3)ᶜ ×ˢ Set.univ)
              + (νij.prod νjk) (Set.univ ×ˢ (Uij hjk : Set SL3)ᶜ) := measure_union_le _ _
        _ = νij (Uij hij)ᶜ * νjk Set.univ + νij Set.univ * νjk (Uij hjk)ᶜ := by
              rw [Measure.prod_prod, Measure.prod_prod]
        _ = 0 := by rw [hcij, hcjk]; simp
  rw [MeasureTheory.ae_iff]
  have hsub : {z : SL3 × SL3 | ¬ ((νik).map (fun g => g * comm z.1 z.2)
        = ENNReal.ofReal (cB / cA) • νik)}
      ⊆ (T ⁻¹' Bad ∪ (Uij hij ×ˢ Uij hjk)ᶜ) := by
    intro z hz
    by_contra hcon
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_compl_iff, not_or, not_not] at hcon
    obtain ⟨hzbad, hzS⟩ := hcon
    obtain ⟨hz1mem, hz2mem⟩ := Set.mem_prod.mp hzS
    set p : ℝ := toMat z.1 i j with hpdef
    set r : ℝ := toMat z.2 j k with hrdef
    have hz1eq : uij hij p = z.1 := by
      rw [hpdef]
      exact uij_of_mem_pcoord hij hjk hik hz1mem
    have hz2eq : uij hjk r = z.2 := by
      rw [hrdef]
      exact uij_of_mem_rcoord hij hjk hik hz2mem
    have hcomm : comm z.1 z.2 = uij hik (p * r) := by
      rw [← hz1eq, ← hz2eq]
      exact uij_commutator hij hjk hik p r
    have hTz : T z = (p, r) := by
      rw [hTdef, hpdef, hrdef]
    rw [hBad] at hzbad
    have huniv : ∀ a : ℚ × ℚ × ℕ,
        ∫ t, tent a.1 a.2.1 a.2.2 t ∂(Cp.map (fun q => p * r + q))
          = ∫ t, tent a.1 a.2.1 a.2.2 t ∂(ENNReal.ofReal (cB / cA) • Cp) := by
      intro a
      rw [MeasureTheory.integral_map
        (by fun_prop : AEMeasurable (fun q : ℝ => p * r + q) Cp)
        ((fr_continuous_tent a.1 a.2.1 a.2.2).aestronglyMeasurable)]
      by_contra hne
      refine hzbad (Set.mem_iUnion.mpr ⟨a, ?_⟩)
      simp only [Set.mem_ofPred_eq, hTz]
      exact hne
    haveI hγfin : IsFiniteMeasureOnCompacts (Cp.map (fun q => p * r + q)) := by
      refine ⟨fun K hK => ?_⟩
      rw [Measure.map_apply (by fun_prop : Measurable fun q : ℝ => p * r + q)
        hK.measurableSet]
      have heq : (fun q : ℝ => p * r + q) ⁻¹' K = (fun q : ℝ => q - p * r) '' K := by
        ext q
        constructor
        · intro hq; exact ⟨p * r + q, hq, by ring⟩
        · rintro ⟨y, hy, rfl⟩; simpa using hy
      rw [heq]
      exact (hK.image (by fun_prop)).measure_lt_top
    haveI hδfin : IsFiniteMeasureOnCompacts (ENNReal.ofReal (cB / cA) • Cp) :=
      IsFiniteMeasureOnCompacts.smul Cp ENNReal.ofReal_ne_top
    have hgoodz : Cp.map (fun q => p * r + q) = ENNReal.ofReal (cB / cA) • Cp :=
      frit_tentDet (γ := Cp.map (fun q => p * r + q))
        (δ := ENNReal.ofReal (cB / cA) • Cp) (fun a b n => huniv (a, b, n))
    have hgoal : (νik).map (fun g => g * comm z.1 z.2)
        = ENNReal.ofReal (cB / cA) • νik := by
      rw [hcomm]
      calc (νik).map (fun g => g * uij hik (p * r))
          = Measure.map (fun g : SL3 => g * uij hik (p * r))
              (Measure.map (fun s : ℝ => uij hik s) Cp) := by rw [hCp]
        _ = Measure.map ((fun g : SL3 => g * uij hik (p * r)) ∘ (fun s : ℝ => uij hik s)) Cp :=
              Measure.map_map ((continuous_id.mul continuous_const).measurable)
                (Work.EKLContract.Lemmas.horoUij_cont hik).measurable
        _ = Measure.map (fun q : ℝ => uij hik (p * r + q)) Cp := by
              congr 1
              funext q
              simp only [Function.comp_apply]
              rw [← fr_uij_add hik q (p * r), add_comm]
        _ = Measure.map (fun s : ℝ => uij hik s) (Measure.map (fun q : ℝ => p * r + q) Cp) :=
              (Measure.map_map (Work.EKLContract.Lemmas.horoUij_cont hik).measurable
                (by fun_prop : Measurable fun q : ℝ => p * r + q)).symm
        _ = ENNReal.ofReal (cB / cA) • νik := by
              rw [hCp, ← Measure.map_smul _ (Work.EKLContract.Lemmas.horoUij_cont hik).measurable.aemeasurable, ← hgoodz]
    exact absurd hgoal hz
  refine measure_mono_null hsub ?_
  refine le_antisymm ?_ bot_le
  calc (νij.prod νjk) (T ⁻¹' Bad ∪ (Uij hij ×ˢ Uij hjk)ᶜ)
      ≤ (νij.prod νjk) (T ⁻¹' Bad) + (νij.prod νjk) ((Uij hij ×ˢ Uij hjk)ᶜ) :=
        measure_union_le _ _
    _ = 0 := by rw [hpre, hSnull]; simp

/-! ## The iterated fibre relation -/

theorem FiberRelIter :
    ∀ {i j k : Fin 3} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
      (νij νjk νik νN : Work.EKLC7.SLm) (cA cB : ℝ),
      MeasureTheory.IsFiniteMeasureOnCompacts νij → MeasureTheory.IsFiniteMeasureOnCompacts νjk →
      MeasureTheory.IsFiniteMeasureOnCompacts νik →
      νij (Work.EKLContract.Uij hij)ᶜ = 0 → νjk (Work.EKLContract.Uij hjk)ᶜ = 0 →
      νik (Work.EKLContract.Uij hik)ᶜ = 0 →
      0 < cA → 0 < cB →
      Work.EKLC7.TripleA νN νij νjk νik cA → Work.EKLC7.TripleB νN νij νjk νik cB →
      Work.EKLC7.CommRel2 νij νjk νik (cB / cA) := by
  intro i j k hij hjk hik νij νjk νik νN cA cB hfij hfjk hfik hcij hcjk hcik hcA hcB hA hB
  exact MeasureTheory.Measure.ae_ae_of_ae_prod
    (frit_fiberRel_prod hij hjk hik νij νjk νik νN cA cB hfij hfjk hfik hcij hcjk hcik
      hcA hcB hA hB)

end Work.EKLC7
