import Mathlib
import Submission.Work.EKLRelCross.entropy_cs_interface
import Submission.Work.EKLRelCross.PeriodDefs
import Submission.Work.EKLRelCross.perSet_isClosed
import Submission.Work.EKLRelCross.perSet_aDiag_conj
import Submission.Work.EKLRelCross.measurableSet_exists_perSet_Icc
import Submission.Work.EKLRelCross.exists_separating_periodFuns
import Submission.Work.EKLRelCross.exp_t0_sub_lt_one

namespace Work.EKLRelCross

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open Work.EKLContract

/-- A closed additive subgroup of `ℝ` which contains arbitrarily small positive elements is all
of `ℝ`. -/
theorem eq_univ_of_closed_small (S : Set ℝ) (hclosed : IsClosed S) (h0 : (0 : ℝ) ∈ S)
    (hadd : ∀ a ∈ S, ∀ b ∈ S, a + b ∈ S) (hneg : ∀ a ∈ S, -a ∈ S)
    (hsmall : ∀ ε > 0, ∃ s ∈ S, 0 < s ∧ s ≤ ε) : S = Set.univ := by
  have hsmul : ∀ (n : ℕ) (s : ℝ), s ∈ S → (n : ℝ) * s ∈ S := by
    intro n s hs
    induction n with
    | zero => simpa using h0
    | succ k ih =>
        have h := hadd _ ih _ hs
        simpa [Nat.cast_succ, add_mul] using h
  have hzsmul : ∀ (z : ℤ) (s : ℝ), s ∈ S → (z : ℝ) * s ∈ S := by
    intro z s hs
    rcases z with n | n
    · exact hsmul n s hs
    · have h1 : (((n : ℕ) : ℝ) + 1) * s ∈ S := by
        have h := hsmul (n + 1) s hs
        simpa [Nat.cast_add, Nat.cast_one] using h
      have h2 : -((((n : ℕ) : ℝ) + 1) * s) ∈ S := hneg _ h1
      have h3 : ((Int.negSucc n : ℤ) : ℝ) * s = -((((n : ℕ) : ℝ) + 1) * s) := by
        rw [Int.cast_negSucc]; push_cast; ring
      rw [h3]; exact h2
  have hdense : closure S = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro x
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨s, hsS, hspos, hsle⟩ := hsmall ε hε
    have hfl : (⌊x / s⌋ : ℝ) * s ≤ x := by
      have h := mul_le_mul_of_nonneg_right (Int.floor_le (x / s)) (le_of_lt hspos)
      rwa [div_mul_cancel₀ x (ne_of_gt hspos)] at h
    have hfr : x < (⌊x / s⌋ : ℝ) * s + s := by
      have h := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x / s)) hspos
      rw [add_mul, one_mul, div_mul_cancel₀ x (ne_of_gt hspos)] at h
      exact h
    refine ⟨(⌊x / s⌋ : ℝ) * s, hzsmul ⌊x / s⌋ s hsS, ?_⟩
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hfl)]
    linarith
  exact hclosed.closure_eq.symm.trans hdense

/-- Scaling a set of reals by a non-zero constant gives `univ` only if the set itself is `univ`. -/
theorem image_mul_eq_univ_iff {c : ℝ} (hc : c ≠ 0) (S : Set ℝ) :
    (fun τ : ℝ => c * τ) '' S = Set.univ ↔ S = Set.univ := by
  constructor
  · intro h
    rw [Set.eq_univ_iff_forall]
    intro y
    have hy : c * y ∈ (fun τ : ℝ => c * τ) '' S := by rw [h]; trivial
    obtain ⟨τ, hτS, hτ⟩ := hy
    have hyτ : y = τ := (mul_left_cancel₀ hc hτ).symm
    rw [hyτ]; exact hτS
  · intro h
    rw [h, Set.image_univ, Set.range_eq_univ]
    exact fun y => ⟨y / c, by simpa using mul_div_cancel₀ y hc⟩

/-- Right translation of a Radon measure on `SL₃(ℝ)` is again finite on compacts. -/
theorem isFiniteMeasureOnCompacts_map_mulRight (ν : Measure SL3) (g : SL3)
    (hν : IsFiniteMeasureOnCompacts ν) : IsFiniteMeasureOnCompacts (ν.map (fun x => x * g)) := by
  haveI := hν
  refine ⟨fun K hK => ?_⟩
  have h1 : (ν.map (fun x : SL3 => x * g)) K = ν ((fun x : SL3 => x * g) ⁻¹' K) := by
    rw [Measure.map_apply (continuous_mul_const g).measurable hK.measurableSet]
  rw [h1]
  have h2 : (fun x : SL3 => x * g) ⁻¹' K = (fun x : SL3 => x * g⁻¹) '' K := by
    ext x
    constructor
    · intro hx; exact ⟨x * g, hx, by simp [mul_assoc]⟩
    · rintro ⟨y, hy, rfl⟩; simpa [mul_assoc] using hy
  rw [h2]
  exact IsFiniteMeasureOnCompacts.lt_top_of_isCompact (hK.image (continuous_mul_const g⁻¹))

theorem ae_translation_invariant_of_period (h2 : Work.EKLContract.P_X3) (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3)
    (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hErg : Work.EKLContract.IsAErgodic μ)
    (hCov : Work.EKLRelCross.Covariance μ U ν X')
    (i j : Fin 3) (hij : i ≠ j) (hUeq : U = Work.EKLContract.Uij hij)
    (hroot : ¬ (∀ᵐ x ∂μ, ∀ s : ℝ, s ≠ 0 → (ν x).map (fun g => g * Work.EKLContract.uij hij s) ≠ ν x)) :
    Work.EKLRelCross.AeHaar μ U ν := by
  classical
  -- ## 0. Hypothesis bookkeeping.
  obtain ⟨X'', hX''sub, hX''meas, hX''conull, hcov⟩ := hCov
  obtain ⟨F, hF⟩ := exists_separating_periodFuns hij
  have hX'meas : MeasurableSet X' := hL.meas_dom
  have hX'conull : μ X'ᶜ = 0 := hL.conull
  have hradon : ∀ x ∈ X', IsFiniteMeasureOnCompacts (ν x) := fun x hx => hL.radon x hx
  have hUij_range : (Uij hij : Set SL3) = Set.range (fun t : ℝ => uij hij t) := by
    ext g
    rw [Set.mem_range]
    exact Work.EKLContract.Lemmas.mem_Uij_iff hij g
  have hrange_closed : IsClosed (Set.range (fun t : ℝ => uij hij t)) := by
    rw [← hUij_range]
    exact (Work.EKLContract.Lemmas.isHoro_Uij hij).1
  have hcar' : ∀ x ∈ X', ν x (Set.range (fun t : ℝ => uij hij t))ᶜ = 0 := by
    intro x hx
    have h2 : ν x ((Uij hij : Subgroup SL3) : Set SL3)ᶜ = 0 := by
      rw [← hUeq]; exact hL.carried x hx
    rwa [hUij_range] at h2
  have hHmeas : ∀ f : CompactlySupportedContinuousMap SL3 ℝ,
      Measurable (fun x => ∫ g, f g ∂(ν x)) := fun f => hL.measurable f
  have hIcc_meas : ∀ {a b : ℚ}, 0 < a →
      MeasurableSet {x : X3 | x ∈ X' ∧ ∃ τ ∈ Set.Icc (a : ℝ) (b : ℝ),
        τ ∈ PerSet ν i j hij x} :=
    fun {a b} ha => measurableSet_exists_perSet_Icc hij ν X' hX'meas hradon hcar' hHmeas F hF ha
  -- ## 1. The contracting diagonal `T`, its factor `c0`, and the conull `T`-invariant set `G`.
  have hc0lt1 : Real.exp (t0 i - t0 j) < 1 := exp_t0_sub_lt_one hij hUeq hcontr
  set c0 : ℝ := Real.exp (t0 i - t0 j) with hc0def
  have hc0pos : 0 < c0 := by rw [hc0def]; exact Real.exp_pos _
  have hc0lt : c0 < 1 := by rw [hc0def]; exact hc0lt1
  have hc0tendsto : Tendsto (fun n : ℕ => c0 ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hc0pos) hc0lt
  set T : X3 → X3 := fun x => aDiag t0 • x with hTdef
  have hTmp : MeasurePreserving T μ μ := ht0
  have hTmeas : Measurable T := by rw [hTdef]; fun_prop
  set G : Set X3 := ⋂ n : ℕ, (T^[n]) ⁻¹' X'' with hGdef
  have hGmeas : MeasurableSet G := by
    rw [hGdef]
    exact MeasurableSet.iInter fun n => hX''meas.preimage (hTmeas.iterate n)
  have hGconull : μ Gᶜ = 0 := by
    rw [hGdef, Set.compl_iInter]
    refine measure_iUnion_null fun n => ?_
    rw [← Set.preimage_compl]
    rw [(hTmp.iterate n).measure_preimage hX''meas.compl.nullMeasurableSet]
    exact hX''conull
  have hGmem : ∀ {x : X3}, x ∈ G → ∀ n : ℕ, T^[n] x ∈ X'' := by
    intro x hx n
    rw [hGdef, Set.mem_iInter] at hx
    exact hx n
  have hGsub : G ⊆ X' := fun x hx => hX''sub (hGmem hx 0)
  have hTG : ∀ {x : X3}, x ∈ G → T x ∈ G := by
    intro x hx
    rw [hGdef, Set.mem_iInter] at hx ⊢
    intro n
    rw [Set.mem_preimage, ← Function.iterate_succ_apply]
    exact hx (n + 1)
  have hTpowG : ∀ {x : X3}, x ∈ G → ∀ n : ℕ, T^[n] x ∈ G := by
    intro x hx n
    induction n with
    | zero => simpa using hx
    | succ k ih => rw [Function.iterate_succ_apply']; exact hTG ih
  -- ## 2. Rescaling the period set along the orbit.
  have hscale : ∀ {x : X3}, x ∈ G →
      PerSet ν i j hij (T x) = Set.image (fun τ : ℝ => c0 * τ) (PerSet ν i j hij x) := by
    intro x hx
    have hx0 : x ∈ X'' := hGmem hx 0
    have hx1 : T x ∈ X'' := by simpa [hTdef] using hGmem hx 1
    obtain ⟨c, hc0, hcT, hcEq⟩ := hcov t0 x hx0 hx1
    have h := perSet_aDiag_conj (ν := ν) hij t0 x c hc0 hcT hcEq
    rw [hTdef]
    simpa [hc0def] using h
  have hscale_pow : ∀ (n : ℕ) {x : X3}, x ∈ G →
      PerSet ν i j hij (T^[n] x) = Set.image (fun τ : ℝ => c0 ^ n * τ) (PerSet ν i j hij x) := by
    intro n
    induction n with
    | zero => intro x hx; simp
    | succ k ih =>
        intro x hx
        have hxG : T^[k] x ∈ G := hTpowG hx k
        rw [Function.iterate_succ_apply', hscale hxG, ih hx, ← Set.image_comp]
        congr 1
        ext τ
        simp only [Function.comp_apply]
        rw [pow_succ]
        ring
  -- ## 3. Measurable sets: "there is a non-zero period" and "there is a period in `(0,δ]`".
  set A0 : Set X3 := ⋃ m : ℕ, {y : X3 | y ∈ X' ∧ ∃ τ ∈ Set.Icc (((1 : ℚ) / ((m : ℚ) + 1) : ℚ) : ℝ)
      ((((m : ℚ) + 1) : ℚ) : ℝ), τ ∈ PerSet ν i j hij y} with hA0def
  have hA0meas : MeasurableSet A0 := by
    rw [hA0def]
    exact MeasurableSet.iUnion fun m => hIcc_meas (by positivity)
  have hA0char : A0 = {y : X3 | y ∈ X' ∧ ∃ τ : ℝ, τ ≠ 0 ∧ τ ∈ PerSet ν i j hij y} := by
    rw [hA0def]
    ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨m, hxX', τ, hτ, hτP⟩ := hx
      refine ⟨hxX', τ, ?_, hτP⟩
      have h1 : (0 : ℝ) < (((1 : ℚ) / ((m : ℚ) + 1) : ℚ) : ℝ) := by positivity
      linarith [hτ.1]
    · rintro ⟨hxX', τ, hτne, hτP⟩
      have hyP : |τ| ∈ PerSet ν i j hij x := by
        rcases lt_trichotomy τ 0 with h | h | h
        · rw [abs_of_neg h]; exact neg_mem_PerSet hτP
        · exact absurd h hτne
        · rw [abs_of_pos h]; exact hτP
      have hypos : 0 < |τ| := abs_pos.mpr hτne
      obtain ⟨N, hN⟩ := exists_nat_ge (max (1 / |τ|) |τ|)
      refine Set.mem_iUnion.mpr ⟨N, hxX', |τ|, ⟨?_, ?_⟩, hyP⟩
      · have hN' : 1 / |τ| ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
        have hineq : (1 : ℝ) / ((N : ℝ) + 1) ≤ |τ| := by
          rw [div_le_iff₀ (by positivity)]
          rw [div_le_iff₀ hypos] at hN'
          linarith
        have hcast : (((1 : ℚ) / ((N : ℚ) + 1) : ℚ) : ℝ) = 1 / ((N : ℝ) + 1) := by
          push_cast; ring
        rwa [hcast]
      · have hN' : |τ| ≤ (N : ℝ) := le_trans (le_max_right _ _) hN
        have hcast : ((((N : ℚ) + 1) : ℚ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
        rw [hcast]; linarith
  have hPchar : ∀ {δ : ℚ}, 0 < δ →
      (⋃ m : ℕ, {y : X3 | y ∈ X' ∧ ∃ τ ∈ Set.Icc (((δ / ((m : ℚ) + 1)) : ℚ) : ℝ) ((δ : ℚ) : ℝ),
          τ ∈ PerSet ν i j hij y})
        = {y : X3 | y ∈ X' ∧ ∃ τ ∈ Set.Ioc (0 : ℝ) ((δ : ℚ) : ℝ), τ ∈ PerSet ν i j hij y} := by
    intro δ hδ
    ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨m, hxX', τ, hτ, hτP⟩ := hx
      refine ⟨hxX', τ, ⟨?_, hτ.2⟩, hτP⟩
      have h1 : (0 : ℝ) < (((δ / ((m : ℚ) + 1)) : ℚ) : ℝ) := by
        have h2 : (0 : ℚ) < δ / ((m : ℚ) + 1) := div_pos hδ (by positivity)
        exact_mod_cast h2
      linarith [hτ.1]
    · rintro ⟨hxX', τ, hτ, hτP⟩
      have hτδ : τ ≤ ((δ : ℚ) : ℝ) := hτ.2
      obtain ⟨m, hm⟩ : ∃ m : ℕ, ((δ : ℚ) : ℝ) / ((m : ℝ) + 1) ≤ τ := by
        obtain ⟨N, hN⟩ := exists_nat_ge (((δ : ℚ) : ℝ) / τ)
        refine ⟨N, ?_⟩
        have hN' : ((δ : ℚ) : ℝ) / τ ≤ (N : ℝ) := hN
        rw [div_le_iff₀ hτ.1] at hN'
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
        nlinarith [hN', hτ.1]
      refine Set.mem_iUnion.mpr ⟨m, hxX', τ, ⟨?_, hτδ⟩, hτP⟩
      have hcast : (((δ / ((m : ℚ) + 1)) : ℚ) : ℝ) = ((δ : ℚ) : ℝ) / ((m : ℝ) + 1) := by
        push_cast; ring
      rw [hcast]; exact hm
  have hPmeas : ∀ {δ : ℚ}, 0 < δ → MeasurableSet {y : X3 | y ∈ X' ∧
      ∃ τ ∈ Set.Ioc (0 : ℝ) ((δ : ℚ) : ℝ), τ ∈ PerSet ν i j hij y} := by
    intro δ hδ
    rw [← hPchar hδ]
    exact MeasurableSet.iUnion fun m => hIcc_meas (div_pos hδ (by positivity))
  -- ## 4. Poincaré recurrence: the points whose period set has a gap above `0` form a null set.
  have hSnull : ∀ {δ : ℚ}, 0 < δ → μ {y : X3 | y ∈ G ∧ y ∈ A0 ∧
      ¬ (∃ τ ∈ Set.Ioc (0 : ℝ) ((δ : ℚ) : ℝ), τ ∈ PerSet ν i j hij y)} = 0 := by
    intro δ hδ
    have hP := hPmeas hδ
    have hSmeas : MeasurableSet {y : X3 | y ∈ G ∧ y ∈ A0 ∧
        ¬ (∃ τ ∈ Set.Ioc (0 : ℝ) ((δ : ℚ) : ℝ), τ ∈ PerSet ν i j hij y)} := by
      have heq : {y : X3 | y ∈ G ∧ y ∈ A0 ∧
          ¬ (∃ τ ∈ Set.Ioc (0 : ℝ) ((δ : ℚ) : ℝ), τ ∈ PerSet ν i j hij y)}
          = G ∩ (A0 \ {y : X3 | y ∈ X' ∧ ∃ τ ∈ Set.Ioc (0 : ℝ) ((δ : ℚ) : ℝ),
              τ ∈ PerSet ν i j hij y}) := by
        ext x
        constructor
        · rintro ⟨hxG, hxA0, hxno⟩
          refine ⟨hxG, hxA0, ?_⟩
          rintro ⟨-, hcon⟩
          exact hxno hcon
        · rintro ⟨hxG, hxA0, hxno⟩
          refine ⟨hxG, hxA0, ?_⟩
          rintro hcon
          exact hxno ⟨(hA0char ▸ hxA0).1, hcon⟩
      rw [heq]
      exact hGmeas.inter (hA0meas.diff hP)
    have hescape : ∀ x ∈ {y : X3 | y ∈ G ∧ y ∈ A0 ∧
        ¬ (∃ τ ∈ Set.Ioc (0 : ℝ) ((δ : ℚ) : ℝ), τ ∈ PerSet ν i j hij y)},
        ∃ N : ℕ, ∀ m ≥ N, T^[m] x ∉ {y : X3 | y ∈ G ∧ y ∈ A0 ∧
          ¬ (∃ τ ∈ Set.Ioc (0 : ℝ) ((δ : ℚ) : ℝ), τ ∈ PerSet ν i j hij y)} := by
      intro x hx
      obtain ⟨hxG, hxA0, hxno⟩ := hx
      obtain ⟨hxX', σ, hσne, hσP⟩ := hA0char ▸ hxA0
      have hσabsP : |σ| ∈ PerSet ν i j hij x := by
        rcases lt_trichotomy σ 0 with h | h | h
        · rw [abs_of_neg h]; exact neg_mem_PerSet hσP
        · exact absurd h hσne
        · rw [abs_of_pos h]; exact hσP
      have hσpos : 0 < |σ| := abs_pos.mpr hσne
      obtain ⟨N, hN⟩ : ∃ N : ℕ, c0 ^ N * |σ| < ((δ : ℚ) : ℝ) := by
        have hpos : (0 : ℝ) < ((δ : ℚ) : ℝ) / |σ| := div_pos (by exact_mod_cast hδ) hσpos
        obtain ⟨N, hN⟩ := (hc0tendsto.eventually (Iio_mem_nhds hpos)).exists
        exact ⟨N, by rw [lt_div_iff₀ hσpos] at hN; exact hN⟩
      refine ⟨N, fun m hm hmem => ?_⟩
      have hper : c0 ^ m * |σ| ∈ PerSet ν i j hij (T^[m] x) := by
        rw [hscale_pow m hxG]
        exact ⟨|σ|, hσabsP, rfl⟩
      have hle : c0 ^ m * |σ| ≤ c0 ^ N * |σ| :=
        mul_le_mul_of_nonneg_right
          (pow_le_pow_of_le_one (le_of_lt hc0pos) (le_of_lt hc0lt) hm) (le_of_lt hσpos)
      have hlt : c0 ^ m * |σ| < ((δ : ℚ) : ℝ) := lt_of_le_of_lt hle hN
      have hpos : 0 < c0 ^ m * |σ| := mul_pos (pow_pos hc0pos m) hσpos
      exact hmem.2.2 ⟨c0 ^ m * |σ|, ⟨hpos, le_of_lt hlt⟩, hper⟩
    refine measure_mono_null ?_ (measure_iUnion_null fun N =>
      (hTmp.conservative).measure_mem_forall_ge_image_notMem_eq_zero hSmeas.nullMeasurableSet N)
    intro x hx
    obtain ⟨N, hN⟩ := hescape x hx
    exact Set.mem_iUnion.mpr ⟨N, hx, fun m hm => hN m hm⟩
  -- ## 5. The dichotomy: a.e. point has trivial or full period set.
  have hdich : ∀ᵐ x ∂μ, x ∈ G → (PerSet ν i j hij x = {0} ∨ PerSet ν i j hij x = Set.univ) := by
    rw [MeasureTheory.ae_iff]
    refine measure_mono_null ?_
      (measure_iUnion_null fun n => hSnull (by
        have h1 : (0 : ℚ) < ((n + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_pos n
        have h2 : ((n + 1 : ℕ) : ℚ) = (n : ℚ) + 1 := by push_cast; ring
        rw [h2] at h1
        exact div_pos one_pos h1))
    intro x hx
    rw [Set.mem_setOf_eq] at hx
    have hxG : x ∈ G := by
      by_contra hcon
      exact hx (fun hxG => absurd hxG hcon)
    have hxrest : ¬ (PerSet ν i j hij x = {0} ∨ PerSet ν i j hij x = Set.univ) :=
      fun hcon => hx (fun _ => hcon)
    have hxX' : x ∈ X' := hGsub hxG
    have hσex : ∃ s : ℝ, s ≠ 0 ∧ s ∈ PerSet ν i j hij x := by
      by_contra hcon
      apply hxrest
      left
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨zero_mem_PerSet ν i j hij x, ?_⟩
      intro y hy
      by_contra hy0
      exact hcon ⟨y, hy0, hy⟩
    have hex : ∃ ε > 0, ∀ s ∈ PerSet ν i j hij x, 0 < s → ε < s := by
      by_contra hcon
      push_neg at hcon
      exact hxrest (Or.inr (eq_univ_of_closed_small _
        (perSet_isClosed ν hij x (hradon x hxX')) (zero_mem_PerSet ν i j hij x)
        (fun a ha b hb => add_mem_PerSet ha hb) (fun a ha => neg_mem_PerSet ha)
        (fun ε hε => hcon ε hε)))
    obtain ⟨ε, hεpos, hε⟩ := hex
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hεpos
    refine Set.mem_iUnion.mpr ⟨n, hxG, ?_, ?_⟩
    · rw [hA0char]
      exact ⟨hxX', hσex⟩
    · rintro ⟨τ, hτ, hτP⟩
      have hn' : (((1 : ℚ) / ((n : ℚ) + 1) : ℚ) : ℝ) < ε := by
        rw [show (((1 : ℚ) / ((n : ℚ) + 1) : ℚ) : ℝ) = 1 / ((n : ℝ) + 1) by push_cast; ring]
        exact hn
      exact absurd (hε τ hτP hτ.1) (not_lt.mpr (le_of_lt (lt_of_le_of_lt hτ.2 hn')))
  -- ## 6. The set of "Haar" points: measurable and almost invariant.
  set C : Set X3 := {y : X3 | y ∈ X' ∧ PerSet ν i j hij y = Set.univ} with hCdef
  have hFq_meas : ∀ (k : ℕ) (t : ℝ), Measurable
      (fun x : X3 => ∫ g, F k g ∂((ν x).map (fun g => g * uij hij t))) := by
    intro k t
    have hshift : ∀ x : X3, ∫ g, F k g ∂((ν x).map (fun g => g * uij hij t))
        = ∫ g, F k (g * uij hij t) ∂(ν x) := by
      intro x
      rw [MeasureTheory.integral_map]
      · exact (Work.EKLC7.measurable_mulRight_uij hij t).aemeasurable
      · exact (F k).continuous.aestronglyMeasurable
    simp_rw [hshift]
    exact hHmeas ⟨⟨fun g => F k (g * uij hij t),
      (F k).continuous.comp (continuous_id.mul continuous_const)⟩,
      (F k).hasCompactSupport.comp_homeomorph (Homeomorph.mulRight (uij hij t))⟩
  have hCmeas : MeasurableSet C := by
    have hCe : C = {y : X3 | y ∈ X' ∧ ∀ q : ℚ, (q : ℝ) ∈ PerSet ν i j hij y} := by
      ext x
      constructor
      · rintro ⟨hxX', huv⟩
        exact ⟨hxX', fun q => by rw [huv]; trivial⟩
      · rintro ⟨hxX', hq⟩
        refine ⟨hxX', ?_⟩
        have hcl : IsClosed (PerSet ν i j hij x) := perSet_isClosed ν hij x (hradon x hxX')
        have hqc : Set.range (fun q : ℚ => (q : ℝ)) ⊆ PerSet ν i j hij x :=
          fun r ⟨q, hq'⟩ => hq' ▸ hq q
        refine Set.eq_univ_of_univ_subset fun y _ => ?_
        rw [← hcl.closure_eq]
        exact closure_mono hqc (Rat.denseRange_cast y)
    rw [hCe]
    have hset : {y : X3 | y ∈ X' ∧ ∀ q : ℚ, (q : ℝ) ∈ PerSet ν i j hij y}
        = X' ∩ ⋂ q : ℚ, (X' ∩ ⋂ k : ℕ, {y : X3 |
            ∫ g, F k g ∂((ν y).map (fun g => g * uij hij (q : ℝ))) = ∫ g, F k g ∂(ν y)}) := by
      ext x
      constructor
      · intro hx
        refine ⟨hx.1, Set.mem_iInter.mpr fun q => ⟨hx.1, Set.mem_iInter.mpr fun k => ?_⟩⟩
        simp only [Set.mem_setOf_eq]
        rw [hx.2 q]
      · intro hx
        have hxX' : x ∈ X' := hx.1
        refine ⟨hxX', fun q => ?_⟩
        have hq := Set.mem_iInter.mp hx.2 q
        have hxk : ∀ k : ℕ, ∫ g, F k g ∂((ν x).map (fun g => g * uij hij (q : ℝ)))
            = ∫ g, F k g ∂(ν x) := fun k => Set.mem_iInter.mp hq.2 k
        have hcarT : ((ν x).map (fun g => g * uij hij (q : ℝ)))
            (Set.range (fun t : ℝ => uij hij t))ᶜ = 0 := by
          rw [Measure.map_apply (Work.EKLC7.measurable_mulRight_uij hij (q : ℝ))
            hrange_closed.measurableSet.compl]
          have hset2 : (fun g : SL3 => g * uij hij (q : ℝ)) ⁻¹'
              (Set.range (fun t : ℝ => uij hij t))ᶜ
              = (Set.range (fun t : ℝ => uij hij t))ᶜ := by
            ext g
            simp only [Set.mem_preimage, Set.mem_compl_iff]
            rw [← hUij_range]
            exact not_congr (Subgroup.mul_mem_cancel_right (Uij hij)
              (Subgroup.subset_closure (Set.mem_range_self (q : ℝ))))
          rw [hset2]
          exact hcar' x hxX'
        exact (hF (ν x) ((ν x).map (fun g => g * uij hij (q : ℝ))) (hradon x hxX')
          (isFiniteMeasureOnCompacts_map_mulRight (ν x) (uij hij (q : ℝ)) (hradon x hxX'))
          (hcar' x hxX') hcarT (fun k => (hxk k).symm)).symm
    rw [hset]
    refine hX'meas.inter ?_
    refine MeasurableSet.iInter fun q => ?_
    refine hX'meas.inter ?_
    refine MeasurableSet.iInter fun k => ?_
    exact measurableSet_eq_fun (hFq_meas k (q : ℝ)) (hHmeas (F k))
  have hCinv : ∀ t : Fin 3 → ℝ, (fun x : X3 => aDiag t • x) ⁻¹' C =ᵐ[μ] C := by
    intro t
    rw [eventuallyEq_set]
    rw [MeasureTheory.ae_iff]
    have hnull : μ (X''ᶜ ∪ (fun x : X3 => aDiag t • x) ⁻¹' X''ᶜ) = 0 := by
      refine measure_union_null hX''conull ?_
      rw [(hErg.1 t).measure_preimage hX''meas.compl.nullMeasurableSet]
      exact hX''conull
    refine measure_mono_null ?_ hnull
    intro x hx
    rw [Set.mem_setOf_eq, Set.mem_preimage] at hx
    by_cases hmem : x ∈ X'' ∧ aDiag t • x ∈ X''
    · exfalso
      obtain ⟨hxX'', hTxX''⟩ := hmem
      have hxX' : x ∈ X' := hX''sub hxX''
      have hTxX' : aDiag t • x ∈ X' := hX''sub hTxX''
      obtain ⟨c, hc0, hcT, hcEq⟩ := hcov t x hxX'' hTxX''
      have h := perSet_aDiag_conj (ν := ν) hij t x c hc0 hcT hcEq
      have key : PerSet ν i j hij (aDiag t • x) = Set.univ ↔ PerSet ν i j hij x = Set.univ := by
        rw [h]
        exact image_mul_eq_univ_iff (Real.exp_ne_zero _) _
      have hiff : (aDiag t • x ∈ C) ↔ (x ∈ C) := by
        rw [hCdef, Set.mem_setOf_eq, Set.mem_setOf_eq]
        exact ⟨fun h => ⟨hxX', key.mp h.2⟩, fun h => ⟨hTxX', key.mpr h.2⟩⟩
      exact hx hiff
    · rcases not_and_or.mp hmem with h | h
      · exact Or.inl h
      · exact Or.inr (Set.mem_preimage.mpr h)
  have hCtriv : μ C = 0 ∨ μ Cᶜ = 0 := hErg.2 C hCmeas hCinv
  -- ## 7. `hroot` gives `μ C > 0`.
  have hA0pos : 0 < μ A0 := by
    have hne : μ {x : X3 | ∃ s : ℝ, s ≠ 0 ∧ s ∈ PerSet ν i j hij x} ≠ 0 := by
      intro h0
      refine hroot ?_
      rw [MeasureTheory.ae_iff]
      have hset : {x : X3 | ¬ (∀ s : ℝ, s ≠ 0 → (ν x).map (fun g => g * uij hij s) ≠ ν x)}
          = {x : X3 | ∃ s : ℝ, s ≠ 0 ∧ s ∈ PerSet ν i j hij x} := by
        ext x
        constructor
        · intro h
          push_neg at h
          exact h
        · rintro ⟨s, hs, hsp⟩ hcon
          exact hcon s hs hsp
      rw [hset]; exact h0
    have hsub : {x : X3 | ∃ s : ℝ, s ≠ 0 ∧ s ∈ PerSet ν i j hij x} ⊆ A0 ∪ X'ᶜ := by
      intro x hx
      by_cases hxX' : x ∈ X'
      · left
        rw [hA0char]
        exact ⟨hxX', hx⟩
      · right; exact hxX'
    have hle : μ {x : X3 | ∃ s : ℝ, s ≠ 0 ∧ s ∈ PerSet ν i j hij x} ≤ μ A0 :=
      calc μ {x : X3 | ∃ s : ℝ, s ≠ 0 ∧ s ∈ PerSet ν i j hij x} ≤ μ (A0 ∪ X'ᶜ) :=
            measure_mono hsub
        _ ≤ μ A0 + μ X'ᶜ := measure_union_le _ _
        _ = μ A0 := by rw [hX'conull, add_zero]
    exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hne) hle
  have hCpos : 0 < μ C := by
    have hAG : μ (A0 ∩ G) = μ A0 := by
      have h0 : μ (A0 \ G) = 0 := measure_mono_null (fun x hx => hx.2) hGconull
      have h1 : μ (A0 ∩ G) + μ (A0 \ G) = μ A0 := measure_inter_add_diff A0 hGmeas
      rw [h0, add_zero] at h1
      exact h1
    have hnull : μ ((A0 ∩ G) \ C) = 0 := by
      refine measure_mono_null ?_ (MeasureTheory.ae_iff.mp hdich)
      intro x hx
      rw [Set.mem_setOf_eq]
      rw [Set.mem_sdiff, Set.mem_inter_iff] at hx
      obtain ⟨⟨hxA0, hxG⟩, hxC⟩ := hx
      have hxX' : x ∈ X' := (hA0char ▸ hxA0).1
      have hper : ∃ s : ℝ, s ≠ 0 ∧ s ∈ PerSet ν i j hij x := (hA0char ▸ hxA0).2
      intro hcon
      rcases hcon hxG with hcon | hcon
      · obtain ⟨s, hs, hsp⟩ := hper
        exact hs (by rw [hcon] at hsp; exact hsp)
      · exact hxC (by rw [hCdef]; exact ⟨hxX', hcon⟩)
    have h1 : μ ((A0 ∩ G) ∩ C) + μ ((A0 ∩ G) \ C) = μ (A0 ∩ G) :=
      measure_inter_add_diff (A0 ∩ G) hCmeas
    rw [hnull, add_zero] at h1
    have hA0GC : 0 < μ ((A0 ∩ G) ∩ C) := by rw [h1, hAG]; exact hA0pos
    exact lt_of_lt_of_le hA0GC (measure_mono Set.inter_subset_right)
  have hCconull : μ Cᶜ = 0 := hCtriv.resolve_left (ne_of_gt hCpos)
  -- ## 8. Conclusion.
  rw [Work.EKLRelCross.AeHaar]
  filter_upwards [MeasureTheory.ae_iff.mpr hCconull] with x hxC u hu
  have hX'x : x ∈ X' := hxC.1
  have hPS : PerSet ν i j hij x = Set.univ := hxC.2
  have hu' : u ∈ Uij hij := by rw [← hUeq]; exact hu
  obtain ⟨τ, hτ⟩ := (Work.EKLContract.Lemmas.mem_Uij_iff hij u).mp hu'
  rw [← hτ]
  have hτP : τ ∈ PerSet ν i j hij x := by rw [hPS]; exact Set.mem_univ τ
  exact hτP

end

end Work.EKLRelCross
