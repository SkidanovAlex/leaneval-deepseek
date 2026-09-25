import Mathlib
import Submission.BourgainPlan.Interfaces
import Submission.Reduction
import Submission.Work.BourgainPlan.Assembly.Defs
import Submission.Commons.Analysis.Measure.memLp_exists_measurable_ae_eq
import Submission.Commons.Analysis.Measure.ae_eq_polynomial_average
import Submission.Commons.Analysis.LpSpace.memLp_lintegral_rpow_toReal_lt_top
import Submission.Commons.Analysis.ErgodicPrinciple.ae_tendsto_of_bounded_and_maximal
import Submission.Work.BourgainPlan.Assembly.osc_transference
import Submission.Work.BourgainPlan.Assembly.ae_tendsto_of_lacunary_monotone
import Submission.Work.BourgainPlan.Assembly.lacunary_ae_of_osc

/-! Guidance from the project lead (the requester):

The soft half, a general ergodic-theory assembly. Delegate under Submission/Work/BourgainPlan/Assembly/.
From hM (ℓᵖ maximal on ℕ) and hO (ℓ² oscillation along ⌊ρ^i⌋):
1. Reduce `IsIntegerPolynomialSequence a` to a P : ℤ[X] with `NonnegOnNat P`, and rewrite
   polynomialErgodicAverage as `Submission.polyAvg P T f` (Reduction.lean) and then as the kernel average
   (`polyAvg_eq_kernel`).
2. Maximal inequality on X: `Submission.ergodic_polynomial_maximal` (proved) applied to hM.
3. Oscillation on X: transfer hO to (X, μ, T), by Calderón transference in the same way (commons:
   `Dynamics/Transference/calderon_transference`, the general version; the maximal one is the model).
4. For f ∈ L²(μ): the oscillation inequality with o(J) implies a.e. convergence of polyAvg along ⌊ρ^i⌋ (the standard
   argument: a non-convergent point set of positive measure forces J disjoint ε-oscillations, contradicting o(J)).
5. Banach principle: the maximal inequality on Lᵖ plus a.e. convergence on the dense class L^∞ ⊂ L² ∩ Lᵖ gives
   a.e. convergence along ⌊ρ^i⌋ for all f ∈ Lᵖ.
6. Squeeze: for f ≥ 0, N·A_N f is nondecreasing in N, so for N_i ≤ N < N_{i+1}:
   (N_i/N_{i+1}) A_{N_i} f ≤ A_N f ≤ (N_{i+1}/N_i) A_{N_{i+1}} f. Take ρ = 1 + 1/m for all m (countably many null
   sets): liminf and limsup agree a.e. Then write f = f⁺ − f⁻.
7. Also handle: p ∈ ℝ≥0∞ with 1 < p < ∞ (convert to real p), MemLp gives a measurable representative (T preserves
   null sets), and F may be taken as the limit where it exists and 0 elsewhere.
Do NOT use `Submission.ergodic_polynomial_ae_of_discrete`: it is vacuous.
-/

open Filter Finset Function MeasureTheory
open scoped BigOperators ENNReal Topology

set_option autoImplicit false

/-- `((ofReal ε) ^ s)⁻¹ * ofReal A = ofReal (A / ε ^ s)` for `ε > 0`. -/
private lemma inv_rpow_mul_ofReal (ε A s : ℝ) (hε : 0 < ε) (_hA : 0 ≤ A) :
    ((ENNReal.ofReal ε) ^ s)⁻¹ * ENNReal.ofReal A = ENNReal.ofReal (A / ε ^ s) := by
  rw [ENNReal.ofReal_rpow_of_pos hε, ← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hε s),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.rpow_nonneg hε.le s)), div_eq_mul_inv, mul_comm]

namespace Work.BourgainPlan.Assembly

/-- The soft half: the discrete maximal and oscillation inequalities imply Bourgain's theorem
(exactly the challenge statement); see `Submission/BourgainPlan/Interfaces.lean`. -/
theorem bourgain_of_parts (hM : Submission.BourgainPlan.MaximalStatement)
    (hO : Submission.BourgainPlan.OscillationStatement)
    {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X} [MeasureTheory.IsProbabilityMeasure μ]
    {p : ENNReal} (hp : 1 < p) (hp_ne_top : p ≠ ⊤)
    {T : X → X} (hT : MeasureTheory.MeasurePreserving T μ μ)
    {a : ℕ → ℕ} (ha : LeanEval.Dynamics.BourgainErgodic.IsIntegerPolynomialSequence a)
    {f : X → ℝ} (hf : MeasureTheory.MemLp f p μ) :
    ∃ F : X → ℝ, ∀ᵐ x ∂μ,
      Filter.Tendsto (fun n : ℕ => LeanEval.Dynamics.BourgainErgodic.polynomialErgodicAverage a T f (n + 1) x)
        Filter.atTop (nhds (F x)) := by
  classical
  -- ## Step 1: extract the integer polynomial, and a measurable representative of `f`
  obtain ⟨P, hP⟩ := ha
  have hPnn : Submission.BourgainPlan.NonnegOnNat P := fun n => (hP n).1
  have hPval : ∀ n : ℕ, a n = Int.toNat (P.eval (n : ℤ)) := fun n => (hP n).2
  obtain ⟨f', hf'meas, hf'eq⟩ := Commons.Analysis.Measure.memLp_exists_measurable_ae_eq hf
  -- ## Step 2: bookkeeping of the exponent
  have hq : 1 < p.toReal := by
    have h := (ENNReal.toReal_lt_toReal (by norm_num : (1 : ENNReal) ≠ ⊤) hp_ne_top).mpr hp
    simpa using h
  have hq0 : (0 : ℝ) < p.toReal := lt_trans zero_lt_one hq
  have hf'fin : ∫⁻ x, ‖f' x‖ₑ ^ p.toReal ∂μ < ⊤ := by
    have h1 : ∫⁻ x, ‖f' x‖ₑ ^ p.toReal ∂μ = ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ :=
      lintegral_congr_ae (hf'eq.mono (fun x hx => by simp only [hx]))
    rw [h1]
    exact Commons.Analysis.LpSpace.memLp_lintegral_rpow_toReal_lt_top hp_ne_top hf
  -- ## Step 3: maximal inequality (from `hM`, through `ergodic_polynomial_maximal`)
  obtain ⟨C, hC0, hCbound⟩ := hM P hPnn p.toReal hq
  have hCpos : (0 : ℝ) < (2 * max C 1) ^ p.toReal :=
    Real.rpow_pos_of_pos (by have h : (1 : ℝ) ≤ max C 1 := le_max_right _ _; linarith) _
  have hmax : ∀ g : X → ℝ, Measurable g → (∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ < ⊤) →
      ∫⁻ x, (⨆ N : ℕ, ‖Submission.polyAvg P T g N x‖ₑ) ^ p.toReal ∂μ
        ≤ ENNReal.ofReal ((2 * max C 1) ^ p.toReal) * ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ := by
    intro g hg hgf
    have hCbound' : ∀ g' : ℕ → ℝ, (∃ s : Finset ℕ, ∀ n, n ∉ s → g' n = 0) →
        ∫⁻ n, (⨆ (N : ℕ), ‖∑ j ∈ Finset.range (Submission.polySupport P N),
            Submission.polyKernel P N j * g' (n + j)‖ₑ) ^ p.toReal ∂Measure.count
          ≤ ENNReal.ofReal ((max C 1) ^ p.toReal) * ∫⁻ n, ‖g' n‖ₑ ^ p.toReal ∂Measure.count := by
      intro g' hg'
      refine le_trans (hCbound g' hg') (mul_le_mul_left ?_ _)
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hC0 (le_max_left _ _) hq0.le)
    exact Submission.ergodic_polynomial_maximal (μ := μ) hT P (le_of_lt hq) (C := max C 1)
      (le_trans (by norm_num : (0:ℝ) ≤ 1) (le_max_right C 1)) hCbound' hg hgf
  -- measurability of the averages
  have hpolyavg_meas : ∀ g : X → ℝ, Measurable g → ∀ N : ℕ,
      Measurable (fun x => Submission.polyAvg P T g N x) := by
    intro g hg N
    simp only [Submission.polyAvg]
    exact measurable_const.mul (Finset.measurable_sum _ (fun i _ =>
      hg.comp (hT.measurable.iterate _)))
  -- ## Step 4: the weak-type inequality for the maximal operator
  have hweakM : ∀ g : X → ℝ, Measurable g → ∀ ε : ℝ, 0 < ε →
      μ {x | ENNReal.ofReal ε < (⨆ N : ℕ, ‖Submission.polyAvg P T g N x‖ₑ)}
        ≤ ENNReal.ofReal ((2 * max C 1) ^ p.toReal / ε ^ p.toReal)
            * ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ := by
    intro g hg ε hε
    by_cases hgf : ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ < ⊤
    swap
    · have htop : ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ = ⊤ := top_le_iff.mp (not_lt.mp hgf)
      have hpos : ENNReal.ofReal ((2 * max C 1) ^ p.toReal / ε ^ p.toReal) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr (div_pos hCpos (Real.rpow_pos_of_pos hε _)))
      calc μ {x : X | ENNReal.ofReal ε < (⨆ N : ℕ, ‖Submission.polyAvg P T g N x‖ₑ)}
          ≤ ⊤ := le_top
        _ = ENNReal.ofReal ((2 * max C 1) ^ p.toReal / ε ^ p.toReal)
              * ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ := by rw [htop, ENNReal.mul_top hpos]
    have hgM : Measurable (fun x => (⨆ N : ℕ, ‖Submission.polyAvg P T g N x‖ₑ) ^ p.toReal) :=
      ENNReal.continuous_rpow_const.measurable.comp
        (Measurable.iSup (fun N => (hpolyavg_meas g hg N).enorm))
    have hcheb := mul_meas_ge_le_lintegral (μ := μ) hgM ((ENNReal.ofReal ε) ^ p.toReal)
    have hsub : {x : X | ENNReal.ofReal ε < (⨆ N : ℕ, ‖Submission.polyAvg P T g N x‖ₑ)}
        ⊆ {x : X | (ENNReal.ofReal ε) ^ p.toReal
            ≤ (⨆ N : ℕ, ‖Submission.polyAvg P T g N x‖ₑ) ^ p.toReal} :=
      fun x hx => ENNReal.rpow_le_rpow hx.le hq0.le
    have hne0 : (ENNReal.ofReal ε) ^ p.toReal ≠ 0 := by
      rw [ENNReal.ofReal_rpow_of_pos hε]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hε _))
    have hnetop : (ENNReal.ofReal ε) ^ p.toReal ≠ ⊤ := by
      rw [ENNReal.ofReal_rpow_of_pos hε]
      exact ENNReal.ofReal_ne_top
    have h1 : μ {x : X | ENNReal.ofReal ε < (⨆ N : ℕ, ‖Submission.polyAvg P T g N x‖ₑ)}
        ≤ ((ENNReal.ofReal ε) ^ p.toReal)⁻¹
            * (ENNReal.ofReal ((2 * max C 1) ^ p.toReal) * ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ) := by
      calc μ {x : X | ENNReal.ofReal ε < (⨆ N : ℕ, ‖Submission.polyAvg P T g N x‖ₑ)}
          ≤ μ {x : X | (ENNReal.ofReal ε) ^ p.toReal
              ≤ (⨆ N : ℕ, ‖Submission.polyAvg P T g N x‖ₑ) ^ p.toReal} := measure_mono hsub
        _ = ((ENNReal.ofReal ε) ^ p.toReal)⁻¹
              * ((ENNReal.ofReal ε) ^ p.toReal
                * μ {x : X | (ENNReal.ofReal ε) ^ p.toReal
                    ≤ (⨆ N : ℕ, ‖Submission.polyAvg P T g N x‖ₑ) ^ p.toReal}) := by
              rw [← mul_assoc, ENNReal.inv_mul_cancel hne0 hnetop, one_mul]
        _ ≤ ((ENNReal.ofReal ε) ^ p.toReal)⁻¹
              * (ENNReal.ofReal ((2 * max C 1) ^ p.toReal) * ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ) :=
              mul_le_mul_right (le_trans hcheb (hmax g hg hgf)) _
    calc μ {x : X | ENNReal.ofReal ε < (⨆ N : ℕ, ‖Submission.polyAvg P T g N x‖ₑ)}
        ≤ ((ENNReal.ofReal ε) ^ p.toReal)⁻¹
            * (ENNReal.ofReal ((2 * max C 1) ^ p.toReal) * ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ) := h1
      _ = ENNReal.ofReal ((2 * max C 1) ^ p.toReal / ε ^ p.toReal)
            * ∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ := by
            rw [← mul_assoc, inv_rpow_mul_ofReal ε ((2 * max C 1) ^ p.toReal) p.toReal hε
              (Real.rpow_nonneg (by have h : (1 : ℝ) ≤ max C 1 := le_max_right _ _; linarith) _)]
  -- ## Step 5: lacunary a.e. convergence for every `ρ > 1`
  have hmain : ∀ ρ : ℝ, 1 < ρ → ∀ g : X → ℝ, Measurable g →
      (∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ < ⊤) →
      ∀ᵐ x ∂μ, ∃ L : ℝ,
        Filter.Tendsto (fun n : ℕ => Submission.polyAvg P T g (lac ρ n) x) Filter.atTop (nhds L) := by
    intro ρ hρ g hg hgf
    have hsub : ∀ (n : ℕ) (g h : X → ℝ) (x : X),
        Submission.polyAvg P T (g - h) (lac ρ n) x
          = Submission.polyAvg P T g (lac ρ n) x - Submission.polyAvg P T h (lac ρ n) x := by
      intro n g h x
      simp only [Submission.polyAvg, Pi.sub_apply]
      rw [Finset.sum_sub_distrib, mul_sub]
    have hbd : ∀ (h : X → ℝ) (x : X) (n : ℕ),
        ‖Submission.polyAvg P T h (lac ρ n) x‖ₑ
          ≤ ⨆ m : ℕ, ‖Submission.polyAvg P T h (lac ρ m) x‖ₑ :=
      fun h x n => le_iSup (fun m : ℕ => ‖Submission.polyAvg P T h (lac ρ m) x‖ₑ) n
    have hweak : ∀ (h : X → ℝ), Measurable h → ∀ ε : ℝ, 0 < ε →
        μ {x : X | ENNReal.ofReal ε < (⨆ m : ℕ, ‖Submission.polyAvg P T h (lac ρ m) x‖ₑ)}
          ≤ ENNReal.ofReal ((2 * max C 1) ^ p.toReal / ε ^ p.toReal)
              * ∫⁻ x, ‖h x‖ₑ ^ p.toReal ∂μ := by
      intro h hh ε hε
      refine le_trans (measure_mono ?_) (hweakM h hh ε hε)
      intro x hx
      exact lt_of_lt_of_le hx (iSup_le (fun m : ℕ =>
        le_iSup (fun N : ℕ => ‖Submission.polyAvg P T h N x‖ₑ) (lac ρ m)))
    have hbdd : ∀ (h : X → ℝ), Measurable h → (∃ B : ℝ, ∀ x, ‖h x‖ ≤ B) →
        ∀ᵐ x ∂μ, ∃ L : ℝ,
          Filter.Tendsto (fun n : ℕ => Submission.polyAvg P T h (lac ρ n) x) Filter.atTop (nhds L) := by
      intro h hh hb
      obtain ⟨B, hB⟩ := hb
      have hb2 : ∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ) ∂μ < ⊤ := by
        have hle : ∀ x : X, ‖h x‖ₑ ≤ ENNReal.ofReal |B| := by
          intro x
          rw [Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal
            (le_trans (by simpa [Real.norm_eq_abs] using hB x) (le_abs_self B))
        calc ∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ) ∂μ
            ≤ ∫⁻ x, (ENNReal.ofReal |B|) ^ (2 : ℝ) ∂μ :=
              lintegral_mono (fun x => ENNReal.rpow_le_rpow (hle x) (by norm_num))
          _ = (ENNReal.ofReal |B|) ^ (2 : ℝ) := by rw [lintegral_const, measure_univ, mul_one]
          _ < ⊤ := (ENNReal.rpow_lt_top_iff_of_pos (by norm_num : (0:ℝ) < 2)).mpr
              ENNReal.ofReal_lt_top
      -- CHILD_A
      have hosc : HasOsc μ (fun i x => Submission.polyAvg P T h (lac ρ i) x)
          (∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ) ∂μ) :=
        osc_transference hO hT hPnn hρ hh hb2
      have hmeasosc : ∀ i : ℕ, Measurable (fun x => Submission.polyAvg P T h (lac ρ i) x) :=
        fun i => hpolyavg_meas h hh (lac ρ i)
      -- CHILD_B
      have hconv : LacConv μ (fun i x => Submission.polyAvg P T h (lac ρ i) x) :=
        lacunary_ae_of_osc hb2 hmeasosc hosc
      obtain ⟨F, hF⟩ := hconv
      filter_upwards [hF] with x hx
      exact ⟨F x, hx⟩
    exact Commons.Analysis.ErgodicPrinciple.ae_tendsto_of_bounded_and_maximal (μ := μ)
      (p := p.toReal) (le_of_lt hq) hCpos
      (A := fun n (h : X → ℝ) x => Submission.polyAvg P T h (lac ρ n) x)
      (M := fun (h : X → ℝ) x => ⨆ m : ℕ, ‖Submission.polyAvg P T h (lac ρ m) x‖ₑ)
      hsub hbd hweak hbdd g hg hgf
  -- ## Step 6: the squeeze, for nonnegative functions
  have hpos : ∀ h : X → ℝ, Measurable h → (∀ x, 0 ≤ h x) →
      (∫⁻ x, ‖h x‖ₑ ^ p.toReal ∂μ < ⊤) →
      ∃ F : X → ℝ, ∀ᵐ x ∂μ,
        Filter.Tendsto (fun N : ℕ => Submission.polyAvg P T h N x) Filter.atTop (nhds (F x)) := by
    intro h hh hnn hfin
    have hMfin : ∫⁻ x, (⨆ N : ℕ, ‖Submission.polyAvg P T h N x‖ₑ) ^ p.toReal ∂μ < ⊤ :=
      lt_of_le_of_lt (hmax h hh hfin) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)
    have hbddx : ∀ᵐ x ∂μ, ∃ B : ℝ, ∀ N, ‖Submission.polyAvg P T h N x‖ ≤ B := by
      have hmeasM : Measurable
          (fun x => (⨆ N : ℕ, ‖Submission.polyAvg P T h N x‖ₑ) ^ p.toReal) :=
        ENNReal.continuous_rpow_const.measurable.comp
          (Measurable.iSup (fun N => (hpolyavg_meas h hh N).enorm))
      filter_upwards [ae_lt_top hmeasM hMfin.ne] with x hx
      have hx' : (⨆ N : ℕ, ‖Submission.polyAvg P T h N x‖ₑ) < ⊤ :=
        (ENNReal.rpow_lt_top_iff_of_pos hq0).mp hx
      refine ⟨(⨆ N : ℕ, ‖Submission.polyAvg P T h N x‖ₑ).toReal, fun N => ?_⟩
      have h1 : ‖Submission.polyAvg P T h N x‖ₑ
          ≤ ENNReal.ofReal ((⨆ N : ℕ, ‖Submission.polyAvg P T h N x‖ₑ).toReal) := by
        rw [ENNReal.ofReal_toReal hx'.ne]
        exact le_iSup (fun N : ℕ => ‖Submission.polyAvg P T h N x‖ₑ) N
      rw [Real.enorm_eq_ofReal_abs] at h1
      rw [Real.norm_eq_abs]
      exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h1
    have havg_nn : ∀ N : ℕ, ∀ x : X, 0 ≤ Submission.polyAvg P T h N x := by
      intro N x
      simp only [Submission.polyAvg]
      exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))
        (Finset.sum_nonneg (fun i _ => hnn _))
    have hρm : ∀ m : ℕ, 1 < (1 : ℝ) + ((m : ℝ) + 1)⁻¹ := fun m => by
      have h1 : (0 : ℝ) < ((m : ℝ) + 1)⁻¹ := inv_pos.mpr (by positivity)
      linarith
    have hρlim : Filter.Tendsto (fun m : ℕ => (1 : ℝ) + ((m : ℝ) + 1)⁻¹) Filter.atTop (nhds 1) := by
      have hmono : Filter.Tendsto (fun m : ℕ => ((m : ℝ) + 1)) Filter.atTop Filter.atTop :=
        tendsto_atTop_mono (fun m => by linarith) tendsto_natCast_atTop_atTop
      have h0 : Filter.Tendsto (fun m : ℕ => ((m : ℝ) + 1)⁻¹) Filter.atTop (nhds 0) :=
        hmono.inv_tendsto_atTop
      simpa using tendsto_const_nhds.add h0
    have hmono : ∀ x : X, Monotone (fun N : ℕ => (N : ℝ) * Submission.polyAvg P T h N x) := by
      intro x N M hNM
      have hkey : ∀ K : ℕ, (K : ℝ) * Submission.polyAvg P T h K x
          = ∑ k ∈ Finset.range K, h (T^[(P.eval (k : ℤ)).toNat] x) := by
        intro K
        rcases Nat.eq_zero_or_pos K with h0 | hpos'
        · subst h0
          simp [Submission.polyAvg]
        · rw [Submission.polyAvg, ← mul_assoc,
            mul_inv_cancel₀ (by positivity : (K : ℝ) ≠ 0), one_mul]
      change (N : ℝ) * Submission.polyAvg P T h N x
        ≤ (M : ℝ) * Submission.polyAvg P T h M x
      rw [hkey N, hkey M]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hNM)
        (fun i _ _ => hnn _)
    have hlac : ∀ m : ℕ, ∃ F : X → ℝ, Filter.Eventually
        (fun x => Filter.Tendsto
          (fun i : ℕ => Submission.polyAvg P T h (lac (1 + ((m : ℝ) + 1)⁻¹) i) x)
          Filter.atTop (nhds (F x))) (MeasureTheory.ae μ) := by
      intro m
      have hAE := hmain (1 + ((m : ℝ) + 1)⁻¹) (hρm m) h hh hfin
      refine ⟨fun x => if hx : ∃ L : ℝ, Filter.Tendsto
          (fun i : ℕ => Submission.polyAvg P T h (lac (1 + ((m : ℝ) + 1)⁻¹) i) x)
          Filter.atTop (nhds L) then hx.choose else 0, ?_⟩
      filter_upwards [hAE] with x hx
      rw [dif_pos hx]
      exact hx.choose_spec
    exact ae_tendsto_of_lacunary_monotone (μ := μ)
      (u := fun N x => Submission.polyAvg P T h N x)
      (ρ := fun m => 1 + ((m : ℝ) + 1)⁻¹) hρm hρlim havg_nn hmono hbddx hlac
  -- ## Step 7: full convergence for every `L^p` function
  have hlin : ∀ (u v : X → ℝ) (N : ℕ) (x : X),
      Submission.polyAvg P T (fun y => u y - v y) N x
        = Submission.polyAvg P T u N x - Submission.polyAvg P T v N x := by
    intro u v N x
    simp only [Submission.polyAvg]
    rw [Finset.sum_sub_distrib, mul_sub]
  have hfull : ∀ g : X → ℝ, Measurable g → (∫⁻ x, ‖g x‖ₑ ^ p.toReal ∂μ < ⊤) →
      ∃ F : X → ℝ, ∀ᵐ x ∂μ,
        Filter.Tendsto (fun N : ℕ => Submission.polyAvg P T g N x) Filter.atTop (nhds (F x)) := by
    intro g hg hgf
    have hgp : Measurable (fun x => max (g x) 0) := hg.max measurable_const
    have hgn : Measurable (fun x => max (-(g x)) 0) := hg.neg.max measurable_const
    have hle : ∀ x : X, ‖max (g x) 0‖ₑ ≤ ‖g x‖ₑ := by
      intro x
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
      refine ENNReal.ofReal_le_ofReal ?_
      by_cases hc : 0 ≤ g x
      · rw [max_eq_left hc]
      · rw [max_eq_right (not_le.mp hc).le]; simp
    have hle' : ∀ x : X, ‖max (-(g x)) 0‖ₑ ≤ ‖g x‖ₑ := by
      intro x
      rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
      refine ENNReal.ofReal_le_ofReal ?_
      by_cases hc : 0 ≤ -(g x)
      · rw [max_eq_left hc, abs_neg]
      · rw [max_eq_right (not_le.mp hc).le]; simp
    have hfinp : ∫⁻ x, ‖max (g x) 0‖ₑ ^ p.toReal ∂μ < ⊤ :=
      lt_of_le_of_lt (lintegral_mono (fun x => ENNReal.rpow_le_rpow (hle x) hq0.le)) hgf
    have hfinn : ∫⁻ x, ‖max (-(g x)) 0‖ₑ ^ p.toReal ∂μ < ⊤ :=
      lt_of_le_of_lt (lintegral_mono (fun x => ENNReal.rpow_le_rpow (hle' x) hq0.le)) hgf
    obtain ⟨Fp, hFp⟩ := hpos (fun x => max (g x) 0) hgp (fun x => le_max_right _ _) hfinp
    obtain ⟨Fm, hFm⟩ := hpos (fun x => max (-(g x)) 0) hgn (fun x => le_max_right _ _) hfinn
    have hdec : g = fun y => max (g y) 0 - max (-(g y)) 0 := by
      funext y
      by_cases hc : 0 ≤ g y
      · rw [max_eq_left hc, max_eq_right (by linarith)]; ring
      · rw [max_eq_right (not_le.mp hc).le, max_eq_left (by linarith)]; ring
    have hEq : ∀ x : X, (fun N : ℕ => Submission.polyAvg P T g N x)
        = fun N : ℕ => Submission.polyAvg P T (fun y => max (g y) 0) N x
            - Submission.polyAvg P T (fun y => max (-(g y)) 0) N x := by
      intro x
      funext N
      rw [← hlin (fun y => max (g y) 0) (fun y => max (-(g y)) 0) N x, ← hdec]
    refine ⟨fun x => Fp x - Fm x, ?_⟩
    filter_upwards [hFp, hFm] with x hx1 hx2
    have h3 : Filter.Tendsto
        (fun N : ℕ => Submission.polyAvg P T (fun y => max (g y) 0) N x
          - Submission.polyAvg P T (fun y => max (-(g y)) 0) N x)
        Filter.atTop (nhds (Fp x - Fm x)) := hx1.sub hx2
    simpa [hEq x] using h3
  -- ## Step 8: transfer back to `f` and rewrite the average
  obtain ⟨F', hF'⟩ := hfull f' hf'meas hf'fin
  have hagree : ∀ᵐ x ∂μ, ∀ N : ℕ,
      Submission.polyAvg P T f N x = Submission.polyAvg P T f' N x := by
    rw [MeasureTheory.ae_all_iff]
    intro N
    filter_upwards [Commons.Analysis.Measure.ae_eq_polynomial_average hT hf'eq P N] with x hx
    exact hx.symm
  have hident : ∀ (N : ℕ) (x : X),
      LeanEval.Dynamics.BourgainErgodic.polynomialErgodicAverage a T f N x
        = Submission.polyAvg P T f N x := by
    intro N x
    simp only [LeanEval.Dynamics.BourgainErgodic.polynomialErgodicAverage, Submission.polyAvg]
    congr 1
    exact Finset.sum_congr rfl (fun k _ => by rw [hPval k])
  refine ⟨F', ?_⟩
  filter_upwards [hagree, hF'] with x hx1 hx2
  have h3 : Filter.Tendsto (fun N : ℕ => Submission.polyAvg P T f N x) Filter.atTop (nhds (F' x)) :=
    hx2.congr' (Filter.Eventually.of_forall (fun N => (hx1 N).symm))
  have h4 : Filter.Tendsto (fun n : ℕ => Submission.polyAvg P T f (n + 1) x)
      Filter.atTop (nhds (F' x)) :=
    (Filter.tendsto_add_atTop_iff_nat (f := fun N : ℕ => Submission.polyAvg P T f N x) 1).mpr h3
  simpa [hident] using h4

end Work.BourgainPlan.Assembly
