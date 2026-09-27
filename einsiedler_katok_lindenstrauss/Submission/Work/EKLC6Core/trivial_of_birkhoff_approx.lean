import Mathlib
import Submission.Work.EKLC6Core.famIndicator
import Submission.Work.EKLC6Core.sqrt_integral_sq_add_le
import Submission.Work.EKLC6Core.abs_integral_le_sqrt_integral_sq
import Submission.Work.EKLC6Core.integral_sq_indicator_sub_toReal
import Submission.Work.EKLC6Core.L2_birkhoffAverage_le
import Submission.Work.EKLC6Core.abs_birkhoffAverage_le
import Submission.Work.EKLC6Core.measurable_birkhoffAverage

open MeasureTheory

noncomputable section

namespace Work.EKLC6Core

/-- **From `L²`-Birkhoff approximation to triviality of the invariant σ-algebra.**

Let `ν` be a `T`-invariant probability, `S` a countable family of measurable sets whose rational
indicator combinations `famIndicator S c` are dense in `L²(ν)`, and assume that for each such
combination `f` the Birkhoff averages `A_n f` approximate the constant `∫ f dν` arbitrarily well in
`L²(ν)` (`happrox`).  Then every `T`-invariant measurable set has `ν`-measure `0` or `1`.

Proof sketch.  Let `B` be measurable with `T ⁻¹' B = B`, `φ := 1_B`, `c := ν B`.  Then `φ ∘ T = φ`,
so `A_n φ = φ` and `∫ A_n φ dν = c`.  For each `j` pick `f_j := famIndicator S c_j` with
`∫ (φ - f_j)² dν < 1/(j+1)²` (`hdense`) and `n_j` with `∫ (A_{n_j} f_j - ∫ f_j dν)² dν < 1/(j+1)²`
(`happrox`).  Writing `‖g‖ := (∫ g² dν)^{1/2}`, since `A_n` is a contraction for `‖·‖` (as `ν` is
`T`-invariant) and `|∫ (f_j - φ) dν| ≤ ‖f_j - φ‖`,
`‖φ - c‖ ≤ 2 ‖φ - f_j‖ + ‖A_{n_j} f_j - ∫ f_j dν‖ → 0`, hence `∫ (φ - c)² dν = 0`.
But `∫ (φ - c)² dν = c - c² = c (1 - c)` (using `ν X = 1`, `φ² = φ`, `∫ φ = c`), so `c ∈ {0,1}`. -/
theorem trivial_of_birkhoff_approx {X : Type*} [MeasurableSpace X]
    (ν : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure ν]
    (T : X → X) (hT : Measurable T) (hν : MeasureTheory.MeasurePreserving T ν ν)
    (S : ℕ → Set X) (hS : ∀ n, MeasurableSet (S n))
    (hdense : ∀ (f : X → ℝ), MeasureTheory.MemLp f 2 ν → ∀ ε > 0,
      ∃ c : ℕ →₀ ℚ, ∫ x, (f x - Work.EKLC6Core.famIndicator S c x)^2 ∂ν < ε)
    (happrox : ∀ c : ℕ →₀ ℚ, ∀ ε > 0, ∃ n : ℕ,
      ∫ y, (birkhoffAverage ℝ T (Work.EKLC6Core.famIndicator S c) n y
        - ∫ z, Work.EKLC6Core.famIndicator S c z ∂ν)^2 ∂ν < ε) :
    ∀ B : Set X, MeasurableSet B → T ⁻¹' B = B → ν B = 0 ∨ ν B = 1 := by
  intro B hB hBinv
  classical
  set φ : X → ℝ := B.indicator (fun _ => (1 : ℝ)) with hφdef
  have hφ_meas : Measurable φ := by
    rw [hφdef]; exact measurable_const.indicator hB
  have hφ_abs : ∀ x, |φ x| ≤ 1 := by
    intro x
    rw [hφdef]
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]; norm_num
    · rw [Set.indicator_of_notMem hx]; norm_num
  have hφ_memLp : MemLp φ 2 ν :=
    MemLp.of_bound hφ_meas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hφ_abs x))
  set c : ℝ := (ν B).toReal with hcdef
  have hc_nonneg : 0 ≤ c := by rw [hcdef]; exact ENNReal.toReal_nonneg
  have hc_le_one : c ≤ 1 := by
    rw [hcdef]
    have h : ν B ≤ 1 := by
      have h' : ν B ≤ ν Set.univ := measure_mono (Set.subset_univ B)
      rwa [measure_univ] at h'
    calc (ν B).toReal ≤ (1 : ENNReal).toReal := ENNReal.toReal_mono (by simp) h
      _ = 1 := by norm_num
  have hφ_int : ∫ x, φ x ∂ν = c := by
    rw [hφdef, hcdef]
    rw [integral_indicator_const (1:ℝ) hB]
    simp [Measure.real_def]
  have hcomp : φ ∘ T = φ := by
    funext x
    rw [Function.comp_apply, hφdef, Set.indicator_apply, Set.indicator_apply]
    have hx : (T x ∈ B) ↔ (x ∈ B) := by rw [← Set.mem_preimage, hBinv]
    by_cases h : x ∈ B
    · rw [if_pos (hx.mpr h), if_pos h]
    · rw [if_neg (fun hh => h (hx.mp hh)), if_neg h]
  have hAvgφ : ∀ n, n ≠ 0 → birkhoffAverage ℝ T φ n = φ :=
    fun n hn => birkhoffAverage_of_comp_eq (R := ℝ) hcomp (Nat.cast_ne_zero.mpr hn)
  have hφ_int' : Integrable φ ν := hφ_memLp.integrable (by norm_num)
  suffices hc01 : c = 0 ∨ c = 1 by
    rcases hc01 with h0 | h1
    · left
      rw [hcdef] at h0
      rcases (ENNReal.toReal_eq_zero_iff (ν B)).mp h0 with hz | ht
      · exact hz
      · exact absurd ht (measure_ne_top ν B)
    · right
      rw [hcdef] at h1
      exact (ENNReal.toReal_eq_one_iff (ν B)).mp h1
  by_contra hcon
  push_neg at hcon
  have hc_pos : 0 < c := lt_of_le_of_ne hc_nonneg (Ne.symm hcon.1)
  have hc_lt_one : c < 1 := lt_of_le_of_ne hc_le_one hcon.2
  set m : ℝ := min c (1 - c) with hmdef
  have hm_pos : 0 < m := by
    rw [hmdef]; exact lt_min hc_pos (by linarith)
  have hm_le_c : m ≤ c := by rw [hmdef]; exact min_le_left _ _
  have hm_le_1c : m ≤ 1 - c := by rw [hmdef]; exact min_le_right _ _
  obtain ⟨cq, hcq0⟩ := hdense φ hφ_memLp ((m/8)^2) (by positivity)
  set f : X → ℝ := famIndicator S cq with hfdef
  have hcq : ∫ x, (φ x - f x)^2 ∂ν < (m/8)^2 := by rw [hfdef]; exact hcq0
  have hf_meas : Measurable f := by rw [hfdef]; exact measurable_famIndicator S hS cq
  have hf_memLp : MemLp f 2 ν := by rw [hfdef]; exact memLp_famIndicator S hS cq ν
  have hf_abs : ∀ x, |f x| ≤ ∑ n ∈ cq.support, |((cq n : ℚ) : ℝ)| := by
    intro x; rw [hfdef]; exact abs_famIndicator_le S cq x
  set Bf : ℝ := ∑ n ∈ cq.support, |((cq n : ℚ) : ℝ)| with hBfdef
  have hBf_nn : 0 ≤ Bf := by rw [hBfdef]; exact Finset.sum_nonneg (fun n _ => abs_nonneg _)
  have hL2φf : Real.sqrt (∫ x, (φ x - f x)^2 ∂ν) < m/8 :=
    (Real.sqrt_lt' (by positivity : (0:ℝ) < m/8)).mpr hcq
  have hf_int : Integrable f ν := hf_memLp.integrable (by norm_num)
  have hintf : |(∫ x, f x ∂ν) - c| ≤ Real.sqrt (∫ x, (φ x - f x)^2 ∂ν) := by
    have h := abs_integral_le_sqrt_integral_sq ν (fun x => f x - φ x) (hf_memLp.sub hφ_memLp)
    rw [integral_sub hf_int hφ_int', hφ_int] at h
    calc |(∫ x, f x ∂ν) - c| ≤ Real.sqrt (∫ x, (f x - φ x)^2 ∂ν) := h
      _ = Real.sqrt (∫ x, (φ x - f x)^2 ∂ν) := by
          congr 1
          exact integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
  have hintf_lt : |(∫ x, f x ∂ν) - c| < m/8 := lt_of_le_of_lt hintf hL2φf
  have hintf_gt : 7 * m / 8 < ∫ x, f x ∂ν := by
    have h := (abs_lt.mp hintf_lt).1
    linarith [h, hm_le_c]
  have hI0 : (m/10)^2 < (∫ x, f x ∂ν)^2 := by
    have hpos : 0 < ∫ x, f x ∂ν := by linarith [hintf_gt, hm_pos]
    have h1 : (7*m/8)^2 < (∫ x, f x ∂ν)^2 := by nlinarith [hintf_gt, hpos, hm_pos]
    have h2 : (m/10)^2 < (7*m/8)^2 := by nlinarith [hm_pos]
    linarith
  obtain ⟨n, hn0⟩ := happrox cq ((m/10)^2) (by positivity)
  have hn : ∫ y, (birkhoffAverage ℝ T f n y - ∫ z, f z ∂ν)^2 ∂ν < (m/10)^2 := by
    rw [hfdef]; exact hn0
  have hn_ne : n ≠ 0 := by
    intro h0
    subst h0
    simp only [birkhoffAverage_zero, Pi.zero_apply] at hn
    have hconst : ∫ y, ((0:ℝ) - ∫ z, f z ∂ν)^2 ∂ν = (∫ z, f z ∂ν)^2 := by
      rw [show (fun y => ((0:ℝ) - ∫ z, f z ∂ν)^2) = fun _ => (∫ z, f z ∂ν)^2 by
        funext y; ring]
      rw [integral_const]; simp [measure_univ]
    rw [hconst] at hn
    linarith [hI0, hn]
  have hterm2 : Real.sqrt (∫ y, (birkhoffAverage ℝ T f n y - ∫ z, f z ∂ν)^2 ∂ν) < m/10 :=
    (Real.sqrt_lt' (by positivity : (0:ℝ) < m/10)).mpr hn
  have hA_meas : Measurable (birkhoffAverage ℝ T f n) := measurable_birkhoffAverage T f hT hf_meas n
  have hA_memLp : MemLp (birkhoffAverage ℝ T f n) 2 ν :=
    MemLp.of_bound hA_meas.aestronglyMeasurable Bf
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]
        exact abs_birkhoffAverage_le T f Bf hBf_nn hf_abs n x))
  have hterm1 : Real.sqrt (∫ x, (φ x - birkhoffAverage ℝ T f n x)^2 ∂ν) < m/8 := by
    have hfun : (fun x => φ x - birkhoffAverage ℝ T f n x) = birkhoffAverage ℝ T (φ - f) n := by
      rw [birkhoffAverage_sub]
      funext x
      simp only [Pi.sub_apply, hAvgφ n hn_ne]
    have hcontr := L2_birkhoffAverage_le ν T hν (φ - f) (hφ_memLp.sub hf_memLp) n
    have h2 : Real.sqrt (∫ x, ((φ - f) x)^2 ∂ν) < m/8 := by
      simpa only [Pi.sub_apply] using hL2φf
    have h3 : Real.sqrt (∫ x, (birkhoffAverage ℝ T (φ - f) n x)^2 ∂ν) < m/8 :=
      lt_of_le_of_lt hcontr h2
    have hfun' : ∀ x, φ x - birkhoffAverage ℝ T f n x = birkhoffAverage ℝ T (φ - f) n x :=
      fun x => congrFun hfun x
    have heq : (∫ x, (φ x - birkhoffAverage ℝ T f n x)^2 ∂ν)
        = (∫ x, (birkhoffAverage ℝ T (φ - f) n x)^2 ∂ν) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => by simp only [hfun' x]))
    rw [heq]; exact h3
  have hterm3 : Real.sqrt (∫ x, ((∫ z, f z ∂ν) - c)^2 ∂ν) < m/8 := by
    have hconst : ∫ x, ((∫ z, f z ∂ν) - c)^2 ∂ν = ((∫ z, f z ∂ν) - c)^2 := by
      rw [integral_const]; simp [measure_univ]
    rw [hconst, Real.sqrt_sq_eq_abs]
    exact hintf_lt
  have hM1 : MemLp (fun x => φ x - birkhoffAverage ℝ T f n x) 2 ν := hφ_memLp.sub hA_memLp
  have hM2 : MemLp (fun x => birkhoffAverage ℝ T f n x - ∫ z, f z ∂ν) 2 ν :=
    hA_memLp.sub (memLp_const _)
  have hM3 : MemLp (fun _ : X => (∫ z, f z ∂ν) - c) 2 ν := memLp_const _
  have hsum : MemLp (fun x => (φ x - birkhoffAverage ℝ T f n x)
      + (birkhoffAverage ℝ T f n x - ∫ z, f z ∂ν)) 2 ν := hM1.add hM2
  have hL2φc : Real.sqrt (∫ x, (φ x - c)^2 ∂ν) < m/8 + m/10 + m/8 := by
    have heq : (∫ x, (φ x - c)^2 ∂ν)
        = ∫ x, (((φ x - birkhoffAverage ℝ T f n x)
            + (birkhoffAverage ℝ T f n x - ∫ z, f z ∂ν)) + ((∫ z, f z ∂ν) - c))^2 ∂ν :=
      integral_congr_ae (Filter.Eventually.of_forall (fun x => by ring))
    rw [heq]
    calc Real.sqrt (∫ x, (((φ x - birkhoffAverage ℝ T f n x)
            + (birkhoffAverage ℝ T f n x - ∫ z, f z ∂ν)) + ((∫ z, f z ∂ν) - c))^2 ∂ν)
        ≤ Real.sqrt (∫ x, ((φ x - birkhoffAverage ℝ T f n x)
            + (birkhoffAverage ℝ T f n x - ∫ z, f z ∂ν))^2 ∂ν)
            + Real.sqrt (∫ x, ((∫ z, f z ∂ν) - c)^2 ∂ν) :=
          sqrt_integral_sq_add_le ν _ _ hsum hM3
      _ ≤ (Real.sqrt (∫ x, (φ x - birkhoffAverage ℝ T f n x)^2 ∂ν)
              + Real.sqrt (∫ x, (birkhoffAverage ℝ T f n x - ∫ z, f z ∂ν)^2 ∂ν))
            + Real.sqrt (∫ x, ((∫ z, f z ∂ν) - c)^2 ∂ν) := by
          have hsub := sqrt_integral_sq_add_le ν (fun x => φ x - birkhoffAverage ℝ T f n x)
            (fun x => birkhoffAverage ℝ T f n x - ∫ z, f z ∂ν) hM1 hM2
          exact add_le_add hsub le_rfl
      _ < m/8 + m/10 + m/8 := by linarith [hterm1, hterm2, hterm3]
  have hN_eq : Real.sqrt (∫ x, (φ x - c)^2 ∂ν) = Real.sqrt (c * (1 - c)) := by
    congr 1
    rw [hφdef, hcdef]
    exact integral_sq_indicator_sub_toReal ν B hB
  have hN_ge : m ≤ Real.sqrt (∫ x, (φ x - c)^2 ∂ν) := by
    rw [hN_eq]
    have hcc : m^2 ≤ c * (1 - c) := by nlinarith [hm_le_c, hm_le_1c, hm_pos]
    calc m = Real.sqrt (m^2) := (Real.sqrt_sq (le_of_lt hm_pos)).symm
      _ ≤ Real.sqrt (c * (1 - c)) := Real.sqrt_le_sqrt hcc
  have hfinal : Real.sqrt (∫ x, (φ x - c)^2 ∂ν) < m := by
    have hm : m/8 + m/10 + m/8 < m := by linarith [hm_pos]
    linarith [hL2φc, hm]
  linarith [hN_ge, hfinal]


end Work.EKLC6Core

end
