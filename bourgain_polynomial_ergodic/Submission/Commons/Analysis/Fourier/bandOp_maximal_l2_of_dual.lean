import Mathlib
import Submission.Commons.Analysis.Fourier.nested_scales_maximal_l2_real
import Submission.Commons.Analysis.Fourier.linearization_bound_dual

namespace Commons.Analysis.Fourier

open MeasureTheory Filter
open scoped ENNReal FourierTransform ComplexInnerProductSpace Topology

noncomputable section

set_option maxHeartbeats 8000000

/-! ### Auxiliary: suprema over initial segments -/

/-- `(⨆ i, x i) ^ 2 = ⨆ i, (x i) ^ 2` in `ℝ≥0∞`. -/
private lemma iSup_sq {ι : Type*} (x : ι → ℝ≥0∞) : (⨆ i, x i) ^ 2 = ⨆ i, (x i) ^ 2 := by
  rw [pow_two, ENNReal.mul_iSup]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun n => ?_
    rw [ENNReal.iSup_mul]
    refine iSup_le fun m => ?_
    have h : x m * x n ≤ x m ^ 2 ⊔ x n ^ 2 := by
      rcases le_total (x m) (x n) with hc | hc
      · calc x m * x n ≤ x n * x n := mul_le_mul' hc le_rfl
          _ = x n ^ 2 := by rw [pow_two]
          _ ≤ x m ^ 2 ⊔ x n ^ 2 := le_sup_right
      · calc x m * x n ≤ x m * x m := mul_le_mul' le_rfl hc
          _ = x m ^ 2 := by rw [pow_two]
          _ ≤ x m ^ 2 ⊔ x n ^ 2 := le_sup_left
    exact le_trans h (sup_le (le_iSup (fun n => x n ^ 2) m) (le_iSup (fun n => x n ^ 2) n))
  · refine iSup_le fun n => ?_
    refine le_trans ?_ (le_iSup (fun i => (⨆ k, x k) * x i) n)
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right (le_iSup (fun k => x k) n) bot_le

/-- The square of a supremum over `ℕ` is the supremum of the squares over the initial segments
`Fin (M+1)`. -/
private lemma iSup_nat_sq_eq_succ (b : ℕ → ℝ≥0∞) :
    (⨆ j : ℕ, b j) ^ 2 = ⨆ M : ℕ, (⨆ i : Fin (M + 1), b i.val) ^ 2 := by
  rw [iSup_sq]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun j => ?_
    refine le_trans ?_ (le_iSup (fun M : ℕ => (⨆ i : Fin (M + 1), b i.val) ^ 2) j)
    exact pow_le_pow_left' (le_iSup (fun i : Fin (j + 1) => b i.val) ⟨j, Nat.lt_succ_self j⟩) 2
  · refine iSup_le fun M => ?_
    rw [iSup_sq]
    exact iSup_le fun i => le_iSup (fun j : ℕ => b j ^ 2) i.val

/-- Monotone convergence over initial segments for `lintegral`s of squared maximal functions. -/
private lemma lintegral_iSup_fin_succ (b : ℕ → ℝ → ℝ≥0∞) (hb : ∀ j, Measurable (b j)) :
    ∫⁻ x, (⨆ j : ℕ, b j x) ^ (2 : ℝ)
      = ⨆ M : ℕ, ∫⁻ x, (⨆ i : Fin (M + 1), b i.val x) ^ (2 : ℝ) := by
  have hpt : (fun x => (⨆ j : ℕ, b j x) ^ (2 : ℝ))
      = fun x => ⨆ M : ℕ, (⨆ i : Fin (M + 1), b i.val x) ^ (2 : ℝ) := by
    funext x
    rw [show (⨆ j : ℕ, b j x) ^ (2 : ℝ) = (⨆ j : ℕ, b j x) ^ 2 by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast],
        show (⨆ M : ℕ, (⨆ i : Fin (M + 1), b i.val x) ^ (2 : ℝ))
            = ⨆ M : ℕ, (⨆ i : Fin (M + 1), b i.val x) ^ 2 by
          refine iSup_congr (fun M => ?_)
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]]
    exact iSup_nat_sq_eq_succ (fun j => b j x)
  rw [hpt]
  have hm : ∀ M : ℕ, Measurable (fun x : ℝ => (⨆ i : Fin (M + 1), b i.val x) ^ (2 : ℝ)) := by
    intro M
    exact (by measurability : Measurable (fun y : ℝ≥0∞ => y ^ (2 : ℝ))).comp
      (Measurable.iSup (fun i : Fin (M + 1) => hb i.val))
  have hmono : Monotone
      (fun M : ℕ => fun x : ℝ => (⨆ i : Fin (M + 1), b i.val x) ^ (2 : ℝ)) := by
    intro M M' hle x
    refine ENNReal.rpow_le_rpow ?_ (by norm_num)
    refine iSup_le fun i =>
      le_iSup (fun i : Fin (M' + 1) => b i.val x) ⟨i.val, lt_of_lt_of_le i.isLt (Nat.succ_le_succ hle)⟩
  exact lintegral_iSup (μ := volume) hm hmono

/-! ### The maximal bound from a weighted bound -/

/-- **Maximal `L²` bound from a weighted/linearisation bound.** -/
theorem maximal_bound_of_weighted_bound {ι : Type*} [Fintype ι] [Nonempty ι]
    (C : ι → Set ℝ) (hmeas : ∀ i, MeasurableSet (C i)) (hbd : ∀ i, Bornology.IsBounded (C i))
    (f : ℝ → ℂ) (hf1 : Integrable f) (hf2 : MemLp f 2 (volume : Measure ℝ))
    (D : ℝ) (hD : 0 ≤ D)
    (hlin : ∀ w : ℝ → ℝ, (∀ x, 0 ≤ w x) → Integrable w → MemLp w 2 (volume : Measure ℝ) →
      (∫ x : ℝ, w x * (⨆ i : ι, ‖bandOp (C i) f x‖))
        ≤ D * Real.sqrt (∫ x : ℝ, w x ^ 2) * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2)) :
    ∫⁻ x : ℝ, (⨆ i : ι, ‖bandOp (C i) f x‖ₑ) ^ (2 : ℝ)
      ≤ ENNReal.ofReal (D ^ 2) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2 : ℝ) := by
  classical
  have hFmem : ∀ i, MemLp (fun x : ℝ => ‖bandOp (C i) f x‖) 2 volume :=
    fun i => (bandOp_memLp (C i) (hmeas i) (hbd i) f hf1 hf2).norm
  set G : ℝ → ℝ := fun x => ⨆ i : ι, ‖bandOp (C i) f x‖ with hG
  have hGbdd : ∀ x : ℝ, BddAbove (Set.range fun i : ι => ‖bandOp (C i) f x‖) :=
    fun x => (Set.finite_range _).bddAbove
  have hGle : ∀ x (i : ι), ‖bandOp (C i) f x‖ ≤ G x :=
    fun x i => le_ciSup (hGbdd x) i
  have hGmeas : Measurable G := by
    rw [hG]
    exact Measurable.iSup (fun i => (bandOp_cont (C i) (hmeas i) (hbd i) f hf1).norm.measurable)
  have hGnonneg : ∀ x, 0 ≤ G x :=
    fun x => le_trans (norm_nonneg _) (hGle x (Classical.arbitrary ι))
  have hGmem : MemLp G 2 volume := by
    have hdom : MemLp (fun x : ℝ => ∑ i : ι, ‖bandOp (C i) f x‖) 2 volume :=
      memLp_finsetSum (Finset.univ : Finset ι) (fun i _ => hFmem i)
    refine MemLp.mono' hdom hGmeas.aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg (hGnonneg x)]
    exact ciSup_le (fun i =>
      Finset.single_le_sum (fun j _ => norm_nonneg (bandOp (C j) f x)) (Finset.mem_univ i))
  have hGsq_int : Integrable (fun x : ℝ => G x ^ 2) := by
    have h : Integrable (fun x : ℝ => (((G x * G x : ℝ)) : ℂ)) := by
      have hh := (memLp_ofReal hGmem).integrable_mul (memLp_ofReal hGmem)
      refine hh.congr ?_
      filter_upwards with x
      simp only [Pi.mul_apply, Complex.ofReal_mul]
    refine h.norm.congr ?_
    filter_upwards with x
    have h1 : ‖((G x : ℝ) : ℂ)‖ = G x := by
      rw [norm_ofReal_eq, abs_of_nonneg (hGnonneg x)]
    show ‖(((G x * G x : ℝ)) : ℂ)‖ = G x ^ 2
    rw [show (((G x * G x : ℝ)) : ℂ) = ((G x : ℝ) : ℂ) * ((G x : ℝ) : ℂ) by push_cast; ring,
      norm_mul, h1]
    ring
  have hN : ∀ N : ℕ, (∫ x : ℝ, G x ^ 2 * (Set.Icc (-(N:ℝ)) (N:ℝ)).indicator (fun _ => (1:ℝ)) x)
      ≤ D * Real.sqrt (∫ x : ℝ, G x ^ 2) * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) := by
    intro N
    set T : Set ℝ := Set.Icc (-(N:ℝ)) (N:ℝ) with hT
    have hTmeas : MeasurableSet T := measurableSet_Icc
    have hTfin : volume T < ⊤ := by
      rw [hT, Real.volume_Icc]
      exact ENNReal.ofReal_lt_top
    have hind_int : Integrable (T.indicator (fun _ => (1:ℝ))) volume :=
      (integrable_indicator_iff hTmeas).2 (integrableOn_const hTfin.ne)
    have hTle : ∀ x : ℝ, T.indicator (fun _ => (1:ℝ)) x ≤ 1 := fun x => by
      by_cases hx : x ∈ T <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
    have hTnn : ∀ x : ℝ, 0 ≤ T.indicator (fun _ => (1:ℝ)) x := fun x => by
      by_cases hx : x ∈ T <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
    have hTmeas_aesm : AEStronglyMeasurable (T.indicator (fun _ => (1:ℝ))) volume :=
      (measurable_const.indicator hTmeas).aestronglyMeasurable
    simp only [hT] at hTle hTnn hTmeas_aesm hind_int
    have hw0 : ∀ x : ℝ, 0 ≤ G x * T.indicator (fun _ => (1:ℝ)) x :=
      fun x => mul_nonneg (hGnonneg x) (hTnn x)
    have hdom_int : Integrable (fun x : ℝ => G x ^ 2 + T.indicator (fun _ => (1:ℝ)) x) :=
      hGsq_int.add hind_int
    have hw1 : Integrable (fun x : ℝ => G x * T.indicator (fun _ => (1:ℝ)) x) := by
      refine Integrable.mono' (g := fun x : ℝ => G x ^ 2 + T.indicator (fun _ => (1:ℝ)) x)
        hdom_int ?_ ?_
      · exact hGmeas.aestronglyMeasurable.mul hTmeas_aesm
      · filter_upwards with x
        rw [Real.norm_of_nonneg (hw0 x)]
        by_cases hx : x ∈ T
        · rw [Set.indicator_of_mem hx]
          nlinarith [hGnonneg x, sq_nonneg (G x - 1)]
        · rw [Set.indicator_of_notMem hx]
          nlinarith [hGnonneg x, hTnn x]
    have hw2 : MemLp (fun x : ℝ => G x * T.indicator (fun _ => (1:ℝ)) x) 2 volume := by
      refine MemLp.of_le hGmem ?_ ?_
      · exact hGmeas.aestronglyMeasurable.mul hTmeas_aesm
      · filter_upwards with x
        rw [Real.norm_of_nonneg (hw0 x), Real.norm_of_nonneg (hGnonneg x)]
        nlinarith [hGnonneg x, hTle x, hTnn x]
    have hkey := hlin _ hw0 hw1 hw2
    have hsq : (∫ x : ℝ, (G x * T.indicator (fun _ => (1:ℝ)) x) ^ 2) ≤ ∫ x : ℝ, G x ^ 2 := by
      refine integral_mono_ae ?_ hGsq_int ?_
      · refine Integrable.mono' (g := fun x : ℝ => G x ^ 2) hGsq_int ?_ ?_
        · exact (hGmeas.aestronglyMeasurable.mul hTmeas_aesm).pow 2
        · filter_upwards with x
          rw [Real.norm_of_nonneg (sq_nonneg _)]
          have h3 : G x * T.indicator (fun _ => (1:ℝ)) x ≤ G x := by
            nlinarith [hGnonneg x, hTle x, hTnn x]
          exact pow_le_pow_left₀ (mul_nonneg (hGnonneg x) (hTnn x)) h3 2
      · filter_upwards with x
        have h3 : G x * T.indicator (fun _ => (1:ℝ)) x ≤ G x := by
          nlinarith [hGnonneg x, hTle x, hTnn x]
        exact pow_le_pow_left₀ (mul_nonneg (hGnonneg x) (hTnn x)) h3 2
    have hprod : (∫ x : ℝ, (G x * T.indicator (fun _ => (1:ℝ)) x) * G x)
        = ∫ x : ℝ, G x ^ 2 * T.indicator (fun _ => (1:ℝ)) x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    calc (∫ x : ℝ, G x ^ 2 * T.indicator (fun _ => (1:ℝ)) x)
        = ∫ x : ℝ, (G x * T.indicator (fun _ => (1:ℝ)) x) * G x := hprod.symm
      _ ≤ D * Real.sqrt (∫ x : ℝ, (G x * T.indicator (fun _ => (1:ℝ)) x) ^ 2)
            * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) := hkey
      _ ≤ D * Real.sqrt (∫ x : ℝ, G x ^ 2) * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) hD
  have htend : Tendsto
      (fun N : ℕ => ∫ x : ℝ, G x ^ 2 * (Set.Icc (-(N:ℝ)) (N:ℝ)).indicator (fun _ => (1:ℝ)) x)
      atTop (𝓝 (∫ x : ℝ, G x ^ 2)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => G x ^ 2) ?_ hGsq_int ?_ ?_
    · intro N
      exact (hGmeas.pow_const 2).aestronglyMeasurable.mul
        ((measurable_const.indicator measurableSet_Icc).aestronglyMeasurable)
    · intro N
      filter_upwards with x
      have h1 : (Set.Icc (-(N:ℝ)) (N:ℝ)).indicator (fun _ => (1:ℝ)) x ≤ 1 := by
        by_cases hx : x ∈ Set.Icc (-(N:ℝ)) (N:ℝ) <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
      have h2 : 0 ≤ (Set.Icc (-(N:ℝ)) (N:ℝ)).indicator (fun _ => (1:ℝ)) x := by
        by_cases hx : x ∈ Set.Icc (-(N:ℝ)) (N:ℝ) <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
      rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) h2)]
      have hsq : (0:ℝ) ≤ G x ^ 2 := sq_nonneg _
      nlinarith [hsq, h1, h2]
    · filter_upwards with x
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop (Nat.ceil |x|)] with N hN
      have hx : x ∈ Set.Icc (-(N:ℝ)) (N:ℝ) := by
        refine ⟨?_, ?_⟩
        · rw [neg_le]
          exact le_trans (neg_le_abs x) (le_trans (Nat.le_ceil |x|) (by exact_mod_cast hN))
        · exact le_trans (le_abs_self x) (le_trans (Nat.le_ceil |x|) (by exact_mod_cast hN))
      rw [Set.indicator_of_mem hx, mul_one]
  have hfinal : (∫ x : ℝ, G x ^ 2) ≤ D * Real.sqrt (∫ x : ℝ, G x ^ 2)
      * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) :=
    le_of_tendsto htend (Filter.Eventually.of_forall hN)
  have hsq_bound : (∫ x : ℝ, G x ^ 2) ≤ D ^ 2 * (∫ x : ℝ, ‖f x‖ ^ 2) := by
    rcases eq_or_lt_of_le (integral_nonneg (f := fun x : ℝ => G x ^ 2) (fun x => sq_nonneg (G x))) with h | h
    · rw [← h]; positivity
    · have hb : Real.sqrt (∫ x : ℝ, G x ^ 2) ≤ D * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) := by
        have hpos : 0 < Real.sqrt (∫ x : ℝ, G x ^ 2) := Real.sqrt_pos.mpr h
        have hfinal' : Real.sqrt (∫ x : ℝ, G x ^ 2) * Real.sqrt (∫ x : ℝ, G x ^ 2)
            ≤ (D * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2)) * Real.sqrt (∫ x : ℝ, G x ^ 2) := by
          rw [← sq]
          calc (Real.sqrt (∫ x : ℝ, G x ^ 2)) ^ 2 = ∫ x : ℝ, G x ^ 2 :=
                Real.sq_sqrt (integral_nonneg (f := fun x : ℝ => G x ^ 2) (fun x => sq_nonneg (G x)))
            _ ≤ D * Real.sqrt (∫ x : ℝ, G x ^ 2) * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2) := hfinal
            _ = (D * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2)) * Real.sqrt (∫ x : ℝ, G x ^ 2) := by ring
        exact le_of_mul_le_mul_right hfinal' hpos
      calc (∫ x : ℝ, G x ^ 2) = (Real.sqrt (∫ x : ℝ, G x ^ 2)) ^ 2 :=
            (Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg (G x)))).symm
        _ ≤ (D * Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2)) ^ 2 :=
            pow_le_pow_left₀ (Real.sqrt_nonneg _) hb 2
        _ = D ^ 2 * (∫ x : ℝ, ‖f x‖ ^ 2) := by
            rw [mul_pow, Real.sq_sqrt (integral_nonneg (fun x => sq_nonneg ‖f x‖))]
  have hGiSup : ∀ x : ℝ, (⨆ i : ι, ‖bandOp (C i) f x‖ₑ) = ‖G x‖ₑ := by
    intro x
    rw [hG]
    rw [show ‖(⨆ i : ι, ‖bandOp (C i) f x‖)‖ₑ
        = ENNReal.ofReal (⨆ i : ι, ‖bandOp (C i) f x‖) by
      rw [enorm_eq_ofReal_norm_real,
        Real.norm_of_nonneg (le_trans (norm_nonneg _) (le_ciSup (hGbdd x) (Classical.arbitrary ι)))]]
    rw [show (⨆ i : ι, ‖bandOp (C i) f x‖ₑ)
        = ⨆ i : ι, ENNReal.ofReal (‖bandOp (C i) f x‖) from
      iSup_congr (fun i => enorm_eq_ofReal_norm _)]
    exact iSup_ofReal_finset (fun i : ι => ‖bandOp (C i) f x‖)
  calc ∫⁻ x : ℝ, (⨆ i : ι, ‖bandOp (C i) f x‖ₑ) ^ (2:ℝ) ∂volume
      = ∫⁻ x : ℝ, ‖G x‖ₑ ^ (2:ℝ) ∂volume := by
        refine lintegral_congr (fun x => ?_)
        rw [hGiSup x]
    _ = ENNReal.ofReal (∫ x : ℝ, ‖G x‖ ^ (2:ℝ)) :=
        lintegral_enorm_rpow_two_real hGmem
    _ = ENNReal.ofReal (∫ x : ℝ, G x ^ 2) := by
        congr 1
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show ‖G x‖ ^ (2:ℝ) = G x ^ 2
        rw [Real.norm_of_nonneg (hGnonneg x), Real.rpow_two]
    _ ≤ ENNReal.ofReal (D ^ 2 * (∫ x : ℝ, ‖f x‖ ^ 2)) :=
        ENNReal.ofReal_le_ofReal hsq_bound
    _ = ENNReal.ofReal (D ^ 2) * ENNReal.ofReal (∫ x : ℝ, ‖f x‖ ^ 2) :=
        ENNReal.ofReal_mul (sq_nonneg D)
    _ = ENNReal.ofReal (D ^ 2) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) ∂volume := by
        rw [show ENNReal.ofReal (∫ x : ℝ, ‖f x‖ ^ 2)
            = ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) ∂volume from by
          rw [show (∫ x : ℝ, ‖f x‖ ^ 2) = ∫ x : ℝ, ‖f x‖ ^ (2:ℝ) from
            integral_congr_ae (Filter.Eventually.of_forall (fun x => (Real.rpow_two _).symm))]
          exact (NestedIndicator.lintegral_enorm_rpow_two volume hf2).symm]

/-! ### Transfer of the dual hypothesis from `ℕ` to `Fin M` -/

private lemma hdual_fin {D : ℝ} {C : ℕ → Set ℝ}
    (hdual : ∀ (J : Finset ℕ) (u : ℕ → ℝ → ℂ),
      (∀ j ∈ J, MemLp (u j) 2 (volume : Measure ℝ)) →
      (∀ j ∈ J, ∀ k ∈ J, j ≠ k → ∀ x : ℝ, u j x * star (u k x) = 0) →
      Real.sqrt (∫ x : ℝ, ‖∑ j ∈ J, bandOp (C j) (u j) x‖ ^ 2)
        ≤ D * Real.sqrt (∑ j ∈ J, ∫ x : ℝ, ‖u j x‖ ^ 2))
    (M : ℕ) :
    ∀ (J : Finset (Fin M)) (u : Fin M → ℝ → ℂ),
      (∀ j ∈ J, MemLp (u j) 2 (volume : Measure ℝ)) →
      (∀ j ∈ J, ∀ k ∈ J, j ≠ k → ∀ x : ℝ, u j x * star (u k x) = 0) →
      Real.sqrt (∫ x : ℝ, ‖∑ j ∈ J, bandOp (C j.val) (u j) x‖ ^ 2)
        ≤ D * Real.sqrt (∑ j ∈ J, ∫ x : ℝ, ‖u j x‖ ^ 2) := by
  intro J u hu hd
  set u' : ℕ → ℝ → ℂ := fun n => if h : n < M then u ⟨n, h⟩ else 0 with hu'def
  have hu'val : ∀ i : Fin M, u' i.val = u i := by
    intro i
    simp [hu'def]
  set J' : Finset ℕ := J.image Fin.val with hJ'def
  have hinj : ∀ a ∈ J, ∀ b ∈ J, (a : ℕ) = (b : ℕ) → a = b := fun a _ b _ h => Fin.ext h
  have hu' : ∀ n ∈ J', MemLp (u' n) 2 (volume : Measure ℝ) := by
    intro n hn
    rw [hJ'def] at hn
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    rw [hu'val i]
    exact hu i hi
  have hd' : ∀ n ∈ J', ∀ k ∈ J', n ≠ k → ∀ x : ℝ, u' n x * star (u' k x) = 0 := by
    intro n hn k hk hnk x
    rw [hJ'def] at hn hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨i', hi', rfl⟩ := Finset.mem_image.mp hk
    rw [hu'val i, hu'val i']
    exact hd i hi i' hi' (fun h => hnk (by rw [h])) x
  have hsum1 : (∫ x : ℝ, ‖∑ j ∈ J, bandOp (C j.val) (u j) x‖ ^ 2)
      = ∫ x : ℝ, ‖∑ n ∈ J', bandOp (C n) (u' n) x‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards with x
    have h : (∑ j ∈ J, bandOp (C j.val) (u j) x)
        = ∑ n ∈ J', bandOp (C n) (u' n) x := by
      rw [hJ'def, Finset.sum_image hinj]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hu'val i]
    rw [h]
  have hsum2 : (∑ j ∈ J, ∫ x : ℝ, ‖u j x‖ ^ 2)
      = ∑ n ∈ J', ∫ x : ℝ, ‖u' n x‖ ^ 2 := by
    rw [hJ'def, Finset.sum_image hinj]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hu'val i]
  rw [hsum1, hsum2]
  exact hdual J' u' hu' hd'

/-! ### The main theorem -/

/-- **Maximal `L²` inequality from a dual "sum" bound, for a `bandOp` family indexed by `ℕ`.**
Let `C : ℕ → Set ℝ` be measurable and bounded.  Assume that for every finite index set `J` and
every family `u j` (`j ∈ J`) of `L²` functions with *pairwise disjoint supports* the dual bound
`‖∑_{j∈J} bandOp (C j) (u j)‖₂ ≤ D (∑_{j∈J} ‖u j‖²)^{1/2}` holds.  Then the maximal operator
`f ↦ sup_j |bandOp (C j) f|` is bounded on `L²` with the *same* constant `D`:
`∫⁻ (sup_j ‖bandOp (C j) f‖ₑ)² ≤ D² ∫⁻ ‖f‖ₑ²`. -/
theorem bandOp_maximal_l2_of_dual (D : ℝ) (hD : 0 ≤ D) (C : ℕ → Set ℝ)
    (hmeas : ∀ j, MeasurableSet (C j)) (hbd : ∀ j, Bornology.IsBounded (C j))
    (hdual : ∀ (J : Finset ℕ) (u : ℕ → ℝ → ℂ),
      (∀ j ∈ J, MeasureTheory.MemLp (u j) 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) →
      (∀ j ∈ J, ∀ k ∈ J, j ≠ k → ∀ x : ℝ, u j x * star (u k x) = 0) →
      Real.sqrt (∫ x : ℝ, ‖∑ j ∈ J, bandOp (C j) (u j) x‖ ^ 2)
        ≤ D * Real.sqrt (∑ j ∈ J, ∫ x : ℝ, ‖u j x‖ ^ 2))
    (f : ℝ → ℂ) (hf1 : MeasureTheory.Integrable f)
    (hf2 : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    ∫⁻ x : ℝ, (⨆ j : ℕ, ‖bandOp (C j) f x‖ₑ) ^ (2:ℝ)
      ≤ ENNReal.ofReal (D ^ 2) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := by
  have hfin : ∀ M : ℕ, ∫⁻ x : ℝ, (⨆ i : Fin (M + 1), ‖bandOp (C i.val) f x‖ₑ) ^ (2:ℝ)
      ≤ ENNReal.ofReal (D ^ 2) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := by
    intro M
    have hlin := linearization_bound_dual (Nat.succ_le_succ (Nat.zero_le M))
      (fun i : Fin (M + 1) => C i.val) (fun i => hmeas i.val) (fun i => hbd i.val)
      D (hdual_fin hdual (M + 1)) f hf1 hf2
    exact maximal_bound_of_weighted_bound (fun i : Fin (M + 1) => C i.val)
      (fun i => hmeas i.val) (fun i => hbd i.val) f hf1 hf2 D hD
      (fun w hw0 hw1 hw2 => hlin w hw0 hw1 hw2)
  have hb : ∀ j : ℕ, Measurable (fun x : ℝ => ‖bandOp (C j) f x‖ₑ) :=
    fun j => (bandOp_cont (C j) (hmeas j) (hbd j) f hf1).measurable.enorm
  calc ∫⁻ x : ℝ, (⨆ j : ℕ, ‖bandOp (C j) f x‖ₑ) ^ (2:ℝ)
      = ⨆ M : ℕ, ∫⁻ x : ℝ, (⨆ i : Fin (M + 1), ‖bandOp (C i.val) f x‖ₑ) ^ (2:ℝ) :=
        lintegral_iSup_fin_succ (fun j x => ‖bandOp (C j) f x‖ₑ) hb
    _ ≤ ENNReal.ofReal (D ^ 2) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := iSup_le hfin

end

end Commons.Analysis.Fourier
