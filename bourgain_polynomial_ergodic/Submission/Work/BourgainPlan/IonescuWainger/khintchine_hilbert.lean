import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.TaoDefs
import Submission.Work.BourgainPlan.IonescuWainger.SuperOrthoDefs
import Submission.Work.BourgainPlan.IonescuWainger.nonceFree_tuple_sum_le
import Submission.Work.BourgainPlan.IonescuWainger.sum_inner_pow_expansion

/-!
# The Hilbert-space-valued superorthogonal Khintchine inequality

Tao (arXiv:2008.05066), Theorem `sys-ortho`(i), in the Hilbert-space-valued form needed for the
probabilistic-decoupling proof of the hypersystem form: a Type II `2r`-superorthogonal system of
`E`-valued functions obeys the Khintchine square-function bound with a constant depending only
on `r`.
-/

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory Finset Filter
open scoped ENNReal BigOperators

variable {X : Type*} [MeasurableSpace X]

/-- `ENNReal.ofReal` is subadditive over finite sums. -/
theorem ofReal_sum_le {α : Type*} (s : Finset α) (g : α → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, g i) ≤ ∑ i ∈ s, ENNReal.ofReal (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [sum_insert ha, sum_insert ha]
      exact ENNReal.ofReal_add_le.trans (add_le_add_right ih (ENNReal.ofReal (g a)))

/-- **Superorthogonal Khintchine inequality** (Tao, arXiv:2008.05066, Theorem `sys-ortho`(i)),
Hilbert-space-valued form. -/
theorem khintchine_hilbert {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (r : ℕ) (hr : 1 ≤ r) (μ : MeasureTheory.Measure X) (f : ι → X → E)
    (hf_meas : ∀ i, AEMeasurable (f i) μ)
    (hf_int : ∀ s : Fin r ⊕ Fin r → ι,
      MeasureTheory.Integrable (fun x => ∏ i : Fin r, ‖f (s (Sum.inl i)) x‖ * ‖f (s (Sum.inr i)) x‖) μ)
    (h_orth : ∀ s : Fin r ⊕ Fin r → ι, HasNonceTuple s →
      ∫ x, (∏ i : Fin r, inner ℂ (f (s (Sum.inl i)) x) (f (s (Sum.inr i)) x)) ∂μ = 0) :
    ∫⁻ x, ‖∑ i, f i x‖ₑ ^ (2 * (r : ℝ)) ∂μ
      ≤ ENNReal.ofReal ((max 1 (Real.exp 1 * (r : ℝ) ^ (2 * r))) ^ r) *
        ∫⁻ x, (∑ i, ‖f i x‖ₑ ^ (2 : ℝ)) ^ r ∂μ := by
  classical
  set D : ℝ := Real.exp 1 * (r : ℝ) ^ (2 * r) with hDdef
  have hDnn : 0 ≤ D := by rw [hDdef]; positivity
  -- ## 1. The pointwise expansion of `‖∑ f_i x‖^{2r}`
  have hpt : ∀ x : X, ‖∑ i, f i x‖ ^ (2 * (r : ℝ))
      = ∑ q : Fin r → ι × ι, (∏ k : Fin r, inner ℂ (f (q k).1 x) (f (q k).2 x)).re := by
    intro x
    have h2 : ‖∑ i, f i x‖ ^ (2 * (r : ℝ))
        = ((inner ℂ (∑ i, f i x) (∑ i, f i x)) ^ r).re := by
      have h : (inner ℂ (∑ i, f i x) (∑ i, f i x)) ^ r
          = (((‖∑ i, f i x‖ ^ (2 * (r : ℝ)) : ℝ)) : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (∑ i, f i x), ← RCLike.ofReal_pow,
          ← RCLike.ofReal_pow,
          show (2 : ℝ) * (r : ℝ) = ((2 * r : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
          pow_mul]
        rfl
      rw [h]
      simp
    rw [h2, sum_inner_pow_expansion r (fun i => f i x)]
    exact map_sum Complex.reCLM _ Finset.univ
  -- ## 2. Integrability of the tuple terms
  have hHnn : ∀ (q : Fin r → ι × ι) (x : X),
      0 ≤ ∏ k : Fin r, ‖f (q k).1 x‖ * ‖f (q k).2 x‖ := by
    intro q x
    exact prod_nonneg fun k _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hHint : ∀ q : Fin r → ι × ι,
      Integrable (fun x => ∏ k : Fin r, ‖f (q k).1 x‖ * ‖f (q k).2 x‖) μ := by
    intro q
    simpa only [tupleOf_inl, tupleOf_inr] using hf_int (tupleOf q)
  have hGmeas : ∀ q : Fin r → ι × ι,
      AEMeasurable (fun x : X => ∏ k : Fin r, inner ℂ (f (q k).1 x) (f (q k).2 x)) μ := by
    intro q
    exact Finset.aemeasurable_fun_prod (Finset.univ : Finset (Fin r)) (fun k _ =>
        continuous_inner.measurable.comp_aemeasurable ((hf_meas _).prodMk (hf_meas _)))
  have hGbound : ∀ (q : Fin r → ι × ι) (x : X),
      ‖∏ k : Fin r, inner ℂ (f (q k).1 x) (f (q k).2 x)‖
        ≤ ∏ k : Fin r, ‖f (q k).1 x‖ * ‖f (q k).2 x‖ := by
    intro q x
    refine (Finset.norm_prod_le (Finset.univ : Finset (Fin r)) _).trans ?_
    exact Finset.prod_le_prod₀ (fun k _ => norm_nonneg _) (fun k _ => norm_inner_le_norm _ _)
  have hGint : ∀ q : Fin r → ι × ι,
      Integrable (fun x : X => ∏ k : Fin r, inner ℂ (f (q k).1 x) (f (q k).2 x)) μ := by
    intro q
    exact Integrable.mono' (hHint q) (AEMeasurable.aestronglyMeasurable (hGmeas q))
      (Eventually.of_forall (hGbound q))
  have hGre : ∀ q : Fin r → ι × ι,
      Integrable (fun x : X => (∏ k : Fin r, inner ℂ (f (q k).1 x) (f (q k).2 x)).re) μ :=
    fun q => (hGint q).re
  have hGre_le : ∀ (q : Fin r → ι × ι) (x : X),
      (∏ k : Fin r, inner ℂ (f (q k).1 x) (f (q k).2 x)).re
        ≤ ∏ k : Fin r, ‖f (q k).1 x‖ * ‖f (q k).2 x‖ := by
    intro q x
    exact (le_abs_self _).trans ((Complex.abs_re_le_norm _).trans (hGbound q x))
  -- ## 3. The integral identity
  have hIntF : Integrable (fun x => ‖∑ i, f i x‖ ^ (2 * (r : ℝ))) μ :=
    (integrable_finsetSum (Finset.univ : Finset (Fin r → ι × ι)) (fun q _ => hGre q)).congr
      (Eventually.of_forall fun x => (hpt x).symm)
  have hint_eq : ∫ x, ‖∑ i, f i x‖ ^ (2 * (r : ℝ)) ∂μ
      = ∑ q : Fin r → ι × ι,
          ∫ x, (∏ k : Fin r, inner ℂ (f (q k).1 x) (f (q k).2 x)).re ∂μ := by
    rw [show (fun x => ‖∑ i, f i x‖ ^ (2 * (r : ℝ)))
          = (fun x => ∑ q : Fin r → ι × ι,
              (∏ k : Fin r, inner ℂ (f (q k).1 x) (f (q k).2 x)).re) from funext hpt]
    exact integral_finsetSum _ (fun q _ => hGre q)
  -- ## 4. Discarding the tuples carrying a nonce
  have hTsum : ∑ q ∈ (Finset.univ : Finset (Fin r → ι × ι)).filter (NonceFreeTuple r),
        ∫ x, (∏ k : Fin r, inner ℂ (f (q k).1 x) (f (q k).2 x)).re ∂μ
      = ∑ q : Fin r → ι × ι,
        ∫ x, (∏ k : Fin r, inner ℂ (f (q k).1 x) (f (q k).2 x)).re ∂μ := by
    rw [← sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin r → ι × ι)))
      (p := NonceFreeTuple r)
      (f := fun q => ∫ x, (∏ k : Fin r, inner ℂ (f (q k).1 x) (f (q k).2 x)).re ∂μ)]
    have hzero : ∑ q ∈ (Finset.univ : Finset (Fin r → ι × ι)).filter
          (fun q => ¬ NonceFreeTuple r q),
        ∫ x, (∏ k : Fin r, inner ℂ (f (q k).1 x) (f (q k).2 x)).re ∂μ = 0 := by
      apply sum_eq_zero
      intro q hq
      rw [mem_filter] at hq
      have hq' : HasNonceTuple (tupleOf q) := by
        simpa only [NonceFreeTuple, not_not] using hq.2
      have h1 : ∫ x, (∏ k : Fin r, inner ℂ (f (q k).1 x) (f (q k).2 x)) ∂μ = 0 :=
        h_orth (tupleOf q) hq'
      have h2 := hGint q
      have h3 : ∫ x, RCLike.re (∏ k : Fin r, inner ℂ (f (q k).1 x) (f (q k).2 x)) ∂μ
          = RCLike.re (∫ x, (∏ k : Fin r, inner ℂ (f (q k).1 x) (f (q k).2 x)) ∂μ) :=
        integral_re h2
      rw [h1] at h3
      simp only [map_zero] at h3
      simpa using h3
    rw [hzero, add_zero]
  -- ## 5. The `ENNReal` chain
  have hRnn : ∀ x : X, 0 ≤ (∑ i, ‖f i x‖ ^ 2) ^ r :=
    fun x => pow_nonneg (sum_nonneg fun _ _ => sq_nonneg _) _
  have hRmeas : AEMeasurable (fun x : X => ENNReal.ofReal ((∑ i, ‖f i x‖ ^ 2) ^ r)) μ := by
    have h1 : AEMeasurable (fun x : X => ∑ i, ‖f i x‖ ^ 2) μ := by
      exact Finset.aemeasurable_fun_sum (Finset.univ : Finset ι)
        (fun i _ => (hf_meas i).norm.pow_const 2)
    exact ENNReal.measurable_ofReal.comp_aemeasurable (h1.pow_const r)
  have hcomb : ∀ x : X, ∑ q ∈ (Finset.univ : Finset (Fin r → ι × ι)).filter (NonceFreeTuple r),
        ∏ k : Fin r, ‖f (q k).1 x‖ * ‖f (q k).2 x‖ ≤ D * (∑ i, ‖f i x‖ ^ 2) ^ r := by
    intro x
    have h := nonceFree_tuple_sum_le r hr (fun i => ‖f i x‖) (fun i => norm_nonneg _)
    rw [hDdef]
    exact h
  have main_chain :
      ENNReal.ofReal (∫ x, ‖∑ i, f i x‖ ^ (2 * (r : ℝ)) ∂μ)
        ≤ ENNReal.ofReal D * ∫⁻ x, ENNReal.ofReal ((∑ i, ‖f i x‖ ^ 2) ^ r) ∂μ := by
    rw [hint_eq, ← hTsum]
    calc ENNReal.ofReal (∑ q ∈ (Finset.univ : Finset (Fin r → ι × ι)).filter (NonceFreeTuple r),
            ∫ x, (∏ k : Fin r, inner ℂ (f (q k).1 x) (f (q k).2 x)).re ∂μ)
        ≤ ∑ q ∈ (Finset.univ : Finset (Fin r → ι × ι)).filter (NonceFreeTuple r),
            ENNReal.ofReal (∫ x, (∏ k : Fin r, inner ℂ (f (q k).1 x) (f (q k).2 x)).re ∂μ) :=
          ofReal_sum_le _ _
      _ ≤ ∑ q ∈ (Finset.univ : Finset (Fin r → ι × ι)).filter (NonceFreeTuple r),
            ENNReal.ofReal (∫ x, ∏ k : Fin r, ‖f (q k).1 x‖ * ‖f (q k).2 x‖ ∂μ) := by
          apply sum_le_sum
          intro q hq
          exact ENNReal.ofReal_le_ofReal
            (integral_mono (hGre q) (hHint q) (fun x => hGre_le q x))
      _ = ∑ q ∈ (Finset.univ : Finset (Fin r → ι × ι)).filter (NonceFreeTuple r),
            ∫⁻ x, ENNReal.ofReal (∏ k : Fin r, ‖f (q k).1 x‖ * ‖f (q k).2 x‖) ∂μ := by
          apply sum_congr rfl
          intro q hq
          exact ofReal_integral_eq_lintegral_ofReal (hHint q)
            (Eventually.of_forall (hHnn q))
      _ = ∫⁻ x, ∑ q ∈ (Finset.univ : Finset (Fin r → ι × ι)).filter (NonceFreeTuple r),
            ENNReal.ofReal (∏ k : Fin r, ‖f (q k).1 x‖ * ‖f (q k).2 x‖) ∂μ := by
          rw [lintegral_finsetSum']
          intro q _
          exact ENNReal.measurable_ofReal.comp_aemeasurable
            (Finset.aemeasurable_fun_prod (Finset.univ : Finset (Fin r)) (fun k _ =>
              (hf_meas _).norm.mul (hf_meas _).norm))
      _ ≤ ∫⁻ x, ENNReal.ofReal (D * (∑ i, ‖f i x‖ ^ 2) ^ r) ∂μ := by
          apply lintegral_mono
          intro x
          simp only
          rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => hHnn q x)]
          exact ENNReal.ofReal_le_ofReal (hcomb x)
      _ = ENNReal.ofReal D * ∫⁻ x, ENNReal.ofReal ((∑ i, ‖f i x‖ ^ 2) ^ r) ∂μ := by
          rw [lintegral_congr (g := fun x => ENNReal.ofReal D *
            ENNReal.ofReal ((∑ i, ‖f i x‖ ^ 2) ^ r)) (fun x => ENNReal.ofReal_mul hDnn),
            lintegral_const_mul'' _ hRmeas]
  -- ## 6. Converting the target
  have hLHS : ∫⁻ x, ‖∑ i, f i x‖ₑ ^ (2 * (r : ℝ)) ∂μ
      = ENNReal.ofReal (∫ x, ‖∑ i, f i x‖ ^ (2 * (r : ℝ)) ∂μ) := by
    have hcongr : ∫⁻ x, ‖∑ i, f i x‖ₑ ^ (2 * (r : ℝ)) ∂μ
        = ∫⁻ x, ENNReal.ofReal (‖∑ i, f i x‖ ^ (2 * (r : ℝ))) ∂μ := by
      apply lintegral_congr
      intro x
      rw [← ofReal_norm (∑ i, f i x),
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by positivity)]
    rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal hIntF
      (Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _)]
  have hRHS : ∫⁻ x, (∑ i, ‖f i x‖ₑ ^ (2 : ℝ)) ^ r ∂μ
      = ∫⁻ x, ENNReal.ofReal ((∑ i, ‖f i x‖ ^ 2) ^ r) ∂μ := by
    apply lintegral_congr
    intro x
    have h1 : ∀ i : ι, ‖f i x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (‖f i x‖ ^ 2) := by
      intro i
      rw [← ofReal_norm (f i x), ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
        Real.rpow_two]
    rw [Finset.sum_congr rfl (fun i _ => h1 i),
      ← ENNReal.ofReal_sum_of_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 2),
      ← ENNReal.ofReal_pow (Finset.sum_nonneg (fun i _ => pow_nonneg (norm_nonneg _) 2))]
  rw [hLHS, hRHS]
  refine main_chain.trans ?_
  rw [hDdef]
  gcongr
  exact le_trans (le_max_right _ _)
    (by simpa using pow_le_pow_right₀ (le_max_left (1 : ℝ) (Real.exp 1 * (r : ℝ) ^ (2 * r))) hr)


/-- **Superorthogonal Khintchine inequality**, variant where the integrability hypothesis is on the
square function (rather than on all `2r`-fold products of norms). -/
theorem khintchine_hilbert_sq {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E]
    (r : ℕ) (hr : 1 ≤ r) (μ : MeasureTheory.Measure X) (f : ι → X → E)
    (hf_meas : ∀ i, AEMeasurable (f i) μ)
    (hint : MeasureTheory.Integrable (fun x => (∑ i, ‖f i x‖ ^ 2) ^ r) μ)
    (h_orth : ∀ s : Fin r ⊕ Fin r → ι, HasNonceTuple s →
      ∫ x, (∏ i : Fin r, inner ℂ (f (s (Sum.inl i)) x) (f (s (Sum.inr i)) x)) ∂μ = 0) :
    ∫⁻ x, ‖∑ i, f i x‖ₑ ^ (2 * (r : ℝ)) ∂μ
      ≤ ENNReal.ofReal ((max 1 (Real.exp 1 * (r : ℝ) ^ (2 * r))) ^ r) *
        ∫⁻ x, (∑ i, ‖f i x‖ₑ ^ (2 : ℝ)) ^ r ∂μ := by
  refine khintchine_hilbert (X := X) (ι := ι) (E := E) r hr μ f hf_meas ?_ h_orth
  intro s
  have hSl : ∀ x : X, 0 ≤ ∑ i, ‖f i x‖ ^ 2 := fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hle : ∀ x : X,
      ∏ j : Fin r, ‖f (s (Sum.inl j)) x‖ * ‖f (s (Sum.inr j)) x‖ ≤ (∑ i, ‖f i x‖ ^ 2) ^ r := by
    intro x
    have hfac : ∀ j : Fin r, ‖f (s (Sum.inl j)) x‖ * ‖f (s (Sum.inr j)) x‖ ≤ ∑ i, ‖f i x‖ ^ 2 := by
      intro j
      have h1 : ‖f (s (Sum.inl j)) x‖ ^ 2 ≤ ∑ i, ‖f i x‖ ^ 2 :=
        Finset.single_le_sum (f := fun i => ‖f i x‖ ^ 2) (fun i _ => sq_nonneg _)
          (Finset.mem_univ _)
      have h2 : ‖f (s (Sum.inr j)) x‖ ^ 2 ≤ ∑ i, ‖f i x‖ ^ 2 :=
        Finset.single_le_sum (f := fun i => ‖f i x‖ ^ 2) (fun i _ => sq_nonneg _)
          (Finset.mem_univ _)
      have hs1 : ‖f (s (Sum.inl j)) x‖ ≤ Real.sqrt (∑ i, ‖f i x‖ ^ 2) :=
        (Real.le_sqrt (norm_nonneg _) (hSl x)).mpr h1
      have hs2 : ‖f (s (Sum.inr j)) x‖ ≤ Real.sqrt (∑ i, ‖f i x‖ ^ 2) :=
        (Real.le_sqrt (norm_nonneg _) (hSl x)).mpr h2
      calc ‖f (s (Sum.inl j)) x‖ * ‖f (s (Sum.inr j)) x‖
          ≤ Real.sqrt (∑ i, ‖f i x‖ ^ 2) * Real.sqrt (∑ i, ‖f i x‖ ^ 2) :=
            mul_le_mul hs1 hs2 (norm_nonneg _) (Real.sqrt_nonneg _)
        _ = ∑ i, ‖f i x‖ ^ 2 := Real.mul_self_sqrt (hSl x)
    calc ∏ j : Fin r, ‖f (s (Sum.inl j)) x‖ * ‖f (s (Sum.inr j)) x‖
        ≤ ∏ _j : Fin r, (∑ i, ‖f i x‖ ^ 2) :=
          Finset.prod_le_prod₀ (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
            (fun j _ => hfac j)
      _ = (∑ i, ‖f i x‖ ^ 2) ^ r := by rw [Finset.prod_const]; simp
  have hmeas : AEMeasurable (fun x => ∏ j : Fin r,
      ‖f (s (Sum.inl j)) x‖ * ‖f (s (Sum.inr j)) x‖) μ :=
    Finset.aemeasurable_fun_prod (Finset.univ : Finset (Fin r))
      (fun j _ => (hf_meas _).norm.mul (hf_meas _).norm)
  refine Integrable.mono' hint hmeas.aestronglyMeasurable ?_
  filter_upwards with x
  rw [Real.norm_of_nonneg (Finset.prod_nonneg (fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))]
  exact hle x

end Work.BourgainPlan.IonescuWainger
