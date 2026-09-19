import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.MeasureTheory.Integral.beta_integral
import Submission.Commons.MeasureTheory.Integral.marginal_set_error_le

open MeasureTheory Set intervalIntegral
open scoped BigOperators ENNReal Pointwise

/-!
# The `k`-dimensional beta-function identity (Polymath8a Lemma 7.2)

`∫_{R^k} (1 - Σ tᵢ)^a ∏ tᵢ^{bᵢ} dt = a! · ∏ bᵢ! / (a + Σ bᵢ + k)!` where
`R^k = {t : Fin k → ℝ | tᵢ ≥ 0, Σ tᵢ ≤ 1}`.

The proof inducts on `k`.  Slicing off the last coordinate (via the
measure-preserving equivalence `ℝ^k × ℝ ≃ᵐ ℝ^{k+1}` and Fubini) and rescaling
the slice using the homogeneity of the simplex reduces the `(k+1)`-dimensional
integral to the `k`-dimensional one times the one-dimensional beta integral,
which is `Commons.MeasureTheory.Integral.beta_integral`.
-/

namespace Commons.MeasureTheory.Integral

noncomputable section

private def simplexSet (n : ℕ) (c : ℝ) : Set (Fin n → ℝ) :=
  {u | (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ c}

private lemma measurableSet_simplexSet (n : ℕ) (c : ℝ) : MeasurableSet (simplexSet n c) := by
  have h : simplexSet n c = (⋂ i, {u : Fin n → ℝ | 0 ≤ u i}) ∩ {u | ∑ i, u i ≤ c} := by
    ext u; simp [simplexSet, Set.mem_iInter]
  rw [h]
  exact (MeasurableSet.iInter fun i => measurableSet_le measurable_const (measurable_pi_apply i)).inter
    (measurableSet_le (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)) measurable_const)

private lemma mem_simplexSet_iff {n : ℕ} {c : ℝ} {u : Fin n → ℝ} :
    u ∈ simplexSet n c ↔ (∀ i, 0 ≤ u i) ∧ ∑ i, u i ≤ c := Iff.rfl

private def E0 (n : ℕ) : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n+1) → ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm

private lemma E0_apply (n : ℕ) (x : ℝ) (u : Fin n → ℝ) : E0 n (x,u) = Fin.cons x u := by
  unfold E0
  rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
  rfl

private lemma E0_measurePreserving (n : ℕ) :
    MeasurePreserving (E0 n) (volume : Measure (ℝ × (Fin n → ℝ))) (volume : Measure (Fin (n+1) → ℝ)) := by
  unfold E0
  have h := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
  rw [Measure.volume_eq_prod] at h
  exact h

private lemma smul_simplexSet {n : ℕ} {c : ℝ} (hc : 0 < c) :
    c • simplexSet n 1 = simplexSet n c := by
  ext u
  constructor
  · intro hu
    rcases hu with ⟨v, hv, rfl⟩
    refine ⟨fun i => mul_nonneg hc.le (hv.1 i), ?_⟩
    have : (∑ i, (c • v) i) = c * ∑ i, v i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => rfl)
    rw [this]
    calc c * ∑ i, v i ≤ c * 1 := mul_le_mul_of_nonneg_left hv.2 hc.le
      _ = c := mul_one c
  · intro hu
    refine ⟨c⁻¹ • u, ⟨fun i => mul_nonneg (inv_nonneg.2 hc.le) (hu.1 i), ?_⟩, ?_⟩
    · have : (∑ i, (c⁻¹ • u) i) = c⁻¹ * ∑ i, u i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => rfl)
      rw [this]
      calc c⁻¹ * ∑ i, u i ≤ c⁻¹ * c := mul_le_mul_of_nonneg_left hu.2 (inv_nonneg.2 hc.le)
        _ = 1 := inv_mul_cancel₀ hc.ne'
    · ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

private lemma setIntegral_simplex_smul {n : ℕ} {c : ℝ} (hc : 0 < c) (f : (Fin n → ℝ) → ℝ) :
    ∫ u in simplexSet n c, f u = c ^ n * ∫ v in simplexSet n 1, f (c • v) := by
  have h := Measure.setIntegral_comp_smul_of_pos (μ := (volume : Measure (Fin n → ℝ))) f
      (simplexSet n 1) hc
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin,
    smul_simplexSet hc, smul_eq_mul] at h
  have hc' : (c : ℝ) ^ n ≠ 0 := by positivity
  rw [h, ← mul_assoc, mul_inv_cancel₀ hc', one_mul]

private lemma volume_simplexSet_lt_top (n : ℕ) :
    (volume : Measure (Fin n → ℝ)) (simplexSet n 1) < ∞ := by
  calc (volume : Measure (Fin n → ℝ)) (simplexSet n 1)
      ≤ (volume : Measure (Fin n → ℝ)) (Set.pi Set.univ (fun _ : Fin n => Icc (0:ℝ) 1)) :=
        measure_mono (fun u hu => by
          simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc]
          exact fun i => ⟨hu.1 i, le_trans (Finset.single_le_sum (fun j _ => hu.1 j)
            (Finset.mem_univ i)) hu.2⟩)
    _ = ∏ _ : Fin n, (volume : Measure ℝ) (Icc (0:ℝ) 1) := volume_pi_pi _
    _ < ∞ := ENNReal.prod_lt_top (fun i _ => by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)

private lemma E0_preimage (n : ℕ) :
    (E0 n) ⁻¹' simplexSet (n+1) 1
      = (Icc (0:ℝ) 1 ×ˢ (univ : Set (Fin n → ℝ)))
        ∩ {z : ℝ × (Fin n → ℝ) | z.2 ∈ simplexSet n (1 - z.1)} := by
  ext z
  rw [Set.mem_preimage, E0_apply]
  simp only [simplexSet, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_Icc,
    Set.mem_univ, and_true]
  rw [Fin.sum_univ_succ, Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  constructor
  · rintro ⟨⟨h0, hu0⟩, hsum⟩
    have hs : 0 ≤ ∑ x, z.2 x := Finset.sum_nonneg (fun i _ => hu0 i)
    exact ⟨⟨h0, by linarith⟩, hu0, by linarith⟩
  · rintro ⟨⟨h0, h1⟩, hu0, hsum⟩
    have hs : 0 ≤ ∑ x, z.2 x := Finset.sum_nonneg (fun i _ => hu0 i)
    exact ⟨⟨h0, hu0⟩, by linarith⟩

private lemma integral_simplex_succ {n : ℕ} (W : (Fin (n+1) → ℝ) → ℝ)
    (hW : Continuous W) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ p ∈ simplexSet (n+1) 1, ‖W p‖ ≤ C) :
    ∫ p in simplexSet (n+1) 1, W p
      = ∫ x in Icc (0:ℝ) 1, ∫ u in simplexSet n (1 - x), W (Fin.cons x u) := by
  classical
  set A : Set (ℝ × (Fin n → ℝ)) := {z | z.2 ∈ simplexSet n (1 - z.1)} with hA
  have hmemA : ∀ z : ℝ × (Fin n → ℝ), z ∈ A ↔ z.2 ∈ simplexSet n (1 - z.1) := by
    intro z; rw [hA]; exact Iff.rfl
  have hAmeas : MeasurableSet A := by
    have h : A = {z : ℝ × (Fin n → ℝ) | (∀ i, 0 ≤ z.2 i) ∧ z.1 + ∑ i, z.2 i ≤ 1} := by
      ext z
      rw [hmemA]
      simp only [simplexSet, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, by linarith⟩
    rw [h]
    have h2 : {z : ℝ × (Fin n → ℝ) | (∀ i, 0 ≤ z.2 i) ∧ z.1 + ∑ i, z.2 i ≤ 1}
        = (⋂ i, {z : ℝ × (Fin n → ℝ) | 0 ≤ z.2 i})
          ∩ {z : ℝ × (Fin n → ℝ) | z.1 + ∑ i, z.2 i ≤ 1} := by
      ext z; simp [Set.mem_iInter]
    rw [h2]
    refine MeasurableSet.inter (MeasurableSet.iInter fun i => ?_) ?_
    · exact measurableSet_le measurable_const ((measurable_pi_apply i).comp measurable_snd)
    · exact measurableSet_le (measurable_fst.add
        (Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).comp measurable_snd)))
        measurable_const
  have hSmeas1 : MeasurableSet (simplexSet n 1) := measurableSet_simplexSet n 1
  have hBmeas : MeasurableSet (Icc (0:ℝ) 1 ×ˢ (univ : Set (Fin n → ℝ))) :=
    measurableSet_Icc.prod MeasurableSet.univ
  have hInt : IntegrableOn (A.indicator (fun z : ℝ × (Fin n → ℝ) => W (E0 n z)))
      (Icc (0:ℝ) 1 ×ˢ simplexSet n 1) (volume : Measure (ℝ × (Fin n → ℝ))) := by
    refine IntegrableOn.of_bound ?_ ?_ C ?_
    · rw [Measure.volume_eq_prod, Measure.prod_prod]
      exact ENNReal.mul_lt_top (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)
        (volume_simplexSet_lt_top n)
    · exact (Measurable.indicator (hW.measurable.comp (E0 n).measurable) hAmeas).aestronglyMeasurable
    · rw [ae_restrict_iff' (measurableSet_Icc.prod hSmeas1)]
      refine Filter.Eventually.of_forall (fun z hz => ?_)
      by_cases hzA : z ∈ A
      · rw [Set.indicator_of_mem hzA]
        refine hC _ ?_
        rw [E0_apply]
        simp only [simplexSet, Set.mem_ofPred_eq]
        rw [Fin.sum_univ_succ, Fin.forall_fin_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        have hz1 : z.1 ∈ Icc (0:ℝ) 1 := hz.1
        have hz2 : z.2 ∈ simplexSet n (1 - z.1) := (hmemA z).mp hzA
        exact ⟨⟨hz1.1, hz2.1⟩, by linarith [hz2.2]⟩
      · rw [Set.indicator_of_notMem hzA, norm_zero]
        exact hC0
  have hstep1 : ∫ p in simplexSet (n+1) 1, W p
      = ∫ z in (Icc (0:ℝ) 1 ×ˢ (univ : Set (Fin n → ℝ))) ∩ A, W (E0 n z) := by
    rw [← (E0_measurePreserving n).map_eq, setIntegral_map_equiv, E0_preimage]
  rw [hstep1]
  rw [← setIntegral_indicator (s := Icc (0:ℝ) 1 ×ˢ (univ : Set (Fin n → ℝ)))
    (f := fun z : ℝ × (Fin n → ℝ) => W (E0 n z)) hAmeas]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (f := A.indicator (fun z : ℝ × (Fin n → ℝ) => W (E0 n z)))
    (s := Icc (0:ℝ) 1 ×ˢ simplexSet n 1) hBmeas
    (Set.prod_mono subset_rfl (subset_univ _)) ?_]
  · rw [Measure.volume_eq_prod ℝ (Fin n → ℝ), setIntegral_prod _ hInt]
    refine setIntegral_congr_fun measurableSet_Icc (fun x hx => ?_)
    have hx0 : 0 ≤ x := hx.1
    have hind : (fun u : Fin n → ℝ => A.indicator (fun z : ℝ × (Fin n → ℝ) => W (E0 n z)) (x, u))
        = (simplexSet n (1 - x)).indicator (fun u => W (Fin.cons x u)) := by
      funext u
      by_cases hu : u ∈ simplexSet n (1 - x)
      · have hmem : (x, u) ∈ A := (hmemA (x,u)).mpr hu
        rw [Set.indicator_of_mem hu, Set.indicator_of_mem hmem, E0_apply]
      · have hmem : (x, u) ∉ A := fun h => hu ((hmemA (x,u)).mp h)
        rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hmem]
    have hset : simplexSet n 1 ∩ simplexSet n (1 - x) = simplexSet n (1 - x) := by
      ext u
      constructor
      · rintro ⟨_, h2⟩; exact h2
      · intro h2
        have hs : 0 ≤ ∑ i, u i := Finset.sum_nonneg (fun i _ => h2.1 i)
        exact ⟨⟨h2.1, by linarith [h2.2, hx0]⟩, h2⟩
    rw [hind, setIntegral_indicator (measurableSet_simplexSet n (1 - x)), hset]
  · intro z hz
    rw [Set.mem_sdiff] at hz
    obtain ⟨hzB, hznot⟩ := hz
    rw [Set.mem_prod] at hzB
    obtain ⟨hz1, hz2⟩ := hzB
    by_cases hzA : z ∈ A
    · refine absurd (Set.mem_prod.2 ⟨hz1, ?_⟩) hznot
      have hz2' : z.2 ∈ simplexSet n (1 - z.1) := (hmemA z).mp hzA
      exact ⟨hz2'.1, by linarith [hz2'.2, hz1.1]⟩
    · rw [Set.indicator_of_notMem hzA]


private lemma continuous_W (n : ℕ) (a : ℕ) (b : Fin (n+1) → ℕ) :
    Continuous (fun p : Fin (n+1) → ℝ => (1 - ∑ i, p i)^a * ∏ i, (p i)^(b i)) := by
  fun_prop

private lemma norm_W_le_one (n : ℕ) (a : ℕ) (b : Fin (n+1) → ℕ) :
    ∀ p ∈ simplexSet (n+1) 1, ‖(1 - ∑ i, p i)^a * ∏ i, (p i)^(b i)‖ ≤ 1 := by
  intro p hp
  have h0 : ∀ i, 0 ≤ p i := hp.1
  have hp1 : ∀ i, p i ≤ 1 := fun i => le_trans (Finset.single_le_sum (fun j _ => h0 j)
    (Finset.mem_univ i)) hp.2
  have hs : 0 ≤ ∑ i, p i := Finset.sum_nonneg (fun i _ => h0 i)
  have h1 : 0 ≤ 1 - ∑ i, p i := by linarith [hp.2]
  have h2 : 1 - ∑ i, p i ≤ 1 := by linarith
  have hpa : (1 - ∑ i, p i)^a ≤ 1 := pow_le_one₀ h1 h2
  have hpb : ∏ i, (p i)^(b i) ≤ 1 := by
    apply Finset.prod_le_one₀
    · intro i _; exact pow_nonneg (h0 i) _
    · intro i _; exact pow_le_one₀ (h0 i) (hp1 i)
  have hprod : 0 ≤ ∏ i, (p i)^(b i) := Finset.prod_nonneg (fun i _ => pow_nonneg (h0 i) _)
  have hnn : 0 ≤ (1 - ∑ i, p i)^a := pow_nonneg h1 _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hnn hprod)]
  calc (1 - ∑ i, p i)^a * ∏ i, (p i)^(b i) ≤ 1 * 1 :=
        mul_le_mul hpa hpb hprod (by norm_num)
    _ = 1 := by norm_num

private lemma simplex_recursion {n : ℕ} (a : ℕ) (b : Fin (n+1) → ℕ) :
    ∫ p in simplexSet (n+1) 1, (1 - ∑ i, p i)^a * ∏ i, (p i)^(b i)
      = (∫ x in Ioo (0:ℝ) 1, x^(b 0) * (1 - x)^(n + a + ∑ i : Fin n, b i.succ))
        * ∫ v in simplexSet n 1, (1 - ∑ i, v i)^a * ∏ i, (v i)^(b i.succ) := by
  set W : (Fin (n+1) → ℝ) → ℝ := fun p => (1 - ∑ i, p i)^a * ∏ i, (p i)^(b i) with hW
  have hWcont : Continuous W := continuous_W n a b
  have hWbound : ∀ p ∈ simplexSet (n+1) 1, ‖W p‖ ≤ 1 := norm_W_le_one n a b
  have hmain : ∫ p in simplexSet (n+1) 1, W p
      = ∫ x in Icc (0:ℝ) 1, ∫ u in simplexSet n (1 - x), W (Fin.cons x u) :=
    integral_simplex_succ W hWcont zero_le_one hWbound
  set Ih : ℝ := ∫ v in simplexSet n 1, (1 - ∑ i, v i)^a * ∏ i, (v i)^(b i.succ) with hIh
  have hstep : ∫ x in Ioo (0:ℝ) 1, (∫ u in simplexSet n (1 - x), W (Fin.cons x u))
      = ∫ x in Ioo (0:ℝ) 1, x^(b 0) * (1 - x)^(n + a + ∑ i : Fin n, b i.succ) * Ih := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun x hx => ?_)
    have hx0 : 0 < x := hx.1
    have hx1 : x < 1 := hx.2
    have hc : 0 < 1 - x := by linarith
    have hWc : ∀ u : Fin n → ℝ,
        W (Fin.cons x u) = ((1 - x) - ∑ i, u i)^a * (x^(b 0) * ∏ i, (u i)^(b i.succ)) := by
      intro u
      have hsum : ∑ i : Fin (n+1), (Fin.cons x u) i = x + ∑ i : Fin n, u i := by
        rw [Fin.sum_univ_succ]; simp
      have hprod : ∏ i : Fin (n+1), ((Fin.cons x u) i)^(b i)
          = x^(b 0) * ∏ i : Fin n, (u i)^(b i.succ) := by
        rw [Fin.prod_univ_succ]; simp
      rw [hW]
      simp only []
      rw [hsum, hprod]
      congr 1
      ring
    have step1 : ∫ u in simplexSet n (1 - x), W (Fin.cons x u)
        = x^(b 0) * ∫ u in simplexSet n (1 - x),
            ((1 - x) - ∑ i, u i)^a * ∏ i, (u i)^(b i.succ) := by
      rw [setIntegral_congr_fun (measurableSet_simplexSet n (1 - x)) (fun u _ => hWc u)]
      rw [show (fun u : Fin n → ℝ => ((1 - x) - ∑ i, u i)^a * (x^(b 0) * ∏ i, (u i)^(b i.succ)))
            = fun u : Fin n → ℝ => x^(b 0) *
                (((1 - x) - ∑ i, u i)^a * ∏ i, (u i)^(b i.succ)) from by funext u; ring]
      rw [MeasureTheory.integral_const_mul]
    have step2 : ∫ u in simplexSet n (1 - x),
            ((1 - x) - ∑ i, u i)^a * ∏ i, (u i)^(b i.succ)
        = (1 - x)^n * ∫ v in simplexSet n 1,
            (((1 - x) - ∑ i, ((1 - x) • v) i)^a * ∏ i, (((1 - x) • v) i)^(b i.succ)) :=
      setIntegral_simplex_smul hc _
    have step3 : ∀ v : Fin n → ℝ,
        (((1 - x) - ∑ i, ((1 - x) • v) i)^a * ∏ i, (((1 - x) • v) i)^(b i.succ))
        = (1 - x)^(a + ∑ i : Fin n, b i.succ) * ((1 - ∑ i, v i)^a * ∏ i, (v i)^(b i.succ)) := by
      intro v
      have hs : ∑ i : Fin n, ((1 - x) • v) i = (1 - x) * ∑ i, v i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => rfl)
      have h1 : ((1 - x) - ∑ i, ((1 - x) • v) i) = (1 - x) * (1 - ∑ i, v i) := by
        rw [hs]; ring
      have h2 : ∏ i : Fin n, (((1 - x) • v) i)^(b i.succ)
          = (1 - x)^(∑ i : Fin n, b i.succ) * ∏ i : Fin n, (v i)^(b i.succ) := by
        have hp : ∀ i : Fin n, (((1 - x) • v) i)^(b i.succ)
            = (1 - x)^(b i.succ) * (v i)^(b i.succ) := by
          intro i; rw [Pi.smul_apply, smul_eq_mul, mul_pow]
        rw [Finset.prod_congr rfl (fun i _ => hp i), Finset.prod_mul_distrib,
          Finset.prod_pow_eq_pow_sum]
      rw [h1, h2, mul_pow, pow_add]
      ring
    rw [step1, step2, hIh, setIntegral_congr_fun (measurableSet_simplexSet n 1) (fun v _ => step3 v),
      MeasureTheory.integral_const_mul]
    rw [show (1 - x)^(n + a + ∑ i : Fin n, b i.succ)
        = (1 - x)^n * (1 - x)^(a + ∑ i : Fin n, b i.succ) by
      rw [← pow_add, Nat.add_assoc]]
    ring
  rw [hW, hmain, integral_Icc_eq_integral_Ioo, hstep, hIh, MeasureTheory.integral_mul_const]


private lemma arith_identity (a b0 P n S : ℕ) :
    ((((n + a + S).factorial * b0.factorial : ℕ) : ℝ)
        / (((n + a + S) + b0 + 1).factorial : ℝ))
      * (((a.factorial * P : ℕ) : ℝ) / ((a + S + n).factorial : ℝ))
    = ((a.factorial * (b0.factorial * P) : ℕ) : ℝ)
        / (((n + a + S) + b0 + 1).factorial : ℝ) := by
  have h1 : (a + S + n) = n + a + S := by omega
  rw [h1]
  have hf1 : (((n + a + S).factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have hf2 : ((((n + a + S) + b0 + 1).factorial : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  push_cast
  field_simp

theorem simplex_monomial_integral {k : ℕ} (a : ℕ) (b : Fin k → ℕ) :
    ∫ t : Fin k → ℝ in {t | (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ 1},
        (1 - ∑ i, t i) ^ a * ∏ i, (t i) ^ (b i) =
      (((a.factorial * ∏ i, (b i).factorial : ℕ)) : ℝ) /
        (((a + ∑ i, b i + k).factorial : ℕ) : ℝ) := by
  suffices h : ∀ (k : ℕ) (a : ℕ) (b : Fin k → ℕ),
      ∫ p in simplexSet k 1, (1 - ∑ i, p i) ^ a * ∏ i, (p i) ^ (b i) =
        (((a.factorial * ∏ i, (b i).factorial : ℕ)) : ℝ) /
          (((a + ∑ i, b i + k).factorial : ℕ) : ℝ) by
    exact h k a b
  intro k
  induction k with
  | zero =>
    intro a b
    have hconst : ∀ p : Fin 0 → ℝ, (1 - ∑ i, p i)^a * ∏ i, (p i)^(b i) = 1 := by
      intro p
      rw [Fin.sum_univ_zero, Fin.prod_univ_zero]
      simp
    have hS : simplexSet 0 1 = (Set.univ : Set (Fin 0 → ℝ)) := by
      ext u; simp [simplexSet]
    have huniv : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
      rw [volume_pi]
      exact Measure.pi_empty_univ _
    rw [hS, setIntegral_congr_fun MeasurableSet.univ (fun p _ => hconst p), setIntegral_const,
      Measure.real_def, huniv]
    rw [Fin.prod_univ_zero, Fin.sum_univ_zero]
    simp only [Nat.mul_one, Nat.add_zero, ENNReal.toReal_one, one_smul]
    rw [div_self (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero a))]
  | succ n ih =>
    intro a b
    rw [simplex_recursion a b, ih a (fun i : Fin n => b i.succ)]
    have hx : ∫ x in Ioo (0:ℝ) 1, x^(b 0) * (1 - x)^(n + a + ∑ i : Fin n, b i.succ)
        = (((n + a + ∑ i : Fin n, b i.succ).factorial * (b 0).factorial : ℕ) : ℝ) /
          (((n + a + ∑ i : Fin n, b i.succ) + b 0 + 1).factorial : ℝ) := by
      rw [show (∫ x in Ioo (0:ℝ) 1, x^(b 0) * (1 - x)^(n + a + ∑ i : Fin n, b i.succ))
            = ∫ x in Ioo (0:ℝ) 1, (1 - x)^(n + a + ∑ i : Fin n, b i.succ) * x^(b 0) from by
          apply setIntegral_congr_fun measurableSet_Ioo
          intro x _
          ring]
      exact beta_integral _ _
    rw [hx]
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
    rw [show (a + (b 0 + ∑ i : Fin n, b i.succ) + (n + 1))
        = ((n + a + ∑ i : Fin n, b i.succ) + b 0 + 1) by omega]
    exact arith_identity a (b 0) (∏ i : Fin n, (b i.succ).factorial) n
      (∑ i : Fin n, b i.succ)

end
end Commons.MeasureTheory.Integral

