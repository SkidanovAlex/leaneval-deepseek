import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Fourier.circle_multiplier_identity

open MeasureTheory Finset
open scoped BigOperators ENNReal ComplexInnerProductSpace

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace Commons.Analysis.Fourier

namespace NestedScales

noncomputable section

private lemma fourier_neg_eq (n : ℤ) (x : ℝ) :
    (fourier (T := (1:ℝ)) (-n) (x : AddCircle (1:ℝ)) : ℂ)
      = Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(x:ℂ))) := by
  rw [fourier_coe_apply, show ((1:ℝ):ℂ) = 1 by norm_num, div_one]
  congr 1
  push_cast
  ring

private lemma coeff_eq_integral (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeff (AddCircle.liftIoc (1:ℝ) 0 f : AddCircle (1:ℝ) → ℂ) n =
      ∫ θ in (0:ℝ)..1, f θ * Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))) := by
  rw [fourierCoeff_liftIoc_eq (a := (0:ℝ)) (T := (1:ℝ)) f n, fourierCoeffOn_eq_integral]
  rw [show (0:ℝ) + 1 - 0 = 1 by norm_num, show (0:ℝ) + 1 = 1 by norm_num]
  simp only [div_one, one_smul]
  refine intervalIntegral.integral_congr (fun x hx => ?_)
  rw [fourier_neg_eq n x, smul_eq_mul, mul_comm]

private lemma circle_integral_eq_interval (Φ : AddCircle (1:ℝ) → ℂ) :
    (∫ t : AddCircle (1:ℝ), Φ t) = ∫ x in (0:ℝ)..1, Φ ↑x := by
  rw [← AddCircle.intervalIntegral_preimage (1:ℝ) (0:ℝ) Φ]
  norm_num

private lemma volume_addCircle_one : (volume : Measure (AddCircle (1:ℝ))) = AddCircle.haarAddCircle := by
  rw [AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]

private lemma inner_toLp_eq {f g : ℝ → ℂ}
    (hf : MemLp (AddCircle.liftIoc (1:ℝ) 0 f) 2 AddCircle.haarAddCircle)
    (hg : MemLp (AddCircle.liftIoc (1:ℝ) 0 g) 2 AddCircle.haarAddCircle) :
    ⟪hg.toLp, hf.toLp⟫ = ∫ θ in (0:ℝ)..1, f θ * star (g θ) := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : (∫ t : AddCircle (1:ℝ),
        ⟪(hg.toLp : AddCircle (1:ℝ) → ℂ) t, (hf.toLp : AddCircle (1:ℝ) → ℂ) t⟫
        ∂AddCircle.haarAddCircle)
      = ∫ t : AddCircle (1:ℝ),
        star ((hg.toLp : AddCircle (1:ℝ) → ℂ) t) * (hf.toLp : AddCircle (1:ℝ) → ℂ) t
        ∂AddCircle.haarAddCircle := by
    apply integral_congr_ae
    filter_upwards with t
    simp only [RCLike.inner_apply', starRingEnd_apply]
  rw [h1, AddCircle.integral_haarAddCircle]
  simp only [inv_one, one_smul]
  have h2 : (∫ t : AddCircle (1:ℝ),
        star ((hg.toLp : AddCircle (1:ℝ) → ℂ) t) * (hf.toLp : AddCircle (1:ℝ) → ℂ) t)
      = ∫ t : AddCircle (1:ℝ),
        star (AddCircle.liftIoc (1:ℝ) 0 g t) * AddCircle.liftIoc (1:ℝ) 0 f t := by
    rw [volume_addCircle_one]
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp, hf.coeFn_toLp] with t ht1 ht2
    rw [ht1, ht2]
  rw [h2, circle_integral_eq_interval]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with x hx
  rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
  have hx' : x ∈ Set.Ioc (0:ℝ) (0 + 1) := by simpa using hx
  rw [AddCircle.liftIoc_coe_apply (p := (1:ℝ)) (a := (0:ℝ)) hx',
      AddCircle.liftIoc_coe_apply (p := (1:ℝ)) (a := (0:ℝ)) hx']
  ring

theorem circle_parseval_bilinear {f g : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Set.Ioc (0:ℝ) 1)))
    (hg : MemLp g 2 (volume.restrict (Set.Ioc (0:ℝ) 1))) :
    ∑' n : ℤ, (∫ θ in (0:ℝ)..1, f θ * Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))))
        * star (∫ θ in (0:ℝ)..1, g θ * Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))))
      = ∫ θ in (0:ℝ)..1, f θ * star (g θ) := by
  have h01 : (0:ℝ) < 1 := by norm_num
  haveI : Fact (0 < (1:ℝ)) := ⟨h01⟩
  have hfF : MemLp (AddCircle.liftIoc (1:ℝ) 0 f) 2 (volume : Measure (AddCircle (1:ℝ))) := by
    have h : MemLp f 2 (volume.restrict (Set.Ioc (0:ℝ) (0+1))) := by simpa using hf
    exact h.memLp_liftIoc
  have hgG : MemLp (AddCircle.liftIoc (1:ℝ) 0 g) 2 (volume : Measure (AddCircle (1:ℝ))) := by
    have h : MemLp g 2 (volume.restrict (Set.Ioc (0:ℝ) (0+1))) := by simpa using hg
    exact h.memLp_liftIoc
  have hfH : MemLp (AddCircle.liftIoc (1:ℝ) 0 f) 2 AddCircle.haarAddCircle := hfF.haarAddCircle
  have hgH : MemLp (AddCircle.liftIoc (1:ℝ) 0 g) 2 AddCircle.haarAddCircle := hgG.haarAddCircle
  have key := HilbertBasis.tsum_inner_mul_inner (fourierBasis (T := (1:ℝ))) hgH.toLp hfH.toLp
  rw [← inner_toLp_eq hfH hgH, ← key]
  refine tsum_congr (fun n => ?_)
  have h1 : ⟪hgH.toLp, (fourierBasis (T := (1:ℝ))) n⟫
      = star (∫ θ in (0:ℝ)..1, g θ * Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))) := by
    rw [← inner_conj_symm,
      ← HilbertBasis.repr_apply_apply (fourierBasis (T := (1:ℝ))) hgH.toLp n, fourierBasis_repr]
    rw [fourierCoeff_congr_ae hgH.coeFn_toLp, coeff_eq_integral, starRingEnd_apply]
  have h2 : ⟪(fourierBasis (T := (1:ℝ))) n, hfH.toLp⟫
      = (∫ θ in (0:ℝ)..1, f θ * Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))) := by
    rw [← HilbertBasis.repr_apply_apply (fourierBasis (T := (1:ℝ))) hfH.toLp n, fourierBasis_repr]
    rw [fourierCoeff_congr_ae hfH.coeFn_toLp, coeff_eq_integral]
  rw [h1, h2, mul_comm]

private abbrev μ01 : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1)

private noncomputable def IP (f g : ℝ → ℂ) : ℝ :=
  (∫ θ in (0:ℝ)..1, f θ * star (g θ)).re

private lemma IP_self (f : ℝ → ℂ) : IP f f = ∫ θ in (0:ℝ)..1, ‖f θ‖ ^ 2 := by
  unfold IP
  have h : (∫ θ in (0:ℝ)..1, f θ * star (f θ)) = ((∫ θ in (0:ℝ)..1, ‖f θ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal (f := fun θ => ‖f θ‖ ^ 2)]
    apply intervalIntegral.integral_congr
    intro θ hθ
    show f θ * star (f θ) = ((‖f θ‖ ^ 2 : ℝ) : ℂ)
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [h, Complex.ofReal_re]

private lemma IP_symm (f g : ℝ → ℂ) : IP f g = IP g f := by
  unfold IP
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have h : star (∫ θ in Set.Ioc (0:ℝ) 1, g θ * star (f θ))
      = ∫ θ in Set.Ioc (0:ℝ) 1, f θ * star (g θ) := by
    simp only [Complex.star_def]
    rw [← integral_conj]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro θ hθ
    simp only [Complex.star_def, map_mul, Complex.conj_conj]
    ring
  rw [← h, Complex.star_def, Complex.conj_re]

private lemma IP_of_integrand_eq {f g f' g' : ℝ → ℂ}
    (h : ∀ θ, f θ * star (g θ) = f' θ * star (g' θ)) : IP f g = IP f' g' := by
  unfold IP
  congr 1
  exact intervalIntegral.integral_congr (fun θ _ => h θ)

private lemma int_mul_star {f g : ℝ → ℂ} (hf : MemLp f 2 μ01) (hg : MemLp g 2 μ01) :
    IntervalIntegrable (fun θ => f θ * star (g θ)) volume 0 1 := by
  have h : Integrable (fun θ => f θ * star (g θ)) μ01 :=
    MemLp.integrable_mul hf hg.star
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact h

private lemma IP_add_left {f1 f2 g : ℝ → ℂ} (hf1 : MemLp f1 2 μ01) (hf2 : MemLp f2 2 μ01)
    (hg : MemLp g 2 μ01) : IP (fun θ => f1 θ + f2 θ) g = IP f1 g + IP f2 g := by
  unfold IP
  have h : (∫ θ in (0:ℝ)..1, (fun θ => f1 θ + f2 θ) θ * star (g θ))
      = (∫ θ in (0:ℝ)..1, f1 θ * star (g θ)) + (∫ θ in (0:ℝ)..1, f2 θ * star (g θ)) := by
    rw [← intervalIntegral.integral_add (int_mul_star hf1 hg) (int_mul_star hf2 hg)]
    apply intervalIntegral.integral_congr
    intro θ _
    show (f1 θ + f2 θ) * star (g θ) = f1 θ * star (g θ) + f2 θ * star (g θ)
    ring
  rw [h, Complex.add_re]

private lemma IP_add_right {f g1 g2 : ℝ → ℂ} (hf : MemLp f 2 μ01) (hg1 : MemLp g1 2 μ01)
    (hg2 : MemLp g2 2 μ01) : IP f (fun θ => g1 θ + g2 θ) = IP f g1 + IP f g2 := by
  rw [IP_symm f (fun θ => g1 θ + g2 θ), IP_add_left hg1 hg2 hf, IP_symm g1 f, IP_symm g2 f]

private lemma IP_add_add {f1 f2 : ℝ → ℂ} (hf1 : MemLp f1 2 μ01) (hf2 : MemLp f2 2 μ01) :
    IP (fun θ => f1 θ + f2 θ) (fun θ => f1 θ + f2 θ)
      = IP f1 f1 + IP f1 f2 + IP f2 f1 + IP f2 f2 := by
  have h12 : MemLp (fun θ => f1 θ + f2 θ) 2 μ01 := hf1.add hf2
  rw [IP_add_left hf1 hf2 h12, IP_add_right hf1 hf1 hf2, IP_add_right hf2 hf1 hf2]
  ring

private lemma IP_sum_left {ι : Type*} (s : Finset ι) (u : ι → ℝ → ℂ) (g : ℝ → ℂ)
    (hu : ∀ i ∈ s, MemLp (u i) 2 μ01) (hg : MemLp g 2 μ01) :
    IP (fun θ => ∑ i ∈ s, u i θ) g = ∑ i ∈ s, IP (u i) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      unfold IP
      simp
  | insert a s ha ih =>
      have hua : MemLp (u a) 2 μ01 := hu a (Finset.mem_insert_self a s)
      have hus : ∀ i ∈ s, MemLp (u i) 2 μ01 := fun i hi => hu i (Finset.mem_insert_of_mem hi)
      have hsplit : IP (fun θ => ∑ i ∈ insert a s, u i θ) g
          = IP (fun θ => u a θ + (fun θ => ∑ i ∈ s, u i θ) θ) g := by
        apply IP_of_integrand_eq
        intro θ
        show (∑ i ∈ insert a s, u i θ) * star (g θ)
            = (u a θ + (fun θ => ∑ i ∈ s, u i θ) θ) * star (g θ)
        rw [Finset.sum_insert ha]
      rw [hsplit, IP_add_left hua (memLp_finsetSum s hus) hg, ih hus, Finset.sum_insert ha]

private lemma IP_sum_right {ι : Type*} (s : Finset ι) (f : ℝ → ℂ) (u : ι → ℝ → ℂ)
    (hf : MemLp f 2 μ01) (hu : ∀ i ∈ s, MemLp (u i) 2 μ01) :
    IP f (fun θ => ∑ i ∈ s, u i θ) = ∑ i ∈ s, IP f (u i) := by
  rw [IP_symm f (fun θ => ∑ i ∈ s, u i θ), IP_sum_left s u f hu hf]
  exact Finset.sum_congr rfl (fun i _ => IP_symm (u i) f)

private lemma IP_sum_sum {ι κ : Type*} (s : Finset ι) (t : Finset κ) (u : ι → ℝ → ℂ)
    (v : κ → ℝ → ℂ) (hu : ∀ i ∈ s, MemLp (u i) 2 μ01) (hv : ∀ j ∈ t, MemLp (v j) 2 μ01) :
    IP (fun θ => ∑ i ∈ s, u i θ) (fun θ => ∑ j ∈ t, v j θ)
      = ∑ i ∈ s, ∑ j ∈ t, IP (u i) (v j) := by
  rw [IP_sum_left s u (fun θ => ∑ j ∈ t, v j θ) hu (memLp_finsetSum t hv)]
  exact Finset.sum_congr rfl (fun i hi => IP_sum_right t (u i) v (hu i hi) hv)

private lemma IP_sum_self_of_orthogonal {ι : Type*} (s : Finset ι) (u : ι → ℝ → ℂ)
    (hu : ∀ i ∈ s, MemLp (u i) 2 μ01)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IP (u i) (u j) = 0) :
    IP (fun θ => ∑ i ∈ s, u i θ) (fun θ => ∑ i ∈ s, u i θ) = ∑ i ∈ s, IP (u i) (u i) := by
  rw [IP_sum_sum s s u u hu hu]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · intro j hj hji
    exact horth i hi j hj (Ne.symm hji)
  · intro hi'
    exact absurd hi hi'

private lemma IP_cauchy {f g : ℝ → ℂ} (hf : MemLp f 2 μ01) (hg : MemLp g 2 μ01) :
    |IP f g| ≤ Real.sqrt (IP f f) * Real.sqrt (IP g g) := by
  have h1 : |IP f g| ≤ ∫ θ in (0:ℝ)..1, ‖f θ‖ * ‖g θ‖ := by
    have ha : |IP f g| ≤ ‖∫ θ in (0:ℝ)..1, f θ * star (g θ)‖ := by
      unfold IP
      exact Complex.abs_re_le_norm _
    have hb : ‖∫ θ in (0:ℝ)..1, f θ * star (g θ)‖
        ≤ ∫ θ in (0:ℝ)..1, ‖f θ * star (g θ)‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    have hc : (∫ θ in (0:ℝ)..1, ‖f θ * star (g θ)‖) = ∫ θ in (0:ℝ)..1, ‖f θ‖ * ‖g θ‖ := by
      apply intervalIntegral.integral_congr
      intro θ _
      show ‖f θ * star (g θ)‖ = ‖f θ‖ * ‖g θ‖
      rw [norm_mul, norm_star]
    rw [hc] at hb
    exact le_trans ha hb
  have h2 : (∫ θ in (0:ℝ)..1, ‖f θ‖ * ‖g θ‖)
      ≤ Real.sqrt (IP f f) * Real.sqrt (IP g g) := by
    rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    have hforder : (2:ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
    have hf2 : MemLp f (ENNReal.ofReal (2:ℝ)) μ01 := by simpa using hf
    have hg2 : MemLp g (ENNReal.ofReal (2:ℝ)) μ01 := by simpa using hg
    have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := μ01) (p := 2) (q := 2)
      hforder hf2 hg2
    have hfp : (∫ x, ‖f x‖ ^ (2:ℝ) ∂μ01) = IP f f := by
      rw [IP_self, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      show ‖f x‖ ^ (2:ℝ) = ‖f x‖ ^ 2
      rw [Real.rpow_two]
    have hgp : (∫ x, ‖g x‖ ^ (2:ℝ) ∂μ01) = IP g g := by
      rw [IP_self, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      show ‖g x‖ ^ (2:ℝ) = ‖g x‖ ^ 2
      rw [Real.rpow_two]
    rw [hfp, hgp] at hholder
    rwa [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact le_trans h1 h2

private lemma two_mul_sqrt_mul_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt a * Real.sqrt b ≤ a + b := by
  have h1 : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := sq_nonneg _
  have h2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have h3 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  nlinarith [h1, h2, h3, Real.sqrt_nonneg a, Real.sqrt_nonneg b]

private lemma intervalIntegrable_norm_sq {f : ℝ → ℂ} (hf : MemLp f 2 μ01) :
    IntervalIntegrable (fun θ => ‖f θ‖ ^ 2) volume 0 1 := by
  have h1 : Integrable (fun θ => (f θ * star (f θ)).re) μ01 :=
    (MemLp.integrable_mul hf hf.star).re
  have h2 : (fun θ => (f θ * star (f θ)).re) = fun θ => ‖f θ‖ ^ 2 := by
    funext θ
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  rw [h2] at h1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  exact h1

private lemma norm_indicator_sq_le (S : Set ℝ) (u : ℝ → ℂ) (θ : ℝ) :
    ‖Set.indicator S u θ‖ ^ 2 ≤ ‖u θ‖ ^ 2 := by
  have h := norm_indicator_le_norm_self (s := S) u θ
  have h1 : 0 ≤ ‖Set.indicator S u θ‖ := norm_nonneg _
  have h2 : 0 ≤ ‖u θ‖ := norm_nonneg _
  nlinarith [h, h1, h2]

private lemma star_indicator (S : Set ℝ) (u : ℝ → ℂ) (θ : ℝ) :
    star (Set.indicator S u θ) = Set.indicator S (fun θ => star (u θ)) θ := by
  by_cases h : θ ∈ S
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, star_zero]

private lemma star_indicator_sum {ι : Type*} (s : Finset ι) (S : ι → Set ℝ) (u : ι → ℝ → ℂ)
    (θ : ℝ) :
    star (∑ i ∈ s, Set.indicator (S i) (u i) θ)
      = ∑ i ∈ s, Set.indicator (S i) (fun θ => star (u i θ)) θ := by
  rw [star_sum]
  exact Finset.sum_congr rfl (fun i _ => star_indicator (S i) (u i) θ)

private lemma collapse_pointwise {n : ℕ} (R : ℕ → Set ℝ) (G : ℕ → ℝ → ℂ)
    (hnest : ∀ i j, i < n → j < n → R (n+j) ⊆ R i) (θ : ℝ) :
    (∑ i ∈ Finset.range n, Set.indicator (R i) (G i) θ)
      * star (∑ j ∈ Finset.range n, Set.indicator (R (n+j)) (G (n+j)) θ)
    = (∑ i ∈ Finset.range n, G i θ)
      * star (∑ j ∈ Finset.range n, Set.indicator (R (n+j)) (G (n+j)) θ) := by
  rw [star_indicator_sum, Finset.sum_mul_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hi' : i < n := Finset.mem_range.mp hi
  have hj' : j < n := Finset.mem_range.mp hj
  by_cases h : θ ∈ R (n+j)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hnest i j hi' hj' h)]
  · rw [Set.indicator_of_notMem h]
    ring

private theorem circle_nested_bound_dyadic :
    ∀ (s : ℕ) (R : ℕ → Set ℝ) (G : ℕ → ℝ → ℂ),
    (∀ i, i < 2^s → MeasurableSet (R i)) →
    (∀ i j, i < 2^s → j < 2^s → i ≤ j → R j ⊆ R i) →
    (∀ i, i < 2^s → MemLp (G i) 2 μ01) →
    (∀ i j, i < 2^s → j < 2^s → i ≠ j → IP (G i) (G j) = 0) →
    IP (fun θ => ∑ i ∈ Finset.range (2^s), Set.indicator (R i) (G i) θ)
       (fun θ => ∑ i ∈ Finset.range (2^s), Set.indicator (R i) (G i) θ)
      ≤ (2*(s:ℝ)+3)^2 * ∑ i ∈ Finset.range (2^s), IP (G i) (G i) := by
  intro s
  induction s with
  | zero =>
      intro R G hmeas hnest hG horth
      simp only [pow_zero, Finset.range_one, Finset.sum_singleton]
      rw [IP_self, IP_self]
      have hmono : (∫ θ in (0:ℝ)..1, ‖Set.indicator (R 0) (G 0) θ‖ ^ 2)
          ≤ ∫ θ in (0:ℝ)..1, ‖G 0 θ‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ ?_
        · exact intervalIntegrable_norm_sq (MemLp.indicator (hmeas 0 (by norm_num)) (hG 0 (by norm_num)))
        · exact intervalIntegrable_norm_sq (hG 0 (by norm_num))
        · intro θ hθ
          exact norm_indicator_sq_le (R 0) (G 0) θ
      have hnn : 0 ≤ ∫ θ in (0:ℝ)..1, ‖G 0 θ‖ ^ 2 :=
        intervalIntegral.integral_nonneg (by norm_num) (fun θ _ => by positivity)
      have hC : (1:ℝ) ≤ (2*((0:ℕ):ℝ)+3)^2 := by norm_num
      calc (∫ θ in (0:ℝ)..1, ‖Set.indicator (R 0) (G 0) θ‖ ^ 2)
          ≤ ∫ θ in (0:ℝ)..1, ‖G 0 θ‖ ^ 2 := hmono
        _ ≤ (2*((0:ℕ):ℝ)+3)^2 * ∫ θ in (0:ℝ)..1, ‖G 0 θ‖ ^ 2 := by
            nlinarith [hnn, hC]
  | succ s ih =>
      intro R G hmeas hnest hG horth
      have hpow : 2^(s+1) = 2^s + 2^s := by rw [pow_succ, Nat.mul_two]
      rw [hpow] at hmeas hnest hG horth ⊢
      set A : ℝ → ℂ := fun θ => ∑ i ∈ Finset.range (2^s), Set.indicator (R i) (G i) θ with hA
      set B : ℝ → ℂ := fun θ => ∑ j ∈ Finset.range (2^s), Set.indicator (R (2^s+j)) (G (2^s+j)) θ with hB
      set σA : ℝ := ∑ i ∈ Finset.range (2^s), IP (G i) (G i) with hσA
      set σB : ℝ := ∑ j ∈ Finset.range (2^s), IP (G (2^s+j)) (G (2^s+j)) with hσB
      have hA_mem : MemLp A 2 μ01 := by
        rw [hA]
        refine memLp_finsetSum _ (fun i hi => ?_)
        have hi' : i < 2^s := Finset.mem_range.mp hi
        exact MemLp.indicator (hmeas i (by omega)) (hG i (by omega))
      have hB_mem : MemLp B 2 μ01 := by
        rw [hB]
        refine memLp_finsetSum _ (fun j hj => ?_)
        have hj' : j < 2^s := Finset.mem_range.mp hj
        exact MemLp.indicator (hmeas (2^s+j) (by omega)) (hG (2^s+j) (by omega))
      have hmain : (fun θ => ∑ i ∈ Finset.range (2^s+2^s), Set.indicator (R i) (G i) θ)
          = fun θ => A θ + B θ := by
        funext θ
        rw [hA, hB, Finset.sum_range_add]
      have hsum : (∑ i ∈ Finset.range (2^s+2^s), IP (G i) (G i)) = σA + σB := by
        rw [hσA, hσB, Finset.sum_range_add]
      have hAA : IP A A ≤ (2*(s:ℝ)+3)^2 * σA := by
        rw [hA, hσA]
        exact ih R G (fun i hi => hmeas i (by omega))
          (fun i j hi hj hij => hnest i j (by omega) (by omega) hij)
          (fun i hi => hG i (by omega)) (fun i j hi hj hij => horth i j (by omega) (by omega) hij)
      have hBB : IP B B ≤ (2*(s:ℝ)+3)^2 * σB := by
        rw [hB, hσB]
        exact ih (fun j => R (2^s+j)) (fun j => G (2^s+j))
          (fun j hj => hmeas (2^s+j) (by omega))
          (fun i j hi hj hij => hnest (2^s+i) (2^s+j) (by omega) (by omega) (by omega))
          (fun j hj => hG (2^s+j) (by omega))
          (fun i j hi hj hij => horth (2^s+i) (2^s+j) (by omega) (by omega) (by omega))
      have hG_mem : MemLp (fun θ => ∑ i ∈ Finset.range (2^s), G i θ) 2 μ01 :=
        memLp_finsetSum _ (fun i hi => hG i (by have := Finset.mem_range.mp hi; omega))
      have hGG : IP (fun θ => ∑ i ∈ Finset.range (2^s), G i θ)
          (fun θ => ∑ i ∈ Finset.range (2^s), G i θ) = σA := by
        rw [hσA]
        exact IP_sum_self_of_orthogonal _ G
          (fun i hi => hG i (by have := Finset.mem_range.mp hi; omega))
          (fun i hi j hj hij => horth i j (by have := Finset.mem_range.mp hi; omega)
            (by have := Finset.mem_range.mp hj; omega) hij)
      have hcoll : IP A B = IP (fun θ => ∑ i ∈ Finset.range (2^s), G i θ) B := by
        apply IP_of_integrand_eq
        intro θ
        rw [hA, hB]
        exact collapse_pointwise (n := 2^s) R G
          (fun i j hi hj => hnest i (2^s+j) (by omega) (by omega) (by omega)) θ
      have hnnA : 0 ≤ σA := by
        rw [hσA]
        exact Finset.sum_nonneg (fun i _ => by
          rw [IP_self]
          exact intervalIntegral.integral_nonneg (by norm_num) (fun θ _ => by positivity))
      have hnnB : 0 ≤ σB := by
        rw [hσB]
        exact Finset.sum_nonneg (fun j _ => by
          rw [IP_self]
          exact intervalIntegral.integral_nonneg (by norm_num) (fun θ _ => by positivity))
      have hCs : (0:ℝ) ≤ 2*(s:ℝ)+3 := by positivity
      have hAB : IP A B ≤ (2*(s:ℝ)+3) * Real.sqrt (σA * σB) := by
        rw [hcoll]
        have hcs := IP_cauchy hG_mem hB_mem
        have h2 : Real.sqrt (IP (fun θ => ∑ i ∈ Finset.range (2^s), G i θ)
              (fun θ => ∑ i ∈ Finset.range (2^s), G i θ)) = Real.sqrt σA := by rw [hGG]
        have h3 : Real.sqrt (IP B B) ≤ Real.sqrt ((2*(s:ℝ)+3)^2 * σB) :=
          Real.sqrt_le_sqrt hBB
        have h4 : Real.sqrt ((2*(s:ℝ)+3)^2 * σB) = (2*(s:ℝ)+3) * Real.sqrt σB := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hCs]
        have h5 : Real.sqrt σA * ((2*(s:ℝ)+3) * Real.sqrt σB)
            = (2*(s:ℝ)+3) * Real.sqrt (σA * σB) := by
          rw [Real.sqrt_mul hnnA σB]; ring
        have h6 : IP (fun θ => ∑ i ∈ Finset.range (2^s), G i θ) B
            ≤ Real.sqrt σA * ((2*(s:ℝ)+3) * Real.sqrt σB) := by
          calc IP (fun θ => ∑ i ∈ Finset.range (2^s), G i θ) B
              ≤ |IP (fun θ => ∑ i ∈ Finset.range (2^s), G i θ) B| := le_abs_self _
            _ ≤ Real.sqrt (IP (fun θ => ∑ i ∈ Finset.range (2^s), G i θ)
                  (fun θ => ∑ i ∈ Finset.range (2^s), G i θ)) * Real.sqrt (IP B B) := hcs
            _ ≤ Real.sqrt σA * ((2*(s:ℝ)+3) * Real.sqrt σB) := by
                rw [h2]
                exact mul_le_mul_of_nonneg_left (le_trans h3 (le_of_eq h4)) (Real.sqrt_nonneg _)
        rw [← h5]
        exact h6
      have hfinal : IP A A + IP A B + IP A B + IP B B
          ≤ (2*((s:ℝ)+1)+3)^2 * (σA + σB) := by
        have harm : (2*(s:ℝ)+3)^2 + (2*(s:ℝ)+3) ≤ (2*((s:ℝ)+1)+3)^2 := by
          have : (0:ℝ) ≤ s := by positivity
          nlinarith
        have h1 : IP A A + IP A B + IP A B + IP B B
            ≤ (2*(s:ℝ)+3)^2 * σA + (2*(s:ℝ)+3)^2 * σB
              + 2 * ((2*(s:ℝ)+3) * Real.sqrt (σA * σB)) := by
          linarith [hAA, hBB, hAB]
        have h2 : (2*(s:ℝ)+3)^2 * σA + (2*(s:ℝ)+3)^2 * σB
              + 2 * ((2*(s:ℝ)+3) * Real.sqrt (σA * σB))
            = (2*(s:ℝ)+3)^2 * (σA + σB)
              + (2*(s:ℝ)+3) * (2 * Real.sqrt (σA*σB)) := by
          ring
        have h3 : (2*(s:ℝ)+3) * (2 * Real.sqrt (σA * σB)) ≤ (2*(s:ℝ)+3) * (σA + σB) := by
          apply mul_le_mul_of_nonneg_left _ hCs
          rw [Real.sqrt_mul hnnA σB]
          linarith [two_mul_sqrt_mul_sqrt_le hnnA hnnB]
        calc IP A A + IP A B + IP A B + IP B B
            ≤ (2*(s:ℝ)+3)^2 * σA + (2*(s:ℝ)+3)^2 * σB
              + 2 * ((2*(s:ℝ)+3) * Real.sqrt (σA * σB)) := h1
          _ = (2*(s:ℝ)+3)^2 * (σA + σB) + (2*(s:ℝ)+3) * (2 * Real.sqrt (σA*σB)) := h2
          _ ≤ (2*(s:ℝ)+3)^2 * (σA + σB) + (2*(s:ℝ)+3) * (σA + σB) := by linarith [h3]
          _ = ((2*(s:ℝ)+3)^2 + (2*(s:ℝ)+3)) * (σA + σB) := by ring
          _ ≤ (2*((s:ℝ)+1)+3)^2 * (σA + σB) := by
              apply mul_le_mul_of_nonneg_right harm (by linarith)
      have hcast : (2*((s:ℝ)+1)+3) = (2*(↑(s+1):ℝ)+3) := by push_cast; ring
      rw [hcast] at hfinal
      rw [hmain, IP_add_add hA_mem hB_mem, hsum, IP_symm B A]
      exact hfinal


/-! ### The projection kernels and the trigonometric transform -/

/-- The `p`-th Fourier coefficient of the indicator of `R`: the kernel of the projection
operator associated with `R`. -/
def projKern (R : Set ℝ) (p : ℤ) : ℂ :=
  ∫ θ in (0:ℝ)..1,
    Set.indicator R (fun θ => Complex.exp (-(2*Real.pi*Complex.I*((p:ℤ):ℂ)*(θ:ℂ)))) θ

/-- The projection operator on `ℓ²(ℤ)` associated with a set `R`: convolution with the Fourier
coefficients of `1_R`. -/
def projOp (R : Set ℝ) (t : Finset ℤ) (g : ℤ → ℂ) (m : ℤ) : ℂ :=
  ∑ n ∈ t, g n * projKern R (m - n)

/-- The trigonometric polynomial (Fourier transform) of a finitely supported sequence. -/
def trig (t : Finset ℤ) (g : ℤ → ℂ) (θ : ℝ) : ℂ :=
  ∑ n ∈ t, g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))

lemma char_integral (k : ℤ) :
    (∫ θ in (0:ℝ)..1, Complex.exp (2*Real.pi*Complex.I*(k:ℂ)*(θ:ℂ)))
      = if k = 0 then 1 else 0 := by
  by_cases hk : k = 0
  · subst hk
    rw [if_pos rfl]
    simp
  · rw [if_neg hk]
    have hc : (2 * Real.pi * Complex.I * (k : ℂ)) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) ?_
      · norm_num
      · exact_mod_cast Real.pi_ne_zero
      · exact Complex.I_ne_zero
      · exact_mod_cast hk
    have h1 : Complex.exp ((2 * Real.pi * Complex.I * (k:ℂ)) * (1:ℝ)) = 1 := by
      have : (2 * Real.pi * Complex.I * (k:ℂ)) * (1:ℝ) = (k:ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; ring
      rw [this, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
    have h0 : Complex.exp ((2 * Real.pi * Complex.I * (k:ℂ)) * (0:ℝ)) = 1 := by simp
    rw [show (fun θ : ℝ => Complex.exp (2*Real.pi*Complex.I*(k:ℂ)*(θ:ℂ)))
        = (fun θ : ℝ => Complex.exp ((2 * Real.pi * Complex.I * (k:ℂ)) * (θ:ℂ))) by
      funext θ; ring]
    rw [integral_exp_mul_complex hc, h1, h0, sub_self, zero_div]

lemma char_mul (m n : ℤ) (θ : ℝ) :
    Complex.exp (2*Real.pi*Complex.I*((m:ℤ):ℂ)*(θ:ℂ))
      * Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))
    = Complex.exp (2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ)) := by
  rw [← Complex.exp_add]
  push_cast
  ring

lemma char_integral_sub (m n : ℤ) :
    (∫ θ in (0:ℝ)..1, Complex.exp (2*Real.pi*Complex.I*((m:ℤ):ℂ)*(θ:ℂ))
        * Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))))
      = if m = n then 1 else 0 := by
  rw [show (fun θ : ℝ => Complex.exp (2*Real.pi*Complex.I*((m:ℤ):ℂ)*(θ:ℂ))
        * Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))))
      = (fun θ : ℝ => Complex.exp (2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ))) by
    funext θ; exact char_mul m n θ]
  rw [char_integral (m - n)]
  by_cases h : m = n
  · subst h; simp
  · rw [if_neg h, if_neg (sub_ne_zero.mpr h)]

lemma trig_coeff (t : Finset ℤ) (g : ℤ → ℂ) (hg : ∀ n, n ∉ t → g n = 0) (n : ℤ) :
    (∫ θ in (0:ℝ)..1, trig t g θ * Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))))
      = if n ∈ t then g n else 0 := by
  have hpt : ∀ θ : ℝ, trig t g θ * Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))
      = ∑ m ∈ t, g m * (Complex.exp (2*Real.pi*Complex.I*((m:ℤ):ℂ)*(θ:ℂ))
          * Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))) := by
    intro θ
    rw [trig, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun m _ => by ring)
  rw [intervalIntegral.integral_congr (fun θ _ => hpt θ)]
  rw [intervalIntegral.integral_finsetSum]
  · have hterm : ∀ m ∈ t, (∫ θ in (0:ℝ)..1, g m * (Complex.exp (2*Real.pi*Complex.I*((m:ℤ):ℂ)*(θ:ℂ))
          * Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ)))))
        = g m * (if m = n then 1 else 0) := by
      intro m hm
      rw [intervalIntegral.integral_const_mul]
      congr 1
      exact char_integral_sub m n
    rw [Finset.sum_congr rfl hterm]
    rw [show (∑ m ∈ t, g m * (if m = n then 1 else 0)) = ∑ m ∈ t, (if m = n then g m else 0) by
      apply Finset.sum_congr rfl
      intro m hm
      by_cases h : m = n <;> simp [h]]
    rw [Finset.sum_ite_eq' t n (fun m => g m)]
  · intro m hm
    exact ((continuous_const.mul ((Complex.continuous_exp.comp (by fun_prop)).mul
      (Complex.continuous_exp.comp (by fun_prop)))).intervalIntegrable 0 1)

lemma projOp_eq_integral (R : Set ℝ) (hR : MeasurableSet R) (t : Finset ℤ) (g : ℤ → ℂ) (m : ℤ) :
    projOp R t g m
      = ∫ θ in (0:ℝ)..1,
          Set.indicator R (fun θ => trig t g θ * Complex.exp (-(2*Real.pi*Complex.I*((m:ℤ):ℂ)*(θ:ℂ)))) θ := by
  rw [projOp]
  exact circle_multiplier_identity R hR g t m

lemma projOp_eq_coeff (R : Set ℝ) (hR : MeasurableSet R) (t : Finset ℤ) (g : ℤ → ℂ) (m : ℤ) :
    projOp R t g m
      = ∫ θ in (0:ℝ)..1,
          Set.indicator R (fun θ => trig t g θ) θ
            * Complex.exp (-(2*Real.pi*Complex.I*((m:ℤ):ℂ)*(θ:ℂ))) := by
  rw [projOp_eq_integral R hR t g m]
  apply intervalIntegral.integral_congr
  intro θ _
  show Set.indicator R (fun θ => trig t g θ * Complex.exp (-(2*Real.pi*Complex.I*((m:ℤ):ℂ)*(θ:ℂ)))) θ
      = Set.indicator R (fun θ => trig t g θ) θ * Complex.exp (-(2*Real.pi*Complex.I*((m:ℤ):ℂ)*(θ:ℂ)))
  by_cases h : θ ∈ R
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]

lemma interval_char (n : ℤ) :
    (∫ θ in (0:ℝ)..1, Complex.exp (-(2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))))
      = ∫ θ in (0:ℝ)..1, Complex.exp (2*Real.pi*Complex.I*(((-n):ℤ):ℂ)*(θ:ℂ)) := by
  apply intervalIntegral.integral_congr
  intro θ _
  congr 1
  push_cast
  ring

lemma memLp_trig (t : Finset ℤ) (g : ℤ → ℂ) : MemLp (trig t g) 2 μ01 := by
  have hcont : Continuous (trig t g) := by
    apply continuous_finset_sum
    intro n hn
    exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
  refine MemLp.of_bound hcont.aestronglyMeasurable (∑ n ∈ t, ‖g n‖) ?_
  filter_upwards with θ
  calc ‖trig t g θ‖ ≤ ∑ n ∈ t, ‖g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))‖ := by
        rw [trig]; exact norm_sum_le _ _
    _ = ∑ n ∈ t, ‖g n‖ := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [norm_mul, Complex.norm_exp]
        simp

lemma memLp_indicator_trig (R : Set ℝ) (hR : MeasurableSet R) (t : Finset ℤ) (g : ℤ → ℂ) :
    MemLp (fun θ => Set.indicator R (fun θ => trig t g θ) θ) 2 μ01 := by
  have hcont : Continuous (trig t g) := by
    apply continuous_finset_sum
    intro n hn
    exact continuous_const.mul (Complex.continuous_exp.comp (by fun_prop))
  have hmeas : AEStronglyMeasurable (fun θ => Set.indicator R (fun θ => trig t g θ) θ) μ01 :=
    ((hcont.measurable.indicator hR).aestronglyMeasurable)
  refine MemLp.of_bound hmeas (∑ n ∈ t, ‖g n‖) ?_
  filter_upwards with θ
  refine le_trans (norm_indicator_le_norm_self (s := R) (fun θ => trig t g θ) θ) ?_
  calc ‖trig t g θ‖ ≤ ∑ n ∈ t, ‖g n * Complex.exp (2*Real.pi*Complex.I*((n:ℤ):ℂ)*(θ:ℂ))‖ := by
        rw [trig]; exact norm_sum_le _ _
    _ = ∑ n ∈ t, ‖g n‖ := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [norm_mul, Complex.norm_exp]
        simp

lemma IP_indicator_trig (R : Set ℝ) (hR : MeasurableSet R) (t : Finset ℤ) (g : ℤ → ℂ)
    (hg : ∀ n, n ∉ t → g n = 0) (u : Finset ℤ) (g' : ℤ → ℂ)
    (hg' : ∀ n, n ∉ u → g' n = 0) :
    IP (fun θ => Set.indicator R (fun θ => trig t g θ) θ) (trig u g')
      = (∑' m : ℤ, projOp R t g m * star (g' m)).re := by
  unfold IP
  rw [← circle_parseval_bilinear (memLp_indicator_trig R hR t g) (memLp_trig u g')]
  apply congrArg Complex.re
  apply tsum_congr
  intro n
  congr 1
  · exact (projOp_eq_coeff R hR t g n).symm
  · rw [trig_coeff u g' hg' n]
    by_cases h : n ∈ u
    · rw [if_pos h]
    · rw [if_neg h, hg' n h]

lemma IP_trig_trig (t : Finset ℤ) (g : ℤ → ℂ) (hg : ∀ n, n ∉ t → g n = 0)
    (u : Finset ℤ) (g' : ℤ → ℂ) (hg' : ∀ n, n ∉ u → g' n = 0) :
    IP (trig t g) (trig u g') = (∑' m : ℤ, g m * star (g' m)).re := by
  unfold IP
  rw [← circle_parseval_bilinear (memLp_trig t g) (memLp_trig u g')]
  apply congrArg Complex.re
  apply tsum_congr
  intro n
  congr 1
  · rw [trig_coeff t g hg n]
    by_cases h : n ∈ t
    · rw [if_pos h]
    · rw [if_neg h, hg n h]
  · rw [trig_coeff u g' hg' n]
    by_cases h : n ∈ u
    · rw [if_pos h]
    · rw [if_neg h, hg' n h]

lemma Complex.re_finsetSum {ι : Type*} (s : Finset ι) (z : ι → ℂ) :
    (∑ i ∈ s, z i).re = ∑ i ∈ s, (z i).re := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Complex.add_re, ih]

lemma sum_re_eq (s : Finset ℤ) (f : ℤ → ℂ) : (∑ x ∈ s, f x).re = ∑ x ∈ s, (f x).re :=
  Complex.re_finsetSum s f

lemma IP_sum_indicator_bound (M : ℕ) (hM : 1 ≤ M) (R : Fin M → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (R i)) (hnest : ∀ i j : Fin M, i ≤ j → R j ⊆ R i)
    (V : Fin M → ℝ → ℂ) (hV : ∀ i, MemLp (V i) 2 μ01)
    (hVorth : ∀ i j : Fin M, i ≠ j → IP (V i) (V j) = 0) :
    IP (fun θ => ∑ i : Fin M, Set.indicator (R i) (V i) θ)
       (fun θ => ∑ i : Fin M, Set.indicator (R i) (V i) θ)
      ≤ (2*((Nat.log2 M : ℝ) + 1) + 3)^2 * ∑ i : Fin M, IP (V i) (V i) := by
  classical
  set ℓ : ℕ := Nat.log2 M + 1 with hℓ
  have hMle : M ≤ 2^ℓ := by
    rw [hℓ]
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) M
    rw [← Nat.log2_eq_log_two, Nat.succ_eq_add_one] at h
    exact le_of_lt h
  set R' : ℕ → Set ℝ := fun i => if hi : i < M then R ⟨i, hi⟩ else R ⟨M-1, by omega⟩ with hR'
  set V' : ℕ → ℝ → ℂ := fun i => if hi : i < M then V ⟨i, hi⟩ else 0 with hV'
  have hR'meas : ∀ i, i < 2^ℓ → MeasurableSet (R' i) := by
    intro i hi
    simp only [hR']
    split_ifs with hiM
    · exact hmeas _
    · exact hmeas _
  have hR'nest : ∀ i j, i < 2^ℓ → j < 2^ℓ → i ≤ j → R' j ⊆ R' i := by
    intro i j hi hj hij
    simp only [hR']
    by_cases hiM : i < M
    · by_cases hjM : j < M
      · rw [dif_pos hiM, dif_pos hjM]
        exact hnest ⟨i, hiM⟩ ⟨j, hjM⟩ hij
      · rw [dif_pos hiM, dif_neg hjM]
        exact hnest ⟨i, hiM⟩ ⟨M-1, by omega⟩ (by simp; omega)
    · have hjM : ¬ j < M := by omega
      rw [dif_neg hiM, dif_neg hjM]
  have hV'mem : ∀ i, i < 2^ℓ → MemLp (V' i) 2 μ01 := by
    intro i hi
    simp only [hV']
    split_ifs with hiM
    · exact hV _
    · exact MemLp.of_bound aestronglyMeasurable_const 0
        (Filter.Eventually.of_forall (fun x => by simp))
  have hV'orth : ∀ i j, i < 2^ℓ → j < 2^ℓ → i ≠ j → IP (V' i) (V' j) = 0 := by
    intro i j hi hj hij
    simp only [hV']
    by_cases hiM : i < M
    · by_cases hjM : j < M
      · rw [dif_pos hiM, dif_pos hjM]
        exact hVorth ⟨i, hiM⟩ ⟨j, hjM⟩ (fun h => hij (by simpa using congrArg Fin.val h))
      · rw [dif_pos hiM, dif_neg hjM]
        unfold IP; simp
    · rw [dif_neg hiM]
      unfold IP; simp
  have key := circle_nested_bound_dyadic ℓ R' V' hR'meas hR'nest hV'mem hV'orth
  have hsame1 : (fun θ => ∑ i ∈ Finset.range (2^ℓ), Set.indicator (R' i) (V' i) θ)
      = fun θ => ∑ i : Fin M, Set.indicator (R i) (V i) θ := by
    funext θ
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr hMle)
      (fun x hx2 hxM => by
        have hxM' : ¬ x < M := by simp only [Finset.mem_range] at hxM; omega
        simp only [hV', dif_neg hxM', Set.indicator_zero', Pi.zero_apply])]
    rw [Finset.sum_range]
    exact Finset.sum_congr rfl (fun i _ => by simp only [hR', hV', dif_pos i.isLt])
  have hsame2 : (∑ i ∈ Finset.range (2^ℓ), IP (V' i) (V' i))
      = ∑ i : Fin M, IP (V i) (V i) := by
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr hMle)
      (fun x hx2 hxM => by
        have hxM' : ¬ x < M := by simp only [Finset.mem_range] at hxM; omega
        simp only [hV', dif_neg hxM']
        unfold IP; simp)]
    rw [Finset.sum_range]
    exact Finset.sum_congr rfl (fun i _ => by simp only [hV', dif_pos i.isLt])
  rw [hsame1, hsame2, hℓ, Nat.cast_add, Nat.cast_one] at key
  exact key

lemma norm_ofReal (r : ℝ) : ‖(r : ℂ)‖ = |r| := by simp

lemma star_indicator_one (S : Set ℝ) (f : ℝ → ℂ) (θ : ℝ) :
    star (Set.indicator S f θ)
      = Set.indicator S (fun _ => (1:ℂ)) θ * star (f θ) := by
  by_cases h : θ ∈ S
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, one_mul]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul, star_zero]

lemma indicator_mul_eq' (S : Set ℝ) (f : ℝ → ℂ) (w : ℂ) (θ : ℝ) :
    Set.indicator S f θ * w = Set.indicator S (fun θ => f θ * w) θ := by
  by_cases h : θ ∈ S
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]

theorem linearization_bound (M : ℕ) (hM : 1 ≤ M) (R : Fin M → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (R i)) (hnest : ∀ i j : Fin M, i ≤ j → R j ⊆ R i)
    (f : ℤ → ℂ) (t : Finset ℤ) (hf : ∀ n, n ∉ t → f n = 0)
    (h : ℤ → ℝ) (hh : ∀ x, 0 ≤ h x) (u : Finset ℤ) (hu : ∀ x, x ∉ u → h x = 0) :
    ∑ x ∈ u, h x * (⨆ i : Fin M, ‖projOp (R i) t f x‖)
      ≤ (2*((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∑ n ∈ t, ‖f n‖^2)
          * Real.sqrt (∑ x ∈ u, h x ^ 2) := by
  classical
  haveI : NeZero M := ⟨by omega⟩
  have hex : ∀ x : ℤ, ∃ i ∈ (Finset.univ : Finset (Fin M)),
      ∀ i' ∈ (Finset.univ : Finset (Fin M)),
        ‖projOp (R i') t f x‖ ≤ ‖projOp (R i) t f x‖ :=
    fun x => Finset.exists_max_image _ _ ⟨⟨0, hM⟩, Finset.mem_univ _⟩
  set i0 : ℤ → Fin M := fun x => (hex x).choose with hi0def
  have hi0 : ∀ x i, ‖projOp (R i) t f x‖ ≤ ‖projOp (R (i0 x)) t f x‖ :=
    fun x i => (hex x).choose_spec.2 i (Finset.mem_univ i)
  have hsup : ∀ x, (⨆ i : Fin M, ‖projOp (R i) t f x‖) = ‖projOp (R (i0 x)) t f x‖ := by
    intro x
    refine le_antisymm (ciSup_le (fun i => hi0 x i)) ?_
    exact le_ciSup (Set.finite_range (fun i : Fin M => ‖projOp (R i) t f x‖)).bddAbove (i0 x)
  set sg : ℤ → ℂ := fun x => if projOp (R (i0 x)) t f x = 0 then 1
      else projOp (R (i0 x)) t f x / ((‖projOp (R (i0 x)) t f x‖ : ℝ) : ℂ) with hsgdef
  have sg_apply : ∀ x, sg x = (if projOp (R (i0 x)) t f x = 0 then 1
      else projOp (R (i0 x)) t f x / ((‖projOp (R (i0 x)) t f x‖ : ℝ) : ℂ)) :=
    fun x => rfl
  have hsg : ∀ x, projOp (R (i0 x)) t f x * star (sg x)
      = ((‖projOp (R (i0 x)) t f x‖ : ℝ) : ℂ) := by
    intro x
    by_cases hz : projOp (R (i0 x)) t f x = 0
    · rw [sg_apply x, if_pos hz, hz, star_one, mul_one, norm_zero]
      simp
    · rw [sg_apply x, if_neg hz]
      have hz0 : ‖projOp (R (i0 x)) t f x‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      rw [Complex.star_def, map_div₀, Complex.conj_ofReal, ← mul_div_assoc,
        Complex.mul_conj, Complex.normSq_eq_norm_sq, ← Complex.ofReal_div]
      congr 1
      field_simp
  set G : Fin M → ℤ → ℂ := fun i x => (h x : ℂ) * sg x * (if i0 x = i then 1 else 0) with hGdef
  have G_apply : ∀ i x, G i x = (h x : ℂ) * sg x * (if i0 x = i then 1 else 0) :=
    fun i x => rfl
  have hGsupp : ∀ i x, x ∉ u → G i x = 0 := by
    intro i x hx
    rw [G_apply i x]
    simp only [hu x hx, Complex.ofReal_zero, zero_mul, zero_mul]
  have hsg_norm : ∀ x, ‖sg x‖ = 1 := by
    intro x
    by_cases hz : projOp (R (i0 x)) t f x = 0
    · rw [sg_apply x, if_pos hz]; simp
    · rw [sg_apply x, if_neg hz, norm_div, norm_ofReal, abs_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr hz)]
  have hGorth : ∀ i j : Fin M, i ≠ j → IP (trig u (G i)) (trig u (G j)) = 0 := by
    intro i j hij
    rw [IP_trig_trig u (G i) (hGsupp i) u (G j) (hGsupp j)]
    have hzero : (∑' x : ℤ, G i x * star (G j x)) = 0 := by
      rw [tsum_eq_sum (s := u) (fun x hx => by rw [hGsupp i x hx, zero_mul])]
      refine Finset.sum_eq_zero (fun x hx => ?_)
      by_cases hx' : i0 x = i
      · have hGj : G j x = 0 := by
          rw [G_apply j x, if_neg (fun hh' => hij (by rw [← hx', hh'])), mul_zero]
        rw [hGj, star_zero, mul_zero]
      · have hGi : G i x = 0 := by
          rw [G_apply i x, if_neg hx', mul_zero]
        rw [hGi, zero_mul]
    rw [hzero, Complex.zero_re]
  have hpt : ∀ x : ℤ, h x * (⨆ i : Fin M, ‖projOp (R i) t f x‖)
      = ∑ i : Fin M, (projOp (R i) t f x * star (G i x)).re := by
    intro x
    rw [← Complex.re_finsetSum, hsup x]
    have hsingle : (∑ i : Fin M, projOp (R i) t f x * star (G i x))
        = ((h x * ‖projOp (R (i0 x)) t f x‖ : ℝ) : ℂ) := by
      rw [Finset.sum_eq_single (i0 x)
        (fun i _ hi0 => by
          have hGi : G i x = 0 := by
            rw [G_apply i x, if_neg (fun hh' => hi0 hh'.symm), mul_zero]
          rw [hGi, star_zero, mul_zero])
        (fun hmem => absurd (Finset.mem_univ (i0 x)) hmem)]
      show projOp (R (i0 x)) t f x
          * star ((h x : ℂ) * sg x * (if i0 x = i0 x then 1 else 0))
          = ((h x * ‖projOp (R (i0 x)) t f x‖ : ℝ) : ℂ)
      rw [if_pos rfl, mul_one]
      have key : projOp (R (i0 x)) t f x * star ((h x : ℂ) * sg x)
          = (h x : ℂ) * (projOp (R (i0 x)) t f x * star (sg x)) := by
        rw [star_mul, Complex.star_def, Complex.conj_ofReal]
        ring
      rw [key, hsg x]
      push_cast
      ring
    rw [hsingle, Complex.ofReal_re]
  have hstep3 : ∀ i : Fin M, (∑ x ∈ u, projOp (R i) t f x * star (G i x)).re
      = IP (fun θ => Set.indicator (R i) (fun θ => trig t f θ) θ) (trig u (G i)) := by
    intro i
    rw [IP_indicator_trig (R i) (hmeas i) t f hf u (G i) (hGsupp i)]
    exact (congrArg Complex.re (tsum_eq_sum (s := u)
      (fun x hx => by rw [hGsupp i x hx, star_zero, mul_zero]))).symm
  have hpointwise : ∀ θ : ℝ,
      (∑ i : Fin M, Set.indicator (R i) (fun θ => trig t f θ) θ * star (trig u (G i) θ))
        = trig t f θ * star (∑ i : Fin M, Set.indicator (R i) (trig u (G i)) θ) := by
    intro θ
    have hp1 : ∀ i : Fin M,
        Set.indicator (R i) (fun θ => trig t f θ) θ * star (trig u (G i) θ)
          = trig t f θ * (Set.indicator (R i) (fun _ => (1:ℂ)) θ * star (trig u (G i) θ)) := by
      intro i
      rw [show Set.indicator (R i) (fun θ => trig t f θ) θ
          = Set.indicator (R i) (fun _ => (1:ℂ)) θ * trig t f θ by
        by_cases hθ : θ ∈ R i
        · rw [Set.indicator_of_mem hθ, Set.indicator_of_mem hθ, one_mul]
        · rw [Set.indicator_of_notMem hθ, Set.indicator_of_notMem hθ, zero_mul]]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hp1 i), ← Finset.mul_sum, star_sum]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [star_indicator_one (R i) (trig u (G i)) θ]
  have hIPsum : ∑ i : Fin M, IP (fun θ => Set.indicator (R i) (fun θ => trig t f θ) θ) (trig u (G i))
      = IP (trig t f) (fun θ => ∑ i : Fin M, Set.indicator (R i) (trig u (G i)) θ) := by
    have hmemU : ∀ i : Fin M, MemLp (fun θ => Set.indicator (R i) (fun θ => trig t f θ) θ) 2 μ01 :=
      fun i => memLp_indicator_trig (R i) (hmeas i) t f
    have hmemV : ∀ i : Fin M, MemLp (trig u (G i)) 2 μ01 := fun i => memLp_trig u (G i)
    have h1 : (∑ i : Fin M, IP (fun θ => Set.indicator (R i) (fun θ => trig t f θ) θ) (trig u (G i)))
        = (∑ i : Fin M, ∫ θ in (0:ℝ)..1,
            Set.indicator (R i) (fun θ => trig t f θ) θ * star (trig u (G i) θ)).re := by
      rw [Complex.re_finsetSum]
      exact Finset.sum_congr rfl (fun i _ => rfl)
    rw [h1, ← intervalIntegral.integral_finsetSum]
    · apply congrArg Complex.re
      apply intervalIntegral.integral_congr
      intro θ _
      show (∑ i : Fin M, Set.indicator (R i) (fun θ => trig t f θ) θ * star (trig u (G i) θ))
          = trig t f θ * star (∑ i : Fin M, Set.indicator (R i) (trig u (G i)) θ)
      exact hpointwise θ
    · intro i _
      exact int_mul_star (hmemU i) (hmemV i)
  have hHmem : MemLp (fun θ => ∑ i : Fin M, Set.indicator (R i) (trig u (G i)) θ) 2 μ01 :=
    memLp_finsetSum _ (fun i _ => MemLp.indicator (hmeas i) (memLp_trig u (G i)))
  have hAA : IP (trig t f) (trig t f) = ∑ n ∈ t, ‖f n‖^2 := by
    rw [IP_trig_trig t f hf t f hf]
    rw [tsum_eq_sum (s := t) (fun n hn => by rw [hf n hn, zero_mul]), Complex.re_finsetSum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have hHH : IP (fun θ => ∑ i : Fin M, Set.indicator (R i) (trig u (G i)) θ)
      (fun θ => ∑ i : Fin M, Set.indicator (R i) (trig u (G i)) θ)
      ≤ (2*((Nat.log2 M : ℝ) + 1) + 3)^2 * ∑ i : Fin M, IP (trig u (G i)) (trig u (G i)) :=
    IP_sum_indicator_bound M hM R hmeas hnest (fun i => trig u (G i))
      (fun i => memLp_trig u (G i)) hGorth
  have hBB : ∑ i : Fin M, IP (trig u (G i)) (trig u (G i)) = ∑ x ∈ u, h x ^ 2 := by
    have h1 : ∀ i : Fin M, IP (trig u (G i)) (trig u (G i)) = ∑ x ∈ u, ‖G i x‖^2 := by
      intro i
      rw [IP_trig_trig u (G i) (hGsupp i) u (G i) (hGsupp i)]
      rw [tsum_eq_sum (s := u) (fun x hx => by rw [hGsupp i x hx, zero_mul]), Complex.re_finsetSum]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
    have h2 : ∀ x : ℤ, (∑ i : Fin M, ‖G i x‖^2) = h x ^ 2 := by
      intro x
      have h3 : ∀ i : Fin M, ‖G i x‖^2 = (if i0 x = i then h x ^ 2 else 0) := by
        intro i
        by_cases hix : i0 x = i
        · rw [if_pos hix]
          rw [G_apply i x]
          simp only [hix, if_true, mul_one]
          simp only [norm_mul, norm_ofReal, hsg_norm x, mul_one, abs_of_nonneg (hh x),
            sq]
        · rw [if_neg hix]
          have hz : G i x = 0 := by
            rw [G_apply i x]
            simp only [hix, if_false, mul_zero]
          rw [hz]
          simp
      rw [Finset.sum_congr rfl (fun i _ => h3 i), Finset.sum_ite_eq, if_pos (Finset.mem_univ (i0 x))]
    calc ∑ i : Fin M, IP (trig u (G i)) (trig u (G i))
        = ∑ i : Fin M, ∑ x ∈ u, ‖G i x‖^2 := Finset.sum_congr rfl (fun i _ => h1 i)
      _ = ∑ x ∈ u, ∑ i : Fin M, ‖G i x‖^2 := Finset.sum_comm
      _ = ∑ x ∈ u, h x ^ 2 := Finset.sum_congr rfl (fun x _ => h2 x)
  have hcs := IP_cauchy (memLp_trig t f) hHmem
  calc ∑ x ∈ u, h x * (⨆ i : Fin M, ‖projOp (R i) t f x‖)
      = ∑ i : Fin M, (∑ x ∈ u, projOp (R i) t f x * star (G i x)).re := by
        rw [Finset.sum_congr rfl (fun x hx => hpt x), Finset.sum_comm]
        exact Finset.sum_congr rfl (fun i _ => (Complex.re_finsetSum u _).symm)
    _ = ∑ i : Fin M, IP (fun θ => Set.indicator (R i) (fun θ => trig t f θ) θ) (trig u (G i)) :=
        Finset.sum_congr rfl (fun i _ => hstep3 i)
    _ = IP (trig t f) (fun θ => ∑ i : Fin M, Set.indicator (R i) (trig u (G i)) θ) := hIPsum
    _ ≤ Real.sqrt (IP (trig t f) (trig t f))
          * Real.sqrt (IP (fun θ => ∑ i : Fin M, Set.indicator (R i) (trig u (G i)) θ)
              (fun θ => ∑ i : Fin M, Set.indicator (R i) (trig u (G i)) θ)) :=
        le_trans (le_abs_self _) hcs
    _ ≤ Real.sqrt (∑ n ∈ t, ‖f n‖^2)
          * Real.sqrt ((2*((Nat.log2 M : ℝ) + 1) + 3)^2 * ∑ x ∈ u, h x ^ 2) := by
        rw [hAA]
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        rw [← hBB]
        exact Real.sqrt_le_sqrt hHH
    _ = (2*((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∑ n ∈ t, ‖f n‖^2)
          * Real.sqrt (∑ x ∈ u, h x ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
        ring


end

end NestedScales

open NestedScales

/-- **Bourgain's Lemma 4.32 (circle form).**  For any finite set `S` of scales, the maximal
function over `S` of the projections onto the periodised `2^{-j-1}`-neighbourhoods of an
arbitrary finite set of frequencies is bounded on `ℓ²(ℤ)` by `C log(#{S}+2)`.

The multipliers `1_{R j}` are *nested* (`R j' ⊆ R j` for `j ≤ j'`), and Lemma 4.32 is the
Burkholder–Davis–Gundy / dual-Doob estimate for such a nested family: its proof uses only the
nestedness, via a dyadic partitioning of `S` and the orthogonality of the difference operators
`P j − P j'` on disjointly supported multipliers. -/
private lemma iSup_ofReal_nested {ι : Type*} [Fintype ι] (y : ι → ℝ) :
    (⨆ i, ENNReal.ofReal (y i)) = ENNReal.ofReal (⨆ i, y i) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h1 : (⨆ i, ENNReal.ofReal (y i)) = 0 := iSup_of_empty _
    have h2 : (⨆ i, y i) = 0 := Real.iSup_of_isEmpty y
    rw [h1, h2, ENNReal.ofReal_zero]
  · refine le_antisymm ?_ ?_
    · exact ciSup_le fun i => ENNReal.ofReal_le_ofReal (le_ciSup (Set.finite_range y).bddAbove i)
    · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image (Finset.univ : Finset ι) y
        ⟨Classical.arbitrary ι, Finset.mem_univ _⟩
      have hsup : (⨆ i, y i) = y i₀ :=
        le_antisymm (ciSup_le fun i => hi₀ i (Finset.mem_univ i))
          (le_ciSup (Set.finite_range y).bddAbove i₀)
      rw [hsup]
      exact le_iSup (fun i => ENNReal.ofReal (y i)) i₀

private lemma enorm_eq_ofReal_norm_nested (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  simp [enorm_eq_nnnorm]

theorem nested_finite_scales_maximal_l2 :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ) (S : Finset ℕ),
      ∀ (f : ℤ → ℂ) (s : Finset ℤ), (∀ n, n ∉ s → f n = 0) →
        ∫⁻ m, (⨆ j ∈ S, ‖∑ n ∈ s, f n *
            (∫ θ in Set.Icc (0:ℝ) 1,
              Set.indicator
                {θ : ℝ | ∃ k : Fin K, ∃ l : ℤ, |θ + (l:ℝ) - lam k| ≤ (2:ℝ)^(-(j:ℝ)-1)}
                (fun θ => Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ)))) θ)‖ₑ)^(2:ℝ)
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((C * Real.log ((S.card:ℝ)+2))^2)
            * ∫⁻ n, ‖f n‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count := by
  classical
  refine ⟨50, by norm_num, ?_⟩
  intro K lam S f s hf
  set R : ℕ → Set ℝ := fun j => {θ : ℝ | ∃ k : Fin K, ∃ l : ℤ,
      |θ + (l:ℝ) - lam k| ≤ (2:ℝ)^(-(j:ℝ)-1)} with hRdef
  have hmeasR : ∀ j, MeasurableSet (R j) := by
    intro j
    simp only [hRdef]
    have hset : {θ : ℝ | ∃ k : Fin K, ∃ l : ℤ, |θ + (l:ℝ) - lam k| ≤ (2:ℝ)^(-(j:ℝ)-1)}
        = ⋃ k : Fin K, ⋃ l : ℤ,
            {θ : ℝ | |θ + (l:ℝ) - lam k| ≤ (2:ℝ)^(-(j:ℝ)-1)} := by
      ext θ; simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    rw [hset]
    refine MeasurableSet.iUnion (fun k => MeasurableSet.iUnion (fun l => ?_))
    have hc : Continuous (fun θ : ℝ => |θ + (l:ℝ) - lam k|) := by fun_prop
    exact (isClosed_Iic.preimage hc).measurableSet
  have hnestR : ∀ i j : ℕ, i ≤ j → R j ⊆ R i := by
    intro i j hij θ hθ
    simp only [hRdef, Set.mem_setOf_eq] at hθ ⊢
    obtain ⟨k, l, hl⟩ := hθ
    refine ⟨k, l, le_trans hl ?_⟩
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
    push_cast
    have : (i:ℝ) ≤ (j:ℝ) := by exact_mod_cast hij
    linarith
  have hKern : ∀ (j : ℕ) (m : ℤ), projKern (R j) m
      = ∫ θ in Set.Icc (0:ℝ) 1,
          Set.indicator (R j) (fun θ => Complex.exp (-(2*Real.pi*Complex.I*((m:ℤ):ℂ)*(θ:ℂ)))) θ := by
    intro j m
    rw [projKern, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      ← integral_Icc_eq_integral_Ioc]
  have hInn : ∀ (j : ℕ) (m : ℤ),
      (∑ n ∈ s, f n * (∫ θ in Set.Icc (0:ℝ) 1,
          Set.indicator (R j) (fun θ => Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ)))) θ))
        = projOp (R j) s f m := by
    intro j m
    rw [projOp]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [hKern j (m - n)]
  rcases S.eq_empty_or_nonempty with hS | hS
  · -- empty case
    rw [hS]
    simp
  · -- main case
    set M : ℕ := S.card with hMdef
    have hMpos : 1 ≤ M := by rw [hMdef]; exact Finset.card_pos.mpr hS
    haveI : NeZero M := ⟨by omega⟩
    set e : Fin M ≃o ↥S := S.orderIsoOfFin rfl with hedef
    set Rp : Fin M → Set ℝ := fun i => R ((e i : ↥S) : ℕ) with hRpdef
    have hmeasRp : ∀ i : Fin M, MeasurableSet (Rp i) := fun i => hmeasR _
    have hnestRp : ∀ i j : Fin M, i ≤ j → Rp j ⊆ Rp i := by
      intro i j hij
      exact hnestR _ _ (by exact_mod_cast (e.monotone hij : ((e i : ↥S) : ℕ) ≤ ((e j : ↥S) : ℕ)))
    -- reindexing the supremum
    have hSupReindex : ∀ (g : ℕ → ℝ≥0∞),
        (⨆ j ∈ S, g j) = ⨆ i : Fin M, g ((e i : ↥S) : ℕ) := by
      intro g
      rw [← Finset.sup_eq_iSup]
      apply le_antisymm
      · refine Finset.sup_le (fun j hj => ?_)
        obtain ⟨i, hi⟩ := e.surjective ⟨j, hj⟩
        have hji : g j = g ((e i : ↥S) : ℕ) := by rw [hi]
        rw [hji]
        exact le_iSup (fun i : Fin M => g ((e i : ↥S) : ℕ)) i
      · refine iSup_le (fun i => ?_)
        exact Finset.le_sup (f := g) (e i).2
    -- the transformed statement
    have hgoal : ∫⁻ m, (⨆ j ∈ S, ‖∑ n ∈ s, f n *
            (∫ θ in Set.Icc (0:ℝ) 1,
              Set.indicator
                {θ : ℝ | ∃ k : Fin K, ∃ l : ℤ, |θ + (l:ℝ) - lam k| ≤ (2:ℝ)^(-(j:ℝ)-1)}
                (fun θ => Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ)))) θ)‖ₑ)^(2:ℝ)
          ∂MeasureTheory.Measure.count
        = ∫⁻ m, (⨆ i : Fin M, ‖projOp (Rp i) s f m‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count := by
      apply lintegral_congr
      intro m
      congr 1
      rw [hSupReindex]
      apply iSup_congr
      intro i
      have hinner : (∑ n ∈ s, f n * (∫ θ in Set.Icc (0:ℝ) 1,
              Set.indicator {θ : ℝ | ∃ k : Fin K, ∃ l : ℤ,
                  |θ + (l:ℝ) - lam k| ≤ (2:ℝ)^(-(((e i : ↥S) : ℕ):ℝ)-1)}
                (fun θ => Complex.exp (-(2*Real.pi*Complex.I*(((m-n:ℤ):ℂ))*(θ:ℂ)))) θ))
          = projOp (Rp i) s f m := by
        simp only [hRpdef]
        exact hInn ((e i : ↥S) : ℕ) m
      rw [hinner]
    rw [hgoal]
    -- the real supremum and the finite bound
    set Sf : ℤ → ℝ := fun x => ⨆ i : Fin M, ‖projOp (Rp i) s f x‖ with hSfdef
    have hSfnn : ∀ x, 0 ≤ Sf x := by
      intro x
      simp only [hSfdef]
      exact le_trans (norm_nonneg _)
        (le_ciSup (Set.finite_range (fun i : Fin M => ‖projOp (Rp i) s f x‖)).bddAbove
          (Classical.arbitrary (Fin M)))
    have hDpos : (0:ℝ) < 2*((Nat.log2 M : ℝ) + 1) + 3 := by positivity
    -- (A) the finite weighted bound from the linearization
    have hA : ∀ (u : Finset ℤ), ∑ x ∈ u, (Sf x)^2
        ≤ (2*((Nat.log2 M : ℝ) + 1) + 3)^2 * ∑ n ∈ s, ‖f n‖^2 := by
      intro u
      have hh : ∀ x, 0 ≤ (fun x => if x ∈ u then Sf x else 0) x := by
        intro x; by_cases hx : x ∈ u <;> simp [hx, hSfnn x]
      have hu : ∀ x, x ∉ u → (fun x => if x ∈ u then Sf x else 0) x = 0 := by
        intro x hx; simp [hx]
      have hlin := linearization_bound M hMpos Rp hmeasRp hnestRp f s hf
        (fun x => if x ∈ u then Sf x else 0) hh u hu
      have h1 : ∑ x ∈ u, (fun x => if x ∈ u then Sf x else 0) x * Sf x = ∑ x ∈ u, (Sf x)^2 := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        simp only [hx, if_true]
        ring
      have h2 : ∑ x ∈ u, ((fun x => if x ∈ u then Sf x else 0) x)^2 = ∑ x ∈ u, (Sf x)^2 := by
        refine Finset.sum_congr rfl (fun x hx => ?_)
        simp only [hx, if_true]
      rw [h1, h2] at hlin
      have hsqrt : Real.sqrt (∑ x ∈ u, (Sf x)^2)
          ≤ (2*((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∑ n ∈ s, ‖f n‖^2) := by
        by_cases hzero : ∑ x ∈ u, (Sf x)^2 = 0
        · rw [hzero, Real.sqrt_zero]
          positivity
        · have hpos : 0 < ∑ x ∈ u, (Sf x)^2 := lt_of_le_of_ne (Finset.sum_nonneg (fun x _ => sq_nonneg _)) (Ne.symm hzero)
          have h3 : Real.sqrt (∑ x ∈ u, (Sf x)^2) * Real.sqrt (∑ x ∈ u, (Sf x)^2)
              ≤ (2*((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∑ n ∈ s, ‖f n‖^2)
                  * Real.sqrt (∑ x ∈ u, (Sf x)^2) := by
            rw [Real.mul_self_sqrt (le_of_lt hpos)]
            exact hlin
          exact le_of_mul_le_mul_right h3 (Real.sqrt_pos.mpr hpos)
      calc ∑ x ∈ u, (Sf x)^2
          = Real.sqrt (∑ x ∈ u, (Sf x)^2) * Real.sqrt (∑ x ∈ u, (Sf x)^2) := by
            rw [Real.mul_self_sqrt (Finset.sum_nonneg (fun x _ => sq_nonneg _))]
        _ ≤ (2*((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∑ n ∈ s, ‖f n‖^2)
              * ((2*((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∑ n ∈ s, ‖f n‖^2)) := by
            calc Real.sqrt (∑ x ∈ u, (Sf x)^2) * Real.sqrt (∑ x ∈ u, (Sf x)^2)
                ≤ ((2*((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∑ n ∈ s, ‖f n‖^2))
                    * Real.sqrt (∑ x ∈ u, (Sf x)^2) := by
                  exact mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg _)
              _ ≤ ((2*((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∑ n ∈ s, ‖f n‖^2))
                    * ((2*((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∑ n ∈ s, ‖f n‖^2)) :=
                  mul_le_mul_of_nonneg_left hsqrt (by positivity)
        _ = (2*((Nat.log2 M : ℝ) + 1) + 3)^2 * ∑ n ∈ s, ‖f n‖^2 := by
            have hSsum : 0 ≤ ∑ n ∈ s, ‖f n‖^2 := Finset.sum_nonneg (fun n _ => by positivity)
            rw [show ((2*((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∑ n ∈ s, ‖f n‖^2))
                * ((2*((Nat.log2 M : ℝ) + 1) + 3) * Real.sqrt (∑ n ∈ s, ‖f n‖^2))
                = (2*((Nat.log2 M : ℝ) + 1) + 3)^2 * (Real.sqrt (∑ n ∈ s, ‖f n‖^2))^2 by ring,
              Real.sq_sqrt hSsum]
    -- (B) the lintegral bound
    have hB : ∫⁻ m, (⨆ i : Fin M, ‖projOp (Rp i) s f m‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((2*((Nat.log2 M : ℝ) + 1) + 3)^2 * ∑ n ∈ s, ‖f n‖^2) := by
      rw [lintegral_count, ENNReal.tsum_eq_iSup_sum]
      refine iSup_le (fun u : Finset ℤ => ?_)
      have h1 : (∑ x ∈ u, (⨆ i : Fin M, ‖projOp (Rp i) s f x‖ₑ)^(2:ℝ))
          = ENNReal.ofReal (∑ x ∈ u, (Sf x)^2) := by
        have hpt : ∀ x : ℤ, (⨆ i : Fin M, ‖projOp (Rp i) s f x‖ₑ)^(2:ℝ)
            = ENNReal.ofReal ((Sf x)^2) := by
          intro x
          have h2 : (⨆ i : Fin M, ‖projOp (Rp i) s f x‖ₑ) = ENNReal.ofReal (Sf x) := by
            have hsfeq : Sf x = ⨆ i : Fin M, ‖projOp (Rp i) s f x‖ := rfl
            rw [hsfeq]
            have h3 : (⨆ i : Fin M, ‖projOp (Rp i) s f x‖ₑ)
                = ⨆ i : Fin M, ENNReal.ofReal (‖projOp (Rp i) s f x‖) :=
              iSup_congr (fun i => enorm_eq_ofReal_norm_nested _)
            rw [h3, iSup_ofReal_nested]
          rw [h2, ENNReal.ofReal_rpow_of_nonneg (hSfnn x) (by norm_num), Real.rpow_two]
        rw [Finset.sum_congr rfl (fun x _ => hpt x),
          ENNReal.ofReal_sum_of_nonneg (fun x _ => by positivity)]
      rw [h1]
      exact ENNReal.ofReal_le_ofReal (hA u)
    -- (C) the RHS
    have hRHS : ∫⁻ n, ‖f n‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count
        = ENNReal.ofReal (∑ n ∈ s, ‖f n‖^2) := by
      rw [lintegral_count]
      have hsummable : Summable (fun n : ℤ => ‖f n‖ ^ 2) := by
        refine summable_of_ne_finset_zero (s := s) (fun n hn => ?_)
        rw [hf n hn, norm_zero]; norm_num
      have hpt : ∀ n : ℤ, ‖f n‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖f n‖ ^ 2) := by
        intro n
        rw [enorm_eq_ofReal_norm_nested,
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num), Real.rpow_two]
      rw [tsum_congr hpt]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _) hsummable]
      rw [tsum_eq_sum (s := s) (fun n hn => by rw [hf n hn, norm_zero]; norm_num)]
    -- (D) the constant comparison
    have hconst : (2*((Nat.log2 M : ℝ) + 1) + 3)^2 * ∑ n ∈ s, ‖f n‖^2
        ≤ (50 * Real.log ((S.card:ℝ) + 2))^2 * ∑ n ∈ s, ‖f n‖^2 := by
      have hSsum : 0 ≤ ∑ n ∈ s, ‖f n‖^2 := Finset.sum_nonneg (fun n _ => by positivity)
      apply mul_le_mul_of_nonneg_right _ hSsum
      have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
      have hlog2half : (1:ℝ)/2 ≤ Real.log 2 := by
        have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
        norm_num at this ⊢
        linarith
      have hMM : (2:ℝ) ≤ (M:ℝ) + 2 := by
        have : (0:ℝ) ≤ M := by positivity
        linarith
      have hlogM : (1:ℝ)/2 ≤ Real.log ((M:ℝ) + 2) :=
        le_trans hlog2half (Real.log_le_log (by norm_num) hMM)
      have hlogMpos : 0 < Real.log ((M:ℝ) + 2) := lt_of_lt_of_le (by norm_num) hlogM
      have hcard : (M:ℝ) = (S.card:ℝ) := by rw [hMdef]
      rw [← hcard]
      have hlog2M : (Nat.log2 M : ℝ) * Real.log 2 ≤ Real.log ((M:ℝ)) := by
        have h2 : ((2:ℝ) ^ (Nat.log2 M)) ≤ (M:ℝ) := by
          have h : 2 ^ Nat.log 2 M ≤ M := Nat.pow_log_le_self 2 (by omega : M ≠ 0)
          rw [← Nat.log2_eq_log_two] at h
          exact_mod_cast h
        have h3 := Real.log_le_log (by positivity) h2
        rwa [Real.log_pow] at h3
      have hlogMM : Real.log ((M:ℝ)) ≤ Real.log ((M:ℝ) + 2) :=
        Real.log_le_log (by positivity) (by linarith)
      have hkey : (Nat.log2 M : ℝ) ≤ 2 * Real.log ((M:ℝ) + 2) := by
        have := le_trans hlog2M hlogMM
        nlinarith [this, hlog2half, hlogMpos]
      have hbig : 2*((Nat.log2 M : ℝ) + 1) + 3 ≤ 50 * Real.log ((M:ℝ) + 2) := by
        nlinarith [hkey, hlogM]
      have hnonneg : 0 ≤ 2*((Nat.log2 M : ℝ) + 1) + 3 := by positivity
      have hnonneg2 : 0 ≤ 50 * Real.log ((M:ℝ) + 2) := by positivity
      calc (2*((Nat.log2 M : ℝ) + 1) + 3)^2
          ≤ (50 * Real.log ((M:ℝ) + 2))^2 := by
            exact pow_le_pow_left₀ hnonneg hbig 2
        _ = (50 * Real.log ((S.card:ℝ) + 2))^2 := by rw [← hcard]
    calc ∫⁻ m, (⨆ i : Fin M, ‖projOp (Rp i) s f m‖ₑ)^(2:ℝ) ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ((2*((Nat.log2 M : ℝ) + 1) + 3)^2 * ∑ n ∈ s, ‖f n‖^2) := hB
      _ ≤ ENNReal.ofReal ((50 * Real.log ((S.card:ℝ) + 2))^2 * ∑ n ∈ s, ‖f n‖^2) :=
          ENNReal.ofReal_le_ofReal hconst
      _ = ENNReal.ofReal ((50 * Real.log ((S.card:ℝ) + 2))^2)
            * ENNReal.ofReal (∑ n ∈ s, ‖f n‖^2) := by
          rw [ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal ((50 * Real.log ((S.card:ℝ) + 2))^2)
            * ∫⁻ n, ‖f n‖ₑ^(2:ℝ) ∂MeasureTheory.Measure.count := by rw [← hMdef, hRHS]

end Commons.Analysis.Fourier