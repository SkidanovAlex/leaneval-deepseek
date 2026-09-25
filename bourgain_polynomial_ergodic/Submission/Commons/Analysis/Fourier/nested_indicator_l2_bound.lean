import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Fourier

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace NestedIndicator

variable {α : Type*} [MeasurableSpace α]

/-- The bilinear pairing `(f, g) ↦ Re ∫ f · conj g` associated with a measure `μ`. -/
def IP (μ : Measure α) (f g : α → ℂ) : ℝ := (∫ a, f a * star (g a) ∂μ).re

lemma IP_of_integrand_eq (μ : Measure α) {f g f' g' : α → ℂ}
    (h : ∀ a, f a * star (g a) = f' a * star (g' a)) : IP μ f g = IP μ f' g' := by
  unfold IP
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall h)

lemma IP_symm (μ : Measure α) (f g : α → ℂ) : IP μ f g = IP μ g f := by
  have h : (∫ a, g a * star (f a) ∂μ) = star (∫ a, f a * star (g a) ∂μ) := by
    have hc : (∫ a, star (f a * star (g a)) ∂μ)
        = star (∫ a, f a * star (g a) ∂μ) :=
      integral_conj (f := fun a => f a * star (g a)) (μ := μ)
    rw [← hc]
    apply integral_congr_ae
    filter_upwards with a
    simp only [star_mul, star_star]
  unfold IP
  rw [h]
  exact Complex.conj_re _

/-- The `L²(μ)`-product `f · conj g` is integrable. -/
lemma integrable_mul_star (μ : Measure α) {f g : α → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun a => f a * star (g a)) μ :=
  MemLp.integrable_mul hf hg.star

lemma IP_self (μ : Measure α) {f : α → ℂ} (hf : MemLp f 2 μ) :
    IP μ f f = ∫ a, ‖f a‖ ^ (2:ℝ) ∂μ := by
  unfold IP
  have h1 : (∫ a, f a * star (f a) ∂μ) = ((∫ a, ‖f a‖ ^ (2:ℝ) ∂μ : ℝ) : ℂ) := by
    have hpt : ∀ a, f a * star (f a) = ((‖f a‖ ^ (2:ℝ) : ℝ) : ℂ) := by
      intro a
      have h : f a * star (f a) = (Complex.normSq (f a) : ℂ) := Complex.mul_conj (f a)
      rw [h, Complex.normSq_eq_norm_sq]
      congr 1
      exact (Real.rpow_two _).symm
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    exact integral_ofReal (𝕜 := ℂ)
  rw [h1]
  exact Complex.ofReal_re _

lemma IP_add_left (μ : Measure α) {f1 f2 g : α → ℂ}
    (hf1 : MemLp f1 2 μ) (hf2 : MemLp f2 2 μ) (hg : MemLp g 2 μ) :
    IP μ (fun a => f1 a + f2 a) g = IP μ f1 g + IP μ f2 g := by
  have h1 : Integrable (fun a => f1 a * star (g a)) μ := integrable_mul_star μ hf1 hg
  have h2 : Integrable (fun a => f2 a * star (g a)) μ := integrable_mul_star μ hf2 hg
  unfold IP
  have h : (∫ a, (f1 a + f2 a) * star (g a) ∂μ)
      = (∫ a, f1 a * star (g a) ∂μ) + (∫ a, f2 a * star (g a) ∂μ) := by
    rw [← integral_add h1 h2]
    apply integral_congr_ae
    filter_upwards with a
    ring
  rw [h, Complex.add_re]

lemma IP_add_right (μ : Measure α) {f g1 g2 : α → ℂ}
    (hf : MemLp f 2 μ) (hg1 : MemLp g1 2 μ) (hg2 : MemLp g2 2 μ) :
    IP μ f (fun a => g1 a + g2 a) = IP μ f g1 + IP μ f g2 := by
  rw [IP_symm μ f (fun a => g1 a + g2 a), IP_add_left μ hg1 hg2 hf, IP_symm μ g1 f,
    IP_symm μ g2 f]

lemma IP_add_add (μ : Measure α) {f1 f2 : α → ℂ} (hf1 : MemLp f1 2 μ) (hf2 : MemLp f2 2 μ) :
    IP μ (fun a => f1 a + f2 a) (fun a => f1 a + f2 a)
      = IP μ f1 f1 + IP μ f1 f2 + IP μ f2 f1 + IP μ f2 f2 := by
  have h12 : MemLp (fun a => f1 a + f2 a) 2 μ := hf1.add hf2
  rw [IP_add_left μ hf1 hf2 h12, IP_add_right μ hf1 hf1 hf2, IP_add_right μ hf2 hf1 hf2]
  ring

lemma IP_sum_left {ι : Type*} (μ : Measure α) (s : Finset ι) (u : ι → α → ℂ) (g : α → ℂ)
    (hu : ∀ i ∈ s, MemLp (u i) 2 μ) (hg : MemLp g 2 μ) :
    IP μ (fun x => ∑ i ∈ s, u i x) g = ∑ i ∈ s, IP μ (u i) g := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      unfold IP
      simp
  | insert a s ha ih =>
      have hua : MemLp (u a) 2 μ := hu a (Finset.mem_insert_self a s)
      have hus : ∀ i ∈ s, MemLp (u i) 2 μ := fun i hi => hu i (Finset.mem_insert_of_mem hi)
      have hsplit : IP μ (fun x => ∑ i ∈ insert a s, u i x) g
          = IP μ (fun x => u a x + (fun x => ∑ i ∈ s, u i x) x) g := by
        apply IP_of_integrand_eq
        intro x
        show (∑ i ∈ insert a s, u i x) * star (g x)
            = (u a x + (fun x => ∑ i ∈ s, u i x) x) * star (g x)
        rw [Finset.sum_insert ha]
      rw [hsplit, IP_add_left μ hua (memLp_finsetSum s hus) hg, ih hus, Finset.sum_insert ha]

lemma IP_sum_right {ι : Type*} (μ : Measure α) (s : Finset ι) (f : α → ℂ) (u : ι → α → ℂ)
    (hf : MemLp f 2 μ) (hu : ∀ i ∈ s, MemLp (u i) 2 μ) :
    IP μ f (fun x => ∑ i ∈ s, u i x) = ∑ i ∈ s, IP μ f (u i) := by
  rw [IP_symm μ f (fun x => ∑ i ∈ s, u i x), IP_sum_left μ s u f hu hf]
  exact Finset.sum_congr rfl (fun i _ => IP_symm μ (u i) f)

lemma IP_sum_sum {ι κ : Type*} (μ : Measure α) (s : Finset ι) (t : Finset κ)
    (u : ι → α → ℂ) (v : κ → α → ℂ) (hu : ∀ i ∈ s, MemLp (u i) 2 μ)
    (hv : ∀ j ∈ t, MemLp (v j) 2 μ) :
    IP μ (fun x => ∑ i ∈ s, u i x) (fun x => ∑ j ∈ t, v j x)
      = ∑ i ∈ s, ∑ j ∈ t, IP μ (u i) (v j) := by
  rw [IP_sum_left μ s u (fun x => ∑ j ∈ t, v j x) hu (memLp_finsetSum t hv)]
  exact Finset.sum_congr rfl (fun i hi => IP_sum_right μ t (u i) v (hu i hi) hv)

lemma IP_sum_self_of_orthogonal {ι : Type*} (μ : Measure α) (s : Finset ι) (u : ι → α → ℂ)
    (hu : ∀ i ∈ s, MemLp (u i) 2 μ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IP μ (u i) (u j) = 0) :
    IP μ (fun x => ∑ i ∈ s, u i x) (fun x => ∑ i ∈ s, u i x) = ∑ i ∈ s, IP μ (u i) (u i) := by
  rw [IP_sum_sum μ s s u u hu hu]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single i]
  · intro j hj hji
    exact horth i hi j hj (Ne.symm hji)
  · intro hi'
    exact absurd hi hi'

lemma two_mul_sqrt_mul_sqrt_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    2 * Real.sqrt a * Real.sqrt b ≤ a + b := by
  have h1 : 0 ≤ (Real.sqrt a - Real.sqrt b) ^ 2 := sq_nonneg _
  have h2 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have h3 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  nlinarith [h1, h2, h3, Real.sqrt_nonneg a, Real.sqrt_nonneg b]

lemma IP_cauchy (μ : Measure α) {f g : α → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |IP μ f g| ≤ Real.sqrt (IP μ f f) * Real.sqrt (IP μ g g) := by
  have h1 : |IP μ f g| ≤ ∫ a, ‖f a‖ * ‖g a‖ ∂μ := by
    have ha : |IP μ f g| ≤ ‖∫ a, f a * star (g a) ∂μ‖ := by
      unfold IP
      exact Complex.abs_re_le_norm _
    have hb : ‖∫ a, f a * star (g a) ∂μ‖ ≤ ∫ a, ‖f a * star (g a)‖ ∂μ :=
      norm_integral_le_integral_norm _
    have hc : (∫ a, ‖f a * star (g a)‖ ∂μ) = ∫ a, ‖f a‖ * ‖g a‖ ∂μ := by
      apply integral_congr_ae
      filter_upwards with a
      rw [norm_mul, norm_star]
    rw [hc] at hb
    exact le_trans ha hb
  have h2 : (∫ a, ‖f a‖ * ‖g a‖ ∂μ) ≤ Real.sqrt (IP μ f f) * Real.sqrt (IP μ g g) := by
    have hforder : (2:ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
    have hf2 : MemLp f (ENNReal.ofReal (2:ℝ)) μ := by
      rw [show ENNReal.ofReal (2:ℝ) = 2 by norm_num]; exact hf
    have hg2 : MemLp g (ENNReal.ofReal (2:ℝ)) μ := by
      rw [show ENNReal.ofReal (2:ℝ) = 2 by norm_num]; exact hg
    have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := μ) (p := 2) (q := 2) hforder hf2 hg2
    rw [IP_self μ hf, IP_self μ hg, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    exact hholder
  exact le_trans h1 h2

/-! ### Pointwise collapse of nested indicators -/

lemma norm_indicator_rpow_two_le (S : Set α) (u : α → ℂ) (x : α) :
    ‖Set.indicator S u x‖ ^ (2:ℝ) ≤ ‖u x‖ ^ (2:ℝ) := by
  have h := norm_indicator_le_norm_self (s := S) u x
  exact Real.rpow_le_rpow (norm_nonneg _) h (by norm_num)

lemma star_indicator (S : Set α) (u : α → ℂ) (x : α) :
    star (Set.indicator S u x) = Set.indicator S (fun x => star (u x)) x := by
  by_cases h : x ∈ S
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, star_zero]

lemma star_indicator_sum {ι : Type*} (s : Finset ι) (S : ι → Set α) (u : ι → α → ℂ)
    (x : α) :
    star (∑ i ∈ s, Set.indicator (S i) (u i) x)
      = ∑ i ∈ s, Set.indicator (S i) (fun x => star (u i x)) x := by
  rw [star_sum]
  exact Finset.sum_congr rfl (fun i _ => star_indicator (S i) (u i) x)

lemma collapse_pointwise {n : ℕ} (R : ℕ → Set α) (G : ℕ → α → ℂ)
    (hnest : ∀ i j, i < n → j < n → R (n+j) ⊆ R i) (x : α) :
    (∑ i ∈ Finset.range n, Set.indicator (R i) (G i) x)
      * star (∑ j ∈ Finset.range n, Set.indicator (R (n+j)) (G (n+j)) x)
    = (∑ i ∈ Finset.range n, G i x)
      * star (∑ j ∈ Finset.range n, Set.indicator (R (n+j)) (G (n+j)) x) := by
  rw [star_indicator_sum, Finset.sum_mul_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hi' : i < n := Finset.mem_range.mp hi
  have hj' : j < n := Finset.mem_range.mp hj
  by_cases h : x ∈ R (n+j)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hnest i j hi' hj' h)]
  · rw [Set.indicator_of_notMem h]
    ring

/-! ### The dyadic recursion -/

theorem dyadic_nested_bound (μ : Measure α) :
    ∀ (s : ℕ) (R : ℕ → Set α) (G : ℕ → α → ℂ),
    (∀ i, i < 2^s → MeasurableSet (R i)) →
    (∀ i j, i < 2^s → j < 2^s → i ≤ j → R j ⊆ R i) →
    (∀ i, i < 2^s → MemLp (G i) 2 μ) →
    (∀ i j, i < 2^s → j < 2^s → i ≠ j → IP μ (G i) (G j) = 0) →
    IP μ (fun x => ∑ i ∈ Finset.range (2^s), Set.indicator (R i) (G i) x)
       (fun x => ∑ i ∈ Finset.range (2^s), Set.indicator (R i) (G i) x)
      ≤ (2*(s:ℝ)+3)^2 * ∑ i ∈ Finset.range (2^s), IP μ (G i) (G i) := by
  intro s
  induction s with
  | zero =>
      intro R G hmeas hnest hG horth
      simp only [pow_zero, Finset.range_one, Finset.sum_singleton]
      rw [IP_self μ (MemLp.indicator (hmeas 0 (by norm_num)) (hG 0 (by norm_num))),
        IP_self μ (hG 0 (by norm_num))]
      have hmono : (∫ x, ‖Set.indicator (R 0) (G 0) x‖ ^ (2:ℝ) ∂μ)
          ≤ ∫ x, ‖G 0 x‖ ^ (2:ℝ) ∂μ := by
        apply integral_mono
        · exact (MemLp.indicator (hmeas 0 (by norm_num)) (hG 0 (by norm_num))).integrable_norm_rpow
            (by norm_num) (by norm_num)
        · exact (hG 0 (by norm_num)).integrable_norm_rpow (by norm_num) (by norm_num)
        · intro x
          exact norm_indicator_rpow_two_le (R 0) (G 0) x
      have hnn : 0 ≤ ∫ x, ‖G 0 x‖ ^ (2:ℝ) ∂μ :=
        integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) 2)
      have hC : (1:ℝ) ≤ (2*((0:ℕ):ℝ)+3)^2 := by norm_num
      calc (∫ x, ‖Set.indicator (R 0) (G 0) x‖ ^ (2:ℝ) ∂μ)
          ≤ ∫ x, ‖G 0 x‖ ^ (2:ℝ) ∂μ := hmono
        _ ≤ (2*((0:ℕ):ℝ)+3)^2 * ∫ x, ‖G 0 x‖ ^ (2:ℝ) ∂μ := by
            nlinarith [hnn, hC]
  | succ s ih =>
      intro R G hmeas hnest hG horth
      have hpow : 2^(s+1) = 2^s + 2^s := by rw [pow_succ, Nat.mul_two]
      rw [hpow] at hmeas hnest hG horth ⊢
      set A : α → ℂ := fun x => ∑ i ∈ Finset.range (2^s), Set.indicator (R i) (G i) x with hA
      set B : α → ℂ := fun x => ∑ j ∈ Finset.range (2^s), Set.indicator (R (2^s+j)) (G (2^s+j)) x
        with hB
      set σA : ℝ := ∑ i ∈ Finset.range (2^s), IP μ (G i) (G i) with hσA
      set σB : ℝ := ∑ j ∈ Finset.range (2^s), IP μ (G (2^s+j)) (G (2^s+j)) with hσB
      have hA_mem : MemLp A 2 μ := by
        rw [hA]
        refine memLp_finsetSum _ (fun i hi => ?_)
        exact MemLp.indicator (hmeas i (by have := Finset.mem_range.mp hi; omega))
          (hG i (by have := Finset.mem_range.mp hi; omega))
      have hB_mem : MemLp B 2 μ := by
        rw [hB]
        refine memLp_finsetSum _ (fun j hj => ?_)
        exact MemLp.indicator (hmeas (2^s+j) (by have := Finset.mem_range.mp hj; omega))
          (hG (2^s+j) (by have := Finset.mem_range.mp hj; omega))
      have hmain : (fun x => ∑ i ∈ Finset.range (2^s+2^s), Set.indicator (R i) (G i) x)
          = fun x => A x + B x := by
        funext x
        rw [hA, hB, Finset.sum_range_add]
      have hsum : (∑ i ∈ Finset.range (2^s+2^s), IP μ (G i) (G i)) = σA + σB := by
        rw [hσA, hσB, Finset.sum_range_add]
      have hAA : IP μ A A ≤ (2*(s:ℝ)+3)^2 * σA := by
        rw [hA, hσA]
        exact ih R G (fun i hi => hmeas i (by omega))
          (fun i j hi hj hij => hnest i j (by omega) (by omega) hij)
          (fun i hi => hG i (by omega)) (fun i j hi hj hij => horth i j (by omega) (by omega) hij)
      have hBB : IP μ B B ≤ (2*(s:ℝ)+3)^2 * σB := by
        rw [hB, hσB]
        exact ih (fun j => R (2^s+j)) (fun j => G (2^s+j))
          (fun j hj => hmeas (2^s+j) (by omega))
          (fun i j hi hj hij => hnest (2^s+i) (2^s+j) (by omega) (by omega) (by omega))
          (fun j hj => hG (2^s+j) (by omega))
          (fun i j hi hj hij => horth (2^s+i) (2^s+j) (by omega) (by omega) (by omega))
      have hG_mem : MemLp (fun x => ∑ i ∈ Finset.range (2^s), G i x) 2 μ :=
        memLp_finsetSum _ (fun i hi => hG i (by have := Finset.mem_range.mp hi; omega))
      have hGG : IP μ (fun x => ∑ i ∈ Finset.range (2^s), G i x)
          (fun x => ∑ i ∈ Finset.range (2^s), G i x) = σA := by
        rw [hσA]
        exact IP_sum_self_of_orthogonal μ _ G
          (fun i hi => hG i (by have := Finset.mem_range.mp hi; omega))
          (fun i hi j hj hij => horth i j (by have := Finset.mem_range.mp hi; omega)
            (by have := Finset.mem_range.mp hj; omega) hij)
      have hcoll : IP μ A B = IP μ (fun x => ∑ i ∈ Finset.range (2^s), G i x) B := by
        apply IP_of_integrand_eq
        intro x
        rw [hA, hB]
        exact collapse_pointwise (n := 2^s) R G
          (fun i j hi hj => hnest i (2^s+j) (by omega) (by omega) (by omega)) x
      have hnnA : 0 ≤ σA := by
        rw [hσA]
        refine Finset.sum_nonneg (fun i hi => ?_)
        rw [IP_self μ (hG i (by have := Finset.mem_range.mp hi; omega))]
        exact integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) 2)
      have hnnB : 0 ≤ σB := by
        rw [hσB]
        refine Finset.sum_nonneg (fun j hj => ?_)
        rw [IP_self μ (hG (2^s+j) (by have := Finset.mem_range.mp hj; omega))]
        exact integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) 2)
      have hCs : (0:ℝ) ≤ 2*(s:ℝ)+3 := by positivity
      have hAB : IP μ A B ≤ (2*(s:ℝ)+3) * Real.sqrt (σA * σB) := by
        rw [hcoll]
        have hcs := IP_cauchy μ hG_mem hB_mem
        have h2 : Real.sqrt (IP μ (fun x => ∑ i ∈ Finset.range (2^s), G i x)
              (fun x => ∑ i ∈ Finset.range (2^s), G i x)) = Real.sqrt σA := by rw [hGG]
        have h3 : Real.sqrt (IP μ B B) ≤ Real.sqrt ((2*(s:ℝ)+3)^2 * σB) :=
          Real.sqrt_le_sqrt hBB
        have h4 : Real.sqrt ((2*(s:ℝ)+3)^2 * σB) = (2*(s:ℝ)+3) * Real.sqrt σB := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hCs]
        have h5 : Real.sqrt σA * ((2*(s:ℝ)+3) * Real.sqrt σB)
            = (2*(s:ℝ)+3) * Real.sqrt (σA * σB) := by
          rw [Real.sqrt_mul hnnA σB]; ring
        have h6 : IP μ (fun x => ∑ i ∈ Finset.range (2^s), G i x) B
            ≤ Real.sqrt σA * ((2*(s:ℝ)+3) * Real.sqrt σB) := by
          calc IP μ (fun x => ∑ i ∈ Finset.range (2^s), G i x) B
              ≤ |IP μ (fun x => ∑ i ∈ Finset.range (2^s), G i x) B| := le_abs_self _
            _ ≤ Real.sqrt (IP μ (fun x => ∑ i ∈ Finset.range (2^s), G i x)
                  (fun x => ∑ i ∈ Finset.range (2^s), G i x)) * Real.sqrt (IP μ B B) := hcs
            _ ≤ Real.sqrt σA * ((2*(s:ℝ)+3) * Real.sqrt σB) := by
                rw [h2]
                exact mul_le_mul_of_nonneg_left (le_trans h3 (le_of_eq h4)) (Real.sqrt_nonneg _)
        rw [← h5]
        exact h6
      have hfinal : IP μ A A + IP μ A B + IP μ A B + IP μ B B
          ≤ (2*((s:ℝ)+1)+3)^2 * (σA + σB) := by
        have harm : (2*(s:ℝ)+3)^2 + (2*(s:ℝ)+3) ≤ (2*((s:ℝ)+1)+3)^2 := by
          have : (0:ℝ) ≤ s := by positivity
          nlinarith
        have h1 : IP μ A A + IP μ A B + IP μ A B + IP μ B B
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
        calc IP μ A A + IP μ A B + IP μ A B + IP μ B B
            ≤ (2*(s:ℝ)+3)^2 * σA + (2*(s:ℝ)+3)^2 * σB
              + 2 * ((2*(s:ℝ)+3) * Real.sqrt (σA * σB)) := h1
          _ = (2*(s:ℝ)+3)^2 * (σA + σB) + (2*(s:ℝ)+3) * (2 * Real.sqrt (σA*σB)) := h2
          _ ≤ (2*(s:ℝ)+3)^2 * (σA + σB) + (2*(s:ℝ)+3) * (σA + σB) := by linarith [h3]
          _ = ((2*(s:ℝ)+3)^2 + (2*(s:ℝ)+3)) * (σA + σB) := by ring
          _ ≤ (2*((s:ℝ)+1)+3)^2 * (σA + σB) := by
              apply mul_le_mul_of_nonneg_right harm (by linarith)
      have hcast : (2*((s:ℝ)+1)+3) = (2*(↑(s+1):ℝ)+3) := by push_cast; ring
      rw [hcast] at hfinal
      rw [hmain, IP_add_add μ hA_mem hB_mem, hsum, IP_symm μ B A]
      exact hfinal

/-- `∫⁻ ‖f‖ₑ^{2} = ofReal (∫ ‖f‖^{2})` for `f ∈ L²(μ)`. -/
lemma lintegral_enorm_rpow_two (μ : Measure α) {f : α → ℂ} (hf : MemLp f 2 μ) :
    ∫⁻ a, ‖f a‖ₑ ^ (2:ℝ) ∂μ = ENNReal.ofReal (∫ a, ‖f a‖ ^ (2:ℝ) ∂μ) := by
  have hint : Integrable (fun a => ‖f a‖ ^ (2:ℝ)) μ := by
    have h := hf.integrable_norm_rpow (p := 2) (by norm_num) (by norm_num)
    simpa using h
  rw [show (∫⁻ a, ‖f a‖ₑ ^ (2:ℝ) ∂μ)
      = ∫⁻ a, ENNReal.ofReal (‖f a‖ ^ (2:ℝ)) ∂μ from
    lintegral_congr (fun a => by
      show ‖f a‖ₑ ^ (2:ℝ) = ENNReal.ofReal (‖f a‖ ^ (2:ℝ))
      rw [← ofReal_norm]
      exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num))]
  exact (ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun a => Real.rpow_nonneg (norm_nonneg _) 2))).symm

end NestedIndicator

/-- **Nested-band `L²` bound (dual Doob / Burkholder–Davis–Gundy estimate for nested
frequency projections).**

Let `C : Fin M → Set α` be a family of measurable sets that is *nested* — `C j ⊆ C i`
whenever `i ≤ j`, i.e. the sets get larger as the index decreases — and let `V i ∈ L²(μ)`
be pairwise orthogonal.  Then the band-pass operator `∑_i 1_{C i} ·` is bounded by
`2 log₂ M + 5`:

`∫⁻ ‖∑_i 1_{C i} · V i‖² ≤ (2 log₂ M + 5)² · ∑_i ∫⁻ ‖V i‖²`.

Only the nesting and the orthogonality enter the proof.  A template is available in the
committed commons file `Submission/Commons/Analysis/Fourier/nested_finite_scales_maximal_l2.lean`
(circle case): the *private* declarations there (`IP`, `IP_cauchy`, `IP_sum_self_of_orthogonal`,
`collapse_pointwise`, `circle_nested_bound_dyadic`, `IP_sum_indicator_bound`) prove exactly this
statement with `μ` replaced by `volume.restrict (Ioc 0 1)` and real parts of integrals; porting
them to a general measure and to the `lintegral` statement above is the task. -/
theorem nested_indicator_l2_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (M : ℕ) (hM : 1 ≤ M) (C : Fin M → Set α) (V : Fin M → α → ℂ)
    (hmeas : ∀ i, MeasurableSet (C i))
    (hnest : ∀ i j : Fin M, i ≤ j → C j ⊆ C i)
    (hV : ∀ i, MemLp (V i) 2 μ)
    (horth : ∀ i j : Fin M, i ≠ j → ∫ a, V i a * star (V j a) ∂μ = 0) :
    ∫⁻ a, ‖∑ i : Fin M, Set.indicator (C i) (V i) a‖ₑ ^ (2:ℝ) ∂μ
      ≤ ENNReal.ofReal ((2 * ((Nat.log2 M : ℝ) + 1) + 3) ^ 2)
        * ∑ i : Fin M, ∫⁻ a, ‖V i a‖ₑ ^ (2:ℝ) ∂μ := by
  classical
  set ℓ : ℕ := Nat.log2 M + 1 with hℓ
  have hMle : M ≤ 2^ℓ := by
    rw [hℓ]
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) M
    rw [← Nat.log2_eq_log_two, Nat.succ_eq_add_one] at h
    exact le_of_lt h
  set R' : ℕ → Set α := fun i => if hi : i < M then C ⟨i, hi⟩ else ∅ with hR'
  set V' : ℕ → α → ℂ := fun i => if hi : i < M then V ⟨i, hi⟩ else 0 with hV'
  have hR'meas : ∀ i, i < 2^ℓ → MeasurableSet (R' i) := by
    intro i _
    simp only [hR']
    split_ifs with hiM
    · exact hmeas _
    · exact MeasurableSet.empty
  have hR'nest : ∀ i j, i < 2^ℓ → j < 2^ℓ → i ≤ j → R' j ⊆ R' i := by
    intro i j _ _ hij
    simp only [hR']
    by_cases hiM : i < M
    · by_cases hjM : j < M
      · rw [dif_pos hiM, dif_pos hjM]
        exact hnest ⟨i, hiM⟩ ⟨j, hjM⟩ hij
      · rw [dif_pos hiM, dif_neg hjM]
        exact Set.empty_subset _
    · have hjM : ¬ j < M := by omega
      rw [dif_neg hiM, dif_neg hjM]
  have hV'mem : ∀ i, i < 2^ℓ → MemLp (V' i) 2 μ := by
    intro i _
    simp only [hV']
    split_ifs with hiM
    · exact hV _
    · exact MemLp.zero
  have hV'orth : ∀ i j, i < 2^ℓ → j < 2^ℓ → i ≠ j → NestedIndicator.IP μ (V' i) (V' j) = 0 := by
    intro i j hi hj hij
    simp only [hV']
    by_cases hiM : i < M
    · by_cases hjM : j < M
      · rw [dif_pos hiM, dif_pos hjM]
        unfold NestedIndicator.IP
        rw [horth ⟨i, hiM⟩ ⟨j, hjM⟩ (fun h => hij (by simpa using congrArg Fin.val h))]
        simp
      · rw [dif_pos hiM, dif_neg hjM]
        unfold NestedIndicator.IP; simp
    · rw [dif_neg hiM]
      unfold NestedIndicator.IP; simp
  have key := NestedIndicator.dyadic_nested_bound μ ℓ R' V' hR'meas hR'nest hV'mem hV'orth
  have hsame1 : (fun x => ∑ i ∈ Finset.range (2^ℓ), Set.indicator (R' i) (V' i) x)
      = fun x => ∑ i : Fin M, Set.indicator (C i) (V i) x := by
    funext x
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr hMle)
      (fun y _ hyM => by
        have hyM' : ¬ y < M := by simpa using hyM
        simp only [hV', dif_neg hyM', Set.indicator_zero', Pi.zero_apply])]
    rw [Finset.sum_range]
    exact Finset.sum_congr rfl (fun i _ => by simp only [hR', hV', dif_pos i.isLt])
  have hsame2 : (∑ i ∈ Finset.range (2^ℓ), NestedIndicator.IP μ (V' i) (V' i))
      = ∑ i : Fin M, NestedIndicator.IP μ (V i) (V i) := by
    rw [← Finset.sum_subset (Finset.range_subset_range.mpr hMle)
      (fun y _ hyM => by
        have hyM' : ¬ y < M := by simpa using hyM
        simp only [hV', dif_neg hyM']
        unfold NestedIndicator.IP; simp)]
    rw [Finset.sum_range]
    exact Finset.sum_congr rfl (fun i _ => by simp only [hV', dif_pos i.isLt])
  rw [hsame1, hsame2] at key
  have hT_mem : MemLp (fun x => ∑ i : Fin M, Set.indicator (C i) (V i) x) 2 μ := by
    have h := memLp_finsetSum (Finset.univ : Finset (Fin M))
      (fun i _ => MemLp.indicator (hmeas i) (hV i))
    simpa using h
  have hp1 : NestedIndicator.IP μ (fun x => ∑ i : Fin M, Set.indicator (C i) (V i) x)
      (fun x => ∑ i : Fin M, Set.indicator (C i) (V i) x)
      = ∫ a, ‖∑ i : Fin M, Set.indicator (C i) (V i) a‖ ^ (2:ℝ) ∂μ :=
    NestedIndicator.IP_self μ hT_mem
  have hp3 : (∑ i : Fin M, NestedIndicator.IP μ (V i) (V i))
      = ∑ i : Fin M, ∫ a, ‖V i a‖ ^ (2:ℝ) ∂μ :=
    Finset.sum_congr rfl (fun i _ => NestedIndicator.IP_self μ (hV i))
  have hcast : (2 * (ℓ:ℝ) + 3) = (2 * ((Nat.log2 M : ℝ) + 1) + 3) := by
    rw [hℓ]; push_cast; ring
  have hmain_real : ∫ a, ‖∑ i : Fin M, Set.indicator (C i) (V i) a‖ ^ (2:ℝ) ∂μ
      ≤ (2 * ((Nat.log2 M : ℝ) + 1) + 3)^2
        * ∑ i : Fin M, ∫ a, ‖V i a‖ ^ (2:ℝ) ∂μ := by
    calc ∫ a, ‖∑ i : Fin M, Set.indicator (C i) (V i) a‖ ^ (2:ℝ) ∂μ
        = NestedIndicator.IP μ (fun x => ∑ i : Fin M, Set.indicator (C i) (V i) x)
            (fun x => ∑ i : Fin M, Set.indicator (C i) (V i) x) := hp1.symm
      _ ≤ (2*(ℓ:ℝ)+3)^2 * ∑ i : Fin M, NestedIndicator.IP μ (V i) (V i) := key
      _ = (2*(ℓ:ℝ)+3)^2 * ∑ i : Fin M, ∫ a, ‖V i a‖ ^ (2:ℝ) ∂μ := by rw [hp3]
      _ = (2 * ((Nat.log2 M : ℝ) + 1) + 3)^2
            * ∑ i : Fin M, ∫ a, ‖V i a‖ ^ (2:ℝ) ∂μ := by rw [hcast]
  have hCst_nn : 0 ≤ (2 * ((Nat.log2 M : ℝ) + 1) + 3)^2 := by positivity
  have hL : ∫⁻ a, ‖∑ i : Fin M, Set.indicator (C i) (V i) a‖ₑ ^ (2:ℝ) ∂μ
      = ENNReal.ofReal (∫ a, ‖∑ i : Fin M, Set.indicator (C i) (V i) a‖ ^ (2:ℝ) ∂μ) :=
    NestedIndicator.lintegral_enorm_rpow_two μ hT_mem
  calc ∫⁻ a, ‖∑ i : Fin M, Set.indicator (C i) (V i) a‖ₑ ^ (2:ℝ) ∂μ
      = ENNReal.ofReal (∫ a, ‖∑ i : Fin M, Set.indicator (C i) (V i) a‖ ^ (2:ℝ) ∂μ) := hL
    _ ≤ ENNReal.ofReal ((2 * ((Nat.log2 M : ℝ) + 1) + 3)^2
          * ∑ i : Fin M, ∫ a, ‖V i a‖ ^ (2:ℝ) ∂μ) := ENNReal.ofReal_le_ofReal hmain_real
    _ = ENNReal.ofReal ((2 * ((Nat.log2 M : ℝ) + 1) + 3)^2)
          * ENNReal.ofReal (∑ i : Fin M, ∫ a, ‖V i a‖ ^ (2:ℝ) ∂μ) := by
        rw [ENNReal.ofReal_mul hCst_nn]
    _ = ENNReal.ofReal ((2 * ((Nat.log2 M : ℝ) + 1) + 3)^2)
          * ∑ i : Fin M, ENNReal.ofReal (∫ a, ‖V i a‖ ^ (2:ℝ) ∂μ) := by
        rw [ENNReal.ofReal_sum_of_nonneg (f := fun i : Fin M => ∫ a, ‖V i a‖ ^ (2:ℝ) ∂μ)
          (fun i _ => integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) 2))]
    _ = ENNReal.ofReal ((2 * ((Nat.log2 M : ℝ) + 1) + 3)^2)
          * ∑ i : Fin M, ∫⁻ a, ‖V i a‖ₑ ^ (2:ℝ) ∂μ := by
        rw [Finset.sum_congr rfl (fun i _ => (NestedIndicator.lintegral_enorm_rpow_two μ (hV i)).symm)]

end

end Commons.Analysis.Fourier