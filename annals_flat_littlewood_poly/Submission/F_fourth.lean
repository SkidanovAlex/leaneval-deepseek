import Mathlib
import Submission.LMProbs
import Submission.LMMeas
import Submission.VecGauss2
import Submission.VecGauss4
import Submission.DirMom

/-!
Fourth-moment bound for the walk (child task).
-/

open scoped BigOperators RealInnerProductSpace ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section
open Classical

namespace Submission.Discrepancy

/-- `ofReal` over a Finset of nonnegative reals. -/
lemma ofReal_sum {α : Type*} (s : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ s, 0 ≤ f a) :
    ENNReal.ofReal (∑ a ∈ s, f a) = ∑ a ∈ s, ENNReal.ofReal (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have h1 : 0 ≤ ∑ x ∈ s, f x := Finset.sum_nonneg (by intro x hx; exact hf x (by
        exact Finset.mem_insert.mpr (Or.inr hx)))
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [ENNReal.ofReal_add (hf a (by simp)) h1]
      rw [ih (by intro x hx; exact hf x (Finset.mem_insert.mpr (Or.inr hx)))]

/-- `ofReal` is additive on sums of nonnegative reals over `Fin n`. -/
lemma ofReal_sum_univ {n : ℕ} (f : Fin n → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    ENNReal.ofReal (∑ i : Fin n, f i) = ∑ i : Fin n, ENNReal.ofReal (f i) := by
  have h := ofReal_sum (Finset.univ : Finset (Fin n)) f (by intro a ha; exact hf a)
  simpa using h

/-- Pointwise bound ‖y‖⁴ ≤ n·Σᵢ yᵢ⁴. -/
lemma norm4_le_mul_sum {n : ℕ} (y : Vec n) : ‖y‖ ^ 4 ≤ (n : ℝ) * ∑ i : Fin n, (y i) ^ 4 := by
  have hsq : ‖y‖ ^ 2 = ∑ i : Fin n, (y i) ^ 2 := norm_sq_sum n y
  have hCS : (∑ i ∈ (Finset.univ : Finset (Fin n)), (y i) ^ 2) ^ 2
      ≤ ((Finset.univ : Finset (Fin n)).card : ℝ) * ∑ i ∈ (Finset.univ : Finset (Fin n)), ((y i) ^ 2) ^ 2 := by
    exact sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := fun i => (y i) ^ 2)
  calc
    ‖y‖ ^ 4 = (∑ i : Fin n, (y i) ^ 2) ^ 2 := by
      rw [show ‖y‖ ^ 4 = (‖y‖ ^ 2) ^ 2 by ring]
      rw [hsq]
    _ = (∑ i ∈ (Finset.univ : Finset (Fin n)), (y i) ^ 2) ^ 2 := by
      congr 1
    _ ≤ ((Finset.univ : Finset (Fin n)).card : ℝ)
          * ∑ i ∈ (Finset.univ : Finset (Fin n)), ((y i) ^ 2) ^ 2 := hCS
    _ = (n : ℝ) * ∑ i : Fin n, (y i) ^ 4 := by
      congr 1
      · simp
      · simp
        apply Finset.sum_congr rfl
        intro i hi
        ring

/-- inner product with a basis vector is the coordinate. -/
lemma vin_basis_right (n : ℕ) (i : Fin n) (x : Vec n) : vin x (basis n i) = x i := by
  have hc := real_inner_comm x (basis n i)
  have hb := vin_basis n i x
  simpa [vin] using hc.symm.trans hb

/-- Norm of a standard basis vector is one. -/
lemma norm_basis (n : ℕ) (i : Fin n) : ‖basis n i‖ = 1 := by
  have hsq : ‖basis n i‖ ^ 2 = 1 := by
    rw [norm_sq_sum]
    have hb : ∀ j : Fin n, ((basis n i) j) ^ 2 = if j = i then 1 else 0 := by
      intro j
      by_cases hj : j = i
      · rw [hj]
        simp [basis, EuclideanSpace.single]
      · have hne : j ≠ i := hj
        simp [basis, EuclideanSpace.single, hne]
    calc
      (∑ j : Fin n, ((basis n i) j) ^ 2) = ∑ j : Fin n, if j = i then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hb j]
      _ = 1 := by simp
  exact sq_eq_of_nonneg (norm_nonneg _) zero_le_one (by simpa using hsq)

/-- Real integral of a nonnegative function is bounded by `B` given the lintegral bound. -/
lemma real_int_le_of_lin {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} {B : ℝ}
    (hf : Measurable f) (hnonneg : 0 ≤ᵐ[μ] f)
    (hB : 0 ≤ B) (hlin : (∫⁻ a, ENNReal.ofReal (f a) ∂μ) ≤ ENNReal.ofReal B) :
    (∫ a, f a ∂μ) ≤ B := by
  have hmeas : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnonneg hmeas]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin).trans (by
    rw [ENNReal.toReal_ofReal hB])

/-- lintegral coordinate bound: ∫⁻ ofReal X_i⁴ ≤ ofReal 361. -/
lemma coord4_lin_bound {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (hx0 : ∀ i : Fin n, |x0 i| ≤ 1)
    (hK : γ ^ 2 * (T : ℝ) ≤ 6) (i : Fin n) :
    (∫⁻ ω : Omega n T, ENNReal.ofReal ((Xn n T δ γ x0 v c ω T i) ^ 4) ∂(mu n T)) ≤
      ENNReal.ofReal 361 := by
  have hd := dir4_lin (n := n) (ι := ι) (T := T) δ γ x0 v c (basis n i)
  have hswap : (∫⁻ ω : Omega n T, ENNReal.ofReal ((Xn n T δ γ x0 v c ω T i) ^ 4) ∂(mu n T))
      = ∫⁻ ω : Omega n T, ENNReal.ofReal ((vin (Xn n T δ γ x0 v c ω T) (basis n i)) ^ 4)
        ∂(mu n T) := by
    congr 1
    funext ω
    congr 1
    rw [vin_basis_right n i (Xn n T δ γ x0 v c ω T)]
  have hx : |x0 i| ≤ 1 := hx0 i
  have hx2 : (x0 i) ^ 2 ≤ 1 := by
    have hsq := pow_le_pow_left₀ (abs_nonneg (x0 i)) hx 2
    simpa [sq_abs] using hsq
  have hA0 : 0 ≤ (x0 i) ^ 2 + 3 * γ ^ 2 * (T : ℝ) := by
    have hT : 0 ≤ (T : ℝ) := by exact_mod_cast Nat.zero_le T
    nlinarith [sq_nonneg (x0 i), sq_nonneg γ]
  have hA19 : (x0 i) ^ 2 + 3 * γ ^ 2 * (T : ℝ) ≤ 19 := by
    have hT : 0 ≤ (T : ℝ) := by exact_mod_cast Nat.zero_le T
    nlinarith [hK]
  have hb : (((x0 i) ^ 2 + 3 * γ ^ 2 * (T : ℝ)) ^ 2) ≤ 361 := by
    have hsq := pow_le_pow_left₀ hA0 hA19 2
    norm_num at hsq ⊢
    exact hsq
  calc
    (∫⁻ ω : Omega n T, ENNReal.ofReal ((Xn n T δ γ x0 v c ω T i) ^ 4) ∂(mu n T))
        = ∫⁻ ω : Omega n T, ENNReal.ofReal ((vin (Xn n T δ γ x0 v c ω T) (basis n i)) ^ 4)
            ∂(mu n T) := hswap
    _ ≤ ENNReal.ofReal ((vin x0 (basis n i)) ^ 2 + 3 * γ ^ 2 * ‖basis n i‖ ^ 2 * (T : ℝ)) ^ 2 := hd
    _ = ENNReal.ofReal (((x0 i) ^ 2 + 3 * γ ^ 2 * (T : ℝ)) ^ 2) := by
            have hT : 0 ≤ (T : ℝ) := by exact_mod_cast Nat.zero_le T
            have hX0 : 0 ≤ (vin x0 (basis n i)) ^ 2 + 3 * γ ^ 2 * ‖basis n i‖ ^ 2 * (T : ℝ) := by
              have hA' : 0 ≤ 3 * γ ^ 2 * ‖basis n i‖ ^ 2 * (T : ℝ) := by
                exact mul_nonneg (by positivity : 0 ≤ 3 * γ ^ 2 * ‖basis n i‖ ^ 2) hT
              nlinarith [sq_nonneg (vin x0 (basis n i))]
            rw [← ENNReal.ofReal_pow hX0]
            congr 1
            rw [vin_basis_right n i x0]
            rw [norm_basis n i]
            ring
    _ ≤ ENNReal.ofReal 361 := by
            exact ENNReal.ofReal_le_ofReal hb

/-- E‖X_T‖⁴ ≤ 900 n². -/
lemma exp_fourth_moment_bound {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (hx0 : ∀ i : Fin n, |x0 i| ≤ 1)
    (hK : γ ^ 2 * (T : ℝ) ≤ 6) :
    (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T‖ ^ 4 ∂(mu n T)) ≤ 900 * (n : ℝ) ^ 2 := by
  have hpt : ∀ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T‖ ^ 4
      ≤ (n : ℝ) * ∑ i : Fin n, (Xn n T δ γ x0 v c ω T i) ^ 4 := by
    intro ω
    exact norm4_le_mul_sum (Xn n T δ γ x0 v c ω T)
  have hmeasX : Measurable (fun ω : Omega n T => ‖Xn n T δ γ x0 v c ω T‖ ^ 4) := by
    exact (continuous_pow 4).measurable.comp ((measurable_norm n).comp
      (measurable_Xn (n := n) (ι := ι) (T := T) (t := T) le_rfl δ γ x0 v c))
  apply real_int_le_of_lin hmeasX
  · exact ae_of_all _ (fun ω => by positivity)
  · positivity
  · -- the lintegral bound
    have hcoord : ∀ i : Fin n, Measurable (fun ω : Omega n T =>
        ENNReal.ofReal ((Xn n T δ γ x0 v c ω T i) ^ 4)) := by
      intro i
      exact ENNReal.measurable_ofReal.comp ((continuous_pow 4).measurable.comp
        ((measurable_coord n i).comp (measurable_Xn (n := n) (ι := ι) (T := T) (t := T) le_rfl δ γ x0 v c)))
    have hsumMeas : Measurable (fun ω : Omega n T =>
        ∑ i : Fin n, ENNReal.ofReal ((Xn n T δ γ x0 v c ω T i) ^ 4)) := by
      -- a finite sum of measurable functions is measurable
      refine Finset.measurable_sum (Finset.univ : Finset (Fin n)) ?_
      intro i hi
      exact hcoord i
    have hbnd : (fun ω : Omega n T => ENNReal.ofReal (‖Xn n T δ γ x0 v c ω T‖ ^ 4))
        ≤ fun ω : Omega n T => ENNReal.ofReal ((n : ℝ) * ∑ i : Fin n, (Xn n T δ γ x0 v c ω T i) ^ 4) := by
      intro ω
      exact ENNReal.ofReal_le_ofReal (hpt ω)
    calc
      (∫⁻ ω : Omega n T, ENNReal.ofReal (‖Xn n T δ γ x0 v c ω T‖ ^ 4) ∂(mu n T))
          ≤ ∫⁻ ω : Omega n T, ENNReal.ofReal ((n : ℝ) * ∑ i : Fin n, (Xn n T δ γ x0 v c ω T i) ^ 4) ∂(mu n T) := by
              exact lintegral_mono hbnd
      _ = ∫⁻ ω : Omega n T, ENNReal.ofReal (n : ℝ) *
            (∑ i : Fin n, ENNReal.ofReal ((Xn n T δ γ x0 v c ω T i) ^ 4)) ∂(mu n T) := by
              congr 1
              funext ω
              rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (n : ℝ))]
              congr 1
              exact ofReal_sum_univ (fun i => (Xn n T δ γ x0 v c ω T i) ^ 4) (fun i => by positivity)
      _ = ENNReal.ofReal (n : ℝ) * ∫⁻ ω : Omega n T,
            (∑ i : Fin n, ENNReal.ofReal ((Xn n T δ γ x0 v c ω T i) ^ 4)) ∂(mu n T) := by
              rw [lintegral_const_mul (ENNReal.ofReal (n : ℝ)) hsumMeas]
      _ = ENNReal.ofReal (n : ℝ) * ∑ i : Fin n,
            ∫⁻ ω : Omega n T, ENNReal.ofReal ((Xn n T δ γ x0 v c ω T i) ^ 4) ∂(mu n T) := by
              congr 1
              have hls := lintegral_finset_sum (μ := (mu n T)) (Finset.univ : Finset (Fin n))
                (f := fun (b : Fin n) (ω : Omega n T) => ENNReal.ofReal ((Xn n T δ γ x0 v c ω T b) ^ 4))
                (by intro b hb; exact hcoord b)
              simpa using hls
      _ ≤ ENNReal.ofReal (n : ℝ) * ∑ i : Fin n, ENNReal.ofReal 361 := by
              have hsum : (∑ i : Fin n,
                  ∫⁻ ω : Omega n T, ENNReal.ofReal ((Xn n T δ γ x0 v c ω T i) ^ 4) ∂(mu n T))
                  ≤ ∑ i : Fin n, ENNReal.ofReal 361 := by
                exact Finset.sum_le_sum (by
                  intro i hi
                  exact coord4_lin_bound (n := n) (ι := ι) (T := T) δ γ x0 v c hx0 hK i)
              exact mul_le_mul_right hsum (ENNReal.ofReal (n : ℝ))
      _ = ENNReal.ofReal (n : ℝ) * ENNReal.ofReal (361 * (n : ℝ)) := by
              congr 1
              have hs := ofReal_sum_univ (fun _ : Fin n => (361 : ℝ)) (fun i => by norm_num)
              rw [← hs]
              congr 1
              simp [Finset.sum_const, nsmul_eq_mul]
              ring
      _ = ENNReal.ofReal ((n : ℝ) * (361 * (n : ℝ))) := by
              rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (n : ℝ))]
      _ = ENNReal.ofReal (361 * (n : ℝ) ^ 2) := by
              congr 1
              ring
      _ ≤ ENNReal.ofReal (900 * (n : ℝ) ^ 2) := by
              apply ENNReal.ofReal_le_ofReal
              have hsq : 0 ≤ (n : ℝ) ^ 2 := sq_nonneg (n : ℝ)
              nlinarith

end Discrepancy
