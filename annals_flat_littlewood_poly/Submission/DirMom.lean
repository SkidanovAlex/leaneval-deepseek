import Mathlib
import Submission.F_gauss
import Submission.LMProbs
import Submission.LMMeas
import Submission.VecGauss2
import Submission.VecGauss4

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory

noncomputable section
open Classical

namespace Submission.Discrepancy

lemma vin_add_right (n : ℕ) (a b w : Vec n) : vin (a + b) w = vin a w + vin b w := by
  simp [vin, inner_add_left]

lemma vin_smul_right (n : ℕ) (γ : ℝ) (a w : Vec n) : vin (γ • a) w = γ * vin a w := by
  simp [vin, inner_smul_left]

/-- The value of the walk in direction `w` at the appended point. -/
lemma app_val {n : ℕ} {ι : Type*} [Fintype ι] (T' : ℕ) (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (g : Vec n) (p : Omega n T') (w : Vec n) :
    vin (Xn n (T' + 1) δ γ x0 v c (Fin.snoc (α := fun _ : Fin (T' + 1) => Vec n) p g) (T' + 1)) w
      = vin (Xn n T' δ γ x0 v c p T') w
        + γ * vin g (walkProj v (frozenVars δ (Xn n T' δ γ x0 v c p T'))
            (frozenRows δ x0 v c (Xn n T' δ γ x0 v c p T')) w) := by
  rw [last_step (n := n) (T' := T') δ γ x0 v c g p]
  rw [vin_add_right, vin_smul_right]
  rw [proj_adjoint (n := n) (v := v)
    (A := frozenVars δ (Xn n T' δ γ x0 v c p T'))
    (B := frozenRows δ x0 v c (Xn n T' δ γ x0 v c p T')) g w]

/-- power of a real-valued measurable function is measurable -/
lemma measurable_rpow_const {α : Type*} [MeasurableSpace α] {f : α → ℝ} (hf : Measurable f)
    (k : ℕ) : Measurable (fun x : α => (f x) ^ k) :=
  (continuous_pow k).measurable.comp hf

/-- Measurability of the (appended) integrand in (g, p), power k. -/
lemma measurable_app_k {ι : Type*} [Fintype ι] (n T' : ℕ) (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (w : Vec n) (k : ℕ) :
    Measurable (fun y : Vec n × Omega n T' =>
      ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c (Fin.snoc y.2 y.1) (T' + 1)) w) ^ k)) := by
  have hm1 : Measurable (fun y : Vec n × Omega n T' =>
      Xn n (T' + 1) δ γ x0 v c (Fin.snoc y.2 y.1) (T' + 1)) :=
    (measurable_Xn (n := n) (ι := ι) (T := T' + 1) (t := T' + 1) le_rfl δ γ x0 v c).comp
      (continuous_snoc_curry n T').measurable
  have hm2 : Measurable (fun y : Vec n × Omega n T' =>
      (vin (Xn n (T' + 1) δ γ x0 v c (Fin.snoc y.2 y.1) (T' + 1)) w) ^ k) :=
    measurable_rpow_const ((measurable_vin n w).comp hm1) k
  exact ENNReal.measurable_ofReal.comp hm2

/-- Measurability of (vin (Xn T' p T') w)^k in p. -/
lemma measurable_dir_k {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (w : Vec n) (k : ℕ) :
    Measurable (fun p : Omega n T =>
      ENNReal.ofReal ((vin (Xn n T δ γ x0 v c p T) w) ^ k)) := by
  have hm2 : Measurable (fun p : Omega n T => (vin (Xn n T δ γ x0 v c p T) w) ^ k) :=
    measurable_rpow_const ((measurable_vin n w).comp
      (measurable_Xn (n := n) (ι := ι) (T := T) (t := T) le_rfl δ γ x0 v c)) k
  exact ENNReal.measurable_ofReal.comp hm2

/-- Direction second moment, lintegral. -/
lemma dir2_lin {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (w : Vec n) :
    (∫⁻ ω : Omega n T, ENNReal.ofReal ((vin (Xn n T δ γ x0 v c ω T) w) ^ 2) ∂(mu n T)) ≤
      ENNReal.ofReal ((vin x0 w) ^ 2 + γ ^ 2 * ‖w‖ ^ 2 * (T : ℝ)) := by
  induction T with
  | zero =>
      have hfun : (fun ω : Omega n 0 =>
          ENNReal.ofReal ((vin (Xn n 0 δ γ x0 v c ω 0) w) ^ 2)) = fun _ : Omega n 0 =>
          ENNReal.ofReal ((vin x0 w) ^ 2) := by
        funext ω
        simp [Xn]
      rw [hfun]
      simp
  | succ T' ih2 =>
      let a0 := (vin x0 w) ^ 2
      let c2 := γ ^ 2 * ‖w‖ ^ 2
      -- LHS = iterated integral over last Gaussian then past
      have hpeel :
          (∫⁻ ω : Omega n (T' + 1), ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c ω (T' + 1)) w) ^ 2) ∂(mu n (T' + 1)))
            = ∫⁻ g : Vec n, ∫⁻ p : Omega n T',
                ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c (Fin.snoc p g) (T' + 1)) w) ^ 2)
                ∂(mu n T') ∂(stdGaussian (Vec n)) := by
          have hfun : (fun ω : Omega n (T' + 1) =>
              ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c ω (T' + 1)) w) ^ 2))
            = fun ω : Omega n (T' + 1) =>
              ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c
                (Fin.snoc (Fin.init ω) (ω (Fin.last T'))) (T' + 1)) w) ^ 2) := by
            funext ω
            congr 1
            congr 1
            rw [Fin.snoc_init_self ω]
          rw [hfun]
          exact lintegral_snoc_form (n := n) (T := T') (F := fun g : Vec n => fun p : Omega n T' =>
            ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c (Fin.snoc p g) (T' + 1)) w) ^ 2))
            (by
              -- hmeas : Measurable (fun y : Vec n × Omega n T' => F y.1 y.2)
              exact measurable_app_k (n := n) (ι := ι) (T' := T') δ γ x0 v c w 2)
      -- swap to integrate g first inside p
      have hswap :
          (∫⁻ g : Vec n, ∫⁻ p : Omega n T',
              ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c (Fin.snoc p g) (T' + 1)) w) ^ 2)
              ∂(mu n T') ∂(stdGaussian (Vec n)))
          = ∫⁻ p : Omega n T', ∫⁻ g : Vec n,
              ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c (Fin.snoc p g) (T' + 1)) w) ^ 2)
              ∂(stdGaussian (Vec n)) ∂(mu n T') := by
          let F : Vec n → Omega n T' → ℝ≥0∞ := fun g p =>
            ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c (Fin.snoc p g) (T' + 1)) w) ^ 2)
          have hmeas : AEMeasurable (fun z : Vec n × Omega n T' => F z.1 z.2)
              ((stdGaussian (Vec n)).prod (mu n T')) :=
            (measurable_app_k (n := n) (ι := ι) (T' := T') δ γ x0 v c w 2).aemeasurable
          simpa [F] using (lintegral_lintegral_swap (μ := (stdGaussian (Vec n))) (ν := mu n T')
            (f := F) hmeas)
      rw [hpeel, hswap]
      -- pointwise-in-p bound of the inner g integral
      have hbnd : (fun p : Omega n T' =>
          ∫⁻ g : Vec n, ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c (Fin.snoc p g) (T' + 1)) w) ^ 2)
            ∂(stdGaussian (Vec n)))
        ≤ fun p : Omega n T' =>
          ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 2 + c2) := by
        intro p
        let A := vin (Xn n T' δ γ x0 v c p T') w
        let u := walkProj v (frozenVars δ (Xn n T' δ γ x0 v c p T'))
          (frozenRows δ x0 v c (Xn n T' δ γ x0 v c p T')) w
        have hnorm : ‖u‖ ≤ ‖w‖ := by
          exact proj_norm_le (v := v)
            (A := frozenVars δ (Xn n T' δ γ x0 v c p T'))
            (B := frozenRows δ x0 v c (Xn n T' δ γ x0 v c p T')) w
        calc
          (∫⁻ g : Vec n, ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c (Fin.snoc p g) (T' + 1)) w) ^ 2)
              ∂(stdGaussian (Vec n)))
              = ∫⁻ g : Vec n, ENNReal.ofReal ((A + γ * vin g u) ^ 2) ∂(stdGaussian (Vec n)) := by
                  congr 1
                  funext g
                  congr 1
                  rw [app_val (n := n) (T' := T') δ γ x0 v c g p w]
          _ = ENNReal.ofReal (A ^ 2 + γ ^ 2 * ‖u‖ ^ 2) := gauss_quad_lin (n := n) A γ u
          _ ≤ ENNReal.ofReal (A ^ 2 + γ ^ 2 * ‖w‖ ^ 2) := by
                  apply ENNReal.ofReal_le_ofReal
                  have hsq : ‖u‖ ^ 2 ≤ ‖w‖ ^ 2 := by
                    simpa [pow_two] using mul_self_le_mul_self (norm_nonneg u) hnorm
                  nlinarith
          _ = ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 2 + c2) := by
                  rfl
      -- integrate the bound over p
      have hmono : (∫⁻ p : Omega n T', ∫⁻ g : Vec n,
            ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c (Fin.snoc p g) (T' + 1)) w) ^ 2)
            ∂(stdGaussian (Vec n)) ∂(mu n T'))
        ≤ ∫⁻ p : Omega n T', ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 2 + c2) ∂(mu n T') := by
        exact lintegral_mono hbnd
      refine le_trans hmono ?_
      -- split constant
      have hsplit : (fun p : Omega n T' =>
          ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 2 + c2))
        = fun p : Omega n T' =>
          ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 2) + ENNReal.ofReal c2 := by
        funext p
        rw [ENNReal.ofReal_add (sq_nonneg _) (mul_nonneg (sq_nonneg γ) (sq_nonneg ‖w‖))]
      rw [hsplit]
      have h1 : Measurable (fun p : Omega n T' =>
          ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 2)) :=
        measurable_dir_k (n := n) (ι := ι) (T := T') δ γ x0 v c w 2
      have h2 : Measurable (fun p : Omega n T' => ENNReal.ofReal c2) := by
        fun_prop
      calc
        (∫⁻ p : Omega n T',
            ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 2) + ENNReal.ofReal c2 ∂(mu n T'))
          = (∫⁻ p : Omega n T', ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 2) ∂(mu n T'))
            + ∫⁻ p : Omega n T', ENNReal.ofReal c2 ∂(mu n T') := by
              simpa [Pi.add_apply] using (lintegral_add_left h1 (fun _ : Omega n T' => ENNReal.ofReal c2))
        _ ≤ ENNReal.ofReal (a0 + c2 * (T' : ℝ)) + ENNReal.ofReal c2 := by
              refine add_le_add ih2 ?_
              rw [lintegral_const]
              simp [h2]
        _ = ENNReal.ofReal (a0 + c2 * (T' : ℝ) + c2) := by
              have hp : 0 ≤ a0 + c2 * (T' : ℝ) := by
                have hT' : 0 ≤ (T' : ℝ) := by exact_mod_cast Nat.zero_le T'
                have hc2 : 0 ≤ c2 := by unfold c2; positivity
                nlinarith [sq_nonneg (vin x0 w), hc2]
              have hq : 0 ≤ c2 := by unfold c2; positivity
              rw [ENNReal.ofReal_add hp hq]
        _ = ENNReal.ofReal (a0 + c2 * (T' + 1 : ℝ)) := by
              congr 1
              ring
        _ = ENNReal.ofReal ((vin x0 w) ^ 2 + γ ^ 2 * ‖w‖ ^ 2 * ((T' + 1 : ℕ) : ℝ)) := by
              congr 1
              rw [Nat.cast_add, Nat.cast_one]
/-- Direction fourth moment, lintegral. -/
lemma dir4_lin {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (w : Vec n) :
    (∫⁻ ω : Omega n T, ENNReal.ofReal ((vin (Xn n T δ γ x0 v c ω T) w) ^ 4) ∂(mu n T)) ≤
      ENNReal.ofReal ((vin x0 w) ^ 2 + 3 * γ ^ 2 * ‖w‖ ^ 2 * (T : ℝ)) ^ 2 := by
  induction T with
  | zero =>
      have hfun : (fun ω : Omega n 0 =>
          ENNReal.ofReal ((vin (Xn n 0 δ γ x0 v c ω 0) w) ^ 4)) = fun _ : Omega n 0 =>
          ENNReal.ofReal ((vin x0 w) ^ 4) := by
        funext ω
        simp [Xn]
      rw [hfun]
      rw [lintegral_const]
      simp
      have hp : 0 ≤ (vin x0 w) ^ 2 := sq_nonneg _
      rw [← ENNReal.ofReal_pow hp]
      have hz : (vin x0 w) ^ 4 = ((vin x0 w) ^ 2) ^ 2 := by ring
      rw [hz]
  | succ T' ih4 =>
      let a0 := (vin x0 w) ^ 2
      let cc := 3 * γ ^ 2 * ‖w‖ ^ 2
      let c1 := 6 * γ ^ 2 * ‖w‖ ^ 2
      let c3 := 3 * γ ^ 4 * ‖w‖ ^ 4
      have hpeel :
          (∫⁻ ω : Omega n (T' + 1), ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c ω (T' + 1)) w) ^ 4) ∂(mu n (T' + 1)))
            = ∫⁻ g : Vec n, ∫⁻ p : Omega n T',
                ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c (Fin.snoc p g) (T' + 1)) w) ^ 4)
                ∂(mu n T') ∂(stdGaussian (Vec n)) := by
          have hfun : (fun ω : Omega n (T' + 1) =>
              ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c ω (T' + 1)) w) ^ 4))
            = fun ω : Omega n (T' + 1) =>
              ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c
                (Fin.snoc (Fin.init ω) (ω (Fin.last T'))) (T' + 1)) w) ^ 4) := by
            funext ω
            congr 1
            congr 1
            rw [Fin.snoc_init_self ω]
          rw [hfun]
          exact lintegral_snoc_form (n := n) (T := T') (F := fun g : Vec n => fun p : Omega n T' =>
            ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c (Fin.snoc p g) (T' + 1)) w) ^ 4))
            (by
              exact measurable_app_k (n := n) (ι := ι) (T' := T') δ γ x0 v c w 4)
      have hswap :
          (∫⁻ g : Vec n, ∫⁻ p : Omega n T',
              ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c (Fin.snoc p g) (T' + 1)) w) ^ 4)
              ∂(mu n T') ∂(stdGaussian (Vec n)))
          = ∫⁻ p : Omega n T', ∫⁻ g : Vec n,
              ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c (Fin.snoc p g) (T' + 1)) w) ^ 4)
              ∂(stdGaussian (Vec n)) ∂(mu n T') := by
          let F : Vec n → Omega n T' → ℝ≥0∞ := fun g p =>
            ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c (Fin.snoc p g) (T' + 1)) w) ^ 4)
          have hmeas : AEMeasurable (fun z : Vec n × Omega n T' => F z.1 z.2)
              ((stdGaussian (Vec n)).prod (mu n T')) :=
            (measurable_app_k (n := n) (ι := ι) (T' := T') δ γ x0 v c w 4).aemeasurable
          simpa [F] using (lintegral_lintegral_swap (μ := (stdGaussian (Vec n))) (ν := mu n T')
            (f := F) hmeas)
      rw [hpeel, hswap]
      have hbnd : (fun p : Omega n T' =>
          ∫⁻ g : Vec n, ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c (Fin.snoc p g) (T' + 1)) w) ^ 4)
            ∂(stdGaussian (Vec n)))
        ≤ fun p : Omega n T' =>
          ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 4 + c1 * (vin (Xn n T' δ γ x0 v c p T') w) ^ 2 + c3) := by
        intro p
        let A := vin (Xn n T' δ γ x0 v c p T') w
        let u := walkProj v (frozenVars δ (Xn n T' δ γ x0 v c p T'))
          (frozenRows δ x0 v c (Xn n T' δ γ x0 v c p T')) w
        have hnorm : ‖u‖ ≤ ‖w‖ := by
          exact proj_norm_le (v := v)
            (A := frozenVars δ (Xn n T' δ γ x0 v c p T'))
            (B := frozenRows δ x0 v c (Xn n T' δ γ x0 v c p T')) w
        calc
          (∫⁻ g : Vec n, ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c (Fin.snoc p g) (T' + 1)) w) ^ 4)
              ∂(stdGaussian (Vec n)))
              = ∫⁻ g : Vec n, ENNReal.ofReal ((A + γ * vin g u) ^ 4) ∂(stdGaussian (Vec n)) := by
                  congr 1
                  funext g
                  congr 1
                  rw [app_val (n := n) (T' := T') δ γ x0 v c g p w]
          _ = ENNReal.ofReal (A ^ 4 + 6 * A ^ 2 * γ ^ 2 * ‖u‖ ^ 2 + 3 * γ ^ 4 * ‖u‖ ^ 4) :=
                  gauss_quartic_lin (n := n) A γ u
          _ ≤ ENNReal.ofReal (A ^ 4 + 6 * A ^ 2 * γ ^ 2 * ‖w‖ ^ 2 + 3 * γ ^ 4 * ‖w‖ ^ 4) := by
                  apply ENNReal.ofReal_le_ofReal
                  have hsq : ‖u‖ ^ 2 ≤ ‖w‖ ^ 2 := by
                    simpa [pow_two] using mul_self_le_mul_self (norm_nonneg u) hnorm
                  have h6 : 6 * A ^ 2 * γ ^ 2 * ‖u‖ ^ 2 ≤ 6 * A ^ 2 * γ ^ 2 * ‖w‖ ^ 2 := by
                    exact mul_le_mul_of_nonneg_left hsq (by positivity)
                  have hsq4 : ‖u‖ ^ 4 ≤ ‖w‖ ^ 4 := by
                    have hm : ‖u‖ ^ 2 * ‖u‖ ^ 2 ≤ ‖w‖ ^ 2 * ‖w‖ ^ 2 :=
                      mul_le_mul hsq hsq (sq_nonneg ‖u‖) (sq_nonneg ‖w‖)
                    calc
                      ‖u‖ ^ 4 = ‖u‖ ^ 2 * ‖u‖ ^ 2 := by ring
                      _ ≤ ‖w‖ ^ 2 * ‖w‖ ^ 2 := hm
                      _ = ‖w‖ ^ 4 := by ring
                  have h3 : 3 * γ ^ 4 * ‖u‖ ^ 4 ≤ 3 * γ ^ 4 * ‖w‖ ^ 4 := by
                    exact mul_le_mul_of_nonneg_left hsq4 (by positivity)
                  linarith
          _ = ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 4 + c1 * (vin (Xn n T' δ γ x0 v c p T') w) ^ 2 + c3) := by
                  congr 1
                  dsimp [A, c1, c3]
                  ring
      have hmono : (∫⁻ p : Omega n T', ∫⁻ g : Vec n,
            ENNReal.ofReal ((vin (Xn n (T' + 1) δ γ x0 v c (Fin.snoc p g) (T' + 1)) w) ^ 4)
            ∂(stdGaussian (Vec n)) ∂(mu n T'))
        ≤ ∫⁻ p : Omega n T',
            ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 4 + c1 * (vin (Xn n T' δ γ x0 v c p T') w) ^ 2 + c3)
            ∂(mu n T') := by
        exact lintegral_mono hbnd
      refine le_trans hmono ?_
      have hsplit : (fun p : Omega n T' =>
          ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 4 + c1 * (vin (Xn n T' δ γ x0 v c p T') w) ^ 2 + c3))
        = fun p : Omega n T' =>
          ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 4)
            + ENNReal.ofReal (c1 * (vin (Xn n T' δ γ x0 v c p T') w) ^ 2)
            + ENNReal.ofReal c3 := by
        funext p
        have h1 : 0 ≤ (vin (Xn n T' δ γ x0 v c p T') w) ^ 4 := by positivity
        have h2 : 0 ≤ c1 * (vin (Xn n T' δ γ x0 v c p T') w) ^ 2 := by positivity
        have h3 : 0 ≤ c3 := by unfold c3; positivity
        rw [ENNReal.ofReal_add (by positivity : 0 ≤ (vin (Xn n T' δ γ x0 v c p T') w) ^ 4
          + c1 * (vin (Xn n T' δ γ x0 v c p T') w) ^ 2) h3]
        rw [ENNReal.ofReal_add h1 h2]
      rw [hsplit]
      have hA4 : Measurable (fun p : Omega n T' =>
          ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 4)) :=
        measurable_dir_k (n := n) (ι := ι) (T := T') δ γ x0 v c w 4
      have hA2raw : Measurable (fun p : Omega n T' => (vin (Xn n T' δ γ x0 v c p T') w) ^ 2) :=
        measurable_rpow_const ((measurable_vin n w).comp
          (measurable_Xn (n := n) (ι := ι) (T := T') (t := T') le_rfl δ γ x0 v c)) 2
      have hg1 : Measurable (fun p : Omega n T' =>
          ENNReal.ofReal (c1 * (vin (Xn n T' δ γ x0 v c p T') w) ^ 2)) := by
        have hc : Continuous (fun x : ℝ => ENNReal.ofReal (c1 * x)) := by
          exact ENNReal.continuous_ofReal.comp (continuous_const.mul continuous_id)
        exact hc.measurable.comp hA2raw
      have hC : Measurable (fun p : Omega n T' => ENNReal.ofReal c3) := by fun_prop
      calc
        (∫⁻ p : Omega n T',
            ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 4)
              + ENNReal.ofReal (c1 * (vin (Xn n T' δ γ x0 v c p T') w) ^ 2)
              + ENNReal.ofReal c3 ∂(mu n T'))
          = (∫⁻ p : Omega n T', ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 4)
              + ENNReal.ofReal (c1 * (vin (Xn n T' δ γ x0 v c p T') w) ^ 2) ∂(mu n T'))
            + ∫⁻ p : Omega n T', ENNReal.ofReal c3 ∂(mu n T') := by
              simpa [Pi.add_apply] using (lintegral_add_left (hA4.add hg1)
                (fun _ : Omega n T' => ENNReal.ofReal c3))
        _ = (∫⁻ p : Omega n T', ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 4) ∂(mu n T')
              + ∫⁻ p : Omega n T', ENNReal.ofReal (c1 * (vin (Xn n T' δ γ x0 v c p T') w) ^ 2) ∂(mu n T'))
            + ∫⁻ p : Omega n T', ENNReal.ofReal c3 ∂(mu n T') := by
              simpa [Pi.add_apply] using (lintegral_add_left hA4
                (fun p : Omega n T' => ENNReal.ofReal (c1 * (vin (Xn n T' δ γ x0 v c p T') w) ^ 2)))
        _ ≤ ENNReal.ofReal ((a0 + cc * (T' : ℝ)) ^ 2)
            + ENNReal.ofReal (c1 * (a0 + cc * (T' : ℝ)))
            + ENNReal.ofReal c3 := by
              have hf4 : (∫⁻ p : Omega n T', ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 4) ∂(mu n T'))
                  ≤ ENNReal.ofReal ((a0 + cc * (T' : ℝ)) ^ 2) := by
                have hT' : 0 ≤ (T' : ℝ) := by exact_mod_cast Nat.zero_le T'
                have hX : 0 ≤ (vin x0 w) ^ 2 + 3 * γ ^ 2 * ‖w‖ ^ 2 * (T' : ℝ) := by
                  have hB : 0 ≤ 3 * γ ^ 2 * ‖w‖ ^ 2 * (T' : ℝ) := by positivity
                  nlinarith [sq_nonneg (vin x0 w), hB]
                have hih := ih4
                rw [← ENNReal.ofReal_pow hX] at hih
                simpa [a0, cc] using hih
              have hsq2 : (∫⁻ p : Omega n T', ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 2) ∂(mu n T'))
                  ≤ ENNReal.ofReal (a0 + cc * (T' : ℝ)) := by
                have hsq2' := dir2_lin (n := n) (ι := ι) (T := T') δ γ x0 v c w
                have hle : (vin x0 w) ^ 2 + γ ^ 2 * ‖w‖ ^ 2 * (T' : ℝ) ≤ (vin x0 w) ^ 2 + 3 * γ ^ 2 * ‖w‖ ^ 2 * (T' : ℝ) := by
                  have hT : 0 ≤ (T' : ℝ) := by exact_mod_cast Nat.zero_le T'
                  have hA : 0 ≤ γ ^ 2 * ‖w‖ ^ 2 := by positivity
                  have hm : γ ^ 2 * ‖w‖ ^ 2 * (T' : ℝ) ≤ 3 * γ ^ 2 * ‖w‖ ^ 2 * (T' : ℝ) := by
                    calc
                      γ ^ 2 * ‖w‖ ^ 2 * (T' : ℝ) = (γ ^ 2 * ‖w‖ ^ 2) * (T' : ℝ) := by ring
                      _ ≤ (γ ^ 2 * ‖w‖ ^ 2) * (3 * (T' : ℝ)) := mul_le_mul_of_nonneg_left (by nlinarith [hT]) hA
                      _ = 3 * γ ^ 2 * ‖w‖ ^ 2 * (T' : ℝ) := by ring
                  linarith
                exact le_trans hsq2' (by simpa [a0, cc] using (ENNReal.ofReal_le_ofReal hle))
              have hgc1 : (∫⁻ p : Omega n T', ENNReal.ofReal (c1 * (vin (Xn n T' δ γ x0 v c p T') w) ^ 2) ∂(mu n T'))
                  ≤ ENNReal.ofReal (c1 * (a0 + cc * (T' : ℝ))) := by
                have hc1 : 0 ≤ c1 := by unfold c1; positivity
                calc
                  (∫⁻ p : Omega n T', ENNReal.ofReal (c1 * (vin (Xn n T' δ γ x0 v c p T') w) ^ 2) ∂(mu n T'))
                    = ENNReal.ofReal c1 * (∫⁻ p : Omega n T', ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 2) ∂(mu n T')) := by
                        rw [show (fun p : Omega n T' =>
                          ENNReal.ofReal (c1 * (vin (Xn n T' δ γ x0 v c p T') w) ^ 2))
                          = fun p : Omega n T' =>
                          ENNReal.ofReal c1 * ENNReal.ofReal ((vin (Xn n T' δ γ x0 v c p T') w) ^ 2) by
                          funext p
                          rw [ENNReal.ofReal_mul hc1]]
                        rw [lintegral_const_mul (ENNReal.ofReal c1)
                          (by exact measurable_dir_k (n := n) (ι := ι) (T := T') δ γ x0 v c w 2)]
                    _ ≤ ENNReal.ofReal c1 * ENNReal.ofReal (a0 + cc * (T' : ℝ)) := by
                        exact mul_le_mul_of_nonneg_left hsq2 (by positivity : 0 ≤ ENNReal.ofReal c1)
                    _ = ENNReal.ofReal (c1 * (a0 + cc * (T' : ℝ))) := by
                        rw [← ENNReal.ofReal_mul hc1]
              have hcconst : (∫⁻ p : Omega n T', ENNReal.ofReal c3 ∂(mu n T')) ≤ ENNReal.ofReal c3 := by
                rw [lintegral_const]
                simp
              exact add_le_add (add_le_add hf4 hgc1) hcconst
        _ = ENNReal.ofReal ((a0 + cc * (T' : ℝ)) ^ 2 + c1 * (a0 + cc * (T' : ℝ)) + c3) := by
              have hx : 0 ≤ (a0 + cc * (T' : ℝ)) ^ 2 := by positivity
              have hz : 0 ≤ a0 + cc * (T' : ℝ) := by
                have hT : 0 ≤ (T' : ℝ) := by exact_mod_cast Nat.zero_le T'
                have hcc : 0 ≤ cc := by unfold cc; positivity
                have ha0 : 0 ≤ a0 := by unfold a0; positivity
                have hcT : 0 ≤ cc * (T' : ℝ) := mul_nonneg hcc hT
                linarith
              have hy : 0 ≤ c1 * (a0 + cc * (T' : ℝ)) := by
                have hc1 : 0 ≤ c1 := by unfold c1; positivity
                exact mul_nonneg hc1 hz
              have hc3 : 0 ≤ c3 := by unfold c3; positivity
              have hxy : 0 ≤ (a0 + cc * (T' : ℝ)) ^ 2 + c1 * (a0 + cc * (T' : ℝ)) := by
                linarith
              rw [ENNReal.ofReal_add hxy hc3]
              rw [ENNReal.ofReal_add hx hy]
        _ ≤ ENNReal.ofReal ((a0 + cc * (T' : ℝ)) ^ 2 + 2 * cc * (a0 + cc * (T' : ℝ)) + cc ^ 2) := by
              apply ENNReal.ofReal_le_ofReal
              have hc3 : c3 ≤ cc ^ 2 := by
                dsimp [c3, cc]
                rw [show (3 * γ ^ 2 * ‖w‖ ^ 2) ^ 2 = 9 * γ ^ 4 * ‖w‖ ^ 4 by ring]
                have h0 : 0 ≤ γ ^ 4 * ‖w‖ ^ 4 := by positivity
                calc
                  3 * γ ^ 4 * ‖w‖ ^ 4 = 3 * (γ ^ 4 * ‖w‖ ^ 4) := by ring
                  _ ≤ 9 * (γ ^ 4 * ‖w‖ ^ 4) := mul_le_mul_of_nonneg_right (by norm_num : (3 : ℝ) ≤ (9 : ℝ)) h0
                  _ = 9 * γ ^ 4 * ‖w‖ ^ 4 := by ring
              have hc1 : c1 = 2 * cc := by dsimp [c1, cc]; ring
              rw [hc1]
              nlinarith [hc3]
        _ = ENNReal.ofReal ((a0 + cc * (T' + 1 : ℝ)) ^ 2) := by
              congr 1
              ring
        _ ≤ ENNReal.ofReal ((vin x0 w) ^ 2 + 3 * γ ^ 2 * ‖w‖ ^ 2 * ((T' + 1 : ℕ) : ℝ)) ^ 2 := by
              have hy : 0 ≤ (vin x0 w) ^ 2 + 3 * γ ^ 2 * ‖w‖ ^ 2 * ((T' + 1 : ℕ) : ℝ) := by
                have hT : 0 ≤ (((T' + 1 : ℕ) : ℝ)) := by exact_mod_cast Nat.zero_le (T' + 1)
                have hB : 0 ≤ 3 * γ ^ 2 * ‖w‖ ^ 2 * ((T' + 1 : ℕ) : ℝ) := by positivity
                nlinarith [sq_nonneg (vin x0 w), hB]
              rw [← ENNReal.ofReal_pow hy]
              congr 1
              dsimp [a0, cc]
              rw [Nat.cast_add, Nat.cast_one]
end Discrepancy
