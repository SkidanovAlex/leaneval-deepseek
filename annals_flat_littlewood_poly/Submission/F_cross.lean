import Mathlib
import Submission.LMProbs
import Submission.LMMeas
import Submission.F_moment

/-!
Position-squared version of the moment growth (child task).

TASK: prove `exp_Xn_norm_sq_lower`.  Add helpers above.

Statement:  E‖X_T‖² ≥ γ²·T·(n − E|A_T| − E|B_T|)     (same RHS as
`exp_norm_sq_lower` in Submission.F_moment, but with ‖X_T‖² on the LHS
instead of ‖X_T − x0‖²).
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory

noncomputable section
open Classical

namespace Submission.Discrepancy

/-! ### Part I: a pointwise norm identity -/

/-- ‖a + b‖² = ‖a‖² + ‖b‖² + 2⟨a,b⟩ on a real inner product space. -/
lemma norm_sq_add_inner {n : ℕ} (a b : Vec n) :
    ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * vin a b := by
  rw [norm_add_sq_real a b]
  simp [vin]
  ring

/-! ### Part II: integrability of the cross term -/

/-- `|vin x y|` is bounded by `‖y‖·(1+‖x‖²)`. -/
lemma vin_le_bound {n : ℕ} (x y : Vec n) :
    |vin x y| ≤ ‖y‖ * (1 + ‖x‖ ^ 2) := by
  have h1 : |vin x y| ≤ ‖x‖ * ‖y‖ := by
    simpa [vin] using (abs_real_inner_le_norm x y)
  have h2 : ‖x‖ * ‖y‖ ≤ ‖y‖ * (1 + ‖x‖ ^ 2) := by
    have hy : 0 ≤ ‖y‖ := norm_nonneg y
    have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
    have hx : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
    calc
      ‖x‖ * ‖y‖ ≤ (1 + ‖x‖ ^ 2) * ‖y‖ := by
        exact mul_le_mul_of_nonneg_right hx hy
      _ = ‖y‖ * (1 + ‖x‖ ^ 2) := by ring
  linarith

/-- vin of the displaced walk with a fixed vector is integrable. -/
lemma integrable_vin_Xn_sub {n : ℕ} {ι : Type*} [Fintype ι] (T t : ℕ) (ht : t ≤ T) (δ γ : ℝ)
    (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ) :
    Integrable (fun ω : Omega n T => vin (Xn n T δ γ x0 v c ω t - x0) x0) (mu n T) := by
  have hX : Measurable (fun ω : Omega n T => Xn n T δ γ x0 v c ω t - x0) := by
    exact (measurable_Xn (n := n) (ι := ι) ht δ γ x0 v c).sub measurable_const
  have hm : AEStronglyMeasurable (fun ω : Omega n T => vin (Xn n T δ γ x0 v c ω t - x0) x0)
      (mu n T) := by
    exact ((measurable_vin n x0).comp hX).aestronglyMeasurable
  have hdom : Integrable (fun ω : Omega n T => ‖x0‖ * (1 + ‖Xn n T δ γ x0 v c ω t - x0‖ ^ 2))
      (mu n T) := by
    have h1 : Integrable (fun ω : Omega n T => (1 : ℝ) + ‖Xn n T δ γ x0 v c ω t - x0‖ ^ 2)
        (mu n T) := by
      simpa using (integrable_norm_sq_Xn (n := n) (T := T) (t := t) ht δ γ x0 v c).add
        (integrable_const (c := (1 : ℝ)) (μ := mu n T))
    simpa [mul_comm, mul_left_comm, mul_assoc] using h1.const_mul ‖x0‖
  refine Integrable.mono' hdom hm ?_
  filter_upwards with ω
  exact vin_le_bound (Xn n T δ γ x0 v c ω t - x0) x0

/-! ### Part III: the cross term vanishes (by induction over T) -/

/-- Cross term of one Gaussian step (fresh coordinate) vanishes. -/
lemma gauss_cross_shift {n : ℕ} {ι : Type*} [Fintype ι] (v : ι → Vec n) (A : Finset (Fin n))
    (B : Finset ι) (γ : ℝ) (a x0 : Vec n) :
    (∫ g : Vec n, vin (a + γ • walkProj v A B g) x0 ∂(stdGaussian (Vec n))) = vin a x0 := by
  have hpoint (g : Vec n) :
      vin (a + γ • walkProj v A B g) x0 = vin a x0 + γ * vin (walkProj v A B g) x0 := by
    simp [vin, inner_add_left, inner_smul_left]
  have hB' : Integrable (fun g : Vec n => vin (walkProj v A B g) x0) (stdGaussian (Vec n)) := by
    have hB'' := integrable_lin_proj v A B x0
    simpa [vin, real_inner_comm] using hB''
  have hB : Integrable (fun g : Vec n => γ * vin (walkProj v A B g) x0) (stdGaussian (Vec n)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hB'.const_mul γ
  have hconst : Integrable (fun _ : Vec n => vin a x0) (stdGaussian (Vec n)) := by
    simp
  have hzero : (∫ g : Vec n, vin (walkProj v A B g) x0 ∂(stdGaussian (Vec n))) = 0 := by
    have hg := gauss_cross v A B x0
    have hsame : (fun g : Vec n => vin (walkProj v A B g) x0) =ᵐ[stdGaussian (Vec n)]
        (fun g : Vec n => inner ℝ x0 (walkProj v A B g)) := by
      filter_upwards with g
      simp [vin, real_inner_comm]
    calc
      (∫ g : Vec n, vin (walkProj v A B g) x0 ∂(stdGaussian (Vec n)))
          = (∫ g : Vec n, inner ℝ x0 (walkProj v A B g) ∂(stdGaussian (Vec n))) := integral_congr_ae hsame
      _ = 0 := hg
  calc
    (∫ g : Vec n, vin (a + γ • walkProj v A B g) x0 ∂(stdGaussian (Vec n)))
        = (∫ g : Vec n, (vin a x0 + γ * vin (walkProj v A B g) x0) ∂(stdGaussian (Vec n))) := by
            apply integral_congr_ae
            filter_upwards with g
            exact hpoint g
    _ = (∫ g : Vec n, vin a x0 ∂(stdGaussian (Vec n)))
          + (∫ g : Vec n, γ * vin (walkProj v A B g) x0 ∂(stdGaussian (Vec n))) := by
            exact integral_add hconst hB
    _ = vin a x0 + γ * (∫ g : Vec n, vin (walkProj v A B g) x0 ∂(stdGaussian (Vec n))) := by
            congr 1
            · have hc : (∫ g : Vec n, vin a x0 ∂(stdGaussian (Vec n))) = vin a x0 := by
                simp [MeasureTheory.integral_const]
              rw [hc]
            · rw [integral_const_mul γ (fun g : Vec n => vin (walkProj v A B g) x0)]
    _ = vin a x0 := by
            rw [hzero]
            ring

/-- The cross term of the (T+1)-step walk is integrable over the peeled product. -/
lemma integrable_peel_cross {n : ℕ} {ι : Type*} [Fintype ι] (T : ℕ) (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) :
    Integrable (fun y : Vec n × Omega n T =>
        vin (Xn n (T+1) δ γ x0 v c (Fin.snoc (α := fun _ : Fin (T+1) => Vec n) y.2 y.1) (T+1) - x0) x0)
      ((stdGaussian (Vec n)).prod (mu n T)) := by
  let e : Omega n (T+1) ≃ᵐ (Vec n × Omega n T) := peelEquiv n T
  let H : Vec n × Omega n T → ℝ := fun y =>
    vin (Xn n (T+1) δ γ x0 v c (Fin.snoc (α := fun _ : Fin (T+1) => Vec n) y.2 y.1) (T+1) - x0) x0
  have hpe : ((mu n (T+1)).map e) =
      ((mu n (T+1)).map (fun ω : Omega n (T+1) => (ω (Fin.last T), Fin.init ω))) := by
    congr 1
    funext ω
    simp [e, peelEquiv_apply]
  rw [← peel_measurePreserving n T]
  rw [← hpe]
  refine (integrable_map_equiv e H).mpr ?_
  have hmain : Integrable (fun ω : Omega n (T+1) =>
      vin (Xn n (T+1) δ γ x0 v c ω (T+1) - x0) x0) (mu n (T+1)) :=
    integrable_vin_Xn_sub (n := n) (T := T + 1) (t := T + 1) (le_refl _) δ γ x0 v c
  have hfun : (fun x : Omega n (T+1) => H (e x)) =ᵐ[mu n (T+1)]
      (fun ω : Omega n (T+1) => vin (Xn n (T+1) δ γ x0 v c ω (T+1) - x0) x0) := by
    filter_upwards with ω
    simp only [H, e, peelEquiv_apply]
    rw [Fin.snoc_init_self]
  exact hmain.congr hfun.symm

/-- The cross term at the last step vanishes when integrated against the fresh
    Gaussian; the remaining piece is exactly the cross term of the T-step walk. -/
lemma cross_step {n : ℕ} {ι : Type*} [Fintype ι] (T : ℕ) (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) :
    (∫ ω' : Omega n (T+1), vin (Xn n (T+1) δ γ x0 v c ω' (T+1) - x0) x0 ∂(mu n (T+1))) =
    (∫ ω : Omega n T, vin (Xn n T δ γ x0 v c ω T - x0) x0 ∂(mu n T)) := by
  let F : Vec n → Omega n T → ℝ := fun g p =>
    vin (Xn n (T+1) δ γ x0 v c (Fin.snoc (α := fun _ : Fin (T+1) => Vec n) p g) (T+1) - x0) x0
  let A : Omega n T → ℝ := fun p => vin (Xn n T δ γ x0 v c p T - x0) x0
  have hhint : Integrable (fun y : Vec n × Omega n T => F y.1 y.2)
      ((stdGaussian (Vec n)).prod (mu n T)) := by
    simpa [F] using (integrable_peel_cross (n := n) (T := T) δ γ x0 v c)
  have hpeel := integral_snoc_form n T F hhint
  have hS : (∫ ω' : Omega n (T+1), vin (Xn n (T+1) δ γ x0 v c ω' (T+1) - x0) x0
        ∂(mu n (T+1))) =
      (∫ g : Vec n, ∫ p : Omega n T, F g p ∂(mu n T) ∂(stdGaussian (Vec n))) := by
    calc
      (∫ ω' : Omega n (T+1), vin (Xn n (T+1) δ γ x0 v c ω' (T+1) - x0) x0 ∂(mu n (T+1)))
          = (∫ ω' : Omega n (T+1), F (ω' (Fin.last T)) (Fin.init ω') ∂(mu n (T+1))) := by
              apply integral_congr_ae
              filter_upwards with ω'
              simp [F, Fin.snoc_init_self]
      _ = (∫ g : Vec n, ∫ p : Omega n T, F g p ∂(mu n T) ∂(stdGaussian (Vec n))) := hpeel
  have hswap : (∫ g : Vec n, ∫ p : Omega n T, F g p ∂(mu n T) ∂(stdGaussian (Vec n))) =
      (∫ p : Omega n T, ∫ g : Vec n, F g p ∂(stdGaussian (Vec n)) ∂(mu n T)) := by
    exact integral_integral_swap (μ := stdGaussian (Vec n)) (ν := mu n T)
      (f := fun (g : Vec n) (p : Omega n T) => F g p) hhint
  -- for each past p the inner integral over the fresh Gaussian equals A p
  have hpp (p : Omega n T) :
      (∫ g : Vec n, F g p ∂(stdGaussian (Vec n))) = A p := by
    have hpoint (g : Vec n) :
        F g p = vin ((Xn n T δ γ x0 v c p T - x0)
            + γ • walkProj v (frozenVars δ (Xn n T δ γ x0 v c p T))
                (frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)) g) x0 := by
      have hx := last_step (T' := T) δ γ x0 v c g p
      calc
        F g p = vin ((Xn n T δ γ x0 v c p T + γ • walkProj v (frozenVars δ (Xn n T δ γ x0 v c p T))
                (frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)) g) - x0) x0 := by
                simp [F, hx]
        _ = vin ((Xn n T δ γ x0 v c p T - x0)
              + γ • walkProj v (frozenVars δ (Xn n T δ γ x0 v c p T))
                  (frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)) g) x0 := by
              congr 1
              abel
    calc
      (∫ g : Vec n, F g p ∂(stdGaussian (Vec n)))
          = (∫ g : Vec n,
              vin ((Xn n T δ γ x0 v c p T - x0)
                + γ • walkProj v (frozenVars δ (Xn n T δ γ x0 v c p T))
                    (frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)) g) x0
              ∂(stdGaussian (Vec n))) := by
              apply integral_congr_ae
              filter_upwards with g
              exact hpoint g
      _ = A p := by
              simpa [A] using (gauss_cross_shift v (frozenVars δ (Xn n T δ γ x0 v c p T))
                (frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)) γ (Xn n T δ γ x0 v c p T - x0) x0)
  calc
    (∫ ω' : Omega n (T+1), vin (Xn n (T+1) δ γ x0 v c ω' (T+1) - x0) x0 ∂(mu n (T+1)))
        = (∫ p : Omega n T, ∫ g : Vec n, F g p ∂(stdGaussian (Vec n)) ∂(mu n T)) := by
            rw [hS, hswap]
    _ = (∫ p : Omega n T, A p ∂(mu n T)) := by
            congr 1
            funext p
            exact hpp p
    _ = (∫ ω : Omega n T, vin (Xn n T δ γ x0 v c ω T - x0) x0 ∂(mu n T)) := by rfl


/-- E⟨X_T − x0, x0⟩ = 0. -/
lemma cross_vanishes {n : ℕ} {ι : Type*} [Fintype ι] (T : ℕ) (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) :
    (∫ ω : Omega n T, vin (Xn n T δ γ x0 v c ω T - x0) x0 ∂(mu n T)) = 0 := by
  induction T with
  | zero =>
      simp [Xn, vin]
  | succ T ih =>
      simpa using (cross_step (n := n) (T := T) δ γ x0 v c).trans ih

/-- Position-squared moment growth: E‖X_T‖² ≥ γ² T (n − E|frozenVars| − E|frozenRows|). -/
lemma exp_Xn_norm_sq_lower {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) :
    (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T‖ ^ 2 ∂(mu n T)) ≥
      γ ^ 2 * (T : ℝ) *
        ((n : ℝ)
          - (∫ ω : Omega n T, ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T))
          - (∫ ω : Omega n T, ((frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T))) := by
  -- shorthand for the two displacement moments
  let L : ℝ := ∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T - x0‖ ^ 2 ∂(mu n T)
  have hlow := exp_norm_sq_lower (n := n) (T := T) δ γ x0 v c
  have hcv : (∫ ω : Omega n T, vin (Xn n T δ γ x0 v c ω T - x0) x0 ∂(mu n T)) = 0 :=
    cross_vanishes (n := n) (T := T) δ γ x0 v c
  -- pointwise identity ‖X‖² = ‖X − x0‖² + (‖x0‖² + 2⟨X − x0, x0⟩)
  have hpoint (ω : Omega n T) :
      ‖Xn n T δ γ x0 v c ω T‖ ^ 2 =
        ‖Xn n T δ γ x0 v c ω T - x0‖ ^ 2 + (‖x0‖ ^ 2 + 2 * vin (Xn n T δ γ x0 v c ω T - x0) x0) := by
    have h := norm_sq_add_inner (Xn n T δ γ x0 v c ω T - x0) x0
    have hsum : (Xn n T δ γ x0 v c ω T - x0) + x0 = Xn n T δ γ x0 v c ω T := by abel
    rw [hsum] at h
    rw [h]
    ring
  have hfun : (fun ω : Omega n T => ‖Xn n T δ γ x0 v c ω T‖ ^ 2) =ᵐ[mu n T]
      (fun ω : Omega n T =>
        ‖Xn n T δ γ x0 v c ω T - x0‖ ^ 2 + (‖x0‖ ^ 2 + 2 * vin (Xn n T δ γ x0 v c ω T - x0) x0)) := by
    filter_upwards with ω
    exact hpoint ω
  -- integrability of the pieces
  have hLint : Integrable (fun ω : Omega n T => ‖Xn n T δ γ x0 v c ω T - x0‖ ^ 2) (mu n T) :=
    integrable_norm_sq_Xn (n := n) (T := T) (t := T) (le_refl _) δ γ x0 v c
  have hcvInt : Integrable (fun ω : Omega n T => vin (Xn n T δ γ x0 v c ω T - x0) x0) (mu n T) :=
    integrable_vin_Xn_sub (n := n) (T := T) (t := T) (le_refl _) δ γ x0 v c
  have hcstInt : Integrable (fun _ : Omega n T => (‖x0‖ ^ 2 : ℝ)) (mu n T) := by
    simp
  have htwoInt : Integrable (fun ω : Omega n T =>
      (2 : ℝ) * vin (Xn n T δ γ x0 v c ω T - x0) x0) (mu n T) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hcvInt.const_mul 2
  have hgcInt : Integrable (fun ω : Omega n T =>
      ‖x0‖ ^ 2 + 2 * vin (Xn n T δ γ x0 v c ω T - x0) x0) (mu n T) := hcstInt.add htwoInt
  -- the "garbage" (constants + cross term) integrates to ‖x0‖²
  have hSum2 : (∫ ω : Omega n T, ‖x0‖ ^ 2 + 2 * vin (Xn n T δ γ x0 v c ω T - x0) x0 ∂(mu n T)) =
      ‖x0‖ ^ 2 := by
    calc
      (∫ ω : Omega n T, ‖x0‖ ^ 2 + 2 * vin (Xn n T δ γ x0 v c ω T - x0) x0 ∂(mu n T))
          = (∫ ω : Omega n T, (‖x0‖ ^ 2 : ℝ) ∂(mu n T))
              + (∫ ω : Omega n T, (2 : ℝ) * vin (Xn n T δ γ x0 v c ω T - x0) x0 ∂(mu n T)) := by
              exact integral_add hcstInt htwoInt
      _ = ‖x0‖ ^ 2 + 2 * (∫ ω : Omega n T, vin (Xn n T δ γ x0 v c ω T - x0) x0 ∂(mu n T)) := by
              rw [integral_const_mul 2 (fun ω : Omega n T => vin (Xn n T δ γ x0 v c ω T - x0) x0)]
              congr 1
              simp
      _ = ‖x0‖ ^ 2 := by
              rw [hcv]
              ring
  -- E‖X‖² = E‖X − x0‖² + ‖x0‖²
  have hEq : (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T‖ ^ 2 ∂(mu n T)) = L + ‖x0‖ ^ 2 := by
    calc
      (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T‖ ^ 2 ∂(mu n T))
          = (∫ ω : Omega n T,
                ‖Xn n T δ γ x0 v c ω T - x0‖ ^ 2 + (‖x0‖ ^ 2 + 2 * vin (Xn n T δ γ x0 v c ω T - x0) x0)
              ∂(mu n T)) := by
              exact integral_congr_ae hfun
      _ = (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T - x0‖ ^ 2 ∂(mu n T))
            + (∫ ω : Omega n T, ‖x0‖ ^ 2 + 2 * vin (Xn n T δ γ x0 v c ω T - x0) x0 ∂(mu n T)) := by
              exact integral_add hLint hgcInt
      _ = L + ‖x0‖ ^ 2 := by
              rw [hSum2]
  -- E‖X‖² ≥ E‖X − x0‖² ≥ γ² T (…)
  have hge : L ≤ (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T‖ ^ 2 ∂(mu n T)) := by
    rw [hEq]
    linarith [sq_nonneg ‖x0‖]
  exact le_trans hlow hge

end Discrepancy

end Submission
