import Mathlib
import Submission.LMProbs
import Submission.LMMeas
import Submission.F_freshlin
import Submission.LMTower

/-!
Tower (exponential moment) bound for the Lovett--Meka walk (child task).

TASK: prove `tower_lin` below (complete the proof).  Everything else in the
statement must stay as is.

Meaning: for the walk `Xn` of `T` Gaussian steps (each step a standard Gaussian
projected orthogonally to the frozen constraints, scaled by `γ`), starting at
`x0`,

    E exp (lam * ⟪X_T - x0, w⟫) ≤ exp (lam^2 * γ^2 * ‖w‖^2 * T / 2)

in lintegral (ENNReal) form.

All names live in `Submission.Discrepancy`.  Key API available:

  Vec n        := EuclideanSpace ℝ (Fin n)
  vin a b      := ⟪a, b⟫
  Omega n T    := Fin T → Vec n
  mu n T       : Measure (Omega n T)  (product of T standard Gaussians on Vec n)
  Xn n T δ γ x0 v c ω t : Vec n      -- position after t ≤ T steps
  walkProj v A B g   : Vec n         -- projection of g onto orth. complement of
                                       span {basis i | i ∈ A} ∪ {v j | j ∈ B}
  frozenVars δ x     : Finset (Fin n)  = {i | 1 - δ ≤ |x i|}
  frozenRows δ x0 v c x : Finset ι     = {j | (c j - δ) * ‖v j‖ ≤ |vin (x-x0) (v j)|}

  -- used by the induction step:
  lintegral_snoc_form n T F hmeas :
      (∫⁻ ω : Omega n (T+1), F (ω (Fin.last T)) (Fin.init ω) ∂ mu n (T+1))
        = ∫⁻ g : Vec n, ∫⁻ p : Omega n T, F g p ∂ mu n T ∂ stdGaussian (Vec n)
  Xn_app_value (T' : ℕ) δ γ x0 v c g p w :
      vin (Xn n (T'+1) δ γ x0 v c (Fin.snoc p g) (T'+1) - x0) w
        = vin (Xn n T' δ γ x0 v c p T' - x0) w
          + γ * vin (walkProj v (frozenVars δ (Xn n T' δ γ x0 v c p T'))
               (frozenRows δ x0 v c (Xn n T' δ γ x0 v c p T')) g) w
  fresh_lin v A B lam γ w :
      (∫⁻ g : Vec n, ofReal (exp (lam * (γ * vin (walkProj v A B g) w)))
         ∂ stdGaussian (Vec n)) ≤ ofReal (exp (lam^2 * γ^2 * ‖w‖^2 / 2))
  ofReal_exp_add' a b : ofReal (exp (a + b)) = ofReal (exp a) * ofReal (exp b)
  (and Xn_snoc, measurable_Xn, measurable_snoc_curry in Submission.LMMeas)

PROOF SKETCH (induction on T):

Base T = 0:  ω : Fin 0 → Vec n, Xn n 0 δ γ x0 v c ω 0 = x0 (definition),
so vin (x0 - x0) w = vin 0 w = 0 and the integrand is exp (lam * 0) = 1.
`mu n 0` is a probability measure, so the lintegral is 1; RHS = ofReal (exp 0) = 1.

Step T' → T'+1 (induction hypothesis for T'):
  Let F : Vec n → Omega n T' → ENNReal :=
      fun g p => ofReal (exp (lam * vin (Xn n (T'+1) δ γ x0 v c (Fin.snoc p g) (T'+1) - x0) w))
  Step 1.  Rewrite the outer integrand as F (ω (Fin.last T')) (Fin.init ω).
           For this use  Fin.snoc_init_self  (or prove ω =
           Fin.snoc (Fin.init ω) (ω (Fin.last T')))  and `lintegral_snoc_form`
           (requires measurability of (y : Vec n × Omega n T') ↦ F y.1 y.2;
           build it from measurable_Xn, measurable_snoc_curry, measurable_vin,
           Real.continuous_exp.measurable, or fun_prop with Measurable pieces).
  Step 2.  For each p, factor the g-integrand using Xn_app_value and
           ofReal_exp_add':
             exp (lam * (A p + γ * vin (walkProj ...) w)) =
               exp (lam * A p) * exp (lam * γ * vin (walkProj ...) w)
           with A p := vin (Xn n T' δ γ x0 v c p T' - x0) w.
  Step 3.  Bound the inner g-integral by fresh_lin (uniformly in p):
             ∫⁻ g, ofReal (exp (lam * A p)) * ofReal(exp(lam*γ*vin(walkProj v (A' p) (B' p) g) w))
               = ofReal (exp (lam * A p)) * ∫⁻ g, ofReal (exp (lam*γ*vin(walkProj v (A' p) (B' p) g) w))
               ≤ ofReal (exp (lam * A p)) * ofReal (exp (lam^2 * γ^2 * ‖w‖^2 / 2))
           (A' p := frozenVars δ (Xn n T' δ γ x0 v c p T'), B' p := frozenRows ...)
  Step 4.  Integrate over p: the p-dependent factor is exactly the integrand of
           the induction hypothesis, so
             ∫⁻ p, ofReal (exp (lam * A p)) ≤ ofReal (exp (lam^2 * γ^2 * ‖w‖^2 * T' / 2)).
  Step 5.  Multiply: ofReal (exp (lam^2 γ^2 ‖w‖^2 / 2)) * ofReal (exp (lam^2 γ^2 ‖w‖^2 T' / 2))
             = ofReal (exp (lam^2 γ^2 ‖w‖^2 (T'+1) / 2))   by ofReal_exp_add' and ring.

Watch out for the exact term order in expressions like
`lam * (γ * vin ... w)` versus `(lam * γ) * vin ... w`; rw [mul_assoc] freely.
The exponent on the RHS must end up literally
`lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 * (T + 1) / 2` (ring can handle re-association
inside exp, but if you use `ring_nf` inside the exp argument it may reorder;
an equality `Real.exp x = Real.exp y` needs `Real.exp_inj` or show x = y first,
or better rewrite the ofReal argument directly).  `ring` works on the real
arguments; then `congr 1` or `rw` to finish.

NOTE on measurability: when rewriting pointwise equalities of integrands, use
`lintegral_congr_ae` or `congr 1` after showing the functions are equal
(funext).  For `lintegral_const_mul` the measured function must be measurable:
build `Measurable` facts explicitly.  `fun_prop` is often enough for continuous
functions composed with measurable ones once the pieces are declared.
-/

open scoped BigOperators RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory

noncomputable section
open Classical

namespace Submission.Discrepancy

/-- Exp of a sum factors through `ofReal` (needs no measurability). -/
lemma ofReal_exp_add' (a b : ℝ) :
    ENNReal.ofReal (Real.exp (a + b)) = ENNReal.ofReal (Real.exp a) * ENNReal.ofReal (Real.exp b) := by
  rw [Real.exp_add]
  exact (ENNReal.ofReal_mul (Real.exp_nonneg a))

/-- Measurability of the appended-step integrand in `(g, p)`. -/
lemma meas_snoc_lin {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (w : Vec n) (lam : ℝ) :
    Measurable (fun y : Vec n × Omega n T =>
      ENNReal.ofReal (Real.exp (lam * vin (Xn n (T+1) δ γ x0 v c (Fin.snoc y.2 y.1) (T+1) - x0) w))) := by
  have hX : Measurable (fun y : Vec n × Omega n T =>
      Xn n (T+1) δ γ x0 v c (Fin.snoc y.2 y.1) (T+1)) :=
    (measurable_Xn (n := n) (ι := ι) (T := T + 1) (t := T + 1) (le_refl (T + 1)) δ γ x0 v c).comp
      (measurable_snoc_curry n T)
  have hsub : Measurable (fun y : Vec n × Omega n T =>
      Xn n (T+1) δ γ x0 v c (Fin.snoc y.2 y.1) (T+1) - x0) := hX.sub measurable_const
  have hvin : Measurable (fun y : Vec n × Omega n T =>
      vin (Xn n (T+1) δ γ x0 v c (Fin.snoc y.2 y.1) (T+1) - x0) w) :=
    (measurable_vin n w).comp hsub
  have hlam : Measurable (fun y : Vec n × Omega n T =>
      lam * vin (Xn n (T+1) δ γ x0 v c (Fin.snoc y.2 y.1) (T+1) - x0) w) :=
    hvin.const_mul lam
  have hexp : Measurable (fun y : Vec n × Omega n T =>
      Real.exp (lam * vin (Xn n (T+1) δ γ x0 v c (Fin.snoc y.2 y.1) (T+1) - x0) w)) :=
    Real.continuous_exp.measurable.comp hlam
  exact ENNReal.measurable_ofReal.comp hexp

/-- Measurability of the prefix factor. -/
lemma meas_prefix_lin {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (w : Vec n) (lam : ℝ) :
    Measurable (fun p : Omega n T =>
      ENNReal.ofReal (Real.exp (lam * vin (Xn n T δ γ x0 v c p T - x0) w))) := by
  have hX : Measurable (fun p : Omega n T => Xn n T δ γ x0 v c p T) :=
    measurable_Xn (n := n) (ι := ι) (T := T) (t := T) (le_refl T) δ γ x0 v c
  have hsub : Measurable (fun p : Omega n T => Xn n T δ γ x0 v c p T - x0) := hX.sub measurable_const
  have hvin : Measurable (fun p : Omega n T => vin (Xn n T δ γ x0 v c p T - x0) w) :=
    (measurable_vin n w).comp hsub
  have hlam : Measurable (fun p : Omega n T => lam * vin (Xn n T δ γ x0 v c p T - x0) w) :=
    hvin.const_mul lam
  have hexp : Measurable (fun p : Omega n T =>
      Real.exp (lam * vin (Xn n T δ γ x0 v c p T - x0) w)) :=
    Real.continuous_exp.measurable.comp hlam
  exact ENNReal.measurable_ofReal.comp hexp

/-- Measurability (in `g`, frozen sets fixed at `p`) of the fresh-step factor. -/
lemma meas_frozen_lin {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (w : Vec n) (lam : ℝ) (p : Omega n T) :
    Measurable (fun g : Vec n =>
      ENNReal.ofReal (Real.exp (lam * (γ * vin
        (walkProj v (frozenVars δ (Xn n T δ γ x0 v c p T)) (frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)) g) w)))) := by
  let A : Finset (Fin n) := frozenVars δ (Xn n T δ γ x0 v c p T)
  let B : Finset ι := frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)
  have hA : A = frozenVars δ (Xn n T δ γ x0 v c p T) := rfl
  have hB : B = frozenRows δ x0 v c (Xn n T δ γ x0 v c p T) := rfl
  rw [← hA, ← hB]
  have h1 : Measurable (fun g : Vec n => vin (walkProj v A B g) w) :=
    (measurable_vin n w).comp (continuous_walkProj v A B).measurable
  have h2 : Measurable (fun g : Vec n => γ * vin (walkProj v A B g) w) := h1.const_mul γ
  have h3 : Measurable (fun g : Vec n => lam * (γ * vin (walkProj v A B g) w)) := h2.const_mul lam
  have h4 : Measurable (fun g : Vec n => Real.exp (lam * (γ * vin (walkProj v A B g) w))) :=
    Real.continuous_exp.measurable.comp h3
  exact ENNReal.measurable_ofReal.comp h4

/-- Inductive step of the tower bound. -/
lemma tower_lin_succ {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (w : Vec n) (lam : ℝ)
    (ih : (∫⁻ ω : Omega n T, ENNReal.ofReal (Real.exp (lam * vin (Xn n T δ γ x0 v c ω T - x0) w))
      ∂(mu n T)) ≤ ENNReal.ofReal (Real.exp (lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 * T / 2))) :
    (∫⁻ ω : Omega n (T+1), ENNReal.ofReal
        (Real.exp (lam * vin (Xn n (T+1) δ γ x0 v c ω (T+1) - x0) w)) ∂(mu n (T+1))) ≤
      ENNReal.ofReal (Real.exp (lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 * ((T + 1 : ℕ) : ℝ) / 2)) := by
  let c0 : ℝ≥0∞ := ENNReal.ofReal (Real.exp (lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 / 2))
  let F : Vec n → Omega n T → ℝ≥0∞ := fun g p =>
    ENNReal.ofReal (Real.exp (lam * vin (Xn n (T+1) δ γ x0 v c (Fin.snoc p g) (T+1) - x0) w))
  let cq : Omega n T → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (Real.exp (lam * vin (Xn n T δ γ x0 v c p T - x0) w))
  let hq : Vec n → Omega n T → ℝ≥0∞ := fun g p =>
    ENNReal.ofReal (Real.exp (lam * (γ * vin
      (walkProj v (frozenVars δ (Xn n T δ γ x0 v c p T)) (frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)) g) w)))
  have hfactor : ∀ (p : Omega n T) (g : Vec n), F g p = cq p * hq g p := by
    intro p g
    dsimp [F, cq, hq]
    rw [Xn_app_value T δ γ x0 v c g p w]
    rw [show lam * (vin (Xn n T δ γ x0 v c p T - x0) w
          + γ * vin (walkProj v (frozenVars δ (Xn n T δ γ x0 v c p T))
              (frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)) g) w)
        = lam * vin (Xn n T δ γ x0 v c p T - x0) w
          + lam * (γ * vin (walkProj v (frozenVars δ (Xn n T δ γ x0 v c p T))
              (frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)) g) w) by ring]
    exact ofReal_exp_add' (lam * vin (Xn n T δ γ x0 v c p T - x0) w)
      (lam * (γ * vin (walkProj v (frozenVars δ (Xn n T δ γ x0 v c p T))
        (frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)) g) w))
  have hmeasHq : ∀ p : Omega n T, Measurable (fun g : Vec n => hq g p) := by
    intro p
    simpa [hq] using meas_frozen_lin n T δ γ x0 v c w lam p
  have hinner : ∀ p : Omega n T,
      (∫⁻ g : Vec n, F g p ∂(stdGaussian (Vec n))) ≤ cq p * c0 := by
    intro p
    calc
      (∫⁻ g : Vec n, F g p ∂(stdGaussian (Vec n)))
          = (∫⁻ g : Vec n, cq p * hq g p ∂(stdGaussian (Vec n))) := by
            apply lintegral_congr
            intro g
            exact hfactor p g
      _ = cq p * (∫⁻ g : Vec n, hq g p ∂(stdGaussian (Vec n))) := by
            rw [lintegral_const_mul (cq p) (hmeasHq p)]
      _ ≤ cq p * c0 := by
            refine mul_le_mul_right ?_ (cq p)
            simpa [hq, c0] using (fresh_lin v (frozenVars δ (Xn n T δ γ x0 v c p T))
              (frozenRows δ x0 v c (Xn n T δ γ x0 v c p T)) lam γ w)
  have hmeasF : Measurable (fun y : Vec n × Omega n T => F y.1 y.2) := by
    simpa [F] using meas_snoc_lin n T δ γ x0 v c w lam
  have hmeasCq : Measurable (fun p : Omega n T => cq p) := by
    simpa [cq] using meas_prefix_lin n T δ γ x0 v c w lam
  calc
    (∫⁻ ω : Omega n (T+1),
        ENNReal.ofReal (Real.exp (lam * vin (Xn n (T+1) δ γ x0 v c ω (T+1) - x0) w)) ∂(mu n (T+1)))
    = (∫⁻ ω : Omega n (T+1), F (ω (Fin.last T)) (Fin.init ω) ∂(mu n (T+1))) := by
        apply lintegral_congr
        intro ω
        dsimp [F]
        rw [Fin.snoc_init_self]
    _ = (∫⁻ g : Vec n, ∫⁻ p : Omega n T, F g p ∂(mu n T) ∂(stdGaussian (Vec n))) := by
        exact lintegral_snoc_form n T F hmeasF
    _ = (∫⁻ p : Omega n T, ∫⁻ g : Vec n, F g p ∂(stdGaussian (Vec n)) ∂(mu n T)) := by
        exact lintegral_lintegral_swap (μ := (stdGaussian (Vec n))) (ν := (mu n T))
          (f := F) hmeasF.aemeasurable
    _ ≤ (∫⁻ p : Omega n T, cq p * c0 ∂(mu n T)) := by
        apply lintegral_mono
        intro p
        exact hinner p
    _ = c0 * (∫⁻ p : Omega n T, cq p ∂(mu n T)) := by
        rw [show (fun p : Omega n T => cq p * c0) = fun p : Omega n T => c0 * cq p by
          funext p; rw [mul_comm]]
        rw [lintegral_const_mul c0 hmeasCq]
    _ ≤ c0 * ENNReal.ofReal (Real.exp (lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 * T / 2)) := by
        exact mul_le_mul_right ih c0
    _ = ENNReal.ofReal (Real.exp (lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 / 2)) *
        ENNReal.ofReal (Real.exp (lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 * T / 2)) := by
        simp [c0]
    _ = ENNReal.ofReal (Real.exp (lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 * ((T + 1 : ℕ) : ℝ) / 2)) := by
        rw [← ofReal_exp_add']
        congr 2
        rw [Nat.cast_add, Nat.cast_one]
        ring

lemma tower_lin {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (w : Vec n) (lam : ℝ) :
    (∫⁻ ω : Omega n T, ENNReal.ofReal (Real.exp (lam * vin (Xn n T δ γ x0 v c ω T - x0) w))
      ∂(mu n T)) ≤ ENNReal.ofReal (Real.exp (lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 * T / 2)) := by
  induction T with
  | zero =>
      have hL : (∫⁻ ω : Omega n 0,
          ENNReal.ofReal (Real.exp (lam * vin (Xn n 0 δ γ x0 v c ω 0 - x0) w)) ∂(mu n 0))
          = (1 : ℝ≥0∞) := by
        calc
          (∫⁻ ω : Omega n 0, ENNReal.ofReal (Real.exp (lam * vin (Xn n 0 δ γ x0 v c ω 0 - x0) w))
              ∂(mu n 0))
              = (∫⁻ _ : Omega n 0, (1 : ℝ≥0∞) ∂(mu n 0)) := by
                apply lintegral_congr
                intro ω
                have hx : Xn n 0 δ γ x0 v c ω 0 = x0 := by simp [Xn]
                rw [hx]
                simp [vin, inner_zero_left]
          _ = 1 := by
                rw [lintegral_const]
                simp
      rw [hL]
      have harg : lam ^ 2 * γ ^ 2 * ‖w‖ ^ 2 * ((0 : ℕ) : ℝ) / 2 = 0 := by norm_num
      rw [harg]
      simp
  | succ T ih =>
      exact tower_lin_succ n T δ γ x0 v c w lam ih


end Discrepancy

end Submission
