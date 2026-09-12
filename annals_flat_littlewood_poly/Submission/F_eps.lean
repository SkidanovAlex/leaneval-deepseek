import Mathlib
import Submission.LMProbs
import Submission.LMMeas
import Submission.LMAux
import Submission.F_moment
import Submission.F_cross
import Submission.F_fourth
import Submission.F_stayP
import Submission.F_rowbudget
import Submission.F_existsT

/-!
The epsilon (slack) partial-coloring lemma by the Lovett--Meka walk (child task).

TASK: prove the theorem `eps_coloring` below (complete the proof).  You may
add any helper lemmas/definitions above it in this file (all fully proved).

MEANING.  For vectors v : ι → Vec n (all nonzero), starting point x0 ∈ [-1,1]^n
and thresholds c j ≥ 0 with Σ exp(-(c j)²/16) ≤ n/16, the walk with parameters
(δ, γ, T) produces — with positive probability — a point x with:
  · |x i| ≤ 1 for all i,
  · |⟨x - x0, v j⟩| ≤ c j ‖v j‖ for all j,
  · at least n/2 coordinates frozen: (n:ℝ)/2 ≤ (frozenVars δ x).card.
The hypotheses on the parameters are those under which the probabilistic
argument of Lovett--Meka works.

Available (already proved, Submission.Discrepancy):
  inPolytope x0 v c x := (∀ i, |x i| ≤ 1) ∧ (∀ j, |vin (x-x0) (v j)| ≤ c j*‖v j‖)
  stay_in_polytope_prob_le n T δ γ x0 v c (hγ) (hδ) (hx0) (hc) (hne) :
     μ.real {ω | ¬ ∀ t ≤ T, inPolytope x0 v c (Xn n T δ γ x0 v c ω t)}
       ≤ 2·(T:ℝ)·((n:ℝ)+(Fintype.card ι:ℝ))·exp(-δ²/(2γ²))
  row_budget n T δ γ x0 v c (hγ) (hT1) (hKle) (hδ10) (hc) (hne) (hsum) :
     Σ_j (mu n T).real {ω | j ∈ frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)} ≤ (7/36)·(n:ℝ)
  frozenRows_card_integral n T δ γ x0 v c :
     ∫ ω, ((frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)).card : ℝ) = Σ_j μ.real {...}
  exp_Xn_norm_sq_lower n T δ γ x0 v c :        (position-squared growth)
     ∫ ω, ‖Xn n T δ γ x0 v c ω T‖² ≥ γ²·(T:ℝ)·(n − ∫|frozenVars| − ∫|frozenRows|)
  exp_fourth_moment_bound n T δ γ x0 v c (hx0) (hK) :
     ∫ ω, ‖Xn n T δ γ x0 v c ω T‖⁴ ≤ 900·(n:ℝ)²        (hK : γ²·T ≤ 6)
  Xn_mgf_real_le / row_frozen_prob_le (not needed directly here)

PROOF OUTLINE.  Let μ := mu n T, Ω := Omega n T, X_t(ω) := Xn n T δ γ x0 v c ω t,
A_T(ω) := frozenVars δ (X_T ω), B_T(ω) := frozenRows δ x0 v c (X_T ω), and
p1 := 2·(T:ℝ)·((n:ℝ)+(Fintype.card ι:ℝ))·exp(-(δ²)/(2γ²)).
Note all integrals/counts below are over ω : Ω with the real measure μ.

 Step 1 (upper bound on E‖X_T‖², from p1 small and the fourth moment).
   Let E1 := {ω | ∀ t ≤ T, inPolytope x0 v c (X_t ω)}.
   - On E1, ‖X_T‖² ≤ n pointwise (each coordinate in [-1,1], so
     ‖X_T‖² = Σ (X_T i)² ≤ n; use `norm_sq_sum` in Submission.LMAux and
     sq_le_one_iff_abs_le_one or nlinarith), so
     ∫ 1_{E1}·‖X_T‖² ≤ n.
   - Off E1: pick any M > 0 (you may choose M := Real.sqrt (E‖X‖⁴ / p1); handle
     p1 = 0 separately — then μ.real (E1ᶜ) = 0 and the integral off E1 is 0),
       ∫ 1_{E1ᶜ}·‖X_T‖² ≤ E‖X‖⁴/M + M·μ.real(E1ᶜ)
     (split 1_{E1ᶜ} = 1_{E1ᶜ∩{‖X‖²≥M}} + 1_{E1ᶜ∩{‖X‖²<M}}; on {‖X‖² ≥ M},
     ‖X‖² ≤ ‖X‖⁴/M, on the other part the integrand is ≤ M).
     With M := √(E‖X‖⁴/p1):  ≤ 2·√(E‖X‖⁴·p1).
   - Hence ∫‖X_T‖² ≤ n + 2·√(E‖X‖⁴)·√p1 ≤ n + 2·√(900·n²)·√p1 ≤ n(1 + 1/5)
     (hsmall gives p1 ≤ 1/10⁶ < 1/90000, so √p1 ≤ 1/300 and
     2·30·√p1 = 60/300 = 1/5; use hnn : 1 ≤ n for √(900·n²) = 30·n — or note
     √(900·n²) = 30·n already for n ≥ 0 since √(x²)=|x| and n ≥ 0).
   Integrability: E‖X‖⁴ and E‖X‖² are finite (F_moment has
   integrable_norm_sq_Xn and similar; the fourth moment bound itself implies
   integrability of ‖X‖² : apply `MeasureTheory.Integrable.of_norm_bounded` or
   bound ‖X‖² ≤ max 1 ‖X‖⁴ pointwise / use the 4th-moment integrand).

 Step 2 (row budget).  From `row_budget` + `frozenRows_card_integral`:
     ∫ |B_T| ≤ (7/36)·n.
 Step 3 (growth).  From `exp_Xn_norm_sq_lower` and steps 1,2:
     γ²T·(n − E|A_T| − E|B_T|) ≤ ∫‖X_T‖² ≤ n(1+1/5), γ²T ≥ 5,
     hence  n − E|A_T| ≤ n·(6/5)/5 + (7/36)·n = n·(6/25) + 7n/36, i.e.
     E|A_T| ≥ n·(29/36 − 6/25) = n·509/900   (linarith/ring; 29/36−6/25 = 509/900).
     Here E|A_T| := ∫ ((frozenVars ...).card : ℝ) and |A_T| ≤ n pointwise.
 Step 4 (Markov on |A_T|).  f := n − |A_T| ≥ 0 is integrable (bounded);
   μ.real {|A_T| < n/2} ≤ μ.real {n/2 ≤ f} ≤ (∫f)/(n/2) = 2(n − E|A_T|)/n
   ≤ 2·(391/900) = 782/900   (use `MeasureTheory.mul_meas_ge_le_integral_of_nonneg`).
   Therefore μ.real H ≥ 118/900 where H := {ω | (n:ℝ)/2 ≤ ((A_T ω).card : ℝ)}
   (Hᶜ = {|A_T| < n/2} up to equality of real inequalities — measurable set;
   complement: `MeasureTheory.probReal_compl_eq_one_sub`).
 Step 5 (intersection).  G := E1 ∩ H:
   μ.real G = μ.real E1 − μ.real(E1 ∩ Hᶜ) ≥ μ.real E1 − μ.real Hᶜ
   ≥ (1 − p1) − (1 − 118/900) = 118/900 − p1 > 0   (hsmall: p1 ≤ 1/10⁶).
   (μ.real E1 ≥ 1 − p1 by `stay_in_polytope_prob_le`; measureReal of
   complements: probReal_compl_eq_one_sub; measurability of E1 and H needed:
   E1 = ⋂_{t≤T} {inPolytope...} — show each {ω | inPolytope x0 v c (X_t ω)}
   is measurable using measurable_Xn, measurable_vin, measurable_abs_coord,
   and the row sets {|vin (x-x0)(v j)| ≤ c j‖v j‖} are closed/measurable;
   H measurable via measurable_frozenVars_card (Submission.LMMeas).)
 Step 6 (extract).  μ.real G > 0 ⇒ G.Nonempty (`MeasureTheory.nonempty_of_measureReal_ne_zero`).
   Take ω₀ ∈ G and set x := Xn n T δ γ x0 v c ω₀ T.  From E1 at t = T,
   inPolytope x0 v c x gives the first two conclusions; from H the third.

FINAL THEOREM STATEMENT (keep exactly):  eps_coloring ... ∃ x : Vec n, ... .

MEASURABILITY / INTEGRABILITY reminders:
  - `measurable_Xn (n := n) (ι := ι) (T := T) (t := t) (ht) δ γ x0 v c`
    : Measurable (fun ω => Xn n T δ γ x0 v c ω t)   for ht : t ≤ T.
  - `measurable_frozenVars_card`, `measurable_frozenRows_card` in F_moment.
  - integrability of bounded functions on the probability space μ n T:
    prove pointwise bounds and use `MeasureTheory.Integrable.of_norm_bounded`
    (‖g‖ ≤ C → Integrable g) or `MeasureTheory.integrable_const` etc.
  - `frozenVars_card_eq_sum'`/`frozenRows_card_eq_sum'` (LMMeas) relate the
    cardinal to a sum of indicators if needed.
  - Real measure: `μ.real E = (μ E).toReal`, `MeasureTheory.measureReal_mono`,
    `MeasureTheory.measureReal_union_le`,
    `MeasureTheory.probReal_compl_eq_one_sub`,
    `MeasureTheory.measureReal_union_add_inter`.

The file must end with no unfinished proofs.  GOOD LUCK.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory ProbabilityTheory

noncomputable section
open Classical

namespace Submission.Discrepancy



/-- Membership events of the polytope at a fixed time are measurable. -/
lemma measurableSet_inPolytope_t {n T t : ℕ} {ι : Type*} [Fintype ι] (ht : t ≤ T) (δ γ : ℝ)
    (x0 : Vec n) (v : ι → Vec n) (c : ι → ℝ) :
    MeasurableSet {ω : Omega n T | inPolytope x0 v c (Xn n T δ γ x0 v c ω t)} := by
  have hX : Measurable (fun ω : Omega n T => Xn n T δ γ x0 v c ω t) :=
    measurable_Xn (n := n) (ι := ι) (T := T) (t := t) ht δ γ x0 v c
  have hcoord (i : Fin n) : MeasurableSet {x : Vec n | |x i| ≤ 1} := by
    rw [show {x : Vec n | |x i| ≤ 1} = (fun x : Vec n => |x i|) ⁻¹' (Set.Iic (1 : ℝ)) by
      ext x; simp]
    exact measurableSet_Iic.preimage (measurable_abs_coord n i)
  have hrow (j : ι) : MeasurableSet {x : Vec n | |vin (x - x0) (v j)| ≤ c j * ‖v j‖} := by
    have hvinabs : Measurable (fun x : Vec n => |vin (x - x0) (v j)|) := by
      have hcont : Continuous (fun x : Vec n => vin (x - x0) (v j)) := by
        change Continuous ((fun p : Vec n × Vec n => ⟪p.1, p.2⟫) ∘ (fun x : Vec n => (x - x0, v j)))
        exact continuous_inner.comp (by fun_prop)
      exact hcont.measurable.abs
    rw [show {x : Vec n | |vin (x - x0) (v j)| ≤ c j * ‖v j‖} =
        (fun x : Vec n => |vin (x - x0) (v j)|) ⁻¹' (Set.Iic (c j * ‖v j‖)) by
      ext x; simp]
    exact measurableSet_Iic.preimage hvinabs
  have hpoly : MeasurableSet {x : Vec n | inPolytope x0 v c x} := by
    rw [show {x : Vec n | inPolytope x0 v c x} =
        (⋂ i : Fin n, {x : Vec n | |x i| ≤ 1}) ∩
          (⋂ j : ι, {x : Vec n | |vin (x - x0) (v j)| ≤ c j * ‖v j‖}) by
      ext x
      simp [inPolytope]]
    exact (MeasurableSet.iInter (fun i : Fin n => hcoord i)).inter
      (MeasurableSet.iInter (fun j : ι => hrow j))
  rw [show {ω : Omega n T | inPolytope x0 v c (Xn n T δ γ x0 v c ω t)} =
      (fun ω : Omega n T => Xn n T δ γ x0 v c ω t) ⁻¹' {x : Vec n | inPolytope x0 v c x} by
    ext ω; simp]
  exact hpoly.preimage hX

/-- The walk stays in the polytope for all times `t ≤ T` is a measurable event. -/
lemma measurableSet_E1 {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) :
    MeasurableSet {ω : Omega n T | ∀ t : ℕ, t ≤ T → inPolytope x0 v c (Xn n T δ γ x0 v c ω t)} := by
  let idx := {t : ℕ // t ≤ T}
  let A : idx → Set (Omega n T) := fun t =>
    {ω : Omega n T | inPolytope x0 v c (Xn n T δ γ x0 v c ω t.1)}
  have hmeas : ∀ t : idx, MeasurableSet (A t) := by
    intro t
    exact measurableSet_inPolytope_t (n := n) (T := T) (ι := ι) t.2 δ γ x0 v c
  have hEq : {ω : Omega n T | ∀ t : ℕ, t ≤ T → inPolytope x0 v c (Xn n T δ γ x0 v c ω t)} =
      ⋂ t : idx, A t := by
    ext ω
    simp [A]
    constructor
    · intro h t
      exact h t.1 t.2
    · intro h t ht
      exact h ⟨t, ht⟩
  rw [hEq]
  exact MeasurableSet.iInter hmeas

/-- The frozen-coordinate count is bounded by `n` pointwise (as a real inequality). -/
lemma card_frozenVars_le_n {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (ω : Omega n T) :
    ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ) ≤ (n : ℝ) := by
  have h := Finset.card_le_univ (frozenVars δ (Xn n T δ γ x0 v c ω T))
  rw [Fintype.card_fin] at h
  exact_mod_cast h

/-- Nonnegative measurable functions with a finite lintegral bound are integrable. -/
lemma integrable_of_lintegral_ofReal_bound {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} (hf : Measurable f) (hf0 : 0 ≤ᵐ[μ] f) {B : ℝ}
    (hB : (∫⁻ a, ENNReal.ofReal (f a) ∂μ) ≤ ENNReal.ofReal B) : Integrable f μ := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hf0]
  exact lt_of_le_of_lt hB ENNReal.ofReal_lt_top

/-- Each coordinate fourth power of `X_T` is integrable. -/
lemma integrable_coord4_Xn {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (hx0 : ∀ i : Fin n, |x0 i| ≤ 1)
    (hK : γ ^ 2 * (T : ℝ) ≤ 6) (i : Fin n) :
    Integrable (fun ω : Omega n T => (Xn n T δ γ x0 v c ω T i) ^ 4) (mu n T) := by
  have hmeas : Measurable (fun ω : Omega n T => (Xn n T δ γ x0 v c ω T i) ^ 4) := by
    exact (continuous_pow 4).measurable.comp
      ((measurable_coord n i).comp (measurable_Xn (n := n) (ι := ι) (T := T) (t := T) le_rfl
        δ γ x0 v c))
  apply integrable_of_lintegral_ofReal_bound hmeas
  · filter_upwards with ω
    positivity
  · exact coord4_lin_bound (n := n) (ι := ι) (T := T) δ γ x0 v c hx0 hK i

/-- `‖X_T‖⁴` is integrable. -/
lemma integrable_norm4_Xn {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (hx0 : ∀ i : Fin n, |x0 i| ≤ 1)
    (hK : γ ^ 2 * (T : ℝ) ≤ 6) :
    Integrable (fun ω : Omega n T => ‖Xn n T δ γ x0 v c ω T‖ ^ 4) (mu n T) := by
  have hsum : Integrable (fun ω : Omega n T =>
      ∑ i : Fin n, (Xn n T δ γ x0 v c ω T i) ^ 4) (mu n T) := by
    refine integrable_finsetSum (Finset.univ : Finset (Fin n)) ?_
    intro i hi
    exact integrable_coord4_Xn (n := n) (ι := ι) (T := T) δ γ x0 v c hx0 hK i
  have hdom : Integrable (fun ω : Omega n T =>
      (n : ℝ) * (∑ i : Fin n, (Xn n T δ γ x0 v c ω T i) ^ 4)) (mu n T) := by
    simpa [mul_comm] using hsum.const_mul (n : ℝ)
  refine Integrable.mono' hdom ?_ ?_
  · exact ((continuous_pow 4).measurable.comp ((measurable_norm n).comp
      (measurable_Xn (n := n) (ι := ι) (T := T) (t := T) le_rfl δ γ x0 v c))).aestronglyMeasurable
  · filter_upwards with ω
    have hle : ‖Xn n T δ γ x0 v c ω T‖ ^ 4 ≤
        (n : ℝ) * (∑ i : Fin n, (Xn n T δ γ x0 v c ω T i) ^ 4) :=
      norm4_le_mul_sum (Xn n T δ γ x0 v c ω T)
    have hnonneg : 0 ≤ ‖Xn n T δ γ x0 v c ω T‖ ^ 4 := by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hle

/-- `‖X_T‖²` is integrable. -/
lemma integrable_norm2_Xn {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (hx0 : ∀ i : Fin n, |x0 i| ≤ 1)
    (hK : γ ^ 2 * (T : ℝ) ≤ 6) :
    Integrable (fun ω : Omega n T => ‖Xn n T δ γ x0 v c ω T‖ ^ 2) (mu n T) := by
  have h4 : Integrable (fun ω : Omega n T => ‖Xn n T δ γ x0 v c ω T‖ ^ 4) (mu n T) :=
    integrable_norm4_Xn (n := n) (ι := ι) (T := T) δ γ x0 v c hx0 hK
  have hdom : Integrable (fun ω : Omega n T =>
      (1 : ℝ) + ‖Xn n T δ γ x0 v c ω T‖ ^ 4) (mu n T) :=
    (integrable_const (c := (1 : ℝ)) (μ := mu n T)).add h4
  refine Integrable.mono' hdom ?_ ?_
  · exact ((continuous_pow 2).measurable.comp ((measurable_norm n).comp
      (measurable_Xn (n := n) (ι := ι) (T := T) (t := T) le_rfl δ γ x0 v c))).aestronglyMeasurable
  · filter_upwards with ω
    have hpow : ‖Xn n T δ γ x0 v c ω T‖ ^ 4 =
        (‖Xn n T δ γ x0 v c ω T‖ ^ 2) ^ 2 := by ring
    have hineq : ‖Xn n T δ γ x0 v c ω T‖ ^ 2 ≤ 1 + ‖Xn n T δ γ x0 v c ω T‖ ^ 4 := by
      rw [hpow]
      nlinarith [sq_nonneg (‖Xn n T δ γ x0 v c ω T‖ ^ 2 - 1 / 2)]
    have hnonneg : 0 ≤ ‖Xn n T δ γ x0 v c ω T‖ ^ 2 := by positivity
    simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hineq

/-- `n - |frozenVars X_T|` is integrable. -/
lemma integrable_free_card {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) :
    Integrable (fun ω : Omega n T => (n : ℝ) -
        ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ)) (mu n T) := by
  have hc : Integrable (fun ω : Omega n T =>
      ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ)) (mu n T) :=
    integrable_frozenVars_card (n := n) (T := T) (t := T) le_rfl δ γ x0 v c
  exact (integrable_const (c := (n : ℝ)) (μ := mu n T)).sub hc

/-- Markov applied to the slack `f = n - |A_T|`. -/
lemma markov_free {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) (hnn : 1 ≤ n) :
    (mu n T).real {ω : Omega n T | (n : ℝ) / 2 ≤ (n : ℝ) -
        ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ)} ≤
      (2 / (n : ℝ)) * (∫ ω : Omega n T, ((n : ℝ) -
        ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ)) ∂(mu n T)) := by
  have hf0 : 0 ≤ᵐ[mu n T] (fun ω : Omega n T => (n : ℝ) -
      ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ)) := by
    filter_upwards with ω
    exact sub_nonneg.mpr (card_frozenVars_le_n (n := n) (T := T) (ι := ι) δ γ x0 v c ω)
  have hfint : Integrable (fun ω : Omega n T => (n : ℝ) -
      ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ)) (mu n T) :=
    integrable_free_card (n := n) (T := T) (ι := ι) δ γ x0 v c
  have hmark := MeasureTheory.mul_meas_ge_le_integral_of_nonneg (μ := mu n T) hf0 hfint
    ((n : ℝ) / 2)
  have hnon : 0 ≤ (2 / (n : ℝ)) := by positivity
  have hnposR : 0 < (n : ℝ) := by positivity
  have hleft : (2 / (n : ℝ)) * (((n : ℝ) / 2) * (mu n T).real {ω : Omega n T | (n : ℝ) / 2 ≤ (n : ℝ) -
        ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ)}) =
      (mu n T).real {ω : Omega n T | (n : ℝ) / 2 ≤ (n : ℝ) -
        ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ)} := by
    field_simp [hnposR.ne']
  have hmul : (2 / (n : ℝ)) * (((n : ℝ) / 2) * (mu n T).real {ω : Omega n T | (n : ℝ) / 2 ≤ (n : ℝ) -
        ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ)}) ≤
      (2 / (n : ℝ)) * (∫ ω : Omega n T, ((n : ℝ) -
        ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ)) ∂(mu n T)) := by
    exact mul_le_mul_of_nonneg_left hmark hnon
  rwa [hleft] at hmul

/-- Measurability of the frozen-count event `n/2 ≤ |A_T|`. -/
lemma measurableSet_frozenMany {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n)
    (v : ι → Vec n) (c : ι → ℝ) :
    MeasurableSet {ω : Omega n T | (n : ℝ) / 2 ≤
      ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ)} := by
  have hfA : Measurable (fun ω : Omega n T =>
      ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ)) :=
    measurable_frozenVars_card (n := n) (T := T) (t := T) le_rfl δ γ x0 v c
  rw [show {ω : Omega n T | (n : ℝ) / 2 ≤
        ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ)} =
      (fun ω : Omega n T => ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ)) ⁻¹'
        (Set.Ici ((n : ℝ) / 2)) by
    ext ω; simp]
  exact measurableSet_Ici.preimage hfA


/-- For `0 < M`, `y² ≤ y⁴/M + M` for every real `y`. -/
lemma two_pow_le_four_div {y M : ℝ} (hM : 0 < M) : y ^ 2 ≤ y ^ 4 / M + M := by
  have hok : y ^ 2 * M ≤ y ^ 4 + M ^ 2 := by
    have hpow : y ^ 4 = (y ^ 2) ^ 2 := by ring
    rw [hpow]
    have hs : 0 ≤ (y ^ 2 - M / 2) ^ 2 := sq_nonneg _
    have hs2 : 0 ≤ M ^ 2 := sq_nonneg M
    nlinarith
  have hdiv : y ^ 2 ≤ (y ^ 4 + M ^ 2) / M := (le_div_iff₀ hM).mpr hok
  have hrew : (y ^ 4 + M ^ 2) / M = y ^ 4 / M + M := by
    field_simp [hM.ne']
  rwa [hrew] at hdiv

/-- A split bound for an integral over a probability space: on a measurable set
`f ≤ A`, on its complement `f ≤ g + B` (with `g ≥ 0` a.e.). -/
lemma prob_int_le_split {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {s : Set α} (hs : MeasurableSet s) {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hg0 : 0 ≤ᵐ[μ] g) (A B : ℝ) (hA : 0 ≤ A)
    (hfs : ∀ ω ∈ s, f ω ≤ A) (hfc : ∀ ω ∈ sᶜ, f ω ≤ g ω + B) :
    (∫ ω, f ω ∂μ) ≤ A + (∫ ω, g ω ∂μ) + B * μ.real sᶜ := by
  have hAs : (∫ x in s, f x ∂μ) ≤ (∫ x in s, A ∂μ) := by
    exact setIntegral_mono_on hf.integrableOn (integrableOn_const (μ := μ) (s := s) (C := A)) hs hfs
  have hAs' : (∫ x in s, A ∂μ) = A * μ.real s := by
    rw [setIntegral_const A]
    simp [mul_comm]
  have hgB : IntegrableOn (fun x : α => g x + B) sᶜ μ := by
    exact hg.integrableOn.add (integrableOn_const (μ := μ) (s := sᶜ) (C := B))
  have hcs : (∫ x in sᶜ, f x ∂μ) ≤ (∫ x in sᶜ, g x + B ∂μ) := by
    exact setIntegral_mono_on hf.integrableOn hgB (MeasurableSet.compl hs) (fun ω hω => hfc ω hω)
  have hsplit : (∫ x in sᶜ, g x + B ∂μ) = (∫ x in sᶜ, g x ∂μ) + B * μ.real sᶜ := by
    have h1 : Integrable g (μ.restrict sᶜ) := hg.integrableOn
    have h2 : Integrable (fun _ : α => B) (μ.restrict sᶜ) :=
      (integrableOn_const (μ := μ) (s := sᶜ) (C := B))
    have hsumm : Integrable (fun x : α => g x + B) (μ.restrict sᶜ) := hgB
    calc
      (∫ x in sᶜ, g x + B ∂μ) = (∫ x : α, g x + B ∂(μ.restrict sᶜ)) := rfl
      _ = (∫ x : α, g x ∂(μ.restrict sᶜ)) + (∫ x : α, B ∂(μ.restrict sᶜ)) := by
          rw [show (fun x : α => g x + B) = (fun x : α => g x) + (fun _ : α => B) by
            funext x; rfl]
          exact integral_add h1 h2
      _ = (∫ x in sᶜ, g x ∂μ) + (∫ x in sᶜ, B ∂μ) := rfl
      _ = (∫ x in sᶜ, g x ∂μ) + B * μ.real sᶜ := by
          rw [setIntegral_const B]
          simp [mul_comm]
  have hA1 : A * μ.real s ≤ A := by
    have hle1 : μ.real s ≤ 1 := measureReal_le_one (μ := μ)
    have hm : A * μ.real s ≤ A * 1 := mul_le_mul_of_nonneg_left hle1 hA
    simpa using hm
  have hsub : (∫ x in sᶜ, g x ∂μ) ≤ ∫ x, g x ∂μ := setIntegral_le_integral hg hg0
  calc
    (∫ x : α, f x ∂μ) = (∫ x in s, f x ∂μ) + (∫ x in sᶜ, f x ∂μ) :=
        (integral_add_compl (μ := μ) hs hf).symm
    _ ≤ (A * μ.real s) + ((∫ x in sᶜ, g x ∂μ) + B * μ.real sᶜ) := by
        exact add_le_add (hAs.trans_eq hAs') (hcs.trans_eq hsplit)
    _ ≤ A + ((∫ x, g x ∂μ) + B * μ.real sᶜ) := by
        linarith
    _ = A + (∫ x, g x ∂μ) + B * μ.real sᶜ := by ring

/-- Upper bound on E‖X_T‖² used in the slack-coloring argument: E‖X_T‖² ≤ (6/5)·n. -/
lemma norm_sq_int_le {n T : ℕ} {ι : Type*} [Fintype ι] (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (hγ : 0 < γ) (hδ : 0 < δ) (hx0 : ∀ i : Fin n, |x0 i| ≤ 1)
    (hc : ∀ j : ι, 0 ≤ c j) (hne : ∀ j : ι, ‖v j‖ ≠ 0) (hnn : 1 ≤ n)
    (hKle : γ ^ 2 * (T : ℝ) ≤ 6)
    (hsmall : 2 * (T : ℝ) * ((n : ℝ) + (Fintype.card ι : ℝ)) *
        Real.exp (-(δ ^ 2) / (2 * γ ^ 2)) ≤ 1 / 1000000) :
    (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T‖ ^ 2 ∂(mu n T)) ≤ (6 / 5) * (n : ℝ) := by
  let E1 : Set (Omega n T) :=
    {ω : Omega n T | ∀ t : ℕ, t ≤ T → inPolytope x0 v c (Xn n T δ γ x0 v c ω t)}
  let M : ℝ := 30000 * (n : ℝ)
  have hmeasE1 : MeasurableSet E1 := by
    simpa [E1] using (measurableSet_E1 (n := n) (T := T) (ι := ι) δ γ x0 v c)
  have hf2int : Integrable (fun ω : Omega n T => ‖Xn n T δ γ x0 v c ω T‖ ^ 2) (mu n T) :=
    integrable_norm2_Xn (n := n) (ι := ι) (T := T) δ γ x0 v c hx0 hKle
  have hf4int : Integrable (fun ω : Omega n T => ‖Xn n T δ γ x0 v c ω T‖ ^ 4) (mu n T) :=
    integrable_norm4_Xn (n := n) (ι := ι) (T := T) δ γ x0 v c hx0 hKle
  have hI4le : (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T‖ ^ 4 ∂(mu n T)) ≤ 900 * (n : ℝ) ^ 2 :=
    exp_fourth_moment_bound (n := n) (T := T) (ι := ι) δ γ x0 v c hx0 hKle
  have hMpos : 0 < M := by
    have hnpos : 0 < (n : ℝ) := by positivity
    positivity
  have hMnonneg : 0 ≤ M := le_of_lt hMpos
  have hstay : (mu n T).real E1ᶜ ≤
      2 * (T : ℝ) * ((n : ℝ) + (Fintype.card ι : ℝ)) *
        Real.exp (-(δ ^ 2) / (2 * γ ^ 2)) := by
    have hset : E1ᶜ = {ω : Omega n T | ¬ (∀ t : ℕ, t ≤ T →
        inPolytope x0 v c (Xn n T δ γ x0 v c ω t))} := by
      ext ω
      simp [E1]
    rw [hset]
    exact stay_in_polytope_prob_le (n := n) (T := T) (ι := ι) δ γ x0 v c hγ hδ hx0 hc hne
  have hfs : ∀ ω, ω ∈ E1 → ‖Xn n T δ γ x0 v c ω T‖ ^ 2 ≤ (n : ℝ) := by
    intro ω hω
    have hp : inPolytope x0 v c (Xn n T δ γ x0 v c ω T) := hω T le_rfl
    have hb : ∀ i : Fin n, (Xn n T δ γ x0 v c ω T i) ^ 2 ≤ 1 := by
      intro i
      exact (sq_le_one_iff_abs_le_one (Xn n T δ γ x0 v c ω T i)).mpr (hp.1 i)
    rw [norm_sq_sum n (Xn n T δ γ x0 v c ω T)]
    calc
      (∑ i : Fin n, (Xn n T δ γ x0 v c ω T i) ^ 2) ≤ ∑ i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum (by intro i hi; exact hb i)
      _ = (n : ℝ) := by simp
  have hfc : ∀ ω, ω ∈ E1ᶜ → ‖Xn n T δ γ x0 v c ω T‖ ^ 2 ≤
      ‖Xn n T δ γ x0 v c ω T‖ ^ 4 / M + M := by
    intro ω hω
    exact two_pow_le_four_div (y := ‖Xn n T δ γ x0 v c ω T‖) hMpos
  have hgint : Integrable (fun ω : Omega n T => ‖Xn n T δ γ x0 v c ω T‖ ^ 4 / M) (mu n T) := by
    have hc' : Integrable (fun ω : Omega n T =>
        (1 / M) * ‖Xn n T δ γ x0 v c ω T‖ ^ 4) (mu n T) :=
      hf4int.const_mul (1 / M)
    convert hc' using 1
    funext ω
    ring
  have hg0 : 0 ≤ᵐ[mu n T] (fun ω : Omega n T => ‖Xn n T δ γ x0 v c ω T‖ ^ 4 / M) := by
    filter_upwards with ω
    positivity
  have hsplit :
      (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T‖ ^ 2 ∂(mu n T)) ≤
        (n : ℝ) + (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T‖ ^ 4 / M ∂(mu n T)) +
          M * (mu n T).real E1ᶜ := by
    exact prob_int_le_split (μ := mu n T) (s := E1) hmeasE1
      (f := fun ω : Omega n T => ‖Xn n T δ γ x0 v c ω T‖ ^ 2)
      (g := fun ω : Omega n T => ‖Xn n T δ γ x0 v c ω T‖ ^ 4 / M)
      hf2int hgint hg0 ((n : ℝ)) M (by positivity) hfs hfc
  have hgint2 : (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T‖ ^ 4 / M ∂(mu n T)) =
      (1 / M) * (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T‖ ^ 4 ∂(mu n T)) := by
    rw [integral_div]
    ring
  have hnR : 0 < (n : ℝ) := by positivity
  have hsmall3 : (1 / M) * (900 * (n : ℝ) ^ 2) ≤ (3 / 100) * (n : ℝ) := by
    have heq : (1 / M) * (900 * (n : ℝ) ^ 2) = (3 / 100) * (n : ℝ) := by
      dsimp [M]
      field_simp [hnR.ne']
      ring
    rw [heq]
  have hsmall4 : M * (1 / 1000000) ≤ (3 / 100) * (n : ℝ) := by
    have heq : M * (1 / 1000000) = (3 / 100) * (n : ℝ) := by
      dsimp [M]
      norm_num
      ring
    rw [heq]
  calc
    (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T‖ ^ 2 ∂(mu n T))
        ≤ (n : ℝ) + (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T‖ ^ 4 / M ∂(mu n T)) +
            M * (mu n T).real E1ᶜ := hsplit
    _ = (n : ℝ) +
          (1 / M) * (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T‖ ^ 4 ∂(mu n T)) +
            M * (mu n T).real E1ᶜ := by rw [hgint2]
    _ ≤ (n : ℝ) + (1 / M) * (900 * (n : ℝ) ^ 2) + M * (1 / 1000000) := by
        have h1 : (1 / M) * (∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T‖ ^ 4 ∂(mu n T)) ≤
            (1 / M) * (900 * (n : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hI4le (by positivity)
        have h2 : M * (mu n T).real E1ᶜ ≤ M * (1 / 1000000) := by
          have hst : (mu n T).real E1ᶜ ≤ 1 / 1000000 := le_trans hstay hsmall
          exact mul_le_mul_of_nonneg_left hst hMnonneg
        nlinarith
    _ ≤ (6 / 5) * (n : ℝ) := by
        have h1 : (1 / M) * (900 * (n : ℝ) ^ 2) ≤ (3 / 100) * (n : ℝ) := hsmall3
        have h2 : M * (1 / 1000000) ≤ (3 / 100) * (n : ℝ) := hsmall4
        nlinarith

/-- The epsilon (slack) partial-coloring lemma (Lovett--Meka). -/
theorem eps_coloring {ι : Type*} [Fintype ι] (n T : ℕ) (δ γ : ℝ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (hγ : 0 < γ) (hT1 : 1 ≤ T) (hnn : 1 ≤ n)
    (hKge : 5 ≤ γ ^ 2 * (T : ℝ)) (hKle : γ ^ 2 * (T : ℝ) ≤ 6)
    (hδ : 0 < δ) (hδ10 : δ ≤ 1 / 10)
    (hsmall : 2 * (T : ℝ) * ((n : ℝ) + (Fintype.card ι : ℝ)) * Real.exp (-(δ ^ 2) / (2 * γ ^ 2))
      ≤ 1 / 1000000)
    (hx0 : ∀ i : Fin n, |x0 i| ≤ 1) (hc : ∀ j : ι, 0 ≤ c j) (hne : ∀ j : ι, ‖v j‖ ≠ 0)
    (hsum : ∑ j : ι, Real.exp (-(c j) ^ 2 / 16) ≤ (n : ℝ) / 16) :
    ∃ x : Vec n,
      (∀ i : Fin n, |x i| ≤ 1) ∧
      (∀ j : ι, |vin (x - x0) (v j)| ≤ c j * ‖v j‖) ∧
      ((n : ℝ) / 2 ≤ (frozenVars δ x).card) := by
  -- Measure, events, and key expectations
  let p1 : ℝ := 2 * (T : ℝ) * ((n : ℝ) + (Fintype.card ι : ℝ)) *
    Real.exp (-(δ ^ 2) / (2 * γ ^ 2))
  let E1 : Set (Omega n T) :=
    {ω : Omega n T | ∀ t : ℕ, t ≤ T → inPolytope x0 v c (Xn n T δ γ x0 v c ω t)}
  let H : Set (Omega n T) :=
    {ω : Omega n T | (n : ℝ) / 2 ≤ ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ)}
  let G : Set (Omega n T) := E1 ∩ H
  let I2 : ℝ := ∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T‖ ^ 2 ∂(mu n T)
  let I4 : ℝ := ∫ ω : Omega n T, ‖Xn n T δ γ x0 v c ω T‖ ^ 4 ∂(mu n T)
  let EA : ℝ := ∫ ω : Omega n T, ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T)
  let EB : ℝ := ∫ ω : Omega n T, ((frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T)
  have hmeasE1 : MeasurableSet E1 := by
    simpa [E1] using (measurableSet_E1 (n := n) (T := T) (ι := ι) δ γ x0 v c)
  have hmeasH : MeasurableSet H := by
    simpa [H] using (measurableSet_frozenMany (n := n) (T := T) (ι := ι) δ γ x0 v c)
  have hf2int : Integrable (fun ω : Omega n T => ‖Xn n T δ γ x0 v c ω T‖ ^ 2) (mu n T) :=
    integrable_norm2_Xn (n := n) (ι := ι) (T := T) δ γ x0 v c hx0 hKle
  have hf4int : Integrable (fun ω : Omega n T => ‖Xn n T δ γ x0 v c ω T‖ ^ 4) (mu n T) :=
    integrable_norm4_Xn (n := n) (ι := ι) (T := T) δ γ x0 v c hx0 hKle
  have hI4le : I4 ≤ 900 * (n : ℝ) ^ 2 := by
    simpa [I4] using (exp_fourth_moment_bound (n := n) (T := T) (ι := ι) δ γ x0 v c hx0 hKle)
  have hp1nonneg : 0 ≤ p1 := by
    unfold p1
    positivity
  have hp1small : p1 ≤ 1 / 1000000 := by
    simpa [p1] using hsmall
  have hstay : (mu n T).real E1ᶜ ≤ p1 := by
    have hset : E1ᶜ = {ω : Omega n T | ¬ (∀ t : ℕ, t ≤ T →
        inPolytope x0 v c (Xn n T δ γ x0 v c ω t))} := by
      ext ω
      simp [E1]
    rw [hset]
    simpa [p1] using (stay_in_polytope_prob_le (n := n) (T := T) (ι := ι) δ γ x0 v c hγ hδ hx0 hc hne)
  -- Step 1: E‖X_T‖² ≤ (6/5)n
  have hI2le : I2 ≤ (6 / 5) * (n : ℝ) := by
    simpa [I2] using (norm_sq_int_le (n := n) (T := T) (ι := ι) δ γ x0 v c hγ hδ hx0 hc hne hnn hKle hsmall)
  -- Step 2: row budget E|B_T| ≤ (7/36)n
  have hEB : EB ≤ (7 / 36) * (n : ℝ) := by
    change (∫ ω : Omega n T, ((frozenRows δ x0 v c (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T)) ≤
        (7 / 36) * (n : ℝ)
    rw [frozenRows_card_integral (n := n) (T := T) (ι := ι) δ γ x0 v c]
    exact row_budget (n := n) (T := T) (ι := ι) δ γ x0 v c hγ hT1 hKle hδ10 hc hne hsum
  -- Step 3: lower bound on E|A_T|
  have hlo : γ ^ 2 * (T : ℝ) * ((n : ℝ) - EA - EB) ≤ I2 := by
    have h := exp_Xn_norm_sq_lower (n := n) (T := T) (ι := ι) δ γ x0 v c
    simpa [I2, EA, EB] using h
  have hEA : (509 / 900) * (n : ℝ) ≤ EA := by
    have hzpos : 0 < γ ^ 2 * (T : ℝ) := by nlinarith [hKge]
    have hle1 : γ ^ 2 * (T : ℝ) * ((n : ℝ) - EA - EB) ≤ (6 / 5) * (n : ℝ) :=
      le_trans hlo hI2le
    have h625n : 0 ≤ (6 / 25) * (n : ℝ) := by positivity
    have hmul : (6 / 5) * (n : ℝ) ≤ (γ ^ 2 * (T : ℝ)) * ((6 / 25) * (n : ℝ)) := by
      have hmm := mul_le_mul_of_nonneg_right hKge h625n
      ring_nf at hmm ⊢
      exact hmm
    have hX : (n : ℝ) - EA - EB ≤ (6 / 25) * (n : ℝ) := by
      have hc1 : γ ^ 2 * (T : ℝ) * ((n : ℝ) - EA - EB) ≤
          (γ ^ 2 * (T : ℝ)) * ((6 / 25) * (n : ℝ)) := le_trans hle1 hmul
      exact (mul_le_mul_iff_of_pos_left hzpos).mp hc1
    nlinarith
  -- Step 4: Markov on the frozen count
  have hHc : (mu n T).real Hᶜ ≤ 782 / 900 := by
    let fA : Omega n T → ℝ := fun ω =>
      ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ)
    have hsubset : Hᶜ ⊆ {ω : Omega n T | (n : ℝ) / 2 ≤ (n : ℝ) - fA ω} := by
      intro ω hω
      have hnot : ¬ (n : ℝ) / 2 ≤ fA ω := by simpa [H, fA] using hω
      have hlt : fA ω < (n : ℝ) / 2 := lt_of_not_ge hnot
      dsimp [fA]
      linarith
    have hmono : (mu n T).real Hᶜ ≤ (mu n T).real
        {ω : Omega n T | (n : ℝ) / 2 ≤ (n : ℝ) - fA ω} := by
      exact MeasureTheory.measureReal_mono hsubset
        (MeasureTheory.measure_ne_top (mu n T) {ω : Omega n T | (n : ℝ) / 2 ≤ (n : ℝ) - fA ω})
    have hmark := markov_free (n := n) (T := T) (ι := ι) δ γ x0 v c hnn
    have hmark' : (mu n T).real
        {ω : Omega n T | (n : ℝ) / 2 ≤ (n : ℝ) - fA ω} ≤
        (2 / (n : ℝ)) * ((n : ℝ) - EA) := by
      -- unfold fA in hmark's integral and evaluate ∫(n - card) = n - EA
      have hci : Integrable fA (mu n T) := by
        simpa [fA] using (integrable_frozenVars_card (n := n) (T := T) (t := T) le_rfl
          δ γ x0 v c)
      have hconst : Integrable (fun _ : Omega n T => (n : ℝ)) (mu n T) := by
        simp
      have hint : (∫ ω : Omega n T, ((n : ℝ) - fA ω) ∂(mu n T)) = (n : ℝ) - EA := by
        have hsub := integral_sub (μ := mu n T) hconst hci
        calc
          (∫ ω : Omega n T, ((n : ℝ) - fA ω) ∂(mu n T))
              = (∫ ω : Omega n T, ((fun _ : Omega n T => (n : ℝ)) ω - fA ω) ∂(mu n T)) := by rfl
          _ = (∫ ω : Omega n T, (fun _ : Omega n T => (n : ℝ)) ω ∂(mu n T)) -
              (∫ ω : Omega n T, fA ω ∂(mu n T)) := hsub
          _ = (n : ℝ) - EA := by
              have hcst : (∫ ω : Omega n T, (fun _ : Omega n T => (n : ℝ)) ω ∂(mu n T)) = (n : ℝ) := by
                rw [integral_const]
                have huniv : (mu n T).real Set.univ = 1 := by
                  rw [MeasureTheory.measureReal_def]
                  simp
                simp [huniv]
              have hfA : (∫ ω : Omega n T, fA ω ∂(mu n T)) = EA := by
                change (∫ ω : Omega n T,
                    ((frozenVars δ (Xn n T δ γ x0 v c ω T)).card : ℝ) ∂(mu n T)) = EA
                rfl
              rw [hcst, hfA]
      have hmark2 := hmark
      -- hmark2 has the same set but with card spelled out; hmono set matches fA form
      have hgoal : (mu n T).real {ω : Omega n T | (n : ℝ) / 2 ≤ (n : ℝ) - fA ω} ≤
          (2 / (n : ℝ)) * (∫ ω : Omega n T, ((n : ℝ) - fA ω) ∂(mu n T)) := by
        simpa [fA] using hmark2
      calc
        (mu n T).real {ω : Omega n T | (n : ℝ) / 2 ≤ (n : ℝ) - fA ω}
            ≤ (2 / (n : ℝ)) * (∫ ω : Omega n T, ((n : ℝ) - fA ω) ∂(mu n T)) := hgoal
        _ = (2 / (n : ℝ)) * ((n : ℝ) - EA) := by rw [hint]
    have hEAupper : (n : ℝ) - EA ≤ (391 / 900) * (n : ℝ) := by
      nlinarith [hEA]
    have hfin : (2 / (n : ℝ)) * ((n : ℝ) - EA) ≤ 782 / 900 := by
      have hnpos : 0 < (n : ℝ) := by positivity
      calc
        (2 / (n : ℝ)) * ((n : ℝ) - EA) ≤ (2 / (n : ℝ)) * ((391 / 900) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hEAupper (by positivity)
        _ = 782 / 900 := by
          field_simp [hnpos.ne']
          ring
    exact le_trans (le_trans hmono hmark') hfin
  -- Step 5: positive measure of G
  have hGpos : 0 < (mu n T).real G := by
    have huniv : (mu n T).real Set.univ = 1 := by
      rw [MeasureTheory.measureReal_def]
      simp
    have hinc : E1 ⊆ G ∪ Hᶜ := by
      intro ω hω
      by_cases hH : ω ∈ H
      · exact Or.inl ⟨hω, hH⟩
      · exact Or.inr hH
    have hsub1 : (mu n T).real E1 ≤ (mu n T).real G + (mu n T).real Hᶜ := by
      calc
        (mu n T).real E1 ≤ (mu n T).real (G ∪ Hᶜ) := by
          exact MeasureTheory.measureReal_mono hinc
        _ ≤ (mu n T).real G + (mu n T).real Hᶜ := MeasureTheory.measureReal_union_le _ _
    have hle1 : 1 ≤ (mu n T).real E1ᶜ + (mu n T).real E1 := by
      have hle := MeasureTheory.measureReal_union_le (μ := mu n T) E1 E1ᶜ
      have hc : 1 ≤ (mu n T).real E1 + (mu n T).real E1ᶜ := by
        calc
          1 = (mu n T).real Set.univ := huniv.symm
          _ = (mu n T).real (E1 ∪ E1ᶜ) := by
              congr 1
              ext ω
              simp
          _ ≤ (mu n T).real E1 + (mu n T).real E1ᶜ := hle
      nlinarith
    have hloG : 1 - (mu n T).real E1ᶜ - (mu n T).real Hᶜ ≤ (mu n T).real G := by
      nlinarith
    have hstep : 1 - p1 - 782 / 900 ≤ (mu n T).real G := by
      calc
        1 - p1 - 782 / 900 ≤ 1 - (mu n T).real E1ᶜ - (mu n T).real Hᶜ := by
            linarith [hstay, hHc]
        _ ≤ (mu n T).real G := hloG
    have hlo : 0 < 1 - p1 - 782 / 900 := by
      have h1 : 118 / 900 - 1 / 1000000 ≤ 1 - p1 - 782 / 900 := by
        linarith [hp1small]
      have h2 : (0 : ℝ) < 118 / 900 - 1 / 1000000 := by norm_num
      exact lt_of_lt_of_le h2 h1
    exact lt_of_lt_of_le hlo hstep
  have hGnonempty : G.Nonempty := by
    exact MeasureTheory.nonempty_of_measureReal_ne_zero (μ := mu n T) (s := G) (ne_of_gt hGpos)
  rcases hGnonempty with ⟨ω₀, hω₀⟩
  let x : Vec n := Xn n T δ γ x0 v c ω₀ T
  refine ⟨x, ?_, ?_, ?_⟩
  · have hp := hω₀.1 T le_rfl
    exact hp.1
  · have hp := hω₀.1 T le_rfl
    exact hp.2
  · have hmem : ω₀ ∈ H := hω₀.2
    simpa [x, H] using hmem

end Discrepancy

end Submission
