import Submission.Work.Deep.Sparse.Prelude
import Submission.Work.Deep.Reed.Prob.Product
import Submission.Work.Deep.Reed.Prob.Expectation
import Submission.Work.Deep.Reed.Prob.pi_prob_inter_eq_mul_of_disjoint
import Submission.Work.Deep.Reed.Prob.hoeffding_core
import Submission.Work.Deep.Reed.Prob.freeze_exp
import Submission.Work.Deep.Reed.Prob.abs_exp_freeze_sub_le
import Submission.Work.Deep.Reed.Prob.hoeffding_one_dim

/-!
# Bounded differences (Azuma--Hoeffding) in a product space

The main statement is `hoeffding_bounded_differences` at the bottom of the file.
The proof has three layers:

* `freeze_exp` disintegrates an expectation at one coordinate,
* `hoeffding_one_dim` is Hoeffding's bound for a single variable in an interval,
  obtained from the analytic core `hoeffding_core`,
* `abs_exp_freeze_sub_le` bounds the oscillation of a slice expectation,

and the induction `mgf_frozen` below combines them: it proves the exponential
moment bound for the product measure in which a set `S` of coordinates is still
"free" and the remaining coordinates are frozen to the values of a reference
point.  Running the induction over `S = Finset.univ` gives the exponential
moment bound for the full product measure; Markov's inequality (`prob_mul_le_exp`)
plus the optimisation of the exponent `λ ↦ λ ^ 2 * S / 8 - λ * t` at `λ = 4 t / S`
(`tail_of_mgf`) gives the tail bound.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Deep.Reed.Prob

/-! ## Freezing a family of measures -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {Ω : ι → Type*} [∀ i, Fintype (Ω i)]

/-- The family of measures which agrees with `μ` on the coordinates in `S` and is a point
mass at `g₀ i` on the coordinates outside `S`. -/
noncomputable def frozenFamily (μ : ∀ i, FinProb (Ω i)) (S : Finset ι) (g₀ : ∀ i, Ω i) :
    ∀ i, FinProb (Ω i) :=
  fun i => if i ∈ S then μ i else FinProb.point (g₀ i)

@[simp] lemma frozenFamily_of_mem {μ : ∀ i, FinProb (Ω i)} {S : Finset ι} {g₀ : ∀ i, Ω i}
    {i : ι} (h : i ∈ S) : frozenFamily μ S g₀ i = μ i := if_pos h

@[simp] lemma frozenFamily_of_notMem {μ : ∀ i, FinProb (Ω i)} {S : Finset ι} {g₀ : ∀ i, Ω i}
    {i : ι} (h : i ∉ S) : frozenFamily μ S g₀ i = FinProb.point (g₀ i) := if_neg h

lemma frozenFamily_univ (μ : ∀ i, FinProb (Ω i)) (g₀ : ∀ i, Ω i) :
    frozenFamily μ Finset.univ g₀ = μ :=
  funext fun i => if_pos (Finset.mem_univ i)

/-- Freezing the coordinates outside `insert i₀ S` at `g₀` and then freezing the coordinate
`i₀` at `x` gives the same family as freezing the coordinates outside `S` at
`Function.update g₀ i₀ x`. -/
lemma freeze_frozenFamily_insert {μ : ∀ i, FinProb (Ω i)} {S : Finset ι} {g₀ : ∀ i, Ω i}
    {i₀ : ι} (h : i₀ ∉ S) (x : Ω i₀) :
    FinProb.freeze (frozenFamily μ (insert i₀ S) g₀) i₀ x
      = frozenFamily μ S (Function.update g₀ i₀ x) := by
  funext i
  by_cases hii : i = i₀
  · rw [hii, FinProb.freeze, Function.update_self]
    rw [frozenFamily_of_notMem h, Function.update_self]
  · rw [FinProb.freeze, Function.update_of_ne hii]
    by_cases hiS : i ∈ S
    · rw [frozenFamily_of_mem hiS, frozenFamily_of_mem (Finset.mem_insert_of_mem hiS)]
    · rw [frozenFamily_of_notMem hiS, frozenFamily_of_notMem (fun hc => by
        rcases Finset.mem_insert.mp hc with h' | h'
        · exact hii h'
        · exact hiS h'), Function.update_of_ne hii]

/-- Freezing the coordinate `i₀` of `frozenFamily μ S g₀` at `x` gives
`frozenFamily μ S (Function.update g₀ i₀ x)` (for `i₀ ∉ S`). -/
lemma freeze_frozenFamily_self {μ : ∀ i, FinProb (Ω i)} {S : Finset ι} {g₀ : ∀ i, Ω i}
    {i₀ : ι} (h : i₀ ∉ S) (x : Ω i₀) :
    FinProb.freeze (frozenFamily μ S g₀) i₀ x
      = frozenFamily μ S (Function.update g₀ i₀ x) := by
  funext i
  by_cases hii : i = i₀
  · rw [hii, FinProb.freeze, Function.update_self]
    rw [frozenFamily_of_notMem h, Function.update_self]
  · rw [FinProb.freeze, Function.update_of_ne hii]
    by_cases hiS : i ∈ S
    · rw [frozenFamily_of_mem hiS, frozenFamily_of_mem hiS]
    · rw [frozenFamily_of_notMem hiS, frozenFamily_of_notMem hiS, Function.update_of_ne hii]

/-- The product of point masses at `g₀` is the point mass at `g₀`, so every expectation is
the value at `g₀`. -/
lemma pi_point_exp (g₀ : ∀ i, Ω i) (Z : (∀ i, Ω i) → ℝ) :
    (FinProb.pi fun i => FinProb.point (g₀ i)).exp Z = Z g₀ := by
  classical
  have hwt : ∀ f : ∀ i, Ω i,
      (FinProb.pi fun i => FinProb.point (g₀ i)).wt f
        = if (∀ i, f i = g₀ i) then 1 else 0 := by
    intro f
    rw [FinProb.pi_wt]
    by_cases h : ∀ i, f i = g₀ i
    · rw [if_pos h]
      exact Finset.prod_eq_one fun i _ => FinProb.point_wt_of_eq (h i)
    · rw [if_neg h]
      obtain ⟨i, hi⟩ := not_forall.mp h
      exact Finset.prod_eq_zero (Finset.mem_univ i) (FinProb.point_wt_of_ne hi)
  rw [FinProb.exp]
  simp only [hwt]
  rw [Finset.sum_eq_single g₀]
  · simp
  · intro b _ hb
    have h : ¬ (∀ i, b i = g₀ i) := fun hh => hb (funext hh)
    simp [h]
  · intro h
    exact absurd (Finset.mem_univ g₀) h

/-! ## Markov's inequality -/

/-- Markov's inequality in the form needed below: if `Y ≥ 0` and `Y ≥ K` on the event `A`,
then `P(A) * K ≤ E[Y]`. -/
lemma prob_mul_le_exp {Ω : Type*} [Fintype Ω] (ν : FinProb Ω) (A : Set Ω) (Y : Ω → ℝ)
    {K : ℝ} (hY : ∀ ω, 0 ≤ Y ω) (hA : ∀ ω ∈ A, K ≤ Y ω) :
    ν.prob A * K ≤ ν.exp Y := by
  classical
  have hprob : ν.prob A = ∑ ω, (if ω ∈ A then ν.wt ω else 0) := by
    rw [FinProb.prob]
  rw [FinProb.exp, hprob, Finset.sum_mul]
  refine Finset.sum_le_sum fun ω _ => ?_
  by_cases h : ω ∈ A
  · rw [if_pos h]
    exact mul_le_mul_of_nonneg_left (hA ω h) (ν.wt_nonneg ω)
  · rw [if_neg h, zero_mul]
    exact mul_nonneg (ν.wt_nonneg ω) (hY ω)

/-! ## The exponential moment bound -/

/-- **Exponential moment bound for a partially frozen product measure.**  If `S` is a set of
"free" coordinates and the remaining coordinates are frozen at the values of `g₀`, then the
exponential moment of `X - E X` is bounded by `exp (λ ^ 2 * ∑_{i ∈ S} c i ^ 2 / 8)`. -/
lemma mgf_frozen (μ : ∀ i, FinProb (Ω i)) (X : (∀ i, Ω i) → ℝ) (c : ι → ℝ)
    (hc : ∀ i, 0 ≤ c i)
    (hlip : ∀ (i : ι) (f : ∀ i, Ω i) (x : Ω i), |X (Function.update f i x) - X f| ≤ c i)
    (lam : ℝ) :
    ∀ (S : Finset ι) (g₀ : ∀ i, Ω i),
      (FinProb.pi (frozenFamily μ S g₀)).exp
          (fun f => Real.exp (lam * (X f - (FinProb.pi (frozenFamily μ S g₀)).exp X)))
        ≤ Real.exp (lam ^ 2 * (∑ i ∈ S, (c i) ^ 2) / 8) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro g₀
      have hfam : frozenFamily μ ∅ g₀ = fun i => FinProb.point (g₀ i) :=
        funext fun i => frozenFamily_of_notMem (Finset.notMem_empty i)
      rw [hfam]
      have h1 : (FinProb.pi fun i => FinProb.point (g₀ i)).exp X = X g₀ := pi_point_exp g₀ X
      rw [h1, pi_point_exp g₀ (fun f => Real.exp (lam * (X f - X g₀)))]
      simp
  | insert i₀ S hi ih =>
      intro g₀
      have hfr : ∀ x : Ω i₀,
          FinProb.freeze (frozenFamily μ (insert i₀ S) g₀) i₀ x
            = frozenFamily μ S (Function.update g₀ i₀ x) :=
        fun x => freeze_frozenFamily_insert (μ := μ) (S := S) (g₀ := g₀) hi x
      have hν'i₀ : frozenFamily μ (insert i₀ S) g₀ i₀ = μ i₀ :=
        frozenFamily_of_mem (Finset.mem_insert_self i₀ S)
      set E : ℝ := (FinProb.pi (frozenFamily μ (insert i₀ S) g₀)).exp X with hE
      set m : Ω i₀ → ℝ :=
        fun x => (FinProb.pi (frozenFamily μ S (Function.update g₀ i₀ x))).exp X with hm
      have hpeelX : E = ∑ x : Ω i₀, (μ i₀).wt x * m x := by
        rw [hE, freeze_exp (frozenFamily μ (insert i₀ S) g₀) i₀ X]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hν'i₀, hfr x, hm]
      have hEm : E = (μ i₀).exp m := by
        rw [hpeelX]
        rfl
      have hmom : (FinProb.pi (frozenFamily μ (insert i₀ S) g₀)).exp
            (fun f => Real.exp (lam * (X f - E)))
          = ∑ x : Ω i₀, (μ i₀).wt x *
              (FinProb.pi (frozenFamily μ S (Function.update g₀ i₀ x))).exp
                (fun f => Real.exp (lam * (X f - E))) := by
        rw [freeze_exp (frozenFamily μ (insert i₀ S) g₀) i₀ (fun f => Real.exp (lam * (X f - E)))]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [hν'i₀, hfr x]
      have hslice : ∀ x : Ω i₀,
          (FinProb.pi (frozenFamily μ S (Function.update g₀ i₀ x))).exp
              (fun f => Real.exp (lam * (X f - E)))
            ≤ Real.exp (lam * (m x - E)) * Real.exp (lam ^ 2 * (∑ i ∈ S, (c i) ^ 2) / 8) := by
        intro x
        have hmx : (FinProb.pi (frozenFamily μ S (Function.update g₀ i₀ x))).exp X = m x := by
          rw [hm]
        have hih : (FinProb.pi (frozenFamily μ S (Function.update g₀ i₀ x))).exp
              (fun f => Real.exp (lam * (X f - m x)))
            ≤ Real.exp (lam ^ 2 * (∑ i ∈ S, (c i) ^ 2) / 8) := by
          have h := ih (Function.update g₀ i₀ x)
          rw [hmx] at h
          exact h
        have hpt : (fun f => Real.exp (lam * (X f - E)))
            = (fun f => Real.exp (lam * (m x - E)) * Real.exp (lam * (X f - m x))) := by
          funext f
          rw [← Real.exp_add]
          congr 1
          ring
        have hmul := FinProb.exp_mul_left
          (FinProb.pi (frozenFamily μ S (Function.update g₀ i₀ x)))
          (Real.exp (lam * (m x - E))) (fun f => Real.exp (lam * (X f - m x)))
        rw [hpt, hmul]
        exact mul_le_mul_of_nonneg_left hih (Real.exp_nonneg _)
      have hmy : ∀ y : Ω i₀,
          m y = (FinProb.pi (FinProb.freeze (frozenFamily μ S g₀) i₀ y)).exp X := by
        intro y
        rw [hm, freeze_frozenFamily_self (μ := μ) (S := S) (g₀ := g₀) (i₀ := i₀) hi y]
      have hosc : ∀ x x' : Ω i₀, |m x - m x'| ≤ c i₀ := by
        intro x x'
        rw [hmy x, hmy x']
        exact abs_exp_freeze_sub_le (frozenFamily μ S g₀) i₀ X (hc i₀)
          (fun f y => hlip i₀ f y) x x'
      have hone : (μ i₀).exp (fun x => Real.exp (lam * (m x - (μ i₀).exp m)))
          ≤ Real.exp (lam ^ 2 * (c i₀) ^ 2 / 8) :=
        hoeffding_one_dim (μ i₀) m (hc i₀) hosc lam
      calc (FinProb.pi (frozenFamily μ (insert i₀ S) g₀)).exp (fun f => Real.exp (lam * (X f - E)))
          = ∑ x : Ω i₀, (μ i₀).wt x *
              (FinProb.pi (frozenFamily μ S (Function.update g₀ i₀ x))).exp
                (fun f => Real.exp (lam * (X f - E))) := hmom
        _ ≤ ∑ x : Ω i₀, (μ i₀).wt x *
              (Real.exp (lam * (m x - E)) * Real.exp (lam ^ 2 * (∑ i ∈ S, (c i) ^ 2) / 8)) := by
              refine Finset.sum_le_sum fun x _ => ?_
              exact mul_le_mul_of_nonneg_left (hslice x) ((μ i₀).wt_nonneg x)
        _ = Real.exp (lam ^ 2 * (∑ i ∈ S, (c i) ^ 2) / 8) *
              (μ i₀).exp (fun x => Real.exp (lam * (m x - (μ i₀).exp m))) := by
              have hexp : (μ i₀).exp (fun x => Real.exp (lam * (m x - (μ i₀).exp m)))
                  = ∑ x : Ω i₀, (μ i₀).wt x * Real.exp (lam * (m x - (μ i₀).exp m)) := rfl
              have hmul : Real.exp (lam ^ 2 * (∑ i ∈ S, (c i) ^ 2) / 8) *
                    (∑ x : Ω i₀, (μ i₀).wt x * Real.exp (lam * (m x - (μ i₀).exp m)))
                  = ∑ x : Ω i₀, Real.exp (lam ^ 2 * (∑ i ∈ S, (c i) ^ 2) / 8) *
                      ((μ i₀).wt x * Real.exp (lam * (m x - (μ i₀).exp m))) :=
                Finset.mul_sum _ _ _
              rw [hEm, hexp, hmul]
              exact Finset.sum_congr rfl fun x _ => by ring
        _ ≤ Real.exp (lam ^ 2 * (∑ i ∈ S, (c i) ^ 2) / 8) *
              Real.exp (lam ^ 2 * (c i₀) ^ 2 / 8) :=
              mul_le_mul_of_nonneg_left hone (Real.exp_nonneg _)
        _ = Real.exp (lam ^ 2 * (∑ i ∈ insert i₀ S, (c i) ^ 2) / 8) := by
              rw [← Real.exp_add, Finset.sum_insert hi]
              congr 1
              ring

/-! ## The tail bound from the moment bound -/

/-- Optimised Markov bound: from the exponential moment bound with the optimal `λ = 4 t / S2`
one gets `P(Z - E Z > t) ≤ exp (-(2 t ^ 2) / S2)`. -/
lemma tail_of_mgf (μ : ∀ i, FinProb (Ω i)) {Z : (∀ i, Ω i) → ℝ} {S2 lam t : ℝ}
    (hmgf : (FinProb.pi μ).exp (fun f => Real.exp (lam * (Z f - (FinProb.pi μ).exp Z)))
      ≤ Real.exp (lam ^ 2 * S2 / 8))
    (hlam_pos : 0 < lam) (hS2_pos : 0 < S2) (hlam : lam = 4 * t / S2) :
    (FinProb.pi μ).prob {f | t < Z f - (FinProb.pi μ).exp Z} ≤ Real.exp (-(2 * t ^ 2) / S2) := by
  have hKpos : 0 < Real.exp (lam * t) := Real.exp_pos _
  have hmk : (FinProb.pi μ).prob {f | t < Z f - (FinProb.pi μ).exp Z} * Real.exp (lam * t)
      ≤ (FinProb.pi μ).exp (fun f => Real.exp (lam * (Z f - (FinProb.pi μ).exp Z))) :=
    prob_mul_le_exp _ _ _ (fun f => Real.exp_nonneg _) (fun f hf =>
      Real.exp_le_exp.mpr (le_of_lt (mul_lt_mul_of_pos_left hf hlam_pos)))
  have h1 : (FinProb.pi μ).prob {f | t < Z f - (FinProb.pi μ).exp Z} * Real.exp (lam * t)
      ≤ Real.exp (lam ^ 2 * S2 / 8) := le_trans hmk hmgf
  have hexp : Real.exp (lam ^ 2 * S2 / 8) / Real.exp (lam * t) = Real.exp (-(2 * t ^ 2) / S2) := by
    rw [← Real.exp_sub]
    congr 1
    rw [hlam]
    field_simp
    ring
  rw [← le_div_iff₀ hKpos] at h1
  rwa [hexp] at h1

end Work.Deep.Reed.Prob

namespace Work.Deep.Reed.Prob

/-- **Bounded differences (Azuma–Hoeffding) in a product space.**

If `X` is a real-valued function on the product of finite probability spaces and
changing the `i`-th coordinate changes `X` by at most `c i`, then `X` is
concentrated around its expectation: for `t ≥ 0`,
`Pr[|X - E X| > t] ≤ 2 exp(-2t² / ∑ i, c i²)`.

This is the workhorse of the naive colouring procedure: applied to a variable
depending on the colours of the `≤ Δ` neighbours of a vertex it gives
`Pr[|X - E X| > t] ≤ 2 exp(-t²/(2Δ))` when each colour change moves `X` by at
most `2`.  The standard proof is the exponential-martingale argument
(Hoeffding's bound on the conditional exponential moments). -/
theorem hoeffding_bounded_differences {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (μ : ∀ i, FinProb (Ω i))
    (X : (∀ i, Ω i) → ℝ) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hlip : ∀ (i : ι) (f : ∀ i, Ω i) (x : Ω i), |X (Function.update f i x) - X f| ≤ c i)
    {t : ℝ} (ht : 0 ≤ t) :
    (FinProb.pi μ).prob {f | t < |X f - (FinProb.pi μ).exp X|}
      ≤ 2 * Real.exp (-(2 * t ^ 2) / ∑ i, (c i) ^ 2) := by
  classical
  by_cases hS : (∑ i, (c i) ^ 2) = 0
  · rw [hS, div_zero, Real.exp_zero, mul_one]
    exact le_trans (FinProb.prob_le_one _ _) (by norm_num)
  · by_cases ht0 : t = 0
    · subst ht0
      rw [show (-(2 * (0 : ℝ) ^ 2)) / (∑ i, (c i) ^ 2) = 0 by simp, Real.exp_zero, mul_one]
      exact le_trans (FinProb.prob_le_one _ _) (by norm_num)
    · have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
      have hS_nonneg : 0 ≤ ∑ i, (c i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (c i)
      have hS_pos : 0 < ∑ i, (c i) ^ 2 := lt_of_le_of_ne hS_nonneg (Ne.symm hS)
      set S2 : ℝ := ∑ i, (c i) ^ 2 with hS2
      have hS2_pos : 0 < S2 := by rw [hS2]; exact hS_pos
      set lam : ℝ := 4 * t / S2 with hlam
      have hlam_pos : 0 < lam := by rw [hlam]; positivity
      obtain g₀ : ∀ i, Ω i := fun i => Classical.choice ((μ i).nonempty_of_finprob)
      have hmgf : (FinProb.pi μ).exp (fun f => Real.exp (lam * (X f - (FinProb.pi μ).exp X)))
          ≤ Real.exp (lam ^ 2 * S2 / 8) := by
        have h := mgf_frozen μ X c hc hlip lam Finset.univ g₀
        rw [frozenFamily_univ, ← hS2] at h
        exact h
      have hupper : (FinProb.pi μ).prob {f | t < X f - (FinProb.pi μ).exp X}
          ≤ Real.exp (-(2 * t ^ 2) / S2) := tail_of_mgf μ hmgf hlam_pos hS2_pos hlam
      have hexpneg : (FinProb.pi μ).exp (fun f => -X f) = -(FinProb.pi μ).exp X := by
        have h := FinProb.exp_mul_left (FinProb.pi μ) (-1) X
        simpa using h
      have hmgf' : (FinProb.pi μ).exp
            (fun f => Real.exp (lam * ((fun f => -X f) f - (FinProb.pi μ).exp (fun f => -X f))))
          ≤ Real.exp (lam ^ 2 * S2 / 8) := by
        have hlip' : ∀ (i : ι) (f : ∀ i, Ω i) (x : Ω i),
            |(fun g => -X g) (Function.update f i x) - (fun g => -X g) f| ≤ c i := by
          intro i f x
          have hh := hlip i f x
          have h1 : (fun g => -X g) (Function.update f i x) - (fun g => -X g) f
              = -(X (Function.update f i x) - X f) := by ring
          rw [h1, abs_neg]
          exact hh
        have h := mgf_frozen μ (fun f => -X f) c hc hlip' lam Finset.univ g₀
        rw [frozenFamily_univ, ← hS2] at h
        exact h
      have hlower : (FinProb.pi μ).prob {f | t < -(X f - (FinProb.pi μ).exp X)}
          ≤ Real.exp (-(2 * t ^ 2) / S2) := by
        have h := tail_of_mgf μ hmgf' hlam_pos hS2_pos hlam
        convert h using 2
        ext f
        simp only [Set.mem_setOf_eq, hexpneg]
        ring_nf
      have hsub : {f | t < |X f - (FinProb.pi μ).exp X|}
          ⊆ {f | t < X f - (FinProb.pi μ).exp X}
            ∪ {f | t < -(X f - (FinProb.pi μ).exp X)} := by
        intro f hf
        rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
        exact lt_abs.mp hf
      have hmain : (FinProb.pi μ).prob {f | t < |X f - (FinProb.pi μ).exp X|}
          ≤ Real.exp (-(2 * t ^ 2) / S2) + Real.exp (-(2 * t ^ 2) / S2) := by
        calc (FinProb.pi μ).prob {f | t < |X f - (FinProb.pi μ).exp X|}
            ≤ (FinProb.pi μ).prob ({f | t < X f - (FinProb.pi μ).exp X}
                ∪ {f | t < -(X f - (FinProb.pi μ).exp X)}) := FinProb.prob_mono _ hsub
          _ ≤ (FinProb.pi μ).prob {f | t < X f - (FinProb.pi μ).exp X}
                + (FinProb.pi μ).prob {f | t < -(X f - (FinProb.pi μ).exp X)} :=
              FinProb.prob_union_le _ _ _
          _ ≤ Real.exp (-(2 * t ^ 2) / S2) + Real.exp (-(2 * t ^ 2) / S2) :=
              add_le_add hupper hlower
      calc (FinProb.pi μ).prob {f | t < |X f - (FinProb.pi μ).exp X|}
          ≤ Real.exp (-(2 * t ^ 2) / S2) + Real.exp (-(2 * t ^ 2) / S2) := hmain
        _ = 2 * Real.exp (-(2 * t ^ 2) / S2) := by ring

end Work.Deep.Reed.Prob
