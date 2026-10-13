import Mathlib
import Submission.Work.WilE3.eaEval_analytic
import Submission.Work.WilE3.Taylor.Polar.Basic
import Submission.Work.WilE3.Taylor.Polar.Lagrange

namespace Work.WilE3.Taylor.Grad

open Filter Topology
open scoped Topology

/-!
  annals_wilkies_conjecture, AREA E3: the order bookkeeping `gradOrderLe`.

  Along an analytic arc `γ` through a point `y` with `a := ord₀(γ - y) > 0`, the order
  `m := ord₀(Φ ∘ γ)` of the composite dominates `r + a`, where `r` bounds the order of vanishing
  of every partial derivative `∂ₗΦ ∘ γ`.  The reason is the one-variable chain rule

    `(Φ ∘ γ)'(t) = Σ_l (∂ₗΦ)(γ t) · γ_l'(t)`,

  read at the level of orders: each summand has order at least `r + (a - 1)` (the factor `γ_l'`
  has order at least `a - 1` because `γ_l - y_l` has order at least `a > 0`), a finite sum has
  order at least the minimum of its summands, and `ord₀((Φ ∘ γ)') = m - 1` because `m > 0`.
-/

/-- If a finite pointwise sum of functions has all its summands of order at least `N` at `0`,
then the sum has order at least `N` at `0`. -/
lemma le_order_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) {f : ι → ℝ → ℝ} {N : ℕ∞}
    (hN : ∀ i ∈ s, N ≤ analyticOrderAt (f i) 0) :
    N ≤ analyticOrderAt (fun t => ∑ i ∈ s, f i t) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hzero : (fun t : ℝ => ∑ i ∈ (∅ : Finset ι), f i t) = (0 : ℝ → ℝ) := by
        funext t; simp
      rw [hzero, analyticOrderAt_zero]
      exact le_top
  | insert a s ha ih =>
      have hstep : (fun t : ℝ => ∑ i ∈ insert a s, f i t)
          = f a + (fun t : ℝ => ∑ i ∈ s, f i t) := by
        funext t; rw [Finset.sum_insert ha]; rfl
      rw [hstep]
      exact (le_min (hN a (Finset.mem_insert_self a s))
        (ih fun i hi => hN i (Finset.mem_insert_of_mem hi))).trans le_analyticOrderAt_add

theorem gradOrderLe {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {γ : ℝ → Fin k → ℝ} {y : Fin k → ℝ}
    {a m r : ℕ}
    (hγ : AnalyticAt ℝ γ 0) (hΦ : ∀ x, AnalyticAt ℝ Φ x)
    (ha : 0 < a) (hm : 0 < m)
    (hram : analyticOrderAt (fun t : ℝ => γ t - y) 0 = a)
    (hord : analyticOrderAt (fun t : ℝ => Φ (γ t)) 0 = m)
    (hr : ∀ l : Fin k, (r : ℕ∞) ≤
      analyticOrderAt (fun t : ℝ => Work.WilE3.Taylor.grad Φ (γ t) l) 0) :
    r + a ≤ m := by
  classical
  -- component analyticity of `γ`
  have hγc : ∀ l : Fin k, AnalyticAt ℝ (fun t : ℝ => γ t l) 0 :=
    (analyticAt_pi_iff (f := fun l t => γ t l) (e := (0 : ℝ))).mp hγ
  -- factorisation `γ t - y = t ^ a • g t` of the components of `γ - y`
  have hsub_an : AnalyticAt ℝ (fun t : ℝ => γ t - y) 0 := hγ.sub analyticAt_const
  obtain ⟨g, hg_an, _hg0, hg_eq⟩ := (hsub_an.analyticOrderAt_eq_natCast).mp hram
  have hgc : ∀ l : Fin k, AnalyticAt ℝ (fun t : ℝ => g t l) 0 :=
    (analyticAt_pi_iff (f := fun l t => g t l) (e := (0 : ℝ))).mp hg_an
  -- `γ 0 = y`
  have hsub_zero : (fun t : ℝ => γ t - y) 0 = 0 := by
    have h := hg_eq.self_of_nhds
    simpa [zero_pow (ne_of_gt ha)] using h
  -- every component of `γ - y` vanishes to order at least `a`
  have hcomp : ∀ l : Fin k, (a : ℕ∞) ≤ analyticOrderAt (fun t : ℝ => γ t l - y l) 0 := by
    intro l
    have han : AnalyticAt ℝ (fun t : ℝ => γ t l - y l) 0 := (hγc l).sub analyticAt_const
    rw [natCast_le_analyticOrderAt han]
    refine ⟨fun t => g t l, hgc l, ?_⟩
    filter_upwards [hg_eq] with t ht
    simpa using congrFun ht l
  -- the derivative of each component has order at least `a - 1`
  have hW : ∀ l : Fin k,
      ((a - 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun t => deriv (fun s : ℝ => γ s l) t) 0 := by
    intro l
    have han : AnalyticAt ℝ (fun t : ℝ => γ t l - y l) 0 := (hγc l).sub analyticAt_const
    have h0 : (fun t : ℝ => γ t l - y l) 0 = 0 := by
      have := congrFun hsub_zero l; simpa using this
    have hiff := analyticOrderAt_deriv_ge_iff han h0 (n := a - 1)
    have hcast : ((a - 1 : ℕ) : ℕ∞) + 1 = (a : ℕ∞) := by
      have h : (a - 1 : ℕ) + 1 = a := Nat.sub_add_cancel (Nat.one_le_of_lt ha)
      exact_mod_cast h
    rw [hcast] at hiff
    have hgot := hiff.mpr (hcomp l)
    rwa [show deriv (fun t : ℝ => γ t l - y l) = deriv (fun s : ℝ => γ s l) from
      funext fun t => deriv_sub_const (y l)] at hgot
  -- analyticity of the gradient components
  have hA_an : ∀ l : Fin k,
      AnalyticAt ℝ (fun t : ℝ => Work.WilE3.Taylor.grad Φ (γ t) l) 0 := by
    intro l
    set v : Fin k → ℝ := Pi.single l (1:ℝ) with hv
    have h1 : AnalyticAt ℝ (fun t : ℝ => fderiv ℝ Φ (γ t)) 0 := ((hΦ (γ 0)).fderiv).comp hγ
    have h2 : AnalyticAt ℝ
        (fun t : ℝ => (ContinuousLinearMap.apply ℝ ℝ v) (fderiv ℝ Φ (γ t))) 0 :=
      AnalyticAt.comp (x := (0:ℝ)) (f := fun t : ℝ => fderiv ℝ Φ (γ t))
        ((ContinuousLinearMap.apply ℝ ℝ v).analyticAt (fderiv ℝ Φ (γ 0))) h1
    simpa [Work.WilE3.Taylor.grad, hv] using h2
  have hW_an : ∀ l : Fin k, AnalyticAt ℝ (fun t : ℝ => deriv (fun s : ℝ => γ s l) t) 0 :=
    fun l => (hγc l).deriv
  -- the one-variable chain rule
  have hchain : deriv (fun t : ℝ => Φ (γ t)) =ᶠ[𝓝 0]
      fun t => ∑ l : Fin k, Work.WilE3.Taylor.grad Φ (γ t) l * deriv (fun s : ℝ => γ s l) t := by
    filter_upwards [hγ.eventually_analyticAt] with t ht
    have h1 : HasDerivAt γ (deriv γ t) t := ht.differentiableAt.hasDerivAt
    have h2 : HasFDerivAt Φ (fderiv ℝ Φ (γ t)) (γ t) := ((hΦ (γ t)).differentiableAt).hasFDerivAt
    have h3 : deriv (fun t : ℝ => Φ (γ t)) t = fderiv ℝ Φ (γ t) (deriv γ t) := by
      simpa [Function.comp_def] using (h2.comp_hasDerivAt t h1).deriv
    rw [h3, Work.WilE3.Taylor.fderiv_eq_sum_grad]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [deriv_pi (fun l => ((analyticAt_pi_iff.mp ht) l).differentiableAt)]
    ring
  -- orders of `Φ ∘ γ` and of its derivative
  have hf_an : AnalyticAt ℝ (fun t : ℝ => Φ (γ t)) 0 := (hΦ (γ 0)).comp hγ
  have hf0 : (fun t : ℝ => Φ (γ t)) 0 = 0 := by
    obtain ⟨u, _hu_an, _hu0, hu_eq⟩ := (hf_an.analyticOrderAt_eq_natCast).mp hord
    have h := hu_eq.self_of_nhds
    simpa [zero_pow (ne_of_gt hm)] using h
  have hderiv_ord : analyticOrderAt (deriv (fun t : ℝ => Φ (γ t))) 0 = ((m - 1 : ℕ) : ℕ∞) := by
    have hiff := analyticOrderAt_deriv_eq_iff hf_an hf0 (n := m - 1)
    have hcast : ((m - 1 : ℕ) : ℕ∞) + 1 = (m : ℕ∞) := by
      have h : (m - 1 : ℕ) + 1 = m := Nat.sub_add_cancel (Nat.one_le_of_lt hm)
      exact_mod_cast h
    rw [hcast] at hiff
    exact hiff.mp hord
  -- the sum of the chain rule has order at least `r + a - 1`
  have hfin : ((r + a - 1 : ℕ) : ℕ∞) ≤ ((m - 1 : ℕ) : ℕ∞) := by
    rw [← hderiv_ord, analyticOrderAt_congr hchain]
    refine le_order_sum Finset.univ (f := fun l : Fin k =>
      (fun t : ℝ => Work.WilE3.Taylor.grad Φ (γ t) l)
        * (fun t : ℝ => deriv (fun s : ℝ => γ s l) t)) ?_
    intro l _
    rw [analyticOrderAt_mul (hA_an l) (hW_an l)]
    have h1 : (r : ℕ∞) ≤ analyticOrderAt (fun t : ℝ => Work.WilE3.Taylor.grad Φ (γ t) l) 0 :=
      hr l
    have h2 : (r : ℕ∞) + ((a - 1 : ℕ) : ℕ∞) = ((r + a - 1 : ℕ) : ℕ∞) := by
      rw [← Nat.cast_add]
      congr 1
      omega
    rw [← h2]
    exact add_le_add h1 (hW l)
  have h1 : r + a - 1 ≤ m - 1 := ENat.natCast_le_natCast.mp hfin
  exact (Nat.sub_le_sub_iff_right (k := 1) (n := r + a) (m := m) hm).mp h1

end Work.WilE3.Taylor.Grad
