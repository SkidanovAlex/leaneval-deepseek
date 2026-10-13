import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.Taylor.Grad.exists_order_of_partial
import Submission.Work.WilE3.Taylor.Grad.gradOrderLe
import Submission.Work.WilE3.eaEval_analytic
import Submission.Work.WilE3.Taylor.Grad.order_deriv_eq_pred
import Submission.Work.WilE3.Taylor.Grad.deriv_eaEval_eventually

namespace Work.WilE3.Taylor.Grad

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / Grad: **the minimal order of the partial
  derivatives along an analytic arc is finite and strictly smaller than the order of `Φ ∘ γ`.**

  Let `γ` be an analytic arc through `y = γ 0` along which `Φ ∘ γ` has the *finite positive*
  order `m` at `0`.  Then among the `k` partial derivatives `∂ᵢΦ ∘ γ` (in the EA vocabulary
  `eaD c i Φ`) one of minimal order occurs, that minimal order `n` is a natural number (not `⊤`),
  and `n < m`.

  Both halves of the statement come from one application of the one-variable chain rule

    `(Φ ∘ γ)'(t) = Σⱼ (∂ⱼΦ)(γ t) · γⱼ'(t)`

  combined with the order bookkeeping of `gradOrderLe.le_order_sum`:

  * if *all* the partial derivatives had order `≥ m`, then every summand on the right would have
    order `≥ m + ord₀(γⱼ') ≥ m`, hence the derivative of `Φ ∘ γ` would have order `≥ m`, whereas
    `ord₀((Φ ∘ γ)') = m - 1 < m` (the order of an analytic function of order `m > 0`);
  * a finite family of orders in `ℕ∞` has an attained minimum, and by the previous point that
    minimum is `< m`, so it is finite.
-/

theorem exists_min_order_partial {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (Φ : WilkiesDesign.E.EAPoly k r) (y : Fin k → ℝ) (γ : ℝ → Fin k → ℝ) (m : ℕ)
    (hγ : AnalyticAt ℝ γ 0) (hγ0 : γ 0 = y) (hm : 0 < m)
    (hord : analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) 0 = m) :
    ∃ (i : Fin k) (n : ℕ),
      analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i Φ) (γ t)) 0
        = n ∧
      n < m ∧
      ∀ j : Fin k, (n : ℕ∞) ≤
        analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c j Φ) (γ t)) 0 := by
  classical
  -- analyticity of `Φ ∘ γ`, of the partial derivatives `∂ⱼΦ ∘ γ` and of the arc derivatives
  have hF_an : AnalyticAt ℝ (fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) 0 :=
    (Work.WilE3.eaEval_analytic c Φ (γ 0)).comp hγ
  have hG_an : ∀ j : Fin k,
      AnalyticAt ℝ (fun t : ℝ => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c j Φ) (γ t)) 0 :=
    fun j => (Work.WilE3.eaEval_analytic c (WilkiesDesign.E.eaD c j Φ) (γ 0)).comp hγ
  have hgp_an : ∀ j : Fin k, AnalyticAt ℝ (fun t : ℝ => deriv (fun s : ℝ => γ s j) t) 0 :=
    fun j => ((analyticAt_pi_iff (f := fun l t => γ t l) (e := (0 : ℝ))).mp hγ j).deriv
  -- `ord₀((Φ ∘ γ)') = m - 1`
  have hderiv_ord : analyticOrderAt (deriv (fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t))) 0
      = ((m - 1 : ℕ) : ℕ∞) := (order_deriv_eq_pred hF_an hm hord).2
  -- (i) some partial derivative has order `< m`
  have hsome : ∃ i : Fin k,
      analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i Φ) (γ t)) 0
        < (m : ℕ∞) := by
    by_cases hall : ∀ j : Fin k, (m : ℕ∞) ≤
        analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c j Φ) (γ t)) 0
    · -- if every partial derivative had order `≥ m`, then so would the derivative of `Φ ∘ γ`
      have hsh : ∀ j : Fin k, (m : ℕ∞) ≤
          analyticOrderAt (fun t : ℝ =>
            WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c j Φ) (γ t) *
              deriv (fun s : ℝ => γ s j) t) 0 := by
        intro j
        change (m : ℕ∞) ≤ analyticOrderAt
          ((fun t : ℝ => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c j Φ) (γ t)) *
            (fun t : ℝ => deriv (fun s : ℝ => γ s j) t)) 0
        rw [analyticOrderAt_mul (hG_an j) (hgp_an j)]
        exact le_trans (hall j) le_self_add
      have hsum : (m : ℕ∞) ≤
          analyticOrderAt (fun t : ℝ => ∑ j : Fin k,
            WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c j Φ) (γ t) *
              deriv (fun s : ℝ => γ s j) t) 0 :=
        le_order_sum Finset.univ (fun j _ => hsh j)
      have hcontra : (m : ℕ∞) ≤ ((m - 1 : ℕ) : ℕ∞) := by
        rw [← analyticOrderAt_congr (deriv_eaEval_eventually c Φ γ hγ), hderiv_ord] at hsum
        exact hsum
      have hmle : m ≤ m - 1 := ENat.natCast_le_natCast.mp hcontra
      exact absurd hmle (Nat.not_le.mpr (Nat.sub_lt hm (by norm_num)))
    · have h := not_forall.mp hall
      obtain ⟨j, hj⟩ := h
      exact ⟨j, not_le.mp hj⟩
  -- (ii) the minimum over the partial derivatives is attained
  obtain ⟨i₀, hi₀⟩ := hsome
  have hne_k : Nonempty (Fin k) := ⟨i₀⟩
  obtain ⟨i, -, hmin⟩ := Finset.exists_min_image Finset.univ
    (fun j : Fin k =>
      analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c j Φ) (γ t)) 0)
    Finset.univ_nonempty
  have hlt : analyticOrderAt
      (fun t : ℝ => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i Φ) (γ t)) 0 < (m : ℕ∞) :=
    lt_of_le_of_lt (hmin i₀ (Finset.mem_univ i₀)) hi₀
  -- by (i), the minimum is finite
  have hne : analyticOrderAt
      (fun t : ℝ => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i Φ) (γ t)) 0 ≠ ⊤ := by
    intro htop
    rw [htop] at hlt
    exact absurd hlt (not_lt.mpr le_top)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  refine ⟨i, n, hn.symm, ?_, ?_⟩
  · have hlt' : (n : ℕ∞) < (m : ℕ∞) := by rw [hn]; exact hlt
    exact ENat.natCast_lt_natCast.mp hlt'
  · intro j
    rw [hn]
    exact hmin j (Finset.mem_univ j)

end Work.WilE3.Taylor.Grad
