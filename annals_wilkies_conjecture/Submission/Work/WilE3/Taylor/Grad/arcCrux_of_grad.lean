import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.Taylor.Grad.hinge
import Submission.Work.WilE3.eaEval_analytic
import Submission.Work.WilE3.Taylor.Grad.exists_min_order_partial
import Submission.Work.WilE3.Taylor.Grad.order_le_of_rpow_le

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / Grad: `arcCrux_of_grad`.

  The *converse* of the hinge `ea_grad_of_arcCrux`: the effective gradient inequality `(GRAD)` for EA
  functions (Gabrielov 1995, Theorem 3.3) implies the *arc crux* `ArcCrux`.

  The argument is the asymptotic analysis of `(GRAD)` along an analytic arc `γ` through `y = γ 0`
  with `ord₀ (Φ ∘ γ) = m > 0`.  The domain `Fin k → ℝ` carries the sup norm, so
  `‖fderiv ℝ Φ x‖ = ∑ l |∂_l Φ x| ≤ √k · ‖∇Φ x‖₂`; along `γ` the inequality therefore reads
  `cst · |(Φ ∘ γ) t| ^ κ ≤ ∑ l |(∂_l Φ ∘ γ) t|`.  Let `n` be the *minimal* order of the partial
  derivatives along `γ` (`exists_min_order_partial`); writing `Φ ∘ γ = t ^ m · g` with `g 0 ≠ 0` and
  `∂_l Φ ∘ γ = t ^ n · w_l` with `w_l` continuous, the sum on the right is `t ^ n · σ t` with
  `σ 0 > 0`, so dividing by `t ^ n` and letting `t → 0⁺` gives `n ≤ κ m` (`order_le_of_rpow_le`).
  Finally `1 / (1 - κ) ≤ A := K.eval (atomDeg Φ)` gives `κ ≤ (A - 1) / A ≤ A / (A + 1)`, whence
  `(A + 1) n ≤ A m`, the bound of `ArcCrux`.

  The hypothesis `PolarLike` is *not* used: the gradient inequality alone suffices.
-/

namespace Work.WilE3.Taylor.Grad

open Filter Set
open scoped Topology
open WilkiesDesign.E

theorem norm_fderiv_le_sum_abs_grad {k : ℕ} (f : (Fin k → ℝ) → ℝ) (x : Fin k → ℝ) :
    ‖fderiv ℝ f x‖ ≤ ∑ l : Fin k, |Work.WilE3.Taylor.grad f x l| := by
  rw [ContinuousLinearMap.opNorm_le_iff (Finset.sum_nonneg fun l _ => abs_nonneg _)]
  intro v
  rw [Work.WilE3.Taylor.Grad.fderiv_apply_eq_sum_grad]
  rw [Real.norm_eq_abs]
  calc |∑ l : Fin k, v l * Work.WilE3.Taylor.grad f x l|
      ≤ ∑ l : Fin k, |v l * Work.WilE3.Taylor.grad f x l| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ l : Fin k, |v l| * |Work.WilE3.Taylor.grad f x l| := by
        exact Finset.sum_congr rfl fun l _ => abs_mul _ _
    _ ≤ ∑ l : Fin k, ‖v‖ * |Work.WilE3.Taylor.grad f x l| := by
        exact Finset.sum_le_sum fun l _ => by
          gcongr
          exact norm_le_pi_norm v l
    _ = (∑ l : Fin k, |Work.WilE3.Taylor.grad f x l|) * ‖v‖ := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- Arithmetic step: the gradient bound `1/(1-κ) ≤ A` and `n ≤ κ m` give `(A+1) n ≤ A m`. -/
lemma arith_bound {A n m : ℕ} {κ : ℝ}
    (hκ1 : κ < 1) (hA : 1 / (1 - κ) ≤ (A : ℝ))
    (hnle : (n : ℝ) ≤ κ * m) :
    (A + 1) * n ≤ A * m := by
  have h1mk : (0:ℝ) < 1 - κ := by linarith
  have hAnonneg : (0:ℝ) ≤ (A:ℝ) := Nat.cast_nonneg A
  have hAmul : (1:ℝ) ≤ (A:ℝ) * (1 - κ) := by
    have h := mul_le_mul_of_nonneg_right hA (le_of_lt h1mk)
    rwa [one_div, inv_mul_cancel₀ h1mk.ne'] at h
  have hkey : κ * (A:ℝ) ≤ (A:ℝ) - 1 := by nlinarith [hAmul, hAnonneg]
  have hstep : ((A:ℝ) + 1) * κ < (A:ℝ) := by nlinarith [hkey, hκ1, hAnonneg]
  have hreal : (((A + 1) * n : ℕ) : ℝ) ≤ ((A * m : ℕ) : ℝ) := by
    push_cast
    calc ((A:ℝ) + 1) * (n:ℝ) ≤ ((A:ℝ) + 1) * (κ * (m:ℝ)) := by
          apply mul_le_mul_of_nonneg_left hnle; positivity
      _ = (((A:ℝ) + 1) * κ) * (m:ℝ) := by ring
      _ ≤ (A:ℝ) * (m:ℝ) :=
          mul_le_mul_of_nonneg_right (le_of_lt hstep) (Nat.cast_nonneg m)
  exact_mod_cast hreal

theorem arcCrux_of_grad
    (hgrad : ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : WilkiesDesign.E.EAChain k r)
      (Φ : WilkiesDesign.E.EAPoly k r) (y : Fin k → ℝ), k + r ≤ F →
      WilkiesDesign.E.eaEval c Φ y = 0 →
      ∃ (κ cst : ℝ), 0 ≤ κ ∧ κ < 1 ∧ 0 < cst ∧
        1 / (1 - κ) ≤ ((K.eval (WilkiesDesign.E.atomDeg Φ) : ℕ) : ℝ) ∧
        (∀ᶠ x in nhds y, cst * |WilkiesDesign.E.eaEval c Φ x| ^ κ ≤
          ‖fderiv ℝ (fun z : Fin k → ℝ => WilkiesDesign.E.eaEval c Φ z) x‖)) :
    Work.WilE3.Taylor.Grad.ArcCrux := by
  intro F
  obtain ⟨K, hK⟩ := hgrad F
  refine ⟨K, ?_⟩
  intro k r c Φ y γ m hkr hγan hγ0 hm hord hPolar
  -- ## Step 1: `Φ y = 0`
  have hGan : AnalyticAt ℝ (fun t : ℝ => eaEval c Φ (γ t)) 0 :=
    (Work.WilE3.eaEval_analytic c Φ (γ 0)).comp hγan
  have hΦy : eaEval c Φ y = 0 := by
    have hne : analyticOrderAt (fun t : ℝ => eaEval c Φ (γ t)) 0 ≠ 0 := by
      rw [hord]
      intro h
      exact hm.ne' (ENat.natCast_inj.mp h)
    have h0 := apply_eq_zero_of_analyticOrderAt_ne_zero hne
    rwa [hγ0] at h0
  -- ## Step 2: apply the gradient hypothesis
  obtain ⟨κ, cst, hκnn, hκlt1, hcst, hκbound, hinev⟩ := hK k r c Φ y hkr hΦy
  -- ## Step 3: the minimal partial derivative
  obtain ⟨i, n, hvi, hnm, hmin⟩ :=
    exists_min_order_partial c Φ y γ m hγan hγ0 hm hord
  have hvjan : ∀ j : Fin k, AnalyticAt ℝ (fun t : ℝ => eaEval c (eaD c j Φ) (γ t)) 0 :=
    fun j => (Work.WilE3.eaEval_analytic c (eaD c j Φ) (γ 0)).comp hγan
  -- ## Step 4: factorisations
  obtain ⟨g, hgan, hg0, hGg⟩ := (hGan.analyticOrderAt_eq_natCast).mp hord
  have hGg' : (fun t : ℝ => eaEval c Φ (γ t)) =ᶠ[nhds (0 : ℝ)] fun t => t ^ m * g t := by
    filter_upwards [hGg] with t ht
    rw [ht]
    simp [smul_eq_mul]
  choose w hwan hvw0 using fun j : Fin k => (natCast_le_analyticOrderAt (hvjan j)).mp (hmin j)
  obtain ⟨gi, hgian, hgi0, hvigi⟩ := (hvjan i).analyticOrderAt_eq_natCast.mp hvi
  set W : Fin k → ℝ → ℝ := Function.update w i gi with hWdef
  have hWi : W i = gi := by rw [hWdef]; exact Function.update_self i gi w
  have hWj : ∀ j : Fin k, j ≠ i → W j = w j := by
    intro j hj; rw [hWdef]; exact Function.update_of_ne hj gi w
  have hWcont : ∀ j : Fin k, ContinuousAt (W j) 0 := by
    intro j
    by_cases h : j = i
    · rw [show W j = gi by rw [h, hWi]]
      exact hgian.continuousAt
    · rw [hWj j h]
      exact (hwan j).continuousAt
  have hWi0 : W i 0 ≠ 0 := by rw [hWi]; exact hgi0
  have hvw : ∀ j : Fin k,
      (fun t : ℝ => eaEval c (eaD c j Φ) (γ t)) =ᶠ[nhds (0 : ℝ)] fun t => t ^ n * W j t := by
    intro j
    by_cases h : j = i
    · subst h
      filter_upwards [hvigi] with t ht
      rw [ht]
      simp [smul_eq_mul, hWi]
    · filter_upwards [hvw0 j] with t ht
      rw [ht]
      simp only [sub_zero, smul_eq_mul]
      rw [hWj j h]
  -- ## Step 5: the inequality along the arc
  have hineq : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      cst * |eaEval c Φ (γ t)| ^ κ ≤ ∑ j : Fin k, |eaEval c (eaD c j Φ) (γ t)| := by
    have hγT : Tendsto γ (nhds (0 : ℝ)) (nhds y) := by
      have h := hγan.continuousAt.tendsto
      rwa [hγ0] at h
    filter_upwards [hγT.eventually hinev |>.filter_mono nhdsWithin_le_nhds] with t ht
    refine le_trans ht ?_
    calc ‖fderiv ℝ (fun z : Fin k → ℝ => eaEval c Φ z) (γ t)‖
        ≤ ∑ l : Fin k, |Work.WilE3.Taylor.grad (fun z : Fin k → ℝ => eaEval c Φ z) (γ t) l| :=
          norm_fderiv_le_sum_abs_grad _ _
      _ = ∑ l : Fin k, |eaEval c (eaD c l Φ) (γ t)| :=
          Finset.sum_congr rfl fun l _ => by rw [grad_eq_eaD]
  -- ## Step 6: `n ≤ κ m`
  have hnle : (n : ℝ) ≤ κ * m :=
    order_le_of_rpow_le (G := fun t : ℝ => eaEval c Φ (γ t))
      (v := fun (j : Fin k) (t : ℝ) => eaEval c (eaD c j Φ) (γ t)) (g := g) (w := W) (i := i)
      (m := m) (n := n) (κ := κ) (c := cst)
      hgan.continuousAt hg0 hGg' hWcont hWi0 hvw hcst hκnn hineq
  exact ⟨i, n, hvi, arith_bound (A := K.eval (atomDeg Φ)) (n := n) (m := m)
    (κ := κ) hκlt1 hκbound hnle⟩

end Work.WilE3.Taylor.Grad
