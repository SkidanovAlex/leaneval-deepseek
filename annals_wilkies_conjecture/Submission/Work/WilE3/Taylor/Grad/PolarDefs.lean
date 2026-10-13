import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE5.Basic

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor: the **EA gradient-polar system** of Gabrielov 1995
  §3, Theorem 3.3, in concrete EA form.

  This module is the *low* half of `Submission/Work/WilE3/Taylor/hasLoj_of_multiplicity.lean`:
  the target file imports it, and so do the polar-counting modules (`Grad/polarCount_goodLevel`,
  `Grad/polarPointsAtLevel`, `Grad/polarSys_eval_toC_eq_zero`), which is why the definitions live
  here rather than in the target file itself (it must be *below* `Grad/polarCount_goodLevel` in the
  import order for the final assembly to be able to use `polarCount_goodLevel`).

  Contents: `sqGrad` (`φ = ∑ₗ (∂ₗΦ)²`), `gpolMinor` (the `2 × 2` minors of `(∇Φ, ∇φ)`),
  `polarSys` (the square system `(Φ, gpolMinor c Φ i₀ ·)`), their evaluations and the atom-degree
  bound `atomDeg (polarSys …) ≤ 3 atomDeg Φ + 3` — the degree range of
  `Work.WilE3.Taylor.HasLoj.polar_count_deformed` — and the vanishing criterion
  `polarSys_eq_zero_iff`.
-/

set_option autoImplicit false
noncomputable section
open Classical Topology
open WilkiesDesign.E

namespace Work.WilE3.Taylor

variable {k r : ℕ}

/-- `φ := ∑ₗ (∂ₗΦ)²`, the squared gradient norm of `Φ` (an EA polynomial). -/
def sqGrad (c : EAChain k r) (Φ : EAPoly k r) : EAPoly k r :=
  ∑ l : Fin k, (eaD c l Φ) ^ 2

/-- The **gradient-polar minor** `∂ᵢΦ · ∂ⱼφ - ∂ⱼΦ · ∂ᵢφ` (with `φ = sqGrad c Φ`).  The joint
vanishing of all the minors at a point with `∇Φ ≠ 0` says `∇φ ∥ ∇Φ` there, i.e. that the point is a
critical point of `φ` restricted to its `Φ`-level set. -/
def gpolMinor (c : EAChain k r) (Φ : EAPoly k r) (i j : Fin k) : EAPoly k r :=
  eaD c i Φ * eaD c j (sqGrad c Φ) - eaD c j Φ * eaD c i (sqGrad c Φ)

/-- The square **gradient-polar system** of `Φ` with pivot `i₀`: row `i₀` is `Φ` itself, and row
`i ≠ i₀` is the minor `gpolMinor c Φ i₀ i`.  On the open set where `∂_{i₀}Φ ≠ 0` its zero set is
`{Φ = 0} ∩ Σ`, because the vanishing of the `k - 1` minors with a fixed non-vanishing pivot row is
equivalent to `∇φ ∥ ∇Φ`. -/
def polarSys (c : EAChain k r) (Φ : EAPoly k r) (i₀ : Fin k) : Fin k → EAPoly k r :=
  fun i => if i = i₀ then Φ else gpolMinor c Φ i₀ i

/-- Evaluation of the squared gradient norm. -/
theorem eaEval_sqGrad (c : EAChain k r) (Φ : EAPoly k r) (x : Fin k → ℝ) :
    eaEval c (sqGrad c Φ) x = ∑ l : Fin k, (eaEval c (eaD c l Φ) x) ^ 2 := by
  simp [sqGrad, eaEval, map_sum, map_pow]

/-- Evaluation of the gradient-polar minors. -/
theorem eaEval_gpolMinor (c : EAChain k r) (Φ : EAPoly k r) (i j : Fin k) (x : Fin k → ℝ) :
    eaEval c (gpolMinor c Φ i j) x =
      eaEval c (eaD c i Φ) x * eaEval c (eaD c j (sqGrad c Φ)) x -
        eaEval c (eaD c j Φ) x * eaEval c (eaD c i (sqGrad c Φ)) x := by
  simp [gpolMinor, eaEval, MvPolynomial.eval_sub, MvPolynomial.eval_mul]

/-- Evaluation of the gradient-polar system. -/
theorem eaEval_polarSys (c : EAChain k r) (Φ : EAPoly k r) (i₀ i : Fin k) (x : Fin k → ℝ) :
    eaEval c (polarSys c Φ i₀ i) x =
      if i = i₀ then eaEval c Φ x else eaEval c (gpolMinor c Φ i₀ i) x := by
  by_cases h : i = i₀
  · simp [polarSys, h]
  · simp [polarSys, h]

/-- **The atom-degree bound for the gradient-polar system**: every row has atom degree
`≤ 3 · atomDeg Φ + 3`, the degree range of `HasLoj.polar_count_deformed`. -/
theorem atomDeg_polarSys_le (c : EAChain k r) (Φ : EAPoly k r) (i₀ i : Fin k) :
    atomDeg (polarSys c Φ i₀ i) ≤ 3 * atomDeg Φ + 3 := by
  have hsq : (sqGrad c Φ).totalDegree ≤ 2 * (Φ.totalDegree + 1) := by
    rw [sqGrad]
    refine MvPolynomial.totalDegree_finsetSum_le (s := Finset.univ)
      (f := fun l : Fin k => (eaD c l Φ) ^ 2) ?_
    intro l _
    have h := Work.WilE5.totalDegree_eaD_le c l Φ
    have h2 := MvPolynomial.totalDegree_pow (eaD c l Φ) 2
    omega
  have h1 : (eaD c i (sqGrad c Φ)).totalDegree ≤ 2 * (Φ.totalDegree + 1) + 1 :=
    le_trans (Work.WilE5.totalDegree_eaD_le c i (sqGrad c Φ)) (by omega)
  have h2 : (eaD c i₀ (sqGrad c Φ)).totalDegree ≤ 2 * (Φ.totalDegree + 1) + 1 :=
    le_trans (Work.WilE5.totalDegree_eaD_le c i₀ (sqGrad c Φ)) (by omega)
  have h3 : (eaD c i₀ Φ).totalDegree ≤ Φ.totalDegree + 1 :=
    Work.WilE5.totalDegree_eaD_le c i₀ Φ
  have h4 : (eaD c i Φ).totalDegree ≤ Φ.totalDegree + 1 :=
    Work.WilE5.totalDegree_eaD_le c i Φ
  have hmin : (gpolMinor c Φ i₀ i).totalDegree ≤ 3 * Φ.totalDegree + 4 := by
    rw [gpolMinor, sub_eq_add_neg]
    refine le_trans (MvPolynomial.totalDegree_add _ _) (max_le ?_ ?_)
    · refine le_trans (MvPolynomial.totalDegree_mul _ _) (by omega)
    · rw [MvPolynomial.totalDegree_neg]
      refine le_trans (MvPolynomial.totalDegree_mul _ _) (by omega)
  by_cases h : i = i₀
  · simp only [polarSys, h, if_true, atomDeg]
    omega
  · simp only [polarSys, h, if_false, atomDeg]
    omega

/-- **The vanishing criterion for the gradient-polar system.**  At a point where `∂_{i₀}Φ ≠ 0`,
the gradient-polar system vanishes iff `Φ = 0` and `∇φ ∥ ∇Φ`. -/
theorem polarSys_eq_zero_iff (c : EAChain k r) (Φ : EAPoly k r) (i₀ : Fin k) (x : Fin k → ℝ)
    (hpiv : eaEval c (eaD c i₀ Φ) x ≠ 0) :
    ((∀ i, eaEval c (polarSys c Φ i₀ i) x = 0) ↔
      eaEval c Φ x = 0 ∧ ∃ cst : ℝ, ∀ j : Fin k,
        eaEval c (eaD c j (sqGrad c Φ)) x = cst * eaEval c (eaD c j Φ) x) := by
  constructor
  · intro h
    have hΦ : eaEval c Φ x = 0 := by
      have := h i₀
      rwa [eaEval_polarSys, if_pos rfl] at this
    refine ⟨hΦ, eaEval c (eaD c i₀ (sqGrad c Φ)) x / eaEval c (eaD c i₀ Φ) x, ?_⟩
    intro j
    by_cases hj : j = i₀
    · subst hj; field_simp
    · have hmin : eaEval c (gpolMinor c Φ i₀ j) x = 0 := by
        have := h j
        rwa [eaEval_polarSys, if_neg hj] at this
      rw [eaEval_gpolMinor] at hmin
      field_simp at hmin ⊢
      linear_combination hmin
  · rintro ⟨hΦ, cst, hcst⟩ i
    rw [eaEval_polarSys]
    by_cases hi : i = i₀
    · rw [if_pos hi]; exact hΦ
    · rw [if_neg hi, eaEval_gpolMinor, hcst i₀, hcst i]
      ring

/-- **Isolated zeros of a holomorphic germ.**  If `D : ℂ → ℂ` is analytic at `0` and does not
vanish identically on a neighbourhood of `0`, then it has no zeros in a punctured ball around `0`.
This is the complex analogue of `Work.WilC4aCS.analyticAt_punctured_ne_zero`, and it is what makes
the *Case A* hypothesis of the polar counting (`the determinant of the polar system is not
identically zero along the branch`) produce *good levels*: for every level `ε` the branch points
lie in a small punctured disc, where the determinant does not vanish. -/
theorem analyticAt_punctured_ne_zero_C {D : ℂ → ℂ} (hD : AnalyticAt ℂ D 0)
    (hnz : ¬ ∀ᶠ s in nhds (0 : ℂ), D s = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ s : ℂ, 0 < ‖s‖ → ‖s‖ < r → D s ≠ 0 := by
  rcases hD.eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd h hnz
  · simp only [Filter.Eventually] at h
    rw [Metric.mem_nhdsWithin_iff] at h
    obtain ⟨r, hr, hball⟩ := h
    refine ⟨r, hr, fun s hs hlt => hball ⟨?_, ?_⟩⟩
    · simpa [Metric.mem_ball, dist_eq_norm] using hlt
    · simpa using hs

end Work.WilE3.Taylor
