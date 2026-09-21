import Mathlib
import Submission.Work.OddCurveB.Existence.KdiagForm
import Submission.Work.OddVolterra.Assembly

/-!
# The closeness of the perturbed data to the base data (the `G`-row)

`Godd n h s z` depends on `h` only through `(h s, h'(s))`
(`Work.OddCurveB.Existence.Godd_eq_GoddDiag`), and the diagonal kernels are continuous functions
of their arguments (`Work.OddCurveB.Existence.Kdiag1_eq`, `Kdiag2_eq`).  Consequently the map

`(s, hs, hp, z) ↦ GoddDiag n s hs hp z`

is continuous on every compact box, and *uniform continuity* on the box gives directly the shape
of hypothesis that the Volterra engines consume:

* `dist_Godd_le` — for every tolerance `τ > 0` there is `ε > 0` such that any `h` with
  `|h| ≤ ε` and `|h'| ≤ ε` has `dist (Godd n h s z) (Godd n 0 s z) < τ` for all `s ∈ [a,b]` and
  all `z` in the closed ball of radius `1` around the *endpoint* base state `baseState b`
  (that is the ball used by `Commons.Geometry.Ulam.volterra_perturbation_exists_v3_small`).

The statement is deliberately in the "for every output tolerance there is an input tolerance"
form rather than the "`dist < δ` from `‖h‖ ≤ δ`" form: uniform continuity gives a modulus, not a
constant, and the caller recovers the "constant `1`" shape by choosing the input tolerance small
enough — see the discussion in `Submission/Work/OddCurveB/README.md`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddCurveB.Est

open Work.OddVolterra
open Work.OddCurveB.Existence

noncomputable section

/-- Continuity of the first diagonal kernel composed with a continuous argument. -/
lemma continuous_Kdiag1_comp (n : ℕ) {f : (ℝ × ℝ × ℝ) × St → ℝ} (hf : Continuous f) :
    Continuous (fun p : (ℝ × ℝ × ℝ) × St => Kdiag1 n p.1.1 p.1.2.1 p.1.2.2 (f p)) := by
  have heq : (fun p : (ℝ × ℝ × ℝ) × St => Kdiag1 n p.1.1 p.1.2.1 p.1.2.2 (f p)) =
      fun p : (ℝ × ℝ × ℝ) × St =>
        ((Nat.doubleFactorial (2 * n + 1) : ℝ) * (-1) ^ (n + 1) / Real.sqrt 2) *
          (Drad p.1.1 p.1.2.1 p.1.2.2 (f p) ^ n *
            Real.sqrt (Drad p.1.1 p.1.2.1 p.1.2.2 (f p))) := by
    funext p; exact Kdiag1_eq n _ _ _ _
  rw [heq]
  simp only [Drad]
  fun_prop

/-- Continuity of the second diagonal kernel composed with a continuous argument. -/
lemma continuous_Kdiag2_comp (n : ℕ) (hn : 1 ≤ n) {f : (ℝ × ℝ × ℝ) × St → ℝ}
    (hf : Continuous f) :
    Continuous (fun p : (ℝ × ℝ × ℝ) × St => Kdiag2 n p.1.1 p.1.2.1 p.1.2.2 (f p)) := by
  have heq : (fun p : (ℝ × ℝ × ℝ) × St => Kdiag2 n p.1.1 p.1.2.1 p.1.2.2 (f p)) =
      fun p : (ℝ × ℝ × ℝ) × St =>
        ((Nat.doubleFactorial (2 * n - 1) : ℝ) * (-1) ^ n / Real.sqrt 2) *
          (Drad p.1.1 p.1.2.1 p.1.2.2 (f p) ^ (n - 1) *
            Real.sqrt (Drad p.1.1 p.1.2.1 p.1.2.2 (f p))) * (f p + p.1.2.2) := by
    funext p; exact Kdiag2_eq n hn _ _ _ _
  rw [heq]
  simp only [Drad]
  fun_prop

/-- The explicit diagonal system is continuous in all of its arguments. -/
lemma continuous_GoddDiag (n : ℕ) (hn : 1 ≤ n) :
    Continuous (fun p : (ℝ × ℝ × ℝ) × St => GoddDiag n p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  have hc0 : Continuous (fun p : (ℝ × ℝ × ℝ) × St => p.2 0) :=
    (continuous_apply (0 : Fin 4)).comp continuous_snd
  have hc1 : Continuous (fun p : (ℝ × ℝ × ℝ) × St => p.2 1) :=
    (continuous_apply (1 : Fin 4)).comp continuous_snd
  have hc2 : Continuous (fun p : (ℝ × ℝ × ℝ) × St => p.2 2) :=
    (continuous_apply (2 : Fin 4)).comp continuous_snd
  have hc3 : Continuous (fun p : (ℝ × ℝ × ℝ) × St => p.2 3) :=
    (continuous_apply (3 : Fin 4)).comp continuous_snd
  have h1 := continuous_Kdiag1_comp n (f := fun p : (ℝ × ℝ × ℝ) × St => -(p.2 0)) hc0.neg
  have h2 := continuous_Kdiag1_comp n (f := fun p : (ℝ × ℝ × ℝ) × St => p.2 1) hc1
  have h3 := continuous_Kdiag2_comp n hn (f := fun p : (ℝ × ℝ × ℝ) × St => -(p.2 0)) hc0.neg
  have h4 := continuous_Kdiag2_comp n hn (f := fun p : (ℝ × ℝ × ℝ) × St => p.2 1) hc1
  rw [show (fun p : (ℝ × ℝ × ℝ) × St => GoddDiag n p.1.1 p.1.2.1 p.1.2.2 p.2) = fun p =>
      ![p.2 0, p.2 1,
        -(abelMass * (-(Kdiag1 n p.1.1 p.1.2.1 p.1.2.2 (-(p.2 0)) * p.2 2 +
          Kdiag1 n p.1.1 p.1.2.1 p.1.2.2 (p.2 1) * p.2 3))),
        -(abelMass * (-(Kdiag2 n p.1.1 p.1.2.1 p.1.2.2 (-(p.2 0)) * p.2 2 +
          Kdiag2 n p.1.1 p.1.2.1 p.1.2.2 (p.2 1) * p.2 3)))] from rfl]
  refine continuous_pi (fun i => ?_)
  fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_fin_one]
  · exact hc0
  · exact hc1
  · exact ((((h1.mul hc2).add (h2.mul hc3)).neg).const_mul abelMass).neg
  · exact ((((h3.mul hc2).add (h4.mul hc3)).neg).const_mul abelMass).neg

/-- The box of the estimates for a fixed bound `ε` on `(h s, h'(s))`. -/
def box (a b e : ℝ) (c : St) : Set ((ℝ × ℝ × ℝ) × St) :=
  (Set.Icc a b ×ˢ (Set.Icc (-e) e ×ˢ Set.Icc (-e) e)) ×ˢ Metric.closedBall c 1

lemma isCompact_box (a b e : ℝ) (c : St) : IsCompact (box a b e c) :=
  ((isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))).prod (isCompact_closedBall c 1)

/-- Membership in the box. -/
lemma mem_box {a b e : ℝ} {c : St} {s hs hp : ℝ} {z : St}
    (hs1 : s ∈ Set.Icc a b) (h1 : |hs| ≤ e) (h2 : |hp| ≤ e)
    (hz : z ∈ Metric.closedBall c 1) :
    (((s, hs, hp) : ℝ × ℝ × ℝ), z) ∈ box a b e c :=
  ⟨⟨hs1, ⟨(abs_le.mp h1).1, (abs_le.mp h1).2⟩, ⟨(abs_le.mp h2).1, (abs_le.mp h2).2⟩⟩, hz⟩

/-- The distance between `((s, hs, hp), z)` and `((s, 0, 0), z)` is `max |hs| |hp|`. -/
lemma dist_pt (s hs hp : ℝ) (z : St) :
    dist (((s, hs, hp) : ℝ × ℝ × ℝ), z) (((s, 0, 0) : ℝ × ℝ × ℝ), z) = max |hs| |hp| := by
  rw [dist_prod_same_right, dist_prod_same_left, Prod.dist_eq, Real.dist_eq, Real.dist_eq,
    sub_zero, sub_zero]

/-- **Closeness of the perturbed `G`-row to the base data.**

For every tolerance `τ > 0` there is `ε > 0` such that for every `h` with `|h| ≤ ε` and
`|h'| ≤ ε` on the line, and every `s ∈ [a,b]`, every `z` in the closed ball of radius `1` around
`baseState b`,

`dist (Godd n h s z) (Godd n 0 s z) < τ`.

This is exactly the hypothesis `hG_close` of
`Commons.Geometry.Ulam.volterra_perturbation_exists_v3_small` (with `G = Godd n h`,
`G0 = Godd n 0`, `Z0 = baseState`), up to the choice of the smallness threshold. -/
theorem dist_Godd_le (n : ℕ) (hn : 1 ≤ n) {a b : ℝ} (hab : a ≤ b) :
    ∀ τ > 0, ∃ ε > 0, ∀ h : ℝ → ℝ,
      (∀ s : ℝ, |h s| ≤ ε) → (∀ s : ℝ, |deriv h s| ≤ ε) →
      ∀ s ∈ Set.Icc a b, ∀ z ∈ Metric.closedBall (baseState b) 1,
        dist (Godd n h s z) (Godd n 0 s z) < τ := by
  intro τ hτ
  obtain ⟨γ, hγ, hunif⟩ := Metric.uniformContinuousOn_iff_le.mp
    ((isCompact_box a b 1 (baseState b)).uniformContinuousOn_of_continuous
      (continuous_GoddDiag n hn).continuousOn) (τ / 2) (by linarith)
  refine ⟨min 1 γ, lt_min one_pos hγ, ?_⟩
  intro h hh hh' s hs z hz
  have hε1 : min 1 γ ≤ 1 := min_le_left _ _
  have hεγ : min 1 γ ≤ γ := min_le_right _ _
  have habs1 : |h s| ≤ 1 := le_trans (hh s) hε1
  have habs2 : |deriv h s| ≤ 1 := le_trans (hh' s) hε1
  have hmem : (((s, h s, deriv h s) : ℝ × ℝ × ℝ), z) ∈ box a b 1 (baseState b) :=
    mem_box hs habs1 habs2 hz
  have hmem0 : (((s, 0, 0) : ℝ × ℝ × ℝ), z) ∈ box a b 1 (baseState b) :=
    mem_box hs (by norm_num) (by norm_num) hz
  have hdist : dist (((s, h s, deriv h s) : ℝ × ℝ × ℝ), z)
      (((s, 0, 0) : ℝ × ℝ × ℝ), z) ≤ γ := by
    rw [dist_pt]
    exact max_le (le_trans (hh s) hεγ) (le_trans (hh' s) hεγ)
  have hfinal := hunif _ hmem _ hmem0 hdist
  rw [Godd_eq_GoddDiag, Godd_zero_eq]
  exact lt_of_le_of_lt hfinal (by linarith)

end

end Work.OddCurveB.Est
