import Mathlib
import Submission.Work.OddCurveB.Est.Defs

/-!
# The derivative of the unperturbed odd Volterra map at the base state

`Godd n 0 s` agrees, near the base state `baseState s` (`s > 0`), with the polynomial model
`model n s`; differentiating the model coordinate by coordinate gives `Phi n s`.  Consequently

`fderiv ℝ (fun z => Godd n 0 s z) (baseState s) = Phi n s`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddCurveB.Est

open Work.OddVolterra
open Commons.Geometry.Ulam

noncomputable section

/-- Derivative of the `(2,2)`-coordinate of the model. -/
lemma hasFDerivAt_gm2 (n : ℕ) (s : ℝ) : HasFDerivAt (gm2 n s) (row2 n s) (baseState s) := by
  have h0 : HasFDerivAt (fun z : St => z 0) (Proj 0) (baseState s) :=
    hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) (0 : Fin 4) (baseState s)
  have h1 : HasFDerivAt (fun z : St => z 1) (Proj 1) (baseState s) :=
    hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) (1 : Fin 4) (baseState s)
  have h2 : HasFDerivAt (fun z : St => z 2) (Proj 2) (baseState s) :=
    hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) (2 : Fin 4) (baseState s)
  have h3 : HasFDerivAt (fun z : St => z 3) (Proj 3) (baseState s) :=
    hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) (3 : Fin 4) (baseState s)
  have m1 : HasFDerivAt (fun z : St => (z 0) ^ (2 * n + 1) * z 2) _ (baseState s) :=
    (h0.pow (2 * n + 1)).mul h2
  have m2 : HasFDerivAt (fun z : St => (z 1) ^ (2 * n + 1) * z 3) _ (baseState s) :=
    (h1.pow (2 * n + 1)).mul h3
  have hsum : HasFDerivAt
      (fun z : St => dc1 n s * ((z 0) ^ (2 * n + 1) * z 2)
        + dc1 n s * ((z 1) ^ (2 * n + 1) * z 3)) _ (baseState s) :=
    (m1.const_mul (dc1 n s)).add (m2.const_mul (dc1 n s))
  have hg : HasFDerivAt
      (fun z : St => abelMass * (dc1 n s * ((z 0) ^ (2 * n + 1) * z 2)
        + dc1 n s * ((z 1) ^ (2 * n + 1) * z 3))) _ (baseState s) :=
    hsum.const_mul abelMass
  refine (hg.congr_of_eventuallyEq ?_).congr_fderiv ?_
  · exact Filter.EventuallyEq.of_eq (by funext z; simp only [gm2]; ring)
  · ext z
    simp [row2, pAA, pA, Proj, baseState]
    ring

/-- Derivative of the `(2,3)`-coordinate of the model. -/
lemma hasFDerivAt_gm3 (n : ℕ) (s : ℝ) : HasFDerivAt (gm3 n s) (row3 n s) (baseState s) := by
  have h0 : HasFDerivAt (fun z : St => z 0) (Proj 0) (baseState s) :=
    hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) (0 : Fin 4) (baseState s)
  have h1 : HasFDerivAt (fun z : St => z 1) (Proj 1) (baseState s) :=
    hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) (1 : Fin 4) (baseState s)
  have h2 : HasFDerivAt (fun z : St => z 2) (Proj 2) (baseState s) :=
    hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) (2 : Fin 4) (baseState s)
  have h3 : HasFDerivAt (fun z : St => z 3) (Proj 3) (baseState s) :=
    hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) (3 : Fin 4) (baseState s)
  have m1 : HasFDerivAt (fun z : St => -((z 0) ^ (2 * n)) * z 2) _ (baseState s) :=
    ((h0.pow (2 * n)).neg).mul h2
  have m2 : HasFDerivAt (fun z : St => (z 1) ^ (2 * n) * z 3) _ (baseState s) :=
    (h1.pow (2 * n)).mul h3
  have hsum : HasFDerivAt
      (fun z : St => dc2 n s * (-((z 0) ^ (2 * n)) * z 2)
        + dc2 n s * ((z 1) ^ (2 * n) * z 3)) _ (baseState s) :=
    (m1.const_mul (dc2 n s)).add (m2.const_mul (dc2 n s))
  have hg : HasFDerivAt
      (fun z : St => abelMass * (dc2 n s * (-((z 0) ^ (2 * n)) * z 2)
        + dc2 n s * ((z 1) ^ (2 * n) * z 3))) _ (baseState s) :=
    hsum.const_mul abelMass
  refine (hg.congr_of_eventuallyEq ?_).congr_fderiv ?_
  · exact Filter.EventuallyEq.of_eq (by funext z; simp only [gm3]; ring)
  · ext z
    simp [row3, pGG, pC, Proj, baseState]
    ring

/-- The derivative of the polynomial model at the base state is `Phi n s`. -/
lemma hasFDerivAt_model (n : ℕ) (s : ℝ) :
    HasFDerivAt (model n s) (Phi n s) (baseState s) := by
  have h0 : HasFDerivAt (fun z : St => z 0) (Proj 0) (baseState s) :=
    hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) (0 : Fin 4) (baseState s)
  have h1 : HasFDerivAt (fun z : St => z 1) (Proj 1) (baseState s) :=
    hasFDerivAt_apply (𝕜 := ℝ) (F' := fun _ : Fin 4 => ℝ) (1 : Fin 4) (baseState s)
  have h2 := hasFDerivAt_gm2 n s
  have h3 := hasFDerivAt_gm3 n s
  have hpi : HasFDerivAt
      (fun z i => ![fun z : St => z 0, fun z : St => z 1, gm2 n s, gm3 n s] i z)
      (ContinuousLinearMap.pi ![Proj 0, Proj 1, row2 n s, row3 n s]) (baseState s) :=
    (hasFDerivAt_pi (φ := ![fun z : St => z 0, fun z : St => z 1, gm2 n s, gm3 n s])
      (φ' := ![Proj 0, Proj 1, row2 n s, row3 n s])).2
      (fun i => by
        fin_cases i
        · exact h0
        · exact h1
        · exact h2
        · exact h3)
  have hfun : model n s
      = (fun z i => ![fun z : St => z 0, fun z : St => z 1, gm2 n s, gm3 n s] i z) := by
    funext z i
    fin_cases i <;> rfl
  exact (hpi.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun)).congr_fderiv rfl

/-! ## `Godd n 0 s` agrees with the model near the base state -/

lemma mul_pow_pred {n : ℕ} (hn : 1 ≤ n) (x : ℝ) : x * x ^ (2 * n - 1) = x ^ (2 * n) := by
  rw [mul_comm, ← pow_succ, Nat.sub_add_cancel (by omega)]

lemma neg_mul_pow_pred {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    (-x) * x ^ (2 * n - 1) = -(x ^ (2 * n)) := by
  rw [neg_mul, mul_pow_pred hn]

/-- Pointwise agreement of `Godd n 0 s` with the model, in the region where both coordinates
`z 0`, `z 1` are positive (so that the absolute values of the diagonal kernels are the
corresponding powers). -/
lemma Godd_eq_model (n : ℕ) (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s) {z : St}
    (hz0 : 0 < z 0) (hz1 : 0 < z 1) : Godd n 0 s z = model n s z := by
  have hK1a : K1 n (fun _ : ℝ => 0) s s (-(z 0)) = dc1 n s * (z 0) ^ (2 * n + 1) := by
    rw [K1_diag n hs (-(z 0)), abs_neg, abs_of_pos hz0]
  have hK1b : K1 n (fun _ : ℝ => 0) s s (z 1) = dc1 n s * (z 1) ^ (2 * n + 1) := by
    rw [K1_diag n hs (z 1), abs_of_pos hz1]
  have hK2a : K2 n (fun _ : ℝ => 0) s s (-(z 0)) = dc2 n s * (-((z 0) ^ (2 * n))) := by
    rw [K2_diag n hn hs (-(z 0)), abs_neg, abs_of_pos hz0, neg_mul_pow_pred hn]
  have hK2b : K2 n (fun _ : ℝ => 0) s s (z 1) = dc2 n s * ((z 1) ^ (2 * n)) := by
    rw [K2_diag n hn hs (z 1), abs_of_pos hz1, mul_pow_pred hn]
  rw [Work.OddVolterra.Existence.Godd_zero_diag, hK1a, hK1b, hK2a, hK2b]
  funext i
  fin_cases i <;> rfl

lemma eventuallyEq_Godd_model (n : ℕ) (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s) :
    Godd n 0 s =ᶠ[𝓝 (baseState s)] model n s := by
  have hmem : {z : St | 0 < z 0 ∧ 0 < z 1} ∈ 𝓝 (baseState s) := by
    have h1 : {z : St | 0 < z 0} ∈ 𝓝 (baseState s) :=
      (isOpen_lt continuous_const (continuous_apply 0)).mem_nhds
        (by simpa [baseState] using profileX_pos s hs)
    have h2 : {z : St | 0 < z 1} ∈ 𝓝 (baseState s) :=
      (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds
        (by simpa [baseState] using profileX_pos s hs)
    exact Filter.inter_mem h1 h2
  exact Filter.eventually_of_mem hmem (fun z hz => Godd_eq_model n hn hs hz.1 hz.2)

/-- **The diagonal linearization of the unperturbed odd Volterra map.** -/
theorem fderiv_Godd (n : ℕ) (hn : 1 ≤ n) {s : ℝ} (hs : 0 < s) :
    fderiv ℝ (fun z => Godd n 0 s z) (baseState s) = Phi n s :=
  (((hasFDerivAt_model n s).congr_of_eventuallyEq (eventuallyEq_Godd_model n hn hs)).fderiv)

end

end Work.OddCurveB.Est
