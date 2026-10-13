import Mathlib
import Submission.Work.WilE3.API.eaTaylor_remainder

namespace Work.WilE3.Taylor

open Classical Topology
open WilkiesDesign.E

/-- The system residual `∑_i |f_i|` of the equations of `B` is bounded by `I · dist (x,y)^N` on the
set where the order-`N` Taylor polynomials of the equations are already `≤ dist (x,y)^N`.  This
combines the effective Taylor remainder `Work.WilE3.API.eaTaylor_remainder` with the triangle
inequality (`|f (x)| ≤ |T_N f (x)| + |f (x) - T_N f (x)| ≤ d^N + C d^{N+1} ≤ (1 + C) d^N` for
`d = dist x y ≤ 1`).  It is the input of the Łojasiewicz inequality in the `(⇐)` direction of
`E3_taylor_closure` (there, `N = κ ^ 2`). -/
theorem E3_residual_bound {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (B : WilkiesDesign.E.Basic k r) (y : Fin k → ℝ) (N : ℕ) :
    ∃ I : ℝ, 0 ≤ I ∧ ∃ R : ℝ, 0 < R ∧ ∀ x : Fin k → ℝ, dist x y < R →
      (∀ f ∈ B.eqs, |WilkiesDesign.E.eaTaylor c f N y x| ≤ dist x y ^ N) →
      (B.eqs.map fun f => |WilkiesDesign.E.eaEval c f x|).sum ≤ I * dist x y ^ N := by
  classical
  -- the effective Taylor remainder, one constant per equation
  have hCf : ∀ f : EAPoly k r, ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ᶠ x in 𝓝 y,
      |eaEval c f x - eaTaylor c f N y x| ≤ Cf * dist x y ^ (N + 1) :=
    fun f => API.eaTaylor_remainder c f N y
  choose C hCnonneg hCbnd using hCf
  -- the same bound, uniformly over the finite list of equations
  have hbdd : ∀ᶠ x in 𝓝 y, ∀ f ∈ B.eqs,
      |eaEval c f x - eaTaylor c f N y x| ≤ C f * dist x y ^ (N + 1) := by
    induction B.eqs with
    | nil => exact Filter.Eventually.of_forall fun x => by simp
    | cons a t ih =>
      have h1 : ∀ᶠ x in 𝓝 y,
          (|eaEval c a x - eaTaylor c a N y x| ≤ C a * dist x y ^ (N + 1)) ∧
            (∀ f ∈ t, |eaEval c f x - eaTaylor c f N y x| ≤ C f * dist x y ^ (N + 1)) :=
        (hCbnd a).and ih
      refine h1.mono fun x hx => ?_
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact hx.1
      · exact hx.2 f hf
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hbdd
  refine ⟨(B.eqs.map fun f => (C f + 1)).sum, ?_, min ε 1, lt_min hε one_pos, ?_⟩
  · apply List.sum_nonneg
    intro a ha
    rcases List.mem_map.mp ha with ⟨f, _, rfl⟩
    linarith [hCnonneg f]
  · intro x hx hTay
    have hd0 : 0 ≤ dist x y := dist_nonneg
    have hd1 : dist x y ≤ 1 := le_of_lt (lt_of_lt_of_le hx (min_le_right ε 1))
    have hdε : dist x y < ε := lt_of_lt_of_le hx (min_le_left ε 1)
    have hbound := hball x hdε
    have hterm : ∀ f ∈ B.eqs, |eaEval c f x| ≤ (C f + 1) * dist x y ^ N := by
      intro f hf
      have h2 : |eaEval c f x| ≤
          |eaTaylor c f N y x| + |eaEval c f x - eaTaylor c f N y x| := by
        have h := abs_sub_abs_le_abs_sub (eaEval c f x) (eaTaylor c f N y x)
        linarith
      have h3 : |eaTaylor c f N y x| ≤ dist x y ^ N := hTay f hf
      have h4 : |eaEval c f x - eaTaylor c f N y x| ≤ C f * dist x y ^ (N + 1) := hbound f hf
      have h5 : dist x y ^ (N + 1) ≤ dist x y ^ N := by
        rw [pow_succ]
        simpa using mul_le_mul_of_nonneg_left hd1 (pow_nonneg hd0 N)
      have h6 : C f * dist x y ^ (N + 1) ≤ C f * dist x y ^ N :=
        mul_le_mul_of_nonneg_left h5 (hCnonneg f)
      linarith [h2, h3, h4, h6]
    calc (B.eqs.map fun f => |eaEval c f x|).sum
        ≤ (B.eqs.map fun f => (C f + 1) * dist x y ^ N).sum := List.sum_le_sum hterm
      _ = (B.eqs.map fun f => (C f + 1)).sum * dist x y ^ N :=
            List.sum_map_mul_right B.eqs (fun f => C f + 1) (dist x y ^ N)

end Work.WilE3.Taylor
