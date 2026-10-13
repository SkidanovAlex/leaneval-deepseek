import Mathlib
import Submission.Work.WilE3.Defs

/-!
  annals_wilkies_conjecture, AREA E3: the two elementary *reductions* of the target lemma
  `Work.WilE3.Taylor.hasLoj_of_multiplicity` that any proof of it needs.

  **Reduction 1 (the residual).**  The target's function is the system residual
  `∑_{f ∈ B.eqs} |eaEval c f x|` against the common zero set `Z`.  Since
  `√ (∑ f²) ≤ ∑ |f|` on the one hand and `Z = {∑ f² = 0}` on the other, it suffices to prove the
  Łojasiewicz inequality for the single EA polynomial `Φ = ∑_{f ∈ B.eqs} f²` with twice the
  exponent.  This module proves the reduction (`hasLoj_residual_of_sum_sq`), so the whole
  problem may be attacked in the *single-function* form, which is the form in which the polar
  argument (Gabrielov 1995, §3) applies.

  **Reduction 2 (the radial form).**  If `y ∈ Z` and `Φ` dominates a constant times
  `dist (·, y) ^ q` near `y`, then it dominates a constant times `infDist (·, Z) ^ q`, because
  `infDist (·, Z) ≤ dist (·, y)`.  So the shell/sphere minimisation form of the inequality
  (`μ (ρ) ≥ C ρ ^ q`, `μ (ρ) = min {Φ : dist (·, y) = ρ}`) implies the target form.
-/

namespace Work.WilE3.Taylor

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

/-- **Cauchy–Schwarz for a list**: `∑ aᵢ² ≤ (∑ |aᵢ|)²`. -/
theorem sum_sq_le_sum_abs_sq : ∀ L : List ℝ,
    (L.map fun a => a ^ 2).sum ≤ ((L.map fun a => |a|).sum) ^ 2
  | [] => by simp
  | a :: L => by
    have ih := sum_sq_le_sum_abs_sq L
    simp only [List.map_cons, List.sum_cons] at ih ⊢
    have ha : (0 : ℝ) ≤ |a| := abs_nonneg a
    have hL : (0 : ℝ) ≤ (L.map fun a => |a|).sum := List.sum_nonneg fun b hb => by
      obtain ⟨d, _, rfl⟩ := List.mem_map.mp hb
      exact abs_nonneg _
    nlinarith [ih, ha, hL, sq_abs a]

/-- **The residual dominates the square root of the sum of squares**: `√ (∑ f²) ≤ ∑ |f|`. -/
theorem sqrt_sum_sq_le_sum_abs {k r : ℕ} (c : EAChain k r) (L : List (EAPoly k r))
    (x : Fin k → ℝ) :
    Real.sqrt ((L.map fun f => (eaEval c f x) ^ 2).sum) ≤ (L.map fun f => |eaEval c f x|).sum := by
  have h := sum_sq_le_sum_abs_sq (L.map fun f => eaEval c f x)
  rw [List.map_map, List.map_map] at h
  have h' : ((L.map fun f => (eaEval c f x) ^ 2).sum) ≤
      ((L.map fun f => |eaEval c f x|).sum) ^ 2 := by
    simpa only [Function.comp_def] using h
  have hR : (0 : ℝ) ≤ (L.map fun f => |eaEval c f x|).sum := List.sum_nonneg fun b hb => by
    obtain ⟨d, _, rfl⟩ := List.mem_map.mp hb
    exact abs_nonneg _
  set S : ℝ := (L.map fun f => |eaEval c f x|).sum with hS
  calc Real.sqrt ((L.map fun f => (eaEval c f x) ^ 2).sum)
      ≤ Real.sqrt (S ^ 2) := by rw [hS]; exact Real.sqrt_le_sqrt h'
    _ = S := Real.sqrt_sq hR
    _ = (L.map fun f => |eaEval c f x|).sum := hS

/-- **Reduction of the target to the single-EA-polynomial (sum of squares) form.**  The Łojasiewicz
inequality for the system residual against the common zero set follows from the same inequality for
`Φ = ∑_{f ∈ B.eqs} f²`, at twice the exponent.

(The zero sets agree — both are the common zero set of `B.eqs` — and `√ Φ ≤ residual`.) -/
theorem hasLoj_residual_of_sum_sq {k r : ℕ} (c : EAChain k r) (B : Basic k r) (y : Fin k → ℝ)
    {q : ℕ}
    (h : Work.WilE3.HasLoj (fun x => (B.eqs.map fun f => (eaEval c f x) ^ 2).sum)
        {x | ∀ f' ∈ B.eqs, eaEval c f' x = 0} y (2 * q)) :
    Work.WilE3.HasLoj (fun x => (B.eqs.map fun f => |eaEval c f x|).sum)
        {x | ∀ f' ∈ B.eqs, eaEval c f' x = 0} y q := by
  obtain ⟨C, hC, hC'⟩ := h
  refine ⟨Real.sqrt C, Real.sqrt_pos.mpr hC, ?_⟩
  filter_upwards [hC'] with x hx
  set Z : Set (Fin k → ℝ) := {x | ∀ f' ∈ B.eqs, eaEval c f' x = 0} with hZdef
  have hsq0 : (0 : ℝ) ≤ (B.eqs.map fun f => (eaEval c f x) ^ 2).sum :=
    List.sum_nonneg fun b hb => by
      obtain ⟨d, _, rfl⟩ := List.mem_map.mp hb
      positivity
  have hR0 : (0 : ℝ) ≤ (B.eqs.map fun f => |eaEval c f x|).sum :=
    List.sum_nonneg fun b hb => by
      obtain ⟨d, _, rfl⟩ := List.mem_map.mp hb
      exact abs_nonneg _
  have hx' : C * Metric.infDist x Z ^ (2 * q) ≤ (B.eqs.map fun f => (eaEval c f x) ^ 2).sum := by
    rw [abs_of_nonneg hsq0] at hx
    exact hx
  have hstep : Real.sqrt (C * Metric.infDist x Z ^ (2 * q)) ≤
      (B.eqs.map fun f => |eaEval c f x|).sum :=
    le_trans (Real.sqrt_le_sqrt hx') (sqrt_sum_sq_le_sum_abs c B.eqs x)
  have hsqrt : Real.sqrt (C * Metric.infDist x Z ^ (2 * q)) =
      Real.sqrt C * Metric.infDist x Z ^ q := by
    rw [Real.sqrt_mul hC.le]
    congr 1
    rw [show 2 * q = q * 2 from Nat.mul_comm 2 q, pow_mul]
    exact Real.sqrt_sq (pow_nonneg Metric.infDist_nonneg q)
  rw [hsqrt] at hstep
  rw [abs_of_nonneg hR0]
  exact hstep

/-- **Reduction to the radial (shell) form.**  If `y ∈ Z` and `Φ` dominates `C · dist (·, y) ^ q`
near `y`, then `Φ` dominates `C · infDist (·, Z) ^ q` near `y`: this is the Łojasiewicz inequality
of the target.  `dist (·, y) ^ q` is the *stronger* right-hand side because `infDist x Z ≤ dist x y`
for `y ∈ Z`. -/
theorem hasLoj_of_dist_bound {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {Z : Set (Fin k → ℝ)} {y : Fin k → ℝ}
    (hy : y ∈ Z) {q : ℕ} {C : ℝ} (hC : 0 < C)
    (h : ∀ᶠ x in 𝓝 y, C * dist x y ^ q ≤ |Φ x|) : Work.WilE3.HasLoj Φ Z y q := by
  refine ⟨C, hC, ?_⟩
  filter_upwards [h] with x hx
  have hle : Metric.infDist x Z ≤ dist x y := Metric.infDist_le_dist_of_mem hy
  calc C * Metric.infDist x Z ^ q ≤ C * dist x y ^ q :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ Metric.infDist_nonneg hle q) hC.le
    _ ≤ |Φ x| := hx

end Work.WilE3.Taylor
