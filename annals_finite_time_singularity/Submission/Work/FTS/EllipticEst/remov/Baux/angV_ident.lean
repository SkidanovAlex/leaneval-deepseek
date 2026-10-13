import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.remov.Baux.SliceAngRoomDefs
import Submission.Work.FTS.EllipticEst.remov.Lzero1_iteratedDeriv_eq
import Submission.Work.FTS.EllipticEst.StraightDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `k`-th angular identity in the divided-profile variable `v = u / cos θ`

`Work.FTS.EllipticEst.remov.Lzero1_iteratedDeriv_eq` expands the `k`-fold derivative of the
slice ODE `Lzero1 u = g` as the Leibniz expansion of `∂_θ^{k+1}(tan θ · u)`:

`u^{(k+2)} = ∑_{i≤k+1} C(k+1,i) (tan)^{(i)} u^{(k+1-i)} - 6 u^{(k)} - g^{(k)}`.

The present lemma is the same statement with the *product written in the `v`-variable*:
because `tan θ · u θ = sin θ · v θ` on `(0, π/2)` (where `v = sv u = u / cos θ`), the Leibniz
expansion of `∂_θ^{k+1}(tan θ · u)` equals that of `∂_θ^{k+1}(sin θ · v)`, and the latter is
`∑_{j≤k+1} C(k+1,j) (sin)^{(k+1-j)} v^{(j)}`.  Since the two products agree on an *open*
interval, the congruence is `Set.EqOn.iteratedDeriv_of_isOpen` — no extra regularity beyond
`C^{k+2}` of `u` is needed (the differentiability of `v = u/cos` on the interval is automatic).

This is the form in which the angular coercivity estimate consumes the ODE, the derivative
`u^{(k+2)}` on the left being replaced by the top-order term in `v` plus lower order terms.
-/

open scoped Real Topology

namespace Work.FTS.EllipticEst.remov.Baux

/-- The `k`-th derivative of the slice ODE `Lzero1 u = g`, with the product `tan θ · u`
rewritten as `sin θ · v`, `v = u / cos θ`. -/
theorem angV_ident (k : ℕ) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      iteratedDeriv (k + 2) u θ
        = (∑ j ∈ Finset.range (k + 2), ((k + 1).choose j : ℝ)
              * iteratedDeriv (k + 1 - j) Real.sin θ * iteratedDeriv j (sv u) θ)
          - 6 * iteratedDeriv k u θ - iteratedDeriv k g θ := by
  intro θ hθ
  have hU : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hcos : Real.cos θ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
  -- regularity at `θ`: `u` is `C^{k+1}` there, hence so is `v = u / cos`
  have huk2 : ContDiffAt ℝ ((k + 2 : ℕ) : WithTop ℕ∞) u θ := hu.contDiffAt (hU.mem_nhds hθ)
  have huk1 : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) u θ :=
    huk2.of_le (by exact_mod_cast (show k + 1 ≤ k + 2 by omega))
  have htan : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) Real.tan θ :=
    (Real.contDiffAt_tan (n := ((k + 1 : ℕ) : WithTop ℕ∞))).mpr hcos
  have hsin : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) Real.sin θ := Real.contDiff_sin.contDiffAt
  have hsv : ContDiffAt ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (sv u) θ :=
    huk1.div (Real.contDiff_cos.contDiffAt) hcos
  -- Leibniz for the two products
  have hA : iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
      = ∑ i ∈ Finset.range (k + 2), ((k + 1).choose i : ℝ)
          * iteratedDeriv i Real.tan θ * iteratedDeriv (k + 1 - i) u θ :=
    iteratedDeriv_mul htan huk1
  have hB : iteratedDeriv (k + 1) (fun t => sv u t * Real.sin t) θ
      = ∑ i ∈ Finset.range (k + 2), ((k + 1).choose i : ℝ)
          * iteratedDeriv i (sv u) θ * iteratedDeriv (k + 1 - i) Real.sin θ :=
    iteratedDeriv_mul hsv hsin
  -- the two products agree on the (open) interval
  have hEqOn : Set.EqOn (fun t => Real.tan t * u t) (fun t => sv u t * Real.sin t)
      (Set.Ioo 0 (Real.pi / 2)) := by
    intro t ht
    have hc : Real.cos t ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩)
    show Real.tan t * u t = sv u t * Real.sin t
    rw [Real.tan_eq_sin_div_cos]
    simp only [sv]
    field_simp
  have hEq : iteratedDeriv (k + 1) (fun t => Real.tan t * u t) θ
      = iteratedDeriv (k + 1) (fun t => sv u t * Real.sin t) θ :=
    Set.EqOn.iteratedDeriv_of_isOpen hEqOn hU (k + 1) hθ
  -- hence the two Leibniz expansions coincide (only the order of the last two factors differs)
  have hsum : (∑ i ∈ Finset.range (k + 2), ((k + 1).choose i : ℝ)
        * iteratedDeriv i Real.tan θ * iteratedDeriv (k + 1 - i) u θ)
      = ∑ j ∈ Finset.range (k + 2), ((k + 1).choose j : ℝ)
          * iteratedDeriv (k + 1 - j) Real.sin θ * iteratedDeriv j (sv u) θ := by
    rw [← hA, hEq, hB]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [Work.FTS.EllipticEst.remov.Lzero1_iteratedDeriv_eq k hu hg θ hθ, hsum]

end Work.FTS.EllipticEst.remov.Baux
