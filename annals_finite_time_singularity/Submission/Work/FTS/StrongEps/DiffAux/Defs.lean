/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/DiffAux/Defs.lean`

The vocabulary of the **mollifier-approximation estimate**

  `|J_ε f - f|_{ℋ^k} ≤ C ε · |f|_{ℋ^{k+1}}`

(`Work.FTS.StrongEps.HkSq_Jeps_sub_le`), the companion of the `E1`-boundedness estimate
`|J_ε f|_{ℋ^k} ≤ e^{Cε} |f|_{ℋ^k}` of `Submission/Work/FTS/StrongEps/HkSq_Jeps_le.lean`.

The `ℋ^k`-integrand of `Work.Spaces` is the sum of the squares of the weighted slots

* `(D_z^i f · wE)^2` for `0 ≤ i ≤ k`, where `wE z θ = w z / sin(2θ)^{η/2}` (`HkZPart`), and
* `(D_z^j D_θ^i f · Wt α)^2` for `1 ≤ i`, `i + j ≤ k` (`HkMPart`).

Here we record

* `wE` — the first of those weights as a single object;
* `slots k` — the exact index set `{q : 1 ≤ q.1 ∧ q.1 + q.2 ≤ k}` of the mixed slots of level
  `k`, where `q = (θ-order, z-order)`, so that `HkMPartF` is the sum over `slots k`;
* `shadow α k f` — the *level-`k+1` shadow* of the level-`k` slots of `J_ε f - f`, i.e. the
  right-hand side produced when each level-`k` slot of `J_ε f - f` is differentiated once more:
  the `D_z`-slot `i` produces the two level-`k+1` slots `(i+1, 0)` and `(i, 1)`, and the mixed
  slot `(j, i)` produces `(j+1, i)` and `(j, i+1)`;
* **`shadow_le`** — the combinatorial heart of the estimate: the sum of the level-`k+1` slots
  produced this way is at most `2` times the level-`k+1` integrand (each level-`k+1` slot is hit
  at most twice, and the produced slots use the *same* weights as the level-`k+1` integrand).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.HkSqAux.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.HkIntegrand_Jeps_le_integral

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.DiffAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The `D_z`-slot weight and the index set of the mixed slots -/

/-- The weight factor of the pure `D_z`-slots of `HkIntegrand`: `w z / sin(2θ)^{η/2}`. -/
def wE (z θ : ℝ) : ℝ := Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)

/-- The index set of the mixed slots at level `k`: the pairs `(θ-order, z-order)` with
`θ-order ≥ 1` and `θ-order + z-order ≤ k`. -/
def slots (k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
    (fun q : ℕ × ℕ => 1 ≤ q.1 ∧ q.1 + q.2 ≤ k)

theorem mem_slots {k : ℕ} {q : ℕ × ℕ} :
    q ∈ slots k ↔ 1 ≤ q.1 ∧ q.1 + q.2 ≤ k ∧ q.1 ≤ k ∧ q.2 ≤ k := by
  simp only [slots, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨h3, h4, by omega, by omega⟩
  · rintro ⟨h3, h4, h1, h2⟩
    exact ⟨⟨by omega, by omega⟩, h3, h4⟩

/-- The `D_z`-part of `HkIntegrand`, written with the weight `wE`. -/
theorem HkZPart_eq (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    HkSqAux.HkZPart k f z θ
      = ∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ * wE z θ) ^ 2 := rfl

/-- The mixed part of `HkIntegrand`, as a sum over the index set `slots k`. -/
theorem HkMPartF_eq (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    HkSqAux.HkMPartF α k f z θ
      = ∑ q ∈ slots k, (Work.Spaces.mixed q.2 q.1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := rfl

/-- `HkIntegrand` as the sum of its two explicit slot sums. -/
theorem HkIntegrand_eq (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α k f z θ
      = (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter i f z θ * wE z θ) ^ 2)
        + ∑ q ∈ slots k, (Work.Spaces.mixed q.2 q.1 f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  rw [HkSqAux.HkIntegrand_eq_parts, HkSqAux.HkMPart_eq_HkMPartF]
  rfl

/-! ## The level-`k+1` shadow of the level-`k` slots -/

/-- The **level-`k+1` shadow** of the level-`k` slot sum of `J_ε f - f`.  When the difference
estimate is applied to the slot `D_z^i h` (`h = J_ε f - f`) of `D_z^i f`, the two derivatives
`D_z` and `D_θ` that appear produce the level-`k+1` slots `(i+1, 0)` and `(i, 1)`; the mixed slot
`(j, i)` produces `(j+1, i)` and `(j, i+1)`.  This is the sum of those produced slots, written
with the *level-`k+1`* weights (`wE` for the pure `D_z`-slots, `Wt α` for the mixed ones).  The
`1/4` on the two `D_θ`-groups is the factor produced by the elementary inequality
`(a + b)² ≤ 2a² + 2b²` (with `b = (p₂/2) D_θ`). -/
def shadow (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter (i + 1) f z θ * wE z θ) ^ 2)
    + (1 / 4) * (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.mixed i 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
    + (∑ q ∈ slots k, (Work.Spaces.mixed (q.2 + 1) q.1 f z θ * Work.Spaces.Wt α z θ) ^ 2)
    + (1 / 4) * (∑ q ∈ slots k,
        (Work.Spaces.mixed q.2 (q.1 + 1) f z θ * Work.Spaces.Wt α z θ) ^ 2)

/-! ## Elementary positivity and comparison of the weights -/

theorem w_nonneg (z : ℝ) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  positivity

theorem wE_nonneg {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 ≤ wE z θ := by
  rw [wE]
  exact div_nonneg (w_nonneg z)
    (Real.rpow_nonneg (le_of_lt (Work.FTS.StrongEps.sin_two_pos hθ)) _)

theorem Wt_nonneg {α : ℝ} {z θ : ℝ} (hθ : θ ∈ Set.Icc 0 (π / 2)) :
    0 ≤ Work.Spaces.Wt α z θ := by
  rw [Work.Spaces.Wt, Work.Spaces.wTheta]
  exact mul_nonneg (w_nonneg z)
    (Real.rpow_nonneg (Work.FTS.StrongEps.sin_two_nonneg hθ) _)

/-- **The two weights of the paper are ordered**: `w / sin(2θ)^{η/2} ≤ w · sin(2θ)^{-γ/2}`,
because `η ≤ γ` and `sin(2θ) ≤ 1` on `[0, π/2]`. -/
theorem wE_le_Wt {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    wE z θ ≤ Work.Spaces.Wt α z θ := by
  have hs : 0 < Real.sin (2 * θ) := Work.FTS.StrongEps.sin_two_pos hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.eta, Work.Spaces.gam]
    linarith [hα.1]
  have hkey : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2)) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)
  rw [wE, Work.Spaces.Wt, Work.Spaces.wTheta]
  have hL : Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
      = Work.Spaces.w z * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hs)]
  rw [hL]
  exact mul_le_mul_of_nonneg_left hkey (w_nonneg z)

/-! ## Vanishing of the two weights on the boundary of the domain -/

/-- On the boundary of the closed quadrant (`z = 0`, `θ = 0` or `θ = π/2`) the weight `wE`
vanishes. -/
theorem wE_eq_zero_of_not_quad {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ)
    (hq : ¬(0 < z ∧ θ ∈ Set.Ioo 0 (π / 2))) : wE z θ = 0 := by
  rw [Work.Spaces.Iz] at hz
  rw [Work.Spaces.Iθ] at hθ
  rcases not_and_or.mp hq with hz0 | hθbad
  · have hz' : z = 0 := le_antisymm (not_lt.mp hz0) hz
    subst hz'
    rw [wE, Work.Spaces.w]
    simp
  · have hθbad' : θ ≤ 0 ∨ π / 2 ≤ θ := by
      rcases not_and_or.mp hθbad with h | h
      · exact Or.inl (not_lt.mp h)
      · exact Or.inr (not_lt.mp h)
    have hsin : Real.sin (2 * θ) = 0 := by
      rcases hθbad' with h | h
      · have h' : θ = 0 := le_antisymm h hθ.1
        subst h'
        simp
      · have h' : θ = π / 2 := le_antisymm hθ.2 h
        subst h'
        rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
    have hη : (Work.Spaces.eta / 2 : ℝ) ≠ 0 := by
      rw [Work.Spaces.eta]; norm_num
    rw [wE, hsin, Real.zero_rpow hη, div_zero]

/-- On the boundary of the closed quadrant the mixed weight `Wt α` vanishes. -/
theorem Wt_eq_zero_of_not_quad {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {z θ : ℝ}
    (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) (hq : ¬(0 < z ∧ θ ∈ Set.Ioo 0 (π / 2))) :
    Work.Spaces.Wt α z θ = 0 := by
  rw [Work.Spaces.Iz] at hz
  rw [Work.Spaces.Iθ] at hθ
  rcases not_and_or.mp hq with hz0 | hθbad
  · have hz' : z = 0 := le_antisymm (not_lt.mp hz0) hz
    subst hz'
    rw [Work.Spaces.Wt, Work.Spaces.w]
    simp
  · have hθbad' : θ ≤ 0 ∨ π / 2 ≤ θ := by
      rcases not_and_or.mp hθbad with h | h
      · exact Or.inl (not_lt.mp h)
      · exact Or.inr (not_lt.mp h)
    have hsin : Real.sin (2 * θ) = 0 := by
      rcases hθbad' with h | h
      · have h' : θ = 0 := le_antisymm h hθ.1
        subst h'
        simp
      · have h' : θ = π / 2 := le_antisymm hθ.2 h
        subst h'
        rw [show 2 * (π / 2) = π by ring, Real.sin_pi]
    have hg : (-(Work.Spaces.gam α / 2) : ℝ) ≠ 0 := by
      rw [Work.Spaces.gam]
      intro h
      have : α / 10 = -1 := by linarith
      linarith [hα.1]
    rw [Work.Spaces.Wt, Work.Spaces.wTheta, hsin, Real.zero_rpow hg, mul_zero]

end Work.FTS.StrongEps.DiffAux
