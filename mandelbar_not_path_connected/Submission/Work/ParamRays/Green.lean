/-
# The Green function (potential) of the mandelbar family

For the antiholomorphic unicritical family `T_c(z) = (conj z)^2 + c` we define the
Green function of the filled Julia set of `T_c` as the `limsup` of the normalized
logarithms of the iterates.  On the escaping set this is the classical limit

`G_c(z) = lim_n 2^{-n} log⁺ ‖T_c^[n] z‖`,

and `G_c` vanishes exactly on the filled Julia set.  The parameter potential
`paramPotential c = G_c 0` (the potential of the critical point) is the function
whose positivity detects the complement of the mandelbar, and whose exponential
gives the modulus of the Böttcher coordinate of the critical value.

## Main definitions

* `Work.ParamRays.greenSeq c w n = 2^{-n} log⁺ ‖T_c^[n] w‖`.
* `Work.ParamRays.greenFun c w = limsup_n greenSeq c w n` (the Green function).
* `Work.ParamRays.paramPotential c = greenFun c 0`.

## Main results (this file)

* `Work.ParamRays.greenFun_nonneg`, `Work.ParamRays.greenSeq_nonneg`.
* `Work.ParamRays.greenFun_le_of_eventually` : a limsup bound.
* `Work.ParamRays.greenFun_eq_of_tendsto` : if the normalized logarithms converge
  then the Green function equals their limit.
-/
import Submission.Work.ParamRays.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Real Topology

namespace Work.ParamRays

/-- The normalized logarithms `2^{-n} log⁺ ‖T_c^[n] w‖` of an orbit. -/
noncomputable def greenSeq (c w : ℂ) (n : ℕ) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * log⁺ ‖orbit c w n‖

/-- The Green function (potential) of the filled Julia set of `T_c`, defined as the
`limsup` of the normalized logarithms `greenSeq`.  On the escaping set this is the
classical limit `lim_n 2^{-n} log⁺ ‖T_c^[n] w‖`. -/
noncomputable def greenFun (c w : ℂ) : ℝ := Filter.limsup (greenSeq c w) Filter.atTop

/-- The **parameter potential**: the Green function of the critical orbit.  It is
positive exactly outside the mandelbar. -/
noncomputable def paramPotential (c : ℂ) : ℝ := greenFun c 0

theorem greenSeq_nonneg (c w : ℂ) (n : ℕ) : 0 ≤ greenSeq c w n := by
  rw [greenSeq]
  exact mul_nonneg (by positivity) Real.posLog_nonneg

/-- If the normalized logarithms are eventually bounded by `L`, then so is the
Green function. -/
theorem greenFun_le_of_eventually {c w : ℂ} {L : ℝ}
    (h : ∀ᶠ n : ℕ in Filter.atTop, greenSeq c w n ≤ L) : greenFun c w ≤ L := by
  rw [greenFun, Filter.limsup_eq]
  refine csInf_le ⟨0, ?_⟩ h
  intro x hx
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hx
  exact le_trans (greenSeq_nonneg c w a) (ha a le_rfl)

theorem greenFun_nonneg (c w : ℂ) : 0 ≤ greenFun c w := by
  rw [greenFun, Filter.limsup_eq]
  by_cases h : ({L : ℝ | ∀ᶠ n : ℕ in Filter.atTop, greenSeq c w n ≤ L}).Nonempty
  · refine le_csInf h fun L hL => ?_
    obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hL
    exact le_trans (greenSeq_nonneg c w a) (ha a le_rfl)
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

/-- If the normalized logarithms converge, the Green function is their limit. -/
theorem greenFun_eq_of_tendsto {c w : ℂ} {L : ℝ}
    (h : Filter.Tendsto (greenSeq c w) Filter.atTop (𝓝 L)) : greenFun c w = L := by
  refine le_antisymm ?_ ?_
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have h' : ∀ᶠ n : ℕ in Filter.atTop, greenSeq c w n ≤ L + ε :=
      h.eventually_le_const (by linarith)
    exact le_trans (greenFun_le_of_eventually h') (by linarith)
  · rw [greenFun, Filter.limsup_eq]
    refine le_csInf ⟨L + 1, h.eventually_le_const (by linarith)⟩ fun M hM => ?_
    by_contra hcon
    have hML : M < L := lt_of_not_ge hcon
    have h2 : ∀ᶠ n : ℕ in Filter.atTop, M < greenSeq c w n := by
      have h3 : Filter.Tendsto (fun n : ℕ => -greenSeq c w n) Filter.atTop (𝓝 (-L)) := h.neg
      have h4 : -L < -M := by linarith
      filter_upwards [h3.eventually_lt_const h4] with n hn
      linarith
    obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp (hM.and h2)
    obtain ⟨h1, h2'⟩ := ha a le_rfl
    linarith

end Work.ParamRays
