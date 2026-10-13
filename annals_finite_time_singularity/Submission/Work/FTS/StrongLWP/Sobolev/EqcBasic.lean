/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EqcBasic`: elementary calculus helpers for the equicontinuity estimate

Support module for `Sobolev/equicontinuous_deriv4_of_uniform_Hk6.lean`: operator-norm bounds from
the values on the standard basis of `ℝ × ℝ`, the elementary Cauchy–Schwarz inequalities
`(a+b)² ≤ 2(a²+b²)` etc., the vanishing of the derivatives of a function on an open set where it
vanishes, and the commuting of the iterated slice derivatives with a change of order.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.SmoothCompact_Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongLWP.Sobolev

set_option autoImplicit false

/-- The operator norm of a continuous linear map on `ℝ × ℝ` is bounded by the sum of the norms
of its values on the standard basis. -/
lemma eqc_opNorm_le_basis_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : (ℝ × ℝ) →L[ℝ] F) : ‖L‖ ≤ ‖L (1, 0)‖ + ‖L (0, 1)‖ := by
  rw [ContinuousLinearMap.opNorm_le_iff (by positivity)]
  intro h
  have hL : L h = h.1 • L ((1 : ℝ), (0 : ℝ)) + h.2 • L ((0 : ℝ), (1 : ℝ)) := by
    conv_lhs => rw [show h = h.1 • ((1 : ℝ), (0 : ℝ)) + h.2 • ((0 : ℝ), (1 : ℝ)) by
      ext <;> simp]
    rw [map_add, map_smul, map_smul]
  rw [hL]
  calc ‖h.1 • L (1, 0) + h.2 • L (0, 1)‖
      ≤ ‖h.1 • L (1, 0)‖ + ‖h.2 • L (0, 1)‖ := norm_add_le _ _
    _ = ‖h.1‖ * ‖L (1, 0)‖ + ‖h.2‖ * ‖L (0, 1)‖ := by rw [norm_smul, norm_smul]
    _ ≤ ‖h‖ * ‖L (1, 0)‖ + ‖h‖ * ‖L (0, 1)‖ :=
        add_le_add (mul_le_mul_of_nonneg_right (by simpa using norm_fst_le h) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (by simpa using norm_snd_le h) (norm_nonneg _))
    _ = (‖L (1, 0)‖ + ‖L (0, 1)‖) * ‖h‖ := by ring

/-- The same for the second derivative: a continuous linear map into `(ℝ × ℝ) →L[ℝ] ℝ` is
bounded by the sum of the absolute values of its four matrix entries. -/
lemma eqc_opNorm_le_basis_sum₂ (L : (ℝ × ℝ) →L[ℝ] ((ℝ × ℝ) →L[ℝ] ℝ)) :
    ‖L‖ ≤ |L (1, 0) (1, 0)| + |L (1, 0) (0, 1)| + |L (0, 1) (1, 0)| + |L (0, 1) (0, 1)| := by
  have h1 := eqc_opNorm_le_basis_sum L
  have h2 : ‖L (1, 0)‖ ≤ |L (1, 0) (1, 0)| + |L (1, 0) (0, 1)| := by
    simpa only [Real.norm_eq_abs] using eqc_opNorm_le_basis_sum (L (1, 0))
  have h3 : ‖L (0, 1)‖ ≤ |L (0, 1) (1, 0)| + |L (0, 1) (0, 1)| := by
    simpa only [Real.norm_eq_abs] using eqc_opNorm_le_basis_sum (L (0, 1))
  linarith

/-- `(a+b)² ≤ 2(a²+b²)`. -/
lemma eqc_sq_add2_le (a b : ℝ) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

/-- `(a+b+c)² ≤ 3(a²+b²+c²)`. -/
lemma eqc_sq_add3_le (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

/-- `(a+b+c+d)² ≤ 4(a²+b²+c²+d²)`. -/
lemma eqc_sq_add4_le (a b c d : ℝ) :
    (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c),
    sq_nonneg (b - d), sq_nonneg (c - d)]

/-- If a function vanishes on a neighbourhood of `x`, its derivative vanishes at `x`. -/
lemma eqc_fderiv_eq_zero_of_eqOn_nhds {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {v : E → F} {s : Set E} {x : E}
    (hs : s ∈ 𝓝 x) (hv : ∀ y ∈ s, v y = 0) : fderiv ℝ v x = 0 := by
  have hev : v =ᶠ[𝓝 x] (fun _ => (0 : F)) := Filter.eventuallyEq_iff_exists_mem.mpr ⟨s, hs, hv⟩
  rw [hev.fderiv_eq]
  simp

/-- If a function vanishes on an *open* set, so do its first and second derivatives. -/
lemma eqc_fderiv_fderiv_eq_zero_of_open {v : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hs : IsOpen s) (hv : ∀ y ∈ s, v y = 0) {x : ℝ × ℝ} (hx : x ∈ s) :
    fderiv ℝ v x = 0 ∧ fderiv ℝ (fderiv ℝ v) x = 0 := by
  have h1 : ∀ y ∈ s, fderiv ℝ v y = 0 :=
    fun y hy => eqc_fderiv_eq_zero_of_eqOn_nhds (hs.mem_nhds hy) hv
  exact ⟨h1 x hx, eqc_fderiv_eq_zero_of_eqOn_nhds (hs.mem_nhds hx) h1⟩

/-- `SmoothNbhd` is preserved by `pthIter`. -/
lemma eqc_smoothNbhd_pthIter {h : ℝ → ℝ → ℝ} (hh : Work.Spaces.SmoothNbhd h) :
    ∀ i : ℕ, Work.Spaces.SmoothNbhd (Work.Spaces.pthIter i h)
  | 0 => hh
  | i + 1 => by
      rw [Work.Spaces.pthIter_succ]
      exact Work.Spaces.SmoothNbhd.pth (eqc_smoothNbhd_pthIter hh i)

/-- `pzIter` composes. -/
lemma eqc_pzIter_comp (m n : ℕ) (h : ℝ → ℝ → ℝ) :
    Work.Spaces.pzIter (m + n) h = Work.Spaces.pzIter m (Work.Spaces.pzIter n h) := by
  induction m with
  | zero => simp
  | succ k ih => rw [Nat.succ_add, Work.Spaces.pzIter_succ, ih, Work.Spaces.pzIter_succ]

/-- `pthIter` composes. -/
lemma eqc_pthIter_comp (m n : ℕ) (h : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter (m + n) h = Work.Spaces.pthIter m (Work.Spaces.pthIter n h) := by
  induction m with
  | zero => simp
  | succ k ih => rw [Nat.succ_add, Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]

/-- The `pth`-analogue of `Work.Spaces.pz_congr_of_isOpen`. -/
lemma eqc_pth_congr_of_isOpen {f f' : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry f') V) {z θ : ℝ} (hx : (z, θ) ∈ V) :
    Work.Spaces.pth f z θ = Work.Spaces.pth f' z θ := by
  have htend : Tendsto (fun θ' : ℝ => (z, θ')) (𝓝 θ) (𝓝 (z, θ)) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hev : (fun θ' => f z θ') =ᶠ[𝓝 θ] (fun θ' => f' z θ') := by
    filter_upwards [htend.eventually (hV.mem_nhds hx)] with θ' hθ'
    exact h hθ'
  exact hev.deriv_eq

end Work.FTS.StrongLWP.Sobolev
