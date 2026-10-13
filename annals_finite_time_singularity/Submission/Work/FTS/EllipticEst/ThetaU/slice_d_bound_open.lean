import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceDefs
import Submission.Work.FTS.EllipticEst.ThetaU.SliceDerivSelfOpen
import Submission.Work.FTS.EllipticEst.Blocks.slice_d_bound
import Submission.Work.FTS.EllipticEst.sd_lop_iter_sin_bound
import Submission.Work.FTS.LocData.DthIter_mul_smoothQuad

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.ThetaU

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The iterated Leibniz expansion of `L^{j+1} (∂_θ u)` in the honest `C^∞` class.**
This is `Work.EllipticEst.Blocks.slice_d_expansion` with the analytic class
`Work.FTS.EllipticEst.SliceSmooth` replaced by `SliceSmoothO`: the only change is that the
iterated Leibniz rule is taken from `Work.FTS.LocData.Lop_iter_mul_eqOn_smooth` (genuine
smooth order, stated as an `EqOn` on an open set) rather than from the analytic
`Work.FTS.EllipticEst.Lop_iter_mul`.  The argument is otherwise verbatim. -/
theorem slice_d_expansion_O {u : ℝ → ℝ} (hsm : SliceSmoothO u) (j : ℕ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.LopIter (j + 1) (deriv u) θ =
      ∑ a ∈ Finset.range (j + 1),
        (j.choose a : ℝ)
          * Work.FTS.EllipticEst.LopIter a (fun θ : ℝ => Real.sin (2 * θ)) θ
          * Work.FTS.EllipticEst.LopIter (j - a) (Work.FTS.EllipticEst.sliceV u) θ := by
  -- `LopIter (j+1) (deriv u) = LopIter j (sin(2·) * sliceV u)`, since
  -- `Lop (deriv u) θ = sin(2θ) * deriv (deriv u) θ = sin(2θ) * sliceV u θ`.
  have hstep : Work.FTS.EllipticEst.LopIter (j + 1) (deriv u)
      = Work.FTS.EllipticEst.LopIter j
          (fun θ : ℝ => Real.sin (2 * θ) * Work.FTS.EllipticEst.sliceV u θ) := by
    rw [Work.FTS.EllipticEst.LopIter, Function.iterate_succ_apply]
    rfl
  rw [hstep]
  -- the point `θ` lies in the open neighbourhood on which the slices are `C^∞`
  have hU : θ ∈ Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1) := by
    rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
    exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  -- the two factors are `C^∞` (genuine smooth order) on that neighbourhood
  have hf : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by fun_prop
  have hg : ContDiffOn ℝ Work.Stability.smoothOrder
      (Work.FTS.EllipticEst.sliceV u) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) := by
    have h1 : ContDiffOn ℝ Work.Stability.smoothOrder (deriv u)
        (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) :=
      hsm.deriv_of_isOpen isOpen_Ioo (le_of_eq Work.FTS.LocData.smoothOrder_add_one)
    exact h1.deriv_of_isOpen isOpen_Ioo (le_of_eq Work.FTS.LocData.smoothOrder_add_one)
  -- the iterated Leibniz rule at the genuine smooth order
  have hmain := Work.FTS.LocData.Lop_iter_mul_eqOn_smooth
    (fun θ : ℝ => Real.sin (2 * θ)) (Work.FTS.EllipticEst.sliceV u)
    (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1)) isOpen_Ioo hf hg j hU
  rw [show Work.FTS.EllipticEst.LopIter j
        (fun θ : ℝ => Real.sin (2 * θ) * Work.FTS.EllipticEst.sliceV u θ) θ
      = ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ)
          * (Work.Spaces.Lop^[a] (fun θ : ℝ => Real.sin (2 * θ)) θ
            * Work.Spaces.Lop^[j - a] (Work.FTS.EllipticEst.sliceV u) θ) from hmain]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Work.FTS.EllipticEst.LopIter, Work.FTS.EllipticEst.LopIter]
  ring

/-- The `∂_θ`-slice estimate in the honest `C^∞` class `SliceSmoothO`: same statement as
`Work.FTS.EllipticEst.Blocks.slice_d_bound` with the analytic
`Work.FTS.EllipticEst.SliceSmooth u = ContDiffOn ℝ ⊤ u _` (`⊤ = ω` is analyticity in this
Mathlib) replaced by `Work.FTS.EllipticEst.ThetaU.SliceSmoothO u = ContDiffOn ℝ ∞ u _`.

PROOF: copy `Submission/Work/FTS/EllipticEst/Blocks/slice_d_bound.lean`, replacing `SliceSmooth`
by `SliceSmoothO`; the ingredient `ThetaU.slice_deriv_sq_le_open`
(`Submission/Work/FTS/EllipticEst/ThetaU/SliceDerivSelfOpen.lean`) is already available in the
`C^∞` class, and the Leibniz rule `Lop_iter_mul` (stated with the analytic `ContDiffAt ℝ ⊤`) has
the `C^∞` counterpart `Work.FTS.LocData.Lop_iter_mul_eqOn_smooth` (open set +
`Work.Stability.smoothOrder`). -/
theorem slice_d_bound_open (K : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.ThetaU.SliceSmoothO u →
      u 0 = 0 → u (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
        Work.Spaces.Iθ →
      (∀ m ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn
        (fun θ => (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ) →
      (∀ θ ∈ Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
            ≤ C * Work.FTS.EllipticEst.slicePhi α K u θ)
        ∧ (∀ i ∈ Finset.Icc 1 K, ∀ θ ∈ Work.Spaces.Iθ,
            (Work.FTS.EllipticEst.LopIter i (deriv u) θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ
              ≤ C * Work.FTS.EllipticEst.slicePhi α K u θ) := by
  -- the bound `|L^a (sin 2θ)| ≤ Cs · sin(2θ)` for all `a ≤ K`, from the sibling file
  obtain ⟨Cs, hCspos, hCsb⟩ := Work.FTS.EllipticEst.sd_lop_iter_sin_bound K
  have hCs0 : 0 ≤ Cs := le_of_lt hCspos
  -- the universal constant: it majorises `π/2` (the `∂_θ u`-case) and
  -- `(2^K)² Cs² K²` (the `D_θ^i ∂_θ u`-case, where at most `K` terms are summed,
  -- the binomial coefficients are `≤ 2^K` and each `|L^a sin| ≤ Cs sin 2θ`)
  refine ⟨max (Real.pi / 2) (((2 : ℝ) ^ K) ^ 2 * Cs ^ 2 * (K : ℝ) ^ 2),
    lt_max_of_lt_left (by positivity), ?_⟩
  intro α u hα hα1 hsm h0 h1 hint hintK
  refine ⟨?_, ?_⟩
  · -- first conjunct: `slice_deriv_sq_le_open` plus `∫ sin(2θ)^η ≤ π/2`
    intro θ hθ
    have hder := slice_deriv_sq_le_open hsm (by rw [h0, h1]) hint θ hθ
    have hB : (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (Work.Spaces.eta)) ≤ Real.pi / 2 :=
      (Work.FTS.EllipticEst.integrableOn_sin_two_rpow (le_of_lt Work.Spaces.eta_pos)).2
    have hA : 0 ≤ Work.FTS.EllipticEst.sliceA u :=
      Work.FTS.EllipticEst.Blocks.sliceA_nonneg u
    have hth : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
    have hAterm := Work.FTS.EllipticEst.Blocks.slicePhi_ge_Aterm α K u hθ
    have hphi : 0 ≤ Work.FTS.EllipticEst.slicePhi α K u θ :=
      Work.FTS.EllipticEst.Blocks.slicePhi_nonneg α K u hθ
    have hCge : Real.pi / 2
        ≤ max (Real.pi / 2) (((2 : ℝ) ^ K) ^ 2 * Cs ^ 2 * (K : ℝ) ^ 2) := le_max_left _ _
    calc (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
        ≤ (Work.FTS.EllipticEst.sliceA u
            * (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (Work.Spaces.eta)))
            * Work.FTS.EllipticEst.thEta θ := mul_le_mul_of_nonneg_right hder hth
      _ = Work.FTS.EllipticEst.sliceA u
            * ((∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (Work.Spaces.eta))
              * Work.FTS.EllipticEst.thEta θ) := by ring
      _ ≤ Work.FTS.EllipticEst.sliceA u
            * ((Real.pi / 2) * Work.FTS.EllipticEst.thEta θ) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hB hth) hA
      _ = (Real.pi / 2) * (Work.FTS.EllipticEst.sliceA u * Work.FTS.EllipticEst.thEta θ) := by
          ring
      _ ≤ (Real.pi / 2) * Work.FTS.EllipticEst.slicePhi α K u θ :=
          mul_le_mul_of_nonneg_left hAterm (by positivity)
      _ ≤ (max (Real.pi / 2) (((2 : ℝ) ^ K) ^ 2 * Cs ^ 2 * (K : ℝ) ^ 2))
            * Work.FTS.EllipticEst.slicePhi α K u θ := mul_le_mul_of_nonneg_right hCge hphi
  · -- second conjunct: the Leibniz expansion of `L^i (∂_θ u)`, the pointwise bound
    -- `|L^a sin(2θ)| ≤ Cs sin(2θ)`, and the algebraic core
    intro i hi θ hθ
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.mp hi
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = j + 1 := ⟨i - 1, by omega⟩
    have hjK : j + 1 ≤ K := hi2
    have hσ : 0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.sin_two_nonneg hθ
    have hΦ : 0 ≤ Work.FTS.EllipticEst.slicePhi α K u θ :=
      Work.FTS.EllipticEst.Blocks.slicePhi_nonneg α K u hθ
    have hCc : (0 : ℝ) ≤ (2 : ℝ) ^ K := by positivity
    -- the expansion `L^{j+1} (∂_θ u) = L^j (sin(2θ) · u'')`, Leibniz in the `C^∞` class
    have hexp := slice_d_expansion_O hsm j hθ
    -- the binomial coefficients are bounded by `2^K`
    have hc : ∀ a ∈ Finset.range (j + 1), |(j.choose a : ℝ)| ≤ (2 : ℝ) ^ K := by
      intro a ha
      have haj : a ≤ j := by have := Finset.mem_range.mp ha; omega
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      have h1 : j.choose a ≤ 2 ^ j := Nat.choose_le_two_pow j a
      have h2R : (((2 : ℕ) ^ j : ℕ) : ℝ) ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) := by
        push_cast
        exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega : j ≤ K)
      calc (j.choose a : ℝ) ≤ (((2 : ℕ) ^ j : ℕ) : ℝ) := by exact_mod_cast h1
        _ ≤ (((2 : ℕ) ^ K : ℕ) : ℝ) := h2R
        _ = (2 : ℝ) ^ K := by push_cast; ring
    -- the pointwise bound on the `sin(2θ)`-factors
    have hS : ∀ a ∈ Finset.range (j + 1),
        |Work.FTS.EllipticEst.LopIter a (fun θ : ℝ => Real.sin (2 * θ)) θ|
          ≤ Cs * Real.sin (2 * θ) := by
      intro a ha
      exact hCsb a (by have := Finset.mem_range.mp ha; omega) θ hθ
    -- each `u''`-factor is dominated by `slicePhi`
    have hY : ∀ a ∈ Finset.range (j + 1),
        (Work.FTS.EllipticEst.LopIter (j - a) (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
          * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
          ≤ Work.FTS.EllipticEst.slicePhi α K u θ := by
      intro a ha
      have haj : a ≤ j := by have := Finset.mem_range.mp ha; omega
      exact Work.FTS.EllipticEst.Blocks.slice_d_term_le_phi (u := u) hα1 K (j - a) (by omega) hθ
    have hcore := Work.EllipticEst.Blocks.slice_d_alg_core (j := j) (σ := Real.sin (2 * θ))
      (γ := Work.Spaces.gam α) (Φ := Work.FTS.EllipticEst.slicePhi α K u θ)
      (Cc := (2 : ℝ) ^ K) (Cs := Cs) (c := fun a => (j.choose a : ℝ))
      (S := fun a => Work.FTS.EllipticEst.LopIter a (fun θ : ℝ => Real.sin (2 * θ)) θ)
      (Y := fun a => Work.FTS.EllipticEst.LopIter (j - a) (Work.FTS.EllipticEst.sliceV u) θ)
      hσ hCc hCs0 hΦ hc hS hY
    -- the constant is dominated by the chosen universal `C`
    have hK2 : (((j + 1 : ℕ)) : ℝ) ^ 2 ≤ (((K : ℕ)) : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hjK) 2
    have hconst : ((2 : ℝ) ^ K) ^ 2 * Cs ^ 2 * (((j + 1 : ℕ)) : ℝ) ^ 2
        ≤ max (Real.pi / 2) (((2 : ℝ) ^ K) ^ 2 * Cs ^ 2 * (K : ℝ) ^ 2) := by
      have hnn : 0 ≤ ((2 : ℝ) ^ K) ^ 2 * Cs ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
      calc ((2 : ℝ) ^ K) ^ 2 * Cs ^ 2 * (((j + 1 : ℕ)) : ℝ) ^ 2
          ≤ ((2 : ℝ) ^ K) ^ 2 * Cs ^ 2 * (((K : ℕ)) : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left hK2 hnn
        _ ≤ max (Real.pi / 2) (((2 : ℝ) ^ K) ^ 2 * Cs ^ 2 * (K : ℝ) ^ 2) := le_max_right _ _
    rw [hexp]
    exact le_trans hcore (mul_le_mul_of_nonneg_right hconst hΦ)

end Work.FTS.EllipticEst.ThetaU
