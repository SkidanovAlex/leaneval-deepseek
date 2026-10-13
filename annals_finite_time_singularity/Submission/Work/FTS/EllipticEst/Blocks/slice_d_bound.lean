import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.SliceAux
import Submission.Work.FTS.EllipticEst.Lop_iter_mul
import Submission.Work.FTS.EllipticEst.Lop_iter_cos_eq
import Submission.Work.FTS.EllipticEst.slice_deriv_sq_le
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.sd_lop_iter_sin_bound
import Submission.Work.FTS.EllipticEst.Blocks.SliceDBook
import Submission.Work.EllipticEst.Blocks.slice_d_expansion
import Submission.Work.EllipticEst.Blocks.slice_d_alg_core

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Blocks

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Two bookkeeping lemmas about the dominating function `slicePhi` -/

/-- `slicePhi` dominates its `A`-term `A · sin(2θ)^{-η}`. -/
theorem slicePhi_ge_Aterm (α : ℝ) (K : ℕ) (u : ℝ → ℝ) {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.sliceA u * Work.FTS.EllipticEst.thEta θ
      ≤ Work.FTS.EllipticEst.slicePhi α K u θ := by
  have hsum := slicePhi_sum_nonneg α K u hθ
  have hA := sliceA_nonneg u
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.sin_two_nonneg hθ
  have hs1 : 0 ≤ Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) := Real.rpow_nonneg hs _
  have hs2 : 0 ≤ Real.sin (2 * θ) ^ (4 - Work.Spaces.gam α) := Real.rpow_nonneg hs _
  have hth : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
  have hV : 0 ≤ (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ :=
    mul_nonneg (sq_nonneg _) hth
  have hkey : Work.FTS.EllipticEst.sliceA u * (Work.FTS.EllipticEst.thEta θ
      + Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
      + Real.sin (2 * θ) ^ (4 - Work.Spaces.gam α))
      = Work.FTS.EllipticEst.sliceA u * Work.FTS.EllipticEst.thEta θ
        + Work.FTS.EllipticEst.sliceA u * (Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
          + Real.sin (2 * θ) ^ (4 - Work.Spaces.gam α)) := by ring
  have h2 : 0 ≤ Work.FTS.EllipticEst.sliceA u * (Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
      + Real.sin (2 * θ) ^ (4 - Work.Spaces.gam α)) := mul_nonneg hA (add_nonneg hs1 hs2)
  rw [Work.FTS.EllipticEst.slicePhi, hkey]
  linarith

/-- Every summand `(D_θ^m u'')² sin(2θ)^{2-γ}` of the `L`-expansion of `∂_θ`-iterates is
dominated by `slicePhi`:  for `m = 0` by the `η`-term (`sin(2θ)^{2-γ} ≤ sin(2θ)^{-η}`), for
`m ≥ 1` by the corresponding `γ`-weighted term. -/
theorem slice_d_term_le_phi {α : ℝ} (hα : α ≤ 1) {u : ℝ → ℝ} (K m : ℕ) (hm : m ≤ K)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
        * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α)
      ≤ Work.FTS.EllipticEst.slicePhi α K u θ := by
  by_cases hm0 : m = 0
  · subst hm0
    have hcmp := sin_two_rpow_two_sub_le_thEta (gam_lt_two hα) (gam_le_two_add_eta hα) hθ
    have hsq : 0 ≤ (Work.FTS.EllipticEst.sliceV u θ) ^ 2 := sq_nonneg _
    exact le_trans (mul_le_mul_of_nonneg_left hcmp hsq) (slicePhi_ge_Vterm α K u hθ)
  · have hm1 : 1 ≤ m := by omega
    have hmem : m ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨hm1, hm⟩
    have hcmp := sin_two_rpow_two_sub_le_thGam (α := α) (gam_lt_two hα) hθ
    have hsq : 0 ≤ (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2 :=
      sq_nonneg _
    exact le_trans (mul_le_mul_of_nonneg_left hcmp hsq)
      (slicePhi_ge_gamterm α K m u hθ hmem)

/-- **The `∂_θ`-slice estimate of the angular `θ`-Poincaré inequality.**  For a smooth slice `u` vanishing at `θ = 0, π/2`, with `v = u''`, `A = ∫_{Iθ} v² sin(2θ)^{-η}` and the dominating function

`slicePhi α K u θ = v θ² sin(2θ)^{-η} + ∑_{m=1}^{K} (D_θ^m v θ)² sin(2θ)^{-γ} + A·(sin(2θ)^{-η} + sin(2θ)^{2-γ} + sin(2θ)^{4-γ})`

(`γ = gam α = 1 + α/10`, `η = eta = 99/100`), one has for every `θ ∈ Iθ`

`(∂_θ u θ)² sin(2θ)^{-η} ≤ C · slicePhi α K u θ`  and  `(D_θ^i (∂_θ u) θ)² sin(2θ)^{-γ} ≤ C · slicePhi α K u θ` for every `1 ≤ i ≤ K`,

with `C` independent of `α ∈ (0,1]` and of `u`.  This is one of the two analytic slice cores of the `ℋ^k`-estimate `theta_poincare_Hk` (the other is `slice_f_bound`).

NOTE.  Use namespace `Work.FTS.EllipticEst.Blocks` (a declaration `Work.FTS.EllipticEst.slice_d_bound` with this statement already exists in a `sorry`-containing sibling; do not import it).

ROUTE (pointwise; `L = D_θ = LopIter 1`).  `L(∂_θ u) = sin(2θ)·v` pointwise, hence for `i ≥ 1` `L^i(∂_θ u) = L^{i-1}(sin(2θ)·v)`, and the Leibniz rule for `L` (`Lop_iter_mul`) expands this as a finite combination of terms `L^a(sin 2θ)·L^m v` with `a + m = i - 1`; use `|L^a(sin 2θ) θ| ≤ C_a sin(2θ)` (`sd_lop_iter_sin_bound` in `Submission/Work/FTS/EllipticEst/sd_lop_iter_sin_bound.lean`, sorry-free).  Each resulting term is at most a fixed constant times `sin(2θ)^{2}`·(weighted `v`-term); the case `m = 0` is dominated by `v² sin(2θ)^{2-γ} ≤ C·slicePhi` (using `2 - γ ≥ -η`), the cases `m ≥ 1` by `(L^m v)² sin(2θ)^{2-γ} ≤ C·slicePhi` (using `2 - γ ≥ -γ`).  The first conjunct follows from `slice_deriv_sq_le` (valid since `u 0 = u (π/2)`).  All constants are uniform in `α ∈ (0,1]` since only `η = 99/100` and `1 < γ ≤ 11/10` enter.  At `θ = 0, π/2` both sides vanish. -/
theorem slice_d_bound (K : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 → Work.FTS.EllipticEst.SliceSmooth u → u 0 = 0
      → u (Real.pi / 2) = 0
      → MeasureTheory.IntegrableOn
          (fun θ => (Work.FTS.EllipticEst.sliceV u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
          Work.Spaces.Iθ
      → (∀ m ∈ Finset.Icc 1 K, MeasureTheory.IntegrableOn
          (fun θ => (Work.FTS.EllipticEst.LopIter m (Work.FTS.EllipticEst.sliceV u) θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ) Work.Spaces.Iθ)
      → (∀ θ ∈ Work.Spaces.Iθ, (deriv u θ) ^ 2 * Work.FTS.EllipticEst.thEta θ
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
  · -- first conjunct: `slice_deriv_sq_le` plus `∫ sin(2θ)^η ≤ π/2`
    intro θ hθ
    have hder := Work.FTS.EllipticEst.slice_deriv_sq_le hsm (by rw [h0, h1]) hint θ hθ
    have hB : (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (Work.Spaces.eta)) ≤ Real.pi / 2 :=
      (Work.FTS.EllipticEst.integrableOn_sin_two_rpow (le_of_lt Work.Spaces.eta_pos)).2
    have hA : 0 ≤ Work.FTS.EllipticEst.sliceA u := sliceA_nonneg u
    have hth : 0 ≤ Work.FTS.EllipticEst.thEta θ := Work.FTS.EllipticEst.thEta_nonneg hθ
    have hAterm := slicePhi_ge_Aterm α K u hθ
    have hphi : 0 ≤ Work.FTS.EllipticEst.slicePhi α K u θ := slicePhi_nonneg α K u hθ
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
    have hΦ : 0 ≤ Work.FTS.EllipticEst.slicePhi α K u θ := slicePhi_nonneg α K u hθ
    have hCc : (0 : ℝ) ≤ (2 : ℝ) ^ K := by positivity
    -- the expansion `L^{j+1} (∂_θ u) = L^j (sin(2θ) · u'')`, Leibniz
    have hexp := Work.EllipticEst.Blocks.slice_d_expansion hsm j hθ
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
      exact slice_d_term_le_phi (u := u) hα1 K (j - a) (by omega) hθ
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

end Work.FTS.EllipticEst.Blocks
