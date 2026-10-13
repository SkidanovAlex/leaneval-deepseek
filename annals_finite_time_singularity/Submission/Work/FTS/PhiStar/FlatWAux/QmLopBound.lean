/-
# `Work.FTS.PhiStar.FlatWAux.QmLopBound`

Growth bound for the `Lop`-iterates of the angular derivative of the divided mode
`Qm m = eFam m / sin 2θ`:

  `|(D_θ)^i (∂_θ Qm m)(θ)| ≤ C i · (2m+1)^(2i+4)`   (`m ≥ 1`, `i ≤ 6`, `θ ∈ (0,π/2)`).

`Work.Spaces.Lop = D_θ = sin(2θ)·∂_θ` is a first-order operator, so `Lop^[i] (∂_θ Qm m)` is a
finite sum of `∂_θ^{r+1}(Qm m)` (`r ≤ i`) with coefficients `a_{i,r}` that are polynomials in
`sin 2θ, cos 2θ`, hence bounded by a constant depending only on `i`.  Each `∂_θ^l(Qm m)`,
`l ≤ 7`, is controlled by `QmDerivBound`.  Multiplying out gives the claim, since every
`(2m+1)^{2r+4} ≤ (2m+1)^{2i+4}` for `r ≤ i`, `2m+1 ≥ 1`.

The one non-elementary input is the expansion identity for the iterated operator
(`Lop_iter_expansion`), obtained from the exact angular expansion
`D_θ^i = Σ_{r ≤ i} a_{i,r} ∂_θ^r` of `Work.FTS.EllipticEst.remov.selfdth`.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.QmDerivBound
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.EllipticEst.remov.high_chain_sum_self

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open Filter Set

namespace Work.FTS.PhiStar.FlatWAux

set_option autoImplicit false

/-! ## The smoothness of the divided mode on the open quadrant -/

/-- Every Gegenbauer polynomial is `C^k` for every `k` (the recurrence only involves products
and divisions by a positive constant). -/
theorem gC_contDiff_all_fts : ∀ k n : ℕ, ContDiff ℝ k (Work.FTS.PhiStar.Gegenbauer.gC n) := by
  intro k n
  induction n using Nat.twoStepInduction with
  | zero =>
      rw [show Work.FTS.PhiStar.Gegenbauer.gC 0 = (fun _ : ℝ => (1 : ℝ)) from rfl]
      exact contDiff_const
  | one =>
      rw [show Work.FTS.PhiStar.Gegenbauer.gC 1 = (fun x : ℝ => 3 * x) from rfl]
      exact contDiff_const.mul contDiff_id
  | more n ih1 ih2 =>
      rw [show Work.FTS.PhiStar.Gegenbauer.gC (n + 2) = (fun x : ℝ =>
        (2 * ((n : ℝ) + 5 / 2) * x * Work.FTS.PhiStar.Gegenbauer.gC (n + 1) x
          - ((n : ℝ) + 3) * Work.FTS.PhiStar.Gegenbauer.gC n x) / ((n : ℝ) + 2)) from rfl]
      exact (((contDiff_const.mul contDiff_id).mul ih2).sub (contDiff_const.mul ih1)).div_const _

/-- `Qm m` is `C^n` on the open quadrant, for every `n`. -/
theorem contDiffOn_Qm_fts (m n : ℕ) :
    ContDiffOn ℝ n (Qm m) (Set.Ioo 0 (Real.pi / 2)) := by
  have heFam : ContDiffOn ℝ n (Work.FTS.PhiStar.Gegenbauer.eFam m)
      (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.contDiff_cos.mul ((gC_contDiff_all_fts n (2 * m + 1)).comp Real.contDiff_sin)).contDiffOn
  have hs2 : ContDiffOn ℝ n (Work.Construction.s2) (Set.Ioo 0 (Real.pi / 2)) := by
    show ContDiffOn ℝ n (fun θ : ℝ => Real.sin (2 * θ)) _
    exact (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn
  have hne : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.Construction.s2 θ ≠ 0 := by
    intro θ hθ
    rw [Work.Construction.s2_eq, Real.sin_two_mul]
    exact mul_ne_zero
      (mul_ne_zero two_ne_zero (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθ.1
        (by linarith [hθ.2, Real.pi_pos]))))
      (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩))
  show ContDiffOn ℝ n (fun θ => Work.FTS.PhiStar.Gegenbauer.eFam m θ
    / Work.Construction.s2 θ) _
  exact heFam.div hs2 hne

/-- The angular derivative of the divided mode is `C^k` at every interior point, for every
`k`. -/
theorem contDiffAt_deriv_Qm_fts (m : ℕ) : ∀ k : ℕ, ∀ θ : ℝ,
    θ ∈ Set.Ioo 0 (Real.pi / 2) → ContDiffAt ℝ k (deriv (Qm m)) θ := by
  intro k θ hθ
  have h1 : ContDiffAt ℝ (k + 1) (Qm m) θ :=
    (contDiffOn_Qm_fts m (k + 1)).contDiffAt (isOpen_Ioo.mem_nhds hθ)
  have h2 : ContDiffAt ℝ k (deriv (Qm m)) θ :=
    h1.derivWithin (m := (k : WithTop ℕ∞)) (by simp)
  exact h2

/-! ## The expansion of `Lop^[i]` in powers of `∂_θ` -/

/-- `Lop^[i] g` expanded in the plain derivatives of `g`, at a point where `g` is `C^∞`. -/
theorem Lop_iter_expansion (i : ℕ) (g : ℝ → ℝ) (θ : ℝ)
    (hg : ∀ k : ℕ, ContDiffAt ℝ k g θ) :
    (Work.Spaces.Lop^[i]) g θ = ∑ r ∈ Finset.range (i + 1),
      Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv r g θ := by
  have hf : ∀ k : ℕ, ContDiffAt ℝ k
      (Function.uncurry (fun (_ : ℝ) (θ' : ℝ) => g θ')) (0, θ) := by
    intro k
    have hsnd : ContDiffAt ℝ k (Prod.snd : ℝ × ℝ → ℝ) ((0 : ℝ), θ) := contDiff_snd.contDiffAt
    have hgk : ContDiffAt ℝ k g (Prod.snd ((0 : ℝ), θ)) := hg k
    have hcomp : ContDiffAt ℝ k (Function.uncurry (fun (_ : ℝ) (θ' : ℝ) => g θ')) (0, θ) :=
      ContDiffAt.comp ((0 : ℝ), θ) hgk hsnd
    exact hcomp
  have hexp := Work.FTS.EllipticEst.remov.selfdth.DthIter_expansion_local i
    (fun (_ : ℝ) (θ' : ℝ) => g θ') 0 θ hf
  have hL : Work.Spaces.DthIter i (fun (_ : ℝ) (θ' : ℝ) => g θ') 0 θ
      = (Work.Spaces.Lop^[i]) g θ := by
    have h := congrFun
      (Work.Spaces.DthIter_eq_iterate_Lop i (fun (_ : ℝ) (θ' : ℝ) => g θ') 0) θ
    simpa using h
  rw [← hL, hexp]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Work.FTS.EllipticEst.remov.selfdth.pthIter_eq_iteratedDeriv_slice]

/-- `|sin(2θ)|^r ≤ 1`. -/
theorem abs_sin_two_pow_le_one (r : ℕ) (θ : ℝ) : |Real.sin (2 * θ)| ^ r ≤ 1 :=
  pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one _)

/-! ## The bound -/

theorem QmLopBound : ∃ C : ℕ → ℝ, (∀ i : ℕ, 0 ≤ C i) ∧
    ∀ (m : ℕ), 1 ≤ m → ∀ (i : ℕ), i ≤ 6 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |(Work.Spaces.Lop^[i]) (deriv (Work.FTS.PhiStar.FlatWAux.Qm m)) θ|
        ≤ C i * (2 * (m : ℝ) + 1) ^ (2 * i + 4) := by
  -- uniform bounds for the coefficients of the expansion
  obtain ⟨KB, hKBpos, hKB⟩ : ∃ KB : ℕ × ℕ → ℝ, (∀ p : ℕ × ℕ, 0 < KB p) ∧
      ∀ (p : ℕ × ℕ) (θ : ℝ),
        |Work.FTS.EllipticEst.remov.selfdth.dthCoef p.1 p.2 θ|
          ≤ KB p * |Real.sin (2 * θ)| ^ p.2 := by
    choose KB hpos hbd using fun p : ℕ × ℕ =>
      Work.FTS.EllipticEst.remov.selfdth.DthCoef_sin_pow_bound p.1 p.2
    exact ⟨KB, hpos, hbd⟩
  -- the derivative growth of the divided mode
  obtain ⟨C₀, hC₀nn, hC₀⟩ := QmDerivBound
  refine ⟨fun i => ∑ r ∈ Finset.range (i + 1), KB (i, r) * C₀ (r + 1), ?_, ?_⟩
  · intro i
    exact Finset.sum_nonneg fun r _ => mul_nonneg (le_of_lt (hKBpos (i, r))) (hC₀nn (r + 1))
  · intro m hm i hi θ hθ
    have hbase : (1 : ℝ) ≤ 2 * (m : ℝ) + 1 := by
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    have hexp := Lop_iter_expansion i (deriv (Qm m)) θ
      (fun k => contDiffAt_deriv_Qm_fts m k θ hθ)
    have hstep : ∀ r : ℕ,
        iteratedDeriv r (deriv (Qm m)) θ = iteratedDeriv (r + 1) (Qm m) θ :=
      fun r => congrFun (iteratedDeriv_succ' (n := r) (f := Qm m)).symm θ
    have hsum : (∑ r ∈ Finset.range (i + 1),
          Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv r (deriv (Qm m)) θ)
        = ∑ r ∈ Finset.range (i + 1),
          Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) (Qm m) θ :=
      Finset.sum_congr rfl fun r _ => by rw [hstep r]
    rw [hexp, hsum]
    calc |∑ r ∈ Finset.range (i + 1),
          Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ * iteratedDeriv (r + 1) (Qm m) θ|
        ≤ ∑ r ∈ Finset.range (i + 1),
            |Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ
              * iteratedDeriv (r + 1) (Qm m) θ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ Finset.range (i + 1),
            (KB (i, r) * C₀ (r + 1)) * (2 * (m : ℝ) + 1) ^ (2 * i + 4) := by
          apply Finset.sum_le_sum
          intro r hr
          have hrle : r ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
          have hr8 : r + 1 ≤ 8 := by omega
          rw [abs_mul]
          have h1 : |Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ| ≤ KB (i, r) := by
            refine le_trans (hKB (i, r) θ) ?_
            exact mul_le_of_le_one_right (le_of_lt (hKBpos (i, r)))
              (abs_sin_two_pow_le_one r θ)
          have h2 : |iteratedDeriv (r + 1) (Qm m) θ|
              ≤ C₀ (r + 1) * (2 * (m : ℝ) + 1) ^ (2 * (r + 1) + 2) :=
            hC₀ m hm (r + 1) hr8 θ hθ
          have h3 : (2 * (m : ℝ) + 1) ^ (2 * (r + 1) + 2)
              ≤ (2 * (m : ℝ) + 1) ^ (2 * i + 4) := by
            apply pow_le_pow_right₀ hbase
            omega
          calc |Work.FTS.EllipticEst.remov.selfdth.dthCoef i r θ|
                * |iteratedDeriv (r + 1) (Qm m) θ|
              ≤ KB (i, r) * (C₀ (r + 1) * (2 * (m : ℝ) + 1) ^ (2 * (r + 1) + 2)) :=
                mul_le_mul h1 h2 (abs_nonneg _) (le_of_lt (hKBpos (i, r)))
            _ ≤ KB (i, r) * (C₀ (r + 1) * (2 * (m : ℝ) + 1) ^ (2 * i + 4)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left h3 (hC₀nn (r + 1)))
                  (le_of_lt (hKBpos (i, r)))
            _ = (KB (i, r) * C₀ (r + 1)) * (2 * (m : ℝ) + 1) ^ (2 * i + 4) := by ring
      _ = (∑ r ∈ Finset.range (i + 1), KB (i, r) * C₀ (r + 1))
            * (2 * (m : ℝ) + 1) ^ (2 * i + 4) := by
          rw [Finset.sum_mul]

end Work.FTS.PhiStar.FlatWAux
