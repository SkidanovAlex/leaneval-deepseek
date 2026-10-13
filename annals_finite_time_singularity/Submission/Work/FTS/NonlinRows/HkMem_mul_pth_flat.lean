/-
# `ℋ⁴`-membership of `f · ∂_θ g` for a *flat* coefficient `f`

Let `f` be `C^∞` on the open quadrant `(0,∞) × (0,π/2)` and suppose that all its mixed
`D`-derivatives of total order `≤ 4` are bounded by `K · sin(2θ)` on the open quadrant
(`hflat`), and let `g` be a Galerkin-class datum (`Work.FTS.Nonlin.GalClass α g`, hence
`g ∈ ℋ⁶`, `SmoothQuad g`).  Then

`Work.Spaces.HkMem α 4 (fun z θ => f z θ * Work.Spaces.pth g z θ)`,

i.e. the product of the flat coefficient by the angular derivative of `g` is in the weighted
space `ℋ⁴`.

The point of the flatness hypothesis is that it supplies exactly one factor `sin(2θ)` per
`f`-derivative, which cancels the `1/sin(2θ)` hidden in `∂_θ = D_θ / sin(2θ)`; the resulting
slots are all summands of `HkIntegrand α 6 g`.

The proof is by the pointwise majorant `HkIntegrand α 4 (f·∂_θ g) ≤ C·K²·HkIntegrand α 6 g`
on the open quadrant (the boundary of the quadrant is harmless: the integrand carries the
weight `w z = 0` at `z = 0` and `sin(2θ)^(-·) = 0` at `θ = 0, π/2`), assembled from

* the pure `D_z`-slots (`pure_slot_mul_pth_le`),
* the mixed slots (`mixed_slot_mul_pth_le`), which consume
* the triangular estimate `sin(2θ)·D_z^cD_θ^r(∂_θ G)` is dominated by `Σ_{m≤r+1}|D_z^cD_θ^m G|`
  (`sin_mul_mixed_pth_le`),

and then the majorant criterion `Work.FTS.LocData.HkMem_of_majorant`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.H2.STFacts
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_Dz
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.TransportS.flat_mixed_le
import Submission.Work.FTS.NonlinRows.pure_slot_mul_pth_le
import Submission.Work.FTS.NonlinRows.mixed_slot_mul_pth_le
import Submission.Work.FTS.NonlinRows.sin_mul_mixed_pth_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Auxiliary facts -/

/-- `SmoothOpen` is preserved by `f ↦ f · ∂_θ g` (`Work.Spaces.pth g` is smooth on the open
quadrant whenever `g` is). -/
theorem smoothOpen_mul_pth {f g : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hg : Work.FTS.EllipticEst.SmoothOpen g) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * Work.Spaces.pth g z θ) := by
  show ContDiffOn ℝ Work.Stability.smoothOrder
    (Function.uncurry (fun z θ => f z θ * Work.Spaces.pth g z θ)) Work.FTS.EllipticEst.Q0
  have h1 : Function.uncurry (fun z θ => f z θ * Work.Spaces.pth g z θ)
      = Function.uncurry f * Function.uncurry (Work.Spaces.pth g) := rfl
  rw [h1]
  exact hf.mul hg.pth

/-- The `ℋ^k`-integrand vanishes at the angular endpoints `θ = 0, π/2` (every term carries a
weight `sin(2θ)^(-c)` with `c ≠ 0`). -/
theorem HkIntegrand_sin_two_eq_zero {α : ℝ} (hα : 0 < α) {k : ℕ} {F : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α k F z θ = 0 :=
  Work.Construction.HkIntegrand_eq_zero_of_sin_two_eq_zero hα h

/-! ## The target -/

theorem HkMem_mul_pth_flat {α : ℝ} {f g : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hf : Work.FTS.EllipticEst.SmoothOpen f)
    (hflat : ∃ K : ℝ, 0 < K ∧ ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
      ∀ b a : ℕ, a + b ≤ 4 → |Work.Spaces.mixed b a f z θ| ≤ K * Real.sin (2 * θ))
    (hg : Work.FTS.Nonlin.GalClass α g) :
    Work.Spaces.HkMem α 4 (fun z θ => f z θ * Work.Spaces.pth g z θ) := by
  classical
  obtain ⟨K, hKpos, hflatK⟩ := hflat
  have hgSO : Work.FTS.EllipticEst.SmoothOpen g :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hg.reg.1
  have hgmem : Work.Spaces.HkMem α 6 g := hg.reg.2.1
  have hhSO : Work.FTS.EllipticEst.SmoothOpen (fun z θ => f z θ * Work.Spaces.pth g z θ) :=
    smoothOpen_mul_pth hf hgSO
  obtain ⟨CB, hCBpos, hB⟩ := pure_slot_mul_pth_le
  obtain ⟨CM, hCMpos, hM⟩ := mixed_slot_mul_pth_le
  -- a single constant dominating all the angular shifts with `r ≤ 4`
  obtain ⟨C0, hC0pos, hC0⟩ := sin_mul_mixed_pth_le 0 (by norm_num)
  obtain ⟨C1, hC1pos, hC1⟩ := sin_mul_mixed_pth_le 1 (by norm_num)
  obtain ⟨C2, hC2pos, hC2⟩ := sin_mul_mixed_pth_le 2 (by norm_num)
  obtain ⟨C3, hC3pos, hC3⟩ := sin_mul_mixed_pth_le 3 (by norm_num)
  obtain ⟨C4, hC4pos, hC4⟩ := sin_mul_mixed_pth_le 4 (by norm_num)
  set Psi : ℝ := max (max (max C0 C1) (max C2 C3)) C4 with hPsid
  have hPsi0 : C0 ≤ Psi := by
    rw [hPsid]
    have h1 := le_max_left C0 C1
    have h2 := le_max_left (max C0 C1) (max C2 C3)
    have h3 := le_max_left (max (max C0 C1) (max C2 C3)) C4
    linarith
  have hPsi1 : C1 ≤ Psi := by
    rw [hPsid]
    have h1 := le_max_right C0 C1
    have h2 := le_max_left (max C0 C1) (max C2 C3)
    have h3 := le_max_left (max (max C0 C1) (max C2 C3)) C4
    linarith
  have hPsi2 : C2 ≤ Psi := by
    rw [hPsid]
    have h1 := le_max_left C2 C3
    have h2 := le_max_right (max C0 C1) (max C2 C3)
    have h3 := le_max_left (max (max C0 C1) (max C2 C3)) C4
    linarith
  have hPsi3 : C3 ≤ Psi := by
    rw [hPsid]
    have h1 := le_max_right C2 C3
    have h2 := le_max_right (max C0 C1) (max C2 C3)
    have h3 := le_max_left (max (max C0 C1) (max C2 C3)) C4
    linarith
  have hPsi4 : C4 ≤ Psi := by
    rw [hPsid]
    exact le_max_right _ _
  have hPsipos : 0 < Psi := lt_of_lt_of_le hC0pos hPsi0
  have hPsi : ∀ (c r : ℕ), r ≤ 4 → ∀ (z : ℝ) (θ : ℝ), 0 < z →
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |Real.sin (2 * θ) * Work.Spaces.mixed c r (Work.Spaces.pth g) z θ|
        ≤ Psi * ∑ m ∈ Finset.Icc 1 (r + 1), |Work.Spaces.mixed c m g z θ| := by
    intro c r hr z θ hz hθ
    have hsum : 0 ≤ ∑ m ∈ Finset.Icc 1 (r + 1), |Work.Spaces.mixed c m g z θ| :=
      Finset.sum_nonneg fun m _ => abs_nonneg _
    rcases (by omega : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4) with h | h | h | h | h <;>
      subst h
    · exact le_trans (hC0 g hgSO c z θ hz hθ) (mul_le_mul_of_nonneg_right hPsi0 hsum)
    · exact le_trans (hC1 g hgSO c z θ hz hθ) (mul_le_mul_of_nonneg_right hPsi1 hsum)
    · exact le_trans (hC2 g hgSO c z θ hz hθ) (mul_le_mul_of_nonneg_right hPsi2 hsum)
    · exact le_trans (hC3 g hgSO c z θ hz hθ) (mul_le_mul_of_nonneg_right hPsi3 hsum)
    · exact le_trans (hC4 g hgSO c z θ hz hθ) (mul_le_mul_of_nonneg_right hPsi4 hsum)
  -- the two families of slots
  set Ctot : ℝ := 5 * CB + 25 * CM * (max Psi 1) ^ 2 with hCtotd
  have hCtotpos : 0 < Ctot := by
    rw [hCtotd]
    have h1 := sq_nonneg (max Psi 1)
    nlinarith [hCBpos, hCMpos, hPsipos]
  have hkey : ∀ (z θ : ℝ), 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.HkIntegrand α 4 (fun z θ => f z θ * Work.Spaces.pth g z θ) z θ
        ≤ Ctot * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ := by
    intro z θ hz hθ
    have hHknn : 0 ≤ Work.Spaces.HkIntegrand α 6 g z θ :=
      Work.Spaces.HkIntegrand_nonneg α 6 g z θ
    have hbnd : 0 ≤ CM * (max Psi 1) ^ 2 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ :=
      mul_nonneg (mul_nonneg (mul_nonneg hCMpos.le (sq_nonneg _)) (sq_nonneg K)) hHknn
    have hZ : (∑ i ∈ Finset.range (4 + 1),
          (Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.pth g z θ) z θ
            * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
        ≤ 5 * (CB * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
      calc (∑ i ∈ Finset.range (4 + 1),
            (Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.pth g z θ) z θ
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
          ≤ ∑ _i ∈ Finset.range (4 + 1),
              (CB * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
            refine Finset.sum_le_sum fun i hi => ?_
            exact hB α hα f g hf hgSO K hKpos hflatK i
              (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) z θ hz hθ
        _ = 5 * (CB * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            norm_num
    have hX : (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
          (if 1 ≤ i ∧ i + j ≤ 4 then
            (Work.Spaces.mixed j i (fun z θ => f z θ * Work.Spaces.pth g z θ) z θ
              * Work.Spaces.Wt α z θ) ^ 2 else 0))
        ≤ 25 * (CM * (max Psi 1) ^ 2 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
      calc (∑ i ∈ Finset.range (4 + 1), ∑ j ∈ Finset.range (4 + 1),
            (if 1 ≤ i ∧ i + j ≤ 4 then
              (Work.Spaces.mixed j i (fun z θ => f z θ * Work.Spaces.pth g z θ) z θ
                * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _i ∈ Finset.range (4 + 1), ∑ _j ∈ Finset.range (4 + 1),
              (CM * (max Psi 1) ^ 2 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
            refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
            by_cases hc : 1 ≤ i ∧ i + j ≤ 4
            · rw [if_pos hc]
              exact hM α hα f g hf hgSO K hKpos hflatK Psi hPsipos hPsi j i hc.1 hc.2
                z θ hz hθ
            · rw [if_neg hc]
              exact hbnd
        _ = 25 * (CM * (max Psi 1) ^ 2 * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_const,
              Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    rw [Work.Spaces.HkIntegrand]
    refine le_trans (add_le_add hZ hX) (le_of_eq ?_)
    rw [hCtotd]
    ring
  refine Work.FTS.LocData.HkMem_of_majorant α 4
    (f := fun z θ => f z θ * Work.Spaces.pth g z θ)
    (M := fun z θ => Ctot * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ)
    (hhSO.continuousOn_HkIntegrand α 4) ?_ ?_ ?_
  · intro z hz
    exact (hgmem.1 z hz).const_mul (Ctot * K ^ 2)
  · have h := hgmem.2.const_mul (Ctot * K ^ 2)
    have hfun : (fun z => ∫ θ in Work.Spaces.Iθ,
          Ctot * K ^ 2 * Work.Spaces.HkIntegrand α 6 g z θ)
        = fun z => Ctot * K ^ 2 * ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 6 g z θ := by
      funext z
      rw [MeasureTheory.integral_const_mul]
    rw [hfun]
    exact h
  · intro z hz θ hθ
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      rw [Work.Spaces.HkIntegrand_zero_z]
      exact mul_nonneg (mul_nonneg hCtotpos.le (sq_nonneg K))
        (Work.Spaces.HkIntegrand_nonneg α 6 g 0 θ)
    · by_cases hθi : θ ∈ Set.Ioo 0 (Real.pi / 2)
      · exact hkey z θ hzpos hθi
      · rw [HkIntegrand_sin_two_eq_zero hα (Work.Spaces.sin_two_eq_zero_of_not_Ioo hθ hθi)]
        exact mul_nonneg (mul_nonneg hCtotpos.le (sq_nonneg K))
          (Work.Spaces.HkIntegrand_nonneg α 6 g z θ)

end Work.FTS.NonlinRows
