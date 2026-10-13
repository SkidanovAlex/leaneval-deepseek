import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulCore
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.FinalClock.HkIntegrandMulDthSmooth
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.ProdRadSup
import Submission.Work.Coercivity.HkIntegrand_endpoint_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.StrongPersist.L3Rhs.NfkAux

set_option maxHeartbeats 1600000

/-- The elementary comparison `(1 + √M)² ≤ 4(1 + M)` for `M ≥ 0`. -/
private theorem sq_one_add_sqrt_le' (M : ℝ) (hM : 0 ≤ M) :
    (1 + Real.sqrt M) ^ 2 ≤ 4 * (1 + M) := by
  nlinarith [Real.sq_sqrt hM, Real.sqrt_nonneg M, sq_nonneg (Real.sqrt M - 1 / 3)]

/-- A pointwise domination of the `ℋᵏ`-integrand on the closed quadrant, with the integrand of
`f` integrable, transfers to `HkSq` (both sides being iterated integrals). -/
private theorem hkSq_le_of_integrand_le' (α : ℝ) (k : ℕ) {f g : ℝ → ℝ → ℝ} (C : ℝ)
    (hmf : Work.Spaces.HkMem α k f)
    (hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k g z θ ≤ C * Work.Spaces.HkIntegrand α k f z θ) :
    Work.Spaces.HkSq α k g ≤ C * Work.Spaces.HkSq α k f := by
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
        ≤ C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) := by
    intro z hz
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α k f z θ :=
      MeasureTheory.integral_mono_of_nonneg
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (f := fun θ => Work.Spaces.HkIntegrand α k g z θ)
        (g := fun θ => C * Work.Spaces.HkIntegrand α k f z θ)
        (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
        ((hmf.1 z hz).const_mul C)
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc fun θ hθ => hpt z hz θ hθ)
    rwa [MeasureTheory.integral_const_mul] at h1
  rw [Work.Spaces.HkSq, Work.Spaces.HkSq]
  have h2 : (∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k g z θ)
      ≤ ∫ z in Work.Spaces.Iz, C * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f z θ) :=
    MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iz)
      (f := fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
      (g := fun z => C * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ))
      (Filter.Eventually.of_forall fun z =>
        MeasureTheory.integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α k g z θ)
      (hmf.2.const_mul C)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hinner z hz)
  rwa [MeasureTheory.integral_const_mul] at h2

/-- **Multiplication of an `ℋᵏ`-datum by a radial factor with bounded `D_z`-iterates**, with the
regularity hypotheses imposed only for the *angles* `θ ∈ (0,π/2)` that occur in the domain
`ℋᵏ`-norm.

For every order `k ≥ 1` there are constants `C > 0`, `Cpow ≥ 0` such that for every `α > 0`,
every `r : ℝ → ℝ` whose iterates `D_z^a r = (z∂_z)^a r`, `a ≤ k`, are bounded by `√M` on
`(0,∞)` (and `C^a` there), and every `h` with the finite-order regularity needed by the Leibniz
rules *on the open angle interval*,
```
      r·h ∈ ℋᵏ   and   |r·h|²_{ℋᵏ} ≤ C·α^{-Cpow}·(1+M)·|h|²_{ℋᵏ}.
```
The proof is the multiplier estimate of `Work.FTS.StrongPersist.L3Aux.zmul_pt`: on the open
quadrant the Leibniz rules `Work.FTS.FinalClock.DzIter_mul_of_contDiffOn` /
`mixed_mul_of_contDiffOn` expand `D_z^i(r·h)` and `D_z^jD_θ^i(r·h)` into the `Zop`-iterates of
`r` times the corresponding derivatives of `h`; the Cauchy–Schwarz step in `zmul_pt` then gives
the pointwise domination of the integrands.  The only angles at which these expansions are
needed are the interior angles `θ ∈ (0,π/2)`, which is exactly the (weaker) hypothesis of the
present version; the boundary angles of `Iθ = [0,π/2]` cost nothing because `sin(2θ) = 0`
there and both weights on the left vanish.  The line `z = 0` is trivial (both integrands vanish
there, `Work.FTS.LocData.HkIntegrand_zero_fst`), and the honesty of the product is transferred
from `h` by `Work.FTS.LocData.HkMem_of_majorant`, using the continuity of the integrand on the
open quadrant (`blocksCont_of_contDiffOn` + `continuousOn_HkIntegrand_of_blocksCont`). -/
theorem ProdRadSupO : ∀ k : ℕ, ∃ C Cpow : ℝ, 0 < C ∧ 0 ≤ Cpow ∧
    ∀ (α : ℝ) (r : ℝ → ℝ) (h : ℝ → ℝ → ℝ) (M : ℝ),
      0 < α → 0 ≤ M → 1 ≤ k →
      (∀ (a : ℕ), a ≤ k → ∀ z ∈ Set.Ioi (0 : ℝ), (Work.Elliptic.DzdIter a r z) ^ 2 ≤ M) →
      (∀ (a : ℕ), a ≤ k → ContDiffOn ℝ a r (Set.Ioi (0 : ℝ))) →
      (∀ (i : ℕ), i ≤ k → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        ContDiffOn ℝ i (fun z => h z θ) (Set.Ioi (0 : ℝ))) →
      (∀ (j i : ℕ), 1 ≤ i → i + j ≤ k → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
        ContDiffOn ℝ j (fun z => Work.Spaces.DthIter i h z θ) (Set.Ioi (0 : ℝ))) →
      ContDiffOn ℝ k (Function.uncurry h) Work.FTS.EllipticEst.Q0 →
      Work.Spaces.HkMem α k h →
      Work.Spaces.HkMem α k (fun z θ => r z * h z θ) ∧
      Work.Spaces.HkSq α k (fun z θ => r z * h z θ)
        ≤ C * α ^ (-Cpow) * (1 + M) * Work.Spaces.HkSq α k h := by
  intro k
  by_cases hk : 1 ≤ k
  · refine ⟨4 * Work.FTS.StrongPersist.L3Aux.zmulConst k, 0, ?_, le_refl 0, ?_⟩
    · have hpos := Work.FTS.StrongPersist.L3Aux.zmulConst_pos k
      linarith
    · intro α r h M hα hM hk1 hDz hra hri hrmi hsh hmem
      -- the bound on the `Zop`-iterates of the radial factor
      have hB : ∀ b ≤ k, ∀ z ∈ Set.Ioi (0 : ℝ), |Work.Spaces.Zop^[b] r z| ≤ Real.sqrt M := by
        intro b hb z hz
        rw [← Work.FTS.CoercivityFix.Transfer.E2pkg.DzdIter_eq_Zop_iter b r]
        calc |Work.Elliptic.DzdIter b r z|
            = Real.sqrt ((Work.Elliptic.DzdIter b r z) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ Real.sqrt M := Real.sqrt_le_sqrt (hDz b hb z hz)
      -- the pointwise bound at an interior angle (`z > 0`, `0 < θ < π/2`)
      have hpt_open : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
          Work.Spaces.HkIntegrand α k (fun z θ => r z * h z θ) z θ
            ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + Real.sqrt M) ^ 2)
                * Work.Spaces.HkIntegrand α k h z θ := by
        intro z hz θ hθ
        refine Work.FTS.StrongPersist.L3Aux.zmul_pt α k r h (Real.sqrt_nonneg M) ?_ ?_ ?_
        · intro b hb
          exact hB b hb z hz
        · intro i hik
          exact Work.FTS.FinalClock.DzIter_mul_of_contDiffOn i r h isOpen_Ioi
            (hra i hik) (hri i hik θ hθ) z hz
        · intro j i hi hij
          exact Work.FTS.FinalClock.mixed_mul_of_contDiffOn j i r h isOpen_Ioi
            (hra j (by omega)) (hrmi j i hi hij θ hθ) z hz
      -- the pointwise bound on the closed quadrant
      have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α k (fun z θ => r z * h z θ) z θ
            ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + Real.sqrt M) ^ 2)
                * Work.Spaces.HkIntegrand α k h z θ := by
        intro z hz θ hθ
        have hCnn : 0 ≤ Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + Real.sqrt M) ^ 2 :=
          mul_nonneg (Work.FTS.StrongPersist.L3Aux.zmulConst_pos k).le (sq_nonneg _)
        rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hzpos
        · subst h0
          rw [Work.FTS.LocData.HkIntegrand_zero_fst]
          exact mul_nonneg hCnn (Work.Spaces.HkIntegrand_nonneg α k h 0 θ)
        · by_cases hs : Real.sin (2 * θ) = 0
          · -- a boundary angle: the `𝒲`-weight kills the integrand
            rw [Work.Coercivity.HkIntegrand_eq_zero_of_sin_eq_zero α k
              (fun z θ => r z * h z θ) z θ hs]
            exact mul_nonneg hCnn (Work.Spaces.HkIntegrand_nonneg α k h z θ)
          · -- an interior angle: the hypotheses apply
            have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
              refine ⟨lt_of_le_of_ne hθ.1 (fun hc => hs (by rw [← hc]; simp)), ?_⟩
              refine lt_of_le_of_ne hθ.2 (fun hc => hs (by
                rw [hc, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]))
            exact hpt_open z hzpos θ hθ'
      -- smoothness of the product and continuity of its integrand on the open quadrant
      have hFsm : ContDiffOn ℝ k (Function.uncurry (fun z θ => r z * h z θ))
          Work.FTS.EllipticEst.Q0 := by
        have hfst : ContDiffOn ℝ k (fun p : ℝ × ℝ => r p.1) Work.FTS.EllipticEst.Q0 :=
          (hra k le_rfl).comp contDiffOn_fst
            (fun p hp => (Work.FTS.EllipticEst.mem_Q0.mp hp).1)
        exact hfst.mul hsh
      have hBc : Work.FTS.CoercivityFix.Assembly.BlocksCont k (fun z θ => r z * h z θ) :=
        Work.FTS.CoercivityFix.Transfer.E2pkg.blocksCont_of_contDiffOn hFsm
      have hcont : ContinuousOn
          (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k (fun z θ => r z * h z θ) p.1 p.2)
          (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
        Work.FTS.CoercivityFix.Transfer.E2pkg.continuousOn_HkIntegrand_of_blocksCont hBc α
      -- membership by domination
      have hmemProd : Work.Spaces.HkMem α k (fun z θ => r z * h z θ) := by
        refine Work.FTS.LocData.HkMem_of_majorant α k hcont ?_ ?_ hpt
        · intro z hz
          exact (hmem.1 z hz).const_mul _
        · have h2 := (hmem.2).const_mul
              (Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + Real.sqrt M) ^ 2)
          have heq : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
                (Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + Real.sqrt M) ^ 2)
                  * Work.Spaces.HkIntegrand α k h z θ)
              = fun z : ℝ =>
                  (Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + Real.sqrt M) ^ 2)
                    * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k h z θ := by
            funext z
            rw [MeasureTheory.integral_const_mul]
          rw [heq]
          exact h2
      refine ⟨hmemProd, ?_⟩
      have hsq := hkSq_le_of_integrand_le' α k
        (Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + Real.sqrt M) ^ 2) hmem hpt
      have harith : (1 + Real.sqrt M) ^ 2 ≤ 4 * (1 + M) := sq_one_add_sqrt_le' M hM
      have hcoef : Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + Real.sqrt M) ^ 2
          ≤ 4 * Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + M) := by
        calc Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + Real.sqrt M) ^ 2
            ≤ Work.FTS.StrongPersist.L3Aux.zmulConst k * (4 * (1 + M)) :=
              mul_le_mul_of_nonneg_left harith
                (Work.FTS.StrongPersist.L3Aux.zmulConst_pos k).le
          _ = 4 * Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + M) := by ring
      calc Work.Spaces.HkSq α k (fun z θ => r z * h z θ)
          ≤ (Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + Real.sqrt M) ^ 2)
              * Work.Spaces.HkSq α k h := hsq
        _ ≤ (4 * Work.FTS.StrongPersist.L3Aux.zmulConst k * (1 + M))
              * Work.Spaces.HkSq α k h :=
              mul_le_mul_of_nonneg_right hcoef (Work.Spaces.HkSq_nonneg α k h)
        _ = 4 * Work.FTS.StrongPersist.L3Aux.zmulConst k * α ^ (-(0 : ℝ)) * (1 + M)
              * Work.Spaces.HkSq α k h := by
              rw [neg_zero, Real.rpow_zero]
              ring
  · exact ⟨1, 0, one_pos, le_refl 0, fun α r h M hα hM hk1 => absurd hk1 hk⟩

end Work.FTS.StrongPersist.L3Rhs.NfkAux
