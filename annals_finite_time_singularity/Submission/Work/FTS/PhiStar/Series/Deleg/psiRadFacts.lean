import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.PhiStar.LinvFlatAux.linv_abs_le_four
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_contDiffOn
import Submission.Work.FTS.PhiStar.RadialWAux.radPsi_iteratedDeriv
import Submission.Work.FTS.PhiStar.Series.DecayRem
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.fstarDat
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6
import Submission.Work.FTS.StrongPersist.Star6
import Submission.Work.FTS.StrongPersist.Vocab
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.PkgJets.cosTailB
import Submission.Work.FTS_RegExport.RXT.Slots.v2_L12DzIterTendsto
import Submission.Work.FTS_RegExport.RXT.Sys.hasDerivAt_mixed_z
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.FstarDzIterFourPsiAe
import Submission.Work.H2W.fstarDzIterFourAe
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.PhiStar.AngU.Wt_differentiableOn =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AngU.Wt_differentiableOn` — differentiability of the resummed angular profile `Wt`

`Wt ψ j = Σ_m b_m λ_m^{-j} Q_m` (`j ≥ 1`) is the resummed angular profile of the
`FlatW_psiSeries` route.  Its termwise-differentiation identity is proved in
`FlatWAux/WtDerivTsum.lean` (and consumed in `FlatWAux/AngDeriv.lean`), but that identity is
stated as an equality of `deriv`-*values*: `deriv f θ = c` does not by itself imply that `f` is
differentiable at `θ` (Mathlib's `deriv` is `0` at a point of non-differentiability), so it
cannot be fed into the `ContDiffOn` bootstrap of `FlatWAux/AngBoundU.lean`.

This file therefore replays the *same* termwise differentiation
(`hasDerivAt_tsum_of_isPreconnected`, the per-mode derivative `deriv Q_m = Linv (λ_m e_m)` of
`FamDerivDivLinv` and the summable majorant `(2m+1)/(λ_m √(2m+1))`), with a `DifferentiableAt`
conclusion — `FlatWAux.Wt_differentiableAt` — and deduces the requested
`AngU.Wt_differentiableOn` from it.
-/

noncomputable section
open scoped Real Topology BigOperators

namespace Work.FTS.PhiStar.FlatWAux

set_option maxHeartbeats 1000000

/-- Pointwise differentiability of the resummed angular profile `Wt ψ j` for `j ≥ 1`: the
series `Σ_m b_m λ_m^{-j} Q_m` may be differentiated termwise on `(0, π/2)`.  (The statement of
`WtDerivTsum` records only the resulting *value* of `deriv`, which is formally weaker.) -/
theorem Wt_differentiableAt (ψ : ℝ → ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1))
    (hQ0 : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 1 ≤ m → ∀ θ : ℝ,
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |Work.FTS.PhiStar.FlatWAux.Qm m θ| ≤ C * (2 * (m : ℝ) + 1) ^ 2)
    (hL : ∃ K : ℝ, 0 < K ∧ ∀ (m : ℕ) (y : ℝ), y ∈ Set.Ioo 0 (Real.pi / 2) →
      |Work.FTS.PhiStar.Linv
        (fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') y|
        ≤ K * (Work.FTS.PhiStar.Gegenbauer.lam m * (2 * (m : ℝ) + 1))) :
    ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      DifferentiableAt ℝ (Work.FTS.PhiStar.FlatWAux.Wt ψ j) θ := by
  obtain ⟨C, hC, hdec⟩ := hdec
  obtain ⟨Cg, hCg, hgr⟩ := hgr
  obtain ⟨K, hK, hL⟩ := hL
  intro θ hθ
  obtain ⟨j', hj'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hj'' : j = j' + 1 := hj'
  rw [hj'']
  -- the summable majorant of the differentiated series
  have hu : Summable (fun m : ℕ => C * K * ((2 * (m : ℝ) + 1)
      / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))) :=
    summable_lam_sqrt_aux.mul_left (C * K)
  -- the `m`-th summand and its derivative
  have hQdiff : ∀ (m : ℕ) (y : ℝ), y ∈ Set.Ioo 0 (Real.pi / 2) →
      HasDerivAt (Qm m)
        (Work.FTS.PhiStar.Linv (fun θ' => Gegenbauer.lam m * Gegenbauer.eFam m θ') y) y := by
    intro m y hy
    have h1 : HasDerivAt (fun z : ℝ => Gegenbauer.eFam m z) (deriv (Gegenbauer.eFam m) y) y :=
      (((contDiff_eFam_fam m).differentiable (by norm_num)).differentiableAt).hasDerivAt
    have h2 : HasDerivAt Work.Construction.s2 (deriv Work.Construction.s2 y) y :=
      (differentiable_s2_fam.differentiableAt).hasDerivAt
    have h3 := h1.div h2 (linv_s2_ne_zero hy)
    have h4 : deriv (fun z : ℝ => Gegenbauer.eFam m z / Work.Construction.s2 z) y
        = (deriv (Gegenbauer.eFam m) y * Work.Construction.s2 y
            - Gegenbauer.eFam m y * deriv Work.Construction.s2 y)
              / Work.Construction.s2 y ^ 2 := h3.deriv
    refine h3.congr_deriv ?_
    rw [← h4]
    exact FamDerivDivLinv m hy
  have hderiv : ∀ (m : ℕ) (y : ℝ), y ∈ Set.Ioo 0 (Real.pi / 2) →
      HasDerivAt (fun z => Work.FTS.PhiStar.Series.bmode m ψ
          * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * Qm m z)
        (Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
          * Work.FTS.PhiStar.Linv (fun θ' => Gegenbauer.lam m * Gegenbauer.eFam m θ') y) y :=
    fun m y hy => (hQdiff m y hy).const_mul _
  -- the uniform bound on the derivatives
  have hbdd : ∀ (m : ℕ) (y : ℝ), y ∈ Set.Ioo 0 (Real.pi / 2) →
      ‖Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
        * Work.FTS.PhiStar.Linv (fun θ' => Gegenbauer.lam m * Gegenbauer.eFam m θ') y‖
      ≤ C * K * ((2 * (m : ℝ) + 1)
          / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
    intro m y hy
    rw [Real.norm_eq_abs]
    by_cases hm : m = 0
    · subst hm
      have hz : ((Gegenbauer.lam 0)⁻¹) ^ (j' + 1) = 0 := by
        rw [show Gegenbauer.lam 0 = 0 by norm_num [Gegenbauer.lam], inv_zero]
        exact zero_pow (Nat.succ_ne_zero j')
      have hzero : Work.FTS.PhiStar.Series.bmode 0 ψ * ((Gegenbauer.lam 0)⁻¹) ^ (j' + 1)
          * Work.FTS.PhiStar.Linv (fun θ' => Gegenbauer.lam 0 * Gegenbauer.eFam 0 θ') y = 0 := by
        rw [hz, mul_zero, zero_mul]
      rw [hzero, abs_zero]
      have hl0 : (0 : ℝ) ≤ Gegenbauer.lam 0 := by norm_num [Gegenbauer.lam]
      exact mul_nonneg (mul_nonneg hC.le hK.le)
        (div_nonneg (by norm_num) (mul_nonneg hl0 (Real.sqrt_nonneg _)))
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hlam_pos : 0 < Gegenbauer.lam m := by
        simp only [Gegenbauer.lam]; nlinarith
      have hlam1 : (1 : ℝ) ≤ Gegenbauer.lam m := by
        simp only [Gegenbauer.lam]; nlinarith
      have hinvnn : (0 : ℝ) ≤ (Gegenbauer.lam m)⁻¹ := inv_nonneg.mpr hlam_pos.le
      have hpownn : (0 : ℝ) ≤ ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) := pow_nonneg hinvnn _
      -- `(λ_m⁻¹)^{j'+1}·λ_m ≤ 1`
      have hcancel : ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * Gegenbauer.lam m ≤ 1 := by
        calc ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * Gegenbauer.lam m
            = ((Gegenbauer.lam m)⁻¹) ^ j' * (Gegenbauer.lam m)⁻¹ * Gegenbauer.lam m := by
              rw [pow_succ]
          _ = ((Gegenbauer.lam m)⁻¹) ^ j' := by
              rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hlam_pos), mul_one]
          _ ≤ 1 := pow_le_one₀ hinvnn ((inv_le_one₀ hlam_pos).mpr hlam1)
      have hK21 : (0 : ℝ) ≤ K * (2 * (m : ℝ) + 1) := by positivity
      rw [abs_mul, abs_mul, abs_of_nonneg hpownn]
      calc |Work.FTS.PhiStar.Series.bmode m ψ| * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
            * |Work.FTS.PhiStar.Linv
                (fun θ' => Gegenbauer.lam m * Gegenbauer.eFam m θ') y|
          ≤ |Work.FTS.PhiStar.Series.bmode m ψ| * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
              * (K * (Gegenbauer.lam m * (2 * (m : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left (hL m y hy) (mul_nonneg (abs_nonneg _) hpownn)
        _ = |Work.FTS.PhiStar.Series.bmode m ψ| * ((((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
              * Gegenbauer.lam m) * (K * (2 * (m : ℝ) + 1))) := by ring
        _ ≤ |Work.FTS.PhiStar.Series.bmode m ψ| * (1 * (K * (2 * (m : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcancel hK21) (abs_nonneg _)
        _ ≤ (C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
              * (K * (2 * (m : ℝ) + 1)) := by
            calc |Work.FTS.PhiStar.Series.bmode m ψ| * (1 * (K * (2 * (m : ℝ) + 1)))
                = |Work.FTS.PhiStar.Series.bmode m ψ| * (K * (2 * (m : ℝ) + 1)) := by ring
              _ ≤ (C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
                    * (K * (2 * (m : ℝ) + 1)) :=
                  mul_le_mul_of_nonneg_right (hdec m hm1) hK21
        _ = C * K * ((2 * (m : ℝ) + 1)
              / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by ring
  -- summability of the series at the base point `π/4`
  have hsum0 : Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ
      * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * Qm m (Real.pi / 4)) := by
    refine Summable.of_norm_bounded (hu.mul_left (Cg / K)) (fun m => ?_)
    rw [Real.norm_eq_abs]
    by_cases hm : m = 0
    · subst hm
      have hz : ((Gegenbauer.lam 0)⁻¹) ^ (j' + 1) = 0 := by
        rw [show Gegenbauer.lam 0 = 0 by norm_num [Gegenbauer.lam], inv_zero]
        exact zero_pow (Nat.succ_ne_zero j')
      have hzero : Work.FTS.PhiStar.Series.bmode 0 ψ * ((Gegenbauer.lam 0)⁻¹) ^ (j' + 1)
          * Qm 0 (Real.pi / 4) = 0 := by
        rw [hz, mul_zero, zero_mul]
      rw [hzero, abs_zero]
      have hl0 : (0 : ℝ) ≤ Gegenbauer.lam 0 := by norm_num [Gegenbauer.lam]
      exact mul_nonneg (div_nonneg hCg.le hK.le)
        (mul_nonneg (mul_nonneg hC.le hK.le)
          (div_nonneg (by norm_num) (mul_nonneg hl0 (Real.sqrt_nonneg _))))
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hlam_pos : 0 < Gegenbauer.lam m := by
        simp only [Gegenbauer.lam]; nlinarith
      have hlam1 : (1 : ℝ) ≤ Gegenbauer.lam m := by
        simp only [Gegenbauer.lam]; nlinarith
      have hinvnn : (0 : ℝ) ≤ (Gegenbauer.lam m)⁻¹ := inv_nonneg.mpr hlam_pos.le
      have hpownn : (0 : ℝ) ≤ ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) := pow_nonneg hinvnn _
      have hpow1 : ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) ≤ 1 :=
        pow_le_one₀ hinvnn ((inv_le_one₀ hlam_pos).mpr hlam1)
      have hQ : Qm m (Real.pi / 4) = Gegenbauer.eFam m (Real.pi / 4) := by
        have hs : Work.Construction.s2 (Real.pi / 4) = 1 := by
          rw [Work.Construction.s2_eq, show 2 * (Real.pi / 4) = Real.pi / 2 by ring,
            Real.sin_pi_div_two]
        simp only [Qm, hs, div_one]
      have he : |Gegenbauer.eFam m (Real.pi / 4)| ≤ Cg * (2 * (m : ℝ) + 1) :=
        hgr m (Real.pi / 4) (by constructor <;> linarith [Real.pi_pos])
      rw [abs_mul, abs_mul, abs_of_nonneg hpownn, hQ]
      calc |Work.FTS.PhiStar.Series.bmode m ψ| * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
            * |Gegenbauer.eFam m (Real.pi / 4)|
          = (|Work.FTS.PhiStar.Series.bmode m ψ| * |Gegenbauer.eFam m (Real.pi / 4)|)
              * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) := by ring
        _ ≤ (C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
              * (Cg * (2 * (m : ℝ) + 1))) * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul (hdec m hm1) he (abs_nonneg _) (by positivity)) hpownn
        _ = C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
              * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * (Cg * (2 * (m : ℝ) + 1)) := by ring
        _ ≤ C / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) * 1
              * (Cg * (2 * (m : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow1 (by positivity))
              (by positivity)
        _ = C * Cg * ((2 * (m : ℝ) + 1)
              / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by ring
        _ = (Cg / K) * (C * K * ((2 * (m : ℝ) + 1)
              / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))) := by
            have hnum : Cg * (C * K * ((2 * (m : ℝ) + 1)
                / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))))
                = (C * Cg * ((2 * (m : ℝ) + 1)
                    / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))) * K := by ring
            rw [div_mul_eq_mul_div, hnum, mul_div_cancel_right₀ _ (ne_of_gt hK)]
  have hmain : HasDerivAt
      (fun z : ℝ => ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * Qm m z)
      (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
        * Work.FTS.PhiStar.Linv (fun θ' => Gegenbauer.lam m * Gegenbauer.eFam m θ') θ) θ :=
    hasDerivAt_tsum_of_isPreconnected
      (u := fun m : ℕ => C * K * ((2 * (m : ℝ) + 1)
        / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))))
      (g := fun m z => Work.FTS.PhiStar.Series.bmode m ψ
        * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1) * Qm m z)
      (g' := fun m z => Work.FTS.PhiStar.Series.bmode m ψ
        * ((Gegenbauer.lam m)⁻¹) ^ (j' + 1)
        * Work.FTS.PhiStar.Linv (fun θ' => Gegenbauer.lam m * Gegenbauer.eFam m θ') z)
      hu isOpen_Ioo isPreconnected_Ioo hderiv hbdd
      (show Real.pi / 4 ∈ Set.Ioo 0 (Real.pi / 2) from
        ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩) hsum0 hθ
  simpa only [Wt] using hmain.differentiableAt

end Work.FTS.PhiStar.FlatWAux

namespace Work.FTS.PhiStar.AngU

theorem Wt_differentiableOn (ψ : ℝ → ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1))
    (hQ0 : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 1 ≤ m → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |Work.FTS.PhiStar.FlatWAux.Qm m θ| ≤ C * (2 * (m : ℝ) + 1) ^ 2)
    (hL : ∃ K : ℝ, 0 < K ∧ ∀ (m : ℕ) (y : ℝ), y ∈ Set.Ioo 0 (Real.pi / 2) →
      |Work.FTS.PhiStar.Linv
        (fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m * Work.FTS.PhiStar.Gegenbauer.eFam m θ') y|
        ≤ K * (Work.FTS.PhiStar.Gegenbauer.lam m * (2 * (m : ℝ) + 1))) :
    DifferentiableOn ℝ (Work.FTS.PhiStar.FlatWAux.Wt ψ j) (Set.Ioo 0 (Real.pi / 2)) := by
  intro θ hθ
  exact (Work.FTS.PhiStar.FlatWAux.Wt_differentiableAt ψ j hj hdec hgr hQ0 hL θ
    hθ).differentiableWithinAt

end Work.FTS.PhiStar.AngU
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.AngDeriv =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

set_option maxHeartbeats 800000

/-! ## Elementary facts about the eigenvalue `lam m` -/

lemma lam_nonneg (m : ℕ) : 0 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]
  positivity

lemma lam_pos {m : ℕ} (hm : 1 ≤ m) : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  simp only [Work.FTS.PhiStar.Gegenbauer.lam]
  positivity

/-! ## `Linv` of a constant multiple, and congruence on `(0, θ]` -/

/-- `Linv` is linear in its argument: `Linv (k · F) θ = k · Linv F θ`. -/
lemma Linv_const_mul (k : ℝ) (F : ℝ → ℝ) (θ : ℝ) :
    Work.FTS.PhiStar.Linv (fun t : ℝ => k * F t) θ = k * Work.FTS.PhiStar.Linv F θ := by
  have hpt : ∀ t : ℝ,
      Real.sin t ^ 2 * Real.cos t ^ 3 * (k * F t) / Work.Construction.s2 t
        = k * (Real.sin t ^ 2 * Real.cos t ^ 3 * F t / Work.Construction.s2 t) :=
    fun t => by ring
  simp only [Work.FTS.PhiStar.Linv]
  rw [intervalIntegral.integral_congr (fun t _ => hpt t),
    intervalIntegral.integral_const_mul]
  ring

/-- `Linv F θ` depends only on the values of `F` on `(0, θ]`. -/
lemma Linv_congr_Ioc {F G : ℝ → ℝ} {θ : ℝ} (hθ : 0 < θ)
    (h : ∀ t ∈ Set.Ioc 0 θ, F t = G t) :
    Work.FTS.PhiStar.Linv F θ = Work.FTS.PhiStar.Linv G θ := by
  simp only [Work.FTS.PhiStar.Linv, neg_inj]
  congr 1
  rw [intervalIntegral.integral_of_le hθ.le, intervalIntegral.integral_of_le hθ.le]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => by rw [h t ht])

/-! ## `chia ψ (j-1)` as a series on `(0, θ]` -/

/-- On `(0, θ] ⊂ (0, π/2)` the `sin 2θ`-multiple `chia ψ (j-1)` is the resummed series
`Σ_m b_m λ_m^{-(j-1)} e_m`.  For `j = 1` this is the expansion hypothesis; for `j ≥ 2` it is
`chia_eq_tsum` together with `s2 · Q_m = e_m`. -/
lemma chia_eq_tsum_Ioc {ψ : ℝ → ℝ}
    (hexp : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ)
    {j : ℕ} (hj : 1 ≤ j) {θ t : ℝ} (ht : t ∈ Set.Ioc 0 θ) (hθ2 : θ < Real.pi / 2) :
    chia ψ (j - 1) t
      = ∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1)
          * Work.FTS.PhiStar.Gegenbauer.eFam m t := by
  have htIoo : t ∈ Set.Ioo 0 (Real.pi / 2) := ⟨ht.1, lt_of_le_of_lt ht.2 hθ2⟩
  have hs2 : Work.Construction.s2 t ≠ 0 := by
    rw [Work.Construction.s2_eq, Real.sin_two_mul]
    exact mul_ne_zero
      (mul_ne_zero two_ne_zero
        (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi htIoo.1
          (by linarith [Real.pi_pos, htIoo.2]))))
      (ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, htIoo.1], htIoo.2⟩))
  rcases eq_or_lt_of_le hj with hj1 | hj2
  · subst hj1
    rw [Nat.sub_self, chia_zero hs2, ← hexp t htIoo]
    exact tsum_congr (fun m => by rw [pow_zero, mul_one])
  · rw [show j - 1 = (j - 2) + 1 by omega, chia_eq_tsum ψ (j - 2) htIoo]

/-! ## The per-mode rewrite replacing `λ_m^{-j} Linv (λ_m e_m)` by `λ_m^{-(j-1)} Linv e_m` -/

/-- Termwise: `b_m λ_m^{-j} Linv (λ_m e_m) = (b_m λ_m^{-(j-1)}) Linv (e_m)`.  The `m = 0` term
vanishes on both sides: `λ_0 = 0` kills the left-hand side and `b_0 = 0` (the moment condition)
the right-hand side. -/
lemma Wt_tsum_deriv_rewrite {ψ : ℝ → ℝ}
    (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0) {j : ℕ} (hj : 1 ≤ j) (θ : ℝ) :
    (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ j
        * Work.FTS.PhiStar.Linv
            (fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ)
      = ∑' m : ℕ, (Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1))
          * Work.FTS.PhiStar.Linv
              (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m t) θ := by
  refine tsum_congr (fun m => ?_)
  by_cases hm : m = 0
  · subst hm
    rw [hb0]
    ring
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hlam : Work.FTS.PhiStar.Gegenbauer.lam m ≠ 0 := ne_of_gt (lam_pos hm1)
    rw [Linv_const_mul]
    set L : ℝ := Work.FTS.PhiStar.Linv
      (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m t) θ with hL
    have hp : (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ ^ j
          * Work.FTS.PhiStar.Gegenbauer.lam m
        = (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ ^ (j - 1) := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show j ≠ 0 by omega)
      rw [show k + 1 - 1 = k by omega, pow_succ, mul_assoc, inv_mul_cancel₀ hlam, mul_one]
    calc Work.FTS.PhiStar.Series.bmode m ψ
            * (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ ^ j
            * (Work.FTS.PhiStar.Gegenbauer.lam m * L)
        = Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ ^ j
              * Work.FTS.PhiStar.Gegenbauer.lam m) * L := by ring
      _ = Work.FTS.PhiStar.Series.bmode m ψ
            * (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ ^ (j - 1) * L := by rw [hp]

/-! ## The decay of the resummed coefficients -/

/-- `1/(λ_m √(2m+1)) ≤ (m+1)^{-5/2}` for `m ≥ 1`. -/
lemma one_div_lam_sqrt_le (m : ℕ) (hm : 1 ≤ m) :
    1 / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
      ≤ ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
  have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < (m : ℝ) := by linarith
  have hx : (0 : ℝ) < (m : ℝ) + 1 := by linarith
  have hpow : ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))
      = 1 / (((m : ℝ) + 1) ^ 2 * Real.sqrt ((m : ℝ) + 1)) := by
    have h5 : ((m : ℝ) + 1) ^ (5 / 2 : ℝ)
        = ((m : ℝ) + 1) ^ 2 * Real.sqrt ((m : ℝ) + 1) := by
      rw [show (5 : ℝ) / 2 = 2 + 1 / 2 by norm_num, Real.rpow_add hx, Real.rpow_two,
        ← Real.sqrt_eq_rpow]
    rw [Real.rpow_neg (le_of_lt hx) (5 / 2), h5, ← one_div]
  rw [hpow]
  refine one_div_le_one_div_of_le (by positivity) ?_
  have h1 : ((m : ℝ) + 1) ^ 2 ≤ 4 * (m : ℝ) ^ 2 := by nlinarith
  have h2 : Real.sqrt ((m : ℝ) + 1) ≤ Real.sqrt (2 * (m : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by linarith)
  have h3 : 4 * (m : ℝ) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
    simp only [Work.FTS.PhiStar.Gegenbauer.lam]
    nlinarith
  calc ((m : ℝ) + 1) ^ 2 * Real.sqrt ((m : ℝ) + 1)
      ≤ (4 * (m : ℝ) ^ 2) * Real.sqrt (2 * (m : ℝ) + 1) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
    _ ≤ Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)

/-- The resummed coefficients `b_m λ_m^{-(j-1)}` decay like `(m+1)^{-5/2}`. -/
lemma bmode_mul_pow_decay {ψ : ℝ → ℝ} {Cb : ℝ} (hCb : 0 < Cb)
    (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0)
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ Cb / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (j : ℕ) (hj : 1 ≤ j) :
    ∀ m : ℕ, |Work.FTS.PhiStar.Series.bmode m ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1)|
      ≤ Cb * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
  intro m
  by_cases hm : m = 0
  · subst hm
    rw [hb0, zero_mul, abs_zero,
      show (((0 : ℕ) : ℝ) + 1) ^ (-(5 / 2 : ℝ)) = 1 by
        rw [show (((0 : ℕ) : ℝ) + 1) = 1 by norm_num, Real.one_rpow],
      mul_one]
    exact hCb.le
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hlam1 : 1 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
      have hmR : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      simp only [Work.FTS.PhiStar.Gegenbauer.lam]
      nlinarith
    have hinvnn : 0 ≤ (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ :=
      inv_nonneg.mpr (by linarith)
    have hinv1 : (Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by linarith)]; linarith
    have hden : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) :=
      mul_pos (by linarith) (Real.sqrt_pos.mpr (by positivity))
    have habs : |((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1)| ≤ 1 := by
      rw [abs_of_nonneg (pow_nonneg hinvnn _)]
      calc ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1) ≤ 1 ^ (j - 1) :=
            pow_le_pow_left₀ hinvnn hinv1 _
        _ = 1 := one_pow _
    rw [abs_mul]
    calc |Work.FTS.PhiStar.Series.bmode m ψ|
            * |((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1)|
        ≤ (Cb / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) * 1 :=
          mul_le_mul (hdec m hm1) habs (abs_nonneg _) (le_of_lt (div_pos hCb hden))
      _ = Cb * (1 / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) := by
          ring
      _ ≤ Cb * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left (one_div_lam_sqrt_le m hm1) hCb.le

/-! ## The `Linv`-bound hypothesis for the termwise differentiation -/

/-- With `|e_m| ≤ Ce (2m+1)` and the vanishing moment of `λ_m e_m` (`MomentLamEFam`), the
zero-moment inverse is bounded by `4 Ce λ_m (2m+1)` uniformly on `(0, π/2)`
(`linv_abs_le_four`). -/
lemma exists_linv_lam_eFam_bound
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1)) :
    ∃ K : ℝ, 0 < K ∧ ∀ (m : ℕ) (y : ℝ), y ∈ Set.Ioo 0 (Real.pi / 2) →
      |Work.FTS.PhiStar.Linv
        (fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ') y|
        ≤ K * (Work.FTS.PhiStar.Gegenbauer.lam m * (2 * (m : ℝ) + 1)) := by
  obtain ⟨Ce, hCe, hgr⟩ := hgr
  refine ⟨4 * Ce, by positivity, fun m y hy => ?_⟩
  obtain ⟨hmom, hint⟩ := MomentLamEFam m
  have hlam : 0 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := lam_nonneg m
  have hK : 0 ≤ Work.FTS.PhiStar.Gegenbauer.lam m * (Ce * (2 * (m : ℝ) + 1)) :=
    mul_nonneg hlam (by positivity)
  have hbdd : ∀ t : ℝ, t ∈ Set.Ioo 0 (Real.pi / 2) →
      |(fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ') t|
        ≤ Work.FTS.PhiStar.Gegenbauer.lam m * (Ce * (2 * (m : ℝ) + 1)) := by
    intro t ht
    rw [abs_mul, abs_of_nonneg hlam]
    exact mul_le_mul_of_nonneg_left
      (hgr m t ⟨le_of_lt ht.1, le_of_lt ht.2⟩) hlam
  have h := Work.FTS.PhiStar.LinvFlatAux.linv_abs_le_four hK hbdd hint hmom y hy
  calc |Work.FTS.PhiStar.Linv
        (fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ') y|
      ≤ 4 * (Work.FTS.PhiStar.Gegenbauer.lam m * (Ce * (2 * (m : ℝ) + 1))) := h
    _ = (4 * Ce) * (Work.FTS.PhiStar.Gegenbauer.lam m * (2 * (m : ℝ) + 1)) := by ring

/-! ## The target -/

theorem AngDeriv (ψ : ℝ → ℝ) (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * (2 * (m : ℝ) + 1))
    (hQ : ∃ C : ℕ → ℝ, (∀ l : ℕ, 0 ≤ C l) ∧
      ∀ (m : ℕ), 1 ≤ m → ∀ (l : ℕ), l ≤ 8 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |iteratedDeriv l (Work.FTS.PhiStar.FlatWAux.Qm m) θ|
          ≤ C l * (2 * (m : ℝ) + 1) ^ (2 * l + 2))
    (hcont : ContinuousOn ψ (Set.Ioo 0 (Real.pi / 2)))
    (hbdd : ∃ M : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |ψ θ| ≤ M)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0)
    (hexp : ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ) :
    ∀ j : ℕ, 1 ≤ j → j ≤ Work.FTS.PhiStar.FlatWAux.J →
      ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      deriv (Work.FTS.PhiStar.FlatWAux.Wt ψ j) θ
        = Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ (j - 1)) θ := by
  obtain ⟨Cb, hCbpos, hdec'⟩ := hdec
  obtain ⟨Ce, hCepos, hgr'⟩ := hgr
  obtain ⟨CQ, hCQnn, hQ'⟩ := hQ
  have hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0 :=
    Work.FTS.PhiStar.Series.bmode_zero ψ hmom
  have hQ0 : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 1 ≤ m → ∀ θ : ℝ,
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
        |Work.FTS.PhiStar.FlatWAux.Qm m θ| ≤ C * (2 * (m : ℝ) + 1) ^ 2 := by
    refine ⟨CQ 0 + 1, by linarith [hCQnn 0], fun m hm θ hθ => ?_⟩
    have h := hQ' m hm 0 (by norm_num) θ hθ
    rw [iteratedDeriv_zero,
      show (2 * (m : ℝ) + 1) ^ (2 * 0 + 2) = (2 * (m : ℝ) + 1) ^ 2 by norm_num] at h
    calc |Work.FTS.PhiStar.FlatWAux.Qm m θ| ≤ CQ 0 * (2 * (m : ℝ) + 1) ^ 2 := h
      _ ≤ (CQ 0 + 1) * (2 * (m : ℝ) + 1) ^ 2 := by
          have h0 : (0 : ℝ) ≤ (2 * (m : ℝ) + 1) ^ 2 := sq_nonneg _
          nlinarith
  obtain ⟨K, hKpos, hK⟩ := exists_linv_lam_eFam_bound ⟨Ce, hCepos, hgr'⟩
  intro j hj hjJ θ hθ
  have hcoef : ∀ m : ℕ, |Work.FTS.PhiStar.Series.bmode m ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1)|
      ≤ Cb * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) :=
    bmode_mul_pow_decay hCbpos hb0 hdec' j hj
  have hstep1 : deriv (Work.FTS.PhiStar.FlatWAux.Wt ψ j) θ
      = (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ j
          * Work.FTS.PhiStar.Linv
              (fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ) :=
    Work.FTS.PhiStar.FlatWAux.WtDerivTsum ψ j hj ⟨Cb, hCbpos, hdec'⟩
      ⟨Ce, hCepos, hgr'⟩ hQ0 ⟨K, hKpos, hK⟩ θ hθ
  have hstep2 : (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ j
          * Work.FTS.PhiStar.Linv
              (fun θ' => Work.FTS.PhiStar.Gegenbauer.lam m
                * Work.FTS.PhiStar.Gegenbauer.eFam m θ') θ)
      = (∑' m : ℕ, (Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1))
          * Work.FTS.PhiStar.Linv
              (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m t) θ) :=
    Wt_tsum_deriv_rewrite hb0 hj θ
  have hstep4 : Work.FTS.PhiStar.Linv
        (fun t : ℝ => ∑' m : ℕ, (Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1))
          * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ
      = (∑' m : ℕ, (Work.FTS.PhiStar.Series.bmode m ψ
          * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1))
          * Work.FTS.PhiStar.Linv
              (fun t : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m t) θ) :=
    Work.FTS.PhiStar.FlatWAux.LinvTsumEFam
      (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ
        * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1))
      Cb Ce hCbpos.le hCepos.le (fun m θ' hθ' => hgr' m θ' hθ') hcoef θ hθ
  have hstep3 : Work.FTS.PhiStar.Linv (Work.FTS.PhiStar.FlatWAux.chia ψ (j - 1)) θ
      = Work.FTS.PhiStar.Linv
          (fun t : ℝ => ∑' m : ℕ, (Work.FTS.PhiStar.Series.bmode m ψ
            * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ (j - 1))
            * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ :=
    Linv_congr_Ioc hθ.1 (fun t ht => chia_eq_tsum_Ioc hexp hj ht hθ.2)
  exact hstep1.trans (hstep2.trans (hstep4.symm.trans hstep3.symm))

end Work.FTS.PhiStar.FlatWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.FlatWAux.summable_bmode_lam_inv_pow_G_Qm =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.FlatWAux

/-! ## Elementary facts about `λ_m = 2m(2m+5)`, about `s2 θ = sin 2θ`, and the
comparison core of the summability estimate. -/

private lemma flam_pos {m : ℕ} (hm : 1 ≤ m) : 0 < Gegenbauer.lam m := by
  have h1 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  simp only [Gegenbauer.lam]
  nlinarith

private lemma flam_ge_one {m : ℕ} (hm : 1 ≤ m) : 1 ≤ Gegenbauer.lam m := by
  have h1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simp only [Gegenbauer.lam]
  nlinarith


/-- The comparison core: `(2m+1)·m² ≤ λ_m²` for `m ≥ 1`.  (`λ_m = 4m² + 10m`, so
`λ_m² ≥ (4m²)² = 16m⁴ ≥ 3m³ = (2m+1)m²` once `m ≥ 1`.) -/
private lemma flam_sq_bound {m : ℕ} (hm : 1 ≤ m) :
    (2 * (m : ℝ) + 1) * (m : ℝ) ^ 2 ≤ (Gegenbauer.lam m) ^ 2 := by
  have hx1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  simp only [Gegenbauer.lam]
  nlinarith [hx1, sq_nonneg ((m : ℝ)), sq_nonneg (2 * (m : ℝ) + 5)]

private lemma fs2_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Construction.s2 θ := by
  rw [Construction.s2_eq, Real.sin_two_mul]
  exact mul_pos
    (mul_pos two_pos (Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])))
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩)

/-- **Summability of `Σ_m b_m λ_m^{-j} G_m Q_m(θ)`.**

The `m`-th summand is bounded by
`C/(λ_m √(2m+1)) · λ_m^{-j} · Cg/λ_m · (C (2m+1)/sin 2θ) ≤ (Cb Cg C/sin 2θ) · (2m+1)/λ_m²`
(since `λ_m ≥ 1` and `j ≥ 0`), and `(2m+1)/λ_m² ≤ m^{-2}` for `m ≥ 1`; the `m = 0` term
vanishes because `b_0 = 0`. -/
theorem summable_bmode_lam_inv_pow_G_Qm (ψ : ℝ → ℝ) (θ : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ' : ℝ), θ' ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ'| ≤ C * (2 * (m : ℝ) + 1))
    (Cg : ℝ) (hCg : 0 < Cg) (G : ℕ → ℝ)
    (hG : ∀ m : ℕ, 1 ≤ m → |G m| ≤ Cg / Work.FTS.PhiStar.Gegenbauer.lam m) :
    Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ
      * ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ j * G m * Work.FTS.PhiStar.FlatWAux.Qm m θ) := by
  obtain ⟨Cb, hCb, hdec⟩ := hdec
  obtain ⟨Cr, hCr, hgr⟩ := hgr
  have hs2pos : 0 < Construction.s2 θ := fs2_pos_of_mem hθ
  have hs2nonneg : (0 : ℝ) ≤ Construction.s2 θ := le_of_lt hs2pos
  have hθI : θ ∈ Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  set K : ℝ := Cb * Cg * Cr / Construction.s2 θ with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    exact div_pos (mul_pos (mul_pos hCb hCg) hCr) hs2pos
  refine Summable.of_norm_bounded (g := fun m : ℕ => K * (m : ℝ) ^ (-(2 : ℝ))) ?_ ?_
  · exact ((Real.summable_nat_rpow (p := (-(2 : ℝ)))).mpr (by norm_num)).mul_left K
  · intro m
    by_cases hm : m = 0
    · subst hm
      simp only [hb0, zero_mul, norm_zero]
      rw [Nat.cast_zero, Real.zero_rpow (by norm_num : (-(2 : ℝ)) ≠ 0), mul_zero]
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hx1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hxpos : (0 : ℝ) < (m : ℝ) := by linarith
      have hLpos : 0 < Gegenbauer.lam m := flam_pos hm1
      have hL1 : 1 ≤ Gegenbauer.lam m := flam_ge_one hm1
      have hLsqpos : 0 < (Gegenbauer.lam m) ^ 2 := pow_pos hLpos 2
      have hx2pos : 0 < (m : ℝ) ^ 2 := pow_pos hxpos 2
      have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (2 * (m : ℝ) + 1) := by
        rw [Real.one_le_sqrt]; linarith
      have hu1 : (0 : ℝ) ≤ 2 * (m : ℝ) + 1 := by linarith
      have hn1 : (0 : ℝ) ≤ Cb / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)) :=
        div_nonneg (le_of_lt hCb) (mul_nonneg (le_of_lt hLpos) (Real.sqrt_nonneg _))
      have hn3 : (0 : ℝ) ≤ Cg / Gegenbauer.lam m :=
        div_nonneg (le_of_lt hCg) (le_of_lt hLpos)
      have hn4 : (0 : ℝ) ≤ Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ :=
        div_nonneg (mul_nonneg (le_of_lt hCr) hu1) hs2nonneg
      have hQm : |Qm m θ| ≤ Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ := by
        simp only [Qm]
        rw [abs_div, abs_of_pos hs2pos]
        exact div_le_div_of_nonneg_right (hgr m θ hθI) hs2nonneg
      have hA2 : ((Gegenbauer.lam m)⁻¹) ^ j ≤ 1 :=
        pow_le_one₀ (inv_nonneg.mpr (le_of_lt hLpos)) (inv_le_one_of_one_le₀ hL1)
      have hpow_nonneg : (0 : ℝ) ≤ ((Gegenbauer.lam m)⁻¹) ^ j :=
        pow_nonneg (inv_nonneg.mpr (le_of_lt hLpos)) j
      -- the four factors, bounded one by one
      have hprod1 : |Series.bmode m ψ| * ((Gegenbauer.lam m)⁻¹) ^ j * |G m| * |Qm m θ|
          ≤ (Cb / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) * 1
              * (Cg / Gegenbauer.lam m) * (Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ) :=
        mul_le_mul
          (mul_le_mul (mul_le_mul (hdec m hm1) hA2 hpow_nonneg hn1) (hG m hm1)
            (abs_nonneg _) (mul_nonneg hn1 zero_le_one))
          hQm (abs_nonneg _) (mul_nonneg (mul_nonneg hn1 zero_le_one) hn3)
      -- drop the `√(2m+1)`
      have hprod2 : (Cb / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) * 1
              * (Cg / Gegenbauer.lam m) * (Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ)
          ≤ (Cb / Gegenbauer.lam m) * (Cg / Gegenbauer.lam m)
              * (Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ) := by
        have hcd : Cb / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
            ≤ Cb / Gegenbauer.lam m :=
          div_le_div_of_nonneg_left (le_of_lt hCb) hLpos (by nlinarith [hsqrt1, hLpos])
        calc (Cb / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) * 1
                * (Cg / Gegenbauer.lam m) * (Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ)
            = (Cb / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
                * ((Cg / Gegenbauer.lam m)
                    * (Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ)) := by ring
          _ ≤ (Cb / Gegenbauer.lam m)
                * ((Cg / Gegenbauer.lam m)
                    * (Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ)) :=
              mul_le_mul_of_nonneg_right hcd (mul_nonneg hn3 hn4)
          _ = (Cb / Gegenbauer.lam m) * (Cg / Gegenbauer.lam m)
                * (Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ) := by ring
      -- the `m`-decay of the remaining factor
      have hkey : (2 * (m : ℝ) + 1) / (Gegenbauer.lam m) ^ 2 ≤ (1 : ℝ) / (m : ℝ) ^ 2 := by
        rw [div_le_div_iff₀ hLsqpos hx2pos]
        nlinarith [flam_sq_bound hm1]
      have hprod3 : (Cb / Gegenbauer.lam m) * (Cg / Gegenbauer.lam m)
              * (Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ) ≤ K * (m : ℝ) ^ (-(2 : ℝ)) := by
        have hfac : (Cb / Gegenbauer.lam m) * (Cg / Gegenbauer.lam m)
              * (Cr * (2 * (m : ℝ) + 1) / Construction.s2 θ)
            = K * ((2 * (m : ℝ) + 1) / (Gegenbauer.lam m) ^ 2) := by
          rw [hKdef]
          simp only [div_eq_mul_inv]
          rw [← inv_pow]
          ring
        rw [hfac]
        calc K * ((2 * (m : ℝ) + 1) / (Gegenbauer.lam m) ^ 2)
            ≤ K * ((1 : ℝ) / (m : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_left hkey (le_of_lt hKpos)
          _ = K * (m : ℝ) ^ (-(2 : ℝ)) := by
              rw [one_div, show (-(2 : ℝ)) = -(((2 : ℕ) : ℝ)) by norm_num,
                  Real.rpow_neg (le_of_lt hxpos), Real.rpow_natCast]
      have hmain : |Series.bmode m ψ * ((Gegenbauer.lam m)⁻¹) ^ j * G m * Qm m θ|
          ≤ K * (m : ℝ) ^ (-(2 : ℝ)) := by
        rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_inv, abs_of_pos hLpos]
        exact le_trans hprod1 (le_trans hprod2 hprod3)
      simpa only [Real.norm_eq_abs] using hmain

end Work.FTS.PhiStar.FlatWAux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Conjunctions34 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

/-! ## Conversion of the coefficient-decay rate -/

/-- `bmode_decay15`'s rate `1/(lam m · √(2m+1))` is bounded by `(m+1)^{-5/2}` (for `m ≥ 1`),
which is the shape the summability estimates use. -/
theorem bmode_decay_pow (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |bmode m ψ| ≤ C * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
  obtain ⟨Cd, hCd, hdec⟩ := bmode_decay15
  refine ⟨Cd, hCd, fun m hm => ?_⟩
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hdec' := hdec α ψ hα hα5 hψ m hm
  have hkey : (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))⁻¹
      ≤ ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
    have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by linarith
    have hden : 0 < Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) := by
      rw [Work.FTS.PhiStar.Gegenbauer.lam]
      have : (0 : ℝ) < Real.sqrt (2 * (m : ℝ) + 1) := Real.sqrt_pos.mpr (by linarith)
      positivity
    have hnum : 0 < ((m : ℝ) + 1) ^ ((5 / 2 : ℝ)) := Real.rpow_pos_of_pos hm0 _
    have hS : ((m : ℝ) + 1) ^ ((5 / 2 : ℝ)) ≤
        Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) := by
      have hsplit : ((m : ℝ) + 1) ^ ((5 / 2 : ℝ))
          = ((m : ℝ) + 1) ^ (2 : ℕ) * Real.sqrt ((m : ℝ) + 1) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hm0]
        norm_num
      rw [hsplit]
      have h3 : ((m : ℝ) + 1) ^ (2 : ℕ) ≤ 4 * (m : ℝ) ^ 2 := by
        have hle : (m : ℝ) + 1 ≤ 2 * (m : ℝ) := by linarith
        have hp := pow_le_pow_left₀ (by linarith : (0 : ℝ) ≤ (m : ℝ) + 1) hle 2
        nlinarith [hp]
      have h4 : (4 : ℝ) * (m : ℝ) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
        rw [Work.FTS.PhiStar.Gegenbauer.lam]
        nlinarith [Nat.cast_nonneg (α := ℝ) m]
      have h5 : Real.sqrt ((m : ℝ) + 1) ≤ Real.sqrt (2 * (m : ℝ) + 1) :=
        Real.sqrt_le_sqrt (by linarith)
      exact mul_le_mul (le_trans h3 h4) h5 (Real.sqrt_nonneg _)
        (le_trans (by positivity : (0 : ℝ) ≤ 4 * (m : ℝ) ^ 2) h4)
    rw [Real.rpow_neg (le_of_lt hm0)]
    exact (inv_le_inv₀ hden hnum).mpr hS
  have hdiv : Cd / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))
      ≤ Cd * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hkey (le_of_lt hCd)
  rw [bmode_eq_cmode m ψ 0]
  exact le_trans hdec' hdiv

/-! ## Summability of the mode series for the remainder source -/

/-- **Absolute summability of the mode series**, unconditionally for `0 < α ≤ 1/5` and
`AngModel α ψ`. -/
theorem summable_modes_inst (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Summable (fun m : ℕ => acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
  obtain ⟨Cr, hCr, hR⟩ := radGreen_phiA_bound
  refine summable_modes α ψ hα hψ eFam_growth (bmode_decay_pow α ψ hα hα5 hψ)
    ⟨Cr, hCr, fun m hm z hz => (hR α hα (by linarith) m hm).1 z hz⟩

/-! ## Conjuncts 3 and 4 of the target -/

/-- **Conjunct 4**: for every `θ ∈ Iθ` the mode series of the remainder source tends to `0` as
`z → ∞` (unconditionally, for `0 < α ≤ 1/5` and `AngModel α ψ`). -/
theorem psiSeries_tendsto_zero_inst (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun z => psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z θ)
        Filter.atTop (nhds 0) := by
  obtain ⟨Cr, hCr, hR⟩ := radGreen_phiA_bound
  refine psiSeries_tendsto_zero_RemSource α ψ hα hψ eFam_growth
    (bmode_decay_pow α ψ hα hα5 hψ)
    ⟨Cr, hCr, fun m hm z hz => (hR α hα (by linarith) m hm).2 z hz⟩
    (fun z hz θ hθ => ?_)
  exact summable_norm_iff.mpr (summable_modes_inst α ψ hα hα5 hψ z hz θ hθ)

/-- **Conjunct 3**: the Dirichlet values of the mode series (unconditional). -/
theorem psiSeries_dirichlet_inst (α : ℝ) (ψ : ℝ → ℝ) :
    ∀ z : ℝ, psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z 0 = 0 ∧
      psiSeries α (Work.FTS.PhiStar.RemSource α ψ) z (Real.pi / 2) = 0 :=
  fun z => ⟨psiSeries_zero_right α _ z, psiSeries_zero_left α _ z⟩

end Work.FTS.PhiStar.Series
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Series.Deleg.psiRadFacts =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Deleg

/-!
# `psiRadFacts`

Three radial facts about the mode-wise Green function `Radial.radGreen` used by the `Φ_*` series:

1. the profile `VocabO.phiA α` has bounded derivatives up to order `22` (delegated);
2. a uniform-in-`m` bound `|∂_z^k (radGreen α m c) z| ≤ C K / lam m` for `k ≤ 2`, `0 < z`, for
   sources `c` of class `C^22` with `|c^{(j)}| ≤ K` (this file);
3. the mode-`m` Euler equation solved by `radGreen`, without the extra integrability hypothesis
   of `Radial.radGreen_solves` on `(0,1)` (delegated).

The second fact is proved through the *rescaled* form of the Green function
(`RadialWAux.radGreen_eq_rescaled`): on `(0,∞)`,

  `radGreen α m c = radK α m · (radPhi α m c + radPsi α m c)`,

and the two summands are bounded, together with their first two `z`-derivatives, by
`K/(k + q)` resp. `K/(p - k)` (`radPhi_iteratedDeriv_bound`, `radPsi_integral_bound`).  The only
delicate point is the transfer of the two `iteratedDeriv`s through the sum: it is done with the
eventual-equality and differentiability lemmas proved below, no `C^∞`-regularity of `radPhi`
being needed (`ContDiffOn` of `radPhi` is only available through the currently unbuildable
`radPhi_contDiffOn`, so we avoid it).
-/

open Work.FTS.PhiStar.RadialWAux (radPhi radPsi radP radQ radK radP_pos radQ_pos ten_le_radP
  thirtyfive_le_radQ radP_add_radQ)
open Work.FTS.PhiStar.Radial (radGreen)
open Work.FTS.PhiStar.Series (rgiA rgiB rgiF1 rgiF2 rgiK rgiSn rgiSp rgiD1)

variable {α : ℝ} {m : ℕ} {c : ℝ → ℝ} {K : ℝ}

/-! ### Elementary bounds and integrability of the two source kernels -/

private lemma c_abs_le (hb : BddDeriv 22 c K) : ∀ t : ℝ, 0 < t → |c t| ≤ K := by
  intro t ht
  simpa only [iteratedDeriv_zero] using hb 0 (by norm_num) t ht

private lemma integrableOn_rgiF1 (hα : 0 < α) (hα5 : α ≤ 1 / 5) (hK : 0 ≤ K)
    (hc : ContDiffOn ℝ 22 c (Set.Ioi 0)) (hb : ∀ t : ℝ, 0 < t → |c t| ≤ K) :
    IntegrableOn (rgiF1 α m c) (Set.Ioo 0 1) := by
  have h25 : (25 : ℝ) ≤ radQ α m := by
    rw [show radQ α m = (2 * (m : ℝ) + 5) / α from rfl]
    rw [le_div_iff₀ hα]
    nlinarith [Nat.cast_nonneg (α := ℝ) m, hα5]
  have hq : (1 : ℝ) < radQ α m := by linarith
  refine IntegrableOn.of_bound (measure_Ioo_lt_top) ?_ K ?_
  · exact ((Work.FTS.PhiStar.Series.rgiF1_continuousOn hc.continuousOn).mono
      (fun t ht => ht.1)).aestronglyMeasurable (μ := volume) measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have ht0 : 0 < t := ht.1
    have ht1 : t < 1 := ht.2
    have he : (0 : ℝ) ≤ (2 * (m : ℝ) + 5) / α - 1 := by
      simpa only [radQ] using sub_nonneg.mpr (le_of_lt hq)
    have hle : t ^ ((2 * (m : ℝ) + 5) / α - 1) ≤ 1 := by
      calc t ^ ((2 * (m : ℝ) + 5) / α - 1) ≤ 1 ^ ((2 * (m : ℝ) + 5) / α - 1) :=
            Real.rpow_le_rpow (le_of_lt ht0) (le_of_lt ht1) he
        _ = 1 := Real.one_rpow _
    rw [Real.norm_eq_abs, Work.FTS.PhiStar.Series.rgiF1, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    calc |c t| * t ^ ((2 * (m : ℝ) + 5) / α - 1) ≤ K * 1 :=
          mul_le_mul (hb t ht0) hle (Real.rpow_nonneg ht0.le _) hK
      _ = K := mul_one K

private lemma integrableOn_rgiF2 (hα : 0 < α) (hm : 1 ≤ m)
    (hc : ContDiffOn ℝ 22 c (Set.Ioi 0)) (hb : ∀ t : ℝ, 0 < t → |c t| ≤ K) :
    IntegrableOn (rgiF2 α m c) (Set.Ioi 1) := by
  have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hpos : 0 < 2 * (m : ℝ) / α := div_pos (by linarith) hα
  have hlt : -(2 * (m : ℝ) / α) - 1 < -1 := by linarith
  have hg : IntegrableOn (fun t : ℝ => K * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt hlt zero_lt_one).const_mul K
  have hcont : ContinuousOn (rgiF2 α m c) (Set.Ioi 1) :=
    (Work.FTS.PhiStar.Series.rgiF2_continuousOn hc.continuousOn).mono
      (fun t ht => by simp only [Set.mem_Ioi] at ht ⊢; linarith)
  refine Integrable.mono' hg (hcont.aestronglyMeasurable (μ := volume) measurableSet_Ioi) ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    rw [Real.norm_eq_abs, Work.FTS.PhiStar.Series.rgiF2, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg ht0.le _)]
    exact mul_le_mul_of_nonneg_right (hb t ht0) (Real.rpow_nonneg ht0.le _)

/-! ### The rescaled form: pointwise identities, derivatives, differentiability -/

/-- The Green function in rescaled form, with the normalisation `rgiK` of the series file. -/
private lemma radGreen_eq_rescaled' (hα : 0 < α) {w : ℝ} (hw : 0 < w) :
    radGreen α m c w = rgiK α m * (radPhi α m c w + radPsi α m c w) := by
  rw [Work.FTS.PhiStar.RadialWAux.radGreen_eq_rescaled hα m c w hw]
  simp only [Work.FTS.PhiStar.RadialWAux.radK, rgiK]

private lemma radPhi_eq_rpow {w : ℝ} (hw : 0 < w) :
    radPhi α m c w = w ^ (rgiSn α m) * rgiA α m c w := by
  simp only [radPhi, rgiA]
  rw [Work.FTS.PhiStar.RadialWAux.integral_zero_one_rpow c (radQ α m - 1) hw]
  have hexp : -((radQ α m - 1) + 1) = rgiSn α m := by
    simp only [radQ, rgiSn]; rw [sub_add_cancel, neg_div]
  rw [hexp]
  congr 1

private lemma radPsi_eq_rpow {w : ℝ} (hw : 0 < w) :
    radPsi α m c w = w ^ (rgiSp α m) * rgiB α m c w := by
  simp only [radPsi, rgiB]
  rw [Work.FTS.PhiStar.RadialWAux.integral_Ioi_one_rpow c (-(radP α m) - 1) hw]
  have hexp : -(-(radP α m) - 1 + 1) = rgiSp α m := by
    simp only [radP, rgiSp]; ring
  rw [hexp]
  congr 1

private lemma deriv_radPhi (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hF1 : IntegrableOn (rgiF1 α m c) (Set.Ioo 0 1)) {w : ℝ} (hw : 0 < w) :
    deriv (radPhi α m c) w
      = rgiSn α m * w ^ (rgiSn α m - 1) * rgiA α m c w
        + w ^ (rgiSn α m) * rgiF1 α m c w := by
  have hwne : w ≠ 0 := ne_of_gt hw
  have heq : radPhi α m c =ᶠ[𝓝 w] (fun u : ℝ => u ^ (rgiSn α m) * rgiA α m c u) := by
    filter_upwards [isOpen_Ioi.mem_nhds hw] with u hu
    exact radPhi_eq_rpow hu
  rw [Filter.EventuallyEq.deriv_eq heq]
  have hp : HasDerivAt (fun u : ℝ => u ^ (rgiSn α m))
      (rgiSn α m * w ^ (rgiSn α m - 1)) w := Real.hasDerivAt_rpow_const (Or.inl hwne)
  have hA : HasDerivAt (rgiA α m c) (rgiF1 α m c w) w :=
    Work.FTS.PhiStar.Series.rgiA_hasDerivAt hc.continuousOn hF1 w hw
  exact (hp.mul hA).deriv

private lemma deriv_radPsi (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hF2 : IntegrableOn (rgiF2 α m c) (Set.Ioi 1)) {w : ℝ} (hw : 0 < w) :
    deriv (radPsi α m c) w
      = rgiSp α m * w ^ (rgiSp α m - 1) * rgiB α m c w
        - w ^ (rgiSp α m) * rgiF2 α m c w := by
  have hwne : w ≠ 0 := ne_of_gt hw
  have heq : radPsi α m c =ᶠ[𝓝 w] (fun u : ℝ => u ^ (rgiSp α m) * rgiB α m c u) := by
    filter_upwards [isOpen_Ioi.mem_nhds hw] with u hu
    exact radPsi_eq_rpow hu
  rw [Filter.EventuallyEq.deriv_eq heq]
  have hp : HasDerivAt (fun u : ℝ => u ^ (rgiSp α m))
      (rgiSp α m * w ^ (rgiSp α m - 1)) w := Real.hasDerivAt_rpow_const (Or.inl hwne)
  have hB : HasDerivAt (rgiB α m c) (-(rgiF2 α m c w)) w :=
    Work.FTS.PhiStar.Series.rgiB_hasDerivAt hc.continuousOn hF2 w hw
  have h := (hp.mul hB).deriv
  rw [mul_neg] at h
  rw [sub_eq_add_neg]
  exact h




private lemma differentiableAt_radPhi (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hF1 : IntegrableOn (rgiF1 α m c) (Set.Ioo 0 1)) {w : ℝ} (hw : 0 < w) :
    DifferentiableAt ℝ (radPhi α m c) w := by
  have hwne : w ≠ 0 := ne_of_gt hw
  have heq : radPhi α m c =ᶠ[𝓝 w] (fun u : ℝ => u ^ (rgiSn α m) * rgiA α m c u) := by
    filter_upwards [isOpen_Ioi.mem_nhds hw] with u hu
    exact radPhi_eq_rpow hu
  refine (heq.differentiableAt_iff).mpr ?_
  exact ((Real.hasDerivAt_rpow_const (p := rgiSn α m) (Or.inl hwne)).differentiableAt).mul
    (Work.FTS.PhiStar.Series.rgiA_hasDerivAt hc.continuousOn hF1 w hw).differentiableAt

private lemma differentiableAt_radPsi (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hF2 : IntegrableOn (rgiF2 α m c) (Set.Ioi 1)) {w : ℝ} (hw : 0 < w) :
    DifferentiableAt ℝ (radPsi α m c) w := by
  have hwne : w ≠ 0 := ne_of_gt hw
  have heq : radPsi α m c =ᶠ[𝓝 w] (fun u : ℝ => u ^ (rgiSp α m) * rgiB α m c u) := by
    filter_upwards [isOpen_Ioi.mem_nhds hw] with u hu
    exact radPsi_eq_rpow hu
  refine (heq.differentiableAt_iff).mpr ?_
  exact ((Real.hasDerivAt_rpow_const (p := rgiSp α m) (Or.inl hwne)).differentiableAt).mul
    (Work.FTS.PhiStar.Series.rgiB_hasDerivAt hc.continuousOn hF2 w hw).differentiableAt

private lemma differentiableAt_deriv_radPhi (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hF1 : IntegrableOn (rgiF1 α m c) (Set.Ioo 0 1)) {w : ℝ} (hw : 0 < w) :
    DifferentiableAt ℝ (deriv (radPhi α m c)) w := by
  have hwne : w ≠ 0 := ne_of_gt hw
  have hd1 : deriv (radPhi α m c) =ᶠ[𝓝 w] (fun u : ℝ => rgiSn α m * u ^ (rgiSn α m - 1)
        * rgiA α m c u + u ^ (rgiSn α m) * rgiF1 α m c u) := by
    filter_upwards [isOpen_Ioi.mem_nhds hw] with u hu
    exact deriv_radPhi hc hF1 hu
  refine (hd1.differentiableAt_iff).mpr ?_
  have h1 : DifferentiableAt ℝ (fun u : ℝ => rgiSn α m * u ^ (rgiSn α m - 1)
      * rgiA α m c u) w :=
    (((Real.hasDerivAt_rpow_const (p := rgiSn α m - 1) (Or.inl hwne)).const_mul
      (rgiSn α m)).mul
      (Work.FTS.PhiStar.Series.rgiA_hasDerivAt hc.continuousOn hF1 w hw)).differentiableAt
  have h2 : DifferentiableAt ℝ (fun u : ℝ => u ^ (rgiSn α m) * rgiF1 α m c u) w :=
    (Real.hasDerivAt_rpow_const (p := rgiSn α m) (Or.inl hwne)).differentiableAt.mul (by
      have hc' : DifferentiableAt ℝ c w :=
        (hc.contDiffAt (isOpen_Ioi.mem_nhds hw)).differentiableAt (by norm_num)
      have h3 : DifferentiableAt ℝ (fun u : ℝ => u ^ ((2 * (m : ℝ) + 5) / α - 1)) w :=
        (Real.hasDerivAt_rpow_const (p := (2 * (m : ℝ) + 5) / α - 1)
          (Or.inl hwne)).differentiableAt
      exact hc'.mul h3)
  exact h1.add h2

private lemma differentiableAt_deriv_radPsi (hc : ContDiffOn ℝ 22 c (Set.Ioi 0))
    (hF2 : IntegrableOn (rgiF2 α m c) (Set.Ioi 1)) {w : ℝ} (hw : 0 < w) :
    DifferentiableAt ℝ (deriv (radPsi α m c)) w := by
  have hwne : w ≠ 0 := ne_of_gt hw
  have hd1 : deriv (radPsi α m c) =ᶠ[𝓝 w] (fun u : ℝ => rgiSp α m * u ^ (rgiSp α m - 1)
        * rgiB α m c u - u ^ (rgiSp α m) * rgiF2 α m c u) := by
    filter_upwards [isOpen_Ioi.mem_nhds hw] with u hu
    exact deriv_radPsi hc hF2 hu
  refine (hd1.differentiableAt_iff).mpr ?_
  have h1 : DifferentiableAt ℝ (fun u : ℝ => rgiSp α m * u ^ (rgiSp α m - 1)
      * rgiB α m c u) w :=
    (((Real.hasDerivAt_rpow_const (p := rgiSp α m - 1) (Or.inl hwne)).const_mul
      (rgiSp α m)).mul
      (Work.FTS.PhiStar.Series.rgiB_hasDerivAt hc.continuousOn hF2 w hw)).differentiableAt
  have h2 : DifferentiableAt ℝ (fun u : ℝ => u ^ (rgiSp α m) * rgiF2 α m c u) w :=
    (Real.hasDerivAt_rpow_const (p := rgiSp α m) (Or.inl hwne)).differentiableAt.mul (by
      have hc' : DifferentiableAt ℝ c w :=
        (hc.contDiffAt (isOpen_Ioi.mem_nhds hw)).differentiableAt (by norm_num)
      have h3 : DifferentiableAt ℝ (fun u : ℝ => u ^ (-(2 * (m : ℝ) / α) - 1)) w :=
        (Real.hasDerivAt_rpow_const (p := -(2 * (m : ℝ) / α) - 1)
          (Or.inl hwne)).differentiableAt
      exact hc'.mul h3)
  exact h1.sub h2

/-! ### Linearity of `iteratedDeriv` up to order `2` -/

/-- `iteratedDeriv` is additive up to order `2` on the open set `(0,∞)`, where both functions and
their derivatives are differentiable. -/
private lemma iteratedDeriv_add_le_two {f g : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hf : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ f x)
    (hg : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ g x)
    (hf' : DifferentiableAt ℝ (deriv f) z) (hg' : DifferentiableAt ℝ (deriv g) z)
    {n : ℕ} (hn : n ≤ 2) :
    iteratedDeriv n (fun x : ℝ => f x + g x) z = iteratedDeriv n f z + iteratedDeriv n g z := by
  interval_cases n
  · simp only [iteratedDeriv_zero]
  · rw [iteratedDeriv_one, iteratedDeriv_one, iteratedDeriv_one]
    exact deriv_add (hf z hz) (hg z hz)
  · have e2 : ∀ X : ℝ → ℝ, iteratedDeriv 2 X = deriv (deriv X) := fun X => by
      rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [e2 (fun x : ℝ => f x + g x), e2 f, e2 g]
    have hder : deriv (fun x : ℝ => f x + g x) =ᶠ[𝓝 z] (deriv f + deriv g) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
      rw [show deriv (fun y : ℝ => f y + g y) x = deriv (f + g) x from rfl]
      exact deriv_add (hf x hx) (hg x hx)
    rw [Filter.EventuallyEq.deriv_eq hder]
    exact deriv_add hf' hg'

/-! ### The second conjunct -/

private theorem radGreen_iteratedDeriv_le (hα : 0 < α) (hα5 : α ≤ 1 / 5) (hm : 1 ≤ m)
    (hK : 0 ≤ K) (hc : ContDiffOn ℝ 22 c (Set.Ioi 0)) (hb : BddDeriv 22 c K)
    (k : ℕ) (hk : k ≤ 2) (z : ℝ) (hz : 0 < z) :
    |iteratedDeriv k (radGreen α m c) z| ≤ 2 * K / Work.FTS.PhiStar.Gegenbauer.lam m := by
  have hb0 : ∀ t : ℝ, 0 < t → |c t| ≤ K := c_abs_le hb
  have hF1 := integrableOn_rgiF1 (α := α) (m := m) (c := c) (K := K) hα hα5 hK hc hb0
  have hF2 := integrableOn_rgiF2 (α := α) (m := m) (c := c) (K := K) hα hm hc hb0
  -- the two indicial exponents and their bounds
  have hqpos : 0 < radQ α m := radQ_pos hα m
  have hp10 : 10 ≤ radP α m := ten_le_radP hα hα5 hm
  have hkp : (k : ℝ) < radP α m := by
    have : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    linarith
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hkq : 0 < (k : ℝ) + radQ α m := by linarith
  have hpk : 0 < radP α m - (k : ℝ) := by
    have h2 : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    linarith
  have hk22 : k ≤ 22 := by omega
  -- the identity `iteratedDeriv k (radGreen) = rgiK * (iteratedDeriv k radPhi + ...)`
  have hres : iteratedDeriv k (radGreen α m c) z
      = rgiK α m * (iteratedDeriv k (radPhi α m c) z
          + iteratedDeriv k (radPsi α m c) z) := by
    have hEq : radGreen α m c =ᶠ[𝓝 z]
        (fun w => rgiK α m * (radPhi α m c w + radPsi α m c w)) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
      exact radGreen_eq_rescaled' (m := m) (c := c) hα hw
    rw [Filter.EventuallyEq.iteratedDeriv_eq k hEq,
      show iteratedDeriv k (fun w => rgiK α m * (radPhi α m c w + radPsi α m c w)) z
          = rgiK α m * iteratedDeriv k (fun w => radPhi α m c w + radPsi α m c w) z from
        iteratedDeriv_const_mul_field (rgiK α m)
          (fun w => radPhi α m c w + radPsi α m c w)]
    congr 1
    exact iteratedDeriv_add_le_two hz
      (fun x hx => differentiableAt_radPhi hc hF1 hx)
      (fun x hx => differentiableAt_radPsi hc hF2 hx)
      (differentiableAt_deriv_radPhi hc hF1 hz) (differentiableAt_deriv_radPsi hc hF2 hz) hk
  -- the two integral bounds
  have hΦ : |iteratedDeriv k (radPhi α m c) z| ≤ K / ((k : ℝ) + radQ α m) :=
    Work.FTS.PhiStar.RadialWAux.radPhi_iteratedDeriv_bound hα m hK hc hb k hk22 z hz
  have hΨ : |iteratedDeriv k (radPsi α m c) z| ≤ K / (radP α m - (k : ℝ)) := by
    rw [Work.FTS.PhiStar.RadialWAux.radPsi_iteratedDeriv hα m hK hc hb k hk22 hkp z hz]
    exact Work.FTS.PhiStar.RadialWAux.radPsi_integral_bound hα m hK hb k hk22 hkp z hz
  -- positivity of the normalisation
  have hKr : 0 < rgiK α m := by simp only [rgiK]; positivity
  -- the algebraic form of the product
  have h1c : (k : ℝ) + radQ α m = ((k : ℝ) * α + 2 * (m : ℝ) + 5) / α := by
    simp only [radQ]
    field_simp <;> ring
  have h2c : radP α m - (k : ℝ) = (2 * (m : ℝ) - (k : ℝ) * α) / α := by
    simp only [radP]
    field_simp <;> ring
  have hE : rgiK α m * (K / ((k : ℝ) + radQ α m) + K / (radP α m - (k : ℝ)))
      = K / (α ^ 2 * ((k : ℝ) + radQ α m) * (radP α m - (k : ℝ))) := by
    have hαne : α ≠ 0 := ne_of_gt hα
    have h45 : 4 * (m : ℝ) + 5 ≠ 0 := by positivity
    have hx : (k : ℝ) + radQ α m ≠ 0 := ne_of_gt hkq
    have hy : radP α m - (k : ℝ) ≠ 0 := ne_of_gt hpk
    have hd : α ^ 2 * ((k : ℝ) + radQ α m) * (radP α m - (k : ℝ)) ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hαne) hx) hy
    have hαpq : α * (radP α m + radQ α m) = 4 * (m : ℝ) + 5 := by
      rw [radP_add_radQ hα m]
      field_simp <;> ring
    simp only [rgiK]
    field_simp [hαne, h45, hx, hy, hd] <;> linear_combination (K : ℝ) * hαpq
  -- the numerical inequality
  have hden : (4 / 5) * Work.FTS.PhiStar.Gegenbauer.lam m
      ≤ α ^ 2 * ((k : ℝ) + radQ α m) * (radP α m - (k : ℝ)) := by
    have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have hk2 : (k : ℝ) ≤ 2 := by exact_mod_cast hk
    have hka : (k : ℝ) * α ≤ (1 / 5) * (2 * (m : ℝ)) := by
      have h1 : (k : ℝ) * α ≤ 2 * α := mul_le_mul_of_nonneg_right hk2 (le_of_lt hα)
      have h2 : 2 * α ≤ 2 / 5 := by linarith
      have h5 : (2 : ℝ) / 5 ≤ (1 / 5) * (2 * (m : ℝ)) := by linarith
      linarith
    have h1 : (4 / 5) * (2 * (m : ℝ)) ≤ 2 * (m : ℝ) - (k : ℝ) * α := by linarith
    have h2 : 2 * (m : ℝ) + 5 ≤ (k : ℝ) * α + 2 * (m : ℝ) + 5 := by
      have hnn : (0 : ℝ) ≤ (k : ℝ) * α := mul_nonneg hk0 (le_of_lt hα)
      linarith
    have h3 : (0 : ℝ) ≤ (4 / 5) * (2 * (m : ℝ)) := by linarith
    have h4 : (0 : ℝ) ≤ (k : ℝ) * α + 2 * (m : ℝ) + 5 := by linarith
    have hprod : (4 / 5) * (2 * (m : ℝ) * (2 * (m : ℝ) + 5))
        ≤ ((k : ℝ) * α + 2 * (m : ℝ) + 5) * (2 * (m : ℝ) - (k : ℝ) * α) :=
      calc (4 / 5) * (2 * (m : ℝ) * (2 * (m : ℝ) + 5))
          = (2 * (m : ℝ) + 5) * ((4 / 5) * (2 * (m : ℝ))) := by ring
        _ ≤ ((k : ℝ) * α + 2 * (m : ℝ) + 5) * (2 * (m : ℝ) - (k : ℝ) * α) :=
            mul_le_mul h2 h1 h3 h4
    have hXeq : α ^ 2 * ((k : ℝ) + radQ α m) * (radP α m - (k : ℝ))
        = ((k : ℝ) * α + 2 * (m : ℝ) + 5) * (2 * (m : ℝ) - (k : ℝ) * α) := by
      rw [h1c, h2c]
      field_simp <;> ring
    rw [hXeq]
    simpa only [Work.FTS.PhiStar.Gegenbauer.lam] using hprod
  have hXpos : 0 < α ^ 2 * ((k : ℝ) + radQ α m) * (radP α m - (k : ℝ)) :=
    mul_pos (mul_pos (pow_pos hα 2) hkq) hpk
  have hLpos : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := by
    simp only [Work.FTS.PhiStar.Gegenbauer.lam]
    have hmr : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h1 : (0 : ℝ) < 2 * (m : ℝ) := by linarith
    have h2 : (0 : ℝ) < 2 * (m : ℝ) + 5 := by linarith
    exact mul_pos h1 h2
  have hfinal : K / (α ^ 2 * ((k : ℝ) + radQ α m) * (radP α m - (k : ℝ)))
      ≤ 2 * K / Work.FTS.PhiStar.Gegenbauer.lam m := by
    have hLne : Work.FTS.PhiStar.Gegenbauer.lam m ≠ 0 := ne_of_gt hLpos
    have h45 : 0 < (4 / 5) * Work.FTS.PhiStar.Gegenbauer.lam m := by linarith
    calc K / (α ^ 2 * ((k : ℝ) + radQ α m) * (radP α m - (k : ℝ)))
        ≤ K / ((4 / 5) * Work.FTS.PhiStar.Gegenbauer.lam m) :=
          div_le_div_of_nonneg_left hK h45 hden
      _ = (5 / 4) * (K / Work.FTS.PhiStar.Gegenbauer.lam m) := by
          field_simp <;> ring
      _ ≤ 2 * (K / Work.FTS.PhiStar.Gegenbauer.lam m) := by
          linarith [div_nonneg hK (le_of_lt hLpos)]
      _ = 2 * K / Work.FTS.PhiStar.Gegenbauer.lam m := by ring
  rw [hres]
  calc |rgiK α m * (iteratedDeriv k (radPhi α m c) z
          + iteratedDeriv k (radPsi α m c) z)|
      = rgiK α m * |iteratedDeriv k (radPhi α m c) z
          + iteratedDeriv k (radPsi α m c) z| := by
        rw [abs_mul, abs_of_nonneg (le_of_lt hKr)]
    _ ≤ rgiK α m * (|iteratedDeriv k (radPhi α m c) z|
          + |iteratedDeriv k (radPsi α m c) z|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (le_of_lt hKr)
    _ ≤ rgiK α m * (K / ((k : ℝ) + radQ α m) + K / (radP α m - (k : ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add hΦ hΨ) (le_of_lt hKr)
    _ = K / (α ^ 2 * ((k : ℝ) + radQ α m) * (radP α m - (k : ℝ))) := hE
    _ ≤ 2 * K / Work.FTS.PhiStar.Gegenbauer.lam m := hfinal

theorem psiRadFacts (α : ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5) :
    (∃ K : ℝ, 0 ≤ K ∧ Work.FTS.PhiStar.BddDeriv 22 (Work.FTS.VocabO.phiA α) K) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (c : ℝ → ℝ) (K : ℝ), 0 ≤ K → 1 ≤ m →
        ContDiffOn ℝ 22 c (Set.Ioi 0) → Work.FTS.PhiStar.BddDeriv 22 c K →
          ∀ k : ℕ, k ≤ 2 → ∀ z : ℝ, 0 < z →
            |iteratedDeriv k (Work.FTS.PhiStar.Radial.radGreen α m c) z|
              ≤ C * K / Work.FTS.PhiStar.Gegenbauer.lam m) ∧
    (∀ (m : ℕ) (c : ℝ → ℝ), ContinuousOn c (Set.Ioi 0) →
        MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
          (Set.Ioo 0 1) →
        MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
          (Set.Ioi 1) →
        ∀ z, 0 < z →
          -α ^ 2 * z ^ 2 * deriv (deriv (Work.FTS.PhiStar.Radial.radGreen α m c)) z
            - α * (5 + α) * z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
            + Work.FTS.PhiStar.Radial.lamR m * Work.FTS.PhiStar.Radial.radGreen α m c z
            = c z) := by
  refine ⟨phiABddDeriv α hα hα5, ⟨2, by norm_num, ?_⟩, ?_⟩
  · intro m c K hK hm hc hb k hk z hz
    exact radGreen_iteratedDeriv_le hα hα5 hm hK hc hb k hk z hz
  · exact fun m c hc h0 hinf => radGreenSolvesNoH0 α hα m hc h0 hinf

end Work.FTS.PhiStar.Series.Deleg
end
end
