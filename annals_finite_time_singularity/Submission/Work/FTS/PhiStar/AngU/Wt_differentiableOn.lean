import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.StarDefs
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.PhiStar.FamDerivDivLinv
import Submission.Work.FTS.PhiStar.FlatWAux.WtDerivTsum

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
