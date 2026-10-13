import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.Defs
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Wgt
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Wgt2
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth.Integ
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6Aux.zeroTerm
import Submission.Work.FTS.StrongPersist.N6Trans.T1SixAux.hardSlotSliceSixZero
import Submission.Work.FTS.TransportS.sup_dz_le_hk
import Submission.Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth

/-! ## The `(i,j) = (0,0)` transport summand of the `D_θ`-row

The integrand `ρ·A·D_θ(D_z^bD_θ^a f)·D_z^bD_θ^af` carries *no* derivative on the coefficient
`A`, so it is controlled by the slice-level transport inequality
`N6Trans.T1SixAux.hardSlotSliceSixZero`, which is stated for a coefficient `F` with *both*
`|F| ≤ Kf` and `|D_θF| ≤ Kf`.  The `CoefData` of this row does not give a pointwise bound on
`D_θA` directly, but the `α`-uniform pointwise bound of mixed slots of order `≤ 2`
(`TransportS.T2SupB2.mixed_pointwise_le_Xn`, at `(i,j) = (1,0)`) gives
`|D_θA| ≤ Cm·|A|_{ℋ⁴} ≤ Cm·K4`, so the slice inequality may be applied with
`Kf := max K0 (Cm·K4)`.  Everything else (the three leaf weights, the `z`-integration, the two
integrability conjuncts, the energy bound `∫∫ρ(D_z^bD_θ^af)² ≤ HkSq α 6 f`) is exactly the
sibling lemma `Npair6Aux.zeroTerm`, which already performs this assembly for the coefficient
hypotheses `CoefHyp`/`DatHyp` (field-for-field the `CoefData`/`DatData` of this row). -/

/-- `D_θ` is the `(i,j) = (1,0)` mixed slot. -/
theorem dth_eq_mixed_zero_one (g : ℝ → ℝ → ℝ) : Work.Spaces.Dth g = Work.Spaces.mixed 0 1 g := rfl

theorem zeroTermDth : ∃ C : ℝ, 0 < C ∧
    ∀ α ∈ Set.Ioc 0 1, ∀ (A f : Work.FTS.Galerkin.Fn) (K0 K4 K6 M : ℝ) (a b : ℕ)
      (ρ : ℝ → ℝ → ℝ),
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.CoefData α A K0 K4 K6 →
      Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.DatData α f M → a + b ≤ 6 →
      Work.FTS.TransportS.IsLeafW α a ρ →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ : ℝ => ρ z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z : ℝ => ∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
          * Work.Spaces.mixed b a f z θ) Work.Spaces.Iz ∧
      |∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ, ρ z θ * A z θ
          * Work.Spaces.Dth (Work.Spaces.mixed b a f) z θ
          * Work.Spaces.mixed b a f z θ|
        ≤ C * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) * (1 + Work.Spaces.HkSq α 6 f) := by
  -- the two proved ingredients: the pointwise bound on the angular slot of the coefficient
  -- (with an `α`-independent constant) and the assembled sibling row `zeroTerm`
  obtain ⟨Cm, hCmpos, hCm⟩ := Work.FTS.TransportS.T2SupB2.mixed_pointwise_le_Xn
  obtain ⟨Cz, hCzpos, hCz⟩ := Work.FTS.StrongPersist.H6Rows.Npair6Aux.zeroTerm
  set C : ℝ := Cz * max 1 Cm with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    exact mul_pos hCzpos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  refine ⟨C, hCpos, ?_⟩
  intro α hαmem A f K0 K4 K6 M a b ρ hcoef hdat hab hleaf
  obtain ⟨hα, hα1⟩ := hαmem
  -- the coefficient is priced pointwise by `K0` and its angular slot by `Cm · K4`
  have hlt : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hK0 : 0 ≤ K0 :=
    le_trans (abs_nonneg (A 1 1)) (hcoef.val 1 1 (by norm_num) (by norm_num) hlt)
  have hK4 : 0 ≤ K4 := le_trans (Work.Spaces.HkNorm_nonneg α 4 A) hcoef.n4
  have hdbA : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed 0 1 A z θ| ≤ Cm * K4 := by
    intro z θ hz hθ hθ2
    refine le_trans (hCm α A hα hα1 hcoef.sm hcoef.h4 0 1 (by norm_num) (by norm_num)
      z θ hz hθ hθ2) ?_
    exact mul_le_mul_of_nonneg_left hcoef.n4 hCmpos.le
  -- the coefficient price for the slice inequality
  set Kf : ℝ := max K0 (Cm * K4) with hKfdef
  have hKf0 : 0 ≤ Kf := by rw [hKfdef]; exact le_trans hK0 (le_max_left _ _)
  have hvalKf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → |A z θ| ≤ Kf := by
    intro z θ hz hθ hθ2
    rw [hKfdef]
    exact le_trans (hcoef.val z θ hz hθ hθ2) (le_max_left _ _)
  have hdbKf : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.Dth A z θ| ≤ Kf := by
    intro z θ hz hθ hθ2
    rw [hKfdef, dth_eq_mixed_zero_one]
    exact le_trans (hdbA z θ hz hθ hθ2) (le_max_right _ _)
  -- the sibling row `zeroTerm`, with the coefficient data transported to `CoefHyp`/`DatHyp`
  have hcoefH : Work.FTS.StrongPersist.H6Rows.Npair6Aux.CoefHyp α A K0 K4 K6 :=
    ⟨hcoef.sm, hcoef.h4, hcoef.h6, hcoef.val, hcoef.n4, hcoef.n6⟩
  have hdatH : Work.FTS.StrongPersist.H6Rows.Npair6Aux.DatHyp α f M :=
    ⟨hdat.sm, hdat.h6, hdat.h7, hdat.vanish, hdat.axis, hdat.bdd⟩
  obtain ⟨h1, h2, h3⟩ := hCz α ⟨hα, hα1⟩ A f Kf M a b ρ
    hcoefH.sm hKf0 hvalKf hdbKf hdatH hab hleaf
  refine ⟨h1, h2, ?_⟩
  -- `max K0 (Cm·K4) ≤ max 1 Cm · (K0 + K4)`
  have hsum0 : 0 ≤ K0 + K4 := add_nonneg hK0 hK4
  have hM0 : 0 ≤ max 1 Cm := le_trans zero_le_one (le_max_left _ _)
  have hKf_le : Kf ≤ max 1 Cm * (K0 + K4) := by
    rw [hKfdef]
    refine max_le ?_ ?_
    · calc K0 ≤ 1 * (K0 + K4) := by rw [one_mul]; exact le_add_of_nonneg_right hK4
        _ ≤ max 1 Cm * (K0 + K4) := mul_le_mul_of_nonneg_right (le_max_left _ _) hsum0
    · calc Cm * K4 ≤ max 1 Cm * K4 := mul_le_mul_of_nonneg_right (le_max_right _ _) hK4
        _ ≤ max 1 Cm * (K0 + K4) := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hK0) hM0
  have hCK : Cz * Kf ≤ C * (K0 + K4) := by
    rw [hCdef]
    calc Cz * Kf ≤ Cz * (max 1 Cm * (K0 + K4)) :=
          mul_le_mul_of_nonneg_left hKf_le hCzpos.le
      _ = Cz * max 1 Cm * (K0 + K4) := by ring
  -- `α^{-1/2} ≥ 1` and `HkSq ≥ 0`
  have hS0 : 0 ≤ Work.Spaces.HkSq α 6 f := Work.Spaces.HkSq_nonneg α 6 f
  have hαr : (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := one_le_alpha_rpow_neg_half hα hα1
  have hSle : Work.Spaces.HkSq α 6 f
      ≤ α ^ (-(1 / 2 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f) := by
    have h1' : Work.Spaces.HkSq α 6 f ≤ α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkSq α 6 f := by
      simpa using mul_le_mul_of_nonneg_right hαr hS0
    have h2' : α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkSq α 6 f
        ≤ α ^ (-(1 / 2 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one)
        (le_trans zero_le_one hαr)
    linarith
  refine le_trans h3 ?_
  calc Cz * Kf * Work.Spaces.HkSq α 6 f
      ≤ (C * (K0 + K4)) * Work.Spaces.HkSq α 6 f :=
        mul_le_mul_of_nonneg_right hCK hS0
    _ ≤ (C * (K0 + K4)) * (α ^ (-(1 / 2 : ℝ)) * (1 + Work.Spaces.HkSq α 6 f)) :=
        mul_le_mul_of_nonneg_left hSle (mul_nonneg hCpos.le hsum0)
    _ = C * α ^ (-(1 / 2 : ℝ)) * (K0 + K4) * (1 + Work.Spaces.HkSq α 6 f) := by ring

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.RowDth
