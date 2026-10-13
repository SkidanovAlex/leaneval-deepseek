import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.R2.Clauses
import Submission.Work.FTS.RegPkgGal.R2.hasDerivAt_slice_pth
import Submission.Work.FTS.RegPkgGal.R2.hasDerivAt_slice_pz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The repaired Taylor packages

Two versions of the repaired statement, both conditional on the single analytic input `hA`
(the angular integral bound `Work.FTS.RegPkgGal.R2.angIntegral_le`):

* `tay_clauses_nbhd_aux` — the shape adopted by the repaired interface (`R2b`): the joint
  smoothness is taken on a neighbourhood of the closed angular range;
* `tay_clauses_of_continuous_aux` — the version with the minimal extra hypothesis (continuity of
  the angular slices on `Iθ`), which additionally needs `hE`
  (`Work.FTS.RegPkgGal.R2.integrableOn_pth_slice`).
-/

open MeasureTheory Set Filter Topology
open scoped Topology Real

namespace Work.FTS.RegPkgGal.R2

/-! ## The two repaired packages

Both are stated with the single analytic input `hA` (the angular integral bound, proved as
`Work.FTS.RegPkgGal.R2.angIntegral_le`) as a hypothesis; the unconditional versions are added
below once `angIntegral_le` is available. -/

/-- **The repaired Taylor clauses, in the shape adopted by the repaired interface (`R2b`)**:
the joint `C¹` hypothesis is taken on a neighbourhood of the closed angular range,
`z ∈ (-1, ∞)`, `θ ∈ (-1, π/2+1)`. -/
theorem tay_clauses_nbhd_aux {α S Cθ K Q : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hCθ : 0 ≤ Cθ) (hK : 0 ≤ K) (hQ : 0 ≤ Q) {g : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ τ ∈ Set.Icc 0 S, ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
        (Set.prod (Set.Ioi (-1 : ℝ)) (Set.Ioo (-1 : ℝ) (Real.pi / 2 + 1))))
    (hd : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ|
        ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (Work.FTS.Regularity.gSlice g τ))
    (hquad : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → z ≤ 2 →
      |g z θ τ| ≤ K * z ^ 2)
    (hlinz : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → z ≤ 2 →
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ| ≤ Q * z)
    (hA : ∃ M : ℝ, 0 ≤ M ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
      IntervalIntegrable
          (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
          volume a b ∧
        (∫ θ in a..b, (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
          ≤ M * (b - a) ^ α) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ τ| ≤ K' * z ^ 2) ∧
      (∀ z z' : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 →
        |g z θ τ - g z' θ τ| ≤ K' * max z z' * |z - z'|) ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → ∀ θ' ∈ Work.Spaces.Iθ,
        |g z θ τ - g z θ' τ| ≤ K' * z ^ 2 * |θ - θ'| ^ α) := by
  obtain ⟨M, hM0, hA'⟩ := hA
  refine ⟨max K (max Q (Cθ * M)), le_trans hK (le_max_left _ _), ?_⟩
  intro τ hτ θ hθ
  refine ⟨?_, ?_, ?_⟩
  · intro z hz hz2
    exact le_trans (hquad τ hτ θ hθ z hz hz2)
      (mul_le_mul_of_nonneg_right (le_max_left K (max Q (Cθ * M))) (sq_nonneg z))
  · have hsmw : ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))) :=
      (hsm τ hτ).mono (Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num))
        (Set.Ioo_subset_Ioo (by linarith) (by linarith)))
    have hQK : max Q K ≤ max K (max Q (Cθ * M)) :=
      max_le (le_trans (le_max_left Q (Cθ * M)) (le_max_right K (max Q (Cθ * M))))
        (le_max_left K (max Q (Cθ * M)))
    have hB2 : ∀ {z θ' : ℝ}, 0 < z → θ' ∈ Set.Ioo (0:ℝ) (Real.pi / 2) →
        HasDerivAt (fun s : ℝ => (fun z θ => g z θ τ) s θ')
          (Work.Spaces.pz (fun z θ => g z θ τ) z θ') z :=
      fun hz hθ' => hasDerivAt_slice_pz (f := fun z θ => g z θ τ) hsmw hz hθ'
    exact zClause_aux hQ hQK hsmw (hvt τ hτ) (hquad τ hτ) (hlinz τ hτ) hB2 θ hθ
  · intro z hz hz2 θ' hθ'
    have hM : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
        (∫ θ in a..b, (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
          ≤ M * (b - a) ^ α := fun a b ha hab hb => (hA' a b ha hab hb).2
    have hIntγ : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
        IntervalIntegrable (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
          volume a b := fun a b ha hab hb => (hA' a b ha hab hb).1
    have hd' : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
        |Work.Spaces.Dth (fun z θ => g z θ τ) z θ|
          ≤ Cθ * z ^ 2 * (Real.sin θ * Real.cos θ ^ 2) ^ α :=
      fun z θ hz hθ => hd τ hτ z θ hz hθ
    have hcl := angClause_nbhd hα hCθ hM0 hM hIntγ (hsm τ hτ) hd' z θ θ' hz hz2 hθ hθ'
    calc |g z θ τ - g z θ' τ| ≤ Cθ * M * z ^ 2 * |θ - θ'| ^ α := hcl
      _ ≤ max K (max Q (Cθ * M)) * z ^ 2 * |θ - θ'| ^ α := by
          have hCM : Cθ * M ≤ max K (max Q (Cθ * M)) :=
            le_trans (le_max_right Q (Cθ * M)) (le_max_right K (max Q (Cθ * M)))
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCM (sq_nonneg z))
            (Real.rpow_nonneg (abs_nonneg _) _)

/-- **The repaired Taylor clauses, with the minimal extra hypothesis of continuity of the
angular slices on `Iθ`** (the weakest repair: the smoothness hypothesis `hsm` is left as in the
requested statement, and one adds exactly the information that the counterexample above
violates). -/
theorem tay_clauses_of_continuous_aux {α S Cθ K Q : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hS : 0 < S)
    (hCθ : 0 ≤ Cθ) (hK : 0 ≤ K) (hQ : 0 ≤ Q) {g : ℝ → ℝ → ℝ → ℝ}
    (hsm : ∀ τ ∈ Set.Icc 0 S, ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hd : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ|
        ≤ Cθ * z ^ 2 * Work.FTS.Regularity.Gamma α θ)
    (hvt : ∀ τ ∈ Set.Icc 0 S, Work.Spaces.VanishTheta (Work.FTS.Regularity.gSlice g τ))
    (hquad : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → z ≤ 2 →
      |g z θ τ| ≤ K * z ^ 2)
    (hlinz : ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 ≤ z → z ≤ 2 →
      |Work.Spaces.pz (Work.FTS.Regularity.gSlice g τ) z θ| ≤ Q * z)
    (hcontθ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 < z → z ≤ 2 →
      ContinuousOn (fun θ => g z θ τ) Work.Spaces.Iθ)
    (hA : ∃ M : ℝ, 0 ≤ M ∧ ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
      IntervalIntegrable
          (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
          volume a b ∧
        (∫ θ in a..b, (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
          ≤ M * (b - a) ^ α)
    (hE : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 < z → IntegrableOn
      (fun s : ℝ => Work.Spaces.pth (fun z θ => g z θ τ) z s)
      (Set.Icc 0 (Real.pi / 2)) volume) :
    ∃ K' : ℝ, 0 ≤ K' ∧ ∀ τ ∈ Set.Icc 0 S, ∀ θ ∈ Work.Spaces.Iθ,
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → |g z θ τ| ≤ K' * z ^ 2) ∧
      (∀ z z' : ℝ, 0 ≤ z → z ≤ 2 → 0 ≤ z' → z' ≤ 2 →
        |g z θ τ - g z' θ τ| ≤ K' * max z z' * |z - z'|) ∧
      (∀ z : ℝ, 0 ≤ z → z ≤ 2 → ∀ θ' ∈ Work.Spaces.Iθ,
        |g z θ τ - g z θ' τ| ≤ K' * z ^ 2 * |θ - θ'| ^ α) := by
  obtain ⟨M, hM0, hA'⟩ := hA
  refine ⟨max K (max Q (Cθ * M)), le_trans hK (le_max_left _ _), ?_⟩
  intro τ hτ θ hθ
  refine ⟨?_, ?_, ?_⟩
  · intro z hz hz2
    exact le_trans (hquad τ hτ θ hθ z hz hz2)
      (mul_le_mul_of_nonneg_right (le_max_left K (max Q (Cθ * M))) (sq_nonneg z))
  · have hsmw : ContDiffOn ℝ 1 (Function.uncurry (fun z θ => g z θ τ))
        (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))) := hsm τ hτ
    have hQK : max Q K ≤ max K (max Q (Cθ * M)) :=
      max_le (le_trans (le_max_left Q (Cθ * M)) (le_max_right K (max Q (Cθ * M))))
        (le_max_left K (max Q (Cθ * M)))
    have hB2 : ∀ {z θ' : ℝ}, 0 < z → θ' ∈ Set.Ioo (0:ℝ) (Real.pi / 2) →
        HasDerivAt (fun s : ℝ => (fun z θ => g z θ τ) s θ')
          (Work.Spaces.pz (fun z θ => g z θ τ) z θ') z :=
      fun hz hθ' => hasDerivAt_slice_pz (f := fun z θ => g z θ τ) hsmw hz hθ'
    exact zClause_aux hQ hQK hsmw (hvt τ hτ) (hquad τ hτ) (hlinz τ hτ) hB2 θ hθ
  · intro z hz hz2 θ' hθ'
    rcases eq_or_lt_of_le hz with hz0 | hzpos
    · subst hz0
      have h1 : g 0 θ τ = 0 := by
        have h := hquad τ hτ θ hθ 0 le_rfl (by norm_num : (0:ℝ) ≤ 2)
        have h' : |g 0 θ τ| ≤ 0 := by simpa using h
        exact abs_eq_zero.mp (le_antisymm h' (abs_nonneg _))
      have h2 : g 0 θ' τ = 0 := by
        have h := hquad τ hτ θ' hθ' 0 le_rfl (by norm_num : (0:ℝ) ≤ 2)
        have h' : |g 0 θ' τ| ≤ 0 := by simpa using h
        exact abs_eq_zero.mp (le_antisymm h' (abs_nonneg _))
      rw [h1, h2, sub_zero, abs_zero]
      exact mul_nonneg (mul_nonneg (le_trans hK (le_max_left _ _)) (sq_nonneg 0))
        (Real.rpow_nonneg (abs_nonneg _) _)
    · have hM : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
          (∫ θ in a..b, (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
            ≤ M * (b - a) ^ α := fun a b ha hab hb => (hA' a b ha hab hb).2
      have hIntγ : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ Real.pi / 2 →
          IntervalIntegrable (fun θ : ℝ => (Real.sin θ * Real.cos θ ^ 2) ^ α / Real.sin (2 * θ))
            volume a b := fun a b ha hab hb => (hA' a b ha hab hb).1
      have hE' : ∀ z : ℝ, 0 < z → IntegrableOn
          (fun s : ℝ => Work.Spaces.pth (fun z θ => g z θ τ) z s)
          (Set.Icc 0 (Real.pi / 2)) volume := fun z hz => hE τ hτ z hz
      have hd' : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
          |Work.Spaces.Dth (fun z θ => g z θ τ) z θ|
            ≤ Cθ * z ^ 2 * (Real.sin θ * Real.cos θ ^ 2) ^ α :=
        fun z θ hz hθ => hd τ hτ z θ hz hθ
      have hcontθ' : ∀ z : ℝ, 0 < z → z ≤ 2 →
          ContinuousOn (fun θ => (fun z θ => g z θ τ) z θ) Work.Spaces.Iθ :=
        fun z hz hz2 => hcontθ τ hτ z hz hz2
      have hB1 : ∀ {z θ' : ℝ}, 0 < z → θ' ∈ Set.Ioo (0:ℝ) (Real.pi / 2) →
          HasDerivAt (fun s : ℝ => (fun z θ => g z θ τ) z s)
            (Work.Spaces.pth (fun z θ => g z θ τ) z θ') θ' :=
        fun hz hθ' => hasDerivAt_slice_pth (f := fun z θ => g z θ τ) (hsm τ hτ) hz hθ'
      have hcl := angClause_aux hα hα1 hCθ hM0 hM hIntγ hE' (hsm τ hτ) hd' hcontθ' hB1
        z θ θ' hzpos hz2 hθ hθ'
      calc |g z θ τ - g z θ' τ| ≤ Cθ * M * z ^ 2 * |θ - θ'| ^ α := hcl
        _ ≤ max K (max Q (Cθ * M)) * z ^ 2 * |θ - θ'| ^ α := by
            have hCM : Cθ * M ≤ max K (max Q (Cθ * M)) :=
              le_trans (le_max_right Q (Cθ * M)) (le_max_right K (max Q (Cθ * M)))
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCM (sq_nonneg z))
              (Real.rpow_nonneg (abs_nonneg _) _)

end Work.FTS.RegPkgGal.R2
