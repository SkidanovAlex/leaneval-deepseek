/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`) — node K2, the genericity input
  of the elimination step.

  `ET_good_exists` produces, for a lifted system `E : ETData N (rt+1) n re` with finitely many
  nondegenerate zeros `s` and a proper remaining system `E.psiMap`, a value `y` of `E.psiMap` which
  is *good* (`E.ETGood y`: submersion, regular value on the eliminated equation, null slice of the
  critical values of the Rolle determinant) together with a radius `ρ`, such that

  * the crossing point `E.psiLift y` (the point with `psiMap = y` and eliminated equation `0`) lies
    in the ball of radius `ρ` about `0`, and
  * *every* value `y'` of the square system map `E.map` in that ball has `s.card` preimages.

  The second part is the perturbation form of the inverse function theorem at the nondegenerate
  zeros `s` (`ET_ift_perturbation`); the first part is the analogue for the lifted setting of
  `Work.WilE2.kho_good_exists`:

  * `ETSubm_dense` (from the Sard hypothesis `hsard` at `E.psiMap`) and `ETSubm_bad_closed`
    (properness makes the critical values of `E.psiMap` closed) give that the regular values of
    `E.psiMap` form an open dense set;
  * `ETReg_bad_null` and `ETSlice_bad_null` give that the two remaining "bad" sets are Lebesgue-null.

  A point of the open ball of regular values which avoids the union of the two null sets — which
  exists because the complement of a null set is dense (`Work.WilE2.avoid_null`) — is a good value,
  and the radius of the inverse function theorem is the radius `ρ` of the statement.
-/
import Mathlib
import Submission.Work.WilE3K.ET
import Submission.Work.WilE3K.Elim
import Submission.Work.WilE3K.contDiff_map_and_det
import Submission.Work.WilE2.KhoGood
import Submission.Work.WilE2.kho_good_exists
import Submission.Work.WilE2.KhoCount
import Submission.Work.WilE2.avoid_null
import Submission.Work.WilE3K.ETSubm_dense
import Submission.Work.WilE3K.ETSubm_bad_closed
import Submission.Work.WilE3K.ET_ift_perturbation
import Submission.Work.WilE3K.ETRegSelf
import Submission.Work.WilE3K.ETSliceSelf

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {N rt n re : ℕ}

/-- `E.psiLift y` is the vector `y` with the additional coordinate `0` at the eliminated row
(`E.psiLift_succAbove`, `E.psiLift_lastRow`), hence has the same norm as `y`. -/
theorem dist_psiLift_zero (E : ETData N (rt + 1) n re) (y : Fin N → ℝ) :
    dist (E.psiLift y) 0 = dist y 0 := by
  rw [dist_zero_right, dist_zero_right]
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg y)]
    intro k
    by_cases h : ∃ i : Fin N, Fin.succAbove E.lastRow i = k
    · rw [ETData.psiLift, dif_pos h]
      exact norm_le_pi_norm y (Classical.choose h)
    · rw [ETData.psiLift, dif_neg h]
      simp
  · rw [pi_norm_le_iff_of_nonneg (norm_nonneg (E.psiLift y))]
    intro i
    rw [← E.psiLift_succAbove y i]
    exact norm_le_pi_norm (E.psiLift y) (Fin.succAbove E.lastRow i)

theorem ET_good_exists {N rt n re : ℕ} (E : Work.WilE3K.ETData N (rt + 1) n re)
    (s : Finset (Fin (N + 1) → ℝ)) (hs : ∀ z ∈ s, E.Nondegen z) (hproper : IsProperMap E.psiMap)
    (hsard : ∀ (m : ℕ) (G : (Fin (m + 1) → ℝ) → (Fin m → ℝ)), ContDiff ℝ 2 G →
      ∀ (y₀ : Fin m → ℝ) (ε : ℝ), 0 < ε → ∃ y : Fin m → ℝ, dist y y₀ < ε ∧
        ∀ z, G z = y → LinearIndependent ℝ (fun a => fderiv ℝ (fun w => G w a) z)) :
    ∃ (y : Fin N → ℝ) (ρ : ℝ), E.ETGood y ∧ 0 < ρ ∧
      dist (E.psiLift y) 0 < ρ ∧
      ∀ y' : Fin (N + 1) → ℝ, dist y' 0 < ρ →
        ∃ t : Finset (Fin (N + 1) → ℝ), t.card = s.card ∧ ∀ z ∈ t, E.map z = y' := by
  -- The radius of the inverse function theorem at the nondegenerate zeros `s`.
  obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ := ET_ift_perturbation E s hs
  -- The two null "bad" sets of the genericity bundle.
  have hR : MeasureTheory.volume {y : Fin N → ℝ | ¬ E.ETRegValue y} = 0 :=
    E.ETRegBadNull
  have hS : MeasureTheory.volume {y : Fin N → ℝ | ¬ E.ETSliceNull y} = 0 :=
    ETSliceBadNull E
  have hunion : MeasureTheory.volume
      ({y : Fin N → ℝ | ¬ E.ETRegValue y} ∪ {y : Fin N → ℝ | ¬ E.ETSliceNull y}) = 0 :=
    measure_union_null hR hS
  -- A value of `E.psiMap` which is regular, well inside the inverse function theorem ball.
  obtain ⟨y₂, hy₂, hy₂sub⟩ := ETSubm_dense E hsard 0 (ρ₁ / 2) (by linarith)
  -- The regular values are open (properness + density).
  have hopen : IsOpen {y : Fin N → ℝ | E.ETSubmersion y} := by
    have hcompl : ({y : Fin N → ℝ | ¬ E.ETSubmersion y} : Set (Fin N → ℝ))ᶜ
        = {y : Fin N → ℝ | E.ETSubmersion y} := by
      ext y; simp
    rw [← hcompl]
    exact (ETSubm_bad_closed E hproper).isOpen_compl
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.isOpen_iff.mp hopen y₂ hy₂sub
  have hgap : 0 < ρ₁ / 2 - dist y₂ 0 := by rw [sub_pos]; exact hy₂
  -- Avoid the null bad sets inside that ball.
  obtain ⟨y, hyd, hybad⟩ := Work.WilE2.avoid_null hunion y₂ (lt_min hδpos hgap)
  have hyO : E.ETSubmersion y :=
    hδsub (Metric.mem_ball.mpr (lt_of_lt_of_le hyd (min_le_left _ _)))
  have hydist : dist y 0 < ρ₁ / 2 := by
    have h1 := dist_triangle y y₂ 0
    have h2 : min δ (ρ₁ / 2 - dist y₂ 0) ≤ ρ₁ / 2 - dist y₂ 0 := min_le_right _ _
    linarith
  have hyR : E.ETRegValue y := not_not.mp (fun h => hybad (Or.inl h))
  have hyS : E.ETSliceNull y := not_not.mp (fun h => hybad (Or.inr h))
  refine ⟨y, ρ₁, ⟨hyO, hyR, hyS⟩, hρ₁pos, ?_, ?_⟩
  · rw [dist_psiLift_zero]
    linarith
  · intro y' hy'
    exact hρ₁ y' hy'

end Work.WilE3K
