import Mathlib
import Submission.Work.HP.MMDefs
import Submission.Work.HP.Defs
import Submission.Work.HP.BCS.PsiPub
import Submission.Work.HP.BCS.cone_count_core
import Submission.Work.HP.BCS.small_basis_clean
import Submission.Work.HP.Lat.detL_basis_gram

/-!
# The cone-count estimate `Work.HP.BCS.BallConeCountPub`

For an integral lattice `L ⊆ ℤ^ι` of rank `R ≥ 1`, two real vectors `v`, `w` and `γ, T, Y > 0` with
`λ_R(L) ≤ Y ≤ T`, the number of `a ∈ L` with `eNorm a ≤ T` lying in the two cones
`𝒞_v^{(γ)}`, `𝒞_w^{(γ)}` is

`T^R / det L * coneSliceVol L v w γ + O(T^R / det L * Y / T)`.

The proof transports the count to the coordinate space `ℝ^R` through a `ℤ`-basis `b` of `L`
(`Submission.Work.HP.BCS.PsiPub`), applies the coordinate statement
`Submission.Work.HP.BCS.cone_count_core`, and controls the resulting constant by the
short-basis lemma `Submission.Work.HP.BCS.small_basis_clean`.
-/

set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

open MeasureTheory Finset
open scoped Pointwise Topology

namespace Work.HP.BCS

theorem BallConeCountPub {ι : Type} [Fintype ι] [DecidableEq ι] :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ T Y : ℝ),
      0 < γ → 1 ≤ rk L → 1 ≤ T → lam L (rk L) ≤ Y → Y ≤ T →
      |(({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ}.ncard : ℝ) -
          T ^ (rk L) / detL L * coneSliceVol L v w γ)|
        ≤ C * T ^ (rk L) / detL L * (Y / T) := by
  classical
  obtain ⟨Cb, hCbpos, hCb⟩ := small_basis_clean (ι := ι)
  -- A uniform choice of the constants produced by the coordinate count `cone_count_core`.
  set Cc : ℕ → ℝ := fun k => if h : 1 ≤ k then Classical.choose (cone_count_core k h) else 1
    with hCc
  have hCcpos : ∀ k, 0 < Cc k := by
    intro k
    rw [hCc]
    by_cases h : 1 ≤ k
    · simp only [dif_pos h]
      exact (Classical.choose_spec (cone_count_core k h)).1
    · simp only [dif_neg h]
      norm_num
  have hCcspec : ∀ k (h : 1 ≤ k),
      ∀ (Ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)),
      Function.Injective Ψ → ∀ (a b : EuclideanSpace ℝ (Fin k)) (c d T : ℝ),
      0 ≤ c → 0 ≤ d → 1 ≤ T →
      |((({y : EuclideanSpace ℝ (Fin k) | y ∈ latImage Ψ ∧ y ∈ coneSet a c ∧
            y ∈ coneSet b d ∧ ‖y‖ ≤ T}).ncard : ℝ) -
          T ^ k * (volume {y : EuclideanSpace ℝ (Fin k) | y ∈ coneSet a c ∧
            y ∈ coneSet b d ∧ ‖y‖ ≤ 1}).toReal / Ψ.normDet)|
        ≤ Cc k * (T + cellRad Ψ) ^ (k - 1) * cellRad Ψ / Ψ.normDet := by
    intro k h
    rw [hCc]
    simp only [dif_pos h]
    exact (Classical.choose_spec (cone_count_core k h)).2
  set Ctot : ℝ := ∑ k ∈ Finset.range (Fintype.card ι + 1), Cc k with hCtot
  have hCtotge : ∀ k, k ≤ Fintype.card ι → Cc k ≤ Ctot := by
    intro k hk
    rw [hCtot]
    exact Finset.single_le_sum (fun j _ => (hCcpos j).le)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  have hCtotpos : 0 < Ctot := lt_of_lt_of_le (hCcpos 0) (hCtotge 0 (Nat.zero_le _))
  refine ⟨(Ctot + 1) * (1 + Cb) ^ (Fintype.card ι + 1) * (Cb + 1), ?_, ?_⟩
  · refine mul_pos (mul_pos ?_ ?_) ?_
    · linarith
    · exact pow_pos (by linarith) _
    · linarith
  intro L v w γ T Y hγ hrk1 hT1 hlam hYT
  obtain ⟨b, hb⟩ := hCb L hrk1
  have hc0 : 0 ≤ ‖toE v‖ / (2 * γ) := div_nonneg (norm_nonneg _) (by linarith)
  have hd0 : 0 ≤ ‖toE w‖ / (2 * γ) := div_nonneg (norm_nonneg _) (by linarith)
  have hcore := hCcspec (rk L) hrk1 (pPsiOf L b) (pPsiOf_injective L b) (pConeVec L b v)
    (pConeVec L b w) (‖toE v‖ / (2 * γ)) (‖toE w‖ / (2 * γ)) T hc0 hd0 hT1
  -- Rewrite the coordinate statement into the lattice data.
  have hmain : |(({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T ∧ toR a ∈ Cgam v γ ∧
          toR a ∈ Cgam w γ}.ncard : ℝ) - T ^ (rk L) / detL L * coneSliceVol L v w γ)|
      ≤ Cc (rk L) * (T + cellRad (pPsiOf L b)) ^ (rk L - 1) * cellRad (pPsiOf L b) / detL L := by
    rw [pNormDet_pPsiOf L b] at hcore
    rw [← pConeVol L b v w γ, ← pNcard_core L b v w γ T] at hcore
    have harg : (({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T ∧ toR a ∈ Cgam v γ ∧
            toR a ∈ Cgam w γ}.ncard : ℝ) - T ^ (rk L) * coneSliceVol L v w γ / detL L)
        = (({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T ∧ toR a ∈ Cgam v γ ∧
            toR a ∈ Cgam w γ}.ncard : ℝ) - T ^ (rk L) / detL L * coneSliceVol L v w γ) := by
      ring
    rw [harg] at hcore
    exact hcore
  -- The arithmetic.
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT1
  have hY0 : 0 ≤ Y := le_trans (lam_nonneg L (rk L)) hlam
  have hdetpos : 0 < detL L := by
    rw [← pNormDet_pPsiOf L b]
    refine lt_of_le_of_ne (LinearMap.normDet_nonneg _) (fun h => ?_)
    exact (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mp h.symm)
      (LinearMap.ker_eq_bot.mpr (pPsiOf_injective L b))
  have hRnn : 0 ≤ cellRad (pPsiOf L b) := cellRad_nonneg _
  have hRle : cellRad (pPsiOf L b) ≤ Cb * Y := by
    rw [pCellRad_pPsiOf L b]
    exact le_trans hb (mul_le_mul_of_nonneg_left hlam hCbpos.le)
  have hTR : T + cellRad (pPsiOf L b) ≤ (1 + Cb) * T := by
    have h2 : Cb * Y ≤ Cb * T := mul_le_mul_of_nonneg_left hYT hCbpos.le
    linarith
  have hkcard : rk L ≤ Fintype.card ι := by
    rw [rk]
    calc Module.finrank ℤ L ≤ Module.finrank ℤ (ι → ℤ) := Submodule.finrank_le L
      _ = Fintype.card ι := Module.finrank_fintype_fun_eq_card ℤ
  have hMnn : 0 ≤ (1 + Cb) ^ (Fintype.card ι + 1) := pow_nonneg (by linarith) _
  have hTk1 : 0 ≤ T ^ (rk L - 1) := pow_nonneg hT0.le _
  have hpowb : (T + cellRad (pPsiOf L b)) ^ (rk L - 1)
      ≤ (1 + Cb) ^ (rk L - 1) * T ^ (rk L - 1) := by
    have h1 : (T + cellRad (pPsiOf L b)) ^ (rk L - 1) ≤ ((1 + Cb) * T) ^ (rk L - 1) :=
      pow_le_pow_left₀ (by linarith) hTR _
    rwa [mul_pow] at h1
  have hCc_le : Cc (rk L) ≤ Ctot := hCtotge (rk L) hkcard
  have hPow_le : (1 + Cb) ^ (rk L - 1) ≤ (1 + Cb) ^ (Fintype.card ι + 1) :=
    pow_le_pow_right₀ (by linarith) (by omega)
  have hstep1 : Cc (rk L) * (T + cellRad (pPsiOf L b)) ^ (rk L - 1) * cellRad (pPsiOf L b)
      ≤ Cc (rk L) * ((1 + Cb) ^ (rk L - 1) * T ^ (rk L - 1)) * (Cb * Y) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hpowb (hCcpos _).le) hRle hRnn
      (mul_nonneg (hCcpos _).le (mul_nonneg (pow_nonneg (by linarith) _) hTk1))
  have hstep2 : Cc (rk L) * ((1 + Cb) ^ (rk L - 1) * T ^ (rk L - 1)) * (Cb * Y)
      = Cc (rk L) * (1 + Cb) ^ (rk L - 1) * Cb * (T ^ (rk L - 1) * Y) := by ring
  have hstep3 : Cc (rk L) * (1 + Cb) ^ (rk L - 1) * Cb
      ≤ (Ctot + 1) * (1 + Cb) ^ (Fintype.card ι + 1) * (Cb + 1) := by
    have h1 : Cc (rk L) * (1 + Cb) ^ (rk L - 1)
        ≤ Ctot * (1 + Cb) ^ (Fintype.card ι + 1) :=
      mul_le_mul hCc_le hPow_le (pow_nonneg (by linarith) _) hCtotpos.le
    refine le_trans (mul_le_mul h1 (by linarith : Cb ≤ Cb + 1) hCbpos.le
      (mul_nonneg hCtotpos.le hMnn)) ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : Ctot ≤ Ctot + 1) hMnn) (by linarith)
  have hkey : Cc (rk L) * (T + cellRad (pPsiOf L b)) ^ (rk L - 1) * cellRad (pPsiOf L b)
      ≤ ((Ctot + 1) * (1 + Cb) ^ (Fintype.card ι + 1) * (Cb + 1)) * (T ^ (rk L - 1) * Y) :=
    le_trans hstep1 (le_trans (le_of_eq hstep2)
      (mul_le_mul_of_nonneg_right hstep3 (mul_nonneg hTk1 hY0)))
  have hTY : T ^ (rk L) * (Y / T) = T ^ (rk L - 1) * Y := by
    have hTne : T ≠ 0 := ne_of_gt hT0
    have hmul : T * (Y * T⁻¹) = Y := by
      rw [mul_comm Y T⁻¹, mul_inv_cancel_left₀ hTne Y]
    have hTk : T ^ (rk L) = T ^ (rk L - 1) * T := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hTk, div_eq_mul_inv, mul_assoc, hmul]
  calc |(({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T ∧ toR a ∈ Cgam v γ ∧
          toR a ∈ Cgam w γ}.ncard : ℝ) - T ^ (rk L) / detL L * coneSliceVol L v w γ)|
      ≤ Cc (rk L) * (T + cellRad (pPsiOf L b)) ^ (rk L - 1) * cellRad (pPsiOf L b) / detL L :=
        hmain
    _ ≤ ((Ctot + 1) * (1 + Cb) ^ (Fintype.card ι + 1) * (Cb + 1)) *
          (T ^ (rk L - 1) * Y) / detL L := div_le_div_of_nonneg_right hkey hdetpos.le
    _ = (Ctot + 1) * (1 + Cb) ^ (Fintype.card ι + 1) * (Cb + 1) *
          T ^ (rk L) / detL L * (Y / T) := by
        rw [← hTY]
        ring

end Work.HP.BCS
