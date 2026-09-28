import Mathlib
import Submission.Work.HP.MMDefs
import Submission.Work.HP.Defs
import Submission.Work.HP.BCS.Defs
import Submission.Work.HP.BCS.Setup
import Submission.Work.HP.BCS.Transport
import Submission.Work.HP.BCS.ncard_eq_core
import Submission.Work.HP.BCS.coneSliceVol_eq
import Submission.Work.HP.BCS.ncard_eq_latImage
import Submission.Work.HP.BCS.cone_count_core
import Submission.Work.HP.BCS.small_basis_clean
import Submission.Work.HP.BCS.normDet_PsiOf
import Submission.Work.HP.BCS.layer_grow_le
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.rk_le_card
import Submission.Work.HP.lam_basic

set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

open MeasureTheory

namespace Work.HP.BCS

/-- A uniform choice of the constant supplied by `cone_count_core` at rank `k`; for `k = 0` it is
set to `1` so that the function is everywhere positive. -/
noncomputable def coneCountUniformConst (k : ℕ) : ℝ :=
  if h : 1 ≤ k then Classical.choose (cone_count_core k h) else 1

lemma coneCountUniformConst_pos {k : ℕ} (h : 1 ≤ k) : 0 < coneCountUniformConst k := by
  rw [coneCountUniformConst, dif_pos h]
  exact (Classical.choose_spec (cone_count_core k h)).1

lemma coneCountUniformConst_nonneg (k : ℕ) : 0 ≤ coneCountUniformConst k := by
  by_cases h : 1 ≤ k
  · exact le_of_lt (coneCountUniformConst_pos h)
  · rw [coneCountUniformConst, dif_neg h]; norm_num

/-- The defining property of `coneCountUniformConst`. -/
lemma coneCountUniformConst_spec {k : ℕ} (h : 1 ≤ k) :
    ∀ (Ψ : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)),
      Function.Injective Ψ → ∀ (a b : EuclideanSpace ℝ (Fin k)) (c d T : ℝ),
      0 ≤ c → 0 ≤ d → 1 ≤ T →
      |((({y : EuclideanSpace ℝ (Fin k) | y ∈ latImage Ψ ∧
            y ∈ coneSet a c ∧ y ∈ coneSet b d ∧ ‖y‖ ≤ T}).ncard : ℝ) -
          T ^ k * (volume {y : EuclideanSpace ℝ (Fin k) |
              y ∈ coneSet a c ∧ y ∈ coneSet b d ∧ ‖y‖ ≤ 1}).toReal / Ψ.normDet)|
        ≤ coneCountUniformConst k * (T + cellRad Ψ) ^ (k - 1) * cellRad Ψ / Ψ.normDet := by
  rw [coneCountUniformConst, dif_pos h]
  exact (Classical.choose_spec (cone_count_core k h)).2

theorem ballConeCountEst {ι : Type} [Fintype ι] [DecidableEq ι] :
    ∃ C : ℝ, 0 < C ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (v w : ι → ℝ) (γ T Y : ℝ),
      0 < γ → 1 ≤ rk L → 1 ≤ T → lam L (rk L) ≤ Y → Y ≤ T →
      |(({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ}.ncard : ℝ) -
          T ^ (rk L) / detL L * coneSliceVol L v w γ)|
        ≤ C * T ^ (rk L) / detL L * (Y / T) := by
  classical
  obtain ⟨C₀, hC₀pos, hC₀⟩ := small_basis_clean (ι := ι)
  by_cases hN0 : Fintype.card ι = 0
  · -- degenerate case: no lattice of positive rank exists
    refine ⟨1, one_pos, ?_⟩
    intro L v w γ T Y hγ hk hT hYlam hYT
    exfalso
    have h1 : rk L ≤ Fintype.card ι := rk_le_card L
    omega
  · have hN1 : 1 ≤ Fintype.card ι := Nat.one_le_iff_ne_zero.mpr hN0
    refine ⟨(∑ k ∈ Finset.Icc 1 (Fintype.card ι), coneCountUniformConst k)
        * (1 + C₀) ^ (Fintype.card ι) * C₀, ?_, ?_⟩
    · -- positivity of the uniform constant
      have hSpos : 0 < ∑ k ∈ Finset.Icc 1 (Fintype.card ι), coneCountUniformConst k := by
        have hmem : 1 ∈ Finset.Icc 1 (Fintype.card ι) := by
          rw [Finset.mem_Icc]; exact ⟨le_rfl, hN1⟩
        have hle := Finset.single_le_sum (s := Finset.Icc 1 (Fintype.card ι))
          (f := coneCountUniformConst) (fun j _ => coneCountUniformConst_nonneg j) hmem
        have h1 : 0 < coneCountUniformConst 1 := coneCountUniformConst_pos le_rfl
        linarith
      have hNpos : (0:ℝ) < (1 + C₀) ^ (Fintype.card ι) := pow_pos (by linarith) _
      positivity
    · -- the counting bound
      intro L v w γ T Y hγ hk hT hYlam hYT
      obtain ⟨b, hb⟩ := hC₀ L hk
      set R : ℝ := ∑ i, eNorm ((b i : ι → ℤ)) with hRdef
      have hRnn : 0 ≤ R := by
        rw [hRdef]; exact Finset.sum_nonneg (fun i _ => eNorm_nonneg _)
      have hYnn : 0 ≤ Y := le_trans (le_of_lt (lam_pos L hk le_rfl)) hYlam
      have hRC : R ≤ C₀ * Y := by
        rw [hRdef]
        exact le_trans hb (mul_le_mul_of_nonneg_left hYlam hC₀pos.le)
      have hcγ : 0 ≤ ‖toE v‖ / (2 * γ) := div_nonneg (norm_nonneg _) (by linarith)
      have hdγ : 0 ≤ ‖toE w‖ / (2 * γ) := div_nonneg (norm_nonneg _) (by linarith)
      -- abbreviations for the three big expressions
      set Nc : ℝ :=
        (({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ T ∧ toR a ∈ Cgam v γ ∧ toR a ∈ Cgam w γ}.ncard : ℝ))
        with hNcdef
      set Yc : ℝ :=
        (({y : EuclideanSpace ℝ (Fin (rk L)) | y ∈ latImage (PsiOf L b) ∧
            y ∈ coneSet (coneVec L b v) (‖toE v‖ / (2 * γ)) ∧
            y ∈ coneSet (coneVec L b w) (‖toE w‖ / (2 * γ)) ∧ ‖y‖ ≤ T}.ncard : ℝ))
        with hYcdef
      set Vy : ℝ :=
        ((volume {y : EuclideanSpace ℝ (Fin (rk L)) |
            y ∈ coneSet (coneVec L b v) (‖toE v‖ / (2 * γ)) ∧
            y ∈ coneSet (coneVec L b w) (‖toE w‖ / (2 * γ)) ∧ ‖y‖ ≤ 1}).toReal)
        with hVydef
      -- the core lattice-point count in coordinates
      have hcore := coneCountUniformConst_spec (k := rk L) hk (PsiOf L b) (PsiOf_injective L b)
        (coneVec L b v) (coneVec L b w) (‖toE v‖ / (2 * γ)) (‖toE w‖ / (2 * γ)) T
        hcγ hdγ hT
      rw [normDet_PsiOf L b, cellRad_PsiOf L b, ← hRdef, ← hYcdef, ← hVydef] at hcore
      -- identify the count
      have hN1' := ncard_eq_latImage L b v w γ T
      rw [← hNcdef, ← hYcdef] at hN1'
      -- identify the volume
      have hset : {y : EuclideanSpace ℝ (Fin (rk L)) | ‖y‖ ≤ 1 ∧
            y ∈ coneSet (coneVec L b v) (‖toE v‖ / (2 * γ)) ∧
            y ∈ coneSet (coneVec L b w) (‖toE w‖ / (2 * γ))}
          = {y : EuclideanSpace ℝ (Fin (rk L)) |
            y ∈ coneSet (coneVec L b v) (‖toE v‖ / (2 * γ)) ∧
            y ∈ coneSet (coneVec L b w) (‖toE w‖ / (2 * γ)) ∧ ‖y‖ ≤ 1} := by
        ext y
        simp only [Set.mem_ofPred_eq]
        tauto
      have hV1 : coneSliceVol L v w γ = Vy := by
        rw [hVydef, coneSliceVol_eq L b v w γ]
        exact congrArg (fun s => (volume s).toReal) hset
      have heq2 : T ^ (rk L) / detL L * coneSliceVol L v w γ = T ^ (rk L) * Vy / detL L := by
        rw [hV1]; ring
      -- bound the error growth
      have hS_le : coneCountUniformConst (rk L)
          ≤ ∑ k' ∈ Finset.Icc 1 (Fintype.card ι), coneCountUniformConst k' := by
        have hmem : rk L ∈ Finset.Icc 1 (Fintype.card ι) := by
          rw [Finset.mem_Icc]; exact ⟨hk, rk_le_card L⟩
        exact Finset.single_le_sum (fun j _ => coneCountUniformConst_nonneg j) hmem
      have hd : 0 < detL L := lt_of_lt_of_le zero_lt_one (Work.HP.Lat.detL_ge_one L)
      have hgrow := layer_grow_le (k := rk L) (N := Fintype.card ι)
        (A := coneCountUniformConst (rk L))
        (B := ∑ k' ∈ Finset.Icc 1 (Fintype.card ι), coneCountUniformConst k')
        (C₀ := C₀) (T := T) (Y := Y) (R := R) (d := detL L)
        hk (rk_le_card L) hT hYnn hYT hRnn hRC hC₀pos.le
        (le_of_lt (coneCountUniformConst_pos hk)) hS_le hd
      calc
        |Nc - T ^ (rk L) / detL L * coneSliceVol L v w γ|
            = |Nc - T ^ (rk L) * Vy / detL L| := by rw [heq2]
        _ = |Yc - T ^ (rk L) * Vy / detL L| := by rw [hN1']
        _ ≤ coneCountUniformConst (rk L) * (T + R) ^ (rk L - 1) * R / detL L := hcore
        _ ≤ (∑ k' ∈ Finset.Icc 1 (Fintype.card ι), coneCountUniformConst k')
              * (1 + C₀) ^ (Fintype.card ι) * C₀ * T ^ (rk L) / detL L * (Y / T) := hgrow

end Work.HP.BCS
