import Mathlib.Probability.Distributions.SetBernoulli
import ChallengeDeps
import Submission.SelCore
import Submission.Deep
import Submission.Multi
import Submission.MultiDeep
import Submission.MultiMass
import Submission.MultiAdd
import Submission.MultiW
import Submission.MultiMLM

/-!
# multi-w: the threshold family over size-N multisets admits an (eNμ)-cover of cost ≤ 1/2.

Finite index set Λ of weight functions lam S : X → ℝ.  EsupN := Esup N μ Λ lam.  For
L := Kbig·10^{12} the family Flw := {S ∈ M_N(X) : L·EsupN ≤ sup_{S∈Λ} Σ_x S x·lam S x}
admits a cover 𝓒 with Σ_{G∈𝓒} ∏_x (eN·μx)^{Gx}/(Gx)! ≤ 1/2.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
open Classical
open MeasureTheory ProbabilityTheory Measure unitInterval Finset
open scoped NNReal ENNReal BigOperators

namespace Submission

open _root_.SupremumOfSelectorProcesses

namespace Multi

open MSys

variable {X : Type*} [Fintype X]

/-- the sup is attained over a nonempty finite index family -/
lemma supLam_att {Λ : Finset (X → ℕ)} {lam : (X → ℕ) → X → ℝ} (m : X → ℕ)
    (hne : Λ.Nonempty) : ∃ S ∈ Λ, lamSum lam S m = supLam Λ lam m := by
  classical
  unfold supLam
  have him : (Λ.image (fun S : X → ℕ => lamSum lam S m)).Nonempty := by
    rcases hne with ⟨S, hS⟩
    exact ⟨lamSum lam S m, Finset.mem_image.mpr ⟨S, hS, rfl⟩⟩
  have hm := Finset.max'_mem (Λ.image (fun S : X → ℕ => lamSum lam S m)) him
  rcases (Finset.mem_image).1 hm with ⟨S, hS, hEq⟩
  refine ⟨S, hS, ?_⟩
  simp [him]
  exact hEq

/-- L of Theorem multi-w -/
noncomputable def Lw : ℝ := (Kbig : ℝ) * (10 : ℝ) ^ 12

/-- the threshold family over size-N multisets -/
noncomputable def threshFamily (N : ℕ) (μ : X → ℝ) (Λ : Finset (X → ℕ))
    (lam : (X → ℕ) → X → ℝ) : Finset (X → ℕ) :=
  (msizeExact (X := X) N).filter (fun S : X → ℕ => Lw * Esup (X := X) N μ Λ lam ≤ supLam Λ lam S)

/-- multi-w: the threshold family admits an (eNμ)-cover of cost ≤ 1/2 -/
theorem multi_w (N : ℕ) (μ : X → ℝ) (Λ : Finset (X → ℕ)) (lam : (X → ℕ) → X → ℝ)
    (hNpos : 0 < N) (hμ0 : ∀ x : X, 0 ≤ μ x) (hμ1 : (∑ x : X, μ x) = 1)
    (hlam0 : ∀ S ∈ Λ, ∀ x : X, 0 ≤ lam S x)
    (hEpos : 0 < Esup (X := X) N μ Λ lam) :
    ∃ 𝓒 : Finset (X → ℕ),
      mCover (↑(threshFamily N μ Λ lam) : Set (X → ℕ)) 𝓒 ∧
      mTotalCost (eN N) μ 𝓒 ≤ (2 : ℝ)⁻¹ := by
  classical
  by_contra hcon
  let EsupN : ℝ := Esup (X := X) N μ Λ lam
  let Flw : Finset (X → ℕ) := threshFamily N μ Λ lam
  have hΛne : Λ.Nonempty := by
    by_contra hne0
    have hΛe : Λ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne0
    have hE0 : Esup (X := X) N μ Λ lam = 0 := by
      unfold Esup
      simp [supLam, hΛe]
    linarith
  have hLw : 0 < Lw := by
    unfold Lw Kbig
    norm_num
  have hd : 0 < Lw * EsupN := by
    unfold EsupN
    exact mul_pos hLw hEpos
  let iOf : (X → ℕ) → X → ℕ := fun S => if hS : S ∈ Flw then
      Classical.choose (supLam_att (Λ := Λ) (lam := lam) S hΛne) else fun _ : X => 0
  have iOf_spec : ∀ S : X → ℕ, S ∈ Flw →
      iOf S ∈ Λ ∧ lamSum lam (iOf S) S = supLam Λ lam S := by
    intro S hS
    unfold iOf
    rw [dif_pos hS]
    exact Classical.choose_spec (supLam_att (Λ := Λ) (lam := lam) S hΛne)
  let lamS : (X → ℕ) → X → ℝ :=
    fun S x => (if hS : S ∈ Flw then lam (iOf S) x else 0) / (Lw * EsupN)
  have hlam0S : ∀ S, S ∈ Flw → ∀ x : X, 0 ≤ lamS S x := by
    intro S hS x
    unfold lamS
    rw [dif_pos hS]
    rcases iOf_spec S hS with ⟨hif, _⟩
    have h0 : 0 ≤ lam (iOf S) x := hlam0 (iOf S) hif x
    exact div_nonneg h0 (le_of_lt hd)
  have htot1S : ∀ S : X → ℕ, S ∈ Flw → 1 ≤ lamSum lamS S S := by
    intro S hS
    rcases iOf_spec S hS with ⟨hif, hEq⟩
    have hge0 : Lw * Esup (X := X) N μ Λ lam ≤ supLam Λ lam S := (Finset.mem_filter.mp hS).2
    have hge : Lw * EsupN ≤ lamSum lam (iOf S) S := by
      unfold EsupN at hge0 ⊢
      rwa [hEq]
    calc
      lamSum lamS S S = ∑ x : X, (S x : ℝ) * ((lam (iOf S) x) / (Lw * EsupN)) := by
            unfold lamSum lamS
            apply Finset.sum_congr rfl
            intro x hx
            simp [hS]
      _ = (∑ x : X, (S x : ℝ) * lam (iOf S) x) / (Lw * EsupN) := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = lamSum lam (iOf S) S / (Lw * EsupN) := by rfl
      _ ≥ 1 := by
            change (1 : ℝ) ≤ lamSum lam (iOf S) S / (Lw * EsupN)
            rw [le_div_iff₀ hd]
            simpa using hge
  have hcon' : ¬ mSmall (eN N) μ (Flw : Set (X → ℕ)) := by
    intro hsm
    rcases hsm with ⟨𝓒, hcov, hcost⟩
    exact hcon ⟨𝓒, hcov, hcost⟩
  have hDeep := MSys.multi'_w N μ Flw lamS hμ0 hμ1 hlam0S htot1S hcon'
  -- hDeep : 10^{-11} ≤ Esup (Kbig·N) μ Flw lamS
  have hpoint : ∀ m : X → ℕ, supLam Flw lamS m ≤ supLam Λ lam m / (Lw * EsupN) := by
    intro m
    have hc0 : 0 ≤ supLam Λ lam m / (Lw * EsupN) := by
      exact div_nonneg (supLam_nonneg (Λ := Λ) (lam := lam) (m := m) hlam0) (le_of_lt hd)
    refine supLam_le_of_forall (Λ := Flw) (lam := lamS) (m := m)
      (c := supLam Λ lam m / (Lw * EsupN)) ?_ hc0
    intro S hS
    rcases iOf_spec S hS with ⟨hif, hEq⟩
    have hle : lamSum lam (iOf S) m ≤ supLam Λ lam m := le_supLam (Λ := Λ) m hif
    calc
      lamSum lamS S m = ∑ x : X, (m x : ℝ) * ((lam (iOf S) x) / (Lw * EsupN)) := by
            unfold lamSum lamS
            apply Finset.sum_congr rfl
            intro x hx
            simp [hS]
      _ = (∑ x : X, (m x : ℝ) * lam (iOf S) x) / (Lw * EsupN) := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro x hx
            ring
      _ = lamSum lam (iOf S) m / (Lw * EsupN) := by rfl
      _ ≤ supLam Λ lam m / (Lw * EsupN) := div_le_div_of_nonneg_right hle (le_of_lt hd)
  have hEdeep2 : Esup (X := X) (Kbig * N) μ Flw lamS ≤
      Esup (X := X) (Kbig * N) μ Λ lam / (Lw * EsupN) := by
    unfold Esup
    calc
      (∑ m ∈ msizeExact (X := X) (Kbig * N), mass (X := X) (Kbig * N) μ m * supLam Flw lamS m)
          ≤ (∑ m ∈ msizeExact (X := X) (Kbig * N), mass (X := X) (Kbig * N) μ m * (supLam Λ lam m / (Lw * EsupN))) := by
            apply Finset.sum_le_sum
            intro m hm
            have hm0 : 0 ≤ mass (X := X) (Kbig * N) μ m := mass_nonneg' hμ0 (Kbig * N) m
            exact mul_le_mul_of_nonneg_left (hpoint m) hm0
      _ = (∑ m ∈ msizeExact (X := X) (Kbig * N), mass (X := X) (Kbig * N) μ m * supLam Λ lam m) / (Lw * EsupN) := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro m hm
            ring
  have hadd := Esup_mul_le (X := X) N μ Λ lam hμ0 hμ1 hlam0
  -- hadd : Esup(Kbig·N) ≤ Kbig·Esup N
  have hK1 : (1 : ℝ) ≤ (Kbig : ℝ) := by
    unfold Kbig
    norm_num
  have hlin1 : ((10 : ℝ) ^ 11)⁻¹ * (Lw * EsupN) ≤ Esup (X := X) (Kbig * N) μ Λ lam := by
    have hE : Esup (X := X) (Kbig * N) μ Flw lamS ≤ Esup (X := X) (Kbig * N) μ Λ lam / (Lw * EsupN) := hEdeep2
    have hE2 : Esup (X := X) (Kbig * N) μ Λ lam / (Lw * EsupN) * (Lw * EsupN)
        = Esup (X := X) (Kbig * N) μ Λ lam := by
      exact div_mul_cancel₀ _ (ne_of_gt hd)
    have hD : ((10 : ℝ) ^ 11)⁻¹ ≤ Esup (X := X) (Kbig * N) μ Λ lam / (Lw * EsupN) :=
      le_trans hDeep hE
    have hD2 : ((10 : ℝ) ^ 11)⁻¹ * (Lw * EsupN) ≤ Esup (X := X) (Kbig * N) μ Λ lam / (Lw * EsupN) * (Lw * EsupN) := by
      exact mul_le_mul_of_nonneg_right hD (le_of_lt hd)
    simpa [hE2, mul_assoc] using hD2
  have hlin2 : ((10 : ℝ) ^ 11)⁻¹ * (Lw * EsupN) ≤ (Kbig : ℝ) * EsupN := by
    unfold EsupN at hadd ⊢
    exact le_trans hlin1 hadd
  -- arithmetic contradiction:
  have hc0 : 0 < ((10 : ℝ) ^ 11)⁻¹ := by positivity
  have hineq : ((10 : ℝ) ^ 11)⁻¹ * Lw ≤ (Kbig : ℝ) := by
    -- from hlin2 and hEpos (0 < EsupN): divide by EsupN
    have hE : 0 < EsupN := by unfold EsupN; exact hEpos
    have hd2 : 0 < EsupN := hE
    -- hlin2 : c·(Lw·EsupN) ≤ Kbig·EsupN = (Kbig·?)·EsupN: rewrite: 
    have hlin2' : ((10 : ℝ) ^ 11)⁻¹ * Lw * EsupN ≤ (Kbig : ℝ) * EsupN := by
      simpa [mul_assoc, mul_comm, mul_left_comm] using hlin2
    have hstep : ((10 : ℝ) ^ 11)⁻¹ * Lw ≤ (Kbig : ℝ) := by
      exact le_of_mul_le_mul_right hlin2' hE
    exact hstep
  have hnum : ((10 : ℝ) ^ 11)⁻¹ * Lw = (Kbig : ℝ) * (10 : ℝ) := by
    unfold Lw
    field_simp [show (10 : ℝ) ^ 11 ≠ 0 by positivity]
  rw [hnum] at hineq
  have hbig : (Kbig : ℝ) * (10 : ℝ) ≤ (Kbig : ℝ) := by exact hineq
  have hKpos : (0 : ℝ) < (Kbig : ℝ) := by unfold Kbig; norm_num
  have hbig' : (Kbig : ℝ) * (10 : ℝ) ≤ (Kbig : ℝ) * (1 : ℝ) := by
    simpa using hbig
  have : (10 : ℝ) ≤ 1 := le_of_mul_le_mul_left hbig' hKpos
  norm_num at this

end Multi
end Submission
