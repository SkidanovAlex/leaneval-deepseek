import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.GonLib
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.ball_count_schmidt
import Submission.Work.HP.FM.RecDefs
import Submission.Work.HP.FM.latStepAux
import Submission.Work.HP.lat_min_attained
import Submission.Work.HP.Sig2.Recursion
import Submission.Work.HP.Sig2.primBasisExt
import Submission.Work.HP.Sig2.minkowski_prod
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.EEupper.latStepCountB
import Submission.Work.HP.EEupper.RecStep

/-!
# Minkowski's second theorem from the peeling recursion

Assembly of `Work.HP.EEupper.recursionMine` (fibre count + minima comparison + covolume
identity from `Work.EEupper.latCovolStep`) into the product bound

`∏_{j < rk L} λ_{j+1}(L) ≤ K · detL L`

for sublattices `L ⊆ ℤ^ι`, which is the hypothesis `hKmk` of the lattice count.

The covolume identity is taken as an explicit hypothesis `hcov` so that this file does not
depend on the (separately proved) `Work.EEupper.latCovolStep`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace Work.HP.EEupper

open Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The covolume identity of one peeling step, as a hypothesis. -/
abbrev CovStep : Prop :=
  ∀ {R : ℕ} (Φ : LatMap (ι := ι) R) (u : Fin R → ℤ) (v : Fin (R - 1) → (Fin R → ℤ)),
    Function.Bijective (fun c : ℤ × (Fin (R - 1) → ℤ) => c.1 • u + ∑ i, c.2 i • v i) →
    latCovol Φ = ‖Φ (fun k => (u k : ℝ))‖ * latCovol (FM.latStep Φ u v)

/-- **The peeling recursion**, with the covolume identity supplied.  It produces a presentation
`Ψ` of the projected lattice together with the fibre count, the comparison of successive minima
and the covolume relation. -/
theorem recursionMine (hcov : CovStep (ι := ι)) {R : ℕ} (hR : 1 ≤ R)
    (Φ : LatMap (ι := ι) R) (hΦ : Function.Injective Φ) (u : Fin R → ℤ) (hu0 : u ≠ 0)
    (hup : IsPrim u) (hu : ‖Φ (fun i => (u i : ℝ))‖ = latMin Φ 1) :
    ∃ Ψ : LatMap (ι := ι) (R - 1), Function.Injective Ψ ∧
      (∀ T : ℝ, 0 ≤ T → (latCount Φ T : ℝ) ≤
        (2 * T / ‖Φ (fun i => (u i : ℝ))‖ + 1) * (latCount Ψ T : ℝ)) ∧
      (∀ j : ℕ, 1 ≤ j → latMin Φ (j + 1) / 2 ≤ latMin Ψ j) ∧
      latCovol Φ = ‖Φ (fun i => (u i : ℝ))‖ * latCovol Ψ := by
  obtain ⟨v, hv_bij, hv_indep⟩ := Work.HP.Sig2.primBasisExt hR u hup
  let D : FM.RecData R ι := ⟨Φ, u, v, hΦ, hu0, hup, hv_bij, hv_indep⟩
  have hDp : D.p = Φ (fun i => (u i : ℝ)) := rfl
  refine ⟨D.step, D.step_injective, ?_, ?_, ?_⟩
  · intro T hT
    have h := Work.EEupper.latStepCountB D hT
    rwa [hDp] at h
  · intro j hj
    exact latStepMinMine D (by rw [hDp]; exact hu) hj
  · have h := hcov Φ u v hv_bij
    rwa [← hDp] at h

/-! ## The product bound -/

/-- The constant of the recursion: `KcM 0 = 1`, `KcM (n+1) = 2^n * KcM n`. -/
def KcM : ℕ → ℝ
  | 0 => 1
  | (n + 1) => 2 ^ n * KcM n

lemma KcM_succ (n : ℕ) : KcM (n + 1) = 2 ^ n * KcM n := rfl

lemma KcM_pos : ∀ n, 0 < KcM n := by
  intro n
  induction n with
  | zero => norm_num [KcM]
  | succ n ih => rw [KcM_succ]; positivity

lemma KcM_nonneg (n : ℕ) : 0 ≤ KcM n := (KcM_pos n).le

lemma KcM_le_succ (n : ℕ) : KcM n ≤ KcM (n + 1) := by
  rw [KcM_succ]
  have h : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
  nlinarith [KcM_nonneg n]

lemma KcM_mono {m n : ℕ} (h : m ≤ n) : KcM m ≤ KcM n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
      calc KcM m ≤ KcM (m + k) := ih
        _ ≤ KcM (m + k + 1) := KcM_le_succ (m + k)
        _ = KcM (m + (k + 1)) := by rw [Nat.add_assoc]

lemma prod_range_eq_zero_mul_aux {R : ℕ} (hpos : 0 < R) (g : ℕ → ℝ) :
    (∏ j ∈ Finset.range R, g j) = g 0 * ∏ i ∈ Finset.range (R - 1), g (i + 1) := by
  conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
  rw [Finset.prod_range_succ', mul_comm, Nat.pred_eq_sub_one]

/-- Minkowski's second theorem in coefficient space, obtained from the peeling recursion. -/
theorem latMapMinkowskiMine (hcov : CovStep (ι := ι)) :
    ∀ (R : ℕ) (Φ : LatMap (ι := ι) R), Function.Injective Φ →
      (∏ j ∈ Finset.range R, latMin Φ (j + 1)) ≤ KcM R * latCovol Φ := by
  intro R
  induction R using Nat.strong_induction_on with
  | _ R ih =>
    intro Φ hΦ
    rcases Nat.eq_zero_or_pos R with h0 | hpos
    · subst h0
      have h1 : latCovol Φ = 1 := by
        rw [latCovol, Matrix.det_fin_zero, Real.sqrt_one]
      simp [KcM, h1]
    · obtain ⟨u, hu_ne, hu_prim, hu_min⟩ := lat_min_attained hpos Φ hΦ
      obtain ⟨Ψ, hΨinj, hcnt, hminj, hcov'⟩ :=
        recursionMine hcov hpos Φ hΦ u hu_ne hu_prim hu_min
      have hKc : KcM R = 2 ^ (R - 1) * KcM (R - 1) := by
        conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
        rw [KcM_succ, Nat.pred_eq_sub_one]
      have hPg : (∏ j ∈ Finset.range (R - 1), latMin Ψ (j + 1)) ≤ KcM (R - 1) * latCovol Ψ :=
        ih (R - 1) (by omega) Ψ hΨinj
      have hsplit : (∏ j ∈ Finset.range R, latMin Φ (j + 1))
          = latMin Φ 1 * ∏ j ∈ Finset.range (R - 1), latMin Φ (j + 2) :=
        prod_range_eq_zero_mul_aux hpos (fun j => latMin Φ (j + 1))
      rw [hsplit]
      have hstep1 : (∏ j ∈ Finset.range (R - 1), latMin Φ (j + 2))
          ≤ 2 ^ (R - 1) * ∏ j ∈ Finset.range (R - 1), latMin Ψ (j + 1) := by
        calc (∏ j ∈ Finset.range (R - 1), latMin Φ (j + 2))
            ≤ ∏ j ∈ Finset.range (R - 1), (2 * latMin Ψ (j + 1)) := by
              refine Finset.prod_le_prod₀ (fun j _ => latMin_nonneg' Φ _) (fun j _ => ?_)
              have h := hminj (j + 1) (by omega)
              rw [show j + 1 + 1 = j + 2 from by omega] at h
              linarith
          _ = 2 ^ (R - 1) * ∏ j ∈ Finset.range (R - 1), latMin Ψ (j + 1) := by
              rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
      have hstep2 : 2 ^ (R - 1) * (∏ j ∈ Finset.range (R - 1), latMin Ψ (j + 1))
          ≤ 2 ^ (R - 1) * (KcM (R - 1) * latCovol Ψ) :=
        mul_le_mul_of_nonneg_left hPg (by positivity)
      calc latMin Φ 1 * (∏ j ∈ Finset.range (R - 1), latMin Φ (j + 2))
          ≤ latMin Φ 1 * (2 ^ (R - 1) * (KcM (R - 1) * latCovol Ψ)) := by
            refine mul_le_mul_of_nonneg_left ?_ (latMin_nonneg' Φ 1)
            exact hstep1.trans hstep2
        _ = KcM R * latCovol Φ := by rw [← hu_min, hcov', hKc]; ring

/-- **Minkowski's second theorem** (product form) for sublattices of `ℤ^{n+1}`. -/
theorem minkowskiProdMine (n : ℕ) (hcov : CovStep (ι := Fin (n + 1))) :
    ∃ K : ℝ, 0 < K ∧ ∀ L : Submodule ℤ (Fin (n + 1) → ℤ),
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ K * detL L := by
  refine ⟨KcM (Fintype.card (Fin (n + 1))), KcM_pos _, fun L => ?_⟩
  obtain ⟨m, b0⟩ := Submodule.basisOfPid (Pi.basisFun ℤ (Fin (n + 1))) L
  have hn : m = rk L := by
    show m = Module.finrank ℤ L
    rw [Module.finrank_eq_card_basis b0, Fintype.card_fin]
  let b : Module.Basis (Fin (rk L)) ℤ L := b0.reindex (finCongr hn)
  have hΦ : Function.Injective (phiOf (Sig2.vbB b)) := Sig2.phiOf_vbB_injective b
  have hprod : (∏ j ∈ Finset.range (rk L), lam L (j + 1))
      = ∏ j ∈ Finset.range (rk L), latMin (phiOf (Sig2.vbB b)) (j + 1) :=
    Finset.prod_congr rfl fun j _ => Sig2.lam_eq_latMin_b b (j + 1)
  rw [hprod]
  have hmain := latMapMinkowskiMine hcov (rk L) (phiOf (Sig2.vbB b)) hΦ
  rw [Sig2.detL_eq_latCovol_b b]
  calc (∏ j ∈ Finset.range (rk L), latMin (phiOf (Sig2.vbB b)) (j + 1))
      ≤ KcM (rk L) * latCovol (phiOf (Sig2.vbB b)) := hmain
    _ ≤ KcM (Fintype.card (Fin (n + 1))) * latCovol (phiOf (Sig2.vbB b)) :=
        mul_le_mul_of_nonneg_right (KcM_mono (rk_le_card L)) (Sig2.latCovol_nonneg _)

end Work.HP.EEupper
