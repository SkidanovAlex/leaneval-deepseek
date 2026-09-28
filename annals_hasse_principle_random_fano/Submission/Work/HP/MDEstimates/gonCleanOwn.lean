import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.GonLib
import Submission.Work.HP.lam_basic
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.Sig2.Recursion
import Submission.Work.HP.phiOf_injective
import Submission.Work.HP.Sig2.schmidt_bound
import Submission.Work.HP.Sig2.minkowski_prod
import Submission.Work.HP.BCS.small_basis_clean
import Submission.Work.HP.Lat.detL_ge_one
import Submission.Work.HP.MDEstimates.latBallVolumeGon
import Submission.Work.HP.MDEstimates.latBallSandwichGon

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP.MDEstimates

/-! ## Local copies of elementary helpers (avoiding the `MMDefs`/`BCSDefs` clash) -/
/-- The volume of the Euclidean unit ball is nonnegative. -/
lemma ballVol_nonneg_local (k : ℕ) : 0 ≤ ballVol k := by
  rw [ballVol]
  exact ENNReal.toReal_nonneg

/-- The value of `phiOf` on a standard basis vector. -/
lemma phiOf_single_local {ι : Type*} [Fintype ι] [DecidableEq ι] {R : ℕ} (v : Fin R → (ι → ℤ)) (i : Fin R) :
    phiOf v (Pi.single i (1:ℝ)) = WithLp.toLp 2 (fun k => ((v i) k : ℝ)) := by
  rw [← WithLp.toLp_ofLp (p := 2) (phiOf v (Pi.single i (1:ℝ)))]
  congr 1
  funext k
  rw [WithLp.ofLp_toLp, phiOf_apply]
  simp [Pi.single_apply]


lemma powDiffUp (T D : ℝ) (hT : 0 ≤ T) (hD : 0 ≤ D) (n : ℕ) :
    (T + D) ^ (n + 1) - T ^ (n + 1) ≤ ((n : ℝ) + 1) * D * (T + D) ^ n := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h : (T + D) ^ (m + 2) - T ^ (m + 2)
        = (T + D) * ((T + D) ^ (m + 1) - T ^ (m + 1)) + D * T ^ (m + 1) := by ring
    rw [h]
    have h2 : (T + D) * ((T + D) ^ (m + 1) - T ^ (m + 1)) ≤
        (T + D) * (((m : ℝ) + 1) * D * (T + D) ^ m) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    have h3 : D * T ^ (m + 1) ≤ D * (T + D) ^ (m + 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT (by linarith) (m + 1)) hD
    have h5 : (T + D) * ((T + D) ^ (m + 1) - T ^ (m + 1)) + D * T ^ (m + 1) ≤
        (T + D) * (((m : ℝ) + 1) * D * (T + D) ^ m) + D * (T + D) ^ (m + 1) :=
      add_le_add h2 h3
    have h6 : (T + D) * (((m : ℝ) + 1) * D * (T + D) ^ m) + D * (T + D) ^ (m + 1)
        = (((m + 1 : ℕ) : ℝ) + 1) * D * (T + D) ^ (m + 1) := by push_cast; ring
    exact h5.trans (le_of_eq h6)

lemma powDiffDown (T D : ℝ) (hD : 0 ≤ D) (hDT : D ≤ T) (n : ℕ) :
    T ^ (n + 1) - (T - D) ^ (n + 1) ≤ ((n : ℝ) + 1) * D * T ^ n := by
  have h := powDiffUp (T - D) D (by linarith) hD n
  rwa [sub_add_cancel] at h




/-- Arithmetic core of the `gon` estimate: given an upper bound `N ≤ v (T+μ)^R / d` and the
matching lower bound `v (T-μ)^R / d ≤ N` when `μ ≤ T`, together with `μ ≤ (C/2)Y` and `Y ≤ T`,
the value `N` is within a controlled multiple of `v T^(R-1) Y / d` from `v T^R / d`.

The upper bound uses `(T+μ)^R - T^R ≤ R μ (T+μ)^(R-1)`, the lower bound (case `μ ≤ T`) uses
`T^R - (T-μ)^R ≤ R μ T^(R-1)`, and in the remaining case `μ > T` one simply drops `N ≥ 0`
and uses `T < (C/2) Y ≤ K0 Y`. -/
theorem gonArithOwn {R : ℕ} (hR : 1 ≤ R) {v d N T Y μ C : ℝ} (hv : 0 ≤ v) (hd : 0 < d)
    (hN : 0 ≤ N) (hT : 1 ≤ T) (hY : 0 < Y) (hμ : 0 ≤ μ) (hC : 0 < C)
    (hμCY : μ ≤ (C / 2) * Y) (hYT : Y ≤ T)
    (hA : N ≤ v * (T + μ) ^ R / d) (hB : μ ≤ T → v * (T - μ) ^ R / d ≤ N) :
    |N - v * T ^ R / d| ≤ v * (R * (C / 2) * (1 + C / 2) ^ (R - 1) + C ^ R + C / 2 + 1)
      * (T ^ (R - 1) * Y / d) := by
  have hTpos : 0 < T := by linarith
  have hTnn : 0 ≤ T := hTpos.le
  have hYnn : 0 ≤ Y := hY.le
  have hC2nn : 0 ≤ C / 2 := by linarith
  have hc1 : 1 ≤ 1 + C / 2 := by linarith
  have h1Cnn : 0 ≤ 1 + C / 2 := by linarith
  have hR1 : R - 1 + 1 = R := Nat.succ_pred_eq_of_pos hR
  have hcast : (((R - 1 : ℕ)) : ℝ) + 1 = (R : ℝ) := by
    have h : (((R - 1 : ℕ)) : ℝ) + 1 = (((R - 1 + 1 : ℕ)) : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one]
    rw [h, hR1]
  have hTR : T ^ R = T ^ (R - 1) * T := by rw [← pow_succ]; congr 1; omega
  have hT0 : 0 ≤ T ^ (R - 1) := pow_nonneg hTnn _
  have hZnn : 0 ≤ T ^ (R - 1) * Y := mul_nonneg hT0 hYnn
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = (R : ℝ) * (C / 2) * (1 + C / 2) ^ (R - 1) := ⟨_, rfl⟩
  have hKnn : 0 ≤ K := by
    rw [hKdef]; exact mul_nonneg (mul_nonneg (Nat.cast_nonneg R) hC2nn) (pow_nonneg h1Cnn _)
  obtain ⟨K0, hK0def⟩ : ∃ K0 : ℝ, K0 = K + C ^ R + C / 2 + 1 := ⟨_, rfl⟩
  have hCRpos : 0 < C ^ R := pow_pos hC R
  have hK_le_K0 : K ≤ K0 := by rw [hKdef, hK0def]; linarith [hCRpos, hC2nn]
  have hC2_le_K0 : C / 2 ≤ K0 := by rw [hK0def]; linarith [hKnn, hCRpos.le]
  obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = v * (T ^ (R - 1) * Y / d) := ⟨_, rfl⟩
  have hVnn : 0 ≤ V := by
    rw [hVdef]; exact mul_nonneg hv (div_nonneg hZnn hd.le)
  have hTRmu : T + μ ≤ (1 + C / 2) * T := by
    have h2 : μ ≤ (C / 2) * T := le_trans hμCY (mul_le_mul_of_nonneg_left hYT hC2nn)
    nlinarith
  have hexp : (T + μ) ^ (R - 1) ≤ (1 + C / 2) ^ (R - 1) * T ^ (R - 1) := by
    calc (T + μ) ^ (R - 1) ≤ ((1 + C / 2) * T) ^ (R - 1) :=
          pow_le_pow_left₀ (by linarith) hTRmu _
      _ = (1 + C / 2) ^ (R - 1) * T ^ (R - 1) := by rw [mul_pow]
  have hP : (T + μ) ^ R - T ^ R ≤ K * (T ^ (R - 1) * Y) := by
    have hps := powDiffUp T μ hTnn hμ (R - 1)
    rw [hcast, hR1] at hps
    have hmu_term : μ * (T + μ) ^ (R - 1) ≤ (C / 2) * Y * ((1 + C / 2) ^ (R - 1) * T ^ (R - 1)) :=
      mul_le_mul hμCY hexp (pow_nonneg (by linarith) _) (mul_nonneg hC2nn hYnn)
    have hmain : (R : ℝ) * μ * (T + μ) ^ (R - 1) ≤ K * (T ^ (R - 1) * Y) := by
      calc (R : ℝ) * μ * (T + μ) ^ (R - 1) = (R : ℝ) * (μ * (T + μ) ^ (R - 1)) := by ring
        _ ≤ (R : ℝ) * ((C / 2) * Y * ((1 + C / 2) ^ (R - 1) * T ^ (R - 1))) :=
              mul_le_mul_of_nonneg_left hmu_term (Nat.cast_nonneg R)
        _ = K * (T ^ (R - 1) * Y) := by rw [hKdef]; ring
    linarith [hps, hmain]
  have hQ : μ ≤ T → T ^ R - (T - μ) ^ R ≤ K * (T ^ (R - 1) * Y) := by
    intro hμT
    have hps := powDiffDown T μ hμ hμT (R - 1)
    rw [hcast, hR1] at hps
    have hb : (1 : ℝ) ≤ (1 + C / 2) ^ (R - 1) := one_le_pow₀ hc1
    have hann : 0 ≤ (R : ℝ) * (C / 2) := mul_nonneg (Nat.cast_nonneg R) hC2nn
    have hstep : (R : ℝ) * μ * T ^ (R - 1) ≤ (R : ℝ) * (C / 2) * (T ^ (R - 1) * Y) := by
      have h1 : μ * T ^ (R - 1) ≤ (C / 2) * Y * T ^ (R - 1) :=
        mul_le_mul_of_nonneg_right hμCY hT0
      calc (R : ℝ) * μ * T ^ (R - 1) = (R : ℝ) * (μ * T ^ (R - 1)) := by ring
        _ ≤ (R : ℝ) * ((C / 2) * Y * T ^ (R - 1)) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg R)
        _ = (R : ℝ) * (C / 2) * (T ^ (R - 1) * Y) := by ring
    have hstep2 : (R : ℝ) * (C / 2) * (T ^ (R - 1) * Y) ≤ K * (T ^ (R - 1) * Y) := by
      calc (R : ℝ) * (C / 2) * (T ^ (R - 1) * Y) = ((R : ℝ) * (C / 2)) * (T ^ (R - 1) * Y) := by ring
        _ ≤ ((R : ℝ) * (C / 2) * (1 + C / 2) ^ (R - 1)) * (T ^ (R - 1) * Y) :=
              mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hann hb) hZnn
        _ = K * (T ^ (R - 1) * Y) := by rw [hKdef]
    linarith [hps, hstep, hstep2]
  have hupper : N - v * T ^ R / d ≤ K0 * V := by
    have h1 : N - v * T ^ R / d ≤ v * ((T + μ) ^ R - T ^ R) / d := by
      have heq : v * (T + μ) ^ R / d - v * T ^ R / d = v * ((T + μ) ^ R - T ^ R) / d := by
        rw [div_sub_div_same]; ring
      linarith [hA, heq]
    have h2 : v * ((T + μ) ^ R - T ^ R) / d ≤ K0 * V := by
      have h3 : v * ((T + μ) ^ R - T ^ R) / d ≤ v * (K * (T ^ (R - 1) * Y)) / d :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hP hv) hd.le
      have h4 : v * (K * (T ^ (R - 1) * Y)) / d = K * V := by
        rw [hVdef, div_eq_mul_inv]; ring
      have h5 : K * V ≤ K0 * V := mul_le_mul_of_nonneg_right hK_le_K0 hVnn
      linarith [h3, h4, h5]
    linarith [h1, h2]
  have hlower : -(K0 * V) ≤ N - v * T ^ R / d := by
    by_cases hμT : μ ≤ T
    · have hb : v * (T - μ) ^ R / d ≤ N := hB hμT
      have h1 : v * T ^ R / d - N ≤ v * (T ^ R - (T - μ) ^ R) / d := by
        have heq : v * T ^ R / d - v * (T - μ) ^ R / d = v * (T ^ R - (T - μ) ^ R) / d := by
          rw [div_sub_div_same]; ring
        rw [← heq]; linarith
      have h2 : v * (T ^ R - (T - μ) ^ R) / d ≤ K0 * V := by
        have h3 : v * (T ^ R - (T - μ) ^ R) / d ≤ v * (K * (T ^ (R - 1) * Y)) / d :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hQ hμT) hv) hd.le
        have h4 : v * (K * (T ^ (R - 1) * Y)) / d = K * V := by
          rw [hVdef, div_eq_mul_inv]; ring
        have h5 : K * V ≤ K0 * V := mul_le_mul_of_nonneg_right hK_le_K0 hVnn
        linarith [h3, h4, h5]
      linarith [h1, h2]
    · have hμT' : T < μ := not_le.mp hμT
      have hTY : T ≤ K0 * Y := by
        have h1 : T < (C / 2) * Y := lt_of_lt_of_le hμT' hμCY
        have h2 : (C / 2) * Y ≤ K0 * Y := mul_le_mul_of_nonneg_right hC2_le_K0 hYnn
        linarith
      have h3 : v * T ^ R / d ≤ K0 * V := by
        rw [hTR]
        have hZv : 0 ≤ v * T ^ (R - 1) / d := div_nonneg (mul_nonneg hv hT0) hd.le
        calc v * (T ^ (R - 1) * T) / d = (v * T ^ (R - 1) / d) * T := by
              rw [div_eq_mul_inv]; ring
          _ ≤ (v * T ^ (R - 1) / d) * (K0 * Y) := mul_le_mul_of_nonneg_left hTY hZv
          _ = K0 * V := by rw [hVdef, div_eq_mul_inv]; ring
      linarith [hN, h3]
  have habs : |N - v * T ^ R / d| ≤ K0 * V := abs_le.mpr ⟨hlower, hupper⟩
  have hfin : K0 * V = v * (R * (C / 2) * (1 + C / 2) ^ (R - 1) + C ^ R + C / 2 + 1)
      * (T ^ (R - 1) * Y / d) := by
    rw [hVdef, hK0def, hKdef]; ring
  rw [hfin] at habs
  exact habs



variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The arithmetic conversion from Schmidt's product to the Schmidt sum

`Work.HP.Sig2.schmidt_bound` bounds `#(L ∩ B(T))` by a constant times
`∏_{i<rk L} (T/λ_i + 1)`, while the target statement is phrased with the sum
`∑_{k} T^k/(λ_1⋯λ_k)`.  The following two lemmas are the required conversion, proved
by induction on the rank; they are self-contained (only `lam_pos`/`lam_mono` are used). -/

/-- The elementary convolution step: the sum `S_R = ∑_{k=0}^{R} T^k/(λ_1⋯λ_k)` satisfies
`S_R · (T/λ_{R+1} + 1) ≤ 2 · S_{R+1}`. -/
theorem convStepSum (L : Submodule ℤ (ι → ℤ)) {T : ℝ} (hT : 1 ≤ T) {R : ℕ}
    (hR : R + 1 ≤ rk L) :
    ((Finset.range (R + 1)).sum (fun k => T ^ k / (Finset.range k).prod (fun i => lam L (i + 1))))
      * (T / lam L (R + 1) + 1) ≤
    2 * ((Finset.range (R + 2)).sum (fun k => T ^ k / (Finset.range k).prod (fun i => lam L (i + 1)))) := by
  classical
  have hPpos : ∀ k, k ≤ R + 1 → 0 < (Finset.range k).prod (fun i => lam L (i + 1)) := by
    intro k hk
    exact Finset.prod_pos (fun i hi => lam_pos L (by omega)
      (by have := Finset.mem_range.mp hi; omega))
  have hterm : ∀ k, k ≤ R →
      (T ^ k / (Finset.range k).prod (fun i => lam L (i + 1))) * (T / lam L (R + 1))
        ≤ T ^ (k + 1) / (Finset.range (k + 1)).prod (fun i => lam L (i + 1)) := by
    intro k hk
    have hPk : 0 < (Finset.range k).prod (fun i => lam L (i + 1)) := hPpos k (by omega)
    have hmono : lam L (k + 1) ≤ lam L (R + 1) := lam_mono L (by omega) hR
    have hprod : (Finset.range (k + 1)).prod (fun i => lam L (i + 1))
        = (Finset.range k).prod (fun i => lam L (i + 1)) * lam L (k + 1) :=
      Finset.prod_range_succ _ _
    rw [hprod]
    rw [div_mul_div_comm, ← pow_succ]
    exact div_le_div_of_nonneg_left (pow_nonneg (by linarith) _)
      (by
        have hlk : 0 < lam L (k + 1) := lam_pos L (by omega) (by omega)
        positivity)
      (mul_le_mul_of_nonneg_left hmono hPk.le)
  have hsum : ((Finset.range (R + 1)).sum
        (fun k => (T ^ k / (Finset.range k).prod (fun i => lam L (i + 1))) * (T / lam L (R + 1))))
      ≤ (Finset.range (R + 2)).sum (fun k => T ^ k / (Finset.range k).prod (fun i => lam L (i + 1))) := by
    have h1 : (Finset.range (R + 1)).sum
          (fun k => (T ^ k / (Finset.range k).prod (fun i => lam L (i + 1))) * (T / lam L (R + 1)))
        ≤ (Finset.range (R + 1)).sum
          (fun k => T ^ (k + 1) / (Finset.range (k + 1)).prod (fun i => lam L (i + 1))) :=
      Finset.sum_le_sum (fun k hk => hterm k (by have := Finset.mem_range.mp hk; omega))
    have h2 : (Finset.range (R + 1)).sum
          (fun k => T ^ (k + 1) / (Finset.range (k + 1)).prod (fun i => lam L (i + 1)))
        = (Finset.range (R + 2)).sum (fun k => T ^ k / (Finset.range k).prod (fun i => lam L (i + 1)))
          - T ^ 0 / (Finset.range 0).prod (fun i => lam L (i + 1)) := by
      have h := Finset.sum_range_succ'
        (fun k => T ^ k / (Finset.range k).prod (fun i => lam L (i + 1))) (R + 1)
      linarith
    have h3 : (0:ℝ) ≤ T ^ 0 / (Finset.range 0).prod (fun i => lam L (i + 1)) := by
      simp
    linarith
  have hBle : (Finset.range (R + 1)).sum (fun k => T ^ k / (Finset.range k).prod (fun i => lam L (i + 1)))
      ≤ (Finset.range (R + 2)).sum (fun k => T ^ k / (Finset.range k).prod (fun i => lam L (i + 1))) := by
    have hsplit : (Finset.range (R + 2)).sum (fun k => T ^ k / (Finset.range k).prod (fun i => lam L (i + 1)))
        = (Finset.range (R + 1)).sum (fun k => T ^ k / (Finset.range k).prod (fun i => lam L (i + 1)))
          + T ^ (R + 1) / (Finset.range (R + 1)).prod (fun i => lam L (i + 1)) := by
      rw [Finset.sum_range_succ]
    rw [hsplit]
    have : (0:ℝ) ≤ T ^ (R + 1) / (Finset.range (R + 1)).prod (fun i => lam L (i + 1)) :=
      div_nonneg (pow_nonneg (by linarith) _) (hPpos (R + 1) le_rfl).le
    linarith
  have hmain : ((Finset.range (R + 1)).sum (fun k => T ^ k / (Finset.range k).prod (fun i => lam L (i + 1))))
        * (T / lam L (R + 1) + 1)
      = ((Finset.range (R + 1)).sum
            (fun k => (T ^ k / (Finset.range k).prod (fun i => lam L (i + 1))) * (T / lam L (R + 1))))
        + (Finset.range (R + 1)).sum (fun k => T ^ k / (Finset.range k).prod (fun i => lam L (i + 1))) := by
    rw [mul_add, mul_one, Finset.sum_mul]
  rw [hmain]
  linarith [hsum, hBle]

/-- `∏_{i=1}^{R} (T/λ_i + 1) ≤ 2^R · ∑_{k=0}^{R} T^k/(λ_1⋯λ_k)`, for `R ≤ rk L` and `T ≥ 1`. -/
theorem convStepProd (L : Submodule ℤ (ι → ℤ)) {T : ℝ} (hT : 1 ≤ T) :
    ∀ R : ℕ, R ≤ rk L →
      (∏ i ∈ Finset.range R, (T / lam L (i + 1) + 1)) ≤
        2 ^ R * (Finset.range (R + 1)).sum
          (fun k => T ^ k / (Finset.range k).prod (fun i => lam L (i + 1))) := by
  intro R
  induction R with
  | zero =>
      intro _
      simp
  | succ R ih =>
      intro hR
      have hR' : R ≤ rk L := by omega
      have ihR := ih hR'
      have hnonneg : 0 ≤ T / lam L (R + 1) + 1 := by
        have hpos : 0 < lam L (R + 1) := lam_pos L (by omega) hR
        have : 0 ≤ T / lam L (R + 1) := div_nonneg (by linarith) hpos.le
        linarith
      rw [Finset.prod_range_succ]
      calc (∏ i ∈ Finset.range R, (T / lam L (i + 1) + 1)) * (T / lam L (R + 1) + 1)
          ≤ (2 ^ R * (Finset.range (R + 1)).sum
                (fun k => T ^ k / (Finset.range k).prod (fun i => lam L (i + 1))))
              * (T / lam L (R + 1) + 1) := mul_le_mul_of_nonneg_right ihR hnonneg
        _ = 2 ^ R * (((Finset.range (R + 1)).sum
                (fun k => T ^ k / (Finset.range k).prod (fun i => lam L (i + 1))))
              * (T / lam L (R + 1) + 1)) := by ring
        _ ≤ 2 ^ R * (2 * ((Finset.range (R + 2)).sum
                (fun k => T ^ k / (Finset.range k).prod (fun i => lam L (i + 1))))) :=
              mul_le_mul_of_nonneg_left (convStepSum L hT hR) (by positivity)
        _ = 2 ^ (R + 1) * (Finset.range (R + 2)).sum
                (fun k => T ^ k / (Finset.range k).prod (fun i => lam L (i + 1))) := by
              rw [pow_succ]; ring

/-! ## The main theorem -/
theorem gonCleanOwn (ι : Type) [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)) (T Y : ℝ), 1 ≤ rk L → 1 ≤ T →
      ((ballCount L T : ℝ) ≤ K * ∑ i ∈ Finset.range (rk L + 1),
          T ^ (rk L - i) / ∏ j ∈ Finset.range (rk L - i), lam L (j + 1)) ∧
      (lam L (rk L) ≤ Y → Y ≤ T →
        |(ballCount L T : ℝ) - ballVol (rk L) * T ^ rk L / detL L|
          ≤ K * T ^ rk L / detL L * (Y / T)) := by
  classical
  obtain ⟨Ks, hKspos, hKs⟩ := Work.HP.Sig2.schmidt_bound (ι := ι)
  obtain ⟨C, hCpos, hC⟩ := Work.HP.BCS.small_basis_clean (ι := ι)
  -- the three constants
  set Svol : ℝ := ∑ R ∈ Finset.range (Fintype.card ι + 1), (ballVol R + 1) with hSvoldef
  set A : ℝ := (Fintype.card ι : ℝ) * (C / 2 + 1) * (1 + C / 2) ^ (Fintype.card ι)
      + (C + 1) ^ (Fintype.card ι) + (C / 2) + 1 with hAdef
  set K1 : ℝ := Ks * 2 ^ (Fintype.card ι) with hK1def
  set K2 : ℝ := Svol * A + 1 with hK2def
  have hSvolnn : 0 ≤ Svol := by
    rw [hSvoldef]
    exact Finset.sum_nonneg fun R _ => by linarith [ballVol_nonneg_local R]
  have hAnn : 0 ≤ A := by
    rw [hAdef]
    have h1 : (0:ℝ) ≤ (Fintype.card ι : ℝ) * (C / 2 + 1) * (1 + C / 2) ^ (Fintype.card ι) := by
      positivity
    have h2 : (0:ℝ) ≤ (C + 1) ^ (Fintype.card ι) := by positivity
    have h3 : (0:ℝ) ≤ C / 2 := by linarith
    linarith
  have hK1nn : 0 ≤ K1 := by rw [hK1def]; positivity
  have hK2nn : 0 ≤ K2 := by rw [hK2def]; positivity
  refine ⟨K1 + K2 + 1, by linarith, ?_⟩
  intro L T Y hL hT
  constructor
  · -- ## First conjunct: Schmidt's bound in sum form
    have hsch := hKs L T hT
    have hprod := convStepProd (ι := ι) L hT (rk L) le_rfl
    have hsum_nn : 0 ≤ ∑ k ∈ Finset.range (rk L + 1),
        T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) := by
      refine Finset.sum_nonneg (fun k hk => ?_)
      refine div_nonneg (pow_nonneg (by linarith) k) ?_
      exact Finset.prod_nonneg (fun i _ => lam_nonneg L (i + 1))
    have hrefl : (∑ i ∈ Finset.range (rk L + 1),
          T ^ (rk L - i) / ∏ j ∈ Finset.range (rk L - i), lam L (j + 1))
        = ∑ k ∈ Finset.range (rk L + 1), T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) := by
      have h := Finset.sum_range_reflect
        (fun k => T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1)) (rk L + 1)
      simp only [Nat.add_sub_cancel] at h
      exact h
    rw [hrefl]
    have hpow : (2:ℝ) ^ (rk L) ≤ 2 ^ (Fintype.card ι) :=
      pow_le_pow_right₀ (by norm_num) (rk_le_card L)
    calc (ballCount L T : ℝ)
        ≤ Ks * ∏ i ∈ Finset.range (rk L), (T / lam L (i + 1) + 1) := hsch
      _ ≤ Ks * (2 ^ (rk L) * ∑ k ∈ Finset.range (rk L + 1),
            T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1)) :=
          mul_le_mul_of_nonneg_left hprod hKspos.le
      _ = (Ks * 2 ^ (rk L)) * ∑ k ∈ Finset.range (rk L + 1),
            T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) := by ring
      _ ≤ K1 * ∑ k ∈ Finset.range (rk L + 1),
            T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) := by
          apply mul_le_mul_of_nonneg_right _ hsum_nn
          rw [hK1def]
          exact mul_le_mul_of_nonneg_left hpow hKspos.le
      _ ≤ (K1 + K2 + 1) * ∑ k ∈ Finset.range (rk L + 1),
            T ^ k / ∏ i ∈ Finset.range k, lam L (i + 1) := by
          apply mul_le_mul_of_nonneg_right _ hsum_nn
          linarith
  · -- ## Second conjunct: the asymptotic count
    intro hYR hYT
    obtain ⟨b, hb⟩ := hC L hL
    set Φ : LatMap (ι := ι) (rk L) := phiOf (fun i => (b i : ι → ℤ)) with hΦdef
    have hv : LinearIndependent ℤ (fun i => (b i : ι → ℤ)) :=
      b.linearIndependent.map' (Submodule.subtype L) (Submodule.ker_subtype L)
    have hΦinj : Function.Injective Φ := by rw [hΦdef]; exact phiOf_injective _ hv
    have hbc : ballCount L T = latCount Φ T := by rw [hΦdef]; exact Sig2Rec.ballCount_eq_latCount b T
    have hdet : detL L = latCovol Φ := by rw [hΦdef]; exact Sig2.detL_eq_latCovol_b b
    have hdetpos : 0 < detL L := lt_of_lt_of_le zero_lt_one (Lat.detL_ge_one L)
    have hcovpos : 0 < latCovol Φ := by rw [← hdet]; exact hdetpos
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
    have hTnn : 0 ≤ T := hTpos.le
    have hYpos : 0 < Y := lt_of_lt_of_le (lam_pos L hL le_rfl) hYR
    have hYnn : 0 ≤ Y := hYpos.le
    -- the covering radius `μ = (1/2) Σ ‖Φ e_i‖ = (1/2) Σ ‖b_i‖`
    set μ : ℝ := (1/2) * ∑ i, eNorm (b i : ι → ℤ) with hμdef
    have hμnn : 0 ≤ μ := by
      rw [hμdef]
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => eNorm_nonneg _))
    have hμle : μ ≤ (C / 2) * Y := by
      rw [hμdef]
      have h1 : ∑ i, eNorm (b i : ι → ℤ) ≤ C * lam L (rk L) := hb
      have h2 : C * lam L (rk L) ≤ C * Y := mul_le_mul_of_nonneg_left hYR hCpos.le
      linarith
    have hμsum : (1 / 2) * ∑ i, ‖Φ (Pi.basisFun ℝ (Fin (rk L)) i)‖ ≤ μ := by
      rw [hμdef]
      have hsum : ∑ i, ‖Φ (Pi.basisFun ℝ (Fin (rk L)) i)‖
          = ∑ i, eNorm (b i : ι → ℤ) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hΦdef, Pi.basisFun_apply, phiOf_single_local]
        exact norm_toLp _
      rw [hsum]
    -- the two-sided sandwich
    have hsand_u := (latBallSandwichGon Φ hΦinj T μ hTnn hμsum).1
    have hsand_l := (latBallSandwichGon Φ hΦinj T μ hTnn hμsum).2
    -- and the volume of the two balls
    have hA : (latCount Φ T : ℝ) ≤ ballVol (rk L) * (T + μ) ^ (rk L) / detL L := by
      rw [hdet]
      have hS : 0 ≤ T + μ := by linarith
      have hvol : (MeasureTheory.volume {x : Fin (rk L) → ℝ | ‖Φ x‖ ≤ T + μ}).toReal
          = ballVol (rk L) * (T + μ) ^ (rk L) / latCovol Φ := by
        rw [latBallVolumeGon hL Φ hΦinj (T + μ) hS]
        exact ENNReal.toReal_ofReal (div_nonneg
          (mul_nonneg (ballVol_nonneg_local _) (pow_nonneg hS _)) hcovpos.le)
      rw [← hvol]
      exact hsand_u
    have hB : μ ≤ T → ballVol (rk L) * (T - μ) ^ (rk L) / detL L ≤ (latCount Φ T : ℝ) := by
      intro hμT
      rw [hdet]
      have hS : 0 ≤ T - μ := by linarith
      have hvol : (MeasureTheory.volume {x : Fin (rk L) → ℝ | ‖Φ x‖ ≤ T - μ}).toReal
          = ballVol (rk L) * (T - μ) ^ (rk L) / latCovol Φ := by
        rw [latBallVolumeGon hL Φ hΦinj (T - μ) hS]
        exact ENNReal.toReal_ofReal (div_nonneg
          (mul_nonneg (ballVol_nonneg_local _) (pow_nonneg hS _)) hcovpos.le)
      rw [← hvol]
      exact hsand_l
    -- the purely arithmetic two-sided estimate
    have hmain := gonArithOwn (R := rk L) (v := ballVol (rk L)) (d := detL L)
      (N := (latCount Φ T : ℝ)) (T := T) (Y := Y) (μ := μ) (C := C)
      hL (ballVol_nonneg_local _) hdetpos (Nat.cast_nonneg _) hT hYpos hμnn hCpos hμle hYT hA hB
    -- the constant is dominated by `K2`
    have hstuff_le : (rk L : ℝ) * (C / 2) * (1 + C / 2) ^ (rk L - 1) ≤
        (Fintype.card ι : ℝ) * (C / 2 + 1) * (1 + C / 2) ^ (Fintype.card ι) := by
      have hbase : (1:ℝ) ≤ 1 + C / 2 := by linarith
      have hRle : rk L ≤ Fintype.card ι := rk_le_card L
      have h1 : (1 + C / 2) ^ (rk L - 1) ≤ (1 + C / 2) ^ (Fintype.card ι) :=
        pow_le_pow_right₀ hbase (by omega)
      have hCn : (0:ℝ) ≤ C / 2 := by linarith
      have hRc : (rk L : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hRle
      have hle1 : (rk L : ℝ) * (C / 2) ≤ (Fintype.card ι : ℝ) * (C / 2 + 1) := by
        have h2 : (C / 2) ≤ C / 2 + 1 := by linarith
        calc (rk L : ℝ) * (C / 2) ≤ (Fintype.card ι : ℝ) * (C / 2) :=
              mul_le_mul_of_nonneg_right hRc hCn
          _ ≤ (Fintype.card ι : ℝ) * (C / 2 + 1) :=
              mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)
      calc (rk L : ℝ) * (C / 2) * (1 + C / 2) ^ (rk L - 1)
          ≤ ((Fintype.card ι : ℝ) * (C / 2 + 1)) * (1 + C / 2) ^ (Fintype.card ι) :=
            mul_le_mul hle1 h1 (pow_nonneg (by linarith) _) (by positivity)
        _ = (Fintype.card ι : ℝ) * (C / 2 + 1) * (1 + C / 2) ^ (Fintype.card ι) := by ring
    have hCpow_le : C ^ (rk L) ≤ (C + 1) ^ (Fintype.card ι) := by
      have h1 : C ^ (rk L) ≤ (C + 1) ^ (rk L) :=
        pow_le_pow_left₀ (by linarith) (by linarith) _
      exact le_trans h1 (pow_le_pow_right₀ (by linarith) (rk_le_card L))
    have hsumA : (rk L : ℝ) * (C / 2) * (1 + C / 2) ^ (rk L - 1) + C ^ (rk L) + C / 2 + 1 ≤ A := by
      rw [hAdef]
      linarith [hstuff_le, hCpow_le]
    have hSvol_le : ballVol (rk L) ≤ Svol := by
      rw [hSvoldef]
      have hmem : rk L ∈ Finset.range (Fintype.card ι + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le (rk_le_card L))
      have h := Finset.single_le_sum (f := fun R => ballVol R + 1)
        (fun R _ => by linarith [ballVol_nonneg_local R]) hmem
      linarith
    have hbound : ballVol (rk L) *
          ((rk L : ℝ) * (C / 2) * (1 + C / 2) ^ (rk L - 1) + C ^ (rk L) + C / 2 + 1) ≤ K2 := by
      rw [hK2def]
      have hsumAnn : (0:ℝ) ≤
          (rk L : ℝ) * (C / 2) * (1 + C / 2) ^ (rk L - 1) + C ^ (rk L) + C / 2 + 1 := by
        have hCn : (0:ℝ) ≤ C / 2 := by linarith
        have hk : (0:ℝ) ≤ (rk L : ℝ) := Nat.cast_nonneg _
        positivity
      have := mul_le_mul hSvol_le hsumA hsumAnn hSvolnn
      linarith
    have hXnn : 0 ≤ T ^ (rk L - 1) * Y / detL L :=
      div_nonneg (mul_nonneg (pow_nonneg hTnn _) hYnn) hdetpos.le
    have hfinal : |(latCount Φ T : ℝ) - ballVol (rk L) * T ^ (rk L) / detL L|
        ≤ K2 * (T ^ (rk L - 1) * Y / detL L) :=
      le_trans hmain (mul_le_mul_of_nonneg_right hbound hXnn)
    have hbcR : (ballCount L T : ℝ) = (latCount Φ T : ℝ) := by rw [hbc]
    rw [hbcR]
    have hconv : (K1 + K2 + 1) * T ^ (rk L) / detL L * (Y / T)
        = (K1 + K2 + 1) * (T ^ (rk L - 1) * Y / detL L) := by
      have hTR : T ^ (rk L) = T ^ (rk L - 1) * T := by rw [← pow_succ]; congr 1; omega
      rw [hTR]
      field_simp
    rw [hconv]
    exact le_trans hfinal (mul_le_mul_of_nonneg_right (by linarith [hK1nn]) hXnn)

end Work.HP.MDEstimates
