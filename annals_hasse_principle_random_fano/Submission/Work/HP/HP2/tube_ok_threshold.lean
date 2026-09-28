import Mathlib
import Submission.Work.HP.PFCountDefs
import Submission.Work.HP.bigW_le_pow
import Submission.Work.HP.HP2.tube_ratio_le
import Submission.Work.HP.HP2.log_rpow_threshold

noncomputable section
open Filter MeasureTheory

namespace Work.HP.HP2

/-- **Tube condition for all large `T`.** `TubeOk` (in `Submission.Work.HP.PFCountDefs`) is the
hypothesis of `grid_coset_lower`: the `8(n+1)W`-neighbourhood of the frontier of the cone region of
radius `T` has volume at most half the volume of the region.

Given the two established ingredient bounds
* `hfront` (`Work.HP.HP2.frontier_tube_le`): `vol(tube of frontier at radius ρ) ≤
   T^{n+1} Cfront ((ρ/T)^{1/Ksub} + ρ/T)`, and
* `hcone` (`Work.HP.HP2.cone_region_lower`): for real-soluble `a`, `vol(coneRegion T) ≥ c T^{n+1}/α^n`,

produce a threshold `W(w(B)) (log B)^m κ` above which `TubeOk` holds, where `W = bigW (wOf B)`,
`α = log B` and the tube radius is `ρ = 8(n+1)W`.  Combining the two bounds reduces the claim to
`Cfront((ρ/T)^{1/Ksub}+ρ/T) ≤ c/(2α^n)`, which holds once `T ≥ W (log B)^m κ` with `κ ≥ 8(n+1)`
chosen so that `ρ/T ≤ (log B)^{-m/Ksub}` and `m` large enough that
`Cfront ((log B)^{-m/Ksub} + (log B)^{-m}) (log B)^n ≤ c/2` for large `B` (e.g. any `m` with
`m/Ksub > n` works; `m` is existentially quantified here), while `A₀ ≥ e` ensures `log B ≥ 1`.
The conclusion asserts `1 ≤ κ` (not merely `κ > 0`): this is what the downstream application needs
in order to know the threshold satisfies `W (log B)^m κ ≥ 1`, and it is achieved by `κ ≥ 8(n+1) ≥ 1`. -/
theorem tube_ok_threshold (d n : ℕ)
    (Cfront ccone Ksub : ℝ) (hCfront : 0 < Cfront) (hKsub : 0 < Ksub) (hccone : 0 < ccone)
    (hfront : ∀ (a : Work.HP.Mon d n → ℤ) (α T ρ : ℝ),
      a ≠ 0 → 1 ≤ α → 1 ≤ T → 0 < ρ → ρ ≤ T →
      (MeasureTheory.volume {x : Fin (n + 1) → ℝ |
          ∃ y ∈ frontier (Work.HP.coneRegion d n a α T), Work.HP.rNorm (x - y) ≤ ρ}).toReal
        ≤ T ^ (n + 1) * Cfront * (Real.rpow (ρ / T) (1 / Ksub) + ρ / T))
    (hcone : ∀ (a : Work.HP.Mon d n → ℤ) (α R : ℝ),
      Work.HP.RealSol d n a → 1 ≤ α → 1 ≤ R →
      ccone * R ^ (n + 1) / α ^ n ≤
        (MeasureTheory.volume (Work.HP.coneRegion d n a α R)).toReal) :
    ∃ m : ℕ, ∃ κ A₀ : ℝ, 1 ≤ κ ∧ 1 ≤ A₀ ∧
      ∀ B : ℝ, A₀ ≤ B → ∀ (a : Work.HP.Mon d n → ℤ) (T : ℝ),
        a ≠ 0 → Work.HP.RealSol d n a → 1 ≤ T →
        (Work.HP.bigW (Work.HP.wOf B) : ℝ) * (Real.log B) ^ m * κ ≤ T →
        Work.HP.TubeOk d n a (Real.log B) T (Work.HP.bigW (Work.HP.wOf B) : ℝ) := by
  obtain ⟨m, hnm, A₀, hA₀exp, hA₀bound⟩ :=
    log_rpow_threshold n Cfront ccone Ksub hCfront hKsub hccone
  have hm1 : 1 ≤ m := by omega
  set κ : ℝ := max 1 (8 * ((n : ℝ) + 1)) with hκdef
  have hκ1 : 1 ≤ κ := le_max_left _ _
  have hκ8 : 8 * ((n : ℝ) + 1) ≤ κ := le_max_right _ _
  refine ⟨m, κ, A₀, hκ1, le_trans (Real.one_le_exp zero_le_one) hA₀exp, ?_⟩
  intro B hB a T ha hsol hT1 hThresh
  have hBexp : Real.exp 1 ≤ B := le_trans hA₀exp hB
  set L : ℝ := Real.log B with hLdef
  have hL1 : 1 ≤ L := by
    have h := Real.log_le_log (Real.exp_pos 1) hBexp
    rw [Real.log_exp] at h
    simpa [hLdef] using h
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  set W : ℝ := (Work.HP.bigW (Work.HP.wOf B) : ℝ) with hWdef
  have hW1 : 1 ≤ W := by
    rw [hWdef]
    exact_mod_cast Work.HP.one_le_bigW (Work.HP.wOf B)
  have hWpos : 0 < W := lt_of_lt_of_le zero_lt_one hW1
  have hThr : W * L ^ m * κ ≤ T := by
    simpa only [← hLdef, ← hWdef] using hThresh
  have hρpos : 0 < 8 * ((n : ℝ) + 1) * W := by positivity
  have hρT : 8 * ((n : ℝ) + 1) * W ≤ T := by
    have hLm : 1 ≤ L ^ m := one_le_pow₀ hL1
    have h8 : 8 * ((n : ℝ) + 1) ≤ L ^ m * κ := by
      have h1 : (1 : ℝ) * (8 * ((n : ℝ) + 1)) ≤ L ^ m * κ :=
        mul_le_mul hLm hκ8 (by positivity) (pow_nonneg hLpos.le m)
      simpa using h1
    calc 8 * ((n : ℝ) + 1) * W = W * (8 * ((n : ℝ) + 1)) := by ring
      _ ≤ W * (L ^ m * κ) := mul_le_mul_of_nonneg_left h8 hWpos.le
      _ = W * L ^ m * κ := by ring
      _ ≤ T := hThr
  obtain ⟨hρle, hρrpow⟩ := tube_ratio_le (n := n) (m := m) (κ := κ) (Ksub := Ksub)
      (W := W) (L := L) (T := T) hKsub hWpos hκ1 hκ8 hL1 hm1 hThr
  have hfr := hfront a L T (8 * ((n : ℝ) + 1) * W) ha hL1 hT1 hρpos hρT
  have hco := hcone a L T hsol hL1 hT1
  have hfac : (0 : ℝ) ≤ T ^ (n + 1) * Cfront :=
    mul_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ T) (n + 1)) hCfront.le
  have step1 : (volume {x : Fin (n + 1) → ℝ |
        ∃ y ∈ frontier (coneRegion d n a L T), rNorm (x - y) ≤ 8 * ((n : ℝ) + 1) * W}).toReal
      ≤ T ^ (n + 1) * Cfront * (L ^ (-((m : ℝ) / Ksub)) + L ^ (-(m : ℝ))) := by
    refine le_trans hfr ?_
    have hsum : Real.rpow ((8 * ((n : ℝ) + 1) * W) / T) (1 / Ksub)
          + (8 * ((n : ℝ) + 1) * W) / T
        ≤ L ^ (-((m : ℝ) / Ksub)) + L ^ (-(m : ℝ)) :=
      add_le_add hρrpow hρle
    exact mul_le_mul_of_nonneg_left hsum hfac
  have hTp : (0 : ℝ) ≤ T ^ (n + 1) := pow_nonneg (by linarith : (0 : ℝ) ≤ T) (n + 1)
  have step2 : T ^ (n + 1) * Cfront * (L ^ (-((m : ℝ) / Ksub)) + L ^ (-(m : ℝ)))
      ≤ (1 / 2) * (ccone * T ^ (n + 1) / L ^ n) := by
    have hC : Cfront * (L ^ (-((m : ℝ) / Ksub)) + L ^ (-(m : ℝ))) * L ^ n ≤ ccone / 2 := by
      simpa only [← hLdef] using hA₀bound B hB
    have hLnpos : 0 < L ^ n := pow_pos hLpos n
    have hC' : Cfront * (L ^ (-((m : ℝ) / Ksub)) + L ^ (-(m : ℝ)))
        ≤ (ccone / 2) * (L ^ n)⁻¹ := by
      have h2 : Cfront * (L ^ (-((m : ℝ) / Ksub)) + L ^ (-(m : ℝ))) * L ^ n
          ≤ ((ccone / 2) * (L ^ n)⁻¹) * L ^ n := by
        have hR : ((ccone / 2) * (L ^ n)⁻¹) * L ^ n = ccone / 2 := by
          rw [mul_assoc, inv_mul_cancel₀ (ne_of_gt hLnpos), mul_one]
        rw [hR]; exact hC
      exact le_of_mul_le_mul_right h2 hLnpos
    calc T ^ (n + 1) * Cfront * (L ^ (-((m : ℝ) / Ksub)) + L ^ (-(m : ℝ)))
        = T ^ (n + 1) * (Cfront * (L ^ (-((m : ℝ) / Ksub)) + L ^ (-(m : ℝ)))) := by ring
      _ ≤ T ^ (n + 1) * ((ccone / 2) * (L ^ n)⁻¹) := mul_le_mul_of_nonneg_left hC' hTp
      _ = (1 / 2) * (ccone * T ^ (n + 1) / L ^ n) := by ring
  have hfinal : (volume {x : Fin (n + 1) → ℝ |
        ∃ y ∈ frontier (coneRegion d n a L T), rNorm (x - y) ≤ 8 * ((n : ℝ) + 1) * W}).toReal
      ≤ (1 / 2) * (volume (coneRegion d n a L T)).toReal := by
    have h2 : (1 / 2) * (ccone * T ^ (n + 1) / L ^ n)
        ≤ (1 / 2) * (volume (coneRegion d n a L T)).toReal :=
      mul_le_mul_of_nonneg_left hco (by norm_num)
    exact le_trans step1 (le_trans step2 h2)
  unfold Work.HP.TubeOk
  exact hfinal

end Work.HP.HP2
