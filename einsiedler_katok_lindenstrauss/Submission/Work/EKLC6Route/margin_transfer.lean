import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Route.dev_estimates
import Submission.Work.EKLC6Route.dev_conj_aDiag_pow_le
import Submission.Work.EKLC6Route.uminus_inv_dev_le
import Submission.Work.EKLC6Route.BigCellAux
import Submission.Work.EKLC6Core.coding_calculus

noncomputable section

namespace Work.EKLC6Route

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract Work.EKLC6Core Work.EKLComp
open Classical

variable {μ : MeasureTheory.Measure X3} {t : Fin 3 → ℝ}

theorem dev_nonneg (g : SL3) : 0 ≤ dev g := le_trans (abs_nonneg _) (abs_dev_entry g 0 0)

/-- `lamExp t > 0`: the minimal contraction exponent of `aDiag t` is positive. -/
theorem lamExp_pos (t : Fin 3 → ℝ) : 0 < lamExp t := by
  rw [lamExp, Finset.lt_inf'_iff]
  rintro ⟨i, j⟩ -
  by_cases h : t i < t j
  · simp only [h, ↓reduceIte]; linarith
  · simp only [h, ↓reduceIte]; norm_num

theorem mem_chart_iff (w : Window μ t) (x : X3) :
    x ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ ↔
      w.uc x ∈ Uball (Uminus t) (2 * w.r) ∧ w.θ x ∈ VtSet t ∩ V w.ρ ∧
        (w.uc x * w.θ x) • w.z0 = x := Iff.rfl

theorem dU_of_mem (w : Window μ t) {z : X3}
    (hz : z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ) :
    w.dU z = |dev (w.uc z) - w.r| := by
  rw [Window.dU, if_pos hz]

theorem dU_of_not_mem (w : Window μ t) {z : X3}
    (hz : z ∉ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ) :
    w.dU z = w.r := by
  rw [Window.dU, if_neg hz]

theorem dU_le_r (w : Window μ t) (z : X3) : w.dU z ≤ w.r := by
  by_cases hz : z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ
  · rw [dU_of_mem w hz, abs_le]
    have hd : dev (w.uc z) < 2 * w.r := (mem_V_iff_dev_lt (w.uc z) (2 * w.r)).mp hz.1.2
    have hd0 : 0 ≤ dev (w.uc z) := dev_nonneg _
    constructor <;> linarith
  · rw [dU_of_not_mem w hz]

theorem dU_nonneg (w : Window μ t) (z : X3) : 0 ≤ w.dU z := by
  by_cases hz : z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ
  · rw [dU_of_mem w hz]; exact abs_nonneg _
  · rw [dU_of_not_mem w hz]; exact w.hr.le

/-! ## `V δ`-membership helpers used in the injectivity argument -/

/-- `dev (s * k) < δ` when `s ∈ Uball (Uminus t) (2r)` and `k ∈ VtSet t ∩ V ρ`. -/
theorem dev_mul_lt_delta_of_ball (w : Window μ t) {s : SL3}
    (hs : s ∈ Uball (Uminus t) (2 * w.r)) {k : SL3} (hk : k ∈ VtSet t ∩ V w.ρ) :
    dev (s * k) < w.δ := by
  have hr : 0 < w.r := w.hr
  have hρ : 0 < w.ρ := w.hρ
  have hδ : 0 < w.δ := w.hδ
  have hδ1 : w.δ ≤ 1 / 100 := w.hδ1
  have hs' : dev s < 2 * w.r := (mem_V_iff_dev_lt s (2 * w.r)).mp hs.2
  have hk' : dev k < w.ρ := (mem_V_iff_dev_lt k w.ρ).mp hk.2
  have hk0 : 0 ≤ dev k := dev_nonneg k
  have h1 : w.r ≤ w.δ / 4000 := by linarith [w.hrδ]
  have h2 : w.ρ ≤ w.δ / 4000 := by linarith [w.hρδ]
  have hnum : 2 * w.r + w.ρ + 3 * (2 * w.r) * w.ρ < w.δ := by
    nlinarith [h1, h2, hr, hρ, hδ, hδ1]
  have hm := dev_mul_le s k
  have hsk : 3 * dev s * dev k ≤ 3 * (2 * w.r) * w.ρ := by
    have h0 : 0 ≤ (2 : ℝ) * w.r := by linarith
    have hlt : dev s * dev k ≤ (2 * w.r) * w.ρ := mul_le_mul hs'.le hk'.le hk0 h0
    linarith [hlt]
  linarith [hm, hs'.le, hk'.le, hsk, hnum]

/-- `dev (v * s * k) < δ` when `v ∈ Uminus t` with `8 dev v ≤ r`, `s ∈ Uball (Uminus t) (2r)`
and `k ∈ VtSet t ∩ V ρ`. -/
theorem dev_uminus_mul_lt_delta (w : Window μ t) {v s k : SL3}
    (he : 8 * dev v ≤ w.r)
    (hs : s ∈ Uball (Uminus t) (2 * w.r)) (hk : k ∈ VtSet t ∩ V w.ρ) :
    dev (v * s * k) < w.δ := by
  have hr : 0 < w.r := w.hr
  have hρ : 0 < w.ρ := w.hρ
  have hδ : 0 < w.δ := w.hδ
  have hδ1 : w.δ ≤ 1 / 100 := w.hδ1
  have he0 : 0 ≤ dev v := dev_nonneg v
  have hs' : dev s < 2 * w.r := (mem_V_iff_dev_lt s (2 * w.r)).mp hs.2
  have hk' : dev k < w.ρ := (mem_V_iff_dev_lt k w.ρ).mp hk.2
  have hk0 : 0 ≤ dev k := dev_nonneg k
  have h1 : w.r ≤ w.δ / 4000 := by linarith [w.hrδ]
  have h2 : w.ρ ≤ w.δ / 4000 := by linarith [w.hρδ]
  have hr6 : 6 * w.r ≤ 1 := by linarith [w.hrδ, w.hδ1]
  have hvs : dev (v * s) ≤ 2 * w.r + 2 * dev v := by
    have h := dev_mul_le v s
    have hmul : dev v * dev s ≤ dev v * (2 * w.r) :=
      mul_le_mul_of_nonneg_left hs'.le he0
    have h6e : 6 * w.r * dev v ≤ dev v := by nlinarith [hr6, he0]
    nlinarith [h, hmul, h6e, he0, hs'.le]
  have hvs' : dev (v * s) ≤ 9 / 4 * w.r := by nlinarith [hvs, he]
  have hvs0 : 0 ≤ dev (v * s) := dev_nonneg _
  have hnum : 9 / 4 * w.r + w.ρ + 3 * (9 / 4 * w.r) * w.ρ < w.δ := by
    nlinarith [h1, h2, hr, hρ, hδ, hδ1]
  have hm := dev_mul_le (v * s) k
  have hsk : 3 * dev (v * s) * dev k ≤ 3 * (9 / 4 * w.r) * w.ρ := by
    have h0 : 0 ≤ (9 : ℝ) / 4 * w.r := by linarith
    have hlt : dev (v * s) * dev k ≤ (9 / 4 * w.r) * w.ρ := mul_le_mul hvs' hk'.le hk0 h0
    linarith [hlt]
  linarith [hm, hvs', hk'.le, hsk, hnum]

/-! ## The pointwise margin transfer -/

/-- **Margin transfer across a small `Uminus t`-translation.**  If `v ∈ Uminus t` is small
relative to `dU z` and `r` (`8 dev v < min (dU z) r`), left multiplication by `v` lowers `dU` by
at most `4 dev v`. -/
theorem dU_smul_lower (w : Window μ t) {z : X3} {v : SL3}
    (hv : v ∈ Uminus t)
    (hsmall : 8 * dev v < min (w.dU z) w.r) :
    w.dU z - 4 * dev v ≤ w.dU (v • z) := by
  have hr : 0 < w.r := w.hr
  have hρ : 0 < w.ρ := w.hρ
  have he_r : 8 * dev v ≤ w.r := le_of_lt (lt_of_lt_of_le hsmall (min_le_right _ _))
  have he0 : 0 ≤ dev v := dev_nonneg v
  have hr6 : 6 * w.r ≤ 1 := by linarith [w.hrδ, w.hδ1]
  have hr_le : w.r ≤ 1 / 400000 := by linarith [w.hrδ, w.hδ1]
  have h3e : 3 * dev v ≤ 1 := by
    have hv8 : dev v ≤ w.r / 8 := by linarith
    nlinarith [hv8, hr6]
  have hvinv : dev v⁻¹ ≤ 2 * dev v := by
    have h := uminus_inv_dev_le hv
    nlinarith [h, he0, h3e]
  by_cases hvzE : v • z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ
  · obtain ⟨haU, hk'm, hpt⟩ := (mem_chart_iff w (v • z)).mp hvzE
    have hk'm2 : w.θ (v • z) ∈ VtSet t ∩ V (2 * w.ρ) :=
      ⟨hk'm.1, fun i j => lt_of_lt_of_le (hk'm.2 i j) (by linarith)⟩
    by_cases hzE : z ∈ chartSet t w.z0 w.uc w.θ (2 * w.r) w.ρ
    · obtain ⟨hbU, hkm, hptz⟩ := (mem_chart_iff w z).mp hzE
      have ha_eq : w.uc (v • z) = v * w.uc z := by
        have h1m : (1 : SL3) ∈ Uball (Uminus t) (2 * w.r) := by
          refine ⟨Subgroup.one_mem _, ?_⟩
          intro i j
          rw [Matrix.SpecialLinearGroup.coe_one, sub_self, abs_zero]
          linarith
        have h1k : (1 : SL3) ∈ VtSet t ∩ V (2 * w.ρ) := by
          refine ⟨VtSet_one_mem t, ?_⟩
          intro i j
          rw [Matrix.SpecialLinearGroup.coe_one, sub_self, abs_zero]
          linarith
        have hgV : w.uc (v • z) * w.θ (v • z) ∈ V w.δ := by
          rw [mem_V_iff_dev_lt]
          exact dev_mul_lt_delta_of_ball w haU hk'm
        have hhV : v * w.uc z * w.θ z ∈ V w.δ := by
          rw [mem_V_iff_dev_lt]
          exact dev_uminus_mul_lt_delta w he_r hbU hkm
        have heq : (w.uc (v • z) * w.θ (v • z)) • w.z0 = (v * w.uc z * w.θ z) • w.z0 := by
          rw [hpt]
          rw [show (v * w.uc z * w.θ z) • w.z0 = v • ((w.uc z * w.θ z) • w.z0) by
            simp only [mul_smul]]
          rw [hptz]
        have hinj := w.inj (1 : SL3) h1m (1 : SL3) h1k
          (w.uc (v • z) * w.θ (v • z)) (v * w.uc z * w.θ z) hgV hhV (by simpa using heq)
        have h2 := congrArg (fun x : SL3 => (w.uc (v • z))⁻¹ * x * (w.θ z)⁻¹) hinj
        have h2L : (w.uc (v • z))⁻¹ * (w.uc (v • z) * w.θ (v • z)) * (w.θ z)⁻¹
            = w.θ (v • z) * (w.θ z)⁻¹ := by group
        have h2R : (w.uc (v • z))⁻¹ * (v * w.uc z * w.θ z) * (w.θ z)⁻¹
            = (w.uc (v • z))⁻¹ * (v * w.uc z) := by group
        rw [h2L, h2R] at h2
        have hUm : (w.uc (v • z))⁻¹ * (v * w.uc z) ∈ Uminus t :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ haU.1) (Subgroup.mul_mem _ hv hbU.1)
        have hVt : w.θ (v • z) * (w.θ z)⁻¹ ∈ VtSet t :=
          VtSet_mul_mem hk'm.1 (VtSet_inv_mem hkm.1)
        have hone : (w.uc (v • z))⁻¹ * (v * w.uc z) = 1 :=
          eq_one_of_mem_uminus_of_mem_VtSet hUm (by rw [← h2]; exact hVt)
        exact inv_mul_eq_one.mp hone
      have hdiff : |dev (w.uc (v • z)) - dev (w.uc z)| ≤ 4 * dev v := by
        rw [ha_eq]
        have hb_dev : dev (w.uc z) < 2 * w.r := (mem_V_iff_dev_lt _ (2 * w.r)).mp hbU.2
        have hvb_dev : dev (v * w.uc z) < 2 * w.r + 2 * dev v := by
          have h := dev_mul_le v (w.uc z)
          have hmul : dev v * dev (w.uc z) ≤ dev v * (2 * w.r) :=
            mul_le_mul_of_nonneg_left hb_dev.le he0
          have h6e : 6 * w.r * dev v ≤ dev v := by nlinarith [hr6, he0]
          nlinarith [h, hmul, h6e, he0]
        have h1s : 1 + 3 * dev (w.uc z) ≤ 2 := by nlinarith [hb_dev, hr_le]
        have h2s : 1 + 3 * dev (v * w.uc z) ≤ 2 := by
          nlinarith [hvb_dev, he_r, hr_le, he0]
        have hup : dev (v * w.uc z) - dev (w.uc z) ≤ 4 * dev v := by
          have h := dev_mul_le v (w.uc z)
          have hmul := mul_le_mul_of_nonneg_left h1s he0
          linarith [h, hmul]
        have hdown : dev (w.uc z) - dev (v * w.uc z) ≤ 4 * dev v := by
          have h := dev_mul_le v⁻¹ (v * w.uc z)
          have heqinv : v⁻¹ * (v * w.uc z) = w.uc z := by group
          rw [heqinv] at h
          have hfac0 : 0 ≤ 1 + 3 * dev (v * w.uc z) := by
            nlinarith [dev_nonneg (v * w.uc z)]
          have hstep : dev v⁻¹ * (1 + 3 * dev (v * w.uc z)) ≤ 4 * dev v := by
            have hm := mul_le_mul hvinv h2s hfac0 (by linarith : (0 : ℝ) ≤ 2 * dev v)
            linarith [hm]
          linarith [h, hstep]
        exact abs_sub_le_iff.mpr ⟨hup, hdown⟩
      rw [dU_of_mem w hzE, dU_of_mem w hvzE]
      have htri : |dev (w.uc z) - w.r|
          ≤ |dev (w.uc z) - dev (w.uc (v • z))| + |dev (w.uc (v • z)) - w.r| :=
        abs_sub_le _ _ _
      have hdiff' : |dev (w.uc z) - dev (w.uc (v • z))| ≤ 4 * dev v := by
        rw [abs_sub_comm]; exact hdiff
      linarith [htri, hdiff']
    · have ha_dev : dev (w.uc (v • z)) < 2 * w.r := (mem_V_iff_dev_lt _ (2 * w.r)).mp haU.2
      have ha0 : 0 ≤ dev (w.uc (v • z)) := dev_nonneg _
      have hc_le : dev (v⁻¹ * w.uc (v • z)) ≤ dev (w.uc (v • z)) + 4 * dev v := by
        have h := dev_mul_le v⁻¹ (w.uc (v • z))
        have h2s : 1 + 3 * dev (w.uc (v • z)) ≤ 2 := by nlinarith [ha_dev, hr_le]
        have hfac0 : 0 ≤ 1 + 3 * dev (w.uc (v • z)) := by nlinarith [ha0]
        have hstep : dev v⁻¹ * (1 + 3 * dev (w.uc (v • z))) ≤ 4 * dev v := by
          have hm := mul_le_mul hvinv h2s hfac0 (by linarith : (0 : ℝ) ≤ 2 * dev v)
          linarith [hm]
        linarith [h, hstep]
      have hc_ge : 2 * w.r ≤ dev (v⁻¹ * w.uc (v • z)) := by
        by_contra hcon
        push Not at hcon
        have hmem : v⁻¹ * w.uc (v • z) ∈ Uball (Uminus t) (2 * w.r) :=
          ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hv) haU.1,
            (mem_V_iff_dev_lt _ (2 * w.r)).mpr hcon⟩
        have hcoord := w.coord (v⁻¹ * w.uc (v • z)) hmem (w.θ (v • z)) hk'm2
        have hz_eq : (v⁻¹ * w.uc (v • z) * w.θ (v • z)) • w.z0 = z := by
          have h1 : (v⁻¹ * w.uc (v • z) * w.θ (v • z)) • w.z0
              = v⁻¹ • ((w.uc (v • z) * w.θ (v • z)) • w.z0) := by simp only [mul_smul]
          rw [h1, hpt, inv_smul_smul]
        rw [hz_eq] at hcoord
        exact hzE ((mem_chart_iff w z).mpr ⟨by rw [hcoord.1]; exact hmem,
          by rw [hcoord.2]; exact ⟨hk'm.1, hk'm.2⟩, by rw [hcoord.1, hcoord.2]; exact hz_eq⟩)
      rw [dU_of_mem w hvzE, dU_of_not_mem w hzE]
      have hge : 2 * w.r - 4 * dev v ≤ dev (w.uc (v • z)) := by linarith [hc_ge, hc_le]
      have hgt : w.r ≤ dev (w.uc (v • z)) := by nlinarith [hge, he_r, he0]
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ dev (w.uc (v • z)) - w.r)]
      linarith [hge]
  · rw [dU_of_not_mem w hvzE]
    linarith [dU_le_r w z, dev_nonneg v]

/-! ## The main transfer theorem -/

theorem margin_transfer {μ : MeasureTheory.Measure Work.EKLContract.X3} {t : Fin 3 → ℝ}
    (w : Work.EKLC6Route.Window μ t) {x y : Work.EKLContract.X3} {u : Work.EKLContract.SL3}
    {δ' : ℝ} (hδ' : 0 < δ') (hu : u ∈ Work.EKLC6Core.Uminus t) (hy : y = u • x)
    (hmar : ∀ n : ℕ, δ' * Real.exp (-(Work.EKLC6Route.lamExp t / 2) * n) ≤
      w.dU ((Work.EKLC6Route.Tm t)^[n] x))
    (hpos : ∀ n : ℕ, w.dU ((Work.EKLC6Route.Tm t)^[n] y) ≠ 0) :
    ∃ δ'' : ℝ, 0 < δ'' ∧ ∀ n : ℕ,
      δ'' * Real.exp (-(Work.EKLC6Route.lamExp t / 2) * n) ≤
        w.dU ((Work.EKLC6Route.Tm t)^[n] y) := by
  have hlam : 0 < lamExp t := lamExp_pos t
  have hlam2 : 0 < lamExp t / 2 := by linarith
  have hδ'r : δ' ≤ w.r := by
    have h0 := hmar 0
    simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one] at h0
    exact le_trans h0 (dU_le_r w x)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 16 * dev u * Real.exp (-(lamExp t / 2) * (N : ℝ)) ≤ δ' := by
    by_cases hu0 : dev u = 0
    · exact ⟨0, by rw [hu0]; simp [hδ'.le]⟩
    · have hdu : 0 < dev u := lt_of_le_of_ne (dev_nonneg u) (Ne.symm hu0)
      have hC : 0 < 16 * dev u := by positivity
      have hpos' : 0 < δ' / (16 * dev u) := by positivity
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (y := Real.exp (-(lamExp t / 2))) hpos'
        (by rw [Real.exp_lt_one_iff]; linarith)
      refine ⟨n, ?_⟩
      have hexp : Real.exp (-(lamExp t / 2) * (n : ℝ)) = Real.exp (-(lamExp t / 2)) ^ n := by
        rw [mul_comm, Real.exp_nat_mul]
      rw [hexp]
      have := mul_lt_mul_of_pos_left hn hC
      rw [mul_div_cancel₀ _ (ne_of_gt hC)] at this
      exact this.le
  have hstep : ∀ n : ℕ, N ≤ n →
      (δ' / 2) * Real.exp (-(lamExp t / 2) * (n : ℝ)) ≤ w.dU ((Tm t)^[n] y) := by
    intro n hn
    have hexpmono : Real.exp (-(lamExp t / 2) * (n : ℝ)) ≤
        Real.exp (-(lamExp t / 2) * (N : ℝ)) := by
      rw [Real.exp_le_exp]
      have h2 : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith [hlam2]
    have hNn : 16 * dev u * Real.exp (-(lamExp t / 2) * (n : ℝ)) ≤ δ' := by
      refine le_trans ?_ hN
      exact mul_le_mul_of_nonneg_left hexpmono (mul_nonneg (by norm_num) (dev_nonneg u))
    have hun_mem : aDiag t ^ n * u * (aDiag t ^ n)⁻¹ ∈ Uminus t :=
      conj_pow_mem_uminus t hu n
    have hun_dev : dev (aDiag t ^ n * u * (aDiag t ^ n)⁻¹) ≤
        Real.exp (-(lamExp t * (n : ℝ))) * dev u := dev_conj_aDiag_pow_le hu n
    have hdu : 0 ≤ dev u := dev_nonneg u
    have hE : 0 < Real.exp (-(lamExp t / 2) * (n : ℝ)) := Real.exp_pos _
    have hfac : Real.exp (-(lamExp t * (n : ℝ)))
        = Real.exp (-(lamExp t / 2) * (n : ℝ)) * Real.exp (-(lamExp t / 2) * (n : ℝ)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hsmall_e : 8 * dev (aDiag t ^ n * u * (aDiag t ^ n)⁻¹) ≤
        (δ' / 2) * Real.exp (-(lamExp t / 2) * (n : ℝ)) := by
      have h1 : 8 * dev (aDiag t ^ n * u * (aDiag t ^ n)⁻¹)
          ≤ 8 * (Real.exp (-(lamExp t * (n : ℝ))) * dev u) :=
        mul_le_mul_of_nonneg_left hun_dev (by norm_num)
      refine h1.trans ?_
      have h8 : 8 * dev u * Real.exp (-(lamExp t / 2) * (n : ℝ)) ≤ δ' / 2 := by linarith [hNn]
      have hmul := mul_le_mul_of_nonneg_right h8 (le_of_lt hE)
      calc 8 * (Real.exp (-(lamExp t * (n : ℝ))) * dev u)
          = 8 * dev u * Real.exp (-(lamExp t / 2) * (n : ℝ))
              * Real.exp (-(lamExp t / 2) * (n : ℝ)) := by rw [hfac]; ring
        _ ≤ δ' / 2 * Real.exp (-(lamExp t / 2) * (n : ℝ)) := hmul
        _ = (δ' / 2) * Real.exp (-(lamExp t / 2) * (n : ℝ)) := by ring
    have hsmall_min : 8 * dev (aDiag t ^ n * u * (aDiag t ^ n)⁻¹)
        < min (w.dU ((Tm t)^[n] x)) w.r := by
      have hlt1 : (δ' / 2) * Real.exp (-(lamExp t / 2) * (n : ℝ))
          < δ' * Real.exp (-(lamExp t / 2) * (n : ℝ)) :=
        mul_lt_mul_of_pos_right (by linarith) hE
      have hdU := hmar n
      have hlt2 : (δ' / 2) * Real.exp (-(lamExp t / 2) * (n : ℝ)) < w.r :=
        lt_of_lt_of_le hlt1 (le_trans hdU (dU_le_r w _))
      exact lt_min (lt_of_le_of_lt hsmall_e (lt_of_lt_of_le hlt1 hdU))
        (lt_of_le_of_lt hsmall_e hlt2)
    have htrans := dU_smul_lower w (v := aDiag t ^ n * u * (aDiag t ^ n)⁻¹) hun_mem hsmall_min
    have h4 : 4 * dev (aDiag t ^ n * u * (aDiag t ^ n)⁻¹) ≤
        (δ' / 2) * Real.exp (-(lamExp t / 2) * (n : ℝ)) := by
      have h1 : 4 * dev (aDiag t ^ n * u * (aDiag t ^ n)⁻¹)
          ≤ 4 * (Real.exp (-(lamExp t * (n : ℝ))) * dev u) :=
        mul_le_mul_of_nonneg_left hun_dev (by norm_num)
      refine h1.trans ?_
      have h8 : 4 * dev u * Real.exp (-(lamExp t / 2) * (n : ℝ)) ≤ δ' / 2 := by linarith [hNn]
      have hmul := mul_le_mul_of_nonneg_right h8 (le_of_lt hE)
      calc 4 * (Real.exp (-(lamExp t * (n : ℝ))) * dev u)
          = 4 * dev u * Real.exp (-(lamExp t / 2) * (n : ℝ))
              * Real.exp (-(lamExp t / 2) * (n : ℝ)) := by rw [hfac]; ring
        _ ≤ δ' / 2 * Real.exp (-(lamExp t / 2) * (n : ℝ)) := hmul
        _ = (δ' / 2) * Real.exp (-(lamExp t / 2) * (n : ℝ)) := by ring
    have hmain : (δ' / 2) * Real.exp (-(lamExp t / 2) * (n : ℝ))
        ≤ w.dU ((aDiag t ^ n * u * (aDiag t ^ n)⁻¹) • ((Tm t)^[n] x)) := by
      have hdU := hmar n
      linarith [htrans, h4, hdU]
    have hyun : (Tm t)^[n] y = (aDiag t ^ n * u * (aDiag t ^ n)⁻¹) • ((Tm t)^[n] x) := by
      show (fun z : X3 => aDiag t • z)^[n] y = _
      rw [hy]
      exact orbit_smul_eq t n u x
    rwa [← hyun] at hmain
  have hsne : ((Finset.range (N + 1)).image (fun n => w.dU ((Tm t)^[n] y))).Nonempty :=
    Finset.image_nonempty.mpr ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
  set β : ℝ := ((Finset.range (N + 1)).image (fun n => w.dU ((Tm t)^[n] y))).min' hsne
    with hβdef
  have hβpos : 0 < β := by
    have hm : β ∈ (Finset.range (N + 1)).image (fun n => w.dU ((Tm t)^[n] y)) := by
      rw [hβdef]; exact Finset.min'_mem _ _
    obtain ⟨n, _, hn⟩ := Finset.mem_image.mp hm
    rw [← hn]
    exact lt_of_le_of_ne (dU_nonneg w _) (Ne.symm (hpos n))
  refine ⟨min β (δ' / 2), lt_min hβpos (by linarith), ?_⟩
  intro n
  rcases le_or_gt n N with hn | hn
  · have hmem : w.dU ((Tm t)^[n] y) ∈
        (Finset.range (N + 1)).image (fun n => w.dU ((Tm t)^[n] y)) :=
      Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le hn), rfl⟩
    have hβle : β ≤ w.dU ((Tm t)^[n] y) := by
      rw [hβdef]
      exact Finset.min'_le _ _ hmem
    have hexp1 : Real.exp (-(lamExp t / 2) * (n : ℝ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [hlam2, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))]
    calc min β (δ' / 2) * Real.exp (-(lamExp t / 2) * (n : ℝ))
        ≤ β * Real.exp (-(lamExp t / 2) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.exp_pos _).le
      _ ≤ β * 1 := mul_le_mul_of_nonneg_left hexp1 hβpos.le
      _ = β := mul_one β
      _ ≤ w.dU ((Tm t)^[n] y) := hβle
  · have hnN : N ≤ n := le_of_lt hn
    calc min β (δ' / 2) * Real.exp (-(lamExp t / 2) * (n : ℝ))
        ≤ (δ' / 2) * Real.exp (-(lamExp t / 2) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.exp_pos _).le
      _ ≤ w.dU ((Tm t)^[n] y) := hstep n hnN

end Work.EKLC6Route
