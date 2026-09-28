import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.tau_basic
import Submission.Work.HP.HP2.exists_orthogonal_mulVec

namespace Work.HP.HP2

open MeasureTheory

/-- Volume of the closed `rNorm`-ball of radius `r` in `ℝ^m` (valid also for `m = 0`). -/
lemma rNorm_ball_volume (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    MeasureTheory.volume {w : Fin m → ℝ | rNorm w ≤ r}
      = ENNReal.ofReal (r ^ m * (Real.sqrt Real.pi ^ m / Real.Gamma ((m : ℝ) / 2 + 1))) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    have hset : {w : Fin 0 → ℝ | rNorm w ≤ r} = Set.univ := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      have h0 : rNorm w = 0 := by simp [rNorm]
      rw [h0]; exact hr
    rw [hset, MeasureTheory.volume_pi]
    simp [Real.Gamma_one]
  · haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have hkey : ∀ v : Fin m → ℝ, (∑ i, |v i| ^ (2:ℝ)) ^ ((1:ℝ)/2) = rNorm v := by
      intro v
      rw [← Real.sqrt_eq_rpow, rNorm]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [Real.rpow_ofNat, sq_abs]
    have hconv : {w : Fin m → ℝ | rNorm w ≤ r}
        = {w : Fin m → ℝ | (∑ i, |w i| ^ (2:ℝ)) ^ ((1:ℝ)/2) ≤ r} := by
      ext w
      simp only [Set.mem_setOf_eq]
      rw [hkey w]
    rw [hconv, MeasureTheory.volume_sum_rpow_le (Fin m) (p := 2) (by norm_num) r]
    simp only [Fintype.card_fin]
    have hpi : 2 * Real.Gamma ((1:ℝ)/2 + 1) = Real.sqrt Real.pi := by
      rw [Real.Gamma_add_one (by norm_num : ((1:ℝ)/2) ≠ 0), Real.Gamma_one_half_eq]
      ring
    rw [hpi, ← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (pow_nonneg hr m)]

/-- The arithmetic core: a point of the "reference box" lies in the cap-cone for `u = e₀`. -/
lemma mem_e0_cap (n : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {y : Fin (n + 1) → ℝ}
    (ha : y 0 ∈ Set.Icc (1/2 : ℝ) (3/4))
    (hw : rNorm (fun j : Fin n => y j.succ) ≤ δ / 2) :
    rNorm y ≤ 1 ∧ rNorm (y - rNorm y • (Pi.single 0 1 : Fin (n + 1) → ℝ)) ≤ δ * rNorm y := by
  have ha1 : (1/2 : ℝ) ≤ y 0 := ha.1
  have ha2 : y 0 ≤ 3/4 := ha.2
  have hρ0 : 0 ≤ rNorm y := rNorm_nonneg y
  have hw0 : 0 ≤ rNorm (fun j : Fin n => y j.succ) := rNorm_nonneg _
  have hδ2 : 0 ≤ δ := le_of_lt hδ0
  have hρsq : (rNorm y) ^ 2 = (y 0) ^ 2 + (rNorm (fun j : Fin n => y j.succ)) ^ 2 := by
    rw [rNorm_sq, rNorm_sq, Fin.sum_univ_succ]
  have hZsq : (rNorm (y - rNorm y • (Pi.single 0 1 : Fin (n + 1) → ℝ))) ^ 2
      = (y 0 - rNorm y) ^ 2 + (rNorm (fun j : Fin n => y j.succ)) ^ 2 := by
    rw [rNorm_sq, rNorm_sq, Fin.sum_univ_succ]
    congr 1
    · simp [Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
    · apply Finset.sum_congr rfl
      intro j _
      simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · have h1 : (rNorm y) ^ 2 ≤ (1:ℝ) ^ 2 := by
      have hA : (y 0) ^ 2 ≤ (3/4) ^ 2 := pow_le_pow_left₀ (by linarith) ha2 2
      have hB : (rNorm (fun j : Fin n => y j.succ)) ^ 2 ≤ (δ / 2) ^ 2 :=
        pow_le_pow_left₀ hw0 hw 2
      have hC : (δ / 2) ^ 2 ≤ (1/2 : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      nlinarith [hρsq, hA, hB, hC]
    have h2 : |rNorm y| ≤ |(1:ℝ)| := sq_le_sq.mp h1
    rwa [abs_of_nonneg hρ0, abs_one] at h2
  · have hρhalf : (1:ℝ)/2 ≤ rNorm y := by
      have hy0 : y 0 ≤ rNorm y := by
        have h := abs_apply_le_rNorm y 0
        rwa [abs_of_nonneg (by linarith : (0:ℝ) ≤ y 0)] at h
      linarith
    have hw2 : (rNorm (fun j : Fin n => y j.succ)) ^ 2 ≤ (δ / 2) ^ 2 :=
      pow_le_pow_left₀ hw0 hw 2
    have hρa_le : rNorm y - y 0 ≤ δ ^ 2 / 4 := by
      have hρpos : 0 < rNorm y + y 0 := by linarith
      have hgeq : 1 ≤ rNorm y + y 0 := by linarith
      have hkey : (rNorm y - y 0) * (rNorm y + y 0)
          = (rNorm (fun j : Fin n => y j.succ)) ^ 2 := by
        nlinarith [hρsq]
      have hquot : rNorm y - y 0
          = (rNorm (fun j : Fin n => y j.succ)) ^ 2 / (rNorm y + y 0) := by
        rw [eq_div_iff hρpos.ne']
        linarith [hkey]
      rw [hquot]
      have ha' : (0:ℝ) ≤ (rNorm (fun j : Fin n => y j.succ)) ^ 2 := sq_nonneg _
      have hle : (rNorm (fun j : Fin n => y j.succ)) ^ 2 / (rNorm y + y 0)
          ≤ (rNorm (fun j : Fin n => y j.succ)) ^ 2 := by
        rw [div_le_iff₀ hρpos]
        nlinarith [ha', hgeq]
      calc (rNorm (fun j : Fin n => y j.succ)) ^ 2 / (rNorm y + y 0)
          ≤ (rNorm (fun j : Fin n => y j.succ)) ^ 2 := hle
        _ ≤ (δ / 2) ^ 2 := hw2
        _ = δ ^ 2 / 4 := by ring
    have hfin : 2 * rNorm y * (rNorm y - y 0) ≤ (δ * rNorm y) ^ 2 := by
      have h1 : 2 * rNorm y * (rNorm y - y 0) ≤ 2 * rNorm y * (δ ^ 2 / 4) :=
        mul_le_mul_of_nonneg_left hρa_le (by positivity)
      have h2e : 2 * rNorm y * (δ ^ 2 / 4) = δ ^ 2 * rNorm y / 2 := by ring
      have h3 : δ ^ 2 * rNorm y / 2 ≤ (δ * rNorm y) ^ 2 := by
        nlinarith [mul_nonneg (mul_nonneg (sq_nonneg δ) hρ0) (by linarith : (0:ℝ) ≤ rNorm y - 1/2)]
      linarith [h1, h2e, h3]
    have hZ2 : (rNorm (y - rNorm y • (Pi.single 0 1 : Fin (n + 1) → ℝ))) ^ 2
        = 2 * rNorm y * (rNorm y - y 0) := by
      rw [hZsq]; nlinarith [hρsq]
    have hfin2 : (rNorm (y - rNorm y • (Pi.single 0 1 : Fin (n + 1) → ℝ))) ^ 2
        ≤ (δ * rNorm y) ^ 2 := by
      rw [hZ2]; exact hfin
    have h3 := sq_le_sq.mp hfin2
    rwa [abs_of_nonneg (rNorm_nonneg _), abs_of_nonneg (mul_nonneg hδ2 hρ0)] at h3

/-- Volume of the reference box, computed by splitting off the zeroth coordinate. -/
lemma cap_box_volume (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) :
    MeasureTheory.volume {y : Fin (n + 1) → ℝ | y 0 ∈ Set.Icc (1/2 : ℝ) (3/4) ∧
        rNorm (fun j : Fin n => y j.succ) ≤ δ / 2}
      = ENNReal.ofReal (1/4 * ((δ / 2) ^ n *
          (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)))) := by
  have hmp : MeasurePreserving
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) volume volume :=
    MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have happly : ∀ y : Fin (n + 1) → ℝ,
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) y
        = (y 0, fun j : Fin n => y j.succ) := fun y => rfl
  have hCeq : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) ⁻¹'
        (Set.Icc (1/2 : ℝ) (3/4) ×ˢ {w : Fin n → ℝ | rNorm w ≤ δ / 2})
      = {y : Fin (n + 1) → ℝ | y 0 ∈ Set.Icc (1/2 : ℝ) (3/4) ∧
          rNorm (fun j : Fin n => y j.succ) ≤ δ / 2} := by
    ext y
    simp only [Set.mem_preimage, happly y, Set.mem_prod, Set.mem_setOf_eq]
  have hrN : Continuous fun w : Fin n → ℝ => rNorm w := by unfold rNorm; fun_prop
  have hPmeas : MeasurableSet (Set.Icc (1/2:ℝ) (3/4) ×ˢ {w : Fin n → ℝ | rNorm w ≤ δ / 2}) :=
    measurableSet_Icc.prod (isClosed_le hrN continuous_const).measurableSet
  have htvol : MeasureTheory.volume
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) ⁻¹'
          (Set.Icc (1/2 : ℝ) (3/4) ×ˢ {w : Fin n → ℝ | rNorm w ≤ δ / 2}))
      = MeasureTheory.volume (Set.Icc (1/2 : ℝ) (3/4) ×ˢ {w : Fin n → ℝ | rNorm w ≤ δ / 2}) :=
    hmp.measure_preimage hPmeas.nullMeasurableSet
  have hI : MeasureTheory.volume (Set.Icc (1/2 : ℝ) (3/4)) = ENNReal.ofReal (1/4) := by
    rw [Real.volume_Icc, show (3:ℝ)/4 - 1/2 = 1/4 from by norm_num]
  rw [← hCeq, htvol, MeasureTheory.Measure.volume_eq_prod ℝ (Fin n → ℝ),
    MeasureTheory.Measure.prod_prod, hI,
    rNorm_ball_volume n (δ / 2) (by positivity)]
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 1/4)]

theorem cone_cap_volume (n : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (u : Fin (n + 1) → ℝ), rNorm u = 1 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ENNReal.ofReal (κ * δ ^ n) ≤
        MeasureTheory.volume {x : Fin (n + 1) → ℝ |
          rNorm x ≤ 1 ∧ rNorm (x - rNorm x • u) ≤ δ * rNorm x} := by
  refine ⟨(1/4) * (1/2) ^ n * (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)), ?_, ?_⟩
  · refine mul_pos (mul_pos (by norm_num) (pow_pos (by norm_num) n)) ?_
    exact div_pos (pow_pos (Real.sqrt_pos.mpr Real.pi_pos) n)
      (Real.Gamma_pos_of_pos (by positivity))
  · intro u hu δ hδ0 hδ1
    obtain ⟨M, _hMM, hnorm, he0, hmap⟩ := exists_orthogonal_mulVec n u hu
    set Su : Set (Fin (n + 1) → ℝ) :=
      {x : Fin (n + 1) → ℝ | rNorm x ≤ 1 ∧ rNorm (x - rNorm x • u) ≤ δ * rNorm x} with hSu
    set Se0 : Set (Fin (n + 1) → ℝ) :=
      {y : Fin (n + 1) → ℝ | rNorm y ≤ 1 ∧
        rNorm (y - rNorm y • (Pi.single 0 1 : Fin (n + 1) → ℝ)) ≤ δ * rNorm y} with hSe0
    set C : Set (Fin (n + 1) → ℝ) :=
      {y : Fin (n + 1) → ℝ | y 0 ∈ Set.Icc (1/2 : ℝ) (3/4) ∧
        rNorm (fun j : Fin n => y j.succ) ≤ δ / 2} with hC
    have hfmeas : Measurable (fun x : Fin (n + 1) → ℝ => M.mulVec x) :=
      (Matrix.mulVecLin M).continuous_of_finiteDimensional.measurable
    have hpre : (fun x : Fin (n + 1) → ℝ => M.mulVec x) ⁻¹' Su = Se0 := by
      rw [hSu, hSe0]
      ext y
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      have h2 : M.mulVec y - rNorm y • u
          = M.mulVec (y - rNorm y • (Pi.single 0 1 : Fin (n + 1) → ℝ)) := by
        rw [← he0, ← Matrix.mulVec_smul, ← Matrix.mulVec_sub]
      rw [hnorm y, h2, hnorm (y - rNorm y • (Pi.single 0 1 : Fin (n + 1) → ℝ))]
    have hCvol : MeasureTheory.volume C
        = ENNReal.ofReal (1/4 * ((δ / 2) ^ n *
            (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)))) := by
      rw [hC]
      exact cap_box_volume n δ (le_of_lt hδ0)
    have hsub : C ⊆ Se0 := by
      intro y hy
      rw [hC] at hy
      rw [hSe0]
      exact mem_e0_cap n hδ0 hδ1 hy.1 hy.2
    have hrNcont : Continuous (fun x : Fin (n + 1) → ℝ => rNorm x) := by
      unfold rNorm; fun_prop
    have hSumeas : MeasurableSet Su := by
      rw [hSu]
      have hcont2 : Continuous
          (fun x : Fin (n + 1) → ℝ => rNorm (x - rNorm x • u)) :=
        hrNcont.comp (continuous_id.sub (hrNcont.smul continuous_const))
      exact (isClosed_le hrNcont continuous_const).inter
        (isClosed_le hcont2 (continuous_const.mul hrNcont)) |>.measurableSet
    have hmpM : MeasurePreserving (fun x : Fin (n + 1) → ℝ => M.mulVec x) volume volume :=
      ⟨hfmeas, hmap⟩
    have hd : MeasureTheory.volume ((fun x : Fin (n + 1) → ℝ => M.mulVec x) ⁻¹' Su)
        = MeasureTheory.volume Su := hmpM.measure_preimage hSumeas.nullMeasurableSet
    have hpow : (δ / 2) ^ n = (1 / 2) ^ n * δ ^ n := by
      have hd2 : (δ:ℝ) / 2 = δ * (1/2) := by ring
      rw [hd2, mul_pow]; ring
    have hka : (1/4) * (1/2) ^ n * (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1)) * δ ^ n
        = 1/4 * ((δ / 2) ^ n * (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1))) := by
      rw [hpow]; ring
    rw [hka]
    calc ENNReal.ofReal (1/4 * ((δ / 2) ^ n *
            (Real.sqrt Real.pi ^ n / Real.Gamma ((n : ℝ) / 2 + 1))))
        = MeasureTheory.volume C := hCvol.symm
      _ ≤ MeasureTheory.volume Se0 := measure_mono hsub
      _ = MeasureTheory.volume ((fun x : Fin (n + 1) → ℝ => M.mulVec x) ⁻¹' Su) := by rw [hpre]
      _ = MeasureTheory.volume Su := hd

end Work.HP.HP2
