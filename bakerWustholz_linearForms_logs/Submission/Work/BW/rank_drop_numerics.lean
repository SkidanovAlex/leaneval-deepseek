import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.rdnDefs
import Submission.Work.BW.rdnNumB

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

/-! # `Work.BW.rank_drop_numerics`

BW §21 numerics, part 2: the check (30), p. 60–61, redone for the two cases of
`multiplicity_prop` with the half split.
-/

namespace Work.BW

/-! ## Elementary auxiliary facts -/

theorem rdnU_eq (r d : ℕ) : rdnU r d = ((2 * r * d : ℕ) : ℝ) := by
  unfold rdnU; push_cast; ring

theorem pI_eq (r d : ℕ) : pI r d = ⌊50 * rdnL r d⌋₊ := rfl

theorem pD0_eq (r d : ℕ) (σ : Fin r → ℝ) :
    pD0 r d σ = ⌊(r : ℝ) * pD r d σ / (2 * rdnL r d)⌋₊ := rfl

theorem pDj_eq (r d : ℕ) (σ : Fin r → ℝ) (j : Fin r) :
    pDj r d σ j = ⌊pD r d σ / ((r : ℝ) * (d : ℝ) * σ j)⌋₊ := rfl

theorem pT_eq (r d : ℕ) (σ : Fin r → ℝ) :
    pT r d σ = ⌊(11.75 : ℝ) * (r : ℝ) * pD r d σ⌋₊ := rfl

theorem pS_cast (r d h : ℕ) : (pS r d h : ℝ) = 16 * (r : ℝ) * (d : ℝ) * (h : ℝ) := by
  unfold pS; push_cast; ring

private theorem calD_zero (r d h : ℕ) (σ : Fin r → ℝ) :
    calD r d h σ 0 = (h : ℝ) * ((pD0 r d σ : ℝ) + 1) := by
  unfold calD; rw [Fin.cons_zero]

private theorem calD_succ (r d h : ℕ) (σ : Fin r → ℝ) (i : Fin r) :
    calD r d h σ i.succ = (pDj r d σ i : ℝ) / (2 : ℝ) ^ pI r d := by
  unfold calD; rw [Fin.cons_succ]

theorem halfSplit_ge (r : ℕ) (hr : 1 ≤ r) {x : ℝ} (hx : 0 ≤ x) (m : ℕ) :
    x / (2 * (r : ℝ)) ≤ (halfSplit r x m : ℝ) + 1 := by
  unfold halfSplit
  split_ifs with hm
  · have h1 : x / 2 < (⌊x / 2⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : x / (2 * (r : ℝ)) ≤ x / 2 := by
      apply div_le_div_of_nonneg_left hx (by norm_num)
      have : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      nlinarith
    linarith
  · have h1 : x / (2 * (r : ℝ)) < (⌊x / (2 * (r : ℝ))⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith

theorem choose_ge (N k : ℕ) :
    ((N + 1 : ℝ) ^ k) ≤ ((N + k).choose k : ℝ) * (k.factorial : ℝ) := by
  have hnat : (N + 1) ^ k ≤ (N + k).choose k * k.factorial := by
    rw [Nat.mul_comm ((N + k).choose k) k.factorial,
      ← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]
    calc (N + 1) ^ k = ∏ i ∈ Finset.range k, (N + 1) := by
          rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ i ∈ Finset.range k, (N + k - i) := by
          apply Finset.prod_le_prod
          intro i hi
          simp only [Finset.mem_range] at hi
          omega
  calc ((N + 1 : ℝ) ^ k) = ((N + 1) ^ k : ℕ) := by push_cast; ring
    _ ≤ ((N + k).choose k * k.factorial : ℕ) := by exact_mod_cast hnat
    _ = ((N + k).choose k : ℝ) * (k.factorial : ℝ) := by push_cast; ring

theorem pI_lower (r d : ℕ) : 50 * rdnL r d - 1 ≤ (pI r d : ℝ) := by
  have h := Nat.lt_floor_add_one (50 * rdnL r d)
  rw [pI_eq]
  push_cast
  linarith

theorem pI_upper {r d : ℕ} (h : 0 ≤ rdnL r d) : (pI r d : ℝ) ≤ 50 * rdnL r d := by
  rw [pI_eq]
  exact Nat.floor_le (mul_nonneg (by norm_num) h)

theorem rdnU_four_le {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) : 4 ≤ rdnU r d := by
  unfold rdnU
  have h1 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have h2 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  nlinarith

theorem rdnU_gt0 {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) : 0 < rdnU r d :=
  lt_of_lt_of_le (by norm_num) (rdnU_four_le hr hd)

theorem rdnU_ge1 {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) : 1 ≤ rdnU r d :=
  le_trans (by norm_num) (rdnU_four_le hr hd)

theorem rdnL_nonneg {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) : 0 ≤ rdnL r d := by
  unfold rdnL
  exact Real.log_nonneg (rdnU_ge1 hr hd)

theorem rdnL_ge_one {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) : 1 ≤ rdnL r d := by
  unfold rdnL
  rw [Real.le_log_iff_exp_le (rdnU_gt0 hr hd)]
  exact le_trans Real.exp_one_lt_three.le (le_trans (by norm_num) (rdnU_four_le hr hd))

/-- `2 ^ pI r d ≥ u ^ (50 log 2) / 2`. -/
theorem two_pow_pI_ge {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) :
    rdnU r d ^ (50 * Real.log 2) / 2 ≤ (2 : ℝ) ^ pI r d := by
  have hu : 0 < rdnU r d := rdnU_gt0 hr hd
  have h1 : 50 * rdnL r d - 1 ≤ (pI r d : ℝ) := pI_lower r d
  have h2 : (2 : ℝ) ^ (50 * rdnL r d - 1) ≤ (2 : ℝ) ^ ((pI r d : ℕ) : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num) h1
  rw [Real.rpow_natCast] at h2
  have h3 : (2 : ℝ) ^ (50 * rdnL r d) = rdnU r d ^ (50 * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hu]
    unfold rdnL
    congr 1
    ring
  have h4 : (2 : ℝ) ^ (50 * rdnL r d - 1) = (2 : ℝ) ^ (50 * rdnL r d) / 2 := by
    rw [Real.rpow_sub (by norm_num : (0:ℝ) < 2)]
    norm_num
  rw [h4, h3] at h2
  linarith

/-! ## The two elementary power bounds for `ξ = pxi r` -/

private theorem pxi_pos {r : ℕ} (hr : 2 ≤ r) : 0 < pxi r := by
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have h : (0.536 : ℝ) / (r : ℝ) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  have hp : pxi r = 1 - (0.536 : ℝ) / (r : ℝ) := rfl
  rw [hp]; linarith

theorem pxi_lt_one {r : ℕ} (hr : 1 ≤ r) : pxi r < 1 := by
  have h : (0 : ℝ) < (0.536 : ℝ) / (r : ℝ) := by positivity
  have hp : pxi r = 1 - (0.536 : ℝ) / (r : ℝ) := rfl
  rw [hp]; linarith

theorem pxi_half_le {r : ℕ} (hr : 2 ≤ r) : 1 / 2 ≤ pxi r := by
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have h : (0.536 : ℝ) / (r : ℝ) ≤ 0.268 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hp : pxi r = 1 - (0.536 : ℝ) / (r : ℝ) := rfl
  rw [hp]; linarith

theorem log_pxi_le {r : ℕ} (hr : 2 ≤ r) : Real.log (pxi r) ≤ -((0.536 : ℝ) / (r : ℝ)) := by
  have hp : 0 < pxi r := pxi_pos hr
  have h1 : Real.log (pxi r) ≤ pxi r - 1 := Real.log_le_sub_one_of_pos hp
  have hp' : pxi r = 1 - (0.536 : ℝ) / (r : ℝ) := rfl
  rw [hp'] at h1 ⊢
  linarith

theorem log_pxi_ge {r : ℕ} (hr : 2 ≤ r) :
    -((0.536 : ℝ) / ((r : ℝ) - 0.536)) ≤ Real.log (pxi r) := by
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hx : (0.536 : ℝ) / (r : ℝ) < 1 := by rw [div_lt_one hrpos]; linarith
  have hpos : 0 < 1 - (0.536 : ℝ) / (r : ℝ) := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  have h2 : (1 - (0.536 : ℝ) / (r : ℝ))⁻¹ - 1 = (0.536 : ℝ) / ((r : ℝ) - 0.536) := by
    have hA : (1 - (0.536 : ℝ) / (r : ℝ)) ≠ 0 := ne_of_gt hpos
    have hB : ((r : ℝ) - 0.536) ≠ 0 := by linarith
    have hC : (r : ℝ) ≠ 0 := ne_of_gt hrpos
    field_simp
    ring
  rw [h2] at h
  have hp : pxi r = 1 - (0.536 : ℝ) / (r : ℝ) := rfl
  rw [hp]
  linarith

theorem rdnCap_nonneg {r : ℕ} (hr : 2 ≤ r) : 0 ≤ rdnCap r := by
  unfold rdnCap
  apply div_nonneg (by positivity)
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  linarith

theorem rdnCap_eq (r : ℕ) : rdnCap r = 50 * ((0.536 : ℝ) * r / ((r:ℝ) - 0.536)) := by
  unfold rdnCap; ring

theorem capR_nonneg {r : ℕ} (hr : 2 ≤ r) : 0 ≤ (0.536 : ℝ) * r / ((r:ℝ) - 0.536) := by
  apply div_nonneg (by positivity)
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  linarith

/-- `ξ^{-(r I)} ≥ u^{26.8}/2`, where `I = pI r d`. -/
theorem pxi_zpow_ge {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) :
    rdnPC r d / 2 ≤ pxi r ^ (-((r * pI r d : ℕ) : ℤ)) := by
  have hu : 0 < rdnU r d := rdnU_gt0 hr hd
  have hp : 0 < pxi r := pxi_pos hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by positivity
  have hI : 50 * rdnL r d - 1 ≤ (pI r d : ℝ) := pI_lower r d
  have hlogr : (r : ℝ) * Real.log (pxi r) ≤ -0.536 := by
    have h1 : Real.log (pxi r) ≤ -((0.536 : ℝ) / (r:ℝ)) := log_pxi_le hr
    have h2 := mul_le_mul_of_nonneg_left h1 hrpos.le
    rw [mul_neg, mul_div_cancel₀ _ (ne_of_gt hrpos)] at h2
    linarith
  have hlog : ((r * pI r d : ℕ) : ℝ) * Real.log (pxi r) ≤ -26.8 * rdnL r d + 0.536 := by
    have h4 : ((r * pI r d : ℕ) : ℝ) * Real.log (pxi r)
        = (pI r d : ℝ) * ((r:ℝ) * Real.log (pxi r)) := by push_cast; ring
    rw [h4]
    have h5 : (pI r d : ℝ) * ((r:ℝ) * Real.log (pxi r)) ≤ (pI r d : ℝ) * (-0.536) :=
      mul_le_mul_of_nonneg_left hlogr (by positivity)
    have h6 : (pI r d : ℝ) * (-0.536) ≤ -26.8 * rdnL r d + 0.536 := by nlinarith [hI]
    linarith
  have hpc_eq : Real.exp (26.8 * rdnL r d) = rdnPC r d := by
    rw [rdnPC, Real.rpow_def_of_pos hu]
    unfold rdnL
    congr 1
    ring
  have hξ : pxi r ^ (r * pI r d) ≤ 2 * (rdnPC r d)⁻¹ := by
    have hξeq : pxi r ^ (r * pI r d)
        = Real.exp (Real.log (pxi r) * ((r * pI r d : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast (pxi r) (r * pI r d), Real.rpow_def_of_pos hp]
    rw [hξeq]
    have hexp : Real.exp (-26.8 * rdnL r d + 0.536) ≤ 2 * (rdnPC r d)⁻¹ := by
      have h1 : Real.exp (-26.8 * rdnL r d + 0.536)
          = Real.exp 0.536 * (rdnPC r d)⁻¹ := by
        rw [Real.exp_add, show -26.8 * rdnL r d = -(26.8 * rdnL r d) by ring,
          Real.exp_neg, hpc_eq]
        ring
      rw [h1]
      have he : Real.exp 0.536 ≤ 2 :=
        (Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 2)).mp
          (by have := Real.log_two_gt_d9; linarith)
      have hpc : 0 < (rdnPC r d)⁻¹ := inv_pos.mpr (by rw [rdnPC]; positivity)
      nlinarith [mul_le_mul_of_nonneg_right he hpc.le]
    have hle : Real.exp (Real.log (pxi r) * ((r * pI r d : ℕ) : ℝ))
        ≤ Real.exp (-26.8 * rdnL r d + 0.536) := by
      apply Real.exp_le_exp.mpr
      rw [mul_comm]
      exact hlog
    exact le_trans hle hexp
  rw [zpow_neg, zpow_natCast]
  have hA : 0 < 2 * (rdnPC r d)⁻¹ := by
    have : 0 < (rdnPC r d)⁻¹ := inv_pos.mpr (by rw [rdnPC]; positivity)
    linarith
  have hB : 0 < pxi r ^ (r * pI r d) := pow_pos hp _
  have h3 := (inv_le_inv₀ hA hB).mpr hξ
  rw [show (2 * (rdnPC r d)⁻¹)⁻¹ = rdnPC r d / 2 by field_simp] at h3
  exact h3

/-- `ξ^{r I} ≥ u^{-(50 cap)}`, where `I = pI r d`. -/
theorem pxi_pow_ge {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) :
    (rdnPowD r d)⁻¹ ≤ pxi r ^ (r * pI r d) := by
  have hu : 0 < rdnU r d := rdnU_gt0 hr hd
  have hp : 0 < pxi r := pxi_pos hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by positivity
  have hL : 0 ≤ rdnL r d := rdnL_nonneg hr hd
  have hIu : (pI r d : ℝ) ≤ 50 * rdnL r d := pI_upper hL
  have hc : 0 ≤ (0.536 : ℝ) * r / ((r:ℝ) - 0.536) := capR_nonneg hr
  have hlogr : -((0.536 : ℝ) * r / ((r:ℝ) - 0.536)) ≤ (r : ℝ) * Real.log (pxi r) := by
    have h1 : -((0.536 : ℝ) / ((r:ℝ) - 0.536)) ≤ Real.log (pxi r) := log_pxi_ge hr
    have h2 := mul_le_mul_of_nonneg_left h1 hrpos.le
    have h3 : (r:ℝ) * -((0.536:ℝ) / ((r:ℝ)-0.536))
        = -((0.536:ℝ)*r/((r:ℝ)-0.536)) := by field_simp
    linarith [h2, h3]
  have hlog : -(rdnCap r * rdnL r d) ≤ Real.log (pxi r) * ((r * pI r d : ℕ) : ℝ) := by
    have h4 : Real.log (pxi r) * ((r * pI r d : ℕ) : ℝ)
        = (pI r d : ℝ) * ((r:ℝ) * Real.log (pxi r)) := by push_cast; ring
    rw [h4]
    have h5 : (pI r d : ℝ) * (-((0.536:ℝ)*r/((r:ℝ)-0.536)))
        ≤ (pI r d : ℝ) * ((r:ℝ) * Real.log (pxi r)) :=
      mul_le_mul_of_nonneg_left hlogr (by positivity)
    have h6 : (50 * rdnL r d) * (-((0.536:ℝ)*r/((r:ℝ)-0.536)))
        ≤ (pI r d : ℝ) * (-((0.536:ℝ)*r/((r:ℝ)-0.536))) :=
      mul_le_mul_of_nonpos_right hIu (by linarith)
    have h7 : (50 * rdnL r d) * (-((0.536:ℝ)*r/((r:ℝ)-0.536)))
        = -(rdnCap r * rdnL r d) := by rw [rdnCap_eq]; ring
    linarith [h5, h6, h7]
  have hbase : (rdnPowD r d)⁻¹ = Real.exp (-(rdnCap r * rdnL r d)) := by
    rw [rdnPowD, ← Real.rpow_neg hu.le, Real.rpow_def_of_pos hu]
    unfold rdnL
    congr 1
    ring
  have hξeq : pxi r ^ (r * pI r d)
      = Real.exp (Real.log (pxi r) * ((r * pI r d : ℕ) : ℝ)) := by
    rw [← Real.rpow_natCast (pxi r) (r * pI r d), Real.rpow_def_of_pos hp]
  rw [hbase, hξeq]
  exact Real.exp_le_exp.mpr hlog

/-! ## Main bounds -/

theorem prod_le_prod_nonneg {ι : Type*} (s : Finset ι) {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i ≤ g i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have hga : 0 ≤ g a := le_trans hfa (h a (Finset.mem_insert_self a s))
      have hf' : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have h' : ∀ i ∈ s, f i ≤ g i := fun i hi => h i (Finset.mem_insert_of_mem hi)
      have ihg : 0 ≤ ∏ i ∈ s, g i := le_trans (Finset.prod_nonneg hf') (ih hf' h')
      exact mul_le_mul (h a (Finset.mem_insert_self a s)) (ih hf' h')
        (Finset.prod_nonneg hf') hga

private theorem pD_nonneg {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 0 ≤ σ j) : 0 ≤ pD r d σ := by
  have hL : 0 ≤ Real.log (2*(r:ℝ)*(d:ℝ)) := rdnL_nonneg hr hd
  have hPi : 0 ≤ ∏ j, σ j := by
    apply Finset.prod_nonneg
    intro j _
    exact hσ j
  have h2 : (0:ℝ) ≤ (r:ℝ)^r := by positivity
  have h3 : (0:ℝ) ≤ ((32:ℝ)*(d:ℝ))^(r+1) := by positivity
  rw [pD]
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h2) h3) hL) hPi

private theorem pDj_le {r d : ℕ} (σ : Fin r → ℝ) (i : Fin r) (hQ : 0 ≤ pD r d σ) (hσi : 0 < σ i) :
    (pDj r d σ i : ℝ) ≤ pD r d σ / ((r:ℝ)*(d:ℝ)*σ i) := by
  rw [pDj_eq]
  exact Nat.floor_le (div_nonneg hQ (by positivity))

/-- `∏_{i ∈ J} σ i · calD r d h σ i.succ ≤ (γ · pD r d σ)^{J.card}`. -/
theorem prod_le {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hσ : ∀ j, 0 < σ j) (J : Finset (Fin r)) :
    ∏ i ∈ J, (σ i * calD r d h σ i.succ) ≤ (rdnGam r d * pD r d σ) ^ J.card := by
  have hu : 0 < rdnU r d := rdnU_gt0 hr hd
  have hpB : 0 < rdnU r d ^ (50 * Real.log 2) := Real.rpow_pos_of_pos hu _
  have h2I : rdnU r d ^ (50 * Real.log 2) / 2 ≤ (2:ℝ)^pI r d := two_pow_pI_ge hr hd
  have h2Ipos : 0 < (2:ℝ)^pI r d := by positivity
  have hinv : (1:ℝ)/(2:ℝ)^pI r d ≤ 2/rdnU r d^(50*Real.log 2) := by
    have hcross : rdnU r d^(50*Real.log 2) ≤ 2 * (2:ℝ)^pI r d := by linarith
    have hpos2 : 0 < (2:ℝ)^pI r d * rdnU r d^(50*Real.log 2) := mul_pos h2Ipos hpB
    calc (1:ℝ)/(2:ℝ)^pI r d
        = rdnU r d^(50*Real.log 2) / ((2:ℝ)^pI r d * rdnU r d^(50*Real.log 2)) := by
          field_simp
      _ ≤ (2 * (2:ℝ)^pI r d) / ((2:ℝ)^pI r d * rdnU r d^(50*Real.log 2)) :=
          div_le_div_of_nonneg_right hcross hpos2.le
      _ = 2/rdnU r d^(50*Real.log 2) := by field_simp
  have hQ0 : 0 ≤ pD r d σ := pD_nonneg hr hd σ (fun j => (hσ j).le)
  have hterm : ∀ i ∈ J, σ i * calD r d h σ i.succ ≤ rdnGam r d * pD r d σ := by
    intro i _
    have hσi : 0 < σ i := hσ i
    have hDj : (pDj r d σ i : ℝ) ≤ pD r d σ / ((r:ℝ)*(d:ℝ)*σ i) :=
      pDj_le σ i hQ0 hσi
    have hratio : 0 ≤ pD r d σ / ((r:ℝ)*(d:ℝ)*σ i) := div_nonneg hQ0 (by positivity)
    have hmul := mul_le_mul hDj hinv (le_of_lt (by positivity : (0:ℝ) < (1:ℝ)/(2:ℝ)^pI r d)) hratio
    have hmul' : (pDj r d σ i : ℝ) * ((1:ℝ)/(2:ℝ)^pI r d)
        ≤ (pD r d σ / ((r:ℝ)*(d:ℝ)*σ i)) * (2/rdnU r d^(50*Real.log 2)) := hmul
    have h1 : (pDj r d σ i : ℝ)/(2:ℝ)^pI r d
        ≤ (pD r d σ / ((r:ℝ)*(d:ℝ)*σ i)) * (2/rdnU r d^(50*Real.log 2)) := by
      simpa [div_eq_mul_inv] using hmul'
    have h2 : σ i * ((pD r d σ / ((r:ℝ)*(d:ℝ)*σ i)) * (2/rdnU r d^(50*Real.log 2)))
        = rdnGam r d * pD r d σ := by
      rw [rdnGam, show rdnU r d = 2*(r:ℝ)*(d:ℝ) from rfl]
      have hrne : (r:ℝ) ≠ 0 := by positivity
      have hdne : (d:ℝ) ≠ 0 := by positivity
      have hsne : σ i ≠ 0 := ne_of_gt hσi
      have hBne : rdnU r d ^ (50*Real.log 2) ≠ 0 := ne_of_gt hpB
      field_simp
      ring
    rw [calD_succ]
    calc σ i * ((pDj r d σ i : ℝ)/(2:ℝ)^pI r d)
        ≤ σ i * ((pD r d σ / ((r:ℝ)*(d:ℝ)*σ i)) * (2/rdnU r d^(50*Real.log 2))) :=
          mul_le_mul_of_nonneg_left h1 hσi.le
      _ = rdnGam r d * pD r d σ := h2
  have hcalDnn : ∀ i : Fin r, 0 ≤ calD r d h σ i.succ := by
    intro i; rw [calD_succ]; positivity
  calc ∏ i ∈ J, (σ i * calD r d h σ i.succ)
      ≤ ∏ _i ∈ J, (rdnGam r d * pD r d σ) :=
        prod_le_prod_nonneg J (fun i _ => mul_nonneg (hσ i).le (hcalDnn i)) hterm
    _ = (rdnGam r d * pD r d σ) ^ J.card := by rw [Finset.prod_const]


theorem rdnDel_pos {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) : 0 < rdnDel r d := by
  rw [rdnDel]
  apply div_pos (by norm_num)
  have : 0 < rdnPowD r d := by
    rw [rdnPowD]; exact Real.rpow_pos_of_pos (rdnU_gt0 hr hd) _
  linarith

/-- `calD r d h σ 0 ≤ 2 h r^{r+1} (32d)^{r+1} ∏σ`. -/
private theorem pD0_le {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ)
    (hPi : 0 ≤ ∏ j, σ j)
    (hone : 1 ≤ (r:ℝ)^(r+1) * ((32:ℝ)*(d:ℝ))^(r+1) * ∏ j, σ j) :
    (pD0 r d σ : ℝ) + 1 ≤ 2 * (r:ℝ)^(r+1) * ((32:ℝ)*(d:ℝ))^(r+1) * ∏ j, σ j := by
  have hL : 0 < rdnL r d := lt_of_lt_of_le (by norm_num) (rdnL_ge_one hr hd)
  have hC : 0 ≤ rdnC r d := by
    have := rdnL_nonneg hr hd
    rw [rdnC]; positivity
  have hQn : 0 ≤ pD r d σ := by rw [pD_eq_rdnC]; exact mul_nonneg hC hPi
  have h1 : (pD0 r d σ : ℝ) ≤ (r:ℝ)*pD r d σ/(2*rdnL r d) := by
    rw [pD0_eq]
    apply Nat.floor_le
    exact div_nonneg (mul_nonneg (by positivity) hQn) (by positivity)
  have h2 : (r:ℝ)*pD r d σ/(2*rdnL r d)
      = (r:ℝ)^(r+1) * ((32:ℝ)*(d:ℝ))^(r+1) * ∏ j, σ j := by
    rw [pD_eq_rdnC, rdnC]
    have hLne : rdnL r d ≠ 0 := ne_of_gt hL
    field_simp
    rw [pow_succ]
    ring
  linarith

/-- `8 d h u^{26.8} ≤ halfSplit r (calS r d h) m + 1`. -/
theorem calS_lower {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (m : ℕ) :
    8 * (d:ℝ) * (h:ℝ) * rdnPC r d ≤ (halfSplit r (calS r d h) m : ℝ) + 1 := by
  have hr1 : 1 ≤ r := by omega
  have hp : 0 < pxi r := pxi_pos hr
  have hz : rdnPC r d / 2 ≤ pxi r ^ (-((r * pI r d : ℕ) : ℤ)) := pxi_zpow_ge hr hd
  have hcs : 0 ≤ calS r d h := by rw [calS]; positivity
  have hS := halfSplit_ge r hr1 hcs m
  have heq : calS r d h / (2*(r:ℝ))
      = pxi r ^ (-((r * pI r d : ℕ) : ℤ)) * (16 * (d:ℝ) * (h:ℝ)) := by
    rw [calS, pS_cast]; field_simp
  have h16 : (0:ℝ) ≤ 16*(d:ℝ)*(h:ℝ) := by positivity
  have h2 : 8*(d:ℝ)*(h:ℝ)*rdnPC r d ≤ calS r d h/(2*(r:ℝ)) := by
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_right hz h16]
  linarith

/-- `δ · pD r d σ ≤ halfSplit r (calT r d σ) m + 1`. -/
theorem calT_lower {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (σ : Fin r → ℝ) (m : ℕ)
    (hQ : 2 ≤ 11.75 * (r:ℝ) * pD r d σ) (hQnn : 0 ≤ pD r d σ) :
    rdnDel r d * pD r d σ ≤ (halfSplit r (calT r d σ) m : ℝ) + 1 := by
  have hr1 : 1 ≤ r := by omega
  have hp : 0 < pxi r := pxi_pos hr
  have hct : 0 ≤ calT r d σ := by rw [calT]; positivity
  have hS := halfSplit_ge r hr1 hct m
  have h1 : (11.75:ℝ)*(r:ℝ)*pD r d σ - 1 ≤ (pT r d σ : ℝ) := by
    have := Nat.lt_floor_add_one ((11.75:ℝ)*(r:ℝ)*pD r d σ)
    rw [pT_eq]
    push_cast
    linarith
  have hT : (11.75:ℝ)*(r:ℝ)*pD r d σ/2 ≤ (pT r d σ : ℝ) := by linarith
  have hpxi : (1/2) * (rdnPowD r d)⁻¹ ≤ pxi r * pxi r ^ (r * pI r d) := by
    have h1 : (1/2:ℝ) ≤ pxi r := pxi_half_le hr
    have h2 : (rdnPowD r d)⁻¹ ≤ pxi r ^ (r * pI r d) := pxi_pow_ge hr hd
    have h3 : (0:ℝ) ≤ (rdnPowD r d)⁻¹ := by
      rw [rdnPowD]
      exact inv_nonneg.mpr (Real.rpow_pos_of_pos (rdnU_gt0 hr hd) _).le
    nlinarith [mul_le_mul h1 h2 h3 hp.le]
  have hle : (1/2) * (rdnPowD r d)⁻¹ * ((11.75:ℝ)*(r:ℝ)*pD r d σ/2) ≤ calT r d σ := by
    have h5 : (1/2) * (rdnPowD r d)⁻¹ * ((11.75:ℝ)*(r:ℝ)*pD r d σ/2)
        ≤ pxi r * pxi r ^ (r*pI r d) * ((11.75:ℝ)*(r:ℝ)*pD r d σ/2) :=
      mul_le_mul_of_nonneg_right hpxi (by positivity)
    have h6 : pxi r * pxi r ^ (r*pI r d) * ((11.75:ℝ)*(r:ℝ)*pD r d σ/2) ≤ calT r d σ := by
      rw [calT]
      exact mul_le_mul_of_nonneg_left hT (by positivity)
    linarith
  have hkey : rdnDel r d * pD r d σ
      = (1/2) * (rdnPowD r d)⁻¹ * ((11.75:ℝ)*(r:ℝ)*pD r d σ/2) / (2*(r:ℝ)) := by
    rw [rdnDel]; field_simp; ring
  have hdiv : (1/2) * (rdnPowD r d)⁻¹ * ((11.75:ℝ)*(r:ℝ)*pD r d σ/2)/(2*(r:ℝ))
      ≤ calT r d σ/(2*(r:ℝ)) := div_le_div_of_nonneg_right hle (by positivity)
  linarith

/-- `(N+k).choose k ≥ (δ pD)^k / k!`. -/
theorem binom_bound {r d : ℕ} (σ : Fin r → ℝ) (m k : ℕ) (hQnn : 0 ≤ pD r d σ)
    (hδ : 0 ≤ rdnDel r d)
    (hT : rdnDel r d * pD r d σ ≤ (halfSplit r (calT r d σ) m : ℝ) + 1) :
    (rdnDel r d * pD r d σ)^k / (k.factorial : ℝ)
      ≤ ((halfSplit r (calT r d σ) m + k).choose k : ℝ) := by
  have h1 : ((halfSplit r (calT r d σ) m : ℝ) + 1)^k
      ≤ ((halfSplit r (calT r d σ) m + k).choose k : ℝ) * (k.factorial : ℝ) := by
    simpa using (choose_ge (halfSplit r (calT r d σ) m) k)
  have hδQ : 0 ≤ rdnDel r d * pD r d σ := mul_nonneg hδ hQnn
  have h2 : (rdnDel r d * pD r d σ)^k
      ≤ ((halfSplit r (calT r d σ) m : ℝ) + 1)^k := pow_le_pow_left₀ hδQ hT k
  have hkf : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  calc (rdnDel r d * pD r d σ)^k / (k.factorial : ℝ)
      ≤ ((halfSplit r (calT r d σ) m : ℝ) + 1)^k / (k.factorial : ℝ) :=
        div_le_div_of_nonneg_right h2 hkf.le
    _ ≤ ((halfSplit r (calT r d σ) m + k).choose k : ℝ) := by
        rw [div_le_iff₀ hkf]
        linarith

/-- `Work.BW.rdnNumA`, proved here. -/
theorem numA {r ρ : ℕ} (hr : 2 ≤ r) (hρ1 : 1 ≤ ρ) (hρr : ρ < r) (d : ℕ) (hd : 1 ≤ d)
    (h : ℕ) (hh : 1 ≤ h) :
    constA r ρ * (rdnGam r d) ^ ρ * rdnC r d * ((ρ - 1).factorial : ℝ) ≤
      (64 * (r : ℝ) * (d : ℝ)) ^ (r - ρ) * 8 * (d : ℝ) * (h : ℝ) * rdnPC r d *
        (rdnDel r d) ^ (ρ - 1) := by
  have hr1 : 1 ≤ r := by omega
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hh1 : (1:ℝ) ≤ (h:ℝ) := by exact_mod_cast hh
  have hr0 : (0:ℝ) < (r:ℝ) := by linarith
  have hd0 : (0:ℝ) < (d:ℝ) := by linarith
  have hρ0 : (0:ℝ) < (ρ:ℝ) := by exact_mod_cast hρ1
  have hρle : ρ ≤ r := le_of_lt hρr
  have hρle' : (ρ:ℝ) ≤ (r:ℝ) := by exact_mod_cast hρle
  have hu : 0 < rdnU r d := rdnU_gt0 hr hd
  have hu1 : (1:ℝ) ≤ rdnU r d := rdnU_ge1 hr hd
  have hlog2 : (34.65:ℝ) ≤ 50 * Real.log 2 := by have := Real.log_two_gt_d9; linarith
  set E : ℝ := 26.8 + (ρ:ℝ)*(1+50*Real.log 2) - rdnCap r*((ρ:ℝ)-1) with hEdef
  have hE1 : (39.2:ℝ) + 8.85*(ρ:ℝ) ≤ E := by
    have hcap : rdnCap r * ((ρ:ℝ) - 1) ≤ 26.8 * ((ρ:ℝ) - 1) + 14.37 := by
      have hden : (0:ℝ) < (r:ℝ) - 0.536 := by linarith
      have hfr : ((ρ:ℝ)-1) / ((r:ℝ)-0.536) ≤ 1 := by
        rw [div_le_one hden]; linarith
      have hid : 26.8*(r:ℝ)/((r:ℝ)-0.536) * ((ρ:ℝ)-1)
          = 26.8*((ρ:ℝ)-1) + 26.8*0.536*(((ρ:ℝ)-1)/((r:ℝ)-0.536)) := by
        field_simp; ring
      rw [rdnCap, hid]
      have h2 : 26.8*0.536*(((ρ:ℝ)-1)/((r:ℝ)-0.536)) ≤ 26.8*0.536 :=
        mul_le_of_le_one_right (by norm_num) hfr
      nlinarith [h2]
    have h3 : (ρ:ℝ)*(1+34.65) ≤ (ρ:ℝ)*(1+50*Real.log 2) :=
      mul_le_mul_of_nonneg_left (by linarith [hlog2]) (le_of_lt hρ0)
    rw [hEdef]
    nlinarith [hcap, h3]
  have hcond_a : 2*(ρ:ℝ) + 5*(r:ℝ) + 7 ≤ 6*((r:ℝ)-(ρ:ℝ)) + 3 + E := by
    rw [hEdef]; linarith [hE1]
  have hcond_b : (r:ℝ) + 6*(ρ:ℝ) + 1 ≤ ((r:ℝ) - (ρ:ℝ)) + E := by
    rw [hEdef]; linarith [hE1]
  have hcond_c : (r:ℝ) + 2 ≤ ((r:ℝ) - (ρ:ℝ)) + E := by
    rw [hEdef]; linarith [hE1]
  have hγ : ((ρ:ℝ)*(1+50*Real.log 2)) = (ρ:ℝ) + (50*Real.log 2)*(ρ:ℝ) := by ring
  have hKL : (rdnU r d)^((ρ:ℝ)*(1+50*Real.log 2)) * (rdnGam r d)^ρ = (4:ℝ)^ρ := by
    have h1 : (rdnGam r d)^ρ = (4:ℝ)^ρ / ((rdnU r d)^ρ * ((rdnU r d)^(50*Real.log 2))^ρ) := by
      rw [rdnGam, div_pow, mul_pow]
    rw [h1]
    have h2 : ((rdnU r d)^(50*Real.log 2))^ρ = (rdnU r d)^((50*Real.log 2)*(ρ:ℝ)) := by
      rw [← Real.rpow_natCast ((rdnU r d)^(50*Real.log 2)) ρ, ← Real.rpow_mul hu.le]
    rw [h2]
    have h3 : (rdnU r d)^ρ * (rdnU r d)^((50*Real.log 2)*(ρ:ℝ))
        = (rdnU r d)^((ρ:ℝ) + (50*Real.log 2)*(ρ:ℝ)) := by
      rw [← Real.rpow_natCast (rdnU r d) ρ, ← Real.rpow_add hu]
    rw [h3, ← hγ]
    rw [div_eq_mul_inv]
    rw [show (rdnU r d)^((ρ:ℝ)*(1+50*Real.log 2)) * ((4:ℝ)^ρ * ((rdnU r d)^((ρ:ℝ)*(1+50*Real.log 2)))⁻¹)
        = (4:ℝ)^ρ * ((rdnU r d)^((ρ:ℝ)*(1+50*Real.log 2)) * ((rdnU r d)^((ρ:ℝ)*(1+50*Real.log 2)))⁻¹) by ring,
      mul_inv_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos hu _)), mul_one]
  have hKR : (rdnU r d)^((ρ:ℝ)*(1+50*Real.log 2)) * rdnPC r d * (rdnDel r d)^(ρ-1)
      = (11.75/8)^(ρ-1) * (rdnU r d)^E := by
    have hpow : (rdnDel r d)^(ρ-1)
        = (11.75/8)^(ρ-1) * (rdnU r d)^(-(rdnCap r*((ρ:ℝ)-1))) := by
      have hpowD : ((rdnU r d)^(rdnCap r))^(ρ-1) = (rdnU r d)^(rdnCap r*((ρ:ℝ)-1)) := by
        rw [← Real.rpow_natCast ((rdnU r d)^(rdnCap r)) (ρ-1), ← Real.rpow_mul hu.le]
        congr 1
        have : ((ρ-1:ℕ):ℝ) = (ρ:ℝ)-1 := by rw [Nat.cast_sub hρ1]; norm_num
        rw [this]
      have h1 : (11.75 / (8 * (rdnU r d)^(rdnCap r)))^(ρ-1)
          = (11.75/8)^(ρ-1) * (((rdnU r d)^(rdnCap r))^(ρ-1))⁻¹ := by
        have hne : ((rdnU r d)^(rdnCap r)) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hu _)
        rw [show (11.75:ℝ) / (8 * (rdnU r d)^(rdnCap r))
            = (11.75/8) * ((rdnU r d)^(rdnCap r))⁻¹ by field_simp]
        rw [mul_pow, inv_pow]
      rw [rdnDel, rdnPowD, h1, hpowD, ← Real.rpow_neg hu.le]
    rw [hpow]
    have hexp : ((ρ:ℝ)*(1+50*Real.log 2)) + 26.8 + (-(rdnCap r*((ρ:ℝ)-1))) = E := by
      rw [hEdef, hγ]; ring
    have hcomb : (rdnU r d)^((ρ:ℝ)*(1+50*Real.log 2)) * (rdnU r d)^(26.8:ℝ) *
          ((rdnU r d)^(-(rdnCap r*((ρ:ℝ)-1))))
        = (rdnU r d)^E := by
      rw [← Real.rpow_add hu, ← Real.rpow_add hu, hexp]
    have hQ : (rdnU r d)^((ρ:ℝ)*(1+50*Real.log 2)) * rdnPC r d * ((11.75/8)^(ρ-1) * (rdnU r d)^(-(rdnCap r*((ρ:ℝ)-1))))
        = (11.75/8)^(ρ-1) * ((rdnU r d)^((ρ:ℝ)*(1+50*Real.log 2)) * (rdnU r d)^(26.8:ℝ) * (rdnU r d)^(-(rdnCap r*((ρ:ℝ)-1)))) := by
      rw [rdnPC]; ring
    rw [hQ, hcomb]
  have hCnn : (0:ℝ) ≤ rdnC r d := by
    have := rdnL_nonneg hr hd; rw [rdnC]; positivity
  have hXnn : (0:ℝ) ≤ 2*(r:ℝ)^r * ((32:ℝ)*(d:ℝ))^(r+1) * (rdnU r d) := by positivity
  have hR2 : (0:ℝ) ≤ (ρ:ℝ)^(2*ρ) * (r:ℝ)^(3*ρ) := by positivity
  have hRAn : (0:ℝ) ≤ ((ρ:ℝ)^(2*ρ) * (r:ℝ)^(3*ρ)) * (2:ℝ)^(2*ρ) *
        (2*(r:ℝ)^r * ((32:ℝ)*(d:ℝ))^(r+1) * (rdnU r d)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (by positivity)) hXnn
  have hlog_le : Real.log (rdnU r d) ≤ rdnU r d := by
    have := Real.log_le_sub_one_of_pos hu; linarith
  have hfact : ((ρ-1).factorial : ℝ) ≤ (ρ:ℝ)^ρ := by
    have h1 : ((ρ-1).factorial : ℝ) ≤ (ρ.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega : ρ - 1 ≤ ρ)
    have h2 : (ρ.factorial : ℝ) ≤ (ρ:ℝ)^ρ := by exact_mod_cast (Nat.factorial_le_pow ρ)
    linarith [h1, h2]
  have hconstA : constA r ρ ≤ (ρ:ℝ)^(2*ρ) * (r:ℝ)^(3*ρ) := by
    have h1 : (2:ℝ)^(1-(ρ:ℤ)) ≤ 1 := by
      have h2 : (2:ℝ)^(1-(ρ:ℤ)) = 2 / (2:ℝ)^ρ := by
        rw [zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0), zpow_one, zpow_natCast]
      rw [h2, div_le_one (by positivity)]
      simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hρ1
    have h2 : ((ρ.factorial:ℝ))^2 ≤ (ρ:ℝ)^(2*ρ) := by
      have hf : (ρ.factorial:ℝ) ≤ (ρ:ℝ)^ρ := by exact_mod_cast (Nat.factorial_le_pow ρ)
      calc ((ρ.factorial:ℝ))^2 ≤ ((ρ:ℝ)^ρ)^2 := pow_le_pow_left₀ (by positivity) hf 2
        _ = (ρ:ℝ)^(2*ρ) := by ring_nf
    have hdesc : ((r+1).descFactorial ρ : ℝ) ≤ (r:ℝ)^(2*ρ) := by
      have hd1' : ((r+1).descFactorial ρ : ℝ) ≤ ((r:ℝ)+1)^ρ := by
        have := Nat.descFactorial_le_pow (r+1) ρ
        push_cast
        exact_mod_cast this
      have hd2 : ((r:ℝ)+1)^ρ ≤ ((2:ℝ)*(r:ℝ))^ρ :=
        pow_le_pow_left₀ (by linarith) (by linarith) ρ
      have hd3 : ((2:ℝ)*(r:ℝ))^ρ = (2:ℝ)^ρ*(r:ℝ)^ρ := mul_pow _ _ _
      have hd4 : (2:ℝ)^ρ ≤ (r:ℝ)^ρ := pow_le_pow_left₀ (by norm_num) hr2 ρ
      have hd5 : (2:ℝ)^ρ*(r:ℝ)^ρ ≤ (r:ℝ)^ρ*(r:ℝ)^ρ :=
        mul_le_mul_of_nonneg_right hd4 (by positivity)
      have hd6 : (r:ℝ)^ρ*(r:ℝ)^ρ = (r:ℝ)^(2*ρ) := by ring_nf
      linarith [hd1', hd2, hd3, hd4, hd5, hd6]
    rw [constA]
    calc (2:ℝ)^(1-(ρ:ℤ)) * ((ρ.factorial:ℝ))^2 * (r:ℝ)^ρ * ((r+1).descFactorial ρ : ℝ)
        ≤ ((1:ℝ) * (ρ:ℝ)^(2*ρ)) * (r:ℝ)^ρ * (r:ℝ)^(2*ρ) :=
          mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (by positivity) (by norm_num))
            (le_refl _) (by positivity) (by positivity)) hdesc (by positivity) (by positivity)
      _ = (ρ:ℝ)^(2*ρ) * (r:ℝ)^(3*ρ) := by rw [one_mul]; ring_nf
  have hCbound : rdnC r d ≤ 2*(r:ℝ)^r * ((32:ℝ)*(d:ℝ))^(r+1) * (rdnU r d) := by
    rw [rdnC, rdnL]
    exact mul_le_mul_of_nonneg_left hlog_le (by positivity)
  have hLHS1 : constA r ρ * (4:ℝ)^ρ * rdnC r d * ((ρ-1).factorial:ℝ)
      ≤ ((ρ:ℝ)^(2*ρ) * (r:ℝ)^(3*ρ)) * (4:ℝ)^ρ * rdnC r d * ((ρ-1).factorial:ℝ) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconstA (by positivity)) (by positivity))
      (by positivity)
  have hLHS2 : ((ρ:ℝ)^(2*ρ) * (r:ℝ)^(3*ρ)) * (4:ℝ)^ρ * rdnC r d * ((ρ-1).factorial:ℝ)
      ≤ ((ρ:ℝ)^(2*ρ) * (r:ℝ)^(3*ρ)) * (2:ℝ)^(2*ρ) *
          (2*(r:ℝ)^r * ((32:ℝ)*(d:ℝ))^(r+1) * (rdnU r d)) * ((ρ-1).factorial:ℝ) := by
    have h4 : (4:ℝ)^ρ = (2:ℝ)^(2*ρ) := by rw [show (4:ℝ) = 2^2 by norm_num, pow_mul]
    have hmid : (4:ℝ)^ρ * rdnC r d ≤ (2:ℝ)^(2*ρ) * (2*(r:ℝ)^r * ((32:ℝ)*(d:ℝ))^(r+1) * (rdnU r d)) := by
      rw [h4]
      exact mul_le_mul (le_refl _) hCbound (by positivity) (by positivity)
    have ht : ((ρ:ℝ)^(2*ρ) * (r:ℝ)^(3*ρ)) * ((4:ℝ)^ρ * rdnC r d)
        ≤ ((ρ:ℝ)^(2*ρ) * (r:ℝ)^(3*ρ)) * ((2:ℝ)^(2*ρ) * (2*(r:ℝ)^r * ((32:ℝ)*(d:ℝ))^(r+1) * (rdnU r d))) :=
      mul_le_mul_of_nonneg_left hmid (by positivity : (0:ℝ) ≤ (ρ:ℝ)^(2*ρ) * (r:ℝ)^(3*ρ))
    have ht2 := mul_le_mul_of_nonneg_right ht (by positivity : (0:ℝ) ≤ ((ρ-1).factorial:ℝ))
    convert ht2 using 1 <;> ring
  have hLHS3 : ((ρ:ℝ)^(2*ρ) * (r:ℝ)^(3*ρ)) * (2:ℝ)^(2*ρ) *
          (2*(r:ℝ)^r * ((32:ℝ)*(d:ℝ))^(r+1) * (rdnU r d)) * ((ρ-1).factorial:ℝ)
      ≤ ((ρ:ℝ)^(2*ρ) * (r:ℝ)^(3*ρ)) * (2:ℝ)^(2*ρ) *
          (2*(r:ℝ)^r * ((32:ℝ)*(d:ℝ))^(r+1) * (rdnU r d)) * ((ρ:ℝ)^ρ) :=
    mul_le_mul_of_nonneg_left hfact hRAn
  have hLHS4 : ((ρ:ℝ)^(2*ρ) * (r:ℝ)^(3*ρ)) * (2:ℝ)^(2*ρ) *
          (2*(r:ℝ)^r * ((32:ℝ)*(d:ℝ))^(r+1) * (rdnU r d)) * ((ρ:ℝ)^ρ)
      ≤ 2^(2*ρ+5*r+7) * (r:ℝ)^(r+6*ρ+1) * (d:ℝ)^(r+2) := by
    have h32 : ((32:ℝ)*(d:ℝ))^(r+1) = (2:ℝ)^(5*(r+1)) * (d:ℝ)^(r+1) := by
      rw [show ((32:ℝ)*(d:ℝ)) = (2:ℝ)^5 * (d:ℝ) by ring, mul_pow, ← pow_mul]
    have hρ3 : (ρ:ℝ)^(3*ρ) ≤ (r:ℝ)^(3*ρ) := pow_le_pow_left₀ (by positivity) hρle' (3*ρ)
    rw [h32, show rdnU r d = 2*(r:ℝ)*(d:ℝ) from rfl]
    have hstep : ((ρ:ℝ)^(2*ρ) * (r:ℝ)^(3*ρ)) * (2:ℝ)^(2*ρ) *
          (2*(r:ℝ)^r * ((2:ℝ)^(5*(r+1)) * (d:ℝ)^(r+1)) * (2*(r:ℝ)*(d:ℝ))) * ((ρ:ℝ)^ρ)
        = (ρ:ℝ)^(3*ρ) * ((r:ℝ)^(3*ρ) * (r:ℝ)^r * (r:ℝ)) *
          ((2:ℝ)^(2*ρ) * 2 * (2:ℝ)^(5*(r+1)) * 2) * ((d:ℝ)^(r+1) * (d:ℝ)) := by ring_nf
    rw [hstep]
    have hstep2 : (ρ:ℝ)^(3*ρ) * ((r:ℝ)^(3*ρ) * (r:ℝ)^r * (r:ℝ)) *
          ((2:ℝ)^(2*ρ) * 2 * (2:ℝ)^(5*(r+1)) * 2) * ((d:ℝ)^(r+1) * (d:ℝ))
        ≤ (r:ℝ)^(3*ρ) * ((r:ℝ)^(3*ρ) * (r:ℝ)^r * (r:ℝ)) *
          ((2:ℝ)^(2*ρ) * 2 * (2:ℝ)^(5*(r+1)) * 2) * ((d:ℝ)^(r+1) * (d:ℝ)) := by
      have h := mul_le_mul_of_nonneg_left hρ3 (by positivity : (0:ℝ) ≤
        ((r:ℝ)^(3*ρ) * (r:ℝ)^r * (r:ℝ)) * ((2:ℝ)^(2*ρ) * 2 * (2:ℝ)^(5*(r+1)) * 2) * ((d:ℝ)^(r+1) * (d:ℝ)))
      convert h using 1 <;> ring
    exact le_trans hstep2 (le_of_eq (by ring_nf))
  have hLHSb := hLHS1.trans (hLHS2.trans (hLHS3.trans hLHS4))
  have hMID : 2^(2*ρ+5*r+7) * (r:ℝ)^(r+6*ρ+1) * (d:ℝ)^(r+2)
      ≤ 2^(6*(r-ρ)+3) * (2:ℝ)^E * (r:ℝ)^(r-ρ+E) * (d:ℝ)^(r-ρ+E) := by
    have h1 : (2:ℝ)^(2*ρ+5*r+7) ≤ 2^(6*(r-ρ)+3) * (2:ℝ)^E := by
      rw [← Real.rpow_natCast (2:ℝ) (2*ρ+5*r+7), ← Real.rpow_natCast (2:ℝ) (6*(r-ρ)+3),
        ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      push_cast [Nat.cast_sub hρle]
      linarith [hcond_a]
    have h2 : (r:ℝ)^(r+6*ρ+1) ≤ (r:ℝ)^(r-ρ+E) := by
      rw [← Real.rpow_natCast (r:ℝ) (r+6*ρ+1),
        show ((r:ℝ) - (ρ:ℝ) + E) = (((r-ρ:ℕ):ℝ) + E) by push_cast [Nat.cast_sub hρle]; ring]
      apply Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ (r:ℝ))
      push_cast [Nat.cast_sub hρle]
      linarith [hcond_b]
    have h3 : (d:ℝ)^(r+2) ≤ (d:ℝ)^(r-ρ+E) := by
      rw [← Real.rpow_natCast (d:ℝ) (r+2),
        show ((r:ℝ) - (ρ:ℝ) + E) = (((r-ρ:ℕ):ℝ) + E) by push_cast [Nat.cast_sub hρle]; ring]
      apply Real.rpow_le_rpow_of_exponent_le hd1
      push_cast [Nat.cast_sub hρle]
      linarith [hcond_c]
    calc 2^(2*ρ+5*r+7) * (r:ℝ)^(r+6*ρ+1) * (d:ℝ)^(r+2)
        ≤ (2^(6*(r-ρ)+3) * (2:ℝ)^E) * (r:ℝ)^(r-ρ+E) * (d:ℝ)^(r-ρ+E) :=
          mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (by positivity) (by positivity)
      _ = 2^(6*(r-ρ)+3) * (2:ℝ)^E * (r:ℝ)^(r-ρ+E) * (d:ℝ)^(r-ρ+E) := by ring
  have huE : (rdnU r d)^E = (2:ℝ)^E * (r:ℝ)^E * (d:ℝ)^E := by
    rw [rdnU, Real.mul_rpow (by norm_num) (by positivity), Real.mul_rpow (by positivity) (by positivity)]
  have hRHSb : 2^(6*(r-ρ)+3) * (2:ℝ)^E * (r:ℝ)^(r-ρ+E) * (d:ℝ)^(r-ρ+E)
      ≤ (64*(r:ℝ)*(d:ℝ))^(r-ρ)*8*(d:ℝ)*(h:ℝ)*((11.75/8)^(ρ-1)*(rdnU r d)^E) := by
    have h64 : (64*(r:ℝ)*(d:ℝ))^(r-ρ)
        = (2:ℝ)^(6*(r-ρ)) * (r:ℝ)^(r-ρ) * (d:ℝ)^(r-ρ) := by
      rw [show ((64:ℝ)*(r:ℝ)*(d:ℝ)) = ((2:ℝ)^6) * (r:ℝ) * (d:ℝ) by ring,
        mul_pow, mul_pow, ← pow_mul]
    rw [huE, h64]
    have hfac : (1:ℝ) ≤ (d:ℝ)*(h:ℝ)*((11.75/8:ℝ)^(ρ-1)) := by
      have h118 : (1:ℝ) ≤ (11.75/8:ℝ)^(ρ-1) := one_le_pow₀ (by norm_num)
      have hdh : (1:ℝ) ≤ (d:ℝ)*(h:ℝ) := by
        have := mul_le_mul hd1 hh1 (by norm_num) (by norm_num)
        simpa using this
      calc (1:ℝ) = 1*1 := by ring
        _ ≤ (d:ℝ)*(h:ℝ)*((11.75/8:ℝ)^(ρ-1)) :=
            mul_le_mul hdh h118 (by norm_num) (by positivity)
    have hY0 : (0:ℝ) ≤ (2:ℝ)^E * (r:ℝ)^E * (d:ℝ)^E := by positivity
    have hone' : (1:ℝ) * ((2:ℝ)^E * (r:ℝ)^E * (d:ℝ)^E) ≤
        ((d:ℝ)*(h:ℝ)*((11.75/8:ℝ)^(ρ-1))) * ((2:ℝ)^E * (r:ℝ)^E * (d:ℝ)^E) :=
      mul_le_mul_of_nonneg_right hfac hY0
    have hfin : 8 * ((2:ℝ)^E * (r:ℝ)^E * (d:ℝ)^E)
        ≤ 8 * (((d:ℝ)*(h:ℝ)*((11.75/8:ℝ)^(ρ-1))) * ((2:ℝ)^E * (r:ℝ)^E * (d:ℝ)^E)) :=
      mul_le_mul_of_nonneg_left (by simpa using hone') (by norm_num)
    have heq1 : 2^(6*(r-ρ)+3) * (2:ℝ)^E * (r:ℝ)^(r-ρ+E) * (d:ℝ)^(r-ρ+E)
        = (2:ℝ)^(6*(r-ρ)) * (r:ℝ)^(r-ρ) * (d:ℝ)^(r-ρ) * (8 * ((2:ℝ)^E * (r:ℝ)^E * (d:ℝ)^E)) := by
      have hr1' : (r:ℝ)^(r-ρ+E) = (r:ℝ)^(r-ρ) * (r:ℝ)^E := by
        rw [← Real.rpow_natCast (r:ℝ) (r-ρ), ← Real.rpow_add (by positivity),
          show ((r:ℝ) - (ρ:ℝ) + E) = (((r-ρ:ℕ):ℝ) + E) by rw [Nat.cast_sub hρle]]
      have hr2' : (d:ℝ)^(r-ρ+E) = (d:ℝ)^(r-ρ) * (d:ℝ)^E := by
        rw [← Real.rpow_natCast (d:ℝ) (r-ρ), ← Real.rpow_add (by positivity),
          show ((r:ℝ) - (ρ:ℝ) + E) = (((r-ρ:ℕ):ℝ) + E) by rw [Nat.cast_sub hρle]]
      rw [hr1', hr2']
      rw [show (2:ℝ)^(6*(r-ρ)+3) = (2:ℝ)^(6*(r-ρ)) * 8 by rw [pow_add]; norm_num]
      ring
    rw [heq1]
    exact le_trans (mul_le_mul_of_nonneg_left hfin (by positivity)) (le_of_eq (by ring_nf))
  have hAB := hLHSb.trans (hMID.trans hRHSb)
  have h1 : (rdnU r d)^((ρ:ℝ)*(1+50*Real.log 2)) *
        (constA r ρ * (rdnGam r d)^ρ * rdnC r d * ((ρ-1).factorial:ℝ))
      = constA r ρ * (4:ℝ)^ρ * rdnC r d * ((ρ-1).factorial:ℝ) := by
    rw [← hKL]; ring
  have h2 : (rdnU r d)^((ρ:ℝ)*(1+50*Real.log 2)) *
        ((64*(r:ℝ)*(d:ℝ))^(r-ρ)*8*(d:ℝ)*(h:ℝ)*rdnPC r d*(rdnDel r d)^(ρ-1))
      = (64*(r:ℝ)*(d:ℝ))^(r-ρ)*8*(d:ℝ)*(h:ℝ)*((11.75/8)^(ρ-1)*(rdnU r d)^E) := by
    rw [← hKR]; ring
  have hmul : (rdnU r d)^((ρ:ℝ)*(1+50*Real.log 2)) *
        (constA r ρ * (rdnGam r d)^ρ * rdnC r d * ((ρ-1).factorial:ℝ))
      ≤ (rdnU r d)^((ρ:ℝ)*(1+50*Real.log 2)) *
        ((64*(r:ℝ)*(d:ℝ))^(r-ρ)*8*(d:ℝ)*(h:ℝ)*rdnPC r d*(rdnDel r d)^(ρ-1)) := by
    rw [h1, h2]; exact hAB
  exact le_of_mul_le_mul_left hmul (Real.rpow_pos_of_pos hu _)

theorem rdn_aux_pow {r d : ℕ} (hd : 1 ≤ d) :
    ((32:ℝ)*(d:ℝ))^(r+1) * (1/(d:ℝ))^r = (32:ℝ)^(r+1)*(d:ℝ) := by
  have hd0 : (0:ℝ) < (d:ℝ) := by positivity
  rw [mul_pow, div_pow, one_pow, mul_one_div, pow_succ]
  field_simp
  ring

/-- BW §21 numerics, part 2 (the check (30), p. 60–61, redone for the two cases of
`multiplicity_prop` with the half split). -/
theorem rank_drop_numerics {r d h : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (hh : 1 ≤ h) (σ : Fin r → ℝ)
    (hσ : ∀ j, 1 / (d : ℝ) ≤ σ j) (ρ : ℕ) (hρ1 : 1 ≤ ρ) (hρr : ρ < r) (J : Finset (Fin r))
    (hJ : J.card = ρ) :
    constA r ρ * ∏ i ∈ J, (σ i * calD r d h σ i.succ) ≤
        (64 * r * d : ℝ) ^ (r - ρ) * (∏ j, σ j) *
          (((halfSplit r (calS r d h) (ρ - 1) : ℝ) + 1) *
            ((halfSplit r (calT r d σ) (ρ - 1) + (ρ - 1)).choose (ρ - 1) : ℝ)) ∧
      constB r ρ * calD r d h σ 0 * ∏ i ∈ J, (σ i * calD r d h σ i.succ) ≤
        (64 * r * d : ℝ) ^ (r - ρ) * (∏ j, σ j) *
          (((halfSplit r (calS r d h) ρ : ℝ) + 1) *
            ((halfSplit r (calT r d σ) ρ + ρ).choose ρ : ℝ)) := by
  have hr1 : 1 ≤ r := by omega
  have hr2 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hd1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hσpos : ∀ j, 0 < σ j := fun j => lt_of_lt_of_le (by positivity) (hσ j)
  have hσnn : ∀ j, 0 ≤ σ j := fun j => (hσpos j).le
  have hPpos : 0 < ∏ j, σ j := Finset.prod_pos (fun j _ => hσpos j)
  have hQnn : 0 ≤ pD r d σ := pD_nonneg hr hd σ hσnn
  have hQeq : pD r d σ = rdnC r d * ∏ j, σ j := pD_eq_rdnC σ
  have hcA : 0 ≤ constA r ρ := by unfold constA; positivity
  have hcB : 0 ≤ constB r ρ := by unfold constB; positivity
  have hCnn : 0 ≤ rdnC r d := by
    have := rdnL_nonneg hr hd; rw [rdnC]; positivity
  have hPge : (1/(d:ℝ))^r ≤ ∏ j, σ j := by
    have h1 : (1/(d:ℝ))^r = ∏ _j : Fin r, (1/(d:ℝ)) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [h1]
    exact prod_le_prod_nonneg Finset.univ (fun j _ => by positivity) (fun j _ => hσ j)
  have hkey := rdn_aux_pow (r:=r) hd
  have hQ1 : 1 ≤ pD r d σ := by
    have hL1 : 1 ≤ Real.log (2*(r:ℝ)*(d:ℝ)) := rdnL_ge_one hr hd
    have hrr : (1:ℝ) ≤ (r:ℝ)^r := one_le_pow₀ (by linarith)
    have h32d : (1:ℝ) ≤ (32:ℝ)^(r+1)*(d:ℝ) := by
      have h32 : (1:ℝ) ≤ (32:ℝ)^(r+1) := one_le_pow₀ (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right h32 (by linarith : (0:ℝ) ≤ (d:ℝ))]
    have hstep : (1:ℝ) ≤ (2:ℝ)*(r:ℝ)^r*((32:ℝ)*(d:ℝ))^(r+1)*(1/(d:ℝ))^r := by
      have h2 : (2:ℝ)*(r:ℝ)^r*((32:ℝ)*(d:ℝ))^(r+1)*(1/(d:ℝ))^r
          = ((r:ℝ)^r) * (2 * ((32:ℝ)^(r+1)*(d:ℝ))) := by
        rw [← hkey]; ring
      rw [h2]; nlinarith [hrr, h32d]
    rw [pD]
    have hmono : (2:ℝ)*(r:ℝ)^r*((32:ℝ)*(d:ℝ))^(r+1)*(1/(d:ℝ))^r
        ≤ (2:ℝ)*(r:ℝ)^r*((32:ℝ)*(d:ℝ))^(r+1)*(∏ j, σ j) :=
      mul_le_mul_of_nonneg_left hPge (by positivity)
    have hfin : (2:ℝ)*(r:ℝ)^r*((32:ℝ)*(d:ℝ))^(r+1)*(∏ j, σ j)
        ≤ (2:ℝ)*(r:ℝ)^r*((32:ℝ)*(d:ℝ))^(r+1)*Real.log (2*(r:ℝ)*(d:ℝ))*(∏ j, σ j) := by
      have h0 : (0:ℝ) ≤ (2:ℝ)*(r:ℝ)^r*((32:ℝ)*(d:ℝ))^(r+1)*(∏ j, σ j) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hL1 h0]
    linarith
  have hQge2 : 2 ≤ 11.75 * (r:ℝ) * pD r d σ := by nlinarith [hQ1, hr2]
  have hPprod : ∏ i ∈ J, (σ i * calD r d h σ i.succ) ≤ (rdnGam r d * pD r d σ)^ρ := by
    have h := prod_le (h := h) hr hd σ hσpos J
    rwa [hJ] at h
  have hcalDnn : ∀ i : Fin r, 0 ≤ calD r d h σ i.succ := by
    intro i; rw [calD_succ]; positivity
  have hprodn : 0 ≤ ∏ i ∈ J, (σ i * calD r d h σ i.succ) :=
    Finset.prod_nonneg (fun i _ => mul_nonneg (hσpos i).le (hcalDnn i))
  have hDel0 : 0 ≤ rdnDel r d := (rdnDel_pos hr hd).le
  have hXnn : (0:ℝ) ≤ (r:ℝ)^(r+1) * ((32:ℝ)*(d:ℝ))^(r+1) := by positivity
  constructor
  · -- case A
    have hS : 8*(d:ℝ)*(h:ℝ)*rdnPC r d ≤ (halfSplit r (calS r d h) (ρ-1) : ℝ) + 1 :=
      calS_lower hr hd (ρ-1)
    have hT : rdnDel r d * pD r d σ ≤ (halfSplit r (calT r d σ) (ρ-1) : ℝ) + 1 :=
      calT_lower hr hd σ (ρ-1) hQge2 hQnn
    have hbin : (rdnDel r d * pD r d σ)^(ρ-1) / ((ρ-1).factorial : ℝ)
        ≤ ((halfSplit r (calT r d σ) (ρ-1) + (ρ-1)).choose (ρ-1) : ℝ) :=
      binom_bound σ (ρ-1) (ρ-1) hQnn hDel0 hT
    have hnum := numA hr hρ1 hρr d hd h hh
    have hγQ : (rdnGam r d * pD r d σ)^ρ
        = (rdnGam r d)^ρ * (rdnC r d)^ρ * (∏ j, σ j)^ρ := by rw [hQeq]; ring
    have hδQ : (rdnDel r d * pD r d σ)^(ρ-1)
        = (rdnDel r d)^(ρ-1) * (rdnC r d)^(ρ-1) * (∏ j, σ j)^(ρ-1) := by rw [hQeq]; ring
    have hCm : rdnC r d * (rdnC r d)^(ρ-1) = (rdnC r d)^ρ := by
      rw [← pow_succ', Nat.sub_add_cancel hρ1]
    have hPm : (∏ j, σ j) * (∏ j, σ j)^(ρ-1) = (∏ j, σ j)^ρ := by
      rw [← pow_succ', Nat.sub_add_cancel hρ1]
    have hMA : 0 ≤ (rdnC r d)^(ρ-1) * (∏ j, σ j)^ρ / ((ρ-1).factorial : ℝ) :=
      div_nonneg (mul_nonneg (pow_nonneg hCnn _) (pow_nonneg hPpos.le _)) (by positivity)
    have hAB := mul_le_mul_of_nonneg_right hnum hMA
    have hstep2 : constA r ρ * (rdnGam r d * pD r d σ)^ρ
        ≤ (64*(r:ℝ)*(d:ℝ))^(r-ρ) * (∏ j, σ j) *
            (8*(d:ℝ)*(h:ℝ)*rdnPC r d * ((rdnDel r d * pD r d σ)^(ρ-1)/((ρ-1).factorial:ℝ))) := by
      have h1 : constA r ρ * (rdnGam r d * pD r d σ)^ρ
          = constA r ρ * (rdnGam r d)^ρ * rdnC r d * ((ρ-1).factorial : ℝ) *
              ((rdnC r d)^(ρ-1) * (∏ j, σ j)^ρ / ((ρ-1).factorial : ℝ)) := by
        rw [hγQ, ← hCm]; field_simp
      have h2 : (64*(r:ℝ)*(d:ℝ))^(r-ρ) * (∏ j, σ j) *
              (8*(d:ℝ)*(h:ℝ)*rdnPC r d * ((rdnDel r d * pD r d σ)^(ρ-1)/((ρ-1).factorial:ℝ)))
          = (64*(r:ℝ)*(d:ℝ))^(r-ρ) * 8*(d:ℝ)*(h:ℝ)*rdnPC r d * (rdnDel r d)^(ρ-1) *
              ((rdnC r d)^(ρ-1) * (∏ j, σ j)^ρ / ((ρ-1).factorial : ℝ)) := by
        rw [hδQ, ← hPm]; field_simp
      rw [h1, h2]; exact hAB
    have hinner : 8*(d:ℝ)*(h:ℝ)*rdnPC r d * ((rdnDel r d * pD r d σ)^(ρ-1)/((ρ-1).factorial:ℝ))
        ≤ ((halfSplit r (calS r d h) (ρ-1) : ℝ) + 1) *
            ((halfSplit r (calT r d σ) (ρ-1) + (ρ-1)).choose (ρ-1) : ℝ) :=
      mul_le_mul hS hbin (by positivity) (by positivity)
    have hstep3 := mul_le_mul_of_nonneg_left hinner
      (by positivity : (0:ℝ) ≤ (64*(r:ℝ)*(d:ℝ))^(r-ρ) * (∏ j, σ j))
    have hstep1 : constA r ρ * ∏ i ∈ J, (σ i * calD r d h σ i.succ)
        ≤ constA r ρ * (rdnGam r d * pD r d σ)^ρ := mul_le_mul_of_nonneg_left hPprod hcA
    linarith [hstep1, hstep2, hstep3]
  · -- case B
    have hS : 8*(d:ℝ)*(h:ℝ)*rdnPC r d ≤ (halfSplit r (calS r d h) ρ : ℝ) + 1 :=
      calS_lower hr hd ρ
    have hT : rdnDel r d * pD r d σ ≤ (halfSplit r (calT r d σ) ρ : ℝ) + 1 :=
      calT_lower hr hd σ ρ hQge2 hQnn
    have hbin : (rdnDel r d * pD r d σ)^ρ / (ρ.factorial : ℝ)
        ≤ ((halfSplit r (calT r d σ) ρ + ρ).choose ρ : ℝ) :=
      binom_bound σ ρ ρ hQnn hDel0 hT
    have hnum := rdnNumB hr hρ1 hρr d hd
    have hone : 1 ≤ (r:ℝ)^(r+1) * ((32:ℝ)*(d:ℝ))^(r+1) * ∏ j, σ j := by
      have hrr : (1:ℝ) ≤ (r:ℝ)^(r+1) := one_le_pow₀ (by linarith)
      have h32d : (1:ℝ) ≤ (32:ℝ)^(r+1)*(d:ℝ) := by
        have h32 : (1:ℝ) ≤ (32:ℝ)^(r+1) := one_le_pow₀ (by norm_num)
        nlinarith [mul_le_mul_of_nonneg_right h32 (by linarith : (0:ℝ) ≤ (d:ℝ))]
      have h2 : (1:ℝ) ≤ ((32:ℝ)*(d:ℝ))^(r+1) * (∏ j, σ j) := by
        have h3 : ((32:ℝ)*(d:ℝ))^(r+1) * (1/(d:ℝ))^r ≤ ((32:ℝ)*(d:ℝ))^(r+1)*(∏ j, σ j) :=
          mul_le_mul_of_nonneg_left hPge (by positivity)
        rw [hkey] at h3
        linarith
      have h4 : (1:ℝ) * 1 ≤ (r:ℝ)^(r+1) * (((32:ℝ)*(d:ℝ))^(r+1) * (∏ j, σ j)) :=
        mul_le_mul hrr h2 (by norm_num) (by linarith)
      linarith [h4, mul_assoc ((r:ℝ)^(r+1)) (((32:ℝ)*(d:ℝ))^(r+1)) (∏ j, σ j)]
    have hcalD0 : calD r d h σ 0 ≤ 2*(h:ℝ)*(r:ℝ)^(r+1) * ((32:ℝ)*(d:ℝ))^(r+1) * ∏ j, σ j := by
      rw [calD_zero]
      have hb := pD0_le hr hd σ hPpos.le hone
      have hb2 := mul_le_mul_of_nonneg_left hb (le_of_lt (by positivity : (0:ℝ) < (h:ℝ)))
      calc (h:ℝ) * ((pD0 r d σ : ℝ) + 1)
          ≤ (h:ℝ) * (2*(r:ℝ)^(r+1) * ((32:ℝ)*(d:ℝ))^(r+1) * ∏ j, σ j) := hb2
        _ = 2*(h:ℝ)*(r:ℝ)^(r+1) * ((32:ℝ)*(d:ℝ))^(r+1) * ∏ j, σ j := by ring
    have hγQ : (rdnGam r d * pD r d σ)^ρ
        = (rdnGam r d)^ρ * (rdnC r d)^ρ * (∏ j, σ j)^ρ := by rw [hQeq]; ring
    have hδQ : (rdnDel r d * pD r d σ)^ρ
        = (rdnDel r d)^ρ * (rdnC r d)^ρ * (∏ j, σ j)^ρ := by rw [hQeq]; ring
    have hPm2 : (∏ j, σ j) * (∏ j, σ j)^ρ = (∏ j, σ j)^(ρ+1) := by rw [pow_succ']
    have hMB : 0 ≤ (rdnC r d)^ρ * (∏ j, σ j)^(ρ+1) / (ρ.factorial : ℝ) :=
      div_nonneg (mul_nonneg (pow_nonneg hCnn _) (pow_nonneg hPpos.le _)) (by positivity)
    have hAB := mul_le_mul_of_nonneg_right hnum hMB
    have hstep2 : constB r ρ * (2*(h:ℝ)*(r:ℝ)^(r+1) * ((32:ℝ)*(d:ℝ))^(r+1) * ∏ j, σ j)
            * (rdnGam r d * pD r d σ)^ρ
        ≤ (64*(r:ℝ)*(d:ℝ))^(r-ρ) * (∏ j, σ j) *
            (8*(d:ℝ)*(h:ℝ)*rdnPC r d * ((rdnDel r d * pD r d σ)^ρ/(ρ.factorial:ℝ))) := by
      have h1 : constB r ρ * (2*(h:ℝ)*(r:ℝ)^(r+1) * ((32:ℝ)*(d:ℝ))^(r+1) * ∏ j, σ j)
              * (rdnGam r d * pD r d σ)^ρ
          = 2*(h:ℝ) * (constB r ρ * ((r:ℝ)^(r+1) * ((32:ℝ)*(d:ℝ))^(r+1)) * (rdnGam r d)^ρ
              * (ρ.factorial:ℝ) * ((rdnC r d)^ρ * (∏ j, σ j)^(ρ+1) / (ρ.factorial:ℝ))) := by
        rw [hγQ, ← hPm2]; field_simp
      have h2 : (64*(r:ℝ)*(d:ℝ))^(r-ρ) * (∏ j, σ j) *
              (8*(d:ℝ)*(h:ℝ)*rdnPC r d * ((rdnDel r d * pD r d σ)^ρ/(ρ.factorial:ℝ)))
          = 2*(h:ℝ) * ((64*(r:ℝ)*(d:ℝ))^(r-ρ) * 4 * (d:ℝ) * rdnPC r d * (rdnDel r d)^ρ
              * ((rdnC r d)^ρ * (∏ j, σ j)^(ρ+1) / (ρ.factorial : ℝ))) := by
        rw [hδQ, ← hPm2]; field_simp; ring
      rw [h1, h2]
      exact mul_le_mul_of_nonneg_left hAB (by positivity)
    have hinner : 8*(d:ℝ)*(h:ℝ)*rdnPC r d * ((rdnDel r d * pD r d σ)^ρ/(ρ.factorial:ℝ))
        ≤ ((halfSplit r (calS r d h) ρ : ℝ) + 1) *
            ((halfSplit r (calT r d σ) ρ + ρ).choose ρ : ℝ) :=
      mul_le_mul hS hbin (by positivity) (by positivity)
    have hstep3 := mul_le_mul_of_nonneg_left hinner
      (by positivity : (0:ℝ) ≤ (64*(r:ℝ)*(d:ℝ))^(r-ρ) * (∏ j, σ j))
    have hstep1 : constB r ρ * calD r d h σ 0 * ∏ i ∈ J, (σ i * calD r d h σ i.succ)
        ≤ constB r ρ * (2*(h:ℝ)*(r:ℝ)^(r+1) * ((32:ℝ)*(d:ℝ))^(r+1) * ∏ j, σ j)
            * (rdnGam r d * pD r d σ)^ρ := by
      have h1 : constB r ρ * calD r d h σ 0 * ∏ i ∈ J, (σ i * calD r d h σ i.succ)
          ≤ constB r ρ * (2*(h:ℝ)*(r:ℝ)^(r+1) * ((32:ℝ)*(d:ℝ))^(r+1) * ∏ j, σ j)
              * ∏ i ∈ J, (σ i * calD r d h σ i.succ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcalD0 hcB) hprodn
      have h2 : 0 ≤ constB r ρ * (2*(h:ℝ)*(r:ℝ)^(r+1) * ((32:ℝ)*(d:ℝ))^(r+1) * ∏ j, σ j) := by
        positivity
      exact le_trans h1 (mul_le_mul_of_nonneg_left hPprod h2)
    linarith [hstep1, hstep2, hstep3]

end Work.BW
