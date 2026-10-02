import Mathlib
import Submission.Work.LinnikBurgess.lf_defs
import Submission.Work.LinnikBurgess.peel_gauss_sum_bound
import Submission.Work.LinnikBurgess.critN_ne_zero_of_unique
import Submission.Work.LinnikBurgess.natDegree_critN_le_four
import Submission.Work.LinnikBurgess.critN_tripleVanish_content
import Submission.Work.LinnikBurgess.cubeLevel_add_bval_le
import Submission.Work.LinnikBurgess.card_hensel_le
import Submission.Work.LinnikBurgess.lfSmall.content_dvd_critN
import Submission.Work.LinnikBurgess.u8three.transfer_three
import Submission.Work.LinnikBurgess.u8three.lvlSet_card_three
import Submission.Work.LinnikAreas.u8three.capSet_three_bound

open scoped BigOperators
open Classical
open Work.LinnikBurgess

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.LinnikAreas.u8three.core

/-! ## Temporary stubs for the three delegated counting lemmas -/

theorem stub_transfer_three {e : ℕ} (he : 2 ≤ e) (a b : Fin 3 → ℕ) :     SuppTransfer 3 e a b :=
  Work.LinnikBurgess.u8three.transfer_three he a b

theorem stub_lvlSet_card_three {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ)     (hN : critN a b ≠ 0) (hdeg : (critN a b).natDegree ≤ 4)     (hbt : SuppTransfer 3 e a b) {s : ℕ} (hs : s < capLevel 3 e) :     (lvlSet 3 e a b s).card ≤ 4 :=
  Work.LinnikBurgess.u8three.lvlSet_card_three he a b hN hdeg hbt hs

/-! ## Arithmetic of `cubeLevel 3` and `capLevel 3` -/

theorem cubeLevel_three (e : ℕ) : cubeLevel 3 e = (e + 2) / 3 := by
  rw [cubeLevel, if_neg (by norm_num : ¬ (3 = 2))]

theorem capLevel_three (e : ℕ) : capLevel 3 e = e - 2 * ((e + 2) / 3) := by
  rw [capLevel, cubeLevel_three]

theorem capLevel_le_cubeLevel_three (e : ℕ) : capLevel 3 e ≤ cubeLevel 3 e := by
  rw [capLevel_three, cubeLevel_three]
  have h := Nat.div_add_mod (e + 2) 3
  have h' := Nat.mod_lt (e + 2) (by norm_num : 0 < 3)
  omega

theorem capLevel_le_self_three (e : ℕ) : capLevel 3 e ≤ e := by
  rw [capLevel_three]; omega

theorem one_le_cubeLevel_three {e : ℕ} (he : 13 ≤ e) : 1 ≤ cubeLevel 3 e := by
  rw [cubeLevel_three]; omega

theorem cubeLevel_add_capLevel_three {e : ℕ} (he : 13 ≤ e) :
    cubeLevel 3 e + capLevel 3 e = e - cubeLevel 3 e := by
  rw [capLevel_three, cubeLevel_three]
  have h := Nat.div_add_mod (e + 2) 3
  have h' := Nat.mod_lt (e + 2) (by norm_num : 0 < 3)
  omega

theorem cubeLevel_add_capLevel_le_three {e : ℕ} (he : 13 ≤ e) :
    cubeLevel 3 e + capLevel 3 e ≤ e := by
  rw [cubeLevel_add_capLevel_three he]
  exact Nat.sub_le _ _

theorem cubeLevel_add_bval_le_three {e : ℕ} (he : 13 ≤ e)
    (a b : Fin 3 → ℕ) (y : ℕ) : cubeLevel 3 e + bval 3 e a b y ≤ e := by
  have hb : bval 3 e a b y ≤ capLevel 3 e := vcap_le 3 (capLevel 3 e) (defect2 3 e a b y).val
  have h := cubeLevel_add_capLevel_le_three he
  omega

theorem e_le_three_mul_cubeLevel_three (e : ℕ) : e ≤ 3 * cubeLevel 3 e := by
  rw [cubeLevel_three]
  have h := Nat.div_add_mod (e + 2) 3
  have h' := Nat.mod_lt (e + 2) (by norm_num : 0 < 3)
  omega

theorem two_mul_cubeLevel_le_three {e : ℕ} (he : 13 ≤ e) :
    2 * cubeLevel 3 e ≤ e := by
  rw [cubeLevel_three]
  have h := Nat.div_add_mod (e + 2) 3
  have h' := Nat.mod_lt (e + 2) (by norm_num : 0 < 3)
  omega

/-! ## The `p = 3` menu -/

theorem menuW_three {e s j : ℕ} (he13 : ¬ e ≤ 12) :
    menuW 3 e s j
      = (if j = 0 ∧ s ≤ capLevel 3 e then (10:ℝ) ^ 6 * (3:ℝ) ^ ((s:ℝ)/2) else 0)
        + (if s = max (capLevel 3 e) j then
            (10:ℝ) ^ 6 * (3:ℝ) ^ (((cubeLevel 3 e : ℝ) + (j:ℝ))/2) else 0) := by
  rw [menuW, if_neg (by norm_num : ¬ (5 ≤ 3)), if_neg he13]
  simp only [Nat.cast_ofNat]

theorem menuW_three_row0 {e s : ℕ} (he13 : ¬ e ≤ 12) (hs : s ≤ capLevel 3 e) :
    (4:ℝ) * (3:ℝ) ^ ((s:ℝ)/2) ≤ menuW 3 e s 0 := by
  rw [menuW_three he13]
  rw [max_eq_left (Nat.zero_le (capLevel 3 e)), if_pos ⟨rfl, hs⟩]
  have h1 : (4:ℝ) * (3:ℝ) ^ ((s:ℝ)/2) ≤ (10:ℝ)^6 * (3:ℝ) ^ ((s:ℝ)/2) :=
    mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg (by norm_num) _)
  have h2 : (0:ℝ) ≤ (if s = capLevel 3 e then
      (10:ℝ)^6 * (3:ℝ)^(((cubeLevel 3 e : ℝ) + (0:ℝ))/2) else 0) := by
    split_ifs with h
    · exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)
    · norm_num
  linarith

theorem menuW_three_T {e : ℕ} (he13 : ¬ e ≤ 12) :
    (10:ℝ) ^ 6 * (3:ℝ) ^ ((cubeLevel 3 e : ℝ)/2) ≤ menuW 3 e (capLevel 3 e) 0 := by
  rw [menuW_three he13]
  rw [max_eq_left (Nat.zero_le (capLevel 3 e)), if_pos ⟨rfl, le_rfl⟩, if_pos rfl]
  simp only [Nat.cast_zero, add_zero]
  have h3 : (0:ℝ) ≤ (10:ℝ)^6 * (3:ℝ) ^ ((cubeLevel 3 e : ℝ)/2) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)
  have h4 : (0:ℝ) ≤ (10:ℝ)^6 * (3:ℝ) ^ ((capLevel 3 e : ℝ)/2) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)
  linarith

/-- A single summand of `localFactor 3 e a b`. -/
noncomputable def LF3 (e : ℕ) (a b : Fin 3 → ℕ) (s j : ℕ) : ℝ :=
  menuW 3 e s j * (if DLp 3 s a b ∧ 3 ^ j ∣ contAB a b then (1:ℝ) else 0)

theorem localFactor_three_eq (e : ℕ) (a b : Fin 3 → ℕ) :
    localFactor 3 e a b
      = ∑ s ∈ Finset.range (e + 2), ∑ j ∈ Finset.range (e + 1), LF3 e a b s j := rfl

theorem LF3_nonneg {e : ℕ} (he13 : ¬ e ≤ 12) (a b : Fin 3 → ℕ) (s j : ℕ) :
    0 ≤ LF3 e a b s j := by
  rw [LF3]
  refine mul_nonneg ?_ ?_
  · rw [menuW_three he13]
    refine add_nonneg ?_ ?_
    · split_ifs with h
      · exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)
      · norm_num
    · split_ifs with h
      · exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)
      · norm_num
  · split_ifs <;> norm_num

/-- `localFactor` dominates the `4·3^(s/2)` atom at `(s,0)` for `s ≤ capLevel 3 e`. -/
theorem LF3_unc_ge {e s : ℕ} (he13 : ¬ e ≤ 12) (a b : Fin 3 → ℕ) (hs : s ≤ capLevel 3 e) :
    (4:ℝ) * (3:ℝ) ^ ((s:ℝ)/2) * (if DLp 3 s a b then 1 else 0) ≤ LF3 e a b s 0 := by
  rw [LF3]
  have hind : (if DLp 3 s a b ∧ 3 ^ 0 ∣ contAB a b then (1:ℝ) else 0)
      = (if DLp 3 s a b then 1 else 0) := by simp
  rw [hind]
  exact mul_le_mul_of_nonneg_right (menuW_three_row0 he13 hs) (by split_ifs <;> norm_num)

/-- The summand at `(capLevel 3 e, 0)` has value at least `10^6 · 3^(cubeLevel 3 e / 2)`. -/
theorem LF3_T_ge {e : ℕ} (he13 : ¬ e ≤ 12) (a b : Fin 3 → ℕ)
    (hDL : DLp 3 (capLevel 3 e) a b) :
    (10:ℝ) ^ 6 * (3:ℝ) ^ ((cubeLevel 3 e : ℝ)/2) ≤ LF3 e a b (capLevel 3 e) 0 := by
  rw [LF3, if_pos ⟨hDL, by simp⟩, mul_one]
  exact menuW_three_T he13

/-- `localFactor` dominates the content atom `10^6 · 3^((cubeLevel + j)/2)` at
`(max (capLevel 3 e) j, j)`. -/
theorem LF3_content_ge {e j : ℕ} (he13 : ¬ e ≤ 12) (a b : Fin 3 → ℕ) (hj1 : 1 ≤ j)
    (hcont : 3 ^ j ∣ contAB a b) (hDL : DLp 3 (max (capLevel 3 e) j) a b) :
    (10:ℝ) ^ 6 * (3:ℝ) ^ (((cubeLevel 3 e : ℝ) + (j:ℝ))/2)
      ≤ LF3 e a b (max (capLevel 3 e) j) j := by
  rw [LF3, if_pos ⟨hDL, hcont⟩, mul_one, menuW_three he13]
  have h1 : ¬ (j = 0 ∧ max (capLevel 3 e) j ≤ capLevel 3 e) := by omega
  rw [if_neg h1, if_pos rfl, zero_add]

/-- The `j = 0` row of `localFactor` up to `capLevel 3 e`, together with the content atom at
`(max T j, j)`, is dominated by `localFactor`. -/
theorem localFactor_three_ge_row_and_atom {e j : ℕ} (he13 : ¬ e ≤ 12) (a b : Fin 3 → ℕ)
    (hje : j ≤ e) (hj1 : 1 ≤ j) :
    (∑ s ∈ Finset.range (capLevel 3 e + 1), LF3 e a b s 0)
      + LF3 e a b (max (capLevel 3 e) j) j ≤ localFactor 3 e a b := by
  classical
  rw [localFactor_three_eq]
  set s₀ := max (capLevel 3 e) j with hs₀
  have hs₀le : s₀ ≤ e := by
    rw [hs₀]
    exact max_le (capLevel_le_self_three e) hje
  have hs₀mem : s₀ ∈ Finset.range (e + 2) := Finset.mem_range.mpr (by omega)
  have hpt : ∀ s ∈ Finset.range (e + 2),
      (if s ≤ capLevel 3 e then LF3 e a b s 0 else 0) + (if s = s₀ then LF3 e a b s j else 0)
        ≤ ∑ j' ∈ Finset.range (e + 1), LF3 e a b s j' := by
    intro s hs
    by_cases hsT : s ≤ capLevel 3 e
    · by_cases hs0 : s = s₀
      · -- both summands are present and distinct
        rw [if_pos hsT, hs0, if_pos rfl]
        have h0mem : (0:ℕ) ∈ Finset.range (e + 1) := Finset.mem_range.mpr (by omega)
        have hjmem : j ∈ Finset.range (e + 1) := Finset.mem_range.mpr (by omega)
        have hsub : insert (0:ℕ) {j} ⊆ Finset.range (e + 1) := by
          intro x hx
          rw [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with h | h
          · subst h; exact h0mem
          · subst h; exact hjmem
        have h2 : (∑ j' ∈ insert (0:ℕ) {j}, LF3 e a b s₀ j')
            ≤ ∑ j' ∈ Finset.range (e + 1), LF3 e a b s₀ j' :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun j' _ _ => LF3_nonneg he13 a b s₀ j')
        rw [Finset.sum_insert (by simp only [Finset.mem_singleton]; omega),
          Finset.sum_singleton] at h2
        exact h2
      · rw [if_pos hsT, if_neg hs0, add_zero]
        exact Finset.single_le_sum (f := fun j' => LF3 e a b s j')
          (fun j' _ => LF3_nonneg he13 a b s j') (a := 0) (Finset.mem_range.mpr (by omega))
    · rw [if_neg hsT]
      by_cases hs0 : s = s₀
      · rw [if_pos hs0, zero_add]
        exact Finset.single_le_sum (f := fun j' => LF3 e a b s j')
          (fun j' _ => LF3_nonneg he13 a b s j') (a := j) (Finset.mem_range.mpr (by omega))
      · rw [if_neg hs0, add_zero]
        exact Finset.sum_nonneg (fun j' _ => LF3_nonneg he13 a b s j')
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib] at hsum
  have hrow : (∑ s ∈ Finset.range (e + 2), (if s ≤ capLevel 3 e then LF3 e a b s 0 else 0))
      = ∑ s ∈ Finset.range (capLevel 3 e + 1), LF3 e a b s 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hcol : (∑ s ∈ Finset.range (e + 2), (if s = s₀ then LF3 e a b s j else 0))
      = LF3 e a b s₀ j := by
    rw [Finset.sum_ite_eq', if_pos hs₀mem]
  rw [hrow, hcol] at hsum
  rw [hs₀]
  exact hsum

/-- The `j = 0` row of `localFactor` up to `capLevel 3 e` is dominated by `localFactor`. -/
theorem localFactor_three_ge_row {e : ℕ} (he13 : ¬ e ≤ 12) (a b : Fin 3 → ℕ) :
    (∑ s ∈ Finset.range (capLevel 3 e + 1), LF3 e a b s 0) ≤ localFactor 3 e a b := by
  have h := localFactor_three_ge_row_and_atom (e := e) (j := 1) he13 a b (by omega) (le_refl 1)
  linarith [h, LF3_nonneg he13 a b (max (capLevel 3 e) 1) 1]

/-! ## The uncapped part of the support -/

theorem suppSet_three_eq (e : ℕ) (a b : Fin 3 → ℕ) :
    suppSet 3 e a b = uncSet 3 e a b ∪ capSet 3 e a b := by
  ext y
  simp only [uncSet, capSet, Finset.mem_filter, Finset.mem_union]
  constructor
  · intro h
    rcases lt_or_ge (nval 3 e a b y) (capLevel 3 e) with hlt | hle
    · exact Or.inl ⟨h, hlt⟩
    · exact Or.inr ⟨h, hle⟩
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

theorem uncCap_disjoint (e : ℕ) (a b : Fin 3 → ℕ) :
    Disjoint (uncSet 3 e a b) (capSet 3 e a b) := by
  rw [Finset.disjoint_left]
  intro y hy1 hy2
  simp only [uncSet, Finset.mem_filter] at hy1
  simp only [capSet, Finset.mem_filter] at hy2
  omega

theorem gaussTwoRHS_three_eq_sum {e : ℕ} (a b : Fin 3 → ℕ) :
    gaussTwoRHS 3 e (cubeLevel 3 e) a b
      = ∑ y ∈ suppSet 3 e a b, (((3:ℕ):ℝ)) ^ ((bval 3 e a b y : ℝ) / 2) := by
  rw [gaussTwoRHS, suppSet, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  by_cases h : suppPred 3 e a b y
  · have h' : UnitAt 3 y a b ∧ 3 ^ (cubeLevel 3 e + vcap 3 (e - 2 * cubeLevel 3 e)
        (defect2 3 e a b y).val) ∣ (defect1 3 e a b y).val := h
    rw [if_pos h, if_pos h']
    simp only [bval, capLevel]
  · have h' : ¬ (UnitAt 3 y a b ∧ 3 ^ (cubeLevel 3 e + vcap 3 (e - 2 * cubeLevel 3 e)
        (defect2 3 e a b y).val) ∣ (defect1 3 e a b y).val) := h
    rw [if_neg h, if_neg h']

theorem DLp_of_unc_three {e : ℕ} (a b : Fin 3 → ℕ) {y : ℕ}
    (hy : suppPred 3 e a b y) (hbt : SuppTransfer 3 e a b) (hlt : nval 3 e a b y < capLevel 3 e) :
    DLp 3 (nval 3 e a b y) a b := by
  obtain ⟨hbval, hNdvd⟩ := hbt y hy
  obtain ⟨hunit, _⟩ := hy
  have hmin : min (nval 3 e a b y) (capLevel 3 e) = nval 3 e a b y :=
    min_eq_left (le_of_lt hlt)
  have hbv : bval 3 e a b y = nval 3 e a b y := by rw [hbval, hmin]
  have hN : ((3 ^ nval 3 e a b y : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ) := by
    rw [hbv] at hNdvd
    exact dvd_trans
      (Nat.cast_dvd_cast (pow_dvd_pow 3 (Nat.le_add_left (nval 3 e a b y) (cubeLevel 3 e))))
      hNdvd
  have hN'ne : (critN a b).derivative.eval (y : ℤ) ≠ 0 := by
    intro h
    rw [nval, if_pos h] at hlt
    omega
  have hnval : nval 3 e a b y
      = padicValNat 3 ((critN a b).derivative.eval (y : ℤ)).natAbs := by
    rw [nval, if_neg hN'ne]
  have hN' : ((3 ^ nval 3 e a b y : ℕ) : ℤ) ∣ (critN a b).derivative.eval (y : ℤ) := by
    have hk : (3 ^ padicValNat 3 ((critN a b).derivative.eval (y : ℤ)).natAbs : ℕ)
        ∣ ((critN a b).derivative.eval (y : ℤ)).natAbs := pow_padicValNat_dvd
    have hkz : ((3 ^ padicValNat 3 ((critN a b).derivative.eval (y : ℤ)).natAbs : ℕ) : ℤ)
        ∣ (critN a b).derivative.eval (y : ℤ) :=
      dvd_trans (Nat.cast_dvd_cast hk) (Int.natAbs_dvd.mpr (dvd_refl _))
    rwa [hnval]
  exact ⟨y, hunit, hN, hN'⟩

theorem DLp_of_cap_three {e : ℕ} (a b : Fin 3 → ℕ) {y : ℕ}
    (hy : suppPred 3 e a b y) (hbt : SuppTransfer 3 e a b)
    (hcap : capLevel 3 e ≤ nval 3 e a b y) : DLp 3 (capLevel 3 e) a b := by
  obtain ⟨hunit, hsupp⟩ := hy
  obtain ⟨hbval, hNdvd⟩ := hbt y ⟨hunit, hsupp⟩
  refine ⟨y, hunit, ?_, ?_⟩
  · have hb : bval 3 e a b y = capLevel 3 e := by
      rw [hbval, min_eq_right hcap]
    have hmT : capLevel 3 e ≤ cubeLevel 3 e + capLevel 3 e := Nat.le_add_left _ _
    refine dvd_trans ?_ hNdvd
    rw [hb]
    exact Int.natCast_dvd_natCast.mpr (pow_dvd_pow 3 hmT)
  · by_cases hz : (critN a b).derivative.eval (y : ℤ) = 0
    · rw [hz]; exact dvd_zero _
    · have hnval : nval 3 e a b y
          = padicValNat 3 ((critN a b).derivative.eval (y : ℤ)).natAbs := by
        rw [nval, if_neg hz]
      have hle : capLevel 3 e ≤
          padicValNat 3 ((critN a b).derivative.eval (y : ℤ)).natAbs := by
        rw [← hnval]; exact hcap
      have hdvd : 3 ^ capLevel 3 e ∣ ((critN a b).derivative.eval (y : ℤ)).natAbs :=
        (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hz)).mpr hle
      exact Int.natCast_dvd.mpr hdvd

theorem dvd_eval_of_dvd_coeff_three {c : ℤ} {P : Polynomial ℤ}
    (h : ∀ n, c ∣ P.coeff n) (x : ℤ) : c ∣ P.eval x := by
  obtain ⟨Q, hQ⟩ := (Polynomial.C_dvd_iff_dvd_coeff c P).mpr h
  rw [hQ, Polynomial.eval_mul, Polynomial.eval_C]
  exact dvd_mul_right c _

theorem dvd_coeff_derivative_three {c : ℤ} {P : Polynomial ℤ} (h : ∀ n, c ∣ P.coeff n) :
    ∀ n, c ∣ (Polynomial.derivative P).coeff n := by
  intro n
  rw [Polynomial.coeff_derivative]
  exact dvd_mul_of_dvd_left (h (n + 1)) _

theorem DLp_of_content_three {j : ℕ} (a b : Fin 3 → ℕ) {y : ℕ} (hy : UnitAt 3 y a b)
    (hdvd : 3 ^ j ∣ contAB a b) : DLp 3 j a b := by
  have hcoeff : ∀ n, (((3 ^ j : ℕ)) : ℤ) ∣ (critN a b).coeff n :=
    lfSmall.dvd_coeff_critN_of_dvd_contAB (3 ^ j) a b hdvd
  exact ⟨y, hy, dvd_eval_of_dvd_coeff_three hcoeff (y : ℤ),
    dvd_eval_of_dvd_coeff_three (dvd_coeff_derivative_three hcoeff) (y : ℤ)⟩

theorem unc_sum_le_three {e : ℕ} (he : 13 ≤ e) (a b : Fin 3 → ℕ)
    (hdeg2 : 2 ≤ (critN a b).natDegree) (hbt : SuppTransfer 3 e a b) :
    ∑ y ∈ uncSet 3 e a b, (((3:ℕ):ℝ)) ^ ((bval 3 e a b y : ℝ) / 2)
      ≤ ∑ s ∈ Finset.range (capLevel 3 e),
          4 * (3:ℝ) ^ ((s : ℝ) / 2) * (if DLp 3 s a b then 1 else 0) := by
  classical
  have hN : critN a b ≠ 0 := fun h => by rw [h] at hdeg2; simp at hdeg2
  have hdeg : (critN a b).natDegree ≤ 4 := natDegree_critN_le_four a b
  have hbv : ∀ y ∈ uncSet 3 e a b, bval 3 e a b y = nval 3 e a b y := by
    intro y hy
    obtain ⟨hys, hlt⟩ := Finset.mem_filter.mp hy
    have hsp : suppPred 3 e a b y := (Finset.mem_filter.mp hys).2
    rw [(hbt y hsp).1, min_eq_left (le_of_lt hlt)]
  rw [Finset.sum_congr rfl (fun y hy => by rw [hbv y hy])]
  have hmap : ∀ y ∈ uncSet 3 e a b, nval 3 e a b y ∈ Finset.range (capLevel 3 e) :=
    fun y hy => Finset.mem_range.mpr (Finset.mem_filter.mp hy).2
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (f := fun y => (((3:ℕ):ℝ)) ^ ((nval 3 e a b y : ℝ) / 2))]
  refine Finset.sum_le_sum (fun s hs => ?_)
  have hsT : s < capLevel 3 e := Finset.mem_range.mp hs
  rw [Finset.sum_congr rfl (fun y hy => by rw [(Finset.mem_filter.mp hy).2])]
  rw [Finset.sum_const, nsmul_eq_mul]
  by_cases hDL : DLp 3 s a b
  · rw [if_pos hDL]
    have hle : ((uncSet 3 e a b).filter (fun y => nval 3 e a b y = s)).card ≤ 4 := by
      refine le_trans (Finset.card_le_card ?_)
        (stub_lvlSet_card_three (e := e) (by omega) a b hN hdeg hbt hsT)
      intro y hy
      obtain ⟨hyu, hys⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hyu).1, hys⟩
    have hstep : ((uncSet 3 e a b).filter (fun y => nval 3 e a b y = s)).card
          * (((3:ℕ):ℝ)) ^ ((s:ℝ)/2) ≤ 4 * (((3:ℕ):ℝ)) ^ ((s:ℝ)/2) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (Real.rpow_nonneg (by norm_num) _)
    rw [Nat.cast_ofNat] at hstep
    simpa using hstep
  · rw [if_neg hDL]
    have hempty : (uncSet 3 e a b).filter (fun y => nval 3 e a b y = s) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro y hyu hy2
      exact hDL (by
        rw [← hy2]
        exact DLp_of_unc_three a b
          (Finset.mem_filter.mp (Finset.mem_filter.mp hyu).1).2 hbt (by rw [hy2]; exact hsT))
    rw [hempty, Finset.card_empty, Nat.cast_zero]
    simp

theorem cap_sum_eq_three {e : ℕ} (a b : Fin 3 → ℕ) (hbt : SuppTransfer 3 e a b) :
    ∑ y ∈ capSet 3 e a b, (((3:ℕ):ℝ)) ^ ((bval 3 e a b y : ℝ) / 2)
      = ((capSet 3 e a b).card : ℝ) * (((3:ℕ):ℝ)) ^ ((capLevel 3 e : ℝ) / 2) := by
  classical
  have hb : ∀ y ∈ capSet 3 e a b, bval 3 e a b y = capLevel 3 e := by
    intro y hy
    obtain ⟨hys, hle⟩ := Finset.mem_filter.mp hy
    have hsp : suppPred 3 e a b y := (Finset.mem_filter.mp hys).2
    rw [(hbt y hsp).1, min_eq_right hle]
  rw [Finset.sum_congr rfl (fun y hy => by rw [hb y hy])]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- The capped part of the support is dominated by the `(capLevel 3 e, 0)` summand of
`localFactor` and the content atom at `(max T (min J e), min J e)`. -/
theorem capSum_bound {e J j : ℕ} (he : 26 ≤ e) (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j' : Fin 6, j' ≠ i → shift a b i ≠ shift a b j')
    (hdeg2 : 2 ≤ (critN a b).natDegree) (hbt : SuppTransfer 3 e a b)
    (hJdef : padicValNat 3 (contAB a b) = J) (hjdef : j = min J e)
    (hcapT : DLp 3 (capLevel 3 e) a b) :
    ∑ y ∈ capSet 3 e a b, (((3:ℕ):ℝ)) ^ ((bval 3 e a b y : ℝ) / 2)
      ≤ LF3 e a b (capLevel 3 e) 0
        + (if 1 ≤ j then
            (10:ℝ) ^ 6 * (3:ℝ) ^ (((cubeLevel 3 e : ℝ) + (j:ℝ))/2) else 0) := by
  classical
  have he13 : ¬ e ≤ 12 := by omega
  have hjJ : j ≤ J := by rw [hjdef]; exact min_le_left _ _
  have hje : j ≤ e := by rw [hjdef]; exact min_le_right _ _
  have hjdvd : 3 ^ j ∣ contAB a b :=
    dvd_trans (Nat.pow_dvd_pow 3 hjJ) (by rw [← hJdef]; exact pow_padicValNat_dvd)
  have hcontent : ∀ n, ((3 ^ j : ℕ) : ℤ) ∣ (critN a b).coeff n :=
    lfSmall.dvd_coeff_critN_of_dvd_contAB (3 ^ j) a b hjdvd
  have hcard := Work.LinnikAreas.u8three.capSet_three_bound (by omega : 13 ≤ e) a b i hi hbt
    hJdef hjdef
  set K := (cubeLevel 3 e + capLevel 3 e - j + 1) / 2 with hKdef
  have hTle : capLevel 3 e ≤ cubeLevel 3 e := capLevel_le_cubeLevel_three e
  have hKle : K ≤ cubeLevel 3 e := by
    rw [hKdef]
    omega
  have hexp : (((cubeLevel 3 e - K : ℕ)) : ℝ) + (capLevel 3 e : ℝ)/2
      ≤ ((cubeLevel 3 e : ℝ) + (j:ℝ))/2 := by
    have hnat : 2 * (cubeLevel 3 e - K) + capLevel 3 e ≤ cubeLevel 3 e + j := by
      rw [hKdef]
      omega
    have hreal : (2:ℝ) * (((cubeLevel 3 e - K : ℕ)) : ℝ) + (capLevel 3 e : ℝ)
        ≤ (cubeLevel 3 e : ℝ) + (j:ℝ) := by exact_mod_cast hnat
    linarith
  have hcardR : (((capSet 3 e a b).card : ℕ) : ℝ)
      ≤ 3000 * (3:ℝ) ^ (((cubeLevel 3 e - K : ℕ)) : ℝ) := by
    calc (((capSet 3 e a b).card : ℕ) : ℝ)
        ≤ ((3000 * 3 ^ (cubeLevel 3 e - K) : ℕ) : ℝ) := by exact_mod_cast hcard
      _ = 3000 * (3:ℝ) ^ (((cubeLevel 3 e - K : ℕ)) : ℝ) := by
            push_cast
            rw [← Real.rpow_natCast]
  rw [cap_sum_eq_three (e := e) a b hbt, Nat.cast_ofNat]
  by_cases hKm : cubeLevel 3 e ≤ K
  · -- the cap is capped at `4`
    have hz : cubeLevel 3 e - K = 0 := Nat.sub_eq_zero_of_le hKm
    have h4 : ((capSet 3 e a b).card : ℝ) ≤ 3000 := by
      have := hcardR
      rw [hz, Nat.cast_zero, Real.rpow_zero, mul_one] at this
      exact this
    have hbound : ((capSet 3 e a b).card : ℝ) * (3:ℝ) ^ ((capLevel 3 e : ℝ)/2)
        ≤ (10:ℝ) ^ 6 * (3:ℝ) ^ ((cubeLevel 3 e : ℝ)/2) := by
      have h1 : ((capSet 3 e a b).card : ℝ) ≤ (10:ℝ)^6 := by linarith
      calc ((capSet 3 e a b).card : ℝ) * (3:ℝ) ^ ((capLevel 3 e : ℝ)/2)
          ≤ (10:ℝ)^6 * (3:ℝ) ^ ((capLevel 3 e : ℝ)/2) :=
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (by norm_num) _)
        _ ≤ (10:ℝ)^6 * (3:ℝ) ^ ((cubeLevel 3 e : ℝ)/2) := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
              have : (capLevel 3 e : ℝ) ≤ (cubeLevel 3 e : ℝ) := by exact_mod_cast hTle
              linarith)
    exact le_trans hbound (le_trans (LF3_T_ge he13 a b hcapT) (le_add_of_nonneg_right (by
      split_ifs with h
      · exact mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _)
      · norm_num)))
  · -- the cap is not capped
    have hKlt : K < cubeLevel 3 e := lt_of_not_ge hKm
    have hbound : ((capSet 3 e a b).card : ℝ) * (3:ℝ) ^ ((capLevel 3 e : ℝ)/2)
        ≤ 3000 * (3:ℝ) ^ (((cubeLevel 3 e : ℝ) + (j:ℝ))/2) := by
      have h1 : (3:ℝ) ^ (((cubeLevel 3 e - K : ℕ) : ℝ)) * (3:ℝ) ^ ((capLevel 3 e : ℝ)/2)
          = (3:ℝ) ^ ((((cubeLevel 3 e - K : ℕ)) : ℝ) + (capLevel 3 e : ℝ)/2) :=
        (Real.rpow_add (by norm_num) _ _).symm
      have h2 : (3:ℝ) ^ ((((cubeLevel 3 e - K : ℕ)) : ℝ) + (capLevel 3 e : ℝ)/2)
          ≤ (3:ℝ) ^ (((cubeLevel 3 e : ℝ) + (j:ℝ))/2) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      calc ((capSet 3 e a b).card : ℝ) * (3:ℝ) ^ ((capLevel 3 e : ℝ)/2)
          ≤ (3000 * (3:ℝ) ^ (((cubeLevel 3 e - K : ℕ)) : ℝ))
              * (3:ℝ) ^ ((capLevel 3 e : ℝ)/2) :=
            mul_le_mul_of_nonneg_right hcardR (Real.rpow_nonneg (by norm_num) _)
        _ = 3000 * ((3:ℝ) ^ (((cubeLevel 3 e - K : ℕ)) : ℝ)
              * (3:ℝ) ^ ((capLevel 3 e : ℝ)/2)) := by ring
        _ = 3000 * (3:ℝ) ^ ((((cubeLevel 3 e - K : ℕ)) : ℝ) + (capLevel 3 e : ℝ)/2) := by rw [h1]
        _ ≤ 3000 * (3:ℝ) ^ (((cubeLevel 3 e : ℝ) + (j:ℝ))/2) :=
            mul_le_mul_of_nonneg_left h2 (by norm_num)
    by_cases hj1 : 1 ≤ j
    · rw [if_pos hj1]
      have hCA : (3000:ℝ) * (3:ℝ) ^ (((cubeLevel 3 e : ℝ) + (j:ℝ))/2)
          ≤ (10:ℝ)^6 * (3:ℝ) ^ (((cubeLevel 3 e : ℝ) + (j:ℝ))/2) :=
        mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg (by norm_num) _)
      exact le_trans (le_trans hbound hCA)
        (le_add_of_nonneg_left (LF3_nonneg he13 a b (capLevel 3 e) 0))
    · rw [if_neg hj1]
      have hj0 : j = 0 := by omega
      have hrew : (3:ℝ) ^ (((cubeLevel 3 e : ℝ) + (j:ℝ))/2)
          = (3:ℝ) ^ ((cubeLevel 3 e : ℝ)/2) := by
        rw [hj0]; norm_num
      have hb2 : ((capSet 3 e a b).card : ℝ) * (3:ℝ) ^ ((capLevel 3 e : ℝ)/2)
          ≤ (3000:ℝ) * (3:ℝ) ^ ((cubeLevel 3 e : ℝ)/2) := by
        rw [hrew] at hbound
        exact hbound
      have hb3 : (3000:ℝ) * (3:ℝ) ^ ((cubeLevel 3 e : ℝ)/2)
          ≤ (10:ℝ)^6 * (3:ℝ) ^ ((cubeLevel 3 e : ℝ)/2) :=
        mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg (by norm_num) _)
      have hfin : (10:ℝ)^6 * (3:ℝ) ^ ((cubeLevel 3 e : ℝ)/2)
          ≤ LF3 e a b (capLevel 3 e) 0 := LF3_T_ge he13 a b hcapT
      exact le_trans hb2 (le_trans hb3 (by simpa using hfin))

/-- `gaussTwoRHS 3 e (cubeLevel 3 e) a b ≤ localFactor 3 e a b` for `26 ≤ e`. -/
theorem gaussTwoRHS_le_localFactor_three {e : ℕ} (he : 26 ≤ e) (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j' : Fin 6, j' ≠ i → shift a b i ≠ shift a b j')
    (hdeg2 : 2 ≤ (critN a b).natDegree) (hbt : SuppTransfer 3 e a b) :
    gaussTwoRHS 3 e (cubeLevel 3 e) a b ≤ localFactor 3 e a b := by
  classical
  have he13 : ¬ e ≤ 12 := by omega
  rw [gaussTwoRHS_three_eq_sum]
  rw [suppSet_three_eq, Finset.sum_union (uncCap_disjoint e a b)]
  have hunc := unc_sum_le_three (e := e) (by omega) a b hdeg2 hbt
  have huncLF : (∑ y ∈ uncSet 3 e a b, (((3:ℕ):ℝ)) ^ ((bval 3 e a b y : ℝ) / 2))
      ≤ ∑ s ∈ Finset.range (capLevel 3 e), LF3 e a b s 0 := by
    refine le_trans hunc ?_
    refine Finset.sum_le_sum (fun s hs => ?_)
    have hsT : s ≤ capLevel 3 e := le_of_lt (Finset.mem_range.mp hs)
    exact LF3_unc_ge he13 a b hsT
  by_cases hne : (capSet 3 e a b).Nonempty
  · obtain ⟨y₀, hy₀⟩ := hne
    have hsp0 : suppPred 3 e a b y₀ := (Finset.mem_filter.mp (Finset.mem_filter.mp hy₀).1).2
    have hcap0 : capLevel 3 e ≤ nval 3 e a b y₀ := (Finset.mem_filter.mp hy₀).2
    have hcapT : DLp 3 (capLevel 3 e) a b := DLp_of_cap_three a b hsp0 hbt hcap0
    have hunit : UnitAt 3 y₀ a b := hsp0.1
    set J := padicValNat 3 (contAB a b) with hJdef
    set j := min J e with hjdef
    have hje : j ≤ e := by rw [hjdef]; exact min_le_right _ _
    have hjdvd : 3 ^ j ∣ contAB a b := by
      rw [hjdef]
      exact dvd_trans (Nat.pow_dvd_pow 3 (min_le_left J e)) (by
        rw [hJdef]; exact pow_padicValNat_dvd)
    have hDLj : DLp 3 (max (capLevel 3 e) j) a b := by
      by_cases h : j ≤ capLevel 3 e
      · rw [max_eq_left h]; exact hcapT
      · rw [max_eq_right (le_of_lt (not_le.mp h))]
        exact DLp_of_content_three a b hunit hjdvd
    have hcap := capSum_bound (e := e) (J := J) (j := j) (by omega) a b i hi hdeg2 hbt
      hJdef.symm hjdef hcapT
    by_cases hj1 : 1 ≤ j
    · have hcont := LF3_content_ge he13 a b hj1 hjdvd hDLj
      have hrow := localFactor_three_ge_row_and_atom (e := e) (j := j) he13 a b hje hj1
      have hcap' : (∑ y ∈ capSet 3 e a b, (((3:ℕ):ℝ)) ^ ((bval 3 e a b y : ℝ) / 2))
          ≤ LF3 e a b (capLevel 3 e) 0 + LF3 e a b (max (capLevel 3 e) j) j := by
        refine le_trans hcap ?_
        rw [if_pos hj1]
        linarith [hcont]
      calc (∑ y ∈ uncSet 3 e a b, (((3:ℕ):ℝ)) ^ ((bval 3 e a b y : ℝ) / 2))
              + ∑ y ∈ capSet 3 e a b, (((3:ℕ):ℝ)) ^ ((bval 3 e a b y : ℝ) / 2)
          ≤ (∑ s ∈ Finset.range (capLevel 3 e), LF3 e a b s 0)
              + (LF3 e a b (capLevel 3 e) 0 + LF3 e a b (max (capLevel 3 e) j) j) :=
            add_le_add huncLF hcap'
        _ = (∑ s ∈ Finset.range (capLevel 3 e + 1), LF3 e a b s 0)
              + LF3 e a b (max (capLevel 3 e) j) j := by rw [Finset.sum_range_succ]; ring
        _ ≤ localFactor 3 e a b := hrow
    · have hcap' : (∑ y ∈ capSet 3 e a b, (((3:ℕ):ℝ)) ^ ((bval 3 e a b y : ℝ) / 2))
          ≤ LF3 e a b (capLevel 3 e) 0 := by
        refine le_trans hcap ?_
        rw [if_neg hj1]
        simp
      calc (∑ y ∈ uncSet 3 e a b, (((3:ℕ):ℝ)) ^ ((bval 3 e a b y : ℝ) / 2))
              + ∑ y ∈ capSet 3 e a b, (((3:ℕ):ℝ)) ^ ((bval 3 e a b y : ℝ) / 2)
          ≤ (∑ s ∈ Finset.range (capLevel 3 e), LF3 e a b s 0)
              + LF3 e a b (capLevel 3 e) 0 := add_le_add huncLF hcap'
        _ = ∑ s ∈ Finset.range (capLevel 3 e + 1), LF3 e a b s 0 := by rw [Finset.sum_range_succ]
        _ ≤ localFactor 3 e a b := localFactor_three_ge_row he13 a b
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty, add_zero]
    refine le_trans huncLF (le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
      (localFactor_three_ge_row he13 a b))
    · intro s hs
      have h := Finset.mem_range.mp hs
      have h2 := capLevel_le_self_three e
      exact Finset.mem_range.mpr (by omega)
    · intro s _ _
      exact LF3_nonneg he13 a b s 0

end Work.LinnikAreas.u8three.core

namespace Work.LinnikAreas.u8three

/-- **U8 (Theorem L'), the `p = 3` hard range `e ≥ 26`.**  For `χ` primitive mod `3^e` and a
singleton pair `(a,b)`, the complete cubic correlation is bounded by `3^(e/2) · localFactor 3 e a b`. -/
theorem localFactor_bound_three_ge26 {e : ℕ} (he : 26 ≤ e)
    (χ : DirichletCharacter ℂ (3 ^ e)) (hχ : χ.IsPrimitive) (a b : Fin 3 → ℕ) (i : Fin 6)
    (hi : ∀ j : Fin 6, j ≠ i → shift a b i ≠ shift a b j) :
    ‖∑ x : ZMod (3 ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (3 ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (3 ^ e)))))‖
      ≤ (3 : ℝ) ^ ((e : ℝ) / 2) * localFactor 3 e a b := by
  classical
  have he13 : 13 ≤ e := by omega
  have hNZ := critN_ne_zero_of_unique a b i hi
  have hdeg2 : 2 ≤ (critN a b).natDegree := hNZ.1
  have hbt : SuppTransfer 3 e a b := u8three.core.stub_transfer_three (by omega) a b
  have hAA := corr6_primePow_gaussTwo_bound (p := 3) (e := e) (m := cubeLevel 3 e)
      (by norm_num) (u8three.core.one_le_cubeLevel_three he13)
      (u8three.core.e_le_three_mul_cubeLevel_three e) (u8three.core.two_mul_cubeLevel_le_three he13)
      χ hχ a b
  have hmain := u8three.core.gaussTwoRHS_le_localFactor_three (e := e) (by omega) a b i hi hdeg2 hbt
  refine le_trans hAA (le_trans (mul_le_mul_of_nonneg_left hmain
    (Real.rpow_nonneg (by norm_num) _)) (le_of_eq ?_))
  rw [Nat.cast_ofNat]

end Work.LinnikAreas.u8three
