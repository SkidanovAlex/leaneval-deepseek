import Mathlib
import Submission.Work.Mostow.BCGDefs
import Submission.Work.Mostow.LinAlgMatrixIneqAux
import Submission.Work.Mostow.matPhi_all_eq_imp
import Submission.Work.Mostow.matF_lt_of_small_coord
import Submission.Work.Mostow.matF_bound_three
import Submission.Work.Mostow.isCompact_Kset
import Submission.Work.Mostow.continuousOn_matF_Kset
import Submission.Work.Mostow.phi_eq_of_isMaxOn_Kset

namespace Work.Mostow

noncomputable section

open scoped BigOperators

/-- `matF` at the uniform point is the claimed constant. -/
lemma matF_uniform_eq (n : ℕ) (hn : 2 ≤ n) :
    matF (fun _ : Fin n => 1 / (n : ℝ)) = matC n := by
  unfold matF matC
  have hnpos : (0 : ℝ) < n := by positivity
  rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← div_pow]
  congr 1
  have hL : Real.sqrt (1 / (n : ℝ)) = 1 / Real.sqrt (n : ℝ) := by
    rw [one_div, Real.sqrt_inv, one_div]
  have hD : (1 : ℝ) - 1 / (n : ℝ) = ((n : ℝ) - 1) / (n : ℝ) := by field_simp
  rw [hL, hD]
  have hsq : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hnpos)
  rw [div_div]
  field_simp
  rw [hsq]

/-- The uniform point lies in the box `Kset n δ` when `δ ≤ 1/n`. -/
lemma one_div_mem_Kset {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδle : δ ≤ 1 / (n : ℝ)) :
    (fun _ : Fin n => 1 / (n : ℝ)) ∈ Kset n δ := by
  constructor
  · intro i; exact hδle
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    field_simp

/-- The predicate: the full inequality together with the equality case in dimension `n`. -/
def matP (n : ℕ) : Prop :=
  ∀ lam : Fin n → ℝ, (∀ i, 0 ≤ lam i) → (∀ i, lam i < 1) → (∑ i, lam i) = 1 →
    matF lam ≤ matC n ∧ (matF lam = matC n ↔ ∀ i, lam i = 1 / (n : ℝ))

/-- The maximum argument: once the boundary is known to be strictly below `matC n`, the
inequality and equality case follow. -/
lemma matP_of_bound (n : ℕ) (hn : 3 ≤ n) {δ : ℝ} (hδ0 : 0 < δ)
    (hδle : δ ≤ 1 / (n : ℝ))
    (hboundary : ∀ lam : Fin n → ℝ, (∀ i, 0 ≤ lam i) → (∀ i, lam i < 1) →
      (∑ i, lam i) = 1 → (∃ i, lam i ≤ δ) → matF lam < matC n) :
    matP n := by
  have hn2 : 2 ≤ n := by omega
  have hnpos : 0 < n := by omega
  haveI : NeZero n := ⟨by omega⟩
  -- the maximum over the compact box
  have hne : (Kset n δ).Nonempty :=
    ⟨fun _ : Fin n => 1 / (n : ℝ), one_div_mem_Kset hnpos hδle⟩
  obtain ⟨xstar, hxstar_mem, hxstar_max⟩ :=
    (isCompact_Kset n hδ0).exists_isMaxOn hne (continuousOn_matF_Kset n hδ0)
  have hxstar_ge : matC n ≤ matF xstar := by
    have h1n : (fun _ : Fin n => 1 / (n : ℝ)) ∈ Kset n δ := one_div_mem_Kset hnpos hδle
    calc matC n = matF (fun _ : Fin n => 1 / (n : ℝ)) := (matF_uniform_eq n hn2).symm
      _ ≤ matF xstar := hxstar_max h1n
  -- `xstar i < 1`
  have hxstar_lt1 : ∀ i, xstar i < 1 := by
    intro i
    have hex : ∃ j : Fin n, j ≠ i := by
      by_cases hi : i = 0
      · refine ⟨⟨1, by omega⟩, ?_⟩
        simp [hi]
      · refine ⟨0, ?_⟩
        intro h
        exact hi h.symm
    obtain ⟨j, hj⟩ := hex
    have hjmem : j ∈ (Finset.univ : Finset (Fin n)).erase i :=
      Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
    have hle : xstar j ≤ ∑ k ∈ (Finset.univ : Finset (Fin n)).erase i, xstar k :=
      Finset.single_le_sum (fun k _ => le_trans hδ0.le (hxstar_mem.1 k)) hjmem
    have hsum_erase : ∑ k ∈ (Finset.univ : Finset (Fin n)).erase i, xstar k
        = 1 - xstar i := by
      have h := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n))) (f := xstar)
        (Finset.mem_univ i)
      rw [hxstar_mem.2] at h
      linarith
    have hposj : 0 < xstar j := lt_of_lt_of_le hδ0 (hxstar_mem.1 j)
    linarith
  -- every coordinate is strictly above `δ`
  have hint : ∀ i, δ < xstar i := by
    intro i
    by_contra hlt
    push_neg at hlt
    have hsmall : ∃ i, xstar i ≤ δ := ⟨i, hlt⟩
    have hlt' : matF xstar < matC n :=
      hboundary xstar (fun k => le_trans hδ0.le (hxstar_mem.1 k)) hxstar_lt1 hxstar_mem.2 hsmall
    linarith
  -- all `matPhi` values are equal, hence the coordinates are equal
  have hphi : ∀ i j, matPhi (xstar i) = matPhi (xstar j) :=
    phi_eq_of_isMaxOn_Kset hn2 hδ0 hxstar_mem hxstar_max hint
  have hxstar_eq : ∀ i, xstar i = 1 / (n : ℝ) :=
    matPhi_all_eq_imp hn xstar (fun i => lt_of_lt_of_le hδ0 (le_of_lt (hint i)))
      hxstar_lt1 hxstar_mem.2 hphi
  have hxstar_val : matF xstar = matC n := by
    rw [show xstar = (fun _ : Fin n => 1 / (n : ℝ)) from funext hxstar_eq]
    exact matF_uniform_eq n hn2
  intro lam h0 h1 hsum
  constructor
  · by_cases hsmall : ∃ i, lam i ≤ δ
    · exact le_of_lt (hboundary lam h0 h1 hsum hsmall)
    · push_neg at hsmall
      have hmem : lam ∈ Kset n δ := ⟨fun i => le_of_lt (hsmall i), hsum⟩
      calc matF lam ≤ matF xstar := hxstar_max hmem
        _ = matC n := hxstar_val
  · constructor
    · intro heq
      have hnot : ¬ ∃ i, lam i ≤ δ := by
        rintro ⟨i, hi⟩
        have := hboundary lam h0 h1 hsum ⟨i, hi⟩
        linarith
      push_neg at hnot
      have hmem : lam ∈ Kset n δ := ⟨fun i => le_of_lt (hnot i), hsum⟩
      have hmaxlam : IsMaxOn (fun y : Fin n → ℝ => matF y) (Kset n δ) lam := by
        intro y hy
        calc matF y ≤ matF xstar := hxstar_max hy
          _ = matC n := hxstar_val
          _ = matF lam := heq.symm
      have hintlam : ∀ i, δ < lam i := by
        intro i
        by_contra hle
        push_neg at hle
        have := hboundary lam h0 h1 hsum ⟨i, hle⟩
        linarith
      have hphilam : ∀ i j, matPhi (lam i) = matPhi (lam j) :=
        phi_eq_of_isMaxOn_Kset hn2 hδ0 hmem hmaxlam hintlam
      exact matPhi_all_eq_imp hn lam (fun i => lt_of_lt_of_le hδ0 (le_of_lt (hintlam i)))
        h1 hsum hphilam
    · intro hall
      rw [show lam = (fun _ : Fin n => 1 / (n : ℝ)) from funext hall]
      exact matF_uniform_eq n hn2

/-- Base case `n = 3`. -/
lemma matP_three : matP 3 := by
  refine matP_of_bound 3 (by norm_num) (δ := 1 / 8) (by norm_num) (by norm_num) ?_
  intro lam h0 h1 hsum hsmall
  have hb := matF_bound_three (δ := 1/8) lam h0 h1 hsum (by norm_num : (0:ℝ) < 1/8) (by norm_num) hsmall
  have hbase : (4:ℝ)/7 < (Real.sqrt 3 / 2) ^ 3 := by
    have hs : Real.sqrt 3 ^ 2 = (3:ℝ) := Real.sq_sqrt (by norm_num)
    have hcube : (Real.sqrt 3 / 2) ^ 3 = 3 * Real.sqrt 3 / 8 := by
      rw [div_pow, show (Real.sqrt 3)^3 = (Real.sqrt 3)^2 * Real.sqrt 3 by ring, hs]
      ring
    rw [hcube]
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg 3]
  have hc : (4:ℝ)/7 < matC 3 := by
    unfold matC
    norm_num
    exact hbase
  have hb' : matF lam ≤ 4/7 := by
    calc matF lam ≤ 1 / (2 * (1 - 1/8:ℝ)) := hb
      _ = 4/7 := by norm_num
  linarith

/-- Induction step. -/
lemma matP_succ (n : ℕ) (hn : 3 ≤ n) (ih : matP n) : matP (n + 1) := by
  have hn2 : 2 ≤ n := by omega
  have hCn : 0 < matC n := matC_pos hn2
  have hCn1 : 0 < matC (n + 1) := matC_pos (by omega)
  set δ : ℝ := min (1 / (2 * (n + 1 : ℝ))) ((matC (n + 1) / (2 * matC n)) ^ 2) with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]
    apply lt_min
    · positivity
    · positivity
  have hδle : δ ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
    rw [hδdef]
    calc min (1 / (2 * (n + 1 : ℝ))) ((matC (n + 1) / (2 * matC n)) ^ 2)
        ≤ 1 / (2 * (n + 1 : ℝ)) := min_le_left _ _
      _ ≤ 1 / ((n + 1 : ℕ) : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one]
        have hpos : (0:ℝ) < (n:ℝ) + 1 := by positivity
        field_simp
        linarith
  refine matP_of_bound (n + 1) (by omega) hδ0 hδle ?_
  intro lam h0 h1 hsum hsmall
  have hδC : Real.sqrt δ * matC n < matC (n + 1) := by
    have hδsq : δ ≤ (matC (n + 1) / (2 * matC n)) ^ 2 := by
      rw [hδdef]; exact min_le_right _ _
    have hsqrt : Real.sqrt δ ≤ matC (n + 1) / (2 * matC n) :=
      (Real.sqrt_le_left (by positivity)).2 hδsq
    have h2 : matC (n + 1) / (2 * matC n) * matC n = matC (n + 1) / 2 := by
      field_simp
    calc Real.sqrt δ * matC n ≤ (matC (n + 1) / (2 * matC n)) * matC n := by
          exact mul_le_mul_of_nonneg_right hsqrt hCn.le
      _ = matC (n + 1) / 2 := h2
      _ < matC (n + 1) := by linarith
  exact matF_lt_of_small_coord (by omega : 4 ≤ n + 1) hδ0 hCn
    (fun y hy0 hy1 hysum => (ih y hy0 hy1 hysum).1) hδC lam h0 h1 hsum hsmall

/-- The statement in every dimension. -/
lemma matP_all : ∀ n, 3 ≤ n → matP n := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases (by omega : n = 3 ∨ 4 ≤ n) with rfl | hn4
    · exact matP_three
    · have ihm : matP (n - 1) := ih (n - 1) (by omega) (by omega)
      have hstep := matP_succ (n - 1) (by omega) ihm
      have : n - 1 + 1 = n := by omega
      rwa [this] at hstep

theorem LinAlgMatrixIneq (n : ℕ) (hn : 3 ≤ n) (lam : Fin n → ℝ)
    (h0 : ∀ i, 0 ≤ lam i) (h1 : ∀ i, lam i < 1) (hsum : ∑ i, lam i = 1) :
    (∏ i, Real.sqrt (lam i)) / (∏ i, (1 - lam i)) ≤ (Real.sqrt n / ((n : ℝ) - 1)) ^ n ∧
    ((∏ i, Real.sqrt (lam i)) / (∏ i, (1 - lam i)) = (Real.sqrt n / ((n : ℝ) - 1)) ^ n ↔
      ∀ i, lam i = 1 / n) := by
  simpa only [matP, matF, matC] using matP_all n hn lam h0 h1 hsum

end

end Work.Mostow
