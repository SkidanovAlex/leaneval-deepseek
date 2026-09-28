import Mathlib
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.SlabGeneral
import Submission.Work.HP.SlabMono

namespace Work.HP

open MeasureTheory MvPolynomial
open scoped ENNReal BigOperators

theorem slab_vol (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (A ε δ : ℝ),
      1 / (n + 1 : ℝ) ≤ |x i| → rNorm x ≤ 2 → 0 ≤ A → 0 ≤ ε → 0 ≤ δ →
      volume {a : Mon d n → ℝ | rNorm a ≤ A ∧ |formEvalR d n a x| ≤ ε ∧
          (∀ j : Fin (n + 1), |gradVec d n a x j| ≤ δ)}
        ≤ ENNReal.ofReal (K * ε * δ ^ n * A ^ (NN d n - n - 1)) := by
  have hd1 : 1 ≤ d := by omega
  refine ⟨(2 ^ (NN d n)) ^ 2 * ((n : ℝ) + 1) ^ (d * (n + 1)), by positivity, ?_⟩
  intro x i A ε δ hxi hx hA hε hδ
  -- the distinguished monomials
  set em : Fin (n + 1) ↪ Mon d n :=
    ⟨spm d n hd1 i, spm_injective d n hd1 i⟩ with hem
  have hm : n + 1 ≤ Fintype.card (Mon d n) := by
    simpa using Fintype.card_le_of_injective em em.injective
  have hmN : n + 1 ≤ NN d n := hm
  -- the coefficient vectors of the peeling forms
  set c : Fin (n + 1) → ℝ := Fin.cases (x i ^ d) (fun _ => x i ^ (d - 1)) with hcdef
  set w : Fin (n + 1) → ℝ := Fin.cases ε (fun _ => δ) with hwdef
  set Kk : Fin (n + 1) → Mon d n → ℝ :=
    Fin.cases (fun m => veronese d n x m) (fun j => gradKer d n x (i.succAbove j)) with hKk
  set L : Fin (n + 1) → (Mon d n → ℝ) →ₗ[ℝ] ℝ :=
    fun k => Fintype.linearCombination ℝ (Kk k) with hL
  -- evaluation of a peeling form at a standard basis vector
  have hKkval : ∀ (k : Fin (n + 1)) (M : Mon d n), L k (Pi.single M 1) = Kk k M := by
    intro k M
    simp only [L, Fintype.linearCombination_apply, Pi.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single M]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ M) h
  have hem0 : em 0 = spm d n hd1 i 0 := rfl
  have hemsucc : ∀ j : Fin n, em j.succ = spm d n hd1 i j.succ := fun j => rfl
  have hc : ∀ k : Fin (n + 1), L k (Pi.single (em k) 1) = c k := by
    intro k
    rw [hKkval k (em k)]
    induction k using Fin.cases with
    | zero =>
      show Kk 0 (em 0) = x i ^ d
      rw [hem0, spm_zero]
      exact veronese_smon_self d n hd1 i x
    | succ j =>
      show Kk j.succ (em j.succ) = x i ^ (d - 1)
      rw [hemsucc j, spm_succ]
      exact gradKer_smon_eq d n hd1 i (i.succAbove j) (Fin.succAbove_ne i j) x
  have hxi0 : x i ≠ 0 := by
    intro h0
    have hz : |x i| = 0 := by rw [h0]; simp
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith [hxi, hz]
  have hc0 : ∀ k : Fin (n + 1), c k ≠ 0 := by
    intro k
    induction k using Fin.cases with
    | zero => show x i ^ d ≠ 0; exact pow_ne_zero _ hxi0
    | succ j => show x i ^ (d - 1) ≠ 0; exact pow_ne_zero _ hxi0
  have hzero : ∀ k l : Fin (n + 1), k < l → L l (Pi.single (em k) 1) = 0 := by
    intro k l hkl
    rw [hKkval l (em k)]
    induction k using Fin.cases with
    | zero =>
      rw [hem0, spm_zero]
      induction l using Fin.cases with
      | zero => exact absurd hkl (by simp)
      | succ j =>
        show gradKer d n x (i.succAbove j) (smon d n hd1 i i) = 0
        exact gradKer_smon_self d n hd1 i (i.succAbove j) (Fin.succAbove_ne i j) x
    | succ k' =>
      rw [hemsucc k', spm_succ]
      induction l using Fin.cases with
      | zero => exact absurd hkl (not_lt.mpr (le_of_lt (Fin.succ_pos k')))
      | succ l' =>
        show gradKer d n x (i.succAbove l') (smon d n hd1 i (i.succAbove k')) = 0
        have hlt : k' < l' := by
          rw [Fin.lt_def] at hkl ⊢
          simp only [Fin.val_succ] at hkl
          omega
        have hne' : i.succAbove k' ≠ i.succAbove l' :=
          fun h => absurd (Fin.succAbove_right_injective h) (ne_of_lt hlt)
        exact gradKer_smon_ne d n hd1 i (i.succAbove l') (i.succAbove k')
          (Fin.succAbove_ne i l') hne' x
  have hw : ∀ k : Fin (n + 1), 0 ≤ w k := by
    intro k
    induction k using Fin.cases with
    | zero => show 0 ≤ ε; exact hε
    | succ j => show 0 ≤ δ; exact hδ
  have hmain := slab_general (ι := Mon d n) (n + 1) em L c hc hc0 hzero hm w hw A hA
  -- the target set is contained in the peeling set
  have hsubset : {a : Mon d n → ℝ | rNorm a ≤ A ∧ |formEvalR d n a x| ≤ ε ∧
        (∀ j : Fin (n + 1), |gradVec d n a x j| ≤ δ)} ⊆
      {a : Mon d n → ℝ | rNorm a ≤ A ∧ ∀ k, |L k a| ≤ w k} := by
    intro a ha
    refine ⟨ha.1, ?_⟩
    intro k
    induction k using Fin.cases with
    | zero =>
      show |L 0 a| ≤ ε
      have h0 : L 0 a = formEvalR d n a x := by
        simp only [L, Kk, Fin.cases_zero, Fintype.linearCombination_apply, formEvalR,
          smul_eq_mul]
      rw [h0]; exact ha.2.1
    | succ j =>
      show |L j.succ a| ≤ δ
      have h0 : L j.succ a = gradVec d n a x (i.succAbove j) := by
        simp only [L, Kk, Fin.cases_succ, Fintype.linearCombination_apply, smul_eq_mul, gradVec,
          gradF_eq_sum_gradKer]
      rw [h0]; exact ha.2.2 (i.succAbove j)
  -- the numerical bound
  have hbase : 1 ≤ |x i| * ((n : ℝ) + 1) := by
    have h1 : 1 / ((n : ℝ) + 1) * ((n : ℝ) + 1) = 1 := by field_simp
    calc (1 : ℝ) = 1 / ((n : ℝ) + 1) * ((n : ℝ) + 1) := h1.symm
      _ ≤ |x i| * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_right hxi (by positivity)
  have hle1 : 2 * ε / |x i| ^ d ≤ 2 * ε * ((n : ℝ) + 1) ^ d := by
    have hpinv : 1 / |x i| ^ d ≤ ((n : ℝ) + 1) ^ d := by
      rw [div_le_iff₀ (pow_pos (abs_pos.mpr hxi0) d)]
      calc (1 : ℝ) = 1 := rfl
        _ ≤ (|x i| * ((n : ℝ) + 1)) ^ d := one_le_pow₀ hbase
        _ = |x i| ^ d * ((n : ℝ) + 1) ^ d := by rw [mul_pow]
        _ = ((n : ℝ) + 1) ^ d * |x i| ^ d := by ring
    calc 2 * ε / |x i| ^ d = 2 * ε * (1 / |x i| ^ d) := by rw [mul_one_div]
      _ ≤ 2 * ε * ((n : ℝ) + 1) ^ d := mul_le_mul_of_nonneg_left hpinv (by positivity)
  have hle2 : 2 * δ / |x i| ^ (d - 1) ≤ 2 * δ * ((n : ℝ) + 1) ^ d := by
    have hpinv : 1 / |x i| ^ (d - 1) ≤ ((n : ℝ) + 1) ^ (d - 1) := by
      rw [div_le_iff₀ (pow_pos (abs_pos.mpr hxi0) (d - 1))]
      calc (1 : ℝ) = 1 := rfl
        _ ≤ (|x i| * ((n : ℝ) + 1)) ^ (d - 1) := one_le_pow₀ hbase
        _ = |x i| ^ (d - 1) * ((n : ℝ) + 1) ^ (d - 1) := by rw [mul_pow]
        _ = ((n : ℝ) + 1) ^ (d - 1) * |x i| ^ (d - 1) := by ring
    calc 2 * δ / |x i| ^ (d - 1) = 2 * δ * (1 / |x i| ^ (d - 1)) := by rw [mul_one_div]
      _ ≤ 2 * δ * ((n : ℝ) + 1) ^ (d - 1) := mul_le_mul_of_nonneg_left hpinv (by positivity)
      _ ≤ 2 * δ * ((n : ℝ) + 1) ^ d :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by have h : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith)
              (by omega))
            (by positivity)
  have hprodval : (∏ k : Fin (n + 1), 2 * w k / |c k|)
      = (2 * ε / |x i| ^ d) * (2 * δ / |x i| ^ (d - 1)) ^ n := by
    rw [Fin.prod_univ_succ]
    have h0 : 2 * w 0 / |c 0| = 2 * ε / |x i| ^ d := by
      simp only [hwdef, hcdef, Fin.cases_zero, abs_pow]
    have h1 : ∀ j : Fin n, 2 * w j.succ / |c j.succ| = 2 * δ / |x i| ^ (d - 1) := by
      intro j; simp only [hwdef, hcdef, Fin.cases_succ, abs_pow]
    rw [h0, Finset.prod_congr rfl (fun j _ => h1 j), Fin.prod_const]
  have hprodle : (∏ k : Fin (n + 1), 2 * w k / |c k|)
      ≤ 2 ^ (n + 1) * ((n : ℝ) + 1) ^ (d * (n + 1)) * ε * δ ^ n := by
    rw [hprodval]
    set X : ℝ := ((n : ℝ) + 1) ^ d with hX
    calc (2 * ε / |x i| ^ d) * (2 * δ / |x i| ^ (d - 1)) ^ n
        ≤ (2 * ε * X) * (2 * δ * X) ^ n := by
          refine mul_le_mul (le_trans hle1 (le_of_eq ?_)) (pow_le_pow_left₀ (by positivity) ?_ n)
            (by positivity) (by positivity)
          · rw [hX]
          · exact le_trans hle2 (le_of_eq (by rw [hX]))
      _ = (2 * 2 ^ n) * (X * X ^ n) * (ε * δ ^ n) := by ring
      _ = 2 ^ (n + 1) * X ^ (n + 1) * ε * δ ^ n := by
          rw [← pow_succ', ← pow_succ']
          ring
      _ = 2 ^ (n + 1) * ((n : ℝ) + 1) ^ (d * (n + 1)) * ε * δ ^ n := by
          rw [hX, ← pow_mul]
  have hexp : NN d n - (n + 1) = NN d n - n - 1 := Nat.sub_succ _ _
  have h2n1 : (2 : ℝ) ^ (n + 1) ≤ (2 : ℝ) ^ (NN d n) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h2N : (2 : ℝ) ^ (NN d n - n - 1) ≤ (2 : ℝ) ^ (NN d n) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hnum : (∏ k : Fin (n + 1), 2 * w k / |c k|) * (2 * A) ^ (NN d n - (n + 1))
      ≤ ((2 ^ (NN d n)) ^ 2 * ((n : ℝ) + 1) ^ (d * (n + 1))) * ε * δ ^ n
          * A ^ (NN d n - n - 1) := by
    rw [mul_pow, hexp]
    calc (∏ k : Fin (n + 1), 2 * w k / |c k|) *
            (2 ^ (NN d n - n - 1) * A ^ (NN d n - n - 1))
        ≤ (2 ^ (n + 1) * ((n : ℝ) + 1) ^ (d * (n + 1)) * ε * δ ^ n) *
            (2 ^ (NN d n) * A ^ (NN d n - n - 1)) := by
          refine mul_le_mul hprodle ?_ (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right h2N (by positivity)
      _ = (2 ^ (n + 1) * 2 ^ (NN d n)) *
            (((n : ℝ) + 1) ^ (d * (n + 1)) * (ε * (δ ^ n * A ^ (NN d n - n - 1)))) := by
          ring
      _ ≤ ((2 ^ (NN d n)) ^ 2) *
            (((n : ℝ) + 1) ^ (d * (n + 1)) * (ε * (δ ^ n * A ^ (NN d n - n - 1)))) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc 2 ^ (n + 1) * 2 ^ (NN d n) ≤ 2 ^ (NN d n) * 2 ^ (NN d n) :=
                mul_le_mul_of_nonneg_right h2n1 (by positivity)
            _ = (2 ^ (NN d n)) ^ 2 := by ring
      _ = ((2 ^ (NN d n)) ^ 2 * ((n : ℝ) + 1) ^ (d * (n + 1))) * ε * δ ^ n
            * A ^ (NN d n - n - 1) := by
          ring
  calc volume {a : Mon d n → ℝ | rNorm a ≤ A ∧ |formEvalR d n a x| ≤ ε ∧
          (∀ j : Fin (n + 1), |gradVec d n a x j| ≤ δ)}
      ≤ volume {a : Mon d n → ℝ | rNorm a ≤ A ∧ ∀ k, |L k a| ≤ w k} := measure_mono hsubset
    _ ≤ ENNReal.ofReal ((∏ k, 2 * w k / |c k|) *
          (2 * A) ^ (Fintype.card (Mon d n) - (n + 1))) := hmain
    _ ≤ ENNReal.ofReal (((2 ^ (NN d n)) ^ 2 * ((n : ℝ) + 1) ^ (d * (n + 1))) * ε * δ ^ n
          * A ^ (NN d n - n - 1)) := ENNReal.ofReal_le_ofReal hnum

end Work.HP
