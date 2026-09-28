import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.DiagDefs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.latOrth_count_degenerate
import Submission.Work.HP.FM.minkowski_lower
import Submission.Work.HP.FM.veronese_lat
import Submission.Work.HP.Sig2.schmidt_bound
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.lw_ncard_prim_le_two
import Submission.Work.HP.lw_prod_one_add_div_le_level
import Submission.Work.HP.lw_sum_inv_le_dyadic_shells

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Finset

namespace Work.HP

/-! ## Plumbing -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The set of integer vectors of Euclidean norm at most `C` is finite. -/
lemma lw_finite_eNorm_le (C : ℝ) : {v : ι → ℤ | eNorm v ≤ C}.Finite := by
  refine (Set.Finite.pi fun _ : ι => Set.finite_Icc (-⌈C⌉) ⌈C⌉).subset ?_
  intro v hv
  rw [Set.mem_univ_pi]
  intro i
  rw [Set.mem_Icc]
  obtain ⟨hlo, hhi⟩ := abs_le.mp (le_trans (abs_coord_le_eNorm v i) hv)
  constructor
  · have h1 : ((-⌈C⌉ : ℤ) : ℝ) ≤ ((v i : ℤ) : ℝ) := by
      have := Int.le_ceil C
      push_cast
      linarith
    exact_mod_cast h1
  · have h1 : ((v i : ℤ) : ℝ) ≤ ((⌈C⌉ : ℤ) : ℝ) := by
      have := Int.le_ceil C
      push_cast
      linarith
    exact_mod_cast h1

/-- Primitive nonzero lattice points of norm at most `r` are counted by `ballCount`. -/
lemma lw_ncard_le_ballCount_of_sub (L : Submodule ℤ (ι → ℤ)) (r : ℝ) {s : Set (ι → ℤ)}
    (hs : s ⊆ {a : ι → ℤ | a ∈ L ∧ IsPrim a ∧ 0 < eNorm a ∧ eNorm a ≤ r}) :
    ((s.ncard : ℕ) : ℝ) ≤ (ballCount L r : ℝ) := by
  have hsub : s ⊆ {a : ι → ℤ | a ∈ L ∧ eNorm a ≤ r} := fun a ha => ⟨(hs ha).1, (hs ha).2.2.2⟩
  have hfin : ({a : ι → ℤ | a ∈ L ∧ eNorm a ≤ r} : Set (ι → ℤ)).Finite :=
    (lw_finite_eNorm_le r).subset (fun a ha => ha.2)
  have := Set.ncard_le_ncard hsub hfin
  simpa [ballCount] using (Nat.cast_le (α := ℝ)).mpr this

/-- The set of primitive lattice points of norm in `(0,T]` is finite. -/
lemma lw_P_finite (L : Submodule ℤ (ι → ℤ)) (T : ℝ) :
    ({a : ι → ℤ | a ∈ L ∧ IsPrim a ∧ 0 < eNorm a ∧ eNorm a ≤ T} : Set (ι → ℤ)).Finite :=
  (lw_finite_eNorm_le T).subset (fun a ha => ha.2.2.2)

/-! ## Elementary geometric sums -/

lemma lw_sum_pow_two_le (K : ℕ) : ∑ j ∈ Finset.range K, (2:ℝ) ^ (j + 1) ≤ (2:ℝ) ^ (K + 1) := by
  induction K with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have h2 : (2:ℝ) ^ (k + 2) = (2:ℝ) ^ (k + 1) * 2 := by
        rw [show k + 2 = k + 1 + 1 from by omega, pow_succ]
      linarith [ih, pow_pos (by norm_num : (0:ℝ) < 2) (k+1)]

lemma lw_sum_half_pow_le (K : ℕ) : ∑ j ∈ Finset.range K, ((1:ℝ)/2) ^ j ≤ 2 := by
  induction K with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ']
      have hshift : ∑ j ∈ Finset.range k, ((1:ℝ)/2) ^ (j+1)
          = ((1:ℝ)/2) * ∑ j ∈ Finset.range k, ((1:ℝ)/2) ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [pow_succ]; ring
      rw [hshift]
      linarith

/-- The dyadic weights `2^{j+1}/T` of shells above the level `L1` sum to at most `4/L1`. -/
lemma lw_geom_filter {T L1 : ℝ} (hT : 1 ≤ T) (hL1 : 0 < L1) (J : ℕ) :
    ∑ j ∈ (Finset.range (J+1)).filter (fun j => L1 ≤ T / (2:ℝ)^j), ((2:ℝ)^(j+1) / T) ≤ 4 / L1 := by
  classical
  set S := (Finset.range (J+1)).filter (fun j => L1 ≤ T / (2:ℝ)^j) with hS
  by_cases hne : S.Nonempty
  · have hne' : S.Nonempty := hne
    set jmax := S.max' hne' with hjmax
    have hle : ∀ j ∈ S, j ≤ jmax := fun j hj => Finset.le_max' S j hj
    have hjSmem : jmax ∈ S := Finset.max'_mem S hne
    have hkey : L1 ≤ T / (2:ℝ)^jmax := (Finset.mem_filter.mp hjSmem).2
    have h2jmax : (2:ℝ)^jmax ≤ T / L1 := by
      rw [le_div_iff₀ hL1, mul_comm]
      rw [le_div_iff₀ (pow_pos (by norm_num) _)] at hkey
      linarith
    have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
    have h1 : ∑ j ∈ S, ((2:ℝ)^(j+1) / T) = (1/T) * ∑ j ∈ S, (2:ℝ)^(j+1) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h1]
    have h2 : ∑ j ∈ S, (2:ℝ)^(j+1) ≤ (2:ℝ)^(jmax+2) := by
      have hsub : S ⊆ Finset.range (jmax+1) := fun j hj =>
        Finset.mem_range.mpr (Nat.lt_succ_of_le (hle j hj))
      calc ∑ j ∈ S, (2:ℝ)^(j+1) ≤ ∑ j ∈ Finset.range (jmax+1), (2:ℝ)^(j+1) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
        _ ≤ (2:ℝ)^(jmax+2) := by
            have := lw_sum_pow_two_le (jmax+1)
            simpa using this
    calc (1/T) * ∑ j ∈ S, (2:ℝ)^(j+1) ≤ (1/T) * (2:ℝ)^(jmax+2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 4 * (2:ℝ)^jmax / T := by ring
      _ ≤ 4 * (T/L1) / T := by
          refine div_le_div_of_nonneg_right ?_ hTpos.le
          linarith [h2jmax]
      _ = 4 / L1 := by
          field_simp
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.sum_empty]
    positivity

/-! ## Elementary real arithmetic for the final comparison -/

/-- `(J-1)+(m-J) = m-1` for `1 ≤ J ≤ m`. -/
lemma lw_exp_helper {m J : ℕ} (h1 : 1 ≤ J) (h2 : J ≤ m) : (J - 1) + (m - J) = m - 1 := by
  have hJ : (J - 1) + 1 = J := Nat.succ_pred_eq_of_pos h1
  have h3 : (m - 1) - (J - 1) = m - J := by rw [Nat.sub_sub, add_comm 1 (J - 1), hJ]
  rw [← h3, add_comm (J - 1), Nat.sub_add_cancel (by omega : J - 1 ≤ m - 1)]

/-- `T^(J-1)/Q ≤ T^(m-1)/C` when `C ≤ Q T^(m-J)`. -/
lemma lw_arith_T {C Q T : ℝ} {m J : ℕ} (hC : 0 < C) (hQ : 0 < Q) (hT : 1 ≤ T) (hJ : 1 ≤ J)
    (hJm : J ≤ m) (h : C ≤ Q * T ^ (m - J)) : T ^ (J - 1) / Q ≤ T ^ (m - 1) / C := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hinv : 1 / Q ≤ T ^ (m - J) / C := by
    rw [div_le_div_iff₀ hQ hC]
    simpa [mul_comm] using h
  calc T ^ (J - 1) / Q = T ^ (J - 1) * (1 / Q) := by ring
    _ ≤ T ^ (J - 1) * (T ^ (m - J) / C) :=
        mul_le_mul_of_nonneg_left hinv (pow_nonneg hT0.le _)
    _ = T ^ (m - 1) / C := by
        rw [← mul_div_assoc, ← pow_add, lw_exp_helper hJ hJm]

/-- `T^(J-1)/Q ≤ T^(m-n-1)` when `Q ≥ 1`, `1 ≤ J` and `J ≤ m-n`. -/
lemma lw_arith_small {Q T : ℝ} {m n J : ℕ} (hQ : 1 ≤ Q) (hT : 1 ≤ T) (hJ : 1 ≤ J)
    (hJm : J ≤ m - n) : T ^ (J - 1) / Q ≤ T ^ (m - n - 1) := by
  have hQ0 : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  have hT1 : (1:ℝ) ≤ T ^ (J - 1) := one_le_pow₀ hT
  have h2 : T ^ (J - 1) / Q ≤ T ^ (J - 1) := by
    rw [div_le_iff₀ hQ0]
    exact le_mul_of_one_le_right (by positivity) hQ
  exact h2.trans (pow_le_pow_right₀ hT (Nat.sub_le_sub_right hJm 1))

/-- `T^(J-1) μ^(m-J) ≤ T^(m-n) μ^(n-1)` for `T ≤ μ` and `m-n+1 ≤ J ≤ m`, `n ≤ m`. -/
lemma lw_interp {T μ : ℝ} (hT0 : 0 ≤ T) (hTμ : T ≤ μ) {m n J : ℕ}
    (hJle : J ≤ m) (hJge : m - n + 1 ≤ J) (hnm : n ≤ m) :
    T ^ (J - 1) * μ ^ (m - J) ≤ T ^ (m - n) * μ ^ (n - 1) := by
  obtain ⟨s, hs⟩ : ∃ s, J = (m - n) + s :=
    ⟨J - (m - n), (Nat.add_sub_of_le (by omega)).symm⟩
  have hs1 : 1 ≤ s := by omega
  have hsn : s ≤ n := by omega
  have hTμ0 : 0 ≤ μ := le_trans hT0 hTμ
  have h1 : (m - n) + s - 1 = (m - n) + (s - 1) := by omega
  have h2 : m - ((m - n) + s) = n - s := by omega
  have hcomb : μ ^ (s - 1) * μ ^ (n - s) = μ ^ (n - 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hstep : T ^ (s - 1) * μ ^ (n - s) ≤ μ ^ (s - 1) * μ ^ (n - s) :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hT0 hTμ _) (pow_nonneg hTμ0 _)
  rw [hs, h1, h2, pow_add]
  calc T ^ (m - n) * T ^ (s - 1) * μ ^ (n - s)
      = T ^ (m - n) * (T ^ (s - 1) * μ ^ (n - s)) := by ring
    _ ≤ T ^ (m - n) * (μ ^ (s - 1) * μ ^ (n - s)) :=
        mul_le_mul_of_nonneg_left hstep (pow_nonneg hT0 _)
    _ = T ^ (m - n) * μ ^ (n - 1) := by rw [hcomb]

/-- `T^(J-1)/Q ≤ T^(m-n) μ^(n-1)/C` when `C ≤ Q μ^(m-J)`, `T ≤ μ`, `m-n+1 ≤ J ≤ m`, `n ≤ m`. -/
lemma lw_arith_mid {C Q μ T : ℝ} {m n J : ℕ} (hC : 0 < C) (hQ : 0 < Q) (hT : 1 ≤ T)
    (hTμ : T ≤ μ) (hJ : 1 ≤ J) (hJle : J ≤ m) (hJge : m - n + 1 ≤ J) (hnm : n ≤ m)
    (h : C ≤ Q * μ ^ (m - J)) : T ^ (J - 1) / Q ≤ T ^ (m - n) * μ ^ (n - 1) / C := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hμ0 : 0 ≤ μ := le_trans hT0.le hTμ
  have hinv : 1 / Q ≤ μ ^ (m - J) / C := by
    rw [div_le_div_iff₀ hQ hC]
    simpa [mul_comm] using h
  have hkey := lw_interp (T := T) (μ := μ) hT0.le hTμ hJle hJge hnm
  calc T ^ (J - 1) / Q = T ^ (J - 1) * (1 / Q) := by ring
    _ ≤ T ^ (J - 1) * (μ ^ (m - J) / C) :=
        mul_le_mul_of_nonneg_left hinv (pow_nonneg hT0.le _)
    _ = T ^ (J - 1) * μ ^ (m - J) / C := by rw [mul_div_assoc]
    _ ≤ T ^ (m - n) * μ ^ (n - 1) / C := by
        rw [div_le_div_iff_of_pos_right hC]
        exact hkey

/-- `T^(J-1)/Q ≤ μ^(n-1)/C` when `C ≤ Q μ^(m-J)`, `T ≤ μ`, `J ≤ m`, `m ≤ n`. -/
lemma lw_arith_large {C Q μ T : ℝ} {m n J : ℕ} (hC : 0 < C) (hQ : 0 < Q) (hT : 1 ≤ T)
    (hTμ : T ≤ μ) (hJ : 1 ≤ J) (hJm : J ≤ m) (hmn : m ≤ n) (h : C ≤ Q * μ ^ (m - J)) :
    T ^ (J - 1) / Q ≤ μ ^ (n - 1) / C := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hμ1 : (1:ℝ) ≤ μ := le_trans hT hTμ
  have hμ0 : 0 ≤ μ := le_trans hT0.le hTμ
  have hinv : 1 / Q ≤ μ ^ (m - J) / C := by
    rw [div_le_div_iff₀ hQ hC]
    simpa [mul_comm] using h
  have hpow : (J - 1) + (m - J) = m - 1 := lw_exp_helper hJ hJm
  calc T ^ (J - 1) / Q = T ^ (J - 1) * (1 / Q) := by ring
    _ ≤ μ ^ (J - 1) * (μ ^ (m - J) / C) :=
        mul_le_mul (pow_le_pow_left₀ hT0.le hTμ _) hinv (by positivity) (pow_nonneg hμ0 _)
    _ = μ ^ (J - 1) * μ ^ (m - J) / C := by rw [mul_div_assoc]
    _ = μ ^ (m - 1) / C := by
        rw [← pow_add, hpow]
    _ ≤ μ ^ (n - 1) / C := by
        rw [div_le_div_iff_of_pos_right hC]
        exact pow_le_pow_right₀ hμ1 (by omega)

/-- The `μ`-branch right-hand side is always at least `1`. -/
lemma lw_target_ge_one {C μ T : ℝ} {m n : ℕ} (hC : 0 < C) (hT : 1 ≤ T) (hμ0 : 0 ≤ μ) :
    1 ≤ T ^ (m - n) * μ ^ (n - 1) / C + T ^ (m - n - 1) := by
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have h2 : 0 ≤ T ^ (m - n) * μ ^ (n - 1) / C :=
    div_nonneg (mul_nonneg (pow_nonneg hT0 _) (pow_nonneg hμ0 _)) hC.le
  by_cases hn : n ≤ m - 1
  · have h1 : (1:ℝ) ≤ T ^ (m - n - 1) := one_le_pow₀ hT
    linarith
  · have h0 : m - n - 1 = 0 := by omega
    have h1 : (1:ℝ) ≤ T ^ (m - n - 1) := by rw [h0]; norm_num
    linarith

/-- `8/L1 ≤ 8 T^(m-1)/C` when `C ≤ L1 μ^(m-1)` and `μ ≤ T`. -/
lemma lw_lam1_bound {C L1 μ T : ℝ} {m : ℕ} (hC : 0 < C) (hL1 : 0 < L1) (hT : 1 ≤ T)
    (hμ0 : 0 ≤ μ) (hμT : μ ≤ T) (h : C ≤ L1 * μ ^ (m - 1)) :
    8 / L1 ≤ 8 * T ^ (m - 1) / C := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hinv : 1 / L1 ≤ μ ^ (m - 1) / C := by
    rw [div_le_div_iff₀ hL1 hC]
    simpa [mul_comm] using h
  have hpow : μ ^ (m - 1) ≤ T ^ (m - 1) := pow_le_pow_left₀ hμ0 hμT _
  calc 8 / L1 = 8 * (1 / L1) := by ring
    _ ≤ 8 * (μ ^ (m - 1) / C) := mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ ≤ 8 * (T ^ (m - 1) / C) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact div_le_div_of_nonneg_right hpow hC.le
    _ = 8 * T ^ (m - 1) / C := by ring


/-- A product of factors each at least `1` is at least `1` (for `ℝ`). -/
lemma lw_one_le_prod (s : Finset ℕ) (f : ℕ → ℝ) (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have h1 : 1 ≤ f a := h a (Finset.mem_insert_self a s)
      have h2 : 1 ≤ ∏ i ∈ s, f i := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      nlinarith

/-- `(T/2^j)^{J-1} = T^{J-1} * ((1/2)^{J-1})^j`. -/
lemma lw_geom_ratio (T : ℝ) (j J : ℕ) (hJ : 1 ≤ J) :
    (T/(2:ℝ)^j)^(J-1) = T^(J-1) * (((1:ℝ)/2)^(J-1))^j := by
  have hR : T/(2:ℝ)^j = T * ((1:ℝ)/2)^j := by
    rw [div_eq_mul_inv, ← inv_pow]
    norm_num
  rw [hR, mul_pow, ← pow_mul, ← pow_mul, show j * (J-1) = (J-1) * j from by ring]

/-- `(2^{j+1}/T) * (T/2^j)^J = 2 * (T/2^j)^{J-1}` for `J ≥ 1`. -/
lemma lw_weight_mul {T : ℝ} (hT : T ≠ 0) (j J : ℕ) (hJ : 1 ≤ J) :
    ((2:ℝ)^(j+1)/T) * (T/(2:ℝ)^j)^J = 2 * (T/(2:ℝ)^j)^(J-1) := by
  have h2j : (2:ℝ)^j ≠ 0 := pow_ne_zero _ (by norm_num)
  have hx : T/(2:ℝ)^j ≠ 0 := div_ne_zero hT h2j
  have hkey : ((2:ℝ)^(j+1)/T) * (T/(2:ℝ)^j) = 2 := by
    have he : (2:ℝ)^(j+1) = (2:ℝ)^j * 2 := pow_succ _ _
    rw [he, div_mul_div_comm, mul_comm T ((2:ℝ)^j),
      mul_div_mul_right ((2:ℝ)^j * 2) ((2:ℝ)^j) (c := T) hT]
    exact mul_div_cancel_left₀ 2 h2j
  have hxJ : (T/(2:ℝ)^j)^J = (T/(2:ℝ)^j) * (T/(2:ℝ)^j)^(J-1) := by
    conv_lhs => rw [show J = (J-1)+1 from (Nat.sub_add_cancel hJ).symm]
    rw [pow_succ]
    ring
  rw [hxJ, ← mul_assoc, hkey]

/-- Core estimate for `latOrth_weighted`. -/
private theorem lw_core (L : Submodule ℤ (ι → ℤ)) (C : ℝ) (hC : 0 < C) (m : ℕ) (hm2 : 2 ≤ m)
    (n : ℕ) (μ T : ℝ) (hT : 1 ≤ T) (hμ : lam L m ≤ μ)
    (hmin : C ≤ ∏ i ∈ Finset.range m, lam L (i + 1))
    (hpos : ∀ i, 1 ≤ i → i ≤ m → 0 < lam L i)
    (hmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ m → lam L i ≤ lam L j)
    (h1 : 1 ≤ lam L 1)
    (Ks : ℝ) (hKs : 0 < Ks)
    (hsch : ∀ T' : ℝ, 1 ≤ T' →
      (ballCount L T' : ℝ) ≤ Ks * ∏ i ∈ Finset.range m, (T' / lam L (i + 1) + 1)) :
    (∑ᶠ a ∈ ({a : ι → ℤ | a ∈ L ∧ IsPrim a ∧ 0 < eNorm a ∧ eNorm a ≤ T} : Set (ι → ℤ)),
        1 / eNorm a)
      ≤ (8 + 4 * Ks * 2 ^ m * m) *
          (if μ ≤ T then T ^ (m - 1) / C
           else T ^ (m - n) * μ ^ (n - 1) / C + T ^ (m - n - 1)) := by
  classical
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hTne : T ≠ 0 := ne_of_gt hT0
  have h1m : lam L 1 ≤ lam L m := hmono 1 m (by norm_num) (by omega) le_rfl
  have hμ0 : 0 ≤ μ := le_trans zero_le_one (le_trans h1 (le_trans h1m hμ))
  have hlam2 : 1 ≤ lam L 2 := le_trans h1 (hmono 1 2 (by norm_num) (by norm_num) (by omega))
  have hPpos : ∀ J : ℕ, J ≤ m → 0 < ∏ i ∈ Finset.range J, lam L (i+1) := by
    intro J hJ
    refine Finset.prod_pos fun i hi => ?_
    exact hpos (i+1) (by omega) (by have := Finset.mem_range.mp hi; omega)
  have hPc1 : ∀ J : ℕ, J ≤ m → 1 ≤ ∏ i ∈ Finset.range J, lam L (i+1) := by
    intro J hJ
    exact lw_one_le_prod _ _ (fun i hi => le_trans h1 (hmono 1 (i+1) (by norm_num) (by omega)
      (by have := Finset.mem_range.mp hi; omega)))
  set Pc : ℕ → ℝ := fun J => ∏ i ∈ Finset.range J, lam L (i+1) with hPc
  set Jj : ℕ → ℕ := fun j => ((Finset.range m).filter (fun i => lam L (i+1) ≤ T/(2:ℝ)^j)).card
    with hJj
  -- (I) C ≤ Pc J * lam L m ^ (m-J) for J ≤ m
  have hCle : ∀ J : ℕ, J ≤ m → C ≤ Pc J * lam L m ^ (m - J) := by
    intro J hJ
    have hJadd : J + (m - J) = m := Nat.add_sub_of_le hJ
    have hsplit : (∏ i ∈ Finset.range m, lam L (i + 1))
        = Pc J * ∏ i ∈ Finset.range (m - J), lam L (J + i + 1) := by
      rw [hPc, ← hJadd, Finset.prod_range_add]
      simp
    have hbnd : ∀ i ∈ Finset.range (m - J), J + i + 1 ≤ m := by
      intro i hi
      have h2 := Nat.add_lt_add_right (Finset.mem_range.mp hi) J
      rw [Nat.sub_add_cancel hJ] at h2
      omega
    have hkey : ∀ i ∈ Finset.range (m - J), lam L (J + i + 1) ≤ lam L m := fun i hi =>
      hmono (J+i+1) m (by omega) (hbnd i hi) le_rfl
    have hle2 : (∏ i ∈ Finset.range (m - J), lam L (J + i + 1)) ≤ lam L m ^ (m - J) := by
      calc (∏ i ∈ Finset.range (m - J), lam L (J + i + 1))
            ≤ ∏ i ∈ Finset.range (m - J), lam L m :=
              Finset.prod_le_prod₀ (fun i hi => (hpos (J+i+1) (by omega) (hbnd i hi)).le) hkey
        _ = lam L m ^ (m - J) := by simp
    calc C ≤ ∏ i ∈ Finset.range m, lam L (i + 1) := hmin
      _ = Pc J * ∏ i ∈ Finset.range (m - J), lam L (J + i + 1) := hsplit
      _ ≤ Pc J * lam L m ^ (m - J) := mul_le_mul_of_nonneg_left hle2 (hPpos J hJ).le
  -- (II) P and the shell decomposition
  set P : Set (ι → ℤ) := {a | a ∈ L ∧ IsPrim a ∧ 0 < eNorm a ∧ eNorm a ≤ T} with hPdef
  have hPfin : P.Finite := (lw_finite_eNorm_le T).subset (fun a ha => ha.2.2.2)
  have hP1 : ∀ a ∈ P, 1 ≤ eNorm a := fun a ha => one_le_eNorm (eNorm_pos_iff.mp ha.2.2.1)
  have hP2 : ∀ a ∈ P, eNorm a ≤ T := fun a ha => ha.2.2.2
  obtain ⟨J0, hJ01, hJ02⟩ : ∃ J : ℕ, (2:ℝ)^J ≤ T ∧ T < (2:ℝ)^(J+1) := by
    have hfloor1 : 1 ≤ ⌊T⌋₊ := by
      have h := Nat.floor_mono hT
      simpa using h
    refine ⟨Nat.log 2 ⌊T⌋₊, ?_, ?_⟩
    · have h1' : 2^(Nat.log 2 ⌊T⌋₊) ≤ ⌊T⌋₊ := Nat.pow_log_le_self 2 (by omega)
      have h2' : ((2:ℕ)^(Nat.log 2 ⌊T⌋₊) : ℝ) ≤ (⌊T⌋₊ : ℝ) := by exact_mod_cast h1'
      have h3' : ((⌊T⌋₊ : ℕ) : ℝ) ≤ T := Nat.floor_le hT0.le
      calc (2:ℝ)^(Nat.log 2 ⌊T⌋₊) = ((2:ℕ)^(Nat.log 2 ⌊T⌋₊) : ℝ) := by push_cast; ring
        _ ≤ (⌊T⌋₊ : ℝ) := h2'
        _ ≤ T := h3'
    · have h1' : ⌊T⌋₊ < 2^((Nat.log 2 ⌊T⌋₊).succ) :=
        Nat.lt_pow_succ_log_self (by norm_num) ⌊T⌋₊
      have h2' : T < (⌊T⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one T
      have h3' : ((⌊T⌋₊ : ℝ) + 1) ≤ (2:ℝ)^((Nat.log 2 ⌊T⌋₊).succ) := by
        have h4 : (⌊T⌋₊ + 1 : ℕ) ≤ 2^((Nat.log 2 ⌊T⌋₊).succ) := Nat.succ_le_of_lt h1'
        have h5 : ((⌊T⌋₊ + 1 : ℕ) : ℝ) ≤ ((2^((Nat.log 2 ⌊T⌋₊).succ) : ℕ) : ℝ) := by
          exact_mod_cast h4
        push_cast at h5 ⊢
        linarith
      exact lt_of_lt_of_le h2' h3'
  have hshell := @lw_sum_inv_le_dyadic_shells ι _ P hPfin T hT hP1 hP2 J0 hJ02
  -- (III) split into the two regimes
  set S1 := (Finset.range (J0+1)).filter (fun j => T/(2:ℝ)^j < lam L 2) with hS1
  set S2 := (Finset.range (J0+1)).filter (fun j => ¬ (T/(2:ℝ)^j < lam L 2)) with hS2
  have hsplit : (∑ j ∈ Finset.range (J0+1), ((2:ℝ)^(j+1)/T) *
        (({a ∈ P | eNorm a ≤ T/(2:ℝ)^j} : Set (ι → ℤ)).ncard : ℝ))
      = (∑ j ∈ S1, ((2:ℝ)^(j+1)/T) * (({a ∈ P | eNorm a ≤ T/(2:ℝ)^j} : Set (ι → ℤ)).ncard : ℝ))
        + (∑ j ∈ S2, ((2:ℝ)^(j+1)/T) * (({a ∈ P | eNorm a ≤ T/(2:ℝ)^j} : Set (ι → ℤ)).ncard : ℝ)) := by
    rw [hS1, hS2]
    exact (Finset.sum_filter_add_sum_filter_not (Finset.range (J0+1))
      (fun j => T/(2:ℝ)^j < lam L 2)
      (fun j => ((2:ℝ)^(j+1)/T) * (({a ∈ P | eNorm a ≤ T/(2:ℝ)^j} : Set (ι → ℤ)).ncard : ℝ))).symm
  -- Part I: shells below lam L 2
  have hPartI : (∑ j ∈ S1, ((2:ℝ)^(j+1)/T) *
        (({a ∈ P | eNorm a ≤ T/(2:ℝ)^j} : Set (ι → ℤ)).ncard : ℝ)) ≤ 8 / lam L 1 := by
    have hNj : ∀ j ∈ S1, (({a ∈ P | eNorm a ≤ T/(2:ℝ)^j} : Set (ι → ℤ)).ncard : ℝ) ≤ 2 := by
      intro j hj
      have hrj : T / (2:ℝ)^j < lam L 2 := (Finset.mem_filter.mp hj).2
      have hsub : ({a ∈ P | eNorm a ≤ T/(2:ℝ)^j} : Set (ι → ℤ))
          ⊆ {a : ι → ℤ | a ∈ L ∧ IsPrim a ∧ 0 < eNorm a ∧ eNorm a ≤ T/(2:ℝ)^j} :=
        fun a ha => ⟨ha.1.1, ha.1.2.1, ha.1.2.2.1, ha.2⟩
      have h2 : (({a ∈ P | eNorm a ≤ T/(2:ℝ)^j} : Set (ι → ℤ)).ncard : ℝ)
          ≤ (({a : ι → ℤ | a ∈ L ∧ IsPrim a ∧ 0 < eNorm a ∧ eNorm a ≤ T/(2:ℝ)^j} :
              Set (ι → ℤ)).ncard : ℝ) := by
        have hfin : ({a : ι → ℤ | a ∈ L ∧ IsPrim a ∧ 0 < eNorm a ∧
            eNorm a ≤ T/(2:ℝ)^j} : Set (ι → ℤ)).Finite :=
          (lw_finite_eNorm_le _).subset (fun a ha => ha.2.2.2)
        exact_mod_cast Set.ncard_le_ncard hsub hfin
      exact h2.trans (lw_ncard_prim_le_two L hrj)
    have hzw : ∀ j, T / (2:ℝ)^j < lam L 1 →
        (({a ∈ P | eNorm a ≤ T/(2:ℝ)^j} : Set (ι → ℤ)).ncard : ℝ) = 0 := by
      intro j hj
      have hempty : ({a ∈ P | eNorm a ≤ T/(2:ℝ)^j} : Set (ι → ℤ)) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro a ⟨ha1, ha2⟩
        have hle := lam_one_le_eNorm L ha1.1 (eNorm_pos_iff.mp ha1.2.2.1)
        exact absurd (lt_of_le_of_lt ha2 hj) (not_lt.mpr hle)
      rw [hempty]; simp
    have hstep : (∑ j ∈ S1, ((2:ℝ)^(j+1)/T) *
          (({a ∈ P | eNorm a ≤ T/(2:ℝ)^j} : Set (ι → ℤ)).ncard : ℝ))
        ≤ ∑ j ∈ S1, (if lam L 1 ≤ T/(2:ℝ)^j then ((2:ℝ)^(j+1)/T) * 2 else 0) := by
      refine Finset.sum_le_sum fun j hj => ?_
      by_cases hcase : lam L 1 ≤ T/(2:ℝ)^j
      · rw [if_pos hcase]
        exact mul_le_mul_of_nonneg_left (hNj j hj) (by positivity)
      · rw [if_neg hcase, hzw j (not_le.mp hcase), mul_zero]
    have hstep2 : (∑ j ∈ S1, (if lam L 1 ≤ T/(2:ℝ)^j then ((2:ℝ)^(j+1)/T) * 2 else 0))
        ≤ ∑ j ∈ (Finset.range (J0+1)).filter (fun j => lam L 1 ≤ T/(2:ℝ)^j),
            ((2:ℝ)^(j+1)/T) * 2 := by
      rw [← Finset.sum_filter]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro j hj
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1, (Finset.mem_filter.mp hj).2⟩
      · intro j _ _; positivity
    have hstep3 : (∑ j ∈ (Finset.range (J0+1)).filter (fun j => lam L 1 ≤ T/(2:ℝ)^j),
          ((2:ℝ)^(j+1)/T) * 2) ≤ 2 * (4 / lam L 1) := by
      rw [show (∑ j ∈ (Finset.range (J0+1)).filter (fun j => lam L 1 ≤ T/(2:ℝ)^j),
            ((2:ℝ)^(j+1)/T) * 2)
          = 2 * ∑ j ∈ (Finset.range (J0+1)).filter (fun j => lam L 1 ≤ T/(2:ℝ)^j),
              ((2:ℝ)^(j+1)/T) from by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring]
      exact mul_le_mul_of_nonneg_left
        (lw_geom_filter hT (lt_of_lt_of_le zero_lt_one h1) J0) (by norm_num)
    calc (∑ j ∈ S1, ((2:ℝ)^(j+1)/T) * (({a ∈ P | eNorm a ≤ T/(2:ℝ)^j} : Set (ι → ℤ)).ncard : ℝ))
        ≤ ∑ j ∈ S1, (if lam L 1 ≤ T/(2:ℝ)^j then ((2:ℝ)^(j+1)/T) * 2 else 0) := hstep
      _ ≤ 2 * (4 / lam L 1) := hstep2.trans hstep3
      _ = 8 / lam L 1 := by ring
  -- Part II: shells above lam L 2, via the level product bound
  have hPartII : (∑ j ∈ S2, ((2:ℝ)^(j+1)/T) *
        (({a ∈ P | eNorm a ≤ T/(2:ℝ)^j} : Set (ι → ℤ)).ncard : ℝ))
      ≤ 4 * Ks * 2^m * (∑ J ∈ Finset.Icc 2 m, T^(J-1)/Pc J) := by
    have hJjmem : ∀ j ∈ S2, Jj j ∈ Finset.Icc 2 m := by
      intro j hj
      have hrj : lam L 2 ≤ T/(2:ℝ)^j := not_lt.mp (Finset.mem_filter.mp hj).2
      have hjm : Jj j ≤ m := by
        rw [hJj]
        simpa using Finset.card_le_card
          (Finset.filter_subset (fun i => lam L (i+1) ≤ T/(2:ℝ)^j) (Finset.range m))
      have hj2 : 2 ≤ Jj j := by
        rw [hJj]
        have hsub : ({0, 1} : Finset ℕ) ⊆
            (Finset.range m).filter (fun i => lam L (i+1) ≤ T/(2:ℝ)^j) := by
          intro i hi
          simp only [Finset.mem_insert, Finset.mem_singleton] at hi
          rcases hi with rfl | rfl
          · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
              le_trans (hmono 1 2 (by norm_num) (by norm_num) (by omega)) hrj⟩
          · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hrj⟩
        have := Finset.card_le_card hsub
        simpa using this
      exact Finset.mem_Icc.mpr ⟨hj2, hjm⟩
    have hNj : ∀ j ∈ S2, (({a ∈ P | eNorm a ≤ T/(2:ℝ)^j} : Set (ι → ℤ)).ncard : ℝ)
        ≤ Ks * 2^m * (T/(2:ℝ)^j)^(Jj j) / Pc (Jj j) := by
      intro j hj
      have hrj : lam L 2 ≤ T/(2:ℝ)^j := not_lt.mp (Finset.mem_filter.mp hj).2
      have hrj1 : 1 ≤ T/(2:ℝ)^j := le_trans hlam2 hrj
      have hsub : ({a ∈ P | eNorm a ≤ T/(2:ℝ)^j} : Set (ι → ℤ))
          ⊆ {a : ι → ℤ | a ∈ L ∧ IsPrim a ∧ 0 < eNorm a ∧ eNorm a ≤ T/(2:ℝ)^j} :=
        fun a ha => ⟨ha.1.1, ha.1.2.1, ha.1.2.2.1, ha.2⟩
      have hprod := lw_prod_one_add_div_le_level (w := fun i => lam L i)
        (hpos := hpos) (hmono := hmono) (hr := lt_of_lt_of_le zero_lt_one hrj1)
      have hprod' : (∏ i ∈ Finset.range m, (T/(2:ℝ)^j / lam L (i + 1) + 1))
          ≤ 2^m * (T/(2:ℝ)^j)^(Jj j) / Pc (Jj j) := by
        rw [hJj, hPc]
        refine le_of_eq (Finset.prod_congr rfl fun i _ => by rw [add_comm])
        |>.trans hprod
      calc (({a ∈ P | eNorm a ≤ T/(2:ℝ)^j} : Set (ι → ℤ)).ncard : ℝ)
          ≤ (ballCount L (T/(2:ℝ)^j) : ℝ) := lw_ncard_le_ballCount_of_sub L _ hsub
        _ ≤ Ks * ∏ i ∈ Finset.range m, (T/(2:ℝ)^j / lam L (i + 1) + 1) := hsch _ hrj1
        _ ≤ Ks * (2^m * (T/(2:ℝ)^j)^(Jj j) / Pc (Jj j)) :=
            mul_le_mul_of_nonneg_left hprod' hKs.le
        _ = Ks * 2^m * (T/(2:ℝ)^j)^(Jj j) / Pc (Jj j) := by ring
    have hstep1 : (∑ j ∈ S2, ((2:ℝ)^(j+1)/T) *
          (({a ∈ P | eNorm a ≤ T/(2:ℝ)^j} : Set (ι → ℤ)).ncard : ℝ))
        ≤ ∑ j ∈ S2, 2 * Ks * 2^m * ((T/(2:ℝ)^j)^(Jj j - 1) / Pc (Jj j)) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hJj1 : 1 ≤ Jj j := le_trans (by norm_num) (Finset.mem_Icc.mp (hJjmem j hj)).1
      calc ((2:ℝ)^(j+1)/T) * (({a ∈ P | eNorm a ≤ T/(2:ℝ)^j} : Set (ι → ℤ)).ncard : ℝ)
          ≤ ((2:ℝ)^(j+1)/T) * (Ks * 2^m * (T/(2:ℝ)^j)^(Jj j) / Pc (Jj j)) :=
            mul_le_mul_of_nonneg_left (hNj j hj) (by positivity)
        _ = 2 * Ks * 2^m * ((T/(2:ℝ)^j)^(Jj j - 1) / Pc (Jj j)) := by
            rw [show ((2:ℝ)^(j+1)/T) * (Ks * 2^m * (T/(2:ℝ)^j)^(Jj j) / Pc (Jj j))
                = ((2:ℝ)^(j+1)/T) * (T/(2:ℝ)^j)^(Jj j) * (Ks * 2^m / Pc (Jj j)) from by ring,
              lw_weight_mul hTne j (Jj j) hJj1]
            ring
    have hsum_eq : (∑ j ∈ S2, (T/(2:ℝ)^j)^(Jj j - 1) / Pc (Jj j))
        = ∑ J ∈ Finset.Icc 2 m,
            ∑ j ∈ S2.filter (fun j => Jj j = J), (T/(2:ℝ)^j)^(J-1) / Pc J := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := S2) (t := Finset.Icc 2 m)
        (g := fun j => Jj j) (f := fun j => (T/(2:ℝ)^j)^(Jj j - 1) / Pc (Jj j))
        (fun j hj => hJjmem j hj)]
      refine Finset.sum_congr rfl fun J hJ => ?_
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [(Finset.mem_filter.mp hj).2]
    have hfiber : (∑ j ∈ S2, 2 * Ks * 2^m * ((T/(2:ℝ)^j)^(Jj j - 1) / Pc (Jj j)))
        = 2 * Ks * 2^m * ∑ J ∈ Finset.Icc 2 m,
            ∑ j ∈ S2.filter (fun j => Jj j = J), (T/(2:ℝ)^j)^(J-1) / Pc J := by
      rw [← Finset.mul_sum, hsum_eq]
    have hfib : ∀ J ∈ Finset.Icc 2 m,
        (∑ j ∈ S2.filter (fun j => Jj j = J), (T/(2:ℝ)^j)^(J - 1) / Pc J)
          ≤ 2 * T^(J-1) / Pc J := by
      intro J hJmem
      obtain ⟨hJ2, hJm⟩ := Finset.mem_Icc.mp hJmem
      have hsub : S2.filter (fun j => Jj j = J) ⊆ Finset.range (J0+1) := fun j hj =>
        (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
      have hsum : (∑ j ∈ S2.filter (fun j => Jj j = J), (T/(2:ℝ)^j)^(J - 1))
          ≤ 2 * T^(J-1) := by
        have hR : ∀ j : ℕ, T/(2:ℝ)^j = T * ((1:ℝ)/2)^j := by
          intro j
          rw [div_eq_mul_inv, ← inv_pow]
          norm_num
        calc (∑ j ∈ S2.filter (fun j => Jj j = J), (T/(2:ℝ)^j)^(J - 1))
            ≤ ∑ j ∈ Finset.range (J0+1), (T/(2:ℝ)^j)^(J - 1) :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => by positivity)
          _ = T^(J-1) * ∑ j ∈ Finset.range (J0+1), (((1:ℝ)/2)^(J-1))^j := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun j _ => ?_
              exact lw_geom_ratio T j J (by omega)
          _ ≤ T^(J-1) * ∑ j ∈ Finset.range (J0+1), ((1:ℝ)/2)^j := by
              refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hT0.le _)
              have hfac : ((1:ℝ)/2)^(J-1) ≤ 1/2 := by
                have hJ2' : 2 ≤ J := hJ2
                have h1 : ((1:ℝ)/2)^(J-1) = (1/2) * ((1:ℝ)/2)^(J-2) := by
                  rw [show J - 1 = (J-2)+1 from by omega, pow_succ, mul_comm]
                have h2 : ((1:ℝ)/2)^(J-2) ≤ 1 :=
                  pow_le_one₀ (by norm_num) (by norm_num)
                rw [h1]
                nlinarith
              refine Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (by positivity) hfac j
          _ ≤ T^(J-1) * 2 := mul_le_mul_of_nonneg_left (lw_sum_half_pow_le (J0+1))
                (pow_nonneg hT0.le _)
          _ = 2 * T^(J-1) := by ring
      calc (∑ j ∈ S2.filter (fun j => Jj j = J), (T/(2:ℝ)^j)^(J - 1) / Pc J)
          = (∑ j ∈ S2.filter (fun j => Jj j = J), (T/(2:ℝ)^j)^(J - 1)) / Pc J := by
            rw [Finset.sum_div]
        _ ≤ (2 * T^(J-1)) / Pc J := by
            rw [div_le_div_iff_of_pos_right (hPpos J hJm)]
            exact hsum
        _ = 2 * T^(J-1) / Pc J := by ring
    calc (∑ j ∈ S2, ((2:ℝ)^(j+1)/T) * (({a ∈ P | eNorm a ≤ T/(2:ℝ)^j} : Set (ι → ℤ)).ncard : ℝ))
        ≤ ∑ j ∈ S2, 2 * Ks * 2^m * ((T/(2:ℝ)^j)^(Jj j - 1) / Pc (Jj j)) := hstep1
      _ = 2 * Ks * 2^m * ∑ J ∈ Finset.Icc 2 m,
            ∑ j ∈ S2.filter (fun j => Jj j = J), (T/(2:ℝ)^j)^(J-1) / Pc J := hfiber
      _ ≤ 2 * Ks * 2^m * ∑ J ∈ Finset.Icc 2 m, 2 * T^(J-1) / Pc J :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hfib) (by positivity)
      _ = 4 * Ks * 2^m * ∑ J ∈ Finset.Icc 2 m, T^(J-1) / Pc J := by
          rw [show (∑ J ∈ Finset.Icc 2 m, 2 * T^(J-1) / Pc J)
              = 2 * ∑ J ∈ Finset.Icc 2 m, T^(J-1) / Pc J from by
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun J _ => by rw [mul_div_assoc]]
          ring
  -- combine the two parts
  have hS : (∑ᶠ a ∈ P, 1 / eNorm a)
      ≤ 8 / lam L 1 + 4 * Ks * 2^m * (∑ J ∈ Finset.Icc 2 m, T^(J-1) / Pc J) := by
    refine le_trans hshell ?_
    rw [hsplit]
    exact add_le_add hPartI hPartII
  -- the two regimes
  by_cases hbranch : μ ≤ T
  · rw [if_pos hbranch]
    have hlam_mone : (1:ℝ) ≤ lam L m := le_trans h1 (hmono 1 m (by norm_num) (by omega) le_rfl)
    have hterm : ∀ J ∈ Finset.Icc 2 m, T^(J-1) / Pc J ≤ T^(m-1) / C := by
      intro J hJmem
      obtain ⟨hJ2, hJm⟩ := Finset.mem_Icc.mp hJmem
      refine lw_arith_T hC (hPpos J hJm) hT (by omega) hJm ?_
      refine le_trans (hCle J hJm) ?_
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (hpos m (by omega) le_rfl).le (le_trans hμ hbranch) (m - J))
        (hPpos J hJm).le
    have hcard : ((Finset.Icc 2 m).card : ℝ) ≤ (m : ℝ) := by
      rw [Nat.card_Icc]
      exact_mod_cast (by omega : (m - 1) ≤ m)
    have hY : 0 ≤ T^(m-1) / C := div_nonneg (pow_nonneg hT0.le _) hC.le
    have hpart1 : 8 / lam L 1 ≤ 8 * (T^(m-1) / C) := by
      have hle : C ≤ lam L 1 * μ ^ (m - 1) := by
        have h := hCle 1 (by omega)
        have hprod : Pc 1 = lam L 1 := by rw [hPc]; simp
        rw [hprod] at h
        refine le_trans h (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (hpos m (by omega) le_rfl).le hμ (m - 1))
          (hpos 1 (by norm_num) (by omega)).le)
      have hlb := lw_lam1_bound hC (hpos 1 (by norm_num) (by omega)) hT hμ0 hbranch hle
      rwa [mul_div_assoc] at hlb
    calc (∑ᶠ a ∈ P, 1 / eNorm a)
        ≤ 8 / lam L 1 + 4 * Ks * 2^m * (∑ J ∈ Finset.Icc 2 m, T^(J-1) / Pc J) := hS
      _ ≤ 8 / lam L 1 + 4 * Ks * 2^m * ((Finset.Icc 2 m).card * (T^(m-1) / C)) := by
          refine add_le_add le_rfl ?_
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc (∑ J ∈ Finset.Icc 2 m, T^(J-1) / Pc J)
              ≤ ∑ _J ∈ Finset.Icc 2 m, (T^(m-1) / C) := Finset.sum_le_sum hterm
            _ = (Finset.Icc 2 m).card * (T^(m-1) / C) := by
                rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 8 * (T^(m-1) / C) + 4 * Ks * 2^m * (m * (T^(m-1) / C)) := by
          refine add_le_add hpart1 ?_
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hY) (by positivity)
      _ = (8 + 4 * Ks * 2^m * m) * (T^(m-1) / C) := by ring
  · rw [if_neg hbranch]
    have hTμ : T ≤ μ := (not_le.mp hbranch).le
    have hlam_mone : (1:ℝ) ≤ lam L m := le_trans h1 (hmono 1 m (by norm_num) (by omega) le_rfl)
    have htarget : 1 ≤ T^(m-n) * μ^(n-1) / C + T^(m-n-1) := lw_target_ge_one hC hT hμ0
    have hY : 0 ≤ T^(m-n) * μ^(n-1) / C + T^(m-n-1) := le_trans zero_le_one htarget
    have hterm : ∀ J ∈ Finset.Icc 2 m,
        T^(J-1) / Pc J ≤ T^(m-n) * μ^(n-1) / C + T^(m-n-1) := by
      intro J hJmem
      obtain ⟨hJ2, hJm⟩ := Finset.mem_Icc.mp hJmem
      have hleμ : C ≤ Pc J * μ ^ (m - J) := le_trans (hCle J hJm)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hpos m (by omega) le_rfl).le hμ (m - J))
          (hPpos J hJm).le)
      by_cases hn : n ≤ m - 1
      · by_cases hJn : J ≤ m - n
        · have h := lw_arith_small (Q := Pc J) (hPc1 J hJm) hT (by omega) hJn
          exact h.trans (le_add_of_nonneg_left
            (div_nonneg (mul_nonneg (pow_nonneg hT0.le _) (pow_nonneg hμ0 _)) hC.le))
        · have hJge : m - n + 1 ≤ J := by omega
          have h := lw_arith_mid hC (hPpos J hJm) hT hTμ (by omega) hJm hJge (by omega) hleμ
          exact h.trans (le_add_of_nonneg_right (pow_nonneg hT0.le _))
      · have hmn : m ≤ n := by omega
        have h := lw_arith_large hC (hPpos J hJm) hT hTμ (by omega) hJm hmn hleμ
        have hA : μ^(n-1) / C = T^(m-n) * μ^(n-1) / C := by
          rw [show m - n = 0 from by omega, pow_zero, one_mul]
        rw [hA] at h
        exact h.trans (le_add_of_nonneg_right (pow_nonneg hT0.le _))
    have hcard : ((Finset.Icc 2 m).card : ℝ) ≤ (m : ℝ) := by
      rw [Nat.card_Icc]
      exact_mod_cast (by omega : (m - 1) ≤ m)
    calc (∑ᶠ a ∈ P, 1 / eNorm a)
        ≤ 8 / lam L 1 + 4 * Ks * 2^m * (∑ J ∈ Finset.Icc 2 m, T^(J-1) / Pc J) := hS
      _ ≤ 8 / lam L 1 + 4 * Ks * 2^m *
            ((Finset.Icc 2 m).card * (T^(m-n) * μ^(n-1) / C + T^(m-n-1))) := by
          refine add_le_add le_rfl ?_
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc (∑ J ∈ Finset.Icc 2 m, T^(J-1) / Pc J)
              ≤ ∑ _J ∈ Finset.Icc 2 m, (T^(m-n) * μ^(n-1) / C + T^(m-n-1)) :=
                Finset.sum_le_sum hterm
            _ = (Finset.Icc 2 m).card * (T^(m-n) * μ^(n-1) / C + T^(m-n-1)) := by
                rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 8 * (T^(m-n) * μ^(n-1) / C + T^(m-n-1)) +
            4 * Ks * 2^m * (m * (T^(m-n) * μ^(n-1) / C + T^(m-n-1))) := by
          refine add_le_add ?_ ?_
          · have h8 : 8 / lam L 1 ≤ 8 := by
              rw [div_le_iff₀ (hpos 1 (by norm_num) (by omega))]
              linarith
            linarith
          · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hY) (by positivity)
      _ = (8 + 4 * Ks * 2^m * m) * (T^(m-n) * μ^(n-1) / C + T^(m-n-1)) := by ring

/-! ## The main theorem -/

theorem latOrth_weighted (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ)
    (hc3 : 5 ≤ Fintype.card ι) :
    ∃ K : ℝ, 0 < K ∧ ∀ (c : ι → ℤ), IsPrim c → ∀ μ T : ℝ, 1 ≤ T →
      lam (latOrth c) (Fintype.card ι - 1) ≤ μ →
      (∑ᶠ a ∈ ({a : ι → ℤ | a ∈ latOrth c ∧ IsPrim a ∧ 0 < eNorm a ∧ eNorm a ≤ T} :
          Set (ι → ℤ)), 1 / eNorm a)
        ≤ K * (if μ ≤ T then T ^ (Fintype.card ι - 2) / eNorm c
               else T ^ (Fintype.card ι - n - 1) * μ ^ (n - 1) / eNorm c
                 + T ^ (Fintype.card ι - n - 2)) := by
  classical
  obtain ⟨Ks, hKs, hsch0⟩ := Sig2.schmidt_bound (ι := ι)
  refine ⟨8 + 4 * Ks * 2 ^ (Fintype.card ι) * (Fintype.card ι), by positivity, ?_⟩
  intro c hc μ T hT hlam
  have hk : 1 ≤ Fintype.card ι := by omega
  have hm2 : 2 ≤ Fintype.card ι - 1 := by omega
  have hrk : rk (latOrth c) = Fintype.card ι - 1 := LCD_rk_latOrth c hc
  have hCpos : 0 < eNorm c := eNorm_pos_of_ne_zero (isPrim_ne_zero hc)
  have hdet : detL (latOrth c) = eNorm c := FM.detL_latOrth_of_prim c hc
  have hmink : eNorm c ≤ ∏ i ∈ Finset.range (Fintype.card ι - 1), lam (latOrth c) (i+1) := by
    rw [← hdet, ← hrk]
    exact FM.minkowski_lower (latOrth c)
  have hpos' : ∀ i, 1 ≤ i → i ≤ Fintype.card ι - 1 → 0 < lam (latOrth c) i := by
    intro i hi1 him
    exact lam_pos (latOrth c) hi1 (by rw [hrk]; exact him)
  have hmono' : ∀ i j, 1 ≤ i → i ≤ j → j ≤ Fintype.card ι - 1 →
      lam (latOrth c) i ≤ lam (latOrth c) j := by
    intro i j hi hij hj
    exact lam_mono (latOrth c) hij (by rw [hrk]; exact hj)
  have h1' : 1 ≤ lam (latOrth c) 1 := by
    rw [lam_eq_sInf]
    refine le_csInf (lamSet_nonempty _ (by rw [hrk]; omega)) ?_
    rintro r ⟨hr0, f, hfL, hfLI, hfr⟩
    have h0 : f 0 ≠ 0 := hfLI.ne_zero 0
    exact (one_le_eNorm h0).trans (hfr 0)
  have hsch' : ∀ T' : ℝ, 1 ≤ T' → (ballCount (latOrth c) T' : ℝ)
      ≤ Ks * ∏ i ∈ Finset.range (Fintype.card ι - 1), (T' / lam (latOrth c) (i + 1) + 1) := by
    intro T' hT'
    have h := hsch0 (latOrth c) T' hT'
    rwa [hrk] at h
  have hcore := lw_core (L := latOrth c) (C := eNorm c) hCpos (Fintype.card ι - 1) hm2 n μ T hT
    hlam hmink hpos' hmono' h1' Ks hKs hsch'
  have hexp2 : Fintype.card ι - 2 = Fintype.card ι - 1 - 1 := by omega
  have hexp1 : Fintype.card ι - n - 1 = Fintype.card ι - 1 - n := by omega
  have hexp0 : Fintype.card ι - n - 2 = Fintype.card ι - 1 - n - 1 := by omega
  have hKle : (8 + 4 * Ks * 2 ^ (Fintype.card ι - 1) * ((Fintype.card ι - 1 : ℕ) : ℝ))
      ≤ 8 + 4 * Ks * 2 ^ (Fintype.card ι) * ((Fintype.card ι : ℕ) : ℝ) := by
    have h2 : (2:ℝ)^(Fintype.card ι - 1) ≤ (2:ℝ)^(Fintype.card ι) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hm : ((Fintype.card ι - 1 : ℕ) : ℝ) ≤ ((Fintype.card ι : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le _ _
    have hA : 0 ≤ 4 * Ks * 2 ^ (Fintype.card ι - 1) := by positivity
    have hB : 0 ≤ 2 ^ (Fintype.card ι) := by positivity
    calc 8 + 4 * Ks * 2 ^ (Fintype.card ι - 1) * ((Fintype.card ι - 1 : ℕ) : ℝ)
        ≤ 8 + 4 * Ks * 2 ^ (Fintype.card ι) * ((Fintype.card ι - 1 : ℕ) : ℝ) := by
          gcongr
      _ ≤ 8 + 4 * Ks * 2 ^ (Fintype.card ι) * ((Fintype.card ι : ℕ) : ℝ) := by
          gcongr
  refine le_trans hcore ?_
  by_cases hbranch : μ ≤ T
  · rw [if_pos hbranch, if_pos hbranch, hexp2]
    refine mul_le_mul_of_nonneg_right hKle ?_
    exact div_nonneg (pow_nonneg (le_trans zero_le_one hT) _) hCpos.le
  · rw [if_neg hbranch, if_neg hbranch, hexp1, hexp0]
    refine mul_le_mul_of_nonneg_right hKle ?_
    have hμ0 : 0 ≤ μ := le_trans zero_le_one (le_trans h1'
      (le_trans (hmono' 1 (Fintype.card ι - 1) (by norm_num) (by omega) le_rfl) hlam))
    exact add_nonneg (div_nonneg (mul_nonneg (pow_nonneg (le_trans zero_le_one hT) _)
      (pow_nonneg hμ0 _)) hCpos.le) (pow_nonneg (le_trans zero_le_one hT) _)

end Work.HP
