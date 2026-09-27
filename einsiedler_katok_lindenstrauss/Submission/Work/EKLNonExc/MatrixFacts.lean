import Submission.Work.EKLNonExc.Defs

/-!
# Entry-level matrix facts for the C9 argument

The computations behind `LsetFacts`: the centraliser characterisation, the contraction of the
`bconj`-conjugate of an element of `Lset hab`, and the `fmax` bound.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.EKLNonExc

open Work.EKLContract

noncomputable section

/-! ## `M * (1 + s E_ab)` and `(1 + s E_ab) * M` -/

lemma mul_one_add_single_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3) (s : ℝ)
    (k l : Fin 3) :
    (M * (1 + Matrix.single a b s)) k l = M k l + (if l = b then M k a * s else 0) := by
  rw [Matrix.mul_apply]
  have h1 : (∑ m, M k m * (if m = l then (1 : ℝ) else 0)) = M k l := by
    rw [show (∑ m, M k m * (if m = l then (1 : ℝ) else 0))
        = ∑ m, (if m = l then M k m * 1 else 0) from
      Finset.sum_congr rfl fun m _ => by split_ifs <;> ring]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ l)]
    ring
  have h2 : (∑ m, M k m * (if a = m ∧ b = l then s else 0)) =
      if l = b then M k a * s else 0 := by
    by_cases hbl : b = l
    · rw [if_pos hbl.symm]
      have hcongr : ∀ m, M k m * (if a = m ∧ b = l then s else 0) =
          (if m = a then M k m * s else 0) := by
        intro m
        by_cases hm : m = a
        · rw [if_pos ⟨hm.symm, hbl⟩, if_pos hm]
        · rw [if_neg (fun hh => hm hh.1.symm), if_neg hm, mul_zero]
      rw [Finset.sum_congr rfl fun m _ => hcongr m, Finset.sum_ite_eq',
        if_pos (Finset.mem_univ a)]
    · rw [if_neg (fun h : l = b => hbl h.symm)]
      exact Finset.sum_eq_zero fun m _ => by
        rw [if_neg (fun hh => hbl hh.2), mul_zero]
  have hsplit : (∑ m, M k m * (1 + Matrix.single a b s) m l) =
      ∑ m, (M k m * (if m = l then (1 : ℝ) else 0) +
        M k m * (if a = m ∧ b = l then s else 0)) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    ring
  rw [hsplit, Finset.sum_add_distrib, h1, h2]

lemma one_add_single_mul_apply (M : Matrix (Fin 3) (Fin 3) ℝ) (a b : Fin 3) (s : ℝ)
    (k l : Fin 3) :
    ((1 + Matrix.single a b s) * M) k l = M k l + (if k = a then s * M b l else 0) := by
  rw [Matrix.mul_apply]
  have h1 : (∑ m, (if k = m then (1 : ℝ) else 0) * M m l) = M k l := by
    rw [show (∑ m, (if k = m then (1 : ℝ) else 0) * M m l)
        = ∑ m, (if k = m then 1 * M m l else 0) from
      Finset.sum_congr rfl fun m _ => by split_ifs <;> ring]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ k)]
    ring
  have h2 : (∑ m, (if a = k ∧ b = m then s else 0) * M m l) =
      if k = a then s * M b l else 0 := by
    by_cases hka : k = a
    · rw [if_pos hka]
      have hcongr : ∀ m, (if a = k ∧ b = m then s else 0) * M m l =
          (if b = m then s * M m l else 0) := by
        intro m
        by_cases hm : m = b
        · rw [if_pos ⟨hka.symm, hm.symm⟩, if_pos hm.symm]
        · rw [if_neg (fun hh => hm hh.2.symm), if_neg (fun h => hm h.symm), zero_mul]
      rw [Finset.sum_congr rfl fun m _ => hcongr m, Finset.sum_ite_eq,
        if_pos (Finset.mem_univ b)]
    · rw [if_neg hka]
      exact Finset.sum_eq_zero fun m _ => by
        rw [if_neg (fun hh => hka hh.1.symm), zero_mul]
  have hsplit : (∑ m, (1 + Matrix.single a b s) k m * M m l) =
      ∑ m, ((if k = m then (1 : ℝ) else 0) * M m l +
        (if a = k ∧ b = m then s else 0) * M m l) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    ring
  rw [hsplit, Finset.sum_add_distrib, h1, h2]

/-! ## The centraliser `Lset` -/

lemma mem_Lset_iff {a b : Fin 3} (hab : a ≠ b) (g : SL3) :
    g ∈ Lset hab ↔ g a a = g b b ∧ (∀ i : Fin 3, i ≠ a → g i a = 0) ∧
      (∀ j : Fin 3, j ≠ b → g b j = 0) := by
  have hu : toMat (uij hab 1) = 1 + Matrix.single a b (1 : ℝ) := rfl
  have hmain : g ∈ Lset hab ↔ ∀ k l : Fin 3,
      (if l = b then g k a else 0) = (if k = a then g b l else 0) := by
    rw [Lset]
    constructor
    · intro h k l
      have h2 : toMat (g * uij hab 1) k l = toMat (uij hab 1 * g) k l := by rw [h]
      rw [toMat_mul, toMat_mul, hu, mul_one_add_single_apply, one_add_single_mul_apply]
        at h2
      simp only [mul_one, one_mul] at h2
      linarith
    · intro h
      refine ext_apply fun k l => ?_
      show toMat (g * uij hab 1) k l = toMat (uij hab 1 * g) k l
      rw [toMat_mul, toMat_mul, hu, mul_one_add_single_apply, one_add_single_mul_apply]
      simp only [mul_one, one_mul]
      rw [h k l]
  rw [hmain]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have h1 := h a b
      rwa [if_pos rfl, if_pos rfl] at h1
    · intro i hi
      have h1 := h i b
      rwa [if_pos rfl, if_neg hi] at h1
    · intro j hj
      have h1 := h a j
      rw [if_neg hj, if_pos rfl] at h1
      exact h1.symm
  · rintro ⟨haa, h1, h2⟩ k l
    by_cases hlb : l = b
    · subst hlb
      by_cases hka : k = a
      · subst hka
        rw [if_pos rfl, if_pos rfl]
        exact haa
      · rw [if_pos rfl, if_neg hka]
        exact h1 k hka
    · by_cases hka : k = a
      · subst hka
        rw [if_neg hlb, if_pos rfl]
        exact (h2 l hlb).symm
      · rw [if_neg hlb, if_neg hka]

lemma eq_a_or_b_or_c {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (i : Fin 3) : i = a ∨ i = b ∨ i = c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases i <;> simp_all

lemma fmax_eq_zero_of_mem_Lset {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    {g : SL3} (hg : g ∈ Lset hab) (hf : fmax a b c g = 0) :
    g a a = g b b ∧ ∀ i j : Fin 3, i ≠ j → g i j = 0 := by
  obtain ⟨haa, h1, h2⟩ := (mem_Lset_iff hab g).mp hg
  have hab0 : g a b = 0 := by
    have hle : |g a b| ≤ 0 := by
      rw [← hf]; exact le_trans (le_max_left _ _) (le_max_left _ _)
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  have hac0 : g a c = 0 := by
    have hle : |g a c| ≤ 0 := by
      rw [← hf]; exact le_trans (le_max_right _ _) (le_max_left _ _)
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  have hcb0 : g c b = 0 := by
    have hle : |g c b| ≤ 0 := by rw [← hf]; exact le_max_right _ _
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  refine ⟨haa, fun i j hij => ?_⟩
  rcases eq_a_or_b_or_c hab hac hcb i with hia | hib | hic
  · rcases eq_a_or_b_or_c hab hac hcb j with hja | hjb | hjc
    · exact absurd (hia.trans hja.symm) hij
    · rw [hia, hjb]; exact hab0
    · rw [hia, hjc]; exact hac0
  · rw [hib]
    rcases eq_a_or_b_or_c hab hac hcb j with hja | hjb | hjc
    · rw [hja]; exact h1 b (Ne.symm hab)
    · exact absurd (hib.trans hjb.symm) hij
    · rw [hjc]; exact h2 c hcb
  · rw [hic]
    rcases eq_a_or_b_or_c hab hac hcb j with hja | hjb | hjc
    · rw [hja]; exact h1 c (Ne.symm hac)
    · rw [hjb]; exact hcb0
    · exact absurd (hic.trans hjc.symm) hij

lemma aPrime_one_mul (c : Fin 3) (r : ℝ) : aPrime c 1 * aPrime c r = aPrime c (r + 1) := by
  rw [aPrime, aPrime, aPrime, aDiag_add]
  congr 1
  funext i
  by_cases h : i = c <;> simp [h] <;> ring

lemma aPrime_pow (c : Fin 3) (n : ℕ) : (aPrime c (1 : ℝ)) ^ n = aPrime c (n : ℝ) := by
  induction n with
  | zero =>
    rw [pow_zero]
    have hv : (fun i : Fin 3 => if i = c then -2 * ((0 : ℕ) : ℝ) else ((0 : ℕ) : ℝ))
        = (0 : Fin 3 → ℝ) := by
      funext i; by_cases h : i = c <;> simp [h]
    rw [aPrime, hv, aDiag_zero]
  | succ k ih =>
    rw [pow_succ, ih, aPrime, aPrime, aDiag_add]
    congr 1
    funext i
    by_cases h : i = c <;> simp [h] <;> push_cast <;> ring

lemma aPrime_commute_bconj (a b c : Fin 3) (s : ℝ) :
    bconj a b c * aPrime c s = aPrime c s * bconj a b c := by
  rw [bconj, aPrime, aDiag_add, aDiag_add]
  congr 1
  funext i
  simp only [Pi.add_apply]
  ring

/-! ## The conjugation by `bconj` -/

lemma sum_uvec {a b c : Fin 3} (hab : a ≠ b) : (∑ i : Fin 3, uvec a b c i) = 0 := by
  have hfun : uvec a b c = fun i : Fin 3 =>
      (if i = a then (-1 : ℝ) else 0) + (if i = b then (1 : ℝ) else 0) := by
    funext i
    by_cases hia : i = a
    · simp only [uvec, if_pos hia, if_neg (fun h => hab (hia.symm.trans h))]
      ring
    · by_cases hib : i = b
      · simp only [uvec, if_neg hia, if_pos hib]
        ring
      · simp only [uvec, if_neg hia, if_neg hib]
        ring
  rw [hfun, Finset.sum_add_distrib]
  have ha : (∑ i : Fin 3, (if i = a then (-1 : ℝ) else 0)) = -1 := by
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ a)]
  have hb : (∑ i : Fin 3, (if i = b then (1 : ℝ) else 0)) = 1 := by
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ b)]
  rw [ha, hb]; ring

lemma toMat_bconj (a b c : Fin 3) (hab : a ≠ b) :
    toMat (bconj a b c) = Matrix.diagonal (fun i => Real.exp (uvec a b c i)) := by
  rw [bconj, toMat_aDiag, sum_uvec hab]
  congr 1
  funext i
  rw [zero_div, sub_zero]

lemma toMat_aPrime (c : Fin 3) (s : ℝ) :
    toMat (aPrime c s) = Matrix.diagonal (fun i => Real.exp (if i = c then -2 * s else s)) := by
  have hsum : (∑ j : Fin 3, (if j = c then -2 * s else s)) = 0 := by
    fin_cases c <;> rw [Fin.sum_univ_three] <;> simp <;> ring
  rw [aPrime, toMat_aDiag, hsum]
  congr 1
  funext i
  rw [zero_div, sub_zero]

lemma diagonal_mul_apply (v : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    (Matrix.diagonal v * M) i j = v i * M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro m _ hm
    rw [Matrix.diagonal_apply_ne _ hm.symm, zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

lemma mul_diagonal_apply (v : Fin 3 → ℝ) (M : Matrix (Fin 3) (Fin 3) ℝ) (i j : Fin 3) :
    (M * Matrix.diagonal v) i j = M i j * v j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.diagonal_apply_eq]
  · intro m _ hm
    rw [Matrix.diagonal_apply_ne _ hm, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

lemma toMat_pow_bconj (a b c : Fin 3) (hab : a ≠ b) (m : ℕ) :
    toMat (bconj a b c ^ m) =
      Matrix.diagonal (fun i => Real.exp ((m : ℝ) * uvec a b c i)) := by
  induction m with
  | zero =>
    rw [pow_zero, toMat_one]
    rw [show (fun i : Fin 3 => Real.exp (((0 : ℕ) : ℝ) * uvec a b c i))
        = (fun _ : Fin 3 => (1 : ℝ)) from by
      funext i; rw [Nat.cast_zero, zero_mul, Real.exp_zero]]
    exact Matrix.diagonal_one
  | succ k ih =>
    rw [pow_succ, toMat_mul, ih, toMat_bconj a b c hab, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring

lemma toMat_inv_pow_bconj (a b c : Fin 3) (hab : a ≠ b) (m : ℕ) :
    toMat ((bconj a b c ^ m)⁻¹) =
      Matrix.diagonal (fun i => Real.exp (-((m : ℝ) * uvec a b c i))) := by
  have hp := toMat_pow_bconj a b c hab m
  have hcoe : toMat ((bconj a b c ^ m)⁻¹) =
      (Matrix.diagonal (fun i => Real.exp ((m : ℝ) * uvec a b c i))).adjugate := by
    rw [← hp]
    exact Matrix.SpecialLinearGroup.coe_inv _
  have herase : ∀ i : Fin 3,
      (∏ j ∈ Finset.univ.erase i, Real.exp ((m : ℝ) * uvec a b c j)) =
        Real.exp (-((m : ℝ) * uvec a b c i)) := by
    intro i
    rw [← Real.exp_sum]
    congr 1
    have htot : (∑ j : Fin 3, (m : ℝ) * uvec a b c j) = 0 := by
      rw [← Finset.mul_sum, sum_uvec hab, mul_zero]
    have hsa := Finset.sum_erase_add (Finset.univ : Finset (Fin 3))
      (fun j => (m : ℝ) * uvec a b c j) (Finset.mem_univ i)
    simp only [htot] at hsa
    linarith
  rw [hcoe, Matrix.adjugate_diagonal]
  exact congrArg Matrix.diagonal (funext herase)

lemma conj_bconj_apply {a b c : Fin 3} (hab : a ≠ b) (m : ℕ) (g : SL3) (i j : Fin 3) :
    (bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹) i j =
      Real.exp ((m : ℝ) * (uvec a b c i - uvec a b c j)) * g i j := by
  have hexp : Real.exp ((m : ℝ) * uvec a b c i) * Real.exp (-((m : ℝ) * uvec a b c j)) =
      Real.exp ((m : ℝ) * (uvec a b c i - uvec a b c j)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  show toMat (bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹) i j =
    Real.exp ((m : ℝ) * (uvec a b c i - uvec a b c j)) * g i j
  rw [toMat_mul, toMat_mul, toMat_pow_bconj a b c hab m, toMat_inv_pow_bconj a b c hab m]
  rw [Matrix.mul_assoc, diagonal_mul_apply, mul_diagonal_apply,
    mul_comm (g i j) (Real.exp (-((m : ℝ) * uvec a b c j))), ← mul_assoc, hexp]

/-! ## The values of `uvec` and the resulting contraction bounds -/

lemma uvec_a (a b c : Fin 3) : uvec a b c a = -1 := by simp [uvec]

lemma uvec_b {a b : Fin 3} (hab : a ≠ b) (c : Fin 3) : uvec a b c b = 1 := by
  simp [uvec, hab.symm]

lemma uvec_c {a b c : Fin 3} (hac : a ≠ c) (hcb : c ≠ b) : uvec a b c c = 0 := by
  simp [uvec, hac.symm, hcb]

lemma uvec_lt_iff {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) (i j : Fin 3) :
    uvec a b c j < uvec a b c i ↔
      (i = b ∧ j = a) ∨ (i = b ∧ j = c) ∨ (i = c ∧ j = a) := by
  have hA := uvec_a a b c
  have hB := uvec_b hab c
  have hC := uvec_c hac hcb
  constructor
  · intro h
    rcases eq_a_or_b_or_c hab hac hcb i with hia | hib | hic
    · rcases eq_a_or_b_or_c hab hac hcb j with hja | hjb | hjc
      · rw [hia, hja, hA] at h; exact absurd h (lt_irrefl _)
      · rw [hia, hjb, hA, hB] at h; exact absurd h (by norm_num)
      · rw [hia, hjc, hA, hC] at h; exact absurd h (by norm_num)
    · rcases eq_a_or_b_or_c hab hac hcb j with hja | hjb | hjc
      · exact Or.inl ⟨hib, hja⟩
      · rw [hib, hjb, hB] at h; exact absurd h (lt_irrefl _)
      · exact Or.inr (Or.inl ⟨hib, hjc⟩)
    · rcases eq_a_or_b_or_c hab hac hcb j with hja | hjb | hjc
      · exact Or.inr (Or.inr ⟨hic, hja⟩)
      · rw [hic, hjb, hC, hB] at h; exact absurd h (by norm_num)
      · rw [hic, hjc, hC] at h; exact absurd h (lt_irrefl _)
  · rintro (⟨hib, hja⟩ | ⟨hib, hjc⟩ | ⟨hic, hja⟩)
    · rw [hib, hja, hA, hB]; norm_num
    · rw [hib, hjc, hC, hB]; norm_num
    · rw [hic, hja, hA, hC]; norm_num

lemma conj_mem_clBox {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) (m : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) {g : SL3} (hg : g ∈ Lset hab) (hgb : g ∈ clBox δ) :
    bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹ ∈ clBox δ := by
  intro i j
  obtain ⟨haa, h1, h2⟩ := (mem_Lset_iff hab g).mp hg
  rw [conj_bconj_apply hab m g i j]
  by_cases hij : i = j
  · subst hij
    rw [show (m : ℝ) * (uvec a b c i - uvec a b c i) = 0 by ring, Real.exp_zero, one_mul,
      Matrix.one_apply, if_pos rfl]
    have hgii := hgb i i
    rwa [Matrix.one_apply, if_pos rfl] at hgii
  · rw [Matrix.one_apply, if_neg hij, sub_zero, abs_mul]
    by_cases hle : uvec a b c i ≤ uvec a b c j
    · have hfe : |Real.exp ((m : ℝ) * (uvec a b c i - uvec a b c j))| ≤ 1 := by
        rw [abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
        nlinarith [Nat.cast_nonneg (α := ℝ) m]
      calc |Real.exp ((m : ℝ) * (uvec a b c i - uvec a b c j))| * |g i j|
          ≤ 1 * |g i j| := mul_le_mul_of_nonneg_right hfe (abs_nonneg _)
        _ ≤ δ := by
            rw [one_mul]
            have hgij := hgb i j
            rwa [Matrix.one_apply, if_neg hij, sub_zero] at hgij
    · have hgt : uvec a b c j < uvec a b c i := not_le.mp hle
      have hzero : g i j = 0 := by
        rcases (uvec_lt_iff hab hac hcb i j).mp hgt with ⟨hib, hja⟩ | ⟨hib, hjc⟩ | ⟨hic, hja⟩
        · rw [hib, hja]; exact h1 b (Ne.symm hab)
        · rw [hib, hjc]; exact h2 c hcb
        · rw [hic, hja]; exact h1 c (Ne.symm hac)
      rw [hzero, abs_zero, mul_zero]
      exact hδ

lemma fmax_conj_le {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b) (m : ℕ)
    {g : SL3} (hg : g ∈ Lset hab) :
    fmax a b c (bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹) ≤
      Real.exp (-(m : ℝ)) * fmax a b c g := by
  have hb1 : |(bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹) a b| ≤
      Real.exp (-(m : ℝ)) * |g a b| := by
    rw [conj_bconj_apply hab m g a b, uvec_a, uvec_b hab, abs_mul, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    apply Real.exp_le_exp.mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hb2 : |(bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹) a c| ≤
      Real.exp (-(m : ℝ)) * |g a c| := by
    rw [conj_bconj_apply hab m g a c, uvec_a, uvec_c hac hcb, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    rw [show (m : ℝ) * ((-1 : ℝ) - 0) = -(m : ℝ) by ring]
  have hb3 : |(bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹) c b| ≤
      Real.exp (-(m : ℝ)) * |g c b| := by
    rw [conj_bconj_apply hab m g c b, uvec_c hac hcb, uvec_b hab, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    rw [show (m : ℝ) * ((0 : ℝ) - 1) = -(m : ℝ) by ring]
  have hpos : (0 : ℝ) ≤ Real.exp (-(m : ℝ)) := (Real.exp_pos _).le
  simp only [fmax]
  refine max_le (max_le ?_ ?_) ?_
  · calc |(bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹) a b|
        ≤ Real.exp (-(m : ℝ)) * |g a b| := hb1
      _ ≤ Real.exp (-(m : ℝ)) * max (max |g a b| |g a c|) |g c b| :=
          mul_le_mul_of_nonneg_left (le_trans (le_max_left _ _) (le_max_left _ _)) hpos
  · calc |(bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹) a c|
        ≤ Real.exp (-(m : ℝ)) * |g a c| := hb2
      _ ≤ Real.exp (-(m : ℝ)) * max (max |g a b| |g a c|) |g c b| :=
          mul_le_mul_of_nonneg_left (le_trans (le_max_right _ _) (le_max_left _ _)) hpos
  · calc |(bconj a b c ^ m * g * (bconj a b c ^ m)⁻¹) c b|
        ≤ Real.exp (-(m : ℝ)) * |g c b| := hb3
      _ ≤ Real.exp (-(m : ℝ)) * max (max |g a b| |g a c|) |g c b| :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) hpos

end

end Work.EKLNonExc
