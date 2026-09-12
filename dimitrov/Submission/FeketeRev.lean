import Mathlib

noncomputable section

open scoped Real Polynomial Topology BigOperators

namespace Submission.FeketeRev

open Polynomial

/-- Monic complex polynomials of degree exactly `n`. -/
def MonicDeg (n : ℕ) : Set ℂ[X] := {p : ℂ[X] | p.Monic ∧ p.natDegree = n}

/-- The Vandermonde product of `n` points (pairs `j < i < n`). -/
def vdm (x : ℕ → ℂ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, ∏ j ∈ Finset.range i, ‖x j - x i‖

/-- The set of Vandermonde products over `n`-point configurations in `E`. -/
def feketeSet (E : Set ℂ) (n : ℕ) : Set ℝ :=
  {d : ℝ | ∃ x : ℕ → ℂ, (∀ i : ℕ, i < n → x i ∈ E) ∧ d = vdm x n}

/-- **Fekete number.** -/
def feketeNumber (E : Set ℂ) (n : ℕ) : ℝ := sSup (feketeSet E n)

/-- The separation product of point `i` in an `(N+1)`-point configuration:
`∏_{j ≠ i} ‖x_i − x_j‖`. -/
def sep (x : ℕ → ℂ) (N i : ℕ) : ℝ :=
  ∏ j ∈ (Finset.range (N + 1)).erase i, ‖x i - x j‖

/-- The configuration with index `i` removed (shifted down by one). -/
def removeIndex (x : ℕ → ℂ) (i : ℕ) : ℕ → ℂ := fun j => if j < i then x j else x (j + 1)

/-- A Vandermonde product is nonnegative. -/
lemma vdm_nonneg (x : ℕ → ℂ) (n : ℕ) : 0 ≤ vdm x n := by
  unfold vdm
  exact Finset.prod_nonneg (fun i _ => Finset.prod_nonneg (fun j _ => norm_nonneg _))

/-- A separation product is nonnegative. -/
lemma sep_nonneg (x : ℕ → ℂ) (N i : ℕ) : 0 ≤ sep x N i := by
  unfold sep
  exact Finset.prod_nonneg (fun j _ => norm_nonneg _)

/-- `sep` is the norm of the corresponding complex product. -/
lemma sep_eq_norm_prod (x : ℕ → ℂ) (N i : ℕ) :
    sep x N i = ‖∏ j ∈ (Finset.range (N + 1)).erase i, (x i - x j)‖ := by
  unfold sep
  rw [norm_prod]

/-- `vdm = 0` when two points (with indices `b < a`) coincide. -/
lemma vdm_eq_zero_of_lt {x : ℕ → ℂ} {n a b : ℕ} (hb : b < a) (ha : a < n) (hx : x b = x a) :
    vdm x n = 0 := by
  unfold vdm
  refine Finset.prod_eq_zero (Finset.mem_range.mpr ha) ?_
  refine Finset.prod_eq_zero (Finset.mem_range.mpr hb) ?_
  rw [hx, sub_self, norm_zero]

/-- A Vandermonde product of pairwise distinct points is positive. -/
lemma vdm_pos {x : ℕ → ℂ} {n : ℕ} (hdist : ∀ a, a < n → ∀ b, b < a → x b ≠ x a) :
    0 < vdm x n := by
  unfold vdm
  refine Finset.prod_pos ?_
  intro i hi
  refine Finset.prod_pos ?_
  intro j hj
  exact norm_pos_iff.mpr ((sub_ne_zero).2 (hdist i (Finset.mem_range.mp hi) j (Finset.mem_range.mp hj)))

lemma row_split (x : ℕ → ℂ) (i a : ℕ) :
    (∏ b ∈ Finset.range a, ‖x b - x a‖) =
      (∏ b ∈ (Finset.range a).erase i, ‖x b - x a‖) * (if i < a then ‖x i - x a‖ else 1) := by
  by_cases hia : i < a
  · rw [if_pos hia]
    exact (Finset.prod_erase_mul (Finset.range a) (fun b => ‖x b - x a‖)
      (Finset.mem_range.mpr hia)).symm
  · rw [if_neg hia]
    have hnot : i ∉ Finset.range a := by
      intro h
      exact hia (Finset.mem_range.mp h)
    rw [Finset.erase_eq_self.mpr hnot]
    simp

lemma disjoint_range_Ico (i n : ℕ) : Disjoint (Finset.range i) (Finset.Ico (i + 1) n) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  have h1 : a < i := by simpa using (Finset.mem_range.mp ha)
  have h2 : i + 1 ≤ a := (Finset.mem_Ico.mp hb).1
  omega

lemma filter_erase_eq_Ico {N i : ℕ} :
    ((Finset.range (N + 1)).erase i).filter (fun a => i < a) = Finset.Ico (i + 1) (N + 1) := by
  ext a
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨by omega, h2⟩
  · intro h
    exact ⟨⟨by omega, h.2⟩, h.1⟩

lemma erase_eq_range_union_Ico {N i : ℕ} (hi : i < N + 1) :
    (Finset.range (N + 1)).erase i = Finset.range i ∪ Finset.Ico (i + 1) (N + 1) := by
  ext x
  simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
  constructor
  · rintro ⟨hx_ne, hx⟩
    by_cases h : x < i
    · exact Or.inl h
    · exact Or.inr ⟨by omega, hx⟩
  · intro h
    rcases h with h | h
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, h.2⟩

/-- E2: sep splits into below and above parts. -/
lemma sep_split {N i : ℕ} (hi : i < N + 1) (x : ℕ → ℂ) :
    sep x N i =
      (∏ j ∈ Finset.range i, ‖x i - x j‖) *
        ∏ j ∈ Finset.Ico (i + 1) (N + 1), ‖x i - x j‖ := by
  rw [sep, erase_eq_range_union_Ico (N := N) (i := i) hi]
  rw [Finset.prod_union (disjoint_range_Ico i (N + 1))]

/-- range n = range i ∪ Ico i n for i ≤ n. -/
lemma range_eq_range_union_Ico_le {n i : ℕ} (hi : i ≤ n) :
    Finset.range n = Finset.range i ∪ Finset.Ico i n := by
  rw [Finset.range_eq_Ico, Finset.range_eq_Ico]
  exact (Finset.Ico_union_Ico_eq_Ico (a := 0) (b := i) (c := n) (by omega) hi).symm

/-- E1: vdm splits into non-diagonal product and the two "i-terms". -/
lemma vdm_split {N i : ℕ} (hi : i < N + 1) (x : ℕ → ℂ) :
    vdm x (N + 1) =
      ((∏ a ∈ (Finset.range (N + 1)).erase i,
          ∏ b ∈ (Finset.range a).erase i, ‖x b - x a‖) *
        (∏ j ∈ Finset.Ico (i + 1) (N + 1), ‖x i - x j‖)) *
        (∏ b ∈ Finset.range i, ‖x b - x i‖) := by
  calc
    vdm x (N + 1) = ∏ a ∈ Finset.range (N + 1), ∏ b ∈ Finset.range a, ‖x b - x a‖ := rfl
    _ = (∏ a ∈ (Finset.range (N + 1)).erase i,
            ∏ b ∈ Finset.range a, ‖x b - x a‖) * (∏ b ∈ Finset.range i, ‖x b - x i‖) := by
      rw [← Finset.prod_erase_mul (Finset.range (N + 1))
        (fun a => ∏ b ∈ Finset.range a, ‖x b - x a‖) (Finset.mem_range.mpr hi)]
    _ = (∏ a ∈ (Finset.range (N + 1)).erase i,
          ((∏ b ∈ (Finset.range a).erase i, ‖x b - x a‖) *
            (if i < a then ‖x i - x a‖ else 1))) * (∏ b ∈ Finset.range i, ‖x b - x i‖) := by
      congr 1
      exact Finset.prod_congr rfl (fun a ha => row_split x i a)
    _ = ((∏ a ∈ (Finset.range (N + 1)).erase i,
            ∏ b ∈ (Finset.range a).erase i, ‖x b - x a‖) *
          (∏ a ∈ (Finset.range (N + 1)).erase i,
            if i < a then ‖x i - x a‖ else 1)) * (∏ b ∈ Finset.range i, ‖x b - x i‖) := by
      rw [Finset.prod_mul_distrib]
    _ = (∏ a ∈ (Finset.range (N + 1)).erase i,
          ∏ b ∈ (Finset.range a).erase i, ‖x b - x a‖) *
        ((∏ a ∈ (Finset.range (N + 1)).erase i,
            if i < a then ‖x i - x a‖ else 1) * (∏ b ∈ Finset.range i, ‖x b - x i‖)) := by
      rw [mul_assoc]
    _ = (∏ a ∈ (Finset.range (N + 1)).erase i,
          ∏ b ∈ (Finset.range a).erase i, ‖x b - x a‖) *
        ((∏ j ∈ Finset.Ico (i + 1) (N + 1), ‖x i - x j‖) *
          (∏ b ∈ Finset.range i, ‖x b - x i‖)) := by
      have hif : (∏ a ∈ (Finset.range (N + 1)).erase i,
            if i < a then ‖x i - x a‖ else 1) =
          ∏ j ∈ Finset.Ico (i + 1) (N + 1), ‖x i - x j‖ := by
        rw [← Finset.prod_filter (fun a : ℕ => i < a) (fun a : ℕ => ‖x i - x a‖)]
        rw [filter_erase_eq_Ico (N := N) (i := i)]
      rw [hif]
    _ = ((∏ a ∈ (Finset.range (N + 1)).erase i,
          ∏ b ∈ (Finset.range a).erase i, ‖x b - x a‖) *
        (∏ j ∈ Finset.Ico (i + 1) (N + 1), ‖x i - x j‖)) *
        (∏ b ∈ Finset.range i, ‖x b - x i‖) := by
      rw [← mul_assoc]


lemma removeIndex_lt (x : ℕ → ℂ) {i k : ℕ} (hk : k < i) : removeIndex x i k = x k := by
  simp [removeIndex, hk]

lemma removeIndex_ge (x : ℕ → ℂ) {i k : ℕ} (hk : i ≤ k) : removeIndex x i k = x (k + 1) := by
  have h : ¬ k < i := by omega
  simp [removeIndex, h]

lemma erase_range_eq_union {a i : ℕ} (hi : i < a) :
    (Finset.range a).erase i = Finset.range i ∪ Finset.Ico (i + 1) a := by
  have ha : a = (a - 1) + 1 := by omega
  rw [ha]
  exact erase_eq_range_union_Ico (N := a - 1) (i := i) (by omega)


lemma disjoint_range_Ico' (i n : ℕ) : Disjoint (Finset.range i) (Finset.Ico i n) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  have h1 : a < i := by simpa using (Finset.mem_range.mp ha)
  have h2 : i ≤ a := (Finset.mem_Ico.mp hb).1
  omega

/-- auxiliary membership helpers -/
lemma Ico_mem_le {x a b : ℕ} (h : x ∈ Finset.Ico a b) : a ≤ x := (Finset.mem_Ico.mp h).1
lemma Ico_mem_lt {x a b : ℕ} (h : x ∈ Finset.Ico a b) : x < b := (Finset.mem_Ico.mp h).2

/-- E3: the product over pairs avoiding `i` equals the Vandermonde of the
config with index `i` removed. -/
lemma nondiag_eq_vdm_remove {N i : ℕ} (hi : i < N + 1) (x : ℕ → ℂ) :
    (∏ a ∈ (Finset.range (N + 1)).erase i,
        ∏ b ∈ (Finset.range a).erase i, ‖x b - x a‖) = vdm (removeIndex x i) N := by
  classical
  have hiN : i ≤ N := by omega
  have himage : (Finset.Ico i N).image (fun A : ℕ => A + 1) = Finset.Ico (i + 1) (N + 1) := by
    ext A
    constructor
    · intro hA
      rcases Finset.mem_image.mp hA with ⟨B, hB, rfl⟩
      have hB1 : i ≤ B := Ico_mem_le hB
      have hB2 : B < N := Ico_mem_lt hB
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · intro hA
      have hA1 : i + 1 ≤ A := Ico_mem_le hA
      have hA2 : A < N + 1 := Ico_mem_lt hA
      refine Finset.mem_image.mpr ⟨A - 1, ?_, ?_⟩
      · exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      · omega
  let low : ℝ := ∏ a ∈ Finset.range i, ∏ b ∈ Finset.range a, ‖x b - x a‖
  let Q2 : ℝ := ∏ a ∈ Finset.Ico (i + 1) (N + 1), ∏ b ∈ Finset.range i, ‖x b - x a‖
  let Q3 : ℝ := ∏ a ∈ Finset.Ico (i + 1) (N + 1), ∏ b ∈ Finset.Ico (i + 1) a, ‖x b - x a‖
  have hlow : low =
      (∏ A ∈ Finset.range i, ∏ B ∈ Finset.range A,
        ‖removeIndex x i B - removeIndex x i A‖) := by
    dsimp [low]
    apply Finset.prod_congr rfl
    intro a ha
    apply Finset.prod_congr rfl
    intro b hb
    have hb_i : b < i := lt_trans (by simpa using (Finset.mem_range.mp hb))
      (by simpa using (Finset.mem_range.mp ha))
    rw [removeIndex_lt x hb_i]
    rw [removeIndex_lt x (by simpa using (Finset.mem_range.mp ha))]
  have hQ2 : Q2 =
      (∏ A ∈ Finset.Ico i N, ∏ B ∈ Finset.range i, ‖x B - x (A + 1)‖) := by
    dsimp [Q2]
    rw [← himage]
    rw [Finset.prod_image (by
      intro A hA B hB h
      simpa using h)]
  have hQ3 : Q3 =
      (∏ A ∈ Finset.Ico i N, ∏ B ∈ Finset.Ico i A, ‖x (B + 1) - x (A + 1)‖) := by
    dsimp [Q3]
    rw [← himage]
    rw [Finset.prod_image (by
      intro A hA B hB h
      simpa using h)]
    apply Finset.prod_congr rfl
    intro A hA
    -- inner shift: b = B + 1
    apply Finset.prod_bij (fun b hb => b - 1)
    · intro b hb
      have hb1 : i + 1 ≤ b := Ico_mem_le hb
      have hb2 : b < A + 1 := Ico_mem_lt hb
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · intro b hb c hc h
      have hb1 : i + 1 ≤ b := Ico_mem_le hb
      have hc1 : i + 1 ≤ c := Ico_mem_le hc
      omega
    · intro B hB
      have hB1 : i ≤ B := Ico_mem_le hB
      have hB2 : B < A := Ico_mem_lt hB
      refine ⟨B + 1, ?_, ?_⟩
      · exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
      · omega
    · intro b hb
      have hb1 : i + 1 ≤ b := Ico_mem_le hb
      have hb2 : b < A + 1 := Ico_mem_lt hb
      have hbb : b - 1 + 1 = b := by omega
      rw [hbb]
  have hvdm : vdm (removeIndex x i) N = low * (Q2 * Q3) := by
    calc
      vdm (removeIndex x i) N
          = (∏ A ∈ Finset.range i, ∏ B ∈ Finset.range A,
              ‖removeIndex x i B - removeIndex x i A‖) *
            (∏ A ∈ Finset.Ico i N, ∏ B ∈ Finset.range A,
              ‖removeIndex x i B - removeIndex x i A‖) := by
            rw [vdm, range_eq_range_union_Ico_le (n := N) (i := i) hiN]
            rw [Finset.prod_union (disjoint_range_Ico' i N)]
      _ = low * (∏ A ∈ Finset.Ico i N,
            (∏ B ∈ Finset.range i, ‖x B - x (A + 1)‖) *
              (∏ B ∈ Finset.Ico i A, ‖x (B + 1) - x (A + 1)‖)) := by
            rw [← hlow]
            congr 1
            apply Finset.prod_congr rfl
            intro A hA
            have hAi : i ≤ A := Ico_mem_le hA
            have hrem : removeIndex x i A = x (A + 1) := removeIndex_ge x hAi
            calc
              (∏ B ∈ Finset.range A, ‖removeIndex x i B - removeIndex x i A‖)
                  = (∏ B ∈ Finset.range A, ‖removeIndex x i B - x (A + 1)‖) := by
                    rw [hrem]
              _ = (∏ B ∈ Finset.range i, ‖x B - x (A + 1)‖) *
                    (∏ B ∈ Finset.Ico i A, ‖x (B + 1) - x (A + 1)‖) := by
                    rw [range_eq_range_union_Ico_le (n := A) (i := i) hAi]
                    rw [Finset.prod_union (disjoint_range_Ico' i A)]
                    congr 1
                    · apply Finset.prod_congr rfl
                      intro B hB
                      rw [removeIndex_lt x (by simpa using (Finset.mem_range.mp hB))]
                    · apply Finset.prod_congr rfl
                      intro B hB
                      rw [removeIndex_ge x (Ico_mem_le hB)]
      _ = low * (Q2 * Q3) := by
            congr 1
            rw [Finset.prod_mul_distrib]
            rw [← hQ2, ← hQ3]
  have hQ : (∏ a ∈ (Finset.range (N + 1)).erase i,
        ∏ b ∈ (Finset.range a).erase i, ‖x b - x a‖) = low * (Q2 * Q3) := by
    calc
      (∏ a ∈ (Finset.range (N + 1)).erase i,
          ∏ b ∈ (Finset.range a).erase i, ‖x b - x a‖)
          = (∏ a ∈ Finset.range i, ∏ b ∈ (Finset.range a).erase i, ‖x b - x a‖) *
            (∏ a ∈ Finset.Ico (i + 1) (N + 1),
              ∏ b ∈ (Finset.range a).erase i, ‖x b - x a‖) := by
            rw [erase_eq_range_union_Ico (N := N) (i := i) hi]
            rw [Finset.prod_union (disjoint_range_Ico i (N + 1))]
      _ = low *
            (∏ a ∈ Finset.Ico (i + 1) (N + 1),
              ∏ b ∈ (Finset.range a).erase i, ‖x b - x a‖) := by
            dsimp [low]
            congr 1
            apply Finset.prod_congr rfl
            intro a ha
            have hi_a : a < i := by simpa using (Finset.mem_range.mp ha)
            rw [Finset.erase_eq_self.mpr (by
              intro h
              exact (not_lt_of_ge (Nat.le_of_lt hi_a)) (Finset.mem_range.mp h))]
      _ = low *
            (∏ a ∈ Finset.Ico (i + 1) (N + 1),
              (∏ b ∈ Finset.range i, ‖x b - x a‖) *
                (∏ b ∈ Finset.Ico (i + 1) a, ‖x b - x a‖)) := by
            congr 1
            apply Finset.prod_congr rfl
            intro a ha
            have hi_a : i < a := Ico_mem_le ha
            rw [erase_range_eq_union (a := a) (i := i) hi_a]
            rw [Finset.prod_union (disjoint_range_Ico i a)]
      _ = low * (Q2 * Q3) := by
            dsimp [Q2, Q3]
            rw [← Finset.prod_mul_distrib]
  rw [hQ, hvdm]


/-- Final assembly: `vdm_remove`. -/
lemma vdm_remove {N i : ℕ} (hi : i < N + 1) (x : ℕ → ℂ) :
    vdm x (N + 1) = sep x N i * vdm (removeIndex x i) N := by
  let nd : ℝ := ∏ a ∈ (Finset.range (N + 1)).erase i,
        ∏ b ∈ (Finset.range a).erase i, ‖x b - x a‖
  let hiP : ℝ := ∏ j ∈ Finset.Ico (i + 1) (N + 1), ‖x i - x j‖
  let lo : ℝ := ∏ b ∈ Finset.range i, ‖x b - x i‖
  let lo' : ℝ := ∏ j ∈ Finset.range i, ‖x i - x j‖
  have hlowPart : lo = lo' := by
    dsimp [lo, lo']
    apply Finset.prod_congr rfl
    intro b hb
    exact norm_sub_rev (x b) (x i)
  calc
    vdm x (N + 1) = (nd * hiP) * lo := by
      simpa [nd, hiP, lo] using vdm_split (N := N) (i := i) hi x
    _ = nd * (hiP * lo) := by rw [mul_assoc]
    _ = nd * (hiP * lo') := by rw [hlowPart]
    _ = nd * (lo' * hiP) := by rw [mul_comm hiP lo']
    _ = nd * sep x N i := by
      rw [sep_split (N := N) (i := i) hi x]
    _ = vdm (removeIndex x i) N * sep x N i := by
      change (∏ a ∈ (Finset.range (N + 1)).erase i,
          ∏ b ∈ (Finset.range a).erase i, ‖x b - x a‖) * sep x N i =
        vdm (removeIndex x i) N * sep x N i
      rw [nondiag_eq_vdm_remove (N := N) (i := i) hi x]
    _ = sep x N i * vdm (removeIndex x i) N := by rw [mul_comm]


/-- Every member of a `feketeSet` is nonnegative. -/
lemma feketeSet_mem_nonneg {E : Set ℂ} {n : ℕ} {d : ℝ} (hd : d ∈ feketeSet E n) : 0 ≤ d := by
  rcases hd with ⟨y, hy, rfl⟩
  exact vdm_nonneg y n

/-- If every point of an `n`-configuration is bounded in norm by `R`, the
Vandermonde product is bounded (each pair factor is at most `max 1 (2R)`). -/
lemma vdm_le_of_norm_le {x : ℕ → ℂ} {n : ℕ} {R : ℝ}
    (hx : ∀ k : ℕ, k < n → ‖x k‖ ≤ R) :
    vdm x n ≤ (max 1 (2 * R)) ^ (n * n) := by
  let c : ℝ := max 1 (2 * R)
  have hc1 : 1 ≤ c := le_max_left 1 (2 * R)
  have hc0 : 0 ≤ c := le_trans zero_le_one hc1
  have hpair : ∀ a, a < n → ∀ b, b < a → ‖x b - x a‖ ≤ c := by
    intro a ha b hb
    calc
      ‖x b - x a‖ ≤ ‖x b‖ + ‖x a‖ := norm_sub_le _ _
      _ ≤ R + R := add_le_add (hx b (lt_trans hb ha)) (hx a ha)
      _ = 2 * R := by ring
      _ ≤ c := le_max_right 1 (2 * R)
  have hin : ∀ a, a < n → (∏ b ∈ Finset.range a, ‖x b - x a‖) ≤ c ^ n := by
    intro a ha
    calc
      (∏ b ∈ Finset.range a, ‖x b - x a‖) ≤ ∏ b ∈ Finset.range a, c :=
        Finset.prod_le_prod (fun b _ => norm_nonneg _) (fun b hb => hpair a ha b (Finset.mem_range.mp hb))
      _ = c ^ (Finset.range a).card := Finset.prod_const c
      _ = c ^ a := by rw [Finset.card_range]
      _ ≤ c ^ n := pow_le_pow_right₀ hc1 (by omega)
  calc
    vdm x n = ∏ a ∈ Finset.range n, (∏ b ∈ Finset.range a, ‖x b - x a‖) := rfl
    _ ≤ ∏ a ∈ Finset.range n, c ^ n := by
      refine Finset.prod_le_prod ?_ (fun a ha => hin a (Finset.mem_range.mp ha))
      intro a ha
      exact Finset.prod_nonneg (fun b _ => norm_nonneg _)
    _ = (c ^ n) ^ (Finset.range n).card := Finset.prod_const (c ^ n)
    _ = (c ^ n) ^ n := by rw [Finset.card_range]
    _ = c ^ (n * n) := by rw [pow_mul]

/-- Bounded set gives bounded-above `feketeSet`. -/
lemma feketeSet_bddAbove {E : Set ℂ} {n : ℕ} (hE : Bornology.IsBounded E) :
    BddAbove (feketeSet E n) := by
  rcases hE.exists_pos_norm_le with ⟨R, hRpos, hR⟩
  refine ⟨(max 1 (2 * R)) ^ (n * n), ?_⟩
  intro d hd
  rcases hd with ⟨y, hy, rfl⟩
  exact vdm_le_of_norm_le (x := y) (n := n) (R := R) (fun k hk => hR (y k) (hy k hk))

/-- Every `n`-point Vandermonde product of a configuration inside a bounded
set `E` is at most the Fekete number. -/
lemma vdm_le_feketeNumber {E : Set ℂ} {n : ℕ} (hE : Bornology.IsBounded E)
    {y : ℕ → ℂ} (hy : ∀ i : ℕ, i < n → y i ∈ E) : vdm y n ≤ feketeNumber E n := by
  unfold feketeNumber
  exact le_csSup (feketeSet_bddAbove (E := E) (n := n) hE) ⟨y, hy, rfl⟩

/-- A bounded `E` plus a nonempty configuration makes the Fekete number
nonnegative. -/
lemma feketeNumber_nonneg_of_mem {E : Set ℂ} {n : ℕ} (hE : Bornology.IsBounded E)
    {y : ℕ → ℂ} (hy : ∀ i : ℕ, i < n → y i ∈ E) : 0 ≤ feketeNumber E n := by
  exact le_trans (vdm_nonneg y n) (vdm_le_feketeNumber (E := E) (n := n) hE hy)

/-- A monic (hence nonzero) nonconstant polynomial can be bounded on a set
only if the set is bounded. -/
lemma isBounded_of_poly_bound {E : Set ℂ} {p : ℂ[X]} (hp : 1 ≤ p.natDegree)
    {M : ℝ} (hb : ∀ X ∈ E, ‖p.eval X‖ ≤ M) : Bornology.IsBounded E := by
  have hp0 : 0 < p.natDegree := by omega
  have hdeg : 0 < p.degree := (Polynomial.natDegree_pos_iff_degree_pos).1 hp0
  have hEsub : E ⊆ (fun z : ℂ => p.eval z) ⁻¹' Metric.closedBall (0 : ℂ) M := by
    intro X hX
    simpa [Metric.mem_closedBall, dist_eq_norm] using hb X hX
  have hpre : IsCompact ((fun z : ℂ => p.eval z) ⁻¹' Metric.closedBall (0 : ℂ) M) :=
    (p.isProperMap_eval hdeg).isCompact_preimage (ProperSpace.isCompact_closedBall (0 : ℂ) M)
  exact hpre.isBounded.subset hEsub

/-- Lagrange interpolation identity for the leading coefficient `1` of a
monic degree-`N` polynomial at `N+1` distinct nodes. -/
lemma lagrange_sum_one {N : ℕ} {p : ℂ[X]} (hpmonic : p.Monic) (hpdeg : p.natDegree = N)
    {x : ℕ → ℂ} (hvs : Set.InjOn x (↑(Finset.range (N + 1)))) :
    (1 : ℂ) = ∑ i ∈ Finset.range (N + 1),
      p.eval (x i) / ∏ j ∈ (Finset.range (N + 1)).erase i, (x i - x j) := by
  have hpne : p ≠ 0 := hpmonic.ne_zero
  have hpdeg' : p.degree = (N : WithBot ℕ) := by
    rw [Polynomial.degree_eq_natDegree hpne, hpdeg]
  have hcard : (↑(Finset.range (N + 1)).card : WithBot ℕ) = p.degree + 1 := by
    simp [hpdeg']
  have hlc := Lagrange.leadingCoeff_eq_sum (s := Finset.range (N + 1)) (v := x) hvs (P := p) hcard
  calc
    (1 : ℂ) = p.leadingCoeff := hpmonic.leadingCoeff.symm
    _ = ∑ i ∈ Finset.range (N + 1),
        p.eval (x i) / ∏ j ∈ (Finset.range (N + 1)).erase i, (x i - x j) := hlc

/-- **Reverse finitary Fekete comparison.** -/
lemma vdm_le_of_monic_bound {E : Set ℂ} {N : ℕ} (hN : 1 ≤ N) {p : ℂ[X]}
    (hpmonic : p.Monic) (hpdeg : p.natDegree = N) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ X ∈ E, ‖p.eval X‖ ≤ M) {x : ℕ → ℂ}
    (hx : ∀ i : ℕ, i < N + 1 → x i ∈ E) :
    vdm x (N + 1) ≤ (N + 1 : ℝ) * M * feketeNumber E N := by
  classical
  have hp1 : 1 ≤ p.natDegree := by rw [hpdeg]; exact hN
  have hEb : Bornology.IsBounded E := isBounded_of_poly_bound (p := p) (hp := hp1) (M := M) hb
  have hxN : ∀ i : ℕ, i < N → x i ∈ E := fun i hi => hx i (by omega)
  have hf0 : 0 ≤ feketeNumber E N :=
    feketeNumber_nonneg_of_mem (E := E) (n := N) hEb hxN
  by_cases hcase : ∃ a : ℕ, a < N + 1 ∧ ∃ b : ℕ, b < a ∧ x b = x a
  · -- Case A: two points coincide
    rcases hcase with ⟨a, ha⟩
    rcases ha with ⟨ha', hb⟩
    rcases hb with ⟨b, hab, hxab⟩
    have hvdm0 : vdm x (N + 1) = 0 :=
      vdm_eq_zero_of_lt (x := x) (n := N + 1) (a := a) (b := b) hab ha' hxab
    have hN0 : 0 ≤ (N + 1 : ℝ) := by positivity
    have hpos : 0 ≤ ((N + 1 : ℝ) * M) * feketeNumber E N :=
      mul_nonneg (mul_nonneg hN0 hM) hf0
    rw [hvdm0]
    exact hpos
  · -- Case B: all points pairwise distinct
    have hdist : ∀ a : ℕ, a < N + 1 → ∀ b : ℕ, b < a → x b ≠ x a := by
      intro a ha b hb h
      exact hcase ⟨a, ha, b, hb, h⟩
    have hdistfull : ∀ a : ℕ, a < N + 1 → ∀ b : ℕ, b < N + 1 → a ≠ b → x a ≠ x b := by
      intro a ha b hb hne
      by_cases hab : a < b
      · exact hdist b hb a hab
      · have hba : b < a := lt_of_le_of_ne (le_of_not_gt hab) (Ne.symm hne)
        exact (hdist a ha b hba).symm
    have hxInj : Set.InjOn x (↑(Finset.range (N + 1))) := by
      intro a ha b hb h
      have ha' : a < N + 1 := by simpa using (Finset.mem_coe.mp ha)
      have hb' : b < N + 1 := by simpa using (Finset.mem_coe.mp hb)
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact (hdistfull a ha' b hb' (ne_of_lt hlt)) h
      · exact (hdistfull b hb' a ha' (ne_of_lt hgt)) h.symm
    have hvdm_pos : 0 < vdm x (N + 1) := vdm_pos (x := x) (n := N + 1) hdist
    have hlc := lagrange_sum_one (N := N) (p := p) hpmonic hpdeg (x := x) hxInj
    -- norm form of the Lagrange identity
    have h1 : (1 : ℝ) ≤
        ∑ i ∈ Finset.range (N + 1), ‖p.eval (x i)‖ / sep x N i := by
      have hnorm := congrArg (fun z : ℂ => ‖z‖) hlc
      calc
        (1 : ℝ) = ‖(1 : ℂ)‖ := by norm_num
        _ = ‖(∑ i ∈ Finset.range (N + 1),
            p.eval (x i) / ∏ j ∈ (Finset.range (N + 1)).erase i, (x i - x j))‖ := hnorm
        _ ≤ ∑ i ∈ Finset.range (N + 1),
            ‖p.eval (x i) / ∏ j ∈ (Finset.range (N + 1)).erase i, (x i - x j)‖ := by
            exact norm_sum_le _ _
        _ = ∑ i ∈ Finset.range (N + 1), ‖p.eval (x i)‖ / sep x N i := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [norm_div]
            rw [← sep_eq_norm_prod x N i]
    let w : ℕ → ℝ := fun i => vdm (removeIndex x i) N
    have hwle : ∀ i, i ∈ Finset.range (N + 1) → w i ≤ feketeNumber E N := by
      intro i hi
      dsimp [w]
      exact vdm_le_feketeNumber (E := E) (n := N) hEb (y := removeIndex x i)
        (fun k hk => by
          by_cases hki : k < i
          · rw [removeIndex_lt x hki]
            exact hx k (by omega)
          · have hik : i ≤ k := by omega
            rw [removeIndex_ge x hik]
            exact hx (k + 1) (by omega))
    have hstep : ∀ i, i ∈ Finset.range (N + 1) →
        (‖p.eval (x i)‖ / sep x N i) * vdm x (N + 1) ≤ M * w i := by
      intro i hi
      have hi' : i < N + 1 := by simpa using hi
      have hsep_pos : 0 < sep x N i := by
        unfold sep
        exact Finset.prod_pos (fun j hj => by
          rcases Finset.mem_erase.mp hj with ⟨hji, hjn⟩
          have hj' : j < N + 1 := by simpa using hjn
          have hne : x i ≠ x j := hdistfull i hi' j hj' (Ne.symm hji)
          exact norm_pos_iff.mpr (sub_ne_zero.mpr hne))
      have hrem_i : vdm x (N + 1) = sep x N i * w i := by
        dsimp [w]
        exact vdm_remove (N := N) (i := i) hi' x
      have hterm : (‖p.eval (x i)‖ / sep x N i) * vdm x (N + 1) = ‖p.eval (x i)‖ * w i := by
        calc
          (‖p.eval (x i)‖ / sep x N i) * vdm x (N + 1)
              = (‖p.eval (x i)‖ / sep x N i) * (sep x N i * w i) := by rw [hrem_i]
          _ = ‖p.eval (x i)‖ * w i := by
              field_simp [ne_of_gt hsep_pos]
      have hMbound : ‖p.eval (x i)‖ ≤ M := hb (x i) (hx i hi')
      have hw0 : 0 ≤ w i := by
        dsimp [w]
        exact vdm_nonneg (removeIndex x i) N
      calc
        (‖p.eval (x i)‖ / sep x N i) * vdm x (N + 1) = ‖p.eval (x i)‖ * w i := hterm
        _ ≤ M * w i := mul_le_mul_of_nonneg_right hMbound hw0
    have h1mul : vdm x (N + 1) ≤
        (∑ i ∈ Finset.range (N + 1), ‖p.eval (x i)‖ / sep x N i) * vdm x (N + 1) := by
      simpa using (mul_le_mul_of_nonneg_right h1 (le_of_lt hvdm_pos))
    have hsumstep :
        (∑ i ∈ Finset.range (N + 1), ‖p.eval (x i)‖ / sep x N i) * vdm x (N + 1) ≤
          ∑ i ∈ Finset.range (N + 1), M * w i := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum (fun i hi => hstep i hi)
    have hsumw : (∑ i ∈ Finset.range (N + 1), w i) ≤ (N + 1 : ℝ) * feketeNumber E N := by
      have hcard' : ((Finset.range (N + 1)).card : ℝ) = (N + 1 : ℝ) := by simp
      calc
        (∑ i ∈ Finset.range (N + 1), w i)
            ≤ ∑ i ∈ Finset.range (N + 1), feketeNumber E N :=
              Finset.sum_le_sum (fun i hi => hwle i hi)
        _ = ((Finset.range (N + 1)).card : ℝ) * feketeNumber E N := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ = (N + 1 : ℝ) * feketeNumber E N := by rw [hcard']
    calc
      vdm x (N + 1)
          ≤ (∑ i ∈ Finset.range (N + 1), ‖p.eval (x i)‖ / sep x N i) * vdm x (N + 1) := h1mul
      _ ≤ ∑ i ∈ Finset.range (N + 1), M * w i := hsumstep
      _ = M * (∑ i ∈ Finset.range (N + 1), w i) := by rw [← Finset.mul_sum]
      _ ≤ M * ((N + 1 : ℝ) * feketeNumber E N) := mul_le_mul_of_nonneg_left hsumw hM
      _ = (N + 1 : ℝ) * M * feketeNumber E N := by ring

end Submission.FeketeRev

end
