import Mathlib
import Submission.Work.Holonomy3.seeding_defs

/-!
# The block sizes are within `2` of the ideal values (`§Seeding`, display `(seed sum est)`)

`blockIdx m γ j` is the index of the block `[γ_p/m, γ_{p+1}/m)` containing `j/d`.  This module
proves `card_blockIdx_close`: the number of ranks `j : Fin d` in block `p` differs from
`d·(γ_{p+1} - γ_p)/m` by at most `2` (in fact by at most `1`), which is the elementary lattice-point
count underlying the paper's seeding estimates.
-/

namespace Work.Holonomy3

open scoped BigOperators

namespace CBC

/-- A downward closed finite set of naturals is an initial segment. -/
lemma downward_eq_range {S : Finset ℕ} (h : ∀ a ∈ S, ∀ b, b ≤ a → b ∈ S) :
    S = Finset.range S.card := by
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    rw [Finset.mem_range]
    by_contra hlt
    push Not at hlt
    have hsub : Finset.range (a + 1) ⊆ S := by
      intro b hb
      rw [Finset.mem_range] at hb
      exact h a ha b (by omega)
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    omega
  · rw [Finset.card_range]

/-- A downward closed finset of `Fin n` is determined by its cardinality. -/
lemma downward_eq_filter {n : ℕ} (T : Finset (Fin n))
    (h : ∀ a ∈ T, ∀ b : Fin n, b ≤ a → b ∈ T) :
    T = Finset.univ.filter (fun k : Fin n => k.1 < T.card) := by
  have hcard : (T.image Fin.val).card = T.card :=
    Finset.card_image_of_injective _ Fin.val_injective
  have himg : T.image Fin.val = Finset.range (T.image Fin.val).card := by
    apply downward_eq_range
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    intro b hb
    refine Finset.mem_image.mpr ⟨⟨b, ?_⟩, h k hk ⟨b, ?_⟩ ?_, rfl⟩
    · exact lt_of_le_of_lt hb k.2
    · exact lt_of_le_of_lt hb k.2
    · simp only [Fin.le_iff_val_le_val]; exact hb
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hcard, ← Finset.mem_range, ← himg]
  exact ⟨fun hk => Finset.mem_image.mpr ⟨k, hk, rfl⟩,
    fun hk => by obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp hk; rwa [Fin.ext hae] at ha⟩

/-- The number of `k : Fin n` with `k < s` is `s` (for `s ≤ n`). -/
lemma card_filter_val_lt {n s : ℕ} (hs : s ≤ n) :
    (Finset.univ.filter (fun k : Fin n => k.1 < s)).card = s := by
  have himg : Finset.univ.filter (fun k : Fin n => k.1 < s)
      = (Finset.univ : Finset (Fin s)).image (Fin.castLE hs) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hk
      exact ⟨⟨k.1, hk⟩, by ext; simp [Fin.castLE]⟩
    · rintro ⟨i, -, rfl⟩
      simp [Fin.castLE]
  rw [himg, Finset.card_image_of_injective _ (Fin.castLE_injective hs), Finset.card_univ,
    Fintype.card_fin]

/-- The number of `j : Fin d` with `A ≤ j < B` is `B - A` (for `A ≤ B ≤ d`). -/
lemma card_filter_val_between {d A B : ℕ} (hAB : A ≤ B) (hBd : B ≤ d) :
    (Finset.univ.filter (fun j : Fin d => A ≤ j.1 ∧ j.1 < B)).card = B - A := by
  rw [← Finset.card_range (B - A)]
  refine Finset.card_bij
    (fun j (_ : j ∈ Finset.univ.filter (fun j : Fin d => A ≤ j.1 ∧ j.1 < B)) => j.1 - A)
    ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    simp only [Finset.mem_range]
    omega
  · intro j₁ h₁ j₂ h₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    have e₁ : j₁.1 = (j₁.1 - A) + A := (Nat.sub_add_cancel h₁.1).symm
    have e₂ : j₂.1 = (j₂.1 - A) + A := (Nat.sub_add_cancel h₂.1).symm
    ext
    rw [e₁, e₂, heq]
  · intro b hb
    simp only [Finset.mem_range] at hb
    refine ⟨⟨A + b, by omega⟩, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    · show (A + b) - A = b
      omega

/-- **Lattice point count.**  For `0 ≤ a ≤ b ≤ 1` the fraction of ranks `j : Fin d` with
`j/d ∈ [a,b)` is `(b-a)` up to `2/d`. -/
lemma count_div_close (d : ℕ) (hd : 0 < d) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    |(((Finset.univ.filter (fun j : Fin d => a ≤ (j:ℝ)/d ∧ (j:ℝ)/d < b)).card : ℝ) / d
       - (b - a))| ≤ 2 / d := by
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have hdne : (d:ℝ) ≠ 0 := ne_of_gt hdR
  have hb0 : 0 ≤ b := le_trans ha hab
  set A : ℕ := ⌈a * d⌉₊ with hA
  set B : ℕ := ⌈b * d⌉₊ with hB
  have hAB : A ≤ B := by
    rw [hA, hB]
    exact Nat.ceil_mono (mul_le_mul_of_nonneg_right hab hdR.le)
  have hBd : B ≤ d := by
    rw [hB]
    refine Nat.ceil_le.mpr ?_
    calc b * d ≤ 1 * d := mul_le_mul_of_nonneg_right hb1 hdR.le
      _ = d := one_mul _
  have hset : (Finset.univ.filter (fun j : Fin d => a ≤ (j:ℝ)/d ∧ (j:ℝ)/d < b))
      = (Finset.univ.filter (fun j : Fin d => A ≤ j.1 ∧ j.1 < B)) := by
    apply Finset.filter_congr
    intro j _
    constructor
    · rintro ⟨h1, h2⟩
      rw [le_div_iff₀ hdR] at h1
      rw [div_lt_iff₀ hdR] at h2
      exact ⟨by rw [hA]; exact Nat.ceil_le.mpr h1, by rw [hB]; exact Nat.lt_ceil.mpr h2⟩
    · rintro ⟨h1, h2⟩
      rw [hA] at h1
      rw [hB] at h2
      exact ⟨by rw [le_div_iff₀ hdR]; exact Nat.ceil_le.mp h1,
             by rw [div_lt_iff₀ hdR]; exact Nat.lt_ceil.mp h2⟩
  rw [hset, card_filter_val_between hAB hBd]
  have hB1 : 0 ≤ (B:ℝ) - b * d := by
    rw [sub_nonneg, hB]; exact Nat.le_ceil (b * d)
  have hB2 : (B:ℝ) - b * d < 1 := by
    have h := Nat.ceil_lt_add_one (mul_nonneg hb0 hdR.le)
    rw [← hB] at h
    linarith
  have hA1 : a * d - (A:ℝ) ≤ 0 := by
    rw [sub_nonpos, hA]; exact Nat.le_ceil (a * d)
  have hA2 : -1 < a * d - (A:ℝ) := by
    have h := Nat.ceil_lt_add_one (mul_nonneg ha hdR.le)
    rw [← hA] at h
    linarith
  have hsum : |((B:ℝ) - A) - (b * d - a * d)| < 1 := by
    have he : ((B:ℝ) - A) - (b * d - a * d) = ((B:ℝ) - b * d) + (a * d - A) := by ring
    rw [he, abs_lt]
    constructor <;> linarith
  have habd : (b - a) * d = b * d - a * d := by ring
  have hgoal : ((B:ℝ) - A) / d - (b - a) = (((B:ℝ) - A) - (b - a) * d) / d := by
    conv_lhs => rw [← mul_div_cancel_right₀ (b - a) hdne]
    rw [← sub_div]
  rw [Nat.cast_sub hAB]
  calc |((B:ℝ) - A) / d - (b - a)| = |(((B:ℝ) - A) - (b - a) * d) / d| := by rw [hgoal]
    _ = |((B:ℝ) - A) - (b - a) * d| / d := by rw [abs_div, abs_of_pos hdR]
    _ = |((B:ℝ) - A) - (b * d - a * d)| / d := by rw [habd]
    _ ≤ 1 / d := by
        rw [div_le_div_iff_of_pos_right hdR]; exact le_of_lt hsum
    _ ≤ 2 / d := div_le_div_of_nonneg_right (by norm_num) hdR.le

/-- **Characterisation of the block index**: `blockIdx m γ j = p` exactly when
`γ_p/m ≤ j/d < γ_{p+1}/m`. -/
lemma blockIdx_iff {l d : ℕ} (m : ℕ) (hm : 0 < m) (hd : 0 < d)
    (γ : Fin (l + 2) → ℝ) (hγ0 : γ 0 = 0) (hγlast : γ (Fin.last (l + 1)) = m)
    (hmono : StrictMono γ) (j : Fin d) (p : Fin (l + 1)) :
    (blockIdx m γ j = p) ↔
      (γ p.castSucc / (m : ℝ) ≤ (j : ℝ) / d ∧ (j : ℝ) / d < γ p.succ / (m : ℝ)) := by
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  set T : Finset (Fin (l+1)) :=
    Finset.univ.filter (fun k : Fin (l+1) => γ k.castSucc / (m:ℝ) ≤ (j:ℝ)/d) with hT
  have hval : (blockIdx m γ j).val = T.card - 1 := by rw [hT]; rfl
  have hTmem : ∀ k : Fin (l+1), k ∈ T ↔ γ k.castSucc / (m:ℝ) ≤ (j:ℝ)/d := by
    intro k; rw [hT]; simp
  have hdown : ∀ a ∈ T, ∀ b : Fin (l+1), b ≤ a → b ∈ T := by
    intro a ha b hb
    rw [hTmem] at ha ⊢
    refine le_trans ?_ ha
    apply div_le_div_of_nonneg_right _ hmR.le
    apply hmono.monotone
    rwa [Fin.castSucc_le_castSucc_iff]
  have hTeq : T = Finset.univ.filter (fun k : Fin (l+1) => k.1 < T.card) :=
    downward_eq_filter T hdown
  constructor
  · intro hp
    have hTcard : T.card = p.1 + 1 := by
      have hv := congrArg Fin.val hp
      rw [hval] at hv
      have h0 : 0 ∈ T := by
        rw [hTmem]
        have hcc : (0 : Fin (l+1)).castSucc = (0 : Fin (l+2)) := by ext; simp
        rw [hcc, hγ0]
        simp only [zero_div]
        exact div_nonneg (by positivity : (0:ℝ) ≤ (j:ℝ)) (by positivity : (0:ℝ) ≤ d)
      have hpos : 1 ≤ T.card := Finset.card_pos.mpr ⟨0, h0⟩
      omega
    have hTeq' : ∀ k : Fin (l+1), k ∈ T ↔ k.1 ≤ p.1 := by
      intro k
      rw [hTeq]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hTcard]
      omega
    constructor
    · exact (hTmem p).mp ((hTeq' p).mpr le_rfl)
    · by_contra hbad
      push Not at hbad
      by_cases hlt : p.1 + 1 < l + 1
      · have hk : (⟨p.1+1, hlt⟩ : Fin (l+1)) ∉ T := by
          intro hmem
          rw [hTeq'] at hmem
          simp only [Fin.val_mk] at hmem
          omega
        rw [hTmem] at hk
        have hsucc : p.succ = (⟨p.1+1, hlt⟩ : Fin (l+1)).castSucc := by
          ext; simp [Fin.val_succ]
        rw [hsucc] at hbad
        exact hk hbad
      · have hpval : p.1 = l := by have := p.2; omega
        have hlast : p.succ = Fin.last (l+1) := by
          ext
          simp [Fin.val_succ, Fin.val_last, hpval]
        rw [hlast, hγlast] at hbad
        have hjlt : ((j.1 : ℕ) : ℝ) < (d:ℝ) := by exact_mod_cast j.2
        have hj1 : (j:ℝ)/(d:ℝ) < 1 := by
          rw [div_lt_one (by exact_mod_cast hd)]
          exact hjlt
        have hmdiv : (m:ℝ)/(m:ℝ) = 1 := div_self (ne_of_gt hmR)
        linarith
  · rintro ⟨h1, h2⟩
    have hTeq' : ∀ k : Fin (l+1), k ∈ T ↔ k.1 ≤ p.1 := by
      intro k
      rw [hTmem]
      constructor
      · intro hk
        by_contra hc
        push Not at hc
        have hle : p.succ ≤ k.castSucc := by
          rw [Fin.le_iff_val_le_val]
          simp only [Fin.val_succ, Fin.val_castSucc]
          omega
        have hmon := hmono.monotone hle
        have hdiv2 : γ p.succ / (m:ℝ) ≤ γ k.castSucc / (m:ℝ) :=
          div_le_div_of_nonneg_right hmon hmR.le
        linarith
      · intro hk
        have hle : k.castSucc ≤ p.castSucc := by
          rw [Fin.castSucc_le_castSucc_iff, Fin.le_iff_val_le_val]
          exact hk
        have hmon := hmono.monotone hle
        have hdiv2 : γ k.castSucc / (m:ℝ) ≤ γ p.castSucc / (m:ℝ) :=
          div_le_div_of_nonneg_right hmon hmR.le
        linarith
    have hTcard : T.card = p.1 + 1 := by
      have heq : T = Finset.univ.filter (fun k : Fin (l+1) => k.1 < p.1 + 1) := by
        ext k
        rw [hTeq']
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [heq]
      exact card_filter_val_lt (n := l + 1) (s := p.1 + 1) (by omega)
    have hvv : (blockIdx m γ j).val = p.1 := by
      rw [hval, hTcard]
      omega
    exact Fin.ext hvv

end CBC

theorem card_blockIdx_close {l d : ℕ} (m : ℕ) (hm : 0 < m) (hd : 0 < d)
    (γ : Fin (l + 2) → ℝ) (hγ0 : γ 0 = 0) (hγlast : γ (Fin.last (l + 1)) = m)
    (hmono : StrictMono γ) (p : Fin (l + 1)) :
    |(((Finset.univ.filter (fun j : Fin d => blockIdx m γ j = p)).card : ℝ) / d
       - (γ p.succ - γ p.castSucc) / m)| ≤ 2 / d := by
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  set a : ℝ := γ p.castSucc / (m:ℝ) with ha
  set b : ℝ := γ p.succ / (m:ℝ) with hb
  have hset : (Finset.univ.filter (fun j : Fin d => blockIdx m γ j = p))
      = (Finset.univ.filter (fun j : Fin d => a ≤ (j:ℝ)/d ∧ (j:ℝ)/d < b)) := by
    apply Finset.filter_congr
    intro j _
    rw [CBC.blockIdx_iff m hm hd γ hγ0 hγlast hmono j p, ha, hb]
  rw [hset]
  have htarget : (γ p.succ - γ p.castSucc) / (m:ℝ) = b - a := by
    rw [ha, hb, sub_div]
  rw [htarget]
  have ha0 : 0 ≤ a := by
    rw [ha]
    refine div_nonneg ?_ hmR.le
    have h := hmono.monotone (Fin.zero_le p.castSucc)
    rwa [hγ0] at h
  have hab : a ≤ b := by
    rw [ha, hb]
    refine div_le_div_of_nonneg_right ?_ hmR.le
    apply hmono.monotone
    rw [Fin.le_iff_val_le_val, Fin.val_succ, Fin.val_castSucc]
    omega
  have hb1 : b ≤ 1 := by
    rw [hb]
    have hle : γ p.succ ≤ (m:ℝ) := by
      rw [← hγlast]
      apply hmono.monotone
      rw [Fin.le_iff_val_le_val]
      simp only [Fin.val_succ, Fin.val_last]
      omega
    calc γ p.succ / (m:ℝ) ≤ (m:ℝ) / (m:ℝ) := div_le_div_of_nonneg_right hle hmR.le
      _ = 1 := div_self (ne_of_gt hmR)
  exact CBC.count_div_close d hd ha0 hab hb1

end Work.Holonomy3
