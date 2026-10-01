import Mathlib
import Submission.Work.LinnikAreas.A7.Defs

/-!
# A7 — the "grid sum" bound of the Linnik assembly

We prove the finite combinatorial inequality `Work.A7.grid_sum_bound`, which is the
Abel-summation step used in the area-7 assembly: a sum of `C (g a)` over the box
`{a ∈ A | g a ≤ Lam 0}` is dominated by the `L`-contribution plus a "staircase"
majorant built from the counting bounds `N0`.

The proof splits the range `(lamS, Lam 0]` into the bands `(Lam (j+1), Lam j]` and
uses Abel summation on the cumulative counts `#{a | g a ≤ Lam j} ≤ N0 j`.
-/

namespace Work.A7

/-- The "staircase" level sequence: `Vf Lam s lamS i = Lam i` for `i ≤ s`, and `lamS`
for `i > s`. -/
def Vf (Lam : ℕ → ℝ) (s : ℕ) (lamS : ℝ) (i : ℕ) : ℝ := if i ≤ s then Lam i else lamS

lemma Vf_of_le (Lam : ℕ → ℝ) (s : ℕ) (lamS : ℝ) {i : ℕ} (h : i ≤ s) :
    Vf Lam s lamS i = Lam i := by simp [Vf, h]

lemma Vf_of_gt (Lam : ℕ → ℝ) (s : ℕ) (lamS : ℝ) {i : ℕ} (h : s < i) :
    Vf Lam s lamS i = lamS := by simp [Vf, not_le.mpr h]

/-- Abel summation (summation by parts) in the form used below. -/
lemma abel_identity (W u : ℕ → ℝ) (s : ℕ) (hW0 : W 0 = 0) :
    ∑ i ∈ Finset.range (s+1), (W (i+1) - W i) * u i
      = W (s+1) * u s + ∑ i ∈ Finset.range s, W (i+1) * (u i - u (i+1)) := by
  induction s with
  | zero => simp [hW0]
  | succ s ih => rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]; ring

/-- Pointwise "staircase" bound.  If `C` is non-increasing with `C (Lam 0) = 0` and
`lamS ≤ x ≤ Lam 0`, then `C x` is dominated by the telescoped indicator sum built from the
levels `Vf Lam s lamS i`. -/
lemma level_pointwise (Lam : ℕ → ℝ) (C : ℝ → ℝ) (s : ℕ) (lamS : ℝ)
    (hmono : ∀ x y : ℝ, x ≤ y → C y ≤ C x)
    (hC0 : C (Lam 0) = 0)
    (hLam_mono : ∀ i j, i ≤ j → j ≤ s → Lam j ≤ Lam i)
    (x : ℝ) (hx0 : x ≤ Lam 0) (hxs : lamS ≤ x) :
    C x ≤ ∑ i ∈ Finset.range (s+1),
      (C (Vf Lam s lamS (i+1)) - C (Vf Lam s lamS i)) * (if x ≤ Vf Lam s lamS i then 1 else 0) := by
  set Sf : Finset ℕ := (Finset.range (s+1)).filter (fun i => x ≤ Vf Lam s lamS i) with hSfdef
  have hSf_ne : Sf.Nonempty := by
    rw [hSfdef]
    exact ⟨0, by simp [Vf_of_le Lam s lamS (Nat.zero_le s), hx0]⟩
  set k : ℕ := Sf.max' hSf_ne with hkdef
  have hk_mem : k ∈ Sf := by rw [hkdef]; exact Finset.max'_mem _ _
  have hk_le : k ≤ s := by
    rw [hSfdef] at hk_mem
    have h1 := (Finset.mem_filter.mp hk_mem).1
    simp only [Finset.mem_range] at h1; omega
  have hkP : x ≤ Vf Lam s lamS k := by
    rw [hSfdef] at hk_mem; exact (Finset.mem_filter.mp hk_mem).2
  have hk_max : ∀ i, i ≤ s → x ≤ Vf Lam s lamS i → i ≤ k := by
    intro i his hxi
    have : i ∈ Sf := by
      rw [hSfdef]; simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hxi⟩
    rw [hkdef]; exact Finset.le_max' _ _ this
  have hkey : Vf Lam s lamS (k+1) ≤ x := by
    by_cases hks : k + 1 ≤ s
    · rw [Vf_of_le Lam s lamS hks]
      by_contra hcon
      rw [not_le] at hcon
      have hle : x ≤ Vf Lam s lamS (k+1) := by
        rw [Vf_of_le Lam s lamS hks]; exact le_of_lt hcon
      have := hk_max (k+1) hks hle
      omega
    · have hv : Vf Lam s lamS (k+1) = lamS := Vf_of_gt Lam s lamS (by omega)
      rw [hv]; exact hxs
  have hzero : ∀ i ∈ Finset.range (s+1), i ∉ Finset.range (k+1) →
      (C (Vf Lam s lamS (i+1)) - C (Vf Lam s lamS i)) * (if x ≤ Vf Lam s lamS i then 1 else 0) = 0 := by
    intro i hi hni
    have his : i ≤ s := by simp only [Finset.mem_range] at hi; omega
    have hxV : ¬ (x ≤ Vf Lam s lamS i) := by
      intro hxi; have := hk_max i his hxi; simp only [Finset.mem_range, not_lt] at hni; omega
    rw [if_neg hxV, mul_zero]
  have hsub : Finset.range (k+1) ⊆ Finset.range (s+1) := by
    intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
  have hstep1 : ∑ i ∈ Finset.range (s+1),
      (C (Vf Lam s lamS (i+1)) - C (Vf Lam s lamS i)) * (if x ≤ Vf Lam s lamS i then 1 else 0)
      = ∑ i ∈ Finset.range (k+1),
      (C (Vf Lam s lamS (i+1)) - C (Vf Lam s lamS i)) * (if x ≤ Vf Lam s lamS i then 1 else 0) :=
    (Finset.sum_subset hsub hzero).symm
  have hstep2 : ∑ i ∈ Finset.range (k+1),
      (C (Vf Lam s lamS (i+1)) - C (Vf Lam s lamS i)) * (if x ≤ Vf Lam s lamS i then 1 else 0)
      = ∑ i ∈ Finset.range (k+1),
      (C (Vf Lam s lamS (i+1)) - C (Vf Lam s lamS i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hik : i ≤ k := by simp only [Finset.mem_range] at hi; omega
    have his : i ≤ s := by omega
    have hxi : x ≤ Vf Lam s lamS i := by
      rw [Vf_of_le Lam s lamS his]
      calc x ≤ Lam k := by rw [← Vf_of_le Lam s lamS hk_le]; exact hkP
        _ ≤ Lam i := hLam_mono i k hik hk_le
    rw [if_pos hxi, mul_one]
  have hstep3 : ∑ i ∈ Finset.range (k+1),
      (C (Vf Lam s lamS (i+1)) - C (Vf Lam s lamS i)) = C (Vf Lam s lamS (k+1)) := by
    rw [Finset.sum_range_sub (fun i => C (Vf Lam s lamS i))]
    have h0 : C (Vf Lam s lamS 0) = 0 := by rw [Vf_of_le Lam s lamS (Nat.zero_le s), hC0]
    rw [h0, sub_zero]
  rw [hstep1, hstep2, hstep3]
  exact hmono _ _ hkey

theorem grid_sum_bound {α : Type*} [DecidableEq α] (A L : Finset α) (g : α → ℝ)
    (Lam : ℕ → ℝ) (C : ℝ → ℝ) (N0 : ℕ → ℕ) (s : ℕ) (lamS : ℝ)
    (hLA : L ⊆ A)
    (hLg : ∀ a ∈ L, g a < lamS)
    (hA : ∀ a ∈ A, g a ≤ Lam 0 → lamS ≤ g a ∨ a ∈ L)
    (hLamS : lamS ≤ Lam s)
    (hdec : ∀ j, j < s → Lam (j+1) ≤ Lam j)
    (hmono : ∀ x y : ℝ, x ≤ y → C y ≤ C x)
    (hC0 : C (Lam 0) = 0)
    (hcount : ∀ j, j ≤ s → ((A.filter (fun a => g a ≤ Lam j)).card : ℝ) ≤ (N0 j : ℝ)) :
    ∑ a ∈ A.filter (fun a => g a ≤ Lam 0), C (g a) ≤
      (∑ a ∈ L, C (g a)) + ((N0 s : ℝ) - (L.card : ℝ)) * C lamS +
        ∑ j ∈ Finset.range s, ((N0 j : ℝ) - (N0 (j+1) : ℝ)) * C (Lam (j+1)) := by
  have hLam_mono : ∀ i j, i ≤ j → j ≤ s → Lam j ≤ Lam i := by
    intro i j hij hj
    have aux : ∀ n, i + n ≤ s → Lam (i + n) ≤ Lam i := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro h
        have hle : i + n ≤ s := by omega
        have hlt : i + n < s := by omega
        have heq : i + (n+1) = i + n + 1 := Nat.add_succ i n
        rw [heq]
        calc Lam (i + n + 1) ≤ Lam (i + n) := hdec (i+n) hlt
          _ ≤ Lam i := ih hle
    obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hij
    rw [hn] at hj ⊢
    exact aux n hj
  have hlamS0 : lamS ≤ Lam 0 := le_trans hLamS (hLam_mono 0 s (Nat.zero_le s) le_rfl)
  have hLS0 : L ⊆ A.filter (fun a => g a ≤ Lam 0) := by
    intro a ha
    simp only [Finset.mem_filter]
    exact ⟨hLA ha, le_of_lt (lt_of_lt_of_le (hLg a ha) hlamS0)⟩
  have hVstep : ∀ i, i ≤ s → Vf Lam s lamS (i+1) ≤ Vf Lam s lamS i := by
    intro i hi
    by_cases h : i + 1 ≤ s
    · rw [Vf_of_le Lam s lamS h, Vf_of_le Lam s lamS hi]
      exact hdec i (by omega)
    · have his : i = s := by omega
      rw [his, Vf_of_gt Lam s lamS (by omega), Vf_of_le Lam s lamS (le_refl s)]
      exact hLamS
  have hpoint : ∀ a ∈ (A.filter (fun a => g a ≤ Lam 0)) \ L,
      C (g a) ≤ ∑ i ∈ Finset.range (s+1),
        (C (Vf Lam s lamS (i+1)) - C (Vf Lam s lamS i)) * (if g a ≤ Vf Lam s lamS i then 1 else 0) := by
    intro a ha
    have h1 := Finset.mem_sdiff.mp ha
    have haA : a ∈ A := (Finset.mem_filter.mp h1.1).1
    have ha0 : g a ≤ Lam 0 := (Finset.mem_filter.mp h1.1).2
    have haL : a ∉ L := h1.2
    have hxa : lamS ≤ g a := by
      rcases hA a haA ha0 with h | h
      · exact h
      · exact absurd h haL
    exact level_pointwise Lam C s lamS hmono hC0 hLam_mono (g a) ha0 hxa
  have hcardid : ∀ i, i ≤ s →
      ∑ a ∈ (A.filter (fun a => g a ≤ Lam 0)) \ L, (if g a ≤ Vf Lam s lamS i then 1 else 0)
        = ((A.filter (fun a => g a ≤ Lam i)).card : ℝ) - (L.card : ℝ) := by
    intro i hi
    rw [Vf_of_le Lam s lamS hi, Finset.sum_boole]
    have hLsub : L ⊆ A.filter (fun a => g a ≤ Lam i) := by
      intro a ha
      simp only [Finset.mem_filter]
      exact ⟨hLA ha, le_of_lt (lt_of_lt_of_le (hLg a ha) (le_trans hLamS (hLam_mono i s hi le_rfl)))⟩
    have hset : (A.filter (fun a => g a ≤ Lam 0) \ L).filter (fun a => g a ≤ Lam i)
        = A.filter (fun a => g a ≤ Lam i) \ L := by
      apply Finset.ext
      intro a
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro ⟨⟨⟨haA, h0⟩, haLi⟩, hai⟩
        exact ⟨⟨haA, hai⟩, haLi⟩
      · rintro ⟨⟨haA, hai⟩, haLi⟩
        exact ⟨⟨⟨haA, le_trans hai (hLam_mono 0 i (Nat.zero_le i) hi)⟩, haLi⟩, hai⟩
    rw [hset, Finset.card_sdiff_of_subset hLsub, Nat.cast_sub (Finset.card_le_card hLsub)]
  have hmain : ∑ a ∈ (A.filter (fun a => g a ≤ Lam 0)) \ L, C (g a) ≤
      ((N0 s : ℝ) - (L.card : ℝ)) * C lamS +
        ∑ j ∈ Finset.range s, ((N0 j : ℝ) - (N0 (j+1) : ℝ)) * C (Lam (j+1)) := by
    calc ∑ a ∈ (A.filter (fun a => g a ≤ Lam 0)) \ L, C (g a)
        ≤ ∑ a ∈ (A.filter (fun a => g a ≤ Lam 0)) \ L, ∑ i ∈ Finset.range (s+1),
            (C (Vf Lam s lamS (i+1)) - C (Vf Lam s lamS i)) * (if g a ≤ Vf Lam s lamS i then 1 else 0) :=
          Finset.sum_le_sum hpoint
      _ = ∑ i ∈ Finset.range (s+1), (C (Vf Lam s lamS (i+1)) - C (Vf Lam s lamS i)) *
            (∑ a ∈ (A.filter (fun a => g a ≤ Lam 0)) \ L, (if g a ≤ Vf Lam s lamS i then 1 else 0)) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i hi
          exact (Finset.mul_sum _ _ _).symm
      _ ≤ ∑ i ∈ Finset.range (s+1), (C (Vf Lam s lamS (i+1)) - C (Vf Lam s lamS i)) * ((N0 i : ℝ) - (L.card : ℝ)) := by
          apply Finset.sum_le_sum
          intro i hi
          have hile : i ≤ s := by simp only [Finset.mem_range] at hi; omega
          apply mul_le_mul_of_nonneg_left
          · rw [hcardid i hile]; have hc := hcount i hile; linarith
          · exact sub_nonneg.mpr (hmono _ _ (hVstep i hile))
      _ = ((N0 s : ℝ) - (L.card : ℝ)) * C lamS +
            ∑ j ∈ Finset.range s, ((N0 j : ℝ) - (N0 (j+1) : ℝ)) * C (Lam (j+1)) := by
          rw [abel_identity (fun i => C (Vf Lam s lamS i)) (fun i => (N0 i : ℝ) - (L.card : ℝ)) s
                (by rw [Vf_of_le Lam s lamS (Nat.zero_le s), hC0])]
          rw [Vf_of_gt Lam s lamS (Nat.lt_succ_self s)]
          congr 1
          · ring
          · apply Finset.sum_congr rfl
            intro i hi
            have hi1 : i + 1 ≤ s := by simp only [Finset.mem_range] at hi; omega
            rw [Vf_of_le Lam s lamS hi1]
            ring
  have hsd := Finset.sum_sdiff (f := fun a => C (g a)) hLS0
  rw [← hsd]
  linarith [hmain]

end Work.A7
