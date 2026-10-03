import Mathlib

/-!
# Counting the indices of an increasing walk that come close to integers

Let `t : ℕ → ℝ` be a walk whose increments are at least `δ > 0`, and let `p` be the predicate
"`t j` is within distance `s` of an integer".  Then the number of good indices `j ≤ n` is bounded
by `((t n - t 0) + 2 s + 1) * (2 s / δ + 1)`:  each good index is attached to an integer of the
window `[t 0 - s, t n + s]`, and for a *single* integer `k` the good indices within `s` of `k`
have values of `t` in an interval of length `2 s`, hence are `δ`-separated, giving at most
`2 s / δ + 1` of them.
-/

namespace Work.Pert.Count

open Classical

/-- Canonical integer within distance `s` of `t j`, if one exists. -/
noncomputable def nearestInt (t : ℕ → ℝ) (s : ℝ) (j : ℕ) : ℤ :=
  if h : ∃ k : ℤ, dist (t j) (k : ℝ) ≤ s then h.choose else 0

lemma dist_nearestInt_le {t : ℕ → ℝ} {s : ℝ} {j : ℕ}
    (h : ∃ k : ℤ, dist (t j) (k : ℝ) ≤ s) : dist (t j) (nearestInt t s j : ℝ) ≤ s := by
  rw [nearestInt, dite_eq_left h]
  exact h.choose_spec

/-- The walk with increments `≥ δ` grows at least linearly: `(j' - j) δ ≤ t j' - t j`. -/
lemma sub_le_of_mono_walk {t : ℕ → ℝ} {n : ℕ} {δ : ℝ}
    (hmono : ∀ j < n, t j + δ ≤ t (j + 1)) :
    ∀ j j' : ℕ, j ≤ j' → j' ≤ n → (j' - j : ℝ) * δ ≤ t j' - t j := by
  have key : ∀ d j : ℕ, j + d ≤ n → (d : ℝ) * δ ≤ t (j + d) - t j := by
    intro d
    induction d with
    | zero => intro j _; simp
    | succ e ih =>
      intro j hj
      have hje : j + e ≤ n := by omega
      have h1 : (e : ℝ) * δ ≤ t (j + e) - t j := ih j hje
      have h2 : t (j + e) + δ ≤ t (j + e + 1) := hmono (j + e) (by omega)
      have h3 : ((e + 1 : ℕ) : ℝ) * δ = (e : ℝ) * δ + δ := by push_cast; ring
      have h4 : j + (e + 1) = j + e + 1 := by omega
      rw [h3, h4]
      linarith
  intro j j' hjj hj'n
  have h := key (j' - j) j (by omega)
  rw [Nat.add_sub_of_le hjj] at h
  rwa [Nat.cast_sub hjj] at h

theorem card_le_of_mono_walk {t : ℕ → ℝ} {n : ℕ} {s δ : ℝ} {p : ℕ → Prop} [DecidablePred p]
    (hδ : 0 < δ) (hs0 : 0 ≤ s) (hmono : ∀ j < n, t j + δ ≤ t (j + 1))
    (hp : ∀ j ≤ n, p j → ∃ k : ℤ, dist (t j) (k : ℝ) ≤ s) :
    ((((Finset.range (n + 1)).filter p).card : ℝ))
      ≤ ((t n - t 0) + 2 * s + 1) * (2 * s / δ + 1) := by
  classical
  have hdiff := sub_le_of_mono_walk hmono
  set A := (Finset.range (n + 1)).filter p with hA
  have hAmem : ∀ j, j ∈ A ↔ j < n + 1 ∧ p j := by
    intro j; rw [hA, Finset.mem_filter, Finset.mem_range]
  have hAle : ∀ j ∈ A, j ≤ n := by
    intro j hj
    have h1 : j < n + 1 := ((hAmem j).mp hj).1
    omega
  have hfspec : ∀ j ∈ A, dist (t j) (nearestInt t s j : ℝ) ≤ s := by
    intro j hj
    exact dist_nearestInt_le (hp j (hAle j hj) ((hAmem j).mp hj).2)
  -- t is nondecreasing on `[0, n]`
  have htmono : ∀ j j' : ℕ, j ≤ j' → j' ≤ n → t j ≤ t j' := by
    intro j j' hjj hj'n
    have h := hdiff j j' hjj hj'n
    have h3 : (0 : ℝ) ≤ ((j' - j : ℕ) : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ.le
    rw [Nat.cast_sub hjj] at h3
    linarith
  have ht0n : t 0 ≤ t n := htmono 0 n (Nat.zero_le n) (le_refl n)
  -- ## the fibre bound: at most `2 s / δ + 1` good indices per integer
  have hfiber : ∀ k : ℤ,
      ((A.filter (fun j => nearestInt t s j = k)).card : ℝ) ≤ 2 * s / δ + 1 := by
    intro k
    set S := A.filter (fun j => nearestInt t s j = k) with hS
    have hmemS : ∀ j, j ∈ S ↔ j ∈ A ∧ nearestInt t s j = k := by
      intro j; rw [hS, Finset.mem_filter]
    by_cases hne : S.Nonempty
    · have hj0 : S.min' hne ∈ S := Finset.min'_mem S hne
      have hj1 : S.max' hne ∈ S := Finset.max'_mem S hne
      have hdist_min : dist (t (S.min' hne)) (k : ℝ) ≤ s := by
        have h := hfspec _ ((hmemS _).mp hj0).1
        have hk : nearestInt t s (S.min' hne) = k := ((hmemS _).mp hj0).2
        rwa [hk] at h
      have hdist_max : dist (t (S.max' hne)) (k : ℝ) ≤ s := by
        have h := hfspec _ ((hmemS _).mp hj1).1
        have hk : nearestInt t s (S.max' hne) = k := ((hmemS _).mp hj1).2
        rwa [hk] at h
      have hle : S.min' hne ≤ S.max' hne := Finset.min'_le S _ hj1
      have hmaxn : S.max' hne ≤ n := hAle _ ((hmemS _).mp hj1).1
      have htle : t (S.max' hne) - t (S.min' hne) ≤ 2 * s := by
        rw [Real.dist_eq, abs_le] at hdist_min hdist_max
        linarith [hdist_min.1, hdist_min.2, hdist_max.1, hdist_max.2]
      have hratio : (S.max' hne : ℝ) - (S.min' hne : ℝ) ≤ 2 * s / δ := by
        rw [le_div_iff₀ hδ]
        have hdif := hdiff (S.min' hne) (S.max' hne) hle hmaxn
        linarith
      have hcard : (S.card : ℝ) ≤ 2 * s / δ + 1 := by
        have hsub : S ⊆ Finset.Icc (S.min' hne) (S.max' hne) := fun j hj =>
          Finset.mem_Icc.mpr ⟨Finset.min'_le S j hj, Finset.le_max' S j hj⟩
        have h1 : S.card ≤ S.max' hne - S.min' hne + 1 := by
          calc S.card ≤ (Finset.Icc (S.min' hne) (S.max' hne)).card := Finset.card_le_card hsub
            _ = S.max' hne + 1 - S.min' hne := Nat.card_Icc _ _
            _ = S.max' hne - S.min' hne + 1 := by omega
        have h2 : (S.card : ℝ) ≤ ((S.max' hne - S.min' hne + 1 : ℕ) : ℝ) := by
          exact_mod_cast h1
        have h3 : ((S.max' hne - S.min' hne + 1 : ℕ) : ℝ)
            = ((S.max' hne : ℝ) - (S.min' hne : ℝ)) + 1 := by
          rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hle]
        rw [h3] at h2
        linarith
      exact hcard
    · have h0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [h0]
      have : (0 : ℝ) ≤ 2 * s / δ + 1 := by
        have := div_nonneg (by linarith : (0 : ℝ) ≤ 2 * s) hδ.le
        linarith
      simpa using this
  -- ## the number of integers in the window `[t 0 - s, t n + s]`
  have himg_sub : A.image (nearestInt t s) ⊆ Finset.Icc ⌈t 0 - s⌉ ⌊t n + s⌋ := by
    intro k hk
    obtain ⟨j, hjA, rfl⟩ := Finset.mem_image.mp hk
    have hdist := hfspec j hjA
    rw [Real.dist_eq, abs_le] at hdist
    have hjn : j ≤ n := hAle j hjA
    have htj_le : t j ≤ t n := htmono j n hjn (le_refl n)
    have ht0_le : t 0 ≤ t j := htmono 0 j (Nat.zero_le j) hjn
    have hle_floor : nearestInt t s j ≤ ⌊t n + s⌋ := by
      rw [Int.le_floor]
      linarith [hdist.2, htj_le]
    have hceil_le : ⌈t 0 - s⌉ ≤ nearestInt t s j := by
      rw [Int.ceil_le]
      linarith [hdist.1, ht0_le]
    exact Finset.mem_Icc.mpr ⟨hceil_le, hle_floor⟩
  have hcard_img : (A.image (nearestInt t s)).card
      ≤ (⌊t n + s⌋ + 1 - ⌈t 0 - s⌉).toNat := by
    calc (A.image (nearestInt t s)).card ≤ (Finset.Icc ⌈t 0 - s⌉ ⌊t n + s⌋).card :=
          Finset.card_le_card himg_sub
      _ = (⌊t n + s⌋ + 1 - ⌈t 0 - s⌉).toNat := Int.card_Icc _ _
  have himage : ((A.image (nearestInt t s)).card : ℝ) ≤ (t n - t 0) + 2 * s + 1 := by
    have h1 : ((⌊t n + s⌋ + 1 - ⌈t 0 - s⌉).toNat : ℝ) ≤ (t n - t 0) + 2 * s + 1 := by
      by_cases hnonneg : (0 : ℤ) ≤ ⌊t n + s⌋ + 1 - ⌈t 0 - s⌉
      · have hz : ((⌊t n + s⌋ + 1 - ⌈t 0 - s⌉ : ℤ) : ℝ) ≤ (t n - t 0) + 2 * s + 1 := by
          have hfl : ((⌊t n + s⌋ : ℤ) : ℝ) ≤ t n + s := Int.floor_le _
          have hce : (t 0 - s) ≤ ((⌈t 0 - s⌉ : ℤ) : ℝ) := Int.le_ceil _
          push_cast
          linarith
        calc ((⌊t n + s⌋ + 1 - ⌈t 0 - s⌉).toNat : ℝ)
            = (((⌊t n + s⌋ + 1 - ⌈t 0 - s⌉).toNat : ℤ) : ℝ) := by push_cast; ring
          _ = ((⌊t n + s⌋ + 1 - ⌈t 0 - s⌉ : ℤ) : ℝ) := by
                rw [Int.toNat_of_nonneg hnonneg]
          _ ≤ (t n - t 0) + 2 * s + 1 := hz
      · have hcast : (⌊t n + s⌋ + 1 - ⌈t 0 - s⌉).toNat = 0 :=
          Int.toNat_of_nonpos (not_le.mp hnonneg).le
        rw [hcast]
        push_cast
        linarith [ht0n, hs0]
    calc ((A.image (nearestInt t s)).card : ℝ)
        ≤ (((⌊t n + s⌋ + 1 - ⌈t 0 - s⌉).toNat : ℕ) : ℝ) := by exact_mod_cast hcard_img
      _ ≤ (t n - t 0) + 2 * s + 1 := h1
  -- ## assembly
  have hfibsum := Finset.card_eq_sum_card_fiberwise (s := A) (f := nearestInt t s)
    (t := A.image (nearestInt t s)) (fun j hj => Finset.mem_image_of_mem _ hj)
  have hcast : (A.card : ℝ)
      = ∑ k ∈ A.image (nearestInt t s),
          ((A.filter (fun j => nearestInt t s j = k)).card : ℝ) := by
    rw [hfibsum]
    push_cast
    rfl
  have hbound : (0 : ℝ) ≤ 2 * s / δ + 1 := by
    have := div_nonneg (by linarith : (0 : ℝ) ≤ 2 * s) hδ.le
    linarith
  calc (A.card : ℝ)
      = ∑ k ∈ A.image (nearestInt t s),
          ((A.filter (fun j => nearestInt t s j = k)).card : ℝ) := hcast
    _ ≤ ∑ _k ∈ A.image (nearestInt t s), (2 * s / δ + 1) :=
        Finset.sum_le_sum (fun k _ => hfiber k)
    _ = ((A.image (nearestInt t s)).card : ℝ) * (2 * s / δ + 1) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((t n - t 0) + 2 * s + 1) * (2 * s / δ + 1) :=
        mul_le_mul_of_nonneg_right himage hbound

end Work.Pert.Count
