import Mathlib

/-!
# Counting integers in a residue class, with an interval constraint

This file proves a small counting lemma used in the Montgomery-type density
argument: the number of integers `m ≤ N` with `m ≡ n (mod q)` and
`|log (m / n)| ≤ D` is bounded simultaneously by

* `N / q + 1` — the plain number of integers up to `N` in a residue class, and
* `(e ^ D - e ^ (-D)) * n / q + 1` — the number of integers in the geometric
  interval `[n e^{-D}, n e^{D}]` lying in a residue class `mod q`.

The two ingredients are the elementary fact that the map `m ↦ m / q` is
injective on any set of integers that are pairwise congruent modulo `q ≥ 1`
(so a residue class occupies at most `N / q + 1` slots in `[1, N]`), and the
same observation combined with the fact that consecutive elements of a residue
class in an interval of length `L` are at least `q` apart, giving at most
`L / q + 1` elements.
-/

namespace Work.ZeroDensity.Montgomery

/-- **Counting a residue class inside a real interval.**
Let `q ≥ 1`, let `s` be a finite set of natural numbers all congruent to `c`
modulo `q`, and suppose every element of `s` lies between the reals `A` and `B`
(with `A ≤ B`). Then `s` has at most `(B - A) / q + 1` elements.

Indeed, all elements of `s` have the same residue modulo `q`, so writing
`mmin` for the least element of `s`, the map `m ↦ (m - mmin) / q` is injective
on `s` and takes values in `{0, …, (max s - min s) / q}`, whence
`#s ≤ (max s - min s) / q + 1 ≤ (B - A) / q + 1`. -/
private lemma card_modEq_le_interval (q : ℕ) (hq : 1 ≤ q) (s : Finset ℕ) (c : ℕ)
    (A B : ℝ) (hAB : A ≤ B) (hA : ∀ m ∈ s, A ≤ (m : ℝ)) (hB : ∀ m ∈ s, (m : ℝ) ≤ B)
    (hmod : ∀ m ∈ s, m ≡ c [MOD q]) :
    (s.card : ℝ) ≤ (B - A) / (q : ℝ) + 1 := by
  rcases s.eq_empty_or_nonempty with hs | hs
  · rw [hs]
    simp only [Finset.card_empty, Nat.cast_zero]
    have h0 : 0 ≤ (B - A) / (q : ℝ) := div_nonneg (sub_nonneg.mpr hAB) (by positivity)
    linarith
  · set mmin := s.min' hs with hmmindef
    set mmax := s.max' hs with hmmaxdef
    have hmmin_mem : mmin ∈ s := by rw [hmmindef]; exact Finset.min'_mem s hs
    have hmmax_mem : mmax ∈ s := by rw [hmmaxdef]; exact Finset.max'_mem s hs
    have hmmin_le : ∀ m ∈ s, mmin ≤ m := by
      intro m hm
      rw [hmmindef]
      exact Finset.min'_le s m hm
    have hle_mmax : ∀ m ∈ s, m ≤ mmax := by
      intro m hm
      rw [hmmaxdef]
      exact Finset.le_max' s m hm
    -- injectivity of `m ↦ (m - mmin) / q` on `s`
    have hinj : Set.InjOn (fun m : ℕ => (m - mmin) / q) ↑s := by
      intro m₁ hm₁ m₂ hm₂ heq
      have h1 : mmin ≤ m₁ := hmmin_le m₁ hm₁
      have h2 : mmin ≤ m₂ := hmmin_le m₂ hm₂
      have hmod12 : m₁ % q = m₂ % q := (hmod m₁ hm₁).trans (hmod m₂ hm₂).symm
      -- subtracting `mmin` preserves the residue, so the remainders agree
      have hsub : (m₁ - mmin) % q = (m₂ - mmin) % q :=
        Nat.ModEq.sub h1 h2 hmod12 (Nat.ModEq.refl (n := q) mmin)
      have e1 : q * ((m₁ - mmin) / q) + (m₁ - mmin) % q = m₁ - mmin := Nat.div_add_mod _ _
      have e2 : q * ((m₂ - mmin) / q) + (m₂ - mmin) % q = m₂ - mmin := Nat.div_add_mod _ _
      have heq' : (m₁ - mmin) / q = (m₂ - mmin) / q := heq
      have hx : m₁ - mmin = m₂ - mmin := by rw [← e1, ← e2, heq', hsub]
      calc m₁ = (m₁ - mmin) + mmin := (Nat.sub_add_cancel h1).symm
        _ = (m₂ - mmin) + mmin := by rw [hx]
        _ = m₂ := Nat.sub_add_cancel h2
    have hcard : s.card ≤ (mmax - mmin) / q + 1 := by
      have hmem : Set.MapsTo (fun m : ℕ => (m - mmin) / q) ↑s
          ↑(Finset.Icc 0 ((mmax - mmin) / q)) := by
        intro m hm
        simp only [Finset.mem_coe, Finset.mem_Icc]
        exact ⟨Nat.zero_le _, Nat.div_le_div_right (Nat.sub_le_sub_right (hle_mmax m hm) mmin)⟩
      have hc := Finset.card_le_card_of_injOn (fun m : ℕ => (m - mmin) / q) hmem hinj
      simpa using hc
    have h1 : (s.card : ℝ) ≤ (((mmax - mmin) / q : ℕ) : ℝ) + 1 := by
      exact_mod_cast hcard
    have h2 : ((((mmax - mmin) / q : ℕ)) : ℝ) ≤ (B - A) / (q : ℝ) := by
      have hstep : ((((mmax - mmin) / q : ℕ)) : ℝ) ≤ (((mmax - mmin : ℕ)) : ℝ) / (q : ℝ) :=
        Nat.cast_div_le
      have hstep2 : (((mmax - mmin : ℕ)) : ℝ) / (q : ℝ) ≤ (B - A) / (q : ℝ) := by
        apply div_le_div_of_nonneg_right
        · rw [Nat.cast_sub (hmmin_le mmax hmmax_mem)]
          have hb : (mmax : ℝ) ≤ B := hB mmax hmmax_mem
          have ha : A ≤ (mmin : ℝ) := hA mmin hmmin_mem
          linarith
        · positivity
      linarith
    linarith

/-- **Counting a residue class inside `[1, N]`.**
For `q ≥ 1`, the integers in `[1, N]` congruent to `n` modulo `q` are at most
`N / q + 1` in number. -/
private lemma card_filter_modEq_le (q n N : ℕ) (_hq : 1 ≤ q) :
    ((((Finset.Icc 1 N).filter (fun m : ℕ => m ≡ n [MOD q])).card : ℝ))
      ≤ (N : ℝ) / (q : ℝ) + 1 := by
  set s : Finset ℕ := (Finset.Icc 1 N).filter (fun m : ℕ => m ≡ n [MOD q]) with hs
  -- `m ↦ m / q` is injective on `s`, since two distinct elements of `s` in the
  -- same block `[k q, k q + q)` are congruent and differ by less than `q`
  have hinj : Set.InjOn (fun m : ℕ => m / q) ↑s := by
    intro m₁ hm₁ m₂ hm₂ heq
    rw [hs] at hm₁ hm₂
    have hmod12 : m₁ % q = m₂ % q :=
      ((Finset.mem_filter.mp hm₁).2).trans ((Finset.mem_filter.mp hm₂).2).symm
    have e1 : q * (m₁ / q) + m₁ % q = m₁ := Nat.div_add_mod _ _
    have e2 : q * (m₂ / q) + m₂ % q = m₂ := Nat.div_add_mod _ _
    have heq' : m₁ / q = m₂ / q := heq
    rw [← e1, ← e2, heq', hmod12]
  have hmem : Set.MapsTo (fun m : ℕ => m / q) ↑s ↑(Finset.Icc 0 (N / q)) := by
    intro m hm
    rw [hs] at hm
    simp only [Finset.mem_coe, Finset.mem_Icc]
    exact ⟨Nat.zero_le _, Nat.div_le_div_right (Finset.mem_Icc.mp (Finset.mem_filter.mp hm).1).2⟩
  have hcard : s.card ≤ (Finset.Icc 0 (N / q)).card :=
    Finset.card_le_card_of_injOn (fun m : ℕ => m / q) hmem hinj
  have hcard' : s.card ≤ N / q + 1 := by simpa using hcard
  have hcast : (s.card : ℝ) ≤ ((N / q : ℕ) : ℝ) + 1 := by exact_mod_cast hcard'
  have hNdiv : (((N / q : ℕ)) : ℝ) ≤ (N : ℝ) / (q : ℝ) := Nat.cast_div_le
  have hgoal : ((((Finset.Icc 1 N).filter (fun m : ℕ => m ≡ n [MOD q])).card : ℝ))
      = (s.card : ℝ) := by
    rw [hs]
  rw [hgoal]
  linarith

/-- **Linnik/Heath-Brown counting lemma.**
The number of integers `m ∈ [1, N]` with `m ≡ n (mod q)` and
`|log (m / n)| ≤ D` (where `n ≥ 1` and `D ≥ 0`) is at most both

* `N / q + 1`, the number of slots in a residue class below `N`, and
* `(e ^ D - e ^ (-D)) * n / q + 1`, the number of slots in a residue class
  inside the geometric interval `[n e^{-D}, n e^{D}]`. -/
theorem countCongLe (q n N : ℕ) (D : ℝ) (hn : 1 ≤ n) (hD : 0 ≤ D) :
    ((((Finset.Icc 1 N).filter (fun m : ℕ => m ≡ n [MOD q] ∧
        |Real.log ((m : ℝ) / (n : ℝ))| ≤ D)).card : ℝ))
      ≤ min ((N : ℝ) / (q : ℝ) + 1) ((Real.exp D - Real.exp (-D)) * (n : ℝ) / (q : ℝ) + 1) := by
  rcases Nat.eq_zero_or_pos q with hq0 | hqpos
  · -- `q = 0`: congruence mod `0` forces `m = n`, so there is at most one term
    rw [hq0]
    have hcard : ((((Finset.Icc 1 N).filter (fun m : ℕ => m ≡ n [MOD 0] ∧
        |Real.log ((m : ℝ) / (n : ℝ))| ≤ D)).card : ℕ)) ≤ 1 := by
      have hsub : (Finset.Icc 1 N).filter (fun m : ℕ => m ≡ n [MOD 0] ∧
            |Real.log ((m : ℝ) / (n : ℝ))| ≤ D) ⊆ ({n} : Finset ℕ) := by
        intro m hm
        simp only [Finset.mem_filter] at hm
        simp only [Finset.mem_singleton]
        exact Nat.modEq_zero_iff.mp hm.2.1
      calc ((Finset.Icc 1 N).filter (fun m : ℕ => m ≡ n [MOD 0] ∧
              |Real.log ((m : ℝ) / (n : ℝ))| ≤ D)).card
          ≤ ({n} : Finset ℕ).card := Finset.card_le_card hsub
        _ = 1 := Finset.card_singleton n
    have hcardR : (((Finset.Icc 1 N).filter (fun m : ℕ => m ≡ n [MOD 0] ∧
        |Real.log ((m : ℝ) / (n : ℝ))| ≤ D)).card : ℝ) ≤ 1 := by exact_mod_cast hcard
    rw [show min ((N : ℝ) / ((0 : ℕ) : ℝ) + 1)
        ((Real.exp D - Real.exp (-D)) * (n : ℝ) / ((0 : ℕ) : ℝ) + 1) = 1 by simp [div_zero]]
    exact hcardR
  · have hq1 : 1 ≤ q := hqpos
    refine le_min ?_ ?_
    · -- first bound: drop the logarithm constraint and count the residue class
      have hsub : (Finset.Icc 1 N).filter (fun m : ℕ => m ≡ n [MOD q] ∧
              |Real.log ((m : ℝ) / (n : ℝ))| ≤ D)
            ⊆ (Finset.Icc 1 N).filter (fun m : ℕ => m ≡ n [MOD q]) := by
        intro m hm
        simp only [Finset.mem_filter] at hm ⊢
        exact ⟨hm.1, hm.2.1⟩
      have hc : ((((Finset.Icc 1 N).filter (fun m : ℕ => m ≡ n [MOD q] ∧
              |Real.log ((m : ℝ) / (n : ℝ))| ≤ D)).card : ℝ))
            ≤ ((((Finset.Icc 1 N).filter (fun m : ℕ => m ≡ n [MOD q])).card : ℝ)) := by
        exact_mod_cast Finset.card_le_card hsub
      exact hc.trans (card_filter_modEq_le q n N hq1)
    · -- second bound: only the terms inside the geometric interval matter
      set s : Finset ℕ := (Finset.Icc 1 N).filter (fun m : ℕ => m ≡ n [MOD q] ∧
              |Real.log ((m : ℝ) / (n : ℝ))| ≤ D) with hs
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      have hexp : Real.exp (-D) ≤ Real.exp D := Real.exp_le_exp.mpr (by linarith)
      have hAB : (n : ℝ) * Real.exp (-D) ≤ (n : ℝ) * Real.exp D :=
        mul_le_mul_of_nonneg_left hexp (le_of_lt hnpos)
      have hmods : ∀ m ∈ s, m ≡ n [MOD q] := by
        intro m hm
        rw [hs] at hm
        exact (Finset.mem_filter.mp hm).2.1
      have hAs : ∀ m ∈ s, (n : ℝ) * Real.exp (-D) ≤ (m : ℝ) := by
        intro m hm
        rw [hs] at hm
        obtain ⟨hmI, _hmod, hlog⟩ := Finset.mem_filter.mp hm
        obtain ⟨hm1, _hm2⟩ := Finset.mem_Icc.mp hmI
        have hmpos : (0 : ℝ) < (m : ℝ) / (n : ℝ) := div_pos (by exact_mod_cast hm1) hnpos
        have hge : -D ≤ Real.log ((m : ℝ) / (n : ℝ)) := (abs_le.mp hlog).1
        have hle : Real.exp (-D) ≤ (m : ℝ) / (n : ℝ) := (Real.le_log_iff_exp_le hmpos).mp hge
        have h' : Real.exp (-D) * (n : ℝ) ≤ (m : ℝ) := (le_div_iff₀ hnpos).mp hle
        calc (n : ℝ) * Real.exp (-D) = Real.exp (-D) * (n : ℝ) := by ring
          _ ≤ (m : ℝ) := h'
      have hBs : ∀ m ∈ s, (m : ℝ) ≤ (n : ℝ) * Real.exp D := by
        intro m hm
        rw [hs] at hm
        obtain ⟨hmI, _hmod, hlog⟩ := Finset.mem_filter.mp hm
        obtain ⟨hm1, _hm2⟩ := Finset.mem_Icc.mp hmI
        have hmpos : (0 : ℝ) < (m : ℝ) / (n : ℝ) := div_pos (by exact_mod_cast hm1) hnpos
        have hle : Real.log ((m : ℝ) / (n : ℝ)) ≤ D := (abs_le.mp hlog).2
        have h' : (m : ℝ) / (n : ℝ) ≤ Real.exp D := (Real.log_le_iff_le_exp hmpos).mp hle
        have h'' : (m : ℝ) ≤ Real.exp D * (n : ℝ) := (div_le_iff₀ hnpos).mp h'
        calc (m : ℝ) ≤ Real.exp D * (n : ℝ) := h''
          _ = (n : ℝ) * Real.exp D := by ring
      have hmain := card_modEq_le_interval q hq1 s n ((n : ℝ) * Real.exp (-D))
            ((n : ℝ) * Real.exp D) hAB hAs hBs hmods
      have hgoal : ((((Finset.Icc 1 N).filter (fun m : ℕ => m ≡ n [MOD q] ∧
              |Real.log ((m : ℝ) / (n : ℝ))| ≤ D)).card : ℝ)) = (s.card : ℝ) := by
        rw [hs]
      rw [hgoal]
      calc (s.card : ℝ) ≤ ((n : ℝ) * Real.exp D - (n : ℝ) * Real.exp (-D)) / (q : ℝ) + 1 := hmain
        _ = (Real.exp D - Real.exp (-D)) * (n : ℝ) / (q : ℝ) + 1 := by ring

end Work.ZeroDensity.Montgomery
