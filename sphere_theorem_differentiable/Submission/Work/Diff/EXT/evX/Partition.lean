import Mathlib
import Submission.Work.Diff.EXT.evX.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The partition of the level-`n` tuple by the shuffle word `ε`

`Work.Diff.EXT.evX.dsf n ε r` (resp. `dsg n ε r`) is the position, in the level-`n` tuple
`Fin (4 + n)`, of the `r`-th `true` (resp. `false`) entry of the word `ε : Fin n → Bool`, and
`Work.Diff.EXT.evX.sPos n t` are the four `reactionMap`-slots (positions `n, …, n+3`).

This file proves `Work.Diff.EXT.evX.Partition`: the three families of positions are injective,
pairwise disjoint, and cover `Fin (4 + n)`.

The proof goes through an auxiliary *numerical* description of `dsf`/`dsg`:

* `posB n ε b r` is the (natural number) position of the `r`-th occurrence of the boolean `b` in
  the word `ε` (junk past the number of occurrences).  It is defined by the same recursion as
  `dsf`/`dsg`, and indeed `(dsf n ε r).val = posB n ε true r`, `(dsg n ε r).val = posB n ε false r`
  (`dsf_val_eq`, `dsg_val_eq`).
* `cntPref n ε b k` counts the occurrences of `b` at indices `< k`; `cntB n ε b = cntPref n ε b n`
  is the total number of occurrences of `b`, and agrees with `cntT n ε` for `b = true`, with
  `cntF n ε` for `b = false` (`cntT_eq`, `cntF_eq`).

The three central properties of `posB` (proved by the induction on `n` suggested by its recursion),
for `r < cntB n ε b`, are

* `posB_lt`  : `posB n ε b r < n`                              (it is a genuine position),
* `posB_mem` : `ε ⟨posB n ε b r, _⟩ = b`                       (it *is* an occurrence of `b`),
* `posB_cnt` : `cntPref n ε b (posB n ε b r) = r`              (exactly `r` occurrences lie before
                                                                 it, which pins it down uniquely),

and, conversely, every occurrence `i` of `b` is of this form (`posB_surj`), with the *same* index
`r = cntPref n ε b i.val`.

Injectivity, disjointness and the covering property are then immediate.
-/

namespace Work.Diff.EXT.evX

open scoped BigOperators

/-- `cntPref n ε b k` is the number of indices `i : Fin n` with `i.val < k` and `ε i = b`. -/
noncomputable def cntPref (n : ℕ) (ε : Fin n → Bool) (b : Bool) (k : ℕ) : ℕ :=
  ∑ i : Fin n, if i.val < k ∧ ε i = b then (1 : ℕ) else 0

/-- The number of occurrences of `b` in the word `ε`. -/
noncomputable def cntB (n : ℕ) (ε : Fin n → Bool) (b : Bool) : ℕ := cntPref n ε b n

/-- The position of the `r`-th occurrence of `b` in the word `ε`, as a natural number
(junk past the number of occurrences of `b`). -/
noncomputable def posB : (n : ℕ) → (Fin n → Bool) → Bool → ℕ → ℕ
  | 0, _, _, _ => 0
  | n + 1, ε, b, r =>
      if ε 0 = b then (if r = 0 then 0 else posB n (fun t => ε t.succ) b (r - 1) + 1)
      else posB n (fun t => ε t.succ) b r + 1

theorem posB_succ (n : ℕ) (ε : Fin (n + 1) → Bool) (b : Bool) (r : ℕ) :
    posB (n + 1) ε b r =
      (if ε 0 = b then (if r = 0 then 0 else posB n (fun t => ε t.succ) b (r - 1) + 1)
        else posB n (fun t => ε t.succ) b r + 1) := rfl

theorem cntPref_zero (n : ℕ) (ε : Fin n → Bool) (b : Bool) : cntPref n ε b 0 = 0 := by
  simp [cntPref]

theorem cntPref_succ (n : ℕ) (ε : Fin (n + 1) → Bool) (b : Bool) (k : ℕ) :
    cntPref (n + 1) ε b (k + 1) =
      (if ε 0 = b then 1 else 0) + cntPref n (fun t => ε t.succ) b k := by
  rw [cntPref, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.zero_lt_succ, true_and, Fin.val_succ]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i _
  by_cases h : i.val < k <;> simp [h]

/-- `Bool.toNat` against the `if`-form used by the counts of `Defs.lean`. -/
theorem toNat_eq_ite (c : Bool) : c.toNat = (if c = true then (1 : ℕ) else 0) := by
  cases c <;> rfl

theorem toNat_not_eq_ite (c : Bool) : (!c).toNat = (if c = false then (1 : ℕ) else 0) := by
  cases c <;> rfl

theorem cntB_zero (ε : Fin 0 → Bool) (b : Bool) : cntB 0 ε b = 0 := by
  rw [cntB, cntPref_zero]

theorem cntB_succ (n : ℕ) (ε : Fin (n + 1) → Bool) (b : Bool) :
    cntB (n + 1) ε b = (if ε 0 = b then 1 else 0) + cntB n (fun t => ε t.succ) b := by
  rw [cntB, cntB, cntPref_succ]

theorem cntT_eq (n : ℕ) (ε : Fin n → Bool) : cntT n ε = cntB n ε true := by
  induction n with
  | zero => simp [cntT, cntB, cntPref]
  | succ n ih =>
    rw [cntT_succ, cntB_succ, ih, toNat_eq_ite, Nat.add_comm]

theorem cntF_eq (n : ℕ) (ε : Fin n → Bool) : cntF n ε = cntB n ε false := by
  induction n with
  | zero => simp [cntF, cntB, cntPref]
  | succ n ih =>
    rw [cntF_succ, cntB_succ, ih, toNat_not_eq_ite, Nat.add_comm]

/-- The `r`-th occurrence of `b` (for `r` smaller than the number of occurrences) is a position in
one of the first `n` slots. -/
theorem posB_lt (n : ℕ) (ε : Fin n → Bool) (b : Bool) (r : ℕ) (h : r < cntB n ε b) :
    posB n ε b r < n := by
  induction n generalizing b r with
  | zero => rw [cntB_zero] at h; omega
  | succ n ih =>
    have hcnt : r < (if ε 0 = b then 1 else 0) + cntB n (fun t => ε t.succ) b := by
      rwa [cntB_succ] at h
    rw [posB_succ]
    by_cases hb : ε 0 = b
    · rw [ite_eq_left hb] at hcnt ⊢
      by_cases hr : r = 0
      · rw [ite_eq_left hr]; exact Nat.zero_lt_succ n
      · rw [ite_eq_right hr]
        have h1 : r - 1 < cntB n (fun t => ε t.succ) b := by omega
        have := ih (fun t => ε t.succ) b (r - 1) h1
        omega
    · rw [ite_eq_right hb] at hcnt ⊢
      have h1 : r < cntB n (fun t => ε t.succ) b := by omega
      have := ih (fun t => ε t.succ) b r h1
      omega

/-- The `r`-th occurrence of `b` really is an occurrence of `b`. -/
theorem posB_mem (n : ℕ) (ε : Fin n → Bool) (b : Bool) (r : ℕ) (h : r < cntB n ε b) :
    ∀ (i : Fin n), i.val = posB n ε b r → ε i = b := by
  induction n generalizing b r with
  | zero => intro i _; rw [cntB_zero] at h; omega
  | succ n ih =>
    intro i hi
    have hcnt : r < (if ε 0 = b then 1 else 0) + cntB n (fun t => ε t.succ) b := by
      rwa [cntB_succ] at h
    rw [posB_succ] at hi
    rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨j, rfl⟩
    · subst h0
      simp only [Fin.val_zero] at hi
      by_cases hb : ε 0 = b
      · rw [ite_eq_left hb] at hi
        by_cases hr : r = 0
        · rw [ite_eq_left hr] at hi
          exact hb
        · rw [ite_eq_right hr] at hi; omega
      · rw [ite_eq_right hb] at hi; omega
    · simp only [Fin.val_succ] at hi
      by_cases hb : ε 0 = b
      · rw [ite_eq_left hb] at hcnt hi
        by_cases hr : r = 0
        · rw [ite_eq_left hr] at hi; omega
        · rw [ite_eq_right hr] at hi
          have h1 : r - 1 < cntB n (fun t => ε t.succ) b := by omega
          exact ih (fun t => ε t.succ) b (r - 1) h1 j (by omega)
      · rw [ite_eq_right hb] at hcnt hi
        have h1 : r < cntB n (fun t => ε t.succ) b := by omega
        exact ih (fun t => ε t.succ) b r h1 j (by omega)

/-- There are exactly `r` occurrences of `b` before the `r`-th one. -/
theorem posB_cnt (n : ℕ) (ε : Fin n → Bool) (b : Bool) (r : ℕ) (h : r < cntB n ε b) :
    cntPref n ε b (posB n ε b r) = r := by
  induction n generalizing b r with
  | zero => rw [cntB_zero] at h; omega
  | succ n ih =>
    have hcnt : r < (if ε 0 = b then 1 else 0) + cntB n (fun t => ε t.succ) b := by
      rwa [cntB_succ] at h
    rw [posB_succ]
    by_cases hb : ε 0 = b
    · rw [ite_eq_left hb] at hcnt ⊢
      by_cases hr : r = 0
      · rw [ite_eq_left hr, hr, cntPref_zero]
      · rw [ite_eq_right hr]
        have h1 : r - 1 < cntB n (fun t => ε t.succ) b := by omega
        rw [cntPref_succ, ite_eq_left hb, ih (fun t => ε t.succ) b (r - 1) h1]
        omega
    · rw [ite_eq_right hb] at hcnt ⊢
      have h1 : r < cntB n (fun t => ε t.succ) b := by omega
      rw [cntPref_succ, ite_eq_right hb, ih (fun t => ε t.succ) b r h1]
      omega

/-- Every occurrence of `b` is the `r`-th one, for `r` = the number of occurrences before it. -/
theorem posB_surj (n : ℕ) (ε : Fin n → Bool) (b : Bool) (i : Fin n) (hi : ε i = b) :
    posB n ε b (cntPref n ε b i.val) = i.val ∧ cntPref n ε b i.val < cntB n ε b := by
  induction n generalizing b with
  | zero => exact i.elim0
  | succ n ih =>
    rcases Fin.eq_zero_or_eq_succ i with h0 | ⟨j, rfl⟩
    · subst h0
      simp only [Fin.val_zero]
      rw [cntPref_zero]
      constructor
      · rw [posB_succ, ite_eq_left hi, ite_eq_left rfl]
      · rw [cntB_succ, ite_eq_left hi]; omega
    · simp only [Fin.val_succ]
      have hi' : (fun t : Fin n => ε t.succ) j = b := hi
      obtain ⟨h1, h2⟩ := ih (fun t => ε t.succ) b j hi'
      rw [cntPref_succ, cntB_succ]
      by_cases hb : ε 0 = b
      · rw [ite_eq_left hb]
        constructor
        · rw [posB_succ, ite_eq_left hb,
            ite_eq_right (by omega : ¬ (1 + cntPref n (fun t => ε t.succ) b j.val = 0)),
            show 1 + cntPref n (fun t => ε t.succ) b j.val - 1
              = cntPref n (fun t => ε t.succ) b j.val by omega, h1]
        · omega
      · rw [ite_eq_right hb]
        constructor
        · rw [posB_succ, ite_eq_right hb, zero_add, h1]
        · omega

theorem dsf_val_eq (n : ℕ) (ε : Fin n → Bool) (r : ℕ) : (dsf n ε r).val = posB n ε true r := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [dsf.eq_2, posB_succ]
    by_cases h : ε 0 = true
    · simp only [ite_eq_left h]
      by_cases hr : r = 0
      · simp only [ite_eq_left hr]
      · simp only [ite_eq_right hr, Fin.val_succ, ih]
    · simp only [ite_eq_right h, Fin.val_succ, ih]

theorem dsg_val_eq (n : ℕ) (ε : Fin n → Bool) (r : ℕ) : (dsg n ε r).val = posB n ε false r := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [dsg.eq_2, posB_succ]
    by_cases h : ε 0 = true
    · have h' : ¬ (ε 0 = false) := by simp [h]
      simp only [ite_eq_left h, ite_eq_right h', Fin.val_succ, ih]
    · have h' : ε 0 = false := by cases hb : ε 0 <;> simp_all
      simp only [ite_eq_right h, ite_eq_left h']
      by_cases hr : r = 0
      · simp only [ite_eq_left hr]
      · simp only [ite_eq_right hr, Fin.val_succ, ih]

theorem Partition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (n : ℕ) (ε : Fin n → Bool) :
    Function.Injective (Work.Diff.EXT.evX.map₁ n ε) ∧
    Function.Injective (Work.Diff.EXT.evX.map₂ n ε) ∧
    (∀ (r : Fin (Work.Diff.EXT.evX.cntT n ε)) (r' : Fin (Work.Diff.EXT.evX.cntF n ε)),
        Work.Diff.EXT.evX.map₁ n ε r ≠ Work.Diff.EXT.evX.map₂ n ε r') ∧
    (∀ (r : Fin (Work.Diff.EXT.evX.cntT n ε)) (t : Fin 4),
        Work.Diff.EXT.evX.map₁ n ε r ≠ Work.Diff.EXT.evX.sPos n t) ∧
    (∀ (r : Fin (Work.Diff.EXT.evX.cntF n ε)) (t : Fin 4),
        Work.Diff.EXT.evX.map₂ n ε r ≠ Work.Diff.EXT.evX.sPos n t) ∧
    (∀ u : Fin (4 + n),
        (∃ r : Fin (Work.Diff.EXT.evX.cntT n ε), Work.Diff.EXT.evX.map₁ n ε r = u) ∨
        (∃ r : Fin (Work.Diff.EXT.evX.cntF n ε), Work.Diff.EXT.evX.map₂ n ε r = u) ∨
        (∃ t : Fin 4, Work.Diff.EXT.evX.sPos n t = u)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `map₁` is injective: the value of the `r`-th `true` determines `r`
    intro r r' hr
    apply Fin.ext
    have h1 : r.val < cntB n ε true := by rw [← cntT_eq]; exact r.isLt
    have h1' : r'.val < cntB n ε true := by rw [← cntT_eq]; exact r'.isLt
    have hpq : posB n ε true r.val = posB n ε true r'.val := by
      have h := congrArg Fin.val hr
      simpa only [map₁, dsf_val_eq] using h
    have h2 := posB_cnt n ε true r.val h1
    have h3 := posB_cnt n ε true r'.val h1'
    rw [← hpq] at h3
    omega
  · -- `map₂` is injective
    intro r r' hr
    apply Fin.ext
    have h1 : r.val < cntB n ε false := by rw [← cntF_eq]; exact r.isLt
    have h1' : r'.val < cntB n ε false := by rw [← cntF_eq]; exact r'.isLt
    have hpq : posB n ε false r.val = posB n ε false r'.val := by
      have h := congrArg Fin.val hr
      simpa only [map₂, dsg_val_eq] using h
    have h2 := posB_cnt n ε false r.val h1
    have h3 := posB_cnt n ε false r'.val h1'
    rw [← hpq] at h3
    omega
  · -- a `true`-position and a `false`-position are different
    intro r r' hr
    have h1 : r.val < cntB n ε true := by rw [← cntT_eq]; exact r.isLt
    have h2 : r'.val < cntB n ε false := by rw [← cntF_eq]; exact r'.isLt
    have hval : posB n ε true r.val = posB n ε false r'.val := by
      have h := congrArg Fin.val hr
      simpa only [map₁, map₂, dsf_val_eq, dsg_val_eq] using h
    have hlt := posB_lt n ε true r.val h1
    have e1 : ε ⟨posB n ε true r.val, hlt⟩ = true := posB_mem n ε true r.val h1 _ rfl
    have e2 : ε ⟨posB n ε true r.val, hlt⟩ = false := by
      refine posB_mem n ε false r'.val h2 _ ?_
      show posB n ε true r.val = posB n ε false r'.val
      exact hval
    rw [e1] at e2
    exact absurd e2 (by decide)
  · -- a `true`-position is not one of the four `reactionMap`-slots
    intro r t hr
    have h1 : r.val < cntB n ε true := by rw [← cntT_eq]; exact r.isLt
    have hval := congrArg Fin.val hr
    simp only [map₁, dsf_val_eq] at hval
    have hs : (sPos n t).val = n + t.val := rfl
    rw [hs] at hval
    have hlt := posB_lt n ε true r.val h1
    omega
  · -- a `false`-position is not one of the four `reactionMap`-slots
    intro r t hr
    have h1 : r.val < cntB n ε false := by rw [← cntF_eq]; exact r.isLt
    have hval := congrArg Fin.val hr
    simp only [map₂, dsg_val_eq] at hval
    have hs : (sPos n t).val = n + t.val := rfl
    rw [hs] at hval
    have hlt := posB_lt n ε false r.val h1
    omega
  · -- every slot is a `true`-position, a `false`-position, or a `reactionMap`-slot
    intro u
    by_cases hu : u.val < n
    · by_cases hb : ε ⟨u.val, hu⟩ = true
      · obtain ⟨hpos, hlt⟩ := posB_surj n ε true ⟨u.val, hu⟩ hb
        refine Or.inl ⟨⟨cntPref n ε true u.val, by rw [cntT_eq]; exact hlt⟩, ?_⟩
        apply Fin.ext
        simpa only [map₁, dsf_val_eq] using hpos
      · have hbf : ε ⟨u.val, hu⟩ = false := by cases hbb : ε ⟨u.val, hu⟩ <;> simp_all
        obtain ⟨hpos, hlt⟩ := posB_surj n ε false ⟨u.val, hu⟩ hbf
        refine Or.inr (Or.inl ⟨⟨cntPref n ε false u.val, by rw [cntF_eq]; exact hlt⟩, ?_⟩)
        apply Fin.ext
        simpa only [map₂, dsg_val_eq] using hpos
    · refine Or.inr (Or.inr ⟨⟨u.val - n, by omega⟩, ?_⟩)
      apply Fin.ext
      have hs : (sPos n ⟨u.val - n, by omega⟩).val = n + (u.val - n) := rfl
      rw [hs]
      omega

end Work.Diff.EXT.evX
