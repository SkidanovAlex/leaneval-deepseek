import Submission.Work.GYLocal2

/-!
# The localisation step of Green–Tao §9, part 3: the assembly

`Submission/Work/GYLocal.lean` builds the box decomposition and the per-box bounds,
`Submission/Work/GYLocal2.lean` the bad-box count.  This file assembles them into
Green–Tao Proposition 9.8: the Goldston–Yıldırım measurement `ν` satisfies the linear forms
condition, given the box-average asymptotic `BoxAvgGood` (their Proposition 9.5).
-/

open Finset
open scoped BigOperators

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1600000

namespace GYMaj
namespace Local

variable {m t p Q : ℕ}

/-- The volume (number of integer points) of the box `u`. -/
noncomputable def vol (p Q : ℕ) {t : ℕ} (u : Fin t → Fin Q) : ℝ :=
  ∏ j, ((sideLen p Q u j : ℕ) : ℝ)

lemma vol_nonneg (p Q : ℕ) {t : ℕ} (u : Fin t → Fin Q) : 0 ≤ vol p Q u := by
  unfold vol; positivity

/-- The box sum is nonnegative (every `ν`-factor is). -/
lemma boxsump_nonneg {p Q R W m t : ℕ} [NeZero p] {εw : ℝ} {A : Fin m → Fin t → ℤ}
    {c : Fin m → ℤ} (hR : 1 < R) (u : Fin t → Fin Q) :
    0 ≤ boxsump p Q R W εw A c u := by
  rw [boxsump]
  refine Finset.sum_nonneg (fun x _ => ?_)
  refine Finset.prod_nonneg (fun i _ => ?_)
  exact nuGT_nonneg (R := R) (W := W) (ε := εw) hR (psi p A c x i)

/-- **The boxes tile the space**: `∑_u vol u = p^t`. -/
theorem sum_vol (hQ : 0 < Q) (hQp : Q ≤ p) :
    (∑ u : Fin t → Fin Q, vol p Q u) = (p : ℝ) ^ t :=
  sum_sideLen (p := p) (Q := Q) (t := t) hQ hQp

open Classical in
/-- The set of indices `i` whose window contains the whole box `u`. -/
noncomputable def InSet (p : ℕ) {m t : ℕ} (A : Fin m → Fin t → ℤ) (c : Fin m → ℤ) (εw : ℝ)
    {Q : ℕ} (u : Fin t → Fin Q) : Finset (Fin m) :=
  Finset.univ.filter (fun i => AllIn p A c εw u i)

lemma mem_InSet {p : ℕ} {m t : ℕ} {A : Fin m → Fin t → ℤ} {c : Fin m → ℤ} {εw : ℝ}
    {Q : ℕ} {u : Fin t → Fin Q} {i : Fin m} :
    i ∈ InSet p A c εw u ↔ AllIn p A c εw u i := by
  classical
  simp [InSet]

/-- A nonempty box cannot be simultaneously all-in and all-out for the window. -/
lemma not_allOut_of_allIn {p Q : ℕ} {m t : ℕ} {A : Fin m → Fin t → ℤ} {c : Fin m → ℤ}
    {εw : ℝ} {u : Fin t → Fin Q} {i : Fin m}
    (hQ : 0 < Q) (hQp : Q ≤ p) (hin : AllIn p A c εw u i) : ¬ AllOut p A c εw u i := by
  intro hout
  have hmem := corner_mem (p := p) (Q := Q) hQ hQp u
  exact hout (corner p Q u) hmem (hin (corner p Q u) hmem)

/-- **Upper bound for a good box**: if every index is either completely in or completely out of
the window, the box sum is at most `(1+ε_box)^m` times the volume. -/
theorem boxsump_le_of_good {p Q k R W m t : ℕ} [NeZero p] {ε_box εw : ℝ}
    {A : Fin m → Fin t → ℤ} {c : Fin m → ℤ} {u : Fin t → Fin Q}
    (hQ : 0 < Q) (hQp : Q ≤ p) (hR1 : 1 ≤ R) (hR : 1 < R) (hW : 0 < W)
    (hε0 : 0 ≤ ε_box) (hε1 : ε_box ≤ 1)
    (hbox : BoxAvgGood k R W ε_box) (hm : m ≤ k * 2 ^ (k - 1)) (ht1 : 0 < t) (ht2 : t ≤ 3 * k - 4)
    (hne : ∀ i, ∃ j, A i j ≠ 0)
    (hprop : ∀ i i', i ≠ i' → ¬ ∃ lam : ℚ, ∀ j, (A i' j : ℚ) = lam * (A i j : ℚ))
    (hside : ∀ j, (R : ℤ) ^ (10 * m) ≤ ((sideLen p Q u j : ℕ) : ℤ))
    {Amax : ℕ} (hA : ∀ i j, (A i j).natAbs ≤ Amax) (hAmax : Amax ≤ k.factorial * k) {Kout Δ D : ℤ}
    (hD : ∀ (u : Fin t → Fin Q) (j : Fin t), ((sideLen p Q u j : ℕ) : ℤ) ≤ D)
    (hD0 : 0 ≤ D) (hΔ : (t : ℤ) * (Amax : ℤ) * D ≤ Δ) (hΔε : (Δ : ℝ) ≤ εw * (p : ℝ))
    (hΔp : (Δ : ℝ) + 2 * εw * (p : ℝ) < (p : ℝ)) (hεw : 0 < εw)
    (hgood : ∀ i, AllOut p A c εw u i ∨ AllIn p A c εw u i)
    (hpos : ∀ x ∈ boxInt p Q u, ∀ i,
        0 < (W : ℤ) * (Lint A c x i - boxShift p Q εw Kout A c u i * p) + 1) :
    boxsump p Q R W εw A c u ≤ (1 + ε_box) ^ m * vol p Q u := by
  classical
  have hSu : ∀ i, i ∉ InSet p A c εw u → AllOut p A c εw u i := by
    intro i hi
    rcases hgood i with h | h
    · exact h
    · exact absurd (mem_InSet.mpr h) hi
  have hSi : ∀ i ∈ InSet p A c εw u, AllIn p A c εw u i := fun i hi => mem_InSet.mp hi
  have hstab : ∀ i ∈ InSet p A c εw u,
      StableAt p Q A c u i (boxShift p Q εw Kout A c u i) := by
    intro i hi
    have hspec := boxShift_spec A c hQ hQp εw hεw Amax hA Kout Δ D hD hD0 hΔ hΔε hΔp u i
    rcases hspec with h | h
    · exact absurd h (not_allOut_of_allIn hQ hQp (hSi i hi))
    · exact h
  have hb := boxsump_le_good (p := p) (Q := Q) (k := k) (R := R) (W := W) (m := m) (t := t)
    (ε_box := ε_box) (εw := εw) (A := A) (c := c)
    (ks := boxShift p Q εw Kout A c u) (u := u) (InSet p A c εw u)
    hQ hR1 hR hW hε0 hbox hm ht1 ht2
    (fun i _ => hne i) (fun i _ i' _ h => hprop i i' h) (fun i j => le_trans (hA i j) hAmax) hside hSu hSi hstab
    (fun x hx i _ => hpos x hx i)
  have hcard : (InSet p A c εw u).card ≤ m := by
    have h := Finset.card_le_univ (InSet p A c εw u)
    simpa using h
  refine le_trans hb ?_
  rw [vol]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith) hcard) (by positivity)

/-- **Lower bound for a good box**: if every index is either completely in or completely out of
the window, the box sum is at least `(1-ε_box)^m` times the volume. -/
theorem boxsump_ge_of_good {p Q k R W m t : ℕ} [NeZero p] {ε_box εw : ℝ}
    {A : Fin m → Fin t → ℤ} {c : Fin m → ℤ} {u : Fin t → Fin Q}
    (hQ : 0 < Q) (hQp : Q ≤ p) (hR1 : 1 ≤ R) (hR : 1 < R) (hW : 0 < W)
    (hε0 : 0 ≤ ε_box) (hε1 : ε_box ≤ 1)
    (hbox : BoxAvgGood k R W ε_box) (hm : m ≤ k * 2 ^ (k - 1)) (ht1 : 0 < t) (ht2 : t ≤ 3 * k - 4)
    (hne : ∀ i, ∃ j, A i j ≠ 0)
    (hprop : ∀ i i', i ≠ i' → ¬ ∃ lam : ℚ, ∀ j, (A i' j : ℚ) = lam * (A i j : ℚ))
    (hside : ∀ j, (R : ℤ) ^ (10 * m) ≤ ((sideLen p Q u j : ℕ) : ℤ))
    {Amax : ℕ} (hA : ∀ i j, (A i j).natAbs ≤ Amax) (hAmax : Amax ≤ k.factorial * k) {Kout Δ D : ℤ}
    (hD : ∀ (u : Fin t → Fin Q) (j : Fin t), ((sideLen p Q u j : ℕ) : ℤ) ≤ D)
    (hD0 : 0 ≤ D) (hΔ : (t : ℤ) * (Amax : ℤ) * D ≤ Δ) (hΔε : (Δ : ℝ) ≤ εw * (p : ℝ))
    (hΔp : (Δ : ℝ) + 2 * εw * (p : ℝ) < (p : ℝ)) (hεw : 0 < εw)
    (hgood : ∀ i, AllOut p A c εw u i ∨ AllIn p A c εw u i)
    (hpos : ∀ x ∈ boxInt p Q u, ∀ i,
        0 < (W : ℤ) * (Lint A c x i - boxShift p Q εw Kout A c u i * p) + 1) :
    (1 - ε_box) ^ m * vol p Q u ≤ boxsump p Q R W εw A c u := by
  classical
  have hSu : ∀ i, i ∉ InSet p A c εw u → AllOut p A c εw u i := by
    intro i hi
    rcases hgood i with h | h
    · exact h
    · exact absurd (mem_InSet.mpr h) hi
  have hSi : ∀ i ∈ InSet p A c εw u, AllIn p A c εw u i := fun i hi => mem_InSet.mp hi
  have hstab : ∀ i ∈ InSet p A c εw u,
      StableAt p Q A c u i (boxShift p Q εw Kout A c u i) := by
    intro i hi
    have hspec := boxShift_spec A c hQ hQp εw hεw Amax hA Kout Δ D hD hD0 hΔ hΔε hΔp u i
    rcases hspec with h | h
    · exact absurd h (not_allOut_of_allIn hQ hQp (hSi i hi))
    · exact h
  have hb := boxsump_ge_good (p := p) (Q := Q) (k := k) (R := R) (W := W) (m := m) (t := t)
    (ε_box := ε_box) (εw := εw) (A := A) (c := c)
    (ks := boxShift p Q εw Kout A c u) (u := u) (InSet p A c εw u)
    hQ hR1 hR hW hε0 hε1 hbox hm ht1 ht2
    (fun i _ => hne i) (fun i _ i' _ h => hprop i i' h) (fun i j => le_trans (hA i j) hAmax) hside hSu hSi hstab
    (fun x hx i _ => hpos x hx i)
  have hcard : (InSet p A c εw u).card ≤ m := by
    have h := Finset.card_le_univ (InSet p A c εw u)
    simpa using h
  refine le_trans ?_ hb
  rw [vol]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hbase0 : 0 ≤ 1 - ε_box := by linarith
  have hone : (1 - ε_box) ≤ 1 := by linarith
  exact pow_le_pow_of_le_one hbase0 hone hcard


/-- **Upper bound for a bad box**: for any box the box sum is at most `(2+ε_box)^m` times the
volume (the crude bound, applied with the canonical shift). -/
theorem boxsump_le_of_bad {p Q k R W m t : ℕ} [NeZero p] {ε_box εw : ℝ}
    {A : Fin m → Fin t → ℤ} {c : Fin m → ℤ} {u : Fin t → Fin Q}
    (hQ : 0 < Q) (hQp : Q ≤ p) (hR1 : 1 ≤ R) (hR : 1 < R) (hW : 0 < W)
    (hε0 : 0 ≤ ε_box)
    (hbox : BoxAvgGood k R W ε_box) (hm : m ≤ k * 2 ^ (k - 1)) (ht1 : 0 < t) (ht2 : t ≤ 3 * k - 4)
    (hne : ∀ i, ∃ j, A i j ≠ 0)
    (hprop : ∀ i i', i ≠ i' → ¬ ∃ lam : ℚ, ∀ j, (A i' j : ℚ) = lam * (A i j : ℚ))
    (hside : ∀ j, (R : ℤ) ^ (10 * m) ≤ ((sideLen p Q u j : ℕ) : ℤ))
    {Amax : ℕ} (hA : ∀ i j, (A i j).natAbs ≤ Amax) (hAmax : Amax ≤ k.factorial * k) {Kout Δ D : ℤ}
    (hD : ∀ (u : Fin t → Fin Q) (j : Fin t), ((sideLen p Q u j : ℕ) : ℤ) ≤ D)
    (hD0 : 0 ≤ D) (hΔ : (t : ℤ) * (Amax : ℤ) * D ≤ Δ) (hΔε : (Δ : ℝ) ≤ εw * (p : ℝ))
    (hΔp : (Δ : ℝ) + 2 * εw * (p : ℝ) < (p : ℝ)) (hεw : 0 < εw)
    (hpos : ∀ x ∈ boxInt p Q u, ∀ i,
        0 < (W : ℤ) * (Lint A c x i - boxShift p Q εw Kout A c u i * p) + 1) :
    boxsump p Q R W εw A c u ≤ (2 + ε_box) ^ m * vol p Q u := by
  have hks : ∀ i, StableAt p Q A c u i (boxShift p Q εw Kout A c u i) ∨ AllOut p A c εw u i := by
    intro i
    exact (boxShift_spec A c hQ hQp εw hεw Amax hA Kout Δ D hD hD0 hΔ hΔε hΔp u i).symm
  have hb := boxsump_le_shifts (p := p) (Q := Q) (k := k) (R := R) (W := W) (m := m) (t := t)
    (ε_box := ε_box) (εw := εw) (A := A) (c := c) (ks := boxShift p Q εw Kout A c u) (u := u)
    hQ hR1 hR hW hε0 hbox hm ht1 ht2 hne hprop (fun i j => le_trans (hA i j) hAmax) hside hks hpos
  rwa [vol]

/-- **The two-sided bound on the total box sum.**  Splitting the boxes into the `Bad` ones and the
rest, the total sum `∑_u boxsump u` is squeezed between `(1-ε_box)^m p^t - V_bad` and
`(1+ε_box)^m p^t + (2+ε_box)^m V_bad`. -/
theorem sum_boxsump_bounds {p Q k R W m t : ℕ} [NeZero p] {ε_box εw : ℝ}
    {A : Fin m → Fin t → ℤ} {c : Fin m → ℤ} (Bad : Finset (Fin t → Fin Q))
    (hBad : ∀ u : Fin t → Fin Q, u ∈ Bad ↔ AllBad p Q εw A c u)
    (hQ : 0 < Q) (hQp : Q ≤ p) (hR1 : 1 ≤ R) (hR : 1 < R) (hW : 0 < W)
    (hε0 : 0 ≤ ε_box) (hε1 : ε_box ≤ 1)
    (hbox : BoxAvgGood k R W ε_box) (hm : m ≤ k * 2 ^ (k - 1)) (ht1 : 0 < t) (ht2 : t ≤ 3 * k - 4)
    (hne : ∀ i, ∃ j, A i j ≠ 0)
    (hprop : ∀ i i', i ≠ i' → ¬ ∃ lam : ℚ, ∀ j, (A i' j : ℚ) = lam * (A i j : ℚ))
    {Amax : ℕ} (hA : ∀ i j, (A i j).natAbs ≤ Amax) (hAmax : Amax ≤ k.factorial * k) {Kout Δ D : ℤ}
    (hD : ∀ (u : Fin t → Fin Q) (j : Fin t), ((sideLen p Q u j : ℕ) : ℤ) ≤ D)
    (hD0 : 0 ≤ D) (hΔ : (t : ℤ) * (Amax : ℤ) * D ≤ Δ) (hΔε : (Δ : ℝ) ≤ εw * (p : ℝ))
    (hΔp : (Δ : ℝ) + 2 * εw * (p : ℝ) < (p : ℝ)) (hεw : 0 < εw)
    (hc : ∀ i, (c i).natAbs ≤ (p : ℤ))
    (hKout : Kout ≤ -((t : ℤ) * (Amax : ℤ) + 2))
    (hside : ∀ (u : Fin t → Fin Q) (j : Fin t), (R : ℤ) ^ (10 * m) ≤ ((sideLen p Q u j : ℕ) : ℤ)) :
    (1 - ε_box) ^ m * ((p : ℝ) ^ t) - ∑ u ∈ Bad, vol p Q u
        ≤ ∑ u : Fin t → Fin Q, boxsump p Q R W εw A c u
      ∧ ∑ u : Fin t → Fin Q, boxsump p Q R W εw A c u
        ≤ (1 + ε_box) ^ m * ((p : ℝ) ^ t)
          + (2 + ε_box) ^ m * ∑ u ∈ Bad, vol p Q u := by
  classical
  have hpos : ∀ (u : Fin t → Fin Q) (x : Fin t → ℤ), x ∈ boxInt p Q u → ∀ i,
      0 < (W : ℤ) * (Lint A c x i - boxShift p Q εw Kout A c u i * p) + 1 :=
    fun u x hx i => boxShift_pos A c hQ hQp εw hεw Amax hA Kout Δ D hD hD0 hΔ hΔε hΔp
      hc hKout W u i x hx
  -- The indicator of the good boxes.
  set Good : Finset (Fin t → Fin Q) := Badᶜ with hGood
  have hbadGood : ∀ u, u ∈ Bad ∨ u ∈ Good := by
    intro u
    by_cases h : u ∈ Bad
    · exact Or.inl h
    · exact Or.inr (by simp [hGood, h])
  have hgood : ∀ u ∈ Good, ∀ i, AllOut p A c εw u i ∨ AllIn p A c εw u i := by
    intro u hu i
    have huB : u ∉ Bad := by
      rw [hGood] at hu
      simpa using hu
    by_contra hcon
    push Not at hcon
    exact huB ((hBad u).mpr ⟨i, hcon.1, hcon.2⟩)
  -- splitting the sum
  have hsplit : (∑ u : Fin t → Fin Q, boxsump p Q R W εw A c u)
      = (∑ u ∈ Bad, boxsump p Q R W εw A c u)
        + (∑ u ∈ Good, boxsump p Q R W εw A c u) := by
    rw [hGood]
    exact (Finset.sum_add_sum_compl Bad (f := fun u => boxsump p Q R W εw A c u)).symm
  have hsplitv : (∑ u : Fin t → Fin Q, vol p Q u)
      = (∑ u ∈ Bad, vol p Q u) + (∑ u ∈ Good, vol p Q u) := by
    rw [hGood]
    exact (Finset.sum_add_sum_compl Bad (f := fun u => vol p Q u)).symm
  have hvol : (∑ u ∈ Good, vol p Q u) = (p : ℝ) ^ t - ∑ u ∈ Bad, vol p Q u := by
    have h := sum_vol (p := p) (Q := Q) (t := t) hQ hQp
    rw [hsplitv] at h
    linarith [h]
  constructor
  · -- lower bound
    have hle : (∑ u ∈ Good, (1 - ε_box) ^ m * vol p Q u)
        ≤ ∑ u ∈ Good, boxsump p Q R W εw A c u := by
      refine Finset.sum_le_sum (fun u hu => ?_)
      exact boxsump_ge_of_good (p := p) (Q := Q) (k := k) (R := R) (W := W) (m := m) (t := t)
        (ε_box := ε_box) (εw := εw) (A := A) (c := c) (u := u)
        hQ hQp hR1 hR hW hε0 hε1 hbox hm ht1 ht2 hne hprop (hside u)
        hA hAmax hD hD0 hΔ hΔε hΔp hεw (hgood u hu) (hpos u)
    rw [← Finset.mul_sum] at hle
    have hbase : (0:ℝ) ≤ 1 - ε_box := by linarith
    have hpow : (1 - ε_box) ^ m ≤ 1 := pow_le_one₀ hbase (by linarith)
    have hbase_nn : (0:ℝ) ≤ (1 - ε_box) ^ m := pow_nonneg hbase m
    have hVnn : 0 ≤ ∑ u ∈ Bad, vol p Q u :=
      Finset.sum_nonneg (fun u _ => vol_nonneg p Q u)
    have hsumBad : 0 ≤ ∑ u ∈ Bad, boxsump p Q R W εw A c u :=
      Finset.sum_nonneg (fun u _ => boxsump_nonneg (p := p) (Q := Q) hR u)
    rw [hsplit]
    have h2 : (1 - ε_box) ^ m * ((p : ℝ) ^ t) - ∑ u ∈ Bad, vol p Q u
        ≤ (1 - ε_box) ^ m * (∑ u ∈ Good, vol p Q u) := by
      rw [hvol]
      nlinarith [hbase_nn, hVnn, hpow]
    linarith [hle, h2, hsumBad]
  · -- upper bound
    have hub : (∑ u ∈ Good, boxsump p Q R W εw A c u)
        ≤ ∑ u ∈ Good, (1 + ε_box) ^ m * vol p Q u := by
      refine Finset.sum_le_sum (fun u hu => ?_)
      exact boxsump_le_of_good (p := p) (Q := Q) (k := k) (R := R) (W := W) (m := m) (t := t)
        (ε_box := ε_box) (εw := εw) (A := A) (c := c) (u := u)
        hQ hQp hR1 hR hW hε0 hε1 hbox hm ht1 ht2 hne hprop (hside u)
        hA hAmax hD hD0 hΔ hΔε hΔp hεw (hgood u hu) (hpos u)
    have hlb : (∑ u ∈ Bad, boxsump p Q R W εw A c u)
        ≤ ∑ u ∈ Bad, (2 + ε_box) ^ m * vol p Q u := by
      refine Finset.sum_le_sum (fun u _ => ?_)
      exact boxsump_le_of_bad (p := p) (Q := Q) (k := k) (R := R) (W := W) (m := m) (t := t)
        (ε_box := ε_box) (εw := εw) (A := A) (c := c) (u := u)
        hQ hQp hR1 hR hW hε0 hbox hm ht1 ht2 hne hprop (hside u)
        hA hAmax hD hD0 hΔ hΔε hΔp hεw (hpos u)
    rw [← Finset.mul_sum] at hub
    rw [← Finset.mul_sum] at hlb
    rw [hsplit]
    have hVnn : 0 ≤ ∑ u ∈ Bad, vol p Q u := Finset.sum_nonneg (fun u _ => vol_nonneg p Q u)
    have hb1 : (0:ℝ) ≤ (1 + ε_box) ^ m := pow_nonneg (by linarith) m
    have hA₁ : (1 + ε_box) ^ m * (∑ u ∈ Good, vol p Q u) ≤ (1 + ε_box) ^ m * ((p : ℝ) ^ t) := by
      rw [hvol]
      nlinarith [hVnn, hb1]
    linarith [hub, hlb, hA₁]

/-- **The final arithmetic**: if the bad boxes occupy at most an `ε_bad` fraction of the space and
`ε_box` is small, the total box sum is `1 ± ε` times `p^t`. -/
theorem boxsum_abs_bound {p Q k R W m t : ℕ} [NeZero p] {ε_box εw ε εbad : ℝ}
    {A : Fin m → Fin t → ℤ} {c : Fin m → ℤ} (Bad : Finset (Fin t → Fin Q))
    (hBad : ∀ u : Fin t → Fin Q, u ∈ Bad ↔ AllBad p Q εw A c u)
    (hQ : 0 < Q) (hQp : Q ≤ p) (hR1 : 1 ≤ R) (hR : 1 < R) (hW : 0 < W)
    (hε0 : 0 ≤ ε_box) (hε1 : ε_box ≤ 1) (hm1 : 1 ≤ m)
    (hbox : BoxAvgGood k R W ε_box) (hm : m ≤ k * 2 ^ (k - 1)) (ht1 : 0 < t) (ht2 : t ≤ 3 * k - 4)
    (hne : ∀ i, ∃ j, A i j ≠ 0)
    (hprop : ∀ i i', i ≠ i' → ¬ ∃ lam : ℚ, ∀ j, (A i' j : ℚ) = lam * (A i j : ℚ))
    {Amax : ℕ} (hA : ∀ i j, (A i j).natAbs ≤ Amax) (hAmax : Amax ≤ k.factorial * k) {Kout Δ D : ℤ}
    (hD : ∀ (u : Fin t → Fin Q) (j : Fin t), ((sideLen p Q u j : ℕ) : ℤ) ≤ D)
    (hD0 : 0 ≤ D) (hΔ : (t : ℤ) * (Amax : ℤ) * D ≤ Δ) (hΔε : (Δ : ℝ) ≤ εw * (p : ℝ))
    (hΔp : (Δ : ℝ) + 2 * εw * (p : ℝ) < (p : ℝ)) (hεw : 0 < εw)
    (hc : ∀ i, (c i).natAbs ≤ (p : ℤ))
    (hKout : Kout ≤ -((t : ℤ) * (Amax : ℤ) + 2))
    (hside : ∀ (u : Fin t → Fin Q) (j : Fin t), (R : ℤ) ^ (10 * m) ≤ ((sideLen p Q u j : ℕ) : ℤ))
    (hsp1 : ε_box * (m : ℝ) * 2 ^ m ≤ ε / 3)
    (hsp2 : ε_box * (m : ℝ) ≤ ε / 3)
    (hεbad0 : 0 ≤ εbad)
    (hsp3 : (3 : ℝ) ^ m * εbad ≤ ε / 3)
    (hVbad : (∑ u ∈ Bad, vol p Q u) ≤ εbad * (p : ℝ) ^ t)
    (hε : 0 < ε) :
    |((p : ℝ) ^ t)⁻¹ * (∑ u : Fin t → Fin Q, boxsump p Q R W εw A c u) - 1| ≤ ε := by
  obtain ⟨hlow, hup⟩ := sum_boxsump_bounds (p := p) (Q := Q) (k := k) (R := R) (W := W)
    (m := m) (t := t) (ε_box := ε_box) (εw := εw) (A := A) (c := c) Bad hBad
    hQ hQp hR1 hR hW hε0 hε1 hbox hm ht1 ht2 hne hprop hA hAmax hD hD0 hΔ hΔε hΔp hεw hc hKout hside
  have hpt : (0:ℝ) < (p : ℝ) ^ t := by
    have hp : (0:ℝ) < p := by
      have := NeZero.pos p
      exact_mod_cast this
    positivity
  have hVnn : 0 ≤ ∑ u ∈ Bad, vol p Q u := Finset.sum_nonneg (fun u _ => vol_nonneg p Q u)
  -- upper bound for the normalised sum
  have hup' : ((p : ℝ) ^ t)⁻¹ * (∑ u : Fin t → Fin Q, boxsump p Q R W εw A c u) - 1
      ≤ ε_box * (m : ℝ) * 2 ^ m + (3 : ℝ) ^ m * εbad := by
    have h1 : ((p : ℝ) ^ t)⁻¹ * (∑ u : Fin t → Fin Q, boxsump p Q R W εw A c u)
        ≤ ((p : ℝ) ^ t)⁻¹ * ((1 + ε_box) ^ m * ((p : ℝ) ^ t)
            + (2 + ε_box) ^ m * (εbad * (p : ℝ) ^ t)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact le_trans hup (by
        refine add_le_add le_rfl ?_
        exact le_trans (mul_le_mul_of_nonneg_left hVbad (by positivity)) (le_of_eq (by ring)))
    have h2 : ((p : ℝ) ^ t)⁻¹ * ((1 + ε_box) ^ m * ((p : ℝ) ^ t)
          + (2 + ε_box) ^ m * (εbad * (p : ℝ) ^ t))
        = (1 + ε_box) ^ m + (2 + ε_box) ^ m * εbad := by
      field_simp
    rw [h2] at h1
    have h3 : (1 + ε_box) ^ m - 1 ≤ ε_box * (m : ℝ) * 2 ^ m := by
      have hx1 : (1:ℝ) ≤ 1 + ε_box := by linarith
      have hgeom : (∑ i ∈ Finset.range m, (1 + ε_box) ^ i) * ε_box = (1 + ε_box) ^ m - 1 := by
        have hg := geom_sum_mul (1 + ε_box) m
        have hsub : (1 + ε_box) - 1 = ε_box := by ring
        rwa [hsub] at hg
      have hsum : (∑ i ∈ Finset.range m, (1 + ε_box) ^ i) ≤ (m : ℝ) * 2 ^ m := by
        calc (∑ i ∈ Finset.range m, (1 + ε_box) ^ i)
            ≤ ∑ _i ∈ Finset.range m, (2:ℝ) ^ m := by
              refine Finset.sum_le_sum (fun i hi => ?_)
              have hi' : i ≤ m := le_of_lt (Finset.mem_range.mp hi)
              calc (1 + ε_box) ^ i ≤ 2 ^ i := pow_le_pow_left₀ (by linarith) (by linarith) i
                _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hi'
          _ = (m : ℝ) * 2 ^ m := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [← hgeom]
      calc (∑ i ∈ Finset.range m, (1 + ε_box) ^ i) * ε_box
          ≤ ((m : ℝ) * 2 ^ m) * ε_box := mul_le_mul_of_nonneg_right hsum hε0
        _ = ε_box * (m : ℝ) * 2 ^ m := by ring
    have h4 : (2 + ε_box) ^ m ≤ (3:ℝ) ^ m :=
      pow_le_pow_left₀ (show (0:ℝ) ≤ 2 + ε_box by linarith)
        (show (2 + ε_box) ≤ (3:ℝ) by linarith) m
    have h4' : (2 + ε_box) ^ m * εbad ≤ (3:ℝ) ^ m * εbad :=
      mul_le_mul_of_nonneg_right h4 hεbad0
    linarith [h1, h3, h4']
  -- lower bound
  have hlow' : -ε ≤ ((p : ℝ) ^ t)⁻¹ * (∑ u : Fin t → Fin Q, boxsump p Q R W εw A c u) - 1 := by
    have h1 : ((p : ℝ) ^ t)⁻¹ * ((1 - ε_box) ^ m * ((p : ℝ) ^ t) - εbad * (p : ℝ) ^ t)
        ≤ ((p : ℝ) ^ t)⁻¹ * (∑ u : Fin t → Fin Q, boxsump p Q R W εw A c u) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have : (1 - ε_box) ^ m * ((p : ℝ) ^ t) - ∑ u ∈ Bad, vol p Q u
          ≥ (1 - ε_box) ^ m * ((p : ℝ) ^ t) - εbad * (p : ℝ) ^ t := by linarith [hVbad]
      linarith [hlow, this]
    have h2 : ((p : ℝ) ^ t)⁻¹ * ((1 - ε_box) ^ m * ((p : ℝ) ^ t) - εbad * (p : ℝ) ^ t)
        = (1 - ε_box) ^ m - εbad := by
      field_simp
    rw [h2] at h1
    have h3 : 1 - (1 - ε_box) ^ m ≤ ε_box * (m : ℝ) := by
      have hb : (1:ℝ) + (m:ℝ) * (-ε_box) ≤ (1 + (-ε_box)) ^ m :=
        one_add_mul_le_pow (a := -ε_box) (show (-2:ℝ) ≤ -ε_box by linarith) m
      have hb' : (1:ℝ) - ε_box * (m:ℝ) ≤ (1 - ε_box) ^ m := by
        convert hb using 2 <;> ring
      linarith
    have h5 : εbad ≤ ε / 3 := by
      have h3m : (1:ℝ) ≤ (3:ℝ) ^ m := one_le_pow₀ (by norm_num)
      nlinarith [hsp3, h3m, hε, hεbad0]
    linarith [h1, h3, h5, hsp2]
  rw [abs_sub_le_iff]
  exact ⟨by linarith [hup', hsp1, hsp3], by linarith [hlow']⟩

end Local
end GYMaj

/-! ## The localisation: `BoxAvgGood` implies the linear forms condition for `ν` -/

namespace GYMaj
namespace Local

variable {m t p Q : ℕ}

/-- The crude bound for the volume of a box: `(p/Q + 1)^t`. -/
noncomputable def volBd (p Q : ℕ) (t : ℕ) : ℝ := (((p / Q + 1 : ℕ)) : ℝ) ^ t

lemma vol_le_volBd (hQ : 0 < Q) {u : Fin t → Fin Q} : vol p Q u ≤ volBd p Q t := by
  rw [vol, volBd]
  calc ∏ j, ((sideLen p Q u j : ℕ) : ℝ)
      ≤ ∏ _j : Fin t, (((p / Q + 1 : ℕ)) : ℝ) :=
        Finset.prod_le_prod (fun j _ => by
          exact_mod_cast Nat.zero_le (sideLen p Q u j))
          (fun j _ => by
            exact_mod_cast bhi_sub_blo_le (p := p) (Q := Q) hQ (u := u) j)
    _ = (((p / Q + 1 : ℕ)) : ℝ) ^ t := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The coefficient bound `k! · k` of the localisation. -/
def AmaxLoc (k : ℕ) : ℕ := k.factorial * k

/-- The side-length bound `D = p/Q + 1`. -/
def Dloc (p Q : ℕ) : ℤ := ((p / Q : ℕ) : ℤ) + 1

/-- The range bound `Δ = t · Amax · D`. -/
def Deltaloc (p Q k t : ℕ) : ℤ := (t : ℤ) * ((AmaxLoc k : ℕ) : ℤ) * Dloc p Q

/-- The bad-box count of the localisation (Green–Tao's `O(Q^{t-1})` bound). -/
noncomputable def BadCnt (p Q k t m : ℕ) : ℕ :=
  2 * m * (Q ^ (t - 1) * ((⌈2 * Kbad p Q (Deltaloc p Q k t) (AmaxLoc k) t⌉₊ + 1) * AmaxLoc k))

/-- **The numeric conditions of the localisation**, bundled: they can all be satisfied by taking
`Q` large and `R` large (they involve only `k`, `t`, `m` and the constants). -/
def LocalConsts (p k R W Q : ℕ) (ε_box εw ε εbad : ℝ) : Prop :=
  0 < Q ∧ Q ≤ p ∧ 0 < W ∧ 1 ≤ R ∧ 1 < R ∧ 0 ≤ ε_box ∧ ε_box ≤ 1 ∧ 0 < εw ∧
  (R : ℤ) ^ (10 * k * 2 ^ (k - 1)) ≤ (p / Q : ℕ) ∧ 0 ≤ εbad ∧ 0 < ε ∧
  (∀ m : ℕ, 1 ≤ m → m ≤ k * 2 ^ (k - 1) → ∀ t : ℕ, 1 ≤ t → t ≤ 3 * k - 4 →
     (Deltaloc p Q k t : ℝ) ≤ εw * (p : ℝ) ∧
     (Deltaloc p Q k t : ℝ) + 2 * εw * (p : ℝ) < (p : ℝ) ∧
     ε_box * (m : ℝ) * 2 ^ m ≤ ε / 3 ∧
     ε_box * (m : ℝ) ≤ ε / 3 ∧
     (3 : ℝ) ^ m * εbad ≤ ε / 3 ∧
     ((BadCnt p Q k t m : ℕ) : ℝ) * volBd p Q t ≤ εbad * (p : ℝ) ^ t)

/-- **Green–Tao Proposition 9.8 (integer coefficients).**  Given the box-average asymptotic
`BoxAvgGood` and the numeric conditions, the box decomposition, the bad-box count and the
per-box bounds assemble into the linear forms condition for `ν = nuGT`, with integer coefficients
`A` and constant terms `b`. -/
theorem int_lfc_nuGT {p : ℕ} [Fact p.Prime] {k R W Q m t : ℕ} {ε_box εw ε εbad : ℝ}
    (A : Fin m → Fin t → ℤ) (b : Fin m → ZMod p)
    (hm1 : 1 ≤ m) (hm : m ≤ k * 2 ^ (k - 1)) (ht1 : 0 < t) (ht2 : t ≤ 3 * k - 4)
    (hA : ∀ i j, (A i j).natAbs ≤ k.factorial * k) (hne : ∀ i, ∃ j, A i j ≠ 0)
    (hprop : ∀ i i', i ≠ i' → ¬ ∃ lam : ℚ, ∀ j, (A i' j : ℚ) = lam * (A i j : ℚ))
    (hbox : BoxAvgGood k R W ε_box) (hC : LocalConsts p k R W Q ε_box εw ε εbad) :
    |((Fintype.card (Fin t → ZMod p) : ℝ))⁻¹ *
        ∑ x : Fin t → ZMod p,
          ∏ i, nuGT R W p εw ((∑ j, ((A i j : ℤ) : ZMod p) * x j) + b i) - 1| ≤ ε := by
  classical
  obtain ⟨hQ, hQp, hW, hR1, hR, hε0, hε1, hεw, hsideQR, hεbad0, hε, hnum⟩ := hC
  have hA' : ∀ i j, (A i j).natAbs ≤ AmaxLoc k := hA
  have hD : ∀ (u : Fin t → Fin Q) (j : Fin t), ((sideLen p Q u j : ℕ) : ℤ) ≤ Dloc p Q := by
    intro u j
    rw [Dloc]
    exact_mod_cast bhi_sub_blo_le (p := p) (Q := Q) hQ (u := u) j
  have hD0 : 0 ≤ Dloc p Q := by
    rw [Dloc]; positivity
  have hΔnum := hnum m hm1 hm t ht1 ht2
  have hΔ : (t : ℤ) * ((AmaxLoc k : ℕ) : ℤ) * Dloc p Q ≤ Deltaloc p Q k t :=
    le_of_eq (by rw [Deltaloc])
  have hΔε : ((Deltaloc p Q k t : ℤ) : ℝ) ≤ εw * (p : ℝ) := hΔnum.1
  have hΔp : ((Deltaloc p Q k t : ℤ) : ℝ) + 2 * εw * (p : ℝ) < (p : ℝ) := hΔnum.2.1
  have hsp1 : ε_box * (m : ℝ) * 2 ^ m ≤ ε / 3 := hΔnum.2.2.1
  have hsp2 : ε_box * (m : ℝ) ≤ ε / 3 := hΔnum.2.2.2.1
  have hsp3 : (3 : ℝ) ^ m * εbad ≤ ε / 3 := hΔnum.2.2.2.2.1
  have hbadnum := hΔnum.2.2.2.2.2
  set c : Fin m → ℤ := fun i => (b i).val with hcdef
  have hc : ∀ i, (c i).natAbs ≤ (p : ℤ) := by
    intro i
    rw [hcdef]
    have h1 : (b i).val < p := ZMod.val_lt (b i)
    have h2 : (((b i).val : ℕ) : ℤ) < (p : ℤ) := by exact_mod_cast h1
    rw [Int.natAbs_natCast]
    linarith
  -- the canonical out-of-window shift
  set Kout : ℤ := -(((3 * k : ℕ) : ℤ) * ((AmaxLoc k : ℕ) : ℤ) + 2) with hKoutdef
  have hKout : Kout ≤ -((t : ℤ) * ((AmaxLoc k : ℕ) : ℤ) + 2) := by
    rw [hKoutdef]
    have h1 : (t : ℤ) ≤ ((3 * k : ℕ) : ℤ) := by
      have h2 : t ≤ 3 * k := by omega
      exact_mod_cast h2
    have h3 : (0 : ℤ) ≤ ((AmaxLoc k : ℕ) : ℤ) := Int.natCast_nonneg _
    nlinarith
  -- the side-length bound, uniformly in `u`
  have hside : ∀ (u : Fin t → Fin Q) (j : Fin t),
      (R : ℤ) ^ (10 * m) ≤ ((sideLen p Q u j : ℕ) : ℤ) := by
    intro u j
    have hm' : 10 * m ≤ 10 * (k * 2 ^ (k - 1)) := by omega
    have hRz : (1 : ℤ) ≤ (R : ℤ) := by exact_mod_cast hR1
    have h1 : (R : ℤ) ^ (10 * m) ≤ (R : ℤ) ^ (10 * (k * 2 ^ (k - 1))) :=
      pow_le_pow_right₀ hRz hm'
    have h2 : (R : ℤ) ^ (10 * (k * 2 ^ (k - 1))) = (R : ℤ) ^ (10 * k * 2 ^ (k - 1)) := by
      ring_nf
    have h3 : ((p / Q : ℕ) : ℤ) ≤ ((sideLen p Q u j : ℕ) : ℤ) := by
      exact_mod_cast div_le_bhi_sub_blo (p := p) (Q := Q) hQ (u := u) j
    calc (R : ℤ) ^ (10 * m) ≤ (R : ℤ) ^ (10 * k * 2 ^ (k - 1)) := by rw [← h2]; exact h1
      _ ≤ ((p / Q : ℕ) : ℤ) := hsideQR
      _ ≤ ((sideLen p Q u j : ℕ) : ℤ) := h3
  -- the bad boxes
  set Bad : Finset (Fin t → Fin Q) :=
    Finset.univ.filter (fun u : Fin t → Fin Q => AllBad p Q εw A c u) with hBaddef
  have hBad : ∀ u : Fin t → Fin Q, u ∈ Bad ↔ AllBad p Q εw A c u := by
    intro u
    rw [hBaddef, Finset.mem_filter]
    simp
  have hcard := bad_box_count (p := p) (Q := Q) (m := m) (t := t) A c hQ hQp hεw hA' hne
    hD hD0 hΔ hΔε hΔp hc hKout
  have hBadcard : (Bad.card : ℝ) ≤ ((BadCnt p Q k t m : ℕ) : ℝ) := by
    have h1 : Set.ncard {u : Fin t → Fin Q | AllBad p Q εw A c u} = Bad.card := by
      rw [hBaddef, ← Set.ncard_coe_finset]
      congr 1
      ext u
      simp
    rw [h1] at hcard
    exact_mod_cast hcard
  have hVbad : (∑ u ∈ Bad, vol p Q u) ≤ εbad * (p : ℝ) ^ t := by
    have h1 : (∑ u ∈ Bad, vol p Q u) ≤ (Bad.card : ℝ) * volBd p Q t := by
      calc ∑ u ∈ Bad, vol p Q u ≤ ∑ _u ∈ Bad, volBd p Q t :=
            Finset.sum_le_sum (fun u _ => vol_le_volBd (p := p) (Q := Q) hQ)
        _ = (Bad.card : ℝ) * volBd p Q t := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have h2 : (Bad.card : ℝ) * volBd p Q t
        ≤ ((BadCnt p Q k t m : ℕ) : ℝ) * volBd p Q t :=
      mul_le_mul_of_nonneg_right hBadcard (by rw [volBd]; positivity)
    linarith [h1, h2, hbadnum]
  rw [lfc_sum_eq_boxsum (p := p) (Q := Q) (R := R) (W := W) (m := m) (t := t)
    (Fact.out : p.Prime).pos hQ hQp εw A b]
  have hcardpt : (Fintype.card (Fin t → ZMod p) : ℝ) = (p : ℝ) ^ t := by
    rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    push_cast
    ring
  rw [hcardpt]
  exact boxsum_abs_bound (p := p) (Q := Q) (k := k) (R := R) (W := W) (m := m) (t := t)
    (ε_box := ε_box) (εw := εw) (ε := ε) (εbad := εbad) (A := A) (c := c) Bad hBad
    (Amax := AmaxLoc k) (Kout := Kout) (Δ := Deltaloc p Q k t) (D := Dloc p Q)
    hQ hQp hR1 hR hW hε0 hε1 hm1 hbox hm ht1 ht2 hne hprop hA' le_rfl hD hD0 hΔ hΔε hΔp hεw
    hc hKout hside hsp1 hsp2 hεbad0 hsp3 hVbad hε

/-- **Green–Tao Proposition 9.8.**  The Goldston–Yıldırım measurement `ν` satisfies the linear
forms condition (with rational coefficients of size `k`), given the box-average asymptotic
`BoxAvgGood` (Green–Tao's Proposition 9.5) and the numeric conditions. -/
theorem linFormsCond_nuGT {p : ℕ} [Fact p.Prime] {k R W Q : ℕ} {ε_box εw ε εbad : ℝ}
    (hk : k.factorial < p)
    (hbox : BoxAvgGood k R W ε_box) (hC : LocalConsts p k R W Q ε_box εw ε εbad) :
    Commons.NumberTheory.Sieve.LinFormsCond p (nuGT R W p εw) (k * 2 ^ (k - 1)) (3 * k - 4) k ε := by
  classical
  refine Commons.NumberTheory.Sieve.linFormsCond_of_int_coeff (L₀ := k) hk ?_
  intro m hm1 hm t ht1 ht2 A hA hne hprop b
  exact int_lfc_nuGT (p := p) (k := k) (R := R) (W := W) (Q := Q) (m := m) (t := t)
    (ε_box := ε_box) (εw := εw) (ε := ε) (εbad := εbad) A b hm1 hm ht1 ht2
    hA hne hprop hbox hC

end Local
end GYMaj
