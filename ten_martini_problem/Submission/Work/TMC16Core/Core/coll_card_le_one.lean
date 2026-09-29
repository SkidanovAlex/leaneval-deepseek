import Mathlib
import Submission.Work.TMC16Core.Core.windows

namespace Work.TMC16Core.Core

/-! ### Integer helpers

A window of integers shorter than `q` contains at most one multiple of `q`; these lemmas turn
`q ∣ (i - j)` together with interval membership into an equality. -/

/-- A multiple of `Q > 0` of absolute value `< Q` is `0`. -/
private lemma coll_dvd_eq_zero_of_abs_lt {Q d : ℤ} (hQ : 0 < Q) (hd : Q ∣ d)
    (h : |d| < Q) : d = 0 := by
  have h1 : |d| < |Q| := by rwa [abs_of_pos hQ]
  rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs] at h1
  have hnat : d.natAbs < Q.natAbs := by exact_mod_cast h1
  have hdvd : Q.natAbs ∣ d.natAbs := Int.natAbs_dvd_natAbs.mpr hd
  have hmod : d.natAbs % Q.natAbs = 0 := Nat.mod_eq_zero_of_dvd hdvd
  rw [Nat.mod_eq_of_lt hnat] at hmod
  exact Int.natAbs_eq_zero.mp hmod

/-- The unique multiple of `Q` lying in the open window `(nQ - Q, nQ + Q)` is `nQ`. -/
private lemma coll_eq_of_dvd_of_mem_Ioo {Q d : ℤ} (hQ : 0 < Q) (hd : Q ∣ d) {n : ℤ}
    (h1 : n * Q - Q < d) (h2 : d < n * Q + Q) : d = n * Q := by
  have hc : Q ∣ n * Q := ⟨n, by ring⟩
  have hsub : Q ∣ d - n * Q := dvd_sub hd hc
  have habs : |d - n * Q| < Q := by rw [abs_lt]; constructor <;> omega
  have h0 := coll_dvd_eq_zero_of_abs_lt hQ hsub habs
  omega

/-- A nonzero multiple of `Q > 0` with `|d| < 2Q` equals `Q` or `-Q`. -/
private lemma coll_eq_or_eq_neg_of_dvd_of_abs_lt_two {Q d : ℤ} (hQ : 0 < Q) (hd : Q ∣ d)
    (h : |d| < 2 * Q) (hne : d ≠ 0) : d = Q ∨ d = -Q := by
  obtain ⟨k, hk⟩ := hd
  have h' : |Q * k| < 2 * Q := by rw [hk] at h; exact h
  rw [abs_mul, abs_of_pos hQ] at h'
  have h2 : |k| < 2 := by
    by_contra hc
    have hc' : (2 : ℤ) ≤ |k| := not_lt.mp hc
    nlinarith [hQ, hc', h', abs_nonneg k]
  have hk0 : k ≠ 0 := by rintro rfl; rw [mul_zero] at hk; exact hne hk
  rw [abs_lt] at h2
  have hk1 : k = 1 ∨ k = -1 := by omega
  rcases hk1 with hk1 | hk1
  · left; rw [hk, hk1, mul_one]
  · right; rw [hk, hk1]; ring

/-- Unfolding of `J1resG` in a form with a single ring-normalized pair of bounds. -/
private lemma coll_mem_J1resG {h : ℕ} {x : ℤ} :
    x ∈ J1resG h ↔ -(h : ℤ) ≤ x ∧ x ≤ (h : ℤ) - 1 := by
  simp [J1resG]

/-- Unfolding of `J2resG`, with the bounds written in terms of the single product
`(ℓ : ℤ) * (q : ℤ)` so that all later integer-linear reasoning sees the same atoms. -/
private lemma coll_mem_J2resG {q h ℓ : ℕ} {x : ℤ} :
    x ∈ J2resG q h ℓ ↔
      (ℓ : ℤ) * (q : ℤ) - (q : ℤ) + (h : ℤ) ≤ x ∧
        x ≤ (ℓ : ℤ) * (q : ℤ) + (q : ℤ) - (h : ℤ) - 1 := by
  have e1 : ((ℓ : ℤ) - 1) * (q : ℤ) + (h : ℤ)
      = (ℓ : ℤ) * (q : ℤ) - (q : ℤ) + (h : ℤ) := by ring
  have e2 : ((ℓ : ℤ) + 1) * (q : ℤ) - (h : ℤ) - 1
      = (ℓ : ℤ) * (q : ℤ) + (q : ℤ) - (h : ℤ) - 1 := by ring
  simp only [J2resG, Finset.mem_Icc, e1, e2]

/-- **Collision index is unique**, general form: only `h < q` is used, not the full
`3q/5 ≤ h ≤ 5q/8` sandwich.  For any `j` in the union of the two resonant windows there is at
most one other element `i` of the union with `q ∣ (i - j)`.

Every `i` of the union with `q ∣ (i - j)`, `i ≠ j`, is determined by `j` and by which window
it lies in: if `j ∈ J₁`, then `i ∈ J₁` forces `i = j ± q` (only one sign fits, as `h < q`)
and `i ∈ J₂` forces `i = j + ℓq`, and the three corresponding ranges for `j` are pairwise
disjoint; if `j ∈ J₂`, then `i ∈ J₂` forces `i = j ± q` and `i ∈ J₁` forces `i = j - ℓq`,
again with pairwise disjoint ranges. -/
theorem coll_card_le_one_of_lt {q h ℓ : ℕ} (hq : 1 ≤ q) (hlt : h < q) (j : ℤ)
    (hj : j ∈ J1resG h ∪ J2resG q h ℓ) :
    ((J1resG h ∪ J2resG q h ℓ).filter (fun i => i ≠ j ∧ (q : ℤ) ∣ (i - j))).card ≤ 1 := by
  have hQ : (0 : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hltZ : (h : ℤ) < (q : ℤ) := by exact_mod_cast hlt
  rw [Finset.card_le_one]
  intro a ha b hb
  rw [Finset.mem_filter] at ha hb
  obtain ⟨haS, haj, hadvd⟩ := ha
  obtain ⟨hbS, hbj, hbdvd⟩ := hb
  rcases Finset.mem_union.mp hj with hj1 | hj2
  · -- the base point `j` lies in `J₁`
    obtain ⟨hjlo, hjhi⟩ := coll_mem_J1resG.mp hj1
    have key : ∀ {x : ℤ}, x ∈ J1resG h ∪ J2resG q h ℓ → x ≠ j → (q : ℤ) ∣ (x - j) →
        (x = j + (q : ℤ) ∧ j ≤ (h : ℤ) - 1 - (q : ℤ)) ∨
        (x = j - (q : ℤ) ∧ (q : ℤ) - (h : ℤ) ≤ j) ∨
        (x = j + (ℓ : ℤ) * (q : ℤ) ∧
          ((h : ℤ) - (q : ℤ) ≤ j ∧ j ≤ (q : ℤ) - (h : ℤ) - 1)) := by
      intro x hxS hxj hxdvd
      rcases Finset.mem_union.mp hxS with hx1 | hx2
      · -- `x` also lies in `J₁`: `x - j = ±q`
        obtain ⟨hxlo, hxhi⟩ := coll_mem_J1resG.mp hx1
        have habs : |x - j| < 2 * (q : ℤ) := by
          rw [abs_lt]; constructor <;> omega
        rcases coll_eq_or_eq_neg_of_dvd_of_abs_lt_two hQ hxdvd habs (sub_ne_zero.mpr hxj)
          with heq | heq
        · exact Or.inl ⟨by omega, by omega⟩
        · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
      · -- `x` lies in `J₂`: the only multiple of `q` available is `ℓq`
        obtain ⟨hxlo, hxhi⟩ := coll_mem_J2resG.mp hx2
        have heq : x - j = (ℓ : ℤ) * (q : ℤ) :=
          coll_eq_of_dvd_of_mem_Ioo hQ hxdvd (n := (ℓ : ℤ)) (by omega) (by omega)
        exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)
    rcases key haS haj hadvd with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
    · rcases key hbS hbj hbdvd with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> omega
    · rcases key hbS hbj hbdvd with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> omega
    · rcases key hbS hbj hbdvd with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> omega
  · -- the base point `j` lies in `J₂`
    obtain ⟨hjlo, hjhi⟩ := coll_mem_J2resG.mp hj2
    have key : ∀ {x : ℤ}, x ∈ J1resG h ∪ J2resG q h ℓ → x ≠ j → (q : ℤ) ∣ (x - j) →
        (x = j + (q : ℤ) ∧ j ≤ (ℓ : ℤ) * (q : ℤ) - (h : ℤ) - 1) ∨
        (x = j - (q : ℤ) ∧ (ℓ : ℤ) * (q : ℤ) + (h : ℤ) ≤ j) ∨
        (x = j - (ℓ : ℤ) * (q : ℤ) ∧
          ((ℓ : ℤ) * (q : ℤ) - (h : ℤ) ≤ j ∧ j ≤ (ℓ : ℤ) * (q : ℤ) + (h : ℤ) - 1)) := by
      intro x hxS hxj hxdvd
      rcases Finset.mem_union.mp hxS with hx1 | hx2
      · -- `x` lies in `J₁`: the only multiple of `q` available is `-ℓq`
        obtain ⟨hxlo, hxhi⟩ := coll_mem_J1resG.mp hx1
        -- work with `j - x`, so that the parameter of the window is `ℓ` and not `-ℓ`
        have hdvd' : (q : ℤ) ∣ j - x := by
          have : j - x = -(x - j) := by ring
          rw [this]
          exact dvd_neg.mpr hxdvd
        have heq : j - x = (ℓ : ℤ) * (q : ℤ) :=
          coll_eq_of_dvd_of_mem_Ioo hQ hdvd' (n := (ℓ : ℤ)) (by omega) (by omega)
        exact Or.inr (Or.inr ⟨by omega, by omega, by omega⟩)
      · -- `x` also lies in `J₂`: `x - j = ±q`
        obtain ⟨hxlo, hxhi⟩ := coll_mem_J2resG.mp hx2
        have habs : |x - j| < 2 * (q : ℤ) := by
          rw [abs_lt]; constructor <;> omega
        rcases coll_eq_or_eq_neg_of_dvd_of_abs_lt_two hQ hxdvd habs (sub_ne_zero.mpr hxj)
          with heq | heq
        · exact Or.inl ⟨by omega, by omega⟩
        · exact Or.inr (Or.inl ⟨by omega, by omega⟩)
    rcases key haS haj hadvd with ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩ | ⟨ha1, ha2⟩
    · rcases key hbS hbj hbdvd with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> omega
    · rcases key hbS hbj hbdvd with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> omega
    · rcases key hbS hbj hbdvd with ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ | ⟨hb1, hb2⟩ <;> omega

/-- **Collision index is unique.**  In the union of the two resonant windows
`J₁ = [-h, h-1]` and `J₂ = [(ℓ-1)q + h, (ℓ+1)q - h - 1]` (phase-index coordinates), for
any `j` in the union there is **at most one** other element `i` with `q ∣ (i - j)`.

Reason: from `3q/5 ≤ h ≤ 5q/8` one gets `h < q` and `2q - 2h - 1 < q`, so
 * if `j ∈ J₁`: `i ∈ J₁` forces `i - j = ±q`, and only one sign can occur (as `h < q`);
   while `i ∈ J₂` forces `i - j = ℓ·q` (since `i - j ∈ [(ℓ-1)q+1, (ℓ+1)q-1]`), and that
   needs `h - q ≤ j ≤ q - h - 1`, disjoint from the `±q` alternatives
   (`j ≤ h-1-q` or `j ≥ q-h`);
 * if `j ∈ J₂`: `i ∈ J₂` is impossible (diameter `< q`) and `i ∈ J₁` forces `i - j = -ℓ·q`.
(The degenerate case `q = 1, h = 0`, where `J₂ = {ℓ-1, ℓ}` has diameter `q`, still has at
most one partner per `j`, differing by `±1`.)

`3 * q / 5` and `5 * q / 8` are ℕ-division, so the hypotheses give `5*h ≥ 3*q - 4`,
`8*h ≤ 5*q`. -/
theorem coll_card_le_one {q h ℓ : ℕ} (hq : 1 ≤ q) (hh : 3 * q / 5 ≤ h) (hh' : h ≤ 5 * q / 8)
    (hℓ : 1 ≤ ℓ) (j : ℤ)
    (hj : j ∈ Work.TMC16Core.Core.J1resG h ∪ Work.TMC16Core.Core.J2resG q h ℓ) :
    ((Work.TMC16Core.Core.J1resG h ∪ Work.TMC16Core.Core.J2resG q h ℓ).filter
      (fun i => i ≠ j ∧ (q : ℤ) ∣ (i - j))).card ≤ 1 := by
  refine coll_card_le_one_of_lt hq ?_ j hj
  -- `h ≤ 5q/8` together with `q ≥ 1` gives `h < q`
  have h8 : h * 8 ≤ 5 * q := (Nat.le_div_iff_mul_le (k := 8) (by norm_num)).mp hh'
  have h8' : (h : ℤ) * 8 ≤ 5 * (q : ℤ) := by exact_mod_cast h8
  have hq1 : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq
  have hltZ : (h : ℤ) < (q : ℤ) := by
    have : (h : ℤ) * 8 < (q : ℤ) * 8 := by linarith
    linarith
  exact_mod_cast hltZ

end Work.TMC16Core.Core
