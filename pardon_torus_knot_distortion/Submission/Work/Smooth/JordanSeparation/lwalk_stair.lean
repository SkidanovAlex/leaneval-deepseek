import Mathlib
import Submission.Work.Smooth.JordanSeparation.lwalk_basic

/-!
# Lattice staircases

* `toward p q k` — the integer obtained from `p` by moving one unit at a time towards `q`, for
  `k` steps (and clamped at `q`);
* `slen p q` — the number of lattice steps in the monotone staircase from `p` to `q`;
* `svec p q k` — the vertices of that staircase: first the `x`-coordinate is moved, then the
  `y`-coordinate;
* `svec_step` — successive vertices are `GridStep`-adjacent;
* the rectangle bound `svec_fst_mem`/`svec_snd_mem`, and the metric bound `svec_gpt_dist_le`:
  every vertex of the staircase is no further from `p` than `q` is.
-/

namespace Work.Smooth.JordanSeparation

open Set Metric

noncomputable section

/-! ### Moving one unit at a time on `ℤ` -/

/-- `toward p q k` is `p` moved `k` unit steps towards `q` (clamped at `q`). -/
def toward (p q : ℤ) (k : ℕ) : ℤ := if p ≤ q then min (p + k) q else max (p - k) q

theorem toward_zero (p q : ℤ) : toward p q 0 = p := by
  have h0 : ((0 : ℕ) : ℤ) = 0 := rfl
  unfold toward
  rw [h0]
  split_ifs with h
  · rw [add_zero]
    exact le_antisymm (min_le_left p q) (le_min le_rfl h)
  · rw [sub_zero]
    exact le_antisymm (max_le le_rfl (not_le.mp h).le) (le_max_left p q)

/-- `((q - p).natAbs : ℤ)` is either `q - p` or `p - q`. -/
theorem natAbs_sub_eq (p q : ℤ) :
    (((q - p).natAbs : ℤ)) = q - p ∨ (((q - p).natAbs : ℤ)) = p - q := by
  by_cases h : p ≤ q
  · left
    exact Int.natAbs_of_nonneg (by omega)
  · right
    have h1 : q - p = -(p - q) := by ring
    have h2 : (q - p).natAbs = (p - q).natAbs := by rw [h1, Int.natAbs_neg]
    rw [h2, Int.natAbs_of_nonneg (by omega : (0:ℤ) ≤ p - q)]

theorem toward_natAbs (p q : ℤ) : toward p q (q - p).natAbs = q := by
  by_cases hpq : p ≤ q
  · have h : (((q - p).natAbs : ℤ)) = q - p := Int.natAbs_of_nonneg (by omega)
    unfold toward
    rw [if_pos hpq, h, show p + (q - p) = q by ring]
    exact min_self q
  · have h : (((q - p).natAbs : ℤ)) = p - q := by
      have h1 : q - p = -(p - q) := by ring
      have h2 : (q - p).natAbs = (p - q).natAbs := by rw [h1, Int.natAbs_neg]
      rw [h2, Int.natAbs_of_nonneg (by omega : (0:ℤ) ≤ p - q)]
    unfold toward
    rw [if_neg hpq, h, show p - (p - q) = q by ring]
    exact max_self q

theorem toward_mem_Icc (p q : ℤ) (k : ℕ) : min p q ≤ toward p q k ∧ toward p q k ≤ max p q := by
  unfold toward
  split_ifs with h
  · refine ⟨le_min (le_trans (min_le_left p q) (le_add_of_nonneg_right (Int.natCast_nonneg k)))
      (min_le_right p q), le_trans (min_le_right (p + (k:ℤ)) q) (le_max_right p q)⟩
  · refine ⟨le_trans (min_le_right p q) (le_max_right (p - (k:ℤ)) q), ?_⟩
    exact max_le (le_trans (by omega : p - (k:ℤ) ≤ p) (le_max_left p q)) (le_max_right p q)

theorem toward_step_up {p q : ℤ} (h : p ≤ q) {k : ℕ} (hk : k < (q - p).natAbs) :
    toward p q (k + 1) = toward p q k + 1 := by
  have hle : ((k : ℤ)) + 1 ≤ q - p := by
    have h1 : (((k + 1 : ℕ)) : ℤ) ≤ (((q - p).natAbs : ℤ)) := by
      exact_mod_cast (Nat.succ_le_of_lt hk)
    have h2 : (((q - p).natAbs : ℤ)) = q - p := Int.natAbs_of_nonneg (by omega)
    push_cast at h1
    omega
  have h1 : toward p q k = p + k := by
    unfold toward
    rw [if_pos h]
    exact le_antisymm (min_le_left _ _) (le_min le_rfl (by linarith [hle]))
  have h2 : toward p q (k + 1) = p + ((k + 1 : ℕ) : ℤ) := by
    unfold toward
    rw [if_pos h]
    exact le_antisymm (min_le_left _ _) (le_min le_rfl (by push_cast; linarith [hle]))
  rw [h1, h2]
  push_cast
  ring

theorem toward_step_down {p q : ℤ} (h : q ≤ p) {k : ℕ} (hk : k < (q - p).natAbs) :
    toward p q (k + 1) = toward p q k - 1 := by
  have hne : ¬ (p ≤ q) := by
    intro hpq
    have h0 : (q - p).natAbs = 0 := by rw [le_antisymm hpq h, sub_self, Int.natAbs_zero]
    rw [h0] at hk
    exact Nat.not_lt_zero k hk
  have hle : ((k : ℤ)) + 1 ≤ p - q := by
    have h1 : (((k + 1 : ℕ)) : ℤ) ≤ (((q - p).natAbs : ℤ)) := by
      exact_mod_cast (Nat.succ_le_of_lt hk)
    have h2 : (((q - p).natAbs : ℤ)) = p - q := by
      have h3 : q - p = -(p - q) := by ring
      have h4 : (q - p).natAbs = (p - q).natAbs := by rw [h3, Int.natAbs_neg]
      rw [h4, Int.natAbs_of_nonneg (by omega : (0:ℤ) ≤ p - q)]
    push_cast at h1
    omega
  have h1 : toward p q k = p - k := by
    unfold toward
    rw [if_neg hne]
    exact max_eq_left (by linarith [hle])
  have h2 : toward p q (k + 1) = p - ((k + 1 : ℕ) : ℤ) := by
    unfold toward
    rw [if_neg hne]
    exact max_eq_left (by push_cast; linarith [hle])
  rw [h1, h2]
  push_cast
  ring

/-- One unit step towards `q`. -/
theorem toward_step (p q : ℤ) {k : ℕ} (hk : k < (q - p).natAbs) :
    toward p q (k + 1) = toward p q k + 1 ∨ toward p q (k + 1) = toward p q k - 1 := by
  by_cases h : p ≤ q
  · exact Or.inl (toward_step_up h hk)
  · exact Or.inr (toward_step_down (not_le.mp h).le hk)

theorem toward_eq_of_le_natAbs {p q : ℤ} (h : p ≤ q) {k : ℕ} (hk : (q - p).natAbs ≤ k) :
    toward p q k = q := by
  have hnat : (((q - p).natAbs : ℤ)) = q - p := Int.natAbs_of_nonneg (by omega)
  have h1 : (((q - p).natAbs : ℤ)) ≤ (k : ℤ) := by exact_mod_cast hk
  unfold toward
  rw [if_pos h]
  refine le_antisymm (min_le_right _ _) (le_min ?_ le_rfl)
  linarith [h1, hnat]

theorem toward_eq_of_le_natAbs' {p q : ℤ} (h : q ≤ p) {k : ℕ} (hk : (q - p).natAbs ≤ k) :
    toward p q k = q := by
  by_cases hpq : p ≤ q
  · have hpq' : p = q := le_antisymm hpq h
    subst hpq'
    exact toward_eq_of_le_natAbs le_rfl hk
  have hnat : (((q - p).natAbs : ℤ)) = p - q := by
    have h3 : q - p = -(p - q) := by ring
    have h4 : (q - p).natAbs = (p - q).natAbs := by rw [h3, Int.natAbs_neg]
    rw [h4, Int.natAbs_of_nonneg (by omega : (0:ℤ) ≤ p - q)]
  have h1 : (((q - p).natAbs : ℤ)) ≤ (k : ℤ) := by exact_mod_cast hk
  unfold toward
  rw [if_neg hpq]
  refine le_antisymm (max_le ?_ le_rfl) (le_max_right _ _)
  linarith [h1, hnat]

/-! ### The staircase on `ℤ × ℤ` -/

/-- The number of steps of the monotone staircase from `p` to `q`. -/
def slen (p q : ℤ × ℤ) : ℕ := (q.1 - p.1).natAbs + (q.2 - p.2).natAbs

/-- The vertices of the monotone staircase from `p` to `q`: first the `x`-coordinate moves,
then the `y`-coordinate. -/
def svec (p q : ℤ × ℤ) (k : ℕ) : ℤ × ℤ :=
  (toward p.1 q.1 (min k (q.1 - p.1).natAbs), toward p.2 q.2 (k - (q.1 - p.1).natAbs))

theorem svec_zero (p q : ℤ × ℤ) : svec p q 0 = p := by
  have h1 : min 0 (q.1 - p.1).natAbs = 0 := Nat.zero_min _
  have h2 : 0 - (q.1 - p.1).natAbs = 0 := Nat.zero_sub _
  simp only [svec, h1, h2, toward_zero]

theorem svec_slen (p q : ℤ × ℤ) : svec p q (slen p q) = q := by
  have hM : (q.1 - p.1).natAbs ≤ slen p q := Nat.le_add_right _ _
  have hsub : slen p q - (q.1 - p.1).natAbs = (q.2 - p.2).natAbs := Nat.add_sub_cancel_left _ _
  simp only [svec, hsub, Nat.min_eq_right hM, toward_natAbs]

theorem svec_fst_mem (p q : ℤ × ℤ) (k : ℕ) :
    min p.1 q.1 ≤ (svec p q k).1 ∧ (svec p q k).1 ≤ max p.1 q.1 :=
  toward_mem_Icc p.1 q.1 _

theorem svec_snd_mem (p q : ℤ × ℤ) (k : ℕ) :
    min p.2 q.2 ≤ (svec p q k).2 ∧ (svec p q k).2 ≤ max p.2 q.2 :=
  toward_mem_Icc p.2 q.2 _

theorem svec_fst_of_le (p q : ℤ × ℤ) {k : ℕ} (hk : (q.1 - p.1).natAbs ≤ k) :
    (svec p q k).1 = q.1 := by
  simp only [svec, Nat.min_eq_right hk, toward_natAbs]

theorem svec_fst_step (p q : ℤ × ℤ) {k : ℕ} (hk : k < (q.1 - p.1).natAbs) :
    (svec p q (k + 1)).1 = (svec p q k).1 + 1 ∨ (svec p q (k + 1)).1 = (svec p q k).1 - 1 := by
  have h1 : min (k + 1) (q.1 - p.1).natAbs = k + 1 := Nat.min_eq_left (Nat.succ_le_of_lt hk)
  have h2 : min k (q.1 - p.1).natAbs = k := Nat.min_eq_left (le_of_lt hk)
  simp only [svec, h1, h2]
  exact toward_step _ _ hk

theorem svec_snd_step (p q : ℤ × ℤ) {k : ℕ} (hM : (q.1 - p.1).natAbs ≤ k)
    (hk : k - (q.1 - p.1).natAbs < (q.2 - p.2).natAbs) :
    (svec p q (k + 1)).2 = (svec p q k).2 + 1 ∨ (svec p q k).2 = (svec p q (k + 1)).2 + 1 := by
  have hsub : k + 1 - (q.1 - p.1).natAbs = (k - (q.1 - p.1).natAbs) + 1 := by omega
  have hstep := toward_step p.2 q.2 hk
  simp only [svec, hsub]
  rcases hstep with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

/-- Successive vertices of the staircase are `GridStep`-adjacent. -/
theorem svec_step (p q : ℤ × ℤ) {k : ℕ} (hk : k < slen p q) :
    GridStep (svec p q k) (svec p q (k + 1)) := by
  by_cases h : k < (q.1 - p.1).natAbs
  · -- moving in `x`: the second coordinate does not change
    have hk1 : k - (q.1 - p.1).natAbs = 0 := Nat.sub_eq_zero_of_le (le_of_lt h)
    have hk2 : k + 1 - (q.1 - p.1).natAbs = 0 := Nat.sub_eq_zero_of_le h
    have hsnd : (svec p q k).2 = (svec p q (k + 1)).2 := by
      simp only [svec, hk1, hk2]
    refine Or.inr ⟨hsnd, ?_⟩
    rcases svec_fst_step p q h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (by omega)
  · -- moving in `y`: the first coordinate is already `q.1`
    have hle : (q.1 - p.1).natAbs ≤ k := not_lt.mp h
    have hkn : k - (q.1 - p.1).natAbs < (q.2 - p.2).natAbs := by
      have hs : slen p q = (q.1 - p.1).natAbs + (q.2 - p.2).natAbs := rfl
      have hk' : k < (q.1 - p.1).natAbs + (q.2 - p.2).natAbs := by rw [← hs]; exact hk
      have h1 : (q.1 - p.1).natAbs + (k - (q.1 - p.1).natAbs) < (q.1 - p.1).natAbs
          + (q.2 - p.2).natAbs := by
        rw [Nat.add_sub_cancel' hle]; exact hk'
      exact Nat.add_lt_add_iff_left.mp h1
    have hfst : (svec p q k).1 = (svec p q (k + 1)).1 := by
      rw [svec_fst_of_le p q hle, svec_fst_of_le p q (by omega)]
    exact Or.inl ⟨hfst, svec_snd_step p q hle hkn⟩

/-! ### Metric bounds -/

theorem abs_sub_le_of_mem_Icc {p s u : ℤ} (h1 : min p s ≤ u) (h2 : u ≤ max p s) :
    |u - p| ≤ |s - p| := by
  by_cases h : p ≤ s
  · rw [min_eq_left h] at h1
    rw [max_eq_right h] at h2
    have h3 : (0:ℤ) ≤ u - p := by omega
    have h4 : u - p ≤ s - p := by omega
    have h5 : (0:ℤ) ≤ s - p := by omega
    calc |u - p| = u - p := abs_of_nonneg h3
      _ ≤ s - p := h4
      _ = |s - p| := (abs_of_nonneg h5).symm
  · have hsp : s ≤ p := (not_le.mp h).le
    rw [min_eq_right hsp] at h1
    rw [max_eq_left hsp] at h2
    have h3 : u - p ≤ 0 := by omega
    have h4 : p - u ≤ p - s := by omega
    have h5 : (0:ℤ) ≤ p - s := by omega
    calc |u - p| = -(u - p) := abs_of_nonpos h3
      _ = p - u := by ring
      _ ≤ p - s := h4
      _ = -(s - p) := by ring
      _ = |s - p| := (abs_of_nonpos (by omega : s - p ≤ 0)).symm

theorem gpt_sub (p q : ℤ × ℤ) :
    gpt q - gpt p = ((q.1 - p.1 : ℤ) : ℂ) + ((q.2 - p.2 : ℤ) : ℂ) * Complex.I := by
  rw [gpt, gpt]
  push_cast
  ring

theorem norm_add_mul_I_le {x y x' y' : ℝ} (hx : |x| ≤ |x'|) (hy : |y| ≤ |y'|) :
    ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ≤ ‖(x' : ℂ) + (y' : ℂ) * Complex.I‖ := by
  have e1 : ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ^ 2 = x ^ 2 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  have e2 : ‖(x' : ℂ) + (y' : ℂ) * Complex.I‖ ^ 2 = x' ^ 2 + y' ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
  have hs : ‖(x : ℂ) + (y : ℂ) * Complex.I‖ ^ 2 ≤ ‖(x' : ℂ) + (y' : ℂ) * Complex.I‖ ^ 2 := by
    rw [e1, e2]
    nlinarith [sq_le_sq.mpr hx, sq_le_sq.mpr hy]
  have h := sq_le_sq.mp hs
  rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h

/-- Every vertex of the staircase from `p` to `q` is at least as close to `p` as `q` is. -/
theorem svec_gpt_dist_le (c : ℝ) (hc : 0 ≤ c) (p q : ℤ × ℤ) (k : ℕ) :
    ‖(c : ℂ) * (gpt (svec p q k) - gpt p)‖ ≤ ‖(c : ℂ) * (gpt q - gpt p)‖ := by
  have hre : |(((svec p q k).1 - p.1 : ℤ) : ℝ)| ≤ |((q.1 - p.1 : ℤ) : ℝ)| := by
    have h := abs_sub_le_of_mem_Icc (p := p.1) (s := q.1) (u := (svec p q k).1)
      (svec_fst_mem p q k).1 (svec_fst_mem p q k).2
    exact_mod_cast h
  have him : |(((svec p q k).2 - p.2 : ℤ) : ℝ)| ≤ |((q.2 - p.2 : ℤ) : ℝ)| := by
    have h := abs_sub_le_of_mem_Icc (p := p.2) (s := q.2) (u := (svec p q k).2)
      (svec_snd_mem p q k).1 (svec_snd_mem p q k).2
    exact_mod_cast h
  have h1 : (c : ℂ) * (gpt (svec p q k) - gpt p)
      = (c : ℂ) * ((((svec p q k).1 - p.1 : ℤ) : ℂ) + (((svec p q k).2 - p.2 : ℤ) : ℂ)
          * Complex.I) := by
    rw [gpt_sub]
  have h2 : (c : ℂ) * (gpt q - gpt p)
      = (c : ℂ) * (((q.1 - p.1 : ℤ) : ℂ) + ((q.2 - p.2 : ℤ) : ℂ) * Complex.I) := by
    rw [gpt_sub]
  rw [h1, h2, norm_mul, norm_mul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  exact norm_add_mul_I_le hre him

end

end Work.Smooth.JordanSeparation
