import Mathlib
import Submission.Work.SphereJordan.ladder_macro
import Submission.Work.Smooth.JordanSeparation.gridWalk_approx
import Submission.Work.Smooth.JordanSeparation.lwalk_peel

/-!
# The ladder walk

Given a continuous map `g : unitInterval → ℂ` (the realization of a loop), a mesh `c > 0` and a
sequence `lad : ℕ → ℤ × ℤ` of lattice points approximating `g` at the points `t k` of a partition,
this file builds the **ladder walk**: the closed lattice walk of `LWalk` whose `k`-th block is the
macro `mac (lad (k+1) - lad k)` of exactly twelve unit steps, so that the walk runs through
`lad k` at the index `k * 12`.

* `dl lad k = lad (k+1) - lad k` — the displacement of the `k`-th block;
* `ladderV lad` — the vertex function (the index schedule `bo` converts an index of the walk into a
  block index and an offset);
* `ladderWalk` — the walk itself;
* `ladderWalk_pt_block` — the walk passes through `c * gpt (lad k)` at index `k * 12`;
* `ladderWalk_pt_lt`, `ladderWalk_pt_succ_lt` — the vertices of the `k`-th block are within `δ` of
  `g (t k)`;
* `ladderWalk_trace` — the trace of the walk lies in `U`.
-/

namespace Work.SphereJordan

open Set Metric
open Work.Smooth.JordanSeparation

noncomputable section

/-! ## Elementary geometry of `gpt` -/

theorem gpt_add (p q : ℤ × ℤ) : gpt (p + q) = gpt p + gpt q := by
  simp only [gpt, Prod.fst_add, Prod.snd_add]
  push_cast
  ring

/-- The norm of `gpt p` is bounded by the sum of the absolute values of the coordinates. -/
theorem norm_gpt_le (p : ℤ × ℤ) : ‖gpt p‖ ≤ |(p.1 : ℝ)| + |(p.2 : ℝ)| := by
  have h := Complex.norm_le_abs_re_add_abs_im (gpt p)
  have h1 : (gpt p).re = (p.1 : ℝ) := by
    simp [gpt, Complex.add_re, Complex.mul_re]
  have h2 : (gpt p).im = (p.2 : ℝ) := by
    simp [gpt, Complex.add_im, Complex.mul_im]
  rwa [h1, h2] at h

/-- The distance from `gpt p` to a point `w : ℂ`, bounded by the coordinate differences. -/
theorem norm_gpt_sub_le (p : ℤ × ℤ) (w : ℂ) :
    ‖gpt p - w‖ ≤ |(p.1 : ℝ) - w.re| + |(p.2 : ℝ) - w.im| := by
  have h := Complex.norm_le_abs_re_add_abs_im (gpt p - w)
  have h1 : (gpt p - w).re = (p.1 : ℝ) - w.re := by
    simp [gpt, Complex.sub_re, Complex.add_re, Complex.mul_re]
  have h2 : (gpt p - w).im = (p.2 : ℝ) - w.im := by
    simp [gpt, Complex.sub_im, Complex.add_im, Complex.mul_im]
  rwa [h1, h2] at h

/-- The rounding error, in the scaled lattice: `‖gpt (snap z) - z‖ ≤ 2`. -/
theorem norm_gpt_snap_sub_le (z : ℂ) : ‖gpt (snap z) - z‖ ≤ 2 := by
  have h := norm_gpt_sub_le (snap z) z
  have h1 : |((snap z).1 : ℝ) - z.re| ≤ 1 := by
    rw [abs_sub_comm]; exact snap_re z
  have h2 : |((snap z).2 : ℝ) - z.im| ≤ 1 := by
    rw [abs_sub_comm]; exact snap_im z
  linarith

/-- Multiplying by the mesh, in norms. -/
theorem norm_mul_mesh {c : ℝ} (hc : 0 < c) (z : ℂ) : ‖c * z‖ = c * ‖z‖ := by
  rw [norm_mul, show ‖(c : ℂ)‖ = c from by simp [abs_of_pos hc]]

/-! ## The displacement of a block, and the walk -/

/-- The displacement of the `k`-th block of the ladder. -/
def dl (lad : ℕ → ℤ × ℤ) (k : ℕ) : ℤ × ℤ := lad (k + 1) - lad k

/-- The vertex function of the ladder walk: the index `m` is read as a block index `(bo m).1` and
an offset `(bo m).2`. -/
def ladderV (lad : ℕ → ℤ × ℤ) (m : ℕ) : ℤ × ℤ :=
  lad ((bo m).1) + mac (dl lad ((bo m).1)) ((bo m).2)

theorem ladderV_zero (lad : ℕ → ℤ × ℤ) : ladderV lad 0 = lad 0 := by
  simp only [ladderV, bo_zero, mac_zero, add_zero]

/-- The block index of the `m`-th vertex is at most `N` for `m ≤ 12 * N`. -/
theorem bo_fst_le_of_le (m N : ℕ) (hm : m ≤ 12 * N) : (bo m).1 ≤ N := by
  rw [bo_eq_div]; omega

theorem bo_fst_lt_of_lt (m N : ℕ) (hm : m < 12 * N) : (bo m).1 < N := by
  rw [bo_eq_div]; omega

theorem bo_succ_fst (m : ℕ) : (bo (m + 1)).1 = (bo m).1 ∨ (bo (m + 1)).1 = (bo m).1 + 1 := by
  rw [bo]
  split_ifs with h
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem natAbs_le_of_abs_le {z : ℤ} (h : |z| ≤ 6) : z.natAbs ≤ 6 := by
  rw [Int.abs_eq_natAbs] at h
  exact_mod_cast h

theorem natAbs_sum_le {q : ℤ × ℤ} (h1 : |q.1| ≤ 6) (h2 : |q.2| ≤ 6) :
    q.1.natAbs + q.2.natAbs ≤ 12 := by
  have ha := natAbs_le_of_abs_le h1
  have hb := natAbs_le_of_abs_le h2
  omega

variable {lad : ℕ → ℤ × ℤ} {N : ℕ}

/-- **The ladder walk has unit lattice steps.** -/
theorem ladderV_step (hq : ∀ k ≤ N, |(dl lad k).1| ≤ 6 ∧ |(dl lad k).2| ≤ 6)
    (hp1 : ∀ k ≤ N, (dl lad k).1.natAbs % 2 = 0)
    (hp2 : ∀ k ≤ N, (dl lad k).2.natAbs % 2 = 0)
    {m : ℕ} (hm : m < 12 * N) : GridStep (ladderV lad m) (ladderV lad (m + 1)) := by
  have hk : (bo m).1 < N := bo_fst_lt_of_lt m N hm
  have hk' : (bo m).1 ≤ N := le_of_lt hk
  have hj : (bo m).2 ≤ 11 := bo_snd_le m
  have hsum : (dl lad ((bo m).1)).1.natAbs + (dl lad ((bo m).1)).2.natAbs ≤ 12 :=
    natAbs_sum_le (hq _ hk').1 (hq _ hk').2
  have hpe1 : (dl lad ((bo m).1)).1.natAbs % 2 = 0 := hp1 _ hk'
  have hpe2 : (dl lad ((bo m).1)).2.natAbs % 2 = 0 := hp2 _ hk'
  by_cases h : (bo m).2 + 1 = 12
  · -- the last step of a block: the walk moves on to the next ladder point
    have hbo1 : (bo (m + 1)).1 = (bo m).1 + 1 := by rw [bo, if_pos h]
    have hbo2 : (bo (m + 1)).2 = 0 := by rw [bo, if_pos h]
    have hj11 : (bo m).2 = 11 := by omega
    have hmac : mac (dl lad ((bo m).1)) 12 = dl lad ((bo m).1) := mac_twelve hsum
    have hg := gridStep_add (lad ((bo m).1))
      (mac_step hsum hpe1 hpe2 (j := (bo m).2) (by omega))
    have hdl : lad ((bo m).1) + dl lad ((bo m).1) = lad ((bo m).1 + 1) := by
      simp only [dl]
      ring
    rw [hj11, show (11 : ℕ) + 1 = 12 from rfl, hmac, hdl] at hg
    have hgoal : ladderV lad (m + 1) = lad ((bo m).1 + 1) := by
      simp only [ladderV, hbo1, hbo2, mac_zero, add_zero]
    rw [hgoal, ladderV, hj11]
    exact hg
  · -- a step inside a block
    have hbo1 : (bo (m + 1)).1 = (bo m).1 := by rw [bo, if_neg h]
    have hbo2 : (bo (m + 1)).2 = (bo m).2 + 1 := by rw [bo, if_neg h]
    have hlt : (bo m).2 < 12 := by omega
    rw [ladderV, ladderV, hbo1, hbo2]
    exact gridStep_add (lad ((bo m).1)) (mac_step hsum hpe1 hpe2 hlt)

/-- **The ladder walk is closed**, provided the ladder is. -/
theorem ladderV_closed (hclosed : lad N = lad 0) : ladderV lad (12 * N) = ladderV lad 0 := by
  rw [ladderV_zero, ladderV, bo_twelve_mul, mac_zero, add_zero, hclosed]

/-- **The ladder walk.** -/
def ladderWalk (N : ℕ) (c : ℝ) (hc : 0 < c) (lad : ℕ → ℤ × ℤ)
    (hq : ∀ k ≤ N, |(dl lad k).1| ≤ 6 ∧ |(dl lad k).2| ≤ 6)
    (hp1 : ∀ k ≤ N, (dl lad k).1.natAbs % 2 = 0)
    (hp2 : ∀ k ≤ N, (dl lad k).2.natAbs % 2 = 0)
    (hclosed : lad N = lad 0) : LWalk where
  n := 12 * N
  c := c
  cpos := hc
  v := ladderV lad
  step := fun k hk => ladderV_step hq hp1 hp2 hk
  closed := ladderV_closed hclosed

/-- The walk passes through the lattice point `lad k` at index `k * 12`. -/
theorem ladderWalk_pt_block {c : ℝ} {hc : 0 < c}
    {hq : ∀ k ≤ N, |(dl lad k).1| ≤ 6 ∧ |(dl lad k).2| ≤ 6}
    {hp1 : ∀ k ≤ N, (dl lad k).1.natAbs % 2 = 0}
    {hp2 : ∀ k ≤ N, (dl lad k).2.natAbs % 2 = 0}
    {hclosed : lad N = lad 0} {k : ℕ} (hk : k ≤ N) :
    (ladderWalk N c hc lad hq hp1 hp2 hclosed).pt (12 * k) = c * gpt (lad k) := by
  show c * gpt (ladderV lad (12 * k)) = c * gpt (lad k)
  rw [ladderV, bo_twelve_mul, mac_zero, add_zero]

/-- The value of `ptMin` before the end of the walk. -/
theorem ptMin_val_of_le {U : Set ℂ} (W : LWalk) (hval : ∀ t, W.path t ∈ U) {k : ℕ}
    (hk : k ≤ W.n) : ((W.ptMin hval k : ↥U) : ℂ) = W.pt k := by
  rw [LWalk.ptMin_apply, Nat.min_eq_left hk]

/-- The rounding error of the ladder, in the ambient space. -/
theorem norm_pt_lad_le {g : unitInterval → ℂ} {t : ℕ → unitInterval} {c : ℝ} (hc : 0 < c)
    {lad : ℕ → ℤ × ℤ} {k : ℕ} (hlad : lad k = snap (g (t k) / (c : ℂ))) :
    ‖c * gpt (lad k) - g (t k)‖ ≤ 2 * c := by
  have hround : ‖gpt (lad k) - g (t k) / (c : ℂ)‖ ≤ 2 := by
    have h := norm_gpt_snap_sub_le (g (t k) / (c : ℂ))
    rwa [← hlad] at h
  have hcne : ((c : ℝ) : ℂ) ≠ 0 := by simp [Complex.ofReal_eq_zero, ne_of_gt hc]
  have hfac : c * (gpt (lad k) - g (t k) / (c : ℂ)) = c * gpt (lad k) - g (t k) := by
    rw [mul_sub, ← mul_div_assoc, mul_div_cancel_left₀ _ hcne]
  rw [← hfac, norm_mul_mesh hc]
  nlinarith

/-- **The walk passes close to the ladder point at each block boundary.** -/
theorem ladderWalk_pt_block_le {g : unitInterval → ℂ} {t : ℕ → unitInterval} {c : ℝ} (hc : 0 < c)
    {lad : ℕ → ℤ × ℤ} {N : ℕ} (hlad : ∀ k ≤ N, lad k = snap (g (t k) / (c : ℂ)))
    {hq : ∀ k ≤ N, |(dl lad k).1| ≤ 6 ∧ |(dl lad k).2| ≤ 6}
    {hp1 : ∀ k ≤ N, (dl lad k).1.natAbs % 2 = 0}
    {hp2 : ∀ k ≤ N, (dl lad k).2.natAbs % 2 = 0}
    {hclosed : lad N = lad 0} {k : ℕ} (hk : k ≤ N) :
    ‖(ladderWalk N c hc lad hq hp1 hp2 hclosed).pt (12 * k) - g (t k)‖ ≤ 2 * c := by
  rw [ladderWalk_pt_block hk]
  exact norm_pt_lad_le hc (hlad k hk)

/-! ## The geometry of the ladder walk -/

/-- **The vertices of the walk are close to the corresponding point of `g`.** -/
theorem ladderWalk_pt_le {g : unitInterval → ℂ} {t : ℕ → unitInterval} {c : ℝ} (hc : 0 < c)
    (hlad : ∀ k ≤ N, lad k = snap (g (t k) / (c : ℂ)))
    {hq : ∀ k ≤ N, |(dl lad k).1| ≤ 6 ∧ |(dl lad k).2| ≤ 6}
    {hp1 : ∀ k ≤ N, (dl lad k).1.natAbs % 2 = 0}
    {hp2 : ∀ k ≤ N, (dl lad k).2.natAbs % 2 = 0}
    {hclosed : lad N = lad 0} {m : ℕ} (hm : m ≤ 12 * N) :
    ‖(ladderWalk N c hc lad hq hp1 hp2 hclosed).pt m - g (t (bo m).1)‖
      ≤ 15 * c := by
  have hk : (bo m).1 ≤ N := bo_fst_le_of_le m N hm
  have hmac : |(mac (dl lad ((bo m).1)) ((bo m).2)).1| ≤ 7 ∧
      |(mac (dl lad ((bo m).1)) ((bo m).2)).2| ≤ 6 :=
    mac_bound (hq _ hk).1 (hq _ hk).2 _
  have hround : ‖gpt (lad ((bo m).1)) - g (t (bo m).1) / (c : ℂ)‖ ≤ 2 := by
    have h := norm_gpt_snap_sub_le (g (t (bo m).1) / (c : ℂ))
    rwa [← hlad ((bo m).1) hk] at h
  have h1 : ‖c * gpt (lad ((bo m).1)) - g (t (bo m).1)‖ ≤ 2 * c := by
    have hcne : ((c : ℝ) : ℂ) ≠ 0 := by simp [Complex.ofReal_eq_zero, ne_of_gt hc]
    have hfac : c * (gpt (lad ((bo m).1)) - g (t (bo m).1) / (c : ℂ))
        = c * gpt (lad ((bo m).1)) - g (t (bo m).1) := by
      rw [mul_sub, ← mul_div_assoc, mul_div_cancel_left₀ _ hcne]
    rw [← hfac, norm_mul_mesh hc]
    nlinarith
  have h2 : ‖c * gpt (mac (dl lad ((bo m).1)) ((bo m).2))‖ ≤ 13 * c := by
    rw [norm_mul_mesh hc]
    have h := norm_gpt_le (mac (dl lad ((bo m).1)) ((bo m).2))
    have hc1 : |(((mac (dl lad ((bo m).1)) ((bo m).2)).1 : ℤ) : ℝ)| ≤ 7 := by
      rw [← Int.cast_abs]; exact_mod_cast hmac.1
    have hc2 : |(((mac (dl lad ((bo m).1)) ((bo m).2)).2 : ℤ) : ℝ)| ≤ 6 := by
      rw [← Int.cast_abs]; exact_mod_cast hmac.2
    have hle : ‖gpt (mac (dl lad ((bo m).1)) ((bo m).2))‖ ≤ 13 := by linarith
    calc c * ‖gpt (mac (dl lad ((bo m).1)) ((bo m).2))‖ ≤ c * 13 :=
          mul_le_mul_of_nonneg_left hle (le_of_lt hc)
      _ = 13 * c := by ring
  have hsplit : (ladderWalk N c hc lad hq hp1 hp2 hclosed).pt m
      = c * gpt (lad ((bo m).1)) + c * gpt (mac (dl lad ((bo m).1)) ((bo m).2)) := by
    show c * gpt (ladderV lad m) = _
    rw [ladderV, gpt_add, mul_add]
  rw [hsplit,
    show c * gpt (lad ((bo m).1)) + c * gpt (mac (dl lad ((bo m).1)) ((bo m).2))
        - g (t (bo m).1)
      = (c * gpt (lad ((bo m).1)) - g (t (bo m).1))
        + c * gpt (mac (dl lad ((bo m).1)) ((bo m).2)) from by ring]
  linarith [norm_add_le (c * gpt (lad ((bo m).1)) - g (t (bo m).1))
    (c * gpt (mac (dl lad ((bo m).1)) ((bo m).2))), h1, h2]

end

end Work.SphereJordan
