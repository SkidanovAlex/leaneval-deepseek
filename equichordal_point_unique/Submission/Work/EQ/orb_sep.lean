import Mathlib
import Submission.Work.EQ.hetero_local
import Submission.Work.EQ.hetero_leaf
import Submission.Work.EQ.geom_sum_sq
import Submission.Work.EQ.geom_sum_kw
import Submission.Work.EQ.kpow_mul_pred
import Submission.Work.EQ.small_Cy_le
import Submission.Work.EQ.small_main
import Submission.Work.EQ.locA_pair_lip
import Submission.Work.EQ.locM_pair_lip

set_option maxHeartbeats 1000000

/-! The leaf-separation estimate for the two-step equichordal half-map `T = locT a`
(`Submission/Work/EQ/hetero_leaf.lean`): two orbits started at the same height with an initial
`x`-gap `D = x₂ - x₁ ≥ 0` keep an `x`-gap of at least `D/2` forever, as long as the starting
height is `LocData.Small`.

The proof is a joint strong induction on the time `n` for the two quantities
`S n = x₂-orbit minus x₁-orbit` and `E n = |y₂-orbit minus y₁-orbit|`:

* the `x`-displacement of one step is `locA`, so the gap changes by at most
  `C·Y₂²·S + C·(Y₁+Y₂)·E`; summed over all times this is
  `(4/3)·C·y²·D/(1-κ²) + 4·C²·y²·D/(1-κ²)²`;
* the height gap contracts by `κ` with the same kind of forcing, giving
  `E n ≤ 2·C·y·D·n·κ^{n-1}`.

The numeric input `(4/3)·C·y²/(1-κ²) + 4·C²·y²/(1-κ²)² ≤ 1/3` is `small_main`, and the
geometric sums are `geom_sum_sq` and `geom_sum_kw`. -/

namespace Work.EQ

open Finset

private theorem orb_fst_step {a : ℝ} (d : LocData a) {x y : ℝ} (hx : |x| ≤ 2 * d.ρ) (hy0 : 0 < y)
    (hyh : y ≤ d.h) (n : ℕ) :
    (LocData.orb a x y (n + 1)).1 = (LocData.orb a x y n).1 + locA a (LocData.orb a x y n) := by
  have h := (d.step (LocData.orb a x y n).1 (LocData.orb a x y n).2
    (d.orb_x_le x y hx hy0 hyh n) (d.orb_y_pos x y hx hy0 hyh n)
    (d.orb_y_le_h x y hx hy0 hyh n)).1
  rw [LocData.orb_succ]
  simpa using h

private theorem orb_snd_step {a : ℝ} (d : LocData a) {x y : ℝ} (hx : |x| ≤ 2 * d.ρ) (hy0 : 0 < y)
    (hyh : y ≤ d.h) (n : ℕ) :
    (LocData.orb a x y (n + 1)).2 = (LocData.orb a x y n).2 * locM a (LocData.orb a x y n) := by
  have h := (d.step (LocData.orb a x y n).1 (LocData.orb a x y n).2
    (d.orb_x_le x y hx hy0 hyh n) (d.orb_y_pos x y hx hy0 hyh n)
    (d.orb_y_le_h x y hx hy0 hyh n)).2.1
  rw [LocData.orb_succ]
  simpa using h

/-- **Leaf separation.** Two orbits of the two-step map `T = locT a` (`LocData.orb a x y n` is
the `n`-th iterate of `locT a` starting from `(x,y)`) that start at the same height `y` with
`x₁ ≤ x₂` keep `x`-coordinates apart by at least half of the initial gap `x₂ - x₁` at every time.

Proof sketch (constants are those of `Work.EQ.LocData`): put `D = x₂ - x₁`,
`S n = (LocData.orb a x₂ y n).1 - (LocData.orb a x₁ y n).1`,
`E n = |(LocData.orb a x₂ y n).2 - (LocData.orb a x₁ y n).2|`.  One step of `locT` is
`(x,y) ↦ (x + locA a (x,y), y * locM a (x,y))` (`LocData.step`) with `|locA| ≤ C y²`,
`0 < locM ≤ κ`, and `locA`, `locM` being `C·y²`- resp. `C`-Lipschitz in `x` and
`C(y₁+y₂)`- resp. `C`-Lipschitz in `y` (`LocData.lipX`, `LocData.lipY`), all on the box
`|x| ≤ 3ρ`; the orbit of a point with `|x| ≤ 2ρ` stays in that box with `y`-coordinate
`≤ κ^n * y` (`LocData.orb_x_le`, `LocData.orb_y_le`, `LocData.orb_y_le_h`).  Since the gaps see
total forcing `Σ_n C (Y n)² D + Σ_n C (Y n) E n = O(y² D)`, the joint induction
`D/2 ≤ S n ≤ 2D`, `E n ≤ (8C/κ) * y * D * (n+1) * κ^n` goes through; all it needs is that `y`
satisfies `LocData.Small y`. -/
theorem orb_sep {a : ℝ} (d : LocData a) {x₁ x₂ y : ℝ} (h1 : |x₁| ≤ 2 * d.ρ)
    (h2 : |x₂| ≤ 2 * d.ρ) (hxy : x₁ ≤ x₂) (hy0 : 0 < y) (hyh : y ≤ d.h) (hs : d.Small y) :
    ∀ n, (LocData.orb a x₂ y n).1 - (LocData.orb a x₁ y n).1 ≥ (x₂ - x₁) / 2 := by
  set D : ℝ := x₂ - x₁ with hD
  have hD0 : 0 ≤ D := by rw [hD]; linarith
  have hC0 : 0 < d.C := d.Cpos
  set K : ℝ := 2 * d.C * y * D with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hC0)) (le_of_lt hy0)) hD0
  have hκ0 : 0 < d.κ := d.κpos
  have hκ1 : d.κ < 1 := d.κlt
  have h1κ2 : 0 < 1 - d.κ ^ 2 := d.one_sub_sq_pos
  have h1κ : 0 < 1 - d.κ := by linarith
  have hkp : ∀ k : ℕ, (d.κ ^ k * y) ^ 2 = (d.κ ^ 2) ^ k * y ^ 2 := by
    intro k; rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm k 2]
  have hkpow : ∀ k : ℕ, d.κ ^ k * d.κ ^ (k - 1) = d.κ ^ (2 * k - 1) := by
    intro k
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
      rw [← pow_add]; congr 1; omega
  have hκm1κ : ∀ m : ℕ, d.κ ^ (m - 1) * d.κ ≤ d.κ ^ m := by
    intro m
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp only [Nat.reduceSub, pow_zero]; simpa using le_of_lt hκ1
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, pow_succ]
      exact le_rfl
  have hEkey : ∀ m : ℕ, d.C * y * ((m : ℝ) * d.κ ^ (m - 1)) ≤ 1 / 3 := by
    intro m
    have hA := small_Cy_le d hs
    have hB := kpow_mul_pred hκ0 hκ1 m
    have hB0 : 0 ≤ (m : ℝ) * d.κ ^ (m - 1) := by positivity
    have hC1 : 0 ≤ d.κ * (1 - d.κ) ^ 2 / 16 := by positivity
    have hmul := mul_le_mul hA hB hB0 hC1
    have hsimp : d.κ * (1 - d.κ) ^ 2 / 16 * (1 / (1 - d.κ)) ≤ 1 / 3 := by
      have heq : d.κ * (1 - d.κ) ^ 2 / 16 * (1 / (1 - d.κ)) = d.κ * (1 - d.κ) / 16 := by
        rw [one_div]
        field_simp
      rw [heq]
      nlinarith [d.κpos, d.κlt, sq_nonneg (d.κ - 1 / 2)]
    linarith
  have key : ∀ n, |(LocData.orb a x₂ y n).1 - (LocData.orb a x₁ y n).1 - D| ≤ D / 3 ∧
      |(LocData.orb a x₂ y n).2 - (LocData.orb a x₁ y n).2| ≤ K * (n : ℝ) * d.κ ^ (n - 1) := by
    intro n
    refine Nat.strong_induction_on n (fun n ih => ?_)
    constructor
    · -- ============ x-separation ============
      have hrec : ∀ k, (LocData.orb a x₂ y (k + 1)).1 - (LocData.orb a x₁ y (k + 1)).1
          - ((LocData.orb a x₂ y k).1 - (LocData.orb a x₁ y k).1)
          = locA a (LocData.orb a x₂ y k) - locA a (LocData.orb a x₁ y k) := by
        intro k
        rw [orb_fst_step d h2 hy0 hyh k, orb_fst_step d h1 hy0 hyh k]
        ring
      have hsumid : ∀ N : ℕ, (LocData.orb a x₂ y N).1 - (LocData.orb a x₁ y N).1 - D
          = ∑ k ∈ Finset.range N,
              (locA a (LocData.orb a x₂ y k) - locA a (LocData.orb a x₁ y k)) := by
        intro N
        induction N with
        | zero => simp [LocData.orb_zero, hD]
        | succ N ih =>
            rw [Finset.sum_range_succ, ← ih, ← hrec N]
            ring
      have htel := hsumid n
      have hbound : |(LocData.orb a x₂ y n).1 - (LocData.orb a x₁ y n).1 - D|
          ≤ ∑ k ∈ Finset.range n,
              (d.C * y ^ 2 * (4 * D / 3) * (d.κ ^ 2) ^ k
                + 4 * d.C ^ 2 * y ^ 2 * D * ((k : ℝ) * d.κ ^ (2 * k - 1))) := by
        rw [htel]
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
        intro k hk
        have hklt : k < n := Finset.mem_range.mp hk
        obtain ⟨ihS, ihE⟩ := ih k hklt
        have hSk0 : 0 ≤ (LocData.orb a x₂ y k).1 - (LocData.orb a x₁ y k).1 := by
          have := (abs_le.mp ihS).1; linarith
        have hSk4 : (LocData.orb a x₂ y k).1 - (LocData.orb a x₁ y k).1 ≤ 4 * D / 3 := by
          have := (abs_le.mp ihS).2; linarith
        have hSabs : |(LocData.orb a x₂ y k).1 - (LocData.orb a x₁ y k).1| ≤ 4 * D / 3 := by
          rw [abs_of_nonneg hSk0]; exact hSk4
        have hX1 : |(LocData.orb a x₁ y k).1| ≤ 3 * d.ρ := d.orb_x_le x₁ y h1 hy0 hyh k
        have hX2 : |(LocData.orb a x₂ y k).1| ≤ 3 * d.ρ := d.orb_x_le x₂ y h2 hy0 hyh k
        have hY10 : 0 < (LocData.orb a x₁ y k).2 := d.orb_y_pos x₁ y h1 hy0 hyh k
        have hY20 : 0 < (LocData.orb a x₂ y k).2 := d.orb_y_pos x₂ y h2 hy0 hyh k
        have hY1h : (LocData.orb a x₁ y k).2 ≤ d.h := d.orb_y_le_h x₁ y h1 hy0 hyh k
        have hY2h : (LocData.orb a x₂ y k).2 ≤ d.h := d.orb_y_le_h x₂ y h2 hy0 hyh k
        have hY1le : (LocData.orb a x₁ y k).2 ≤ d.κ ^ k * y := d.orb_y_le x₁ y h1 hy0 hyh k
        have hY2le : (LocData.orb a x₂ y k).2 ≤ d.κ ^ k * y := d.orb_y_le x₂ y h2 hy0 hyh k
        have hlip := locA_pair_lip d hX1 hX2 hY10 hY1h hY20 hY2h
        have hlip' : |locA a (LocData.orb a x₂ y k) - locA a (LocData.orb a x₁ y k)|
            ≤ d.C * (LocData.orb a x₂ y k).2 ^ 2
                * |(LocData.orb a x₂ y k).1 - (LocData.orb a x₁ y k).1|
              + d.C * ((LocData.orb a x₁ y k).2 + (LocData.orb a x₂ y k).2)
                * |(LocData.orb a x₂ y k).2 - (LocData.orb a x₁ y k).2| := by
          simpa using hlip
        have hE' : |(LocData.orb a x₂ y k).2 - (LocData.orb a x₁ y k).2|
            ≤ K * ((k : ℝ) * d.κ ^ (k - 1)) := by
          simpa [mul_assoc] using ihE
        have ht1 : d.C * (LocData.orb a x₂ y k).2 ^ 2
              * |(LocData.orb a x₂ y k).1 - (LocData.orb a x₁ y k).1|
            ≤ d.C * y ^ 2 * (4 * D / 3) * (d.κ ^ 2) ^ k := by
          have hY2sq : (LocData.orb a x₂ y k).2 ^ 2 ≤ (d.κ ^ 2) ^ k * y ^ 2 := by
            calc (LocData.orb a x₂ y k).2 ^ 2 ≤ (d.κ ^ k * y) ^ 2 :=
                  pow_le_pow_left₀ (le_of_lt hY20) hY2le 2
              _ = (d.κ ^ 2) ^ k * y ^ 2 := hkp k
          calc d.C * (LocData.orb a x₂ y k).2 ^ 2
                * |(LocData.orb a x₂ y k).1 - (LocData.orb a x₁ y k).1|
              ≤ d.C * ((d.κ ^ 2) ^ k * y ^ 2) * (4 * D / 3) := by
                exact mul_le_mul (mul_le_mul_of_nonneg_left hY2sq (le_of_lt hC0)) hSabs
                  (abs_nonneg _) (by positivity)
            _ = d.C * y ^ 2 * (4 * D / 3) * (d.κ ^ 2) ^ k := by ring
        have ht2 : d.C * ((LocData.orb a x₁ y k).2 + (LocData.orb a x₂ y k).2)
              * |(LocData.orb a x₂ y k).2 - (LocData.orb a x₁ y k).2|
            ≤ 4 * d.C ^ 2 * y ^ 2 * D * ((k : ℝ) * d.κ ^ (2 * k - 1)) := by
          have hsum : (LocData.orb a x₁ y k).2 + (LocData.orb a x₂ y k).2 ≤ 2 * (d.κ ^ k * y) := by
            linarith
          calc d.C * ((LocData.orb a x₁ y k).2 + (LocData.orb a x₂ y k).2)
                * |(LocData.orb a x₂ y k).2 - (LocData.orb a x₁ y k).2|
              ≤ d.C * (2 * (d.κ ^ k * y)) * (K * ((k : ℝ) * d.κ ^ (k - 1))) := by
                exact mul_le_mul (mul_le_mul_of_nonneg_left hsum (le_of_lt hC0)) hE'
                  (abs_nonneg _) (by positivity)
            _ = 4 * d.C ^ 2 * y ^ 2 * D * ((k : ℝ) * d.κ ^ (2 * k - 1)) := by
                rw [hK, ← hkpow k]; ring
        linarith [hlip', ht1, ht2]
      have hsumle : (∑ k ∈ Finset.range n,
              (d.C * y ^ 2 * (4 * D / 3) * (d.κ ^ 2) ^ k
                + 4 * d.C ^ 2 * y ^ 2 * D * ((k : ℝ) * d.κ ^ (2 * k - 1))))
          ≤ (4 / 3) * (d.C * y ^ 2) * D / (1 - d.κ ^ 2)
            + 4 * (d.C ^ 2 * y ^ 2) * D / (1 - d.κ ^ 2) ^ 2 := by
        rw [Finset.sum_add_distrib]
        rw [show (∑ k ∈ Finset.range n, d.C * y ^ 2 * (4 * D / 3) * (d.κ ^ 2) ^ k)
            = d.C * y ^ 2 * (4 * D / 3) * ∑ k ∈ Finset.range n, (d.κ ^ 2) ^ k from by
          rw [← Finset.mul_sum]]
        rw [show (∑ k ∈ Finset.range n,
              4 * d.C ^ 2 * y ^ 2 * D * ((k : ℝ) * d.κ ^ (2 * k - 1)))
            = 4 * d.C ^ 2 * y ^ 2 * D * ∑ k ∈ Finset.range n, ((k : ℝ) * d.κ ^ (2 * k - 1)) from by
          rw [← Finset.mul_sum]]
        have hg1 := geom_sum_sq (le_of_lt hκ0) hκ1 n
        have hg2 := geom_sum_kw (le_of_lt hκ0) hκ1 n
        have hc1 : 0 ≤ d.C * y ^ 2 * (4 * D / 3) := by positivity
        have hc2 : 0 ≤ 4 * d.C ^ 2 * y ^ 2 * D := by positivity
        have := add_le_add (mul_le_mul_of_nonneg_left hg1 hc1) (mul_le_mul_of_nonneg_left hg2 hc2)
        refine le_trans this (le_of_eq ?_)
        ring
      have hfinal : (4 / 3) * (d.C * y ^ 2) * D / (1 - d.κ ^ 2)
            + 4 * (d.C ^ 2 * y ^ 2) * D / (1 - d.κ ^ 2) ^ 2 ≤ D / 3 := by
        have h1' : D * ((4 / 3) * (d.C * y ^ 2) / (1 - d.κ ^ 2)
            + 4 * (d.C ^ 2 * y ^ 2) / (1 - d.κ ^ 2) ^ 2) ≤ D / 3 := by
          have := mul_le_mul_of_nonneg_left (small_main d hs) hD0
          have h3 : D * (1 / 3) = D / 3 := by ring
          linarith
        have h2' : D * ((4 / 3) * (d.C * y ^ 2) / (1 - d.κ ^ 2)
            + 4 * (d.C ^ 2 * y ^ 2) / (1 - d.κ ^ 2) ^ 2)
            = (4 / 3) * (d.C * y ^ 2) * D / (1 - d.κ ^ 2)
              + 4 * (d.C ^ 2 * y ^ 2) * D / (1 - d.κ ^ 2) ^ 2 := by ring
        linarith [h1', h2']
      linarith [hbound, hsumle, hfinal]
    · -- ============ y-contraction ============
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        simp [LocData.orb_zero]
      · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos hnpos).symm⟩
        have ihS := (ih m (Nat.lt_succ_self m)).1
        have ihE := (ih m (Nat.lt_succ_self m)).2
        have hSk0 : 0 ≤ (LocData.orb a x₂ y m).1 - (LocData.orb a x₁ y m).1 := by
          have := (abs_le.mp ihS).1; linarith
        have hSabs : |(LocData.orb a x₂ y m).1 - (LocData.orb a x₁ y m).1| ≤ 4 * D / 3 := by
          rw [abs_of_nonneg hSk0]
          have := (abs_le.mp ihS).2; linarith
        have hE' : |(LocData.orb a x₂ y m).2 - (LocData.orb a x₁ y m).2|
            ≤ K * ((m : ℝ) * d.κ ^ (m - 1)) := by
          simpa [mul_assoc] using ihE
        have hY1m0 : 0 < (LocData.orb a x₁ y m).2 := d.orb_y_pos x₁ y h1 hy0 hyh m
        have hY2m0 : 0 < (LocData.orb a x₂ y m).2 := d.orb_y_pos x₂ y h2 hy0 hyh m
        have hY1le : (LocData.orb a x₁ y m).2 ≤ d.κ ^ m * y := d.orb_y_le x₁ y h1 hy0 hyh m
        have hstepM := d.step (LocData.orb a x₂ y m).1 (LocData.orb a x₂ y m).2
            (d.orb_x_le x₂ y h2 hy0 hyh m) (d.orb_y_pos x₂ y h2 hy0 hyh m)
            (d.orb_y_le_h x₂ y h2 hy0 hyh m)
        have hM2pos : 0 < locM a (LocData.orb a x₂ y m) := by simpa using hstepM.2.2.2.1
        have hM2 : |locM a (LocData.orb a x₂ y m)| ≤ d.κ := by
          rw [abs_of_pos hM2pos]
          simpa using hstepM.2.2.2.2
        have hlipM := locM_pair_lip d (d.orb_x_le x₁ y h1 hy0 hyh m) (d.orb_x_le x₂ y h2 hy0 hyh m)
            hY1m0 (d.orb_y_le_h x₁ y h1 hy0 hyh m) hY2m0 (d.orb_y_le_h x₂ y h2 hy0 hyh m)
        have hlipM' : |locM a (LocData.orb a x₂ y m) - locM a (LocData.orb a x₁ y m)|
            ≤ d.C * |(LocData.orb a x₂ y m).1 - (LocData.orb a x₁ y m).1|
              + d.C * |(LocData.orb a x₂ y m).2 - (LocData.orb a x₁ y m).2| := by
          simpa using hlipM
        have hME : |locM a (LocData.orb a x₂ y m) - locM a (LocData.orb a x₁ y m)|
            ≤ d.C * (4 * D / 3) + d.C * (K * ((m : ℝ) * d.κ ^ (m - 1))) := by
          have h1 := mul_le_mul_of_nonneg_left hSabs (le_of_lt hC0)
          have h2 := mul_le_mul_of_nonneg_left hE' (le_of_lt hC0)
          linarith [hlipM', h1, h2]
        have hstepe : (LocData.orb a x₂ y (m + 1)).2
            = (LocData.orb a x₂ y m).2 * locM a (LocData.orb a x₂ y m) :=
          orb_snd_step d h2 hy0 hyh m
        have hstepe1 : (LocData.orb a x₁ y (m + 1)).2
            = (LocData.orb a x₁ y m).2 * locM a (LocData.orb a x₁ y m) :=
          orb_snd_step d h1 hy0 hyh m
        have hsplit : (LocData.orb a x₂ y (m + 1)).2 - (LocData.orb a x₁ y (m + 1)).2
            = ((LocData.orb a x₂ y m).2 - (LocData.orb a x₁ y m).2)
                * locM a (LocData.orb a x₂ y m)
              + (LocData.orb a x₁ y m).2
                * (locM a (LocData.orb a x₂ y m) - locM a (LocData.orb a x₁ y m)) := by
          rw [hstepe, hstepe1]; ring
        have hbound2 : |(LocData.orb a x₂ y (m + 1)).2 - (LocData.orb a x₁ y (m + 1)).2|
            ≤ K * ((m : ℝ) * d.κ ^ (m - 1)) * d.κ
              + (d.κ ^ m * y) * (d.C * (4 * D / 3)
                  + d.C * (K * ((m : ℝ) * d.κ ^ (m - 1)))) := by
          rw [hsplit]
          calc |((LocData.orb a x₂ y m).2 - (LocData.orb a x₁ y m).2)
                  * locM a (LocData.orb a x₂ y m)
                + (LocData.orb a x₁ y m).2
                  * (locM a (LocData.orb a x₂ y m) - locM a (LocData.orb a x₁ y m))|
              ≤ |((LocData.orb a x₂ y m).2 - (LocData.orb a x₁ y m).2)
                  * locM a (LocData.orb a x₂ y m)|
                + |(LocData.orb a x₁ y m).2
                  * (locM a (LocData.orb a x₂ y m) - locM a (LocData.orb a x₁ y m))| :=
                abs_add_le _ _
            _ = |(LocData.orb a x₂ y m).2 - (LocData.orb a x₁ y m).2|
                  * |locM a (LocData.orb a x₂ y m)|
                + |(LocData.orb a x₁ y m).2|
                  * |locM a (LocData.orb a x₂ y m) - locM a (LocData.orb a x₁ y m)| := by
                rw [abs_mul, abs_mul]
            _ ≤ K * ((m : ℝ) * d.κ ^ (m - 1)) * d.κ
                  + (d.κ ^ m * y) * (d.C * (4 * D / 3)
                      + d.C * (K * ((m : ℝ) * d.κ ^ (m - 1)))) := by
                apply add_le_add
                · exact mul_le_mul hE' hM2 (abs_nonneg _) (by positivity)
                · exact mul_le_mul (by rw [abs_of_pos hY1m0]; exact hY1le) hME
                    (abs_nonneg _) (by positivity)
        have harith : K * ((m : ℝ) * d.κ ^ (m - 1)) * d.κ
              + (d.κ ^ m * y) * (d.C * (4 * D / 3)
                  + d.C * (K * ((m : ℝ) * d.κ ^ (m - 1))))
            ≤ K * ((m : ℝ) + 1) * d.κ ^ m := by
          have hP : d.C * y * ((m : ℝ) * d.κ ^ (m - 1)) ≤ 1 / 3 := hEkey m
          have hk1 : d.κ ^ (m - 1) * d.κ ≤ d.κ ^ m := hκm1κ m
          have h1 : K * ((m : ℝ) * d.κ ^ (m - 1)) * d.κ ≤ K * ((m : ℝ) * d.κ ^ m) := by
            have := mul_le_mul_of_nonneg_left hk1 (show (0 : ℝ) ≤ (m : ℝ) by positivity)
            nlinarith [this]
          have h2 : d.κ ^ m * y * (d.C * (4 * D / 3)) = (2 / 3) * K * d.κ ^ m := by
            rw [hK]; ring
          have h3 : d.κ ^ m * y * (d.C * (K * ((m : ℝ) * d.κ ^ (m - 1))))
              ≤ (1 / 3) * K * d.κ ^ m := by
            have h4 : d.κ ^ m * y * (d.C * (K * ((m : ℝ) * d.κ ^ (m - 1))))
                = K * d.κ ^ m * (d.C * y * ((m : ℝ) * d.κ ^ (m - 1))) := by ring
            rw [h4]
            calc K * d.κ ^ m * (d.C * y * ((m : ℝ) * d.κ ^ (m - 1)))
                ≤ K * d.κ ^ m * (1 / 3) := mul_le_mul_of_nonneg_left hP (by positivity)
              _ = (1 / 3) * K * d.κ ^ m := by ring
          nlinarith [h1, h2, h3, hK0, hD0]
        have hgoal : |(LocData.orb a x₂ y (m + 1)).2 - (LocData.orb a x₁ y (m + 1)).2|
            ≤ K * ((m : ℝ) + 1) * d.κ ^ m := le_trans hbound2 harith
        simpa [Nat.cast_add, Nat.add_sub_cancel] using hgoal
  intro n
  have hSn := (key n).1
  have hge : D - D / 3 ≤ (LocData.orb a x₂ y n).1 - (LocData.orb a x₁ y n).1 := by
    have := (abs_le.mp hSn).1; linarith
  rw [hD] at hge ⊢
  linarith

end Work.EQ

