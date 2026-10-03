import Mathlib
import Submission.Work.Peluse.PET.boxNormPow_control_linear
import Submission.Work.Peluse.Peel.windowSum_block_transfer
import Submission.Work.Peluse.Peel.arithIcc_sum_window_eq
import Submission.Work.Peluse.BoxNormDilation.dilated_directions_ge
import Submission.Work.Peluse.Track.diag_collapse_cs
import Submission.Work.Peluse.Peel.windowSum_block_le

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse.PetLinear

noncomputable section

/-! ## Elementary helpers -/

/-- Membership in `symIcc N = [-N,N]`, expressed with `Int.natAbs`. -/
lemma mem_symIcc_natAbs {N : ℕ} {x : ℤ} : x ∈ Work.Peluse.symIcc N ↔ x.natAbs ≤ N := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩
    have h : |x| ≤ (N : ℤ) := abs_le.mpr ⟨h1, h2⟩
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  · intro hx
    have h : (x.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hx
    rw [Int.natCast_natAbs] at h
    exact abs_le.mp h

/-- The complement of `symIcc L` is described by `L < x.natAbs`. -/
lemma natAbs_lt_of_not_mem_symIcc {L : ℕ} {x : ℤ} (hx : x ∉ Work.Peluse.symIcc L) :
    L < x.natAbs := by
  by_contra hle
  exact hx (mem_symIcc_natAbs.mpr (by omega))

/-- A function supported in `[-N,N]` (in the `natAbs` sense) vanishes off the `Finset`. -/
lemma off_symIcc_eq_zero {N : ℕ} {f : ℤ → ℂ} (h : Work.Peluse.SupportIn f N) :
    ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → f x = 0 := fun x hx =>
  h x (lt_of_not_ge fun hle => hx (mem_symIcc_natAbs.mpr hle))

/-- **The support-vanishing used twice below.**  If `ψ` vanishes off `[-N,N]` and
`N + H|c| < |x|`, then every term of the `c`-arithmetic-progression window of length `H` based at `x`
vanishes: `ψ (x + c y) = 0` for `1 ≤ y ≤ H`. -/
lemma supportIn_arithIcc_shift {N H : ℕ} {c : ℤ} {ψ : ℤ → ℂ}
    (hsup : ∀ z : ℤ, z ∉ Work.Peluse.symIcc N → ψ z = 0)
    {x : ℤ} (hx : N + H * c.natAbs < x.natAbs) {y : ℕ} (hy : y ≤ H) :
    ψ (x + c * (y : ℤ)) = 0 := by
  refine hsup _ (fun hmem => ?_)
  have hle : (x + c * (y : ℤ)).natAbs ≤ N := mem_symIcc_natAbs.mp hmem
  have huabs : ((N + H * c.natAbs : ℕ) : ℤ) < |x| := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hx
  have hdy : |c * (y : ℤ)| ≤ ((H * c.natAbs : ℕ) : ℤ) := by
    rw [abs_mul]
    have hy' : |(y : ℤ)| ≤ (H : ℤ) := by
      rw [abs_of_nonneg (by positivity : (0 : ℤ) ≤ (y : ℤ))]
      exact_mod_cast hy
    have hc' : |c| = (c.natAbs : ℤ) := (Int.natCast_natAbs c).symm
    have hcast : (H : ℤ) * (c.natAbs : ℤ) = ((H * c.natAbs : ℕ) : ℤ) := by
      push_cast
      ring
    calc |c| * |(y : ℤ)| ≤ |c| * (H : ℤ) := mul_le_mul_of_nonneg_left hy' (abs_nonneg c)
      _ = (c.natAbs : ℤ) * (H : ℤ) := by rw [hc']
      _ = (H : ℤ) * (c.natAbs : ℤ) := by ring
      _ = ((H * c.natAbs : ℕ) : ℤ) := hcast
  have htri : |x| ≤ |x + c * (y : ℤ)| + |c * (y : ℤ)| := by
    calc |x| = |(x + c * (y : ℤ)) + (-(c * (y : ℤ)))| := by ring_nf
      _ ≤ |x + c * (y : ℤ)| + |-(c * (y : ℤ))| := abs_add_le _ _
      _ = |x + c * (y : ℤ)| + |c * (y : ℤ)| := by rw [abs_neg]
  have hcast2 : ((N + H * c.natAbs : ℕ) : ℤ) = (N : ℤ) + ((H * c.natAbs : ℕ) : ℤ) := by
    push_cast
    ring
  have h1 : (N : ℤ) < ((x + c * (y : ℤ)).natAbs : ℤ) := by
    rw [Int.natCast_natAbs]
    linarith [huabs, hdy, htri, hcast2]
  have h2 : N < (x + c * (y : ℤ)).natAbs := by exact_mod_cast h1
  omega

/-! ## Block transfer for complex window sums -/

/-- **Block transfer for complex window sums with an arbitrary step.**  The squared `M`-window sums
over `[-N,N]` are dominated by the squared `H`-window sums over the enlarged window
`[-N-H|d|, N+H|d|]`, plus one window's worth of error (`H² · #[-N,N]`), with the constants
`2(M/H+1)²` and `2(M/H+1)`.

The factor `2` is harmless downstream (it only enters the final constant); the mechanism is the
block decomposition of `[1,M]` into `M/H` blocks of length `H` plus a remainder, Cauchy–Schwarz,
and the support of the short window sums. -/
theorem windowSum_complex_block_le_aux {N M H : ℕ} (hH : 1 ≤ H) (hHM : H ≤ M) (d : ℤ)
    (ψ : ℤ → ℂ) (hsup : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → ψ x = 0)
    (hbd : ∀ x : ℤ, ‖ψ x‖ ≤ 1) :
    (∑ x ∈ Work.Peluse.symIcc N, ‖∑ y ∈ Finset.Icc 1 M, ψ (x + d * (y : ℤ))‖ ^ 2)
      ≤ 2 * (((M / H + 1 : ℕ)) : ℝ) ^ 2
          * (∑ x ∈ Work.Peluse.symIcc (N + H * d.natAbs),
              ‖∑ y ∈ Finset.Icc 1 H, ψ (x + d * (y : ℤ))‖ ^ 2)
        + 2 * (((M / H + 1 : ℕ)) : ℝ) * (H : ℝ) ^ 2
            * ((Work.Peluse.symIcc N).card : ℝ) := by
  classical
  set q : ℕ := M / H with hq
  set r : ℕ := M % H with hr
  have hMH : M = q * H + r := by
    rw [hq, hr]
    calc M = H * (M / H) + M % H := (Nat.div_add_mod M H).symm
      _ = M / H * H + M % H := by rw [Nat.mul_comm]
  have hrH : r < H := by rw [hr]; exact Nat.mod_lt M (by omega)
  have hqK : (((M / H + 1 : ℕ)) : ℝ) = (q : ℝ) + 1 := by
    rw [hq]
    push_cast
    ring
  let W : ℕ → ℤ → ℂ := fun T x => ∑ y ∈ Finset.Icc 1 T, ψ (x + d * (y : ℤ))
  -- ### Step 1: the block decomposition, pointwise
  have hblocks : ∀ x : ℤ, (∑ y ∈ Finset.Icc 1 M, ψ (x + d * (y : ℤ)))
      = (∑ j ∈ Finset.range q, W H (x + d * ((j * H : ℕ) : ℤ)))
        + W r (x + d * ((q * H : ℕ) : ℤ)) := by
    intro x
    have hsplit : (∑ z ∈ Finset.Icc 1 (q * H), ψ (x + d * (z : ℤ)))
        + (∑ z ∈ Finset.Icc (q * H + 1) M, ψ (x + d * (z : ℤ)))
        = ∑ z ∈ Finset.Icc 1 M, ψ (x + d * (z : ℤ)) := by
      rw [← Finset.Ico_add_one_right_eq_Icc (1 : ℕ) (q * H),
        ← Finset.Ico_add_one_right_eq_Icc (q * H + 1) M,
        ← Finset.Ico_add_one_right_eq_Icc (1 : ℕ) M]
      exact Finset.sum_Ico_consecutive (fun z : ℕ => ψ (x + d * (z : ℤ)))
        (by omega) (by omega)
    have hfirst : (∑ z ∈ Finset.Icc 1 (q * H), ψ (x + d * (z : ℤ)))
        = ∑ j ∈ Finset.range q, W H (x + d * ((j * H : ℕ) : ℤ)) := by
      rw [← Work.Peluse.Peel.sum_range_Icc_blocks q H (fun z : ℕ => ψ (x + d * (z : ℤ)))]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [← Work.Peluse.Peel.sum_Icc_add_const
        (fun z : ℕ => ψ (x + d * (z : ℤ))) (j * H) 1 H]
      show (∑ y ∈ Finset.Icc 1 H, ψ (x + d * ((j * H + y : ℕ) : ℤ)))
          = ∑ y ∈ Finset.Icc 1 H, ψ ((x + d * ((j * H : ℕ) : ℤ)) + d * (y : ℤ))
      refine Finset.sum_congr rfl (fun y _ => ?_)
      have harg : x + d * ((j * H + y : ℕ) : ℤ)
          = (x + d * ((j * H : ℕ) : ℤ)) + d * (y : ℤ) := by
        push_cast
        ring
      rw [harg]
    have hsecond : (∑ z ∈ Finset.Icc (q * H + 1) M, ψ (x + d * (z : ℤ)))
        = W r (x + d * ((q * H : ℕ) : ℤ)) := by
      rw [hMH]
      rw [← Work.Peluse.Peel.sum_Icc_add_const
        (fun z : ℕ => ψ (x + d * (z : ℤ))) (q * H) 1 r]
      show (∑ y ∈ Finset.Icc 1 r, ψ (x + d * ((q * H + y : ℕ) : ℤ)))
          = ∑ y ∈ Finset.Icc 1 r, ψ ((x + d * ((q * H : ℕ) : ℤ)) + d * (y : ℤ))
      refine Finset.sum_congr rfl (fun y _ => ?_)
      have harg : x + d * ((q * H + y : ℕ) : ℤ)
          = (x + d * ((q * H : ℕ) : ℤ)) + d * (y : ℤ) := by
        push_cast
        ring
      rw [harg]
    rw [← hsplit, hfirst, hsecond]
  -- ### Step 2: the pointwise Cauchy--Schwarz bound
  have hpoint : ∀ x : ℤ, ‖W M x‖ ^ 2
      ≤ 2 * (q : ℝ) * (∑ j ∈ Finset.range q, ‖W H (x + d * ((j * H : ℕ) : ℤ))‖ ^ 2)
        + 2 * ‖W r (x + d * ((q * H : ℕ) : ℤ))‖ ^ 2 := by
    intro x
    set a : ℝ := ‖∑ j ∈ Finset.range q, W H (x + d * ((j * H : ℕ) : ℤ))‖ with ha
    set b : ℝ := ‖W r (x + d * ((q * H : ℕ) : ℤ))‖ with hb
    set D : ℝ := ∑ j ∈ Finset.range q, ‖W H (x + d * ((j * H : ℕ) : ℤ))‖ ^ 2 with hD
    have hcs : a ^ 2 ≤ (q : ℝ) * D := by
      rw [ha, hD]
      simpa using Work.Peluse.Peel.norm_sum_sq_le_card_mul_sq (Finset.range q)
        (fun j => W H (x + d * ((j * H : ℕ) : ℤ)))
    have htri : ‖W M x‖ ≤ a + b := by
      show ‖(∑ y ∈ Finset.Icc 1 M, ψ (x + d * (y : ℤ)))‖ ≤ a + b
      rw [hblocks x, ha, hb]
      exact norm_add_le _ _
    calc ‖W M x‖ ^ 2 ≤ (a + b) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) htri 2
      _ ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
      _ ≤ 2 * ((q : ℝ) * D) + 2 * b ^ 2 := by nlinarith [hcs]
      _ = 2 * (q : ℝ) * D + 2 * b ^ 2 := by ring
  -- ### Step 3: summation in `x` and the shift of the short windows
  have hshift : ∀ j : ℕ,
      (∑ x ∈ Work.Peluse.symIcc N, ‖W H (x + d * ((j * H : ℕ) : ℤ))‖ ^ 2)
        ≤ ∑ x ∈ Work.Peluse.symIcc (N + H * d.natAbs), ‖W H x‖ ^ 2 := by
    intro j
    have hvanish : ∀ u : ℤ, u ∉ Work.Peluse.symIcc (N + H * d.natAbs) → ‖W H u‖ ^ 2 = 0 := by
      intro u hu
      have huN : N + H * d.natAbs < u.natAbs := natAbs_lt_of_not_mem_symIcc hu
      have hW0 : W H u = 0 := by
        show (∑ y ∈ Finset.Icc 1 H, ψ (u + d * (y : ℤ))) = 0
        refine Finset.sum_eq_zero (fun y hy => ?_)
        exact supportIn_arithIcc_shift hsup huN (Finset.mem_Icc.mp hy).2
      rw [hW0, norm_zero]
      norm_num
    have hinj : Set.InjOn (fun x : ℤ => x + d * ((j * H : ℕ) : ℤ))
        (↑(Work.Peluse.symIcc N) : Set ℤ) := by
      intro u hu v hv huv
      have huv' : u + d * ((j * H : ℕ) : ℤ) = v + d * ((j * H : ℕ) : ℤ) := huv
      exact (add_right_cancel_iff).mp huv'
    calc (∑ x ∈ Work.Peluse.symIcc N, ‖W H (x + d * ((j * H : ℕ) : ℤ))‖ ^ 2)
        = ∑ u ∈ (Work.Peluse.symIcc N).image (fun x : ℤ => x + d * ((j * H : ℕ) : ℤ)),
            ‖W H u‖ ^ 2 := by
          rw [Finset.sum_image (f := fun u : ℤ => ‖W H u‖ ^ 2) hinj]
      _ = ∑ u ∈ ((Work.Peluse.symIcc N).image (fun x : ℤ => x + d * ((j * H : ℕ) : ℤ)))
              ∩ Work.Peluse.symIcc (N + H * d.natAbs), ‖W H u‖ ^ 2 :=
          (Finset.sum_subset Finset.inter_subset_left
            (fun u hu hnot => hvanish u (fun hbig =>
              hnot (Finset.mem_inter.mpr ⟨hu, hbig⟩)))).symm
      _ ≤ ∑ u ∈ Work.Peluse.symIcc (N + H * d.natAbs), ‖W H u‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
            (fun u _ _ => by positivity)
  -- ### Step 4: the remainder window
  have herr : (∑ x ∈ Work.Peluse.symIcc N, ‖W r (x + d * ((q * H : ℕ) : ℤ))‖ ^ 2)
      ≤ (H : ℝ) ^ 2 * ((Work.Peluse.symIcc N).card : ℝ) := by
    have hbdr : ∀ u : ℤ, ‖W r u‖ ≤ (H : ℝ) := by
      intro u
      show ‖∑ y ∈ Finset.Icc 1 r, ψ (u + d * (y : ℤ))‖ ≤ (H : ℝ)
      calc ‖∑ y ∈ Finset.Icc 1 r, ψ (u + d * (y : ℤ))‖
          ≤ ∑ y ∈ Finset.Icc 1 r, ‖ψ (u + d * (y : ℤ))‖ := norm_sum_le _ _
        _ ≤ ∑ y ∈ Finset.Icc 1 r, (1 : ℝ) := Finset.sum_le_sum (fun y _ => hbd _)
        _ = (r : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one]
            congr 1
            rw [Nat.card_Icc]
            omega
        _ ≤ (H : ℝ) := by exact_mod_cast (le_of_lt hrH)
    calc (∑ x ∈ Work.Peluse.symIcc N, ‖W r (x + d * ((q * H : ℕ) : ℤ))‖ ^ 2)
        ≤ ∑ x ∈ Work.Peluse.symIcc N, (H : ℝ) ^ 2 :=
          Finset.sum_le_sum (fun x _ => pow_le_pow_left₀ (norm_nonneg _) (hbdr _) 2)
      _ = (H : ℝ) ^ 2 * ((Work.Peluse.symIcc N).card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
  -- ### Step 5: assembly
  have hSnn : (0 : ℝ) ≤ ∑ x ∈ Work.Peluse.symIcc (N + H * d.natAbs), ‖W H x‖ ^ 2 :=
    Finset.sum_nonneg (fun x _ => sq_nonneg _)
  have hCnn : (0 : ℝ) ≤ ((Work.Peluse.symIcc N).card : ℝ) := Nat.cast_nonneg _
  have hmain : (∑ x ∈ Work.Peluse.symIcc N, ‖W M x‖ ^ 2)
      ≤ 2 * (q : ℝ) * ((q : ℝ) * (∑ x ∈ Work.Peluse.symIcc (N + H * d.natAbs), ‖W H x‖ ^ 2))
        + 2 * ((H : ℝ) ^ 2 * ((Work.Peluse.symIcc N).card : ℝ)) := by
    calc (∑ x ∈ Work.Peluse.symIcc N, ‖W M x‖ ^ 2)
        ≤ ∑ x ∈ Work.Peluse.symIcc N,
            (2 * (q : ℝ) * (∑ j ∈ Finset.range q, ‖W H (x + d * ((j * H : ℕ) : ℤ))‖ ^ 2)
              + 2 * ‖W r (x + d * ((q * H : ℕ) : ℤ))‖ ^ 2) :=
          Finset.sum_le_sum (fun x _ => hpoint x)
      _ = 2 * (q : ℝ) * (∑ x ∈ Work.Peluse.symIcc N,
              ∑ j ∈ Finset.range q, ‖W H (x + d * ((j * H : ℕ) : ℤ))‖ ^ 2)
            + 2 * (∑ x ∈ Work.Peluse.symIcc N, ‖W r (x + d * ((q * H : ℕ) : ℤ))‖ ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = 2 * (q : ℝ) * (∑ j ∈ Finset.range q,
              ∑ x ∈ Work.Peluse.symIcc N, ‖W H (x + d * ((j * H : ℕ) : ℤ))‖ ^ 2)
            + 2 * (∑ x ∈ Work.Peluse.symIcc N, ‖W r (x + d * ((q * H : ℕ) : ℤ))‖ ^ 2) := by
          rw [Finset.sum_comm]
      _ ≤ 2 * (q : ℝ) * (∑ j ∈ Finset.range q,
              (∑ x ∈ Work.Peluse.symIcc (N + H * d.natAbs), ‖W H x‖ ^ 2))
            + 2 * ((H : ℝ) ^ 2 * ((Work.Peluse.symIcc N).card : ℝ)) := by
          refine add_le_add ?_ ?_
          · refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact Finset.sum_le_sum (fun j _ => hshift j)
          · exact mul_le_mul_of_nonneg_left herr (by norm_num)
      _ = 2 * (q : ℝ) * ((q : ℝ) * (∑ x ∈ Work.Peluse.symIcc (N + H * d.natAbs), ‖W H x‖ ^ 2))
            + 2 * ((H : ℝ) ^ 2 * ((Work.Peluse.symIcc N).card : ℝ)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hq1 : (0 : ℝ) ≤ (q : ℝ) + 1 := by positivity
  have hstep : 2 * (q : ℝ) * ((q : ℝ) * (∑ x ∈ Work.Peluse.symIcc (N + H * d.natAbs), ‖W H x‖ ^ 2))
        + 2 * ((H : ℝ) ^ 2 * ((Work.Peluse.symIcc N).card : ℝ))
      ≤ 2 * ((q : ℝ) + 1) ^ 2 * (∑ x ∈ Work.Peluse.symIcc (N + H * d.natAbs), ‖W H x‖ ^ 2)
        + 2 * ((q : ℝ) + 1) * (H : ℝ) ^ 2 * ((Work.Peluse.symIcc N).card : ℝ) := by
    have h1 : 2 * (q : ℝ) * ((q : ℝ) * (∑ x ∈ Work.Peluse.symIcc (N + H * d.natAbs), ‖W H x‖ ^ 2))
        ≤ 2 * ((q : ℝ) + 1) ^ 2 * (∑ x ∈ Work.Peluse.symIcc (N + H * d.natAbs), ‖W H x‖ ^ 2) := by
      nlinarith [hSnn, sq_nonneg ((q : ℝ) + 1), sq_nonneg (q : ℝ)]
    have h2 : 2 * ((H : ℝ) ^ 2 * ((Work.Peluse.symIcc N).card : ℝ))
        ≤ 2 * ((q : ℝ) + 1) * (H : ℝ) ^ 2 * ((Work.Peluse.symIcc N).card : ℝ) := by
      have hHc : (0 : ℝ) ≤ (H : ℝ) ^ 2 * ((Work.Peluse.symIcc N).card : ℝ) :=
        mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
      have h1 : (1 : ℝ) ≤ (q : ℝ) + 1 := by linarith
      have h3 := mul_le_mul_of_nonneg_right h1 hHc
      nlinarith [h3]
    linarith [h1, h2]
  rw [hqK]
  calc (∑ x ∈ Work.Peluse.symIcc N, ‖∑ y ∈ Finset.Icc 1 M, ψ (x + d * (y : ℤ))‖ ^ 2)
      ≤ 2 * (q : ℝ) * ((q : ℝ) * (∑ x ∈ Work.Peluse.symIcc (N + H * d.natAbs), ‖W H x‖ ^ 2))
        + 2 * ((H : ℝ) ^ 2 * ((Work.Peluse.symIcc N).card : ℝ)) := hmain
    _ ≤ 2 * ((q : ℝ) + 1) ^ 2 * (∑ x ∈ Work.Peluse.symIcc (N + H * d.natAbs), ‖W H x‖ ^ 2)
        + 2 * ((q : ℝ) + 1) * (H : ℝ) ^ 2 * ((Work.Peluse.symIcc N).card : ℝ) := hstep

/-! ## The level-one box-norm power as a window sum -/

/-- **The level-one box-norm power of a function supported in `[-N,N]` at the
arithmetic-progression shift set `c[1,H]` (`c ≠ 0`)**, as an explicit finite window sum. -/
theorem boxNormPow_one_arithIcc_window_aux {N H : ℕ} {c : ℤ} (hc : c ≠ 0) (hH : 1 ≤ H)
    {ψ : ℤ → ℂ} (hsup : Work.Peluse.SupportIn ψ N) :
    Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Work.Peluse.arithIcc c H) (Work.Peluse.symIcc N) ψ
      = ((Work.Peluse.symIcc N).card : ℝ)⁻¹ * ((H : ℝ))⁻¹ ^ 2
        * ∑ x ∈ Work.Peluse.symIcc (N + H * c.natAbs),
            ‖∑ y ∈ Finset.Icc 1 H, ψ (x + c * (y : ℤ))‖ ^ 2 := by
  rw [Work.Peluse.Peel.boxNormPow_one_tsum (N := N) (Work.Peluse.arithIcc c H)
    (Work.Peluse.symIcc N) hsup]
  have hcard : ((Work.Peluse.arithIcc c H).card : ℝ) = (H : ℝ) := by
    rw [Work.Peluse.BoxNormDilation.card_arithIcc hc H]
  rw [hcard]
  have hinner : ∀ x : ℤ, (∑ a ∈ Work.Peluse.arithIcc c H, ψ (x + a))
      = ∑ y ∈ Finset.Icc 1 H, ψ (x + c * (y : ℤ)) := by
    intro x
    rw [Work.Peluse.arithIcc, Finset.sum_image (Work.Peluse.Peel.injOn_arithIcc hc)]
  have htsum : (∑' x : ℤ, ‖∑ a ∈ Work.Peluse.arithIcc c H, ψ (x + a)‖ ^ 2)
      = ∑ x ∈ Work.Peluse.symIcc (N + H * c.natAbs),
          ‖∑ y ∈ Finset.Icc 1 H, ψ (x + c * (y : ℤ))‖ ^ 2 := by
    rw [tsum_congr (fun x => by rw [hinner x])]
    refine tsum_eq_sum (fun x hx => ?_)
    have hxN : N + H * c.natAbs < x.natAbs := natAbs_lt_of_not_mem_symIcc hx
    have hsum0 : (∑ y ∈ Finset.Icc 1 H, ψ (x + c * (y : ℤ))) = 0 :=
      Finset.sum_eq_zero (fun y hy =>
        supportIn_arithIcc_shift (off_symIcc_eq_zero hsup) hxN (Finset.mem_Icc.mp hy).2)
    rw [hsum0, norm_zero]
    norm_num
  rw [htsum]

/-! ## The core estimate -/

/-- **The mathematical core of `linear_boxnorm_control_one`.**  From a lower bound `γ` for the
linear bilinear average, the level-one box-norm power of the last function at the shifts
`c₁[⌊γ'M⌋]` is at least `γ/1000`.

The two constituent estimates are the Cauchy–Schwarz step `diag_collapse_cs` (which converts the
size of the average into an `ℓ²` bound for the `M`-window sums) and the block transfer
`windowSum_complex_block_le` (which replaces the `M`-windows by the `⌊γ'M⌋`-windows). -/
lemma core_one {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (c₁ : ℤ) (F0 Fm : ℤ → ℂ) {γ γ' : ℝ}
    (hγ : 0 < γ) (hγ' : 0 < γ') (hγ1 : γ ≤ 1)
    (hF0 : ∀ x, ‖F0 x‖ ≤ 1) (hFm : ∀ x, ‖Fm x‖ ≤ 1)
    (hS0 : Work.Peluse.SupportIn F0 N) (hSm : Work.Peluse.SupportIn Fm N)
    (hγ'le : γ' ≤ γ / 2000)
    (hval : 1 ≤ (⌊γ' * (M : ℝ)⌋).toNat)
    (hLam : γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F0 x *
        ∑ y ∈ Finset.Icc 1 M, Fm (x + c₁ * (y : ℤ))‖ ^ 2) :
    γ / 1000 ≤ Work.Peluse.boxNormPow 1
      (fun _ : Fin 1 => Work.Peluse.arithIcc c₁ (⌊γ' * (M : ℝ)⌋).toNat)
      (Work.Peluse.symIcc N) Fm := by
  set H : ℕ := (⌊γ' * (M : ℝ)⌋).toNat with hHdef
  have hH1 : 1 ≤ H := hval
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (show 0 < H by omega)
  have hHcast : ((H : ℕ) : ℝ) ≤ γ' * (M : ℝ) := by
    rw [hHdef, Int.floor_toNat]
    exact Nat.floor_le (le_of_lt (mul_pos hγ' hMpos))
  have hγ'2000 : γ' ≤ 1 / 2000 := by linarith
  have hHleM : H ≤ M := by
    have h1 : ((H : ℕ) : ℝ) ≤ (M : ℝ) := by
      have h2 : γ' * (M : ℝ) ≤ (1 / 2000) * (M : ℝ) :=
        mul_le_mul_of_nonneg_right hγ'2000 (le_of_lt hMpos)
      nlinarith [hHcast, h2, hMpos]
    exact_mod_cast h1
  by_cases hc₁ : c₁ = 0
  · -- #### Case `c₁ = 0`
    have harith0 : Work.Peluse.arithIcc c₁ H = ({0} : Finset ℤ) := by
      rw [hc₁]
      exact Work.Peluse.PET.control_linear_arithIcc_zero hH1
    have hW0 : ∀ x : ℤ, (∑ y ∈ Finset.Icc 1 M, Fm (x + c₁ * (y : ℤ))) = (M : ℂ) * Fm x := by
      intro x
      rw [hc₁]
      simp only [zero_mul, add_zero]
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : (Finset.Icc 1 M).card = M := by rw [Nat.card_Icc]; omega
      rw [hcard]
    have hW0' : (∑' x : ℤ, F0 x * (∑ y ∈ Finset.Icc 1 M, Fm (x + c₁ * (y : ℤ))))
        = ∑' x : ℤ, F0 x * ((M : ℂ) * Fm x) := tsum_congr (fun x => by rw [hW0 x])
    have hLam0 : γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F0 x * ((M : ℂ) * Fm x)‖ ^ 2 := by
      rw [hW0'] at hLam
      exact hLam
    have hcs := Work.Peluse.Track.diag_collapse_cs (N := N) (M := M) hN hM
      (F0 := F0) (W := fun x : ℤ => (M : ℂ) * Fm x) (γ := γ) hS0 hF0 hLam0
    have hsum_sq : (∑ x ∈ Work.Peluse.symIcc N, ‖(M : ℂ) * Fm x‖ ^ 2)
        = (M : ℝ) ^ 2 * ∑ x ∈ Work.Peluse.symIcc N, ‖Fm x‖ ^ 2 := by
      have h1 : ∀ x : ℤ, ‖(M : ℂ) * Fm x‖ ^ 2 = (M : ℝ) ^ 2 * ‖Fm x‖ ^ 2 := by
        intro x
        rw [norm_mul, Complex.norm_natCast, mul_pow]
      refine (Finset.sum_congr rfl (fun x _ => h1 x)).trans ?_
      exact (Finset.mul_sum _ _ _).symm
    rw [hsum_sq] at hcs
    have hM2pos : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
    have hTge : γ * (N : ℝ) ^ 2 ≤
        (2 * (N : ℝ) + 1) * ∑ x ∈ Work.Peluse.symIcc N, ‖Fm x‖ ^ 2 := by
      have hcs' : (γ * (N : ℝ) ^ 2) * (M : ℝ) ^ 2 ≤
          ((2 * (N : ℝ) + 1) * ∑ x ∈ Work.Peluse.symIcc N, ‖Fm x‖ ^ 2) * (M : ℝ) ^ 2 := by
        nlinarith [hcs]
      exact le_of_mul_le_mul_right hcs' hM2pos
    have hbox : Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Work.Peluse.arithIcc c₁ H)
        (Work.Peluse.symIcc N) Fm
        = ((Work.Peluse.symIcc N).card : ℝ)⁻¹ * ∑ x ∈ Work.Peluse.symIcc N, ‖Fm x‖ ^ 2 := by
      rw [Work.Peluse.Peel.boxNormPow_one_tsum (N := N) (Work.Peluse.arithIcc c₁ H)
        (Work.Peluse.symIcc N) hSm, harith0]
      have h2 : (∑' x : ℤ, ‖∑ a ∈ ({0} : Finset ℤ), Fm (x + a)‖ ^ 2)
          = ∑ x ∈ Work.Peluse.symIcc N, ‖Fm x‖ ^ 2 := by
        have hstep : ∀ x : ℤ, ‖∑ a ∈ ({0} : Finset ℤ), Fm (x + a)‖ ^ 2 = ‖Fm x‖ ^ 2 := by
          intro x
          rw [Finset.sum_singleton, add_zero]
        rw [tsum_congr hstep]
        exact tsum_eq_sum (fun x hx => by
          rw [off_symIcc_eq_zero hSm x hx, norm_zero]
          norm_num)
      rw [h2]
      simp only [Finset.card_singleton, Nat.cast_one, inv_one, one_pow, mul_one]
    have hAcard : ((Work.Peluse.symIcc N).card : ℝ) = 2 * (N : ℝ) + 1 := by
      rw [Work.Peluse.PET.card_symIcc]
      push_cast
      ring
    rw [hbox, hAcard, inv_mul_eq_div]
    have hpos : (0 : ℝ) < 2 * (N : ℝ) + 1 := by positivity
    have hN2 : (2 * (N : ℝ) + 1) ^ 2 / 1000 ≤ (N : ℝ) ^ 2 := by
      have h3 : 2 * (N : ℝ) + 1 ≤ 3 * (N : ℝ) := by linarith [hN1]
      have h5 : (2 * (N : ℝ) + 1) ^ 2 ≤ (3 * (N : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) h3 2
      nlinarith [h5, sq_nonneg (N : ℝ)]
    have hA1 : γ * (2 * (N : ℝ) + 1) / 1000
        ≤ γ * (N : ℝ) ^ 2 / (2 * (N : ℝ) + 1) := by
      rw [le_div_iff₀ hpos]
      nlinarith [hN2, hγ]
    have hA2 : γ * (N : ℝ) ^ 2 / (2 * (N : ℝ) + 1)
        ≤ ∑ x ∈ Work.Peluse.symIcc N, ‖Fm x‖ ^ 2 := by
      rw [div_le_iff₀ hpos]
      linarith [hTge]
    rw [le_div_iff₀ hpos]
    linarith [hA1, hA2]
  · -- #### Case `c₁ ≠ 0`
    let WM : ℤ → ℂ := fun x => ∑ y ∈ Finset.Icc 1 M, Fm (x + c₁ * (y : ℤ))
    let WH : ℤ → ℂ := fun x => ∑ y ∈ Finset.Icc 1 H, Fm (x + c₁ * (y : ℤ))
    let T : ℝ := ∑ x ∈ Work.Peluse.symIcc N, ‖WM x‖ ^ 2
    let S : ℝ := ∑ x ∈ Work.Peluse.symIcc (N + H * c₁.natAbs), ‖WH x‖ ^ 2
    let P : ℝ := Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Work.Peluse.arithIcc c₁ H)
      (Work.Peluse.symIcc N) Fm
    let K : ℝ := ((M / H + 1 : ℕ) : ℝ)
    have hAcard : ((Work.Peluse.symIcc N).card : ℝ) = 2 * (N : ℝ) + 1 := by
      rw [Work.Peluse.PET.card_symIcc]
      push_cast
      ring
    have hsupp : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → Fm x = 0 := off_symIcc_eq_zero hSm
    have hKpos : 0 < K := by
      show 0 < ((M / H + 1 : ℕ) : ℝ)
      positivity
    have hA : γ * (N : ℝ) ^ 2 * (M : ℝ) ^ 2 ≤ (2 * (N : ℝ) + 1) * T :=
      Work.Peluse.Track.diag_collapse_cs (N := N) (M := M) hN hM
        (F0 := F0) (W := WM) (γ := γ) hS0 hF0 hLam
    have hB : T ≤ 2 * K ^ 2 * S + 2 * K * (H : ℝ) ^ 2 * (2 * (N : ℝ) + 1) := by
      have h := windowSum_complex_block_le_aux (N := N) (M := M) (H := H) hH1 hHleM c₁ Fm hsupp hFm
      rw [hAcard] at h
      exact h
    have hC : P = ((Work.Peluse.symIcc N).card : ℝ)⁻¹ * ((H : ℝ))⁻¹ ^ 2 * S :=
      boxNormPow_one_arithIcc_window_aux (N := N) (H := H) (c := c₁) hc₁ hH1 hSm
    have hS_eq : S = (2 * (N : ℝ) + 1) * (H : ℝ) ^ 2 * P := by
      have hA2ne : (2 * (N : ℝ) + 1) * (H : ℝ) ^ 2 ≠ 0 := by positivity
      have h := hC
      rw [hAcard] at h
      have h2 : (2 * (N : ℝ) + 1)⁻¹ * (H : ℝ)⁻¹ ^ 2 * S
          = ((2 * (N : ℝ) + 1) * (H : ℝ) ^ 2)⁻¹ * S := by
        rw [mul_inv, inv_pow]
      rw [h2] at h
      rw [h]
      rw [← mul_assoc, mul_inv_cancel₀ hA2ne, one_mul]
    have hmain1 : γ * (N : ℝ) ^ 2 * (M : ℝ) ^ 2
        ≤ (2 * (N : ℝ) + 1) * (2 * K ^ 2 * S + 2 * K * (H : ℝ) ^ 2 * (2 * (N : ℝ) + 1)) :=
      le_trans hA (mul_le_mul_of_nonneg_left hB (by positivity))
    have hmain2 : γ * (N : ℝ) ^ 2 * (M : ℝ) ^ 2
        ≤ 2 * ((2 * (N : ℝ) + 1) ^ 2 * K ^ 2 * (H : ℝ) ^ 2) * P
          + 2 * ((2 * (N : ℝ) + 1) ^ 2 * K * (H : ℝ) ^ 2) := by
      have h := hmain1
      rw [hS_eq] at h
      nlinarith [h]
    have h1K : 1 / K ≤ γ' := by
      show 1 / ((M / H + 1 : ℕ) : ℝ) ≤ γ'
      have hMH : 1 / γ' ≤ (M : ℝ) / (H : ℝ) := by
        rw [div_le_div_iff₀ hγ' hHpos]
        linarith [hHcast]
      have hKgt : (M : ℝ) / (H : ℝ) < ((M / H + 1 : ℕ) : ℝ) := by
        rw [div_lt_iff₀ hHpos]
        have h1 : M < (M / H + 1) * H := by
          have hdiv : H * (M / H) + M % H = M := Nat.div_add_mod M H
          have hmod : M % H < H := Nat.mod_lt M (show 0 < H by omega)
          have hd : (M / H + 1) * H = H * (M / H) + H := by ring
          rw [hd]
          omega
        exact_mod_cast h1
      have hKge : 1 / γ' ≤ ((M / H + 1 : ℕ) : ℝ) := le_trans hMH (le_of_lt hKgt)
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < ((M / H + 1 : ℕ) : ℝ))]
      have h := hKge
      rw [div_le_iff₀ hγ'] at h
      linarith [h]
    have hcle : 2 * (N : ℝ) + 1 ≤ 3 * (N : ℝ) := by linarith [hN1]
    have hKH : K * (H : ℝ) ≤ 2 * (M : ℝ) := by
      show ((M / H + 1 : ℕ) : ℝ) * (H : ℝ) ≤ 2 * (M : ℝ)
      have h1 : (((M / H + 1 : ℕ)) : ℝ) * (H : ℝ) = (((M / H + 1) * H : ℕ) : ℝ) := by
        push_cast
        ring
      rw [h1]
      have h2 : (M / H + 1) * H ≤ 2 * M := by
        have h3 : (M / H) * H ≤ M := Nat.div_mul_le_self M H
        have hd : (M / H + 1) * H = (M / H) * H + H := by ring
        rw [hd]
        omega
      exact_mod_cast h2
    have hA2KH2 : (2 * (N : ℝ) + 1) ^ 2 * K ^ 2 * (H : ℝ) ^ 2
        ≤ 36 * (N : ℝ) ^ 2 * (M : ℝ) ^ 2 := by
      have h1 : (2 * (N : ℝ) + 1) ^ 2 ≤ (3 * (N : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hcle 2
      have h2 : (K * (H : ℝ)) ^ 2 ≤ (2 * (M : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hKH 2
      have h3 : (2 * (N : ℝ) + 1) ^ 2 * (K * (H : ℝ)) ^ 2
          ≤ (3 * (N : ℝ)) ^ 2 * (2 * (M : ℝ)) ^ 2 :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
      nlinarith [h3]
    have hA2KH2' : 2 * ((2 * (N : ℝ) + 1) ^ 2 * K ^ 2 * (H : ℝ) ^ 2)
        ≤ 72 * (N : ℝ) ^ 2 * (M : ℝ) ^ 2 := by
      nlinarith [hA2KH2]
    have hXpos : 0 < 2 * ((2 * (N : ℝ) + 1) ^ 2 * K ^ 2 * (H : ℝ) ^ 2) := by positivity
    have hmain3 : γ * (N : ℝ) ^ 2 * (M : ℝ) ^ 2
        ≤ (2 * ((2 * (N : ℝ) + 1) ^ 2 * K ^ 2 * (H : ℝ) ^ 2)) * (P + γ') := by
      have h1 : 1 ≤ K * γ' := by
        have h2 := h1K
        rw [div_le_iff₀ hKpos] at h2
        linarith [h2]
      have hY : 2 * ((2 * (N : ℝ) + 1) ^ 2 * K * (H : ℝ) ^ 2)
          ≤ (2 * ((2 * (N : ℝ) + 1) ^ 2 * K ^ 2 * (H : ℝ) ^ 2)) * γ' := by
        have hXeq : 2 * ((2 * (N : ℝ) + 1) ^ 2 * K ^ 2 * (H : ℝ) ^ 2)
            = K * (2 * ((2 * (N : ℝ) + 1) ^ 2 * K * (H : ℝ) ^ 2)) := by ring
        rw [hXeq]
        have hYnn : (0 : ℝ) ≤ 2 * ((2 * (N : ℝ) + 1) ^ 2 * K * (H : ℝ) ^ 2) := by positivity
        nlinarith [h1, hYnn]
      nlinarith [hmain2, hY]
    have hXinv : γ * (N : ℝ) ^ 2 * (M : ℝ) ^ 2
        / (2 * ((2 * (N : ℝ) + 1) ^ 2 * K ^ 2 * (H : ℝ) ^ 2)) ≤ P + γ' := by
      rw [div_le_iff₀ hXpos]
      nlinarith [hmain3]
    have h36 : γ / 72 ≤ γ * (N : ℝ) ^ 2 * (M : ℝ) ^ 2
        / (2 * ((2 * (N : ℝ) + 1) ^ 2 * K ^ 2 * (H : ℝ) ^ 2)) := by
      rw [le_div_iff₀ hXpos]
      have h := mul_le_mul_of_nonneg_left hA2KH2' (show (0 : ℝ) ≤ γ / 72 by positivity)
      nlinarith [h]
    have hnum : γ / 1000 ≤ γ / 72 - γ' := by linarith [hγ, hγ'2000]
    have hfinal : γ / 1000 ≤ P := by linarith [hXinv, h36, hnum]
    exact hfinal

end

/-! ## The target -/

theorem linear_boxnorm_control_one {m : ℕ} (hm : m = 1) :
    ∃ K : ℕ, 1 ≤ K ∧
      ∀ (c : Fin (m + 1) → ℤ), c 0 = 0 → ∀ {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
      (F : Fin (m + 1) → ℤ → ℂ) {γ γ' : ℝ}, 0 < γ → 0 < γ' → γ ≤ 1 →
      (∀ i x, ‖F i x‖ ≤ 1) → (∀ i, Work.Peluse.SupportIn (F i) N) →
      (∀ y ∈ Finset.Icc 1 M, ∀ i : Fin (m + 1), |c i * (y : ℤ)| ≤ (N : ℤ)) →
      γ' ≤ γ / (1000 * (m + 1)) → 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat →
      γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ ^ 2 →
      (γ / 1000) ^ K ≤ Work.Peluse.boxNormPow m
        (fun i : Fin m => Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc)
          (⌊γ' * (M : ℝ)⌋).toNat) (Work.Peluse.symIcc N) (F ⟨m, Nat.lt_succ_self m⟩) := by
  subst hm
  refine ⟨1, le_refl 1, ?_⟩
  intro c hc0 N M hN hM F γ γ' hγ hγ' hγ1 hF hFs hcy hγ'le hHge hLam
  rw [pow_one]
  have hQeq : (fun i : Fin 1 => Work.Peluse.arithIcc
        (c ⟨1, Nat.lt_succ_self 1⟩ - c i.castSucc) (⌊γ' * (M : ℝ)⌋).toNat)
      = fun _ : Fin 1 => Work.Peluse.arithIcc (c ⟨1, Nat.lt_succ_self 1⟩)
          (⌊γ' * (M : ℝ)⌋).toNat := by
    funext i
    have hcs : i.castSucc = (0 : Fin 2) := by
      apply Fin.ext
      show i.val = 0
      omega
    rw [hcs, hc0, sub_zero]
  have hprod : ∀ x : ℤ, (∑ y ∈ Finset.Icc 1 M, ∏ i : Fin 1, F i.succ (x + c i.succ * (y : ℤ)))
      = ∑ y ∈ Finset.Icc 1 M,
          F ⟨1, Nat.lt_succ_self 1⟩ (x + c ⟨1, Nat.lt_succ_self 1⟩ * (y : ℤ)) := by
    intro x
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Fin.prod_univ_one]
    have hs : (0 : Fin 1).succ = (⟨1, Nat.lt_succ_self 1⟩ : Fin 2) := by
      apply Fin.ext
      show (0 : Fin 1).val + 1 = 1
      simp
    rw [hs]
  have hγ'le' : γ' ≤ γ / 2000 := by
    norm_num at hγ'le
    exact hγ'le
  have hLamR : (∑' x : ℤ, F 0 x *
        (∑ y ∈ Finset.Icc 1 M, ∏ i : Fin 1, F i.succ (x + c i.succ * (y : ℤ))))
      = ∑' x : ℤ, F 0 x * (∑ y ∈ Finset.Icc 1 M,
          F ⟨1, Nat.lt_succ_self 1⟩ (x + c ⟨1, Nat.lt_succ_self 1⟩ * (y : ℤ))) :=
    tsum_congr (fun x => by rw [hprod x])
  have hLam' : γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
      ∑ y ∈ Finset.Icc 1 M,
        F ⟨1, Nat.lt_succ_self 1⟩ (x + c ⟨1, Nat.lt_succ_self 1⟩ * (y : ℤ))‖ ^ 2 := by
    rw [hLamR] at hLam
    exact hLam
  rw [hQeq]
  exact core_one (N := N) (M := M) (c₁ := c ⟨1, Nat.lt_succ_self 1⟩) (F0 := F 0)
    (Fm := F ⟨1, Nat.lt_succ_self 1⟩) hN hM hγ hγ' hγ1 (hF 0) (hF ⟨1, Nat.lt_succ_self 1⟩)
    (hFs 0) (hFs ⟨1, Nat.lt_succ_self 1⟩) hγ'le' hHge hLam'

end Work.Peluse.PetLinear
