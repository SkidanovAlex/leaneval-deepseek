import Mathlib
import Submission.Commons.Analysis.DiscreteCZ.discrete_convolution_lp_bounded_large
import Submission.Commons.Analysis.Hilbert.radial_kernel_tsum_le_maximal
import Submission.Commons.Analysis.MeasureTheory.iSup_rpow_eq
import Submission.Commons.Analysis.Walsh.exists_khintchine_hilbert

/-!
# The `τ`-averaging identity for the shifted-dyadic ball kernels, and the decomposition of the
annulus kernel of the discrete Hilbert transform

This file is the **first stone of the "engine"** for the variational inequality
`Work.Analysis.Hilbert.hilbert_var_dyad_sq`: the exact kernel identity that lets the truncation walk
`k ↦ T_{2^k}f` be written, up to one explicit remainder, as an *average over shifted dyadic lattices
of martingale walks*.  Averaging over the shifts is what turns a non-martingale walk into a convex
combination of martingales, and `V^r` is convex; Lépingle's inequality (proved in this tree,
`Work.Analysis.Probability.lepingle_variation_lp_le`) then controls the martingale part.

## The two objects

* `shiftAtom k τ n` — the atom of the `τ`-shifted dyadic lattice of scale `2^k` (`τ ∈ [0,2^k)`)
  containing `0`, i.e. the interval `[-τ, -τ+2^k)`.  For fixed `τ` these atoms are nested in `k`,
  so `(E_k^τ)_k` is a filtration of `ℤ` and `shiftKernel k τ` is the kernel of `E_k^τ` (the
  normalized indicator of the atom containing `0`).
* `triKernel k n = max 0 ((2^k - |n|)/2^{2k})` — the triangular (Fejér) kernel of total mass `1`.

## Main results

* `shiftKernel_average` — **the identity**: the average of the shifted-dyadic ball kernels over a
  complete residue system of shifts `τ ∈ [0,2^k)` is the triangular kernel:
  `(∑_{τ ∈ [0,2^k)} shiftKernel k τ n) / 2^k = triKernel k n`.
* `annK_decomp` — the annulus kernel of the discrete Hilbert transform is the `τ`-averaged
  martingale difference `fejerDiff k = triKernel (k+1) - triKernel k` plus the **explicit
  sacrificed-mass remainder** `remKernel k`.
* `remKernel_eq_zero_of_large`, `remKernel_bound` — the remainder is supported in `|n| ≤ 2^{k+1}`
  and is `O(2^{-k})` pointwise.

## The route this opens

With `D_k f = annK k * f` the walk's increments and `G = ∑_k D_k f`, the identity gives
`D_k f = (fejerDiff k) * G + (remKernel k) * f`, where `(fejerDiff k) * G` is the `τ`-average of
the martingale differences `(E_{k+1}^τ - E_k^τ)G`.  So the walk is the average over `τ` of the
martingale walks `(E_k^τ G)_k` plus the remainder walk; convexity of `V^r` (a supremum of norms of
linear maps) reduces the first term to `‖G‖_{ℓᵖ}`, and the remaining work is the `L^p` cost of the
remainder walk — the "sacrificed mass" — together with the multi-scale (Carleson/Besicovitch)
bookkeeping.
-/

open Finset
open scoped BigOperators

namespace Work.Analysis.Hilbert

noncomputable section

/-! ## The shifted-dyadic ball kernels and their `τ`-average -/

/-- The atom of the `τ`-shifted dyadic lattice of scale `2^k` that contains `0`: the interval
`[-τ, -τ + 2^k)`.  (For `τ ∈ [0,2^k)` these are the atoms of the partition of `ℤ` into the cosets
of `2^kℤ` shifted by `-τ`.) -/
def shiftAtom (k : ℕ) (τ : ℤ) (n : ℤ) : Prop := -τ ≤ n ∧ n < -τ + (2:ℤ)^k

instance shiftAtom_dec (k : ℕ) (τ n : ℤ) : Decidable (shiftAtom k τ n) := by
  unfold shiftAtom; infer_instance

/-- The kernel of the `τ`-shifted dyadic conditional expectation at scale `2^k`, as a convolution
kernel on `ℤ`: the normalized indicator of the atom containing `0`. -/
def shiftKernel (k : ℕ) (τ : ℤ) (n : ℤ) : ℝ := by
  classical
  exact if shiftAtom k τ n then ((2:ℝ)^k)⁻¹ else 0

/-- The triangular (Fejér) kernel at scale `2^k`, of total mass `1`. -/
def triKernel (k : ℕ) (n : ℤ) : ℝ := max 0 (((2:ℝ)^k - |(n:ℝ)|) / (2:ℝ)^(2*k))

/-! ### Elementary arithmetic -/

lemma toNat_max_zero (c : ℤ) : (max 0 c).toNat = c.toNat := by
  by_cases h : 0 ≤ c
  · rw [max_eq_right h]
  · rw [max_eq_left (le_of_lt (not_le.mp h)), Int.toNat_zero,
      Int.toNat_of_nonpos (le_of_lt (not_le.mp h))]

lemma toNat_cast_max (c : ℤ) : ((max 0 c).toNat : ℝ) = max 0 (c : ℝ) := by
  have h : ((max 0 c).toNat : ℤ) = max 0 c := by
    rw [Int.toNat_eq_max]
    exact max_eq_left (le_max_left 0 c)
  calc ((max 0 c).toNat : ℝ) = (((max 0 c).toNat : ℤ) : ℝ) := by push_cast; ring
    _ = ((max 0 c : ℤ) : ℝ) := by rw [h]
    _ = max 0 (c : ℝ) := by rw [Int.cast_max, Int.cast_zero]

/-- Casting `n.natAbs` to `ℝ` gives `|n|`. -/
lemma natAbs_cast (n : ℤ) : ((n.natAbs : ℤ) : ℝ) = |(n:ℝ)| := by
  rcases lt_or_ge n 0 with h | h
  · have hn : (n.natAbs : ℤ) = -n := by
      rw [← Int.natAbs_neg n]; exact Int.natAbs_of_nonneg (by omega)
    rw [hn, abs_of_neg (by exact_mod_cast h)]
    push_cast; ring
  · have hn : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg h
    rw [hn, abs_of_nonneg (by exact_mod_cast h)]

lemma natAbs_cast_real (n : ℤ) : (n.natAbs : ℝ) = |(n:ℝ)| := by
  rw [← Int.cast_natCast, natAbs_cast]

lemma filter_eq_Ico_nonneg {k : ℕ} {n : ℤ} (hn : 0 ≤ n) :
    (Finset.Ico (0:ℤ) ((2:ℤ)^k)).filter (fun a => shiftAtom k a n)
      = Finset.Ico (0:ℤ) ((2:ℤ)^k - n) := by
  have hM : (0:ℤ) < (2:ℤ)^k := by positivity
  ext a
  rw [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ico, shiftAtom]
  constructor <;> intro h <;> omega

lemma filter_eq_Ico_neg {k : ℕ} {n : ℤ} (hn : n < 0) :
    (Finset.Ico (0:ℤ) ((2:ℤ)^k)).filter (fun a => shiftAtom k a n)
      = Finset.Ico (-n) ((2:ℤ)^k) := by
  have hM : (0:ℤ) < (2:ℤ)^k := by positivity
  ext a
  rw [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Ico, shiftAtom]
  constructor <;> intro h <;> omega

/-- The number of shifts `τ ∈ [0,2^k)` for which `n` lies in the atom containing `0` is
`max 0 (2^k - |n|)`. -/
lemma card_shiftAtom (k : ℕ) (n : ℤ) :
    ((Finset.Ico (0:ℤ) ((2:ℤ)^k)).filter (fun a => shiftAtom k a n)).card
      = (max 0 ((2:ℤ)^k - (n.natAbs : ℤ))).toNat := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [filter_eq_Ico_neg (k := k) hn, Int.card_Ico, toNat_max_zero]
    rw [show ((n.natAbs : ℤ)) = -n from by
      rw [← Int.natAbs_neg n]; exact Int.natAbs_of_nonneg (by omega)]
  · rw [filter_eq_Ico_nonneg (k := k) hn, Int.card_Ico, Int.natAbs_of_nonneg hn, toNat_max_zero]
    simp

lemma inv_sq (k : ℕ) : ((2:ℝ)^k)⁻¹ * ((2:ℝ)^k)⁻¹ = ((2:ℝ)^(2*k))⁻¹ := by
  rw [← mul_inv]
  congr 1
  rw [← pow_add]
  ring_nf

/-! ## The `τ`-averaging identity (the first stone) -/

/-- **The `τ`-averaging identity.**  The average of the shifted-dyadic ball (interval) kernels at
scale `2^k` over a complete residue system of shifts `τ ∈ [0,2^k)` is the triangular kernel at
scale `2^k`. -/
theorem shiftKernel_average (k : ℕ) (n : ℤ) :
    (∑ τ ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), shiftKernel k τ n) / (2:ℝ)^k = triKernel k n := by
  classical
  have hstep : ∀ τ : ℤ, shiftKernel k τ n
      = ((2:ℝ)^k)⁻¹ * (if shiftAtom k τ n then (1:ℝ) else 0) := by
    intro τ
    by_cases h : shiftAtom k τ n <;> simp [shiftKernel, h]
  rw [Finset.sum_congr rfl (fun τ _ => hstep τ)]
  rw [← Finset.mul_sum, ← Finset.sum_filter]
  rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [card_shiftAtom, toNat_cast_max]
  push_cast
  rw [triKernel, div_eq_mul_inv, div_eq_mul_inv, ← inv_sq k]
  rw [show ((2:ℝ)^k)⁻¹ * max 0 ((2:ℝ)^k - |(n:ℝ)|) * ((2:ℝ)^k)⁻¹
        = max 0 ((2:ℝ)^k - |(n:ℝ)|) * (((2:ℝ)^k)⁻¹ * ((2:ℝ)^k)⁻¹) by ring]
  rw [max_mul_of_nonneg 0 _ (by positivity : (0:ℝ) ≤ ((2:ℝ)^k)⁻¹ * ((2:ℝ)^k)⁻¹)]
  simp

/-! ## The martingale-difference kernel, the annulus decomposition, and the remainder -/

/-- The `τ`-averaged martingale difference at level `k`: the difference of the averaged low-pass
kernels at scales `2^{k+1}` and `2^k`. -/
def fejerDiff (k : ℕ) (n : ℤ) : ℝ := triKernel (k+1) n - triKernel k n

lemma triKernel_nonneg (k : ℕ) (n : ℤ) : 0 ≤ triKernel k n := le_max_left _ _

/-- The triangular kernel vanishes once `|n| ≥ 2^k`. -/
lemma triKernel_eq_zero_of_le {k : ℕ} {n : ℤ} (h : (2:ℝ)^k ≤ |(n:ℝ)|) :
    triKernel k n = 0 := by
  rw [triKernel, max_eq_left]
  apply div_nonpos_of_nonpos_of_nonneg
  · linarith
  · positivity

/-- `2^k / 2^{2k} = 2^{-k}`. -/
lemma pow_div_pow_pow (k : ℕ) : (2:ℝ)^k / (2:ℝ)^(2*k) = ((2:ℝ)^k)⁻¹ := by
  have h2 : (2:ℝ)^(2*k) = (2:ℝ)^k * (2:ℝ)^k := by
    rw [← pow_add]; congr 1; ring
  rw [h2, div_eq_mul_inv, mul_inv, ← mul_assoc]
  rw [mul_inv_cancel₀ (by positivity), one_mul]

/-- The triangular kernel at scale `2^k` is bounded by `2^{-k}`. -/
lemma triKernel_le (k : ℕ) (n : ℤ) : triKernel k n ≤ ((2:ℝ)^k)⁻¹ := by
  rw [triKernel]
  rcases lt_or_ge 0 (((2:ℝ)^k - |(n:ℝ)|) / (2:ℝ)^(2*k)) with h | h
  · rw [max_eq_right (le_of_lt h)]
    have hnum : ((2:ℝ)^k - |(n:ℝ)|) ≤ (2:ℝ)^k := by linarith [abs_nonneg (n:ℝ)]
    calc ((2:ℝ)^k - |(n:ℝ)|) / (2:ℝ)^(2*k) ≤ (2:ℝ)^k / (2:ℝ)^(2*k) :=
          div_le_div_of_nonneg_right hnum (by positivity)
      _ = ((2:ℝ)^k)⁻¹ := pow_div_pow_pow k
  · rw [max_eq_left h]
    positivity

/-- The triangular kernel at scale `2^{k+1}` is bounded by `2^{-k}`. -/
lemma triKernel_le_succ (k : ℕ) (n : ℤ) : triKernel (k+1) n ≤ ((2:ℝ)^k)⁻¹ := by
  refine le_trans (triKernel_le (k+1) n) ?_
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  exact pow_le_pow_right₀ (by norm_num) (by omega)

/-- The averaged martingale difference is bounded by `2^{-k}`. -/
lemma abs_fejerDiff_le (k : ℕ) (n : ℤ) : |fejerDiff k n| ≤ ((2:ℝ)^k)⁻¹ := by
  have h1 : 0 ≤ triKernel (k+1) n := triKernel_nonneg _ _
  have h2 : triKernel (k+1) n ≤ ((2:ℝ)^k)⁻¹ := triKernel_le_succ k n
  have h3 : 0 ≤ triKernel k n := triKernel_nonneg _ _
  have h4 : triKernel k n ≤ ((2:ℝ)^k)⁻¹ := triKernel_le k n
  rw [fejerDiff, abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- If `2^m < |n|` as integers then `2^m < |n|` in `ℝ`. -/
lemma cast_two_pow_lt_natAbs {m : ℕ} {n : ℤ} (h : (2:ℤ)^m < n.natAbs) :
    (2:ℝ)^m < |(n:ℝ)| := by
  have h1 : (2:ℝ)^m < (n.natAbs : ℝ) := by exact_mod_cast h
  rwa [natAbs_cast_real] at h1


/-! ## Stone 1: the τ-averaged conditional expectations are the triangular smoothing

`shiftExp k τ g` is the `τ`-shifted dyadic conditional expectation `E_k^τ g` written as an explicit
atom average on `ℤ` (the mean of `g` over the atom of the `τ`-shifted lattice of scale `2^k`
containing the point).  `shiftExp_eq_sum` identifies it with the convolution by the ball kernel
`shiftKernel k τ`, and `shiftExp_average` is the **operator-level averaging identity**: the sum over
a complete residue system of the shifts `τ` is `2^k` times the triangular smoothing of `g`,
`∑_{τ} E_k^τ g = 2^k · (triKernel k * g)`.  Hence `(triKernel k * g)_k` is the average of the
martingale walks `(E_k^τ g)_k`, and Jensen for the convex functional `V^r` plus Lépingle bounds its
`ℓᵖ` variation by `C ‖g‖_{ℓᵖ}`.
-/

/-- The `τ`-shifted dyadic conditional expectation as an explicit atom average on `ℤ`. -/
def shiftExp (k : ℕ) (τ : ℤ) (g : ℤ → ℂ) (n : ℤ) : ℂ :=
  ((2:ℂ)^k)⁻¹ * ∑ d ∈ Finset.Ico (-τ) (-τ + (2:ℤ)^k), g (n - d)

lemma shiftKernel_eq_inv {k : ℕ} {τ d : ℤ} (hd : d ∈ Finset.Ico (-τ) (-τ + (2:ℤ)^k)) :
    shiftKernel k τ d = ((2:ℝ)^k)⁻¹ := by
  classical
  rw [shiftKernel, if_pos]
  exact ⟨(Finset.mem_Ico.mp hd).1, (Finset.mem_Ico.mp hd).2⟩

lemma shiftKernel_eq_zero_of_notMem {k : ℕ} {τ d : ℤ} (_hτ : τ < (2:ℤ)^k)
    (_hd : -(2:ℤ)^k ≤ d ∧ d ≤ (2:ℤ)^k) (h : d ∉ Finset.Ico (-τ) (-τ + (2:ℤ)^k)) :
    shiftKernel k τ d = 0 := by
  classical
  rw [shiftKernel, if_neg]
  rintro ⟨h1, h2⟩
  exact h (Finset.mem_Ico.mpr ⟨h1, h2⟩)

lemma cast_inv_pow (k : ℕ) : Complex.ofReal (((2:ℝ)^k)⁻¹) = ((2:ℂ)^k)⁻¹ := by
  norm_num

/-- **The convolution identification**: the `τ`-shifted conditional expectation is the convolution
with the ball kernel `shiftKernel k τ`. -/
lemma shiftExp_eq_sum (k : ℕ) {τ : ℤ} (h0 : 0 ≤ τ) (hτ : τ < (2:ℤ)^k) (g : ℤ → ℂ) (n : ℤ) :
    shiftExp k τ g n
      = ∑ d ∈ Finset.Icc (-((2:ℤ)^k)) ((2:ℤ)^k), shiftKernel k τ d * g (n - d) := by
  classical
  have hsub : Finset.Ico (-τ) (-τ + (2:ℤ)^k) ⊆ Finset.Icc (-((2:ℤ)^k)) ((2:ℤ)^k) := by
    intro d hd
    rw [Finset.mem_Ico] at hd
    rw [Finset.mem_Icc]
    omega
  have hcongr : ∑ d ∈ Finset.Ico (-τ) (-τ + (2:ℤ)^k), shiftKernel k τ d * g (n - d)
      = ∑ d ∈ Finset.Ico (-τ) (-τ + (2:ℤ)^k), ((2:ℂ)^k)⁻¹ * g (n - d) := by
    refine Finset.sum_congr rfl (fun d hd => ?_)
    rw [shiftKernel_eq_inv hd, cast_inv_pow]
  rw [shiftExp, Finset.mul_sum, ← hcongr, Finset.sum_subset hsub]
  intro d hd hnot
  rw [shiftKernel_eq_zero_of_notMem hτ (Finset.mem_Icc.mp hd) hnot]
  simp

/-- **Stone 1, the averaging identity**: the sum of the `τ`-shifted dyadic conditional expectations
over a complete residue system of shifts is `2^k` times the triangular smoothing of `g`. -/
theorem shiftExp_average (k : ℕ) (g : ℤ → ℂ) (n : ℤ) :
    ∑ τ ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), shiftExp k τ g n
      = ((2:ℂ)^k) * ∑ d ∈ Finset.Icc (-((2:ℤ)^k)) ((2:ℤ)^k), (triKernel k d : ℂ) * g (n - d) := by
  classical
  have hkey : ∀ d : ℤ, ∑ τ ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), shiftKernel k τ d
      = (2:ℝ)^k * triKernel k d := by
    intro d
    have h := shiftKernel_average k d
    rw [div_eq_iff (ne_of_gt (show (0:ℝ) < (2:ℝ)^k by positivity))] at h
    rw [h]; ring
  calc ∑ τ ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), shiftExp k τ g n
      = ∑ τ ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k),
          ∑ d ∈ Finset.Icc (-((2:ℤ)^k)) ((2:ℤ)^k), shiftKernel k τ d * g (n - d) := by
        refine Finset.sum_congr rfl (fun τ hτ => ?_)
        exact shiftExp_eq_sum k (Finset.mem_Ico.mp hτ).1 (Finset.mem_Ico.mp hτ).2 g n
    _ = ∑ d ∈ Finset.Icc (-((2:ℤ)^k)) ((2:ℤ)^k),
          ∑ τ ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), shiftKernel k τ d * g (n - d) := Finset.sum_comm
    _ = ∑ d ∈ Finset.Icc (-((2:ℤ)^k)) ((2:ℤ)^k),
          ((2:ℂ)^k) * ((triKernel k d : ℂ) * g (n - d)) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        have hcast : ((∑ i ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), shiftKernel k i d : ℝ) : ℂ)
            = ∑ i ∈ Finset.Ico (0:ℤ) ((2:ℤ)^k), ((shiftKernel k i d : ℝ) : ℂ) := by
          push_cast; ring
        rw [← Finset.sum_mul]
        rw [← hcast, hkey d]
        push_cast
        ring
    _ = ((2:ℂ)^k) * ∑ d ∈ Finset.Icc (-((2:ℤ)^k)) ((2:ℤ)^k),
          (triKernel k d : ℂ) * g (n - d) := by
        rw [Finset.mul_sum]

end

end Work.Analysis.Hilbert
