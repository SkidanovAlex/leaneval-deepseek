import Mathlib.NumberTheory.LSeries.RiemannZeta
import Submission.Commons.NumberTheory.Zeta.cpow_shift_sub_summable
import Submission.Commons.NumberTheory.Zeta.cpow_shift_tendsto_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped BigOperators Topology
open Filter Finset

noncomputable section

namespace Commons.NumberTheory.Zeta

private lemma cpow_neg_nat (n : ℕ) (s : ℂ) :
    (((n : ℕ) : ℂ) ^ (-s)) = 1 / (((n : ℕ) : ℂ) ^ s) := by
  rw [Complex.cpow_neg]
  simp [one_div]

private lemma zeta_eq_tsum_neg_cpow {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = (∑' n : ℕ, (((n : ℕ) : ℂ) ^ (-s))) := by
  calc
    riemannZeta s = (∑' n : ℕ, 1 / (((n : ℕ) : ℂ) ^ s)) := zeta_eq_tsum_one_div_nat_cpow hs
    _ = (∑' n : ℕ, (((n : ℕ) : ℂ) ^ (-s))) := by
      apply tsum_congr
      intro n
      exact (cpow_neg_nat n s).symm

private lemma summable_nat_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (((n : ℕ) : ℂ) ^ (-s))) := by
  have hsum1 : Summable (fun n : ℕ => 1 / (((n : ℕ) : ℂ) ^ s)) :=
    (Complex.summable_one_div_nat_cpow).mpr hs
  exact (summable_congr (fun n => cpow_neg_nat n s)).mpr hsum1

private lemma sum_range_succ_eq_Icc_one (N : ℕ) (f : ℕ → ℂ) (hf0 : f 0 = 0) :
    (∑ i ∈ Finset.range (N + 1), f i) = (∑ i ∈ Finset.Icc 1 N, f i) := by
  induction N with
  | zero => simp [hf0]
  | succ N ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      rw [Finset.sum_Icc_succ_top (a := 1) (b := N) (by omega : 1 ≤ N + 1)]

/-- Telescoping: `∑ m ((N+m+1)^w - (N+m)^w)/c = -(N^w)/c` whenever `w.re < 0`. -/
private lemma tsum_cpow_shift_sub_div {w c : ℂ} {N : ℕ} (hN : 1 ≤ N) (hw : w.re < 0) :
    (∑' m : ℕ, ((((N + m + 1 : ℕ) : ℂ) ^ w) - (((N + m : ℕ) : ℂ) ^ w)) / c) =
      -(((N : ℕ) : ℂ) ^ w) / c := by
  let a : ℕ → ℂ := fun m => (((N + m : ℕ) : ℂ) ^ w)
  let d : ℕ → ℂ := fun m => ((((N + m + 1 : ℕ) : ℂ) ^ w) - (((N + m : ℕ) : ℂ) ^ w)) / c
  -- summability of the telescoping terms
  have hsum_a : Summable (fun m : ℕ => a (m + 1) - a m) := by
    have hfun : (fun m : ℕ => a (m + 1) - a m) =
        (fun m : ℕ => ((((N + m + 1 : ℕ) : ℂ) ^ w) - (((N + m : ℕ) : ℂ) ^ w))) := by
      rfl
    rw [hfun]
    exact cpow_shift_sub_summable hN hw
  have hsum_d : Summable d := by
    unfold d
    exact hsum_a.div_const c
  -- tendency of the tail
  have ht0 : Tendsto a atTop (𝓝 (0 : ℂ)) := by
    simpa [a] using cpow_shift_tendsto_zero hN hw
  -- partial sums of `d` telescope to `(a M - a 0)/c`
  have hconv : (fun M : ℕ => ∑ i ∈ Finset.range M, d i) = fun M => (a M - a 0) / c := by
    funext M
    calc
      (∑ i ∈ Finset.range M, d i)
          = ∑ i ∈ Finset.range M, ((a (i + 1) - a i) / c) := by
            apply Finset.sum_congr rfl
            intro i hi
            rfl
      _ = (∑ i ∈ Finset.range M, (a (i + 1) - a i)) / c := by
            rw [Finset.sum_div]
      _ = (a M - a 0) / c := by rw [Finset.sum_range_sub]
  have hps : Tendsto (fun M : ℕ => ∑ i ∈ Finset.range M, d i) atTop
      (𝓝 (-(((N : ℕ) : ℂ) ^ w) / c)) := by
    rw [hconv]
    have hconst : Tendsto (fun _ : ℕ => a 0) atTop (𝓝 (a 0)) := tendsto_const_nhds
    have hsub := ht0.sub hconst
    have hdiv := hsub.div_const c
    simpa [a] using hdiv
  have hhas : HasSum d (-(((N : ℕ) : ℂ) ^ w) / c) :=
    (Summable.hasSum_iff_tendsto_nat hsum_d).2 hps
  simpa [d] using hhas.tsum_eq

/-- Euler-Maclaurin style decomposition of `riemannZeta` on the half-plane `1 < re s`. -/
theorem zeta_eq_emN_re_gt_one {s : ℂ} (hs : 1 < s.re) (N : ℕ) (hN : 1 ≤ N) :
    riemannZeta s =
      (∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s))) +
      ((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1)) +
      (∑' m : ℕ,
        ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
          (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))) := by
  let w : ℂ := 1 - s
  let g : ℕ → ℂ := fun n => (((n : ℕ) : ℂ) ^ (-s))
  let P : ℂ := ∑ n ∈ Finset.Icc 1 N, g n
  let tail : ℂ := ∑' m : ℕ, g (N + m + 1)
  let v : ℕ → ℂ := fun m => ((((N + m + 1 : ℕ) : ℂ) ^ w) - (((N + m : ℕ) : ℂ) ^ w)) / (1 - s)
  let M : ℂ := (((N : ℕ) : ℂ) ^ w) / (s - 1)
  let T : ℂ := ∑' m : ℕ, (g (N + m + 1) - v m)
  have hs_ne0 : s ≠ 0 := by
    intro h
    have hre : s.re = 0 := by rw [h]; simp
    linarith
  have hs1 : s ≠ 1 := by
    intro h
    have hre : s.re = 1 := by rw [h]; simp
    linarith
  have hw : w.re < 0 := by
    unfold w
    rw [Complex.sub_re, Complex.one_re]
    linarith
  have hg0 : g 0 = 0 := by
    unfold g
    rw [Complex.cpow_neg]
    simp [Complex.zero_cpow hs_ne0]
  have hsum_g : Summable g := summable_nat_cpow_neg hs
  -- zeta = P + tail
  have hsplit := Summable.sum_add_tsum_nat_add (k := N + 1) (f := g) hsum_g
  have hzeta_split : riemannZeta s = P + tail := by
    rw [zeta_eq_tsum_neg_cpow hs]
    rw [← hsplit]
    congr 1
    · simpa [P] using sum_range_succ_eq_Icc_one N g hg0
    · apply tsum_congr
      intro m
      exact congrArg g (by omega)
  -- summability of v and of the g-shift
  have hsum_v : Summable v := by
    unfold v
    exact (cpow_shift_sub_summable hN hw).div_const (1 - s)
  have hsum_gshift : Summable (fun m : ℕ => g (N + m + 1)) := by
    have hgsh : Summable (fun m : ℕ => g (m + (N + 1))) := (summable_nat_add_iff (N + 1)).2 hsum_g
    exact hgsh.congr (fun m => congrArg g (by omega))
  -- ∑' v = M
  have hsum_v_eq : (∑' m : ℕ, v m) = M := by
    unfold v M
    rw [tsum_cpow_shift_sub_div (c := 1 - s) hN hw]
    have hs1c : (s - 1 : ℂ) ≠ 0 := sub_ne_zero.mpr hs1
    field_simp [hs1c]
    ring
  -- T = tail - M
  have hT_val : T = tail - M := by
    unfold T
    rw [Summable.tsum_sub hsum_gshift hsum_v, hsum_v_eq]
  have htail_eq : tail = M + T := by
    rw [hT_val]
    abel
  calc
    riemannZeta s = P + tail := hzeta_split
    _ = P + (M + T) := by rw [htail_eq]
    _ = (P + M) + T := by abel
    _ = (∑ n ∈ Finset.Icc 1 N, (((n : ℕ) : ℂ) ^ (-s))) +
        ((((N : ℕ) : ℂ) ^ (1 - s)) / (s - 1)) +
        (∑' m : ℕ,
          ((((N + m + 1 : ℕ) : ℂ) ^ (-s)) -
            (((((N + m + 1 : ℕ) : ℂ) ^ (1 - s)) - (((N + m : ℕ) : ℂ) ^ (1 - s))) / (1 - s)))) := by
      simp [P, M, T, v, w, g]

end Commons.NumberTheory.Zeta