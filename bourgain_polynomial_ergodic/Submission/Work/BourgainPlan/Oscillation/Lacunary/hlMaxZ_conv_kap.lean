import Mathlib
import Submission.Work.BourgainPlan.Oscillation.Lacunary.defs

/-!
# Domination of the Poisson-kernel convolution by the discrete Hardy--Littlewood maximal function

`hlMaxZ G x` is the two-sided maximal function on `ℤ`: the supremum over all integer intervals
`[a,b] ∋ x` of the average of `G` over the interval.  The Poisson kernel
`kap ρ i z = (1-λ)/(1+λ)·λ^{|z|}` (with `λ = exp(-2π ρ^{-i}) ∈ (0,1)`) is a probability density on
`ℤ`, symmetric and non-increasing in `|z|`.

The classical fact used here is that such a kernel is a convex combination of the uniform
distributions on the symmetric intervals `[-N,N]`:
`kap ρ i z = ∑_{N ≥ |z|} d_N`, where `d_N = kap ρ i N - kap ρ i (N+1) ≥ 0` and
`∑_N (2N+1) d_N = 1`.  Consequently every interval average is bounded by `hlMaxZ G x`, and so is
the whole convolution.  We prove

`∑' z, ofReal (kap ρ i z) * G (x - z) ≤ hlMaxZ G x`.
-/

open scoped BigOperators ENNReal

namespace Work.BourgainPlan.Oscillation.Lacunary

noncomputable section

/-- The mass of the Poisson kernel difference sequence: `d_N = κ_N - κ_{N+1}`. -/
private def kapD (ρ : ℝ) (i : ℕ) (N : ℕ) : ℝ := kap ρ i (N : ℤ) - kap ρ i ((N+1 : ℕ) : ℤ)

private lemma kap_natAbs (ρ : ℝ) (i : ℕ) (z : ℤ) : kap ρ i z = kap ρ i (z.natAbs : ℤ) := by
  unfold kap; rw [Int.natAbs_natCast]

private lemma kap_succ (ρ : ℝ) (i : ℕ) (N : ℕ) :
    kap ρ i ((N+1 : ℕ) : ℤ) = lam ρ i * kap ρ i (N : ℤ) := by
  unfold kap; rw [Int.natAbs_natCast, Int.natAbs_natCast, pow_succ]; ring

private lemma kapD_eq (ρ : ℝ) (i : ℕ) (N : ℕ) :
    kapD ρ i N = (1 - lam ρ i) * kap ρ i (N : ℤ) := by
  unfold kapD; rw [kap_succ]; ring

private lemma kap_nat (ρ : ℝ) (i : ℕ) (N : ℕ) :
    kap ρ i (N : ℤ) = (1 - lam ρ i)/(1 + lam ρ i) * (lam ρ i)^N := by
  unfold kap; rw [Int.natAbs_natCast]

private lemma kap_nonneg (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) (z : ℤ) : 0 ≤ kap ρ i z := by
  have hρ0 : (0:ℝ) < ρ := by linarith
  have h1 := lam_nonneg hρ0 i
  have h2 := one_sub_lam_pos hρ0 i
  have h3 := one_add_lam_pos hρ0 i
  simp only [kap]
  positivity

private lemma kapD_nonneg (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) (N : ℕ) : 0 ≤ kapD ρ i N := by
  have hρ0 : (0:ℝ) < ρ := by linarith
  rw [kapD_eq, kap_nat]
  have h1 : 0 ≤ (1 - lam ρ i)/(1 + lam ρ i) :=
    div_nonneg (le_of_lt (one_sub_lam_pos hρ0 i)) (le_of_lt (one_add_lam_pos hρ0 i))
  have h2 : 0 ≤ (lam ρ i)^N := pow_nonneg (lam_nonneg hρ0 i) N
  have h3 : 0 ≤ 1 - lam ρ i := le_of_lt (one_sub_lam_pos hρ0 i)
  exact mul_nonneg h3 (mul_nonneg h1 h2)

private lemma kap_tendsto_zero (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) :
    Filter.Tendsto (fun n : ℕ => kap ρ i (n : ℤ)) Filter.atTop (nhds 0) := by
  have hρ0 : (0:ℝ) < ρ := by linarith
  have hfun : (fun n : ℕ => kap ρ i (n:ℤ))
      = fun n => ((1 - lam ρ i)/(1 + lam ρ i)) * (lam ρ i)^n := by
    funext n; simp only [kap, Int.natAbs_natCast]
  rw [hfun]
  have h : Filter.Tendsto (fun n : ℕ => (lam ρ i)^n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (lam_nonneg hρ0 i) (lam_lt_one hρ0 i)
  simpa using h.const_mul ((1 - lam ρ i)/(1 + lam ρ i))

/-- Telescoping of the difference sequence. -/
private lemma sum_range_kapD (ρ : ℝ) (i : ℕ) (m J : ℕ) :
    ∑ k ∈ Finset.range J, kapD ρ i (m + k) = kap ρ i (m : ℤ) - kap ρ i ((m + J : ℕ) : ℤ) := by
  induction J with
  | zero => simp
  | succ J ih =>
      have h1 : m + (J+1) = (m + J) + 1 := by omega
      rw [Finset.sum_range_succ, ih, h1, kapD]
      ring

private lemma sum_range_ite_kapD (ρ : ℝ) (i : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    ∑ N ∈ Finset.range n, (if m ≤ N then kapD ρ i N else 0)
      = kap ρ i (m : ℤ) - kap ρ i (n : ℤ) := by
  rw [← Finset.sum_filter]
  have hf : (Finset.range n).filter (fun N => m ≤ N) = Finset.Ico m n := by
    ext N; simp [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  rw [hf, Finset.sum_Ico_eq_sum_range]
  have hm : m + (n - m) = n := by omega
  rw [sum_range_kapD, hm]

private lemma hasSum_ite_kapD (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) (m : ℕ) :
    HasSum (fun N : ℕ => if m ≤ N then kapD ρ i N else 0) (kap ρ i (m : ℤ)) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun N => by split <;> simp [kapD_nonneg ρ hρ])]
  refine Filter.Tendsto.congr' (f₁ := fun n : ℕ => kap ρ i (m:ℤ) - kap ρ i (n:ℤ)) ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop m] with n hn
    exact (sum_range_ite_kapD ρ i hn).symm
  · simpa using (tendsto_const_nhds.sub (kap_tendsto_zero ρ hρ i) :
      Filter.Tendsto (fun n : ℕ => kap ρ i (m:ℤ) - kap ρ i (n:ℤ)) Filter.atTop
        (nhds (kap ρ i (m:ℤ) - 0)))

/-- Shell decomposition: `kap ρ i z = ∑_{N ≥ |z|} d_N`, in `ℝ≥0∞`. -/
private lemma ofReal_kap_shell (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) (z : ℤ) :
    ENNReal.ofReal (kap ρ i z)
      = ∑' N : ℕ, ENNReal.ofReal (kapD ρ i N) * (if z.natAbs ≤ N then 1 else 0) := by
  have hsummable : Summable (fun N : ℕ => if z.natAbs ≤ N then kapD ρ i N else 0) :=
    (hasSum_ite_kapD ρ hρ i z.natAbs).summable
  have hnn : ∀ N, 0 ≤ (if z.natAbs ≤ N then kapD ρ i N else 0) := fun N => by
    split <;> simp [kapD_nonneg ρ hρ]
  have htsum : ∑' N : ℕ, (if z.natAbs ≤ N then kapD ρ i N else 0) = kap ρ i (z.natAbs : ℤ) :=
    (hasSum_ite_kapD ρ hρ i z.natAbs).tsum_eq
  calc ENNReal.ofReal (kap ρ i z)
      = ENNReal.ofReal (kap ρ i ((z.natAbs : ℤ))) := by rw [kap_natAbs]
    _ = ENNReal.ofReal (∑' N : ℕ, (if z.natAbs ≤ N then kapD ρ i N else 0)) := by rw [htsum]
    _ = ∑' N : ℕ, ENNReal.ofReal (if z.natAbs ≤ N then kapD ρ i N else 0) :=
          ENNReal.ofReal_tsum_of_nonneg hnn hsummable
    _ = ∑' N : ℕ, ENNReal.ofReal (kapD ρ i N) * (if z.natAbs ≤ N then 1 else 0) := by
          refine tsum_congr (fun N => ?_)
          split <;> simp

private lemma kapD_term (ρ : ℝ) (i : ℕ) (N : ℕ) :
    kapD ρ i N * ((2*N+1 : ℕ) : ℝ)
      = ((1 - lam ρ i)^2/(1 + lam ρ i)) * ((lam ρ i)^N * (2*(N:ℝ)+1)) := by
  rw [kapD_eq, kap_nat]
  have hcast : ((2*N+1 : ℕ) : ℝ) = 2*(N:ℝ)+1 := by push_cast; ring
  rw [hcast]; ring

private lemma summable_kapD_mul (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) :
    Summable (fun N : ℕ => kapD ρ i N * ((2*N+1 : ℕ) : ℝ)) := by
  have hρ0 : (0:ℝ) < ρ := by linarith
  have hl0 := lam_nonneg hρ0 i
  have hl1 := lam_lt_one hρ0 i
  have hnorm : ‖lam ρ i‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hl0]; exact hl1
  have hf : Summable (fun N : ℕ => (N:ℝ) * (lam ρ i)^N) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
  have hg : Summable (fun N : ℕ => (lam ρ i)^N) := summable_geometric_of_norm_lt_one hnorm
  have h2 : Summable (fun N : ℕ => (lam ρ i)^N * (2*(N:ℝ)+1)) := by
    have h : (fun N : ℕ => (lam ρ i)^N * (2*(N:ℝ)+1))
        = fun N : ℕ => (2 * ((N:ℝ) * (lam ρ i)^N) + (lam ρ i)^N) := by
      funext N; ring
    rw [h]; exact (hf.mul_left 2).add hg
  have h3 := h2.mul_left ((1 - lam ρ i)^2/(1 + lam ρ i))
  refine h3.congr (fun N => ?_)
  rw [kapD_term]

/-- The total mass identity `∑_N (2N+1) d_N = 1`. -/
private lemma tsum_kapD_mul (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) :
    ∑' N : ℕ, kapD ρ i N * ((2*N+1 : ℕ) : ℝ) = 1 := by
  have hρ0 : (0:ℝ) < ρ := by linarith
  have hl0 := lam_nonneg hρ0 i
  have hl1 := lam_lt_one hρ0 i
  have hlne : (1 - lam ρ i) ≠ 0 := by linarith
  have hlne2 : (1 + lam ρ i) ≠ 0 := by linarith
  have hnorm : ‖lam ρ i‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg hl0]; exact hl1
  have hf : Summable (fun N : ℕ => (N:ℝ) * (lam ρ i)^N) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hnorm
  have hg : Summable (fun N : ℕ => (lam ρ i)^N) := summable_geometric_of_norm_lt_one hnorm
  have hsum : ∑' N : ℕ, (lam ρ i)^N * (2*(N:ℝ)+1)
      = 2 * (lam ρ i/(1 - lam ρ i)^2) + (1 - lam ρ i)⁻¹ := by
    rw [show (∑' N : ℕ, (lam ρ i)^N * (2*(N:ℝ)+1))
        = ∑' N : ℕ, (2 * ((N:ℝ) * (lam ρ i)^N) + (lam ρ i)^N) from
          tsum_congr (fun N => by ring)]
    rw [(hf.mul_left 2).tsum_add hg, tsum_mul_left,
        tsum_coe_mul_geometric_of_norm_lt_one hnorm, tsum_geometric_of_norm_lt_one hnorm]
  rw [show (∑' N : ℕ, kapD ρ i N * ((2*N+1 : ℕ) : ℝ))
      = ∑' N : ℕ, ((1 - lam ρ i)^2/(1 + lam ρ i)) * ((lam ρ i)^N * (2*(N:ℝ)+1)) from
        tsum_congr (fun N => kapD_term ρ i N)]
  rw [tsum_mul_left, hsum]
  field_simp
  ring

/-- The total mass identity in `ℝ≥0∞`. -/
private lemma sum_kapD_mul_one (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) :
    ∑' N : ℕ, ENNReal.ofReal (kapD ρ i N) * ((2*N+1 : ℕ) : ℝ≥0∞) = 1 := by
  have hsumm := summable_kapD_mul ρ hρ i
  have hnn : ∀ N, 0 ≤ kapD ρ i N * ((2*N+1 : ℕ) : ℝ) :=
    fun N => mul_nonneg (kapD_nonneg ρ hρ i N) (by positivity)
  rw [← ENNReal.ofReal_one, ← tsum_kapD_mul ρ hρ i]
  rw [ENNReal.ofReal_tsum_of_nonneg hnn hsumm]
  refine tsum_congr (fun N => ?_)
  rw [ENNReal.ofReal_mul (kapD_nonneg ρ hρ i N), ENNReal.ofReal_natCast]

/-! ## The interval averages are dominated by the maximal function -/

private lemma hlMaxZ_ge (G : ℤ → ℝ≥0∞) (x : ℤ) {a b : ℤ} (ha : a ≤ x) (hb : x ≤ b) :
    ((b - a + 1).toNat : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc a b, G k ≤ hlMaxZ G x := by
  unfold hlMaxZ
  exact le_iSup_of_le a (le_iSup_of_le b (le_iSup_of_le ⟨ha, hb⟩ le_rfl))

/-- Reindexing the symmetric window in `z` as an interval in `k = x - z`. -/
private lemma sum_Icc_neg_sub_eq (G : ℤ → ℝ≥0∞) (x : ℤ) (N : ℕ) :
    ∑ z ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), G (x - z)
      = ∑ k ∈ Finset.Icc (x - (N:ℤ)) (x + (N:ℤ)), G k := by
  refine Finset.sum_bij (fun z _ => x - z) ?_ ?_ ?_ ?_
  · intro z hz; simp only [Finset.mem_Icc] at hz ⊢; omega
  · intro z1 _ z2 _ h; omega
  · intro k hk; simp only [Finset.mem_Icc] at hk
    exact ⟨x - k, by simp only [Finset.mem_Icc]; omega, by ring⟩
  · intro z _; rfl

private lemma window_le (G : ℤ → ℝ≥0∞) (x : ℤ) (N : ℕ) :
    ∑ z ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), G (x - z) ≤ ((2*N+1 : ℕ) : ℝ≥0∞) * hlMaxZ G x := by
  rw [sum_Icc_neg_sub_eq G x N]
  have hcard : ((x + (N:ℤ)) - (x - (N:ℤ)) + 1).toNat = 2*N+1 := by
    have h : (x + (N:ℤ)) - (x - (N:ℤ)) + 1 = ((2*N+1 : ℕ) : ℤ) := by push_cast; ring
    rw [h, Int.toNat_natCast]
  have h := hlMaxZ_ge G x (a := x - (N:ℤ)) (b := x + (N:ℤ)) (by omega) (by omega)
  rw [hcard] at h
  calc ∑ k ∈ Finset.Icc (x - ↑N) (x + ↑N), G k
      = ((2*N+1 : ℕ) : ℝ≥0∞) *
          (((2*N+1 : ℕ) : ℝ≥0∞)⁻¹ * ∑ k ∈ Finset.Icc (x - ↑N) (x + ↑N), G k) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top (2*N+1)),
          one_mul]
    _ ≤ ((2*N+1 : ℕ) : ℝ≥0∞) * hlMaxZ G x := mul_le_mul_right h _

private lemma mem_Icc_iff_natAbs (z : ℤ) (N : ℕ) :
    z.natAbs ≤ N ↔ z ∈ Finset.Icc (-(N:ℤ)) (N:ℤ) := by
  rw [Finset.mem_Icc]
  exact ⟨fun h => by
      rw [← Nat.cast_le (α := ℤ), ← Int.abs_eq_natAbs, abs_le] at h; exact h,
    fun h => by
      rw [← Nat.cast_le (α := ℤ), ← Int.abs_eq_natAbs, abs_le]; exact h⟩

private lemma ite_natAbs (G : ℤ → ℝ≥0∞) (x : ℤ) (N : ℕ) (z : ℤ)
    (hz : z ∉ Finset.Icc (-(N:ℤ)) (N:ℤ)) :
    (if z.natAbs ≤ N then G (x - z) else 0) = 0 := by
  rw [if_neg (fun h => hz ((mem_Icc_iff_natAbs z N).mp h))]

theorem hlMaxZ_conv_kap (ρ : ℝ) (hρ : 1 < ρ) (i : ℕ) (G : ℤ → ENNReal) (x : ℤ) :
    ∑' z : ℤ, ENNReal.ofReal (Work.BourgainPlan.Oscillation.Lacunary.kap ρ i z) * G (x - z)
      ≤ Work.BourgainPlan.Oscillation.Lacunary.hlMaxZ G x := by
  have hstep1 : ∑' z : ℤ, ENNReal.ofReal (kap ρ i z) * G (x - z)
      = ∑' N : ℕ, ENNReal.ofReal (kapD ρ i N) *
          (∑' z : ℤ, (if z.natAbs ≤ N then G (x - z) else 0)) := by
    calc ∑' z : ℤ, ENNReal.ofReal (kap ρ i z) * G (x - z)
        = ∑' z : ℤ, (∑' N : ℕ, ENNReal.ofReal (kapD ρ i N) *
              (if z.natAbs ≤ N then 1 else 0)) * G (x - z) :=
            tsum_congr (fun z => by rw [ofReal_kap_shell ρ hρ i z])
      _ = ∑' z : ℤ, ∑' N : ℕ, (ENNReal.ofReal (kapD ρ i N) *
              (if z.natAbs ≤ N then 1 else 0)) * G (x - z) :=
            tsum_congr (fun z => by rw [ENNReal.tsum_mul_right])
      _ = ∑' N : ℕ, ∑' z : ℤ, (ENNReal.ofReal (kapD ρ i N) *
              (if z.natAbs ≤ N then 1 else 0)) * G (x - z) := ENNReal.tsum_comm
      _ = ∑' N : ℕ, ∑' z : ℤ, ENNReal.ofReal (kapD ρ i N) *
              ((if z.natAbs ≤ N then 1 else 0) * G (x - z)) :=
            tsum_congr (fun N => tsum_congr (fun z => by rw [mul_assoc]))
      _ = ∑' N : ℕ, ENNReal.ofReal (kapD ρ i N) *
              (∑' z : ℤ, (if z.natAbs ≤ N then 1 else 0) * G (x - z)) :=
            tsum_congr (fun N => ENNReal.tsum_mul_left)
      _ = ∑' N : ℕ, ENNReal.ofReal (kapD ρ i N) *
              (∑' z : ℤ, (if z.natAbs ≤ N then G (x - z) else 0)) := by
            refine tsum_congr (fun N => ?_)
            congr 1
            refine tsum_congr (fun z => ?_)
            split <;> simp
  rw [hstep1]
  have hwindow : ∀ N : ℕ, (∑' z : ℤ, (if z.natAbs ≤ N then G (x - z) else 0))
      ≤ ((2*N+1 : ℕ) : ℝ≥0∞) * hlMaxZ G x := by
    intro N
    rw [tsum_eq_sum (s := Finset.Icc (-(N:ℤ)) (N:ℤ))
      (fun z hz => ite_natAbs G x N z hz)]
    rw [show (∑ z ∈ Finset.Icc (-↑N) ↑N, (if z.natAbs ≤ N then G (x - z) else 0))
          = ∑ z ∈ Finset.Icc (-↑N) ↑N, G (x - z) from
        Finset.sum_congr rfl (fun z hz => by
          rw [if_pos ((mem_Icc_iff_natAbs z N).mpr hz)])]
    exact window_le G x N
  calc ∑' N : ℕ, ENNReal.ofReal (kapD ρ i N) *
        (∑' z : ℤ, (if z.natAbs ≤ N then G (x - z) else 0))
      ≤ ∑' N : ℕ, ENNReal.ofReal (kapD ρ i N) * (((2*N+1 : ℕ) : ℝ≥0∞) * hlMaxZ G x) :=
        ENNReal.tsum_le_tsum (fun N => mul_le_mul_right (hwindow N) _)
    _ = ∑' N : ℕ, (ENNReal.ofReal (kapD ρ i N) * ((2*N+1 : ℕ) : ℝ≥0∞)) * hlMaxZ G x :=
        tsum_congr (fun N => by rw [mul_assoc])
    _ = (∑' N : ℕ, ENNReal.ofReal (kapD ρ i N) * ((2*N+1 : ℕ) : ℝ≥0∞)) * hlMaxZ G x :=
        ENNReal.tsum_mul_right
    _ = 1 * hlMaxZ G x := by rw [sum_kapD_mul_one ρ hρ i]
    _ = hlMaxZ G x := one_mul _

end

end Work.BourgainPlan.Oscillation.Lacunary
