import Mathlib
import Submission.Work.Drive.seeleyEpsDefs

/-!
# Flatness of the tail sums `ε_n`

`ε_n(s) = Σ_j a_j (1 - ρ(b_j s)) b_j^n` is smooth, and each of its derivatives of order `k` is
`O(|s|^L)` near `s = 0`, uniformly for `k ≤ L` and `n ≤ n₀`.  The point is that the `k`-th
derivative is a sum of terms `a_j b_j^{n+k} (1-ρ)^{(k)}(b_j s)`, and `(1-ρ)^{(k)}` vanishes for
`|b_j s| ≤ 1/2`, so in each surviving term one may trade `m` powers of `b_j` for a factor
`(2|s|)^m`, at the cost of the (finite) absolute moment `Σ_j |a_j| b_j^{n+k+m}`.
-/

open scoped ContDiff Topology

namespace Work.Drive

/-- A uniform bound for `|(1 - ρ)^{(k)}|`. -/
lemma seeleyOneSubRho_deriv_bdd (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y : ℝ, |iteratedDeriv k (fun t : ℝ => 1 - seeleyRho t) y| ≤ M := by
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => 1 - seeleyRho t) :=
    ContDiff.sub contDiff_const seeleyRho_contDiff
  have hcont : Continuous (fun y : ℝ => iteratedDeriv k (fun t : ℝ => 1 - seeleyRho t) y) :=
    hcd.continuous_iteratedDeriv k (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (f := fun y : ℝ => iteratedDeriv k (fun t : ℝ => 1 - seeleyRho t) y) hcont.continuousOn
  refine ⟨max C 1, le_trans zero_le_one (le_max_right _ _), fun y => ?_⟩
  by_cases hy : |y| ≤ 1
  · have hy' : y ∈ Set.Icc (-1 : ℝ) 1 := ⟨neg_le_of_abs_le hy, le_of_abs_le hy⟩
    have h := hC y hy'
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  · have hy' : 1 < |y| := not_le.mp hy
    have hev : (fun t : ℝ => 1 - seeleyRho t) =ᶠ[𝓝 y] (fun _ => (1 : ℝ)) := by
      filter_upwards [Metric.ball_mem_nhds y (by linarith : (0 : ℝ) < |y| - 1)] with z hz
      rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] at hz
      have h1 : 1 ≤ |z| := by
        have h2 := abs_sub_abs_le_abs_sub y z
        have h3 : |y - z| < |y| - 1 := by rwa [abs_sub_comm] at hz
        linarith
      rw [seeleyRho_eq_zero h1]
      ring
    rw [Filter.EventuallyEq.iteratedDeriv_eq k hev, iteratedDeriv_const]
    split_ifs <;> simpa using le_max_right C 1

/-- A uniform bound for `|(1 - ρ)^{(k)}|`. -/
noncomputable def seeleyRhoDS (k : ℕ) : ℝ := Classical.choose (seeleyOneSubRho_deriv_bdd k)

lemma seeleyRhoDS_nonneg (k : ℕ) : 0 ≤ seeleyRhoDS k :=
  (Classical.choose_spec (seeleyOneSubRho_deriv_bdd k)).1

lemma seeleyRhoDS_bound (k : ℕ) (y : ℝ) :
    |iteratedDeriv k (fun t : ℝ => 1 - seeleyRho t) y| ≤ seeleyRhoDS k :=
  (Classical.choose_spec (seeleyOneSubRho_deriv_bdd k)).2 y

lemma contDiff_oneSubRho (k : ℕ) :
    ContDiff ℝ (((k : ℕ) : ℕ∞) : WithTop ℕ∞) (fun t : ℝ => 1 - seeleyRho t) :=
  (ContDiff.sub contDiff_const seeleyRho_contDiff).of_le (WithTop.coe_le_coe.mpr le_top)

/-- `(1 - ρ)^{(k)}` vanishes on the ball of radius `1/2` (the cutoff is constant there). -/
lemma iteratedDeriv_oneSubRho_eq_zero {y : ℝ} (hy : |y| < 1 / 2) (k : ℕ) :
    iteratedDeriv k (fun t : ℝ => 1 - seeleyRho t) y = 0 := by
  have hev : (fun t : ℝ => 1 - seeleyRho t) =ᶠ[𝓝 y] (fun _ => (0 : ℝ)) := by
    filter_upwards [Metric.ball_mem_nhds y (by linarith : (0 : ℝ) < 1 / 2 - |y|)] with z hz
    rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs] at hz
    have hz1 : |z| ≤ 1 / 2 := by
      have h2 := abs_sub_abs_le_abs_sub z y
      linarith
    rw [seeleyRho_eq_one hz1]
    ring
  rw [Filter.EventuallyEq.iteratedDeriv_eq k hev, iteratedDeriv_const]
  split_ifs <;> rfl

/-- The `k`-th derivative of the `j`-th summand of `ε_n` is bounded by the (unrestricted) moment
of order `n + k`. -/
lemma seeleyEps_term_bound_plain {a b : ℕ → ℝ} (hb : ∀ j : ℕ, 0 < b j) (n k j : ℕ) (s : ℝ) :
    |iteratedDeriv k (fun s : ℝ => a j * (b j) ^ n * (1 - seeleyRho (b j * s))) s|
      ≤ |a j| * (b j) ^ (n + k) * seeleyRhoDS k := by
  have hkey : iteratedDeriv k (fun s : ℝ => a j * (b j) ^ n * (1 - seeleyRho (b j * s))) s
      = (a j * (b j) ^ n) *
        ((b j) ^ k * iteratedDeriv k (fun t : ℝ => 1 - seeleyRho t) (b j * s)) := by
    rw [iteratedDeriv_const_mul_field]
    rw [congrFun (iteratedDeriv_comp_const_mul (contDiff_oneSubRho k) (b j)) s]
  rw [hkey]
  have hQ := seeleyRhoDS_bound k (b j * s)
  have h1 : |a j * (b j) ^ n| = |a j| * (b j) ^ n := by
    rw [abs_mul, abs_pow, abs_of_pos (hb j)]
  have h2 : |(b j) ^ k| = (b j) ^ k := by rw [abs_pow, abs_of_pos (hb j)]
  rw [abs_mul, h1, abs_mul, h2]
  have hA : (0 : ℝ) ≤ |a j| * (b j) ^ n :=
    mul_nonneg (abs_nonneg _) (pow_nonneg (le_of_lt (hb j)) n)
  have hB : (0 : ℝ) ≤ (b j) ^ k := pow_nonneg (le_of_lt (hb j)) k
  calc |a j| * (b j) ^ n *
        ((b j) ^ k * |iteratedDeriv k (fun t : ℝ => 1 - seeleyRho t) (b j * s)|)
      ≤ |a j| * (b j) ^ n * ((b j) ^ k * seeleyRhoDS k) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQ hB) hA
    _ = |a j| * (b j) ^ (n + k) * seeleyRhoDS k := by rw [pow_add]; ring

/-- The termwise flat bound: outside the tail `2 b_j |s| < 1` the derivative vanishes. -/
lemma seeleyEps_term_bound {a b : ℕ → ℝ} (hb : ∀ j : ℕ, 0 < b j) (n k j : ℕ) (s : ℝ) :
    |iteratedDeriv k (fun s : ℝ => a j * (b j) ^ n * (1 - seeleyRho (b j * s))) s|
      ≤ (if 1 ≤ 2 * (b j) * |s| then |a j| * (b j) ^ (n + k) * seeleyRhoDS k else 0) := by
  by_cases hcase : 1 ≤ 2 * (b j) * |s|
  · rw [if_pos hcase]
    exact seeleyEps_term_bound_plain hb n k j s
  · rw [if_neg hcase]
    have hlt : |b j * s| < 1 / 2 := by
      rw [abs_mul, abs_of_pos (hb j)]
      linarith
    have hkey : iteratedDeriv k (fun s : ℝ => a j * (b j) ^ n * (1 - seeleyRho (b j * s))) s
        = (a j * (b j) ^ n) *
          ((b j) ^ k * iteratedDeriv k (fun t : ℝ => 1 - seeleyRho t) (b j * s)) := by
      rw [iteratedDeriv_const_mul_field]
      rw [congrFun (iteratedDeriv_comp_const_mul (contDiff_oneSubRho k) (b j)) s]
    rw [hkey, iteratedDeriv_oneSubRho_eq_zero hlt k]
    simp

/-- `ε_n` is smooth. -/
theorem seeleyEps_contDiff {a b : ℕ → ℝ} (hb : ∀ j : ℕ, 0 < b j)
    (hsum : ∀ q : ℕ, Summable (fun j : ℕ => |a j| * (b j) ^ q)) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (seeleyEps a b n) := by
  have hf : ∀ j : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun s : ℝ => a j * (b j) ^ n * (1 - seeleyRho (b j * s))) := by
    intro j
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s : ℝ => 1 - seeleyRho (b j * s)) :=
      ContDiff.sub contDiff_const (seeleyRho_contDiff.comp (contDiff_const.mul contDiff_id))
    exact ContDiff.mul contDiff_const h2
  have hv : ∀ k : ℕ, (k : ℕ∞) ≤ (⊤ : ℕ∞) →
      Summable (fun j : ℕ => seeleyRhoDS k * |a j| * (b j) ^ (n + k)) := by
    intro k _
    simpa [mul_assoc] using (hsum (n + k)).mul_left (seeleyRhoDS k)
  have h'f : ∀ (k : ℕ) (j : ℕ) (x : ℝ), (k : ℕ∞) ≤ (⊤ : ℕ∞) →
      ‖iteratedFDeriv ℝ k (fun s : ℝ => a j * (b j) ^ n * (1 - seeleyRho (b j * s))) x‖
        ≤ seeleyRhoDS k * |a j| * (b j) ^ (n + k) := by
    intro k j x _
    have h := seeleyEps_term_bound_plain (a := a) hb n k j x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    calc |iteratedDeriv k (fun s : ℝ => a j * (b j) ^ n * (1 - seeleyRho (b j * s))) x|
        ≤ |a j| * (b j) ^ (n + k) * seeleyRhoDS k := h
      _ = seeleyRhoDS k * |a j| * (b j) ^ (n + k) := by ring
  exact contDiff_tsum (𝕜 := ℝ) (N := ⊤)
    (f := fun j : ℕ => fun s : ℝ => a j * (b j) ^ n * (1 - seeleyRho (b j * s)))
    (v := fun k j => seeleyRhoDS k * |a j| * (b j) ^ (n + k)) hf hv h'f

/-- The `k`-th derivative of `ε_n` is bounded by `(2|s|)^m` times the `(n+k+m)`-th moment. -/
theorem seeleyEps_iteratedDeriv_bound {a b : ℕ → ℝ} (hb : ∀ j : ℕ, 0 < b j)
    (hsum : ∀ q : ℕ, Summable (fun j : ℕ => |a j| * (b j) ^ q)) (n k m : ℕ) (s : ℝ) :
    |iteratedDeriv k (seeleyEps a b n) s|
      ≤ seeleyRhoDS k * (2 * |s|) ^ m * seeleyS a b (n + k + m) := by
  set f : ℕ → ℝ → ℝ := fun j s => a j * (b j) ^ n * (1 - seeleyRho (b j * s)) with hfdef
  have hf : ∀ j : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f j) := by
    intro j
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s : ℝ => 1 - seeleyRho (b j * s)) :=
      ContDiff.sub contDiff_const (seeleyRho_contDiff.comp (contDiff_const.mul contDiff_id))
    exact ContDiff.mul contDiff_const h2
  have hv : ∀ k' : ℕ, (k' : ℕ∞) ≤ (⊤ : ℕ∞) →
      Summable (fun j : ℕ => seeleyRhoDS k' * |a j| * (b j) ^ (n + k')) := by
    intro k' _
    simpa [mul_assoc] using (hsum (n + k')).mul_left (seeleyRhoDS k')
  have h'f : ∀ (k' : ℕ) (j : ℕ) (x : ℝ), (k' : ℕ∞) ≤ (⊤ : ℕ∞) →
      ‖iteratedFDeriv ℝ k' (f j) x‖ ≤ seeleyRhoDS k' * |a j| * (b j) ^ (n + k') := by
    intro k' j x _
    have h := seeleyEps_term_bound_plain (a := a) hb n k' j x
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
    calc |iteratedDeriv k' (fun s : ℝ => a j * (b j) ^ n * (1 - seeleyRho (b j * s))) x|
        ≤ |a j| * (b j) ^ (n + k') * seeleyRhoDS k' := h
      _ = seeleyRhoDS k' * |a j| * (b j) ^ (n + k') := by ring
  have hderiv : iteratedFDeriv ℝ k (seeleyEps a b n) s = ∑' j : ℕ, iteratedFDeriv ℝ k (f j) s :=
    iteratedFDeriv_tsum_apply hf hv h'f (k := k) le_top s
  have hmom : Summable (fun j : ℕ => seeleyRhoDS k * |a j| * (b j) ^ (n + k)) :=
    hv k le_top
  have hsumm : Summable (fun j : ℕ => ‖iteratedFDeriv ℝ k (f j) s‖) := by
    refine Summable.of_norm_bounded hmom (fun j => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact h'f k j s le_top
  have hsumm2 : Summable (fun j : ℕ =>
      (if 1 ≤ 2 * (b j) * |s| then |a j| * (b j) ^ (n + k) * seeleyRhoDS k else 0)) := by
    refine Summable.of_norm_bounded hmom (fun j => ?_)
    by_cases hc : 1 ≤ 2 * (b j) * |s|
    · rw [if_pos hc]
      have hnn : (0 : ℝ) ≤ |a j| * (b j) ^ (n + k) * seeleyRhoDS k :=
        mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (le_of_lt (hb j)) _))
          (seeleyRhoDS_nonneg k)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact le_of_eq (by ring)
    · rw [if_neg hc, norm_zero]
      exact mul_nonneg (mul_nonneg (seeleyRhoDS_nonneg k) (abs_nonneg _))
        (pow_nonneg (le_of_lt (hb j)) _)
  have hstep : ∑' j : ℕ, ‖iteratedFDeriv ℝ k (f j) s‖
      ≤ (2 * |s|) ^ m * (seeleyRhoDS k * seeleyS a b (n + k + m)) := by
    calc ∑' j : ℕ, ‖iteratedFDeriv ℝ k (f j) s‖
        ≤ ∑' j : ℕ,
            (if 1 ≤ 2 * (b j) * |s| then |a j| * (b j) ^ (n + k) * seeleyRhoDS k else 0) :=
          Summable.tsum_le_tsum (fun j => by
            rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
            exact seeleyEps_term_bound hb n k j s) hsumm hsumm2
      _ ≤ (2 * |s|) ^ m * (seeleyRhoDS k * seeleyS a b (n + k + m)) := by
          have hmain : ∀ j : ℕ,
              (if 1 ≤ 2 * (b j) * |s| then |a j| * (b j) ^ (n + k) * seeleyRhoDS k else 0)
                ≤ |a j| * (b j) ^ (n + k + m) * ((2 * |s|) ^ m * seeleyRhoDS k) := by
            intro j
            by_cases hc : 1 ≤ 2 * (b j) * |s|
            · rw [if_pos hc]
              have hbj : (1 : ℝ) ≤ (2 * (b j) * |s|) ^ m := one_le_pow₀ hc
              have hR := seeleyRhoDS_nonneg k
              have hpos : (0 : ℝ) ≤ |a j| * (b j) ^ (n + k) * seeleyRhoDS k :=
                mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (le_of_lt (hb j)) _)) hR
              calc |a j| * (b j) ^ (n + k) * seeleyRhoDS k
                  ≤ |a j| * (b j) ^ (n + k) * seeleyRhoDS k * (2 * (b j) * |s|) ^ m :=
                    le_mul_of_one_le_right hpos hbj
                _ = |a j| * (b j) ^ (n + k + m) * ((2 * |s|) ^ m * seeleyRhoDS k) := by
                    rw [mul_pow, pow_add]; ring
            · rw [if_neg hc]
              exact mul_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (le_of_lt (hb j)) _))
                (mul_nonneg (by positivity) (seeleyRhoDS_nonneg k))
          have hsum3 : Summable (fun j : ℕ =>
              |a j| * (b j) ^ (n + k + m) * ((2 * |s|) ^ m * seeleyRhoDS k)) := by
            have := (hsum (n + k + m)).mul_right ((2 * |s|) ^ m * seeleyRhoDS k)
            simpa [mul_assoc] using this
          calc ∑' j : ℕ,
                (if 1 ≤ 2 * (b j) * |s| then |a j| * (b j) ^ (n + k) * seeleyRhoDS k else 0)
              ≤ ∑' j : ℕ, |a j| * (b j) ^ (n + k + m) * ((2 * |s|) ^ m * seeleyRhoDS k) :=
                Summable.tsum_le_tsum hmain hsumm2 hsum3
            _ = seeleyS a b (n + k + m) * ((2 * |s|) ^ m * seeleyRhoDS k) := by
                rw [seeleyS, tsum_mul_right]
            _ = (2 * |s|) ^ m * (seeleyRhoDS k * seeleyS a b (n + k + m)) := by ring
  calc |iteratedDeriv k (seeleyEps a b n) s|
      = ‖iteratedFDeriv ℝ k (seeleyEps a b n) s‖ := by
        rw [← Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    _ = ‖∑' j : ℕ, iteratedFDeriv ℝ k (f j) s‖ := by rw [hderiv]
    _ ≤ ∑' j : ℕ, ‖iteratedFDeriv ℝ k (f j) s‖ := norm_tsum_le_tsum_norm hsumm
    _ ≤ (2 * |s|) ^ m * (seeleyRhoDS k * seeleyS a b (n + k + m)) := hstep
    _ = seeleyRhoDS k * (2 * |s|) ^ m * seeleyS a b (n + k + m) := by ring

/-- `ε_n` is smooth and its derivatives are flat at `0`, uniformly for `n ≤ n₀`, `k ≤ L`. -/
theorem seeleyEps_flat {a b : ℕ → ℝ} (hb : ∀ j : ℕ, 0 < b j)
    (hsum : ∀ q : ℕ, Summable (fun j : ℕ => |a j| * (b j) ^ q))
    (n₀ L : ℕ) :
    (∀ n : ℕ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (seeleyEps a b n)) ∧
    (∃ C r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ n ≤ n₀, ∀ s : ℝ, -r < s → s < r → ∀ k ≤ L,
      |iteratedDeriv k (seeleyEps a b n) s| ≤ C * |s| ^ L) := by
  refine ⟨fun n => seeleyEps_contDiff hb hsum n, ?_⟩
  have hB : ∀ k ≤ L, seeleyRhoDS k
      ≤ ∑ i ∈ Finset.range (L + 1), seeleyRhoDS i := by
    intro k hk
    refine Finset.single_le_sum (fun i _ => seeleyRhoDS_nonneg i) ?_
    rw [Finset.mem_range]; omega
  have hS : ∀ q ≤ n₀ + L + L, seeleyS a b q
      ≤ ∑ i ∈ Finset.range (n₀ + L + L + 1), seeleyS a b i := by
    intro q hq
    refine Finset.single_le_sum (fun i _ => seeleyS_nonneg hb i) ?_
    rw [Finset.mem_range]; omega
  refine ⟨2 ^ L * (∑ i ∈ Finset.range (L + 1), seeleyRhoDS i)
    * (∑ i ∈ Finset.range (n₀ + L + L + 1), seeleyS a b i), 1, one_pos, le_refl 1, ?_⟩
  intro n hn s hs1 hs2 k hk
  have hs : |s| < 1 := abs_lt.mpr ⟨hs1, hs2⟩
  have h1 := seeleyEps_iteratedDeriv_bound hb hsum n k L s
  have hBk := hB k hk
  have hSk := hS (n + k + L) (by omega)
  have hRnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range (L + 1), seeleyRhoDS i :=
    Finset.sum_nonneg fun i _ => seeleyRhoDS_nonneg i
  have hSnn : (0 : ℝ) ≤ ∑ i ∈ Finset.range (n₀ + L + L + 1), seeleyS a b i :=
    Finset.sum_nonneg fun i _ => seeleyS_nonneg hb i
  have hsL : (0 : ℝ) ≤ |s| ^ L := pow_nonneg (abs_nonneg s) L
  have h2 : seeleyRhoDS k * (2 * |s|) ^ L * seeleyS a b (n + k + L)
      ≤ 2 ^ L * (∑ i ∈ Finset.range (L + 1), seeleyRhoDS i)
        * (∑ i ∈ Finset.range (n₀ + L + L + 1), seeleyS a b i) * |s| ^ L := by
    rw [mul_pow]
    calc seeleyRhoDS k * (2 ^ L * |s| ^ L) * seeleyS a b (n + k + L)
        ≤ (∑ i ∈ Finset.range (L + 1), seeleyRhoDS i) * (2 ^ L * |s| ^ L)
            * (∑ i ∈ Finset.range (n₀ + L + L + 1), seeleyS a b i) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hBk (by positivity)) hSk
            (seeleyS_nonneg hb _) (mul_nonneg hRnn (by positivity))
      _ = 2 ^ L * (∑ i ∈ Finset.range (L + 1), seeleyRhoDS i)
            * (∑ i ∈ Finset.range (n₀ + L + L + 1), seeleyS a b i) * |s| ^ L := by ring
  exact h1.trans h2

end Work.Drive
