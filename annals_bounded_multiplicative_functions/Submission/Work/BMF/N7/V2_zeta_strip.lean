import Mathlib
import Submission.Work.BMF.zeta_approx_functional_eq
import Submission.Commons.Analysis.ExponentialSums.second_derivative_test
import Submission.Work.BMF.sdt_defs
import Submission.Work.BMF.zeta_approx.sdt_ioc_partial_sum
import Submission.Work.BMF.N7.sum_Ioc_dyadic_eq_range
import Submission.Work.BMF.N7.dyadic_vk_sum_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# V2 (conditional on V1): the `ζ`-strip bound

This file isolates the analytic core of `Work.BMF.N7.L_growth_VK_of_V1`: the growth bound
`‖ζ(σ+it)‖ ≤ A (log(|t|+3))^{6/7}` in the strip `σ ≥ 1 - c (log(|t|+3))^{-6/7}`, deduced from
the Vinogradov-exponential-sum hypothesis **V1** (in the explicit form `VKExpSumRaw` below,
which is literally `Work.BMF.VKExpSumRestrictedN7`'s body).

Route: Euler–Maclaurin (`Work.BMF.zeta_sub_Icc_sum_le`) with cutoff `N ≍ T·exp(2cζ L^{1/7})`,
then a dyadic decomposition `(2^j, min(2^{j+1},N)]` of the partial sum.  Blocks with `2^j < K₀`
are bounded trivially, blocks with `K₀ ≤ 2^j ≤ t` by V1 (Abel summation,
`Work.BMF.abel_ioc_block`), and blocks with `2^j > t` by the van der Corput second-derivative
test.
-/

open Finset Filter
open scoped Topology BigOperators

set_option maxHeartbeats 0

namespace Work.BMF.N7

noncomputable section

/-- **V1 in explicit form** (identical to `Work.BMF.VKExpSumRestrictedN7`). -/
def VKExpSumRaw : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (N t : ℝ), 2 ≤ N → N ≤ t →
    Real.log t ≤ c * Real.log N ^ (7 / 6 : ℝ) →
    ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ R : ℝ, N < R → R ≤ 2 * N →
      ‖∑ n ∈ Finset.Ioc ⌊N⌋₊ ⌊R⌋₊, ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤
        C * N ^ (1 - c * (Real.log N / Real.log t) ^ 2 /
          Real.log (Real.log t / Real.log N + 2))

lemma tendsto_cpow_shift (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    Tendsto (fun u : ℝ => ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ))))
      (𝓝 (0:ℝ)) (𝓝 (((n : ℂ)) ^ (-(Complex.I * (t : ℂ))))) := by
  have hmem : ((((n : ℝ) + 0 : ℝ)) : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.2 (by positivity)
  have houter : ContinuousAt (fun x : ℂ => x ^ (-(Complex.I * (t : ℂ)))) ((((n : ℝ) + 0 : ℝ)) : ℂ) :=
    continuousAt_cpow_const (b := -(Complex.I * (t : ℂ))) hmem
  have hinner : ContinuousAt (fun u : ℝ => ((((n : ℝ) + u : ℝ)) : ℂ)) 0 := by fun_prop
  have hc := ContinuousAt.comp' (g := fun x : ℂ => x ^ (-(Complex.I * (t : ℂ))))
    (f := fun u : ℝ => ((((n : ℝ) + u : ℝ)) : ℂ)) houter hinner
  simpa using hc.tendsto

/-- **V1 with the shift parameter `u` sent to `0`.** -/
theorem vk_exp_sum_zero (hV1 : VKExpSumRaw) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (K t : ℝ), 2 ≤ K → K ≤ t →
      Real.log t ≤ c * Real.log K ^ (7 / 6 : ℝ) →
      ∀ R : ℝ, K < R → R ≤ 2 * K →
        ‖∑ n ∈ Finset.Ioc ⌊K⌋₊ ⌊R⌋₊, (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤
          C * K ^ (1 - c * (Real.log K / Real.log t) ^ 2 /
            Real.log (Real.log t / Real.log K + 2)) := by
  obtain ⟨C, c, hC, hc, hb⟩ := hV1
  refine ⟨C, c, hC, hc, ?_⟩
  intro K t hK ht hlog R hKR hR2K
  have hsum : Tendsto
      (fun u : ℝ => ∑ n ∈ (Finset.Ioc ⌊K⌋₊ ⌊R⌋₊ : Finset ℕ),
        ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ))))
      (𝓝 (0:ℝ))
      (𝓝 (∑ n ∈ (Finset.Ioc ⌊K⌋₊ ⌊R⌋₊ : Finset ℕ),
        (n : ℂ) ^ (-(Complex.I * (t : ℂ))))) :=
    tendsto_finsetSum _ (fun n hn => tendsto_cpow_shift n (by
      have h1 := (Finset.mem_Ioc.mp hn).1
      omega) t)
  have hlim : Tendsto (fun u : ℝ => ‖∑ n ∈ (Finset.Ioc ⌊K⌋₊ ⌊R⌋₊ : Finset ℕ),
        ((((n : ℝ) + u : ℝ)) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖)
      (𝓝[>] (0:ℝ))
      (𝓝 ‖∑ n ∈ (Finset.Ioc ⌊K⌋₊ ⌊R⌋₊ : Finset ℕ),
        (n : ℂ) ^ (-(Complex.I * (t : ℂ)))‖) :=
    hsum.norm.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hlim ?_
  have hmem : ∀ᶠ u : ℝ in 𝓝[>] (0:ℝ), u ≤ 1 :=
    (eventually_le_nhds (by norm_num : (0:ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hmem] with u hu0 hu1
  exact hb K t hK ht hlog u hu0 hu1 R hKR hR2K

/-! ## Elementary block lemmas -/

/-- The summand of the `L`-series factors as an oscillating times a monotone weight. -/
lemma cpow_split (n : ℕ) (hn : 1 ≤ n) (σ t : ℝ) :
    (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
      = (n : ℂ) ^ (-(Complex.I * (t : ℂ))) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  have hn0 : (n : ℂ) ≠ 0 := by
    have hpos : 0 < n := by omega
    exact_mod_cast (ne_of_gt hpos)
  have h1 : (((-σ : ℝ)) : ℂ) = -(σ : ℂ) := by push_cast; ring
  have h2 : (((n : ℝ) ^ (-σ) : ℝ) : ℂ) = (n : ℂ) ^ (-(σ : ℂ)) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n) (-σ), h1]
    norm_num
  rw [show -((σ : ℂ) + (t : ℂ) * Complex.I) = (-(σ : ℂ)) + (-(Complex.I * (t : ℂ))) by ring]
  rw [Complex.cpow_add _ _ hn0, ← h2, mul_comm]

lemma rpow_neg_antitone_nat {σ : ℝ} (hσ : 0 < σ) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (n : ℝ) ^ (-σ) ≤ (m : ℝ) ^ (-σ) := by
  have hm0 : (0:ℝ) < (m:ℝ) := by positivity
  have hmn' : (m:ℝ) ≤ (n:ℝ) := by exact_mod_cast hmn
  have h := Real.rpow_le_rpow_of_nonpos hm0 hmn' (by linarith : -σ ≤ 0)
  simpa using h

/-- **Abel block bound.** If all exponential sums `Σ_{K<n≤h} n^{-it}` over `h ≤ R` are bounded
by `V`, then the block `Σ_{K<n≤R} n^{-σ-it}` is bounded by `V·K^{-σ}`. -/
lemma dsum_block_bound {K R : ℕ} {σ t V : ℝ} (hK1 : 1 ≤ K) (hKR : K < R) (hV0 : 0 ≤ V)
    (hσ : 0 < σ)
    (hV : ∀ h, K ≤ h → h ≤ R →
      ‖∑ h' ∈ Finset.Ioc K h, (h' : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ V) :
    ‖∑ n ∈ Finset.Ioc K R, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
      ≤ V * (K : ℝ) ^ (-σ) := by
  have hsum : ∑ n ∈ Finset.Ioc K R, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
      = ∑ n ∈ Finset.Ioc K R,
          (n : ℂ) ^ (-(Complex.I * (t : ℂ))) * (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl (fun n hn => ?_)
    refine cpow_split n ?_ σ t
    have h1 := (Finset.mem_Ioc.mp hn).1
    omega
  rw [hsum]
  refine le_trans (abel_ioc_block K R _ (fun n => (n : ℝ) ^ (-σ)) V hKR hV0 ?_ ?_ ?_ hV) le_rfl
  · intro h hh
    have h1 : 1 ≤ h := le_trans hK1 hh
    exact rpow_neg_antitone_nat (m := h) (n := h + 1) hσ h1 (by omega)
  · exact Real.rpow_nonneg (by positivity) _
  · exact Real.rpow_nonneg (by positivity) _

/-- Trivial block bound: `‖Σ_{K<n≤R} n^{-σ-it}‖ ≤ K^{1-σ}` when `1 ≤ K < R ≤ 2K`. -/
lemma trivial_block_bound {K R : ℕ} {σ t : ℝ} (hK1 : 1 ≤ K) (hσ : 0 < σ)
    (hKR : K < R) (hR : R ≤ 2 * K) :
    ‖∑ n ∈ Finset.Ioc K R, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
      ≤ (K : ℝ) ^ (1 - σ) := by
  have h1 : ∀ n ∈ Finset.Ioc K R, ‖(n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
      = (n : ℝ) ^ (-σ) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have h1 := (Finset.mem_Ioc.mp hn).1
      exact_mod_cast (by omega : 0 < n)
    have hcast : ((n : ℕ) : ℂ) = (((n : ℝ)) : ℂ) := by push_cast; norm_num
    rw [hcast, Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    congr 1
    simp [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
  calc ‖∑ n ∈ Finset.Ioc K R, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
      ≤ ∑ n ∈ Finset.Ioc K R, ‖(n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ :=
        norm_sum_le _ _
    _ = ∑ n ∈ Finset.Ioc K R, (n : ℝ) ^ (-σ) := Finset.sum_congr rfl h1
    _ ≤ ∑ _n ∈ Finset.Ioc K R, (K : ℝ) ^ (-σ) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        have hnK : K ≤ n := (Finset.mem_Ioc.mp hn).1.le
        exact rpow_neg_antitone_nat (m := K) (n := n) hσ hK1 hnK
    _ = ((Finset.Ioc K R).card : ℝ) * (K : ℝ) ^ (-σ) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (K : ℝ) * (K : ℝ) ^ (-σ) := by
        have hcard : ((Finset.Ioc K R).card : ℝ) ≤ (K : ℝ) := by
          have hc : (Finset.Ioc K R).card = R - K := by simp
          have : R - K ≤ K := by omega
          rw [hc]
          exact_mod_cast this
        exact mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (by positivity) _)
    _ = (K : ℝ) ^ (1 - σ) := by
        have h2 : (1 : ℝ) - σ = 1 + (-σ) := by ring
        rw [h2, Real.rpow_add (by positivity : (0 : ℝ) < (K : ℝ)), Real.rpow_one]

/-- Division monotonicity, elementary form. -/
lemma div_le_div_aux {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (hc : 0 < c) (h : c ≤ b) :
    a / b ≤ a / c := by
  have h1 : a / c - a / b = a * (b - c) / (c * b) := by
    field_simp
  have h2 : 0 ≤ a * (b - c) / (c * b) :=
    div_nonneg (mul_nonneg ha (by linarith)) (by positivity)
  linarith [h1, h2]

/-- **Main theorem.** -/
theorem zeta_strip_bound_of_vk_aux (hV1 : VKExpSumRaw)
    (hArith : ∀ c₀ cζ : ℝ, 0 < c₀ → 0 < cζ → ∃ A : ℝ, 0 < A ∧ ∀ (L δ : ℝ) (j₀ J : ℕ),
      3 ≤ L → 0 ≤ δ → δ ≤ cζ * L ^ (-(6 / 7 : ℝ)) →
      (L / c₀) ^ (6 / 7 : ℝ) ≤ (j₀ : ℝ) * Real.log 2 →
      1 ≤ (j₀ : ℝ) * Real.log 2 →
      j₀ ≤ J → (J : ℝ) * Real.log 2 ≤ L + 2 →
      (∑ j ∈ Finset.Icc j₀ (J - 1),
          (2 : ℝ) ^ ((j : ℝ) * (δ - c₀ * (((j : ℝ) * Real.log 2) / L) ^ 2 /
            Real.log (L / ((j : ℝ) * Real.log 2) + 2)))) ≤ A * L ^ (6 / 7 : ℝ)) :
    ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∀ σ t : ℝ, 3 ≤ |t| →
      1 - c * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        A * Real.log (|t| + 3) ^ (6 / 7 : ℝ) := by
  obtain ⟨C₁, c₁, hC₁, hc₁, hVK⟩ := hV1
  obtain ⟨C₂, c₂, hC₂, hc₂, hVK0⟩ := vk_exp_sum_zero ⟨C₁, c₁, hC₁, hc₁, hVK⟩
  obtain ⟨C₀sdt, hC₀sdt, hsdt0⟩ :=
    Commons.Analysis.ExponentialSums.second_derivative_test (B := 4) (by norm_num)
  obtain ⟨C₃, hC₃, hSDT⟩ := Work.BMF.zeta_approx.sdt_ioc_partial_sum
    ⟨C₀sdt, hC₀sdt, fun {a} {n} hn f r hr hf hpp => hsdt0 hn f hr hf hpp⟩
  set cζ : ℝ := min 1 c₂ / 4 with hcζdef
  have hcζpos : 0 < cζ := by
    have h : 0 < min 1 c₂ := lt_min zero_lt_one hc₂
    rw [hcζdef]; positivity
  obtain ⟨Ablk, hAblk0, hAblk⟩ := hArith c₂ cζ hc₂ hcζpos
  -- the final multiplicative constant
  set Apart : ℝ := 1 + 2 * Real.exp (cζ / c₂ ^ (6 / 7 : ℝ) + 1) / (Real.log 2 * c₂ ^ (6 / 7 : ℝ))
      + C₂ * Ablk + C₃ * (1 + Real.sqrt (8 * Real.pi)) with hApart
  -- the "large L" conditions
  let Cond : ℝ → Prop := fun L =>
    (3 ≤ L) ∧ (cζ * L ^ (-(6 / 7 : ℝ)) ≤ 1 / 2) ∧
    (Real.log 2 ≤ cζ * L ^ (1 / 7 : ℝ) / 2) ∧
    (cζ * L ^ (1 / 7 : ℝ) + 4 * cζ * L ^ (-(6 / 7 : ℝ)) + 4 * cζ ^ 2 * L ^ (-(5 / 7 : ℝ))
        + 4 ≤ L / 2) ∧
    (2 * cζ * L ^ (1 / 7 : ℝ) / Real.log 2 + 5 ≤ L ^ (6 / 7 : ℝ)) ∧
    (Real.log 2 ≤ (L / c₂) ^ (6 / 7 : ℝ)) ∧ (c₂ ≤ L) ∧
    ((L / c₂) ^ (6 / 7 : ℝ) + 4 ≤ L) ∧
    (cζ * Real.log 2 * L ^ (-(6 / 7 : ℝ)) ≤ 1) ∧ (4 * cζ ≤ L ^ (6 / 7 : ℝ))
  have hev : ∀ᶠ L : ℝ in atTop, Cond L := by
    have h1 : ∀ᶠ L : ℝ in atTop, 3 ≤ L := eventually_ge_atTop 3
    have h2 : ∀ᶠ L : ℝ in atTop, cζ * L ^ (-(6 / 7 : ℝ)) ≤ 1 / 2 := by
      have h : Tendsto (fun L : ℝ => cζ * L ^ (-(6 / 7 : ℝ))) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 6/7)).const_mul cζ
      exact h.eventually (eventually_le_nhds (by norm_num))
    have h3 : ∀ᶠ L : ℝ in atTop, Real.log 2 ≤ cζ * L ^ (1 / 7 : ℝ) / 2 := by
      have h4 : ∀ᶠ L : ℝ in atTop, 2 * Real.log 2 / cζ ≤ L ^ (1 / 7 : ℝ) :=
        (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/7)).eventually_ge_atTop _
      filter_upwards [h4] with L hL
      rw [div_le_iff₀ hcζpos] at hL
      rw [le_div_iff₀ (by norm_num : (0:ℝ) < 2)]
      linarith
    have h4 : ∀ᶠ L : ℝ in atTop,
        cζ * L ^ (1 / 7 : ℝ) + 4 * cζ * L ^ (-(6 / 7 : ℝ)) + 4 * cζ ^ 2 * L ^ (-(5 / 7 : ℝ))
          + 4 ≤ L / 2 := by
      have ha : ∀ᶠ L : ℝ in atTop, cζ * L ^ (1 / 7 : ℝ) ≤ L / 4 := by
        have h5 : ∀ᶠ L : ℝ in atTop, 4 * cζ ≤ L ^ (6 / 7 : ℝ) :=
          (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 6/7)).eventually_ge_atTop _
        filter_upwards [h5, eventually_gt_atTop (0:ℝ)] with L hL hLpos
        have hLr : 0 < L ^ (1/7:ℝ) := Real.rpow_pos_of_pos hLpos _
        have hmul := mul_le_mul_of_nonneg_right hL hLr.le
        rw [← Real.rpow_add hLpos (6/7) (1/7)] at hmul
        have hsum : (6/7:ℝ) + 1/7 = 1 := by norm_num
        rw [hsum, Real.rpow_one] at hmul
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
        linarith
      have hb : ∀ᶠ L : ℝ in atTop,
          4 * cζ * L ^ (-(6 / 7 : ℝ)) + 4 * cζ ^ 2 * L ^ (-(5 / 7 : ℝ)) + 4 ≤ L / 4 := by
        have hb1 : ∀ᶠ L : ℝ in atTop,
            4 * cζ * L ^ (-(6 / 7 : ℝ)) + 4 * cζ ^ 2 * L ^ (-(5 / 7 : ℝ)) ≤ 1 := by
          have h : Tendsto (fun L : ℝ => 4 * cζ * L ^ (-(6 / 7 : ℝ)) + 4 * cζ ^ 2 * L ^ (-(5 / 7 : ℝ)))
              atTop (𝓝 0) := by
            have h1' : Tendsto (fun L : ℝ => 4 * cζ * L ^ (-(6 / 7 : ℝ))) atTop (𝓝 0) := by
              simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 6/7)).const_mul (4 * cζ)
            have h2' : Tendsto (fun L : ℝ => 4 * cζ ^ 2 * L ^ (-(5 / 7 : ℝ))) atTop (𝓝 0) := by
              simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 5/7)).const_mul (4 * cζ ^ 2)
            simpa using h1'.add h2'
          exact h.eventually (eventually_le_nhds (by norm_num))
        have hb2 : ∀ᶠ L : ℝ in atTop, 5 ≤ L / 4 := by
          filter_upwards [eventually_ge_atTop (20:ℝ)] with L hL
          linarith
        filter_upwards [hb1, hb2] with L hL1 hL2
        linarith
      filter_upwards [ha, hb] with L hLa hLb
      linarith
    have h5 : ∀ᶠ L : ℝ in atTop, 2 * cζ * L ^ (1 / 7 : ℝ) / Real.log 2 + 5 ≤ L ^ (6 / 7 : ℝ) := by
      have hz : Tendsto (fun L : ℝ => 2 * cζ / Real.log 2 * L ^ (-(5 / 7 : ℝ)) + 5 * L ^ (-(6 / 7 : ℝ)))
          atTop (𝓝 0) := by
        have h1' : Tendsto (fun L : ℝ => 2 * cζ / Real.log 2 * L ^ (-(5 / 7 : ℝ))) atTop (𝓝 0) := by
          simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 5/7)).const_mul (2 * cζ / Real.log 2)
        have h2' : Tendsto (fun L : ℝ => 5 * L ^ (-(6 / 7 : ℝ))) atTop (𝓝 0) := by
          simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 6/7)).const_mul 5
        simpa using h1'.add h2'
      filter_upwards [hz.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1)),
                      eventually_gt_atTop (0:ℝ)] with L hL hLpos
      have hL67 : 0 < L ^ (6/7:ℝ) := Real.rpow_pos_of_pos hLpos _
      have e1 : 2 * cζ / Real.log 2 * L ^ (-(5/7:ℝ)) * L ^ (6/7:ℝ)
          = 2 * cζ / Real.log 2 * L ^ (1/7:ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hLpos]
        norm_num
      have e2 : 5 * L ^ (-(6/7:ℝ)) * L ^ (6/7:ℝ) = 5 := by
        rw [mul_assoc, ← Real.rpow_add hLpos]
        norm_num
      have hm := mul_le_mul_of_nonneg_right hL hL67.le
      rw [add_mul, e1, e2] at hm
      have hgoal : 2 * cζ * L ^ (1/7:ℝ) / Real.log 2 + 5 = 2 * cζ / Real.log 2 * L ^ (1/7:ℝ) + 5 := by
        ring
      rw [hgoal]
      linarith [hm]
    have h6 : ∀ᶠ L : ℝ in atTop, Real.log 2 ≤ (L / c₂) ^ (6 / 7 : ℝ) := by
      have h : Tendsto (fun L : ℝ => (L / c₂) ^ (6 / 7 : ℝ)) atTop atTop := by
        have h7 : Tendsto (fun L : ℝ => L / c₂) atTop atTop := tendsto_id.atTop_div_const hc₂
        exact (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 6/7)).comp h7
      exact h.eventually_ge_atTop _
    have h7 : ∀ᶠ L : ℝ in atTop, c₂ ≤ L := eventually_ge_atTop c₂
    have h8 : ∀ᶠ L : ℝ in atTop, (L / c₂) ^ (6 / 7 : ℝ) + 4 ≤ L := by
      have hA : ∀ᶠ L : ℝ in atTop, 2 * c₂ ^ (-(6/7:ℝ)) ≤ L ^ (1/7:ℝ) :=
        (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1/7)).eventually_ge_atTop _
      filter_upwards [hA, eventually_ge_atTop (8:ℝ), eventually_gt_atTop (0:ℝ)] with L hA hL4 hLpos
      have hdiv : (L / c₂) ^ (6/7:ℝ) = L ^ (6/7:ℝ) * c₂ ^ (-(6/7:ℝ)) := by
        rw [Real.div_rpow hLpos.le (le_of_lt hc₂) (6/7:ℝ), div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hc₂)]
      have hL67 : 0 < L ^ (6/7:ℝ) := Real.rpow_pos_of_pos hLpos _
      have hmul := mul_le_mul_of_nonneg_right hA hL67.le
      rw [← Real.rpow_add hLpos (1/7) (6/7)] at hmul
      have hsum : (1/7:ℝ) + 6/7 = 1 := by norm_num
      rw [hsum, Real.rpow_one] at hmul
      rw [hdiv]
      have hmul' : L ^ (6/7:ℝ) * c₂ ^ (-(6/7:ℝ)) ≤ L / 2 := by
        rw [show L ^ (6/7:ℝ) * c₂ ^ (-(6/7:ℝ)) = (2 * c₂ ^ (-(6/7:ℝ)) * L ^ (6/7:ℝ)) / 2 by ring]
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
        linarith [hmul]
      linarith [hmul', hL4]
    have h9 : ∀ᶠ L : ℝ in atTop, cζ * Real.log 2 * L ^ (-(6 / 7 : ℝ)) ≤ 1 := by
      have h : Tendsto (fun L : ℝ => cζ * Real.log 2 * L ^ (-(6 / 7 : ℝ))) atTop (𝓝 0) := by
        simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 6/7)).const_mul (cζ * Real.log 2)
      exact h.eventually (eventually_le_nhds (by norm_num))
    have h10 : ∀ᶠ L : ℝ in atTop, 4 * cζ ≤ L ^ (6 / 7 : ℝ) :=
      (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 6/7)).eventually_ge_atTop _
    filter_upwards [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10] with L m1 m2 m3 m4 m5 m6 m7 m8 m9 m10
    exact ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10⟩
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp hev
  have hL₀3 : 3 ≤ L₀ := (hL₀ L₀ le_rfl).1
  have hApartpos : 0 < Apart + 2 := by
    rw [hApart]; positivity
  refine ⟨max (Apart + 2) ((1 + 1/3 + (2 + Real.exp L₀) / (1/2)) / (Real.log 6) ^ (6/7:ℝ)),
    cζ, lt_of_lt_of_le hApartpos (le_max_left _ _), hcζpos, ?_⟩
  -- ============ main statement ============
  have key : ∀ σ t : ℝ, 3 ≤ t → 1 - cζ * Real.log (t + 3) ^ (-(6 / 7 : ℝ)) ≤ σ → σ ≤ 2 →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        Real.log (t + 3) ^ (6 / 7 : ℝ) * max (Apart + 2)
          ((1 + 1/3 + (2 + Real.exp L₀) / (1/2)) / (Real.log 6) ^ (6/7:ℝ)) := by
    intro σ t ht3 hσlo hσhi
    set L : ℝ := Real.log (t + 3) with hLdef
    set δp : ℝ := max (1 - σ) 0 with hδpdef
    have hδp0 : 0 ≤ δp := le_max_right _ _
    have hδple : δp ≤ cζ * L ^ (-(6/7:ℝ)) := by
      by_cases h : 1 - σ ≤ 0
      · rw [hδpdef, max_eq_right h]
        exact mul_nonneg hcζpos.le (Real.rpow_nonneg (by rw [hLdef]; exact Real.log_nonneg (by linarith)) _)
      · rw [hδpdef, max_eq_left (le_of_lt (not_le.mp h))]
        linarith [hσlo]
    have hTpos : 0 < t + 3 := by linarith
    have hLpos : 0 < L := by rw [hLdef]; exact Real.log_pos (by linarith)
    have htpos : 0 < t := by linarith
    have hcζle : cζ ≤ 1/4 := by
      rw [hcζdef]
      have := min_le_left (1:ℝ) c₂
      linarith
    have hL1 : 1 ≤ L := by
      rw [hLdef, Real.le_log_iff_exp_le (by linarith : (0:ℝ) < t + 3)]
      linarith [Real.exp_one_lt_d9]
    have hσhalf0 : 1/2 ≤ σ := by
      have h1 : L ^ (-(6/7:ℝ)) ≤ 1 := by
        rw [Real.rpow_neg (le_of_lt hLpos)]
        exact inv_le_one_of_one_le₀ (Real.one_le_rpow hL1 (by norm_num))
      have h2 : cζ * L ^ (-(6/7:ℝ)) ≤ 1/4 := by nlinarith [hcζpos, h1, hcζle]
      linarith [hσlo, h2]
    have hσpos : 0 < σ := by linarith [hσhalf0]
    by_cases hLbig : L₀ ≤ L
    · obtain ⟨hA, hB, hC, hD, hE, hF, hG, hH, hI, hJ⟩ := hL₀ L hLbig
      have hσhalf : 1/2 ≤ σ := by linarith [hσlo, hB]
      have hlogt_le : Real.log t ≤ L := by
        rw [hLdef]; exact Real.log_le_log (by linarith) (by linarith)
      have hlogt_ge : L - Real.log 2 ≤ Real.log t := by
        have h2t : (t + 3) ≤ 2 * t := by linarith
        have h := Real.log_le_log hTpos h2t
        rw [Real.log_mul (by norm_num) (by linarith : t ≠ 0)] at h
        rw [← hLdef] at h; linarith
      -- ===== the Euler-Maclaurin cutoff =====
      set E : ℝ := Real.exp (2 * cζ * L ^ (1/7:ℝ)) with hEdef
      have hE1 : 1 ≤ E := by rw [hEdef]; exact Real.one_le_exp (by positivity)
      have hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE1
      set N : ℕ := ⌈(t + 3) * E⌉₊ with hNdef
      have hNlow : (t + 3) * E ≤ (N:ℝ) := Nat.le_ceil _
      have hNup : (N:ℝ) ≤ 2 * ((t + 3) * E) := by
        have h1 : ((N:ℝ)) < (t + 3) * E + 1 := by
          rw [hNdef]; exact Nat.ceil_lt_add_one (by positivity)
        nlinarith [h1, hTpos, hE1]
      have hN1 : 1 ≤ N := by
        have h1 : (1:ℝ) ≤ (N:ℝ) := le_trans (by nlinarith [hTpos, hE1]) hNlow
        exact_mod_cast h1
      have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
      have htN : t < (N:ℝ) := by nlinarith [hNlow, hE1, hTpos]
      have hlogN_le : Real.log N ≤ L + Real.log 2 + 2 * cζ * L ^ (1/7:ℝ) := by
        have h1 : Real.log N ≤ Real.log (2 * ((t + 3) * E)) := Real.log_le_log hNpos hNup
        have h2 : Real.log (2 * ((t + 3) * E)) = Real.log 2 + (L + 2 * cζ * L ^ (1/7:ℝ)) := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by linarith) (by positivity),
            hEdef, Real.log_exp, hLdef]
        rw [h2] at h1; linarith
      have hlogN_ge : L + 2 * cζ * L ^ (1/7:ℝ) ≤ Real.log N := by
        have h1 : Real.log ((t + 3) * E) ≤ Real.log N := Real.log_le_log (by positivity) hNlow
        have h2 : Real.log ((t + 3) * E) = L + 2 * cζ * L ^ (1/7:ℝ) := by
          rw [Real.log_mul (by linarith) (ne_of_gt hEpos), hEdef, Real.log_exp, hLdef]
        rw [h2] at h1; exact h1
      -- ===== Euler-Maclaurin errors =====
      have hEM := zeta_sub_Icc_sum_le hσpos (by linarith : t ≠ 0) N hN1
      have herr1 : (N:ℝ)^(1-σ)/|t| ≤ 1 := by
        rw [abs_of_pos htpos]
        have h1 : (N:ℝ)^(1-σ) ≤ (N:ℝ)^δp :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (le_max_left _ _)
        have h2 : (N:ℝ)^δp = Real.exp (δp * Real.log N) := by
          rw [Real.rpow_def_of_pos hNpos δp]; congr 1; ring
        have h3 : δp * Real.log N ≤ δp * (L + Real.log 2 + 2 * cζ * L ^ (1/7:ℝ)) :=
          mul_le_mul_of_nonneg_left hlogN_le hδp0
        have h4 : δp * (L + Real.log 2 + 2 * cζ * L ^ (1/7:ℝ)) ≤ cζ * L ^ (-(6/7:ℝ)) *
            (L + Real.log 2 + 2 * cζ * L ^ (1/7:ℝ)) :=
          mul_le_mul_of_nonneg_right hδple (by positivity)
        have h5 : cζ * L ^ (-(6/7:ℝ)) * (L + Real.log 2 + 2 * cζ * L ^ (1/7:ℝ))
            ≤ L / 2 - Real.log 2 := by
          have e : cζ * L ^ (-(6/7:ℝ)) * (L + Real.log 2 + 2 * cζ * L ^ (1/7:ℝ))
              = cζ * L ^ (1/7:ℝ) + cζ * Real.log 2 * L ^ (-(6/7:ℝ))
                + 2 * cζ ^ 2 * L ^ (-(5/7:ℝ)) := by
            rw [mul_add, mul_add]
            have e1 : cζ * L ^ (-(6/7:ℝ)) * L = cζ * L ^ (1/7:ℝ) := by
              have h1 : L ^ (-(6/7:ℝ)) * L ^ (1:ℝ) = L ^ (1/7:ℝ) := by
                rw [← Real.rpow_add hLpos]; norm_num
              rw [Real.rpow_one] at h1
              rw [mul_assoc, h1]
            have e2 : cζ * L ^ (-(6/7:ℝ)) * Real.log 2 = cζ * Real.log 2 * L ^ (-(6/7:ℝ)) := by ring
            have e3 : cζ * L ^ (-(6/7:ℝ)) * (2 * cζ * L ^ (1/7:ℝ)) = 2 * cζ ^ 2 * L ^ (-(5/7:ℝ)) := by
              rw [show cζ * L ^ (-(6/7:ℝ)) * (2 * cζ * L ^ (1/7:ℝ))
                  = 2 * cζ ^ 2 * (L ^ (-(6/7:ℝ)) * L ^ (1/7:ℝ)) by ring,
                ← Real.rpow_add hLpos]
              norm_num
            rw [e1, e2, e3]
          rw [e]
          have hlog2le2 : Real.log 2 ≤ 2 := Real.log_le_self (by norm_num)
          have hD' : cζ * L ^ (1/7:ℝ) + cζ * Real.log 2 * L ^ (-(6/7:ℝ))
              + 2 * cζ ^ 2 * L ^ (-(5/7:ℝ)) ≤ L/2 - Real.log 2 := by
            have h5 : cζ * Real.log 2 * L ^ (-(6/7:ℝ)) ≤ 2 * cζ * L ^ (-(6/7:ℝ)) := by
              have h6 : cζ * L ^ (-(6/7:ℝ)) * Real.log 2 ≤ cζ * L ^ (-(6/7:ℝ)) * 2 :=
                mul_le_mul_of_nonneg_left hlog2le2 (mul_nonneg hcζpos.le (Real.rpow_nonneg hLpos.le _))
              linarith [h6]
            have h6p := Real.rpow_pos_of_pos hLpos (-(6/7:ℝ))
            have h7p := Real.rpow_pos_of_pos hLpos (-(5/7:ℝ))
            have h8p : cζ * L ^ (1/7:ℝ) + 2 * cζ * L ^ (-(6/7:ℝ)) + 2 * cζ ^ 2 * L ^ (-(5/7:ℝ))
                ≤ cζ * L ^ (1/7:ℝ) + 4 * cζ * L ^ (-(6/7:ℝ)) + 4 * cζ ^ 2 * L ^ (-(5/7:ℝ)) := by
              nlinarith [h6p, h7p, hcζpos]
            have h9p : cζ * L ^ (1/7:ℝ) + 4 * cζ * L ^ (-(6/7:ℝ)) + 4 * cζ ^ 2 * L ^ (-(5/7:ℝ))
                ≤ L / 2 - 4 := by linarith [hD]
            calc cζ * L ^ (1/7:ℝ) + cζ * Real.log 2 * L ^ (-(6/7:ℝ)) + 2 * cζ ^ 2 * L ^ (-(5/7:ℝ))
                ≤ cζ * L ^ (1/7:ℝ) + 2 * cζ * L ^ (-(6/7:ℝ)) + 2 * cζ ^ 2 * L ^ (-(5/7:ℝ)) := by
                  linarith [h5]
              _ ≤ cζ * L ^ (1/7:ℝ) + 4 * cζ * L ^ (-(6/7:ℝ)) + 4 * cζ ^ 2 * L ^ (-(5/7:ℝ)) := h8p
              _ ≤ L / 2 - Real.log 2 := by linarith [h9p, Real.log_two_lt_d9]
          exact hD'
        have h6 : (N:ℝ)^(1-σ) ≤ Real.exp (L/2 - Real.log 2) := by
          rw [h2] at h1
          exact le_trans h1 (Real.exp_le_exp.mpr (le_trans h3 (le_trans h4 h5)))
        have h7 : Real.exp (L/2 - Real.log 2) ≤ t := by
          have h8 : Real.exp (L/2 - Real.log 2) ≤ Real.exp (Real.log t) :=
            Real.exp_le_exp.mpr (by linarith)
          rwa [Real.exp_log htpos] at h8
        exact (div_le_one htpos).mpr (le_trans h6 h7)
      have herr2 : (‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ / σ) * (N:ℝ)^(-σ) ≤ 1 := by
        have hsn : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ t + 3 := by
          have h1 : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ σ + t := by
            have h := norm_add_le ((σ : ℂ)) ((t : ℂ) * Complex.I)
            simp only [Complex.norm_real, Complex.norm_mul, Complex.norm_I, mul_one,
              Real.norm_eq_abs, abs_of_pos hσpos, abs_of_pos htpos] at h
            exact h
          linarith [hσhi]
        have hNσ : (N:ℝ)^(-σ) ≤ Real.exp (-(L + 2 * cζ * L ^ (1/7:ℝ)) * σ) := by
          rw [Real.rpow_def_of_pos hNpos]
          refine Real.exp_le_exp.mpr ?_
          nlinarith [hlogN_ge, hσpos]
        have hσsplit : -(L + 2 * cζ * L ^ (1/7:ℝ)) * σ
            ≤ -L - cζ * L ^ (1/7:ℝ) + 2 * cζ ^ 2 * L ^ (-(5/7:ℝ)) := by
          have hδ1 : 1 - σ ≤ δp := le_max_left _ _
          have hδL : (1 - σ) * L ≤ cζ * L ^ (1/7:ℝ) := by
            have h1 : (1 - σ) * L ≤ δp * L := mul_le_mul_of_nonneg_right hδ1 hLpos.le
            have h2 : δp * L ≤ cζ * L ^ (-(6/7:ℝ)) * L := mul_le_mul_of_nonneg_right hδple hLpos.le
            have h3 : cζ * L ^ (-(6/7:ℝ)) * L = cζ * L ^ (1/7:ℝ) := by
              have h1 : L ^ (-(6/7:ℝ)) * L ^ (1:ℝ) = L ^ (1/7:ℝ) := by
                rw [← Real.rpow_add hLpos]; norm_num
              rw [Real.rpow_one] at h1
              rw [mul_assoc, h1]
            rw [h3] at h2; linarith
          have hδL2 : (1 - σ) * (2 * cζ * L ^ (1/7:ℝ)) ≤ 2 * cζ ^ 2 * L ^ (-(5/7:ℝ)) := by
            have h1 : (1 - σ) * (2 * cζ * L ^ (1/7:ℝ)) ≤ δp * (2 * cζ * L ^ (1/7:ℝ)) :=
              mul_le_mul_of_nonneg_right hδ1 (by positivity)
            have h2 : δp * (2 * cζ * L ^ (1/7:ℝ)) ≤ (cζ * L ^ (-(6/7:ℝ))) * (2 * cζ * L ^ (1/7:ℝ)) :=
              mul_le_mul_of_nonneg_right hδple (by positivity)
            have h3 : (cζ * L ^ (-(6/7:ℝ))) * (2 * cζ * L ^ (1/7:ℝ))
                = 2 * cζ ^ 2 * L ^ (-(5/7:ℝ)) := by
              rw [show (cζ * L ^ (-(6/7:ℝ))) * (2 * cζ * L ^ (1/7:ℝ))
                  = 2 * cζ ^ 2 * (L ^ (-(6/7:ℝ)) * L ^ (1/7:ℝ)) by ring,
                ← Real.rpow_add hLpos]
              norm_num
            rw [h3] at h2; linarith
          have hexp : -(L + 2 * cζ * L ^ (1/7:ℝ)) * σ
              = -L - 2 * cζ * L ^ (1/7:ℝ) + (1 - σ) * L + (1 - σ) * (2 * cζ * L ^ (1/7:ℝ)) := by
            ring
          rw [hexp]; linarith
        have hstep1 : (N:ℝ)^(-σ) ≤ Real.exp (-L - cζ * L ^ (1/7:ℝ) + 2 * cζ ^ 2 * L ^ (-(5/7:ℝ))) :=
          le_trans hNσ (Real.exp_le_exp.mpr hσsplit)
        have hstep2 : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ * (N:ℝ)^(-σ)
            ≤ Real.exp (L) * Real.exp (-L - cζ * L ^ (1/7:ℝ) + 2 * cζ ^ 2 * L ^ (-(5/7:ℝ))) := by
          have hsn' : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ Real.exp L := by
            rw [hLdef, Real.exp_log hTpos]; exact hsn
          exact mul_le_mul hsn' hstep1 (by positivity) (by positivity)
        have hstep3 : (2 * cζ ^ 2 * L ^ (-(5/7:ℝ))) ≤ cζ * L ^ (1/7:ℝ) / 2 := by
          have h1 : 4 * cζ * L ^ (-(6/7:ℝ)) ≤ 1 := by
            have h2 : L ^ (-(6/7:ℝ)) * L ^ (6/7:ℝ) = 1 := by
              rw [← Real.rpow_add hLpos]; norm_num
            nlinarith [h2, hJ, Real.rpow_pos_of_pos hLpos (-(6/7:ℝ)),
              Real.rpow_pos_of_pos hLpos (6/7:ℝ)]
          have h2 : 2 * cζ ^ 2 * L ^ (-(5/7:ℝ)) = cζ * L ^ (1/7:ℝ) * (2 * cζ * L ^ (-(6/7:ℝ))) := by
            rw [show cζ * L ^ (1/7:ℝ) * (2 * cζ * L ^ (-(6/7:ℝ)))
                = 2 * cζ ^ 2 * (L ^ (1/7:ℝ) * L ^ (-(6/7:ℝ))) by ring,
              ← Real.rpow_add hLpos]
            norm_num
          rw [h2]
          nlinarith [h1, Real.rpow_pos_of_pos hLpos (1/7:ℝ)]
        have hstep4 : Real.exp (L) * Real.exp (-L - cζ * L ^ (1/7:ℝ) + 2 * cζ ^ 2 * L ^ (-(5/7:ℝ)))
            = Real.exp (-cζ * L ^ (1/7:ℝ) + 2 * cζ ^ 2 * L ^ (-(5/7:ℝ))) := by
          rw [← Real.exp_add]; ring_nf
        have hstep5 : Real.exp (-cζ * L ^ (1/7:ℝ) + 2 * cζ ^ 2 * L ^ (-(5/7:ℝ)))
            ≤ Real.exp (-(cζ * L ^ (1/7:ℝ) / 2)) := by
          refine Real.exp_le_exp.mpr ?_
          linarith [hstep3]
        have hstep6 : Real.exp (-(cζ * L ^ (1/7:ℝ) / 2)) ≤ 1/2 := by
          have h1 : Real.exp (-(cζ * L ^ (1/7:ℝ) / 2)) ≤ Real.exp (- Real.log 2) :=
            Real.exp_le_exp.mpr (by linarith [hC])
          have h2 : Real.exp (- Real.log 2) = (2:ℝ)⁻¹ := by
            rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ) < 2)]
          rw [h2] at h1
          norm_num at h1 ⊢
          exact h1
        rw [div_mul_eq_mul_div]
        rw [div_le_one hσpos]
        calc ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ * (N:ℝ)^(-σ)
            ≤ Real.exp (-cζ * L ^ (1/7:ℝ) + 2 * cζ ^ 2 * L ^ (-(5/7:ℝ))) := by
              rw [hstep4] at hstep2; exact hstep2
          _ ≤ Real.exp (-(cζ * L ^ (1/7:ℝ) / 2)) := hstep5
          _ ≤ 1/2 := hstep6
          _ ≤ σ := hσhalf
      -- ===== the partial sum =====
      set J₁ : ℕ := Nat.log 2 ⌊t⌋₊ with hJ₁def
      set J₀ : ℕ := ⌈(L / c₂) ^ (6/7:ℝ) / Real.log 2⌉₊ with hJ₀def
      set J : ℕ := Nat.log 2 N + 1 with hJdef
      set blk : ℕ → ℂ := fun j => ∑ n ∈ Finset.Ioc (2^j) (Nat.min (2^(j+1)) N),
          (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) with hblkdef
      have hdecomp := sum_Ioc_dyadic_eq_range
        (fun n => (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) N J
        (le_of_lt (by rw [hJdef]; exact Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) N))
        (by rw [hJdef]; omega)
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      -- index facts
      have hJ₀log : (L / c₂) ^ (6/7:ℝ) ≤ (J₀ : ℝ) * Real.log 2 := by
        have hA : (L / c₂) ^ (6/7:ℝ) / Real.log 2 * Real.log 2
            ≤ (⌈(L / c₂) ^ (6/7:ℝ) / Real.log 2⌉₊ : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_right (Nat.le_ceil _) hlog2pos.le
        have hB : (L / c₂) ^ (6/7:ℝ) = (L / c₂) ^ (6/7:ℝ) / Real.log 2 * Real.log 2 := by
          field_simp
        rw [hB, hJ₀def]
        exact hA
      have hJ₀log' : (J₀ : ℝ) * Real.log 2 ≤ (L / c₂) ^ (6/7:ℝ) + Real.log 2 := by
        have hA := Nat.ceil_lt_add_one
          (show (0:ℝ) ≤ (L / c₂) ^ (6/7:ℝ) / Real.log 2 by positivity)
        have hB := mul_lt_mul_of_pos_right hA hlog2pos
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hlog2pos), one_mul] at hB
        rw [hJ₀def]
        linarith [hB]
      have hflpos : 1 ≤ ⌊t⌋₊ := Nat.floor_pos.mpr (by linarith)
      have hJ₁log : (J₁ : ℝ) * Real.log 2 ≤ Real.log t := by
        have h1 : 2 ^ J₁ ≤ ⌊t⌋₊ := by
          rw [hJ₁def]; exact Nat.pow_log_le_self 2 (by omega : ⌊t⌋₊ ≠ 0)
        have h2 : (2:ℝ)^J₁ ≤ (⌊t⌋₊ : ℝ) := by
          have h2' : ((2:ℕ)^J₁ : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast h1
          simpa using h2'
        have h3 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
        have h4 : Real.log ((2:ℝ)^J₁) ≤ Real.log t := Real.log_le_log (by positivity) (le_trans h2 h3)
        rw [Real.log_pow] at h4
        push_cast at h4
        exact h4
      have hJ₁log_low : Real.log ⌊t⌋₊ - Real.log 2 ≤ (J₁ : ℝ) * Real.log 2 := by
        have h1 : ⌊t⌋₊ < 2^(J₁+1) := by
          rw [hJ₁def]; exact Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _
        have h2 : (⌊t⌋₊ : ℝ) < (2:ℝ)^(J₁+1) := by
          have h2' : (⌊t⌋₊ : ℝ) < ((2:ℕ)^(J₁+1) : ℝ) := by exact_mod_cast h1
          simpa using h2'
        have h3 : Real.log ((⌊t⌋₊ : ℕ) : ℝ) < Real.log ((2:ℝ)^(J₁+1)) :=
          Real.log_lt_log (by positivity) h2
        rw [Real.log_pow] at h3
        push_cast at h3
        linarith
      have hlogfl_low : L - 2 * Real.log 2 ≤ Real.log ⌊t⌋₊ := by
        have h8 : (t : ℝ) / 2 ≤ (⌊t⌋₊ : ℝ) := by
          have h := Nat.lt_floor_add_one t
          linarith
        have h9 : Real.log ((t:ℝ)/2) ≤ Real.log ⌊t⌋₊ := Real.log_le_log (by linarith) h8
        rw [Real.log_div (by linarith : t ≠ 0) (by norm_num)] at h9
        linarith [hlogt_ge]
      have hJ₀pos : 1 ≤ J₀ := by
        by_contra hc
        push_neg at hc
        have h1 : J₀ = 0 := by omega
        rw [h1] at hJ₀log
        simp only [Nat.cast_zero, zero_mul] at hJ₀log
        linarith [hF, hlog2pos]
      have hJ₀J₁ : J₀ ≤ J₁ + 1 := by
        have h1 : (L / c₂) ^ (6/7:ℝ) ≤ L - 4 := by linarith [hH]
        have h2 : L - 4 ≤ (J₁ : ℝ) * Real.log 2 := by
          have h3 : L - 4 ≤ L - 3 * Real.log 2 := by linarith [Real.log_two_lt_d9]
          linarith [hJ₁log_low, hlogfl_low]
        have h4 : (J₀ : ℝ) * Real.log 2 ≤ ((J₁ : ℝ) + 1) * Real.log 2 := by
          rw [add_mul, one_mul]; linarith [hJ₀log', h1, h2]
        have h5 : (J₀ : ℝ) ≤ (J₁ : ℝ) + 1 := le_of_mul_le_mul_right h4 hlog2pos
        have h6 : ((J₀ : ℕ) : ℝ) ≤ (((J₁ + 1 : ℕ)) : ℝ) := by push_cast; exact h5
        exact_mod_cast h6
      have hJ₁J : J₁ + 1 ≤ J := by
        rw [hJdef]
        have h1 : 2^J₁ ≤ ⌊t⌋₊ := by
          rw [hJ₁def]; exact Nat.pow_log_le_self 2 (by omega : ⌊t⌋₊ ≠ 0)
        have h2 : ⌊t⌋₊ ≤ N := by
          have : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
          exact_mod_cast (by linarith [htN] : (⌊t⌋₊ : ℝ) ≤ (N:ℝ))
        have h3 : 2^J₁ < 2^(Nat.log 2 N + 1) :=
          lt_of_le_of_lt (le_trans h1 h2) (Nat.lt_pow_succ_log_self (by norm_num) N)
        have h4 : J₁ < Nat.log 2 N + 1 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h3
        exact Nat.add_le_add_right (Nat.lt_succ_iff.mp h4) 1
      have hJ₀J : J₀ ≤ J := le_trans hJ₀J₁ hJ₁J
      -- ** blocks **
      have hmin_le : ∀ j : ℕ, Nat.min (2^(j+1)) N ≤ 2 * 2^j := by
        intro j
        refine le_trans (min_le_left _ _) ?_
        rw [pow_succ]; omega
      have hblk_empty : ∀ j : ℕ, N ≤ 2^j → blk j = 0 := by
        intro j hj
        rw [hblkdef]
        apply Finset.sum_eq_zero
        intro n hn
        exfalso
        rw [Finset.mem_Ioc] at hn
        have h1 : Nat.min (2^(j+1)) N ≤ 2^j := le_trans (min_le_right _ _) hj
        omega
      have hmin_lt : ∀ j : ℕ, 2^j < N → 2^j < Nat.min (2^(j+1)) N := by
        intro j hj
        exact Nat.lt_min.mpr ⟨Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self j), hj⟩
      -- trivial blocks
      have hblk_triv : ∀ j ∈ Finset.range J₀, ‖blk j‖ ≤ (2:ℝ) ^ ((j:ℝ) * δp) := by
        intro j hj
        by_cases hlt : N ≤ 2^j
        · rw [hblk_empty j hlt]
          simp only [norm_zero]
          exact Real.rpow_nonneg (by norm_num) _
        · have hgt : 2^j < N := not_le.mp hlt
          rw [hblkdef]
          refine le_trans (trivial_block_bound Nat.one_le_two_pow hσpos (hmin_lt j hgt) (hmin_le j)) ?_
          have h1 : (((2^j : ℕ)) : ℝ) = (2:ℝ)^j := by push_cast; ring
          rw [h1]
          have h2 : ((2:ℝ)^j) ^ (1 - σ) ≤ ((2:ℝ)^j) ^ δp :=
            Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.one_le_two_pow) (le_max_left _ _)
          refine le_trans h2 ?_
          rw [← Real.rpow_natCast (2:ℝ) j, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
      -- V1 blocks
      have hblk_v1 : ∀ j ∈ Finset.Icc J₀ J₁, ‖blk j‖
          ≤ C₂ * (2:ℝ) ^ ((j:ℝ) * (δp - c₂ * (((j:ℝ) * Real.log 2) / L) ^ 2 /
              Real.log (L / ((j:ℝ) * Real.log 2) + 2))) := by
        intro j hj
        rw [Finset.mem_Icc] at hj
        obtain ⟨hj₀, hj₁⟩ := hj
        have hj1 : 1 ≤ j := le_trans hJ₀pos hj₀
        by_cases hlt : N ≤ 2^j
        · rw [hblk_empty j hlt]
          simp only [norm_zero]
          exact mul_nonneg hC₂.le (Real.rpow_nonneg (by norm_num) _)
        · have hgt : 2^j < N := not_le.mp hlt
          set γ : ℝ := c₂ * (Real.log ((2^j : ℕ) : ℝ) / Real.log t) ^ 2 /
              Real.log (Real.log t / Real.log ((2^j : ℕ) : ℝ) + 2) with hγdef
          have hV : ∀ h, 2^j ≤ h → h ≤ Nat.min (2^(j+1)) N →
              ‖∑ h' ∈ Finset.Ioc (2^j) h, (h' : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
                ≤ C₂ * ((2^j : ℕ) : ℝ) ^ (1 - γ) := by
            intro h hKh hhR
            rcases eq_or_lt_of_le hKh with hEq | hLt
            · subst hEq; simp
              exact mul_nonneg hC₂.le (Real.rpow_nonneg (by positivity) _)
            · have hK2 : 2 ≤ ((2^j : ℕ) : ℝ) := by
                have h1 : 2 ≤ 2^j := by
                  simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hj1
                exact_mod_cast h1
              have hKt : ((2^j : ℕ) : ℝ) ≤ t := by
                have h1 : 2^j ≤ 2^J₁ := Nat.pow_le_pow_right (by norm_num) hj₁
                have h2 : 2^J₁ ≤ ⌊t⌋₊ := Nat.pow_log_le_self 2 (by omega : ⌊t⌋₊ ≠ 0)
                have h3 : ((2^j : ℕ) : ℝ) ≤ (⌊t⌋₊ : ℝ) := by exact_mod_cast (le_trans h1 h2)
                have h4 : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
                linarith
              have hlogK : (L / c₂) ^ (6/7:ℝ) ≤ Real.log ((2^j : ℕ) : ℝ) := by
                have h2 : (J₀ : ℝ) * Real.log 2 ≤ (j : ℝ) * Real.log 2 :=
                  mul_le_mul_of_nonneg_right (by exact_mod_cast hj₀) hlog2pos.le
                have h3 : ((j:ℝ) * Real.log 2) = Real.log ((2^j : ℕ) : ℝ) := by
                  rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
                linarith [hJ₀log, h2, h3.le, h3.ge]
              have hlogpos : 0 < Real.log ((2^j : ℕ) : ℝ) := by
                apply Real.log_pos
                have h1 : (1:ℝ) < (2:ℝ)^j := one_lt_pow₀ (by norm_num) (by omega : j ≠ 0)
                have h2 : (2:ℝ)^j = ((2^j : ℕ) : ℝ) := by push_cast; ring
                linarith [h1, h2.le, h2.ge]
              have hrange : Real.log t ≤ c₂ * (Real.log ((2^j : ℕ) : ℝ)) ^ (7/6:ℝ) := by
                have h2 : ((L / c₂) ^ (6/7:ℝ)) ^ (7/6:ℝ) = L / c₂ := by
                  rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ L / c₂)]; norm_num
                have h4 : L / c₂ ≤ (Real.log ((2^j : ℕ) : ℝ)) ^ (7/6:ℝ) := by
                  have h5 : ((L / c₂) ^ (6/7:ℝ)) ^ (7/6:ℝ)
                      ≤ (Real.log ((2^j : ℕ) : ℝ)) ^ (7/6:ℝ) :=
                    Real.rpow_le_rpow (by positivity) hlogK (by norm_num)
                  rwa [h2] at h5
                have h6 : L ≤ c₂ * (Real.log ((2^j : ℕ) : ℝ)) ^ (7/6:ℝ) := by
                  have h7 : c₂ * (L / c₂) = L := by field_simp
                  calc L = c₂ * (L / c₂) := h7.symm
                    _ ≤ c₂ * (Real.log ((2^j : ℕ) : ℝ)) ^ (7/6:ℝ) :=
                        mul_le_mul_of_nonneg_left h4 hc₂.le
                linarith [hlogt_le]
              have hhN : (h:ℝ) ≤ 2 * ((2^j:ℕ):ℝ) := by
                have h2 : (h:ℝ) ≤ ((2:ℕ)^(j+1) : ℝ) := by
                  have h3 : h ≤ 2^(j+1) := le_trans hhR (min_le_left _ _)
                  exact_mod_cast h3
                have h4 : ((2:ℕ)^(j+1) : ℝ) = 2 * ((2^j:ℕ):ℝ) := by push_cast; ring
                linarith [h2, h4.le, h4.ge]
              have hh := hVK0 ((2^j : ℕ) : ℝ) t hK2 hKt hrange ((h:ℕ):ℝ)
                (by exact_mod_cast hLt) hhN
              rw [Nat.floor_natCast, Nat.floor_natCast] at hh
              rw [hγdef]
              exact hh
          have hb := dsum_block_bound Nat.one_le_two_pow (hmin_lt j hgt) (mul_nonneg hC₂.le
            (Real.rpow_nonneg (by positivity) _)) hσpos hV
          rw [hblkdef]
          refine le_trans hb ?_
          -- C₂ * (2^j)^{1-γ} * (2^j)^{-σ} ≤ C₂ * 2^{j(δp-γ')}
          rw [mul_assoc]
          refine mul_le_mul_of_nonneg_left ?_ hC₂.le
          have hbase : (0:ℝ) < ((2^j : ℕ) : ℝ) := by positivity
          have hbase1 : (1:ℝ) ≤ ((2^j : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
          have hγ : c₂ * (((j:ℝ) * Real.log 2) / L) ^ 2 / Real.log (L / ((j:ℝ) * Real.log 2) + 2) ≤ γ := by
            rw [hγdef]
            have hlogeq : Real.log ((2^j : ℕ) : ℝ) = (j:ℝ) * Real.log 2 := by
              rw [Nat.cast_pow, Real.log_pow]; push_cast; ring
            rw [hlogeq]
            have hxpos : 0 < (j:ℝ) * Real.log 2 := by
              have hj0 : (0:ℝ) < j := by exact_mod_cast hj1
              positivity
            have hltpos : 0 < Real.log t := Real.log_pos (by linarith)
            have h1 : (j:ℝ) * Real.log 2 / L ≤ (j:ℝ) * Real.log 2 / Real.log t :=
              div_le_div_aux hxpos.le hLpos hltpos hlogt_le
            have h2 : Real.log t / ((j:ℝ) * Real.log 2) + 2
                ≤ L / ((j:ℝ) * Real.log 2) + 2 := by
              have h2' : Real.log t / ((j:ℝ) * Real.log 2)
                  ≤ L / ((j:ℝ) * Real.log 2) := div_le_div_of_nonneg_right hlogt_le hxpos.le
              linarith
            have h3 : 0 < L / ((j:ℝ) * Real.log 2) + 2 := by positivity
            have h4 : 0 < Real.log t / ((j:ℝ) * Real.log 2) + 2 := by positivity
            have h5 : Real.log (Real.log t / ((j:ℝ) * Real.log 2) + 2)
                ≤ Real.log (L / ((j:ℝ) * Real.log 2) + 2) := Real.log_le_log h4 h2
            have h7 : (((j:ℝ) * Real.log 2) / L) ^ 2
                ≤ (((j:ℝ) * Real.log 2) / Real.log t) ^ 2 :=
              pow_le_pow_left₀ (by positivity) h1 2
            have hA : c₂ * (((j:ℝ) * Real.log 2) / L) ^ 2
                ≤ c₂ * (((j:ℝ) * Real.log 2) / Real.log t) ^ 2 :=
              mul_le_mul_of_nonneg_left h7 hc₂.le
            have hv : 0 < Real.log (Real.log t / ((j:ℝ) * Real.log 2) + 2) :=
              Real.log_pos (by
                have hpos : (0:ℝ) ≤ Real.log t / ((j:ℝ) * Real.log 2) :=
                  div_nonneg hltpos.le hxpos.le
                linarith [hpos])
            have hu : 0 < Real.log (L / ((j:ℝ) * Real.log 2) + 2) :=
              Real.log_pos (by
                have hpos : (0:ℝ) ≤ L / ((j:ℝ) * Real.log 2) := div_nonneg hLpos.le hxpos.le
                linarith [hpos])
            have huv : 1 / Real.log (L / ((j:ℝ) * Real.log 2) + 2)
                ≤ 1 / Real.log (Real.log t / ((j:ℝ) * Real.log 2) + 2) :=
              div_le_div_aux (by norm_num) hu hv h5
            calc c₂ * (((j:ℝ) * Real.log 2) / L) ^ 2 / Real.log (L / ((j:ℝ) * Real.log 2) + 2)
                = (c₂ * (((j:ℝ) * Real.log 2) / L) ^ 2)
                  * (1 / Real.log (L / ((j:ℝ) * Real.log 2) + 2)) := by ring
              _ ≤ (c₂ * (((j:ℝ) * Real.log 2) / Real.log t) ^ 2)
                  * (1 / Real.log (Real.log t / ((j:ℝ) * Real.log 2) + 2)) :=
                  mul_le_mul hA huv (by positivity) (by positivity)
              _ = c₂ * (((j:ℝ) * Real.log 2) / Real.log t) ^ 2
                  / Real.log (Real.log t / ((j:ℝ) * Real.log 2) + 2) := by ring
          have hK' : ((2^j : ℕ) : ℝ) = (2:ℝ)^j := by push_cast; ring
          have heq : ((2^j : ℕ) : ℝ) ^ (1 - γ) * ((2^j : ℕ) : ℝ) ^ (-σ)
              = (2:ℝ) ^ ((j:ℝ) * (1 - γ - σ)) := by
            rw [hK', ← Real.rpow_natCast (2:ℝ) j,
              ← Real.rpow_add (by positivity : (0:ℝ) < (2:ℝ)^(j:ℝ)),
              ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
            ring_nf
          rw [heq]
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) ?_
          have hj0 : (0:ℝ) ≤ j := by positivity
          have h1 : 1 - σ ≤ δp := le_max_left _ _
          nlinarith [hγ, hj0, h1]
      have hb2 : ∀ x : ℝ, t ≤ x → x ≤ 4 * (t + 3) * E →
          x ^ (-σ) * (Real.sqrt (t/(8*Real.pi)) + x * Real.sqrt (8*Real.pi/t))
            ≤ 1 + Real.sqrt (8 * Real.pi) := by
        intro x hxt hxN
        have htpos' : 0 < t := htpos
        have hxpos : 0 < x := lt_of_lt_of_le htpos hxt
        rw [Real.sqrt_div (le_of_lt htpos') (8*Real.pi), Real.sqrt_div' (8*Real.pi) (le_of_lt htpos')]
        have h1 : x ^ (-σ) * (Real.sqrt t / Real.sqrt (8*Real.pi)) ≤ 1 := by
          have h2 : x ^ (-σ) ≤ t ^ (-σ) := Real.rpow_le_rpow_of_nonpos htpos' hxt (by linarith)
          have h3 : t ^ (-σ) * Real.sqrt t ≤ 1 := by
            rw [Real.sqrt_eq_rpow, ← Real.rpow_add htpos']
            have h4 : (-σ) + 1/2 ≤ 0 := by linarith
            calc t ^ ((-σ) + 1/2) ≤ t ^ (0:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) h4
              _ = 1 := Real.rpow_zero t
          have h5 : (1:ℝ) ≤ Real.sqrt (8*Real.pi) := by
            rw [Real.le_sqrt (by positivity) (by positivity)]
            nlinarith [Real.pi_gt_three]
          calc x ^ (-σ) * (Real.sqrt t / Real.sqrt (8*Real.pi))
              = (x ^ (-σ) * Real.sqrt t) / Real.sqrt (8*Real.pi) := by ring
            _ ≤ (t ^ (-σ) * Real.sqrt t) / Real.sqrt (8*Real.pi) :=
                div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg t)) (by positivity)
            _ ≤ 1 := by
                rw [div_le_one (by positivity : (0:ℝ) < Real.sqrt (8 * Real.pi))]
                exact le_trans h3 h5
        have h2main : x ^ (-σ) * (x * Real.sqrt (8*Real.pi) / Real.sqrt t) ≤ Real.sqrt (8*Real.pi) := by
          have hx1 : x ^ (-σ) * x = x ^ (1 - σ) := by
            have h5 : x ^ (-σ) * x ^ (1:ℝ) = x ^ (1 - σ) := by
              rw [← Real.rpow_add hxpos]; ring_nf
            rwa [Real.rpow_one] at h5
          have hexp_le_sqrt : Real.exp (L / 2 - 4) ≤ Real.sqrt t := by
            have h1 : Real.log (Real.sqrt t) = Real.log t / 2 := Real.log_sqrt htpos'.le
            have h3 : Real.log (Real.sqrt 2) = Real.log 2 / 2 := Real.log_sqrt (by norm_num : (0:ℝ) ≤ 2)
            have h4 : L / 2 - 4 ≤ Real.log (Real.sqrt t) := by
              rw [h1]; linarith [hlogt_ge, Real.log_le_self (by norm_num : (0:ℝ) ≤ 2)]
            have h5 : Real.exp (L / 2 - 4) ≤ Real.exp (Real.log (Real.sqrt t)) :=
              Real.exp_le_exp.mpr h4
            rwa [Real.exp_log (Real.sqrt_pos.mpr htpos')] at h5
          have h3 : x ^ (1 - σ) / Real.sqrt t ≤ 1 := by
            rw [div_le_one (Real.sqrt_pos.mpr htpos')]
            have hsqrt_ge_one : (1:ℝ) ≤ Real.sqrt t := by
              rw [Real.le_sqrt (by norm_num) (by linarith)]
              linarith [ht3]
            by_cases hσ1 : σ ≤ 1
            · have h4TE : (1:ℝ) ≤ 4 * (t + 3) * E := by nlinarith [hTpos, hE1]
              have h4TEpos : (0:ℝ) < 4 * (t + 3) * E := by linarith
              have hexp : (4 * (t + 3) * E) ^ δp
                  = Real.exp (Real.log (4 * (t + 3) * E) * δp) :=
                Real.rpow_def_of_pos h4TEpos δp
              have hlog4TE : Real.log (4 * (t + 3) * E) = L + Real.log 4 + 2 * cζ * L ^ (1/7:ℝ) := by
                have h1 : Real.log (4 * (t + 3) * E) = Real.log 4 + Real.log ((t + 3) * E) := by
                  rw [mul_assoc, Real.log_mul (by norm_num) (by positivity)]
                have h2 : Real.log ((t + 3) * E) = L + 2 * cζ * L ^ (1/7:ℝ) := by
                  rw [Real.log_mul (by linarith) (ne_of_gt hEpos), hEdef, Real.log_exp, hLdef]
                rw [h1, h2]; ring
              have hswap : (L + Real.log 4 + 2 * cζ * L ^ (1/7:ℝ)) * δp
                  = δp * (L + Real.log 4 + 2 * cζ * L ^ (1/7:ℝ)) := by ring
              have hδlog : Real.log (4 * (t + 3) * E) * δp ≤ L / 2 - 4 := by
                rw [hlog4TE, hswap]
                have h6 : δp * (L + Real.log 4 + 2 * cζ * L ^ (1/7:ℝ))
                    ≤ cζ * L ^ (-(6/7:ℝ)) * (L + Real.log 4 + 2 * cζ * L ^ (1/7:ℝ)) :=
                  mul_le_mul_of_nonneg_right hδple (by
                    have h7 := Real.log_pos (by norm_num : (1:ℝ) < 4)
                    positivity)
                have h7 : cζ * L ^ (-(6/7:ℝ)) * (L + Real.log 4 + 2 * cζ * L ^ (1/7:ℝ))
                    ≤ cζ * L ^ (1/7:ℝ) + 4 * cζ * L ^ (-(6/7:ℝ)) + 4 * cζ ^ 2 * L ^ (-(5/7:ℝ)) := by
                  have e1 : cζ * L ^ (-(6/7:ℝ)) * L = cζ * L ^ (1/7:ℝ) := by
                    have h9 : L ^ (-(6/7:ℝ)) * L ^ (1:ℝ) = L ^ (1/7:ℝ) := by
                      rw [← Real.rpow_add hLpos]; norm_num
                    rw [Real.rpow_one] at h9
                    rw [mul_assoc, h9]
                  have e2 : cζ * L ^ (-(6/7:ℝ)) * Real.log 4 ≤ 4 * cζ * L ^ (-(6/7:ℝ)) := by
                    have h9 : Real.log 4 ≤ 4 := Real.log_le_self (by norm_num)
                    have h10 : cζ * L ^ (-(6/7:ℝ)) * Real.log 4 ≤ cζ * L ^ (-(6/7:ℝ)) * 4 :=
                      mul_le_mul_of_nonneg_left h9 (mul_nonneg hcζpos.le (Real.rpow_nonneg hLpos.le _))
                    linarith [h10]
                  have e3 : cζ * L ^ (-(6/7:ℝ)) * (2 * cζ * L ^ (1/7:ℝ)) ≤ 4 * cζ ^ 2 * L ^ (-(5/7:ℝ)) := by
                    have h9 : cζ * L ^ (-(6/7:ℝ)) * (2 * cζ * L ^ (1/7:ℝ))
                        = 2 * cζ ^ 2 * (L ^ (-(6/7:ℝ)) * L ^ (1/7:ℝ)) := by ring
                    rw [h9, ← Real.rpow_add hLpos]
                    norm_num
                    nlinarith [hcζpos, Real.rpow_pos_of_pos hLpos (-(5/7:ℝ)), Real.rpow_pos_of_pos hLpos (-(6/7:ℝ))]
                  have e4 : cζ * L ^ (-(6/7:ℝ)) * (L + Real.log 4 + 2 * cζ * L ^ (1/7:ℝ))
                      = cζ * L ^ (-(6/7:ℝ)) * L + cζ * L ^ (-(6/7:ℝ)) * Real.log 4
                        + cζ * L ^ (-(6/7:ℝ)) * (2 * cζ * L ^ (1/7:ℝ)) := by ring
                  rw [e4]; linarith [e1, e2, e3]
                linarith [h6, h7, hD]
              by_cases hx1' : (1:ℝ) ≤ x
              · have h1 : x ^ (1 - σ) ≤ x ^ δp :=
                  Real.rpow_le_rpow_of_exponent_le hx1' (le_max_left _ _)
                have h2 : x ^ δp ≤ (4 * (t + 3) * E) ^ δp :=
                  Real.rpow_le_rpow (le_trans zero_le_one hx1') hxN hδp0
                have h3a : (4 * (t + 3) * E) ^ δp ≤ Real.exp (L / 2 - 4) := by
                  rw [hexp]; exact Real.exp_le_exp.mpr hδlog
                linarith [h1, h2, h3a, hexp_le_sqrt]
              · have h1 : x ^ (1 - σ) ≤ 1 :=
                  Real.rpow_le_one hxpos.le (le_of_lt (not_le.mp hx1')) (by linarith)
                linarith [h1, hsqrt_ge_one]
            · have hσgt : 1 < σ := lt_of_not_ge hσ1
              have hxlog : Real.log 2 ≤ x :=
                le_trans (le_trans (by linarith [Real.log_two_lt_d9] : Real.log 2 ≤ 3) ht3) hxt
              have h1 : x ^ (1 - σ) ≤ (Real.log 2) ^ (1 - σ) :=
                Real.rpow_le_rpow_of_nonpos (Real.log_pos (by norm_num)) hxlog (by linarith)
              have h2 : (Real.log 2) ^ (1 - σ) ≤ (Real.log 2) ^ (-1:ℝ) :=
                Real.rpow_le_rpow_of_exponent_ge (Real.log_pos (by norm_num))
                  (by linarith [Real.log_two_lt_d9]) (by linarith [hσhi])
              have h4 : (Real.log 2) ^ (-1:ℝ) ≤ Real.sqrt t := by
                rw [Real.rpow_neg_one, inv_eq_one_div]
                rw [div_le_iff₀ (Real.log_pos (by norm_num))]
                have h17 : (1.7:ℝ) ≤ Real.sqrt t := by
                  rw [Real.le_sqrt (by norm_num) (by linarith)]
                  linarith [ht3]
                nlinarith [h17, Real.log_two_gt_d9]
              linarith [h1, h2, h4]
          calc x ^ (-σ) * (x * Real.sqrt (8*Real.pi) / Real.sqrt t)
              = (x ^ (-σ) * x) * Real.sqrt (8*Real.pi) / Real.sqrt t := by ring
            _ = x ^ (1 - σ) * Real.sqrt (8*Real.pi) / Real.sqrt t := by rw [hx1]
            _ = (x ^ (1 - σ) / Real.sqrt t) * Real.sqrt (8*Real.pi) := by ring
            _ ≤ 1 * Real.sqrt (8*Real.pi) := mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
            _ = Real.sqrt (8*Real.pi) := one_mul _
        calc x ^ (-σ) * (Real.sqrt t / Real.sqrt (8*Real.pi) + x * (Real.sqrt (8*Real.pi) / Real.sqrt t))
            = x ^ (-σ) * (Real.sqrt t / Real.sqrt (8*Real.pi))
              + x ^ (-σ) * (x * Real.sqrt (8*Real.pi) / Real.sqrt t) := by ring
          _ ≤ 1 + Real.sqrt (8 * Real.pi) := add_le_add h1 h2main
      -- SDT blocks
      have hblk_sdt : ∀ j ∈ Finset.Icc (J₁ + 1) (J - 1), ‖blk j‖
          ≤ C₃ * (1 + Real.sqrt (8 * Real.pi)) := by
        intro j hj
        rw [Finset.mem_Icc] at hj
        obtain ⟨hj₁, hjJ⟩ := hj
        by_cases hlt : N ≤ 2^j
        · rw [hblk_empty j hlt]
          simp only [norm_zero]
          exact mul_nonneg hC₃.le (by positivity)
        · have hgt : 2^j < N := not_le.mp hlt
          have hKt : t < ((2^j : ℕ) : ℝ) := by
            have h1 : ⌊t⌋₊ < 2^(J₁+1) := by
              rw [hJ₁def]; exact Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) _
            have h2 : (⌊t⌋₊ : ℝ) < ((2:ℕ)^(J₁+1) : ℝ) := by exact_mod_cast h1
            have h3 : ((2:ℕ)^(J₁+1) : ℝ) ≤ ((2^j : ℕ) : ℝ) := by
              exact_mod_cast (Nat.pow_le_pow_right (by norm_num) hj₁)
            have h5 : t < ((2:ℕ)^(J₁+1) : ℝ) := by
              have h6 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
              have h7 : (⌊t⌋₊ : ℝ) + 1 ≤ ((2:ℕ)^(J₁+1) : ℝ) := by
                have h8 : ⌊t⌋₊ + 1 ≤ 2^(J₁+1) := h1
                exact_mod_cast h8
              linarith [h6, h7]
            exact lt_of_lt_of_le h5 h3
          have hV : ∀ h, 2^j ≤ h → h ≤ Nat.min (2^(j+1)) N →
              ‖∑ h' ∈ Finset.Ioc (2^j) h, (h' : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
                ≤ C₃ * (Real.sqrt (t / (8 * Real.pi))
                    + ((2^j:ℕ):ℝ) * Real.sqrt (8 * Real.pi / t)) := by
            intro h hKh hhR
            rcases eq_or_lt_of_le hKh with hEq | hLt
            · subst hEq; simp
              exact mul_nonneg hC₃.le (by positivity)
            · have hhN : h ≤ 2 * 2^j := by
                have h2 : h ≤ 2^(j+1) := le_trans hhR (min_le_left _ _)
                rw [pow_succ] at h2; omega
              exact hSDT (2^j) h t Nat.one_le_two_pow (by omega) hhN htpos
          have hb := dsum_block_bound Nat.one_le_two_pow (hmin_lt j hgt) (mul_nonneg hC₃.le (by positivity))
            hσpos hV
          rw [hblkdef]
          refine le_trans hb ?_
          have hxE : ((2^j:ℕ):ℝ) ≤ 4 * (t + 3) * E := by
            have h1 : j ≤ Nat.log 2 N := by
              have hJm : J - 1 = Nat.log 2 N := by omega
              omega
            have h2 : (2:ℝ)^j ≤ (N:ℝ) := by
              have h2' : 2^j ≤ N := le_trans (Nat.pow_le_pow_right (by norm_num) h1)
                (Nat.pow_log_le_self 2 (by omega : N ≠ 0))
              exact_mod_cast h2'
            have h3 : ((2^j:ℕ):ℝ) = (2:ℝ)^j := by push_cast; ring
            rw [h3]
            have h4 : (N:ℝ) ≤ 2 * ((t + 3) * E) := hNup
            nlinarith [h2, h4, hE1, hTpos]
          have hstep := hb2 ((2^j:ℕ):ℝ) (by linarith [hKt]) hxE
          calc C₃ * (Real.sqrt (t / (8 * Real.pi)) + ((2^j:ℕ):ℝ) * Real.sqrt (8 * Real.pi / t))
                * ((2^j:ℕ):ℝ) ^ (-σ)
              = C₃ * ((((2^j:ℕ):ℝ) ^ (-σ))
                  * (Real.sqrt (t / (8 * Real.pi)) + ((2^j:ℕ):ℝ) * Real.sqrt (8 * Real.pi / t))) := by ring
            _ ≤ C₃ * (1 + Real.sqrt (8 * Real.pi)) := mul_le_mul_of_nonneg_left hstep hC₃.le
      -- ** summation bounds **
      have htriv_sum : ‖∑ j ∈ Finset.range J₀, blk j‖
          ≤ (2 * Real.exp (cζ / c₂ ^ (6/7:ℝ) + 1) / (Real.log 2 * c₂ ^ (6/7:ℝ))) * L ^ (6/7:ℝ) := by
        refine le_trans (norm_sum_le _ _) ?_
        have h1 : ∑ j ∈ Finset.range J₀, (2:ℝ) ^ ((j:ℝ) * δp)
            ≤ (J₀ : ℝ) * (2:ℝ) ^ ((J₀:ℝ) * δp) := by
          calc ∑ j ∈ Finset.range J₀, (2:ℝ) ^ ((j:ℝ) * δp)
              ≤ ∑ _j ∈ Finset.range J₀, (2:ℝ) ^ ((J₀:ℝ) * δp) := by
                refine Finset.sum_le_sum (fun j hj => ?_)
                refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
                have h2 : (j:ℝ) ≤ J₀ := by exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hj))
                nlinarith [hδp0]
            _ = (J₀ : ℝ) * (2:ℝ) ^ ((J₀:ℝ) * δp) := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        refine le_trans (le_trans (Finset.sum_le_sum hblk_triv) h1) ?_
        have h2 : (2:ℝ) ^ ((J₀:ℝ) * δp) = Real.exp (Real.log 2 * ((J₀:ℝ) * δp)) :=
          Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2) _
        rw [h2]
        have h3 : Real.log 2 * ((J₀:ℝ) * δp) ≤ cζ / c₂ ^ (6/7:ℝ) + 1 := by
          have h4 : δp * ((J₀:ℝ) * Real.log 2) ≤ δp * ((L / c₂) ^ (6/7:ℝ) + Real.log 2) :=
            mul_le_mul_of_nonneg_left hJ₀log' hδp0
          have h5 : δp * ((L / c₂) ^ (6/7:ℝ)) ≤ cζ / c₂ ^ (6/7:ℝ) := by
            have h6 : δp * ((L / c₂) ^ (6/7:ℝ)) ≤ (cζ * L ^ (-(6/7:ℝ))) * ((L / c₂) ^ (6/7:ℝ)) :=
              mul_le_mul_of_nonneg_right hδple (by positivity)
            have h7 : cζ * L ^ (-(6/7:ℝ)) * (L / c₂) ^ (6/7:ℝ) = cζ / c₂ ^ (6/7:ℝ) := by
              rw [Real.div_rpow (le_of_lt hLpos) (le_of_lt hc₂) (6/7:ℝ)]
              have hLp : L ^ (-(6/7:ℝ)) * L ^ (6/7:ℝ) = 1 := by
                rw [← Real.rpow_add hLpos]; norm_num
              have hc2p : (0:ℝ) < c₂ ^ (6/7:ℝ) := Real.rpow_pos_of_pos hc₂ _
              calc cζ * L ^ (-(6/7:ℝ)) * (L ^ (6/7:ℝ) / c₂ ^ (6/7:ℝ))
                  = cζ * (L ^ (-(6/7:ℝ)) * L ^ (6/7:ℝ)) / c₂ ^ (6/7:ℝ) := by ring
                _ = cζ * 1 / c₂ ^ (6/7:ℝ) := by rw [hLp]
                _ = cζ / c₂ ^ (6/7:ℝ) := by ring
            rw [h7] at h6; exact h6
          have h8 : δp * Real.log 2 ≤ 1 := by
            have hlog2nn : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
            have hmid : δp * Real.log 2 ≤ (cζ * L ^ (-(6/7:ℝ))) * Real.log 2 :=
              mul_le_mul_of_nonneg_right hδple hlog2nn
            have hcm : (cζ * L ^ (-(6/7:ℝ))) * Real.log 2 = cζ * Real.log 2 * L ^ (-(6/7:ℝ)) := by ring
            rw [hcm] at hmid
            linarith [hmid, hI]
          linarith [h4, h5, h8]
        calc (J₀ : ℝ) * Real.exp (Real.log 2 * ((J₀:ℝ) * δp))
            ≤ (2 * ((L / c₂) ^ (6/7:ℝ) / Real.log 2)) * Real.exp (cζ / c₂ ^ (6/7:ℝ) + 1) := by
              refine mul_le_mul ?_ (Real.exp_le_exp.mpr h3) (Real.exp_pos _).le (by positivity)
              have hA := Nat.ceil_lt_add_one
                (show (0:ℝ) ≤ (L / c₂) ^ (6/7:ℝ) / Real.log 2 by positivity)
              have hF' : 1 ≤ (L / c₂) ^ (6/7:ℝ) / Real.log 2 := by
                rw [le_div_iff₀ hlog2pos, one_mul]
                exact hF
              rw [hJ₀def]
              linarith
          _ = (2 * Real.exp (cζ / c₂ ^ (6/7:ℝ) + 1) / (Real.log 2 * c₂ ^ (6/7:ℝ))) * L ^ (6/7:ℝ) := by
              have hL6 : (L / c₂) ^ (6/7:ℝ) = L ^ (6/7:ℝ) / c₂ ^ (6/7:ℝ) :=
                Real.div_rpow (le_of_lt hLpos) (le_of_lt hc₂) (6/7:ℝ)
              rw [hL6]
              field_simp
      have hv1_sum : ‖∑ j ∈ Finset.Icc J₀ J₁, blk j‖ ≤ C₂ * Ablk * L ^ (6/7:ℝ) := by
        refine le_trans (norm_sum_le _ _) ?_
        have h1 : ∑ j ∈ Finset.Icc J₀ J₁, ‖blk j‖ ≤ C₂ * (∑ j ∈ Finset.Icc J₀ J₁,
            (2:ℝ) ^ ((j:ℝ) * (δp - c₂ * (((j:ℝ) * Real.log 2) / L) ^ 2 /
                Real.log (L / ((j:ℝ) * Real.log 2) + 2)))) := by
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum hblk_v1
        refine le_trans h1 ?_
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ hC₂.le
        have hsub : Finset.Icc J₀ J₁ ⊆ Finset.Icc J₀ (max (J₁ + 1) (J₀ + 1) - 1) := by
          intro x hx
          rw [Finset.mem_Icc] at hx ⊢
          omega
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun x _ _ => Real.rpow_nonneg (by norm_num) _)) ?_
        exact hAblk L δp J₀ (max (J₁ + 1) (J₀ + 1)) hA hδp0 hδple hJ₀log
          (le_trans (Real.one_le_rpow (by rw [le_div_iff₀ hc₂, one_mul]; exact hG) (by norm_num)) hJ₀log)
            (le_trans (Nat.le_succ J₀) (le_max_right _ _)) (by
            rw [Nat.cast_max, max_mul_of_nonneg _ _ hlog2pos.le]
            refine max_le ?_ ?_
            · rw [Nat.cast_add, Nat.cast_one]; linarith [hJ₁log, Real.log_two_lt_d9]
            · rw [Nat.cast_add, Nat.cast_one]; linarith [hJ₀log', hH, Real.log_two_lt_d9])
      have hsdt_sum : ‖∑ j ∈ Finset.Icc (J₁ + 1) (J - 1), blk j‖
          ≤ C₃ * (1 + Real.sqrt (8 * Real.pi)) * L ^ (6/7:ℝ) := by
        refine le_trans (norm_sum_le _ _) ?_
        have h1 : ∑ j ∈ Finset.Icc (J₁+1) (J-1), ‖blk j‖
            ≤ ∑ _j ∈ Finset.Icc (J₁+1) (J-1), C₃ * (1 + Real.sqrt (8 * Real.pi)) :=
          Finset.sum_le_sum hblk_sdt
        have h2 : ∑ _j ∈ Finset.Icc (J₁+1) (J-1), C₃ * (1 + Real.sqrt (8 * Real.pi))
            = (((Finset.Icc (J₁+1) (J-1)).card : ℝ)) * (C₃ * (1 + Real.sqrt (8 * Real.pi))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        rw [h2] at h1
        have h3 : (((Finset.Icc (J₁+1) (J-1)).card : ℝ)) ≤ 2 * cζ * L ^ (1/7:ℝ) / Real.log 2 + 5 := by
          have h4 : (Finset.Icc (J₁+1) (J-1)).card ≤ J - J₁ := by
            have h0 : (Finset.Icc (J₁+1) (J-1)).card = (J-1) + 1 - (J₁+1) := by simp
            omega
          have h5 : ((Finset.Icc (J₁+1) (J-1)).card : ℝ) ≤ (J:ℝ) - (J₁:ℝ) := by
            have h6 : ((Finset.Icc (J₁+1) (J-1)).card : ℝ) ≤ ((J - J₁ : ℕ) : ℝ) := by
              exact_mod_cast h4
            have h7 : ((J - J₁ : ℕ) : ℝ) ≤ (J:ℝ) - (J₁:ℝ) := by
              have h8 : J₁ ≤ J := by omega
              rw [Nat.cast_sub h8]
            linarith
          have h8 : (J:ℝ) ≤ Real.log N / Real.log 2 + 1 := by
            have h9 : (2:ℝ)^(J-1) ≤ N := by
              have h9' : 2^(J-1) ≤ N := by
                have hJm : J - 1 = Nat.log 2 N := by omega
                rw [hJm]
                exact Nat.pow_log_le_self 2 (by omega : N ≠ 0)
              exact_mod_cast h9'
            have h11 : ((J:ℝ) - 1) * Real.log 2 ≤ Real.log N := by
              have h11' : Real.log ((2:ℝ)^(J-1)) ≤ Real.log N := Real.log_le_log (by positivity) h9
              rw [Real.log_pow] at h11'
              push_cast [Nat.cast_sub (by omega : 1 ≤ J)] at h11'
              exact h11'
            have h12 : (J:ℝ) - 1 ≤ Real.log N / Real.log 2 := by
              rw [le_div_iff₀ hlog2pos]; linarith
            linarith
          have h10 : Real.log ⌊t⌋₊ / Real.log 2 - 1 ≤ (J₁:ℝ) := by
            have h11 : Real.log ⌊t⌋₊ / Real.log 2 ≤ (J₁:ℝ) + 1 := by
              rw [div_le_iff₀ hlog2pos]
              linarith [hJ₁log_low]
            linarith
          have h12 : Real.log N - Real.log ⌊t⌋₊ ≤ 3 * Real.log 2 + 2 * cζ * L ^ (1/7:ℝ) := by
            linarith [hlogN_le, hlogfl_low]
          have h13 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
          have h14 : (Real.log N - Real.log ⌊t⌋₊) / Real.log 2
              ≤ (3 * Real.log 2 + 2 * cζ * L ^ (1/7:ℝ)) / Real.log 2 :=
            div_le_div_of_nonneg_right h12 hlog2pos.le
          have h15 : (3 * Real.log 2 + 2 * cζ * L ^ (1/7:ℝ)) / Real.log 2
              = 3 + 2 * cζ * L ^ (1/7:ℝ) / Real.log 2 := by
            field_simp
          rw [div_add' _ _ _ (ne_of_gt hlog2pos)] at h8
          rw [h15] at h14
          have h16 : (Real.log N - Real.log ⌊t⌋₊) / Real.log 2
              = Real.log N / Real.log 2 - Real.log ⌊t⌋₊ / Real.log 2 := sub_div _ _ _
          have h17 : (J:ℝ) - (J₁:ℝ) ≤ (Real.log N - Real.log ⌊t⌋₊) / Real.log 2 + 2 := by
            have e : Real.log N / Real.log 2 - Real.log ⌊t⌋₊ / Real.log 2
                = (Real.log N - Real.log ⌊t⌋₊) / Real.log 2 := h16.symm
            have h18 : (J:ℝ) - (J₁:ℝ) ≤ Real.log N / Real.log 2 - Real.log ⌊t⌋₊ / Real.log 2 + 2 := by
              have hs := sub_le_sub h8 h10
              have he : (Real.log N + 1 * Real.log 2) / Real.log 2
                  - (Real.log ⌊t⌋₊ / Real.log 2 - 1)
                  = Real.log N / Real.log 2 - Real.log ⌊t⌋₊ / Real.log 2 + 2 := by
                field_simp
                ring
              linarith [hs, he]
            linarith [h18, e]
          linarith [h5, h17, h14]
        refine le_trans h1 ?_
        have hCsdt0 : 0 ≤ C₃ * (1 + Real.sqrt (8 * Real.pi)) :=
          mul_nonneg hC₃.le (by positivity)
        refine le_trans (mul_le_mul_of_nonneg_right h3 hCsdt0) ?_
        calc (2 * cζ * L ^ (1/7:ℝ) / Real.log 2 + 5) * (C₃ * (1 + Real.sqrt (8 * Real.pi)))
            ≤ L ^ (6/7:ℝ) * (C₃ * (1 + Real.sqrt (8 * Real.pi))) :=
              mul_le_mul_of_nonneg_right hE hCsdt0
          _ = C₃ * (1 + Real.sqrt (8 * Real.pi)) * L ^ (6/7:ℝ) := by ring
      have hpart : ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
          ≤ Apart * L ^ (6/7:ℝ) := by
        have hIcc : ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
            = 1 + ∑ j ∈ Finset.range J, blk j := by
          have hins : Finset.Icc 1 N = insert 1 (Finset.Ioc 1 N) := by
            ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]; omega
          have h1c : (((1:ℕ) : ℂ)) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) = 1 := by
            push_cast
            exact Complex.one_cpow _
          rw [hins, Finset.sum_insert (by simp), h1c]
          rw [hdecomp]
        rw [hIcc]
        have hpart1 : Finset.range J = Finset.range J₀ ∪ Finset.Icc J₀ (J - 1) := by
          ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Icc]; omega
        have hdisj1 : Disjoint (Finset.range J₀) (Finset.Icc J₀ (J-1)) := by
          rw [Finset.disjoint_left]; intro x hx hx'
          simp only [Finset.mem_range] at hx; simp only [Finset.mem_Icc] at hx'; omega
        have hpart2 : Finset.Icc J₀ (J-1) = Finset.Icc J₀ J₁ ∪ Finset.Icc (J₁+1) (J-1) := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
        have hdisj2 : Disjoint (Finset.Icc J₀ J₁) (Finset.Icc (J₁+1) (J-1)) := by
          rw [Finset.disjoint_left]; intro x hx hx'
          simp only [Finset.mem_Icc] at hx hx'; omega
        have hsplit : ∑ j ∈ Finset.range J, blk j
            = (∑ j ∈ Finset.range J₀, blk j) + (∑ j ∈ Finset.Icc J₀ J₁, blk j)
              + ∑ j ∈ Finset.Icc (J₁+1) (J-1), blk j := by
          rw [hpart1, Finset.sum_union hdisj1, hpart2, Finset.sum_union hdisj2]
          ring
        rw [hsplit]
        have hL67 : 1 ≤ L ^ (6/7:ℝ) := Real.one_le_rpow hL1 (by norm_num)
        calc ‖1 + ((∑ j ∈ Finset.range J₀, blk j) + (∑ j ∈ Finset.Icc J₀ J₁, blk j)
              + ∑ j ∈ Finset.Icc (J₁+1) (J-1), blk j)‖
            ≤ 1 + (‖∑ j ∈ Finset.range J₀, blk j‖ + ‖∑ j ∈ Finset.Icc J₀ J₁, blk j‖
                + ‖∑ j ∈ Finset.Icc (J₁+1) (J-1), blk j‖) := by
              have h := norm_add_le (1 : ℂ) ((∑ j ∈ Finset.range J₀, blk j)
                + (∑ j ∈ Finset.Icc J₀ J₁, blk j) + ∑ j ∈ Finset.Icc (J₁+1) (J-1), blk j)
              rw [norm_one] at h
              have h2 := norm_add_le ((∑ j ∈ Finset.range J₀, blk j) + (∑ j ∈ Finset.Icc J₀ J₁, blk j))
                (∑ j ∈ Finset.Icc (J₁+1) (J-1), blk j)
              have h3 := norm_add_le (∑ j ∈ Finset.range J₀, blk j) (∑ j ∈ Finset.Icc J₀ J₁, blk j)
              linarith
          _ ≤ 1 + ((2 * Real.exp (cζ / c₂ ^ (6/7:ℝ) + 1) / (Real.log 2 * c₂ ^ (6/7:ℝ))) * L ^ (6/7:ℝ)
                + C₂ * Ablk * L ^ (6/7:ℝ) + C₃ * (1 + Real.sqrt (8 * Real.pi)) * L ^ (6/7:ℝ)) :=
              by linarith [htriv_sum, hv1_sum, hsdt_sum]
          _ ≤ Apart * L ^ (6/7:ℝ) := by
              rw [hApart]
              nlinarith [hL67, Real.exp_pos (cζ / c₂ ^ (6/7:ℝ) + 1), hC₂, hC₃, hAblk0,
                Real.sqrt_nonneg (8 * Real.pi), Real.log_pos (by norm_num : (1:ℝ) < 2),
                Real.rpow_pos_of_pos hLpos (6/7:ℝ), Real.rpow_pos_of_pos hc₂ (6/7:ℝ)]
      have hmain : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ Real.log (t + 3) ^ (6/7:ℝ) * (Apart + 2) := by
        have h1 : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
            ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
                - ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
              + ‖∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖ := by
          have h := norm_add_le (riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
              - ∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))
            (∑ n ∈ Finset.Icc 1 N, (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))
          rwa [sub_add_cancel] at h
        have h2 : 1 + 1 ≤ (2:ℝ) * L ^ (6/7:ℝ) := by
          have := Real.one_le_rpow hL1 (by norm_num : (0:ℝ) ≤ 6/7)
          linarith
        have h3 : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ (Apart + 2) * L ^ (6/7:ℝ) := by
          have hh := hEM
          linarith [h1, hEM, hpart, herr1, herr2, h2]
        rw [hLdef] at h3
        linarith [h3, mul_comm (Apart + 2) (Real.log (t + 3) ^ (6/7:ℝ))]
      have hcnn : (0:ℝ) ≤ Real.log (t + 3) ^ (6/7:ℝ) :=
        Real.rpow_nonneg (Real.log_nonneg (by linarith : (1:ℝ) ≤ t + 3)) _
      exact le_trans hmain (mul_le_mul_of_nonneg_left (le_max_left _ _) hcnn)
    · -- small L : crude bound
      have hTlt : t + 3 < Real.exp L₀ := by
        have h := Real.exp_lt_exp.mpr (lt_of_not_ge (by rw [hLdef] at hLbig; exact hLbig))
        rwa [Real.exp_log hTpos] at h
      have hEm1 := zeta_sub_Icc_sum_le hσpos (by linarith : t ≠ 0) 1 le_rfl
      have hnorm1 : ‖(∑ n ∈ Finset.Icc 1 1, ((n : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖ = 1 := by
        simp
      have hcb : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ 1 + 1/3 + (2 + Real.exp L₀) / (1/2) := by
        have hsn : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 2 + Real.exp L₀ := by
          have h1 : ‖((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ σ + t := by
            have h := norm_add_le ((σ : ℂ)) ((t : ℂ) * Complex.I)
            simp only [Complex.norm_real, Complex.norm_mul, Complex.norm_I, mul_one,
              Real.norm_eq_abs, abs_of_pos hσpos, abs_of_pos htpos] at h
            exact h
          linarith [hσhi, hTlt]
        have hsub : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
            - (∑ n ∈ Finset.Icc 1 1, ((n : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖
            ≤ 1/3 + (2 + Real.exp L₀) / (1/2) := by
          refine le_trans hEm1 ?_
          have hden : 0 < σ := hσpos
          have h1 : (1:ℝ)^(1-σ)/|t| ≤ 1/3 := by
            rw [Real.one_rpow, abs_of_pos htpos]
            rw [div_le_iff₀ (by linarith : (0:ℝ) < t)]
            nlinarith [ht3]
          have h2 : (‖((σ : ℂ) + (t : ℂ) * Complex.I)‖/σ) * (1:ℝ)^(-σ) ≤ (2 + Real.exp L₀)/(1/2) := by
            rw [Real.one_rpow, mul_one]
            rw [div_le_iff₀ hσpos]
            have h3 : (2 + Real.exp L₀) ≤ (2 + Real.exp L₀) / (1/2) * σ := by
              have h4 : (2 + Real.exp L₀) / (1/2) = 2 * (2 + Real.exp L₀) := by ring
              rw [h4]; nlinarith [hσhalf0]
            linarith [hsn, h3]
          linarith
        have h2 := norm_add_le (riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
            - (∑ n ∈ Finset.Icc 1 1, ((n : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))))
          (∑ n ∈ Finset.Icc 1 1, ((n : ℕ) : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))
        rw [sub_add_cancel, hnorm1] at h2
        linarith [h2, hsub]
      have hlog6 : Real.log 6 ≤ L := by
        rw [hLdef]; exact Real.log_le_log (by norm_num) (by linarith)
      have hAcrude : (1 + 1/3 + (2 + Real.exp L₀) / (1/2)) / (Real.log 6) ^ (6/7:ℝ)
          * L ^ (6/7:ℝ) = (1 + 1/3 + (2 + Real.exp L₀) / (1/2))
            * (L ^ (6/7:ℝ) / (Real.log 6) ^ (6/7:ℝ)) := by ring
      have hAcrude2 : (1 + 1/3 + (2 + Real.exp L₀) / (1/2))
          ≤ ((1 + 1/3 + (2 + Real.exp L₀) / (1/2)) / (Real.log 6) ^ (6/7:ℝ)) * L ^ (6/7:ℝ) := by
        have h1 : (1:ℝ) ≤ L ^ (6/7:ℝ) / (Real.log 6) ^ (6/7:ℝ) := by
          rw [le_div_iff₀ (Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _), one_mul]
          exact Real.rpow_le_rpow (Real.log_nonneg (by norm_num)) hlog6 (by norm_num)
        have h2 : (0:ℝ) ≤ 1 + 1/3 + (2 + Real.exp L₀) / (1/2) := by positivity
        calc (1 + 1/3 + (2 + Real.exp L₀) / (1/2))
            = (1 + 1/3 + (2 + Real.exp L₀) / (1/2)) * 1 := by ring
          _ ≤ (1 + 1/3 + (2 + Real.exp L₀) / (1/2)) * (L ^ (6/7:ℝ) / (Real.log 6) ^ (6/7:ℝ)) :=
              mul_le_mul_of_nonneg_left h1 h2
          _ = ((1 + 1/3 + (2 + Real.exp L₀) / (1/2)) / (Real.log 6) ^ (6/7:ℝ)) * L ^ (6/7:ℝ) := by
              ring
      have hcnn : (0:ℝ) ≤ Real.log (t + 3) ^ (6/7:ℝ) :=
        Real.rpow_nonneg (Real.log_nonneg (by linarith : (1:ℝ) ≤ t + 3)) _
      have hgoal : ((1 + 1/3 + (2 + Real.exp L₀) / (1/2)) / (Real.log 6) ^ (6/7:ℝ)) * L ^ (6/7:ℝ)
          ≤ Real.log (t + 3) ^ (6/7:ℝ) * max (Apart + 2)
              ((1 + 1/3 + (2 + Real.exp L₀) / (1/2)) / (Real.log 6) ^ (6/7:ℝ)) := by
        rw [hLdef]
        calc ((1 + 1/3 + (2 + Real.exp L₀) / (1/2)) / (Real.log 6) ^ (6/7:ℝ))
              * Real.log (t + 3) ^ (6/7:ℝ)
            = Real.log (t + 3) ^ (6/7:ℝ)
              * ((1 + 1/3 + (2 + Real.exp L₀) / (1/2)) / (Real.log 6) ^ (6/7:ℝ)) := by ring
          _ ≤ Real.log (t + 3) ^ (6/7:ℝ) * max (Apart + 2)
                ((1 + 1/3 + (2 + Real.exp L₀) / (1/2)) / (Real.log 6) ^ (6/7:ℝ)) :=
              mul_le_mul_of_nonneg_left (le_max_right _ _) hcnn
      linarith [hcb, hAcrude2, hgoal]
  intro σ t ht hσlo hσhi
  by_cases ht0 : 0 ≤ t
  · have ht3 : 3 ≤ t := by rw [abs_of_nonneg ht0] at ht; exact ht
    have h := key σ t ht3 (by rw [abs_of_nonneg ht0] at hσlo; exact hσlo) hσhi
    have hrw : Real.log (t + 3) = Real.log (|t| + 3) := by rw [abs_of_nonneg ht0]
    rw [hrw] at h
    calc ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        ≤ Real.log (|t| + 3) ^ (6 / 7 : ℝ) * max (Apart + 2)
            ((1 + 1/3 + (2 + Real.exp L₀) / (1/2)) / (Real.log 6) ^ (6/7:ℝ)) := h
      _ = max (Apart + 2) ((1 + 1/3 + (2 + Real.exp L₀) / (1/2)) / (Real.log 6) ^ (6/7:ℝ))
            * Real.log (|t| + 3) ^ (6 / 7 : ℝ) := by ring
  · have ht0' : t < 0 := lt_of_not_ge ht0
    have ht3 : 3 ≤ -t := by
      rw [abs_of_neg ht0'] at ht
      exact ht
    have hσlo' : 1 - cζ * Real.log ((-t) + 3) ^ (-(6 / 7 : ℝ)) ≤ σ := by
      rw [abs_of_neg ht0'] at hσlo
      exact hσlo
    have h := key σ (-t) ht3 hσlo' hσhi
    have htcast : (t : ℂ) = -((-t : ℝ) : ℂ) := by
      rw [← Complex.ofReal_neg (-t), neg_neg]
    have hconj : ((σ : ℂ) + (t : ℂ) * Complex.I)
        = (starRingEnd ℂ) ((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I) := by
      rw [htcast]
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring_nf
    rw [hconj, riemannZeta_conj]
    simp only [starRingEnd_apply, norm_star]
    have habs : |t| = -t := abs_of_neg ht0'
    rw [habs]
    calc ‖riemannZeta (((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I))‖
        ≤ Real.log ((-t) + 3) ^ (6 / 7 : ℝ) * max (Apart + 2)
            ((1 + 1/3 + (2 + Real.exp L₀) / (1/2)) / (Real.log 6) ^ (6/7:ℝ)) := h
      _ = max (Apart + 2) ((1 + 1/3 + (2 + Real.exp L₀) / (1/2)) / (Real.log 6) ^ (6/7:ℝ))
            * Real.log ((-t) + 3) ^ (6 / 7 : ℝ) := by ring


end

end Work.BMF.N7
