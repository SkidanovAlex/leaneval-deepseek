import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.n8_defs
import Submission.Work.BMF.aemeasurable_window_avg
import Submission.Work.N8.exists_large_fiber

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# N8: aggregation of local twists into a global twisted correlation

This file proves `Work.N8.aggregate_twist`, the "Step 7 aggregation" of the N8 node: if each of at
least `cA * N` well-separated short intervals `[x, x+L]` inside `[N*L/10, 10*N*L]` carries a local
twisted correlation for one of at most `R₀^R₀` periodic functions `ψ ∈ Ψ`, then a *single* `ψ ∈ Ψ`
satisfies a global twisted correlation `TwistCorr f ψ T₀ Y H' c'` at some dyadic scale
`max Y₀ X^{1/2} ≤ Y ≤ X`.

The two ingredients are
* `Work.N8.exists_large_fiber` (a pigeonhole over the fibers of `Ψ`), and
* the two measure-theoretic lemmas below: integrability of the window-sum norm on every interval,
  and the dyadic aggregation of a sum of integrals over separated short intervals.
-/

namespace Work.N8

open MeasureTheory intervalIntegral
open scoped BigOperators

/-- The normed window sum `y ↦ ‖∑_{n ∈ natIcc y (y+H')} a n‖` is integrable on every interval
`uIcc c d`.  It is a measurable step function of `y` (finite sum of indicators), and on a bounded
interval the summation range is contained in the fixed finite set `natIcc c (d + H')`, so it is
bounded. -/
lemma integrableOn_natIcc_norm (H' : ℝ) (a : ℕ → ℂ) :
    ∀ c d : ℝ,
      IntegrableOn (fun y : ℝ => ‖∑ n ∈ Work.BMF.natIcc y (y + H'), a n‖) (Set.uIcc c d) := by
  intro c d
  set F : ℝ → ℝ := fun y => ‖∑ n ∈ Work.BMF.natIcc y (y + H'), a n‖ with hF
  have hmeas : Measurable F := (Work.BMF.measurable_window_sum a H').norm
  set N : ℕ := ⌊max c d + H'⌋₊ with hN
  set C₀ : ℝ := ∑ n ∈ Finset.Icc 0 N, ‖a n‖ with hC₀
  have hbound : ∀ y ∈ Set.uIcc c d, ‖F y‖ ≤ C₀ := by
    intro y hy
    have hyM : y ≤ max c d := by
      rw [Set.mem_uIcc] at hy
      rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact le_trans h2 (le_max_right c d)
      · exact le_trans h2 (le_max_left c d)
    have hsub : Work.BMF.natIcc y (y + H') ⊆ Finset.Icc 0 N := by
      intro n hn
      have hn' : ⌈y⌉₊ ≤ n ∧ n ≤ ⌊y + H'⌋₊ := by
        simpa only [Work.BMF.natIcc, Finset.mem_Icc] using hn
      refine Finset.mem_Icc.mpr ⟨Nat.zero_le n, ?_⟩
      calc n ≤ ⌊y + H'⌋₊ := hn'.2
        _ ≤ ⌊max c d + H'⌋₊ := Nat.floor_mono (by linarith)
        _ = N := by rw [hN]
    have hle : ‖∑ n ∈ Work.BMF.natIcc y (y + H'), a n‖ ≤ C₀ := by
      calc ‖∑ n ∈ Work.BMF.natIcc y (y + H'), a n‖
          ≤ ∑ n ∈ Work.BMF.natIcc y (y + H'), ‖a n‖ := norm_sum_le _ _
        _ ≤ ∑ n ∈ Finset.Icc 0 N, ‖a n‖ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => norm_nonneg _)
        _ = C₀ := by rw [hC₀]
    have hFy : F y = ‖∑ n ∈ Work.BMF.natIcc y (y + H'), a n‖ := by rw [hF]
    rw [hFy, Real.norm_of_nonneg (norm_nonneg _)]
    exact hle
  have hmem : ∀ᵐ y ∂(volume.restrict (Set.uIcc c d)), ‖F y‖ ≤ C₀ :=
    (ae_restrict_iff' measurableSet_uIcc).mpr
      (Filter.Eventually.of_forall (fun y hy => hbound y hy))
  exact IntegrableOn.of_bound isCompact_uIcc.measure_lt_top hmeas.aestronglyMeasurable C₀ hmem

/-- Dyadic aggregation.  Let `G ≥ 0` be integrable on every `uIcc`, and let `S` be a finite set of
reals whose intervals `(x, x+L]` lie in `(u, 100u]` and are pairwise disjoint.  Then there is a
dyadic window `[Y, 2Y]` with `u ≤ Y ≤ 64u` (and hence `Y ≤ X` when `64u ≤ X`) which captures a `1/7`
fraction of the total integral: `Σ_{x∈S} ∫_x^{x+L} G ≤ 7 ∫_Y^{2Y} G`. -/
lemma dyadic_aggregate (G : ℝ → ℝ) (hG : ∀ y, 0 ≤ G y)
    (hint : ∀ a b : ℝ, IntegrableOn G (Set.uIcc a b))
    (u X L : ℝ) (hu : 0 < u) (hL : 0 < L) (hXu : 64 * u ≤ X) (S : Finset ℝ)
    (hmem : ∀ x ∈ S, u ≤ x ∧ x + L ≤ 100 * u)
    (hsep : ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → 2 * L ≤ |x - x'|) :
    ∃ Y : ℝ, u ≤ Y ∧ Y ≤ 64 * u ∧ Y ≤ X ∧
      (∑ x ∈ S, ∫ y in x..(x + L), G y) ≤ 7 * ∫ y in Y..(2 * Y), G y := by
  have hIocU : ∀ a b : ℝ, a ≤ b → Set.Ioc a b ⊆ Set.uIcc a b := by
    intro a b _ y hy
    rw [Set.mem_uIcc]
    exact Or.inl ⟨hy.1.le, hy.2⟩
  -- every short interval lies inside `(u, 128u]`
  have hsub : ∀ x ∈ S, Set.Ioc x (x + L) ⊆ Set.Ioc u (128 * u) := by
    intro x hx y hy
    obtain ⟨h1, h2⟩ := hmem x hx
    exact ⟨lt_of_le_of_lt h1 hy.1, le_trans hy.2 (by linarith)⟩
  -- the short intervals are pairwise disjoint
  have hdisj : ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' →
      Disjoint (Set.Ioc x (x + L)) (Set.Ioc x' (x' + L)) := by
    intro x hx x' hx' hne
    rw [Set.disjoint_left]
    intro y hy hy'
    have h := hsep x hx x' hx' hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : x' < x + L := lt_of_lt_of_le hy'.1 hy.2
      rw [abs_of_neg (by linarith)] at h
      linarith
    · have h1 : x < x' + L := lt_of_lt_of_le hy.1 hy'.2
      rw [abs_of_pos (by linarith)] at h
      linarith
  have hint_ind : ∀ x ∈ S, Integrable ((Set.Ioc x (x + L)).indicator G) := by
    intro x hx
    exact ((hint x (x + L)).mono_set (hIocU x (x + L) (by linarith))).integrable_indicator
      measurableSet_Ioc
  -- the sum of the short-interval integrals is the integral of the sum of the indicators
  have hAsum : (∑ x ∈ S, ∫ y in x..(x + L), G y)
      = ∫ y, ∑ x ∈ S, (Set.Ioc x (x + L)).indicator G y := by
    rw [MeasureTheory.integral_finsetSum _ hint_ind]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [intervalIntegral.integral_of_le (by linarith)]
    exact (MeasureTheory.integral_indicator (s := Set.Ioc x (x + L)) (f := G)
      measurableSet_Ioc).symm
  -- pointwise domination by the indicator of `(u, 128u)`
  have hpt : ∀ y, (∑ x ∈ S, (Set.Ioc x (x + L)).indicator G y)
      ≤ (Set.Ioc u (128 * u)).indicator G y := by
    intro y
    by_cases hy : y ∈ Set.Ioc u (128 * u)
    · rw [Set.indicator_of_mem hy]
      have hcnt : (∑ x ∈ S, (Set.Ioc x (x + L)).indicator (fun _ => (1 : ℝ)) y) ≤ 1 := by
        by_cases hex : ∃ x ∈ S, y ∈ Set.Ioc x (x + L)
        · obtain ⟨x₀, hx₀, hy₀⟩ := hex
          have hsingle :
              (∑ x ∈ S, (Set.Ioc x (x + L)).indicator (fun _ => (1 : ℝ)) y) = 1 := by
            rw [Finset.sum_eq_single x₀]
            · rw [Set.indicator_of_mem hy₀]
            · intro b hb hbne
              rw [Set.indicator_of_notMem]
              intro hyb
              exact (Set.disjoint_left.mp (hdisj b hb x₀ hx₀ hbne)) hyb hy₀
            · intro hx₀not
              exact absurd hx₀ hx₀not
          rw [hsingle]
        · push Not at hex
          rw [Finset.sum_eq_zero]
          · norm_num
          · intro x hx
            rw [Set.indicator_of_notMem]
            exact hex x hx
      calc ∑ x ∈ S, (Set.Ioc x (x + L)).indicator G y
          = (∑ x ∈ S, (Set.Ioc x (x + L)).indicator (fun _ => (1 : ℝ)) y) * G y := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun x hx => ?_)
            by_cases h : y ∈ Set.Ioc x (x + L)
            · simp [Set.indicator_of_mem h]
            · simp [Set.indicator_of_notMem h]
        _ ≤ 1 * G y := mul_le_mul_of_nonneg_right hcnt (hG y)
        _ = G y := one_mul _
    · rw [Set.indicator_of_notMem hy]
      have hzero : ∀ x ∈ S, (Set.Ioc x (x + L)).indicator G y = 0 := by
        intro x hx
        rw [Set.indicator_of_notMem]
        intro hyx
        exact hy (hsub x hx hyx)
      rw [Finset.sum_eq_zero hzero]
  have hint_sum : Integrable (fun y => ∑ x ∈ S, (Set.Ioc x (x + L)).indicator G y) :=
    integrable_finsetSum S hint_ind
  have hintR : Integrable (fun y => (Set.Ioc u (128 * u)).indicator G y) :=
    ((hint u (128 * u)).mono_set (hIocU u (128 * u) (by linarith))).integrable_indicator
      measurableSet_Ioc
  have hstep : (∑ x ∈ S, ∫ y in x..(x + L), G y) ≤ ∫ y in u..(128 * u), G y := by
    rw [hAsum, intervalIntegral.integral_of_le (by linarith)]
    rw [← MeasureTheory.integral_indicator (s := Set.Ioc u (128 * u)) (f := G) measurableSet_Ioc]
    exact MeasureTheory.integral_mono hint_sum hintR hpt
  -- split `[u, 128u]` into the seven dyadic pieces `[2^k u, 2^{k+1} u]`
  have hsplit : (∑ k ∈ Finset.range 7, ∫ y in (2 : ℝ) ^ k * u..(2 : ℝ) ^ (k + 1) * u, G y)
      = ∫ y in u..(128 * u), G y := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := G)
      (a := fun k => (2 : ℝ) ^ k * u) (n := 7)
      (fun k hk => (hint _ _).intervalIntegrable)
    have h20 : (2 : ℝ) ^ 0 * u = u := by norm_num
    have h27 : (2 : ℝ) ^ 7 * u = 128 * u := by norm_num
    simpa only [h20, h27] using h
  have hMsum : (∑ x ∈ S, ∫ y in x..(x + L), G y)
      ≤ ∑ k ∈ Finset.range 7, ∫ y in (2 : ℝ) ^ k * u..(2 : ℝ) ^ (k + 1) * u, G y := by
    rw [hsplit]; exact hstep
  have hconst : (∑ _k ∈ Finset.range 7, (∑ x ∈ S, ∫ y in x..(x + L), G y) / 7)
      = (∑ x ∈ S, ∫ y in x..(x + L), G y) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  obtain ⟨j, hj, hjle⟩ := Finset.exists_le_of_sum_le (s := Finset.range 7)
    (f := fun _ => (∑ x ∈ S, ∫ y in x..(x + L), G y) / 7)
    (g := fun k => ∫ y in (2 : ℝ) ^ k * u..(2 : ℝ) ^ (k + 1) * u, G y)
    ⟨0, Finset.mem_range.mpr (by norm_num)⟩ (by rw [hconst]; exact hMsum)
  have hYu : u ≤ (2 : ℝ) ^ j * u := by
    have hp : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    calc u = 1 * u := by ring
      _ ≤ (2 : ℝ) ^ j * u := mul_le_mul_of_nonneg_right hp (le_of_lt hu)
  have hj6 : j ≤ 6 := by
    have : j < 7 := Finset.mem_range.mp hj
    omega
  have hY64 : (2 : ℝ) ^ j * u ≤ 64 * u := by
    have hp : (2 : ℝ) ^ j ≤ 64 := by
      calc (2 : ℝ) ^ j ≤ (2 : ℝ) ^ 6 := pow_le_pow_right₀ (by norm_num) hj6
        _ = 64 := by norm_num
    exact mul_le_mul_of_nonneg_right hp (le_of_lt hu)
  refine ⟨(2 : ℝ) ^ j * u, hYu, hY64, le_trans hY64 hXu, ?_⟩
  have h2 : (2 : ℝ) * ((2 : ℝ) ^ j * u) = (2 : ℝ) ^ (j + 1) * u := by
    rw [pow_succ]; ring
  rw [h2]
  linarith [hjle]

theorem aggregate_twist (R₀ : ℕ) (hR₀ : 1 ≤ R₀) (cA : ℝ) (hcA : 0 < cA) :
    ∃ c' : ℝ, 0 < c' ∧
    ∀ (Y₀ N L H' T₀ X : ℝ) (f : ℕ → ℂ) (Xt : Finset ℝ) (Ψ : Finset (ℕ → ℂ)) (r : ℕ),
      0 < L → 0 < H' → H' ≤ L → 1 ≤ N → 16 ≤ cA * N → r ≤ R₀ →
      (Ψ.card : ℝ) ≤ (R₀ : ℝ) ^ R₀ →
      (∀ ψ ∈ Ψ, Work.BMF.IsPeriodicBdd r ψ) →
      (∀ x ∈ Xt, ∃ ψ ∈ Ψ, Work.BMF.LocalTwist f ψ T₀ x L H' cA) →
      (∀ x ∈ Xt, N * L / 10 ≤ x ∧ x + L ≤ 10 * (N * L)) →
      (∀ x ∈ Xt, ∀ x' ∈ Xt, x ≠ x' → 2 * L ≤ |x - x'|) →
      cA * N ≤ (Xt.card : ℝ) →
      10 * (X ^ (1 / 2 : ℝ)) ≤ N * L → 10 * (N * L) ≤ X → Y₀ ≤ N * L / 10 →
      ∃ ψ : ℕ → ℂ, ψ ∈ Ψ ∧ ∃ Y : ℝ,
        Y₀ ≤ Y ∧ X ^ (1 / 2 : ℝ) ≤ Y ∧ Y ≤ X ∧ Work.BMF.TwistCorr f ψ T₀ Y H' c'
:= by
  have hR₀pos : (0 : ℝ) < (R₀ : ℝ) := by exact_mod_cast hR₀
  have hMpos : (0 : ℝ) < (R₀ : ℝ) ^ R₀ := pow_pos hR₀pos R₀
  refine ⟨cA ^ 2 / (100 * (R₀ : ℝ) ^ R₀),
    div_pos (pow_pos hcA 2) (mul_pos (by norm_num) hMpos), ?_⟩
  intro Y₀ N L H' T₀ X f Xt Ψ r hL hH' hH'L hN hcAN hrR hΨcard hper hex hplace hsep hcard
    hXsqrt hXbig hY₀
  -- pigeonhole over the fibers of `Ψ`
  obtain ⟨ψ, hψΨ, S, hSsub, hScard, hSprop⟩ :=
    Work.N8.exists_large_fiber (fun ψ x => Work.BMF.LocalTwist f ψ T₀ x L H' cA) Xt Ψ cA N
      ((R₀ : ℝ) ^ R₀) hcA hN hMpos hΨcard hcard hex
  set G : ℝ → ℝ :=
    fun y => ‖∑ n ∈ Work.BMF.natIcc y (y + H'),
      f n * ψ n * (n : ℂ) ^ (-(Complex.I * T₀))‖ with hGdef
  have hint : ∀ a b : ℝ, IntegrableOn G (Set.uIcc a b) := by
    intro a b
    have h := integrableOn_natIcc_norm H' (fun n => f n * ψ n * (n : ℂ) ^ (-(Complex.I * T₀))) a b
    simpa only [hGdef] using h
  have hGnn : ∀ y, 0 ≤ G y := fun y => norm_nonneg _
  have hNLpos : 0 < N * L := by
    have : (0 : ℝ) < N := by linarith
    positivity
  have hu : 0 < N * L / 10 := by linarith [hNLpos]
  have hXu : 64 * (N * L / 10) ≤ X := by nlinarith [hXbig, hNLpos]
  have hmemS : ∀ x ∈ S, N * L / 10 ≤ x ∧ x + L ≤ 100 * (N * L / 10) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hplace x (hSsub hx)
    refine ⟨h1, ?_⟩
    have : 100 * (N * L / 10) = 10 * (N * L) := by ring
    rw [this]; exact h2
  have hsepS : ∀ x ∈ S, ∀ x' ∈ S, x ≠ x' → 2 * L ≤ |x - x'| :=
    fun x hx x' hx' hne => hsep x (hSsub hx) x' (hSsub hx') hne
  obtain ⟨Y, hYu, hY64, hYX, hYineq⟩ :=
    dyadic_aggregate G hGnn hint (N * L / 10) X L hu hL hXu S hmemS hsepS
  refine ⟨ψ, hψΨ, Y, ?_, ?_, hYX, ?_⟩
  · exact le_trans hY₀ hYu
  · have : X ^ (1 / 2 : ℝ) ≤ N * L / 10 := by linarith [hXsqrt]
    exact le_trans this hYu
  · -- the main inequality
    have hSprop' : ∀ x ∈ S, cA * L * H' ≤ ∫ y in x..(x + L), G y :=
      fun x hx => hSprop x hx
    have hsum_lb : (∑ x ∈ S, cA * L * H') ≤ ∑ x ∈ S, ∫ y in x..(x + L), G y :=
      Finset.sum_le_sum hSprop'
    have hsum_const : (∑ x ∈ S, cA * L * H') = (S.card : ℝ) * (cA * L * H') := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have hYnn : 0 ≤ Y := le_trans (le_of_lt hu) hYu
    have hAnn : 0 ≤ ∫ y in Y..(2 * Y), G y :=
      intervalIntegral.integral_nonneg (by linarith) (fun u _ => hGnn u)
    have hlow : (S.card : ℝ) * (cA * L * H') ≤ 7 * ∫ y in Y..(2 * Y), G y := by
      rw [← hsum_const]
      exact le_trans hsum_lb hYineq
    -- clear the denominator
    have h4 : cA ^ 2 * N * L * H' ≤ 7 * (∫ y in Y..(2 * Y), G y) * (R₀ : ℝ) ^ R₀ := by
      have h1 : cA * N / (R₀ : ℝ) ^ R₀ * (cA * L * H')
          ≤ (S.card : ℝ) * (cA * L * H') :=
        mul_le_mul_of_nonneg_right hScard
          (mul_nonneg (mul_nonneg (le_of_lt hcA) (le_of_lt hL)) (le_of_lt hH'))
      have h2 : cA * N / (R₀ : ℝ) ^ R₀ * (cA * L * H')
          = cA ^ 2 * N * L * H' / (R₀ : ℝ) ^ R₀ := by
        field_simp
      have h5 : cA ^ 2 * N * L * H' / (R₀ : ℝ) ^ R₀
          ≤ 7 * (∫ y in Y..(2 * Y), G y) := by
        rw [← h2]
        exact le_trans h1 hlow
      rwa [div_le_iff₀ hMpos] at h5
    have hYb : Y ≤ 32 * N * L / 5 := by nlinarith [hY64]
    have hb1 : cA ^ 2 * H' * Y ≤ cA ^ 2 * H' * (32 * N * L / 5) :=
      mul_le_mul_of_nonneg_left hYb (mul_nonneg (sq_nonneg cA) (le_of_lt hH'))
    have hb2 : cA ^ 2 * H' * (32 * N * L / 5) = 32 / 5 * (cA ^ 2 * N * L * H') := by
      ring
    have hb3 : 32 / 5 * (cA ^ 2 * N * L * H')
        ≤ 32 / 5 * (7 * (∫ y in Y..(2 * Y), G y) * (R₀ : ℝ) ^ R₀) :=
      mul_le_mul_of_nonneg_left h4 (by norm_num)
    have hAM : 0 ≤ (∫ y in Y..(2 * Y), G y) * (R₀ : ℝ) ^ R₀ :=
      mul_nonneg hAnn (le_of_lt hMpos)
    have hb4 : 32 / 5 * (7 * (∫ y in Y..(2 * Y), G y) * (R₀ : ℝ) ^ R₀)
        ≤ (∫ y in Y..(2 * Y), G y) * (100 * (R₀ : ℝ) ^ R₀) := by
      nlinarith [hAM]
    have hmain2 : cA ^ 2 * H' * Y
        ≤ (∫ y in Y..(2 * Y), G y) * (100 * (R₀ : ℝ) ^ R₀) :=
      le_trans hb1 (le_trans (le_of_eq hb2) (le_trans hb3 hb4))
    have hkey : cA ^ 2 / (100 * (R₀ : ℝ) ^ R₀) * H' * Y ≤ ∫ y in Y..(2 * Y), G y := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
        div_le_iff₀ (mul_pos (by norm_num) hMpos)]
      linarith [hmain2]
    rw [Work.BMF.TwistCorr]
    exact hkey

end Work.N8
