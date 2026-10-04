import Mathlib
import Submission.Work.Diff.EXT.iteratedDeriv_tsum
import Submission.Work.Diff.EXT.iteratedDeriv_flat_mul_pow_jet
import Submission.Work.Diff.EXT.borel_bump_pow_le
import Submission.Work.Diff.EXT.borel_smul_cutoff
import Submission.Work.Diff.EXT.borel_eps_exists

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Filter Set
open scoped Topology ContDiff

namespace Work.Diff.EXT

/-- The iterated derivative of `q ↦ c q.1` on `ℝ × E` is bounded by the iterated derivative
of `c` at `p.1`: the former is the latter post-composed, in every argument, with the
(norm-one) first projection. -/
theorem borel_norm_iteratedFDeriv_fst_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : ℝ → F) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (a : ℕ) (p : ℝ × E) :
    ‖iteratedFDeriv ℝ a (fun q : ℝ × E => c q.1) p‖ ≤ ‖iteratedFDeriv ℝ a c p.1‖ := by
  have hfst : (fun q : ℝ × E => c q.1) = c ∘ (ContinuousLinearMap.fst ℝ ℝ E) := rfl
  rw [hfst]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.fst ℝ ℝ E) hc p
      (WithTop.coe_le_coe.mpr le_top)]
  refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
  show ‖iteratedFDeriv ℝ a c p.1‖ * ∏ _i : Fin a, ‖(ContinuousLinearMap.fst ℝ ℝ E)‖ ≤
    ‖iteratedFDeriv ℝ a c p.1‖
  have hprod : ∏ _i : Fin a, ‖(ContinuousLinearMap.fst ℝ ℝ E)‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ ℝ E)
  calc ‖iteratedFDeriv ℝ a c p.1‖ * ∏ _i : Fin a, ‖(ContinuousLinearMap.fst ℝ ℝ E)‖
      ≤ ‖iteratedFDeriv ℝ a c p.1‖ * 1 := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ a c p.1‖ := mul_one _

/-- The iterated derivative of `q ↦ c q.2` on `ℝ × E` is bounded by the iterated derivative
of `c` at `p.2`. -/
theorem borel_norm_iteratedFDeriv_snd_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (c : E → F) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (a : ℕ) (p : ℝ × E) :
    ‖iteratedFDeriv ℝ a (fun q : ℝ × E => c q.2) p‖ ≤ ‖iteratedFDeriv ℝ a c p.2‖ := by
  have hsnd : (fun q : ℝ × E => c q.2) = c ∘ (ContinuousLinearMap.snd ℝ ℝ E) := rfl
  rw [hsnd]
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.snd ℝ ℝ E) hc p
      (WithTop.coe_le_coe.mpr le_top)]
  refine le_trans (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _) ?_
  show ‖iteratedFDeriv ℝ a c p.2‖ * ∏ _i : Fin a, ‖(ContinuousLinearMap.snd ℝ ℝ E)‖ ≤
    ‖iteratedFDeriv ℝ a c p.2‖
  have hprod : ∏ _i : Fin a, ‖(ContinuousLinearMap.snd ℝ ℝ E)‖ ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ ℝ E)
  calc ‖iteratedFDeriv ℝ a c p.2‖ * ∏ _i : Fin a, ‖(ContinuousLinearMap.snd ℝ ℝ E)‖
      ≤ ‖iteratedFDeriv ℝ a c p.2‖ * 1 := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ a c p.2‖ := mul_one _

/-- **Borel's theorem on jets, on an open set.**  Given smooth functions `f k` on an open set
`U` of a finite-dimensional real normed space `E` and a point `y₀ ∈ U`, there are a radius
`ε > 0`, an open neighbourhood `W ∋ y₀` with `W ⊆ U`, and a smooth `F : ℝ × E → Z` such that
for every `k` and every `y ∈ W` the `k`-th `t`-derivative of `t ↦ F (t, y)` at `0` equals `f k y`.

The construction is the classical one: `F (t, y) = ∑' n, φ (t / ε n) * t ^ n / n ! • (χ y • f n y)`
where `χ` is a bump equal to `1` near `y₀` with support in `U`, `φ` is a bump equal to `1` near
`0`, and the widths `ε n` are chosen so small that every term is dominated by `2 ^ (-n)`. -/
theorem borel_jet_on
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    {U : Set E} (hU : IsOpen U) (f : ℕ → E → Z) (hf : ∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (f k) U)
    {y₀ : E} (hy₀ : y₀ ∈ U) :
    ∃ ε > 0, ∃ W : Set E, IsOpen W ∧ y₀ ∈ W ∧ W ⊆ U ∧ ∃ F : ℝ × E → Z,
      ContDiffOn ℝ (⊤ : ℕ∞) F ((Set.Ioo (-ε) ε) ×ˢ W) ∧
      ∀ k : ℕ, ∀ y ∈ W, iteratedDeriv k (fun t : ℝ => F (t, y)) 0 = f k y := by
  -- A ball around `y₀` inside `U`.
  obtain ⟨δ, hδpos, hδU⟩ : ∃ δ > 0, Metric.ball y₀ δ ⊆ U := Metric.isOpen_iff.mp hU y₀ hy₀
  -- The cut-off in the space variable.
  let χ : ContDiffBump y₀ := ⟨δ / 4, δ / 2, by linarith, by linarith⟩
  have hχ_rIn : χ.rIn = δ / 4 := rfl
  have hχ_rOut : χ.rOut = δ / 2 := rfl
  have hχ_smooth : ContDiff ℝ (⊤ : ℕ∞) (χ : E → ℝ) := χ.contDiff
  have hχ_tsupp : tsupport (χ : E → ℝ) ⊆ U := by
    rw [ContDiffBump.tsupport_eq, hχ_rOut]
    exact subset_trans (Metric.closedBall_subset_ball (by linarith)) hδU
  have hχ_cs : HasCompactSupport (χ : E → ℝ) := χ.hasCompactSupport
  let W : Set E := Metric.ball y₀ (δ / 4)
  have hW_open : IsOpen W := Metric.isOpen_ball
  have hW_mem : y₀ ∈ W := Metric.mem_ball_self (by linarith)
  have hW_sub : W ⊆ U := fun y hy => hδU (Metric.ball_subset_ball (by linarith) hy)
  have hW_one : ∀ y ∈ W, (χ : E → ℝ) y = 1 := by
    intro y hy
    refine χ.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, hχ_rIn]
    exact le_of_lt (Metric.mem_ball.mp hy)
  -- The (compactly supported) space part of the `n`-th term.
  let A : ℕ → E → Z := fun n y => (χ : E → ℝ) y • f n y
  have hA : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (A n) :=
    fun n => borel_smul_cutoff (χ : E → ℝ) hχ_smooth hU hχ_tsupp (f n) (hf n)
  have hA_cs : ∀ n, HasCompactSupport (A n) := by
    intro n
    refine hχ_cs.mono' (subset_trans (subset_tsupport (A n)) ?_)
    exact tsupport_smul_subset_left (χ : E → ℝ) (f n)
  -- Uniform bounds for the derivatives of the space parts.
  choose M hMspec using fun n b => (hA_cs n).exists_bound_iteratedFDeriv (hA n) b
  have hMnn : ∀ n b, 0 ≤ M n b := fun n b => (hMspec n b).1
  have hMb : ∀ n b i, i ≤ b → ∀ y, ‖iteratedFDeriv ℝ i (A n) y‖ ≤ M n b :=
    fun n b i hi y => (hMspec n b).2 i hi y
  -- The one-variable bump, flat outside `[-3/2, 3/2]` and equal to `1` on `[-1,1]`.
  let φ : ContDiffBump (0 : ℝ) := ⟨1, 3 / 2, one_pos, by norm_num⟩
  have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) (φ : ℝ → ℝ) := φ.contDiff
  have hφ_one : ∀ t : ℝ, |t| ≤ 1 → (φ : ℝ → ℝ) t = 1 := by
    intro t ht
    refine φ.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
    change |t| ≤ 1
    exact ht
  have hφ_zero : ∀ t : ℝ, 3 / 2 ≤ |t| → (φ : ℝ → ℝ) t = 0 := by
    intro t ht
    refine φ.zero_of_le_dist ?_
    rw [Real.dist_eq, sub_zero]
    change 3 / 2 ≤ |t|
    exact ht
  have hφ_cs : HasCompactSupport (φ : ℝ → ℝ) := φ.hasCompactSupport
  have hφ_zero_iter : ∀ (j : ℕ) (t : ℝ), 2 ≤ |t| → iteratedFDeriv ℝ j (φ : ℝ → ℝ) t = 0 := by
    intro j t ht
    set V : Set ℝ := {s : ℝ | 3 / 2 < |s|} with hV
    have htV : t ∈ V := by
      rw [hV]
      simp only [Set.mem_setOf_eq]
      linarith
    have hVopen : IsOpen V := isOpen_lt continuous_const continuous_abs
    have hEq : Set.EqOn (φ : ℝ → ℝ) (0 : ℝ → ℝ) V := by
      intro s hs
      rw [hV] at hs
      exact hφ_zero s (le_of_lt hs)
    have h1 : iteratedFDerivWithin ℝ j (φ : ℝ → ℝ) V t =
        iteratedFDerivWithin ℝ j (0 : ℝ → ℝ) V t :=
      iteratedFDerivWithin_congr hEq htV j
    have h2 : iteratedFDerivWithin ℝ j (0 : ℝ → ℝ) V t = 0 := by
      simp [iteratedFDerivWithin_zero]
    rw [← iteratedFDerivWithin_eq_iteratedFDeriv hVopen.uniqueDiffOn
        (hφ_smooth.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) htV, h1, h2]
  -- Derivatives bounds for `φ`.
  choose Φ hΦspec using fun b => hφ_cs.exists_bound_iteratedFDeriv hφ_smooth b
  have hΦnn : ∀ b, 0 ≤ Φ b := fun b => (hΦspec b).1
  have hΦ : ∀ b t, ‖iteratedFDeriv ℝ b (φ : ℝ → ℝ) t‖ ≤ Φ b :=
    fun b t => (hΦspec b).2 b le_rfl t
  -- The combinatorial constant of the scalar estimate.
  let Cap : ℕ → ℝ := fun a => ∑ d ∈ Finset.range (a + 1), (a.choose d : ℝ) * Φ (a - d) * 8
  have hCap : ∀ a, 0 ≤ Cap a := by
    intro a
    refine Finset.sum_nonneg (fun d _ => ?_)
    have h1 : (0 : ℝ) ≤ (a.choose d : ℝ) := Nat.cast_nonneg _
    exact mul_nonneg (mul_nonneg h1 (hΦnn _)) (by norm_num)
  -- The widths, chosen so that the terms of the series decay like `2 ^ (-n)`.
  obtain ⟨ε, hεpos, hεle1, hεb⟩ := borel_eps_exists Cap M hCap hMnn
  -- The scalar `t`-part of the `n`-th term.
  have hTscalar : ∀ n, ContDiff ℝ (⊤ : ℕ∞)
      (fun t : ℝ => (φ : ℝ → ℝ) (t / ε n) * t ^ n / (n.factorial : ℝ)) := by
    intro n
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (φ : ℝ → ℝ) (t / ε n)) :=
      hφ_smooth.comp (contDiff_id.div_const (ε n))
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => t ^ n) := contDiff_id.pow n
    exact (h1.mul h2).div_const _
  have hTsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞)
      (fun p : ℝ × E => (φ : ℝ → ℝ) (p.1 / ε n) * p.1 ^ n / (n.factorial : ℝ)) :=
    fun n => (hTscalar n).comp_continuousLinearMap (g := ContinuousLinearMap.fst ℝ ℝ E)
  have hAsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × E => A n p.2) :=
    fun n => (hA n).comp_continuousLinearMap (g := ContinuousLinearMap.snd ℝ ℝ E)
  -- The terms of the series and the series itself.
  let gg : ℕ → ℝ × E → Z :=
    fun n p => ((φ : ℝ → ℝ) (p.1 / ε n) * p.1 ^ n / (n.factorial : ℝ)) • A n p.2
  have hgg_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (gg n) :=
    fun n => (hTsmooth n).smul (hAsmooth n)
  -- The key estimate: for `2 * (j+1) ≤ n` the `j`-th derivative of the `n`-th term is `≤ 2 ^ (-n)`.
  have hgbound : ∀ j n p, 2 * (j + 1) ≤ n →
      ‖iteratedFDeriv ℝ j (gg n) p‖ ≤ ((j + 1 : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ n := by
    intro j n p hn
    have hj : j ≤ n := by omega
    have hleib := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (𝕜' := ℝ) (E := ℝ × E) (F := Z)
      (f := fun p : ℝ × E => (φ : ℝ → ℝ) (p.1 / ε n) * p.1 ^ n / (n.factorial : ℝ))
      (g := fun p : ℝ × E => A n p.2) (hTsmooth n) (hAsmooth n) p (n := j)
      (WithTop.coe_le_coe.mpr le_top)
    calc ‖iteratedFDeriv ℝ j (gg n) p‖
        = ‖iteratedFDeriv ℝ j (fun q : ℝ × E =>
            (fun p : ℝ × E => (φ : ℝ → ℝ) (p.1 / ε n) * p.1 ^ n / (n.factorial : ℝ)) q
              • (fun p : ℝ × E => A n p.2) q) p‖ := rfl
      _ ≤ ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) *
            ‖iteratedFDeriv ℝ a
              (fun p : ℝ × E => (φ : ℝ → ℝ) (p.1 / ε n) * p.1 ^ n / (n.factorial : ℝ)) p‖ *
            ‖iteratedFDeriv ℝ (j - a) (fun p : ℝ × E => A n p.2) p‖ := hleib
      _ ≤ ∑ a ∈ Finset.range (j + 1), (j.choose a : ℝ) *
            ((ε n) ^ (n - a) * Cap a) * M n (j - a) := by
          refine Finset.sum_le_sum (fun a ha => ?_)
          have haj : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
          have han : a ≤ n := le_trans haj hj
          have hfst_le := borel_norm_iteratedFDeriv_fst_le
            (fun t : ℝ => (φ : ℝ → ℝ) (t / ε n) * t ^ n / (n.factorial : ℝ)) (hTscalar n) a p
          have hsnd_le := borel_norm_iteratedFDeriv_snd_le (A n) (hA n) (j - a) p
          have hsc := borel_bump_pow_le (φ : ℝ → ℝ) hφ_smooth Φ hΦ hΦnn hφ_zero_iter
            (a := a) (n := n) (ε n) (hεpos n) han p.1
          have hMn := hMb n (j - a) (j - a) le_rfl p.2
          have h1 : ‖iteratedFDeriv ℝ a
              (fun p : ℝ × E => (φ : ℝ → ℝ) (p.1 / ε n) * p.1 ^ n / (n.factorial : ℝ)) p‖ ≤
              (ε n) ^ (n - a) * Cap a := le_trans hfst_le hsc
          have h2 : ‖iteratedFDeriv ℝ (j - a) (fun p : ℝ × E => A n p.2) p‖ ≤ M n (j - a) :=
            le_trans hsnd_le hMn
          have hc0 : (0 : ℝ) ≤ (j.choose a : ℝ) := Nat.cast_nonneg _
          have h10 : 0 ≤ (ε n) ^ (n - a) * Cap a :=
            mul_nonneg (pow_nonneg (le_of_lt (hεpos n)) _) (hCap a)
          have h20 : 0 ≤ M n (j - a) := hMnn _ _
          calc (j.choose a : ℝ) * ‖iteratedFDeriv ℝ a
                (fun p : ℝ × E => (φ : ℝ → ℝ) (p.1 / ε n) * p.1 ^ n / (n.factorial : ℝ)) p‖ *
                ‖iteratedFDeriv ℝ (j - a) (fun p : ℝ × E => A n p.2) p‖
              = (j.choose a : ℝ) * (‖iteratedFDeriv ℝ a
                  (fun p : ℝ × E => (φ : ℝ → ℝ) (p.1 / ε n) * p.1 ^ n / (n.factorial : ℝ)) p‖ *
                  ‖iteratedFDeriv ℝ (j - a) (fun p : ℝ × E => A n p.2) p‖) := by ring
            _ ≤ (j.choose a : ℝ) * (((ε n) ^ (n - a) * Cap a) * M n (j - a)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) h10) hc0
            _ = (j.choose a : ℝ) * ((ε n) ^ (n - a) * Cap a) * M n (j - a) := by ring
      _ ≤ ((j + 1 : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ n := by
          have hle : ∀ a ∈ Finset.range (j + 1),
              (j.choose a : ℝ) * ((ε n) ^ (n - a) * Cap a) * M n (j - a) ≤
                ((1 : ℝ) / 2) ^ n := by
            intro a ha
            have haj : a ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
            have h := hεb n j a hn haj
            calc (j.choose a : ℝ) * ((ε n) ^ (n - a) * Cap a) * M n (j - a)
                = (j.choose a : ℝ) * Cap a * M n (j - a) * (ε n) ^ (n - a) := by ring
              _ ≤ ((1 : ℝ) / 2) ^ n / ((j : ℝ) + 1) := h
              _ ≤ ((1 : ℝ) / 2) ^ n := by
                  rw [div_le_iff₀ (by positivity)]
                  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]
          calc ∑ a ∈ Finset.range (j + 1),
                (j.choose a : ℝ) * ((ε n) ^ (n - a) * Cap a) * M n (j - a)
              ≤ ∑ _a ∈ Finset.range (j + 1), ((1 : ℝ) / 2) ^ n :=
                Finset.sum_le_sum hle
            _ = ((j + 1 : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ n := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- The function `F`.
  let F : ℝ × E → Z := fun p => ∑' n, gg n p
  have hF_smooth : ContDiff ℝ (⊤ : ℕ∞) F := by
    refine contDiff_tsum_of_eventually (𝕜 := ℝ) (E := ℝ × E) (F := Z) (α := ℕ)
      (f := gg) (v := fun k n => ((k + 1 : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ n) (N := ⊤)
      hgg_smooth ?_ ?_
    · intro k _
      exact (summable_geometric_of_norm_lt_one (by norm_num : ‖((1 : ℝ) / 2)‖ < 1)).mul_left _
    · intro k _
      rw [Nat.cofinite_eq_atTop]
      exact Filter.eventually_atTop.2 ⟨2 * (k + 1), fun n hn p => hgbound k n p hn⟩
  -- The `t`-jets of `F` along the hyperplane.
  have hjet : ∀ k : ℕ, ∀ y ∈ W, iteratedDeriv k (fun t : ℝ => F (t, y)) 0 = f k y := by
    intro k y hy
    have hslice_cd : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => gg n (t, y)) := by
      intro n
      exact (hTscalar n).smul_const (A n y)
    have hslice_bd : ∀ j n t, 2 * j + 2 ≤ n →
        ‖iteratedDeriv j (fun t : ℝ => gg n (t, y)) t‖ ≤ ((1 : ℝ) / 2) ^ n := by
      intro j n t hn
      have hj : j ≤ n := by omega
      have hca : ContDiffAt ℝ (j : ℕ∞ω)
          (fun t : ℝ => (φ : ℝ → ℝ) (t / ε n) * t ^ n / (n.factorial : ℝ)) t :=
        (hTscalar n).contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
      have hsm := iteratedDeriv_smul_const (𝕜 := ℝ) (f := fun t : ℝ =>
        (φ : ℝ → ℝ) (t / ε n) * t ^ n / (n.factorial : ℝ)) (x := t) (n := j) hca (A n y)
      have hsc := borel_bump_pow_le (φ : ℝ → ℝ) hφ_smooth Φ hΦ hΦnn hφ_zero_iter
        (a := j) (n := n) (ε n) (hεpos n) hj t
      have h1 : ‖iteratedDeriv j
          (fun t : ℝ => (φ : ℝ → ℝ) (t / ε n) * t ^ n / (n.factorial : ℝ)) t‖ ≤
          (ε n) ^ (n - j) * Cap j := by
        rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
        exact hsc
      have h2 : ‖A n y‖ ≤ M n 0 := by
        have h := hMb n 0 0 le_rfl y
        rwa [norm_iteratedFDeriv_zero] at h
      have h3 := hεb n j j (by omega) le_rfl
      have h4 : (j.choose j : ℝ) = 1 := by simp
      rw [h4, one_mul, Nat.sub_self] at h3
      have heq : ((ε n) ^ (n - j) * Cap j) * M n 0 = Cap j * M n 0 * (ε n) ^ (n - j) := by ring
      have hdiv : ((1 : ℝ) / 2) ^ n / (j + 1) ≤ ((1 : ℝ) / 2) ^ n := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) n]
      calc ‖iteratedDeriv j (fun t : ℝ => gg n (t, y)) t‖
          = ‖iteratedDeriv j (fun t : ℝ =>
              ((φ : ℝ → ℝ) (t / ε n) * t ^ n / (n.factorial : ℝ)) • (A n y)) t‖ := rfl
        _ = ‖(iteratedDeriv j
              (fun t : ℝ => (φ : ℝ → ℝ) (t / ε n) * t ^ n / (n.factorial : ℝ)) t) •
              (A n y)‖ := by rw [hsm]
        _ = ‖iteratedDeriv j
              (fun t : ℝ => (φ : ℝ → ℝ) (t / ε n) * t ^ n / (n.factorial : ℝ)) t‖ *
              ‖A n y‖ := norm_smul _ _
        _ ≤ ((ε n) ^ (n - j) * Cap j) * M n 0 := by
              have h0 : (0 : ℝ) ≤ (ε n) ^ (n - j) * Cap j :=
                mul_nonneg (pow_nonneg (le_of_lt (hεpos n)) _) (hCap j)
              exact mul_le_mul h1 h2 (norm_nonneg _) h0
        _ = Cap j * M n 0 * (ε n) ^ (n - j) := heq
        _ ≤ ((1 : ℝ) / 2) ^ n := le_trans h3 hdiv
    -- The slices are compactly supported, so their derivatives are bounded.
    have hslice_cs : ∀ n, HasCompactSupport (fun t : ℝ => gg n (t, y)) := by
      intro n
      refine HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall 0 (2 * ε n))
        (isCompact_closedBall 0 (2 * ε n)) ?_
      intro t ht
      rw [Function.mem_support] at ht
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero]
      by_contra hcon
      rw [not_le] at hcon
      refine ht ?_
      have hφ0 : (φ : ℝ → ℝ) (t / ε n) = 0 := by
        apply hφ_zero
        have h2 : (2 : ℝ) * ε n < |t| := hcon
        have hε := hεpos n
        rw [abs_div, abs_of_pos hε, le_div_iff₀ hε]
        linarith
      rw [show gg n (t, y) = ((φ : ℝ → ℝ) (t / ε n) * t ^ n / (n.factorial : ℝ)) •
        (A n y) from rfl, hφ0]
      simp
    have hw_sup : ∀ j n, BddAbove (Set.range fun t : ℝ =>
        ‖iteratedDeriv j (fun t : ℝ => gg n (t, y)) t‖) := by
      intro j n
      obtain ⟨C, _hC0, hC⟩ := (hslice_cs n).exists_bound_iteratedFDeriv (hslice_cd n) j
      refine ⟨C, ?_⟩
      rintro _ ⟨t, rfl⟩
      change ‖iteratedDeriv j (fun t : ℝ => gg n (t, y)) t‖ ≤ C
      rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      exact hC j le_rfl t
    let w : ℕ → ℕ → ℝ := fun j n =>
      sSup (Set.range fun t : ℝ => ‖iteratedDeriv j (fun t : ℝ => gg n (t, y)) t‖)
    have hw_bound : ∀ j n t, ‖iteratedDeriv j (fun t : ℝ => gg n (t, y)) t‖ ≤ w j n :=
      fun j n t => le_csSup (hw_sup j n) (Set.mem_range_self t)
    have hw_small : ∀ j n, 2 * j + 2 ≤ n → w j n ≤ ((1 : ℝ) / 2) ^ n := by
      intro j n hn
      refine csSup_le ⟨‖iteratedDeriv j (fun t : ℝ => gg n (t, y)) 0‖, Set.mem_range_self 0⟩ ?_
      rintro _ ⟨t, rfl⟩
      exact hslice_bd j n t hn
    have hw_sum : ∀ j, Summable (w j) := by
      intro j
      refine Summable.of_norm_bounded_eventually
        (summable_geometric_of_norm_lt_one (by norm_num : ‖((1 : ℝ) / 2)‖ < 1)) ?_
      rw [Nat.cofinite_eq_atTop]
      refine Filter.eventually_atTop.2 ⟨2 * j + 2, fun n hn => ?_⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (le_trans (norm_nonneg _) (hw_bound j n 0))]
      exact hw_small j n hn
    have hts := iteratedDeriv_tsum (fun n t => gg n (t, y)) w hslice_cd hw_sum hw_bound k
    have h1 : iteratedDeriv k (fun t : ℝ => F (t, y)) 0 =
        ∑' n, iteratedDeriv k (fun t : ℝ => gg n (t, y)) 0 := by
      rw [show (fun t : ℝ => F (t, y)) = (fun t : ℝ => ∑' n, gg n (t, y)) from rfl, hts]
    rw [h1]
    have hterm : ∀ n, iteratedDeriv k (fun t : ℝ => gg n (t, y)) 0 =
        (if k = n then A n y else 0) := by
      intro n
      exact iteratedDeriv_flat_mul_pow_jet (φ : ℝ → ℝ) hφ_one (ε n) (hεpos n) (A n y) k n
    rw [tsum_congr hterm]
    rw [tsum_eq_single k (fun b hb => by simp [Ne.symm hb])]
    rw [if_pos rfl]
    show (χ : E → ℝ) y • f k y = f k y
    rw [hW_one y hy, one_smul]
  exact ⟨1, one_pos, W, hW_open, hW_mem, hW_sub, F, hF_smooth.contDiffOn, hjet⟩

end Work.Diff.EXT
