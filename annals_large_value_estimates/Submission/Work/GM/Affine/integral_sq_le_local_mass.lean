import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.ceil_C0T_bounds

/-!
# `Work.GM.Affine.integral_sq_le_local_mass` (GM §9: the total mass is controlled by the
local masses)

For `f : ℝ → ℝ` continuous, non-negative and supported in `[1/C₀, C₀]` with `C₀ ≥ 1`, and for
`T ≥ 1`, the square of the total mass `V = ∫ f` is dominated by the *local* masses of `f` at
scale `1/T`:

  `(∫ f)² ≤ 4 C₀ T · ∫ u, f u · (∫_{u - 1/T}^{u + 1/T} f)`.

## The argument

Put `W = 1/T`, `N = ⌈C₀ T⌉` and `M u = ∫_{u-W}^{u+W} f`.  Since `f` is supported in
`[1/C₀, 1/C₀ + N·W]` (because `C₀ ≤ 1/C₀ + N/T`), split that interval into the `N` chunks
`J j = (a + j W, a + (j+1) W]`, `j < N`, and let `μ j = ∫_{J j} f ≥ 0` be their masses.  Then

* `∑_j μ j = ∫ f` (the chunks tile the support: adjacent-interval summation), and
* `∑_j (μ j)² ≤ ∫ u, f u · M u`, because `M u ≥ μ j` for `u ∈ J j` (`J j ⊆ [u-W, u+W]`),
  so `∫_{J j} f · M ≥ μ j · μ j`, and the chunks are disjoint.

Cauchy–Schwarz gives `(∑_j μ j)² ≤ N · ∑_j (μ j)²`, hence `(∫ f)² ≤ N · ∫ f·M`, and finally
`N ≤ 2 C₀ T`, so `(∫ f)² ≤ 4 C₀ T · ∫ f·M`.

The two measure-theoretic inputs are that `u ↦ M u` is continuous (it is
`P(u + W) - P(u - W)` for a primitive `P` of the integrable `f`) and that `f · M` is integrable
(it is dominated by `(∫ f) · f`).
-/

open MeasureTheory
open scoped Interval

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.GM.Affine

noncomputable section

/-! ### The local mass function -/

/-- **Continuity of the local mass.**  For integrable `f`, the moving-interval integral
`u ↦ ∫ v in Set.Icc (u - W) (u + W), f v` is continuous: for `W ≥ 0` it is
`P (u + W) - P (u - W)` for the primitive `P x = ∫_0^x f`, and for `W < 0` the interval is
empty and the function vanishes identically. -/
lemma gm_continuous_localmass {W : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (hfi : Integrable f) :
    Continuous fun u : ℝ => ∫ v in Set.Icc (u - W) (u + W), f v := by
  by_cases hW : 0 ≤ W
  · have hP : Continuous fun b : ℝ => ∫ x in (0:ℝ)..b, f x := hfi.continuous_primitive 0
    have hkey : ∀ u : ℝ, (∫ v in Set.Icc (u - W) (u + W), f v)
        = (∫ x in (0:ℝ)..(u + W), f x) - (∫ x in (0:ℝ)..(u - W), f x) := by
      intro u
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (show u - W ≤ u + W by linarith)]
      exact (intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _)
        (hf.intervalIntegrable _ _)).symm
    simp only [hkey]
    exact (hP.comp (continuous_id.add continuous_const)).sub
      (hP.comp (continuous_id.sub continuous_const))
  · have hzero : (fun u : ℝ => ∫ v in Set.Icc (u - W) (u + W), f v) = fun _ => 0 := by
      funext u
      have hemp : Set.Icc (u - W) (u + W) = ∅ := by
        rw [Set.Icc_eq_empty_iff]; linarith
      rw [hemp, setIntegral_empty]
    rw [hzero]
    exact continuous_const

/-- **Integrability of the local-mass weighted mass.**  For continuous non-negative integrable
`f`, the function `u ↦ f u * ∫ v in Set.Icc (u - W) (u + W), f v` is integrable: it is
measurable (product of continuous functions) and dominated by `(∫ f) · f`. -/
lemma gm_integrable_mul_localmass {W : ℝ} {f : ℝ → ℝ} (hf : Continuous f) (hfi : Integrable f)
    (hnn : ∀ u, 0 ≤ f u) :
    Integrable fun u : ℝ => f u * (∫ v in Set.Icc (u - W) (u + W), f v) := by
  set M : ℝ → ℝ := fun u => ∫ v in Set.Icc (u - W) (u + W), f v with hM
  have hMcont : Continuous M := gm_continuous_localmass (W := W) hf hfi
  have hMnn : ∀ u, 0 ≤ M u := fun u => setIntegral_nonneg measurableSet_Icc (fun v _ => hnn v)
  have hMle : ∀ u, M u ≤ ∫ u, f u := fun u =>
    setIntegral_le_integral hfi (ae_of_all _ fun x => hnn x)
  have hmeas : AEStronglyMeasurable (fun u => f u * M u) volume :=
    (hf.mul hMcont).aestronglyMeasurable
  refine Integrable.mono' (hfi.const_mul (∫ u, f u)) hmeas ?_
  refine ae_of_all _ fun u => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnn u) (hMnn u))]
  calc f u * M u ≤ f u * (∫ u, f u) := mul_le_mul_of_nonneg_left (hMle u) (hnn u)
    _ = (∫ u, f u) * f u := by ring

/-! ### The chunking inequality -/

/-- **The chunking (interval-partition) inequality.**  If `f ≥ 0` is continuous with support in
`[a, a + N·W]` (`W > 0`, `N ≥ 1`), then `(∫ f)² ≤ N · ∫ u, f u · ∫_{u-W}^{u+W} f`; the right
side is the `N`-fold local-mass double integral and the constant `N` is the number of chunks of
length `W` needed to cover the support. -/
lemma sq_integral_le_chunk_local {a W : ℝ} {N : ℕ} {f : ℝ → ℝ}
    (hf : Continuous f) (hnn : ∀ u, 0 ≤ f u) (hW : 0 < W) (hN : 1 ≤ N)
    (hsupp : ∀ u, f u ≠ 0 → u ∈ Set.Icc a (a + N * W))
    (hMint : Integrable fun u : ℝ => f u * (∫ v in Set.Icc (u - W) (u + W), f v)) :
    (∫ u, f u) ^ 2 ≤ (N : ℝ) * ∫ u, f u * (∫ v in Set.Icc (u - W) (u + W), f v) := by
  have hcs : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (fun x hx => hsupp x hx)
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hcs
  set M : ℝ → ℝ := fun u => ∫ v in Set.Icc (u - W) (u + W), f v with hM
  have hMnn : ∀ u, 0 ≤ M u := fun u => setIntegral_nonneg measurableSet_Icc (fun v _ => hnn v)
  have hfMnn : ∀ u, 0 ≤ f u * M u := fun u => mul_nonneg (hnn u) (hMnn u)
  set seq : ℕ → ℝ := fun j => a + (j : ℝ) * W with hseq
  have hseq_succ : ∀ j : ℕ, seq (j + 1) = seq j + W := by
    intro j; simp only [hseq]; push_cast; ring
  have hseq_mono : ∀ j : ℕ, seq j ≤ seq (j+1) := by
    intro j; rw [hseq_succ]; linarith [hW]
  have hseq0 : seq 0 = a := by simp [hseq]
  have hseqN : seq N = a + (N : ℝ) * W := by simp [hseq]
  set mu : ℕ → ℝ := fun j => ∫ v in Set.Ioc (seq j) (seq (j+1)), f v with hmu
  have hbound : a ≤ a + (N:ℝ) * W := by
    have h1 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
    nlinarith [hW, h1]
  -- the chunks tile the support, so the total mass is the sum of the chunk masses
  have hVsum : (∫ u, f u) = ∑ j ∈ Finset.range N, mu j := by
    have h1 : ∫ u, f u = ∫ u in Set.Icc a (a + (N:ℝ)*W), f u :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        by_contra hcon; exact hx (hsupp x hcon))).symm
    rw [h1, MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hbound]
    rw [← hseqN, ← hseq0]
    rw [← intervalIntegral.sum_integral_adjacent_intervals (a := seq) (n := N)
      (f := f) (μ := volume) (fun k _ => hf.intervalIntegrable _ _)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hmu]
    exact intervalIntegral.integral_of_le (hseq_mono j)
  -- each chunk contributes at least the square of its mass
  have hchunk_j : ∀ j ∈ Finset.range N,
      (mu j)^2 ≤ ∫ v in Set.Ioc (seq j) (seq (j+1)), f v * M v := by
    intro j _
    have hkey : ∀ v ∈ Set.Ioc (seq j) (seq (j+1)), mu j ≤ M v := by
      intro v hv
      have hsub : Set.Ioc (seq j) (seq (j+1)) ⊆ Set.Icc (v - W) (v + W) := by
        intro x hx
        rw [Set.mem_Ioc] at hv hx
        rw [Set.mem_Icc]
        have hs := hseq_succ j
        exact ⟨by linarith [hv.1, hv.2, hx.1, hs], by linarith [hv.1, hv.2, hx.2, hs]⟩
      have hle := setIntegral_mono_set (μ := volume) (f := f)
        (s := Set.Ioc (seq j) (seq (j+1))) (t := Set.Icc (v - W) (v + W))
        hfi.integrableOn (ae_of_all _ fun x => hnn x) hsub.eventuallyLE
      simpa [hmu, hM] using hle
    have heq : ∫ v in Set.Ioc (seq j) (seq (j+1)), f v * mu j = (mu j)^2 := by
      rw [hmu, integral_mul_const]
      ring
    calc (mu j)^2 = ∫ v in Set.Ioc (seq j) (seq (j+1)), f v * mu j := heq.symm
      _ ≤ ∫ v in Set.Ioc (seq j) (seq (j+1)), f v * M v := by
        refine setIntegral_mono_on (μ := volume) (f := fun v => f v * mu j)
          (g := fun v => f v * M v) (s := Set.Ioc (seq j) (seq (j+1)))
          (hfi.mul_const (mu j)).integrableOn hMint.integrableOn measurableSet_Ioc
          (fun v hv => ?_)
        exact mul_le_mul_of_nonneg_left (hkey v hv) (hnn v)
  have hsum_j : ∑ j ∈ Finset.range N, (mu j)^2 ≤ ∫ u, f u * M u := by
    have hmono0N : seq 0 ≤ seq N := by
      rw [hseq0, hseqN]; exact hbound
    have hsum_eq : ∑ j ∈ Finset.range N, ∫ v in Set.Ioc (seq j) (seq (j+1)), f v * M v
        = ∫ u in Set.Ioc a (a + (N:ℝ)*W), f u * M u := by
      rw [← hseqN, ← hseq0]
      rw [← intervalIntegral.integral_of_le hmono0N]
      rw [← intervalIntegral.sum_integral_adjacent_intervals (a := seq) (n := N)
        (f := fun u => f u * M u) (μ := volume)
        (fun k _ => hMint.intervalIntegrable (a := seq k) (b := seq (k+1)))]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      exact (intervalIntegral.integral_of_le (hseq_mono j)).symm
    calc ∑ j ∈ Finset.range N, (mu j)^2
        ≤ ∑ j ∈ Finset.range N, ∫ v in Set.Ioc (seq j) (seq (j+1)), f v * M v :=
          Finset.sum_le_sum hchunk_j
      _ = ∫ u in Set.Ioc a (a + (N:ℝ)*W), f u * M u := hsum_eq
      _ ≤ ∫ u, f u * M u := setIntegral_le_integral hMint (ae_of_all _ hfMnn)
  have hjensen : (∑ j ∈ Finset.range N, mu j)^2 ≤ (N:ℝ) * ∑ j ∈ Finset.range N, (mu j)^2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range N) (f := mu)
    simpa using h
  calc (∫ u, f u)^2 ≤ (∑ j ∈ Finset.range N, mu j)^2 := by rw [hVsum]
    _ ≤ (N:ℝ) * ∑ j ∈ Finset.range N, (mu j)^2 := hjensen
    _ ≤ (N:ℝ) * (∫ u, f u * M u) := mul_le_mul_of_nonneg_left hsum_j (Nat.cast_nonneg N)
    _ = (N:ℝ) * (∫ u, f u * (∫ v in Set.Icc (u - W) (u + W), f v)) := by rw [hM]

/-! ### The main theorem -/

theorem integral_sq_le_local_mass {C₀ T : ℝ} (hC₀ : 1 ≤ C₀) (hT : 1 ≤ T) {f : ℝ → ℝ}
    (hf : Continuous f) (hnn : ∀ u, 0 ≤ f u) (hs : Work.GM.Affine.SuppHyp C₀ f) :
    (∫ u, f u) ^ 2 ≤ 4 * C₀ * T * ∫ u, f u * (∫ v in Set.Icc (u - 1 / T) (u + 1 / T), f v) := by
  have hTpos : 0 < T := by linarith
  have hW : 0 < 1 / T := by positivity
  obtain ⟨hN1, hN2, hN3⟩ := ceil_C0T_bounds hC₀ hT
  have hcs : HasCompactSupport f :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (fun x hx => hs x hx)
  have hfint : Integrable f := hf.integrable_of_hasCompactSupport hcs
  have hint : Integrable fun u : ℝ => f u * (∫ v in Set.Icc (u - 1 / T) (u + 1 / T), f v) :=
    gm_integrable_mul_localmass (W := 1 / T) hf hfint hnn
  have hsupp : ∀ u, f u ≠ 0 →
      u ∈ Set.Icc (1 / C₀) (1 / C₀ + (Nat.ceil (C₀ * T) : ℝ) * (1 / T)) := by
    intro u hu
    obtain ⟨h1, h2⟩ := hs u hu
    exact ⟨h1, le_trans h2 hN3⟩
  have hch := sq_integral_le_chunk_local (a := 1 / C₀) (W := 1 / T) (N := Nat.ceil (C₀ * T))
    hf hnn hW hN1 hsupp hint
  have hA0 : 0 ≤ ∫ u, f u * (∫ v in Set.Icc (u - 1 / T) (u + 1 / T), f v) :=
    integral_nonneg (fun u => mul_nonneg (hnn u)
      (setIntegral_nonneg measurableSet_Icc (fun v _ => hnn v)))
  have h23 : (Nat.ceil (C₀ * T) : ℝ)
        * (∫ u, f u * (∫ v in Set.Icc (u - 1 / T) (u + 1 / T), f v))
      ≤ (2 * C₀ * T) * (∫ u, f u * (∫ v in Set.Icc (u - 1 / T) (u + 1 / T), f v)) :=
    mul_le_mul_of_nonneg_right hN2 hA0
  have h34 : (2 * C₀ * T) * (∫ u, f u * (∫ v in Set.Icc (u - 1 / T) (u + 1 / T), f v))
      ≤ (4 * C₀ * T) * (∫ u, f u * (∫ v in Set.Icc (u - 1 / T) (u + 1 / T), f v)) := by
    apply mul_le_mul_of_nonneg_right _ hA0
    nlinarith [hTpos, hC₀]
  linarith [hch, h23, h34]

end

end Work.GM.Affine
