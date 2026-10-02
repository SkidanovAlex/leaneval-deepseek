/-
# `Work.ZeroFreeTables.OffAxis.RectP3EngineH`

HB Lemma 9.1 / (9.13) at height `H` with room `W` (HB's `P₃` method).

This file proves `RectP3EngineH` (the statement of `OffAxis/HBLemma9_1_engine_H.lean`, and the
`RectP3EngineStmt` of `OffAxis/RectC_Z4.lean`): for positive `a, K, ε` and `1 ≤ H`, `3H + 1 ≤ W`
there is `q₀` such that for `q ≥ q₀`, two distinct zeros `ρ₁ ≠ ρ₀` of a non-principal `χ₁ (mod q)`
with `|Im ρ₁| ≤ H`, `|Im ρ₀| ≤ H`, `λ₁` minimal over all non-principal zeros of height `≤ W`, the
real-character exclusions of HB, and the side condition `cond913 (λ₁) (λ₀) a K`, one has
`ineq913 (λ₁) (λ₀) a K ε`.

The structure is a transcription of `Work.ZeroFreeTables.HBLemma9_1_proof` (the case `H = 1`,
`W = 10` with `IsZ` in place of the height hypotheses) with:

* every height literal `3` replaced by the parameter `R = 3H` (all shifts `γ₁, γ₀, γ₁ ± γ₀,
  2γ₁, 2γ₁ ± γ₀` are bounded by `3H`), and every minimality window `10` by `3H + 1 ≤ W`;
* the `ζ`-inputs taken at the height `Θ = 3H + 2` (the norm bound `‖σ + it‖ ≤ Θ` for `|t| ≤ 3H`);
* HB's case `χ₁² = χ₀` (the real character), which is *not* in `HBLemma9_1_proof` (its only
  `sorry`) but is treated here in full, including the degenerate sub-case `ρ₀` real (HB's
  "if `γ₀ = 0` we obtain only the weaker bound"): the conjugate zeros `ρ̄₁, ρ̄₀` are kept, the
  drop-out quantity is HB's `A' + C + D` (non-negative by `P9.rescale_variants` and
  `P3.CaseC_D`), and for `ρ₀` real the `β`-terms cancel (`caseCg0_bridge`).
-/
import Mathlib
import Submission.Work.ZeroFreeTables.Engine
import Submission.Work.ZeroFreeTables.OffAxis.WideDefs
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroFreeTables.HB94.Lam0GeEngine
import Submission.Work.ZeroFreeTables.OffAxis.zetaLogDerivPoleSplitH
import Submission.Work.ZeroFreeTables.OffAxis.nearP3sum_ge_kept_R
import Submission.Work.ZeroFreeTables.OffAxis.pointEngine_prim_gen
import Submission.Work.ZeroFreeTables.OffAxis.invNearSum_eq_tsum_gen
import Submission.Work.LinnikAreas.FarRepel.zeroSumInvSqBound
import Submission.Work.A7.zeroMult_conj_sq_one
import Submission.Work.ZeroFreeTables.Table4.zeroMult_changeLevel
import Submission.Work.ZeroFreeTables.P3.CaseC_D
import Submission.Work.ZeroFreeTables.P3.SideConditions
import Submission.Work.ZeroFreeTables.P9.rescale_variants
import Submission.Work.ZeroFreeTables.P9.HbCombinationL_nonneg
import Submission.Work.ZeroFreeTables.P9.InvNearSum_anti
import Submission.Work.ZeroFreeTables.P9.SigmaP3L_changeLevel_diff
import Submission.Work.ZeroFreeTables.P9.primeFactors_logPow_div_le
import Submission.Work.ZeroFreeTables.P9.parity_bound_re
import Submission.Work.ZeroFreeTables.P9.absorption_eventual

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 8000000

namespace Work.ZeroFreeTables.OffAxis

namespace P3H

/-! ## The `ζ`-inputs at height `Θ` -/

/-- **`ζ` has no zeros in a fixed strip next to the real axis with `|Im| ≤ Θ`** (the
height-`Θ` version of `Commons.NumberTheory.Zeta.zeta_zeroFree_near_axis`, itself for `|Im| ≤ 4`).
The zeros of `ζ` in the compact rectangle `1/2 ≤ re s ≤ 2`, `|im s| ≤ Θ` are finite and lie
strictly to the left of `re s = 1`; they are separated from that line by a positive distance `d`,
and the strip `1 - d/2 ≤ re s`, `re s ≤ 2`, `|im s| ≤ Θ` is zero-free. -/
theorem zetaZeroFreeStripHt (Θ : ℝ) (hΘ : 0 ≤ Θ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (t σ : ℝ), |t| ≤ Θ → 1 - ε₀ ≤ σ → σ ≤ 2 →
        riemannZeta (((σ : ℂ) + Complex.I * (t : ℂ)) : ℂ) ≠ 0 := by
  let S₀ : Set ℂ := (fun p : ℝ × ℝ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)) ''
    (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (-Θ) Θ)
  have hS₀compact : IsCompact S₀ := by
    dsimp [S₀]
    exact (IsCompact.prod isCompact_Icc isCompact_Icc).image
      (by fun_prop : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + Complex.I * (p.2 : ℂ)))
  let Z : Set ℂ := S₀ ∩ riemannZetaZeros
  have hZfin : Z.Finite := by
    dsimp [Z]
    exact hS₀compact.inter_riemannZetaZeros_finite
  have hZm : ∀ z : ℂ, z ∈ Z →
      (1 / 2 : ℝ) ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ Θ ∧ riemannZeta z = 0 := by
    intro z hz
    rcases hz.1 with ⟨p, hp, hpeq⟩
    have hzre : z.re = p.1 := by rw [← hpeq]; simp
    have hzim : z.im = p.2 := by rw [← hpeq]; simp
    have hz0 : riemannZeta z = 0 := by simpa [riemannZetaZeros] using hz.2
    exact ⟨by linarith only [hp.1.1, hzre], by linarith only [hp.1.2, hzre],
      abs_le.mpr (by simpa [hzim] using hp.2), hz0⟩
  have hZ_re_lt_one : ∀ z : ℂ, z ∈ Z → z.re < 1 := by
    intro z hz
    have hz0 : riemannZeta z = 0 := (hZm z hz).2.2.2
    exact lt_of_not_ge (fun hge : (1 : ℝ) ≤ z.re =>
      riemannZeta_ne_zero_of_one_le_re (s := z) hge hz0)
  by_cases hZempty : Z = ∅
  · refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
    intro t σ ht hσlo hσhi hz0
    let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
    have hsZ : s ∈ Z := by
      constructor
      · dsimp [S₀]
        refine ⟨(σ, t), ⟨⟨by linarith only [hσlo], hσhi⟩, abs_le.mp ht⟩, rfl⟩
      · simpa [Z, riemannZetaZeros, s] using hz0
    rw [hZempty] at hsZ
    exact hsZ
  · have hZn : Z.Nonempty := Set.nonempty_iff_ne_empty.mpr hZempty
    let fz : Finset ℂ := hZfin.toFinset
    have hfz_mem_iff : ∀ z : ℂ, z ∈ fz ↔ z ∈ Z := fun z => hZfin.mem_toFinset
    have hg_ne : (fz.image (fun z : ℂ => 1 - z.re)).Nonempty := by
      rcases hZn with ⟨z, hz⟩
      exact ⟨1 - z.re, Finset.mem_image.mpr ⟨z, (hfz_mem_iff z).2 hz, rfl⟩⟩
    let d : ℝ := (fz.image (fun z : ℂ => 1 - z.re)).min' hg_ne
    have hd_mem : d ∈ fz.image (fun z : ℂ => 1 - z.re) := by
      dsimp [d]
      exact Finset.min'_mem _ hg_ne
    rcases Finset.mem_image.mp hd_mem with ⟨z₀, hz₀f, hz₀eq⟩
    have hz₀Z : z₀ ∈ Z := (hfz_mem_iff z₀).1 hz₀f
    have hd0 : 0 < d := by
      have hz₀re : z₀.re < 1 := hZ_re_lt_one z₀ hz₀Z
      have hd : d = 1 - z₀.re := by simpa [d] using hz₀eq.symm
      linarith only [hd, hz₀re]
    have hd_le_half : d ≤ 1 / 2 := by
      have hz₀ge : (1 / 2 : ℝ) ≤ z₀.re := (hZm z₀ hz₀Z).1
      have hd : d = 1 - z₀.re := by simpa [d] using hz₀eq.symm
      linarith only [hd, hz₀ge]
    have hd_le : ∀ z : ℂ, z ∈ Z → d ≤ 1 - z.re := by
      intro z hz
      dsimp [d]
      exact Finset.min'_le (fz.image (fun z : ℂ => 1 - z.re))
        (1 - z.re) (Finset.mem_image.mpr ⟨z, (hfz_mem_iff z).2 hz, rfl⟩)
    refine ⟨d / 2, by positivity, ?_⟩
    intro t σ ht hσlo hσhi hz0
    let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
    have hsZ : s ∈ Z := by
      constructor
      · dsimp [S₀]
        refine ⟨(σ, t), ⟨⟨by linarith only [hσlo, hd_le_half], hσhi⟩, abs_le.mp ht⟩, rfl⟩
      · simpa [Z, riemannZetaZeros, s] using hz0
    have hre : s.re = σ := by simp [s]
    have h1 : d ≤ 1 - σ := by
      have hd' := hd_le s hsZ
      rwa [hre] at hd'
    have h2 : 1 - σ ≤ d / 2 := by linarith only [hσlo]
    linarith only [h1, h2, hd0]

/-- **Inverse-square `ζ` zero sum at height `Θ`.** From the height-free bound
`Work.LinnikAreas.FarRepel.zetaHalfKernelBound` (which holds for every `w`), the sum
`∑_u ord(u)/(1+‖s-u‖²)` is bounded by a constant depending only on `Θ` when `‖s‖ ≤ Θ`. -/
theorem zetaInvSqSumBoundHt (Θ : ℝ) (hΘ : 0 ≤ Θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, ‖s‖ ≤ Θ →
      (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) ≤ C := by
  obtain ⟨C, hCpos, hC⟩ := Work.LinnikAreas.FarRepel.zetaHalfKernelBound
  refine ⟨C * (Real.log (2 + Θ) + 2) + 1, ?_, ?_⟩
  · have h1 : 0 ≤ Real.log (2 + Θ) := Real.log_nonneg (by linarith only [hΘ])
    nlinarith [hCpos, h1]
  · intro s hs
    have h := (hC s).2
    have hlog : Real.log (2 + ‖s‖) ≤ Real.log (2 + Θ) :=
      Real.log_le_log (by positivity) (by linarith only [hs])
    have h2 : C * (Real.log (2 + ‖s‖) + 2) ≤ C * (Real.log (2 + Θ) + 2) :=
      mul_le_mul_of_nonneg_left (by linarith only [hlog]) hCpos.le
    linarith only [h, h2]

/-! ## The point bound inputs at height `R` -/

/-- `‖σ + it‖ ≤ R + 2` for `σ = 1 + a/L`, `a ≤ L`, `L > 0` and `|t| ≤ R`. -/
theorem norm_sPt_le_R {a L t R : ℝ} (ha : 0 < a) (haL : a ≤ L) (hL : 0 < L)
    (hR : |t| ≤ R) :
    ‖Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L t‖ ≤ R + 2 := by
  have h1 : (Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L t).re = 1 + a / L := by
    simp [Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt]
  have h2 : (Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L t).im = t := by
    simp [Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt]
  have hRnn : 0 ≤ R := le_trans (abs_nonneg t) hR
  have h3 : 1 + a / L ≤ 2 := by
    have h : a / L ≤ 1 := (div_le_iff₀ hL).mpr (by linarith only [haL])
    linarith only [h]
  have h4 : 0 ≤ 1 + a / L := by
    have h : 0 ≤ a / L := div_nonneg ha.le hL.le
    linarith only [h]
  have h5 : (1 + a / L) ^ 2 + t ^ 2 ≤ (R + 2) ^ 2 := by
    have h6 := abs_le.mp hR
    nlinarith only [h3, h4, h6.1, h6.2, hRnn]
  calc ‖Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L t‖
      = Real.sqrt ((Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L t).re ^ 2
          + (Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L t).im ^ 2) := by
        rw [Complex.norm_def, Complex.normSq_apply]; ring_nf
    _ = Real.sqrt ((1 + a / L) ^ 2 + t ^ 2) := by rw [h1, h2]
    _ ≤ Real.sqrt ((R + 2) ^ 2) := Real.sqrt_le_sqrt h5
    _ = R + 2 := Real.sqrt_sq (by linarith only [hRnn])

/-- **The `k = 1` input** of the engine at one test point, from HB Lemma 3.1
(`lemma3_1_free_gen`): on shrinking `δ ≤ δ₀` one has
`(-logDeriv L(·,χ)).re + nearInvSum N χ s δ ≤ (1/6 + ε₁)L` for points with `|Im s| ≤ 10 L`. -/
theorem k1InputH {L₀ δ₀ δ ε₁ a L : ℝ}
    (h31 : ∀ {M : ℕ} [NeZero M], 3 ≤ M → ∀ (χ : DirichletCharacter ℂ M), χ ≠ 1 →
      χ.IsPrimitive →
      ∀ {L : ℝ}, L₀ ≤ L → Real.log (M : ℝ) ≤ L → ∀ s : ℂ,
        1 + 1 / (L * Real.log L) ≤ s.re → s.re ≤ 1 + Real.log L / L → |s.im| ≤ 10 * L →
        (-logDeriv (DirichletCharacter.LFunction χ) s).re
          + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
              (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ₀ then ((1 / (s - u)).re) else 0))
          ≤ (1 / 6 + ε₁) * L)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    (hN3 : 3 ≤ N) (hL0 : L₀ ≤ L) (hlogN : Real.log (N : ℝ) ≤ L)
    (hδδ₀ : δ ≤ δ₀) (hδ₀1 : δ₀ ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (ha : 0 < a) (hL1 : 1 ≤ L) (h1 : 1 ≤ a * Real.log L) (h2 : a ≤ Real.log L)
    {s : ℂ} (hsre : s.re = 1 + a / L) (hs3 : |s.im| ≤ 10 * L) :
    (-logDeriv (DirichletCharacter.LFunction χ) s).re
      + Work.ZeroFreeTables.P9.nearInvSum N χ s δ ≤ (1 / 6 + ε₁) * L := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL1
  have hlogLpos : 0 < Real.log L := by nlinarith only [h1, ha]
  have hs1 : 1 + 1 / (L * Real.log L) ≤ s.re := by
    rw [hsre]
    have hkey : 1 / (L * Real.log L) ≤ a / L := by
      field_simp
      nlinarith only [h1, hLpos]
    linarith only [hkey]
  have hs2 : s.re ≤ 1 + Real.log L / L := by
    rw [hsre]
    have h3 : a / L ≤ Real.log L / L := div_le_div_of_nonneg_right h2 hLpos.le
    linarith only [h3]
  have h31' := h31 hN3 χ hχ hprim hL0 hlogN s hs1 hs2 hs3
  have hre1 : (1 : ℝ) ≤ s.re := by
    rw [hsre]
    have h4 : 0 ≤ a / L := div_nonneg ha.le hLpos.le
    linarith only [h4]
  have hmono : Work.ZeroFreeTables.InvNearSum N χ s δ ≤
      Work.ZeroFreeTables.InvNearSum N χ s δ₀ :=
    Work.ZeroFreeTables.P9.InvNearSum_anti χ hχ hprim hre1 hδδ₀ hδ₀1
  have heq : Work.ZeroFreeTables.InvNearSum N χ s δ = Work.ZeroFreeTables.P9.nearInvSum N χ s δ :=
    Work.ZeroFreeTables.OffAxis.invNearSum_eq_tsum_gen χ hχ hprim hδ0 hδ1
  rw [heq] at hmono
  simp only [Work.ZeroFreeTables.InvNearSum, Work.ZeroFreeTables.pdiv] at hmono
  linarith only [h31', hmono]

/-- **The point bound at a primitive non-principal character, at height `R`.**
`pointEngine_prim_gen` + the dropping rule `nearP3sum_ge_kept_R`. -/
theorem pointBoundPrimH {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) {L a lam₁ δ R c Ct Cj : ℝ}
    (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hδ : 0 < δ) (hδ1 : δ < 1) (hLt : 1 < L)
    (haδL : 2 * a ≤ δ * L) {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ R)
    (hlog : (-logDeriv (DirichletCharacter.LFunction χ) s).re
      + Work.ZeroFreeTables.P9.nearInvSum N χ s δ ≤ c * L)
    (par : ℕ) (hpar0 : χ.Even → par = 0) (hpar1 : χ.Odd → par = 1)
    (hS2 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re| ≤ Ct)
    (hS3 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re| ≤ Ct)
    (hJ : Work.ZeroFreeTables.P9.invSqSum N χ s ≤ Cj)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult χ u ≠ 0 → |u.im| ≤ R + 1 →
      lam₁ ≤ (1 - u.re) * L)
    (T : Finset ℂ) (hT : ∀ u ∈ T, Work.LinnikContract.zeroMult χ u ≠ 0)
    (hTim : ∀ u ∈ T, |u.im| ≤ R + 1) :
    Work.ZeroFreeTables.SigmaP3L N L χ s a lam₁
      ≤ -(∑ u ∈ T, (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re)
        + (a + lam₁) * c + ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct)
        + (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct)
        + (T.card : ℝ) * (8 * (a + lam₁) / (δ * L)) := by
  have h1 := Work.ZeroFreeTables.OffAxis.pointEngine_prim_gen χ hχ hprim ha hlam₁ hδ hδ1 hLt
    haδL hsre hlog par hpar0 hpar1 hS2 hS3
  have h2 := Work.ZeroFreeTables.OffAxis.nearP3sum_ge_kept_R χ hχ (by linarith only [hLt]) ha
    hlam₁ hδ hδ1 haδL hsre hsim hmin T hT hTim
  have hw : (0 : ℝ) ≤ 1 + 4 / δ ^ 2 := by positivity
  have hc1 : ((a + lam₁) ^ 2 / L ^ 2)
        * ((1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct)
      ≤ ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    linarith only [mul_le_mul_of_nonneg_left hJ hw]
  have hc2 : (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3)
        * ((2 / δ) * (1 + 4 / δ ^ 2) * Work.ZeroFreeTables.P9.invSqSum N χ s + Ct)
      ≤ (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hw2 : (0 : ℝ) ≤ (2 / δ) * (1 + 4 / δ ^ 2) := by positivity
    linarith only [mul_le_mul_of_nonneg_left hJ hw2]
  linarith only [h1, h2, hc1, hc2]

/-- **The point bound at an imprimitive character, at height `R`**: reduce `Σ(s,ψ)` at the
ambient level `q` to the primitive level `N` (`SigmaP3L_changeLevel_diff`), apply
`pointBoundPrimH` there and add the correction back. -/
theorem pointBoundQH {q N : ℕ} [NeZero q] [NeZero N] (hNq : N ∣ q)
    (φ : DirichletCharacter ℂ N) (hφ : φ ≠ 1) (hprim : φ.IsPrimitive)
    {a lam₁ δ R L c Ct Cj Cc : ℝ}
    (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hδ : 0 < δ) (hδ1 : δ < 1) (hLt : 1 < L)
    (haδL : 2 * a ≤ δ * L) {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ R)
    (hlog : (-logDeriv (DirichletCharacter.LFunction φ) s).re
        + Work.ZeroFreeTables.P9.nearInvSum N φ s δ ≤ c * L)
    (par : ℕ) (hpar0 : φ.Even → par = 0) (hpar1 : φ.Odd → par = 1)
    (hS2 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re| ≤ Ct)
    (hS3 : |∑' n : ℕ, (((1 / (s + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re| ≤ Ct)
    (hJ : Work.ZeroFreeTables.P9.invSqSum N φ s ≤ Cj)
    (hmin : ∀ u : ℂ, Work.LinnikContract.zeroMult φ u ≠ 0 → |u.im| ≤ R + 1 →
      lam₁ ≤ (1 - u.re) * L)
    (T : Finset ℂ) (hT : ∀ u ∈ T, Work.LinnikContract.zeroMult φ u ≠ 0)
    (hTim : ∀ u ∈ T, |u.im| ≤ R + 1)
    (hcorr : |Work.ZeroFreeTables.SigmaP3L q L (DirichletCharacter.changeLevel hNq φ) s a lam₁
        - Work.ZeroFreeTables.SigmaP3L N L φ s a lam₁| ≤ Cc) :
    Work.ZeroFreeTables.SigmaP3L q L (DirichletCharacter.changeLevel hNq φ) s a lam₁
      ≤ -(∑ u ∈ T, (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - u) * (L : ℂ)))).re)
        + (a + lam₁) * c
        + ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct)
        + (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct)
        + (T.card : ℝ) * (8 * (a + lam₁) / (δ * L)) + Cc := by
  have h1 := pointBoundPrimH φ hφ hprim ha hlam₁ hδ hδ1 hLt haδL hsre hsim hlog
    par hpar0 hpar1 hS2 hS3 hJ hmin T hT hTim
  have h2 : Work.ZeroFreeTables.SigmaP3L q L (DirichletCharacter.changeLevel hNq φ) s a lam₁
      ≤ Work.ZeroFreeTables.SigmaP3L N L φ s a lam₁ + Cc := by
    have h := (abs_le.mp hcorr).2
    linarith only [h]
  linarith only [h1, h2]

/-- **The point bound at the principal character, at height `R`**: `SigmaP3L_changeLevel_diff` at
level `1` plus the `ζ`-engine `P9.zetaEngine_principal`, with the `ζ`-inputs taken at height
`Θ = R + 2` (the norm of a test point). -/
theorem pointBoundPrincipalH {q : ℕ} [NeZero q] {a lam₁ δ L Ct Cz C₀ Cc R : ℝ}
    (ha : 0 < a) (hlam₁ : 0 ≤ lam₁) (hδ : 0 < δ) (hδ1 : δ < 1) (hLt : 1 < L)
    (haδL : 2 * a ≤ δ * L) (haL : a ≤ L)
    (hCz : ∀ s : ℂ, ‖s‖ ≤ R + 2 → (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ)
        * (1 / (1 + ‖s - u‖ ^ 2))) ≤ Cz)
    (hC0 : ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ R + 2 →
        (-logDeriv riemannZeta s).re ≤ (1 / (s - 1)).re + C₀)
    (hnz : ∀ t : ℝ, |t| ≤ R → ∀ u : ℂ, riemannZeta u = 0 →
        δ < ‖(1 : ℂ) + (t : ℂ) * Complex.I - u‖)
    {s : ℂ} (hsre : s.re = 1 + a / L) (hsim : |s.im| ≤ R)
    (hS2 : |∑' n : ℕ, (((1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 2)).re| ≤ Ct)
    (hS3 : |∑' n : ℕ, (((1 / (s + ((2 * (n + 1) : ℕ) : ℂ))) ^ 3)).re| ≤ Ct)
    (hcorr : |Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
        - Work.ZeroFreeTables.SigmaP3L 1 L 1 s a lam₁| ≤ Cc) :
    Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
      ≤ (Work.ZeroFreeTables.P3 ((a + lam₁) / ((s - 1) * (L : ℂ)))).re + ((a + lam₁) / L) * C₀
        + ((a + lam₁) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cz + Ct)
        + (2 / 3) * ((a + lam₁) ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cz + Ct) + Cc := by
  have hLpos : 0 < L := lt_trans zero_lt_one hLt
  have hdiv1 : a / L ≤ 1 := div_le_one_of_le₀ haL hLpos.le
  have hsre2 : s.re ≤ 2 := by rw [hsre]; linarith only [hdiv1]
  have hsre1 : 1 < s.re := by
    rw [hsre]
    have : 0 < a / L := div_pos ha hLpos
    linarith only [this]
  have hnorm : ‖s‖ ≤ R + 2 := by
    have hsq : ‖s‖ ^ 2 = s.re ^ 2 + s.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
    have h2 : |s.re| ≤ 2 := abs_le.mpr ⟨by linarith only [hsre1], hsre2⟩
    have h4 : s.re ^ 2 ≤ 4 := by have h := abs_le.mp h2; nlinarith only [h.1, h.2]
    have hRnn : 0 ≤ R := le_trans (abs_nonneg s.im) hsim
    have hR2 : s.im ^ 2 ≤ R ^ 2 := by have h := abs_le.mp hsim; nlinarith only [h.1, h.2]
    have h20 : ‖s‖ ^ 2 ≤ (R + 2) ^ 2 := by rw [hsq]; nlinarith only [h4, hR2, hRnn]
    nlinarith only [norm_nonneg s, h20, hRnn]
  have him2 : |s.im| ≤ R + 2 := by
    have hRnn : 0 ≤ R := le_trans (abs_nonneg s.im) hsim
    linarith only [hsim, hRnn]
  have h1 := Work.ZeroFreeTables.P9.zetaEngine_principal (a := a) (lam₁ := lam₁) (δ := δ) (L := L)
    (Ct := Ct) (Cz := Cz) (C₀ := C₀) ha hlam₁ hδ hδ1 hLt haδL hsre
    (fun u hu => hnz s.im hsim u hu) (hC0 s hsre1 hsre2 him2) (hCz s hnorm) hS2 hS3
  have h2 : Work.ZeroFreeTables.SigmaP3L q L (1 : DirichletCharacter ℂ q) s a lam₁
      ≤ Work.ZeroFreeTables.SigmaP3L 1 L 1 s a lam₁ + Cc := by
    have h := (abs_le.mp hcorr).2
    linarith only [h]
  linarith only [h1, h2]

/-! ## The algebraic bridge for HB's case `χ₁² = χ₀` with `ρ₀` real -/

/-- **Case C with `ρ₀` real** (`γ₀ = 0`).  The four non-principal point bounds keep the
conjugate zeros; when `ρ₀` is real the `β`- and `Δ`-terms coincide and the drop-out quantity is
`2A' + D` (HB's `A'` twice and `D`), non-negative because each piece is.  This is the
`caseCg0_bridge` companion of `HB94.Lam0GeEngine.caseC_bridge` (which covers `γ₀ ≠ 0`). -/
theorem caseCg0_bridge {a lam₁ lam₀ K ε ε₁ Δ γ : ℝ}
    {S1 S2 S3 S4 S5 S6 S7 S8 e1 e2 e3 e4 e5 e6 e7 e8 corr : ℝ}
    (hK : 0 ≤ K) (hα : 0 ≤ a + lam₁)
    (h1 : S1 ≤ Work.ZeroFreeTables.P3R ((a + lam₁) / a) + e1)
    (h2 : S2 ≤ -Work.ZeroFreeTables.P3R ((a + lam₁) / (a + lam₀))
        - Work.ZeroFreeTables.P9.PhiG (a + lam₁) (a + lam₁) Δ
        - Work.ZeroFreeTables.P9.PhiG (a + lam₁) (a + lam₁) Δ
        + (a + lam₁) * (1/6 + ε₁) + e2)
    (h3 : S3 ≤ Work.ZeroFreeTables.P9.PhiG (a + lam₁) a Δ + e3)
    (h4 : S4 ≤ -Work.ZeroFreeTables.P3R 1 - Work.ZeroFreeTables.P9.PhiG (a + lam₁) (a + lam₀) Δ
        - Work.ZeroFreeTables.P9.PhiG (a + lam₁) (a + lam₁) γ
        + (a + lam₁) * (1/6 + ε₁) + e4)
    (h5 : S5 ≤ Work.ZeroFreeTables.P9.PhiG (a + lam₁) a Δ + e5)
    (h6 : S6 ≤ -Work.ZeroFreeTables.P9.PhiG (a + lam₁) (a + lam₁) Δ
        - Work.ZeroFreeTables.P9.PhiG (a + lam₁) (a + lam₀) γ
        + (a + lam₁) * (1/6 + ε₁) + e6)
    (h7 : S7 ≤ Work.ZeroFreeTables.P9.PhiG (a + lam₁) a γ + e7)
    (h8 : S8 ≤ -Work.ZeroFreeTables.P9.PhiG (a + lam₁) (a + lam₁) Δ
        - Work.ZeroFreeTables.P9.PhiG (a + lam₁) (a + lam₀) γ
        + (a + lam₁) * (1/6 + ε₁) + e8)
    (hcomb : 0 ≤ (K ^ 2 + 1 / 2) * (S1 + S2) + K * (S3 + 2 * S4 + S5)
        + (1 / 4) * (S6 + 2 * S7 + S8) + corr)
    (hExpr : 0 ≤ 2 * ((K ^ 2 + 3 / 4) * Work.ZeroFreeTables.P9.PhiG (a + lam₁) (a + lam₁) Δ
          + K * Work.ZeroFreeTables.P9.PhiG (a + lam₁) (a + lam₀) Δ
          - K * Work.ZeroFreeTables.P9.PhiG (a + lam₁) a Δ)
        + (2 * K * Work.ZeroFreeTables.P9.PhiG (a + lam₁) (a + lam₁) γ
          + (1 / 2) * Work.ZeroFreeTables.P9.PhiG (a + lam₁) (a + lam₀) γ
          - (1 / 2) * Work.ZeroFreeTables.P9.PhiG (a + lam₁) a γ))
    (habs : (K ^ 2 + 1 / 2) * (e1 + e2) + K * (e3 + 2 * e4 + e5) + (1 / 4) * (e6 + 2 * e7 + e8)
        + corr + (a + lam₁) * ε₁ * (K ^ 2 + 2 * K + 1) ≤ (a + lam₁) * ε) :
    Work.ZeroFreeTables.ineq913 lam₁ lam₀ a K ε := by
  rw [Work.ZeroFreeTables.ineq913, Work.ZeroFreeTables.p913, Work.ZeroFreeTables.psi13] at *
  have hK0 : 0 ≤ K ^ 2 + 1 / 2 := by positivity
  have h14 : (0 : ℝ) ≤ 1 / 4 := by norm_num
  nlinarith only [hcomb, h1, h2, h3, h4, h5, h6, h7, h8, hExpr, habs, hK0, h14, hα, hK]

end P3H

open Work.ZeroFreeTables.HB94.Lam0GeEngine
open Work.ZeroFreeTables.P9

private theorem rect_case0
  (a : ℝ)
  (K : ℝ)
  (ε : ℝ)
  (ha : (0 : ℝ) < a)
  (hK : (0 : ℝ) < K)
  (hε : (0 : ℝ) < ε)
  (H : ℝ)
  (W : ℝ)
  (hH1 : (1 : ℝ) ≤ H)
  (R : ℝ)
  (hRdef : R = (3 : ℝ) * H)
  (hRnn : (0 : ℝ) ≤ R)
  (hRW : R + (1 : ℝ) ≤ W)
  (hΘ : (0 : ℝ) ≤ R + (2 : ℝ))
  (ε₁ : ℝ)
  (hε₁pos : (0 : ℝ) < ε₁)
  (hε₁bud : ε₁ * (K ^ (2 : ℕ) + (3 : ℝ) * K + (3 / 2 : ℝ)) ≤ ε / (4 : ℝ))
  (Ct : ℝ)
  (hCtpos : (0 : ℝ) < Ct)
  (C₀ : ℝ)
  (hC₀pos : (0 : ℝ) < C₀)
  (Cc : ℝ)
  (hCcpos : (0 : ℝ) < Cc)
  (Cz : ℝ)
  (hCzpos : (0 : ℝ) < Cz)
  (δ : ℝ)
  (hδpos : (0 : ℝ) < δ)
  (hδlt1 : δ < (1 : ℝ))
  (q : ℕ)
  [hqne : NeZero q]
  (χ₁ : DirichletCharacter ℂ q)
  (ρ₁ : ℂ)
  (ρ₀ : ℂ)
  (hmin : IsMinWideAt H W χ₁ ρ₁)
  (hnotreal : ¬(χ₁ ^ (2 : ℕ) = (1 : DirichletCharacter ℂ q) ∧ ρ₁.im = (0 : ℝ)))
  (hzm0 : LinnikContract.zeroMult χ₁ ρ₀ ≠ (0 : ℕ))
  (hγ₀ : |ρ₀.im| ≤ H)
  (hne : ρ₁ ≠ ρ₀)
  (hconj : χ₁ ^ (2 : ℕ) = (1 : DirichletCharacter ℂ q) → ρ₀ ≠ (starRingEnd ℂ : ℂ → ℂ) ρ₁)
  (hcond : cond913 (LinnikContract.lamOf q ρ₁) (LinnikContract.lamOf q ρ₀) a K)
  (L : ℝ)
  (hLdef : L = Real.log (↑q : ℝ))
  (haL : a ≤ L)
  (hLt : (1 : ℝ) < L)
  (hLpos : (0 : ℝ) < L)
  (hLne : L ≠ (0 : ℝ))
  (hL1 : (1 : ℝ) ≤ L)
  (hlogLnn : (0 : ℝ) ≤ Real.log L)
  (h1aL : (1 : ℝ) ≤ a * Real.log L)
  (haδL : (2 : ℝ) * a ≤ δ * L)
  (Cj : ℝ)
  (hCjnn : (0 : ℝ) ≤ Cj)
  (Corr : ℝ)
  (hlam₁nn : (0 : ℝ) ≤ LinnikContract.lamOf q ρ₁)
  (hlam₀nn : (0 : ℝ) ≤ LinnikContract.lamOf q ρ₀)
  (hγ₁ : |ρ₁.im| ≤ H)
  (hlam₁lam₀ : LinnikContract.lamOf q ρ₁ ≤ LinnikContract.lamOf q ρ₀)
  (hχ₁ne : χ₁ ≠ (1 : DirichletCharacter ℂ q))
  (hα0 : (0 : ℝ) ≤ a + LinnikContract.lamOf q ρ₁)
  (hlamOf_eq : ∀ (u : ℂ), LinnikContract.lamOf q u = ((1 : ℝ) - u.re) * L)
  (hminPrim : ∀ {N : ℕ} [inst : NeZero N],
      N ∣ q →
        ∀ (φ : DirichletCharacter ℂ N),
          φ ≠ (1 : DirichletCharacter ℂ N) →
            φ.IsPrimitive →
              ∀ (u : ℂ),
                LinnikContract.zeroMult φ u ≠ (0 : ℕ) → |u.im| ≤ W → LinnikContract.lamOf q ρ₁ ≤ ((1 : ℝ) - u.re) * L)
  (hSpr : ∀ par ≤ (2 : ℕ),
      ∀ (t : ℝ),
        |∑' (n : ℕ), (((1 : ℂ) / (sPt a L t + (↑(par + (2 : ℕ) * n) : ℂ))) ^ (2 : ℕ)).re| ≤ Ct ∧
          |∑' (n : ℕ), (((1 : ℂ) / (sPt a L t + (↑(par + (2 : ℕ) * n) : ℂ))) ^ (3 : ℕ)).re| ≤ Ct)
  (hSzeta : ∀ (t : ℝ),
      |∑' (n : ℕ), (((1 : ℂ) / (sPt a L t + (↑((2 : ℕ) * (n + (1 : ℕ))) : ℂ))) ^ (2 : ℕ)).re| ≤ Ct ∧
        |∑' (n : ℕ), (((1 : ℂ) / (sPt a L t + (↑((2 : ℕ) * (n + (1 : ℕ))) : ℂ))) ^ (3 : ℕ)).re| ≤ Ct)
  (hCzZeta : ∀ (s : ℂ),
      ‖s‖ ≤ R + (2 : ℝ) →
        ∑' (u : ℂ), (↑(analyticOrderNatAt completedRiemannZeta u) : ℝ) * ((1 : ℝ) / ((1 : ℝ) + ‖s - u‖ ^ (2 : ℕ))) ≤ Cz)
  (hC0b' : ∀ (s : ℂ),
      (1 : ℝ) < s.re →
        s.re ≤ (2 : ℝ) → |s.im| ≤ R + (2 : ℝ) → (-logDeriv riemannZeta s).re ≤ ((1 : ℂ) / (s - (1 : ℂ))).re + C₀)
  (hnzδ : ∀ (t : ℝ), |t| ≤ R → ∀ (u : ℂ), riemannZeta u = (0 : ℂ) → δ < ‖(1 : ℂ) + (↑t : ℂ) * I - u‖)
  (hJOf : ∀ {N : ℕ} [inst : NeZero N],
      N ∣ q →
        ∀ (φ : DirichletCharacter ℂ N),
          φ ≠ (1 : DirichletCharacter ℂ N) → φ.IsPrimitive → ∀ (s : ℂ), ‖s‖ ≤ R + (2 : ℝ) → invSqSum N φ s ≤ Cj)
  (hCcOf : ∀ {N : ℕ} [inst : NeZero N] (hNq : N ∣ q) (φ : DirichletCharacter ℂ N) (t : ℝ),
      |SigmaP3L q L ((changeLevel hNq : DirichletCharacter ℂ N → DirichletCharacter ℂ q) φ) (sPt a L t) a
              (LinnikContract.lamOf q ρ₁) -
            SigmaP3L N L φ (sPt a L t) a (LinnikContract.lamOf q ρ₁)| ≤
        Corr)
  (hk1Of : ∀ {N : ℕ} [inst : NeZero N] (φ : DirichletCharacter ℂ N),
      φ ≠ (1 : DirichletCharacter ℂ N) →
        φ.IsPrimitive →
          (3 : ℕ) ≤ N →
            Real.log (↑N : ℝ) ≤ L →
              ∀ (t : ℝ),
                |t| ≤ R →
                  (-logDeriv (LFunction φ) (sPt a L t)).re + nearInvSum N φ (sPt a L t) δ ≤ ((1 / 6 : ℝ) + ε₁) * L)
  (hN3 : (3 : ℕ) ≤ χ₁.conductor)
  (Δ : ℝ)
  (hΔdef : Δ = (ρ₁.im - ρ₀.im) * L)
  (β : ℝ)
  (hβdef : β = (ρ₁.im + ρ₀.im) * L)
  (γ : ℝ)
  (hγdef : γ = (2 : ℝ) * ρ₁.im * L)
  (E2 : ℝ)
  (hE2def : E2 = (a + LinnikContract.lamOf q ρ₁) ^ (2 : ℕ) / L ^ (2 : ℕ) * (((1 : ℝ) + (4 : ℝ) / δ ^ (2 : ℕ)) * Cj + Ct))
  (E3 : ℝ)
  (hE3def : E3 =
      (2 / 3 : ℝ) * ((a + LinnikContract.lamOf q ρ₁) ^ (3 : ℕ) / L ^ (3 : ℕ)) *
        ((2 : ℝ) / δ * ((1 : ℝ) + (4 : ℝ) / δ ^ (2 : ℕ)) * Cj + Ct))
  (E2z : ℝ)
  (hE2zdef : E2z = (a + LinnikContract.lamOf q ρ₁) ^ (2 : ℕ) / L ^ (2 : ℕ) * (((1 : ℝ) + (4 : ℝ) / δ ^ (2 : ℕ)) * Cz + Ct))
  (E3z : ℝ)
  (hE3zdef : E3z =
      (2 / 3 : ℝ) * ((a + LinnikContract.lamOf q ρ₁) ^ (3 : ℕ) / L ^ (3 : ℕ)) *
        ((2 : ℝ) / δ * ((1 : ℝ) + (4 : ℝ) / δ ^ (2 : ℕ)) * Cz + Ct))
  (C0c : ℝ)
  (Fc : ℝ)
  (Ee : ℝ)
  (hcFar : ∀ k ≤ (4 : ℕ), (↑k : ℝ) * ((8 : ℝ) * (a + LinnikContract.lamOf q ρ₁) / (δ * L)) ≤ Fc)
  (hcC0 : (a + LinnikContract.lamOf q ρ₁) / L * C₀ ≤ C0c)
  (heE : ∀ e ≤ E2 + E3 + Fc + Corr + C0c, e ≤ Ee)
  (heEz : ∀ e ≤ E2z + E3z + Fc + Corr + C0c, e ≤ Ee)
  (hEebound : (2 : ℝ) * (K + (1 : ℝ)) ^ (2 : ℕ) * Ee ≤ a * ε / (2 : ℝ))
  (hFcnn : (0 : ℝ) ≤ Fc)
  (hC0cnn : (0 : ℝ) ≤ C0c)
  (hlogNOf : ∀ {N : ℕ}, N ∣ q → N ≠ (0 : ℕ) → Real.log (↑N : ℝ) ≤ L)
  (hC : χ₁ ^ (2 : ℕ) = (1 : DirichletCharacter ℂ q)) :
  ineq913 (LinnikContract.lamOf q ρ₁) (LinnikContract.lamOf q ρ₀) a K ε := by
  have hγ₁ne : ρ₁.im ≠ 0 := fun h0 => hnotreal ⟨hC, h0⟩
  have hconj' : ρ₀ ≠ starRingEnd ℂ ρ₁ := hconj hC
  have hC3 : χ₁ ^ 3 = χ₁ := by rw [pow_succ, hC, one_mul]
  have hzmconj : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ ((starRingEnd ℂ) u)
      = Work.LinnikContract.zeroMult χ₁ u := fun u => Work.A7.zeroMult_conj_sq_one χ₁ hC u
  haveI hN1 : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hφ₁ne : χ₁.primitiveCharacter ≠ 1 := by
    intro hh
    exact hχ₁ne (by rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₁, hh,
      DirichletCharacter.changeLevel_one χ₁.conductor_dvd_level])
  have hφ₁prim : χ₁.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ₁
  have hlogN1 : Real.log ((χ₁.conductor : ℕ) : ℝ) ≤ L :=
    hlogNOf χ₁.conductor_dvd_level χ₁.conductor_ne_zero
  have hzm1 : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u
      = Work.LinnikContract.zeroMult χ₁.primitiveCharacter u := by
    intro u
    have h := Work.ZeroFreeTables.Table4.zeroMult_changeLevel χ₁.conductor_dvd_level
      χ₁.primitiveCharacter u
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
    exact h
  obtain ⟨par₁, hpar₁2, hpar₁0, hpar₁1⟩ := exists_par χ₁.primitiveCharacter
  have hminP1 : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 →
      |u.im| ≤ R + 1 → Work.LinnikContract.lamOf q ρ₁ ≤ (1 - u.re) * L :=
    fun u hu him => hminPrim χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim u hu
      (le_trans him hRW)
  have hk1P1 : ∀ t : ℝ, |t| ≤ R → (-logDeriv (DirichletCharacter.LFunction χ₁.primitiveCharacter)
      (sPt a L t)).re + P9.nearInvSum χ₁.conductor χ₁.primitiveCharacter (sPt a L t) δ
      ≤ (1 / 6 + ε₁) * L := fun t ht =>
    hk1Of χ₁.primitiveCharacter hφ₁ne hφ₁prim hN3 hlogN1 t ht
  have hJ1 : ∀ s : ℂ, ‖s‖ ≤ R + 2 → P9.invSqSum χ₁.conductor χ₁.primitiveCharacter s ≤ Cj :=
    fun s hs => hJOf χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim s hs
  have hCc1 : ∀ t : ℝ, |SigmaP3L q L (DirichletCharacter.changeLevel χ₁.conductor_dvd_level
        χ₁.primitiveCharacter) (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)
      - SigmaP3L χ₁.conductor L χ₁.primitiveCharacter (sPt a L t) a
        (Work.LinnikContract.lamOf q ρ₁)| ≤ Corr :=
    fun t => hCcOf χ₁.conductor_dvd_level χ₁.primitiveCharacter t
  have hρ₁re : ρ₁.re = 1 - (Work.LinnikContract.lamOf q ρ₁) / L := by
    rw [hlamOf_eq ρ₁]; field_simp; ring
  have hρ₀re : ρ₀.re = 1 - (Work.LinnikContract.lamOf q ρ₀) / L := by
    rw [hlamOf_eq ρ₀]; field_simp; ring
  have hρc₁re : (starRingEnd ℂ ρ₁).re = 1 - (Work.LinnikContract.lamOf q ρ₁) / L := by
    rw [Complex.conj_re]; exact hρ₁re
  have hρc₀re : (starRingEnd ℂ ρ₀).re = 1 - (Work.LinnikContract.lamOf q ρ₀) / L := by
    rw [Complex.conj_re]; exact hρ₀re
  -- ### shift bounds (`R = 3H` dominates every shift)
  have hm₁ : |ρ₁.im| ≤ R := by rw [hRdef]; linarith only [hγ₁, hH1]
  have hm₀ : |ρ₀.im| ≤ R := by rw [hRdef]; linarith only [hγ₀, hH1]
  have hm_a : |ρ₁.im - ρ₀.im| ≤ R := by
    have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp hγ₀
    rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
  have hm_b : |ρ₁.im + ρ₀.im| ≤ R := by
    have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp hγ₀
    rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2]
  have hm_g : |2 * ρ₁.im| ≤ R := by
    have h1 := abs_le.mp hγ₁
    rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2]
  have hm_d : |2 * ρ₁.im - ρ₀.im| ≤ R := by
    have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp hγ₀
    rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2]
  have hm_e : |2 * ρ₁.im + ρ₀.im| ≤ R := by
    have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp hγ₀
    rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2]
  -- ### multiplicities of the conjugate zeros
  have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
    rw [← hzm1 ρ₁]; exact hmin.2.1
  have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
    rw [← hzm1 ρ₀]; exact hzm0
  have hzc₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter (starRingEnd ℂ ρ₁) ≠ 0 := by
    rw [← hzm1 (starRingEnd ℂ ρ₁), hzmconj ρ₁]; exact hmin.2.1
  have hzc₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter (starRingEnd ℂ ρ₀) ≠ 0 := by
    rw [← hzm1 (starRingEnd ℂ ρ₀), hzmconj ρ₀]; exact hzm0
  have hρ₀ρ₁ : ρ₀ ≠ ρ₁ := Ne.symm hne
  have hρ₁c₀ : ρ₁ ≠ starRingEnd ℂ ρ₀ := by
    intro hh
    exact hconj' (by have h := congrArg (starRingEnd ℂ) hh; simpa using h.symm)
  have hρ₁c₁ : ρ₁ ≠ starRingEnd ℂ ρ₁ := by
    intro hh
    have h := congrArg Complex.im hh
    simp only [Complex.conj_im] at h
    exact hγ₁ne (by linarith only [h, hC0cnn])
  -- ### error budgets
  set e1 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he1def
  set e2 : ℝ := E2 + E3 + 3 * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) + Corr with he2def
  set e3 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he3def
  set e4 : ℝ := E2 + E3 + 4 * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) + Corr with he4def
  set e5 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he5def
  set e6 : ℝ := E2 + E3 + 2 * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) + Corr with he6def
  set e7 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he7def
  set e8 : ℝ := E2 + E3 + 2 * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) + Corr with he8def
  -- ### the eight points
  set S1 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L 0) a (Work.LinnikContract.lamOf q ρ₁) with hS1'
  set S2 : ℝ := SigmaP3L q L χ₁ (sPt a L ρ₀.im) a (Work.LinnikContract.lamOf q ρ₁) with hS2'
  set S3 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L (ρ₁.im - ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS3'
  set S4 : ℝ := SigmaP3L q L χ₁ (sPt a L ρ₁.im) a (Work.LinnikContract.lamOf q ρ₁) with hS4'
  set S5 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L (ρ₁.im + ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS5'
  set S6 : ℝ := SigmaP3L q L χ₁ (sPt a L (2 * ρ₁.im - ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS6'
  set S7 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L (2 * ρ₁.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS7'
  set S8 : ℝ := SigmaP3L q L χ₁ (sPt a L (2 * ρ₁.im + ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS8'
  clear_value S1 S2 S3 S4 S5 S6 S7 S8
  -- ### point 1: the principal character at `σ`
  have hS1 : S1 ≤ P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / a) + e1 := by
    have hcc0 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) 0
    rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc0
    have hb := P3H.pointBoundPrincipalH (q := q) (a := a)
      (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L) (Ct := Ct) (Cz := Cz)
      (C₀ := C₀) (Cc := Corr) (R := R) ha hlam₁nn hδpos hδlt1 hLt haδL haL
      hCzZeta hC0b' hnzδ (s := sPt a L 0) (by simp [sPt])
      (by rw [show (sPt a L 0).im = 0 by simp [sPt], abs_zero]; exact hRnn)
      (hSzeta 0).1 (hSzeta 0).2 hcc0
    have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
          / ((sPt a L 0 - 1) * (L : ℂ)))).re
        = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / a) := by
      rw [P3_arg_eq_pole_split (a := a) (L := L) (t := 0)
        (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne]
      rw [zero_mul, PhiG_zero]
    rw [hpole] at hb
    linarith only [hb, hS1', he1def, hE2zdef, hE3zdef]
  -- ### point 2: `χ₁` at `σ + iγ₀`, kept `{ρ₀, ρ₁, ρc₁}`
  have hS2 : S2 ≤ -P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀)))
      - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
      - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) β
      + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e2 := by
    have hT : ∀ u ∈ ({ρ₀, ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ),
        Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with h | h | h
      · rw [h]; exact hz₀
      · rw [h]; exact hz₁
      · rw [h]; exact hzc₁
    have hTim : ∀ u ∈ ({ρ₀, ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ), |u.im| ≤ R + 1 := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with h | h | h
      · rw [h]; linarith only [hm₀, hRnn]
      · rw [h]; linarith only [hm₁, hRnn]
      · rw [h]; rw [show ((starRingEnd ℂ) ρ₁).im = -(ρ₁.im) by simp, abs_neg]
        linarith only [hm₁, hRnn]
    have hb := P3H.pointBoundQH (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
      (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
      (s := sPt a L ρ₀.im) (by simp [sPt]) (by simpa [sPt] using hm₀)
      (hk1P1 ρ₀.im hm₀) par₁ hpar₁0 hpar₁1
      (hSpr par₁ hpar₁2 ρ₀.im).1 (hSpr par₁ hpar₁2 ρ₀.im).2
      (hJ1 (sPt a L ρ₀.im) (by simpa [sPt] using P3H.norm_sPt_le_R ha haL hLpos hm₀))
      hminP1 ({ρ₀, ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ) hT hTim (hCc1 ρ₀.im)
    have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
          / ((sPt a L ρ₀.im - ρ₀) * (L : ℂ)))).re
        = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀))) := by
      rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
        (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im) (t := ρ₀.im) (ρ := ρ₀)
        hLne hρ₀re rfl]
      rw [sub_self, zero_mul, PhiG_zero]
    have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
          / ((sPt a L ρ₀.im - ρ₁) * (L : ℂ)))).re
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
      rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
        (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im) (t := ρ₀.im) (ρ := ρ₁)
        hLne hρ₁re rfl]
      rw [show (ρ₀.im - ρ₁.im) * L = -Δ by rw [hΔdef]; ring]
      rw [PhiG_neg']
    have t3 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
          / ((sPt a L ρ₀.im - starRingEnd ℂ ρ₁) * (L : ℂ)))).re
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) β := by
      rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
        (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := -(ρ₁.im)) (t := ρ₀.im)
        (ρ := starRingEnd ℂ ρ₁) hLne hρc₁re (by simp)]
      rw [show (ρ₀.im - -(ρ₁.im)) * L = β by rw [hβdef]; ring]
    have hsum : (∑ u ∈ ({ρ₀, ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ),
        (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
          / ((sPt a L ρ₀.im - u) * (L : ℂ)))).re)
        = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀)))
          + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
          + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) β := by
      rw [Finset.sum_insert (by simp [hρ₀ρ₁, hconj']),
        Finset.sum_insert (by simp [hρ₁c₁]), Finset.sum_singleton, t1, t2, t3]
      ring
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
    rw [show ({ρ₀, ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ).card = 3 by
      rw [Finset.card_insert_of_notMem (by simp [hρ₀ρ₁, hconj']),
        Finset.card_insert_of_notMem (by simp [hρ₁c₁]), Finset.card_singleton]] at hb
    rw [hsum] at hb
    push_cast at hb
    linarith only [hb, hS2', he2def, hE2def, hE3def]
  -- ### point 3: the principal character at `σ + i(γ₁-γ₀)`
  have hS3 : S3 ≤ P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ + e3 := by
    have hcc3 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) (ρ₁.im - ρ₀.im)
    rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc3
    have hb := P3H.pointBoundPrincipalH (q := q) (a := a)
      (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L) (Ct := Ct) (Cz := Cz)
      (C₀ := C₀) (Cc := Corr) (R := R) ha hlam₁nn hδpos hδlt1 hLt haδL haL
      hCzZeta hC0b' hnzδ (s := sPt a L (ρ₁.im - ρ₀.im)) (by simp [sPt])
      (by simpa [sPt] using hm_a)
      (hSzeta (ρ₁.im - ρ₀.im)).1 (hSzeta (ρ₁.im - ρ₀.im)).2 hcc3
    have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
          / ((sPt a L (ρ₁.im - ρ₀.im) - 1) * (L : ℂ)))).re
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ := by
      rw [P3_arg_eq_pole_split (a := a) (L := L) (t := (ρ₁.im - ρ₀.im))
        (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne]
      try simp only [hΔdef, hβdef, hγdef]
    rw [hpole] at hb
    linarith only [hb, hS3', he3def, hE2zdef, hE3zdef]
  -- ### point 5: the principal character at `σ + i(γ₁+γ₀)`
  have hS5 : S5 ≤ P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a β + e5 := by
    have hcc5 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) (ρ₁.im + ρ₀.im)
    rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc5
    have hb := P3H.pointBoundPrincipalH (q := q) (a := a)
      (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L) (Ct := Ct) (Cz := Cz)
      (C₀ := C₀) (Cc := Corr) (R := R) ha hlam₁nn hδpos hδlt1 hLt haδL haL
      hCzZeta hC0b' hnzδ (s := sPt a L (ρ₁.im + ρ₀.im)) (by simp [sPt])
      (by simpa [sPt] using hm_b)
      (hSzeta (ρ₁.im + ρ₀.im)).1 (hSzeta (ρ₁.im + ρ₀.im)).2 hcc5
    have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
          / ((sPt a L (ρ₁.im + ρ₀.im) - 1) * (L : ℂ)))).re
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a β := by
      rw [P3_arg_eq_pole_split (a := a) (L := L) (t := (ρ₁.im + ρ₀.im))
        (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne]
      try simp only [hΔdef, hβdef, hγdef]
    rw [hpole] at hb
    linarith only [hb, hS5', he5def, hE2zdef, hE3zdef]
  -- ### point 7: the principal character at `σ + 2iγ₁`
  have hS7 : S7 ≤ P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a γ + e7 := by
    have hcc7 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) (2 * ρ₁.im)
    rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc7
    have hb := P3H.pointBoundPrincipalH (q := q) (a := a)
      (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L) (Ct := Ct) (Cz := Cz)
      (C₀ := C₀) (Cc := Corr) (R := R) ha hlam₁nn hδpos hδlt1 hLt haδL haL
      hCzZeta hC0b' hnzδ (s := sPt a L (2 * ρ₁.im)) (by simp [sPt])
      (by simpa [sPt] using hm_g)
      (hSzeta (2 * ρ₁.im)).1 (hSzeta (2 * ρ₁.im)).2 hcc7
    have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
          / ((sPt a L (2 * ρ₁.im) - 1) * (L : ℂ)))).re
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a γ := by
      rw [P3_arg_eq_pole_split (a := a) (L := L) (t := (2 * ρ₁.im))
        (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne]
      try simp only [hΔdef, hβdef, hγdef]
    rw [hpole] at hb
    linarith only [hb, hS7', he7def, hE2zdef, hE3zdef]
  -- ### point 6: `χ₁` at `σ + i(2γ₁-γ₀)`, kept `{ρ₁, ρc₀}`
  have hS6 : S6 ≤ -P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
      - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) γ
      + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e6 := by
    have hT : ∀ u ∈ ({ρ₁, starRingEnd ℂ ρ₀} : Finset ℂ),
        Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
      intro u hu
      rcases Finset.mem_insert.mp hu with h | h
      · rw [h]; exact hz₁
      · rw [Finset.mem_singleton.mp h]; exact hzc₀
    have hTim : ∀ u ∈ ({ρ₁, starRingEnd ℂ ρ₀} : Finset ℂ), |u.im| ≤ R + 1 := by
      intro u hu
      rcases Finset.mem_insert.mp hu with h | h
      · rw [h]; linarith only [hm₁, hRnn]
      · rw [Finset.mem_singleton.mp h]
        rw [show ((starRingEnd ℂ) ρ₀).im = -(ρ₀.im) by simp, abs_neg]
        linarith only [hm₀, hRnn]
    have hb := P3H.pointBoundQH (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
      (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
      (s := sPt a L (2 * ρ₁.im - ρ₀.im)) (by simp [sPt]) (by simpa [sPt] using hm_d)
      (hk1P1 (2 * ρ₁.im - ρ₀.im) hm_d) par₁ hpar₁0 hpar₁1
      (hSpr par₁ hpar₁2 (2 * ρ₁.im - ρ₀.im)).1 (hSpr par₁ hpar₁2 (2 * ρ₁.im - ρ₀.im)).2
      (hJ1 (sPt a L (2 * ρ₁.im - ρ₀.im)) (by simpa [sPt] using P3H.norm_sPt_le_R ha haL hLpos hm_d))
      hminP1 ({ρ₁, starRingEnd ℂ ρ₀} : Finset ℂ) hT hTim (hCc1 (2 * ρ₁.im - ρ₀.im))
    have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
          / ((sPt a L (2 * ρ₁.im - ρ₀.im) - ρ₁) * (L : ℂ)))).re
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
      rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
        (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im) (t := 2 * ρ₁.im - ρ₀.im)
        (ρ := ρ₁) hLne hρ₁re rfl]
      rw [show (2 * ρ₁.im - ρ₀.im - ρ₁.im) * L = Δ by rw [hΔdef]; ring]
    have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
          / ((sPt a L (2 * ρ₁.im - ρ₀.im) - starRingEnd ℂ ρ₀) * (L : ℂ)))).re
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) γ := by
      rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
        (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := -(ρ₀.im)) (t := 2 * ρ₁.im - ρ₀.im)
        (ρ := starRingEnd ℂ ρ₀) hLne hρc₀re (by simp)]
      rw [show (2 * ρ₁.im - ρ₀.im - -(ρ₀.im)) * L = γ by rw [hγdef]; ring]
    have hsum : (∑ u ∈ ({ρ₁, starRingEnd ℂ ρ₀} : Finset ℂ),
        (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
          / ((sPt a L (2 * ρ₁.im - ρ₀.im) - u) * (L : ℂ)))).re)
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
          + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) γ := by
      rw [Finset.sum_pair hρ₁c₀, t1, t2]
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
    rw [Finset.card_pair hρ₁c₀, Nat.cast_ofNat, hsum] at hb
    rw [neg_add] at hb
    linarith only [hb, hS6', he6def, hE2def, hE3def]
  -- ### point 8: `χ₁` at `σ + i(2γ₁+γ₀)`, kept `{ρ₁, ρ₀}`
  have hS8 : S8 ≤ -P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) β
      - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) γ
      + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e8 := by
    have hT : ∀ u ∈ ({ρ₁, ρ₀} : Finset ℂ),
        Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
      intro u hu
      rcases Finset.mem_insert.mp hu with h | h
      · rw [h]; exact hz₁
      · rw [Finset.mem_singleton.mp h]; exact hz₀
    have hTim : ∀ u ∈ ({ρ₁, ρ₀} : Finset ℂ), |u.im| ≤ R + 1 := by
      intro u hu
      rcases Finset.mem_insert.mp hu with h | h
      · rw [h]; linarith only [hm₁, hRnn]
      · rw [Finset.mem_singleton.mp h]; linarith only [hm₀, hRnn]
    have hb := P3H.pointBoundQH (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
      (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
      (s := sPt a L (2 * ρ₁.im + ρ₀.im)) (by simp [sPt]) (by simpa [sPt] using hm_e)
      (hk1P1 (2 * ρ₁.im + ρ₀.im) hm_e) par₁ hpar₁0 hpar₁1
      (hSpr par₁ hpar₁2 (2 * ρ₁.im + ρ₀.im)).1 (hSpr par₁ hpar₁2 (2 * ρ₁.im + ρ₀.im)).2
      (hJ1 (sPt a L (2 * ρ₁.im + ρ₀.im)) (by simpa [sPt] using P3H.norm_sPt_le_R ha haL hLpos hm_e))
      hminP1 ({ρ₁, ρ₀} : Finset ℂ) hT hTim (hCc1 (2 * ρ₁.im + ρ₀.im))
    have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
          / ((sPt a L (2 * ρ₁.im + ρ₀.im) - ρ₁) * (L : ℂ)))).re
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) β := by
      rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
        (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im) (t := 2 * ρ₁.im + ρ₀.im)
        (ρ := ρ₁) hLne hρ₁re rfl]
      rw [show (2 * ρ₁.im + ρ₀.im - ρ₁.im) * L = β by rw [hβdef]; ring]
    have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
          / ((sPt a L (2 * ρ₁.im + ρ₀.im) - ρ₀) * (L : ℂ)))).re
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) γ := by
      rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
        (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im) (t := 2 * ρ₁.im + ρ₀.im)
        (ρ := ρ₀) hLne hρ₀re rfl]
      rw [show (2 * ρ₁.im + ρ₀.im - ρ₀.im) * L = γ by rw [hγdef]; ring]
    have hsum : (∑ u ∈ ({ρ₁, ρ₀} : Finset ℂ),
        (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
          / ((sPt a L (2 * ρ₁.im + ρ₀.im) - u) * (L : ℂ)))).re)
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) β
          + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) γ := by
      rw [Finset.sum_pair hne, t1, t2]
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
    rw [Finset.card_pair hne, Nat.cast_ofNat, hsum] at hb
    rw [neg_add] at hb
    linarith only [hb, hS8', he8def, hE2def, hE3def]
  -- ### the assembly
  have hE1 : e1 ≤ Ee := by rw [he1def]; exact heEz _ (by linarith only [hcC0, hFcnn])
  have hE2 : e2 ≤ Ee := by rw [he2def]; exact heE _ (by have h := hcFar 3 (by norm_num); linarith only [h, hC0cnn])
  have hE3 : e3 ≤ Ee := by rw [he3def]; exact heEz _ (by linarith only [hcC0, hFcnn])
  have hE4 : e4 ≤ Ee := by rw [he4def]; exact heE _ (by have h := hcFar 4 (by norm_num); linarith only [h, hC0cnn])
  have hE5 : e5 ≤ Ee := by rw [he5def]; exact heEz _ (by linarith only [hcC0, hFcnn])
  have hE6 : e6 ≤ Ee := by rw [he6def]; exact heE _ (by have h := hcFar 2 (by norm_num); linarith only [h, hC0cnn])
  have hE7 : e7 ≤ Ee := by rw [he7def]; exact heEz _ (by linarith only [hcC0, hFcnn])
  have hE8 : e8 ≤ Ee := by rw [he8def]; exact heE _ (by have h := hcFar 2 (by norm_num); linarith only [h, hC0cnn])
  have hcomb : 0 ≤ (K ^ 2 + 1 / 2) * (S1 + S2) + K * (S3 + 2 * S4 + S5)
      + (1 / 4) * (S6 + 2 * S7 + S8) + 0 := by
    have h0 := P9.HbCombinationL_nonneg (q := q) χ₁ K (1 + a / L) ρ₀.im ρ₁.im a
      (Work.LinnikContract.lamOf q ρ₁) hK.le
      (by have h : 0 < a / L := div_pos ha hLpos; linarith only [h, hC0cnn]) ha hlam₁nn
    rw [Work.ZeroFreeTables.HbCombinationL, ← hLdef, hC, hC3] at h0
    push_cast at h0
    simp only [hS1', hS2', hS3', hS4', hS5', hS6', hS7', hS8', sPt, Complex.ofReal_zero,
      zero_mul, add_zero]
    push_cast
    exact h0
  have hExpr : 0 ≤
      (K ^ 2 + 3 / 4) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
        + K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
        - K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ
      + ((K ^ 2 + 3 / 4) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) β
        + K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) β
        - K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a β)
      + (2 * K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) γ
        + (1 / 2) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) γ
        - (1 / 2) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a γ)
      + K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
      + K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) β := by
    have hs := Work.ZeroFreeTables.side913 ha hK (by linarith only [ha, hlam₁nn])
      (by linarith only [ha, hlam₀nn]) hcond
    have hA1 := P9.rescale_variants.1 a (Work.LinnikContract.lamOf q ρ₁)
      (Work.LinnikContract.lamOf q ρ₀) K Δ ha hlam₁nn hlam₁lam₀ hK hs.2.2.1
    have hA2 := P9.rescale_variants.1 a (Work.LinnikContract.lamOf q ρ₁)
      (Work.LinnikContract.lamOf q ρ₀) K β ha hlam₁nn hlam₁lam₀ hK hs.2.2.1
    have hD := Work.ZeroFreeTables.P3.CaseC_D (a := a) (lam₁ := Work.LinnikContract.lamOf q ρ₁)
      (lam₀ := Work.LinnikContract.lamOf q ρ₀) (K := K) (t := γ) ha hK.le hlam₁nn hlam₁lam₀ hs.2.2.2
    have hD' : 0 ≤ 2 * K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) γ
        + (1/2) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) γ
        - (1/2) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a γ := by
      have h := hD
      simp only [P9.PhiG] at h ⊢
      push_cast at h ⊢
      simp only [Complex.add_re, Complex.sub_re] at h ⊢
      simp [Complex.mul_re] at h ⊢
      exact h
    have hα0' : 0 < a + (Work.LinnikContract.lamOf q ρ₁) := by linarith only [ha, hlam₁nn]
    have hΦ1 : 0 ≤ P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
        (a + (Work.LinnikContract.lamOf q ρ₀)) Δ :=
      P9.PhiG_nonneg hα0' (by linarith only [hlam₁lam₀])
    have hΦ2 : 0 ≤ P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
        (a + (Work.LinnikContract.lamOf q ρ₀)) β :=
      P9.PhiG_nonneg hα0' (by linarith only [hlam₁lam₀])
    have hΦK1 : 0 ≤ K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
        (a + (Work.LinnikContract.lamOf q ρ₀)) Δ := mul_nonneg hK.le hΦ1
    have hΦK2 : 0 ≤ K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁))
        (a + (Work.LinnikContract.lamOf q ρ₀)) β := mul_nonneg hK.le hΦ2
    linarith only [hA1, hA2, hD', hΦK1, hΦK2]
  have habs' : (K ^ 2 + 1 / 2) * (e1 + e2) + K * (e3 + 2 * e4 + e5)
      + (1 / 4) * (e6 + 2 * e7 + e8) + 0
      + (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ * (K ^ 2 + 2 * K + 1)
      ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε := by
    have hsum := Work.ZeroFreeTables.HB94.Lam0GeEngine.sumErr_le hK.le hE1 hE2 hE3 hE4 hE5 hE6 hE7 hE8
    have hεbud := mul_le_mul_of_nonneg_left hε₁bud hα0
    have hmain : 2 * (K + 1) ^ 2 * Ee ≤ a * ε / 2 := hEebound
    have h54 : (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ * (K ^ 2 + 2 * K + 1)
        ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * (ε / 4) := by
      have h1 : (K ^ 2 + 2 * K + 1 : ℝ) ≤ K ^ 2 + 3 * K + 3 / 2 := by
        nlinarith only [hK]
      have h2 : 0 ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ := by positivity
      calc (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ * (K ^ 2 + 2 * K + 1)
          ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ * (K ^ 2 + 3 * K + 3 / 2) :=
            mul_le_mul_of_nonneg_left h1 h2
        _ = (a + (Work.LinnikContract.lamOf q ρ₁)) * (ε₁ * (K ^ 2 + 3 * K + 3 / 2)) := by ring
        _ ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * (ε / 4) :=
            mul_le_mul_of_nonneg_left hε₁bud hα0
    have hfin : a * ε / 2 + (a + (Work.LinnikContract.lamOf q ρ₁)) * (ε / 4)
        ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε := by
      nlinarith only [hε, hlam₁nn, ha]
    linarith only [hsum, hmain, hεbud, hfin, h54]
  by_cases hγ₀0 : ρ₀.im = 0
  · -- ### sub-case `ρ₀` real
    have hS4 : S4 ≤ -P3R 1
        - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
        - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) γ
        + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e4 := by
      have hT : ∀ u ∈ ({ρ₀, ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ),
          Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h | h
        · rw [h]; exact hz₀
        · rw [h]; exact hz₁
        · rw [h]; exact hzc₁
      have hTim : ∀ u ∈ ({ρ₀, ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ), |u.im| ≤ R + 1 := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h | h
        · rw [h]; linarith only [hm₀, hRnn]
        · rw [h]; linarith only [hm₁, hRnn]
        · rw [h]; rw [show ((starRingEnd ℂ) ρ₁).im = -(ρ₁.im) by simp, abs_neg]
          linarith only [hm₁, hRnn]
      have hb := P3H.pointBoundQH (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
        (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
        (s := sPt a L ρ₁.im) (by simp [sPt]) (by simpa [sPt] using hm₁)
        (hk1P1 ρ₁.im hm₁) par₁ hpar₁0 hpar₁1
        (hSpr par₁ hpar₁2 ρ₁.im).1 (hSpr par₁ hpar₁2 ρ₁.im).2
        (hJ1 (sPt a L ρ₁.im) (by simpa [sPt] using P3H.norm_sPt_le_R ha haL hLpos hm₁))
        hminP1 ({ρ₀, ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ) hT hTim (hCc1 ρ₁.im)
      have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L ρ₁.im - ρ₁) * (L : ℂ)))).re = P3R 1 := by
        rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
          (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im) (t := ρ₁.im) (ρ := ρ₁)
          hLne hρ₁re rfl]
        rw [sub_self, zero_mul, PhiG_zero]
        rw [show (a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₁)) = 1 by
          rw [div_self (ne_of_gt (lt_of_lt_of_le ha (le_add_of_nonneg_right hlam₁nn)))]]
      have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L ρ₁.im - ρ₀) * (L : ℂ)))).re
          = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ := by
        rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
          (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im) (t := ρ₁.im) (ρ := ρ₀)
          hLne hρ₀re rfl]
        try simp only [hΔdef, hβdef, hγdef]
      have t3 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L ρ₁.im - starRingEnd ℂ ρ₁) * (L : ℂ)))).re
          = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) γ := by
        rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
          (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := -(ρ₁.im)) (t := ρ₁.im)
          (ρ := starRingEnd ℂ ρ₁) hLne hρc₁re (by simp)]
        rw [show (ρ₁.im - -(ρ₁.im)) * L = γ by rw [hγdef]; ring]
      have hsum : (∑ u ∈ ({ρ₀, ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ),
          (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L ρ₁.im - u) * (L : ℂ)))).re)
          = P3R 1
            + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
            + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) γ := by
        rw [Finset.sum_insert (by simp [hρ₀ρ₁, hconj']),
          Finset.sum_insert (by simp [hρ₁c₁]), Finset.sum_singleton, t1, t2, t3]
        ring
      rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
      rw [show ({ρ₀, ρ₁, starRingEnd ℂ ρ₁} : Finset ℂ).card = 3 by
        rw [Finset.card_insert_of_notMem (by simp [hρ₀ρ₁, hconj']),
          Finset.card_insert_of_notMem (by simp [hρ₁c₁]), Finset.card_singleton]] at hb
      rw [hsum] at hb
      push_cast at hb
      have hE23nn : 0 ≤ E2 + E3 := by rw [hE2def, hE3def]; positivity
      have hcnn : 0 ≤ 8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L) := by positivity
      linarith only [hb, hS4', he4def, hE2def, hE3def, hE23nn, hcnn]
    have hExpr' : 0 ≤ 2 * ((K ^ 2 + 3 / 4)
            * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
          + K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
          - K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ)
        + (2 * K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) γ
          + (1 / 2) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) γ
          - (1 / 2) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a γ) := by
      have hs := Work.ZeroFreeTables.side913 ha hK (by linarith only [ha, hlam₁nn])
        (by linarith only [ha, hlam₀nn]) hcond
      have hA1 := P9.rescale_variants.1 a (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₀) K Δ ha hlam₁nn hlam₁lam₀ hK hs.2.2.1
      have hD := Work.ZeroFreeTables.P3.CaseC_D (a := a) (lam₁ := Work.LinnikContract.lamOf q ρ₁)
        (lam₀ := Work.LinnikContract.lamOf q ρ₀) (K := K) (t := γ) ha hK.le hlam₁nn hlam₁lam₀ hs.2.2.2
      have hD' : 0 ≤ 2 * K * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) γ
          + (1/2) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) γ
          - (1/2) * P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a γ := by
        have h := hD
        simp only [P9.PhiG] at h ⊢
        push_cast at h ⊢
        simp only [Complex.add_re, Complex.sub_re] at h ⊢
        simp [Complex.mul_re] at h ⊢
        exact h
      linarith only [hA1, hD']
    have hΔβ : β = Δ := by rw [hΔdef, hβdef, hγ₀0]; ring
    have hS2' : S2 ≤ -P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀)))
        - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
        - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
        + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e2 := by
      have := hS2
      rwa [hΔβ] at this
    have hS6' : S6 ≤ -P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
        - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) γ
        + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e6 := hS6
    have hS8' : S8 ≤ -P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
        - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) γ
        + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e8 := by
      have := hS8
      rwa [hΔβ] at this
    have hS5' : S5 ≤ P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ + e5 := by
      have := hS5
      rwa [hΔβ] at this
    exact P3H.caseCg0_bridge (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
      (lam₀ := (Work.LinnikContract.lamOf q ρ₀)) (K := K) (ε := ε) (ε₁ := ε₁)
      (Δ := Δ) (γ := γ)
      (S1 := S1) (S2 := S2) (S3 := S3) (S4 := S4) (S5 := S5) (S6 := S6) (S7 := S7)
      (S8 := S8) (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4) (e5 := e5) (e6 := e6)
      (e7 := e7) (e8 := e8) (corr := 0)
      hK.le hα0 hS1 hS2' hS3 hS4 hS5' hS6' hS7 hS8' hcomb hExpr' habs'
  · -- ### sub-case `ρ₀` non-real
    have hγ₀ne : ρ₀.im ≠ 0 := hγ₀0
    have hρ₀c₀ : ρ₀ ≠ starRingEnd ℂ ρ₀ := by
      intro hh
      have h := congrArg Complex.im hh
      simp only [Complex.conj_im] at h
      exact hγ₀ne (by linarith only [h, hC0cnn])
    have hS4 : S4 ≤ -P3R 1
        - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
        - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) β
        - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) γ
        + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e4 := by
      have hT : ∀ u ∈ ({ρ₁, ρ₀, starRingEnd ℂ ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ),
          Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h | h | h
        · rw [h]; exact hz₁
        · rw [h]; exact hz₀
        · rw [h]; exact hzc₀
        · rw [h]; exact hzc₁
      have hTim : ∀ u ∈ ({ρ₁, ρ₀, starRingEnd ℂ ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ),
          |u.im| ≤ R + 1 := by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with h | h | h | h
        · rw [h]; linarith only [hm₁, hRnn]
        · rw [h]; linarith only [hm₀, hRnn]
        · rw [h]; rw [show ((starRingEnd ℂ) ρ₀).im = -(ρ₀.im) by simp, abs_neg]
          linarith only [hm₀, hRnn]
        · rw [h]; rw [show ((starRingEnd ℂ) ρ₁).im = -(ρ₁.im) by simp, abs_neg]
          linarith only [hm₁, hRnn]
      have hb := P3H.pointBoundQH (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
        (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
        (s := sPt a L ρ₁.im) (by simp [sPt]) (by simpa [sPt] using hm₁)
        (hk1P1 ρ₁.im hm₁) par₁ hpar₁0 hpar₁1
        (hSpr par₁ hpar₁2 ρ₁.im).1 (hSpr par₁ hpar₁2 ρ₁.im).2
        (hJ1 (sPt a L ρ₁.im) (by simpa [sPt] using P3H.norm_sPt_le_R ha haL hLpos hm₁))
        hminP1 ({ρ₁, ρ₀, starRingEnd ℂ ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ) hT hTim (hCc1 ρ₁.im)
      have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L ρ₁.im - ρ₁) * (L : ℂ)))).re = P3R 1 := by
        rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
          (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im) (t := ρ₁.im) (ρ := ρ₁)
          hLne hρ₁re rfl]
        rw [sub_self, zero_mul, PhiG_zero]
        rw [show (a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₁)) = 1 by
          rw [div_self (ne_of_gt (lt_of_lt_of_le ha (le_add_of_nonneg_right hlam₁nn)))]]
      have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L ρ₁.im - ρ₀) * (L : ℂ)))).re
          = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ := by
        rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
          (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im) (t := ρ₁.im) (ρ := ρ₀)
          hLne hρ₀re rfl]
        try simp only [hΔdef, hβdef, hγdef]
      have t3 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L ρ₁.im - starRingEnd ℂ ρ₀) * (L : ℂ)))).re
          = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) β := by
        rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
          (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := -(ρ₀.im)) (t := ρ₁.im)
          (ρ := starRingEnd ℂ ρ₀) hLne hρc₀re (by simp)]
        rw [show (ρ₁.im - -(ρ₀.im)) * L = β by rw [hβdef]; ring]
      have t4 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L ρ₁.im - starRingEnd ℂ ρ₁) * (L : ℂ)))).re
          = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) γ := by
        rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
          (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := -(ρ₁.im)) (t := ρ₁.im)
          (ρ := starRingEnd ℂ ρ₁) hLne hρc₁re (by simp)]
        rw [show (ρ₁.im - -(ρ₁.im)) * L = γ by rw [hγdef]; ring]
      have hmem1 : ρ₁ ∉ ({ρ₀, starRingEnd ℂ ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hne, hρ₁c₀, hρ₁c₁⟩
      have hmem2 : ρ₀ ∉ ({starRingEnd ℂ ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨hρ₀c₀, hconj'⟩
      have hmem3 : starRingEnd ℂ ρ₀ ∉ ({starRingEnd ℂ ρ₁} : Finset ℂ) := by
        simp only [Finset.mem_singleton]
        intro hh
        exact hρ₀ρ₁ (by
          have h := congrArg (starRingEnd ℂ) hh
          simpa using h)
      have hsum : (∑ u ∈ ({ρ₁, ρ₀, starRingEnd ℂ ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ),
          (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ))
            / ((sPt a L ρ₁.im - u) * (L : ℂ)))).re)
          = P3R 1
            + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
            + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) β
            + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) γ := by
        rw [Finset.sum_insert hmem1, Finset.sum_insert hmem2, Finset.sum_insert hmem3,
          Finset.sum_singleton, t1, t2, t3, t4]
        ring
      rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
      rw [show ({ρ₁, ρ₀, starRingEnd ℂ ρ₀, starRingEnd ℂ ρ₁} : Finset ℂ).card = 4 by
        rw [Finset.card_insert_of_notMem hmem1, Finset.card_insert_of_notMem hmem2,
          Finset.card_insert_of_notMem hmem3, Finset.card_singleton]] at hb
      rw [hsum] at hb
      push_cast at hb
      linarith only [hb, hS4', he4def, hE2def, hE3def]
    exact Work.ZeroFreeTables.HB94.Lam0GeEngine.caseC_bridge (a := a)
      (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam₀ := (Work.LinnikContract.lamOf q ρ₀))
      (K := K) (ε := ε) (ε₁ := ε₁) (Δ := Δ) (β := β) (γ := γ)
      (S1 := S1) (S2 := S2) (S3 := S3) (S4 := S4) (S5 := S5) (S6 := S6) (S7 := S7)
      (S8 := S8) (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4) (e5 := e5) (e6 := e6)
      (e7 := e7) (e8 := e8) (corr := 0)
      hK.le hα0 hS1 hS2 hS3 hS4 hS5 hS6 hS7 hS8 hcomb hExpr habs'

private theorem rect_case1
  (a : ℝ)
  (K : ℝ)
  (ε : ℝ)
  (ha : (0 : ℝ) < a)
  (hK : (0 : ℝ) < K)
  (hε : (0 : ℝ) < ε)
  (H : ℝ)
  (W : ℝ)
  (hH1 : (1 : ℝ) ≤ H)
  (R : ℝ)
  (hRdef : R = (3 : ℝ) * H)
  (hRnn : (0 : ℝ) ≤ R)
  (hRW : R + (1 : ℝ) ≤ W)
  (hΘ : (0 : ℝ) ≤ R + (2 : ℝ))
  (ε₁ : ℝ)
  (hε₁pos : (0 : ℝ) < ε₁)
  (hε₁bud : ε₁ * (K ^ (2 : ℕ) + (3 : ℝ) * K + (3 / 2 : ℝ)) ≤ ε / (4 : ℝ))
  (Ct : ℝ)
  (hCtpos : (0 : ℝ) < Ct)
  (C₀ : ℝ)
  (hC₀pos : (0 : ℝ) < C₀)
  (Cc : ℝ)
  (hCcpos : (0 : ℝ) < Cc)
  (Cp : ℝ)
  (hCpnn : (0 : ℝ) ≤ Cp)
  (Cz : ℝ)
  (hCzpos : (0 : ℝ) < Cz)
  (Cn : ℝ)
  (hCnpos : (0 : ℝ) < Cn)
  (δ : ℝ)
  (hδpos : (0 : ℝ) < δ)
  (hδlt1 : δ < (1 : ℝ))
  (aup : ℝ)
  (hauppos : (0 : ℝ) < aup)
  (qabs : ℕ)
  (habs : ∀ (q : ℕ),
      qabs ≤ q →
        (2 : ℝ) * (K + (1 : ℝ)) ^ (2 : ℕ) *
            (aup / Real.log (↑q : ℝ) * C₀ +
                    aup ^ (2 : ℕ) / Real.log (↑q : ℝ) ^ (2 : ℕ) *
                      (((1 : ℝ) + (4 : ℝ) / δ ^ (2 : ℕ)) * (Cn * (Real.log (↑q : ℝ) + (6 : ℝ)) + Cz) + Ct) +
                  (2 / 3 : ℝ) * (aup ^ (3 : ℕ) / Real.log (↑q : ℝ) ^ (3 : ℕ)) *
                    ((2 : ℝ) / δ * ((1 : ℝ) + (4 : ℝ) / δ ^ (2 : ℕ)) * (Cn * (Real.log (↑q : ℝ) + (6 : ℝ)) + Cz) + Ct) +
                Cc / Real.log (↑q : ℝ) *
                  (aup * Cp * Real.log (Real.log (↑q : ℝ)) ^ (2 : ℕ) +
                      aup ^ (2 : ℕ) / Real.log (↑q : ℝ) * Cp * Real.log (Real.log (↑q : ℝ)) ^ (3 : ℕ) +
                    aup ^ (3 : ℕ) / Real.log (↑q : ℝ) ^ (2 : ℕ) * Cp * Real.log (Real.log (↑q : ℝ)) ^ (4 : ℕ)) +
              (64 : ℝ) * aup / (δ * Real.log (↑q : ℝ))) ≤
          a * ε / (2 : ℝ))
  (q : ℕ)
  [hqne : NeZero q]
  (χ₁ : DirichletCharacter ℂ q)
  (ρ₁ : ℂ)
  (ρ₀ : ℂ)
  (hmin : IsMinWideAt H W χ₁ ρ₁)
  (hzm0 : LinnikContract.zeroMult χ₁ ρ₀ ≠ (0 : ℕ))
  (hγ₀ : |ρ₀.im| ≤ H)
  (hne : ρ₁ ≠ ρ₀)
  (hcond : cond913 (LinnikContract.lamOf q ρ₁) (LinnikContract.lamOf q ρ₀) a K)
  (L : ℝ)
  (hLdef : L = Real.log (↑q : ℝ))
  (haL : a ≤ L)
  (hLt : (1 : ℝ) < L)
  (hLpos : (0 : ℝ) < L)
  (hLne : L ≠ (0 : ℝ))
  (hL1 : (1 : ℝ) ≤ L)
  (hlogLnn : (0 : ℝ) ≤ Real.log L)
  (h1aL : (1 : ℝ) ≤ a * Real.log L)
  (haδL : (2 : ℝ) * a ≤ δ * L)
  (Cj : ℝ)
  (hCjnn : (0 : ℝ) ≤ Cj)
  (Corr : ℝ)
  (hlam₁nn : (0 : ℝ) ≤ LinnikContract.lamOf q ρ₁)
  (hlam₀nn : (0 : ℝ) ≤ LinnikContract.lamOf q ρ₀)
  (hγ₁ : |ρ₁.im| ≤ H)
  (hlam₁lam₀ : LinnikContract.lamOf q ρ₁ ≤ LinnikContract.lamOf q ρ₀)
  (hχ₁ne : χ₁ ≠ (1 : DirichletCharacter ℂ q))
  (hα0 : (0 : ℝ) ≤ a + LinnikContract.lamOf q ρ₁)
  (hαaup : a + LinnikContract.lamOf q ρ₁ ≤ aup)
  (hlamOf_eq : ∀ (u : ℂ), LinnikContract.lamOf q u = ((1 : ℝ) - u.re) * L)
  (hminPrim : ∀ {N : ℕ} [inst : NeZero N],
      N ∣ q →
        ∀ (φ : DirichletCharacter ℂ N),
          φ ≠ (1 : DirichletCharacter ℂ N) →
            φ.IsPrimitive →
              ∀ (u : ℂ),
                LinnikContract.zeroMult φ u ≠ (0 : ℕ) → |u.im| ≤ W → LinnikContract.lamOf q ρ₁ ≤ ((1 : ℝ) - u.re) * L)
  (hSpr : ∀ par ≤ (2 : ℕ),
      ∀ (t : ℝ),
        |∑' (n : ℕ), (((1 : ℂ) / (sPt a L t + (↑(par + (2 : ℕ) * n) : ℂ))) ^ (2 : ℕ)).re| ≤ Ct ∧
          |∑' (n : ℕ), (((1 : ℂ) / (sPt a L t + (↑(par + (2 : ℕ) * n) : ℂ))) ^ (3 : ℕ)).re| ≤ Ct)
  (hSzeta : ∀ (t : ℝ),
      |∑' (n : ℕ), (((1 : ℂ) / (sPt a L t + (↑((2 : ℕ) * (n + (1 : ℕ))) : ℂ))) ^ (2 : ℕ)).re| ≤ Ct ∧
        |∑' (n : ℕ), (((1 : ℂ) / (sPt a L t + (↑((2 : ℕ) * (n + (1 : ℕ))) : ℂ))) ^ (3 : ℕ)).re| ≤ Ct)
  (hCzZeta : ∀ (s : ℂ),
      ‖s‖ ≤ R + (2 : ℝ) →
        ∑' (u : ℂ), (↑(analyticOrderNatAt completedRiemannZeta u) : ℝ) * ((1 : ℝ) / ((1 : ℝ) + ‖s - u‖ ^ (2 : ℕ))) ≤ Cz)
  (hC0b' : ∀ (s : ℂ),
      (1 : ℝ) < s.re →
        s.re ≤ (2 : ℝ) → |s.im| ≤ R + (2 : ℝ) → (-logDeriv riemannZeta s).re ≤ ((1 : ℂ) / (s - (1 : ℂ))).re + C₀)
  (hnzδ : ∀ (t : ℝ), |t| ≤ R → ∀ (u : ℂ), riemannZeta u = (0 : ℂ) → δ < ‖(1 : ℂ) + (↑t : ℂ) * I - u‖)
  (hJOf : ∀ {N : ℕ} [inst : NeZero N],
      N ∣ q →
        ∀ (φ : DirichletCharacter ℂ N),
          φ ≠ (1 : DirichletCharacter ℂ N) → φ.IsPrimitive → ∀ (s : ℂ), ‖s‖ ≤ R + (2 : ℝ) → invSqSum N φ s ≤ Cj)
  (hCcOf : ∀ {N : ℕ} [inst : NeZero N] (hNq : N ∣ q) (φ : DirichletCharacter ℂ N) (t : ℝ),
      |SigmaP3L q L ((changeLevel hNq : DirichletCharacter ℂ N → DirichletCharacter ℂ q) φ) (sPt a L t) a
              (LinnikContract.lamOf q ρ₁) -
            SigmaP3L N L φ (sPt a L t) a (LinnikContract.lamOf q ρ₁)| ≤
        Corr)
  (hk1Of : ∀ {N : ℕ} [inst : NeZero N] (φ : DirichletCharacter ℂ N),
      φ ≠ (1 : DirichletCharacter ℂ N) →
        φ.IsPrimitive →
          (3 : ℕ) ≤ N →
            Real.log (↑N : ℝ) ≤ L →
              ∀ (t : ℝ),
                |t| ≤ R →
                  (-logDeriv (LFunction φ) (sPt a L t)).re + nearInvSum N φ (sPt a L t) δ ≤ ((1 / 6 : ℝ) + ε₁) * L)
  (hN3 : (3 : ℕ) ≤ χ₁.conductor)
  (Δ : ℝ)
  (hΔdef : Δ = (ρ₁.im - ρ₀.im) * L)
  (β : ℝ)
  (γ : ℝ)
  (E2 : ℝ)
  (hE2def : E2 = (a + LinnikContract.lamOf q ρ₁) ^ (2 : ℕ) / L ^ (2 : ℕ) * (((1 : ℝ) + (4 : ℝ) / δ ^ (2 : ℕ)) * Cj + Ct))
  (E3 : ℝ)
  (hE3def : E3 =
      (2 / 3 : ℝ) * ((a + LinnikContract.lamOf q ρ₁) ^ (3 : ℕ) / L ^ (3 : ℕ)) *
        ((2 : ℝ) / δ * ((1 : ℝ) + (4 : ℝ) / δ ^ (2 : ℕ)) * Cj + Ct))
  (E2z : ℝ)
  (hE2zdef : E2z = (a + LinnikContract.lamOf q ρ₁) ^ (2 : ℕ) / L ^ (2 : ℕ) * (((1 : ℝ) + (4 : ℝ) / δ ^ (2 : ℕ)) * Cz + Ct))
  (E3z : ℝ)
  (hE3zdef : E3z =
      (2 / 3 : ℝ) * ((a + LinnikContract.lamOf q ρ₁) ^ (3 : ℕ) / L ^ (3 : ℕ)) *
        ((2 : ℝ) / δ * ((1 : ℝ) + (4 : ℝ) / δ ^ (2 : ℕ)) * Cz + Ct))
  (C0c : ℝ)
  (hC0cdef : C0c = aup / L * C₀)
  (Fc : ℝ)
  (hFcdef : Fc = (64 : ℝ) * aup / (δ * L))
  (Ee : ℝ)
  (hcFar : ∀ k ≤ (4 : ℕ), (↑k : ℝ) * ((8 : ℝ) * (a + LinnikContract.lamOf q ρ₁) / (δ * L)) ≤ Fc)
  (heE : ∀ e ≤ E2 + E3 + Fc + Corr + C0c, e ≤ Ee)
  (heEz : ∀ e ≤ E2z + E3z + Fc + Corr + C0c, e ≤ Ee)
  (hEebound : (2 : ℝ) * (K + (1 : ℝ)) ^ (2 : ℕ) * Ee ≤ a * ε / (2 : ℝ))
  (hFcnn : (0 : ℝ) ≤ Fc)
  (hC0cnn : (0 : ℝ) ≤ C0c)
  (hlogNOf : ∀ {N : ℕ}, N ∣ q → N ≠ (0 : ℕ) → Real.log (↑N : ℝ) ≤ L)
  (hC : ¬χ₁ ^ (2 : ℕ) = (1 : DirichletCharacter ℂ q))
  (hB : χ₁ ^ (3 : ℕ) = (1 : DirichletCharacter ℂ q)) :
  ineq913 (LinnikContract.lamOf q ρ₁) (LinnikContract.lamOf q ρ₀) a K ε := by
  have hχ2 : χ₁ ^ 2 ≠ 1 := hC
  haveI hN1 : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hφ₁ne : χ₁.primitiveCharacter ≠ 1 := by
    intro hh
    exact hχ₁ne (by rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₁, hh,
      DirichletCharacter.changeLevel_one χ₁.conductor_dvd_level])
  have hφ₁prim : χ₁.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ₁
  have hlogN1 : Real.log ((χ₁.conductor : ℕ) : ℝ) ≤ L :=
    hlogNOf χ₁.conductor_dvd_level χ₁.conductor_ne_zero
  have hzm1 : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u
      = Work.LinnikContract.zeroMult χ₁.primitiveCharacter u := by
    intro u
    have h := Work.ZeroFreeTables.Table4.zeroMult_changeLevel χ₁.conductor_dvd_level
      χ₁.primitiveCharacter u
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
    exact h
  obtain ⟨par₁, hpar₁2, hpar₁0, hpar₁1⟩ := exists_par χ₁.primitiveCharacter
  have hminP1 : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 →
      |u.im| ≤ R + 1 → Work.LinnikContract.lamOf q ρ₁ ≤ (1 - u.re) * L :=
    fun u hu him => hminPrim χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim u hu
      (le_trans him hRW)
  have hk1P1 : ∀ t : ℝ, |t| ≤ R → (-logDeriv (DirichletCharacter.LFunction χ₁.primitiveCharacter)
      (sPt a L t)).re + P9.nearInvSum χ₁.conductor χ₁.primitiveCharacter (sPt a L t) δ
      ≤ (1 / 6 + ε₁) * L := fun t ht =>
    hk1Of χ₁.primitiveCharacter hφ₁ne hφ₁prim hN3 hlogN1 t ht
  have hJ1 : ∀ s : ℂ, ‖s‖ ≤ R + 2 → P9.invSqSum χ₁.conductor χ₁.primitiveCharacter s ≤ Cj :=
    fun s hs => hJOf χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim s hs
  have hCc1 : ∀ t : ℝ, |SigmaP3L q L (DirichletCharacter.changeLevel χ₁.conductor_dvd_level
        χ₁.primitiveCharacter) (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)
      - SigmaP3L χ₁.conductor L χ₁.primitiveCharacter (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)| ≤ Corr :=
    fun t => hCcOf χ₁.conductor_dvd_level χ₁.primitiveCharacter t
  have hρ₁re : ρ₁.re = 1 - (Work.LinnikContract.lamOf q ρ₁) / L := by
    rw [hlamOf_eq ρ₁]; field_simp; ring
  have hρ₀re : ρ₀.re = 1 - (Work.LinnikContract.lamOf q ρ₀) / L := by
    rw [hlamOf_eq ρ₀]; field_simp; ring
  have hm₀ : |ρ₀.im| ≤ R := by rw [hRdef]; linarith only [hγ₀, hH1]
  have hm₁ : |ρ₁.im| ≤ R := by rw [hRdef]; linarith only [hγ₁, hH1]
  have hm_a : |ρ₁.im - ρ₀.im| ≤ R := by
    have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp hγ₀
    rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
  have hm_f : |-(ρ₁.im + ρ₀.im)| ≤ R := by
    have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp hγ₀
    rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
  have hm_d : |2 * ρ₁.im - ρ₀.im| ≤ R := by
    have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp hγ₀
    rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
  have hm_g : |-(2 * ρ₁.im)| ≤ R := by
    have h1 := abs_le.mp hγ₁
    rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, hH1]
  have hm_e : |2 * ρ₁.im + ρ₀.im| ≤ R := by
    have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp hγ₀
    rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
  -- ### error budgets
  set e1 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he1def
  set e2 : ℝ := E2 + E3 + 2 * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) + Corr with he2def
  set e3 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he3def
  set e4 : ℝ := E2 + E3 + 2 * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) + Corr with he4def
  set e5 : ℝ := E2 + E3 + 8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L) + Corr with he5def
  set e6 : ℝ := E2 + E3 + 8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L) + Corr with he6def
  set e7 : ℝ := E2 + E3 + 8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L) + Corr with he7def
  set e8 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he8def
  -- ### the eight points
  set S1 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L 0) a (Work.LinnikContract.lamOf q ρ₁) with hS1'
  set S2 : ℝ := SigmaP3L q L χ₁ (sPt a L ρ₀.im) a (Work.LinnikContract.lamOf q ρ₁) with hS2'
  set S3 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L (ρ₁.im - ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS3'
  set S4 : ℝ := SigmaP3L q L χ₁ (sPt a L ρ₁.im) a (Work.LinnikContract.lamOf q ρ₁) with hS4'
  set S5 : ℝ := SigmaP3L q L (χ₁ ^ 2) (sPt a L (ρ₁.im + ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS5'
  set S6 : ℝ := SigmaP3L q L χ₁ (sPt a L (2 * ρ₁.im - ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS6'
  set S7 : ℝ := SigmaP3L q L (χ₁ ^ 2) (sPt a L (2 * ρ₁.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS7'
  set S8 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L (2 * ρ₁.im + ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS8'
  clear_value S1 S2 S3 S4 S5 S6 S7 S8
  -- ### point 1
  have hS1 : S1 ≤ P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / a) + e1 := by
    have hcc0 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) 0
    rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc0
    have hb := P3H.pointBoundPrincipalH (q := q) (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
      (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
      hCzZeta hC0b' hnzδ (s := sPt a L 0) (by simp [sPt]) (by rw [show (sPt a L 0).im = 0 by simp [sPt], abs_zero]; exact hRnn)
      (hSzeta 0).1 (hSzeta 0).2 hcc0
    have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L 0 - 1) * (L : ℂ)))).re
        = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / a) := by
      rw [P3_arg_eq_pole_split (a := a) (L := L) (t := 0) (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne]
      rw [zero_mul, PhiG_zero]
    rw [hpole] at hb
    linarith only [hb, hS1', he1def, hE2zdef, hE3zdef]
  -- ### point 2 (χ₁ at σ+iγ₀, kept {ρ₀,ρ₁})
  have hS2 : S2 ≤ -P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀))) - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
      + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e2 := by
    have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
      rw [← hzm1 ρ₁]; exact hmin.2.1
    have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
      rw [← hzm1 ρ₀]; exact hzm0
    have hT : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
        Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
      intro u hu
      rcases Finset.mem_insert.mp hu with h | h
      · rw [h]; exact hz₀
      · rw [Finset.mem_singleton.mp h]; exact hz₁
    have hTim : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ), |u.im| ≤ R + 1 := by
      intro u hu
      rcases Finset.mem_insert.mp hu with h | h
      · rw [h]; linarith only [hm₀, hRdef, hH1]
      · rw [Finset.mem_singleton.mp h]; linarith only [hm₁, hRdef, hH1]
    have hb := P3H.pointBoundQH (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
      (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
      (s := sPt a L ρ₀.im) (by simp [sPt]) (by simpa [sPt] using hm₀)
      (hk1P1 ρ₀.im hm₀) par₁ hpar₁0 hpar₁1
      (hSpr par₁ hpar₁2 ρ₀.im).1 (hSpr par₁ hpar₁2 ρ₀.im).2
      (hJ1 (sPt a L ρ₀.im) (P3H.norm_sPt_le_R ha haL hLpos hm₀))
      hminP1 ({ρ₀, ρ₁} : Finset ℂ) hT hTim (hCc1 ρ₀.im)
    have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₀.im - ρ₀) * (L : ℂ)))).re
        = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀))) := by
      rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im)
        (t := ρ₀.im) (ρ := ρ₀) hLne hρ₀re rfl]
      rw [sub_self, zero_mul, PhiG_zero]
    have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₀.im - ρ₁) * (L : ℂ)))).re
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
      rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
        (t := ρ₀.im) (ρ := ρ₁) hLne hρ₁re rfl]
      rw [show (ρ₀.im - ρ₁.im) * L = -Δ by rw [hΔdef]; ring]
      rw [PhiG_neg']
    have hsum : (∑ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
        (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₀.im - u) * (L : ℂ)))).re)
        = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀))) + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
      rw [Finset.sum_pair (Ne.symm hne), t1, t2]
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
    rw [Finset.card_pair (Ne.symm hne), Nat.cast_ofNat, hsum] at hb
    rw [neg_add] at hb
    linarith only [hb, hS2', he2def, hE2def, hE3def]
  -- ### point 3
  have hS3 : S3 ≤ P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ + e3 := by
    have hcc3 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) (ρ₁.im - ρ₀.im)
    rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc3
    have hb := P3H.pointBoundPrincipalH (q := q) (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
      (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
      hCzZeta hC0b' hnzδ (s := sPt a L (ρ₁.im - ρ₀.im))
      (by simp [sPt]) (by simpa [sPt] using hm_a)
      (hSzeta (ρ₁.im - ρ₀.im)).1 (hSzeta (ρ₁.im - ρ₀.im)).2 hcc3
    have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (ρ₁.im - ρ₀.im) - 1) * (L : ℂ)))).re
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ :=
      hΔdef ▸ P3_arg_eq_pole_split (a := a) (L := L) (t := ρ₁.im - ρ₀.im) (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne
    rw [hpole] at hb
    linarith only [hb, hS3', he3def, hE2zdef, hE3zdef]
  -- ### point 4 (χ₁ at σ+iγ₁, kept {ρ₀,ρ₁})
  have hS4 : S4 ≤ -P3R 1 - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
      + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e4 := by
    have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
      rw [← hzm1 ρ₁]; exact hmin.2.1
    have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
      rw [← hzm1 ρ₀]; exact hzm0
    have hT : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
        Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
      intro u hu
      rcases Finset.mem_insert.mp hu with h | h
      · rw [h]; exact hz₀
      · rw [Finset.mem_singleton.mp h]; exact hz₁
    have hTim : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ), |u.im| ≤ R + 1 := by
      intro u hu
      rcases Finset.mem_insert.mp hu with h | h
      · rw [h]; linarith only [hm₀, hRdef, hH1]
      · rw [Finset.mem_singleton.mp h]; linarith only [hm₁, hRdef, hH1]
    have hb := P3H.pointBoundQH (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
      (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
      (s := sPt a L ρ₁.im) (by simp [sPt]) (by simpa [sPt] using hm₁)
      (hk1P1 ρ₁.im hm₁) par₁ hpar₁0 hpar₁1
      (hSpr par₁ hpar₁2 ρ₁.im).1 (hSpr par₁ hpar₁2 ρ₁.im).2
      (hJ1 (sPt a L ρ₁.im) (P3H.norm_sPt_le_R ha haL hLpos hm₁))
      hminP1 ({ρ₀, ρ₁} : Finset ℂ) hT hTim (hCc1 ρ₁.im)
    have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₁.im - ρ₁) * (L : ℂ)))).re = P3R 1 := by
      rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
        (t := ρ₁.im) (ρ := ρ₁) hLne hρ₁re rfl]
      rw [sub_self, zero_mul, PhiG_zero]
      rw [show (a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₁)) = 1 by
        rw [div_self (ne_of_gt (lt_of_lt_of_le ha (le_add_of_nonneg_right hlam₁nn)))]]
    have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₁.im - ρ₀) * (L : ℂ)))).re
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ := by
      rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im)
        (t := ρ₁.im) (ρ := ρ₀) hLne hρ₀re rfl, hΔdef]
    have hsum : (∑ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
        (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₁.im - u) * (L : ℂ)))).re)
        = P3R 1 + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ := by
      rw [Finset.sum_pair (Ne.symm hne), t2, t1]
      ring
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
    rw [Finset.card_pair (Ne.symm hne), Nat.cast_ofNat, hsum] at hb
    rw [neg_add] at hb
    linarith only [hb, hS4', he4def, hE2def, hE3def]
  -- ### point 5 (χ₁² via conjugation, kept {ρ₁})
  have hconj5 : SigmaP3L q L (χ₁ ^ 2) (sPt a L (ρ₁.im + ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁)
      = SigmaP3L q L χ₁ (sPt a L (-(ρ₁.im + ρ₀.im))) a (Work.LinnikContract.lamOf q ρ₁) := by
    rw [P9.SigmaP3L_conj_eq (χ₁ ^ 2) L (sPt a L (ρ₁.im + ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁)]
    have hinv : (χ₁ ^ 2)⁻¹ = χ₁ := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ]
      exact hB
    rw [hinv]
    congr 1
    apply Complex.ext <;> simp [sPt, Complex.conj_re, Complex.conj_im]
  have hS5 : S5 ≤ -P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) ((2 * ρ₁.im + ρ₀.im) * L)
      + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e5 := by
    have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
      rw [← hzm1 ρ₁]; exact hmin.2.1
    have hT : ∀ u ∈ ({ρ₁} : Finset ℂ),
        Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
      intro u hu; rw [Finset.mem_singleton.mp hu]; exact hz₁
    have hTim : ∀ u ∈ ({ρ₁} : Finset ℂ), |u.im| ≤ R + 1 := by
      intro u hu; rw [Finset.mem_singleton.mp hu]; linarith only [hm₁, hRdef, hH1]
    have hb := P3H.pointBoundQH (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
      (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
      (s := sPt a L (-(ρ₁.im + ρ₀.im))) (by simp [sPt]) (by simpa [sPt] using hm_f)
      (hk1P1 (-(ρ₁.im + ρ₀.im)) hm_f) par₁ hpar₁0 hpar₁1
      (hSpr par₁ hpar₁2 (-(ρ₁.im + ρ₀.im))).1 (hSpr par₁ hpar₁2 (-(ρ₁.im + ρ₀.im))).2
      (hJ1 (sPt a L (-(ρ₁.im + ρ₀.im))) (P3H.norm_sPt_le_R ha haL hLpos hm_f))
      hminP1 ({ρ₁} : Finset ℂ) hT hTim (hCc1 (-(ρ₁.im + ρ₀.im)))
    have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (-(ρ₁.im + ρ₀.im)) - ρ₁) * (L : ℂ)))).re
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) ((2 * ρ₁.im + ρ₀.im) * L) := by
      rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
        (t := -(ρ₁.im + ρ₀.im)) (ρ := ρ₁) hLne hρ₁re rfl]
      rw [show (-(ρ₁.im + ρ₀.im) - ρ₁.im) * L = -((2 * ρ₁.im + ρ₀.im) * L) by ring]
      rw [PhiG_neg']
    have hsum : (∑ u ∈ ({ρ₁} : Finset ℂ),
        (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (-(ρ₁.im + ρ₀.im)) - u) * (L : ℂ)))).re)
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) ((2 * ρ₁.im + ρ₀.im) * L) := by
      rw [Finset.sum_singleton, t1]
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
    rw [Finset.card_singleton, Nat.cast_one, one_mul, hsum] at hb
    rw [← hconj5] at hb
    linarith only [hb, hS5', he5def, hE2def, hE3def]
  -- ### point 6 (χ₁ at σ+i(2γ₁-γ₀), kept {ρ₁})
  have hS6 : S6 ≤ -P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
      + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e6 := by
    have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
      rw [← hzm1 ρ₁]; exact hmin.2.1
    have hT : ∀ u ∈ ({ρ₁} : Finset ℂ),
        Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
      intro u hu; rw [Finset.mem_singleton.mp hu]; exact hz₁
    have hTim : ∀ u ∈ ({ρ₁} : Finset ℂ), |u.im| ≤ R + 1 := by
      intro u hu; rw [Finset.mem_singleton.mp hu]; linarith only [hm₁, hRdef, hH1]
    have hb := P3H.pointBoundQH (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
      (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
      (s := sPt a L (2 * ρ₁.im - ρ₀.im)) (by simp [sPt]) (by simpa [sPt] using hm_d)
      (hk1P1 (2 * ρ₁.im - ρ₀.im) hm_d) par₁ hpar₁0 hpar₁1
      (hSpr par₁ hpar₁2 (2 * ρ₁.im - ρ₀.im)).1 (hSpr par₁ hpar₁2 (2 * ρ₁.im - ρ₀.im)).2
      (hJ1 (sPt a L (2 * ρ₁.im - ρ₀.im)) (P3H.norm_sPt_le_R ha haL hLpos hm_d))
      hminP1 ({ρ₁} : Finset ℂ) hT hTim (hCc1 (2 * ρ₁.im - ρ₀.im))
    have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im - ρ₀.im) - ρ₁) * (L : ℂ)))).re
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
      rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
        (t := 2 * ρ₁.im - ρ₀.im) (ρ := ρ₁) hLne hρ₁re rfl,
        show (2 * ρ₁.im - ρ₀.im - ρ₁.im) * L = Δ by rw [hΔdef]; ring]
    have hsum : (∑ u ∈ ({ρ₁} : Finset ℂ),
        (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im - ρ₀.im) - u) * (L : ℂ)))).re)
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
      rw [Finset.sum_singleton, t1]
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
    rw [Finset.card_singleton, Nat.cast_one, one_mul, hsum] at hb
    linarith only [hb, hS6', he6def, hE2def, hE3def]
  -- ### point 7 (χ₁² via conjugation, kept {ρ₀})
  have hconj7 : SigmaP3L q L (χ₁ ^ 2) (sPt a L (2 * ρ₁.im)) a (Work.LinnikContract.lamOf q ρ₁)
      = SigmaP3L q L χ₁ (sPt a L (-(2 * ρ₁.im))) a (Work.LinnikContract.lamOf q ρ₁) := by
    rw [P9.SigmaP3L_conj_eq (χ₁ ^ 2) L (sPt a L (2 * ρ₁.im)) a (Work.LinnikContract.lamOf q ρ₁)]
    have hinv : (χ₁ ^ 2)⁻¹ = χ₁ := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ]
      exact hB
    rw [hinv]
    congr 1
    apply Complex.ext <;> simp [sPt, Complex.conj_re, Complex.conj_im]
  have hS7 : S7 ≤ -P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) ((2 * ρ₁.im + ρ₀.im) * L)
      + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e7 := by
    have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
      rw [← hzm1 ρ₀]; exact hzm0
    have hT : ∀ u ∈ ({ρ₀} : Finset ℂ),
        Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
      intro u hu; rw [Finset.mem_singleton.mp hu]; exact hz₀
    have hTim : ∀ u ∈ ({ρ₀} : Finset ℂ), |u.im| ≤ R + 1 := by
      intro u hu; rw [Finset.mem_singleton.mp hu]; linarith only [hm₀, hRdef, hH1]
    have hb := P3H.pointBoundQH (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
      (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
      (s := sPt a L (-(2 * ρ₁.im))) (by simp [sPt]) (by simpa [sPt] using hm_g)
      (hk1P1 (-(2 * ρ₁.im)) hm_g) par₁ hpar₁0 hpar₁1
      (hSpr par₁ hpar₁2 (-(2 * ρ₁.im))).1 (hSpr par₁ hpar₁2 (-(2 * ρ₁.im))).2
      (hJ1 (sPt a L (-(2 * ρ₁.im))) (P3H.norm_sPt_le_R ha haL hLpos hm_g))
      hminP1 ({ρ₀} : Finset ℂ) hT hTim (hCc1 (-(2 * ρ₁.im)))
    have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (-(2 * ρ₁.im)) - ρ₀) * (L : ℂ)))).re
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) ((2 * ρ₁.im + ρ₀.im) * L) := by
      rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im)
        (t := -(2 * ρ₁.im)) (ρ := ρ₀) hLne hρ₀re rfl]
      rw [show (-(2 * ρ₁.im) - ρ₀.im) * L = -((2 * ρ₁.im + ρ₀.im) * L) by ring]
      rw [PhiG_neg']
    have hsum : (∑ u ∈ ({ρ₀} : Finset ℂ),
        (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (-(2 * ρ₁.im)) - u) * (L : ℂ)))).re)
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) ((2 * ρ₁.im + ρ₀.im) * L) := by
      rw [Finset.sum_singleton, t1]
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at hb
    rw [Finset.card_singleton, Nat.cast_one, one_mul, hsum] at hb
    rw [← hconj7] at hb
    linarith only [hb, hS7', he7def, hE2def, hE3def]
  -- ### point 8 (χ₁³ = 1, principal at σ+i(2γ₁+γ₀))
  have hS8 : S8 ≤ P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a ((2 * ρ₁.im + ρ₀.im) * L) + e8 := by
    have hcc8 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) (2 * ρ₁.im + ρ₀.im)
    rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc8
    have hb := P3H.pointBoundPrincipalH (q := q) (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
      (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
      hCzZeta hC0b' hnzδ (s := sPt a L (2 * ρ₁.im + ρ₀.im))
      (by simp [sPt]) (by simpa [sPt] using hm_e)
      (hSzeta (2 * ρ₁.im + ρ₀.im)).1 (hSzeta (2 * ρ₁.im + ρ₀.im)).2 hcc8
    have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im + ρ₀.im) - 1) * (L : ℂ)))).re
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a ((2 * ρ₁.im + ρ₀.im) * L) :=
      P3_arg_eq_pole_split (a := a) (L := L) (t := 2 * ρ₁.im + ρ₀.im) (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne
    rw [hpole] at hb
    linarith only [hb, hS8', he8def, hE2zdef, hE3zdef]
  -- ### the assembly
  have hFcnn : 0 ≤ Fc := by rw [hFcdef]; positivity
  have hC0cnn : 0 ≤ C0c := by rw [hC0cdef]; positivity
  have h1C0 : ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ ≤ C0c := by
    rw [hC0cdef]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hαaup hLpos.le) hC₀pos.le
  have hE1 : e1 ≤ Ee := by rw [he1def]; exact heEz _ (by linarith only [h1C0, hFcnn])
  have hE2 : e2 ≤ Ee := by rw [he2def]; exact heE _ (by have h := hcFar 2 (by norm_num); linarith only [h, hC0cnn])
  have hE4 : e4 ≤ Ee := by rw [he4def]; exact heE _ (by have h := hcFar 2 (by norm_num); linarith only [h, hC0cnn])
  have hE5 : e5 ≤ Ee := by rw [he5def]; exact heE _ (by have h := hcFar 1 (by norm_num); linarith only [h, hC0cnn])
  have hE6 : e6 ≤ Ee := by rw [he6def]; exact heE _ (by have h := hcFar 1 (by norm_num); linarith only [h, hC0cnn])
  have hE7 : e7 ≤ Ee := by rw [he7def]; exact heE _ (by have h := hcFar 1 (by norm_num); linarith only [h, hC0cnn])
  have hE8 : e8 ≤ Ee := by rw [he8def]; exact heEz _ (by linarith only [h1C0, hFcnn])
  have hcomb : 0 ≤ (K ^ 2 + 1 / 2) * (S1 + S2) + K * (S3 + 2 * S4 + S5)
      + (1 / 4) * (S6 + 2 * S7 + S8) + 0 := by
    have h0 := P9.HbCombinationL_nonneg (q := q) χ₁ K (1 + a / L) ρ₀.im ρ₁.im a (Work.LinnikContract.lamOf q ρ₁)
      hK.le (by have h : 0 < a / L := div_pos ha hLpos; linarith only [h]) ha hlam₁nn
    rw [Work.ZeroFreeTables.HbCombinationL, ← hLdef, hB] at h0
    push_cast at h0
    simp only [hS1', hS2', hS3', hS4', hS5', hS6', hS7', hS8', sPt, Complex.ofReal_zero,
      zero_mul, add_zero]
    push_cast
    exact h0
  have habs : (K ^ 2 + 1 / 2) * (e1 + e2) + K * (e3 + 2 * e4 + e5)
      + (1 / 4) * (e6 + 2 * e7 + e8) + 0 + (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ * (K ^ 2 + 3 * K + 5 / 4)
      ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε := by
    have hsum := Work.ZeroFreeTables.HB94.Lam0GeEngine.sumErr_le hK.le hE1 hE2 hE1 hE4 hE5 hE6 hE7 hE8
    have hε := mul_le_mul_of_nonneg_left hε₁bud hα0
    have hmain : 2 * (K + 1) ^ 2 * Ee ≤ a * ε / 2 := hEebound
    have h54 : (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ * (K ^ 2 + 3 * K + 5 / 4)
        ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * (ε / 4) := by
      have h1 : (K ^ 2 + 3 * K + 5 / 4 : ℝ) ≤ K ^ 2 + 3 * K + 3 / 2 := by norm_num
      have h2 : 0 ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ := by positivity
      calc (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ * (K ^ 2 + 3 * K + 5 / 4)
          ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ * (K ^ 2 + 3 * K + 3 / 2) :=
            mul_le_mul_of_nonneg_left h1 h2
        _ = (a + (Work.LinnikContract.lamOf q ρ₁)) * (ε₁ * (K ^ 2 + 3 * K + 3 / 2)) := by ring
        _ ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * (ε / 4) :=
            mul_le_mul_of_nonneg_left hε₁bud hα0
    have hfin : a * ε / 2 + (a + (Work.LinnikContract.lamOf q ρ₁)) * (ε / 4)
        ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε := by
      linarith only [mul_nonneg hlam₁nn (le_of_lt ‹0 < ε›), mul_pos ha ‹0 < ε›]
    linarith only [hsum, hmain, hε, hfin, h54]
  exact Work.ZeroFreeTables.HB94.Lam0GeEngine.caseB_bridge (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁))
    (lam₀ := (Work.LinnikContract.lamOf q ρ₀)) (K := K) (ε := ε) (ε₁ := ε₁)
    (Δ := Δ) (tB := (2 * ρ₁.im + ρ₀.im) * L)
    (S1 := S1) (S2 := S2) (S3 := S3) (S4 := S4) (S5 := S5) (S6 := S6)
    (S7 := S7) (S8 := S8) (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4) (e5 := e5)
    (e6 := e6) (e7 := e7) (e8 := e8) (corr := 0)
    hK.le hα0 hS1 hS2 hS3 hS4 hS5 hS6 hS7 hS8 hcomb
    (P3.P3Bounds.2 a (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₀) K Δ
      ha hK hlam₁nn hlam₁lam₀ (side913 ha hK (by linarith only [ha, hlam₁nn]) (by linarith only [ha, hlam₀nn]) hcond).1)
    ((P9.rescale_variants.2.1) a (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₀) K
      ((2 * ρ₁.im + ρ₀.im) * L) ha hlam₁nn hlam₁lam₀ hK
      (side913 ha hK (by linarith only [ha, hlam₁nn]) (by linarith only [ha, hlam₀nn]) hcond).2.1)
    habs

private theorem rect_case2
  (a : ℝ)
  (K : ℝ)
  (ε : ℝ)
  (ha : (0 : ℝ) < a)
  (hK : (0 : ℝ) < K)
  (hε : (0 : ℝ) < ε)
  (H : ℝ)
  (W : ℝ)
  (hH1 : (1 : ℝ) ≤ H)
  (R : ℝ)
  (hRdef : R = (3 : ℝ) * H)
  (hRnn : (0 : ℝ) ≤ R)
  (hRW : R + (1 : ℝ) ≤ W)
  (hΘ : (0 : ℝ) ≤ R + (2 : ℝ))
  (ε₁ : ℝ)
  (hε₁pos : (0 : ℝ) < ε₁)
  (hε₁bud : ε₁ * (K ^ (2 : ℕ) + (3 : ℝ) * K + (3 / 2 : ℝ)) ≤ ε / (4 : ℝ))
  (Ct : ℝ)
  (hCtpos : (0 : ℝ) < Ct)
  (C₀ : ℝ)
  (hC₀pos : (0 : ℝ) < C₀)
  (Cc : ℝ)
  (hCcpos : (0 : ℝ) < Cc)
  (Cp : ℝ)
  (hCpnn : (0 : ℝ) ≤ Cp)
  (Cz : ℝ)
  (hCzpos : (0 : ℝ) < Cz)
  (Cn : ℝ)
  (hCnpos : (0 : ℝ) < Cn)
  (δ : ℝ)
  (hδpos : (0 : ℝ) < δ)
  (hδlt1 : δ < (1 : ℝ))
  (aup : ℝ)
  (hauppos : (0 : ℝ) < aup)
  (qabs : ℕ)
  (habs : ∀ (q : ℕ),
      qabs ≤ q →
        (2 : ℝ) * (K + (1 : ℝ)) ^ (2 : ℕ) *
            (aup / Real.log (↑q : ℝ) * C₀ +
                    aup ^ (2 : ℕ) / Real.log (↑q : ℝ) ^ (2 : ℕ) *
                      (((1 : ℝ) + (4 : ℝ) / δ ^ (2 : ℕ)) * (Cn * (Real.log (↑q : ℝ) + (6 : ℝ)) + Cz) + Ct) +
                  (2 / 3 : ℝ) * (aup ^ (3 : ℕ) / Real.log (↑q : ℝ) ^ (3 : ℕ)) *
                    ((2 : ℝ) / δ * ((1 : ℝ) + (4 : ℝ) / δ ^ (2 : ℕ)) * (Cn * (Real.log (↑q : ℝ) + (6 : ℝ)) + Cz) + Ct) +
                Cc / Real.log (↑q : ℝ) *
                  (aup * Cp * Real.log (Real.log (↑q : ℝ)) ^ (2 : ℕ) +
                      aup ^ (2 : ℕ) / Real.log (↑q : ℝ) * Cp * Real.log (Real.log (↑q : ℝ)) ^ (3 : ℕ) +
                    aup ^ (3 : ℕ) / Real.log (↑q : ℝ) ^ (2 : ℕ) * Cp * Real.log (Real.log (↑q : ℝ)) ^ (4 : ℕ)) +
              (64 : ℝ) * aup / (δ * Real.log (↑q : ℝ))) ≤
          a * ε / (2 : ℝ))
  (q : ℕ)
  [hqne : NeZero q]
  (χ₁ : DirichletCharacter ℂ q)
  (ρ₁ : ℂ)
  (ρ₀ : ℂ)
  (hmin : IsMinWideAt H W χ₁ ρ₁)
  (hzm0 : LinnikContract.zeroMult χ₁ ρ₀ ≠ (0 : ℕ))
  (hγ₀ : |ρ₀.im| ≤ H)
  (hne : ρ₁ ≠ ρ₀)
  (hcond : cond913 (LinnikContract.lamOf q ρ₁) (LinnikContract.lamOf q ρ₀) a K)
  (L : ℝ)
  (hLdef : L = Real.log (↑q : ℝ))
  (haL : a ≤ L)
  (hLt : (1 : ℝ) < L)
  (hLpos : (0 : ℝ) < L)
  (hLne : L ≠ (0 : ℝ))
  (hL1 : (1 : ℝ) ≤ L)
  (hlogLnn : (0 : ℝ) ≤ Real.log L)
  (h1aL : (1 : ℝ) ≤ a * Real.log L)
  (haδL : (2 : ℝ) * a ≤ δ * L)
  (Cj : ℝ)
  (hCjnn : (0 : ℝ) ≤ Cj)
  (Corr : ℝ)
  (hlam₁nn : (0 : ℝ) ≤ LinnikContract.lamOf q ρ₁)
  (hlam₀nn : (0 : ℝ) ≤ LinnikContract.lamOf q ρ₀)
  (hγ₁ : |ρ₁.im| ≤ H)
  (hlam₁lam₀ : LinnikContract.lamOf q ρ₁ ≤ LinnikContract.lamOf q ρ₀)
  (hχ₁ne : χ₁ ≠ (1 : DirichletCharacter ℂ q))
  (hα0 : (0 : ℝ) ≤ a + LinnikContract.lamOf q ρ₁)
  (hαaup : a + LinnikContract.lamOf q ρ₁ ≤ aup)
  (hlamOf_eq : ∀ (u : ℂ), LinnikContract.lamOf q u = ((1 : ℝ) - u.re) * L)
  (hminPrim : ∀ {N : ℕ} [inst : NeZero N],
      N ∣ q →
        ∀ (φ : DirichletCharacter ℂ N),
          φ ≠ (1 : DirichletCharacter ℂ N) →
            φ.IsPrimitive →
              ∀ (u : ℂ),
                LinnikContract.zeroMult φ u ≠ (0 : ℕ) → |u.im| ≤ W → LinnikContract.lamOf q ρ₁ ≤ ((1 : ℝ) - u.re) * L)
  (hSpr : ∀ par ≤ (2 : ℕ),
      ∀ (t : ℝ),
        |∑' (n : ℕ), (((1 : ℂ) / (sPt a L t + (↑(par + (2 : ℕ) * n) : ℂ))) ^ (2 : ℕ)).re| ≤ Ct ∧
          |∑' (n : ℕ), (((1 : ℂ) / (sPt a L t + (↑(par + (2 : ℕ) * n) : ℂ))) ^ (3 : ℕ)).re| ≤ Ct)
  (hSzeta : ∀ (t : ℝ),
      |∑' (n : ℕ), (((1 : ℂ) / (sPt a L t + (↑((2 : ℕ) * (n + (1 : ℕ))) : ℂ))) ^ (2 : ℕ)).re| ≤ Ct ∧
        |∑' (n : ℕ), (((1 : ℂ) / (sPt a L t + (↑((2 : ℕ) * (n + (1 : ℕ))) : ℂ))) ^ (3 : ℕ)).re| ≤ Ct)
  (hCzZeta : ∀ (s : ℂ),
      ‖s‖ ≤ R + (2 : ℝ) →
        ∑' (u : ℂ), (↑(analyticOrderNatAt completedRiemannZeta u) : ℝ) * ((1 : ℝ) / ((1 : ℝ) + ‖s - u‖ ^ (2 : ℕ))) ≤ Cz)
  (hC0b' : ∀ (s : ℂ),
      (1 : ℝ) < s.re →
        s.re ≤ (2 : ℝ) → |s.im| ≤ R + (2 : ℝ) → (-logDeriv riemannZeta s).re ≤ ((1 : ℂ) / (s - (1 : ℂ))).re + C₀)
  (hnzδ : ∀ (t : ℝ), |t| ≤ R → ∀ (u : ℂ), riemannZeta u = (0 : ℂ) → δ < ‖(1 : ℂ) + (↑t : ℂ) * I - u‖)
  (hJOf : ∀ {N : ℕ} [inst : NeZero N],
      N ∣ q →
        ∀ (φ : DirichletCharacter ℂ N),
          φ ≠ (1 : DirichletCharacter ℂ N) → φ.IsPrimitive → ∀ (s : ℂ), ‖s‖ ≤ R + (2 : ℝ) → invSqSum N φ s ≤ Cj)
  (hCcOf : ∀ {N : ℕ} [inst : NeZero N] (hNq : N ∣ q) (φ : DirichletCharacter ℂ N) (t : ℝ),
      |SigmaP3L q L ((changeLevel hNq : DirichletCharacter ℂ N → DirichletCharacter ℂ q) φ) (sPt a L t) a
              (LinnikContract.lamOf q ρ₁) -
            SigmaP3L N L φ (sPt a L t) a (LinnikContract.lamOf q ρ₁)| ≤
        Corr)
  (hk1Of : ∀ {N : ℕ} [inst : NeZero N] (φ : DirichletCharacter ℂ N),
      φ ≠ (1 : DirichletCharacter ℂ N) →
        φ.IsPrimitive →
          (3 : ℕ) ≤ N →
            Real.log (↑N : ℝ) ≤ L →
              ∀ (t : ℝ),
                |t| ≤ R →
                  (-logDeriv (LFunction φ) (sPt a L t)).re + nearInvSum N φ (sPt a L t) δ ≤ ((1 / 6 : ℝ) + ε₁) * L)
  (hN3 : (3 : ℕ) ≤ χ₁.conductor)
  (Δ : ℝ)
  (hΔdef : Δ = (ρ₁.im - ρ₀.im) * L)
  (β : ℝ)
  (γ : ℝ)
  (E2 : ℝ)
  (hE2def : E2 = (a + LinnikContract.lamOf q ρ₁) ^ (2 : ℕ) / L ^ (2 : ℕ) * (((1 : ℝ) + (4 : ℝ) / δ ^ (2 : ℕ)) * Cj + Ct))
  (E3 : ℝ)
  (hE3def : E3 =
      (2 / 3 : ℝ) * ((a + LinnikContract.lamOf q ρ₁) ^ (3 : ℕ) / L ^ (3 : ℕ)) *
        ((2 : ℝ) / δ * ((1 : ℝ) + (4 : ℝ) / δ ^ (2 : ℕ)) * Cj + Ct))
  (E2z : ℝ)
  (hE2zdef : E2z = (a + LinnikContract.lamOf q ρ₁) ^ (2 : ℕ) / L ^ (2 : ℕ) * (((1 : ℝ) + (4 : ℝ) / δ ^ (2 : ℕ)) * Cz + Ct))
  (E3z : ℝ)
  (hE3zdef : E3z =
      (2 / 3 : ℝ) * ((a + LinnikContract.lamOf q ρ₁) ^ (3 : ℕ) / L ^ (3 : ℕ)) *
        ((2 : ℝ) / δ * ((1 : ℝ) + (4 : ℝ) / δ ^ (2 : ℕ)) * Cz + Ct))
  (C0c : ℝ)
  (hC0cdef : C0c = aup / L * C₀)
  (Fc : ℝ)
  (hFcdef : Fc = (64 : ℝ) * aup / (δ * L))
  (Ee : ℝ)
  (hcFar : ∀ k ≤ (4 : ℕ), (↑k : ℝ) * ((8 : ℝ) * (a + LinnikContract.lamOf q ρ₁) / (δ * L)) ≤ Fc)
  (heE : ∀ e ≤ E2 + E3 + Fc + Corr + C0c, e ≤ Ee)
  (heEz : ∀ e ≤ E2z + E3z + Fc + Corr + C0c, e ≤ Ee)
  (hEebound : (2 : ℝ) * (K + (1 : ℝ)) ^ (2 : ℕ) * Ee ≤ a * ε / (2 : ℝ))
  (hFcnn : (0 : ℝ) ≤ Fc)
  (hC0cnn : (0 : ℝ) ≤ C0c)
  (hlogNOf : ∀ {N : ℕ}, N ∣ q → N ≠ (0 : ℕ) → Real.log (↑N : ℝ) ≤ L)
  (hC : ¬χ₁ ^ (2 : ℕ) = (1 : DirichletCharacter ℂ q))
  (hB : ¬χ₁ ^ (3 : ℕ) = (1 : DirichletCharacter ℂ q)) :
  ineq913 (LinnikContract.lamOf q ρ₁) (LinnikContract.lamOf q ρ₀) a K ε := by
  have hχ2 : χ₁ ^ 2 ≠ 1 := hC
  have hχ3 : χ₁ ^ 3 ≠ 1 := hB
  haveI hN1 : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  have hφ₁ne : χ₁.primitiveCharacter ≠ 1 := by
    intro hh
    exact hχ₁ne (by rw [← DirichletCharacter.changeLevel_primitiveCharacter χ₁, hh,
      DirichletCharacter.changeLevel_one χ₁.conductor_dvd_level])
  have hφ₁prim : χ₁.primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive χ₁
  have hlogN1 : Real.log ((χ₁.conductor : ℕ) : ℝ) ≤ L :=
    hlogNOf χ₁.conductor_dvd_level χ₁.conductor_ne_zero
  have hzm1 : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁ u
      = Work.LinnikContract.zeroMult χ₁.primitiveCharacter u := by
    intro u
    have h := Work.ZeroFreeTables.Table4.zeroMult_changeLevel χ₁.conductor_dvd_level
      χ₁.primitiveCharacter u
    rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
    exact h
  obtain ⟨par₁, hpar₁2, hpar₁0, hpar₁1⟩ := exists_par χ₁.primitiveCharacter
  have hminP1 : ∀ u : ℂ, Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 →
      |u.im| ≤ R + 1 → Work.LinnikContract.lamOf q ρ₁ ≤ (1 - u.re) * L :=
    fun u hu him => hminPrim χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim u hu
      (le_trans him hRW)
  have hk1P1 : ∀ t : ℝ, |t| ≤ R → (-logDeriv (DirichletCharacter.LFunction χ₁.primitiveCharacter)
      (sPt a L t)).re + P9.nearInvSum χ₁.conductor χ₁.primitiveCharacter (sPt a L t) δ
      ≤ (1 / 6 + ε₁) * L := fun t ht =>
    hk1Of χ₁.primitiveCharacter hφ₁ne hφ₁prim hN3 hlogN1 t ht
  have hJ1 : ∀ s : ℂ, ‖s‖ ≤ R + 2 → P9.invSqSum χ₁.conductor χ₁.primitiveCharacter s ≤ Cj :=
    fun s hs => hJOf χ₁.conductor_dvd_level χ₁.primitiveCharacter hφ₁ne hφ₁prim s hs
  have hCc1 : ∀ t : ℝ, |SigmaP3L q L (DirichletCharacter.changeLevel χ₁.conductor_dvd_level
        χ₁.primitiveCharacter) (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)
      - SigmaP3L χ₁.conductor L χ₁.primitiveCharacter (sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)| ≤ Corr :=
    fun t => hCcOf χ₁.conductor_dvd_level χ₁.primitiveCharacter t
  have hρ₁re : ρ₁.re = 1 - (Work.LinnikContract.lamOf q ρ₁) / L := by
    rw [hlamOf_eq ρ₁]; field_simp; ring
  have hρ₀re : ρ₀.re = 1 - (Work.LinnikContract.lamOf q ρ₀) / L := by
    rw [hlamOf_eq ρ₀]; field_simp; ring
  have hm₁ : |ρ₁.im| ≤ R := by rw [hRdef]; linarith only [hγ₁, hH1]
  have hm₀ : |ρ₀.im| ≤ R := by rw [hRdef]; linarith only [hγ₀, hH1]
  have hm_a : |ρ₁.im - ρ₀.im| ≤ R := by
    have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp hγ₀
    rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
  have hm_b : |ρ₁.im + ρ₀.im| ≤ R := by
    have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp hγ₀
    rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
  have hm_g : |2 * ρ₁.im| ≤ R := by
    have h1 := abs_le.mp hγ₁
    rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, hH1]
  have hm_d : |2 * ρ₁.im - ρ₀.im| ≤ R := by
    have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp hγ₀
    rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
  have hm_e : |2 * ρ₁.im + ρ₀.im| ≤ R := by
    have h1 := abs_le.mp hγ₁; have h0 := abs_le.mp hγ₀
    rw [hRdef, abs_le]; constructor <;> linarith only [h1.1, h1.2, h0.1, h0.2, hH1]
  have hcc0 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) 0
  rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc0
  -- ### error budgets
  set e1 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he1def
  set e2 : ℝ := E2 + E3 + 2 * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) + Corr with he2def
  set e3 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ + E2z + E3z + Corr with he3def
  set e4 : ℝ := E2 + E3 + 2 * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) + Corr with he4def
  set e5 : ℝ := E2 + E3 + Corr with he5def
  set e6 : ℝ := E2 + E3 + 8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L) + Corr with he6def
  set e7 : ℝ := E2 + E3 + Corr with he7def
  set e8 : ℝ := E2 + E3 + Corr with he8def
  -- ### the eight points
  set S1 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L 0) a (Work.LinnikContract.lamOf q ρ₁) with hS1'
  set S2 : ℝ := SigmaP3L q L χ₁ (sPt a L ρ₀.im) a (Work.LinnikContract.lamOf q ρ₁) with hS2'
  set S3 : ℝ := SigmaP3L q L (1 : DirichletCharacter ℂ q) (sPt a L (ρ₁.im - ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS3'
  set S4 : ℝ := SigmaP3L q L χ₁ (sPt a L ρ₁.im) a (Work.LinnikContract.lamOf q ρ₁) with hS4'
  set S5 : ℝ := SigmaP3L q L (χ₁ ^ 2) (sPt a L (ρ₁.im + ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS5'
  set S6 : ℝ := SigmaP3L q L χ₁ (sPt a L (2 * ρ₁.im - ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS6'
  set S7 : ℝ := SigmaP3L q L (χ₁ ^ 2) (sPt a L (2 * ρ₁.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS7'
  set S8 : ℝ := SigmaP3L q L (χ₁ ^ 3) (sPt a L (2 * ρ₁.im + ρ₀.im)) a (Work.LinnikContract.lamOf q ρ₁) with hS8'
  clear_value S1 S2 S3 S4 S5 S6 S7 S8
  -- ### point 1: the principal character at σ
  have hS1 : S1 ≤ P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / a) + e1 := by
    have hb := P3H.pointBoundPrincipalH (q := q) (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
      (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
      hCzZeta hC0b' hnzδ (s := sPt a L 0) (by simp [sPt]) (by rw [show (sPt a L 0).im = 0 by simp [sPt], abs_zero]; exact hRnn)
      (hSzeta 0).1 (hSzeta 0).2 (by rw [hS1'] at hcc0; exact hcc0)
    have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L 0 - 1) * (L : ℂ)))).re
        = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / a) := by
      rw [P3_arg_eq_pole_split (a := a) (L := L) (t := 0) (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne]
      rw [zero_mul, PhiG_zero]
    rw [hpole] at hb
    linarith only [hb, hS1', he1def, hE2zdef, hE3zdef]
  -- ### point 2: χ₁ at σ + iγ₀, kept {ρ₀, ρ₁}
  have hS2 : S2 ≤ -P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀))) - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
      + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e2 := by
    have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
      rw [← hzm1 ρ₁]; exact hmin.2.1
    have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
      rw [← hzm1 ρ₀]; exact hzm0
    have hT : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
        Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
      intro u hu
      rcases Finset.mem_insert.mp hu with h | h
      · rw [h]; exact hz₀
      · rw [Finset.mem_singleton.mp h]; exact hz₁
    have hTim : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ), |u.im| ≤ R + 1 := by
      intro u hu
      rcases Finset.mem_insert.mp hu with h | h
      · rw [h]; linarith only [hm₀, hRdef, hH1]
      · rw [Finset.mem_singleton.mp h]; linarith only [hm₁, hRdef, hH1]
    have hb := P3H.pointBoundQH (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
      (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
      (s := sPt a L ρ₀.im) (by simp [sPt]) (by simpa [sPt] using hm₀)
      (hk1P1 ρ₀.im hm₀) par₁ hpar₁0 hpar₁1
      (hSpr par₁ hpar₁2 ρ₀.im).1 (hSpr par₁ hpar₁2 ρ₀.im).2
      (hJ1 (sPt a L ρ₀.im) (P3H.norm_sPt_le_R ha haL hLpos hm₀))
      hminP1 ({ρ₀, ρ₁} : Finset ℂ) hT hTim (hCc1 ρ₀.im)
    have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₀.im - ρ₀) * (L : ℂ)))).re
        = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀))) := by
      rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im)
        (t := ρ₀.im) (ρ := ρ₀) hLne hρ₀re rfl]
      rw [sub_self, zero_mul, PhiG_zero]
    have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₀.im - ρ₁) * (L : ℂ)))).re
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
      rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
        (t := ρ₀.im) (ρ := ρ₁) hLne hρ₁re rfl]
      rw [show (ρ₀.im - ρ₁.im) * L = -Δ by rw [hΔdef]; ring]
      rw [PhiG_neg']
    have hsum : (∑ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
        (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₀.im - u) * (L : ℂ)))).re)
        = P3R ((a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₀))) + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
      rw [Finset.sum_pair (Ne.symm hne), t1, t2]
    rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS2'] at hb
    rw [Finset.card_pair (Ne.symm hne), Nat.cast_ofNat, hsum] at hb
    rw [neg_add] at hb
    linarith only [hb, hS2', he2def, hE2def, hE3def]
  -- ### point 3: the principal character at σ + i(γ₁-γ₀)
  have hS3 : S3 ≤ P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ + e3 := by
    have hcc3 := hCcOf (N := 1) (one_dvd q) (1 : DirichletCharacter ℂ 1) (ρ₁.im - ρ₀.im)
    rw [DirichletCharacter.changeLevel_one (one_dvd q)] at hcc3
    have hb := P3H.pointBoundPrincipalH (q := q) (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (δ := δ) (L := L)
      (Ct := Ct) (Cz := Cz) (C₀ := C₀) (Cc := Corr) ha hlam₁nn hδpos hδlt1 hLt haδL haL
      hCzZeta hC0b' hnzδ (s := sPt a L (ρ₁.im - ρ₀.im))
      (by simp [sPt]) (by simpa [sPt] using hm_a)
      (hSzeta (ρ₁.im - ρ₀.im)).1 (hSzeta (ρ₁.im - ρ₀.im)).2 hcc3
    have hpole : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (ρ₁.im - ρ₀.im) - 1) * (L : ℂ)))).re
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) a Δ :=
      hΔdef ▸ P3_arg_eq_pole_split (a := a) (L := L) (t := ρ₁.im - ρ₀.im)
        (lam := (Work.LinnikContract.lamOf q ρ₁)) hLne
    rw [hpole] at hb
    linarith only [hb, hS3', he3def, hE2zdef, hE3zdef]
  -- ### point 4: χ₁ at σ + iγ₁, kept {ρ₀, ρ₁}
  have hS4 : S4 ≤ -P3R 1 - P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ
      + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e4 := by
    have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
      rw [← hzm1 ρ₁]; exact hmin.2.1
    have hz₀ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₀ ≠ 0 := by
      rw [← hzm1 ρ₀]; exact hzm0
    have hT : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
        Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
      intro u hu
      rcases Finset.mem_insert.mp hu with h | h
      · rw [h]; exact hz₀
      · rw [Finset.mem_singleton.mp h]; exact hz₁
    have hTim : ∀ u ∈ ({ρ₀, ρ₁} : Finset ℂ), |u.im| ≤ R + 1 := by
      intro u hu
      rcases Finset.mem_insert.mp hu with h | h
      · rw [h]; linarith only [hm₀, hRdef, hH1]
      · rw [Finset.mem_singleton.mp h]; linarith only [hm₁, hRdef, hH1]
    have hb := P3H.pointBoundQH (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
      (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
      (s := sPt a L ρ₁.im) (by simp [sPt]) (by simpa [sPt] using hm₁)
      (hk1P1 ρ₁.im hm₁) par₁ hpar₁0 hpar₁1
      (hSpr par₁ hpar₁2 ρ₁.im).1 (hSpr par₁ hpar₁2 ρ₁.im).2
      (hJ1 (sPt a L ρ₁.im) (P3H.norm_sPt_le_R ha haL hLpos hm₁))
      hminP1 ({ρ₀, ρ₁} : Finset ℂ) hT hTim (hCc1 ρ₁.im)
    have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₁.im - ρ₁) * (L : ℂ)))).re = P3R 1 := by
      rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
        (t := ρ₁.im) (ρ := ρ₁) hLne hρ₁re rfl]
      rw [sub_self, zero_mul, PhiG_zero]
      rw [show (a + (Work.LinnikContract.lamOf q ρ₁)) / (a + (Work.LinnikContract.lamOf q ρ₁)) = 1 by
        rw [div_self (ne_of_gt (lt_of_lt_of_le ha (le_add_of_nonneg_right hlam₁nn)))]]
    have t2 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₁.im - ρ₀) * (L : ℂ)))).re
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ := by
      rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₀)) (gam := ρ₀.im)
        (t := ρ₁.im) (ρ := ρ₀) hLne hρ₀re rfl, hΔdef]
    have hsum : (∑ u ∈ ({ρ₀, ρ₁} : Finset ℂ),
        (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L ρ₁.im - u) * (L : ℂ)))).re)
        = P3R 1 + P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₀)) Δ := by
      rw [Finset.sum_pair (Ne.symm hne), t2, t1]
      ring
    rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS4'] at hb
    rw [Finset.card_pair (Ne.symm hne), Nat.cast_ofNat, hsum] at hb
    rw [neg_add] at hb
    linarith only [hb, hS4', he4def, hE2def, hE3def]
  -- ### point 5: χ₁² at σ + i(γ₁+γ₀), nothing kept
  haveI hN2 : NeZero (χ₁ ^ 2).conductor := ⟨(χ₁ ^ 2).conductor_ne_zero⟩
  have hφ₂ne : (χ₁ ^ 2).primitiveCharacter ≠ 1 := by
    intro hh
    exact hχ2 (by rw [← DirichletCharacter.changeLevel_primitiveCharacter (χ₁ ^ 2), hh,
      DirichletCharacter.changeLevel_one (χ₁ ^ 2).conductor_dvd_level])
  have hφ₂prim : (χ₁ ^ 2).primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive (χ₁ ^ 2)
  have hlogN2 : Real.log (((χ₁ ^ 2).conductor : ℕ) : ℝ) ≤ L :=
    hlogNOf (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).conductor_ne_zero
  have hN2_3 : 3 ≤ (χ₁ ^ 2).conductor :=
    Work.LinnikAreas2.three_le_conductor (χ₁ ^ 2) hχ2
  have hS5 : S5 ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e5 := by
    obtain ⟨par₂, hpar₂2, hpar₂0, hpar₂1⟩ := exists_par (χ₁ ^ 2).primitiveCharacter
    have hb := P3H.pointBoundQH (q := q) (N := (χ₁ ^ 2).conductor)
      (hNq := (χ₁ ^ 2).conductor_dvd_level) (φ := (χ₁ ^ 2).primitiveCharacter) hφ₂ne
      hφ₂prim ha hlam₁nn hδpos hδlt1 hLt haδL
      (s := sPt a L (ρ₁.im + ρ₀.im)) (by simp [sPt]) (by simpa [sPt] using hm_b)
      (hk1Of (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim hN2_3 hlogN2 (ρ₁.im + ρ₀.im) hm_b)
      par₂ hpar₂0 hpar₂1
      (hSpr par₂ hpar₂2 (ρ₁.im + ρ₀.im)).1 (hSpr par₂ hpar₂2 (ρ₁.im + ρ₀.im)).2
      (hJOf (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim
        (sPt a L (ρ₁.im + ρ₀.im)) (P3H.norm_sPt_le_R ha haL hLpos hm_b))
      (fun u hu him => hminPrim (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim u hu (le_trans him hRW))
      (∅ : Finset ℂ) (by simp) (by simp)
      (hCcOf (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter (ρ₁.im + ρ₀.im))
    have hsum : (∑ u ∈ (∅ : Finset ℂ),
        (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (ρ₁.im + ρ₀.im) - u) * (L : ℂ)))).re) = 0 :=
      Finset.sum_empty
    rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS5'] at hb
    rw [hsum, Finset.card_empty, Nat.cast_zero, zero_mul, neg_zero, zero_add, add_zero] at hb
    linarith only [hb, hS5', he5def, hE2def, hE3def]
  -- ### point 6: χ₁ at σ + i(2γ₁-γ₀), kept {ρ₁}
  have hS6 : S6 ≤ -P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ
      + (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e6 := by
    have hz₁ : Work.LinnikContract.zeroMult χ₁.primitiveCharacter ρ₁ ≠ 0 := by
      rw [← hzm1 ρ₁]; exact hmin.2.1
    have hT : ∀ u ∈ ({ρ₁} : Finset ℂ),
        Work.LinnikContract.zeroMult χ₁.primitiveCharacter u ≠ 0 := by
      intro u hu; rw [Finset.mem_singleton.mp hu]; exact hz₁
    have hTim : ∀ u ∈ ({ρ₁} : Finset ℂ), |u.im| ≤ R + 1 := by
      intro u hu; rw [Finset.mem_singleton.mp hu]; linarith only [hm₁, hRdef, hH1]
    have hb := P3H.pointBoundQH (q := q) (N := χ₁.conductor) (hNq := χ₁.conductor_dvd_level)
      (φ := χ₁.primitiveCharacter) hφ₁ne hφ₁prim ha hlam₁nn hδpos hδlt1 hLt haδL
      (s := sPt a L (2 * ρ₁.im - ρ₀.im)) (by simp [sPt]) (by simpa [sPt] using hm_d)
      (hk1P1 (2 * ρ₁.im - ρ₀.im) hm_d) par₁ hpar₁0 hpar₁1
      (hSpr par₁ hpar₁2 (2 * ρ₁.im - ρ₀.im)).1 (hSpr par₁ hpar₁2 (2 * ρ₁.im - ρ₀.im)).2
      (hJ1 (sPt a L (2 * ρ₁.im - ρ₀.im)) (P3H.norm_sPt_le_R ha haL hLpos hm_d))
      hminP1 ({ρ₁} : Finset ℂ) hT hTim (hCc1 (2 * ρ₁.im - ρ₀.im))
    have t1 : (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im - ρ₀.im) - ρ₁) * (L : ℂ)))).re
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
      rw [P3_arg_eq_split (a := a) (L := L) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam := (Work.LinnikContract.lamOf q ρ₁)) (gam := ρ₁.im)
        (t := 2 * ρ₁.im - ρ₀.im) (ρ := ρ₁) hLne hρ₁re rfl]
      rw [show (2 * ρ₁.im - ρ₀.im - ρ₁.im) * L = Δ by rw [hΔdef]; ring]
    have hsum : (∑ u ∈ ({ρ₁} : Finset ℂ),
        (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im - ρ₀.im) - u) * (L : ℂ)))).re)
        = P9.PhiG (a + (Work.LinnikContract.lamOf q ρ₁)) (a + (Work.LinnikContract.lamOf q ρ₁)) Δ := by
      rw [Finset.sum_singleton, t1]
    rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS6'] at hb
    rw [Finset.card_singleton, Nat.cast_one, one_mul, hsum] at hb
    linarith only [hb, hS6', he6def, hE2def, hE3def]
  -- ### point 7: χ₁² at σ + 2iγ₁, nothing kept
  have hS7 : S7 ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e7 := by
    obtain ⟨par₂, hpar₂2, hpar₂0, hpar₂1⟩ := exists_par (χ₁ ^ 2).primitiveCharacter
    have hb := P3H.pointBoundQH (q := q) (N := (χ₁ ^ 2).conductor)
      (hNq := (χ₁ ^ 2).conductor_dvd_level) (φ := (χ₁ ^ 2).primitiveCharacter) hφ₂ne
      hφ₂prim ha hlam₁nn hδpos hδlt1 hLt haδL
      (s := sPt a L (2 * ρ₁.im)) (by simp [sPt]) (by simpa [sPt] using hm_g)
      (hk1Of (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim hN2_3 hlogN2 (2 * ρ₁.im) hm_g)
      par₂ hpar₂0 hpar₂1
      (hSpr par₂ hpar₂2 (2 * ρ₁.im)).1 (hSpr par₂ hpar₂2 (2 * ρ₁.im)).2
      (hJOf (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim
        (sPt a L (2 * ρ₁.im)) (P3H.norm_sPt_le_R ha haL hLpos hm_g))
      (fun u hu him => hminPrim (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter hφ₂ne hφ₂prim u hu (le_trans him hRW))
      (∅ : Finset ℂ) (by simp) (by simp)
      (hCcOf (χ₁ ^ 2).conductor_dvd_level (χ₁ ^ 2).primitiveCharacter (2 * ρ₁.im))
    have hsum : (∑ u ∈ (∅ : Finset ℂ),
        (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im) - u) * (L : ℂ)))).re) = 0 :=
      Finset.sum_empty
    rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS7'] at hb
    rw [hsum, Finset.card_empty, Nat.cast_zero, zero_mul, neg_zero, zero_add, add_zero] at hb
    linarith only [hb, hS7', he7def, hE2def, hE3def]
  -- ### point 8: χ₁³ at σ + i(2γ₁+γ₀), nothing kept
  haveI hN3' : NeZero (χ₁ ^ 3).conductor := ⟨(χ₁ ^ 3).conductor_ne_zero⟩
  have hφ₃ne : (χ₁ ^ 3).primitiveCharacter ≠ 1 := by
    intro hh
    exact hχ3 (by rw [← DirichletCharacter.changeLevel_primitiveCharacter (χ₁ ^ 3), hh,
      DirichletCharacter.changeLevel_one (χ₁ ^ 3).conductor_dvd_level])
  have hφ₃prim : (χ₁ ^ 3).primitiveCharacter.IsPrimitive :=
    DirichletCharacter.primitiveCharacter_isPrimitive (χ₁ ^ 3)
  have hlogN3 : Real.log (((χ₁ ^ 3).conductor : ℕ) : ℝ) ≤ L :=
    hlogNOf (χ₁ ^ 3).conductor_dvd_level (χ₁ ^ 3).conductor_ne_zero
  have hN3_3 : 3 ≤ (χ₁ ^ 3).conductor :=
    Work.LinnikAreas2.three_le_conductor (χ₁ ^ 3) hχ3
  have hS8 : S8 ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * (1 / 6 + ε₁) + e8 := by
    obtain ⟨par₃, hpar₃2, hpar₃0, hpar₃1⟩ := exists_par (χ₁ ^ 3).primitiveCharacter
    have hb := P3H.pointBoundQH (q := q) (N := (χ₁ ^ 3).conductor)
      (hNq := (χ₁ ^ 3).conductor_dvd_level) (φ := (χ₁ ^ 3).primitiveCharacter) hφ₃ne
      hφ₃prim ha hlam₁nn hδpos hδlt1 hLt haδL
      (s := sPt a L (2 * ρ₁.im + ρ₀.im)) (by simp [sPt]) (by simpa [sPt] using hm_e)
      (hk1Of (χ₁ ^ 3).primitiveCharacter hφ₃ne hφ₃prim hN3_3 hlogN3 (2 * ρ₁.im + ρ₀.im) hm_e)
      par₃ hpar₃0 hpar₃1
      (hSpr par₃ hpar₃2 (2 * ρ₁.im + ρ₀.im)).1 (hSpr par₃ hpar₃2 (2 * ρ₁.im + ρ₀.im)).2
      (hJOf (χ₁ ^ 3).conductor_dvd_level (χ₁ ^ 3).primitiveCharacter hφ₃ne hφ₃prim
        (sPt a L (2 * ρ₁.im + ρ₀.im)) (P3H.norm_sPt_le_R ha haL hLpos hm_e))
      (fun u hu him => hminPrim (χ₁ ^ 3).conductor_dvd_level (χ₁ ^ 3).primitiveCharacter hφ₃ne hφ₃prim u hu (le_trans him hRW))
      (∅ : Finset ℂ) (by simp) (by simp)
      (hCcOf (χ₁ ^ 3).conductor_dvd_level (χ₁ ^ 3).primitiveCharacter (2 * ρ₁.im + ρ₀.im))
    have hsum : (∑ u ∈ (∅ : Finset ℂ),
        (P3 (((a : ℂ) + ((Work.LinnikContract.lamOf q ρ₁) : ℂ)) / ((sPt a L (2 * ρ₁.im + ρ₀.im) - u) * (L : ℂ)))).re) = 0 :=
      Finset.sum_empty
    rw [DirichletCharacter.changeLevel_primitiveCharacter, ← hS8'] at hb
    rw [hsum, Finset.card_empty, Nat.cast_zero, zero_mul, neg_zero, zero_add, add_zero] at hb
    linarith only [hb, hS8', he8def, hE2def, hE3def]
  -- ### the assembly
  have hFcnn : 0 ≤ Fc := by rw [hFcdef]; positivity
  have hC0cnn : 0 ≤ C0c := by rw [hC0cdef]; positivity
  have h1C0 : ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ ≤ C0c := by
    rw [hC0cdef]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hαaup hLpos.le) hC₀pos.le
  have hE1 : e1 ≤ Ee := by
    exact heEz _ (by linarith only [he1def, h1C0, hFcnn])
  have hE2 : e2 ≤ Ee := by
    exact heE _ (by have h := hcFar 2 (by norm_num); linarith only [h, he2def, hC0cnn])
  have hE4 : e4 ≤ Ee := by
    exact heE _ (by have h := hcFar 2 (by norm_num); linarith only [h, he4def, hC0cnn])
  have hE5 : e5 ≤ Ee := by
    exact heE _ (by have h := hcFar 0 (by norm_num); linarith only [h, he5def, hC0cnn, hFcnn])
  have hE6 : e6 ≤ Ee := by
    exact heE _ (by have h := hcFar 1 (by norm_num); linarith only [h, he6def, hC0cnn])
  have hE7 : e7 ≤ Ee := by
    exact heE _ (by have h := hcFar 0 (by norm_num); linarith only [h, he7def, hC0cnn, hFcnn])
  have hE8 : e8 ≤ Ee := by
    exact heE _ (by have h := hcFar 0 (by norm_num); linarith only [h, he8def, hC0cnn, hFcnn])
  have hcomb : 0 ≤ (K ^ 2 + 1 / 2) * (S1 + S2) + K * (S3 + 2 * S4 + S5)
      + (1 / 4) * (S6 + 2 * S7 + S8) + 0 := by
    have h0 := P9.HbCombinationL_nonneg (q := q) χ₁ K (1 + a / L) ρ₀.im ρ₁.im a (Work.LinnikContract.lamOf q ρ₁)
      hK.le (by have h : 0 < a / L := div_pos ha hLpos; linarith only [h]) ha hlam₁nn
    rw [Work.ZeroFreeTables.HbCombinationL, ← hLdef] at h0
    push_cast at h0
    simp only [hS1', hS2', hS3', hS4', hS5', hS6', hS7', hS8', sPt, Complex.ofReal_zero,
      zero_mul, add_zero]
    push_cast
    exact h0
  have habs : (K ^ 2 + 1 / 2) * (e1 + e2) + K * (e3 + 2 * e4 + e5)
      + (1 / 4) * (e6 + 2 * e7 + e8) + 0 + (a + (Work.LinnikContract.lamOf q ρ₁)) * ε₁ * (K ^ 2 + 3 * K + 3 / 2)
      ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε := by
    have hsum := Work.ZeroFreeTables.HB94.Lam0GeEngine.sumErr_le hK.le hE1 hE2 hE1 hE4 hE5 hE6 hE7 hE8
    have hε := mul_le_mul_of_nonneg_left hε₁bud hα0
    have hmain : 2 * (K + 1) ^ 2 * Ee ≤ a * ε / 2 := hEebound
    have hfin : a * ε / 2 + (a + (Work.LinnikContract.lamOf q ρ₁)) * (ε / 4) ≤ (a + (Work.LinnikContract.lamOf q ρ₁)) * ε := by
      linarith only [mul_nonneg hlam₁nn (le_of_lt ‹0 < ε›), mul_pos ha ‹0 < ε›]
    linarith only [hsum, hmain, hε, hfin]
  exact Work.ZeroFreeTables.HB94.Lam0GeEngine.caseA_bridge (a := a) (lam₁ := (Work.LinnikContract.lamOf q ρ₁)) (lam₀ := (Work.LinnikContract.lamOf q ρ₀)) (K := K) (ε := ε) (ε₁ := ε₁)
    (Δ := Δ) (S1 := S1) (S2 := S2) (S3 := S3) (S4 := S4) (S5 := S5) (S6 := S6)
    (S7 := S7) (S8 := S8) (e1 := e1) (e2 := e2) (e3 := e3) (e4 := e4) (e5 := e5)
    (e6 := e6) (e7 := e7) (e8 := e8) (corr := 0)
    hK.le hS1 hS2 hS3 hS4 hS5 hS6 hS7 hS8 hcomb
    (P3.P3Bounds.2 a (Work.LinnikContract.lamOf q ρ₁) (Work.LinnikContract.lamOf q ρ₀) K Δ ha hK hlam₁nn hlam₁lam₀
      (side913 ha hK (by linarith only [ha, hlam₁nn]) (by linarith only [ha, hlam₀nn]) hcond).1) habs


theorem RectP3EngineH : ∀ (a K ε : ℝ), 0 < a → 0 < K → 0 < ε →
    ∀ H W : ℝ, 1 ≤ H → 3 * H + 1 ≤ W →
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (ρ₁ ρ₀ : ℂ),
      H ≤ Real.log (q : ℝ) →
      Work.ZeroFreeTables.IsMinWideAt H W χ₁ ρ₁ →
      ¬ (χ₁ ^ 2 = 1 ∧ ρ₁.im = 0) →
      Work.LinnikContract.zeroMult χ₁ ρ₀ ≠ 0 → |ρ₀.im| ≤ H → ρ₁ ≠ ρ₀ →
      (χ₁ ^ 2 = 1 → ρ₀ ≠ starRingEnd ℂ ρ₁) →
      Work.ZeroFreeTables.cond913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₀) a K →
      Work.ZeroFreeTables.ineq913 (Work.LinnikContract.lamOf q ρ₁)
        (Work.LinnikContract.lamOf q ρ₀) a K ε := by
  intro a K ε ha hK hε H W hH1 hHW
  set R : ℝ := 3 * H with hRdef
  have hRnn : 0 ≤ R := by rw [hRdef]; linarith only [hH1]
  have hRW : R + 1 ≤ W := by rw [hRdef]; linarith only [hHW]
  have hΘ : (0 : ℝ) ≤ R + 2 := by linarith only [hRnn]
  -- ## the constants
  set ε₁ : ℝ := ε / (4 * (K ^ 2 + 3 * K + 4)) with hε₁def
  have hε₁pos : 0 < ε₁ := by rw [hε₁def]; positivity
  have hε₁bud : ε₁ * (K ^ 2 + 3 * K + 3 / 2) ≤ ε / 4 := by
    rw [hε₁def, div_mul_eq_mul_div,
      div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (K ^ 2 + 3 * K + 4))]
    nlinarith [hε.le, sq_nonneg K, hK.le]
  obtain ⟨L₀, δ₀, hδ₀pos, hδ₀lt1, h31⟩ :=
    Work.LinnikAreas.l31free.lemma3_1_free_gen (φ := 1 / 3) (by norm_num) hε₁pos
      Work.LinnikAreas.LBound13_holds
  obtain ⟨εζ, hεζpos, hεζ⟩ := P3H.zetaZeroFreeStripHt (R + 2) hΘ
  obtain ⟨Ct, hCtpos, hCtS⟩ := Work.ZeroFreeTables.P9.parity_bound_re
  obtain ⟨Czζ, hCzζpos, hCzζ⟩ := P3H.zetaInvSqSumBoundHt (R + 2) hΘ
  obtain ⟨C₀, hC₀pos, hC₀b⟩ := Work.ZeroFreeTables.OffAxis.zetaLogDerivPoleSplitH (R + 2) hΘ
  obtain ⟨Cc, hCcpos, hCc⟩ := Work.ZeroFreeTables.P9.SigmaP3L_changeLevel_diff
  obtain ⟨Cp1, hCp1pos, hCp1⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 1 (by norm_num)
  obtain ⟨Cp2, hCp2pos, hCp2⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 2 (by norm_num)
  obtain ⟨Cp3, hCp3pos, hCp3⟩ := Work.ZeroFreeTables.P9.primeFactors_logPow_div_le 3 (by norm_num)
  set Cp : ℝ := max (max Cp1 Cp2) Cp3 with hCpdef
  have hCpnn : 0 ≤ Cp := by rw [hCpdef]; positivity
  have hCp1le : Cp1 ≤ Cp := by rw [hCpdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hCp2le : Cp2 ≤ Cp := by rw [hCpdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hCp3le : Cp3 ≤ Cp := by rw [hCpdef]; exact le_max_right _ _
  obtain ⟨Cq, hCqpos, hCq⟩ := Work.ZeroFreeTables.HB94.Lam0GeEngine.invSqSum_uniform
  set Cz : ℝ := max Czζ 1 with hCzdef
  have hCzpos : 0 < Cz := by rw [hCzdef]; positivity
  have hCzζle : Czζ ≤ Cz := by rw [hCzdef]; exact le_max_left _ _
  set Cn : ℝ := max Cq (max 1 (((Cq * (Real.log (R + 4) + 2) - Cz) / 6) + 1)) with hCndef
  have hCqle : Cq ≤ Cn := by rw [hCndef]; exact le_max_left _ _
  have hCnpos : 0 < Cn := lt_of_lt_of_le hCqpos hCqle
  have hCnbig : Cq * (Real.log (R + 4) + 2) ≤ 6 * Cn + Cz := by
    have h1 : ((Cq * (Real.log (R + 4) + 2) - Cz) / 6) + 1 ≤ Cn := by
      rw [hCndef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
    have h6 : 6 * (((Cq * (Real.log (R + 4) + 2) - Cz) / 6) + 1) ≤ 6 * Cn :=
      mul_le_mul_of_nonneg_left h1 (by norm_num)
    have heq : 6 * (((Cq * (Real.log (R + 4) + 2) - Cz) / 6) + 1)
        = Cq * (Real.log (R + 4) + 2) - Cz + 6 := by ring
    linarith only [h6, heq.le, heq.ge]
  set δ : ℝ := min δ₀ (min (εζ / 2) (1 / 2)) with hδdef
  have hδpos : 0 < δ := lt_min hδ₀pos (lt_min (by linarith only [hεζpos]) (by norm_num))
  have hδleδ₀ : δ ≤ δ₀ := min_le_left _ _
  have hδleζ : δ ≤ εζ / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδlehalf : δ ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hδlt1 : δ < 1 := lt_of_le_of_lt hδlehalf (by norm_num)
  set aup : ℝ := (a ^ 3 * (Kond K + 1)) ^ (1 / 3 : ℝ) with haupdef
  have hauppos : 0 < aup := by
    rw [haupdef]
    exact Real.rpow_pos_of_pos (by
      have h1 : 0 < Kond K := lt_min (by positivity) (by positivity)
      positivity) _
  obtain ⟨qabs, habs⟩ := Work.ZeroFreeTables.P9.absorption_eventual a K ε aup δ C₀ Ct Cn Cz Cc Cp
    ha hK.le hε hδpos hauppos (le_of_lt hC₀pos) hCtpos hCnpos hCzpos hCcpos.le hCpnn
  set Λ : ℝ := max (max L₀ (2 * a / δ))
    (max (max (R + 2) a) (Real.exp (max (1 / a) (max a 1)))) with hΛdef
  refine ⟨max qabs (max 3 (Nat.ceil (Real.exp Λ))), ?_⟩
  intro q hq hqne χ₁ ρ₁ ρ₀ hHlog hmin hnotreal hzm0 hγ₀ hne hconj hcond
  have hqq : 3 ≤ q := by have h := hq; simp only [max_le_iff] at h; exact h.2.1
  have hqexp : Nat.ceil (Real.exp Λ) ≤ q := by
    have h := hq; simp only [max_le_iff] at h; exact h.2.2
  have hΛL : Λ ≤ Real.log q := by
    have h1 : Real.exp Λ ≤ (q : ℝ) :=
      le_trans (Nat.le_ceil (Real.exp Λ)) (by exact_mod_cast hqexp)
    rw [← Real.log_exp Λ]
    exact Real.log_le_log (Real.exp_pos Λ) h1
  set L : ℝ := Real.log q with hLdef
  have hHL : H ≤ L := hHlog
  have hL₀L : L₀ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hΛL
  have h2aδL : 2 * a / δ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hΛL
  have haL : a ≤ L :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hΛL
  have hΘL : R + 2 ≤ L :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hΛL
  have hexpL : Real.exp (max (1 / a) (max a 1)) ≤ L :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hΛL
  have heL : Real.exp 1 ≤ L := by
    refine le_trans (Real.exp_le_exp.mpr ?_) hexpL
    exact le_trans (le_max_right a 1) (le_max_right (1 / a) (max a 1))
  have hLt : 1 < L := lt_of_lt_of_le (Real.one_lt_exp_iff.mpr one_pos) heL
  have hLpos : 0 < L := lt_trans zero_lt_one hLt
  have hLne : L ≠ 0 := ne_of_gt hLpos
  have hL1 : 1 ≤ L := le_of_lt hLt
  have h12L : (1 : ℝ) / 2 ≤ L := by linarith only [hL1]
  have hlogLnn : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hlogLmax : max (1 / a) (max a 1) ≤ Real.log L := by
    rw [← Real.log_exp (max (1 / a) (max a 1))]
    exact Real.log_le_log (Real.exp_pos _) hexpL
  have hlogL1a : 1 / a ≤ Real.log L := le_trans (le_max_left _ _) hlogLmax
  have hlogLa : a ≤ Real.log L :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hlogLmax
  have h1aL : 1 ≤ a * Real.log L := by
    have h := mul_le_mul_of_nonneg_left hlogL1a ha.le
    have h2 : a * (1 / a) = 1 := by field_simp
    linarith only [h, h2.le, h2.ge]
  have haδL : 2 * a ≤ δ * L := by
    rw [div_le_iff₀ hδpos] at h2aδL
    linarith only [h2aδL]
  have hR3L : R ≤ 3 * L := by rw [hRdef]; linarith only [hHL]
  have hR10L : R ≤ 10 * L := by linarith only [hR3L, hL1]
  have hR2L : R + 2 ≤ 10 * L := by linarith only [hR3L, hL1]
  -- ## the E-terms
  set Cj : ℝ := Cn * (L + 6) + Cz with hCjdef
  have hCjnn : 0 ≤ Cj := by rw [hCjdef]; positivity
  set Sp1 : ℝ := ∑ p ∈ q.primeFactors, Real.log (p : ℝ) / (p : ℝ) with hSp1def
  set Sp2 : ℝ := ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 2 / (p : ℝ) with hSp2def
  set Sp3 : ℝ := ∑ p ∈ q.primeFactors, (Real.log (p : ℝ)) ^ 3 / (p : ℝ) with hSp3def
  set Corr : ℝ := (Cc / L) * ((a + Work.LinnikContract.lamOf q ρ₁) * Sp1
    + ((a + Work.LinnikContract.lamOf q ρ₁) ^ 2 / L) * Sp2
    + ((a + Work.LinnikContract.lamOf q ρ₁) ^ 3 / L ^ 2) * Sp3) with hCorrdef
  set E : ℝ := (aup / L) * C₀ + (aup ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct)
    + (2 / 3) * (aup ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct)
    + (Cc / L) * (aup * Cp * (Real.log L) ^ 2 + (aup ^ 2 / L) * Cp * (Real.log L) ^ 3
        + (aup ^ 3 / L ^ 2) * Cp * (Real.log L) ^ 4)
    + 64 * aup / (δ * L) with hEdef
  have hEbound : 2 * (K + 1) ^ 2 * E ≤ a * ε / 2 := by
    have h := habs q (by have hh := hq; simp only [max_le_iff] at hh; omega)
    rw [show Real.log q = L from hLdef.symm] at h
    rw [hEdef, hCjdef]
    exact h
  -- ## basic bounds
  have hlam₁nn : 0 ≤ Work.LinnikContract.lamOf q ρ₁ :=
    Work.ZeroFreeTables.HB94.Lam0GeEngine.lamOf_nonneg_of_zeroMult hmin.2.1
  have hlam₀nn : 0 ≤ Work.LinnikContract.lamOf q ρ₀ :=
    Work.ZeroFreeTables.HB94.Lam0GeEngine.lamOf_nonneg_of_zeroMult hzm0
  have hγ₁ : |ρ₁.im| ≤ H := hmin.2.2.1
  have hlam₁lam₀ : Work.LinnikContract.lamOf q ρ₁ ≤ Work.LinnikContract.lamOf q ρ₀ := by
    have := hmin.2.2.2 χ₁ ρ₀ hmin.1 hzm0 (le_trans hγ₀ (le_trans (by linarith only [hH1]) hRW))
    simpa using this
  have hχ₁ne : χ₁ ≠ 1 := hmin.1
  have hα0 : 0 ≤ a + Work.LinnikContract.lamOf q ρ₁ := by linarith only [ha, hlam₁nn]
  have hαaup : a + Work.LinnikContract.lamOf q ρ₁ ≤ aup := by
    rw [haupdef]
    exact Work.ZeroFreeTables.HB94.Lam0GeEngine.alpha_le_aup ha hlam₁nn hlam₁lam₀ hcond
  have hαaup2 : (a + Work.LinnikContract.lamOf q ρ₁) ^ 2 ≤ aup ^ 2 := pow_le_pow_left₀ hα0 hαaup 2
  have hαaup3 : (a + Work.LinnikContract.lamOf q ρ₁) ^ 3 ≤ aup ^ 3 := pow_le_pow_left₀ hα0 hαaup 3
  have hlamOf_eq : ∀ u : ℂ, Work.LinnikContract.lamOf q u = (1 - u.re) * L := by
    intro u; rw [Work.LinnikContract.lamOf, ← hLdef]
  have hminOf : ∀ (ψ : DirichletCharacter ℂ q), ψ ≠ 1 → ∀ u : ℂ,
      Work.LinnikContract.zeroMult ψ u ≠ 0 → |u.im| ≤ W →
      Work.LinnikContract.lamOf q ρ₁ ≤ (1 - u.re) * L := by
    intro ψ hψ u hu him
    rw [← hlamOf_eq u]
    exact hmin.2.2.2 ψ u hψ hu him
  have hminPrim : ∀ {N : ℕ} [NeZero N] (hNq : N ∣ q) (φ : DirichletCharacter ℂ N), φ ≠ 1 →
      φ.IsPrimitive → ∀ u : ℂ, Work.LinnikContract.zeroMult φ u ≠ 0 → |u.im| ≤ W →
      Work.LinnikContract.lamOf q ρ₁ ≤ (1 - u.re) * L := by
    intro N _ hNq φ hφ hprim u hu him
    refine hminOf (DirichletCharacter.changeLevel hNq φ)
      (Work.ZeroFreeTables.HB94.Lam0GeEngine.changeLevel_ne_one hNq φ hφ) u ?_ him
    rw [Work.ZeroFreeTables.Table4.zeroMult_changeLevel hNq φ u]
    exact hu
  -- ## the families of bounds
  have hSpr : ∀ (par : ℕ), par ≤ 2 → ∀ t : ℝ,
      |∑' n : ℕ, (((1 / (Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L t
        + ((par + 2 * n : ℕ) : ℂ))) ^ 2)).re| ≤ Ct ∧
      |∑' n : ℕ, (((1 / (Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L t
        + ((par + 2 * n : ℕ) : ℂ))) ^ 3)).re| ≤ Ct := by
    intro par hpar t
    refine hCtS (Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L t) ?_ par hpar
    have h : (Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L t).re = 1 + a / L := by
      simp [Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt]
    rw [h]
    have : 0 ≤ a / L := div_nonneg ha.le hLpos.le
    linarith only [this]
  have hSzeta : ∀ t : ℝ,
      |∑' n : ℕ, (((1 / (Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L t
        + ((2 * (n + 1) : ℕ) : ℂ))) ^ 2)).re| ≤ Ct ∧
      |∑' n : ℕ, (((1 / (Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L t
        + ((2 * (n + 1) : ℕ) : ℂ))) ^ 3)).re| ≤ Ct := by
    intro t
    have h := hSpr 2 (by norm_num) t
    have hnat : ∀ n : ℕ, (2 * (n + 1) : ℕ) = 2 + 2 * n := fun n => by ring
    constructor
    · refine le_trans (le_of_eq ?_) h.1
      apply congrArg abs
      apply tsum_congr
      intro n
      rw [hnat n]
    · refine le_trans (le_of_eq ?_) h.2
      apply congrArg abs
      apply tsum_congr
      intro n
      rw [hnat n]
  have hCzZeta : ∀ s : ℂ, ‖s‖ ≤ R + 2 →
      (∑' u : ℂ, (analyticOrderNatAt completedRiemannZeta u : ℝ) * (1 / (1 + ‖s - u‖ ^ 2))) ≤ Cz := by
    intro s hs
    exact le_trans (hCzζ s hs) hCzζle
  have hC0b' : ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → |s.im| ≤ R + 2 →
      (-logDeriv riemannZeta s).re ≤ (1 / (s - 1)).re + C₀ := hC₀b
  have hnzδ : ∀ t : ℝ, |t| ≤ R → ∀ u : ℂ, riemannZeta u = 0 →
      δ < ‖(1 : ℂ) + (t : ℂ) * Complex.I - u‖ := by
    intro t ht u hu
    by_contra hle
    push Not at hle
    have hre1 : |(1 : ℝ) - u.re| ≤ δ := by
      have h := Complex.abs_re_le_norm ((1 : ℂ) + (t : ℂ) * Complex.I - u)
      have h2 : ((1 : ℂ) + (t : ℂ) * Complex.I - u).re = 1 - u.re := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re]
      rw [h2] at h
      linarith only [h, hle]
    have him1 : |t - u.im| ≤ δ := by
      have h := Complex.abs_im_le_norm ((1 : ℂ) + (t : ℂ) * Complex.I - u)
      have h2 : ((1 : ℂ) + (t : ℂ) * Complex.I - u).im = t - u.im := by
        simp [Complex.sub_im, Complex.add_im, Complex.mul_im]
      rw [h2] at h
      linarith only [h, hle]
    have hure : 1 - εζ ≤ u.re := by
      have h := (abs_le.mp hre1).2
      linarith only [h, hδleζ, hεζpos]
    have hure2 : u.re ≤ 2 := by
      have h := (abs_le.mp hre1).1
      linarith only [h, hδlehalf]
    have huim : |u.im| ≤ R + 2 := by
      have h1 := (abs_le.mp him1).1
      have h2 := (abs_le.mp him1).2
      have h3 := (abs_le.mp ht)
      rw [abs_le]
      constructor <;> linarith only [h1, h2, h3.1, h3.2, hδlehalf]
    have hz : ((u.re : ℂ) + Complex.I * (u.im : ℂ)) = u := by
      rw [mul_comm]; exact Complex.re_add_im u
    exact hεζ u.im u.re huim hure hure2 (by rw [hz]; exact hu)
  have hJOf : ∀ {N : ℕ} [NeZero N] (hNq : N ∣ q) (φ : DirichletCharacter ℂ N), φ ≠ 1 →
      φ.IsPrimitive → ∀ s : ℂ, ‖s‖ ≤ R + 2 → Work.ZeroFreeTables.P9.invSqSum N φ s ≤ Cj := by
    intro N _ hNq φ hφ hprim s hs
    have h1 : Work.ZeroFreeTables.P9.invSqSum N φ s
        ≤ Cq * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2) := hCq φ hφ hprim s
    have h2 : Real.log (N : ℝ) ≤ L := by
      rw [hLdef]
      have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
      refine Real.log_le_log hNpos ?_
      exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hNq
    have h3 : Real.log (2 + ‖s‖) ≤ Real.log (R + 4) :=
      Real.log_le_log (by positivity) (by linarith only [hs])
    have h4 : Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2 ≤ L + (Real.log (R + 4) + 2) := by
      linarith only [h2, h3]
    have h5 : Cq * (Real.log (N : ℝ) + Real.log (2 + ‖s‖) + 2)
        ≤ Cq * (L + (Real.log (R + 4) + 2)) :=
      mul_le_mul_of_nonneg_left h4 hCqpos.le
    have h6 : Cq * (L + (Real.log (R + 4) + 2))
        = Cq * L + Cq * (Real.log (R + 4) + 2) := by ring
    have h7 : Cq * L ≤ Cn * L := mul_le_mul_of_nonneg_right hCqle (le_of_lt hLpos)
    have h8 : Cn * L + (6 * Cn + Cz) = Cn * (L + 6) + Cz := by ring
    rw [hCjdef]
    linarith only [h1, h5, h6.le, h6.ge, h7, hCnbig, h8.le, h8.ge]
  have hCcOf : ∀ {N : ℕ} [NeZero N] (hNq : N ∣ q) (φ : DirichletCharacter ℂ N) (t : ℝ),
      |Work.ZeroFreeTables.SigmaP3L q L (DirichletCharacter.changeLevel hNq φ)
          (Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L t) a (Work.LinnikContract.lamOf q ρ₁)
        - Work.ZeroFreeTables.SigmaP3L N L φ
          (Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L t) a
          (Work.LinnikContract.lamOf q ρ₁)| ≤ Corr := by
    intro N _ hNq φ t
    have h := hCc (hNq := hNq) (ψ := φ) (L := L) hL1 (by
      have h2 : (Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L t).re = 1 + a / L := by
        simp [Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt]
      rw [h2]
      have : 0 < a / L := div_pos ha hLpos
      linarith only [this]) (a := a) (lam₁ := Work.LinnikContract.lamOf q ρ₁) ha hlam₁nn
    rw [hCorrdef, hSp1def, hSp2def, hSp3def]
    rw [← hSp1def, ← hSp2def, ← hSp3def] at h
    exact h
  have h31' : ∀ {N : ℕ} [NeZero N], 3 ≤ N → ∀ (χ : DirichletCharacter ℂ N), χ ≠ 1 →
      χ.IsPrimitive →
      ∀ {L : ℝ}, L₀ ≤ L → Real.log (N : ℝ) ≤ L → ∀ s : ℂ,
        1 + 1 / (L * Real.log L) ≤ s.re → s.re ≤ 1 + Real.log L / L → |s.im| ≤ 10 * L →
        (-logDeriv (DirichletCharacter.LFunction χ) s).re
          + (∑ᶠ u : ℂ, ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
                (Metric.closedBall 0 (|s.im| + 2))) u : ℤ) *
              (if ‖(1 : ℂ) + (s.im : ℂ) * Complex.I - u‖ ≤ δ₀ then ((1 / (s - u)).re) else 0))
          ≤ (1 / 6 + ε₁) * L := by
    intro M _ hM χ hχ hprim L hL0 hlogN s hs1 hs2 hs3
    simpa only [show ((1 : ℝ) / 3 / 2) = 1 / 6 by norm_num] using
      h31 hM χ hχ hprim hL0 hlogN s hs1 hs2 hs3
  have hk1Of : ∀ {N : ℕ} [NeZero N] (φ : DirichletCharacter ℂ N), φ ≠ 1 → φ.IsPrimitive →
      3 ≤ N → Real.log (N : ℝ) ≤ L → ∀ t : ℝ, |t| ≤ R →
      (-logDeriv (DirichletCharacter.LFunction φ)
          (Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L t)).re
        + Work.ZeroFreeTables.P9.nearInvSum N φ
            (Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L t) δ ≤ (1 / 6 + ε₁) * L := by
    intro N _ φ hφ hprim hN3 hlogN t ht
    refine P3H.k1InputH (L₀ := L₀) (δ₀ := δ₀) (δ := δ) (ε₁ := ε₁) (a := a) (L := L) h31'
      (N := N) φ hφ hprim hN3 hL₀L hlogN hδleδ₀ (le_of_lt hδ₀lt1) hδpos (le_of_lt hδlt1)
      ha hL1 h1aL hlogLa
      (s := Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt a L t)
      (by simp [Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt])
      (by simpa [Work.ZeroFreeTables.HB94.Lam0GeEngine.sPt] using le_trans ht hR10L)
  have hSp1le : Sp1 ≤ Cp * (Real.log L) ^ 2 := by
    have h := hCp1 q hqq
    rw [hSp1def]
    have h' : (Real.log (Real.log (q : ℝ))) ^ (1 + 1) = (Real.log L) ^ 2 := by rw [hLdef]
    rw [h'] at h
    simp only [pow_one] at h
    exact le_trans h (mul_le_mul_of_nonneg_right hCp1le (by positivity))
  have hSp2le : Sp2 ≤ Cp * (Real.log L) ^ 3 := by
    have h := hCp2 q hqq
    rw [hSp2def]
    have h' : (Real.log (Real.log (q : ℝ))) ^ (2 + 1) = (Real.log L) ^ 3 := by rw [hLdef]
    rw [h'] at h
    exact le_trans h (mul_le_mul_of_nonneg_right hCp2le (by positivity))
  have hSp3le : Sp3 ≤ Cp * (Real.log L) ^ 4 := by
    have h := hCp3 q hqq
    rw [hSp3def]
    have h' : (Real.log (Real.log (q : ℝ))) ^ (3 + 1) = (Real.log L) ^ 4 := by rw [hLdef]
    rw [h'] at h
    exact le_trans h (mul_le_mul_of_nonneg_right hCp3le (by positivity))
  have hSpnn1 : 0 ≤ Sp1 := by rw [hSp1def]; positivity
  have hSpnn2 : 0 ≤ Sp2 := by rw [hSp2def]; positivity
  have hSpnn3 : 0 ≤ Sp3 := by rw [hSp3def]; positivity
  have hN3 : 3 ≤ χ₁.conductor := Work.LinnikAreas2.three_le_conductor χ₁ hχ₁ne
  haveI hNc : NeZero χ₁.conductor := ⟨χ₁.conductor_ne_zero⟩
  set Δ : ℝ := (ρ₁.im - ρ₀.im) * L with hΔdef
  set β : ℝ := (ρ₁.im + ρ₀.im) * L with hβdef
  set γ : ℝ := 2 * ρ₁.im * L with hγdef
  -- ## E-term comparisons
  set E2 : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L ^ 2)
    * ((1 + 4 / δ ^ 2) * Cj + Ct) with hE2def
  set E3 : ℝ := (2 / 3) * ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 3)
    * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct) with hE3def
  set E2z : ℝ := ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L ^ 2)
    * ((1 + 4 / δ ^ 2) * Cz + Ct) with hE2zdef
  set E3z : ℝ := (2 / 3) * ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 3)
    * ((2 / δ) * (1 + 4 / δ ^ 2) * Cz + Ct) with hE3zdef
  set E2c : ℝ := (aup ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct) with hE2cdef
  set E3c : ℝ := (2 / 3) * (aup ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct) with hE3cdef
  set Corrc : ℝ := (Cc / L) * (aup * Cp * (Real.log L) ^ 2 + (aup ^ 2 / L) * Cp * (Real.log L) ^ 3
      + (aup ^ 3 / L ^ 2) * Cp * (Real.log L) ^ 4) with hCorrcdef
  set C0c : ℝ := (aup / L) * C₀ with hC0cdef
  set Fc : ℝ := 64 * aup / (δ * L) with hFcdef
  set Ee : ℝ := C0c + E2c + E3c + Corrc + Fc with hEedef
  have hcE2 : E2 ≤ E2c := by
    rw [hE2def, hE2cdef]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact div_le_div_of_nonneg_right hαaup2 (by positivity)
  have hcE3 : E3 ≤ E3c := by
    rw [hE3def, hE3cdef]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hαaup3 (by positivity))
      (by norm_num : (0 : ℝ) ≤ 2 / 3)
  have hCzCj : Cz ≤ Cj := by
    rw [hCjdef]
    have h1 : 0 ≤ Cn * (L + 6) := by positivity
    linarith only [h1]
  have hcE2z : E2z ≤ E2c := by
    rw [hE2zdef, hE2cdef]
    calc ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cz + Ct)
        ≤ (aup ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cz + Ct) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact div_le_div_of_nonneg_right hαaup2 (by positivity)
      _ ≤ (aup ^ 2 / L ^ 2) * ((1 + 4 / δ ^ 2) * Cj + Ct) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h1 : 0 ≤ (1 + 4 / δ ^ 2 : ℝ) := by positivity
          have h2 := mul_le_mul_of_nonneg_left hCzCj h1
          linarith only [h2]
  have hcE3z : E3z ≤ E3c := by
    rw [hE3zdef, hE3cdef]
    calc (2 / 3) * ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 3)
          * ((2 / δ) * (1 + 4 / δ ^ 2) * Cz + Ct)
        ≤ (2 / 3) * (aup ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cz + Ct) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hαaup3 (by positivity))
            (by norm_num : (0 : ℝ) ≤ 2 / 3)
      _ ≤ (2 / 3) * (aup ^ 3 / L ^ 3) * ((2 / δ) * (1 + 4 / δ ^ 2) * Cj + Ct) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h1 : 0 ≤ (2 / δ) * (1 + 4 / δ ^ 2 : ℝ) := by positivity
          have h2 := mul_le_mul_of_nonneg_left hCzCj h1
          linarith only [h2]
  have hcFar : ∀ k : ℕ, k ≤ 4 → (k : ℝ) * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L)) ≤ Fc := by
    intro k hk
    have h1 : (k : ℝ) ≤ 4 := by exact_mod_cast hk
    rw [hFcdef]
    have h2 : (k : ℝ) * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L))
        ≤ 4 * (8 * aup / (δ * L)) := by
      have h3 : (k : ℝ) * (8 * (a + (Work.LinnikContract.lamOf q ρ₁)) / (δ * L))
          ≤ (k : ℝ) * (8 * aup / (δ * L)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith only [hαaup]
      have h4 : (k : ℝ) * (8 * aup / (δ * L)) ≤ 4 * (8 * aup / (δ * L)) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      linarith only [h3, h4]
    have h5 : (4 : ℝ) * (8 * aup / (δ * L)) = 32 * aup / (δ * L) := by ring_nf
    have h6 : (32 : ℝ) * aup / (δ * L) ≤ 64 * aup / (δ * L) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith only [hauppos.le]
    linarith only [h2, h5.le, h5.ge, h6]
  have hcC0 : ((a + (Work.LinnikContract.lamOf q ρ₁)) / L) * C₀ ≤ C0c := by
    rw [hC0cdef]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hαaup hLpos.le) hC₀pos.le
  have hcCorr : Corr ≤ Corrc := by
    rw [hCorrdef, hCorrcdef]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have e1 : (a + (Work.LinnikContract.lamOf q ρ₁)) * Sp1 ≤ aup * (Cp * (Real.log L) ^ 2) :=
      le_trans (mul_le_mul_of_nonneg_right hαaup hSpnn1)
        (mul_le_mul_of_nonneg_left hSp1le hauppos.le)
    have e2 : ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L) * Sp2
        ≤ (aup ^ 2 / L) * (Cp * (Real.log L) ^ 3) := by
      refine le_trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hαaup2 hLpos.le) hSpnn2) ?_
      exact mul_le_mul_of_nonneg_left hSp2le (by positivity)
    have e3 : ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 2) * Sp3
        ≤ (aup ^ 3 / L ^ 2) * (Cp * (Real.log L) ^ 4) := by
      refine le_trans (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hαaup3 (by positivity)) hSpnn3) ?_
      exact mul_le_mul_of_nonneg_left hSp3le (by positivity)
    have e4 : (a + (Work.LinnikContract.lamOf q ρ₁)) * Sp1
          + ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 2 / L) * Sp2
          + ((a + (Work.LinnikContract.lamOf q ρ₁)) ^ 3 / L ^ 2) * Sp3
        ≤ aup * (Cp * (Real.log L) ^ 2) + (aup ^ 2 / L) * (Cp * (Real.log L) ^ 3)
          + (aup ^ 3 / L ^ 2) * (Cp * (Real.log L) ^ 4) := by linarith only [e1, e2, e3]
    have e5 : aup * (Cp * (Real.log L) ^ 2) + (aup ^ 2 / L) * (Cp * (Real.log L) ^ 3)
        + (aup ^ 3 / L ^ 2) * (Cp * (Real.log L) ^ 4)
        = aup * Cp * (Real.log L) ^ 2 + (aup ^ 2 / L) * Cp * (Real.log L) ^ 3
          + (aup ^ 3 / L ^ 2) * Cp * (Real.log L) ^ 4 := by ring
    linarith only [e4, e5.le, e5.ge]
  have heE : ∀ e : ℝ, e ≤ E2 + E3 + Fc + Corr + C0c → e ≤ Ee :=
    fun e he => Work.ZeroFreeTables.HB94.Lam0GeEngine.le_E_of_le hEedef hcE2 hcE3 hcCorr he
  have heEz : ∀ e : ℝ, e ≤ E2z + E3z + Fc + Corr + C0c → e ≤ Ee :=
    fun e he => Work.ZeroFreeTables.HB94.Lam0GeEngine.le_E_of_le_zeta hEedef hcE2z hcE3z hcCorr he
  have hEebound : 2 * (K + 1) ^ 2 * Ee ≤ a * ε / 2 := by
    have h : Ee = E := by
      rw [hEedef, hEdef, hC0cdef, hE2cdef, hE3cdef, hCorrcdef, hFcdef]
    rw [h]; exact hEbound
  clear_value Ee Fc C0c Corrc E3c E2c E3z E2z E3 E2 E Corr Sp3 Sp2 Sp1 Cj L Λ aup δ Cn Cz Cp ε₁

  have hFcnn : 0 ≤ Fc := by rw [hFcdef]; positivity
  have hC0cnn : 0 ≤ C0c := by rw [hC0cdef]; positivity
  have hlogNOf : ∀ {N : ℕ} (hNq : N ∣ q), N ≠ 0 → Real.log (N : ℝ) ≤ L := by
    intro N hNq hN0
    rw [hLdef]
    refine Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hN0) ?_
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hNq

  -- ## the case distinction
  by_cases hC : χ₁ ^ 2 = 1
  · -- ### case C : χ₁² = χ₀ (χ₁ real, ρ₁ non-real)
    exact rect_case0 a K ε ha hK hε H W hH1 R hRdef hRnn hRW hΘ ε₁ hε₁pos hε₁bud Ct hCtpos C₀ hC₀pos Cc hCcpos Cz hCzpos δ hδpos hδlt1 q χ₁ ρ₁ ρ₀ hmin hnotreal hzm0 hγ₀ hne hconj hcond L hLdef haL hLt hLpos hLne hL1 hlogLnn h1aL haδL Cj hCjnn Corr hlam₁nn hlam₀nn hγ₁ hlam₁lam₀ hχ₁ne hα0 hlamOf_eq hminPrim hSpr hSzeta hCzZeta hC0b' hnzδ hJOf hCcOf hk1Of hN3 Δ hΔdef β hβdef γ hγdef E2 hE2def E3 hE3def E2z hE2zdef E3z hE3zdef C0c Fc Ee hcFar hcC0 heE heEz hEebound hFcnn hC0cnn hlogNOf hC
  · by_cases hB : χ₁ ^ 3 = 1
    · -- ### case B (χ₁³ = 1, χ₁² ≠ 1)
      exact rect_case1 a K ε ha hK hε H W hH1 R hRdef hRnn hRW hΘ ε₁ hε₁pos hε₁bud Ct hCtpos C₀ hC₀pos Cc hCcpos Cp hCpnn Cz hCzpos Cn hCnpos δ hδpos hδlt1 aup hauppos qabs habs q χ₁ ρ₁ ρ₀ hmin hzm0 hγ₀ hne hcond L hLdef haL hLt hLpos hLne hL1 hlogLnn h1aL haδL Cj hCjnn Corr hlam₁nn hlam₀nn hγ₁ hlam₁lam₀ hχ₁ne hα0 hαaup hlamOf_eq hminPrim hSpr hSzeta hCzZeta hC0b' hnzδ hJOf hCcOf hk1Of hN3 Δ hΔdef β γ E2 hE2def E3 hE3def E2z hE2zdef E3z hE3zdef C0c hC0cdef Fc hFcdef Ee hcFar heE heEz hEebound hFcnn hC0cnn hlogNOf hC hB
    · -- ### case A (χ₁ of order neither 2 nor 3)
      exact rect_case2 a K ε ha hK hε H W hH1 R hRdef hRnn hRW hΘ ε₁ hε₁pos hε₁bud Ct hCtpos C₀ hC₀pos Cc hCcpos Cp hCpnn Cz hCzpos Cn hCnpos δ hδpos hδlt1 aup hauppos qabs habs q χ₁ ρ₁ ρ₀ hmin hzm0 hγ₀ hne hcond L hLdef haL hLt hLpos hLne hL1 hlogLnn h1aL haδL Cj hCjnn Corr hlam₁nn hlam₀nn hγ₁ hlam₁lam₀ hχ₁ne hα0 hαaup hlamOf_eq hminPrim hSpr hSzeta hCzZeta hC0b' hnzδ hJOf hCcOf hk1Of hN3 Δ hΔdef β γ E2 hE2def E3 hE3def E2z hE2zdef E3z hE3zdef C0c hC0cdef Fc hFcdef Ee hcFar heE heEz hEebound hFcnn hC0cnn hlogNOf hC hB
end Work.ZeroFreeTables.OffAxis
