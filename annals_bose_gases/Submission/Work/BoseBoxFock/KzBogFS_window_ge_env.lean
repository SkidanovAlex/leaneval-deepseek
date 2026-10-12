import Mathlib.Algebra.Algebra.Basic
import Mathlib.Analysis.Real.Sqrt
import Submission.Work.BoseBoxFock.KzBogFS_envCoefSums
import Submission.Work.BoseBoxFock.KzWindowGeAbsA
import Submission.Work.BoseBoxFock.KzWindowGeArith
import Submission.Work.BoseBoxFock.KzWindowGeDagPair
import Submission.Work.BoseBoxFock.KzWindowGeLin
import Submission.Work.BoseBoxFock.bddBelow_valFS_honest
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.KzBogFS_window_ge_env`

The **`ρ`-uniform** version of the window lower bound for the Bogoliubov quadratic
`KzBogFS F E ρ` (FS `eq:BogHamPositive-1`):

> on FS's spectral window `T.NWindow M g` there is a single constant `C ≥ 0`,
> depending on the mode datum `F`, the window data `T`, the environment `E`, the
> window height `M` and the Bessel constant `Cn`, but **not** on `ρ`, such that
>
> `-(C·(1 + ρ^{3/2}))·‖g‖² ≤ ⟨g, KzBogFS F E ρ g⟩` for every `ρ ≥ 0`.

## Why this needs an argument

The sibling module `Work.BoseBoxFock.KzBogFS_window_ge` proves the *statewise* form
`∃ K, ∀ g ∈ window, K‖g‖² ≤ ⟨g, KzBogFS F E ρ g⟩` with the explicit constant

`K(ρ) = -((Σ_k|τ_k + ρŴ₁(k)|) + (Σ_k|ρŴ₁(k)|) + 2Σ_k|C_k|)·(Cn(M+1) + √(Cn(M+1)) + 1)`

where `C_k = (ρ-μ)Ŵ₁(0)χ̂_k√(ρℓ³)`.  That constant is *existentially* quantified, so it
cannot be bounded from outside as a function of `ρ`: uniformity in `ρ` requires the
explicit form.  We reproduce the explicit-constant inequality here
(`KzBogFS_window_ge_explicit`, the only place where the operator algebra is used) and then
record the *analytic* input: each of the three coefficient families grows at most like the
envelope `genv ρ = 1 + √ρ·ρ`, with coefficients built from `E`:

* `|τ_k + ρŴ₁(k)| ≤ (|τ_k| + |Ŵ₁(k)|)·genv ρ`   (`|τ_k| ≤ |τ_k|·genv ρ`, `ρ ≤ genv ρ`),
* `|ρŴ₁(k)| = ρ|Ŵ₁(k)| ≤ |Ŵ₁(k)|·genv ρ`,
* `|C_k| ≤ |Ŵ₁(0)χ̂_k|·√|ℓ|³·(1+|μ|)·genv ρ`, because `|√(ρℓ³)| ≤ √ρ·√|ℓ|³` and
  `|ρ-μ|√ρ ≤ (ρ+|μ|)√ρ ≤ (1+|μ|)genv ρ` (`ρ√ρ ≤ genv ρ`, `√ρ ≤ genv ρ`).

Summing gives a `ρ`-independent coefficient `K0`, and the final constant is
`K0·(Cn(M+1) + √(Cn(M+1)) + 1)`.  (The `√` degree is right: the third family is
`|ρ-μ|·√(ρℓ³) = O(ρ^{3/2})`, exactly the envelope's degree.)  No hypothesis on the
environment `E` is used beyond finiteness of `Mode`: the bound is unconditional in `E`,
as in its statewise companion.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 0. Elementary absolute-value arithmetic -/

private theorem kzbEnv_abs2_le {t u D : ℝ} (h1 : |t| ≤ D) (h2 : |u| ≤ D) : |t + u| ≤ 2 * D := by
  have h := abs_add_le t u
  linarith

private theorem kzbEnv_abs4_le {t u v w D : ℝ} (h1 : |t| ≤ D) (h2 : |u| ≤ D) (h3 : |v| ≤ D)
    (h4 : |w| ≤ D) : |t + u + v + w| ≤ 4 * D := by
  have hb := abs_add_le (t + u) v
  have hc := abs_add_le (t + u + v) w
  have hta : |t + u| ≤ 2 * D := kzbEnv_abs2_le h1 h2
  have htc : |t + u + v| ≤ 2 * D + |v| := by linarith
  linarith [hc, htc, h3, h4]

/-- `x ≥ 0` and `A` arbitrary: the halved sign bound `−½|A|x ≤ ½Ax`. -/
private theorem kzbEnv_half_neg_abs_mul_le {A x : ℝ} (hx : 0 ≤ x) :
    -(1 / 2) * (|A| * x) ≤ (1 / 2) * (A * x) := by
  have h : -(|A| * x) ≤ A * x := by
    have h1 : -|A| ≤ A := neg_abs_le A
    have h2 := mul_le_mul_of_nonneg_right h1 hx
    rwa [neg_mul] at h2
  have h3 := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 1 / 2)
  linarith

/-- `|y| ≤ C₀`, `B` arbitrary: the halved magnitude bound `−½|B|C₀ ≤ ½By`. -/
private theorem kzbEnv_half_mul_abs_le {B y C0 : ℝ} (hy : |y| ≤ C0) :
    -(1 / 2) * (|B| * C0) ≤ (1 / 2) * (B * y) := by
  have h1 : -(|B| * |y|) ≤ B * y := by
    have h := neg_abs_le (B * y)
    rwa [abs_mul] at h
  have h2 : |B| * |y| ≤ |B| * C0 := mul_le_mul_of_nonneg_left hy (abs_nonneg B)
  have h4 : -(|B| * C0) ≤ B * y := by linarith
  have h5 := mul_le_mul_of_nonneg_left h4 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  linarith

/-! ## 1. The mode-by-mode expansion of `KzBogFS` in the Fock form

(Proved here rather than imported: the sibling module `qw_KzBogFS_window_ge` that houses the
same identity is not part of the trusted closure.) -/

private theorem kzbEnv_qw_univ_sum {F : Work.BoseB7.FockData Mode} {ι : Type*} [Fintype ι]
    (Φ : F.H) (X : ι → F.H →ₗ[ℝ] F.H) :
    F.qw Φ (∑ i : ι, X i) = ∑ i : ι, F.qw Φ (X i) := by
  simp only [Work.BoseB7.FockData.qw, LinearMap.sum_apply, map_sum]

/-- FS `eq:BogHamPositive-1`, expanded mode by mode in the Fock form (no hypothesis on `E`). -/
private theorem kzbEnv_qw_decomp (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (ρ : ℝ) (Φ : F.H) :
    F.qw Φ (KzBogFS F E ρ)
      = ∑ k : Mode, (1 / 2 : ℝ) *
          ((E.tau k + ρ * E.W1 k) * (F.bp (F.nOp k Φ) Φ + F.bp (F.nOp (-k) Φ) Φ)
         + (ρ * E.W1 k) * (F.bp ((F.a k ∘ₗ F.a (-k)) Φ) Φ
             + F.bp ((F.aDag k ∘ₗ F.aDag (-k)) Φ) Φ)
         + ((ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)) *
             (F.bp (F.a k Φ) Φ + F.bp (F.aDag k Φ) Φ
              + F.bp (F.a (-k) Φ) Φ + F.bp (F.aDag (-k) Φ) Φ)) := by
  have hunfold : KzBogFS F E ρ
      = ∑ k : Mode, (1 / 2 : ℝ) •
          ((E.tau k + ρ * E.W1 k) • (F.nOp k + F.nOp (-k))
          + (ρ * E.W1 k) • (F.a k ∘ₗ F.a (-k) + F.aDag k ∘ₗ F.aDag (-k))
          + ((ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)) •
              (F.a k + F.aDag k + F.a (-k) + F.aDag (-k))) := rfl
  rw [hunfold, kzbEnv_qw_univ_sum (F := F) Φ
    (fun k : Mode => (1 / 2 : ℝ) •
      ((E.tau k + ρ * E.W1 k) • (F.nOp k + F.nOp (-k))
      + (ρ * E.W1 k) • (F.a k ∘ₗ F.a (-k) + F.aDag k ∘ₗ F.aDag (-k))
      + ((ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)) •
          (F.a k + F.aDag k + F.a (-k) + F.aDag (-k))))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [Work.BoseB7.FockData.qw, LinearMap.add_apply, map_add, LinearMap.smul_apply,
    map_smul, smul_eq_mul]

/-! ## 2. The explicit-constant window bound

This is `Work.BoseBoxFock.KzBogFS_window_ge` with (i) the existential constant resolved and
(ii) the unused hypothesis `Cn ≤ 16` dropped.  The proof expands `KzBogFS` mode by mode and
estimates each of the three rows against the window. -/

theorem KzBogFS_window_ge_explicit (F : Work.BoseB7.FockData Mode)
    (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (ρ M Cn : ℝ) (hCn0 : 0 ≤ Cn) (hM : 0 ≤ M)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f)
    {g : F.H} (hg : T.NWindow M g) :
    -(((∑ k : Mode, |E.tau k + ρ * E.W1 k|) + (∑ k : Mode, |ρ * E.W1 k|)
        + 2 * (∑ k : Mode, |(ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)|))
      * (Cn * (M + 1) + Real.sqrt (Cn * (M + 1)) + 1)) * F.normSq g
      ≤ F.qw g (KzBogFS F E ρ) := by
  set SA : ℝ := ∑ k : Mode, |E.tau k + ρ * E.W1 k| with hSA
  set SB : ℝ := ∑ k : Mode, |ρ * E.W1 k| with hSB
  set SC : ℝ := ∑ k : Mode, |(ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)|
    with hSC
  have hSA0 : 0 ≤ SA := by rw [hSA]; exact Finset.sum_nonneg (fun k _ => abs_nonneg _)
  have hSB0 : 0 ≤ SB := by rw [hSB]; exact Finset.sum_nonneg (fun k _ => abs_nonneg _)
  have hSC0 : 0 ≤ SC := by rw [hSC]; exact Finset.sum_nonneg (fun k _ => abs_nonneg _)
  have hn : 0 ≤ F.normSq g := F.bp_nonneg g
  have hCnM1 : 0 ≤ Cn * (M + 1) := mul_nonneg hCn0 (by linarith)
  -- the per-mode lower bound
  have hterm : ∀ k ∈ (Finset.univ : Finset Mode),
      -(1 / 2) * (|E.tau k + ρ * E.W1 k| * (F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g)
        + |ρ * E.W1 k| * (2 * (Cn * (M + 1) * F.normSq g))
        + |(ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)|
            * (4 * (Real.sqrt (Cn * (M + 1)) * F.normSq g)))
      ≤ (1 / 2) * ((E.tau k + ρ * E.W1 k) * (F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g)
        + (ρ * E.W1 k) * (F.bp ((F.a k ∘ₗ F.a (-k)) g) g
            + F.bp ((F.aDag k ∘ₗ F.aDag (-k)) g) g)
        + ((ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)) *
            (F.bp (F.a k g) g + F.bp (F.aDag k g) g
              + F.bp (F.a (-k) g) g + F.bp (F.aDag (-k) g) g)) := by
    intro k _
    have hp : 0 ≤ F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g :=
      add_nonneg (Work.BoseB7.bp_nOp_nonneg F k g) (Work.BoseB7.bp_nOp_nonneg F (-k) g)
    have hpair : |F.bp ((F.a k ∘ₗ F.a (-k)) g) g| ≤ Cn * (M + 1) * F.normSq g := by
      have h := window_a_pair_le F T Cn hCn0 hBessel hM hg k (-k)
      simpa only [LinearMap.comp_apply] using h
    have hpaird : |F.bp ((F.aDag k ∘ₗ F.aDag (-k)) g) g| ≤ Cn * (M + 1) * F.normSq g := by
      have h := KzWindowGeDagPair F T Cn hCn0 hBessel hM hg k (-k)
      simpa only [LinearMap.comp_apply] using h
    have hlin : ∀ j : Mode, |F.bp (F.a j g) g| ≤ Real.sqrt (Cn * (M + 1)) * F.normSq g :=
      fun j => KzWindowGeLin F T Cn hCn0 hBessel hM hg j
    have hlinD : ∀ j : Mode,
        |F.bp (F.aDag j g) g| ≤ Real.sqrt (Cn * (M + 1)) * F.normSq g := by
      intro j
      have h1 : F.bp (F.aDag j g) g = F.bp (F.a j g) g := by
        rw [F.aDag_adjoint, F.bp_symm]
      rw [h1]
      exact hlin j
    have h1 : -(1 / 2) * (|E.tau k + ρ * E.W1 k| *
          (F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g))
        ≤ (1 / 2) * ((E.tau k + ρ * E.W1 k) *
            (F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g)) :=
      kzbEnv_half_neg_abs_mul_le (A := E.tau k + ρ * E.W1 k) hp
    have h2 : -(1 / 2) * (|ρ * E.W1 k| * (2 * (Cn * (M + 1) * F.normSq g)))
        ≤ (1 / 2) * ((ρ * E.W1 k) * (F.bp ((F.a k ∘ₗ F.a (-k)) g) g
            + F.bp ((F.aDag k ∘ₗ F.aDag (-k)) g) g)) :=
      kzbEnv_half_mul_abs_le (B := ρ * E.W1 k) (C0 := 2 * (Cn * (M + 1) * F.normSq g))
        (kzbEnv_abs2_le hpair hpaird)
    have h3 : -(1 / 2) * (|(ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)|
          * (4 * (Real.sqrt (Cn * (M + 1)) * F.normSq g)))
        ≤ (1 / 2) * (((ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)) *
            (F.bp (F.a k g) g + F.bp (F.aDag k g) g
              + F.bp (F.a (-k) g) g + F.bp (F.aDag (-k) g) g)) :=
      kzbEnv_half_mul_abs_le (kzbEnv_abs4_le (hlin k) (hlinD k) (hlin (-k)) (hlinD (-k)))
    linarith [h1, h2, h3]
  -- the mode-by-mode expansion
  have hdecomp : F.qw g (KzBogFS F E ρ)
      = ∑ k : Mode, (1 / 2 : ℝ) *
          ((E.tau k + ρ * E.W1 k) * (F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g)
         + (ρ * E.W1 k) * (F.bp ((F.a k ∘ₗ F.a (-k)) g) g
             + F.bp ((F.aDag k ∘ₗ F.aDag (-k)) g) g)
         + ((ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)) *
             (F.bp (F.a k g) g + F.bp (F.aDag k g) g
              + F.bp (F.a (-k) g) g + F.bp (F.aDag (-k) g) g)) :=
    kzbEnv_qw_decomp F E ρ g
  have step1 : -(1 / 2) * (∑ k : Mode,
      (|E.tau k + ρ * E.W1 k| * (F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g)
        + |ρ * E.W1 k| * (2 * (Cn * (M + 1) * F.normSq g))
        + |(ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)|
            * (4 * (Real.sqrt (Cn * (M + 1)) * F.normSq g))))
      ≤ F.qw g (KzBogFS F E ρ) := by
    have hsum1 : (∑ k : Mode,
          -(1 / 2) * (|E.tau k + ρ * E.W1 k| * (F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g)
            + |ρ * E.W1 k| * (2 * (Cn * (M + 1) * F.normSq g))
            + |(ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)|
                * (4 * (Real.sqrt (Cn * (M + 1)) * F.normSq g))))
        ≤ ∑ k : Mode, (1 / 2) *
          ((E.tau k + ρ * E.W1 k) * (F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g)
         + (ρ * E.W1 k) * (F.bp ((F.a k ∘ₗ F.a (-k)) g) g
             + F.bp ((F.aDag k ∘ₗ F.aDag (-k)) g) g)
         + ((ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)) *
             (F.bp (F.a k g) g + F.bp (F.aDag k g) g
              + F.bp (F.a (-k) g) g + F.bp (F.aDag (-k) g) g)) :=
      Finset.sum_le_sum hterm
    have h2 : (∑ k : Mode,
          -(1 / 2) * (|E.tau k + ρ * E.W1 k| * (F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g)
            + |ρ * E.W1 k| * (2 * (Cn * (M + 1) * F.normSq g))
            + |(ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)|
                * (4 * (Real.sqrt (Cn * (M + 1)) * F.normSq g))))
        = -(1 / 2) * (∑ k : Mode,
          (|E.tau k + ρ * E.W1 k| * (F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g)
            + |ρ * E.W1 k| * (2 * (Cn * (M + 1) * F.normSq g))
            + |(ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)|
                * (4 * (Real.sqrt (Cn * (M + 1)) * F.normSq g)))) := by
      rw [Finset.mul_sum]
    rw [h2] at hsum1
    rw [hdecomp]
    exact hsum1
  -- the `ℓ¹`-bounds for the three rows of coefficients
  have hY : (∑ k : Mode,
      (|E.tau k + ρ * E.W1 k| * (F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g)
        + |ρ * E.W1 k| * (2 * (Cn * (M + 1) * F.normSq g))
        + |(ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)|
            * (4 * (Real.sqrt (Cn * (M + 1)) * F.normSq g))))
      ≤ SA * (2 * Cn * M * F.normSq g) + SB * (2 * Cn * (M + 1) * F.normSq g)
        + SC * (4 * Real.sqrt (Cn * (M + 1)) * F.normSq g) := by
    have hA : (∑ k : Mode, |E.tau k + ρ * E.W1 k| *
          (F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g))
        ≤ SA * (2 * Cn * M * F.normSq g) := by
      have h := KzWindowGeAbsA F T Cn hCn0 hBessel hM hg
        (fun k : Mode => E.tau k + ρ * E.W1 k)
      rw [hSA]
      linarith [h]
    have hB : (∑ k : Mode, |ρ * E.W1 k| * (2 * (Cn * (M + 1) * F.normSq g)))
        = SB * (2 * Cn * (M + 1) * F.normSq g) := by
      rw [hSB, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    have hC : (∑ k : Mode, |(ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)|
          * (4 * (Real.sqrt (Cn * (M + 1)) * F.normSq g)))
        = SC * (4 * Real.sqrt (Cn * (M + 1)) * F.normSq g) := by
      rw [hSC, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    linarith [hA, hB, hC]
  have step2 : -(1 / 2) * (SA * (2 * Cn * M * F.normSq g)
        + SB * (2 * Cn * (M + 1) * F.normSq g)
        + SC * (4 * Real.sqrt (Cn * (M + 1)) * F.normSq g))
      ≤ -(1 / 2) * (∑ k : Mode,
      (|E.tau k + ρ * E.W1 k| * (F.bp (F.nOp k g) g + F.bp (F.nOp (-k) g) g)
        + |ρ * E.W1 k| * (2 * (Cn * (M + 1) * F.normSq g))
        + |(ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)|
            * (4 * (Real.sqrt (Cn * (M + 1)) * F.normSq g)))) := by
    linarith [hY]
  have step3 : -((SA + SB + 2 * SC) * (Cn * (M + 1) + Real.sqrt (Cn * (M + 1)) + 1)
        * F.normSq g)
      ≤ -(1 / 2) * (SA * (2 * Cn * M * F.normSq g)
        + SB * (2 * Cn * (M + 1) * F.normSq g)
        + SC * (4 * Real.sqrt (Cn * (M + 1)) * F.normSq g)) :=
    KzWindowGeArith hSA0 hSB0 hSC0 hCn0 hM hn
  have hK : -(((∑ k : Mode, |E.tau k + ρ * E.W1 k|) + (∑ k : Mode, |ρ * E.W1 k|)
        + 2 * (∑ k : Mode, |(ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)|))
      * (Cn * (M + 1) + Real.sqrt (Cn * (M + 1)) + 1)) * F.normSq g
      = -((SA + SB + 2 * SC) * (Cn * (M + 1) + Real.sqrt (Cn * (M + 1)) + 1)
          * F.normSq g) := by
    rw [hSA, hSB, hSC]
    ring
  rw [hK]
  exact le_trans (le_trans step3 step2) step1

/-! ## 3. The `ρ`-uniform constant

`kzbEnv_combine` is the purely scalar closing step: a `ρ`-independent bound `S ≤ K0·genv ρ`
on the coefficient sum `S` upgrades the statewise bound `-(S·DM)‖g‖² ≤ ⟨g, Kg⟩` into
`-((K0·DM)·genv ρ)‖g‖² ≤ ⟨g, Kg⟩`. -/

private theorem kzbEnv_combine {S K0 gρ DM n qw : ℝ} (hcoef : S ≤ K0 * gρ) (hDM0 : 0 ≤ DM)
    (hn : 0 ≤ n) (hexp : -(S * DM) * n ≤ qw) : -((K0 * DM) * gρ) * n ≤ qw := by
  have h1 : S * DM ≤ (K0 * gρ) * DM := mul_le_mul_of_nonneg_right hcoef hDM0
  have h2 : S * DM * n ≤ (K0 * gρ) * DM * n := mul_le_mul_of_nonneg_right h1 hn
  have h3 : -((K0 * DM) * gρ) * n = -((K0 * gρ) * DM * n) := by ring
  rw [h3]
  linarith [h2, hexp]

theorem KzBogFS_window_ge_env {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (M Cn : ℝ) (hM : 0 ≤ M) (hCn0 : 0 ≤ Cn)
    (hBessel : ∀ f : F.H, F.bp ((∑ k : Mode, F.nOp k) f) f ≤ Cn * F.bp (T.N f) f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 ≤ ρ → ∀ g : F.H, T.NWindow M g →
      -(C * Work.BoseBoxFock.genv ρ) * F.normSq g ≤ F.qw g (Work.BoseBoxFock.KzBogFS F E ρ) := by
  -- the `ρ`-free coefficient of the envelope and the (statewise) Bessel factor
  set K0 : ℝ := (∑ k : Mode, (|E.tau k| + |E.W1 k|)) + (∑ k : Mode, |E.W1 k|)
      + 2 * (∑ k : Mode, |E.W1 0 * E.hatChi k| * Real.sqrt (|E.ell| ^ 3) * (1 + |E.mu|))
    with hK0
  set DM : ℝ := Cn * (M + 1) + Real.sqrt (Cn * (M + 1)) + 1 with hDM
  have hK00 : 0 ≤ K0 := by
    rw [hK0]
    have h1 : 0 ≤ ∑ k : Mode, (|E.tau k| + |E.W1 k|) :=
      Finset.sum_nonneg (fun k _ => add_nonneg (abs_nonneg (E.tau k)) (abs_nonneg (E.W1 k)))
    have h2 : 0 ≤ ∑ k : Mode, |E.W1 k| :=
      Finset.sum_nonneg (fun k _ => abs_nonneg (E.W1 k))
    have h3 : 0 ≤ ∑ k : Mode,
        |E.W1 0 * E.hatChi k| * Real.sqrt (|E.ell| ^ 3) * (1 + |E.mu|) :=
      Finset.sum_nonneg (fun k _ => mul_nonneg
        (mul_nonneg (abs_nonneg (E.W1 0 * E.hatChi k)) (Real.sqrt_nonneg (|E.ell| ^ 3)))
        (add_nonneg zero_le_one (abs_nonneg E.mu)))
    linarith
  have hDM0 : 0 ≤ DM := by
    rw [hDM]
    have h1 : 0 ≤ Cn * (M + 1) := mul_nonneg hCn0 (by linarith)
    have h2 : 0 ≤ Real.sqrt (Cn * (M + 1)) := Real.sqrt_nonneg _
    linarith
  refine ⟨K0 * DM, mul_nonneg hK00 hDM0, ?_⟩
  intro ρ hρ g hg
  -- the coefficient sum of the statewise bound, and its `genv`-uniform version
  have hcoef : (∑ k : Mode, |E.tau k + ρ * E.W1 k|) + (∑ k : Mode, |ρ * E.W1 k|)
      + 2 * (∑ k : Mode, |(ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)|)
      ≤ K0 * genv ρ := by
    rw [hK0]
    exact KzBogFS_envCoefSums E ρ hρ
  -- the statewise window bound with the explicit constant
  have hexp : -(((∑ k : Mode, |E.tau k + ρ * E.W1 k|) + (∑ k : Mode, |ρ * E.W1 k|)
        + 2 * (∑ k : Mode, |(ρ - E.mu) * E.W1 0 * E.hatChi k * Real.sqrt (ρ * E.ell ^ 3)|))
      * DM) * F.normSq g ≤ F.qw g (KzBogFS F E ρ) := by
    simpa only [hDM] using KzBogFS_window_ge_explicit F T E ρ M Cn hCn0 hM hBessel hg
  have hn : 0 ≤ F.normSq g := F.bp_nonneg g
  exact kzbEnv_combine hcoef hDM0 hn hexp

end Work.BoseBoxFock
