import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.FarBogPair
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/FarZPDefs.lean` — the quadratic/linear split of FS's pair form

The far-leg zero-point slot `Work.BoseFixR.FarZPSumFixW` compares the quadratic form of
FS `eq:BogHamPositive-1`'s pair operator `KzBogFS` at the `ε`-split environment `farEnv`
with `−(½ρ²ℓ³·6M + ErrRes/2)‖f‖²` on the spectral window.  `KzBogFS` bundles **three**
things per mode `k`:

* the *quadratic* (pairing + number) part `𝒜_k(n_k+n_{−k}) + ℬ_k(a_ka_{−k}+a_k†a_{−k}†)`,
  whose Bogoliubov ground energy is the zero point `𝒵_k = 𝒜_k − √(𝒜_k²−ℬ_k²)`;
* the *linear* part `𝒞_k(a_k + a_k† + a_{−k} + a_{−k}†)`, whose cost on the window is paid
  by Cauchy–Schwarz against `⟨n₊⟩ ≤ Cn𝓜` (FS `eq:LocalizedAftercNumber`).

This module provides the split, the per-mode Bogoliubov bound for the quadratic part
(`qw_quadOpFar_ge`, FS `eq:BogIneq` at the half-weighted pair form), and the two summed
forms `qw_KzBogFS_decomp` / `sum_qw_quad_ge` that the far-leg assembly consumes.

Everything here is proved; the hard analytic inputs live elsewhere.
-/

noncomputable section

open scoped Real BigOperators

namespace Work.BoseFixR

open Work.BoseB7 Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-! ## 1. The quadratic part of the pair form, and the summed linear part -/

/-- The quadratic (no linear term) part of FS `eq:BogHamPositive-1`'s pair form at the datum
`(E, ρ)`: `𝒜_k(n_k+n_{−k}) + ℬ_k(a_ka_{−k}+a_k†a_{−k}†)` with `𝒜, ℬ` read off `KzEnvAt E ρ`. -/
noncomputable def quadOpFar (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode) :
    F.H →ₗ[ℝ] F.H :=
  ((KzEnvAt E ρ).A k) • (F.nOp k + F.nOp (-k))
    + ((KzEnvAt E ρ).B k) • (F.a k ∘ₗ F.a (-k) + F.aDag k ∘ₗ F.aDag (-k))

/-- The *linear* part of the pair form, summed over the modes with FS's weight `½`
(the `𝒬₁(z)`-word of FS `eq:SimplifyKz`, at the `c`-number coefficient `cCoefFar`). -/
noncomputable def pairLinOp (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) : F.H →ₗ[ℝ] F.H :=
  ∑ k : Mode, (1 / 2 : ℝ) •
    ((cCoefFar E ρ k) • (F.a k + F.aDag k + F.a (-k) + F.aDag (-k)))

/-- The per-mode split: `pairOpFar = quadOpFar + (linear)`. -/
lemma pairOpFar_eq_quad_add_lin (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode) :
    pairOpFar F E ρ k = quadOpFar F E ρ k
      + (cCoefFar E ρ k) • (F.a k + F.aDag k + F.a (-k) + F.aDag (-k)) := by
  simp only [pairOpFar, quadOpFar, cCoefFar]

/-- **The decomposition of `KzBogFS`**: the quadratic part is the half-weighted sum of the
per-mode `quadOpFar`, the rest is the summed linear operator `pairLinOp`. -/
lemma KzBogFS_eq_sum_quad_add_lin (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) :
    KzBogFS F E ρ = (∑ k : Mode, (1 / 2 : ℝ) • quadOpFar F E ρ k) + pairLinOp F E ρ := by
  rw [KzBogFS_eq_sum_pairOpFar, pairLinOp, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by rw [pairOpFar_eq_quad_add_lin, smul_add]

/-- The `qw`-form of the decomposition. -/
lemma qw_KzBogFS_decomp (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (f : F.H) :
    F.qw f (KzBogFS F E ρ)
      = (∑ k : Mode, (1 / 2 : ℝ) * F.qw f (quadOpFar F E ρ k)) + F.qw f (pairLinOp F E ρ) := by
  rw [KzBogFS_eq_sum_quad_add_lin, FockData.qw_add, qw_sum_smul_zp]

/-! ## 2. The per-mode Bogoliubov bound for the quadratic part -/

/-- The shifted squeezing operator `b_k + c_k` is the adjoint of its dagger for the form `bp`. -/
lemma pairShiftDag_bp (F : FockData Mode) (A B C : Mode → ℝ) (k : Mode) (g f : F.H) :
    F.bp ((pairShiftDag F A B C k) g) f = F.bp g ((pairShift F A B C k) f) := by
  simp only [pairShiftDag, pairShift, LinearMap.add_apply, LinearMap.smul_apply, map_add,
    map_smul, Module.End.one_apply]
  rw [Work.BoseB7.bOpDag_bp F (pairAlpha A B) k g f]

/-- The value of the quadratic part at a state, in the diagonalised form: `qw f (quadOpFar)`
`= 𝒟_k(‖b_kf‖² + ‖b_{−k}f‖²) − 𝒟_kα_k²([a_k,a_k†]+[a_{−k},a_{−k}†])‖f‖²`. -/
lemma qw_quadOpFar_eq (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode)
    (hA : 0 < (KzEnvAt E ρ).A k) (hB : |(KzEnvAt E ρ).B k| ≤ (KzEnvAt E ρ).A k)
    (hAB : 0 < (KzEnvAt E ρ).A k + (KzEnvAt E ρ).B k)
    (hAe : (KzEnvAt E ρ).A (-k) = (KzEnvAt E ρ).A k)
    (hBe : (KzEnvAt E ρ).B (-k) = (KzEnvAt E ρ).B k) (f : F.H) :
    F.qw f (quadOpFar F E ρ k)
      = (pairD (KzEnvAt E ρ).A (KzEnvAt E ρ).B k)
          * (F.normSq ((pairShift F (KzEnvAt E ρ).A (KzEnvAt E ρ).B (fun _ => 0) k) f)
            + F.normSq ((pairShift F (KzEnvAt E ρ).A (KzEnvAt E ρ).B (fun _ => 0) (-k)) f))
        - ((pairD (KzEnvAt E ρ).A (KzEnvAt E ρ).B k
              * (pairAlpha (KzEnvAt E ρ).A (KzEnvAt E ρ).B k) ^ 2
              * (F.ccrK k k + F.ccrK (-k) (-k))) * F.normSq f) := by
  have hid := pairOp_shift_identity F (KzEnvAt E ρ).A (KzEnvAt E ρ).B (fun _ => 0) k
    hA hB hAB hAe hBe (by simp)
  have hquad : quadOpFar F E ρ k
      = ((KzEnvAt E ρ).A k) • (F.nOp k + F.nOp (-k))
        + ((KzEnvAt E ρ).B k) • (F.a k ∘ₗ F.a (-k) + F.aDag k ∘ₗ F.aDag (-k))
        + ((0 : ℝ)) • (F.a k + F.aDag k + F.a (-k) + F.aDag (-k)) := by
    simp [quadOpFar]
  rw [hquad, hid]
  have hK : Work.BoseB6.bogKappaErr ((KzEnvAt E ρ).A k) ((KzEnvAt E ρ).B k) (0 : ℝ) = 0 := by
    simp [Work.BoseB6.bogKappaErr_eq]
  have hbp1 : F.bp (((pairShiftDag F (KzEnvAt E ρ).A (KzEnvAt E ρ).B (fun _ => 0) k) ∘ₗ
      (pairShift F (KzEnvAt E ρ).A (KzEnvAt E ρ).B (fun _ => 0) k)) f) f
      = F.normSq ((pairShift F (KzEnvAt E ρ).A (KzEnvAt E ρ).B (fun _ => 0) k) f) := by
    rw [FockData.normSq, LinearMap.comp_apply, pairShiftDag_bp]
  have hbp2 : F.bp (((pairShiftDag F (KzEnvAt E ρ).A (KzEnvAt E ρ).B (fun _ => 0) (-k)) ∘ₗ
      (pairShift F (KzEnvAt E ρ).A (KzEnvAt E ρ).B (fun _ => 0) (-k))) f) f
      = F.normSq ((pairShift F (KzEnvAt E ρ).A (KzEnvAt E ρ).B (fun _ => 0) (-k)) f) := by
    rw [FockData.normSq, LinearMap.comp_apply, pairShiftDag_bp]
  simp only [smul_eq_mul, map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.comp_apply, Module.End.one_apply, FockData.qw,
    FockData.normSq] at hbp1 hbp2 ⊢
  rw [hbp1, hbp2, hK]
  ring

/-- **FS `eq:BogIneq` per mode, at the quadratic part of the pair form**: `qw f (quadOpFar)`
is bounded below by minus the zero point, provided the box commutators sum to at most `2`. -/
theorem qw_quadOpFar_ge (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (k : Mode)
    (hA : 0 < (KzEnvAt E ρ).A k) (hB : |(KzEnvAt E ρ).B k| ≤ (KzEnvAt E ρ).A k)
    (hAB : 0 < (KzEnvAt E ρ).A k + (KzEnvAt E ρ).B k)
    (hAe : (KzEnvAt E ρ).A (-k) = (KzEnvAt E ρ).A k)
    (hBe : (KzEnvAt E ρ).B (-k) = (KzEnvAt E ρ).B k)
    (hccr : F.ccrK k k + F.ccrK (-k) (-k) ≤ 2) (f : F.H) :
    -(Work.BoseB6.bogZeroPoint ((KzEnvAt E ρ).A k) ((KzEnvAt E ρ).B k)) * F.normSq f
      ≤ F.qw f (quadOpFar F E ρ k) := by
  rw [qw_quadOpFar_eq F E ρ k hA hB hAB hAe hBe f]
  have hDnn : 0 ≤ pairD (KzEnvAt E ρ).A (KzEnvAt E ρ).B k := by
    simp only [pairD]
    exact le_of_lt (Submission.BoseGases.bogD_pos (A := (KzEnvAt E ρ).A k)
      (B := (KzEnvAt E ρ).B k) hA hB)
  have hα2 : 0 ≤ pairD (KzEnvAt E ρ).A (KzEnvAt E ρ).B k
      * (pairAlpha (KzEnvAt E ρ).A (KzEnvAt E ρ).B k) ^ 2 := mul_nonneg hDnn (sq_nonneg _)
  have hzp : 2 * (pairD (KzEnvAt E ρ).A (KzEnvAt E ρ).B k
      * (pairAlpha (KzEnvAt E ρ).A (KzEnvAt E ρ).B k) ^ 2)
      = Work.BoseB6.bogZeroPoint ((KzEnvAt E ρ).A k) ((KzEnvAt E ρ).B k) := by
    simp only [pairD, pairAlpha, KzEnvAt]
    exact two_zpD_mul_zpAlpha_sq E ρ k hA hB
  have hkey : pairD (KzEnvAt E ρ).A (KzEnvAt E ρ).B k
      * (pairAlpha (KzEnvAt E ρ).A (KzEnvAt E ρ).B k) ^ 2
      * (F.ccrK k k + F.ccrK (-k) (-k))
      ≤ Work.BoseB6.bogZeroPoint ((KzEnvAt E ρ).A k) ((KzEnvAt E ρ).B k) := by
    have h := mul_le_mul_of_nonneg_left hccr hα2
    linarith [hzp]
  have h1 : 0 ≤ F.normSq ((pairShift F (KzEnvAt E ρ).A (KzEnvAt E ρ).B (fun _ => 0) k) f) :=
    F.bp_nonneg _
  have h2 : 0 ≤ F.normSq ((pairShift F (KzEnvAt E ρ).A (KzEnvAt E ρ).B (fun _ => 0) (-k)) f) :=
    F.bp_nonneg _
  have h3 : 0 ≤ F.normSq f := F.bp_nonneg f
  nlinarith [hDnn, h1, h2, h3, hkey]

/-! ## 3. The summed quadratic bound -/

/-- The half-weighted sum of the per-mode quadratic lower bounds. -/
theorem sum_qw_quad_ge (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) (f : F.H)
    (hA : ∀ k, 0 < (KzEnvAt E ρ).A k)
    (hB : ∀ k, |(KzEnvAt E ρ).B k| ≤ (KzEnvAt E ρ).A k)
    (hAB : ∀ k, 0 < (KzEnvAt E ρ).A k + (KzEnvAt E ρ).B k)
    (hAe : ∀ k, (KzEnvAt E ρ).A (-k) = (KzEnvAt E ρ).A k)
    (hBe : ∀ k, (KzEnvAt E ρ).B (-k) = (KzEnvAt E ρ).B k)
    (hccr : ∀ k, F.ccrK k k + F.ccrK (-k) (-k) ≤ 2) :
    -((∑ k : Mode, (1 / 2 : ℝ) *
        Work.BoseB6.bogZeroPoint ((KzEnvAt E ρ).A k) ((KzEnvAt E ρ).B k))) * F.normSq f
      ≤ ∑ k : Mode, (1 / 2 : ℝ) * F.qw f (quadOpFar F E ρ k) := by
  have hper : ∀ k : Mode,
      -((1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint ((KzEnvAt E ρ).A k) ((KzEnvAt E ρ).B k))
          * F.normSq f
        ≤ (1 / 2 : ℝ) * F.qw f (quadOpFar F E ρ k) := by
    intro k
    have h := qw_quadOpFar_ge F E ρ k (hA k) (hB k) (hAB k) (hAe k) (hBe k) (hccr k) f
    nlinarith [h]
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset Mode)) => hper k)
  refine le_trans (le_of_eq ?_) hsum
  rw [← Finset.sum_mul, Finset.sum_neg_distrib]

end Work.BoseFixR

namespace Work.BoseFixR

open Work.BoseB7 Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- The scalar `Σ_k ½𝒵_k` of the half-weighted pair zero points at the datum `(E, ρ)`. -/
noncomputable def zeroPointSum (F : FockData Mode) (E : Q3Env Mode) (ρ : ℝ) : ℝ :=
  ∑ k : Mode, (1 / 2 : ℝ) * Work.BoseB6.bogZeroPoint
    ((KzEnvAt E ρ).A k) ((KzEnvAt E ρ).B k)

/-- The continuum mass `M = (2π)^{-3}∫Ŵ₁(q)²/(2‖q‖²)dq` of the far leg's zero-point slot. -/
noncomputable def farMass (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) : ℝ :=
  ((2 * Real.pi) ^ 3)⁻¹ *
    ∫ q : E3, (chat (W1fun v h (ell v μ)) q) ^ 2 / (2 * ‖q‖ ^ 2)

/-- The lattice row `Σ_{k≠0}Ŵ₁(k)²/(2‖k‖²)` over the box lattice of size `N`. -/
noncomputable def latRow (v : E3 → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
    (chat (W1fun v h (ell v μ)) (Work.BoseBoxFock.kmomLab (ell v μ) N k)) ^ 2
      / (2 * ‖Work.BoseBoxFock.kmomLab (ell v μ) N k‖ ^ 2)

end Work.BoseFixR
