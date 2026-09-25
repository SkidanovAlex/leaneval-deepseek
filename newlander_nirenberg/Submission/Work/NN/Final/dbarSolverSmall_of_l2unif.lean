import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Core.CnPert
import Submission.Work.NN.Assemble.DbarJSolver
import Submission.Work.NN.Final.holderNormCongr

/-!
# `dbar_solver_small` from uniform `L²`-solvability and hypoellipticity

This file assembles the target of `Submission/Work/NN/Final/dbar_solver_small.lean` out of

* the **uniform `L²`-solvability** `Work.NN.Final.l2SolvabilityHyp` (the statement of
  `Work.NN.Final.l2Solvability_uniform`): a `C¹` solution of `∂̄_J u = f` on `pd n ρ 2` with
  `‖u‖_{L²} ≤ C Σ_m ‖f·e_m‖_{C^{0,α}(pd n ρ 4)}`;
* the **interior Schauder a priori estimate** `Work.NN.Final.aPrioriEstimate_of_vecHolder`
  (PROVED, axiom-clean): it upgrades the `L²` bound to the `C^{1,α}` estimate of the solver;
* the **inhomogeneous interior regularity** `Work.NN.Final.HypoSmoothHyp` (the statement of
  `Work.NN.Final.dbarCn_smooth_local_of_smooth_datum`), which gives the smoothness field.

No additional analytic input is used; in particular the `C^{1,α}` estimates (the `est` field) are
*derived* from the a priori estimate, so the `L²` statement does not have to carry them.
-/

namespace Work.NN.Final

open scoped ENNReal
open Work.NN.Core

noncomputable section

/-- The uniform `L²`-solvability statement (`Work.NN.Final.l2Solvability_uniform`), packaged as a
`Prop`. -/
def L2SolvabilityHyp (n : ℕ) (α : ℝ) (ρ : Fin n → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (A : Cn n → Cn n →L[ℝ] Cn n),
      (∀ m : ℕ, ContDiff ℝ m A) → ∀ {ε : ℝ}, ε ≤ ε₀ →
      (∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α (fun z => A z (Pi.single i 1) j)
          (pd n ρ 4) ≤ ENNReal.ofReal ε) →
      (∀ z, z ∈ pd n ρ 4 → ∀ v : Cn n,
        (JstdCn n + A) z ((JstdCn n + A) z v) = -v) →
      (∀ u : Cn n → ℂ, (∀ k : ℕ, ContDiff ℝ k u) →
        ∀ z, z ∈ pd n ρ 4 → ∀ V W : Cn n,
          proj02 (JstdCn n + A)
            (fun z' => dOne (fun z'' => dbarCn (JstdCn n + A) u z'') z') z V W = 0) →
      ∀ f : Cn n → Cn n →L[ℝ] ℂ, (∀ m : ℕ, ContDiff ℝ m f) →
        (∀ z, z ∈ pd n ρ 4 → ∀ V : Cn n,
          f z ((JstdCn n + A) z V) = -Complex.I * f z V) →
        (∀ z, z ∈ pd n ρ 4 → ∀ V W : Cn n,
          proj02 (JstdCn n + A) (fun z' => dOne f z') z V W = 0) →
        ∃ u : Cn n → ℂ, ContDiffOn ℝ 1 u (pd n ρ 2) ∧
          (∀ z, z ∈ pd n ρ 2 → ∀ V : Cn n,
            dbarCn (JstdCn n + A) u z V = f z V) ∧
          MeasureTheory.eLpNorm u 2 (MeasureTheory.volume.restrict (pd n ρ 2))
            ≤ ENNReal.ofReal C * ∑ j : Fin n, Work.CR.Flat.holderNorm 0 α
                (fun z => f z (Pi.single j 1)) (pd n ρ 4)

/-- The interior-regularity statement
(`Work.NN.Final.dbarCn_smooth_local_of_smooth_datum`), packaged as a `Prop`. -/
def HypoSmoothHyp (n : ℕ) (α : ℝ) (ρ : Fin n → ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {A : Cn n → Cn n →L[ℝ] Cn n},
      (∀ m : ℕ, ContDiffOn ℝ m A (pd n ρ 4)) → ∀ {ε : ℝ}, ε ≤ ε₀ →
      (∀ i j : Fin n, Work.CR.Flat.holderNorm 0 α (fun z => A z (Pi.single i 1) j)
          (pd n ρ 4) ≤ ENNReal.ofReal ε) →
      (∀ z, z ∈ pd n ρ 4 → ∀ v : Cn n,
        (JstdCn n + A) z ((JstdCn n + A) z v) = -v) →
      ∀ (f : Cn n → Cn n →L[ℝ] ℂ),
        (∀ m : ℕ, ContDiffOn ℝ m (fun z => f z) (pd n ρ 2)) →
        ∀ h : Cn n → ℂ, ContDiffOn ℝ 1 h (pd n ρ 2) →
          (∀ z, z ∈ pd n ρ 2 → ∀ V : Cn n,
            dbarCn (JstdCn n + A) h z V = f z V) →
          ∀ k : ℕ, ContDiffOn ℝ k h (pd n ρ 1)

/-! ## Auxiliary estimates -/

/-- The `C^{0,α}`-bound on the coordinate datum `∂̄_{Jstd+A} z_j`: it is
`(i/2)·(A z e_m)_j`, hence controlled by the values and the Hölder modulus of `A` alone. -/
lemma coordDatum_holderNorm_le {n : ℕ} {α ε : ℝ} {ρ : Fin n → ℝ}
    {A : Cn n → Cn n →L[ℝ] Cn n}
    (hsup : ∀ z, z ∈ pd n ρ 4 → ‖A z‖ ≤ ε)
    (hhold : ∀ z, z ∈ pd n ρ 4 → ∀ z', z' ∈ pd n ρ 4 →
      ‖A z - A z'‖ ≤ ε * ‖z - z'‖ ^ α)
    (hε : 0 ≤ ε) (j m : Fin n) :
    Work.CR.Flat.holderNorm 0 α
        (fun z => dbarCn (JstdCn n + A) (fun y => y j) z (Pi.single m 1)) (pd n ρ 4)
      ≤ ENNReal.ofReal (2 * ε) := by
  -- the coordinate function has the constant derivative `proj j`
  have hfd : ∀ z : Cn n, fderiv ℝ (fun y : Cn n => y j) z
      = (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ) := by
    intro z
    have hlin : (fun y : Cn n => y j) = (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ) := rfl
    rw [hlin, (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ).fderiv]
  -- the value of the datum
  have hpt : ∀ z, dbarCn (JstdCn n + A) (fun y => y j) z (Pi.single m 1)
      = Complex.I / 2 * (A z (Pi.single m 1)) j := by
    intro z
    rw [dbarCn_apply, hfd z]
    have h1 : (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ)
        (((JstdCn n + A) z) (Pi.single m 1))
        = ((JstdCn n + A) z (Pi.single m 1)) j := rfl
    rw [h1]
    have hJ : ((JstdCn n + A) z (Pi.single m 1)) j
        = Complex.I * ((Pi.single m (1 : ℂ) : Cn n) j) + (A z (Pi.single m 1)) j := by
      simp only [ContinuousLinearMap.add_apply, JstdCn_apply, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
    rw [hJ]
    have halg : ∀ x y : ℂ, (1 / 2 : ℂ) * (x + Complex.I * (Complex.I * x + y))
        = Complex.I / 2 * y := by
      intro x y
      have hI : Complex.I * (Complex.I * x) = -x := by
        rw [← mul_assoc, Complex.I_mul_I, neg_mul, one_mul]
      simp only [mul_add, hI]
      ring
    exact halg _ _
  have h1 : Work.CR.Flat.iterDerivNorm 0
      (fun z => dbarCn (JstdCn n + A) (fun y => y j) z (Pi.single m 1)) (pd n ρ 4)
      ≤ ENNReal.ofReal ε := by
    rw [Work.CR.Flat.iterDerivNorm_zero]
    refine iSup₂_le fun z hz => ?_
    rw [hpt z]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖Complex.I / 2 * (A z (Pi.single m 1)) j‖
        = (1 / 2) * ‖(A z (Pi.single m 1)) j‖ := by
          rw [norm_mul, show ‖(Complex.I / 2 : ℂ)‖ = 1 / 2 from by norm_num [Complex.normSq]]
      _ ≤ (1 / 2) * ‖A z (Pi.single m 1)‖ := by
          have h := norm_le_pi_norm (A z (Pi.single m 1)) j
          nlinarith [norm_nonneg ((A z (Pi.single m 1)) j)]
      _ ≤ (1 / 2) * ‖A z‖ := by
          have h := ContinuousLinearMap.le_opNorm (A z) (Pi.single m (1 : ℂ))
          rw [Pi.norm_single, norm_one, mul_one] at h
          nlinarith [norm_nonneg (A z)]
      _ ≤ (1 / 2) * ε := by nlinarith [hsup z hz]
      _ ≤ ε := by nlinarith [hε]
  have h2 : Work.CR.Flat.holderSeminorm 0 α
      (fun z => dbarCn (JstdCn n + A) (fun y => y j) z (Pi.single m 1)) (pd n ρ 4)
      ≤ ENNReal.ofReal ε := by
    refine iSup₂_le fun z hz => iSup₂_le fun z' hz' => iSup_le fun hzz' =>
      ENNReal.ofReal_le_ofReal ?_
    have hd : 0 < ‖z - z'‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzz')
    have hdα : 0 < ‖z - z'‖ ^ α := Real.rpow_pos_of_pos hd α
    rw [div_le_iff₀ hdα, Work.CR.Flat.Holder.norm_iteratedFDerivWithin_zero_sub]
    calc ‖dbarCn (JstdCn n + A) (fun y => y j) z (Pi.single m 1)
            - dbarCn (JstdCn n + A) (fun y => y j) z' (Pi.single m 1)‖
        = ‖Complex.I / 2 * ((A z (Pi.single m 1)) j - (A z' (Pi.single m 1)) j)‖ := by
          rw [hpt z, hpt z']
          ring_nf
      _ ≤ (1 / 2) * ‖(A z - A z') (Pi.single m 1)‖ := by
          rw [norm_mul, show ‖(Complex.I / 2 : ℂ)‖ = 1 / 2 from by norm_num [Complex.normSq]]
          have hsub : (A z (Pi.single m 1)) j - (A z' (Pi.single m 1)) j
              = ((A z - A z') (Pi.single m 1)) j := by simp [Pi.sub_apply]
          rw [hsub]
          have h := norm_le_pi_norm ((A z - A z') (Pi.single m 1)) j
          nlinarith [norm_nonneg (((A z - A z') (Pi.single m 1)) j)]
      _ ≤ (1 / 2) * (ε * ‖z - z'‖ ^ α) := by
          have h := ContinuousLinearMap.le_opNorm (A z - A z') (Pi.single m (1 : ℂ))
          rw [Pi.norm_single, norm_one, mul_one] at h
          nlinarith [hhold z hz z' hz']
      _ ≤ ε * ‖z - z'‖ ^ α := by nlinarith [hε, Real.rpow_pos_of_pos hd α]
  rw [Work.CR.Flat.holderNorm, Finset.sum_range_one]
  calc Work.CR.Flat.iterDerivNorm 0 _ (pd n ρ 4)
        + Work.CR.Flat.holderSeminorm 0 α _ (pd n ρ 4)
      ≤ ENNReal.ofReal ε + ENNReal.ofReal ε := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * ε) := by rw [← ENNReal.ofReal_add hε hε]; congr 1; ring

/-- `ℝ≥0∞` bookkeeping: `C₁·(a + C₂·a) ≤ (C₁(1+C₂))·a`. -/
lemma ennreal_mul_chain {C₁ C₂ : ℝ} (h₁ : 0 ≤ C₁) (h₂ : 0 ≤ C₂) (a : ℝ≥0∞) :
    ENNReal.ofReal C₁ * (a + ENNReal.ofReal C₂ * a)
      ≤ ENNReal.ofReal (C₁ * (1 + C₂)) * a := by
  have hsum : a + ENNReal.ofReal C₂ * a = ENNReal.ofReal (1 + C₂) * a := by
    have h1 : (1 : ℝ≥0∞) + ENNReal.ofReal C₂ = ENNReal.ofReal (1 + C₂) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one h₂]
    rw [← h1, add_mul, one_mul]
  rw [hsum, ← mul_assoc, ← ENNReal.ofReal_mul h₁]


/-! ## Componentwise `VecHolder` bound and smoothness of the coordinate datum -/

/-- A `VecHolder` bound on a `Cn n`-valued map gives the componentwise `C^{0,α}` bound. -/
lemma comp_holderNorm_zero_le {n : ℕ} {α ε : ℝ} {Ω : Set (Cn n)} {φ : Cn n → Cn n}
    (h : VecHolder φ α ε Ω) (hε : 0 ≤ ε) (j : Fin n) :
    Work.CR.Flat.holderNorm 0 α (fun z => φ z j) Ω ≤ ENNReal.ofReal (2 * ε) := by
  have h1 : Work.CR.Flat.Holder.iDN 0 (fun z => φ z j) Ω ≤ ENNReal.ofReal ε := by
    rw [Work.CR.Flat.Holder.iDN_zero_deriv]
    exact iSup₂_le fun z hz =>
      ENNReal.ofReal_le_ofReal (le_trans (norm_le_pi_norm (φ z) j) (h.1 z hz))
  have h2 : Work.CR.Flat.Holder.hSN 0 α (fun z => φ z j) Ω ≤ ENNReal.ofReal ε := by
    rw [Work.CR.Flat.Holder.hSN_zero_deriv]
    refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy =>
      ENNReal.ofReal_le_ofReal ?_
    have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    have hdα : 0 < ‖x - y‖ ^ α := Real.rpow_pos_of_pos hd α
    rw [div_le_iff₀ hdα]
    calc ‖φ x j - φ y j‖ = ‖(φ x - φ y) j‖ := by rw [Pi.sub_apply]
      _ ≤ ‖φ x - φ y‖ := norm_le_pi_norm (φ x - φ y) j
      _ ≤ ε * ‖x - y‖ ^ α := h.2 x hx y hy
  rw [Work.CR.Flat.holderNorm, Finset.sum_range_one]
  calc Work.CR.Flat.Holder.iDN 0 (fun z => φ z j) Ω
        + Work.CR.Flat.Holder.hSN 0 α (fun z => φ z j) Ω
      ≤ ENNReal.ofReal ε + ENNReal.ofReal ε := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * ε) := by
        rw [← ENNReal.ofReal_add hε hε]
        congr 1
        ring

/-- The coordinate datum `z ↦ ∂̄_{Jstd+A} z_j` is smooth for smooth `A`. -/
lemma coordDatum_contDiff {n : ℕ} {A : Cn n → Cn n →L[ℝ] Cn n}
    (hAsm : ∀ m : ℕ, ContDiff ℝ m A) (j : Fin n) (m : ℕ) :
    ContDiff ℝ m (fun z => dbarCn (JstdCn n + A) (fun y => y j) z) := by
  have hfd : ∀ z : Cn n, fderiv ℝ (fun y : Cn n => y j) z
      = (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ) := by
    intro z
    have hlin : (fun y : Cn n => y j) = (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ) := rfl
    rw [hlin, (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ).fderiv]
  have hexp : (fun z : Cn n => dbarCn (JstdCn n + A) (fun y => y j) z)
      = fun z => (1 / 2 : ℝ) • ((ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ)
          + Complex.I • ((ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ).comp
              ((JstdCn n + A) z))) := by
    funext z
    rw [dbarCn, hfd z]
  rw [hexp]
  have hJA : ContDiff ℝ m (fun z : Cn n => ((JstdCn n + A) z : Cn n →L[ℝ] Cn n)) := by
    have hJ : ContDiff ℝ m (fun z : Cn n => ((JstdCn n : Cn n → Cn n →L[ℝ] Cn n) z)) :=
      contDiff_const
    exact hJ.add (hAsm m)
  have hc : ContDiff ℝ m (fun z : Cn n => (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ).comp
        ((JstdCn n + A) z)) :=
    (ContinuousLinearMap.contDiff (((ContinuousLinearMap.compL ℝ (Cn n) (Cn n) ℂ)
      (ContinuousLinearMap.proj j)))).comp hJA
  have hconst : ContDiff ℝ m (fun _ : Cn n => (ContinuousLinearMap.proj j : Cn n →L[ℝ] ℂ)) :=
    contDiff_const
  exact (hconst.add (hc.const_smul (Complex.I : ℂ))).const_smul (1 / 2 : ℝ)

/-- The hypothesis shape of `L2SolvabilityHyp` on a datum. -/
def GoodDatum (n : ℕ) (ρ : Fin n → ℝ) (A : Cn n → Cn n →L[ℝ] Cn n)
    (f : Cn n → Cn n →L[ℝ] ℂ) : Prop :=
  (∀ m : ℕ, ContDiff ℝ m f) ∧
  (∀ z, z ∈ pd n ρ 4 → ∀ V : Cn n, f z ((JstdCn n + A) z V) = -Complex.I * f z V) ∧
  (∀ z, z ∈ pd n ρ 4 → ∀ V W : Cn n,
    proj02 (JstdCn n + A) (fun z' => dOne f z') z V W = 0)

end

end Work.NN.Final
