import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Holder.holderNorm_le_wirtinger_coord
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.CnPert

/-!
# The `n`-dimensional Wirtinger estimate with a `ContDiffOn` hypothesis

This is `Work.CR.Flat.Holder.holderNorm_le_wirtinger_coord` with the global hypothesis
`ContDiff ℝ (k+1) u` replaced by `ContDiffOn ℝ (k+1) u Ω`.  The only place where the global
hypothesis was used is the smoothness `ContDiffOn ℝ K (fun z => dCoord j u z) Ω` of the
Wirtinger derivatives, which is available directly from `ContDiffOn.fderiv_of_isOpen`.
-/

noncomputable section

open scoped NNReal ENNReal
open Set

namespace Work.NN.Core

variable {n : ℕ}

/-! ### Smoothness of the coordinate Wirtinger derivatives, `ContDiffOn` version -/

lemma contDiffOn_dCoord_of_contDiffOn {Ω : Set (Cn n)} (hΩ : IsOpen Ω) {K : ℕ}
    {u : Cn n → ℂ} (hu : ContDiffOn ℝ (K+1) u Ω) (j : Fin n) :
    ContDiffOn ℝ (K:ℕ∞) (fun z => Work.CR.Flat.dCoord j u z) Ω := by
  have hm : ((K:ℕ):WithTop ℕ∞) + 1 ≤ (((K+1:ℕ):WithTop ℕ∞)) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
  have hfd : ContDiffOn ℝ (K:ℕ∞) (fun z => fderiv ℝ u z) Ω :=
    ContDiffOn.fderiv_of_isOpen hu hΩ hm
  have h1 : ContDiffOn ℝ (K:ℕ∞) (fun z => fderiv ℝ u z (Pi.single j (1:ℂ))) Ω :=
    (ContinuousLinearMap.apply ℝ ℂ (Pi.single j (1:ℂ) : Cn n)).contDiff.comp_contDiffOn hfd
  have h2 : ContDiffOn ℝ (K:ℕ∞) (fun z => fderiv ℝ u z (Pi.single j (Complex.I))) Ω :=
    (ContinuousLinearMap.apply ℝ ℂ (Pi.single j (Complex.I) : Cn n)).contDiff.comp_contDiffOn hfd
  have h3 : ContDiffOn ℝ (K:ℕ∞)
      (fun z => Complex.I * fderiv ℝ u z (Pi.single j (Complex.I))) Ω :=
    contDiffOn_const.mul h2
  have h4 : ContDiffOn ℝ (K:ℕ∞) (fun z => fderiv ℝ u z (Pi.single j (1:ℂ))
      - Complex.I * fderiv ℝ u z (Pi.single j (Complex.I))) Ω := h1.sub h3
  have h5 : ContDiffOn ℝ (K:ℕ∞) (fun z => (1/2:ℂ) * (fderiv ℝ u z (Pi.single j (1:ℂ))
      - Complex.I * fderiv ℝ u z (Pi.single j (Complex.I)))) Ω := contDiffOn_const.mul h4
  simpa [Work.CR.Flat.dCoord] using h5

lemma contDiffOn_dbarCoord_of_contDiffOn {Ω : Set (Cn n)} (hΩ : IsOpen Ω) {K : ℕ}
    {u : Cn n → ℂ} (hu : ContDiffOn ℝ (K+1) u Ω) (j : Fin n) :
    ContDiffOn ℝ (K:ℕ∞) (fun z => Work.CR.Flat.dbarCoord j u z) Ω := by
  have hm : ((K:ℕ):WithTop ℕ∞) + 1 ≤ (((K+1:ℕ):WithTop ℕ∞)) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
  have hfd : ContDiffOn ℝ (K:ℕ∞) (fun z => fderiv ℝ u z) Ω :=
    ContDiffOn.fderiv_of_isOpen hu hΩ hm
  have h1 : ContDiffOn ℝ (K:ℕ∞) (fun z => fderiv ℝ u z (Pi.single j (1:ℂ))) Ω :=
    (ContinuousLinearMap.apply ℝ ℂ (Pi.single j (1:ℂ) : Cn n)).contDiff.comp_contDiffOn hfd
  have h2 : ContDiffOn ℝ (K:ℕ∞) (fun z => fderiv ℝ u z (Pi.single j (Complex.I))) Ω :=
    (ContinuousLinearMap.apply ℝ ℂ (Pi.single j (Complex.I) : Cn n)).contDiff.comp_contDiffOn hfd
  have h3 : ContDiffOn ℝ (K:ℕ∞)
      (fun z => Complex.I * fderiv ℝ u z (Pi.single j (Complex.I))) Ω :=
    contDiffOn_const.mul h2
  have h4 : ContDiffOn ℝ (K:ℕ∞) (fun z => fderiv ℝ u z (Pi.single j (1:ℂ))
      + Complex.I * fderiv ℝ u z (Pi.single j (Complex.I))) Ω := h1.add h3
  have h5 : ContDiffOn ℝ (K:ℕ∞) (fun z => (1/2:ℂ) * (fderiv ℝ u z (Pi.single j (1:ℂ))
      + Complex.I * fderiv ℝ u z (Pi.single j (Complex.I)))) Ω := contDiffOn_const.mul h4
  simpa [Work.CR.Flat.dbarCoord] using h5

/-! ### The two estimates -/

/-- Bound on the sup norms of the derivatives of `u` of order `1 ≤ i ≤ k+1`. -/
private lemma iterDerivNorm_le_wirtinger_on {Ω : Set (Cn n)} (hΩ : IsOpen Ω)
    (k : ℕ) (α : ℝ) {u : Cn n → ℂ} (hu : ContDiffOn ℝ (k + 1) u Ω)
    {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k + 1) :
    Work.CR.Flat.iterDerivNorm i u Ω ≤ ∑ j : Fin n,
      (Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dCoord j u z) Ω
        + Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dbarCoord j u z) Ω) := by
  have hΩu : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  have hpred : i - 1 ≤ k := by omega
  have hsucc : i - 1 + 1 = i := by omega
  have hdz : ∀ j : Fin n, ContDiffOn ℝ (((i-1):ℕ):ℕ∞)
      (fun z => Work.CR.Flat.dCoord j u z) Ω := fun j =>
    (contDiffOn_dCoord_of_contDiffOn hΩ hu j).of_le
      (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hpred))
  have hdb : ∀ j : Fin n, ContDiffOn ℝ (((i-1):ℕ):ℕ∞)
      (fun z => Work.CR.Flat.dbarCoord j u z) Ω := fun j =>
    (contDiffOn_dbarCoord_of_contDiffOn hΩ hu j).of_le
      (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hpred))
  have hg : ∀ j : Fin n, ContDiffOn ℝ (((i-1):ℕ):ℕ∞)
      (fun z => Work.CR.Flat.Holder.PhiN j (Work.CR.Flat.dCoord j u z)
        + Work.CR.Flat.Holder.PsiN j (Work.CR.Flat.dbarCoord j u z)) Ω := fun j =>
    ((Work.CR.Flat.Holder.PhiN j).contDiff.comp_contDiffOn (hdz j)).add
      ((Work.CR.Flat.Holder.PsiN j).contDiff.comp_contDiffOn (hdb j))
  have hperj : ∀ j : Fin n,
      Work.CR.Flat.Holder.iDN (i - 1) (fun z => Work.CR.Flat.Holder.PhiN j
          (Work.CR.Flat.dCoord j u z) + Work.CR.Flat.Holder.PsiN j
          (Work.CR.Flat.dbarCoord j u z)) Ω
        ≤ Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dCoord j u z) Ω
          + Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dbarCoord j u z) Ω := by
    intro j
    have hφ : ContDiffOn ℝ (((i-1):ℕ):ℕ∞)
        (fun z => Work.CR.Flat.Holder.PhiN j (Work.CR.Flat.dCoord j u z)) Ω :=
      (Work.CR.Flat.Holder.PhiN j).contDiff.comp_contDiffOn (hdz j)
    have hψ : ContDiffOn ℝ (((i-1):ℕ):ℕ∞)
        (fun z => Work.CR.Flat.Holder.PsiN j (Work.CR.Flat.dbarCoord j u z)) Ω :=
      (Work.CR.Flat.Holder.PsiN j).contDiff.comp_contDiffOn (hdb j)
    calc Work.CR.Flat.Holder.iDN (i - 1) (fun z => Work.CR.Flat.Holder.PhiN j
          (Work.CR.Flat.dCoord j u z) + Work.CR.Flat.Holder.PsiN j
          (Work.CR.Flat.dbarCoord j u z)) Ω
        ≤ Work.CR.Flat.Holder.iDN (i - 1) (fun z => Work.CR.Flat.Holder.PhiN j
              (Work.CR.Flat.dCoord j u z)) Ω
          + Work.CR.Flat.Holder.iDN (i - 1) (fun z => Work.CR.Flat.Holder.PsiN j
              (Work.CR.Flat.dbarCoord j u z)) Ω :=
          Work.CR.Flat.Holder.iDN_add_le (i - 1) hφ hψ hΩu
      _ ≤ ENNReal.ofReal ‖Work.CR.Flat.Holder.PhiN j‖
            * Work.CR.Flat.Holder.iDN (i - 1) (fun z => Work.CR.Flat.dCoord j u z) Ω
          + ENNReal.ofReal ‖Work.CR.Flat.Holder.PsiN j‖
            * Work.CR.Flat.Holder.iDN (i - 1) (fun z => Work.CR.Flat.dbarCoord j u z) Ω :=
          add_le_add (Work.CR.Flat.Holder.comp_linear_le (Work.CR.Flat.Holder.PhiN j) (i - 1) α
              (hdz j) hΩu).1
            (Work.CR.Flat.Holder.comp_linear_le (Work.CR.Flat.Holder.PsiN j) (i - 1) α
              (hdb j) hΩu).1
      _ ≤ Work.CR.Flat.Holder.iDN (i - 1) (fun z => Work.CR.Flat.dCoord j u z) Ω
          + Work.CR.Flat.Holder.iDN (i - 1) (fun z => Work.CR.Flat.dbarCoord j u z) Ω := by
          refine add_le_add ?_ ?_
          · calc ENNReal.ofReal ‖Work.CR.Flat.Holder.PhiN j‖
                  * Work.CR.Flat.Holder.iDN (i - 1) (fun z => Work.CR.Flat.dCoord j u z) Ω
                ≤ 1 * Work.CR.Flat.Holder.iDN (i - 1) (fun z => Work.CR.Flat.dCoord j u z) Ω :=
                  mul_le_mul_of_nonneg_right
                    (ENNReal.ofReal_le_one.mpr (Work.CR.Flat.Holder.norm_PhiN_le j)) bot_le
              _ = Work.CR.Flat.Holder.iDN (i - 1) (fun z => Work.CR.Flat.dCoord j u z) Ω :=
                  one_mul _
          · calc ENNReal.ofReal ‖Work.CR.Flat.Holder.PsiN j‖
                  * Work.CR.Flat.Holder.iDN (i - 1) (fun z => Work.CR.Flat.dbarCoord j u z) Ω
                ≤ 1 * Work.CR.Flat.Holder.iDN (i - 1) (fun z => Work.CR.Flat.dbarCoord j u z) Ω :=
                  mul_le_mul_of_nonneg_right
                    (ENNReal.ofReal_le_one.mpr (Work.CR.Flat.Holder.norm_PsiN_le j)) bot_le
              _ = Work.CR.Flat.Holder.iDN (i - 1) (fun z => Work.CR.Flat.dbarCoord j u z) Ω :=
                  one_mul _
      _ ≤ Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dCoord j u z) Ω
          + Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dbarCoord j u z) Ω :=
          add_le_add (Work.CR.Flat.iterDerivNorm_le_holderNorm k α _ Ω hpred)
            (Work.CR.Flat.iterDerivNorm_le_holderNorm k α _ Ω hpred)
  calc Work.CR.Flat.iterDerivNorm i u Ω
      = Work.CR.Flat.Holder.iDN i u Ω := rfl
    _ = Work.CR.Flat.Holder.iDN ((i-1)+1) u Ω := by rw [hsucc]
    _ = Work.CR.Flat.Holder.iDN (i-1) (fun z => fderivWithin ℝ u Ω z) Ω :=
        (Work.CR.Flat.Holder.iDN_fderivWithin (i-1) u Ω hΩu).symm
    _ = Work.CR.Flat.Holder.iDN (i-1)
          (fun z => ∑ j : Fin n, (Work.CR.Flat.Holder.PhiN j (Work.CR.Flat.dCoord j u z)
            + Work.CR.Flat.Holder.PsiN j (Work.CR.Flat.dbarCoord j u z))) Ω :=
        Work.CR.Flat.Holder.iDN_congr (fun z hz => by
          rw [fderivWithin_of_isOpen hΩ hz, Work.CR.Flat.Holder.fderiv_eq_sum_PhiN_PsiN])
    _ ≤ ∑ j : Fin n,
          Work.CR.Flat.Holder.iDN (i-1) (fun z => Work.CR.Flat.Holder.PhiN j
            (Work.CR.Flat.dCoord j u z) + Work.CR.Flat.Holder.PsiN j
            (Work.CR.Flat.dbarCoord j u z)) Ω :=
        Work.CR.Flat.Holder.iDN_sum_le Finset.univ (i-1) (fun j _ => hg j) hΩu
    _ ≤ ∑ j : Fin n, (Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dCoord j u z) Ω
          + Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dbarCoord j u z) Ω) :=
        Finset.sum_le_sum (fun j _ => hperj j)

/-- Bound on the Hölder seminorms of the derivatives of `u` of order `1 ≤ i ≤ k+1`. -/
private lemma holderSeminorm_le_wirtinger_on {Ω : Set (Cn n)} (hΩ : IsOpen Ω)
    (k : ℕ) (α : ℝ) {u : Cn n → ℂ} (hu : ContDiffOn ℝ (k + 1) u Ω)
    {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k + 1) :
    Work.CR.Flat.holderSeminorm i α u Ω ≤ ∑ j : Fin n,
      (Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dCoord j u z) Ω
        + Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dbarCoord j u z) Ω) := by
  have hΩu : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  have hpred : i - 1 ≤ k := by omega
  have hsucc : i - 1 + 1 = i := by omega
  have hdz : ∀ j : Fin n, ContDiffOn ℝ (((i-1):ℕ):ℕ∞)
      (fun z => Work.CR.Flat.dCoord j u z) Ω := fun j =>
    (contDiffOn_dCoord_of_contDiffOn hΩ hu j).of_le
      (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hpred))
  have hdb : ∀ j : Fin n, ContDiffOn ℝ (((i-1):ℕ):ℕ∞)
      (fun z => Work.CR.Flat.dbarCoord j u z) Ω := fun j =>
    (contDiffOn_dbarCoord_of_contDiffOn hΩ hu j).of_le
      (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hpred))
  have hg : ∀ j : Fin n, ContDiffOn ℝ (((i-1):ℕ):ℕ∞)
      (fun z => Work.CR.Flat.Holder.PhiN j (Work.CR.Flat.dCoord j u z)
        + Work.CR.Flat.Holder.PsiN j (Work.CR.Flat.dbarCoord j u z)) Ω := fun j =>
    ((Work.CR.Flat.Holder.PhiN j).contDiff.comp_contDiffOn (hdz j)).add
      ((Work.CR.Flat.Holder.PsiN j).contDiff.comp_contDiffOn (hdb j))
  have hperj : ∀ j : Fin n,
      Work.CR.Flat.Holder.hSN (i - 1) α (fun z => Work.CR.Flat.Holder.PhiN j
          (Work.CR.Flat.dCoord j u z) + Work.CR.Flat.Holder.PsiN j
          (Work.CR.Flat.dbarCoord j u z)) Ω
        ≤ Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dCoord j u z) Ω
          + Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dbarCoord j u z) Ω := by
    intro j
    have hφ : ContDiffOn ℝ (((i-1):ℕ):ℕ∞)
        (fun z => Work.CR.Flat.Holder.PhiN j (Work.CR.Flat.dCoord j u z)) Ω :=
      (Work.CR.Flat.Holder.PhiN j).contDiff.comp_contDiffOn (hdz j)
    have hψ : ContDiffOn ℝ (((i-1):ℕ):ℕ∞)
        (fun z => Work.CR.Flat.Holder.PsiN j (Work.CR.Flat.dbarCoord j u z)) Ω :=
      (Work.CR.Flat.Holder.PsiN j).contDiff.comp_contDiffOn (hdb j)
    calc Work.CR.Flat.Holder.hSN (i - 1) α (fun z => Work.CR.Flat.Holder.PhiN j
          (Work.CR.Flat.dCoord j u z) + Work.CR.Flat.Holder.PsiN j
          (Work.CR.Flat.dbarCoord j u z)) Ω
        ≤ Work.CR.Flat.Holder.hSN (i - 1) α (fun z => Work.CR.Flat.Holder.PhiN j
              (Work.CR.Flat.dCoord j u z)) Ω
          + Work.CR.Flat.Holder.hSN (i - 1) α (fun z => Work.CR.Flat.Holder.PsiN j
              (Work.CR.Flat.dbarCoord j u z)) Ω :=
          Work.CR.Flat.Holder.hSN_add_le (i - 1) α hφ hψ hΩu
      _ ≤ ENNReal.ofReal ‖Work.CR.Flat.Holder.PhiN j‖
            * Work.CR.Flat.Holder.hSN (i - 1) α (fun z => Work.CR.Flat.dCoord j u z) Ω
          + ENNReal.ofReal ‖Work.CR.Flat.Holder.PsiN j‖
            * Work.CR.Flat.Holder.hSN (i - 1) α (fun z => Work.CR.Flat.dbarCoord j u z) Ω :=
          add_le_add (Work.CR.Flat.Holder.comp_linear_le (Work.CR.Flat.Holder.PhiN j) (i - 1) α
              (hdz j) hΩu).2
            (Work.CR.Flat.Holder.comp_linear_le (Work.CR.Flat.Holder.PsiN j) (i - 1) α
              (hdb j) hΩu).2
      _ ≤ Work.CR.Flat.Holder.hSN (i - 1) α (fun z => Work.CR.Flat.dCoord j u z) Ω
          + Work.CR.Flat.Holder.hSN (i - 1) α (fun z => Work.CR.Flat.dbarCoord j u z) Ω := by
          refine add_le_add ?_ ?_
          · calc ENNReal.ofReal ‖Work.CR.Flat.Holder.PhiN j‖
                  * Work.CR.Flat.Holder.hSN (i - 1) α (fun z => Work.CR.Flat.dCoord j u z) Ω
                ≤ 1 * Work.CR.Flat.Holder.hSN (i - 1) α (fun z => Work.CR.Flat.dCoord j u z) Ω :=
                  mul_le_mul_of_nonneg_right
                    (ENNReal.ofReal_le_one.mpr (Work.CR.Flat.Holder.norm_PhiN_le j)) bot_le
              _ = Work.CR.Flat.Holder.hSN (i - 1) α (fun z => Work.CR.Flat.dCoord j u z) Ω :=
                  one_mul _
          · calc ENNReal.ofReal ‖Work.CR.Flat.Holder.PsiN j‖
                  * Work.CR.Flat.Holder.hSN (i - 1) α (fun z => Work.CR.Flat.dbarCoord j u z) Ω
                ≤ 1 * Work.CR.Flat.Holder.hSN (i - 1) α (fun z => Work.CR.Flat.dbarCoord j u z) Ω :=
                  mul_le_mul_of_nonneg_right
                    (ENNReal.ofReal_le_one.mpr (Work.CR.Flat.Holder.norm_PsiN_le j)) bot_le
              _ = Work.CR.Flat.Holder.hSN (i - 1) α (fun z => Work.CR.Flat.dbarCoord j u z) Ω :=
                  one_mul _
      _ ≤ Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dCoord j u z) Ω
          + Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dbarCoord j u z) Ω :=
          add_le_add (Work.CR.Flat.holderSeminorm_le_holderNorm k α _ Ω hpred)
            (Work.CR.Flat.holderSeminorm_le_holderNorm k α _ Ω hpred)
  calc Work.CR.Flat.holderSeminorm i α u Ω
      = Work.CR.Flat.Holder.hSN i α u Ω := rfl
    _ = Work.CR.Flat.Holder.hSN ((i-1)+1) α u Ω := by rw [hsucc]
    _ = Work.CR.Flat.Holder.hSN (i-1) α (fun z => fderivWithin ℝ u Ω z) Ω :=
        (Work.CR.Flat.Holder.hSN_fderivWithin (i-1) α u Ω hΩu).symm
    _ = Work.CR.Flat.Holder.hSN (i-1) α
          (fun z => ∑ j : Fin n, (Work.CR.Flat.Holder.PhiN j (Work.CR.Flat.dCoord j u z)
            + Work.CR.Flat.Holder.PsiN j (Work.CR.Flat.dbarCoord j u z))) Ω :=
        Work.CR.Flat.Holder.hSN_congr (fun z hz => by
          rw [fderivWithin_of_isOpen hΩ hz, Work.CR.Flat.Holder.fderiv_eq_sum_PhiN_PsiN])
    _ ≤ ∑ j : Fin n,
          Work.CR.Flat.Holder.hSN (i-1) α (fun z => Work.CR.Flat.Holder.PhiN j
            (Work.CR.Flat.dCoord j u z) + Work.CR.Flat.Holder.PsiN j
            (Work.CR.Flat.dbarCoord j u z)) Ω :=
        Work.CR.Flat.Holder.hSN_sum_le Finset.univ (i-1) α (fun j _ => hg j) hΩu
    _ ≤ ∑ j : Fin n, (Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dCoord j u z) Ω
          + Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dbarCoord j u z) Ω) :=
        Finset.sum_le_sum (fun j _ => hperj j)

/-- The `n`-dimensional Wirtinger estimate with a `ContDiffOn` hypothesis: the `C^{k+1,α}` norm of `u` on an open set `Ω` is controlled by its `C^{0,α}` norm together with the `C^{k,α}` norms of the first Wirtinger derivatives `∂_j u`, `∂̄_j u`. This is `Work.CR.Flat.Holder.holderNorm_le_wirtinger_coord` with the global hypothesis `ContDiff ℝ (k+1) u` replaced by `ContDiffOn ℝ (k+1) u Ω` (the proof only uses it through `ContDiffOn.fderiv_of_isOpen`, which is available in this form; every other step uses `UniqueDiffOn Ω` and `fderivWithin_of_isOpen`). -/
theorem holderNorm_le_wirtinger_coord_on {n : ℕ} (k : ℕ) {α : ℝ} {Ω : Set (Cn n)}
    (hΩ : IsOpen Ω) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : Cn n → ℂ, ContDiffOn ℝ (k + 1) u Ω →
      Work.CR.Flat.holderNorm (k + 1) α u Ω
        ≤ ENNReal.ofReal K * (Work.CR.Flat.holderNorm 0 α u Ω
            + ∑ j : Fin n, (Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dCoord j u z) Ω
                + Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dbarCoord j u z) Ω)) := by
  refine ⟨2 * (k + 2), by positivity, ?_⟩
  intro u hu
  set A := Work.CR.Flat.holderNorm 0 α u Ω with hA
  set B := ∑ j : Fin n, (Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dCoord j u z) Ω
      + Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dbarCoord j u z) Ω) with hB
  have hterm : ∀ i ∈ Finset.range ((k+1)+1),
      Work.CR.Flat.iterDerivNorm i u Ω + Work.CR.Flat.holderSeminorm i α u Ω ≤ 2 * (A + B) := by
    intro i hi
    rw [Finset.mem_range] at hi
    obtain h0 | hpos := Nat.eq_zero_or_pos i
    · subst h0
      have h1 : Work.CR.Flat.iterDerivNorm 0 u Ω ≤ A :=
        Work.CR.Flat.iterDerivNorm_le_holderNorm 0 α u Ω le_rfl
      have h2 : Work.CR.Flat.holderSeminorm 0 α u Ω ≤ A :=
        Work.CR.Flat.holderSeminorm_le_holderNorm 0 α u Ω le_rfl
      calc Work.CR.Flat.iterDerivNorm 0 u Ω + Work.CR.Flat.holderSeminorm 0 α u Ω ≤ A + A :=
            add_le_add h1 h2
        _ = 2 * A := (two_mul A).symm
        _ ≤ 2 * (A + B) := by gcongr; exact le_add_right le_rfl
    · have hi1 : 1 ≤ i := hpos
      have hik : i ≤ k + 1 := by omega
      have h1 := iterDerivNorm_le_wirtinger_on hΩ k α hu hi1 hik
      have h2 := holderSeminorm_le_wirtinger_on hΩ k α hu hi1 hik
      calc Work.CR.Flat.iterDerivNorm i u Ω + Work.CR.Flat.holderSeminorm i α u Ω ≤ B + B :=
            add_le_add h1 h2
        _ = 2 * B := (two_mul B).symm
        _ ≤ 2 * (A + B) := by gcongr; exact le_add_left le_rfl
  calc Work.CR.Flat.holderNorm (k + 1) α u Ω
      = ∑ i ∈ Finset.range ((k+1)+1),
          (Work.CR.Flat.iterDerivNorm i u Ω + Work.CR.Flat.holderSeminorm i α u Ω) := rfl
    _ ≤ ∑ i ∈ Finset.range ((k+1)+1), (2 * (A + B)) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (2 * (k + 2)) * (A + B) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← mul_assoc]
        rw [show (2:ℝ≥0∞) = ((2:ℕ):ℝ≥0∞) from by norm_num, ← Nat.cast_mul]
        rw [show ENNReal.ofReal (2 * (k+2) : ℝ) = ((2*(k+2):ℕ) : ℝ≥0∞) from by
          rw [show (2*(k+2):ℝ) = ((2*(k+2):ℕ):ℝ) from by norm_num, ENNReal.ofReal_natCast]]
        congr 1
        ring_nf

end Work.NN.Core
