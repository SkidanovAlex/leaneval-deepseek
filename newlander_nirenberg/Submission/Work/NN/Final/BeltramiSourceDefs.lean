import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.NN.Core.DbarCnPertAux
import Submission.Work.NN.Core.dbarCn_implicit_form
import Submission.Work.NN.Core.dbarCoord_eq_beltramiCoeff
import Submission.Work.NN.Core.dbarCoord_eq_beltramiCoeff_pointwise
import Submission.Work.NN.Core.isInvertible_one_add_and_inverse_norm_le
import Submission.Work.NN.Core.betaCoef_Bop_contDiff
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
# The source term of the decoupled Beltrami form of the inhomogeneous `\bar\partial`-equation

...
-/

namespace Work.NN.Final

open scoped NNReal ENNReal ContDiff
open Set

noncomputable section

/-! ## The source term of the decoupled Beltrami form of the inhomogeneous equation -/

/-- The source term of the decoupled Beltrami system attached to the inhomogeneous equation
`∂̄_{Jstd + A} u = f`: the `(1 + BopBar A z)⁻¹`-image of the datum vector `f z e_·`. -/
noncomputable def beltramiSource {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ) (z : Work.NN.Core.Cn n) :
    Work.NN.Core.Cn n :=
  ContinuousLinearMap.inverse (1 + Work.NN.Core.BopBar A z)
    (fun j : Fin n => f z (Pi.single j (1 : ℂ)))

/-- **Pointwise Beltrami form of the inhomogeneous perturbed `∂̄`-equation.**

If `∂̄_{Jstd + A} u` equals the datum `f` at `z` in every coordinate direction `e_k`, and
`‖BopBar A z‖ ≤ 1/4`, then at `z` the Wirtinger derivatives of `u` satisfy the decoupled
Beltrami system with the source term `beltramiSource A f z`:

`∂̄_k u(z) = Σ_j beltramiCoef A k j z · ∂_j u(z) + beltramiSource A f z k`. -/
theorem dbarCoord_eq_beltramiCoeff_source_pointwise {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ)
    (u : Work.NN.Core.Cn n → ℂ) (z : Work.NN.Core.Cn n)
    (hquarter : ‖Work.NN.Core.BopBar A z‖ ≤ 1 / 4)
    (hz : ∀ k : Fin n,
      Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z (Pi.single k 1)
        = f z (Pi.single k 1))
    (k : Fin n) :
    Work.CR.Flat.dbarCoord k u z
      = ∑ j : Fin n, Work.NN.Core.beltramiCoef A k j z * Work.CR.Flat.dCoord j u z
        + beltramiSource A f z k := by
  have hInv : (1 + Work.NN.Core.BopBar A z).IsInvertible :=
    (Work.NN.Core.isInvertible_one_add_and_inverse_norm_le hquarter).1
  have hsys : (1 + Work.NN.Core.BopBar A z) (fun j => Work.CR.Flat.dbarCoord j u z)
      = (fun j : Fin n => f z (Pi.single j (1 : ℂ)))
        + Work.NN.Core.Bop A z (fun j => Work.CR.Flat.dCoord j u z) := by
    have h := Work.NN.Core.dbarCn_implicit_form A u z
    rw [show (fun j : Fin n => Work.NN.Core.dbarCn (Work.NN.Core.JstdCn n + A) u z
          (Pi.single j (1 : ℂ))) = fun j : Fin n => f z (Pi.single j (1 : ℂ)) from
      funext fun j => hz j] at h
    exact h
  have hinv0 : ContinuousLinearMap.inverse (1 + Work.NN.Core.BopBar A z)
      ((fun j : Fin n => f z (Pi.single j (1 : ℂ)))
        + Work.NN.Core.Bop A z (fun j => Work.CR.Flat.dCoord j u z))
      = (fun j => Work.CR.Flat.dbarCoord j u z) := by
    have h0 := ContinuousLinearMap.IsInvertible.inverse_apply_self hInv
      (fun j => Work.CR.Flat.dbarCoord j u z)
    rwa [hsys] at h0
  have hsplit : ContinuousLinearMap.inverse (1 + Work.NN.Core.BopBar A z)
      ((fun j : Fin n => f z (Pi.single j (1 : ℂ)))
        + Work.NN.Core.Bop A z (fun j => Work.CR.Flat.dCoord j u z))
      = beltramiSource A f z
        + Work.NN.Core.beltramiCoeff A z (fun j => Work.CR.Flat.dCoord j u z) := by
    rw [map_add]
    rfl
  have hlast : (Work.NN.Core.beltramiCoeff A z (fun j => Work.CR.Flat.dCoord j u z)) k
      = ∑ j : Fin n, Work.NN.Core.beltramiCoef A k j z * Work.CR.Flat.dCoord j u z := by
    have hlinμ : ∀ (c : ℂ) (v : Work.NN.Core.Cn n),
        Work.NN.Core.beltramiCoeff A z (c • v) = c • Work.NN.Core.beltramiCoeff A z v := by
      intro c v
      have hlin : ∀ (c : ℂ) (v : Work.NN.Core.Cn n),
          Work.NN.Core.BopBar A z (c • v) = c • Work.NN.Core.BopBar A z v :=
        fun c v => (Work.NN.Core.Bop_map_smul A z v c).2
      rw [Work.NN.Core.beltramiCoeff, mul_apply_eq_comp,
        mul_apply_eq_comp, (Work.NN.Core.Bop_map_smul A z v c).1]
      exact Work.NN.Core.inverse_one_add_map_smul hInv hlin c (Work.NN.Core.Bop A z v)
    have hw : (fun j => Work.CR.Flat.dCoord j u z)
        = ∑ j : Fin n, (Work.CR.Flat.dCoord j u z) • (Pi.single j (1 : ℂ) : Work.NN.Core.Cn n) := by
      ext m
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Finset.sum_eq_single m]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne (Ne.symm hb)]
      · intro h
        exact absurd (Finset.mem_univ m) h
    rw [hw, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hlinμ, Pi.smul_apply, smul_eq_mul, Work.NN.Core.beltramiCoef]
    ring
  have h2 : (fun j => Work.CR.Flat.dbarCoord j u z)
      = beltramiSource A f z
        + Work.NN.Core.beltramiCoeff A z (fun j => Work.CR.Flat.dCoord j u z) := by
    rw [← hsplit, ← hinv0]
  change (fun j => Work.CR.Flat.dbarCoord j u z) k
      = (∑ j : Fin n, Work.NN.Core.beltramiCoef A k j z * Work.CR.Flat.dCoord j u z)
        + beltramiSource A f z k
  rw [h2, Pi.add_apply, hlast]
  ring

/-! ## Smoothness of `BopBar` for merely smooth `A` (a local copy of the private argument of
`Work.NN.Core.exists_beltramiCoef_small_smooth`) -/

/-- The continuous linear map `c ↦ f.smulRight c`. -/
private noncomputable def smulRightCLMS {n : ℕ} (f : Work.NN.Core.Cn n →L[ℝ] ℂ) :
    ℂ →L[ℝ] (Work.NN.Core.Cn n →L[ℝ] ℂ) :=
  LinearMap.mkContinuous (f.smulRightₗ) ‖f‖ (fun c => by
    rw [ContinuousLinearMap.coe_smulRightₗ]
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
    rw [ContinuousLinearMap.smulRight_apply, norm_smul]
    calc ‖f v‖ * ‖c‖ ≤ (‖f‖ * ‖v‖) * ‖c‖ := by gcongr; exact f.le_opNorm v
      _ = ‖f‖ * ‖c‖ * ‖v‖ := by ring)

private lemma smulRightCLMS_apply {n : ℕ} (f : Work.NN.Core.Cn n →L[ℝ] ℂ) (c : ℂ) :
    smulRightCLMS f c = f.smulRight c := by
  simp only [smulRightCLMS, LinearMap.mkContinuous_apply, ContinuousLinearMap.coe_smulRightₗ]

private theorem contDiff_pi_smulRight_betaCoefS {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => ContinuousLinearMap.pi (fun k : Fin n => ∑ j : Fin n,
        ContinuousLinearMap.smulRight
          (ContinuousLinearMap.proj j : Work.NN.Core.Cn n →L[ℝ] ℂ)
          (φ (Work.NN.Core.betaCoef A k j z)))) := by
  have hβ : ∀ k j : Fin n, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => Work.NN.Core.betaCoef A k j z) :=
    fun k j => by unfold Work.NN.Core.betaCoef; fun_prop
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Work.NN.Core.Cn n => fun k : Fin n => ∑ j : Fin n,
        ContinuousLinearMap.smulRight
          (ContinuousLinearMap.proj j : Work.NN.Core.Cn n →L[ℝ] ℂ)
          (φ (Work.NN.Core.betaCoef A k j z))) := by
    refine contDiff_pi.mpr (fun k => ?_)
    have hsum : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Work.NN.Core.Cn n =>
        ∑ j : Fin n, ContinuousLinearMap.smulRight
          (ContinuousLinearMap.proj j : Work.NN.Core.Cn n →L[ℝ] ℂ)
          (φ (Work.NN.Core.betaCoef A k j z))) := by
      refine ContDiff.sum (s := Finset.univ) (f := fun (j : Fin n) (z : Work.NN.Core.Cn n) =>
        ContinuousLinearMap.smulRight
          (ContinuousLinearMap.proj j : Work.NN.Core.Cn n →L[ℝ] ℂ)
          (φ (Work.NN.Core.betaCoef A k j z))) (fun j _ => ?_)
      have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z => φ (Work.NN.Core.betaCoef A k j z)) := hφ.comp (hβ k j)
      have h2 := (smulRightCLMS (ContinuousLinearMap.proj j : Work.NN.Core.Cn n →L[ℝ] ℂ)).contDiff.comp h1
      convert h2 using 1
      funext z
      rw [Function.comp_apply, smulRightCLMS_apply]
    simpa using hsum
  have h3 := (ContinuousLinearEquiv.comp_contDiff_iff
      (ContinuousLinearMap.piEquivL ℝ (Work.NN.Core.Cn n) (fun _ : Fin n => ℂ))).mpr hg
  convert h3 using 1
  funext z
  rw [Function.comp_apply, ContinuousLinearMap.piEquivL_apply]

private theorem BopBar_contDiff_smooth {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Work.NN.Core.BopBar A z) := by
  have hconj : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (starRingEnd ℂ : ℂ → ℂ) := by
    have h : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (⇑Complex.conjCLE) :=
      Complex.conjCLE.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    rwa [funext Complex.conjCLE_apply] at h
  simpa only [Work.NN.Core.BopBar] using contDiff_pi_smulRight_betaCoefS A hA hconj

/-- The source term is smooth in `z` when `A` and `f` are smooth (and `BopBar A` is small enough
that `1 + BopBar A z` is invertible, so that the inverse map `z ↦ (1 + BopBar A z)⁻¹` is smooth). -/
theorem beltramiSource_contDiff {n : ℕ}
    (A : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
    (hA : ∀ m : ℕ, ContDiff ℝ m A)
    (hquarter : ∀ z, ‖Work.NN.Core.BopBar A z‖ ≤ 1 / 4)
    (f : Work.NN.Core.Cn n → Work.NN.Core.Cn n →L[ℝ] ℂ) (hf : ∀ m : ℕ, ContDiff ℝ m f)
    (k : Fin n) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => beltramiSource A f z k) := by
  have hBopBar : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => Work.NN.Core.BopBar A z) := BopBar_contDiff_smooth A (contDiff_infty.mpr hA)
  have hInv : ∀ z, (1 + Work.NN.Core.BopBar A z).IsInvertible := fun z =>
    (Work.NN.Core.isInvertible_one_add_and_inverse_norm_le (hquarter z)).1
  have hY : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => ContinuousLinearMap.inverse (1 + Work.NN.Core.BopBar A z)) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    have hz : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun w => (1 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)
          + Work.NN.Core.BopBar A w) z :=
      ((contDiff_const (c := (1 : Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n))).add
        hBopBar).contDiffAt
    have h := (ContinuousLinearMap.IsInvertible.contDiffAt_map_inverse (hInv z)).comp z hz
    simpa only [Function.comp_def] using h
  have hσ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Work.NN.Core.Cn n => fun j : Fin n => f z (Pi.single j (1 : ℂ))) := by
    refine contDiff_pi.mpr fun j => ?_
    exact ((contDiff_infty.mpr hf).clm_apply
      (contDiff_const : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun _ : Work.NN.Core.Cn n => (Pi.single j (1 : ℂ) : Work.NN.Core.Cn n))))
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Work.NN.Core.Cn n =>
        ContinuousLinearMap.inverse (1 + Work.NN.Core.BopBar A z)
          (fun j : Fin n => f z (Pi.single j (1 : ℂ)))) :=
    hY.clm_apply hσ
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Work.NN.Core.Cn n =>
        (ContinuousLinearMap.proj k : Work.NN.Core.Cn n →L[ℝ] ℂ)
          (ContinuousLinearMap.inverse (1 + Work.NN.Core.BopBar A z)
            (fun j : Fin n => f z (Pi.single j (1 : ℂ))))) :=
    ((ContinuousLinearMap.proj k : Work.NN.Core.Cn n →L[ℝ] ℂ).contDiff).comp h1
  convert h2 using 1
  ext z
  rfl

end

end Work.NN.Final
