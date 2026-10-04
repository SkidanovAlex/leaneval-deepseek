import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep8.CSqZ
import Submission.Work.Diff.STE.B3.SymCalcStep8.perTransfer_csq_le_of_support
import Submission.Work.Diff.STE.B3.SymCalcStep8.integral_periodization_mul
import Submission.Work.Diff.STE.B3.SymCalcStep8.abs_det_fderiv_comp_eq_inv
import Submission.Work.Diff.STE.B3.SymCalcStep8.periodization_compact_contDiff
import Submission.Work.Diff.STE.B3.SymCalcStep8.localInverseData
import Submission.Work.Diff.STE.B3.SymCalcStep8.contDiff_mul_of_contDiffOn
import Submission.Work.Diff.STE.B3.SymCalcStep8.contDiffOn_inv_abs_det_fderiv_comp
import Submission.Work.Diff.STE.B3.SymCalcStep8.csqZ_neg_le_of_adjoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The local chart transfer is bounded on the negative Sobolev levels `H^{-t}`

For a fixed smooth compactly supported amplitude `c` and a fixed smooth map `θ` that is injective
with nonvanishing Jacobian determinant on the support of `c`, the local transfer

`perTransfer c θ W z = ∑' m, c (z + iVec m) * W (θ (z + iVec m))`

(the periodisation of `c · (W ∘ θ)`) is bounded on the Sobolev level `H^t` for every integer `t`.
The positive range `t ≥ 0` is `perTransfer_csq_le_of_support`; the present file proves the
**negative** range, the target `perTransfer_CSqZ_neg_le` (`t : ℕ`, exponent `-(t : ℤ)`).

## Route (duality, the adjoint produced by the inverse function theorem)

By the duality principle `csqZ_neg_le_of_adjoint` it suffices to produce an adjoint
`T* = perTransfer γ σ` of the transfer with

* the exact pairing identity `L2re (perTransfer c θ W) V = L2re (T* V) W`
  (`L2re_perTransfer_pairing` below, from the two periodisation identities
  `integral_periodization_mul` and the **area formula**
  `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` applied to `θ` on `tsupport c`),
* the bound `CSqZ t (fourierCoeff (T* V)) ≤ C * CSqZ t (fourierCoeff V)`, which is
  `perTransfer_csq_le_of_support` applied to `(γ, σ)`.

Here `σ` is a local inverse of `θ` (`localInverseData`: the injectivity of `θ` on the compact
support of `c` plus the nonvanishing Jacobian yield a local inverse, extended globally by a bump),
`Ω` is an open set containing `θ '' tsupport c` on which `θ ∘ σ = id`, and

`γ z = Φ z * (star (c (σ z)) * (((|(fderiv ℝ θ (σ z)).det| : ℝ))⁻¹ : ℂ))`

is the transported amplitude with the Jacobian `|det Dσ| = (|det Dθ ∘ σ|)⁻¹` of the inverse
(chain rule on `Ω`), cut off by a bump `Φ` which is `1` on `θ '' tsupport c` and whose support
lies in `{z | det (fderiv ℝ θ (σ z)) ≠ 0} ∩ Ω`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.Diff.STE.B3.SymCalcStep8

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A transfer of a smooth compactly supported amplitude is smooth and `1`-periodic.**  This is
the periodisation of the smooth compactly supported function `x ↦ c x * W (θ x)`
(`periodization_compact_contDiff`), read through the definition of `perTransfer`. -/
lemma perTransfer_contDiff_periodic_of
    (c : (ι → ℝ) → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcs : HasCompactSupport c)
    (θ : (ι → ℝ) → (ι → ℝ)) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (W : (ι → ℝ) → ℂ) (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hWp : Work.Diff.STE.Periodic1 W) :
    ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.perTransfer c θ W) ∧
      Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.perTransfer c θ W) := by
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) (fun x : ι → ℝ => c x * W (θ x)) := hc.mul (hW.comp hθ)
  have hcsΦ : HasCompactSupport (fun x : ι → ℝ => c x * W (θ x)) := hcs.mul_right
  have h := Work.Diff.STE.B3.SymCalcStep8.periodization_compact_contDiff
      (fun x : ι → ℝ => c x * W (θ x)) hΦ hcsΦ
  have hdef : Work.Diff.STE.B3.perTransfer c θ W
      = fun z : ι → ℝ => ∑' m : ι → ℤ,
          c (z + Work.Diff.STE.iVec m) * W (θ (z + Work.Diff.STE.iVec m)) := rfl
  rw [hdef]
  exact h

/-- **The pairing identity for the local transfer.**  For a smooth `θ` injective on the (compact)
support of a smooth compactly supported `c`, a smooth `σ` inverting `θ` on `U ⊇ tsupport c` and on
an open neighbourhood `Ω` of `θ '' tsupport c` (so that `|det Dσ| = (|det Dθ ∘ σ|)⁻¹` there by the
chain rule), and a bump `Φ` equal to `1` on `θ '' tsupport c` whose support lies in `Ω`,

  `L2re (perTransfer c θ G) F = L2re (perTransfer γ σ F) G`   for all smooth periodic `F`, `G`,

with the transported amplitude
`γ z = Φ z * (star (c (σ z)) * (((|(fderiv ℝ θ (σ z)).det| : ℝ))⁻¹ : ℂ))`.

Proof: unfold both sides into integrals over `ℝ^ι` with `integral_periodization_mul`, apply the
area formula `integral_image_eq_integral_abs_det_fderiv_smul` to `θ` on `tsupport c`, and use the
pointwise identities `σ (θ x) = x`, `Φ (θ x) = 1` and `|det Dσ (θ x)| · |det Dθ x| = 1`; the last
step takes the real part of the conjugate integral. -/
theorem L2re_perTransfer_pairing
    (c : (ι → ℝ) → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcs : HasCompactSupport c)
    (θ : (ι → ℝ) → (ι → ℝ)) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hinj : Set.InjOn θ (tsupport c))
    (hdet : ∀ z ∈ tsupport c, (fderiv ℝ θ z).det ≠ 0)
    (σ : (ι → ℝ) → (ι → ℝ)) (hσ : ContDiff ℝ (⊤ : ℕ∞) σ)
    (U Ω : Set (ι → ℝ)) (hU : IsOpen U) (hUc : tsupport c ⊆ U) (hστ : ∀ z ∈ U, σ (θ z) = z)
    (hΩK : θ '' tsupport c ⊆ Ω) (hθσ : ∀ y ∈ Ω, θ (σ y) = y)
    (Φ : (ι → ℝ) → ℂ) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (hΦcs : HasCompactSupport Φ)
    (hΦΩ : tsupport Φ ⊆ Ω)
    (hΦV : tsupport Φ ⊆ {z : ι → ℝ | (fderiv ℝ θ (σ z)).det ≠ 0})
    (hΦ1 : ∀ y ∈ θ '' tsupport c, Φ y = 1)
    (F G : (ι → ℝ) → ℂ) (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFp : Work.Diff.STE.Periodic1 F)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGp : Work.Diff.STE.Periodic1 G) :
    Work.Diff.STE.L2re (Work.Diff.STE.B3.perTransfer c θ G) F
      = Work.Diff.STE.L2re
          (Work.Diff.STE.B3.perTransfer
            (fun z => Φ z * (star (c (σ z))
              * (((|(fderiv ℝ θ (σ z)).det| : ℝ))⁻¹ : ℂ))) σ F) G := by
  classical
  set K : Set (ι → ℝ) := tsupport c with hK
  set γ : (ι → ℝ) → ℂ :=
    fun z => Φ z * (star (c (σ z)) * (((|(fderiv ℝ θ (σ z)).det| : ℝ))⁻¹ : ℂ)) with hγ
  -- (0) continuity of the transported amplitude
  have hγcont : Continuous γ := by
    have hdet_cont : Continuous (fun z : ι → ℝ => (fderiv ℝ θ (σ z)).det) :=
      ContinuousLinearMap.continuous_det.comp ((hθ.continuous_fderiv (by simp)).comp hσ.continuous)
    have habs : Continuous (fun z : ι → ℝ => ((|(fderiv ℝ θ (σ z)).det| : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp hdet_cont.abs
    have hstar : Continuous (fun z : ι → ℝ => star (c (σ z))) :=
      (hc.continuous.comp hσ.continuous).star
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ tsupport Φ
    · have hxV : (fderiv ℝ θ (σ x)).det ≠ 0 := hΦV hx
      have hne : ((|(fderiv ℝ θ (σ x)).det| : ℝ) : ℂ) ≠ 0 := by
        rw [Complex.ofReal_ne_zero]
        exact abs_ne_zero.mpr hxV
      have hinv : ContinuousAt
          (fun z : ι → ℝ => (((|(fderiv ℝ θ (σ z)).det| : ℝ) : ℂ))⁻¹) x :=
        (habs.continuousAt).inv₀ hne
      refine (hΦ.continuous.continuousAt).mul ?_
      exact hstar.continuousAt.mul hinv
    · have hopen : IsOpen ((tsupport Φ)ᶜ) := (isClosed_tsupport Φ).isOpen_compl
      have hev : γ =ᶠ[nhds x] 0 := by
        filter_upwards [hopen.mem_nhds hx] with y hy
        have hy0 : Φ y = 0 := Function.notMem_support.mp fun h => hy (subset_closure h)
        simp only [hγ, hy0, zero_mul, Pi.zero_apply]
      exact continuousAt_const.congr hev.symm
  -- (0') compact support of the transported amplitudes
  have hcs1 : HasCompactSupport (fun x : ι → ℝ => γ x * F (σ x)) := by
    refine IsCompact.of_isClosed_subset hΦcs (isClosed_tsupport _)
      (closure_minimal ?_ (isClosed_tsupport Φ))
    intro x hx
    simp only [Function.mem_support] at hx
    have hγx : γ x ≠ 0 := fun h0 => hx (by rw [h0, zero_mul])
    have hΦx : Φ x ≠ 0 := fun h0 => hγx (by simp only [hγ, h0, zero_mul])
    exact subset_closure (Function.mem_support.mpr hΦx)
  have hcs2 : HasCompactSupport (fun x : ι → ℝ => γ x * F (σ x) * star (G x)) := by
    refine IsCompact.of_isClosed_subset hΦcs (isClosed_tsupport _)
      (closure_minimal ?_ (isClosed_tsupport Φ))
    intro x hx
    simp only [Function.mem_support] at hx
    have hγx : γ x ≠ 0 := fun h0 => hx (by simp [h0])
    have hΦx : Φ x ≠ 0 := fun h0 => hγx (by simp only [hγ, h0, zero_mul])
    exact subset_closure (Function.mem_support.mpr hΦx)
  -- (1) the left-hand side is the integral of `c · (G ∘ θ) · star F`
  have hL : Work.Diff.STE.L2re (Work.Diff.STE.B3.perTransfer c θ G) F
      = Complex.re (∫ x, c x * G (θ x) * star (F x)) := by
    have h := Work.Diff.STE.B3.SymCalcStep8.integral_periodization_mul
      (f := fun x : ι → ℝ => c x * G (θ x)) (P := F)
      (hc.continuous.mul (hG.continuous.comp hθ.continuous)) (hcs.mul_right)
      hF.continuous hFp
    rw [Work.Diff.STE.L2re]
    have h2 : (fun z : ι → ℝ => (Work.Diff.STE.B3.perTransfer c θ G) z * star (F z))
        = (fun z : ι → ℝ => (∑' m : ι → ℤ,
            (c (z + Work.Diff.STE.iVec m) * G (θ (z + Work.Diff.STE.iVec m))))
              * star (F z)) := by
      funext z
      simp only [Work.Diff.STE.B3.perTransfer]
    rw [h2]
    exact congrArg Complex.re h
  -- (2) the right-hand side is the integral of `γ · (F ∘ σ) · star G`
  have hR : Work.Diff.STE.L2re (Work.Diff.STE.B3.perTransfer γ σ F) G
      = Complex.re (∫ x, γ x * F (σ x) * star (G x)) := by
    have h := Work.Diff.STE.B3.SymCalcStep8.integral_periodization_mul
      (f := fun x : ι → ℝ => γ x * F (σ x)) (P := G)
      (hγcont.mul (hF.continuous.comp hσ.continuous)) hcs1 hG.continuous hGp
    rw [Work.Diff.STE.L2re]
    have h2 : (fun z : ι → ℝ => (Work.Diff.STE.B3.perTransfer γ σ F) z * star (G z))
        = (fun z : ι → ℝ => (∑' m : ι → ℤ,
            γ (z + Work.Diff.STE.iVec m) * F (σ (z + Work.Diff.STE.iVec m)))
              * star (G z)) := by
      funext z
      simp only [Work.Diff.STE.B3.perTransfer]
    rw [h2]
    exact congrArg Complex.re h
  rw [hL, hR]
  -- the transported integrand
  set g : (ι → ℝ) → ℂ := fun x => γ x * F (σ x) * star (G x) with hg
  -- (3) the change of variables
  have hA : ∫ x, γ x * F (σ x) * star (G x)
      = ∫ x in K, ((|(fderiv ℝ θ x).det| : ℝ) : ℂ) * g (θ x) := by
    have hkey := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
      (μ := volume) (s := K)
      (f' := fun x : ι → ℝ => fderiv ℝ θ x) (f := θ) (g := g)
      hcs.isCompact.measurableSet
      (fun x _ => ((hθ.differentiable (by simp) x).hasFDerivAt).hasFDerivWithinAt)
      hinj
    have hsuppmem : ∀ x : ι → ℝ, x ∉ θ '' K → g x = 0 := by
      intro x hx
      have hγx : γ x = 0 := by
        by_cases hΦx : Φ x = 0
        · simp only [hγ, hΦx, zero_mul]
        · have hxΩ : x ∈ Ω := hΦΩ (subset_closure (Function.mem_support.mpr hΦx))
          have hxc : c (σ x) = 0 := by
            by_contra hcne
            exact hx ⟨σ x, subset_closure (Function.mem_support.mpr hcne),
              hθσ x hxΩ⟩
          simp only [hγ, hxc, star_zero, zero_mul, mul_zero]
      simp only [hg, hγx, zero_mul]
    have h1 : ∫ x, g x = ∫ x in θ '' K, g x :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hsuppmem).symm
    have h2 : ∫ x in θ '' K, g x
        = ∫ x in K, ((|(fderiv ℝ θ x).det| : ℝ) : ℂ) * g (θ x) := by
      rw [hkey]
      refine setIntegral_congr_fun hcs.isCompact.measurableSet (fun x _ => ?_)
      rw [Complex.real_smul]
    rw [h1, h2]
  rw [hA]
  -- (4) the pointwise identity on `K`
  have hpt : ∀ x ∈ K, ((|(fderiv ℝ θ x).det| : ℝ) : ℂ) * g (θ x)
      = star (c x) * F x * star (G (θ x)) := by
    intro x hx
    have hxU : x ∈ U := hUc hx
    have h1 : σ (θ x) = x := hστ x hxU
    have h2 : Φ (θ x) = 1 := hΦ1 (θ x) ⟨x, hx, rfl⟩
    have hr : ((|(fderiv ℝ θ x).det| : ℝ)) ≠ 0 := abs_ne_zero.mpr (hdet x hx)
    have hrC : ((|(fderiv ℝ θ x).det| : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact hr
    simp only [hg, hγ, h1, h2, one_mul]
    calc ((|(fderiv ℝ θ x).det| : ℝ) : ℂ)
          * (star (c x) * (((|(fderiv ℝ θ x).det| : ℝ) : ℂ))⁻¹ * F x * star (G (θ x)))
        = (((|(fderiv ℝ θ x).det| : ℝ) : ℂ) * (((|(fderiv ℝ θ x).det| : ℝ) : ℂ))⁻¹)
            * (star (c x) * F x * star (G (θ x))) := by ring
      _ = star (c x) * F x * star (G (θ x)) := by
          rw [mul_inv_cancel₀ hrC, one_mul]
  have h3 : ∫ x in K, ((|(fderiv ℝ θ x).det| : ℝ) : ℂ) * g (θ x)
      = ∫ x in K, star (c x) * F x * star (G (θ x)) :=
    setIntegral_congr_fun hcs.isCompact.measurableSet hpt
  rw [h3]
  -- (5) conjugation, and restricting the other integral to `K`
  have hconj : Complex.re (∫ x in K, star (c x) * F x * star (G (θ x)))
      = Complex.re (∫ x in K, c x * G (θ x) * star (F x)) := by
    have h4 : (fun x : ι → ℝ => star (c x) * F x * star (G (θ x)))
        = fun x : ι → ℝ => star (c x * G (θ x) * star (F x)) := by
      funext x
      simp only [star_mul, star_star]
      ring
    rw [h4]
    have h6 : (∫ x in K, star (c x * G (θ x) * star (F x)))
        = star (∫ x in K, c x * G (θ x) * star (F x)) := by
      rw [Complex.star_def, starRingEnd_apply]
      exact integral_conj
    rw [h6]
    simp only [Complex.star_def, Complex.conj_re]
  rw [hconj]
  have h5 : ∫ x in K, c x * G (θ x) * star (F x)
      = ∫ x, c x * G (θ x) * star (F x) := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => ?_)
    by_contra hne
    exact hx (subset_closure (Function.mem_support.mpr
      (fun hc0 => hne (by simp [hc0]))))
  rw [← h5]

/-- **The local chart transfer is bounded on the negative Sobolev levels `H^{-t}`.**  The
`CSqZ (-t)` companion of `perTransfer_csq_le_of_support` (same hypotheses, `t : ℕ`, exponent
`-(t : ℤ)` on both sides).

Route (duality; the reviewers both flagged that `CSqZ_mono` is *not* enough, and that the naive
adjoint formula of `local_transfer_adjoint` is false as stated): `perTransfer c θ` is the adjoint
of the transfer with amplitude `c (σ y) · |det Dθ (σ y)|⁻¹` and map `σ`, for a local inverse `σ`
of `θ` chosen so that `σ y ∉ tsupport c` off `θ '' tsupport c` (`local_transfer_adjoint_of_preimage`
/ `_of_support` supply the corrected forms).  The adjoint amplitude is smooth, compactly supported
in `θ '' tsupport c`, `σ` has nonvanishing `fderiv` determinant there, so
`perTransfer_csq_le_of_support` applies to the adjoint at exponent `t`; duality
(`‖P‖_{H^{-t}} = ‖P^*‖_{H^t}` for the coefficient families, which is the identity
`CSqZ (-t) (fourierCoeff (P W)) = sup`-free version obtained by inserting `wt^t · wt^{-t} = 1`)
finishes. -/
theorem perTransfer_CSqZ_neg_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : (ι → ℝ) → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcs : HasCompactSupport c)
    (θ : (ι → ℝ) → (ι → ℝ)) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (hinj : Set.InjOn θ (tsupport c))
    (hdet : ∀ z ∈ tsupport c, (fderiv ℝ θ z).det ≠ 0) (t : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) W →
      Work.Diff.STE.Periodic1 W →
      Work.Diff.STE.B3.SymCalcStep8.CSqZ (-(t : ℤ))
          (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.perTransfer c θ W))
        ≤ C * Work.Diff.STE.B3.SymCalcStep8.CSqZ (-(t : ℤ))
            (Work.Diff.STE.fourierCoeff W) := by
  classical
  -- ## The local inverse data of `θ` on the support of `c`
  obtain ⟨σ, hσsm, U, hUopen, hUc, hστ, Ω, hΩopen, hΩK, hθσ⟩ :=
    Work.Diff.STE.B3.SymCalcStep8.localInverseData θ hθ (tsupport c) hcs.isCompact hinj hdet
  -- ## The open set on which the Jacobian of `θ ∘ σ` does not vanish
  set V : Set (ι → ℝ) := {z : ι → ℝ | (fderiv ℝ θ (σ z)).det ≠ 0} with hV
  have hVopen : IsOpen V := by
    have hcont : Continuous (fun z : ι → ℝ => (fderiv ℝ θ (σ z)).det) :=
      ContinuousLinearMap.continuous_det.comp
        ((hθ.continuous_fderiv (by simp)).comp hσsm.continuous)
    exact isOpen_ne.preimage hcont
  have hKV : θ '' tsupport c ⊆ V := by
    rintro z ⟨y, hy, rfl⟩
    show (fderiv ℝ θ (σ (θ y))).det ≠ 0
    rw [hστ y (hUc hy)]
    exact hdet y hy
  have hKc : IsCompact (θ '' tsupport c) := hcs.isCompact.image hθ.continuous
  obtain ⟨δ, hδ, hδsub⟩ :=
    hKc.exists_cthickening_subset_open (hΩopen.inter hVopen)
      (fun z hz => ⟨hΩK hz, hKV hz⟩)
  have hδ2 : (0 : ℝ) < δ / 2 := by linarith
  -- ## A smooth bump which is `1` on `θ '' tsupport c` and supported inside `Ω ∩ V`
  set s : Set (ι → ℝ) := Metric.thickening (δ / 2) (θ '' tsupport c) with hs
  have hsopen : IsOpen s := Metric.isOpen_thickening
  obtain ⟨Φ₀, hΦ₀sm, -, hΦ₀supp, hΦ₀one⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) (s := s) (t := θ '' tsupport c)
      hsopen hKc.isClosed (fun z hz => by
        have h1 : z ∈ Metric.thickening (δ / 2) (θ '' tsupport c) :=
          Metric.self_subset_thickening hδ2 _ hz
        rwa [hs])
  set Φ : (ι → ℝ) → ℂ := fun z => ((Φ₀ z : ℝ) : ℂ) with hΦdef
  have hΦsm : ContDiff ℝ (⊤ : ℕ∞) Φ :=
    (ContinuousLinearMap.contDiff (Complex.ofRealCLM : ℝ →L[ℝ] ℂ)).comp hΦ₀sm
  have hsuppΦ : Function.support Φ = s := by
    rw [← hΦ₀supp]
    ext z
    simp only [Function.mem_support, hΦdef]
    exact not_congr Complex.ofReal_eq_zero
  have htsΦ : tsupport Φ = closure s := by
    simp only [tsupport, hsuppΦ]
  have hΦtsub : tsupport Φ ⊆ Ω ∩ V := by
    rw [htsΦ]
    exact (Metric.closure_thickening_subset_cthickening (δ / 2) (θ '' tsupport c)).trans
      ((Metric.cthickening_mono (by linarith) (θ '' tsupport c)).trans hδsub)
  have hΦΩ : tsupport Φ ⊆ Ω := hΦtsub.trans (fun _ hz => hz.1)
  have hΦV : tsupport Φ ⊆ V := hΦtsub.trans (fun _ hz => hz.2)
  have hΦcs : HasCompactSupport Φ := by
    refine IsCompact.of_isClosed_subset (hKc.cthickening (r := δ / 2)) (isClosed_tsupport Φ) ?_
    rw [htsΦ]
    exact Metric.closure_thickening_subset_cthickening (δ / 2) (θ '' tsupport c)
  have hΦ1 : ∀ y ∈ θ '' tsupport c, Φ y = 1 := by
    intro y hy
    have h1 : Φ₀ y = 1 := (hΦ₀one y).mp hy
    simp only [hΦdef, h1, Complex.ofReal_one]
  -- ## The transported amplitude
  set γ : (ι → ℝ) → ℂ :=
    fun z => Φ z * (star (c (σ z)) * (((|(fderiv ℝ θ (σ z)).det| : ℝ))⁻¹ : ℂ)) with hγdef
  have hstar_cd : ContDiff ℝ (⊤ : ℕ∞) (fun z : ι → ℝ => star (c (σ z))) :=
    (ContinuousLinearMap.contDiff (Complex.conjCLE : ℂ →L[ℝ] ℂ)).comp (hc.comp hσsm)
  have hγsm : ContDiff ℝ (⊤ : ℕ∞) γ := by
    have hf : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : ι → ℝ => star (c (σ z)) * (((|(fderiv ℝ θ (σ z)).det| : ℝ))⁻¹ : ℂ)) V :=
      hstar_cd.contDiffOn.mul
        (Work.Diff.STE.B3.SymCalcStep8.contDiffOn_inv_abs_det_fderiv_comp θ σ hθ hσsm)
    exact Work.Diff.STE.B3.SymCalcStep8.contDiff_mul_of_contDiffOn V hVopen _ hf Φ hΦsm hΦV
  have hγcs : HasCompactSupport γ := by
    refine IsCompact.of_isClosed_subset hΦcs (isClosed_tsupport γ)
      (closure_minimal ?_ (isClosed_tsupport Φ))
    intro z hz
    simp only [Function.mem_support] at hz
    have hΦz : Φ z ≠ 0 := fun h0 => hz (by simp [hγdef, h0])
    exact subset_closure (Function.mem_support.mpr hΦz)
  have hγΩ : tsupport γ ⊆ Ω := by
    refine (closure_mono ?_).trans hΦΩ
    intro z hz
    simp only [Function.mem_support] at hz ⊢
    exact fun h0 => hz (by simp [hγdef, h0])
  -- ## The hypotheses of the positive bound for the adjoint
  have hinjσ : Set.InjOn σ (tsupport γ) := by
    intro y hy y' hy' hyy'
    rw [← hθσ y (hγΩ hy), hyy', hθσ y' (hγΩ hy')]
  have hdetσ : ∀ z ∈ tsupport γ, (fderiv ℝ σ z).det ≠ 0 := by
    intro z hz
    have hzΩ : z ∈ Ω := hγΩ hz
    have hone : (fderiv ℝ θ (σ z)).comp (fderiv ℝ σ z) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
      have hdθ : DifferentiableAt ℝ θ (σ z) :=
        (hθ.differentiable (by simp)).differentiableAt (x := σ z)
      have hdσ : DifferentiableAt ℝ σ z :=
        (hσsm.differentiable (by simp)).differentiableAt (x := z)
      have hcomp : fderiv ℝ (θ ∘ σ) z = (fderiv ℝ θ (σ z)).comp (fderiv ℝ σ z) :=
        fderiv_comp z hdθ hdσ
      have hev : (θ ∘ σ) =ᶠ[nhds z] id := by
        filter_upwards [hΩopen.mem_nhds hzΩ] with y hy
        exact hθσ y hy
      rw [← hcomp, hev.fderiv_eq, fderiv_id]
    have hdet1 : (fderiv ℝ θ (σ z)).det * (fderiv ℝ σ z).det = 1 := by
      have h2 := congrArg ContinuousLinearMap.det hone
      simp only [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp,
        ContinuousLinearMap.coe_id, LinearMap.det_id] at h2
      exact h2
    intro h0
    rw [h0, mul_zero] at hdet1
    exact zero_ne_one hdet1
  -- ## The bound on the positive level for the adjoint transfer
  obtain ⟨C₁, hC₁, hC₁b⟩ :=
    Work.Diff.STE.B3.SymCalcStep8.perTransfer_csq_le_of_support γ hγsm hγcs σ hσsm hinjσ hdetσ t
  have hbd : ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ V' : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) V' →
      Work.Diff.STE.Periodic1 V' →
      Work.Diff.STE.B3.SymCalcStep8.CSqZ (t : ℤ)
          (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.perTransfer γ σ V'))
        ≤ C₁ * Work.Diff.STE.B3.SymCalcStep8.CSqZ (t : ℤ)
            (Work.Diff.STE.fourierCoeff V') := by
    refine ⟨C₁, hC₁, fun V' hV' hV'p => ?_⟩
    rw [Work.Diff.STE.B3.SymCalcStep8.CSqZ_natCast,
      Work.Diff.STE.B3.SymCalcStep8.CSqZ_natCast]
    exact hC₁b V' hV' hV'p
  -- ## Duality
  obtain ⟨C, hC, hCb⟩ :=
    Work.Diff.STE.B3.SymCalcStep8.csqZ_neg_le_of_adjoint t
      (fun W => Work.Diff.STE.B3.perTransfer c θ W)
      (fun V' => Work.Diff.STE.B3.perTransfer γ σ V')
      (fun W hW hWp => perTransfer_contDiff_periodic_of c hc hcs θ hθ W hW hWp)
      (fun V' hV' hV'p => perTransfer_contDiff_periodic_of γ hγsm hγcs σ hσsm V' hV' hV'p)
      (fun W V' hW hWp hV' hV'p =>
        L2re_perTransfer_pairing c hc hcs θ hθ hinj hdet σ hσsm U Ω hUopen hUc hστ hΩK hθσ
          Φ hΦsm hΦcs hΦΩ hΦV hΦ1 V' W hV' hV'p hW hWp)
      hbd
  exact ⟨C, hC, hCb⟩

end Work.Diff.STE.B3.SymCalcStep8
