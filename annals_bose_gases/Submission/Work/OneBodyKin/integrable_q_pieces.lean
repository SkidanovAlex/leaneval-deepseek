import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.integrable_kinFT_sq
import Submission.Work.OneBodyKin.SymAPI
import Submission.Work.OneBodyKin.bsFamilyFormUnproj_eq_symbol
import Submission.Work.OneBodyKin.integrable_bsKern
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.OneBodyKin.integrable_q_pieces`

The three `q`-integrals of the symbol expansion of the projected moving-box family form

  `symA ℓ F q * ‖kinFT ψ q‖²`,  `boxHat ℓ q * symD ℓ F q * ‖kinFT ψ q‖²`,
  `symC ℓ F q * ‖kinFT ψ q‖²`

are `L¹` for a radial-`L¹` symbol `F(‖·‖)` and a smooth compactly supported `ψ`.

The argument is the crudest possible one: each of the three symbols is **bounded** (the profile
`profHat` is bounded by the bump mass `∫|χ|` by `abs_profHat_le`, `boxHat ℓ` by the box volume
`ℓ³` by `abs_boxHat_le`, and the symbol `F(‖·‖)` is `L¹` so only the `(2π)`-factors and the
`ℓ`-powers of `symA`/`symD`/`symC` enter), and `‖kinFT ψ‖²` is `L¹`
(`Work.BSKinetic.integrable_kinFT_sq`, the `L²` half of Plancherel).  The only non-elementary
point is **measurability**: `F` itself is only assumed `L¹` in the radial variable
(`∫_p F ‖p‖ < ∞`), so it is not known to be measurable.  We therefore replace `F` by a strongly
measurable representative `H` of `p ↦ F ‖p‖` (`hFi.aestronglyMeasurable`); since both `symA` (in
its *shifted* form `symA_eq_shiftedIntegral`, where the `F`-factor carries the unshifted variable
`p`) and `symD` evaluate `F` at the unshifted argument `p`, the two define the same function, and
the rewritten integrals are strongly measurable by the parametric-integral lemma
`StronglyMeasurable.integral_prod_right`.  `boxHat` is strongly measurable directly.
-/

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real

namespace Work.OneBodyKin

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary estimates for the bump profile -/

private lemma chiMass_nonneg : 0 ≤ ∫ z : ℝ³, |chi z| :=
  integral_nonneg (f := fun z : ℝ³ => |chi z|) fun z => abs_nonneg _

private lemma abs_integral_nonneg (f : ℝ³ → ℝ) : 0 ≤ ∫ p : ℝ³, |f p| :=
  integral_nonneg (f := fun p : ℝ³ => |f p|) fun p => abs_nonneg _

private lemma profHat_abs_mul_le (p q : ℝ³) :
    |profHat p| * |profHat q| ≤ (∫ z : ℝ³, |chi z|) * (∫ z : ℝ³, |chi z|) :=
  mul_le_mul (abs_profHat_le p) (abs_profHat_le q) (abs_nonneg _) chiMass_nonneg

private lemma profHat_abs_sq_le (p : ℝ³) :
    |profHat p| ^ 2 ≤ (∫ z : ℝ³, |chi z|) * (∫ z : ℝ³, |chi z|) := by
  rw [pow_two]
  exact profHat_abs_mul_le p p

/-! ## A domination bound for the symbol integrals -/

/-- If `g` is uniformly bounded by `M` and `H ∈ L¹`, then
`|∫_p H p · g p| ≤ (∫_p |H p|) · M`. -/
private lemma abs_integral_mul_le {H g : ℝ³ → ℝ} (hHi : Integrable H)
    (hHsm : StronglyMeasurable H) (hgsm : StronglyMeasurable g) {M : ℝ}
    (hM : ∀ p : ℝ³, |g p| ≤ M) :
    |∫ p : ℝ³, H p * g p| ≤ (∫ p : ℝ³, |H p|) * M := by
  have hHabs : Integrable (fun p : ℝ³ => |H p|) := by
    simpa only [Real.norm_eq_abs] using hHi.norm
  have hdom : Integrable (fun p : ℝ³ => |H p| * M) := hHabs.mul_const M
  have hb : ∀ p : ℝ³, ‖H p * g p‖ ≤ |H p| * M := by
    intro p
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hM p) (abs_nonneg _)
  have hint : Integrable (fun p : ℝ³ => H p * g p) :=
    Integrable.mono' hdom (hHsm.mul hgsm).aestronglyMeasurable (Filter.Eventually.of_forall hb)
  calc |∫ p : ℝ³, H p * g p|
      = ‖∫ p : ℝ³, H p * g p‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ p : ℝ³, ‖H p * g p‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ p : ℝ³, |H p| * M := integral_mono hint.norm hdom hb
    _ = (∫ p : ℝ³, |H p|) * M := integral_mul_const M _

/-! ## `symA` -/

/-- With a strongly measurable representative `H` of `p ↦ F ‖p‖`, the shifted form of `symA`
(`symA_eq_shiftedIntegral`) has the *unshifted* `F`-argument, so `F` may be replaced by `H`. -/
private lemma symA_eq_ae {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ} {H : ℝ³ → ℝ}
    (hHae : (fun p : ℝ³ => F ‖p‖) =ᵐ[volume] H) (q : ℝ³) :
    symA ℓ F q = ((2 * Real.pi) ^ 3)⁻¹ * (ℓ ^ 3 * ∫ p : ℝ³, H p * (profHat (ℓ • (q - p))) ^ 2) := by
  rw [symA_eq_shiftedIntegral hℓ F q,
    integral_congr_ae (by filter_upwards [hHae] with p hp; rw [hp])]

private lemma aestronglyMeasurable_symA {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : Integrable (fun p : ℝ³ => F ‖p‖)) : AEStronglyMeasurable (symA ℓ F) := by
  obtain ⟨H, hHsm, hHae⟩ := hFi.aestronglyMeasurable
  have hI : StronglyMeasurable
      (fun q : ℝ³ => ∫ p : ℝ³, H p * (profHat (ℓ • (q - p))) ^ 2) := by
    refine StronglyMeasurable.integral_prod_right (ν := (volume : Measure ℝ³)) ?_
    have h1 : StronglyMeasurable (fun w : ℝ³ × ℝ³ => H w.2) :=
      hHsm.comp_measurable measurable_snd
    have h2 : StronglyMeasurable (fun w : ℝ³ × ℝ³ => profHat (ℓ • (w.1 - w.2))) :=
      stronglyMeasurable_profHat.comp_measurable
        ((measurable_fst.sub measurable_snd).const_smul ℓ)
    show StronglyMeasurable (fun w : ℝ³ × ℝ³ => H w.2 * (profHat (ℓ • (w.1 - w.2))) ^ 2)
    exact h1.mul (h2.pow 2)
  have hfun : symA ℓ F
      = fun q : ℝ³ => ((2 * Real.pi) ^ 3)⁻¹ *
          (ℓ ^ 3 * ∫ p : ℝ³, H p * (profHat (ℓ • (q - p))) ^ 2) := by
    funext q
    rw [symA_eq_ae hℓ hHae q]
  rw [hfun]
  exact ((hI.const_mul (ℓ ^ 3)).const_mul (((2 * Real.pi) ^ 3)⁻¹)).aestronglyMeasurable

private lemma abs_symA_le {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : Integrable (fun p : ℝ³ => F ‖p‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ³, |symA ℓ F q| ≤ C := by
  obtain ⟨H, hHsm, hHae⟩ := hFi.aestronglyMeasurable
  have hHi : Integrable H := hFi.congr hHae
  have hc : 0 ≤ ((2 * Real.pi) ^ 3)⁻¹ := inv_nonneg.mpr (by positivity)
  have hl3 : 0 ≤ ℓ ^ 3 := pow_nonneg hℓ.le 3
  have hHabs0 : 0 ≤ ∫ p : ℝ³, |H p| := abs_integral_nonneg H
  have hCχ0 : 0 ≤ ∫ z : ℝ³, |chi z| := chiMass_nonneg
  refine ⟨((2 * Real.pi) ^ 3)⁻¹ * (ℓ ^ 3 * ((∫ p : ℝ³, |H p|) * ((∫ z : ℝ³, |chi z|) * (∫ z : ℝ³, |chi z|)))),
    mul_nonneg hc (mul_nonneg hl3 (mul_nonneg hHabs0 (mul_nonneg hCχ0 hCχ0))), fun q => ?_⟩
  have hg_sm : StronglyMeasurable (fun p : ℝ³ => (profHat (ℓ • (q - p))) ^ 2) :=
    (stronglyMeasurable_profHat.comp_measurable
      ((measurable_const.sub measurable_id).const_smul ℓ)).pow 2
  have hM : ∀ p : ℝ³, |(profHat (ℓ • (q - p))) ^ 2| ≤
      (∫ z : ℝ³, |chi z|) * (∫ z : ℝ³, |chi z|) := by
    intro p
    rw [abs_pow]
    exact profHat_abs_sq_le (ℓ • (q - p))
  have hbound := abs_integral_mul_le hHi hHsm hg_sm hM
  calc |symA ℓ F q|
      = |((2 * Real.pi) ^ 3)⁻¹ * (ℓ ^ 3 * ∫ p : ℝ³, H p * (profHat (ℓ • (q - p))) ^ 2)| := by
        rw [symA_eq_ae hℓ hHae q]
    _ = ((2 * Real.pi) ^ 3)⁻¹ *
          (ℓ ^ 3 * |∫ p : ℝ³, H p * (profHat (ℓ • (q - p))) ^ 2|) := by
        simp only [abs_mul, abs_of_nonneg hc, abs_of_nonneg hl3]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * (ℓ ^ 3 * ((∫ p : ℝ³, |H p|) * ((∫ z : ℝ³, |chi z|) * (∫ z : ℝ³, |chi z|)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbound hl3) hc

/-! ## `symD` -/

private lemma symD_eq_ae {ℓ : ℝ} {F : ℝ → ℝ} {H : ℝ³ → ℝ}
    (hHae : (fun p : ℝ³ => F ‖p‖) =ᵐ[volume] H) (q : ℝ³) :
    symD ℓ F q = ∫ p : ℝ³, H p * profHat (ℓ • p) * profHat (ℓ • (q - p)) := by
  unfold symD
  exact integral_congr_ae (by filter_upwards [hHae] with p hp; rw [hp])

private lemma aestronglyMeasurable_symD {ℓ : ℝ} {F : ℝ → ℝ}
    (hFi : Integrable (fun p : ℝ³ => F ‖p‖)) : AEStronglyMeasurable (symD ℓ F) := by
  obtain ⟨H, hHsm, hHae⟩ := hFi.aestronglyMeasurable
  have hI : StronglyMeasurable
      (fun q : ℝ³ => ∫ p : ℝ³, H p * profHat (ℓ • p) * profHat (ℓ • (q - p))) := by
    refine StronglyMeasurable.integral_prod_right (ν := (volume : Measure ℝ³)) ?_
    have h1 : StronglyMeasurable (fun w : ℝ³ × ℝ³ => H w.2) :=
      hHsm.comp_measurable measurable_snd
    have h2 : StronglyMeasurable (fun w : ℝ³ × ℝ³ => profHat (ℓ • w.2)) :=
      stronglyMeasurable_profHat.comp_measurable (measurable_snd.const_smul ℓ)
    have h3 : StronglyMeasurable (fun w : ℝ³ × ℝ³ => profHat (ℓ • (w.1 - w.2))) :=
      stronglyMeasurable_profHat.comp_measurable
        ((measurable_fst.sub measurable_snd).const_smul ℓ)
    show StronglyMeasurable
      (fun w : ℝ³ × ℝ³ => H w.2 * profHat (ℓ • w.2) * profHat (ℓ • (w.1 - w.2)))
    exact (h1.mul h2).mul h3
  have hfun : symD ℓ F
      = fun q : ℝ³ => ∫ p : ℝ³, H p * profHat (ℓ • p) * profHat (ℓ • (q - p)) := by
    funext q
    rw [symD_eq_ae (ℓ := ℓ) hHae q]
  rw [hfun]
  exact hI.aestronglyMeasurable

private lemma abs_symD_le {ℓ : ℝ} {F : ℝ → ℝ}
    (hFi : Integrable (fun p : ℝ³ => F ‖p‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ³, |symD ℓ F q| ≤ C := by
  obtain ⟨H, hHsm, hHae⟩ := hFi.aestronglyMeasurable
  have hHi : Integrable H := hFi.congr hHae
  have hHabs0 : 0 ≤ ∫ p : ℝ³, |H p| := abs_integral_nonneg H
  have hCχ0 : 0 ≤ ∫ z : ℝ³, |chi z| := chiMass_nonneg
  refine ⟨(∫ p : ℝ³, |H p|) * ((∫ z : ℝ³, |chi z|) * (∫ z : ℝ³, |chi z|)),
    mul_nonneg hHabs0 (mul_nonneg hCχ0 hCχ0), fun q => ?_⟩
  have hg_sm : StronglyMeasurable
      (fun p : ℝ³ => profHat (ℓ • p) * profHat (ℓ • (q - p))) :=
    (stronglyMeasurable_profHat.comp_measurable (measurable_id.const_smul ℓ)).mul
      (stronglyMeasurable_profHat.comp_measurable
        ((measurable_const.sub measurable_id).const_smul ℓ))
  have hM : ∀ p : ℝ³, |profHat (ℓ • p) * profHat (ℓ • (q - p))| ≤
      (∫ z : ℝ³, |chi z|) * (∫ z : ℝ³, |chi z|) := by
    intro p
    rw [abs_mul]
    exact profHat_abs_mul_le (ℓ • p) (ℓ • (q - p))
  have hassoc : (fun p : ℝ³ => H p * profHat (ℓ • p) * profHat (ℓ • (q - p)))
      = fun p : ℝ³ => H p * (profHat (ℓ • p) * profHat (ℓ • (q - p))) := by
    funext p
    ring
  rw [symD_eq_ae (ℓ := ℓ) hHae q, hassoc]
  exact abs_integral_mul_le hHi hHsm hg_sm hM

/-! ## `boxHat` and `symC` -/

private lemma stronglyMeasurable_boxHat (ℓ : ℝ) (hℓ : 0 ≤ ℓ) : StronglyMeasurable (boxHat ℓ) := by
  have h : StronglyMeasurable
      (fun q : ℝ³ => ∫ z, Real.cos (inner ℝ q z) ∂(volume.restrict (acube ℓ))) := by
    refine StronglyMeasurable.integral_prod_right (ν := volume.restrict (acube ℓ)) ?_
    show StronglyMeasurable (fun w : ℝ³ × ℝ³ => Real.cos (inner ℝ w.1 w.2))
    exact (Real.continuous_cos.comp (continuous_fst.inner continuous_snd)).stronglyMeasurable
  have hfun : (fun q : ℝ³ => ∫ z, Real.cos (inner ℝ q z) ∂(volume.restrict (acube ℓ)))
      = boxHat ℓ := by
    funext q
    simp [boxHat]
  rw [hfun] at h
  exact h

private lemma aestronglyMeasurable_symC {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {F : ℝ → ℝ} :
    AEStronglyMeasurable (symC ℓ F) := by
  have hfun : symC ℓ F
      = fun q : ℝ³ => (symA ℓ F 0 * (ℓ ^ 6)⁻¹) * (boxHat ℓ q) ^ 2 := by
    funext q
    rw [symC]
  rw [hfun]
  exact (((stronglyMeasurable_boxHat ℓ hℓ).pow 2).const_mul _).aestronglyMeasurable

private lemma abs_symC_le {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : Integrable (fun p : ℝ³ => F ‖p‖)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : ℝ³, |symC ℓ F q| ≤ C := by
  obtain ⟨CA, hCA0, hCA⟩ := abs_symA_le hℓ hFi
  refine ⟨CA, hCA0, fun q => ?_⟩
  have hinv : 0 ≤ (ℓ ^ 6)⁻¹ := by positivity
  have hbH : |boxHat ℓ q| ≤ ℓ ^ 3 := abs_boxHat_le hℓ.le q
  have hboxsq : |boxHat ℓ q| ^ 2 ≤ ℓ ^ 6 := by
    calc |boxHat ℓ q| ^ 2 ≤ (ℓ ^ 3) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hbH 2
      _ = ℓ ^ 6 := by ring
  have hstep : |symA ℓ F 0| * (ℓ ^ 6)⁻¹ ≤ CA * (ℓ ^ 6)⁻¹ :=
    mul_le_mul_of_nonneg_right (hCA 0) hinv
  calc |symC ℓ F q|
      = |symA ℓ F 0| * (ℓ ^ 6)⁻¹ * |boxHat ℓ q| ^ 2 := by
        rw [symC]
        simp only [abs_mul, abs_of_nonneg hinv, abs_pow]
    _ ≤ CA * (ℓ ^ 6)⁻¹ * ℓ ^ 6 :=
        mul_le_mul hstep hboxsq (by positivity) (mul_nonneg hCA0 hinv)
    _ = CA := by
        rw [mul_assoc, inv_mul_cancel₀ (by positivity : (ℓ : ℝ) ^ 6 ≠ 0), mul_one]

/-- **Integrability of the three `q`-pieces of the symbol expansion.** -/
theorem integrable_q_pieces {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    (hFnn : ∀ r : ℝ, 0 ≤ F r) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
        Work.OneBodyKin.symA ℓ F q *
          ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2) ∧
      MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
        Work.OneBodyKin.boxHat ℓ q * Work.OneBodyKin.symD ℓ F q *
          ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2) ∧
      MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) =>
        Work.OneBodyKin.symC ℓ F q *
          ‖Submission.BoseGases.kinFT (fun z : EuclideanSpace ℝ (Fin 3) => (ψ z : ℂ)) q‖ ^ 2) := by
  have hK : Integrable (fun q : ℝ³ => ‖kinFT (fun z : ℝ³ => (ψ z : ℂ)) q‖ ^ 2) :=
    Work.BSKinetic.integrable_kinFT_sq ψ hψ hcs
  obtain ⟨CA, hCA0, hCA⟩ := abs_symA_le (ℓ := ℓ) hℓ hFi
  obtain ⟨CD, hCD0, hCD⟩ := abs_symD_le (ℓ := ℓ) hFi
  obtain ⟨CC, hCC0, hCC⟩ := abs_symC_le hℓ hFi
  have hAb : AEStronglyMeasurable (symA ℓ F) := aestronglyMeasurable_symA hℓ hFi
  have hDb : AEStronglyMeasurable (symD ℓ F) := aestronglyMeasurable_symD (ℓ := ℓ) hFi
  have hbox : StronglyMeasurable (boxHat ℓ) := stronglyMeasurable_boxHat ℓ hℓ.le
  have hBD : ∀ q : ℝ³, |boxHat ℓ q * symD ℓ F q| ≤ ℓ ^ 3 * CD := fun q =>
    calc |boxHat ℓ q * symD ℓ F q| = |boxHat ℓ q| * |symD ℓ F q| := abs_mul _ _
      _ ≤ ℓ ^ 3 * CD := mul_le_mul (abs_boxHat_le hℓ.le q) (hCD q) (abs_nonneg _)
          (pow_nonneg hℓ.le 3)
  refine ⟨?_, ?_, ?_⟩
  · exact Integrable.bdd_mul hK hAb
      (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hCA q)
  · exact Integrable.bdd_mul hK (hbox.aestronglyMeasurable.mul hDb)
      (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hBD q)
  · exact Integrable.bdd_mul hK (aestronglyMeasurable_symC hℓ.le (F := F))
      (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hCC q)

end Work.OneBodyKin
