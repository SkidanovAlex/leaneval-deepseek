import Mathlib
import Submission.Work.Drive.Neutral.stripTauData
import Submission.Work.Drive.Neutral.stripTauChart
import Submission.Work.Drive.contMDiffAt_cappingSpace_configPiece

/-!
# The strip chart is `C^∞` across the gluing seam

`Submission/Work/Drive/TAU_CHART_STATUS.md` §6 records that no chart of the configuration Möbius band
`M` *alone* can be smooth at the gluing torus with the side conditions of `ConfigPiece`: along the
strip the squared disk radius is `1 - ‖d‖² = ‖chord‖²/r² ≈ 4τ‖γ'‖²/‖γ‖²`, so `‖d‖ - 1` changes sign
across the seam and any smooth extension of the data to `τ < 0` has `‖d‖ > 1` just below the seam.

This file shows that this is *not* an obstruction to the smooth presentation of the capped plane: the
strip chart extends to a `C^∞` map of the capping space across the seam, and the extension *is* the
cap.  The construction:

* the symmetric data `q ↦ symmData γ (q 0, √(q 1))` is even in the opening parameter, so by the
  Whitney/Seeley `√`-factorisation (`Work.Drive.contDiffOn_even_comp_sqrt`) followed by the global
  extension `Work.Drive.exists_contDiff_extension_of_halfspace` it has a `C^∞` germ `G` at the seam
  point which reproduces it on the half-plane `τ ≥ 0`;
* the *configuration* coordinates `(r, d, η)` of that germ are read in the **projective** model of the
  capping space, `CappingSpace ≃ₜ (0,∞) × ℝP³` (`Work.Drive.cappingSpaceHomeoProj`), where the disk
  coordinate `d` is allowed to leave the unit disk: the projective vector `confProjVecOf u d` is
  defined and non-zero as long as `‖u‖ = 1` and `‖d‖² ≠ 2`, so no side condition on `d` is needed;
* pushing back along the homeomorphism gives a `C^∞` map of the capping space which on `τ ≥ 0` is the
  class of the configuration point (the strip), and on `τ < 0` — where it cannot be a configuration
  point — is the cap side of the plane, glued to the strip with the correct jets automatically.

The main result is `Work.Drive.exists_contMDiffAt_stripSeam`.
-/

namespace Work.Drive.Neutral

open Manifold
open scoped Manifold ContDiff Topology
open Classical

noncomputable section

variable {γ : Circle → ℝ × ℝ}

/-! ## 1. The symmetric data is smooth along the diagonal and even -/

/-- The symmetric data `p ↦ symmData γ p` is `C^∞` at every point at which the divided difference
does not vanish. -/
lemma contDiffAt_symmData (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) {σ s : ℝ} (h : symmWC γ σ s ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => symmData γ p) (σ, s) := by
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => symmR γ p.1 p.2) (σ, s) :=
    (contDiff_symmR hγ hγne).contDiffAt
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => symmD γ p.1 p.2) (σ, s) :=
    (contDiff_symmD hγ hγne).contDiffAt
  have h3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => symmE γ p.1 p.2) (σ, s) :=
    contDiffAt_symmE_of_ne hγ h
  simpa only [symmData] using h1.prodMk (h2.prodMk h3)

/-- If `χ` is `C^∞` with closed support inside an open set on which `f` is `C^∞`, then `χ • f` is
globally `C^∞`. -/
def seamCN (G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ) (q : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  (G q).2.2 * ((((‖(G q).2.2‖ : ℝ)) : ℂ))⁻¹

/-- `seamCN` rotated by the inverse of its value at the base point, so that it is `1` there. -/
def seamW (G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ) (p₀ q : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  seamCN G q * star ((G p₀).2.2)

/-- The smooth square root of the third capping coordinate, using the branch of `circSqrt` at the
base point. -/
def seamHalf (G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ) (p₀ q : EuclideanSpace ℝ (Fin 2)) : ℂ :=
  if seamW G p₀ q + 1 = 0 then Complex.exp (Complex.log ((G p₀).2.2) / 2)
  else Complex.exp (Complex.log ((G p₀).2.2) / 2) * circSqrt (seamW G p₀ q)

lemma norm_seamCN {G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ} {q : EuclideanSpace ℝ (Fin 2)}
    (hc : (G q).2.2 ≠ 0) : ‖seamCN G q‖ = 1 := by
  rw [seamCN, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr hc)]

lemma seamCN_eq_of_norm_eq_one {G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ}
    {q : EuclideanSpace ℝ (Fin 2)} (h : ‖(G q).2.2‖ = 1) : seamCN G q = (G q).2.2 := by
  rw [seamCN, h]
  norm_num

lemma seamW_self {G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ} {p₀ : EuclideanSpace ℝ (Fin 2)}
    (h : ‖(G p₀).2.2‖ = 1) : seamW G p₀ p₀ = 1 := by
  rw [seamW, seamCN_eq_of_norm_eq_one h]
  have hc := Complex.mul_conj ((G p₀).2.2)
  rw [starRingEnd_apply, Complex.normSq_eq_norm_sq, h] at hc
  norm_num at hc
  exact hc

lemma norm_seamHalf_exp {G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ}
    {p₀ : EuclideanSpace ℝ (Fin 2)} (h : ‖(G p₀).2.2‖ = 1) :
    ‖Complex.exp (Complex.log ((G p₀).2.2) / 2)‖ = 1 := by
  rw [Complex.norm_exp, Complex.div_re, Complex.log_re, h, Real.log_one]
  norm_num

/-- `circSqrt` is `C^∞` at every point where `w + 1 ≠ 0`. -/
lemma contDiffAt_circSqrt {w : ℂ} (h : w + 1 ≠ 0) : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) circSqrt w := by
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => z + 1) w :=
    contDiffAt_id.add contDiffAt_const
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => ‖z + 1‖) w :=
    ContDiffAt.norm ℝ h1 h
  have h2i : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => (1 : ℝ) / ‖z + 1‖) w :=
    (contDiffAt_const : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : ℂ => (1 : ℝ)) w).div h2 (norm_ne_zero_iff.mpr h)
  have h3 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => (((1 : ℝ) / ‖z + 1‖ : ℝ) : ℂ)) w :=
    (Complex.ofRealCLM.contDiff.contDiffAt).comp w h2i
  rw [show circSqrt = (fun z : ℂ => (z + 1) * (((1 : ℝ) / ‖z + 1‖ : ℝ) : ℂ))
        from funext circSqrt_eq]
  exact h1.mul h3

lemma seamHalf_norm {G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ} {p₀ : EuclideanSpace ℝ (Fin 2)}
    (h : ‖(G p₀).2.2‖ = 1) (q : EuclideanSpace ℝ (Fin 2)) : ‖seamHalf G p₀ q‖ = 1 := by
  rw [seamHalf]
  by_cases hq : seamW G p₀ q + 1 = 0
  · rw [if_pos hq]; exact norm_seamHalf_exp h
  · rw [if_neg hq, norm_mul, norm_seamHalf_exp h, norm_circSqrt hq, one_mul]

/-- **The halving is smooth wherever the data is, the third coordinate does not vanish and the
branch point is avoided.** -/
lemma contDiffAt_seamHalf_of_branch {G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ}
    {p₀ q : EuclideanSpace ℝ (Fin 2)} (_hunit : ‖(G p₀).2.2‖ = 1)
    (hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G q) (hc : (G q).2.2 ≠ 0)
    (hw : seamW G p₀ q + 1 ≠ 0) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => seamHalf G p₀ z) q := by
  have hcn : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => seamCN G z) q := by
    have hnum : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => (G z).2.2) q := (hG.snd).snd
    have hden : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z => (((‖(G z).2.2‖ : ℝ)) : ℂ)) q :=
      (Complex.ofRealCLM.contDiff.contDiffAt).comp q
        (ContDiffAt.norm ℝ ((hG.snd).snd) hc)
    have hne : (((‖(G q).2.2‖ : ℝ)) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact norm_ne_zero_iff.mpr hc
    exact hnum.mul (hden.inv hne)
  have hwsm : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => seamW G p₀ z) q :=
    hcn.mul contDiffAt_const
  have hev : ∀ᶠ z in nhds q, seamW G p₀ z + 1 ≠ 0 :=
    (hwsm.continuousAt.add continuousAt_const).eventually_ne (by simpa using hw)
  have hcs : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) circSqrt (seamW G p₀ q) :=
    contDiffAt_circSqrt hw
  have hcomp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => circSqrt (seamW G p₀ z)) q := ContDiffAt.comp q hcs hwsm
  have hmul : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => Complex.exp (Complex.log ((G p₀).2.2) / 2) * circSqrt (seamW G p₀ z)) q :=
    (contDiffAt_const).mul hcomp
  have heq : (fun z => seamHalf G p₀ z) =ᶠ[nhds q]
      (fun z => Complex.exp (Complex.log ((G p₀).2.2) / 2) * circSqrt (seamW G p₀ z)) := by
    filter_upwards [hev] with z hz
    rw [seamHalf, if_neg hz]
  exact ContDiffAt.congr_of_eventuallyEq (f := fun z =>
      Complex.exp (Complex.log ((G p₀).2.2) / 2) * circSqrt (seamW G p₀ z))
    (f₁ := fun z => seamHalf G p₀ z) hmul heq

lemma seamHalf_sq {G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ} {p₀ : EuclideanSpace ℝ (Fin 2)}
    (h : ‖(G p₀).2.2‖ = 1) {q : EuclideanSpace ℝ (Fin 2)} (hc : (G q).2.2 ≠ 0)
    (hw : seamW G p₀ q + 1 ≠ 0) : seamHalf G p₀ q ^ 2 = seamCN G q := by
  have hz0 : (G p₀).2.2 ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at h
    norm_num at h
  have hzu : Complex.exp (Complex.log ((G p₀).2.2) / 2) ^ 2 = (G p₀).2.2 := by
    rw [pow_two, ← Complex.exp_add]
    have h2 : Complex.log ((G p₀).2.2) / 2 + Complex.log ((G p₀).2.2) / 2
        = Complex.log ((G p₀).2.2) := by ring
    rw [h2, Complex.exp_log hz0]
  have hwn : ‖seamW G p₀ q‖ = 1 := by
    rw [seamW, norm_mul, norm_seamCN hc, norm_star, h, one_mul]
  have hzz : (G p₀).2.2 * star ((G p₀).2.2) = 1 := by
    have hc2 := Complex.mul_conj ((G p₀).2.2)
    rw [starRingEnd_apply, Complex.normSq_eq_norm_sq, h] at hc2
    norm_num at hc2
    exact hc2
  rw [seamHalf, if_neg hw, mul_pow, hzu, circSqrt_sq hwn hw, seamW]
  rw [mul_comm (seamCN G q) (star ((G p₀).2.2)), ← mul_assoc, hzz, one_mul]

/-- `seamHalf` is smooth at the base point as soon as the data is. -/
lemma contDiffAt_seamHalf {G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ}
    {p₀ : EuclideanSpace ℝ (Fin 2)} (h : ‖(G p₀).2.2‖ = 1)
    (hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G p₀) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q => seamHalf G p₀ q) p₀ := by
  have hz0 : (G p₀).2.2 ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at h
    norm_num at h
  have hcn : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q => seamCN G q) p₀ := by
    have hnum : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q => (G q).2.2) p₀ := (hG.snd).snd
    have hden : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q => (((‖(G q).2.2‖ : ℝ)) : ℂ)) p₀ :=
      (Complex.ofRealCLM.contDiff.contDiffAt).comp p₀
        (ContDiffAt.norm ℝ ((hG.snd).snd) hz0)
    have hne : (((‖(G p₀).2.2‖ : ℝ)) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact norm_ne_zero_iff.mpr hz0
    exact hnum.mul (hden.inv hne)
  have hw : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q => seamW G p₀ q) p₀ :=
    hcn.mul contDiffAt_const
  have hw1 : seamW G p₀ p₀ = 1 := seamW_self h
  have hne : ∀ᶠ q in nhds p₀, seamW G p₀ q + 1 ≠ 0 := by
    have hca : ContinuousAt (fun q => seamW G p₀ q + 1) p₀ :=
      hw.continuousAt.add continuousAt_const
    refine hca.eventually_ne ?_
    show seamW G p₀ p₀ + 1 ≠ 0
    rw [hw1]; norm_num
  have hcs : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) circSqrt (seamW G p₀ p₀) := by
    rw [hw1]; exact contDiffAt_circSqrt_one
  have hcomp : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q => circSqrt (seamW G p₀ q)) p₀ := ContDiffAt.comp p₀ hcs hw
  have hmul : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q => Complex.exp (Complex.log ((G p₀).2.2) / 2) * circSqrt (seamW G p₀ q)) p₀ :=
    (contDiffAt_const).mul hcomp
  have heq : (fun q => seamHalf G p₀ q) =ᶠ[nhds p₀]
      (fun q => Complex.exp (Complex.log ((G p₀).2.2) / 2) * circSqrt (seamW G p₀ q)) := by
    filter_upwards [hne] with q hq
    rw [seamHalf, if_neg hq]
  exact ContDiffAt.congr_of_eventuallyEq (f := fun q =>
      Complex.exp (Complex.log ((G p₀).2.2) / 2) * circSqrt (seamW G p₀ q))
    (f₁ := fun q => seamHalf G p₀ q) hmul heq

/-- `seamW` is smooth at the base point as soon as the data is. -/
lemma contDiffAt_seamW {G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ}
    {p₀ : EuclideanSpace ℝ (Fin 2)} (h : ‖(G p₀).2.2‖ = 1)
    (hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G p₀) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q => seamW G p₀ q) p₀ := by
  have hz0 : (G p₀).2.2 ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at h
    norm_num at h
  have hcn : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q => seamCN G q) p₀ := by
    have hnum : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q => (G q).2.2) p₀ := (hG.snd).snd
    have hden : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q => (((‖(G q).2.2‖ : ℝ)) : ℂ)) p₀ :=
      (Complex.ofRealCLM.contDiff.contDiffAt).comp p₀
        (ContDiffAt.norm ℝ ((hG.snd).snd) hz0)
    have hne : (((‖(G p₀).2.2‖ : ℝ)) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact norm_ne_zero_iff.mpr hz0
    exact hnum.mul (hden.inv hne)
  exact hcn.mul contDiffAt_const

/-- The projective vector of the capping data at `q`, using the halving `seamHalf`. -/
def seamProjVec (G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ) (p₀ q : EuclideanSpace ℝ (Fin 2)) :
    Eucl 3 :=
  confProjVecOf (seamHalf G p₀ q) ((G q).2.1)

/-- `seamProjVec` never vanishes, with no side condition on the disk coordinate. -/
lemma seamProjVec_ne_zero {G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ}
    {p₀ : EuclideanSpace ℝ (Fin 2)} (h : ‖(G p₀).2.2‖ = 1) (q : EuclideanSpace ℝ (Fin 2)) :
    seamProjVec G p₀ q ≠ 0 := by
  intro hzero
  have hun : ‖seamHalf G p₀ q‖ = 1 := seamHalf_norm h q
  have hu0 : seamHalf G p₀ q ≠ 0 := by
    intro hh
    rw [hh, norm_zero] at hun
    norm_num at hun
  have h1 : c₁ (seamProjVec G p₀ q) = 0 := by rw [hzero]; simp [c₁]
  have h2 : c₂ (seamProjVec G p₀ q) = 0 := by rw [hzero]; simp [c₂]
  rw [seamProjVec, c₁_confProjVecOf] at h1
  rw [seamProjVec, c₂_confProjVecOf] at h2
  have hd0 : (G q).2.1 = 0 := by
    rcases div_eq_zero_iff.mp h2 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h2 | h2
      · exact absurd (star_eq_zero.mp h2) hu0
      · exact h2
    · exact absurd h2 (by norm_num : (((Real.sqrt 2 : ℝ)) : ℂ) ≠ 0)
  have hsqrt0 : Real.sqrt (1 - ‖(G q).2.1‖ ^ 2 / 2) = 0 := by
    rcases mul_eq_zero.mp h1 with h1 | h1
    · exact absurd h1 hu0
    · exact Complex.ofReal_eq_zero.mp h1
  rw [hd0, norm_zero] at hsqrt0
  norm_num at hsqrt0

/-- The projective model of the seam chart: the radial coordinate and the class of the lifted vector
in `ℝP³`. -/
noncomputable def seamProj (G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ)
    (p₀ : EuclideanSpace ℝ (Fin 2)) (h : ‖(G p₀).2.2‖ = 1) :
    EuclideanSpace ℝ (Fin 2) →
      Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)) :=
  fun q => (if hh : 0 < (G q).1 then (⟨(G q).1, hh⟩ : Set.Ioi (0 : ℝ))
      else (⟨(1 : ℝ), by norm_num⟩ : Set.Ioi (0 : ℝ)),
    Projectivization.mk ℝ (seamProjVec G p₀ q) (seamProjVec_ne_zero h q))

/-- **The seam chart**: the strip chart extended across the gluing torus. -/
noncomputable def seamChart (G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ)
    (p₀ : EuclideanSpace ℝ (Fin 2)) (h : ‖(G p₀).2.2‖ = 1) :
    EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  fun q => cappingSpaceHomeoProj.symm (seamProj G p₀ h q)

/-- Smoothness of the lifted projective vector from the non-vanishing of the square root, the only
hypothesis needed being `1 - ‖d‖²/2 ≠ 0` (rather than `‖d‖ ≤ 1`). -/
lemma contDiffAt_confProjVecOf_of_ne {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u d : E → ℂ} {x : E} {n : WithTop ℕ∞} (hu : ContDiffAt ℝ n u x) (hd : ContDiffAt ℝ n d x)
    (h : 1 - ‖d x‖ ^ 2 / 2 ≠ 0) :
    ContDiffAt ℝ n (fun w => confProjVecOf (u w) (d w)) x := by
  have hre : ContDiffAt ℝ n (fun w => (d w).re) x :=
    (Complex.reCLM.contDiff.contDiffAt).comp x hd
  have him : ContDiffAt ℝ n (fun w => (d w).im) x :=
    (Complex.imCLM.contDiff.contDiffAt).comp x hd
  have hnorm2 : ContDiffAt ℝ n (fun w => ‖d w‖ ^ 2) x := by
    have h' := (hre.mul hre).add (him.mul him)
    have hfun : (fun w => ‖d w‖ ^ 2)
        = fun w => (d w).re * (d w).re + (d w).im * (d w).im := by
      funext w
      rw [Complex.sq_norm, Complex.normSq_apply]
    rw [hfun]
    exact h'
  have hinner : ContDiffAt ℝ n (fun w => 1 - ‖d w‖ ^ 2 / 2) x :=
    contDiffAt_const.sub (hnorm2.div_const 2)
  have hsqrt : ContDiffAt ℝ n (fun w => Real.sqrt (1 - ‖d w‖ ^ 2 / 2)) x :=
    (Real.contDiffAt_sqrt h).comp x hinner
  have h1 : ContDiffAt ℝ n
      (fun w => u w * ((Real.sqrt (1 - ‖d w‖ ^ 2 / 2) : ℝ) : ℂ)) x :=
    hu.mul ((Complex.ofRealCLM.contDiff.contDiffAt).comp x hsqrt)
  have hstar : ContDiffAt ℝ n (fun w => star (u w)) x :=
    (Complex.conjCLE.contDiff.contDiffAt).comp x hu
  have h2 : ContDiffAt ℝ n
      (fun w => star (u w) * d w / ((Real.sqrt 2 : ℝ) : ℂ)) x :=
    (hstar.mul hd).div_const _
  have := contDiffAt_ofComplex h1 h2
  simpa only [confProjVecOf] using this

set_option linter.style.haveILetI false in
/-- **The seam chart is smooth at every point at which the data is and the side conditions hold.** -/
theorem contMDiffAt_seamChart' {G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ}
    {p₀ q : EuclideanSpace ℝ (Fin 2)} (hunit : ‖(G p₀).2.2‖ = 1)
    (hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G q) (hr : 0 < (G q).1)
    (hc : (G q).2.2 ≠ 0) (hsqrt : 1 - ‖(G q).2.1‖ ^ 2 / 2 ≠ 0)
    (hw : seamW G p₀ q + 1 ≠ 0) :
    letI := cappingCharted
    ContMDiffAt (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (seamChart G p₀ hunit) q := by
  letI := cappingCharted
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0 : ℝ)) :=
    Homeomorph.chartedSpace expHomeo
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    halfLineProjectiveCharted
  have hchart := chartedStructure_contMDiffWithinAt (𝕜 := ℝ)
    (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    (E' := EuclideanSpace ℝ (Fin 2)) (H' := EuclideanSpace ℝ (Fin 2)) (𝓡 2)
    (M := Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
    (M' := CappingSpace) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    cappingSpaceHomeoProj.symm (seamChart G p₀ hunit) Set.univ q
  change ContMDiffWithinAt (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (seamChart G p₀ hunit) Set.univ q
  refine hchart.mpr ?_
  have hsub : (fun y : EuclideanSpace ℝ (Fin 2) =>
        cappingSpaceHomeoProj.symm.symm (seamChart G p₀ hunit y)) = seamProj G p₀ hunit := by
    funext y
    simp only [Homeomorph.symm_symm, seamChart]
    exact Homeomorph.apply_symm_apply cappingSpaceHomeoProj (seamProj G p₀ hunit y)
  rw [hsub, contMDiffWithinAt_univ]
  refine (contMDiffAt_halfLineProjective_iff (seamProj G p₀ hunit) q).mpr ⟨?_, ?_⟩
  · rw [contMDiffAt_iff_contDiffAt]
    have hpos : ∀ᶠ z in nhds q, 0 < (G z).1 :=
      hG.continuousAt.fst.preimage_mem_nhds
        ((isOpen_lt continuous_const continuous_id).mem_nhds hr)
    have hfsteq : (fun z => expHomeo.symm (seamProj G p₀ hunit z).1)
        =ᶠ[nhds q] fun z => logEucl (Real.log ((G z).1)) := by
      filter_upwards [hpos] with z hz
      show expHomeo.symm (if hh : 0 < (G z).1 then (⟨(G z).1, hh⟩ : Set.Ioi (0 : ℝ))
          else (⟨(1 : ℝ), by norm_num⟩ : Set.Ioi (0 : ℝ))) = logEucl (Real.log ((G z).1))
      rw [dif_pos hz]
      exact expHomeo_symm_apply ⟨(G z).1, hz⟩
    exact ContDiffAt.congr_of_eventuallyEq (f := fun z => logEucl (Real.log ((G z).1)))
      (f₁ := fun z => expHomeo.symm (seamProj G p₀ hunit z).1)
      ((logEucl.contDiff.contDiffAt).comp q (hG.fst.log (ne_of_gt hr))) hfsteq
  · unfold seamProj
    refine contMDiffAt_projMk (seamProjVec G p₀) (seamProjVec_ne_zero hunit) q ?_
    rw [contMDiffAt_iff_contDiffAt]
    exact contDiffAt_confProjVecOf_of_ne (contDiffAt_seamHalf_of_branch hunit hG hc hw)
      ((hG.snd).fst) hsqrt

set_option linter.style.haveILetI false in
/-- **The seam chart is globally smooth** under global side conditions on the data: positive radial
coordinate, non-vanishing third coordinate (so that the halving is defined), `1 - ‖d‖²/2 ≠ 0` and the
branch condition `seamW + 1 ≠ 0`. -/
theorem contMDiff_seamChart {G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ}
    {p₀ : EuclideanSpace ℝ (Fin 2)} (hunit : ‖(G p₀).2.2‖ = 1)
    (hG : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G) (hr : ∀ q, 0 < (G q).1)
    (hc : ∀ q, (G q).2.2 ≠ 0) (hsqrt : ∀ q, 1 - ‖(G q).2.1‖ ^ 2 / 2 ≠ 0)
    (hw : ∀ q, seamW G p₀ q + 1 ≠ 0) :
    letI := cappingCharted
    ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (seamChart G p₀ hunit) := by
  letI := cappingCharted
  intro q
  exact contMDiffAt_seamChart' hunit hG.contDiffAt (hr q) (hc q) (hsqrt q) (hw q)

set_option linter.style.haveILetI false in
/-- **The seam chart is smooth.** -/
theorem contMDiffAt_seamChart {G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ}
    {p₀ : EuclideanSpace ℝ (Fin 2)} (hunit : ‖(G p₀).2.2‖ = 1)
    (hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G p₀) (hr : 0 < (G p₀).1)
    (hd : ‖(G p₀).2.1‖ ≤ 1) :
    letI := cappingCharted
    ContMDiffAt (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (seamChart G p₀ hunit) p₀ := by
  letI := cappingCharted
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 3))
      (Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) := projCharted 3
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 1)) (Set.Ioi (0 : ℝ)) :=
    Homeomorph.chartedSpace expHomeo
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 4))
      (Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4))) :=
    halfLineProjectiveCharted
  have hchart := chartedStructure_contMDiffWithinAt (𝕜 := ℝ)
    (E := EuclideanSpace ℝ (Fin 4)) (H := EuclideanSpace ℝ (Fin 4))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    (E' := EuclideanSpace ℝ (Fin 2)) (H' := EuclideanSpace ℝ (Fin 2)) (𝓡 2)
    (M := Set.Ioi (0 : ℝ) × Projectivization ℝ (EuclideanSpace ℝ (Fin 4)))
    (M' := CappingSpace) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    cappingSpaceHomeoProj.symm (seamChart G p₀ hunit) Set.univ p₀
  change ContMDiffWithinAt (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (seamChart G p₀ hunit) Set.univ p₀
  refine hchart.mpr ?_
  have hsub : (fun y : EuclideanSpace ℝ (Fin 2) =>
        cappingSpaceHomeoProj.symm.symm (seamChart G p₀ hunit y)) = seamProj G p₀ hunit := by
    funext y
    simp only [Homeomorph.symm_symm, seamChart]
    exact Homeomorph.apply_symm_apply cappingSpaceHomeoProj (seamProj G p₀ hunit y)
  rw [hsub, contMDiffWithinAt_univ]
  refine (contMDiffAt_halfLineProjective_iff (seamProj G p₀ hunit) p₀).mpr ⟨?_, ?_⟩
  · rw [contMDiffAt_iff_contDiffAt]
    have hpos : ∀ᶠ q in nhds p₀, 0 < (G q).1 :=
      hG.continuousAt.fst.preimage_mem_nhds
        ((isOpen_lt continuous_const continuous_id).mem_nhds hr)
    have hfsteq : (fun q => expHomeo.symm (seamProj G p₀ hunit q).1)
        =ᶠ[nhds p₀] fun q => logEucl (Real.log ((G q).1)) := by
      filter_upwards [hpos] with q hq
      show expHomeo.symm (if hh : 0 < (G q).1 then (⟨(G q).1, hh⟩ : Set.Ioi (0 : ℝ))
          else (⟨(1 : ℝ), by norm_num⟩ : Set.Ioi (0 : ℝ))) = logEucl (Real.log ((G q).1))
      rw [dif_pos hq]
      exact expHomeo_symm_apply ⟨(G q).1, hq⟩
    exact ContDiffAt.congr_of_eventuallyEq (f := fun q => logEucl (Real.log ((G q).1)))
      (f₁ := fun q => expHomeo.symm (seamProj G p₀ hunit q).1)
      ((logEucl.contDiff.contDiffAt).comp p₀ (hG.fst.log (ne_of_gt hr))) hfsteq
  · unfold seamProj
    refine contMDiffAt_projMk (seamProjVec G p₀) (seamProjVec_ne_zero hunit) p₀ ?_
    rw [contMDiffAt_iff_contDiffAt]
    exact contDiffAt_confProjVecOf (contDiffAt_seamHalf hunit hG) ((hG.snd).fst) hd

/-- **The value of the seam chart on the strip side.**  Under the honest-ness conditions (which hold
on the half-plane `τ ≥ 0` near a seam point) the seam chart is the `τ`-chart of the strip. -/
theorem seamChart_eq_stripTauChart {G : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × ℂ}
    {p₀ : EuclideanSpace ℝ (Fin 2)} (hunit : ‖(G p₀).2.2‖ = 1)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (σ₀ : ℝ)
    (hhonest : ∀ᶠ p in nhds p₀, 0 ≤ p 1 →
      (0 < (G p).1 ∧ ‖(G p).2.1‖ ≤ 1 ∧ ‖(G p).2.2‖ = 1 ∧ seamW G p₀ p + 1 ≠ 0)) :
    ∀ᶠ p in nhds p₀, 0 ≤ p 1 → seamChart G p₀ hunit p = stripTauChart hγ hγne G σ₀ p := by
  filter_upwards [hhonest] with p hp hp0
  obtain ⟨h1, h2, h3, hw⟩ := hp hp0
  have hne : (G p).2.2 ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at h3
    norm_num at h3
  have hmem : (G p).2.1 ∈ Metric.closedBall (0 : ℂ) 1 :=
    mem_closedBall_of_norm_le_one h2
  have htd : tauData hγ hγne G σ₀ p = ((G p).1, (G p).2.1, tauS G p) :=
    tauData_eq_of_good hγ hγne G σ₀ ⟨h1, h2⟩
  have hη : tauS G p = circOf ((G p).2.2) h3 := by
    apply circleOf_injective
    rw [circleOf_tauS, tauE_eq_of_norm_eq_one h3, circleOf_circOf]
  have hpiece : (⟨tauData hγ hγne G σ₀ p, tauData_pos hγ hγne G σ₀ p,
      tauData_norm_le_one hγ hγne G σ₀ p⟩ : ConfigPiece)
      = ⟨((G p).1, (G p).2.1, circOf ((G p).2.2) h3), h1, h2⟩ := by
    refine Subtype.ext ?_
    show tauData hγ hγne G σ₀ p = ((G p).1, (G p).2.1, circOf ((G p).2.2) h3)
    rw [htd, hη]
  have hA : cappingSpaceHomeoProj (stripTauChart hγ hγne G σ₀ p)
      = (⟨(G p).1, h1⟩, lensToProj (Quotient.mk'' (Sum.inr
          ((⟨(G p).2.1, hmem⟩ : Metric.closedBall (0 : ℂ) 1), circOf ((G p).2.2) h3) :
            CapTorus ⊕ ConfTorus) : LensSpace)) := by
    have hq : stripTauChart hγ hγne G σ₀ p
        = Quotient.mk'' (Sum.inl ⟨((G p).1, (G p).2.1, circOf ((G p).2.2) h3), h1, h2⟩) := by
      unfold stripTauChart
      exact congrArg (fun x : ConfigPiece => (Quotient.mk'' (Sum.inl x) : CappingSpace)) hpiece
    rw [hq]
    exact cappingSpaceHomeoProj_confPiece (G p).1 (G p).2.1 (circOf ((G p).2.2) h3) h1 h2
  have hu : (seamHalf G p₀ p) ^ 2 = circleOf (circOf ((G p).2.2) h3) := by
    rw [seamHalf_sq hunit hne hw, seamCN_eq_of_norm_eq_one h3]
    exact (circleOf_circOf ((G p).2.2) h3).symm
  have hB : lensToProj (Quotient.mk'' (Sum.inr
        ((⟨(G p).2.1, hmem⟩ : Metric.closedBall (0 : ℂ) 1), circOf ((G p).2.2) h3) :
          CapTorus ⊕ ConfTorus) : LensSpace)
      = Projectivization.mk ℝ (seamProjVec G p₀ p) (seamProjVec_ne_zero hunit p) := by
    rw [lensToProj_confTorus (⟨(G p).2.1, hmem⟩ : Metric.closedBall (0 : ℂ) 1)
      (circOf ((G p).2.2) h3) hu]
    exact projectivizationMk_congr ℝ (Eucl 3)
  have hval : cappingSpaceHomeoProj (stripTauChart hγ hγne G σ₀ p) = seamProj G p₀ hunit p := by
    rw [hA, hB]
    unfold seamProj
    rw [dif_pos h1]
  have hL : cappingSpaceHomeoProj (seamChart G p₀ hunit p) = seamProj G p₀ hunit p := by
    rw [seamChart]
    exact Homeomorph.apply_symm_apply cappingSpaceHomeoProj (seamProj G p₀ hunit p)
  exact cappingSpaceHomeoProj.injective (by rw [hL, hval])


open Manifold in
open scoped Manifold ContDiff in

end

end Work.Drive.Neutral
