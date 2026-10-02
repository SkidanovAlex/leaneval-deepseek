/-
Work.MRMT.Beltrami — **the Cauchy transform inverts `∂̄`**: `∂̄(C ω) = ω` for `ω ∈ L¹(ℂ)`.

Statement: for `ω : ℂ → ℂ` with `∫ ‖ω‖ < ∞`,

  `Work.MRMT.IsDbarDeriv (Work.MRMT.cauchyTransform ω) ω`

i.e. `C ω` and `ω` are locally integrable and for every test function `φ : 𝓓(⊤, ℂ)`

  `∫ z, C ω z * ∂̄φ(z) = -∫ z, ω z * φ(z)`,  where `C ω z = -(1/π) ∫ ζ, ω ζ / (ζ - z)`.

This is the non-degenerate form of `∂̄(C ω) = ω` (the sibling statement
`Work.MRMT.Cauchy.isDbarDeriv_cauchy` is vacuous because its hypothesis `ContDiff ℝ ⊤ ω` is
*real analyticity*, which with compact support forces `ω = 0`).

## Route of the proof

`CauchyTransform ω(z) = -(1/π) ∫ ζ, ω ζ /(ζ - z)` is an absolutely convergent integral, and for
every test function `φ`, writing `G = ∂̄φ` (smooth, compactly supported),

`∫ z, C ω z * G z = -(1/π) ∫ z, (∫ ζ, ω ζ /(ζ - z)) * G z`
`                = -(1/π) ∫∫ ω ζ * G z /(ζ - z)`
`                = -(1/π) ∫ ζ, ω ζ * (∫ z, G z /(ζ - z))   (Fubini)`
`                = -(1/π) ∫ ζ, ω ζ * (π * φ ζ)             (Cauchy–Pompeiu: ∫ ∂̄φ(z)/(ζ - z) = π φ ζ)`
`                = -∫ ζ, ω ζ * φ ζ`,

the Fubini step being licensed by `Work.MRMT.Cauchy.integrable_prod_mul_div_sub`
(`1/‖ζ - z‖` is only logarithmically singular, and `∂̄φ` has compact support).

The two analytic inputs are

* `Work.MRMT.Cauchy.locallyIntegrable_cauchyTransform`: an `L¹` function's Cauchy transform is
  locally integrable (needed both for the first conjunct of `IsDbarDeriv` and for the
  integrability of `z ↦ C ω z * ∂̄φ z`, `∂̄φ` being continuous with compact support); and
* `Work.MRMT.Cauchy.integral_dzbar_div_sub_eq_pi_mul`: the Cauchy–Pompeiu identity
  `∫ z, ∂̄ψ(z)/(ζ - z) = π ψ(ζ)` for smooth compactly supported `ψ`, i.e. the distributional
  statement `∂̄(1/(πζ)) = δ₀` (here in the equivalent shifted form).

The remaining two integrabilities (`z ↦ C ω z * ∂̄φ z` and `z ↦ ω z * φ z`) and the Fubini
identity above are proved here.
-/
import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Cauchy.Defs
import Submission.Work.MRMT.Cauchy.integrable_prod_mul_div_sub
import Submission.Work.MRMT.Cauchy.locallyIntegrable_cauchyTransform
import Submission.Work.MRMT.Cauchy.integral_dzbar_div_sub_eq_pi_mul

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal

namespace Work.MRMT.Beltrami

/-- `∂̄φ` is smooth for every test function `φ ∈ 𝓓(⊤, ℂ)`.

`∂̄φ z = (Dφ(z)(1) + i·Dφ(z)(i))/2`, and `x ↦ Dφ(x)(v)` is smooth for `φ` smooth
(`ContDiff.contDiff_fderiv_apply` composed with `z ↦ (z, v)`, `contDiff_prodMk_left`). -/
private lemma contDiff_dzbar_test (φ : 𝓓(⊤, ℂ)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => Work.MRMT.dzbar (φ : ℂ → ℂ) z) := by
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φ : ℂ → ℂ) := φ.contDiff
  have hmn : ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by simp
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℂ × ℂ => (fderiv ℝ (φ : ℂ → ℂ) p.1) p.2) := hc.contDiff_fderiv_apply hmn
  have hA : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => fderiv ℝ (φ : ℂ → ℂ) z (1 : ℂ)) :=
    h1.comp (contDiff_prodMk_left (1 : ℂ))
  have hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => fderiv ℝ (φ : ℂ → ℂ) z Complex.I) :=
    h1.comp (contDiff_prodMk_left Complex.I)
  have hcst : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : ℂ => Complex.I) := contDiff_const
  have hcomb := (hA.add (hcst.mul hB)).div_const 2
  simpa only [Work.MRMT.dzbar, div_eq_mul_inv] using hcomb

/-- `∂̄φ` has compact support for every test function `φ`, since `∂̄φ` vanishes where `φ` does. -/
private lemma hasCompactSupport_dzbar_test (φ : 𝓓(⊤, ℂ)) :
    HasCompactSupport (fun z => Work.MRMT.dzbar (φ : ℂ → ℂ) z) := by
  have h1 : HasCompactSupport (fun z : ℂ => fderiv ℝ (φ : ℂ → ℂ) z (1 : ℂ)) :=
    (φ.hasCompactSupport).fderiv_apply ℝ (1 : ℂ)
  have h2 : HasCompactSupport (fun z : ℂ => fderiv ℝ (φ : ℂ → ℂ) z Complex.I) :=
    (φ.hasCompactSupport).fderiv_apply ℝ Complex.I
  have h3 : HasCompactSupport (fun z : ℂ => Complex.I * fderiv ℝ (φ : ℂ → ℂ) z Complex.I) :=
    h2.comp_left (g := fun w : ℂ => Complex.I * w) (by simp)
  have h4 : HasCompactSupport (fun z : ℂ =>
      fderiv ℝ (φ : ℂ → ℂ) z (1 : ℂ) + Complex.I * fderiv ℝ (φ : ℂ → ℂ) z Complex.I) :=
    h1.add h3
  have h5 := h4.comp_left (g := fun w : ℂ => w * (2 : ℂ)⁻¹) (by simp)
  simpa only [Work.MRMT.dzbar, div_eq_mul_inv, Function.comp_def] using h5

theorem cauchyTransform_inversion (ω : ℂ → ℂ)
    (hω : MeasureTheory.Integrable ω (MeasureTheory.volume : MeasureTheory.Measure ℂ)) :
    Work.MRMT.IsDbarDeriv (Work.MRMT.cauchyTransform ω) ω := by
  -- The Cauchy transform of an `L¹` function is locally integrable.
  have hLoc : MeasureTheory.LocallyIntegrable (Work.MRMT.cauchyTransform ω)
      (MeasureTheory.volume : MeasureTheory.Measure ℂ) :=
    Work.MRMT.Cauchy.locallyIntegrable_cauchyTransform ω hω
  refine ⟨hLoc, hω.locallyIntegrable, fun φ => ?_⟩
  -- `C ω · ∂̄φ` and `ω · φ` are integrable, and the pairing identity holds.
  have h1 : Integrable (fun z => Work.MRMT.cauchyTransform ω z *
      Work.MRMT.dzbar (φ : ℂ → ℂ) z) :=
    (hLoc.integrable_smul_left_of_hasCompactSupport (contDiff_dzbar_test φ).continuous
      (hasCompactSupport_dzbar_test φ)).congr (by
        filter_upwards with z
        rw [smul_eq_mul, mul_comm])
  have h2 : Integrable (fun z => ω z * (φ : ℂ → ℂ) z) :=
    (hω.locallyIntegrable.integrable_smul_left_of_hasCompactSupport φ.contDiff.continuous
      φ.hasCompactSupport).congr (by
        filter_upwards with z
        rw [smul_eq_mul, mul_comm])
  refine ⟨h1, h2, ?_⟩
  -- The Cauchy–Pompeiu identity for smooth compactly supported functions.
  have hShift : ∀ (ψ : ℂ → ℂ), ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
      ∀ ζ : ℂ, ∫ z, Work.MRMT.dzbar ψ z / (ζ - z) = (Real.pi : ℂ) * ψ ζ :=
    fun ψ hψc hψs ζ => Work.MRMT.Cauchy.integral_dzbar_div_sub_eq_pi_mul ψ hψc hψs ζ
  set ψ : ℂ → ℂ := (φ : ℂ → ℂ) with hψdef
  set G : ℂ → ℂ := fun z => Work.MRMT.dzbar ψ z with hGdef
  have hψc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ := by rw [hψdef]; exact φ.contDiff
  have hψs : HasCompactSupport ψ := by rw [hψdef]; exact φ.hasCompactSupport
  have hGc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G := by rw [hGdef, hψdef]; exact contDiff_dzbar_test φ
  have hGs : HasCompactSupport G := by rw [hGdef, hψdef]; exact hasCompactSupport_dzbar_test φ
  have hFub : Integrable (Function.uncurry (fun ζ z : ℂ => ω ζ * G z / (ζ - z)))
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    Work.MRMT.Cauchy.integrable_prod_mul_div_sub ω hω G hGc hGs
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  calc ∫ z, Work.MRMT.cauchyTransform ω z * G z
      = Work.MRMT.cauchyConst * ∫ z, (∫ ζ, ω ζ / (ζ - z)) * G z := by
          simp only [Work.MRMT.cauchyTransform, mul_assoc]
          rw [integral_const_mul]
    _ = Work.MRMT.cauchyConst * ∫ z, ∫ ζ, (ω ζ / (ζ - z)) * G z := by
          congr 1
          apply integral_congr_ae
          filter_upwards with z
          rw [integral_mul_const]
    _ = Work.MRMT.cauchyConst * ∫ z, ∫ ζ, ω ζ * G z / (ζ - z) := by
          congr 1
          apply integral_congr_ae
          filter_upwards with z
          apply integral_congr_ae
          filter_upwards with ζ
          ring
    _ = Work.MRMT.cauchyConst * ∫ ζ, ∫ z, ω ζ * G z / (ζ - z) := by
          rw [integral_integral_swap hFub]
    _ = Work.MRMT.cauchyConst * ∫ ζ, ω ζ * (∫ z, G z / (ζ - z)) := by
          congr 1
          apply integral_congr_ae
          filter_upwards with ζ
          rw [show (fun z : ℂ => ω ζ * G z / (ζ - z)) = fun z => (G z / (ζ - z)) * ω ζ from by
            funext z; ring]
          rw [integral_mul_const]
          ring
    _ = Work.MRMT.cauchyConst * ∫ ζ, ω ζ * ((Real.pi : ℂ) * ψ ζ) := by
          congr 1
          apply integral_congr_ae
          filter_upwards with ζ
          rw [hGdef]
          rw [hShift ψ hψc hψs ζ]
    _ = Work.MRMT.cauchyConst * ((Real.pi : ℂ) * ∫ ζ, ω ζ * ψ ζ) := by
          congr 1
          rw [show (fun ζ : ℂ => ω ζ * ((Real.pi : ℂ) * ψ ζ))
              = fun ζ => (Real.pi : ℂ) * (ω ζ * ψ ζ) from by funext z; ring]
          rw [integral_const_mul]
    _ = -(∫ ζ, ω ζ * ψ ζ) := by
          rw [Work.MRMT.cauchyConst, neg_mul, ← mul_assoc, inv_mul_cancel₀ hpi, one_mul]

end Work.MRMT.Beltrami
