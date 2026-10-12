import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.BoxChi` — FS's localization function `χ_Λ` and the Fourier convention

This module **pins once** the `L²(Λ)` dictionary that FS §8 and every later
section use, in the exact normalisation of FS's Appendix (`eq:Def_chi`,
`eq:chinormalization`, `eq:Theta`, l. 760–790 of `final_v2.tex`):

* `χ` is the localization function on the **unit cell**, with
  `0 ≤ χ`, `χ` even, `∫ χ² = 1`, `χ` supported in the unit cell `cell`;
* `χ_Λ(x) = χ(x/ℓ)` (`ℓ` the side of the box), so `∫ χ_Λ² = ℓ³`;
* `θ = 1_Λ` is the **sharp** characteristic function of the box
  `Λ(ℓ) = ℓ • cell` (`eq:Theta`), and the box projection is
  `P φ = ℓ^{-3}⟨θ,φ⟩θ`, `Q = 1 − P` (`def:projections`);
* `χ̂(p) = ∫ χ(x) cos⟪p,x⟫ dx` and `χ̂²(p) = ∫ χ²(x) cos⟪p,x⟫ dx` are the
  (real, even) Fourier transforms of `χ` and `χ²`; the cos-only form is exactly
  FS's `χ̂` because `χ` is even and real, so the sine part of the Fourier
  integral vanishes.

FS's localised plane waves are `f_k = e^{i k·x} χ_Λ`, and their Gram products

    `ℓ⁻³ ⟪Q f_k, Q f_k'⟫ = χ̂²((k−k')ℓ) − χ̂(kℓ) χ̂(k'ℓ)`

is FS `eq:Commutator_general`, the box kernel `Work.BoseB7.ccrKernel`.  Because
`Q f_k = f_k − χ̂(kℓ)·θ` (one power of `χ_Λ` in each factor, and `θ = 1_Λ`
absorbs the second: `θ · χ_Λ = χ_Λ` on the box), the whole identity is the two
integrals

    `∫ χ_Λ e^{i k·x} = ℓ³ χ̂(ℓk)`,        `∫ χ_Λ² e^{i k·x} = ℓ³ χ̂²(ℓk)`,

together with `volume Λ = ℓ³`.

Everything here is stated over `ℝ³ = EuclideanSpace ℝ (Fin 3)`; the real inner
product `realIP f g = ∫ Re(conj(f x) g x)` is the real part of the `L²(ℂ)` inner
product, which is what the *real* bosonic Fock space of `Work.BoseB4.RealFock`
carries.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseB4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **FS's localization data.**  `chi` is the localization function of FS's
Appendix (`eq:Def_chi`), normalised to `∫χ² = 1` (`eq:chinormalization`); `cell`
is the unit cell it is supported in (`0 ≤ χ`, `χ` even, `χ = 0` off `cell`).

The box of side `ℓ` is `boxL ℓ = ℓ • cell` (`χ_Λ(x) = χ(x/ℓ)` is then supported
in it, and `volume (boxL ℓ) = ℓ³`). -/
structure BoxData where
  /-- The localization function on the unit cell. -/
  chi : ℝ³ → ℝ
  chi_cont : Continuous chi
  chi_nonneg : ∀ x, 0 ≤ chi x
  chi_even : ∀ x, chi (-x) = chi x
  /-- The unit cell (`Λ(0)`), of volume `1`. -/
  cell : Set ℝ³
  cell_meas : MeasurableSet cell
  cell_compact : IsCompact cell
  cell_vol : volume cell = 1
  /-- `χ` vanishes off the unit cell (FS's `ζ(y) = 0` for `|y| > 1/2`). -/
  chi_supp : Function.support chi ⊆ cell
  /-- FS's normalisation `∫χ² = 1`. -/
  chi_int : ∫ x, (chi x) ^ 2 = 1

/-- The real inner product `∫ Re(conj(f x) · g x)`: the real part of the `L²(ℂ)`
inner product, i.e. the inner product of the real bosonic Fock space.  It does
not depend on the box data, but is attached to it so that every notion of this
chapter is reached through the same name. -/
def BoxData.realIP (_B : BoxData) (f g : ℝ³ → ℂ) : ℝ :=
  ∫ x, ((starRingEnd ℂ) (f x) * g x).re

namespace BoxData

variable (B : BoxData)

/-- `χ_Λ(x) = χ(x/ℓ)`: the localization function on the box of side `ℓ`. -/
def chiLam (ℓ : ℝ) : ℝ³ → ℝ := fun x => B.chi (ℓ⁻¹ • x)

/-- The box `Λ(ℓ) = ℓ • cell` of side `ℓ` (FS's `Λ(u) = ℓu + [−ℓ/2,ℓ/2]³`). -/
def boxL (ℓ : ℝ) : Set ℝ³ := ℓ • B.cell

/-- FS's `χ̂`: the (real, even) Fourier transform of `χ`; the sine part vanishes
because `χ` is even and real. -/
def hatChi (p : ℝ³) : ℝ := ∫ x, B.chi x * Real.cos (inner ℝ p x)

/-- FS's `χ̂²`: the (real, even) Fourier transform of `χ²`.  Note that this is
the transform of the *square*, not the square of the transform — the notation is
FS's. -/
def hatChiSq (p : ℝ³) : ℝ := ∫ x, (B.chi x) ^ 2 * Real.cos (inner ℝ p x)

/-- FS's `θ = 1_Λ`: the sharp characteristic function of the box. -/
def thetaFun (ℓ : ℝ) : ℝ³ → ℂ := fun x => if x ∈ B.boxL ℓ then 1 else 0

/-- FS's **unnormalised θ-mode** `e^{isx}θ = e^{isx}1_Λ`: the one-particle vector
of `a(Q(e^{isx}θ))`.  FS's `ã_s = ℓ^{-3/2}a(Q(e^{isx}θ))` has one-particle vector
`ℓ^{-3/2}Q(e^{isx}θ)`, which is orthonormal in `s` for lattice momenta
(`Work.BoseB4.ThetaMode`). -/
def thetaExp (ℓ : ℝ) (s : ℝ³) : ℝ³ → ℂ :=
  fun x => Complex.exp (Complex.I * ((inner ℝ s x : ℝ) : ℂ)) * B.thetaFun ℓ x

/-- FS's localised plane wave `e^{ikx} χ_Λ`. -/
def modeVec (ℓ : ℝ) (k : ℝ³) : ℝ³ → ℂ :=
  fun x => Complex.exp (Complex.I * ((inner ℝ k x : ℝ) : ℂ)) * ((B.chiLam ℓ x : ℝ) : ℂ)

/-- `Q(e^{ikx}χ_Λ) = e^{ikx}χ_Λ − χ̂(kℓ)·θ`: FS's localised plane wave with the
condensate component removed.  (This is `Q` of `def:projections`, using
`ℓ⁻³⟨θ, e^{ikx}χ_Λ⟩ = χ̂(kℓ)`, which is the module `BoxChiIP`.) -/
def qVec (ℓ : ℝ) (k : ℝ³) : ℝ³ → ℂ :=
  fun x => B.modeVec ℓ k x - ((B.hatChi (ℓ • k) : ℝ) : ℂ) * B.thetaFun ℓ x

/-- The real inner product `∫ Re(conj(f x) · g x)` of `L²(ℂ)` (see
`BoxData.realIP`). -/
@[simp] lemma realIP_apply (f g : ℝ³ → ℂ) :
    B.realIP f g = ∫ x, ((starRingEnd ℂ) (f x) * g x).re := rfl

/-- **FS's box kernel** `χ̂²((k−k')ℓ) − χ̂(kℓ)χ̂(k'ℓ)`
(`eq:Commutator_general`), in the form `Work.BoseB7.ccrKernel` uses. -/
def boxKernel (ℓ : ℝ) (k k' : ℝ³) : ℝ :=
  B.hatChiSq (ℓ • (k - k')) - B.hatChi (ℓ • k) * B.hatChi (ℓ • k')

/-! ## Elementary properties -/

lemma chiLam_nonneg (ℓ : ℝ) (x : ℝ³) : 0 ≤ B.chiLam ℓ x := B.chi_nonneg _

lemma chiLam_even (ℓ : ℝ) (x : ℝ³) : B.chiLam ℓ (-x) = B.chiLam ℓ x := by
  simp only [chiLam, smul_neg, B.chi_even]

lemma chiLam_cont (ℓ : ℝ) : Continuous (B.chiLam ℓ) :=
  B.chi_cont.comp (continuous_const_smul _)

lemma hasCompactSupport_chi : HasCompactSupport B.chi :=
  B.cell_compact.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal B.chi_supp B.cell_compact.isClosed)

lemma chi_integrable : Integrable B.chi :=
  B.chi_cont.integrable_of_hasCompactSupport B.hasCompactSupport_chi

lemma chi_sq_integrable : Integrable fun x => (B.chi x) ^ 2 := by
  have h : Integrable (B.chi * B.chi) :=
    (B.chi_cont.mul B.chi_cont).integrable_of_hasCompactSupport
      B.hasCompactSupport_chi.mul_right
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.mul_apply, pow_two]

/-- `χ_Λ` vanishes off the box `Λ(ℓ)`. -/
lemma chiLam_supp {ℓ : ℝ} (hℓ : 0 < ℓ) : Function.support (B.chiLam ℓ) ⊆ B.boxL ℓ := by
  intro x hx
  rw [boxL, Set.mem_smul_set_iff_inv_smul_mem₀ (ne_of_gt hℓ)]
  exact B.chi_supp (show B.chi (ℓ⁻¹ • x) ≠ 0 from hx)

lemma boxL_compact (ℓ : ℝ) : IsCompact (B.boxL ℓ) :=
  IsCompact.smul ℓ B.cell_compact

lemma boxL_measurableSet (ℓ : ℝ) : MeasurableSet (B.boxL ℓ) :=
  (B.boxL_compact ℓ).isClosed.measurableSet

/-- **`volume Λ(ℓ) = ℓ³`**: the box of side `ℓ` has volume `ℓ³`. -/
lemma volume_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) : volume (B.boxL ℓ) = ENNReal.ofReal (ℓ ^ 3) := by
  have hfin : Module.finrank ℝ ℝ³ = 3 := finrank_euclideanSpace_fin
  rw [boxL, Measure.addHaar_smul, hfin, B.cell_vol, mul_one,
    abs_of_nonneg (by positivity)]

/-- The Fourier transform of the localization function is even. -/
lemma hatChi_neg (p : ℝ³) : B.hatChi (-p) = B.hatChi p := by
  simp only [hatChi, inner_neg_left, Real.cos_neg]

/-- The Fourier transform of `χ²` is even. -/
lemma hatChiSq_neg (p : ℝ³) : B.hatChiSq (-p) = B.hatChiSq p := by
  simp only [hatChiSq, inner_neg_left, Real.cos_neg]

/-- `χ̂(0) = ∫χ` is the total mass of `χ`. -/
lemma hatChi_zero : B.hatChi 0 = ∫ x, B.chi x := by
  simp only [hatChi, inner_zero_left, Real.cos_zero, mul_one]

/-- FS's normalisation read at `p = 0`: `χ̂²(0) = 1`. -/
lemma hatChiSq_zero : B.hatChiSq 0 = 1 := by
  simp only [hatChiSq, inner_zero_left, Real.cos_zero, mul_one, B.chi_int]

/-! ## Unfolding lemmas (the interface the proofs below use) -/

@[simp] lemma chiLam_apply (ℓ : ℝ) (x : ℝ³) : B.chiLam ℓ x = B.chi (ℓ⁻¹ • x) := rfl

@[simp] lemma thetaFun_apply (ℓ : ℝ) (x : ℝ³) :
    B.thetaFun ℓ x = if x ∈ B.boxL ℓ then 1 else 0 := rfl

@[simp] lemma modeVec_apply (ℓ : ℝ) (k : ℝ³) (x : ℝ³) :
    B.modeVec ℓ k x
      = Complex.exp (Complex.I * ((inner ℝ k x : ℝ) : ℂ)) * ((B.chiLam ℓ x : ℝ) : ℂ) := rfl

@[simp] lemma thetaExp_apply (ℓ : ℝ) (s : ℝ³) (x : ℝ³) :
    B.thetaExp ℓ s x = Complex.exp (Complex.I * ((inner ℝ s x : ℝ) : ℂ)) * B.thetaFun ℓ x := rfl

@[simp] lemma qVec_apply (ℓ : ℝ) (k : ℝ³) (x : ℝ³) :
    B.qVec ℓ k x = B.modeVec ℓ k x - ((B.hatChi (ℓ • k) : ℝ) : ℂ) * B.thetaFun ℓ x := rfl

end BoxData

end Work.BoseB4
