import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.chat_W1fun_pos_near_zero`

**FS §5.1's second positivity ingredient**: the Fourier transform
`Ŵ₁(k) = chat (W1fun v h ℓ) k = ∫ e^{−i⟨k,y⟩}·g₀(y)/(χ⋆χ)(y/ℓ) dy`
of the χ-renormalised one-body kernel `W₁ = g₀/(χ⋆χ)_ℓ` (`g₀ = v(1−w₀)`) is bounded
*below* by a positive constant `w₀ > 0` in a whole neighbourhood `‖k‖ ≤ r₀` of the origin.
This is the companion of the `−w₁ ≤ Ŵ₁`-row in `Gate.lean`'s `bogA_pos_and_add_pos`: the
gate itself only gives `|Ŵ₁| ≤ K₀ a`, and the Bogoliubov quadratic `𝒜(k) = τ(k) + ρŴ₁(k)`
(and `𝒜+ℬ`) would degenerate if `Ŵ₁` could vanish near `k = 0`.

## The argument

1. `Ŵ₁` is *integrable* and *nonnegative a.e.* in the dilute regime `R ≤ ℓ·chiR0`
   (`Submission.BoseGases.wScaled_g0_integrable`, `…wScaled_g0_nonneg_ae`).
2. `chat W 0 = ∫ W` for integrable `W` (private lemma `chat_zero_eq_integral`: the
   `p`-convention Fourier transform at `0` is the plain integral), so the value at the
   origin is the total mass `∫W₁`.
3. **The mass is strictly positive.**  If `∫W₁ = 0` then, `W₁ ≥ 0` a.e. being integrable,
   `W₁ = 0` a.e.; but on the support of `g₀` the denominator `(χ⋆χ)(·/ℓ)` is `≥ 1/2`
   (`Submission.BoseGases.chiR0_half`), so `g₀ = W₁·(χ⋆χ)(·/ℓ)` *pointwise*
   (`Submission.BoseGases.kRat_mul_convScale`); hence `g₀ = 0` a.e. and `∫g₀ = 0`,
   contradicting FS's mass identity `∫g₀ = 8π·a v > 0`
   (`Submission.BoseGases.g0_integral`, `hav`).
4. `chat W₁` is *continuous* on `ℝ³` (private lemma `continuous_chat`: the Fourier
   transform of an `L¹` function, `VectorFourier.fourierIntegral_continuous`), so the
   positive value `Ŵ₁(0) = ∫W₁` persists on a ball of radius `r₀`, with the lower bound
   `w₀ := ½·Ŵ₁(0) > 0`.

The three independent pieces are also proved as standalone modules
(`Work.BoseBogFS.chat_zero_eq_integral`, `Work.BoseBogFS.continuous_chat`,
`Work.BoseBogFS.W1fun_mass_pos`); the private copies below keep this module
self-contained.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. `chat` as the real part of Mathlib's Fourier transform -/

/-- `chat W k` is the real part of Mathlib's Fourier transform of the complexification
of `W`, evaluated at `(2π)⁻¹ • k` — i.e. `chat = pairW`. -/
private lemma chat_eq_pairW (W : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.BoseFixR.chat W = Submission.BoseGases.pairW W := by
  funext k
  rw [Work.BoseFixR.chat, Submission.BoseGases.pairW]
  exact congrArg Complex.re (Work.SmallBoxBridge.Resolve.kinFT_eq_fourier _ k)

/-- **The Fourier transform at the origin is the plain integral**:
`chat W 0 = ∫ W` for integrable `W` (`e^{−i⟨0,y⟩} = 1`, and `Re` commutes with the
Bochner integral). -/
private lemma chat_zero_eq_integral (W : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hW : MeasureTheory.Integrable W) :
    Work.BoseFixR.chat W 0 = ∫ y : EuclideanSpace ℝ (Fin 3), W y := by
  have hcf : Submission.BoseGases.cfourier W 0
      = ∫ y : EuclideanSpace ℝ (Fin 3), ((W y : ℝ) : ℂ) := by
    rw [Submission.BoseGases.cfourier, Real.fourier_eq']
    simp
  have hre : (∫ y : EuclideanSpace ℝ (Fin 3), ((W y : ℝ) : ℂ)).re = ∫ y, W y := by
    have h := Complex.reCLM.integral_comp_comm
      (φ := fun y : EuclideanSpace ℝ (Fin 3) => ((W y : ℝ) : ℂ)) hW.ofReal
    simpa using h.symm
  rw [chat_eq_pairW]
  show (Submission.BoseGases.cfourier W
      ((2 * Real.pi)⁻¹ • (0 : EuclideanSpace ℝ (Fin 3)))).re = _
  rw [smul_zero, hcf, hre]

/-- **Continuity of the Fourier transform of an `L¹` function**: `chat W` is continuous
whenever `W` is integrable (Riemann–Lebesgue in its weakest form). -/
private lemma continuous_chat (W : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hW : MeasureTheory.Integrable W) :
    Continuous (Work.BoseFixR.chat W) := by
  rw [chat_eq_pairW]
  show Continuous (fun k : EuclideanSpace ℝ (Fin 3) =>
    (Submission.BoseGases.cfourier W ((2 * Real.pi)⁻¹ • k)).re)
  exact Complex.continuous_re.comp ((Submission.BoseGases.continuous_cfourier hW).comp
    (continuous_const_smul ((2 * Real.pi)⁻¹)))

/-! ## 2. The mass of `W₁ = g₀/(χ⋆χ)_ℓ` is strictly positive -/

/-- **FS `0 < ∫W₁`** in the dilute regime: the total mass of the renormalised kernel
`W₁ = wScaled ℓ (g₀ v h)` is strictly positive.  Indeed `W₁ ≥ 0` a.e. and
`g₀ = W₁·(χ⋆χ)_ℓ` pointwise (`kRat_mul_convScale`), so `∫W₁ = 0` would force `∫g₀ = 0`,
against `∫g₀ = 8π·a v > 0`. -/
private theorem W1fun_mass_pos (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    {R ℓ : ℝ} (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (hℓ : 0 < ℓ) :
    0 < ∫ y : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ y := by
  show 0 < ∫ z : EuclideanSpace ℝ (Fin 3),
    Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) z
  have hInt : MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) z) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  have hnn : ∀ᵐ z ∂(volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
      0 ≤ Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) z :=
    Submission.BoseGases.wScaled_g0_nonneg_ae hR hv hvrad hv_supp h
  have hle : 0 ≤ ∫ z, Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) z :=
    MeasureTheory.integral_nonneg_of_ae hnn
  have hne : (∫ z, Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) z) ≠ 0 := by
    intro hzero
    -- `W₁ = 0` a.e., since it is integrable and nonnegative with vanishing integral
    have hz : (fun z => Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) z)
        =ᵐ[volume] 0 :=
      (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae hnn hInt).mp hzero
    -- the pointwise identity `g₀ = W₁·(χ⋆χ)_ℓ`, valid on the support of `g₀`
    have hsupp : ∀ x : EuclideanSpace ℝ (Fin 3),
        R ≤ ‖x‖ → Submission.BoseGases.g0 v h x = 0 :=
      fun x hx => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hx h
    have hpoint : ∀ z, Submission.BoseGases.g0 v h z =
        Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) z
          * Submission.BoseGases.convScale ℓ z := by
      intro z
      have hk := Submission.BoseGases.kRat_mul_convScale (h := Submission.BoseGases.g0 v h)
        (R := R) (r₀ := Submission.BoseGases.chiR0) hℓ hsupp hRℓ
        Submission.BoseGases.chiR0_half z
      simpa [Submission.BoseGases.kRat, Submission.BoseGases.wScaled] using hk.symm
    have hg0zero : (fun z => Submission.BoseGases.g0 v h z) =ᵐ[volume] 0 := by
      filter_upwards [hz] with z hz'
      rw [hpoint z, hz']
      simp
    have hgz : (∫ z, Submission.BoseGases.g0 v h z) = 0 := by
      rw [MeasureTheory.integral_congr_ae hg0zero]
      simp
    -- but FS's mass identity says `∫g₀ = 8π·(a v) ≠ 0`
    have hgi := Submission.BoseGases.g0_integral hR hv_supp h
    rw [hgi] at hgz
    nlinarith [Real.pi_pos, hav]
  exact lt_of_le_of_ne' hle hne

/-! ## 3. The target -/

theorem chat_W1fun_pos_near_zero (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    {R ℓ : ℝ} (hR : 0 < R) (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (hℓ : 0 < ℓ) :
    ∃ (w₀ r₀ : ℝ), 0 < w₀ ∧ 0 < r₀ ∧ ∀ k : EuclideanSpace ℝ (Fin 3), ‖k‖ ≤ r₀ →
      w₀ ≤ Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) k := by
  -- `W₁` is integrable, so `chat W₁` is continuous and `chat W₁ 0 = ∫W₁ > 0`
  have hInt : MeasureTheory.Integrable (Work.BoseFixR.W1fun v h ℓ) := by
    show MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.wScaled ℓ (Submission.BoseGases.g0 v h) z)
    exact Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  have hpos : 0 < Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) 0 := by
    rw [chat_zero_eq_integral _ hInt]
    exact W1fun_mass_pos v h hR hv hvrad hv_supp hav hRℓ hℓ
  have hcont : Continuous (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)) :=
    continuous_chat _ hInt
  -- continuity at the origin gives a whole neighbourhood where `Ŵ₁ ≥ ½Ŵ₁(0)`
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.continuousAt_iff.mp hcont.continuousAt)
    (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) 0 / 2) (by linarith)
  refine ⟨Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) 0 / 2, δ / 2,
    by linarith, by linarith, fun k hk => ?_⟩
  have hd : dist k 0 < δ := by
    rw [dist_zero_right]
    linarith
  have hdist := hδ hd
  rw [Real.dist_eq] at hdist
  have := (abs_lt.mp hdist).1
  linarith

end Work.BoseBogFS
