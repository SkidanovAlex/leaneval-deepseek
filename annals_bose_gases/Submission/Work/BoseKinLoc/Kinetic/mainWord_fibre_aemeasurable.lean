import Mathlib
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Measurability of the slot-`i` fibre of FS's main kinetic word `mainWord`

The localised kinetic word `Work.BoseKinLoc.mainWord` is the one-body quadratic form
`Q_uχ_u{(1−ε_T)[√−Δ−½(sℓ)⁻¹]₊²+ε_T[√−Δ−½(dsℓ)⁻¹]₊²}χ_uQ_u` (FS `eq:T'u`), written in the
corpus's momentum convention as a sum of two `bsOneBody` terms.  In the `N`-body localisation
one integrates the *fibre* of this form along the slot `i`,

    `(u,q₂) ↦ mainWord ℓ d s ε_T u (z ↦ Φ (kcInsN n i (z,q₂)))`,

over the translation parameter `u` and the remaining coordinates `q₂`, so that this function
must be (a.e.) strongly measurable.

## What is proved here

`bsOneBody ℓ F u ψ = (2π)⁻³∫_p F(‖p‖)·‖kinFT (χ_u·Q_uψ)‖²` is an integral over `p` of the
square of an integral over `z`, and `Q_uψ = ψ − |Λ(u)|⁻¹∫_{Λ(u)}ψ` is itself an integral over
the box `acube ℓ`.  Measurability is therefore obtained by *three* successive applications of
`StronglyMeasurable.integral_prod_right` (which needs no integrability hypothesis, only joint
strong measurability of the uncurried integrand and `SFinite` of the inner measure):

* the box mean `fibMean` of the fibre,
* the windowed Fourier transform `fibK`,
* the momentum integral `fibBC`.

The joint integrands are built from the smooth `Φ` composed with the *measurable* insertion
`kcInsN n i`, and from the continuous bump `chi`, so they are measurable outright.

Everything is stated for an arbitrary **measurable** symbol `F : ℝ → ℝ`; the application to
FS's `F = fsKinCoeff c = [·−c]₊²` supplies `measurable_fsKinCoeff`.

## Conventions

Same as `Submission.Work.BoseKinLoc.Defs` and `Submission.Work.BSKinetic.Defs`:
`ℝ³ = EuclideanSpace ℝ (Fin 3)`, `X N = Fin N → ℝ³`, `acube ℓ = [−ℓ/2,ℓ/2]³`,
`bsWin ℓ u z = χ((z−ℓu)/ℓ)`, `bsMean ℓ u ψ = ℓ⁻³∫_{acube ℓ}ψ(ℓu+z)`, `bsQ ℓ u ψ = ψ − bsMean ℓ u ψ`,
and `kinFT u p = ∫_y e^{−i⟪p,y⟫}u(y)dy`.
-/

noncomputable section

open MeasureTheory
open Submission.BoseGases
open Work.BSKinetic

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.BoseKinLoc.Kinetic

/-! ## 1. The pieces of the fibre of the one-body form

The fibre of the one-body state `ψ` at the slot `i` and the configuration `q₂` is
`z ↦ Φ (kcInsN n i (z,q₂))`.  Its box mean, its windowed Fourier transform and the resulting
momentum form are packaged below so that each measurability step is a short statement. -/

/-- The box mean `bsMean ℓ u (z ↦ Φ(kcInsN n i (z,q₂)))` of the slot-`i` fibre, as a function
of the pair `q = (u,q₂)`. -/
noncomputable def fibMean (ℓ : ℝ) {n : ℕ} (i : Fin (n + 1))
    (Φ : Submission.BoseGases.X (n + 1) → ℝ)
    (q : ℝ³ × Submission.BoseGases.X n) : ℝ :=
  bsMean ℓ q.1 (fun z : ℝ³ => Φ (kcInsN n i (z, q.2)))

/-- The `z`-integrand of the windowed Fourier transform of the mean-free slot-`i` fibre:
`e^{−i⟪p,z⟫}·χ_u(z)·(Φ(z,q₂) − m(u,q₂))`, as a function of `(u,q₂,p)` and `z`. -/
noncomputable def fibZ (ℓ : ℝ) {n : ℕ} (i : Fin (n + 1))
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) :
    ((ℝ³ × Submission.BoseGases.X n) × ℝ³) → ℝ³ → ℂ :=
  fun r z => Complex.exp (-(Complex.I * (inner ℝ r.2 z : ℂ))) *
    ((bsWin ℓ r.1.1 z : ℂ) *
      (((fun z : ℝ³ => Φ (kcInsN n i (z, r.1.2))) z - fibMean ℓ i Φ r.1 : ℝ) : ℂ))

/-- The windowed Fourier transform `kinFT (χ_u·Q_uψ) p` of the mean-free slot-`i` fibre. -/
noncomputable def fibK (ℓ : ℝ) {n : ℕ} (i : Fin (n + 1))
    (Φ : Submission.BoseGases.X (n + 1) → ℝ)
    (r : (ℝ³ × Submission.BoseGases.X n) × ℝ³) : ℂ :=
  ∫ z : ℝ³, fibZ ℓ i Φ r z

/-- The `p`-integrand of `bsOneBody`: `F(‖p‖)·‖kinFT (χ_uQ_uψ)(p)‖²` for the slot-`i` fibre. -/
noncomputable def fibP (ℓ : ℝ) {n : ℕ} (i : Fin (n + 1)) (F : ℝ → ℝ)
    (Φ : Submission.BoseGases.X (n + 1) → ℝ)
    (r : (ℝ³ × Submission.BoseGases.X n) × ℝ³) : ℝ :=
  F ‖r.2‖ * ‖fibK ℓ i Φ r‖ ^ 2

/-- The momentum form `(2π)⁻³∫_p F(‖p‖)·‖kinFT (χ_uQ_uψ)(p)‖²` of the slot-`i` fibre, i.e.
`bsOneBody ℓ F u ψ` at `ψ = z ↦ Φ(kcInsN n i (z,q₂))`. -/
noncomputable def fibBC (ℓ : ℝ) {n : ℕ} (i : Fin (n + 1)) (F : ℝ → ℝ)
    (Φ : Submission.BoseGases.X (n + 1) → ℝ)
    (q : ℝ³ × Submission.BoseGases.X n) : ℝ :=
  ∫ p : ℝ³, fibP ℓ i F Φ (q, p)

/-! ## 2. Measurability of the symbol `fsKinCoeff` -/

/-- FS's symbol `r ↦ [r−c]₊²` is continuous, hence measurable. -/
lemma measurable_fsKinCoeff (c : ℝ) : Measurable (fsKinCoeff c) := by
  unfold fsKinCoeff
  fun_prop

/-! ## 3. The three measurability steps -/

/-- The box mean of the fibre is measurable in `(u,q₂)`: the integrand
`(u,q₂,w) ↦ Φ(kcInsN n i (ℓu+w,q₂))` is jointly measurable and `acube ℓ` has finite volume. -/
lemma fibMean_measurable {n : ℕ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) (ℓ : ℝ) :
    Measurable (fibMean ℓ i Φ) := by
  have hbase : Measurable (fun r : (ℝ³ × Submission.BoseGases.X n) × ℝ³ =>
      Φ (kcInsN n i (ℓ • r.1.1 + r.2, r.1.2))) := by
    refine hΦ.continuous.measurable.comp ?_
    refine (kcInsN n i).measurable.comp ?_
    fun_prop
  have h : StronglyMeasurable (fun q : ℝ³ × Submission.BoseGases.X n =>
      ∫ w, Φ (kcInsN n i (ℓ • q.1 + w, q.2)) ∂(volume.restrict (acube ℓ))) := by
    refine StronglyMeasurable.integral_prod_right (ν := volume.restrict (acube ℓ)) ?_
    exact hbase.stronglyMeasurable
  have h2 := (h.const_mul ((ℓ ^ 3)⁻¹)).measurable
  convert h2 using 1
  ext q
  simp [fibMean, bsMean]

/-- The joint `z`-integrand `(u,q₂,p,z) ↦ e^{−i⟪p,z⟫}χ_u(z)(Φ(z,q₂)−m(u,q₂))` is measurable. -/
lemma measurable_fibZ {n : ℕ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) (ℓ : ℝ) :
    Measurable (Function.uncurry (fibZ ℓ i Φ)) := by
  have hcont : Continuous (fun rs : ((ℝ³ × Submission.BoseGases.X n) × ℝ³) × ℝ³ =>
      (ℓ⁻¹) • (rs.2 - ℓ • rs.1.1.1)) := by fun_prop
  have hchi : Measurable (fun rs : ((ℝ³ × Submission.BoseGases.X n) × ℝ³) × ℝ³ =>
      (bsWin ℓ rs.1.1.1 rs.2 : ℂ)) := by
    simp only [bsWin, chiScale]
    exact Complex.continuous_ofReal.measurable.comp
      (chi_continuous.measurable.comp hcont.measurable)
  have hphi : Measurable (fun rs : ((ℝ³ × Submission.BoseGases.X n) × ℝ³) × ℝ³ =>
      Φ (kcInsN n i (rs.2, rs.1.1.2))) := by
    refine hΦ.continuous.measurable.comp ?_
    refine (kcInsN n i).measurable.comp ?_
    fun_prop
  have hproj : Measurable (fun rs : ((ℝ³ × Submission.BoseGases.X n) × ℝ³) × ℝ³ => rs.1.1) := by
    fun_prop
  have hm : Measurable (fibMean ℓ i Φ) := fibMean_measurable hΦ i ℓ
  have hmean : Measurable (fun rs : ((ℝ³ × Submission.BoseGases.X n) × ℝ³) × ℝ³ =>
      fibMean ℓ i Φ rs.1.1) := hm.comp hproj
  have hsub : Measurable (fun rs : ((ℝ³ × Submission.BoseGases.X n) × ℝ³) × ℝ³ =>
      Φ (kcInsN n i (rs.2, rs.1.1.2)) - fibMean ℓ i Φ rs.1.1) := hphi.sub hmean
  have hexp : Measurable (fun rs : ((ℝ³ × Submission.BoseGases.X n) × ℝ³) × ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ rs.1.2 rs.2 : ℂ)))) := by fun_prop
  have hfin := hexp.mul (hchi.mul (Complex.continuous_ofReal.measurable.comp hsub))
  show Measurable (fun rs : ((ℝ³ × Submission.BoseGases.X n) × ℝ³) × ℝ³ =>
      fibZ ℓ i Φ rs.1 rs.2)
  simp only [fibZ]
  convert hfin using 1
  ext rs
  simp [Pi.mul_apply]

/-- The windowed Fourier transform `kinFT (χ_uQ_uψ)` of the slot-`i` fibre is strongly
measurable in `(u,q₂,p)`. -/
lemma fibK_stronglyMeasurable {n : ℕ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) (ℓ : ℝ) :
    StronglyMeasurable (fibK ℓ i Φ) := by
  refine StronglyMeasurable.integral_prod_right (ν := volume) ?_
  exact (measurable_fibZ hΦ i ℓ).stronglyMeasurable

/-- The `p`-integrand `F(‖p‖)‖kinFT (χ_uQ_uψ)(p)‖²` of the slot-`i` fibre is measurable in
`(u,q₂,p)` for a measurable symbol `F`. -/
lemma fibP_measurable {n : ℕ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) (ℓ : ℝ) {F : ℝ → ℝ}
    (hF : Measurable F) : Measurable (fibP ℓ i F Φ) := by
  have hK : Measurable (fibK ℓ i Φ) := (fibK_stronglyMeasurable hΦ i ℓ).measurable
  unfold fibP
  exact (hF.comp (by fun_prop)).mul (hK.norm.pow_const 2)

/-- The momentum form of the slot-`i` fibre is strongly measurable in `(u,q₂)`. -/
lemma fibBC_stronglyMeasurable {n : ℕ} {Φ : Submission.BoseGases.X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) (ℓ : ℝ) {F : ℝ → ℝ}
    (hF : Measurable F) : StronglyMeasurable (fibBC ℓ i F Φ) := by
  have hp : Measurable (fibP ℓ i F Φ) := fibP_measurable hΦ i ℓ hF
  refine StronglyMeasurable.integral_prod_right (ν := volume) ?_
  exact hp.stronglyMeasurable.comp_measurable (by fun_prop)

/-! ## 4. `bsOneBody` on the fibre, and the target theorem -/

/-- `bsOneBody ℓ F u ψ` at the slot-`i` fibre `ψ = z ↦ Φ(kcInsN n i (z,q₂))` is a.e. strongly
measurable in `(u,q₂)`. -/
lemma bsOneBody_fibre_aemeasurable {ℓ : ℝ} {F : ℝ → ℝ} (hF : Measurable F) {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    AEStronglyMeasurable
      (fun q : ℝ³ × Submission.BoseGases.X n =>
        bsOneBody ℓ F q.1 (fun z : ℝ³ => Φ (kcInsN n i (z, q.2))))
      (volume.prod volume) := by
  have h : AEStronglyMeasurable (fun q : ℝ³ × Submission.BoseGases.X n =>
      ((2 * Real.pi) ^ 3)⁻¹ * fibBC ℓ i F Φ q) (volume.prod volume) :=
    ((fibBC_stronglyMeasurable hΦ i ℓ hF).const_mul ((2 * Real.pi) ^ 3)⁻¹).aestronglyMeasurable
  simpa [bsOneBody, kinFT, bsWin, bsQ, bsMean, fibBC, fibP, fibK, fibZ, fibMean] using h

theorem mainWord_fibre_aemeasurable {ℓ d s εT : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X n =>
        Work.BoseKinLoc.mainWord ℓ d s εT q.1 (fun z : EuclideanSpace ℝ (Fin 3) =>
          Φ (Submission.BoseGases.kcInsN n i (z, q.2))))
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n))) := by
  have h : ∀ (F : ℝ → ℝ), Measurable F →
      AEStronglyMeasurable
        (fun q : ℝ³ × Submission.BoseGases.X n =>
          bsOneBody ℓ F q.1 (fun z : ℝ³ => Φ (kcInsN n i (z, q.2))))
        (volume.prod volume) :=
    fun F hF => bsOneBody_fibre_aemeasurable hF hΦ i
  have h1 := (h (fsKinCoeff ((2 * (s * ℓ))⁻¹))
    (measurable_fsKinCoeff _)).const_mul (1 - εT)
  have h2 := (h (fsKinCoeff ((2 * (d * s * ℓ))⁻¹))
    (measurable_fsKinCoeff _)).const_mul εT
  have hsum := h1.add h2
  simp only [Work.BoseKinLoc.mainWord]
  convert hsum using 1
  all_goals
    ext q
    simp [Pi.add_apply]

end Work.BoseKinLoc.Kinetic
