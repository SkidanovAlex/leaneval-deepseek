import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.pairRung.framePerXBound
import Submission.Work.BoseFixB1S.win.chiSmallB_kinFT_decay
import Submission.Work.BoseFixB1S.win.slotContentIntegrableC2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.winModeContentC2`

The `F`-weighted windowed-mode content of an arbitrary state is paid by the `p`-diagonal kinetic
word `Work.UBBInputs8.tBdiagFormInd` with the slot count as constant, at the **weakest regularity
the applications need**: `χ ∈ C²` (not `C^∞`) together with the *support* hypothesis `χ = 0` off
the box `Ac`:

    `(2π)⁻³∫_q fsKinCoeff c₀ ‖q‖ · boxWinModePGen a volA Ac χ Ψ q
        ≤ n · tBdiagFormInd a Ac volA χ (fsKinCoeff c₀) Ψ`.

## Why the case is different from the proved `C^∞` version, and where the content sits

`Work.BoseFixB1B.pairRung.winModeContentLeWord` proves the same inequality for `χ ∈ C^∞`; its only
`C^∞`-dependent ingredient is the *integrability* of the `p`-integrand of `tBdiagFormInd`,
obtained there from the `(1+‖p‖)⁻³` decay of `tBamp` (`tBamp_decay`, which needs three derivatives
of `χ`).  With only `χ ∈ C²` the sharp pointwise decay is `(1+‖p‖)⁻²`, which is *not* enough: the
product `fsKinCoeff c₀ ‖p‖ · ‖tBamp‖²` is then only of size `‖p‖⁻²`, non-integrable in `ℝ³`, so
the Bochner integrals of `tBdiagFormInd` collapse to the junk value `0` while the left-hand side
may stay honest and positive (this is exactly the failure mode recorded in
`Submission/Work/BoseFixB1/FINDING_boxWinModePGen_le_tBdiagFormInd_FALSE.md`).

The support hypothesis `hχsupp` is what repairs it: it makes the windowed fibre
`z ↦ χ z · (Q_{Ac,i}Ψ)(x_{i↦z})` equal to `χ z · (Ψ(x_{i↦z}) − mean)` (`chi_mul_boxQInd_update`,
`winFib_eq_ofReal_winFibR` below), i.e. a `C²` compactly supported *function of `z`*, so it lies in
`H¹` and the weighted Plancherel identity of `Work.BoseFixB1S.kinFTMomC1` in the `p`-convention,

    `(2π)⁻³ ∫_p ‖p‖² ‖kinFT φ p‖² = ∑_k ∫_z ‖∂_k φ(z)‖²`,

is available at `C¹` regularity of the fibre.  Since `fsKinCoeff c₀ ‖p‖ ≤ ‖p‖²` this makes the
`p`-integrand of `tBdiagFormInd` *finite* (uniformly in the configuration of the other slots) —
which is precisely the hypothesis under which the `q`-integration step goes through.

**Division of labour.**  The analytic finiteness is the proved theorem
`Work.BoseFixB1S.win.slotContentIntegrableC2` (sibling module
`Submission/Work/BoseFixB1S/win/slotContentIntegrableC2.lean`).  This file contributes the
`q`-integration step `winModeContentC2_of_integrable`, which is smoothness-free: given the sharp
pointwise slot Cauchy–Schwarz of `Work.BoseFixB1B.pairRung.boxWinModePGen_le_slotSum_clean` and
integrability of the `p`-integrand, monotonicity of the integral gives the weighted `q`-integral
inequality with the slot count as constant.  (The statement of this file is the same as that of
`Work.BoseFixB1S.winModeContentLeWordC2`, whose prover assembled it along the parallel route.)
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 0. The windowed fibres of the box mean-free projection -/

/-- **The windowed fibre of FS's box mean-free projection**, complexified:
`z ↦ χ z · (Q_{Ac,i}Ψ)(x_{i↦z})`.  Its `p`-convention Fourier transform is the amplitude
`tBamp χ p (Q_{Ac,i}Ψ) i x` (`Work.BoseFixB1.SectorAux.tBamp_boxQInd_eq_kinFT_boxQ`). -/
noncomputable def winFib (volA : ℝ) (Ac : Set E3) (χ : E3 → ℝ) {n : ℕ}
    (Ψ : Submission.BoseGases.X n → ℝ) (i : Fin n) (x : Submission.BoseGases.X n) : E3 → ℂ :=
  fun z => (χ z : ℂ) * ((Work.UBBInputs8.boxQInd volA Ac i Ψ (Function.update x i z) : ℝ) : ℂ)

/-- **The plain windowed fibre** `z ↦ χ z · (Ψ(x_{i↦z}) − mean)`.  Under the support hypothesis
`χ = 0` off `Ac` it is the same function of `z` as `winFib` (`winFib_eq_ofReal_winFibR`), and it
is `C²` — unlike `winFib`, whose definition contains the box indicator. -/
noncomputable def winFibR (volA : ℝ) (Ac : Set E3) (χ : E3 → ℝ) {n : ℕ}
    (Ψ : Submission.BoseGases.X n → ℝ) (i : Fin n) (x : Submission.BoseGases.X n) : E3 → ℝ :=
  fun z => χ z * (Ψ (Function.update x i z)
    - (1 / volA) * ∫ w in Ac, Ψ (Function.update x i w))

/-! ## 1. The fibre dictionary -/

/-- **The box indicator of `Q_{Ac,i}` is invisible under a window supported in `Ac`.** -/
lemma chi_mul_boxQInd_update {n : ℕ} {volA : ℝ} {Ac : Set E3} {χ : E3 → ℝ}
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0) {Ψ : Submission.BoseGases.X n → ℝ} (i : Fin n)
    (x : Submission.BoseGases.X n) (z : E3) :
    χ z * Work.UBBInputs8.boxQInd volA Ac i Ψ (Function.update x i z) =
      winFibR volA Ac χ Ψ i x z := by
  have hint : (∫ w in Ac, Ψ (Function.update (Function.update x i z) i w))
      = ∫ w in Ac, Ψ (Function.update x i w) := by
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp
  show χ z * (Ac.indicator (fun _ => (1 : ℝ)) ((Function.update x i z) i)
        * Ψ (Function.update x i z)
      - (1 / volA) * (∫ w in Ac, Ψ (Function.update (Function.update x i z) i w))
        * Ac.indicator (fun _ => (1 : ℝ)) ((Function.update x i z) i))
      = χ z * (Ψ (Function.update x i z)
        - (1 / volA) * ∫ w in Ac, Ψ (Function.update x i w))
  rw [hint, Function.update_self]
  by_cases hz : z ∈ Ac
  · rw [Set.indicator_of_mem hz]
    ring
  · rw [Set.indicator_of_notMem hz, hχsupp z hz]
    ring

/-- The complex windowed fibre is the complexification of the plain one. -/
lemma winFib_eq_ofReal_winFibR {n : ℕ} {volA : ℝ} {Ac : Set E3} {χ : E3 → ℝ}
    (hχsupp : ∀ z, z ∉ Ac → χ z = 0) {Ψ : Submission.BoseGases.X n → ℝ} (i : Fin n)
    (x : Submission.BoseGases.X n) :
    winFib volA Ac χ Ψ i x = fun z => ((winFibR volA Ac χ Ψ i x z : ℝ) : ℂ) := by
  funext z
  show (χ z : ℂ) * ((Work.UBBInputs8.boxQInd volA Ac i Ψ (Function.update x i z) : ℝ) : ℂ)
      = ((winFibR volA Ac χ Ψ i x z : ℝ) : ℂ)
  rw [← Complex.ofReal_mul, chi_mul_boxQInd_update hχsupp i x z]

/-! ## 2. The `q`-integration step -/

/-- **The `q`-integration step** (the `C²`/support analogue of
`winModeContentLeWord_of_pointwise`).  If the sharp pointwise slot bound holds at every `q` and
each `p`-integrand of `tBdiagFormInd` is integrable, the weighted `q`-integral inequality follows
with the slot count as constant.  No smoothness of `χ` is used. -/
theorem winModeContentC2_of_integrable {n : ℕ} {a volA : ℝ} (ha : 0 < a)
    {Ac : Set E3} (hAcm : MeasurableSet Ac) (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (volume Ac).toReal) (hvolpos : 0 < volA)
    {χ : E3 → ℝ} (hχc : Continuous χ)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨc : Continuous Ψ)
    (hpoint : ∀ q : E3, Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q
      ≤ (n : ℝ) * ∑ i : Fin n, (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ q (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
    (hint : ∀ i : Fin n, Integrable (fun p : E3 =>
      Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * ((a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2))) :
    ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3,
        Submission.BoseGases.fsKinCoeff c₀ ‖q‖ * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q)
      ≤ (n : ℝ) * Work.UBBInputs8.tBdiagFormInd a Ac volA χ
          (Submission.BoseGases.fsKinCoeff c₀) Ψ := by
  classical
  set P : E3 → ℝ := fun q => Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q with hP
  have htwoπ : (0 : ℝ) < (2 * Real.pi) ^ 3 := by positivity
  have hFnn : ∀ q : E3, 0 ≤ Submission.BoseGases.fsKinCoeff c₀ ‖q‖ :=
    fun q => Submission.BoseGases.fsKinCoeff_nonneg c₀ ‖q‖
  have hFcont : Continuous (fun q : E3 => Submission.BoseGases.fsKinCoeff c₀ ‖q‖) := by
    simp only [Submission.BoseGases.fsKinCoeff]
    fun_prop
  have hPnn : ∀ q : E3, 0 ≤ P q := by
    intro q
    rw [hP]
    simp only [Work.BoseFixB1.boxWinModePGen, Work.BoseFixB1.boxModePGen]
    exact add_nonneg (integral_nonneg fun x => sq_nonneg _)
      (integral_nonneg fun x => sq_nonneg _)
  have hPmeas : AEStronglyMeasurable P (volume : Measure E3) := by
    rw [hP]
    exact Work.BoseFixB1B.pairRung.aeStronglyMeasurable_boxWinModePGen hAcm hχc hΨc
  have hpt : ∀ p : E3, P p ≤ (n : ℝ) * ∑ i : Fin n, (a ^ 3)⁻¹ *
      ∫ x in Submission.BoseGases.abox n a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2 := by
    intro p
    rw [hP]
    exact hpoint p
  have hIntRight : Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c₀ ‖p‖ *
      ((n : ℝ) * ∑ i : Fin n, (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
        ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)) := by
    have hIntSum : Integrable (fun p : E3 => ∑ i : Fin n,
        Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * ((a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)) :=
      integrable_finsetSum _ (fun i _ => hint i)
    have hIntT : Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c₀ ‖p‖ *
        ∑ i : Fin n, (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2) :=
      hIntSum.congr (Eventually.of_forall fun p =>
        (Finset.mul_sum Finset.univ
          (fun i : Fin n => (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
          (Submission.BoseGases.fsKinCoeff c₀ ‖p‖)).symm)
    refine (hIntT.const_mul (n : ℝ)).congr (Eventually.of_forall fun p => ?_)
    ring
  have hIntLeft : Integrable (fun p : E3 => Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * P p) :=
    Integrable.mono' hIntRight (hFcont.aestronglyMeasurable.mul hPmeas)
      (Eventually.of_forall fun p => by
        rw [Real.norm_of_nonneg (mul_nonneg (hFnn p) (hPnn p))]
        exact mul_le_mul_of_nonneg_left (hpt p) (hFnn p))
  have hmono : (∫ p : E3, Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * P p)
      ≤ ∫ p : E3, Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * ((n : ℝ) * ∑ i : Fin n, (a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2) :=
    integral_mono hIntLeft hIntRight
      (fun p => mul_le_mul_of_nonneg_left (hpt p) (hFnn p))
  have hright : (∫ p : E3, Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * ((n : ℝ) * ∑ i : Fin n,
        (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2))
      = (n : ℝ) * ((2 * Real.pi) ^ 3) * Work.UBBInputs8.tBdiagFormInd a Ac volA χ
          (Submission.BoseGases.fsKinCoeff c₀) Ψ := by
    have e1 : (fun p : E3 => Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * ((n : ℝ) * ∑ i : Fin n,
          (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2))
        = fun p : E3 => (n : ℝ) * (Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * ∑ i : Fin n,
          (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2) := by
      funext p
      ring
    rw [e1, MeasureTheory.integral_const_mul]
    have e2 : (fun p : E3 => Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * ∑ i : Fin n,
          (a ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2)
        = fun p : E3 => ∑ i : Fin n, Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * ((a ^ 3)⁻¹ *
          ∫ x in Submission.BoseGases.abox n a,
            ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2) := by
      funext p
      rw [Finset.mul_sum]
    rw [e2, MeasureTheory.integral_finsetSum _ (fun i _ => hint i)]
    rw [Work.UBBInputs8.tBdiagFormInd]
    set X : Fin n → ℝ := fun i => ∫ p : E3, Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * ((a ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n a,
          ‖Work.SmallBoxTBWord.tBamp χ p (Work.UBBInputs8.boxQInd volA Ac i Ψ) i x‖ ^ 2) with hX
    rw [Finset.mul_sum (s := Finset.univ) (f := X) (a := (n : ℝ))]
    rw [Finset.mul_sum (s := Finset.univ)
      (f := fun i : Fin n => ((2 * Real.pi) ^ 3)⁻¹ * X i)
      (a := (n : ℝ) * (2 * Real.pi) ^ 3)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    field_simp
  have hmain : (∫ p : E3, Submission.BoseGases.fsKinCoeff c₀ ‖p‖ * P p)
      ≤ (n : ℝ) * ((2 * Real.pi) ^ 3) * Work.UBBInputs8.tBdiagFormInd a Ac volA χ
          (Submission.BoseGases.fsKinCoeff c₀) Ψ := hmono.trans (le_of_eq hright)
  have hgoal : ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, Submission.BoseGases.fsKinCoeff c₀ ‖q‖ *
        Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q)
      = ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, Submission.BoseGases.fsKinCoeff c₀ ‖q‖ * P q) := by
    rw [hP]
  rw [hgoal]
  calc ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : E3, Submission.BoseGases.fsKinCoeff c₀ ‖q‖ * P q)
      ≤ ((2 * Real.pi) ^ 3)⁻¹ * ((n : ℝ) * ((2 * Real.pi) ^ 3) *
          Work.UBBInputs8.tBdiagFormInd a Ac volA χ (Submission.BoseGases.fsKinCoeff c₀) Ψ) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = (n : ℝ) * Work.UBBInputs8.tBdiagFormInd a Ac volA χ
          (Submission.BoseGases.fsKinCoeff c₀) Ψ := by
        field_simp

/-! ## 3. The theorem -/

theorem winModeContentC2 {n : ℕ} {a volA : ℝ} (ha : 0 < a) (hvolpos : 0 < volA)
    {Ac : Set (EuclideanSpace ℝ (Fin 3))} (hAcm : MeasurableSet Ac)
    (hAcsub : Ac ⊆ Submission.BoseGases.acube a)
    (hvol : volA = (MeasureTheory.volume Ac).toReal)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχc : ContDiff ℝ 2 χ)
    (hχs : HasCompactSupport χ) (hχsupp : ∀ z, z ∉ Ac → χ z = 0) (hχnn : ∀ z, 0 ≤ χ z)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    ((2 * Real.pi) ^ 3)⁻¹ * (∫ q : EuclideanSpace ℝ (Fin 3),
        Submission.BoseGases.fsKinCoeff c₀ ‖q‖ * Work.BoseFixB1.boxWinModePGen a volA Ac χ Ψ q)
      ≤ (n : ℝ) * Work.UBBInputs8.tBdiagFormInd a Ac volA χ
          (Submission.BoseGases.fsKinCoeff c₀) Ψ := by
  classical
  obtain ⟨Cχ, hCχ⟩ := (Submission.BoseGases.acube_compact ha).exists_bound_of_continuousOn
    hχc.continuous.continuousOn
  set κ : ℝ := max Cχ 0 with hκdef
  have hκ0 : 0 ≤ κ := le_max_right _ _
  have hκ : ∀ z : EuclideanSpace ℝ (Fin 3), χ z ≤ κ := by
    intro z
    by_cases hz : z ∈ Submission.BoseGases.acube a
    · exact le_trans (le_trans (le_abs_self (χ z)) (hCχ z hz)) (le_max_left _ _)
    · rw [hχsupp z (fun h => hz (hAcsub h))]
      exact hκ0
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ := Work.BoseFixB1.exists_bound_abox_pos (ℓ := a) ha hΨc.continuous
  refine winModeContentC2_of_integrable ha hAcm hAcsub hvol hvolpos hχc.continuous hc₀
    hΨc.continuous ?_ ?_
  · intro q
    exact Work.BoseFixB1B.pairRung.boxWinModePGen_le_slotSum_clean ha hvolpos hκ0 hAcm hAcsub
      hvol hχc.continuous hχs hχnn hκ hΨc.continuous hCΨ hCΨ0 q
  · intro i
    exact Work.BoseFixB1S.win.slotContentIntegrableC2 ha hAcm hAcsub hvol hvolpos hχc hχs hχsupp
      hχnn hc₀ hΨc i

end Work.BoseFixB1S
