import Mathlib
import Submission.Work.EKLC6Core.covAlong
import Submission.Work.EKLC6Core.growth_le_atomInfo_mp

/-!
# `EKLC6Core.atomInfo_ae_eq_aux_along` — the pointwise identity of Pisa 7.34 along `ℤ·t`

`Work.EKLC6Core.atomInfo_ae_eq_aux_mp` (the `MeasurePreserving` variant of Pisa 7.34) proves, for
a leafwise system `ν = μ_x^U` of a probability `μ` preserved by the *single* diagonal map
`x ↦ aDiag t • x`, a descending plaque algebra `A` with atoms the `U`-plaques, and the full
`A`-covariance `ACovariant ν X''` of the system,

`atomInfo A U ν t x = log ν (a·x) (shape A U (a·x)) - log ν x (shape A U x) + growthFun U ν t (a·x)`.

The proof of that identity reads the covariance hypothesis at exactly *one* parameter: `-t`
(the parameter of the one-step covariance `covariant_step`, see
`Work.EKLC6Core.covAlong`'s one-step covariances).  Hence the identity holds under the much weaker
hypothesis `ACovariantAlong ν t X''` (EKL (4) restricted to the integer multiples of the single
direction `t`), which is the form produced by `Work.EKLC6Core.acovariantAlong_of_leafwise` for a
`μ` preserved only by `aDiag t ·`.  That is the content of the present file: the whole proof of
`atomInfo_ae_eq_aux_mp` goes through verbatim, with `covariant_step` replaced by its along-`ℤ·t`
version `covstep_neg_along` below.

The statement also uses the capitalised spelling `Work.EKLContract.Shape` of the shape of a plaque
algebra (`Work.EKLContract.shape`); it is the same object, recorded here as an abbreviation so
that the statement elaborates.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLContract

/-- The shape `{u ∈ U : u • x ∈ [x]_m}` of a plaque algebra, in the capitalised spelling used by
the statement of `Work.EKLC6Core.atomInfo_ae_eq_aux_along`.  By definition this is
`Work.EKLContract.shape`. -/
abbrev Shape (m : MeasurableSpace X3) (U : Subgroup SL3) (x : X3) : Set SL3 := shape m U x

end Work.EKLContract

namespace Work.EKLC6Core

open Work.EKLContract

/-- **One step of the covariance along `ℤ·t`, read at `z = -1`.**  This is `covariant_step` with
the full `A`-covariance `ACovariant ν X''` replaced by the covariance along the integer multiples
of the single direction `t` (`ACovariantAlong ν t X''`): the (single) parameter `-t = (-1) · t`
is provided by the hypothesis at the integer multiple `z = -1`.

  `ν (aDiag (-t) · y) C * ν y (conjBox U t) = ν y (conjBy t C)`. -/
theorem covstep_neg_along {μ : Measure X3} {U : Subgroup SL3} {ν : X3 → Measure SL3}
    {X' X'' : Set X3} {t : Fin 3 → ℝ} (hL : IsLeafwise μ U ν X')
    (hcov : ACovariantAlong ν t X'') (hBox1 : MeasurableSet (Box1 U))
    {y : X3} (hy : y ∈ X' ∩ X'') (hy' : aDiag (-t) • y ∈ X' ∩ X'') {C : Set SL3}
    (hC : MeasurableSet C) :
    ν (aDiag (-t) • y) C * ν y (conjBox U t) = ν y (conjBy t C) := by
  have hz : (((-1 : ℤ) : ℝ) • t : Fin 3 → ℝ) = -t := by
    funext i
    simp
  obtain ⟨c, -, -, hceq⟩ := hcov (-1) y hy.2 (by rw [hz]; exact hy'.2)
  rw [hz] at hceq
  have hmap : Measurable (fun g : SL3 => aDiag (-t) * g * (aDiag (-t))⁻¹) := measurable_conj _
  have key : ∀ {D : Set SL3}, MeasurableSet D →
      ν (aDiag (-t) • y) D = c * ν y (conjBy t D) := by
    intro D hD
    rw [hceq, Measure.smul_apply, smul_eq_mul, Measure.map_apply hmap hD, preimage_conj_neg]
  have h1 : ν (aDiag (-t) • y) (Box1 U) = c * ν y (conjBox U t) := key hBox1
  have h2 : ν (aDiag (-t) • y) (Box1 U) = 1 := hL.normalised _ hy'.1
  calc ν (aDiag (-t) • y) C * ν y (conjBox U t)
      = (c * ν y (conjBy t C)) * ν y (conjBox U t) := by rw [key hC]
    _ = (c * ν y (conjBox U t)) * ν y (conjBy t C) := by ac_rfl
    _ = ν y (conjBy t C) := by rw [← h1, h2, one_mul]

theorem atomInfo_ae_eq_aux_along {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} {t : Fin 3 → ℝ}
    (hL : Work.EKLContract.IsLeafwise μ U ν X') (hU : Work.EKLContract.IsHoro U)
    (hcov : Work.EKLC6Core.ACovariantAlong ν t X'')
    (hX'' : μ X''ᶜ = 0)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplaq : Work.EKLContract.IsPlaqueAlgebra U Z A) (hZ : μ Zᶜ = 0) :
    ∀ᵐ x ∂μ, Work.EKLC6Core.atomInfo A U ν t x =
      Real.log ((ν (Work.EKLContract.aDiag t • x)
          (Work.EKLContract.Shape A U (Work.EKLContract.aDiag t • x))).toReal) -
        Real.log ((ν x (Work.EKLContract.shape A U x)).toReal) +
        Work.EKLC6Core.growthFun U ν t (Work.EKLContract.aDiag t • x) := by
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  have hqmp : Measure.QuasiMeasurePreserving (fun x : X3 => aDiag t • x) μ μ :=
    hmp.quasiMeasurePreserving
  have hX' : ∀ᵐ x ∂μ, x ∈ X' := by rw [ae_iff]; exact hL.conull
  have hX''ae : ∀ᵐ x ∂μ, x ∈ X'' := by rw [ae_iff]; exact hX''
  have hZae : ∀ᵐ x ∂μ, x ∈ Z := by rw [ae_iff]; exact hZ
  filter_upwards [hX', hX''ae, hZae, hqmp.ae hX', hqmp.ae hX''ae, hqmp.ae hZae]
    with x hxX' hxX'' hxZ haxX' haxX'' haxZ
  set S : Set SL3 := shape A U (aDiag t • x) with hSdef
  -- measurability of the conjugated shape
  obtain ⟨O, hOopen, hOeq⟩ := (hplaq.2.2.2 (aDiag t • x) haxZ).2.2.1
  have hSmeas : MeasurableSet S := by
    rw [hSdef, hOeq]
    exact hOopen.measurableSet.inter hU.1.measurableSet
  have hCmeas : MeasurableSet (conjBy (-t) S) := by
    rw [← preimage_conj_neg (-t) S]
    exact hSmeas.preimage (measurable_conj (-(-t)))
  -- the diagonal step back
  have hcancel : aDiag (-t) • (aDiag t • x) = x := by
    rw [aDiag_smul_mul]
    have h0 : -t + t = (0 : Fin 3 → ℝ) := by funext i; simp
    rw [h0, aDiag_zero, one_smul]
  have hconj : conjBy t (conjBy (-t) S) = S := by
    rw [← conjBy_add]
    have h0 : t + (-t) = (0 : Fin 3 → ℝ) := by funext i; simp
    rw [h0, conjBy_zero]
  -- the one-step covariance, along the integer multiples of `t`
  have hstep := covstep_neg_along hL hcov (measurableSet_box1 hU)
    (y := aDiag t • x) ⟨haxX', haxX''⟩ (by rw [hcancel]; exact ⟨hxX', hxX''⟩)
    (C := conjBy (-t) S) hCmeas
  rw [hcancel, hconj] at hstep
  -- identify `conjBy (-t) S` with the shape of the pulled-back atom
  have hW : shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x = conjBy (-t) S := by
    rw [hSdef]; exact shape_comap_conj hU t x
  have hstep' : ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x) *
      ν (aDiag t • x) (conjBox U t) = ν (aDiag t • x) S := by
    rw [hW]; exact hstep
  -- positivity and finiteness
  obtain ⟨hposV, hltV⟩ := shape_mass_pos hL hplaq hxX' hxZ
  obtain ⟨hposVax, hltVax⟩ := shape_mass_pos hL hplaq haxX' haxZ
  obtain ⟨hposBox, hltBox⟩ := conjBox_mass_pos hL hU t haxX'
  have hne0 : ν (aDiag t • x) (conjBox U t) ≠ 0 := ne_of_gt hposBox
  have hnetop : ν (aDiag t • x) (conjBox U t) ≠ ⊤ := ne_of_lt hltBox
  have hWmass : ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x) =
      ν (aDiag t • x) S / ν (aDiag t • x) (conjBox U t) := by
    rw [ENNReal.eq_div_iff hne0 hnetop]
    rw [mul_comm]
    exact hstep'
  have hWne0 : ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x) ≠ 0 := by
    rw [hWmass]; exact ne_of_gt (ENNReal.div_pos (ne_of_gt hposVax) hnetop)
  have hWnetop : ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x) ≠ ⊤ := by
    rw [hWmass]; exact ENNReal.div_ne_top (ne_of_lt hltVax) hne0
  have hWtoReal :
      (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal =
      (ν (aDiag t • x) S).toReal / (ν (aDiag t • x) (conjBox U t)).toReal := by
    rw [hWmass, ENNReal.toReal_div]
  -- nonzero reals
  have hz_ne : (ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos hWne0 hWnetop)
  have hy_ne : (ν x (shape A U x)).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos (ne_of_gt hposV) (ne_of_lt hltV))
  have hv_ne : (ν (aDiag t • x) S).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos (ne_of_gt hposVax) (ne_of_lt hltVax))
  have hc_ne : (ν (aDiag t • x) (conjBox U t)).toReal ≠ 0 :=
    ne_of_gt (ENNReal.toReal_pos hne0 hnetop)
  -- logarithm bookkeeping
  have hlogz : Real.log ((ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal)
      = Real.log ((ν (aDiag t • x) S).toReal) -
        Real.log ((ν (aDiag t • x) (conjBox U t)).toReal) := by
    rw [hWtoReal]; exact Real.log_div hv_ne hc_ne
  have hlogmain : Real.log (((ν x (shape A U x)).toReal) /
      ((ν x (shape (MeasurableSpace.comap (fun y : X3 => aDiag t • y) A) U x)).toReal)) =
      Real.log ((ν x (shape A U x)).toReal) - Real.log ((ν (aDiag t • x) S).toReal) +
        Real.log ((ν (aDiag t • x) (conjBox U t)).toReal) := by
    rw [Real.log_div hy_ne hz_ne, hlogz]
    ring
  rw [atomInfo, hlogmain]
  simp only [growthFun, Shape]
  ring

end Work.EKLC6Core

end
