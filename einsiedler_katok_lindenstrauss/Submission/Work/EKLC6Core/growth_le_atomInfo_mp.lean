import Mathlib
import Submission.Work.EKLC6Core.growth_le_atomInfo

/-!
# `EKLC6Core.growth_le_atomInfo_mp` — the `MeasurePreserving` variant

`Work.EKLC6Core.growth_le_atomInfo` proves

`ofReal (∫ growthFun) ≤ ∫⁻ ofReal (atomInfo)`

under the hypothesis `IsAInvariant μ`, i.e. under `MeasurePreserving (aDiag t ·) μ μ` *for every*
`t`.  In the applications (Pisa §7) `μ` is only known to be preserved by the *single* diagonal
element at hand, so the present file records the same conclusion with `MeasurePreserving` assumed
for the single parameter `t` occurring in the statement.

Nothing new is needed: the proof of `growth_le_atomInfo` uses `IsAInvariant μ` only through the
single instance `hAinv t`, so both the pointwise identity `atomInfo_ae_eq_aux` and the main
assembly go through verbatim with `hmp` supplied as a hypothesis.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## The pointwise identity with `MeasurePreserving` for the single parameter -/

/-- `atomInfo_ae_eq_aux` with the hypothesis `IsAInvariant μ` weakened to
`MeasurePreserving (fun x => aDiag t • x) μ μ` for the single `t` at hand. -/
theorem atomInfo_ae_eq_aux_mp {μ : Measure X3} [IsProbabilityMeasure μ] {U : Subgroup SL3}
    {ν : X3 → Measure SL3} {X' X'' : Set X3} {t : Fin 3 → ℝ}
    (hL : IsLeafwise μ U ν X') (hU : IsHoro U) (hcov : ACovariant ν X'')
    (hX'' : μ X''ᶜ = 0)
    (hmp : MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {A : MeasurableSpace X3} {Z : Set X3} (hplaq : IsPlaqueAlgebra U Z A) (hZ : μ Zᶜ = 0) :
    ∀ᵐ x ∂μ, atomInfo A U ν t x =
      Real.log ((ν (aDiag t • x) (shape A U (aDiag t • x))).toReal) -
        Real.log ((ν x (shape A U x)).toReal) +
        growthFun U ν t (aDiag t • x) := by
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
  -- the one-step covariance
  have hstep := covariant_step hL hcov (measurableSet_box1 hU) t
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
  simp only [growthFun]
  ring

/-! ## The main theorem with `MeasurePreserving` for the single parameter -/

theorem growth_le_atomInfo_mp {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hU : Work.EKLContract.IsHoro U) (hcov : Work.EKLC6Core.ACovariant ν X'')
    (hX'' : μ (X''ᶜ) = 0) (t : Fin 3 → ℝ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1))
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hmeas : Measurable (Work.EKLC6Core.growthFun U ν t))
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun U ν t) μ)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplaq : Work.EKLContract.IsPlaqueAlgebra U Z A)
    (hdec : MeasurableSpace.comap
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A)
    (hZ : μ (Zᶜ) = 0)
    (hψ : MeasureTheory.Integrable (fun x : Work.EKLContract.X3 => Real.log
      ((ν x (Work.EKLContract.shape A U x)).toReal)) μ) :
    ENNReal.ofReal (∫ x, Work.EKLC6Core.growthFun U ν t x ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (Work.EKLC6Core.atomInfo A U ν t x) ∂μ := by
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  let ψ : X3 → ℝ := fun y => Real.log ((ν y (shape A U y)).toReal)
  have hψint : Integrable ψ μ := hψ
  have hψa : Integrable (fun x => ψ (aDiag t • x)) μ :=
    (hmp.integrable_comp hψint.aestronglyMeasurable).mpr hψint
  have hga : Integrable (fun x => growthFun U ν t (aDiag t • x)) μ :=
    (hmp.integrable_comp hint.aestronglyMeasurable).mpr hint
  have hFint : Integrable (fun x => ψ (aDiag t • x) - ψ x + growthFun U ν t (aDiag t • x)) μ :=
    (hψa.sub hψint).add hga
  have hae := atomInfo_ae_eq_aux_mp (t := t) hL hU hcov hX'' hmp hplaq hZ
  have hae' : atomInfo A U ν t =ᵐ[μ]
      (fun x => ψ (aDiag t • x) - ψ x + growthFun U ν t (aDiag t • x)) := by
    filter_upwards [hae] with x hx
    rw [hx]
  have hatomInfo_int : Integrable (atomInfo A U ν t) μ := hFint.congr hae'.symm
  have hψa_int : ∫ x, ψ (aDiag t • x) ∂μ = ∫ y, ψ y ∂μ := by
    have hmap : μ.map (fun x : X3 => aDiag t • x) = μ := hmp.map_eq
    have hAESM : AEStronglyMeasurable ψ (Measure.map (fun x : X3 => aDiag t • x) μ) := by
      rw [hmap]; exact hψint.aestronglyMeasurable
    calc ∫ x, ψ (aDiag t • x) ∂μ
        = ∫ y, ψ y ∂(μ.map (fun x : X3 => aDiag t • x)) :=
          (integral_map hmp.aemeasurable hAESM).symm
      _ = ∫ y, ψ y ∂μ := by rw [hmap]
  have hga_int : ∫ x, growthFun U ν t (aDiag t • x) ∂μ = ∫ y, growthFun U ν t y ∂μ := by
    have hmap : μ.map (fun x : X3 => aDiag t • x) = μ := hmp.map_eq
    have hAESM : AEStronglyMeasurable (growthFun U ν t) (Measure.map (fun x : X3 => aDiag t • x) μ) := by
      rw [hmap]; exact hint.aestronglyMeasurable
    calc ∫ x, growthFun U ν t (aDiag t • x) ∂μ
        = ∫ y, growthFun U ν t y ∂(μ.map (fun x : X3 => aDiag t • x)) :=
          (integral_map hmp.aemeasurable hAESM).symm
      _ = ∫ y, growthFun U ν t y ∂μ := by rw [hmap]
  have hsplit : ∫ x, ψ (aDiag t • x) - ψ x + growthFun U ν t (aDiag t • x) ∂μ
      = (∫ x, ψ (aDiag t • x) ∂μ - ∫ x, ψ x ∂μ) + ∫ x, growthFun U ν t (aDiag t • x) ∂μ := by
    rw [integral_add (f := fun x => ψ (aDiag t • x) - ψ x)
          (g := fun x => growthFun U ν t (aDiag t • x)) (hψa.sub hψint) hga]
    rw [integral_sub (f := fun x => ψ (aDiag t • x)) (g := ψ) hψa hψint]
  have hIntEq : ∫ x, atomInfo A U ν t x ∂μ = ∫ x, growthFun U ν t x ∂μ := by
    calc ∫ x, atomInfo A U ν t x ∂μ
        = ∫ x, ψ (aDiag t • x) - ψ x + growthFun U ν t (aDiag t • x) ∂μ :=
          integral_congr_ae hae'
      _ = (∫ x, ψ (aDiag t • x) ∂μ - ∫ x, ψ x ∂μ) + ∫ x, growthFun U ν t (aDiag t • x) ∂μ :=
          hsplit
      _ = ∫ x, growthFun U ν t x ∂μ := by rw [hψa_int, hga_int]; ring
  rw [← hIntEq]
  exact ofReal_integral_le_lintegral_ofReal hatomInfo_int

end Work.EKLC6Core

end
