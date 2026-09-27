import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLC6Core.growth_le_HcondSig
import Submission.Work.EKLC6Core.conjBox_nhds
import Submission.Work.EKLC6Core.conjBox_measurable
import Submission.Work.EKLC6Core.measurable_growthFun
import Submission.Work.EKLComp.atom_comap
import Submission.Work.EKLProd.sl3EntryBox_compact
import Submission.Work.EKLC6Core.shape_comap_conj
import Submission.Work.EKLC6Core.shape_mass_pos
import Submission.Work.EKLC6Core.conjBox_mass_pos
import Submission.Work.EKLContract.All

/-!
# `EKLC6Core.growth_le_atomInfo` — the entropy contribution is bounded by the atom information

The pointwise form of Pisa 7.34: for a.e. `x`, the Shannon information of the `A`-atom `[x]_A`
under the conditional measure of `comap (aDiag t ·) A` telescopes along the `aDiag t`-orbit into
a coboundary plus the entropy summand `growthFun`:

`atomInfo A U ν t x = ψ (a·x) - ψ x + growthFun U ν t (a·x)`,  `ψ x = log (ν x (shape A U x))`.

Since `aDiag t` preserves `μ`, the coboundary integrates to `0`, so `∫ atomInfo = ∫ growthFun`,
and the Bochner/lintegral comparison `ofReal (∫ f) ≤ ∫⁻ ofReal f` gives the stated inequality.

This file depends on three auxiliary lemmas (delegated):
* `Work.EKLC6Core.shape_comap_conj` — `shape (comap (aDiag t ·) A) U x = conjBy (-t) (shape A U (a·x))`;
* `Work.EKLC6Core.shape_mass_pos` — a plaque-algebra shape has positive finite `ν x`-mass;
* `Work.EKLC6Core.conjBox_mass_pos` — `conjBox U t` has positive finite `ν x`-mass.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

-- (The three auxiliary lemmas are proved in the sibling modules
-- `EKLC6Core.shape_comap_conj`, `EKLC6Core.shape_mass_pos` and `EKLC6Core.conjBox_mass_pos`,
-- imported above.)

/-! ## A general Bochner/lintegral comparison -/

/-- For an integrable real-valued function, `ofReal` of its Bochner integral is bounded by the
Lebesgue integral of its `ofReal`. -/
theorem ofReal_integral_le_lintegral_ofReal {μ : Measure X3} {f : X3 → ℝ}
    (hf : Integrable f μ) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
  have hpos : Integrable (fun x => max (f x) 0) μ := hf.pos_part
  have hle : ∫ x, f x ∂μ ≤ ∫ x, max (f x) 0 ∂μ :=
    integral_mono hf hpos (fun x => le_max_left (f x) 0)
  have hnn : 0 ≤ᵐ[μ] fun x => max (f x) 0 := ae_of_all _ (fun x => le_max_right (f x) 0)
  have heq : ∫ x, max (f x) 0 ∂μ = (∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae hnn hpos.aestronglyMeasurable
  have hcongr : ∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂μ = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
    refine lintegral_congr (fun x => ?_)
    rw [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (by positivity)]
  calc ENNReal.ofReal (∫ x, f x ∂μ)
      ≤ ENNReal.ofReal (∫ x, max (f x) 0 ∂μ) := ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal ((∫⁻ x, ENNReal.ofReal (f x) ∂μ).toReal) := by rw [heq, hcongr]
    _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := ENNReal.ofReal_toReal_le

/-! ## The pointwise identity (Pisa 7.34) -/

theorem atomInfo_ae_eq_aux {μ : Measure X3} [IsProbabilityMeasure μ] {U : Subgroup SL3}
    {ν : X3 → Measure SL3} {X' X'' : Set X3} {t : Fin 3 → ℝ}
    (hL : IsLeafwise μ U ν X') (hU : IsHoro U) (hcov : ACovariant ν X'')
    (hX'' : μ X''ᶜ = 0) (hAinv : IsAInvariant μ)
    {A : MeasurableSpace X3} {Z : Set X3} (hplaq : IsPlaqueAlgebra U Z A) (hZ : μ Zᶜ = 0) :
    ∀ᵐ x ∂μ, atomInfo A U ν t x =
      Real.log ((ν (aDiag t • x) (shape A U (aDiag t • x))).toReal) -
        Real.log ((ν x (shape A U x)).toReal) +
        growthFun U ν t (aDiag t • x) := by
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  have hmp := hAinv t
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

/-! ## The main theorem -/

theorem growth_le_atomInfo {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {U : Subgroup Work.EKLContract.SL3}
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (hL : Work.EKLContract.IsLeafwise μ U ν X')
    (hU : Work.EKLContract.IsHoro U) (hcov : Work.EKLC6Core.ACovariant ν X'')
    (hX'' : μ (X''ᶜ) = 0) (t : Fin 3 → ℝ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1))
    (hAinv : Work.EKLContract.IsAInvariant μ)
    (hmeas : Measurable (Work.EKLC6Core.growthFun U ν t))
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun U ν t) μ)
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplaq : Work.EKLContract.IsPlaqueAlgebra U Z A)
    (hdec : MeasurableSpace.comap (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A)
    (hZ : μ (Zᶜ) = 0)
    (hψ : MeasureTheory.Integrable
      (fun x : Work.EKLContract.X3 => Real.log
        ((ν x (Work.EKLContract.shape A U x)).toReal)) μ) :
    ENNReal.ofReal (∫ x, Work.EKLC6Core.growthFun U ν t x ∂μ) ≤
      ∫⁻ x, ENNReal.ofReal (Work.EKLC6Core.atomInfo A U ν t x) ∂μ := by
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  let ψ : X3 → ℝ := fun y => Real.log ((ν y (shape A U y)).toReal)
  have hψint : Integrable ψ μ := hψ
  have hmp := hAinv t
  have hψa : Integrable (fun x => ψ (aDiag t • x)) μ :=
    (hmp.integrable_comp hψint.aestronglyMeasurable).mpr hψint
  have hga : Integrable (fun x => growthFun U ν t (aDiag t • x)) μ :=
    (hmp.integrable_comp hint.aestronglyMeasurable).mpr hint
  have hFint : Integrable (fun x => ψ (aDiag t • x) - ψ x + growthFun U ν t (aDiag t • x)) μ :=
    (hψa.sub hψint).add hga
  have hae := atomInfo_ae_eq_aux (t := t) hL hU hcov hX'' hAinv hplaq hZ
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
