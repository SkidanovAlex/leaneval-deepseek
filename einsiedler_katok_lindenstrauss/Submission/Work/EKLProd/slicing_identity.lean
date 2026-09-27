import Mathlib
import Submission.Work.EKLComp.PlaqueToolkit
import Submission.Work.EKLProd.null_transfer

namespace Work.EKLProd

open MeasureTheory

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

noncomputable section

theorem slicing_identity {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ] {H T : Subgroup Work.EKLContract.SL3} {νH : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XH : Set Work.EKLContract.X3} (hνH : Work.EKLContract.IsLeafwise μ H νH XH) {νT : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3} {XT : Set Work.EKLContract.X3} (hνT : Work.EKLContract.IsLeafwise μ T νT XT) {x₀ : Work.EKLContract.X3} {ε : ℝ} (hε : 0 < ε) (hHc : IsClosed (H : Set Work.EKLContract.SL3)) (hinj : ∀ h₁ ∈ H, ∀ h₂ ∈ H, h₁ • x₀ = h₂ • x₀ → h₁ = h₂) (hP : μ (Work.EKLComp.orbitPlaque H x₀ ε) ≠ 0) (f : Work.EKLContract.X3 → ℝ) (hf : Measurable f) (hfb : ∃ C, ∀ y, |f y| ≤ C) {mT : MeasurableSpace Work.EKLContract.X3} (hplaT : Work.EKLContract.IsPlaqueAlgebra T (Work.EKLComp.orbitPlaque H x₀ ε) mT) (halign : MeasurableSpace.generateFrom {Work.EKLComp.orbitPlaque H x₀ ε} ≤ mT) :
    ∀ᵐ x ∂(μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)), MeasureTheory.integral (MeasureTheory.Measure.restrict (νH x) (Work.EKLContract.shape (Work.EKLComp.plaqueSigma H x₀ ε) H x)) (fun h => f (h • x)) / (νH x (Work.EKLContract.shape (Work.EKLComp.plaqueSigma H x₀ ε) H x)).toReal = MeasureTheory.integral (MeasureTheory.Measure.restrict (νH x) (Work.EKLContract.shape (Work.EKLComp.plaqueSigma H x₀ ε) H x)) (fun h => MeasureTheory.integral (MeasureTheory.Measure.restrict (νT (h • x)) (Work.EKLContract.shape mT T (h • x))) (fun t => f (t • (h • x))) / (νT (h • x) (Work.EKLContract.shape mT T (h • x))).toReal) / (νH x (Work.EKLContract.shape (Work.EKLComp.plaqueSigma H x₀ ε) H x)).toReal := by
  -- Keeps the ambient σ-algebra of `X₃` available for instance search, so that the
  -- hypothesis `{mT : MeasurableSpace X₃}` (which is a local hypothesis of a class type
  -- and therefore participates in instance search) does not silently capture occurrences of
  -- `Measurable`/`MeasurableSet`.  See `EKLComp/ProductPlan.md` §5.
  letI : MeasurableSpace Work.EKLContract.X3 := Work.EKLContract.instMeasurableSpaceX3
  classical
  -- Abbreviations (defined with `let`, hence definitionally transparent).
  let F : Work.EKLContract.X3 → ℝ :=
    MeasureTheory.condExp mT (μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)) f
  let Tavg : Work.EKLContract.X3 → ℝ := fun y =>
    MeasureTheory.integral (MeasureTheory.Measure.restrict (νT y) (Work.EKLContract.shape mT T y))
        (fun t => f (t • y))
      / (νT y (Work.EKLContract.shape mT T y)).toReal
  -- The bound on `f`.
  have hfb_copy : ∃ C, ∀ y, |f y| ≤ C := hfb
  obtain ⟨C, hC⟩ := hfb_copy
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC (Work.EKLContract.mkX 1))
  let g : Work.EKLContract.X3 → ℝ := fun y => max (-C) (min (F y) C)
  let Nbad : Set Work.EKLContract.X3 := {y | g y ≠ Tavg y}
  -- The plaque algebra of the `H`-plaque.
  have hplaH : Work.EKLContract.IsPlaqueAlgebra H (Work.EKLComp.orbitPlaque H x₀ ε)
      (Work.EKLComp.plaqueSigma H x₀ ε) :=
    Work.EKLComp.isPlaqueAlgebra_orbitPlaque hHc hε hinj
  have hZ : MeasurableSet (Work.EKLComp.orbitPlaque H x₀ ε) := hplaH.1 _ hplaH.2.2.1
  have hmem : ∀ᵐ x ∂(μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)),
      x ∈ Work.EKLComp.orbitPlaque H x₀ ε :=
    (MeasureTheory.ae_restrict_iff' hZ).mpr (Filter.Eventually.of_forall (fun _ hx => hx))
  -- The σ-algebra inclusions.
  have hTle : mT ≤ Work.EKLContract.instMeasurableSpaceX3 := hplaT.1
  have hLe : Work.EKLComp.plaqueSigma H x₀ ε ≤ mT := halign
  -- σ-finiteness for the tower property.
  haveI hμfin : MeasureTheory.IsFiniteMeasure μ :=
    ⟨by rw [MeasureTheory.IsProbabilityMeasure.measure_univ]; norm_num⟩
  haveI : MeasureTheory.IsFiniteMeasure (μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)) :=
    inferInstance
  haveI : MeasureTheory.IsFiniteMeasure
      ((μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)).trim hTle) := inferInstance
  haveI : MeasureTheory.SigmaFinite
      ((μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)).trim hTle) := inferInstance
  -- `F` is Borel and bounded a.e. by `C`.
  have hFmeas : Measurable F := by
    have h : @MeasureTheory.StronglyMeasurable Work.EKLContract.X3 ℝ _ mT F :=
      MeasureTheory.stronglyMeasurable_condExp
        (μ := μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)) (f := f)
    exact h.measurable.mono hTle le_rfl
  have hFbound : ∀ᵐ y ∂(μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)), |F y| ≤ C := by
    have h1 : (fun y => ‖F y‖) ≤ᵐ[μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)]
        MeasureTheory.condExp mT (μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε))
          (fun y => ‖f y‖) := by
      simpa [F] using norm_condExp_le (μ := μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε))
        (m := mT) f
    have h2 : MeasureTheory.condExp mT (μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε))
        (fun y => ‖f y‖) ≤ᵐ[μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)]
          (fun _ => C) :=
      MeasureTheory.condExp_le_nonneg_const (μ := μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε))
        (m := mT) (f := fun y => ‖f y‖) (c := C) hC0
        (Filter.Eventually.of_forall (fun y => by rw [Real.norm_eq_abs]; exact hC y))
    filter_upwards [h1, h2] with y hy1 hy2
    rw [Real.norm_eq_abs] at hy1
    exact hy1.trans hy2
  -- `g` agrees with `F` a.e. and is Borel and bounded everywhere by `C`.
  have hgF : g =ᵐ[μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)] F := by
    filter_upwards [hFbound] with y hy
    show max (-C) (min (F y) C) = F y
    rw [min_eq_left (le_of_abs_le hy), max_eq_right (neg_le_of_abs_le hy)]
  have hgmeas : Measurable g := by
    show Measurable (fun y => max (-C) (min (F y) C))
    exact measurable_const.max (hFmeas.min measurable_const)
  have hgbound : ∃ C', ∀ y, |g y| ≤ C' := ⟨C, fun y => by
    show |max (-C) (min (F y) C)| ≤ C
    exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩⟩
  -- The tower property, and `condExp` depends only on the a.e. class.
  have htower : MeasureTheory.condExp (Work.EKLComp.plaqueSigma H x₀ ε)
        (μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε))
        (MeasureTheory.condExp mT (μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)) f)
      =ᵐ[μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)]
        MeasureTheory.condExp (Work.EKLComp.plaqueSigma H x₀ ε)
          (μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)) f :=
    MeasureTheory.condExp_condExp_of_le (μ := μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε))
      (f := f) (m₁ := Work.EKLComp.plaqueSigma H x₀ ε) (m₂ := mT) hLe hTle
  have hCong : MeasureTheory.condExp (Work.EKLComp.plaqueSigma H x₀ ε)
        (μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)) g
      =ᵐ[μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)]
        MeasureTheory.condExp (Work.EKLComp.plaqueSigma H x₀ ε)
          (μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)) f :=
    (MeasureTheory.condExp_congr_ae (μ := μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε))
      (m := Work.EKLComp.plaqueSigma H x₀ ε) hgF).trans htower
  -- The `T`-condexp field: `F` equals the `T`-slice averages a.e.
  have hTavg : ∀ᵐ x ∂(μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)),
      MeasureTheory.condExp mT (μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)) f x = Tavg x := by
    have h := hνT.condexp (Work.EKLComp.orbitPlaque H x₀ ε) mT hplaT f hf hfb
    filter_upwards [h] with x hx
    exact hx
  have hgTavg : g =ᵐ[μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)] Tavg := hgF.trans hTavg
  have hNbadnull : (μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)) Nbad = 0 := by
    have h := MeasureTheory.ae_iff.mp hgTavg
    simpa [Nbad] using h
  -- The null transfer: `νH x` charges no `μ`-null set along the plaque.
  have hNtransfer := Work.EKLProd.null_transfer (μ := μ) hνH hε hHc hinj hP hNbadnull
  -- Hence the `νH x`-average of `Tavg (· • x)` equals that of `g (· • x)`.
  have hNullEq : ∀ᵐ x ∂(μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)),
      MeasureTheory.integral (MeasureTheory.Measure.restrict (νH x)
          (Work.EKLContract.shape (Work.EKLComp.plaqueSigma H x₀ ε) H x))
          (fun h => MeasureTheory.integral (MeasureTheory.Measure.restrict (νT (h • x))
              (Work.EKLContract.shape mT T (h • x))) (fun t => f (t • (h • x)))
            / (νT (h • x) (Work.EKLContract.shape mT T (h • x))).toReal)
        = MeasureTheory.integral (MeasureTheory.Measure.restrict (νH x)
            (Work.EKLContract.shape (Work.EKLComp.plaqueSigma H x₀ ε) H x))
            (fun h => g (h • x)) := by
    filter_upwards [hNtransfer, hmem] with x hxN hxP
    apply MeasureTheory.integral_congr_ae
    show ∀ᵐ h ∂((νH x).restrict
        (Work.EKLContract.shape (Work.EKLComp.plaqueSigma H x₀ ε) H x)), Tavg (h • x) = g (h • x)
    rw [MeasureTheory.ae_iff]
    have hshape_meas : MeasurableSet
        (Work.EKLContract.shape (Work.EKLComp.plaqueSigma H x₀ ε) H x) := by
      obtain ⟨O, hOopen, hOeq⟩ := (hplaH.2.2.2 x hxP).2.2.1
      rw [hOeq]
      exact hOopen.measurableSet.inter hHc.measurableSet
    rw [MeasureTheory.Measure.restrict_apply' hshape_meas]
    have hsub : ({h : Work.EKLContract.SL3 | ¬ (Tavg (h • x) = g (h • x))}
          ∩ Work.EKLContract.shape (Work.EKLComp.plaqueSigma H x₀ ε) H x)
        ⊆ {u : Work.EKLContract.SL3 |
            u • x ∈ Nbad ∩ Work.EKLComp.orbitPlaque H x₀ ε} := by
      rintro h ⟨hbad, hsh⟩
      have hhxP : h • x ∈ Work.EKLComp.orbitPlaque H x₀ ε := by
        have hatom : Work.EKLContract.atom (Work.EKLComp.plaqueSigma H x₀ ε) x
            = Work.EKLComp.orbitPlaque H x₀ ε :=
          Work.EKLProd.atom_generateFrom_singleton
            (Work.EKLComp.orbitPlaque H x₀ ε) x hxP
        exact hatom ▸ hsh.2
      exact ⟨Ne.symm hbad, hhxP⟩
    exact le_antisymm ((MeasureTheory.measure_mono hsub).trans (le_of_eq hxN)) bot_le
  -- The two `condExp` fields (with test functions `f` resp. `g`).
  have hfieldf : ∀ᵐ x ∂(μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)),
      MeasureTheory.integral (MeasureTheory.Measure.restrict (νH x)
          (Work.EKLContract.shape (Work.EKLComp.plaqueSigma H x₀ ε) H x)) (fun h => f (h • x))
        / (νH x (Work.EKLContract.shape (Work.EKLComp.plaqueSigma H x₀ ε) H x)).toReal
      = MeasureTheory.condExp (Work.EKLComp.plaqueSigma H x₀ ε)
          (μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)) f x := by
    have h := hνH.condexp (Work.EKLComp.orbitPlaque H x₀ ε)
      (Work.EKLComp.plaqueSigma H x₀ ε) hplaH f hf hfb
    filter_upwards [h] with x hx
    exact hx.symm
  have hfieldg : ∀ᵐ x ∂(μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)),
      MeasureTheory.integral (MeasureTheory.Measure.restrict (νH x)
          (Work.EKLContract.shape (Work.EKLComp.plaqueSigma H x₀ ε) H x)) (fun h => g (h • x))
        / (νH x (Work.EKLContract.shape (Work.EKLComp.plaqueSigma H x₀ ε) H x)).toReal
      = MeasureTheory.condExp (Work.EKLComp.plaqueSigma H x₀ ε)
          (μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)) g x := by
    have h := hνH.condexp (Work.EKLComp.orbitPlaque H x₀ ε)
      (Work.EKLComp.plaqueSigma H x₀ ε) hplaH g hgmeas hgbound
    filter_upwards [h] with x hx
    exact hx.symm
  -- The right-hand side equals the same `condExp`.
  have hfieldR : ∀ᵐ x ∂(μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)),
      MeasureTheory.integral (MeasureTheory.Measure.restrict (νH x)
          (Work.EKLContract.shape (Work.EKLComp.plaqueSigma H x₀ ε) H x))
          (fun h => MeasureTheory.integral (MeasureTheory.Measure.restrict (νT (h • x))
              (Work.EKLContract.shape mT T (h • x))) (fun t => f (t • (h • x)))
            / (νT (h • x) (Work.EKLContract.shape mT T (h • x))).toReal)
        / (νH x (Work.EKLContract.shape (Work.EKLComp.plaqueSigma H x₀ ε) H x)).toReal
      = MeasureTheory.condExp (Work.EKLComp.plaqueSigma H x₀ ε)
          (μ.restrict (Work.EKLComp.orbitPlaque H x₀ ε)) f x := by
    filter_upwards [hNullEq, hfieldg, hCong] with x hn hg hc
    rw [hn, hg, hc]
  filter_upwards [hfieldf, hfieldR] with x h1 h2
  rw [h1, h2]

end

end Work.EKLProd
