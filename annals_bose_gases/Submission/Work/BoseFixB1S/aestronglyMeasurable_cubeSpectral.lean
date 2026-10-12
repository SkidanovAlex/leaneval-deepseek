import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1B.MargPiece.integrable_bsW_chiB_sub_holds
import Submission.Work.BoseFixB1S.CubeWindow.marginalCube
import Submission.Work.BoseFixB1S.CubeWindowKinetic
import Submission.Work.BoseFixB1S.win.chiSmallB_fsKinPGenIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.aestronglyMeasurable_cubeSpectral`

The **cube-window** twin of `Work.BoseFixB1.aestronglyMeasurable_tBwordBInd`'s spectral half: the
sliding spectral slot

`u ↦ tBwordKinInd ℓ (B(u)) |B(u)| χ_{B(u)} c Φ`

(with the single cube cutoff `χ_{B(u)} = chiSmallB M ℓ d u`) is `AEStronglyMeasurable` in the
sliding centre `u ∈ ℝ³`, for *every continuous* state `Φ`.

The frozen (ball-window) proof and this one use the same device, and *none* of it is
window-specific except two places:

* the **joint continuity** of the window, `(u,z) ↦ χ_{B(u)}(z)`: for the ball window this is
  `chiB`'s explicit product form, for the cube window it is `chiSmallB_continuous_pair` below
  (a product of `chiScale ℓ` in `z` and `chiSmall M` along `(ℓd)⁻¹•z − u`, hence jointly
  continuous — note `chiSmall_continuous_all` needs **no** hypothesis on `M`);
* the **linearity identity** `Work.BoseBox.tBamp_boxQInd_eq_sub`, which is generic in the window
  given only `χ` supported in the box, continuous and compactly supported — all three hold for
  `chiSmallB M ℓ d u` (`chiSmallB_eq_zero_of_not_mem_dlBox`, `chiSmallB_continuous`,
  `Submission.BoseGases.chiSmallB_hasCompactSupport`).

Everything else (the box volume `boxMass`, the slot integral, the box mean `boxP`, the two
parametric-integral lemmas) is window-independent and is transcribed from the frozen proof.
-/

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000

/-- **Joint continuity of the cube window** `(u,z) ↦ chiSmallB M ℓ d u z`.  The `z`-scale factor
is `chiScale ℓ z` and the small factor is `chiSmall M ((ℓd)⁻¹ • z − u)`, i.e. the
(continuous, for every `M`) bump `chiSmall M` composed with a continuous affine map. -/
lemma chiSmallB_continuous_pair (M : ℕ) (ℓ d : ℝ) :
    Continuous (fun q : E3 × E3 => Submission.BoseGases.chiSmallB M ℓ d q.1 q.2) := by
  have hchi : Continuous (fun z : E3 => Submission.BoseGases.chiSmall M z) :=
    Work.SmallBoxSliding.chiSmall_continuous_all M
  have h1 : Continuous (fun q : E3 × E3 => Submission.BoseGases.chiScale ℓ q.2) :=
    (Submission.BoseGases.chiScale_continuous ℓ).comp continuous_snd
  have h2 : Continuous (fun q : E3 × E3 =>
      Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • q.2 - q.1)) :=
    hchi.comp ((continuous_snd.const_smul ((ℓ * d)⁻¹)).sub continuous_fst)
  have heq : (fun q : E3 × E3 => Submission.BoseGases.chiSmallB M ℓ d q.1 q.2)
      = fun q => Submission.BoseGases.chiScale ℓ q.2 *
          Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • q.2 - q.1) := rfl
  rw [heq]
  exact h1.mul h2

/-- **Joint measurability of the sliding spectral integrand at the cube cutoff.**  For a
continuous state `Φ`, the `(u,p)`-parametrised amplitude energy
`∫_{abox n ℓ}‖tBamp (χ_{B(u)}) p (Q_{B(u),i}Φ) i x‖²` is a.e. strongly measurable for
`volume.prod volume`.

This is the cube-window transcription of `Work.BoseFixB1.aemeasurable_diagIntegrand`: the three
ingredients of FS's decomposition `Q_{B(u),i}Φ = 1_{B(u)}Φ − P_{B(u),i}Φ` — the box mass
`boxMass ℓ d u`, the slot integral `∫_{B(u)}Φ(update x i z)dz` and the amplitudes of the fixed
states `Φ` and `1` — are each a.e. strongly measurable in `s = ((u,p),x)` as marginals of
*jointly measurable* kernels on `s × ℝ³`; the only window input is the joint continuity
`chiSmallB_continuous_pair`. -/
private lemma aemeasurable_diagIntegrandCube {n : ℕ} {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ)
    (i : Fin n) :
    AEMeasurable
      (fun q : E3 × E3 =>
        ∫ x in Submission.BoseGases.abox n ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d q.1) q.2
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d q.1)
              (Submission.BoseGases.dlBox ℓ d q.1) i Φ) i x‖ ^ 2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  classical
  -- ## 1. The box volume `boxMass ℓ d u`, as a function of `s ∈ S`
  have hmass : AEMeasurable (fun s : (E3 × E3) × Submission.BoseGases.X n =>
      Work.SmallBoxSliding.boxMass ℓ d s.1.1)
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume).prod
        MeasureTheory.volume) := by
    have hboxInd : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
        Work.SmallBoxSliding.boxInd ℓ d t.1.1.1 t.2) := by
      have hmap : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          (t.1.1.1, t.2)) :=
        (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd
      have hset : MeasurableSet {t : ((E3 × E3) × Submission.BoseGases.X n) × E3 |
          t.2 ∈ Submission.BoseGases.dlBox ℓ d t.1.1.1} :=
        (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d).preimage hmap
      have hfun : (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          Work.SmallBoxSliding.boxInd ℓ d t.1.1.1 t.2)
          = {t : ((E3 × E3) × Submission.BoseGases.X n) × E3 |
              t.2 ∈ Submission.BoseGases.dlBox ℓ d t.1.1.1}.indicator (fun _ => (1 : ℝ)) := by
        funext t
        rw [Work.SmallBoxSliding.boxInd]
        by_cases h : t.2 ∈ Submission.BoseGases.dlBox ℓ d t.1.1.1
        · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show t ∈ _ from h)]
        · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show t ∉ _ from h)]
      rw [hfun]
      exact measurable_const.indicator hset
    have h := MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := (MeasureTheory.volume : MeasureTheory.Measure E3)) hboxInd.stronglyMeasurable
    have hfun2 : (fun s : (E3 × E3) × Submission.BoseGases.X n =>
        ∫ z : E3, Work.SmallBoxSliding.boxInd ℓ d s.1.1 z)
        = fun s : (E3 × E3) × Submission.BoseGases.X n =>
            Work.SmallBoxSliding.boxMass ℓ d s.1.1 := by
      funext s; rw [Work.SmallBoxSliding.boxMass]
    rw [hfun2] at h
    exact h.aemeasurable
  -- ## 2. The slot integral `∫_{B(u)}Φ(update x i z)dz`, as a function of `s ∈ S`
  have hslot : AEMeasurable (fun s : (E3 × E3) × Submission.BoseGases.X n =>
      ∫ z in Submission.BoseGases.dlBox ℓ d s.1.1, Φ (Function.update s.2 i z))
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume).prod
        MeasureTheory.volume) := by
    have hjoint : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
        (Submission.BoseGases.dlBox ℓ d t.1.1.1).indicator
          (fun z => Φ (Function.update t.1.2 i z)) t.2) := by
      have hmap : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          (t.1.1.1, t.2)) :=
        (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd
      have hset : MeasurableSet {t : ((E3 × E3) × Submission.BoseGases.X n) × E3 |
          t.2 ∈ Submission.BoseGases.dlBox ℓ d t.1.1.1} :=
        (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d).preimage hmap
      have hupd : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          Function.update t.1.2 i t.2) :=
        (measurable_update' (a := i)).comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
      have hcomp : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          Φ (Function.update t.1.2 i t.2)) := hΦ.measurable.comp hupd
      have hite : (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          (Submission.BoseGases.dlBox ℓ d t.1.1.1).indicator
            (fun z => Φ (Function.update t.1.2 i z)) t.2)
          = fun t => if t.2 ∈ Submission.BoseGases.dlBox ℓ d t.1.1.1
              then Φ (Function.update t.1.2 i t.2) else 0 := by
        funext t
        by_cases h : t.2 ∈ Submission.BoseGases.dlBox ℓ d t.1.1.1
        · rw [if_pos h, Set.indicator_of_mem h]
        · rw [if_neg h, Set.indicator_of_notMem h]
      rw [hite]
      exact Measurable.ite hset hcomp measurable_const
    have h := MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := (MeasureTheory.volume : MeasureTheory.Measure E3)) hjoint.stronglyMeasurable
    refine h.aemeasurable.congr ?_
    filter_upwards with s
    rw [MeasureTheory.integral_indicator
      (Work.SmallBoxSliding.measurableSet_dlBox ℓ d s.1.1)]
  -- ## 3. The box mean `P_{B(u),i}Φ`, as a function of `s ∈ S`
  have hmean : AEMeasurable (fun s : (E3 × E3) × Submission.BoseGases.X n =>
      ((Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d s.1.1)
        (Submission.BoseGases.dlBox ℓ d s.1.1) i Φ (Function.update s.2 i 0) : ℝ) : ℂ))
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume).prod
        MeasureTheory.volume) := by
    have hR : AEMeasurable (fun s : (E3 × E3) × Submission.BoseGases.X n =>
        Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d s.1.1)
          (Submission.BoseGases.dlBox ℓ d s.1.1) i Φ (Function.update s.2 i 0))
        (((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume).prod
          MeasureTheory.volume) := by
      have hfun : (fun s : (E3 × E3) × Submission.BoseGases.X n =>
          Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d s.1.1)
            (Submission.BoseGases.dlBox ℓ d s.1.1) i Φ (Function.update s.2 i 0))
          = fun s => (Work.SmallBoxSliding.boxMass ℓ d s.1.1)⁻¹ *
              ∫ z in Submission.BoseGases.dlBox ℓ d s.1.1, Φ (Function.update s.2 i z) := by
        funext s
        rw [Work.SmallBoxTBWord.boxP]
        simp only [one_div, Function.update_idem]
      rw [hfun]
      exact (hmass.inv).mul hslot
    exact Complex.measurable_ofReal.comp_aemeasurable hR
  -- ## 4. The amplitudes of the fixed states `Φ` and `1`, as functions of `s ∈ S`
  have hamp : ∀ (Ψ : Submission.BoseGases.X n → ℝ), Continuous Ψ →
      AEMeasurable (fun s : (E3 × E3) × Submission.BoseGases.X n =>
        Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d s.1.1) s.1.2 Ψ i s.2)
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume).prod
        MeasureTheory.volume) := by
    intro Ψ hΨ
    have hchi_cont : Continuous (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
        Submission.BoseGases.chiSmallB M ℓ d t.1.1.1 t.2) := by
      -- the two factors of the cube window, jointly in `(u,z) = (t.1.1.1, t.2)`
      have hchi : Continuous (fun z : E3 => Submission.BoseGases.chiSmall M z) :=
        Work.SmallBoxSliding.chiSmall_continuous_all M
      have hz : Continuous (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 => t.2) :=
        continuous_snd
      have hu : Continuous (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 => t.1.1.1) :=
        (continuous_fst (X := E3) (Y := E3)).comp
          ((continuous_fst (X := E3 × E3) (Y := Submission.BoseGases.X n)).comp
            (continuous_fst (X := (E3 × E3) × Submission.BoseGases.X n) (Y := E3)))
      have harg : Continuous (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          (ℓ * d)⁻¹ • t.2 - t.1.1.1) := (hz.const_smul ((ℓ * d)⁻¹)).sub hu
      have hsmall : Continuous (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • t.2 - t.1.1.1)) := hchi.comp harg
      have hbig : Continuous (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          Submission.BoseGases.chiScale ℓ t.2) :=
        (Submission.BoseGases.chiScale_continuous ℓ).comp continuous_snd
      have heq : (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
            Submission.BoseGases.chiSmallB M ℓ d t.1.1.1 t.2)
          = fun t => Submission.BoseGases.chiScale ℓ t.2 *
              Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • t.2 - t.1.1.1) := rfl
      rw [heq]
      exact hbig.mul hsmall
    have hupd : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
        Function.update t.1.2 i t.2) :=
      (measurable_update' (a := i)).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    have hker : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
        (Submission.BoseGases.chiSmallB M ℓ d t.1.1.1 t.2 : ℂ)
          * Complex.exp (-(Complex.I * (inner ℝ t.1.1.2 t.2 : ℂ)))
          * (Ψ (Function.update t.1.2 i t.2) : ℂ)) := by
      have hexp : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          Complex.exp (-(Complex.I * (inner ℝ t.1.1.2 t.2 : ℂ)))) := by
        have hcont : Continuous (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
            -(Complex.I * (inner ℝ t.1.1.2 t.2 : ℂ))) := by
          refine Continuous.neg ?_
          refine continuous_const.mul ?_
          exact Complex.continuous_ofReal.comp (by fun_prop)
        exact Complex.measurable_exp.comp hcont.measurable
      have hchi : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          (Submission.BoseGases.chiSmallB M ℓ d t.1.1.1 t.2 : ℂ)) :=
        Complex.measurable_ofReal.comp hchi_cont.measurable
      have hPsi : Measurable (fun t : ((E3 × E3) × Submission.BoseGases.X n) × E3 =>
          (Ψ (Function.update t.1.2 i t.2) : ℂ)) :=
        Complex.measurable_ofReal.comp (hΨ.measurable.comp hupd)
      exact (hchi.mul hexp).mul hPsi
    have h := MeasureTheory.StronglyMeasurable.integral_prod_right'
      (ν := (MeasureTheory.volume : MeasureTheory.Measure E3)) hker.stronglyMeasurable
    exact h.aemeasurable
  have hA := hamp Φ hΦ
  have hB := hamp (fun _ : Submission.BoseGases.X n => (1 : ℝ)) continuous_const
  -- ## 5. The FS decomposition of the projected amplitude, pointwise in `s ∈ S`
  have hdec : AEMeasurable (fun s : (E3 × E3) × Submission.BoseGases.X n =>
      (Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d s.1.1) s.1.2 Φ i s.2
        - ((Work.SmallBoxTBWord.boxP (Work.SmallBoxSliding.boxMass ℓ d s.1.1)
            (Submission.BoseGases.dlBox ℓ d s.1.1) i Φ (Function.update s.2 i 0) : ℝ) : ℂ)
          * Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d s.1.1) s.1.2
              (fun _ : Submission.BoseGases.X n => (1 : ℝ)) i s.2))
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume).prod
        MeasureTheory.volume) :=
    hA.sub (hmean.mul hB)
  have hproj : AEMeasurable (fun s : (E3 × E3) × Submission.BoseGases.X n =>
      Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d s.1.1) s.1.2
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d s.1.1)
          (Submission.BoseGases.dlBox ℓ d s.1.1) i Φ) i s.2)
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume).prod
        MeasureTheory.volume) := by
    refine hdec.congr ?_
    filter_upwards with s
    exact (Work.BoseBox.tBamp_boxQInd_eq_sub
      (volA := Work.SmallBoxSliding.boxMass ℓ d s.1.1)
      (A := Submission.BoseGases.dlBox ℓ d s.1.1)
      (χ := Submission.BoseGases.chiSmallB M ℓ d s.1.1) Φ i s.1.2 s.2 0
      (fun z hz => chiSmallB_eq_zero_of_not_mem_dlBox hM hℓ hd s.1.1 hz)
      (Work.BoseFixB1S.chiSmallB_continuous hM ℓ d s.1.1)
      (Submission.BoseGases.chiSmallB_hasCompactSupport hM hℓ s.1.1)
      hΦ).symm
  -- ## 6. Square, restrict the `x`-integral to the box, and integrate `x` out
  have hsquare : MeasureTheory.AEStronglyMeasurable
      (fun s : (E3 × E3) × Submission.BoseGases.X n =>
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d s.1.1) s.1.2
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d s.1.1)
            (Submission.BoseGases.dlBox ℓ d s.1.1) i Φ) i s.2‖ ^ 2)
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume).prod
        MeasureTheory.volume) := by
    have h1 : AEMeasurable (fun s : (E3 × E3) × Submission.BoseGases.X n =>
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d s.1.1) s.1.2
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d s.1.1)
            (Submission.BoseGases.dlBox ℓ d s.1.1) i Φ) i s.2‖)
        (((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume).prod
          MeasureTheory.volume) :=
      hproj.norm
    exact (h1.pow_const 2).aestronglyMeasurable
  have hres : MeasureTheory.AEStronglyMeasurable
      (fun s : (E3 × E3) × Submission.BoseGases.X n =>
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d s.1.1) s.1.2
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d s.1.1)
            (Submission.BoseGases.dlBox ℓ d s.1.1) i Φ) i s.2‖ ^ 2)
      (((MeasureTheory.volume : MeasureTheory.Measure E3).prod MeasureTheory.volume).prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.abox n ℓ))) :=
    hsquare.mono_measure (MeasureTheory.Measure.prod_mono le_rfl
      MeasureTheory.Measure.restrict_le_self)
  exact (hres.integral_prod_right').aemeasurable

theorem aestronglyMeasurable_cubeSpectral {M : ℕ} (hM : 1 ≤ M) {ℓ d c : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) {N : ℕ} {Φ : Submission.BoseGases.X N → ℝ}
    (hΦ : Continuous Φ) :
    MeasureTheory.AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
        (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u) c Φ)
      MeasureTheory.volume := by
  rw [show (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.UBBInputs8.tBwordKinInd ℓ (Submission.BoseGases.dlBox ℓ d u)
          (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u) c Φ)
      = fun u : EuclideanSpace ℝ (Fin 3) => ∑ i : Fin N,
          ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
            Submission.BoseGases.fsKinCoeff c ‖p‖ * ((ℓ ^ 3)⁻¹ *
              ∫ x in Submission.BoseGases.abox N ℓ,
                ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) p
                  (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
                    (Submission.BoseGases.dlBox ℓ d u) i Φ) i x‖ ^ 2) from rfl]
  refine Finset.aestronglyMeasurable_fun_sum Finset.univ (fun i _ => ?_)
  have hF := aemeasurable_diagIntegrandCube (n := N) hM hℓ hd hΦ i
  have hcoefcont : Continuous (fun r : ℝ => Submission.BoseGases.fsKinCoeff c r) := by
    unfold Submission.BoseGases.fsKinCoeff
    exact ((continuous_id.sub continuous_const).max continuous_const).pow 2
  have hcoef : AEMeasurable (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff c ‖q.2‖)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    (hcoefcont.comp (continuous_norm.comp continuous_snd)).measurable.aemeasurable
  have hjoint : AEMeasurable (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.fsKinCoeff c ‖q.2‖ * ((ℓ ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox N ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d q.1) q.2
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d q.1)
              (Submission.BoseGases.dlBox ℓ d q.1) i Φ) i x‖ ^ 2))
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    hcoef.mul (hF.const_mul _)
  have hinter := hjoint.aestronglyMeasurable.integral_prod_right'
  exact hinter.const_mul _

end Work.BoseFixB1S
