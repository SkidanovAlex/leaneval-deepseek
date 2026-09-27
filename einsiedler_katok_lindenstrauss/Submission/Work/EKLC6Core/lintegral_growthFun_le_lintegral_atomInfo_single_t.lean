import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.covAlong
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.box_conjBox_subset
import Submission.Work.EKLC6Core.growth_le_HcondSig
import Submission.Work.EKLC6Core.growth_le_HcondSig_mp
import Submission.Work.EKLC6Core.atomInfo_ae_eq_aux_along
import Submission.Work.EKLC6Core.atomInfo_aemeasurable
import Submission.Work.EKLC6Core.coboundary_integral

/-!
# `EKLC6Core.lintegral_growthFun_le_lintegral_atomInfo_single_t`

The `ENNReal` form of Pisa 7.18/7.34 for the full contracted horospherical subgroup
`Uminus t` -- the join of the root groups `Uij` with `t i < t j` -- in the single-parameter
setting: `MeasurePreserving (aDiag t .) mu mu` for the one parameter `t` at hand, and the
covariance of the leafwise system only along the integer multiples of `t`.

It rests on the a.e. identity of Pisa 7.34 at the single parameter `t`
(`EKLC6Core.atomInfo_ae_eq_aux_along`),

`atomInfo A U nu t x = psi (T x) - psi x + growthFun U nu t (T x)`,
`psi y = Real.log ((nu y (shape A U y)).toReal)`, `T x = aDiag t . x`,

together with the general analytic fact `st_lintegral_ofReal_comp_le_of_coboundary` below (the
truncation/Fatou argument; `psi` need not be integrable), and on the a.e. non-negativity of
`growthFun` for a contracted subgroup (`box_conjBox_subset` and `nu x (Box1 U) = 1`).

NOTE.  The general horospherical form `EKLC6Core.lintegral_growthFun_le_lintegral_atomInfo_horo`
lives in the module `EKLC6Core.lintegral_growthFun_le_lintegral_atomInfo_uij`, which is *not*
importable here: that module imports the file `EKLC6Core.per_t_covariance_mp`, which declares
`Work.EKLC6Core.per_t_covariance_mp`, already declared (with a different statement) by
`EKLC6Core.covAlong`, the module that defines `ACovariantAlong`.  The general analytic input is
therefore reproduced here under names prefixed `st_`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## Truncation bookkeeping -/

theorem st_ekTrunc_mono (M : ℝ) : Monotone (ekTrunc M) := by
  intro a b hab
  simp only [ekTrunc]
  exact max_le_max le_rfl (min_le_min le_rfl hab)

theorem st_ekTrunc_sub_le_max (M t s : ℝ) :
    ekTrunc M t - ekTrunc M s ≤ max (t - s) 0 := by
  by_cases h : t ≤ s
  · have h1 : ekTrunc M t ≤ ekTrunc M s := st_ekTrunc_mono M h
    have h2 : max (t - s) 0 = 0 := max_eq_right (by linarith)
    linarith [h1, h2]
  · have ht : s < t := not_le.mp h
    have h2 : max (t - s) 0 = t - s := max_eq_left (by linarith)
    have h1 : |ekTrunc M t - ekTrunc M s| ≤ |t - s| := ekTrunc_abs_lipschitz M t s
    have h3 : |t - s| = t - s := abs_of_nonneg (by linarith)
    have h4 : ekTrunc M t - ekTrunc M s ≤ |t - s| := (abs_le.mp h1).2
    linarith [h2, h3, h4]

theorem st_tendsto_ekTrunc_nat (y : ℝ) :
    Tendsto (fun N : ℕ => ekTrunc (N : ℝ) y) atTop (𝓝 y) := by
  have hev : (fun N : ℕ => ekTrunc (N : ℝ) y) =ᶠ[atTop] (fun _ => y) := by
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt |y|
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have hNy : |y| ≤ (N : ℝ) := le_trans (le_of_lt hN₀) (by exact_mod_cast hN)
    show max (-(N : ℝ)) (min (N : ℝ) y) = y
    rw [min_eq_right (le_trans (le_abs_self y) hNy),
      max_eq_right (le_trans (neg_le_neg hNy) (neg_abs_le y))]
  exact Tendsto.congr' hev.symm tendsto_const_nhds

/-! ## The coboundary inequality -/

theorem st_lintegral_ofReal_comp_le_of_coboundary {X : Type*} [MeasurableSpace X]
    {μ : MeasureTheory.Measure X} [MeasureTheory.IsProbabilityMeasure μ] {T : X → X}
    (hT : MeasureTheory.MeasurePreserving T μ μ) {a ψ g : X → ℝ}
    (ha_int : MeasureTheory.Integrable a μ) (ha_nn : 0 ≤ᵐ[μ] a)
    (hψ : AEMeasurable ψ μ) (hg_nn : 0 ≤ᵐ[μ] g)
    (hid : ∀ᵐ x ∂μ, a x = ψ (T x) - ψ x + g (T x)) :
    ∫⁻ x, ENNReal.ofReal (g (T x)) ∂μ ≤ ∫⁻ x, ENNReal.ofReal (a x) ∂μ := by
  classical
  have hcongr : (fun x => ENNReal.ofReal (g (T x)))
      =ᵐ[μ] (fun x => ENNReal.ofReal (a x - (ψ (T x) - ψ x))) := by
    filter_upwards [hid] with x hx
    rw [show g (T x) = a x - (ψ (T x) - ψ x) by linarith]
  rw [lintegral_congr_ae hcongr]
  set Ψ : ℕ → X → ℝ := fun N y => ekTrunc (N : ℝ) (ψ y) with hΨ
  set A : ℕ → X → ℝ := fun N x => a x - (Ψ N (T x) - Ψ N x) with hA
  have hΨ_aemeas : ∀ N, AEMeasurable (Ψ N) μ := fun N =>
    (ekTrunc_cont (N : ℝ)).measurable.comp_aemeasurable hψ
  have hΨT_aemeas : ∀ N, AEMeasurable (fun x => Ψ N (T x)) μ := fun N => by
    have h' : AEMeasurable (Ψ N) (Measure.map T μ) := by rw [hT.map_eq]; exact hΨ_aemeas N
    exact AEMeasurable.comp_measurable (f := T) (g := Ψ N) h' hT.measurable
  have hA_aemeas : ∀ N, AEMeasurable (A N) μ := fun N =>
    (ha_int.aestronglyMeasurable.aemeasurable).sub ((hΨT_aemeas N).sub (hΨ_aemeas N))
  have hΨ_int : ∀ N, Integrable (Ψ N) μ := fun N =>
    Integrable.of_bound (hΨ_aemeas N).aestronglyMeasurable (N : ℝ)
      (ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs]
        exact ekTrunc_abs_le (N : ℝ) (Nat.cast_nonneg N) (ψ x)))
  have hΨT_int : ∀ N, Integrable (fun x => Ψ N (T x)) μ := fun N =>
    Integrable.of_bound (hΨT_aemeas N).aestronglyMeasurable (N : ℝ)
      (ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs]
        exact ekTrunc_abs_le (N : ℝ) (Nat.cast_nonneg N) (ψ (T x))))
  have hA_int : ∀ N, Integrable (A N) μ := fun N =>
    ha_int.sub ((hΨT_int N).sub (hΨ_int N))
  have hcomp : ∀ N, ∫ x, Ψ N (T x) ∂μ = ∫ x, Ψ N x ∂μ := by
    intro N
    have h1 : ∫ y, Ψ N y ∂(Measure.map T μ) = ∫ x, Ψ N (T x) ∂μ :=
      integral_map hT.aemeasurable (by rw [hT.map_eq]; exact (hΨ_int N).aestronglyMeasurable)
    rw [← h1, hT.map_eq]
  have hA_int_eq : ∀ N, ∫ x, A N x ∂μ = ∫ x, a x ∂μ := by
    intro N
    have h1 : ∫ x, Ψ N (T x) - Ψ N x ∂μ = 0 := by
      rw [MeasureTheory.integral_sub (hΨT_int N) (hΨ_int N), hcomp N, sub_self]
    have h2 : ∫ x, A N x ∂μ = ∫ x, a x - (Ψ N (T x) - Ψ N x) ∂μ := by
      simp only [hA]
    have h3 : ∫ x, a x - (Ψ N (T x) - Ψ N x) ∂μ
        = (∫ x, a x ∂μ) - ∫ x, Ψ N (T x) - Ψ N x ∂μ := by
      have hsub := MeasureTheory.integral_sub (f := fun x : X => a x)
        (g := fun x : X => Ψ N (T x) - Ψ N x) ha_int ((hΨT_int N).sub (hΨ_int N))
      simpa only [Pi.sub_apply] using hsub
    rw [h2, h3, h1, sub_zero]
  have hA_nn' : ∀ N, ∀ᵐ x ∂μ, 0 ≤ a x - (Ψ N (T x) - Ψ N x) := by
    intro N
    filter_upwards [hid, ha_nn, hT.quasiMeasurePreserving.ae hg_nn] with x hx hxa hxg
    have hxa' : 0 ≤ a x := hxa
    have hxg' : 0 ≤ g (T x) := hxg
    have h1 : Ψ N (T x) - Ψ N x ≤ max (ψ (T x) - ψ x) 0 := by
      simpa only [hΨ] using st_ekTrunc_sub_le_max (N : ℝ) (ψ (T x)) (ψ x)
    have h2 : max (ψ (T x) - ψ x) 0 ≤ a x := by
      by_cases hle : ψ (T x) - ψ x ≤ 0
      · rw [max_eq_right hle]; exact hxa'
      · have hpos : 0 < ψ (T x) - ψ x := not_le.mp hle
        rw [max_eq_left hpos.le]; linarith
    linarith
  have hA_nn : ∀ N, 0 ≤ᵐ[μ] A N := fun N =>
    (hA_nn' N).mono (fun x hx => by rw [hA]; simpa using hx)
  have hlin : ∀ N, ∫⁻ x, ENNReal.ofReal (A N x) ∂μ = ENNReal.ofReal (∫ x, a x ∂μ) := by
    intro N
    rw [← hA_int_eq N]
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hA_int N) (hA_nn N)).symm
  have hfatou : ∫⁻ x, Filter.liminf (fun N => ENNReal.ofReal (A N x)) atTop ∂μ
      ≤ Filter.liminf (fun N => ∫⁻ x, ENNReal.ofReal (A N x) ∂μ) atTop :=
    MeasureTheory.lintegral_liminf_le' (fun N => (hA_aemeas N).ennreal_ofReal)
  have hliminf : ∫⁻ x, Filter.liminf (fun N => ENNReal.ofReal (A N x)) atTop ∂μ
      = ∫⁻ x, ENNReal.ofReal (a x - (ψ (T x) - ψ x)) ∂μ := by
    refine lintegral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    have hconv : Tendsto (fun N : ℕ => A N x) atTop (𝓝 (a x - (ψ (T x) - ψ x))) := by
      have h1 : Tendsto (fun N : ℕ => Ψ N (T x)) atTop (𝓝 (ψ (T x))) := by
        simpa only [hΨ] using st_tendsto_ekTrunc_nat (ψ (T x))
      have h2 : Tendsto (fun N : ℕ => Ψ N x) atTop (𝓝 (ψ x)) := by
        simpa only [hΨ] using st_tendsto_ekTrunc_nat (ψ x)
      have h3 : Tendsto (fun N : ℕ => Ψ N (T x) - Ψ N x) atTop (𝓝 (ψ (T x) - ψ x)) :=
        h1.sub h2
      simpa only [hA] using tendsto_const_nhds.sub h3
    exact (ENNReal.tendsto_ofReal hconv).liminf_eq
  have hconst : Filter.liminf (fun N : ℕ => ∫⁻ x, ENNReal.ofReal (A N x) ∂μ) atTop
      = ENNReal.ofReal (∫ x, a x ∂μ) := by
    have hfun : (fun N : ℕ => ∫⁻ x, ENNReal.ofReal (A N x) ∂μ)
        = fun _ => ENNReal.ofReal (∫ x, a x ∂μ) := funext hlin
    rw [hfun, Filter.liminf_const]
  calc ∫⁻ x, ENNReal.ofReal (a x - (ψ (T x) - ψ x)) ∂μ
      = ∫⁻ x, Filter.liminf (fun N => ENNReal.ofReal (A N x)) atTop ∂μ := hliminf.symm
    _ ≤ Filter.liminf (fun N : ℕ => ∫⁻ x, ENNReal.ofReal (A N x) ∂μ) atTop := hfatou
    _ = ENNReal.ofReal (∫ x, a x ∂μ) := hconst
    _ = ∫⁻ x, ENNReal.ofReal (a x) ∂μ :=
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal ha_int ha_nn

/-! ## The main theorem -/

theorem lintegral_growthFun_le_lintegral_atomInfo_single_t {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariantAlong ν t X'') (hX'' : μ (X''ᶜ) = 0)
    (hmeas : Measurable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t))
    {A : MeasurableSpace Work.EKLContract.X3} {Z : Set Work.EKLContract.X3}
    (hplq : Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z A) (hZ : μ Zᶜ = 0)
    (hdec : MeasurableSpace.comap
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) A ≤ A)
    (hfin : ∫⁻ x, ENNReal.ofReal
      (Work.EKLC6Core.atomInfo A (Work.EKLC6Core.Uminus t) ν t x) ∂μ ≠ ⊤) :
    ∫⁻ x, ENNReal.ofReal
        (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x) ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal
        (Work.EKLC6Core.atomInfo A (Work.EKLC6Core.Uminus t) ν t x) ∂μ := by
  letI : MeasurableSpace X3 := instMeasurableSpaceX3
  -- `Uminus t` is an admissible (horospherical) subgroup, contracted by `aDiag t` itself.
  have hU : IsHoro (Uminus t) := (uminus_isHoro t).1
  have hcontr : ∀ u ∈ Uminus t, Filter.Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) Filter.atTop (nhds 1) :=
    (uminus_isHoro t).2
  -- `atomInfo` is a.e. non-negative (it is `-log` of a ratio `<= 1` for a descending algebra).
  have hg_nn : 0 ≤ᵐ[μ] (fun x => atomInfo A (Uminus t) ν t x) :=
    Filter.Eventually.of_forall (fun x =>
      atomInfo_nonneg_mp (U := Uminus t) (ν := ν) (t := t) hdec x)
  -- `growthFun` is a.e. non-negative: the contracted box sits inside the normalising box.
  have hf_nn : 0 ≤ᵐ[μ] (fun x => growthFun (Uminus t) ν t x) := by
    have hsub : conjBox (Uminus t) t ⊆ Box1 (Uminus t) := (box_conjBox_subset hU hcontr).1
    have hX' : ∀ᵐ x ∂μ, x ∈ X' := by rw [MeasureTheory.ae_iff]; exact hL.conull
    filter_upwards [hX'] with x hx
    have hle : ν x (conjBox (Uminus t) t) ≤ 1 := by
      calc ν x (conjBox (Uminus t) t) ≤ ν x (Box1 (Uminus t)) := MeasureTheory.measure_mono hsub
        _ = 1 := hL.normalised x hx
    have htoReal : (ν x (conjBox (Uminus t) t)).toReal ≤ 1 :=
      ENNReal.toReal_mono ENNReal.one_ne_top hle
    have hlog : Real.log ((ν x (conjBox (Uminus t) t)).toReal) ≤ 0 :=
      Real.log_nonpos ENNReal.toReal_nonneg htoReal
    show 0 ≤ growthFun (Uminus t) ν t x
    simp only [growthFun]
    linarith
  -- `atomInfo` is integrable, by the finiteness hypothesis.
  have hg_aemeas : AEMeasurable (fun x => atomInfo A (Uminus t) ν t x) μ :=
    atomInfo_aemeasurable (μ := μ) (U := Uminus t) (ν := ν) (X' := X') t hL hU hplq
  have hg_int : MeasureTheory.Integrable (fun x => atomInfo A (Uminus t) ν t x) μ :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
      hg_aemeas.aestronglyMeasurable hg_nn).mp hfin
  -- the `psi` of the coboundary
  have hψ : AEMeasurable (fun y => Real.log ((ν y (shape A (Uminus t) y)).toReal)) μ :=
    Real.measurable_log.comp_aemeasurable ((aemeasurable_shape_mass_two (μ := μ) (U := Uminus t)
      (ν := ν) (X' := X') t hL hU hplq).1)
  -- Pisa 7.34 at the single parameter `t`, under covariance along the integer multiples of `t`
  have hid := atomInfo_ae_eq_aux_along (μ := μ) (U := Uminus t) (ν := ν)
    (X' := X') (X'' := X'') (t := t) (A := A) (Z := Z)
    hL hU hcov hX'' hmp hplq hZ
  have hkey := st_lintegral_ofReal_comp_le_of_coboundary (μ := μ)
    (T := fun x : X3 => aDiag t • x) hmp hg_int hg_nn hψ hf_nn hid
  -- `g ∘ T` and `g` have the same `∫⁻`, by measure preservation
  have hshift : ∫⁻ x, ENNReal.ofReal (growthFun (Uminus t) ν t (aDiag t • x)) ∂μ
      = ∫⁻ x, ENNReal.ofReal (growthFun (Uminus t) ν t x) ∂μ :=
    MeasureTheory.MeasurePreserving.lintegral_comp hmp hmeas.ennreal_ofReal
  rw [← hshift]
  exact hkey

end Work.EKLC6Core

end
