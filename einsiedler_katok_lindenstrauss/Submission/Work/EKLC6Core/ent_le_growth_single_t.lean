import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.covAlong
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.countableGenEntropy
import Submission.Work.EKLC6Core._ChGenDev
import Submission.Work.EKLC6Core.HcondSig_eq_growth_along
import Submission.Work.EKLC6Core.exists_plaque_alg_gen_modmu
import Submission.Work.EKLC6Core.fiber_leafwise_along
import Submission.Work.EKLC6Core.condExpKernel_quasiErgodic
import Submission.Work.EKLComp.ent_jacobs
import Submission.Work.EKLEntJacobs.fiber_inv
import Submission.Work.EKLC6Core.box_conjBox_subset
import Submission.Work.EKLComp.X3Background
import Submission.Work.EKLC6Core.chart_nonempty_aux
import Submission.Work.EKLC6Core.C6_tsum_entropy

/-!
# `Work.EKLC6Core.ent_le_growth_single_t` — Pisa 7.6(ii) for a single diagonal element

The equality direction of Pisa 7.6(ii): for a probability `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` preserved by
the single element `T = (aDiag t ·)`, a leaf-wise system `ν` for the contracted horospherical
subgroup `Uminus t = G⁻(t)`, and the single-`t` covariance `ACovariantAlong ν t X''`, one has

`ent μ T ≤ ofReal (∫ growthFun (Uminus t) ν t dμ)`.

## Route

The proof is the ergodic-component reduction of Pisa 7.19–7.24 together with, on each
`T`-ergodic component, the *countable*-generator form of Pisa 7.43 + 7.34:

* the geometric input is `Work.EKLC6Core.exists_plaque_alg_gen_modmu` (Pisa 7.43: a countable Borel
  family `P` that generates modulo `μ`, with a conull `Z` on which the past σ-algebra
  `pastSigSet t P` is a plaque algebra for `Uminus t`, and with `HcondSig μ (σ (range P)) ⊥ ≠ ⊤`,
  i.e. Pisa 7.50's finite entropy);
* `Work.EKLC6Core.ChDev_ent_le_HcondSig_of_genData_modMu` (Pisa 7.6(ii)′ for a countable generator)
  bounds `ent μ T` by `HcondSig μ (pastSigSet t P) (comap T (pastSigSet t P))`, and
* `Work.EKLC6Core.HcondSig_eq_growth_along` (Pisa 7.34/7.35, the shape comparison) identifies
  that conditional entropy with `ofReal (∫ growthFun (Uminus t) ν t)`;
* the ergodic-component reduction is `Work.EKLComp.ent_jacobs` (Pisa 5.14 / Jacobs) together with
  the invariance, a.e.-ergodicity, leaf-wise and null-set statements for the conditional measures
  `condExpKernel μ (invariants T) x`;
* the degenerate case `Uminus t = ⊥` (so that `aDiag t = 1` and `T` is the identity) is settled
  directly: the entropy vanishes and the growth function is `0` a.e.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- The `T`-ergodicity predicate (a.e.-invariant measurable sets are null or conull), for
`T = (aDiag t ·)`. -/
abbrev TErg (t : Fin 3 → ℝ) (μ : MeasureTheory.Measure Work.EKLContract.X3) : Prop :=
  ∀ E : Set Work.EKLContract.X3, MeasurableSet E →
    (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ⁻¹' E =ᵐ[μ] E →
    μ E = 0 ∨ μ Eᶜ = 0

/-! ## 1. The conditional measures over the invariant σ-algebra vanish on null sets -/

theorem condExpKernel_eq_zero_of_null_single_t {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] [StandardBorelSpace Work.EKLContract.X3]
    {T : Work.EKLContract.X3 → Work.EKLContract.X3} (hT : Measurable T)
    (hmp : MeasureTheory.MeasurePreserving T μ μ)
    {B : Set Work.EKLContract.X3} (hBmeas : MeasurableSet B) (hB0 : μ B = 0) :
    ∀ᵐ x ∂μ, ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x B = 0 := by
  have hm : MeasurableSpace.invariants T ≤ (inferInstance : MeasurableSpace Work.EKLContract.X3) :=
    MeasurableSpace.invariants_le T
  have hind : B.indicator (fun _ => (1 : ℝ)) =ᵐ[μ] (0 : Work.EKLContract.X3 → ℝ) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine le_antisymm ?_ bot_le
    refine le_trans (MeasureTheory.measure_mono ?_) (le_of_eq hB0)
    intro x hx
    by_contra hxc
    exact hx (by simp [Set.indicator_of_notMem hxc])
  have h2 : μ[B.indicator (fun _ => (1 : ℝ)) | MeasurableSpace.invariants T] =ᵐ[μ]
      (0 : Work.EKLContract.X3 → ℝ) := by
    have h := MeasureTheory.condExp_congr_ae (μ := μ)
      (m := MeasurableSpace.invariants T) hind
    rwa [MeasureTheory.condExp_zero] at h
  have hreal : (fun x => (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x).real B)
      =ᵐ[μ] (0 : Work.EKLContract.X3 → ℝ) :=
    (ProbabilityTheory.condExpKernel_ae_eq_condExp (μ := μ)
      (m := MeasurableSpace.invariants T) hm hBmeas).trans h2
  filter_upwards [hreal] with x hx
  haveI : MeasureTheory.IsProbabilityMeasure
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) :=
    ProbabilityTheory.IsMarkovKernel.is_probability_measure' x
  have hfin : ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x B < ⊤ := by
    refine lt_of_le_of_lt (MeasureTheory.measure_mono (Set.subset_univ B)) ?_
    rw [MeasureTheory.measure_univ]
    exact ENNReal.one_lt_top
  rw [MeasureTheory.measureReal_def] at hx
  rcases (ENNReal.toReal_eq_zero_iff _).mp hx with h | h
  · exact h
  · exact absurd h (ne_of_lt hfin)

/-! ## 2. The per-ergodic-component bound -/

/-- **Pisa 7.19–7.24, per ergodic component.**  Given, for every `T`-ergodic probability in the
range of the conditional measures, a countable generator with the Pisa 7.43/7.50 properties, the
entropy of that component is bounded by the integral of the growth function. -/
theorem ent_le_growth_fiber_along_single_t {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] [StandardBorelSpace Work.EKLContract.X3]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariantAlong ν t X'') (hX'' : μ (X''ᶜ) = 0)
    (hmeas : Measurable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t))
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) μ)
    (hne : Work.EKLC6Core.Uminus t ≠ ⊥)
    (hG : ∀ (κ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure κ],
        MeasureTheory.MeasurePreserving
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) κ κ →
        TErg t κ → Work.EKLC6Core.Uminus t ≠ ⊥ → 0 < Work.EKLContract.ent κ
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) →
        ∃ (P : ℕ → Set Work.EKLContract.X3) (Z : Set Work.EKLContract.X3),
          (∀ n : ℕ, MeasurableSet (P n)) ∧
          Work.EKLC6Core.GeneratesModMuSet κ t P ∧
          Work.EKLC6Core.HcondSig κ (MeasurableSpace.generateFrom (Set.range P))
            (⊥ : MeasurableSpace Work.EKLContract.X3) ≠ ⊤ ∧
          Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z
            (Work.EKLC6Core.pastSigSet t P) ∧
          κ Zᶜ = 0) :
    ∀ᵐ x ∂μ,
      Work.EKLContract.ent
        (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)) x)
        (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ≤
      ENNReal.ofReal (∫ y, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t y
        ∂(ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)) x)) := by
  let T : Work.EKLContract.X3 → Work.EKLContract.X3 := fun x => Work.EKLContract.aDiag t • x
  have hT : Measurable T := (continuous_const_smul (Work.EKLContract.aDiag t)).measurable
  have hX''fib : ∀ᵐ x ∂μ,
      ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x (X''ᶜ) = 0 := by
    obtain ⟨B, hXB, hBmeas, hB0⟩ := MeasureTheory.exists_measurable_superset_of_null hX''
    filter_upwards [condExpKernel_eq_zero_of_null_single_t hT hmp hBmeas hB0] with x hx
    exact le_antisymm (le_trans (MeasureTheory.measure_mono hXB) (le_of_eq hx)) bot_le
  have hintfib : ∀ᵐ x ∂μ,
      MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t)
        (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) :=
    hint.condExpKernel_ae
  filter_upwards [Work.EKLEntJacobs.fiber_inv μ T hT hmp,
      condExpKernel_quasiErgodic μ T hT hmp,
      fiber_leafwise_along (μ := μ) (ν := ν) (X' := X') (X'' := X'') t hmp hL hcov hX'',
      hX''fib, hintfib] with x hinv hqerg hLx hX''x hintx
  haveI : MeasureTheory.IsProbabilityMeasure
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) :=
    ProbabilityTheory.IsMarkovKernel.is_probability_measure' x
  by_cases hpos : 0 < Work.EKLContract.ent
      (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) T
  · obtain ⟨P, Z, hPmeas, hgen, hfin, hplq, hZ⟩ := hG _ hinv hqerg hne hpos
    have h1 := ChDev_ent_le_HcondSig_of_genData_modMu (μ := ProbabilityTheory.condExpKernel μ
        (MeasurableSpace.invariants T) x) t hinv P hPmeas hgen hfin
    have h2 := HcondSig_eq_growth_along (μ := ProbabilityTheory.condExpKernel μ
        (MeasurableSpace.invariants T) x) t hinv hLx hcov hX''x hmeas hintx hplq hZ
      (comap_pastSigSet_le t P)
    exact h1.trans (le_of_eq h2)
  · have hzero : Work.EKLContract.ent
        (ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x) T = 0 :=
      le_antisymm (le_of_not_gt hpos) bot_le
    rw [hzero]
    exact bot_le

/-! ## 3. The assembly -/

/-- **The assembly.**  If the countable-generator geometric input is available for every
`T`-ergodic probability, then `ent μ T ≤ ofReal (∫ growthFun (Uminus t) ν t)` for every `μ`
preserved by `T` and every leaf-wise system `ν` for `Uminus t` with the single-`t` covariance. -/
theorem ent_le_growth_mp_along_of_fibre_geom_gen {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariantAlong ν t X'') (hX'' : μ (X''ᶜ) = 0)
    (hmeas : Measurable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t))
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) μ)
    (hne : Work.EKLC6Core.Uminus t ≠ ⊥)
    (hG : ∀ (κ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure κ],
        MeasureTheory.MeasurePreserving
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) κ κ →
        TErg t κ → Work.EKLC6Core.Uminus t ≠ ⊥ → 0 < Work.EKLContract.ent κ
          (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) →
        ∃ (P : ℕ → Set Work.EKLContract.X3) (Z : Set Work.EKLContract.X3),
          (∀ n : ℕ, MeasurableSet (P n)) ∧
          Work.EKLC6Core.GeneratesModMuSet κ t P ∧
          Work.EKLC6Core.HcondSig κ (MeasurableSpace.generateFrom (Set.range P))
            (⊥ : MeasurableSpace Work.EKLContract.X3) ≠ ⊤ ∧
          Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z
            (Work.EKLC6Core.pastSigSet t P) ∧
          κ Zᶜ = 0) :
    Work.EKLContract.ent μ (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)
      ≤ ENNReal.ofReal (∫ x, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x ∂μ) := by
  haveI hSB : StandardBorelSpace Work.EKLContract.X3 := Work.EKLComp.X3Background.2.2.2.2
  let T : Work.EKLContract.X3 → Work.EKLContract.X3 := fun x => Work.EKLContract.aDiag t • x
  have hTmeas : Measurable T := (continuous_const_smul (Work.EKLContract.aDiag t)).measurable
  have hm : MeasurableSpace.invariants T ≤ (inferInstance : MeasurableSpace Work.EKLContract.X3) :=
    MeasurableSpace.invariants_le T
  let g : Work.EKLContract.X3 → ℝ := Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t
  let κ : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.X3 :=
    fun x => ProbabilityTheory.condExpKernel μ (MeasurableSpace.invariants T) x
  have hJ : Work.EKLContract.ent μ T = ∫⁻ x, Work.EKLContract.ent (κ x) T ∂μ :=
    Work.EKLComp.ent_jacobs μ T hTmeas hmp
  have hper : ∀ᵐ x ∂μ, Work.EKLContract.ent (κ x) T ≤
      ENNReal.ofReal (∫ y, g y ∂(κ x)) :=
    ent_le_growth_fiber_along_single_t (μ := μ) (ν := ν) (X' := X') (X'' := X'') t hmp hL hcov
      hX'' hmeas hint hne hG
  have hgpt : ∀ y ∈ X', 0 ≤ g y := by
    intro y hy
    have hbox := (Work.EKLC6Core.box_conjBox_subset (Work.EKLC6Core.uminus_isHoro t).1
      (Work.EKLC6Core.uminus_isHoro t).2).1
    have hmono : ν y (Work.EKLC6Core.conjBox (Work.EKLC6Core.Uminus t) t) ≤
        ν y (Work.EKLContract.Box1 (Work.EKLC6Core.Uminus t)) := MeasureTheory.measure_mono hbox
    have h1 : ν y (Work.EKLContract.Box1 (Work.EKLC6Core.Uminus t)) = 1 := hL.normalised y hy
    have hle1 : (ν y (Work.EKLC6Core.conjBox (Work.EKLC6Core.Uminus t) t)).toReal ≤ 1 := by
      rw [h1] at hmono
      simpa using ENNReal.toReal_mono ENNReal.one_ne_top hmono
    have hge0 : 0 ≤ (ν y (Work.EKLC6Core.conjBox (Work.EKLC6Core.Uminus t) t)).toReal :=
      ENNReal.toReal_nonneg
    simp only [g, Work.EKLC6Core.growthFun]
    exact neg_nonneg.mpr (Real.log_nonpos hge0 hle1)
  have hX'fib : ∀ᵐ x ∂μ, κ x (X'ᶜ) = 0 :=
    condExpKernel_eq_zero_of_null_single_t hTmeas hmp hL.meas_dom.compl hL.conull
  let a : Work.EKLContract.X3 → ℝ := fun x => ∫ y, g y ∂(κ x)
  have ha_int : MeasureTheory.Integrable a μ :=
    hint.integral_condExpKernel (m := MeasurableSpace.invariants T)
  have ha_nonneg : 0 ≤ᵐ[μ] a := by
    filter_upwards [hX'fib] with x hx
    refine MeasureTheory.integral_nonneg_of_ae ?_
    change ∀ᵐ y ∂(κ x), 0 ≤ g y
    rw [MeasureTheory.ae_iff]
    have hsub : {y | ¬ 0 ≤ g y} ⊆ X'ᶜ := by
      intro y hy
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff] at hy ⊢
      by_contra hc
      exact hy (hgpt y hc)
    exact le_antisymm (le_trans (MeasureTheory.measure_mono hsub) (le_of_eq hx)) bot_le
  have ha_condExp : a =ᵐ[μ] μ[g | MeasurableSpace.invariants T] :=
    (ProbabilityTheory.condExp_ae_eq_integral_condExpKernel hm hint).symm
  have ha_eq : ∫ x, a x ∂μ = ∫ x, g x ∂μ := by
    rw [MeasureTheory.integral_congr_ae ha_condExp]
    exact MeasureTheory.integral_condExp (m := MeasurableSpace.invariants T) (μ := μ) hm
  calc Work.EKLContract.ent μ T
      = ∫⁻ x, Work.EKLContract.ent (κ x) T ∂μ := hJ
    _ ≤ ∫⁻ x, ENNReal.ofReal (a x) ∂μ := MeasureTheory.lintegral_mono_ae hper
    _ = ENNReal.ofReal (∫ x, a x ∂μ) :=
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal ha_int ha_nonneg).symm
    _ = ENNReal.ofReal (∫ x, g x ∂μ) := by rw [ha_eq]

/-! ## 4. The degenerate case `Uminus t = ⊥` -/

/-- `Box1` of the trivial subgroup is the identity. -/
theorem box1_bot_single_t : Box1 (⊥ : Subgroup SL3) = {1} := by
  ext g
  simp only [Box1, Set.mem_ofPred_eq, Subgroup.mem_bot, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hg, -⟩
    exact hg
  · intro hg
    subst hg
    refine ⟨rfl, ?_⟩
    intro i j
    simp [Matrix.one_apply]

/-- Conjugation fixes the identity. -/
theorem conjBy_singleton_one_single_t (t : Fin 3 → ℝ) : conjBy t ({1} : Set SL3) = {1} := by
  ext g
  simp only [conjBy, Set.mem_image, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h, hh, rfl⟩
    subst hh
    simp
  · intro hg
    refine ⟨1, rfl, ?_⟩
    subst hg
    simp

/-- In the degenerate case `Uminus t = ⊥` the growth function vanishes a.e. -/
theorem growthFun_eq_zero_ae_of_uminus_eq_bot_single_t
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hL : Work.EKLContract.IsLeafwise μ (⊥ : Subgroup SL3) ν X') :
    ∀ᵐ x ∂μ, Work.EKLC6Core.growthFun (⊥ : Subgroup SL3) ν t x = 0 := by
  have hX' : ∀ᵐ x ∂μ, x ∈ X' := MeasureTheory.ae_iff.mpr hL.conull
  have hconjBox : conjBox (⊥ : Subgroup SL3) t = {1} := by
    rw [conjBox, box1_bot_single_t, conjBy_singleton_one_single_t]
  filter_upwards [hX'] with x hx
  have hn : ν x (conjBox (⊥ : Subgroup SL3) t) = 1 := by
    rw [hconjBox, ← box1_bot_single_t]
    exact hL.normalised x hx
  rw [growthFun, hn, ENNReal.toReal_one, Real.log_one, neg_zero]


/-- **The countable generator with finite entropy, from an explicit chart.**
Same content as `EKLC6st_geom_input`, but taking the chart of Pisa 7.27 / L2a as an argument, so
that the last remaining open obligation of the geometric route (`Work.EKLC6Route.exists_chart`) is
replaced by an explicit hypothesis. -/
theorem EKLC6st_geom_input_of_chart {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hqerg : TErg t μ) (hU : Work.EKLC6Core.Uminus t ≠ ⊥)
    (c : Work.EKLC6Route.Chart μ t) :
    ∃ (P : ℕ → Set Work.EKLContract.X3) (Z : Set Work.EKLContract.X3),
      (∀ n : ℕ, MeasurableSet (P n)) ∧
      Work.EKLC6Core.GeneratesModMuSet μ t P ∧
      Work.EKLC6Core.HcondSig μ (MeasurableSpace.generateFrom (Set.range P))
        (⊥ : MeasurableSpace Work.EKLContract.X3) ≠ ⊤ ∧
      Work.EKLContract.IsPlaqueAlgebra (Work.EKLC6Core.Uminus t) Z
        (Work.EKLC6Core.pastSigSet t P) ∧ μ Zᶜ = 0 := by
  obtain ⟨w, -⟩ := Work.EKLC6Route.exists_window (μ := μ) c
  obtain ⟨Z, hZm, hZ, hplq, hpos, hbnd⟩ :=
    Work.EKLC6Route.plaque_data (μ := μ) w hmp hqerg
  have hbasic := Work.EKLC6Route.S_basic (μ := μ) w hmp
  have hWmeas : MeasurableSet w.W := hbasic.2.2.2.2.1
  have hBmeas : MeasurableSet (Z ∩ w.W) := hZm.inter hWmeas
  have hrec := Work.EKLC6Route.ae_frequently_mem_neg (μ := μ) hmp hqerg hBmeas hpos
  have hent : @Work.EKLC6Core.HcondSig Work.EKLContract.X3
      Work.EKLContract.instMeasurableSpaceX3 μ
      (MeasurableSpace.generateFrom (Set.range w.S)) (⊥ : MeasurableSpace Work.EKLContract.X3)
      ≠ ⊤ :=
    Work.EKLC6Core.HcondSig_ne_top_of_tsum (μ := μ) w.S hbasic.1 hbasic.2.1
      (Work.EKLC6Route.tsum_negMulLog_ne_top (μ := μ) w hmp)
  obtain ⟨S, Z', hS, hplq', hZ', hgen, hfin⟩ :=
    Work.EKLC6Core.exists_plaque_alg_gen_modmu_of_data_rec (μ := μ) t hmp
      ⟨w.S, Z, Z ∩ w.W, 2, hbasic.1, hZ, hplq, Set.inter_subset_left,
        (fun x hx u hu hux i j => hbnd x hx u hu hux i j), hrec, hent⟩
  exact ⟨S, Z', hS, hgen, hfin, hplq', hZ'⟩

/-! ## 5. The target -/

theorem ent_le_growth_single_t {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ]
    {ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3}
    {X' X'' : Set Work.EKLContract.X3} (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hL : Work.EKLContract.IsLeafwise μ (Work.EKLC6Core.Uminus t) ν X')
    (hcov : Work.EKLC6Core.ACovariantAlong ν t X'') (hX'' : μ (X''ᶜ) = 0)
    (hmeas : Measurable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t))
    (hint : MeasureTheory.Integrable (Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t) μ) :
    Work.EKLContract.ent μ (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x)
      ≤ ENNReal.ofReal (∫ x, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x ∂μ) := by
  by_cases hU : Work.EKLC6Core.Uminus t = ⊥
  · have hzero : (∫ x, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x ∂μ) = 0 := by
      have hae : ∀ᵐ x ∂μ, Work.EKLC6Core.growthFun (Work.EKLC6Core.Uminus t) ν t x = 0 := by
        have h := growthFun_eq_zero_ae_of_uminus_eq_bot_single_t (μ := μ) (ν := ν) (X' := X') t
          (hU ▸ hL)
        filter_upwards [h] with x hx
        rwa [hU]
      rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_zero]
    have hent : Work.EKLContract.ent μ
        (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) = 0 :=
      ent_aDiag_eq_zero_of_uminus_eq_bot t hU
    rw [hent, hzero, ENNReal.ofReal_zero]
  · exact ent_le_growth_mp_along_of_fibre_geom_gen (μ := μ) (ν := ν) (X' := X') (X'' := X'') t
      hmp hL hcov hX'' hmeas hint hU
      (fun κ _ hmp' hqerg _ _ =>
        EKLC6st_geom_input_of_chart (μ := κ) t hmp' hqerg hU
          (Classical.choice (Work.EKLC6Core.chart_nonempty_aux (μ := κ) t)))

end Work.EKLC6Core

end
