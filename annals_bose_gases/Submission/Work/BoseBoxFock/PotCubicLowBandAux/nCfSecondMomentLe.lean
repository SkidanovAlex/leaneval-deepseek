import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Submission.Work.BoseBoxFock.PotCubicLowBandAux.windowCGAuxAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PotCubicLowBandAux.nCfSecondMomentLe`

The second-moment comparison between the *mode-projected* excited vector
`∑ j, (A_j Θ − P_j Θ)` and the honest excited vector `n₊Θ = ∑ j, (Θ − P_j Θ)`, where

* `A_j = slotProj1 e j` is the orthogonal projection of slot `j` onto the span of the modes `e`,
* `P_j = aPC ℓ j` is the orthogonal projection of slot `j` onto the constants (`e 0 = c·θ_Λ`).

**Mathematical content.**  Write `v_j := Θ − P_j Θ` (so `n₊Θ = ∑_j v_j`) and
`Π_j := A_j − P_j` (so the left-hand side is `∑_j Π_j Θ`).  Both `A_j` and `P_j` are
orthogonal projections on `L²(abox)` with `P_j A_j = A_j P_j = P_j`, and distinct slots commute;
hence `Π_j = A_j − P_j` is itself an orthogonal projection with `Π_j Π_l = Π_l Π_j` for `j ≠ l`,
`Π_j Z_j = 0` where `Z_j := 1 − A_j`, and (for `j ≠ l`) `Π_j Z_l` is again an orthogonal
projection.  Splitting `n₊Θ = (∑_j Π_j Θ) + (∑_j Z_j Θ)` and expanding the square gives

    ∫ ‖n₊Θ‖² − ∫ ‖∑_j Π_j Θ‖² = 2 Re ∫ ⟨∑_k Π_k Θ, ∑_l Z_l Θ⟩ + ∫ ‖∑_l Z_l Θ‖²,

and the cross term is a sum of terms `⟨Π_k Θ, Z_l Θ⟩` which vanish for `k = l` and equal
`‖Π_k Z_l Θ‖² ≥ 0` for `k ≠ l`.  All the analytic inputs are the proved lemmas of
`Submission/Work/MB/` and `Submission/Work/BoseBoxFock/` for the weak (measurable, everywhere
bounded, box supported) bundle; the only new a.e. ingredient is the insensitivity of `slotProj1`
to null modifications *on the box*, which is reduced here to the full-measure version
`Work.BoseBoxFock.slotProj1_ae_eq_congr_aux` by multiplying the states by the box indicator.
-/

namespace Work.BoseBoxFock.PotCubicLowBandAux

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "𝕏" n:max => Submission.BoseGases.X n
local notation "sA" => Work.BoseBoxFock.slotProj1
local notation "sP" => Work.BoseBoxFock.aPC
local notation "PiF[" e "," l "," T "," j "]" => (fun z_1 => sA e j T z_1 - sP l j T z_1)
local notation "XF[" e "," l "," T "," j "," k "]" =>
  (fun z_2 => PiF[e, l, T, j] z_2 - sA e k (PiF[e, l, T, j]) z_2)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- Lebesgue measure restricted to the configuration box. -/
noncomputable abbrev μS {n : ℕ} (ℓ : ℝ) : Measure (𝕏 n) :=
  (MeasureTheory.volume : Measure (𝕏 n)).restrict (Submission.BoseGases.abox n ℓ)

/-! ## 1. Elementary closure and congruence lemmas -/

/-- A full-measure a.e. statement is an a.e. statement on the box. -/
lemma ae_box_of_ae {n : ℕ} {ℓ : ℝ} {f g : 𝕏 n → ℂ}
    (h : f =ᵐ[(MeasureTheory.volume : Measure (𝕏 n))] g) : f =ᵐ[μS ℓ] g :=
  MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_le_self
    (μ := (MeasureTheory.volume : Measure (𝕏 n))) (s := Submission.BoseGases.abox n ℓ)) h

/-- Measurable everywhere bounded functions are integrable on the box. -/
lemma integrableOn_box_of_bound {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {E : Type*}
    [NormedAddCommGroup E] {F : 𝕏 n → E}
    (hF : AEStronglyMeasurable F (MeasureTheory.volume : Measure (𝕏 n)))
    {C : ℝ} (hC : ∀ x, ‖F x‖ ≤ C) :
    IntegrableOn F (Submission.BoseGases.abox n ℓ) :=
  MeasureTheory.IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top n ℓ hℓ.le)
    hF.restrict C (Filter.Eventually.of_forall hC)

/-- Bounded measurable products are integrable on the box. -/
lemma integrableOn_star_mul {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {a b : 𝕏 n → ℂ}
    (ham : Measurable a) (hab : ∃ C, ∀ x, ‖a x‖ ≤ C)
    (hbm : Measurable b) (hbb : ∃ C, ∀ x, ‖b x‖ ≤ C) :
    IntegrableOn (fun x => star (a x) * b x) (Submission.BoseGases.abox n ℓ) :=
  integrableOn_star_mul_bdd hℓ ham.aestronglyMeasurable hab hbm.aestronglyMeasurable hbb

/-- Congruence of box integrals along an a.e. equality. -/
lemma int_congr_ae_box {n : ℕ} {ℓ : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F G : 𝕏 n → E} (h : F =ᵐ[μS ℓ] G) :
    (∫ x in Submission.BoseGases.abox n ℓ, F x) = ∫ x in Submission.BoseGases.abox n ℓ, G x :=
  MeasureTheory.integral_congr_ae h

/-- Congruence of box integrals of `star (f ·) * h` along an a.e. equality of `f`. -/
lemma int_star_congr_box {n : ℕ} {ℓ : ℝ} {f g h : 𝕏 n → ℂ} (he : f =ᵐ[μS ℓ] g) :
    (∫ x in Submission.BoseGases.abox n ℓ, star (f x) * h x)
      = ∫ x in Submission.BoseGases.abox n ℓ, star (g x) * h x := by
  refine int_congr_ae_box ?_
  filter_upwards [he] with x hx
  rw [hx]

/-- The box integral of an a.e. vanishing function vanishes. -/
lemma int_eq_zero_of_ae_zero {n : ℕ} {ℓ : ℝ} {F : 𝕏 n → ℂ}
    (h : F =ᵐ[μS ℓ] (0 : 𝕏 n → ℂ)) :
    (∫ x in Submission.BoseGases.abox n ℓ, F x) = 0 := by
  rw [show (∫ x in Submission.BoseGases.abox n ℓ, F x)
      = ∫ x in Submission.BoseGases.abox n ℓ, (0 : 𝕏 n → ℂ) x from int_congr_ae_box h]
  simp

/-! ## 2. Measurability and boundedness of the slot operators -/

/-- The condensate slot mean of a measurable state is measurable. -/
lemma aPC_measurable {n : ℕ} (ℓ : ℝ) (j : Fin n) {f : 𝕏 n → ℂ} (hf : Measurable f) :
    Measurable (sP ℓ j f) := by
  have hj : StronglyMeasurable (fun p : 𝕏 n × E3 => f (Function.update p.1 j p.2)) :=
    (hf.stronglyMeasurable).comp_measurable (by fun_prop)
  have hint : StronglyMeasurable (fun x : 𝕏 n =>
      ∫ y : E3, f (Function.update x j y)
        ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
    MeasureTheory.StronglyMeasurable.integral_prod_right
      (f := fun (x : 𝕏 n) (y : E3) => f (Function.update x j y)) hj
  have hfun : sP ℓ j f = fun x : 𝕏 n => ((1 / ℓ ^ 3 : ℝ) : ℂ) *
      ∫ y : E3, f (Function.update x j y)
        ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := rfl
  rw [hfun]
  exact (hint.const_mul _).measurable

/-- `sP` preserves measurability and everywhere boundedness. -/
lemma sP_meas_bdd {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n) {f : 𝕏 n → ℂ}
    (hfm : Measurable f) (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C) :
    Measurable (sP ℓ j f) ∧ ∃ C, ∀ x, ‖sP ℓ j f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hfb
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  exact ⟨aPC_measurable ℓ j hfm, ⟨C, fun x => Work.BoseBoxFock.norm_aPC_le hℓ j hC0 hC x⟩⟩

/-- `sA` preserves measurability and everywhere boundedness (weak modes). -/
lemma sA_meas_bdd {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {f : 𝕏 n → ℂ} (hfm : Measurable f) (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C) (j : Fin n) :
    Measurable (sA e j f) ∧ ∃ C, ∀ x, ‖sA e j f x‖ ≤ C := by
  have h := Work.MB.slotProj_mb_weak hmeas hbdd hsupp ({j} : Finset (Fin n)) hfm hfb
  rwa [Work.BoseBoxFock.slotProj_singleton_eq_slotProj1_aux] at h

/-- `sA` is additive in its state argument (weak modes). -/
lemma sA_sub {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (j : Fin n) {f g : 𝕏 n → ℂ} (hfm : Measurable f) (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C)
    (hgm : Measurable g) (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    sA e j (fun x => f x - g x) = fun x => sA e j f x - sA e j g x :=
  (Work.MB.slotProj1_linear_bdd hmeas hbdd hsupp).2 j f g hfm hfb hgm hgb

/-- `sP` is additive in its state argument. -/
lemma sP_sub {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (j : Fin n) {f g : 𝕏 n → ℂ}
    (hfm : Measurable f) (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C)
    (hgm : Measurable g) (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    sP ℓ j (fun x => f x - g x) = fun x => sP ℓ j f x - sP ℓ j g x := by
  funext x
  obtain ⟨Cf, hCf⟩ := hfb
  obtain ⟨Cg, hCg⟩ := hgb
  have hIf : IntegrableOn (fun y : E3 => f (Function.update x j y))
      (Submission.BoseGases.acube ℓ) :=
    MeasureTheory.IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
      (hfm.comp (measurable_update (f := x) (a := j))).aestronglyMeasurable Cf
      (Filter.Eventually.of_forall (fun y => hCf _))
  have hIg : IntegrableOn (fun y : E3 => g (Function.update x j y))
      (Submission.BoseGases.acube ℓ) :=
    MeasureTheory.IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le)
      (hgm.comp (measurable_update (f := x) (a := j))).aestronglyMeasurable Cg
      (Filter.Eventually.of_forall (fun y => hCg _))
  have hsub : (∫ y : E3, (f (Function.update x j y) - g (Function.update x j y))
        ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)))
      = (∫ y : E3, f (Function.update x j y)
          ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)))
        - (∫ y : E3, g (Function.update x j y)
          ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
    integral_sub hIf hIg
  simp only [Work.BoseBoxFock.aPC]
  rw [hsub]
  ring

/-- `PiF[e, ℓ, Θ, j]` is measurable and everywhere bounded. -/
lemma PiFun_meas_bdd {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ} (hℓ : 0 < ℓ)
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Θ : 𝕏 n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) (j : Fin n) :
    Measurable PiF[e, ℓ, Θ, j] ∧ ∃ C, ∀ x, ‖PiF[e, ℓ, Θ, j] x‖ ≤ C := by
  obtain ⟨hAm, hAb⟩ := sA_meas_bdd hmeas hbdd hsupp hΘm hΘb j
  obtain ⟨hPm, hPb⟩ := sP_meas_bdd hℓ j hΘm hΘb
  obtain ⟨CA, hCA⟩ := hAb
  obtain ⟨CP, hCP⟩ := hPb
  exact ⟨hAm.sub hPm, ⟨CA + CP, fun x => le_trans (norm_sub_le _ _) (add_le_add (hCA x) (hCP x))⟩⟩

/-- `XF[e, ℓ, Θ, j, l]` is measurable and everywhere bounded. -/
lemma XFun_meas_bdd {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ} (hℓ : 0 < ℓ)
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Θ : 𝕏 n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) (j l : Fin n) :
    Measurable XF[e, ℓ, Θ, j, l] ∧ ∃ C, ∀ x, ‖XF[e, ℓ, Θ, j, l] x‖ ≤ C := by
  obtain ⟨hPm, hPb⟩ := PiFun_meas_bdd hℓ hmeas hbdd hsupp hΘm hΘb j
  obtain ⟨CP, hCP⟩ := hPb
  obtain ⟨hAm, hAb⟩ := sA_meas_bdd hmeas hbdd hsupp hPm ⟨CP, hCP⟩ l
  obtain ⟨CA, hCA⟩ := hAb
  exact ⟨hPm.sub hAm, ⟨CP + CA, fun x => le_trans (norm_sub_le _ _) (add_le_add (hCP x) (hCA x))⟩⟩

/-! ## 3. Congruence of `sA` on the box -/

/-- **`slotProj1` is insensitive to modifications of its argument off the box.**  For the
Lebesgue measure restricted to the box. -/
lemma sA_congr_box {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → E3 → ℂ}
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ) (j : Fin n)
    {f g : 𝕏 n → ℂ} (h : f =ᵐ[μS ℓ] g) : sA e j f =ᵐ[μS ℓ] sA e j g := by
  have hSmeas : MeasurableSet (Submission.BoseGases.abox n ℓ) :=
    Submission.BoseGases.abox_measurable n ℓ
  have hbox : ∀ᵐ x ∂(μS (n := n) ℓ), x ∈ Submission.BoseGases.abox n ℓ :=
    MeasureTheory.self_mem_ae_restrict hSmeas
  have hind : (Submission.BoseGases.abox n ℓ).indicator f
      =ᵐ[(MeasureTheory.volume : Measure (𝕏 n))] (Submission.BoseGases.abox n ℓ).indicator g := by
    have h' : ∀ᵐ x ∂(MeasureTheory.volume : Measure (𝕏 n)),
        x ∈ Submission.BoseGases.abox n ℓ → f x = g x :=
      (MeasureTheory.ae_restrict_iff' hSmeas).mp h
    filter_upwards [h'] with x hx
    by_cases hxS : x ∈ Submission.BoseGases.abox n ℓ
    · rw [Set.indicator_of_mem hxS, Set.indicator_of_mem hxS, hx hxS]
    · rw [Set.indicator_of_notMem hxS, Set.indicator_of_notMem hxS]
  have hmid : sA e j ((Submission.BoseGases.abox n ℓ).indicator f)
      =ᵐ[μS ℓ] sA e j ((Submission.BoseGases.abox n ℓ).indicator g) :=
    ae_box_of_ae (Work.BoseBoxFock.slotProj1_ae_eq_congr_aux e j hind)
  have h1 : sA e j f =ᵐ[μS ℓ] sA e j ((Submission.BoseGases.abox n ℓ).indicator f) := by
    filter_upwards [hbox] with x hx
    exact (slotProj1_indicator_abox hℓ hsupp j f x hx).symm
  have h2 : sA e j ((Submission.BoseGases.abox n ℓ).indicator g) =ᵐ[μS ℓ] sA e j g := by
    filter_upwards [hbox] with x hx
    exact slotProj1_indicator_abox hℓ hsupp j g x hx
  exact h1.trans (hmid.trans h2)

/-! ## 4. The a.e. operator identities -/

/-- Distinct slots commute: `A_j A_l = A_l A_j` (as functions). -/
lemma sA_comm {m n : ℕ} {ℓ : ℝ} {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    {f : 𝕏 n → ℂ} (hfm : Measurable f) (hfb : ∃ C, ∀ x, ‖f x‖ ≤ C) (j l : Fin n) :
    sA e j (sA e l f) = sA e l (sA e j f) := by
  have h1 := Work.MB.slotProj_comp_weak hmeas hbdd hsupp horth
    ({l} : Finset (Fin n)) ({j} : Finset (Fin n)) hfm hfb
  have h2 := Work.MB.slotProj_comp_weak hmeas hbdd hsupp horth
    ({j} : Finset (Fin n)) ({l} : Finset (Fin n)) hfm hfb
  simp only [Work.BoseBoxFock.slotProj_singleton_eq_slotProj1_aux] at h1 h2
  rw [h2, h1, Finset.union_comm]

/-- `A_j Π_j Θ = Π_j Θ` (a.e. on the box). -/
lemma Pi_A_absorb {m n : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hml : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      e 0 =ᵐ[(MeasureTheory.volume : Measure E3)] fun x =>
        c * Work.BoseK15.corpusBox.thetaFun ℓ x)
    {Θ : 𝕏 n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) (j : Fin n) :
    sA e j PiF[e, ℓ, Θ, j] =ᵐ[μS ℓ] PiF[e, ℓ, Θ, j] := by
  obtain ⟨hAm, hAb⟩ := sA_meas_bdd hmeas hbdd hsupp hΘm hΘb j
  obtain ⟨hPm, hPb⟩ := sP_meas_bdd hℓ j hΘm hΘb
  have hCΘ : ∀ x : 𝕏 n, ‖Θ x‖ ≤ hΘb.choose := hΘb.choose_spec
  have hmemΘ : MeasureTheory.MemLp Θ ⊤ (MeasureTheory.volume : Measure (𝕏 n)) :=
    MeasureTheory.memLp_top_of_bound hΘm.aestronglyMeasurable hΘb.choose
      (Filter.Eventually.of_forall hCΘ)
  have hlin := sA_sub hmeas hbdd hsupp j hAm hAb hPm hPb
  have hidem := Work.MB.slotProj1_idem_weak hmeas hbdd hsupp horth hΘm hΘb j
  have habs := Work.BoseBoxFock.slotProj1_aPC_absorb_self ℓ hℓ horth hml hsupp hc j hmemΘ
  rw [hlin, hidem]
  have he1 : sA e j Θ =ᵐ[μS ℓ] sA e j Θ := Filter.EventuallyEq.refl _ _
  have he2 : sA e j (sP ℓ j Θ) =ᵐ[μS ℓ] sP ℓ j Θ := habs
  exact he1.sub he2

/-- `P_j Π_j Θ = 0` (a.e. on the box). -/
lemma Pi_P_zero {m n : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hml : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      e 0 =ᵐ[(MeasureTheory.volume : Measure E3)] fun x =>
        c * Work.BoseK15.corpusBox.thetaFun ℓ x)
    {Θ : 𝕏 n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) (j : Fin n) :
    sP ℓ j PiF[e, ℓ, Θ, j] =ᵐ[μS ℓ] (0 : 𝕏 n → ℂ) := by
  obtain ⟨hAm, hAb⟩ := sA_meas_bdd hmeas hbdd hsupp hΘm hΘb j
  obtain ⟨hPm, hPb⟩ := sP_meas_bdd hℓ j hΘm hΘb
  have hCΘ : ∀ x : 𝕏 n, ‖Θ x‖ ≤ hΘb.choose := hΘb.choose_spec
  have hmemΘ : MeasureTheory.MemLp Θ ⊤ (MeasureTheory.volume : Measure (𝕏 n)) :=
    MeasureTheory.memLp_top_of_bound hΘm.aestronglyMeasurable hΘb.choose
      (Filter.Eventually.of_forall hCΘ)
  have hlin := sP_sub hℓ j hAm hAb hPm hPb
  have h1 : sP ℓ j (sA e j Θ) =ᵐ[(MeasureTheory.volume : Measure (𝕏 n))] sP ℓ j Θ :=
    Work.BoseBoxFock.aPC_slotProj1_absorb ℓ hℓ horth hml hsupp hc j hmemΘ
  have h2 : sP ℓ j (sP ℓ j Θ) = sP ℓ j Θ := Work.BoseBoxFock.aPC_idem hℓ j
  rw [hlin]
  exact ((ae_box_of_ae h1).sub (Filter.Eventually.of_forall (fun x => congrFun h2 x))).trans
    (by filter_upwards with x; simp)

/-- `A_l X_{j,l} Θ = 0` (exact identity). -/
lemma X_A_zero {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    {Θ : 𝕏 n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) (j l : Fin n) :
    sA e l XF[e, ℓ, Θ, j, l] =ᵐ[μS ℓ] (0 : 𝕏 n → ℂ) := by
  obtain ⟨hPm, hPb⟩ := PiFun_meas_bdd hℓ hmeas hbdd hsupp hΘm hΘb j
  obtain ⟨hAlm, hAlb⟩ := sA_meas_bdd hmeas hbdd hsupp hPm hPb l
  have hlin := sA_sub hmeas hbdd hsupp l hPm hPb hAlm hAlb
  have hidem := Work.MB.slotProj1_idem_weak hmeas hbdd hsupp horth hPm hPb l
  rw [hlin, hidem]
  filter_upwards with x
  simp

/-- `A_j X_{j,l} Θ = X_{j,l} Θ` for `j ≠ l` (a.e. on the box). -/
lemma X_A_fix {m n : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hml : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      e 0 =ᵐ[(MeasureTheory.volume : Measure E3)] fun x =>
        c * Work.BoseK15.corpusBox.thetaFun ℓ x)
    {Θ : 𝕏 n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C)
    {j l : Fin n} (hjl : j ≠ l) :
    sA e j XF[e, ℓ, Θ, j, l] =ᵐ[μS ℓ] XF[e, ℓ, Θ, j, l] := by
  obtain ⟨hPm, hPb⟩ := PiFun_meas_bdd hℓ hmeas hbdd hsupp hΘm hΘb j
  obtain ⟨hAlm, hAlb⟩ := sA_meas_bdd hmeas hbdd hsupp hPm hPb l
  obtain ⟨hAjm, hAjb⟩ := sA_meas_bdd hmeas hbdd hsupp hPm hPb j
  have hlin := sA_sub hmeas hbdd hsupp j hPm hPb hAlm hAlb
  have hswap := sA_comm hmeas hbdd hsupp horth hPm hPb j l
  have hAi := Pi_A_absorb hℓ hmeas hbdd hsupp hml horth hc hΘm hΘb j
  have hcong := sA_congr_box hℓ hsupp l hAi
  rw [hlin, hswap]
  exact hAi.sub hcong

/-- `P_j X_{j,l} Θ = 0` for `j ≠ l` (a.e. on the box). -/
lemma X_P_zero {m n : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hml : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      e 0 =ᵐ[(MeasureTheory.volume : Measure E3)] fun x =>
        c * Work.BoseK15.corpusBox.thetaFun ℓ x)
    {Θ : 𝕏 n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C)
    {j l : Fin n} (hjl : j ≠ l) :
    sP ℓ j XF[e, ℓ, Θ, j, l] =ᵐ[μS ℓ] (0 : 𝕏 n → ℂ) := by
  obtain ⟨hPm, hPb⟩ := PiFun_meas_bdd hℓ hmeas hbdd hsupp hΘm hΘb j
  obtain ⟨CP, hCP⟩ := hPb
  obtain ⟨hAlm, hAlb⟩ := sA_meas_bdd hmeas hbdd hsupp hPm ⟨CP, hCP⟩ l
  have hlin := sP_sub hℓ j hPm ⟨CP, hCP⟩ hAlm hAlb
  have hPi := Pi_P_zero hℓ hmeas hbdd hsupp hml horth hc hΘm hΘb j
  have hmemPi : MeasureTheory.MemLp PiF[e, ℓ, Θ, j] ⊤ (MeasureTheory.volume : Measure (𝕏 n)) :=
    MeasureTheory.memLp_top_of_bound hPm.aestronglyMeasurable CP
      (Filter.Eventually.of_forall hCP)
  have hcomm := Work.BoseBoxFock.aPC_slotProj1_comm_ne ℓ hℓ horth hml hsupp hjl hmemPi
  have hcong := sA_congr_box hℓ hsupp l hPi
  have hzero : sA e l (0 : 𝕏 n → ℂ) = (0 : 𝕏 n → ℂ) := by
    funext x
    simp [Work.BoseBoxFock.slotProj1]
  have hB : sP ℓ j (sA e l PiF[e, ℓ, Θ, j]) =ᵐ[μS ℓ] (0 : 𝕏 n → ℂ) :=
    ((ae_box_of_ae hcomm).trans
      (hcong.trans (Filter.Eventually.of_forall (fun x => congrFun hzero x))))
  rw [hlin]
  exact (hPi.sub hB).trans (by filter_upwards with x; simp)

/-! ## 5. The two integral identities -/

/-- `star z * z` is the (real) square norm of `z`, as a complex number. -/
lemma star_mul_self_eq (z : ℂ) : star z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]

/-- The `j = l` cross term vanishes. -/
lemma self_cross_zero {m n : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hml : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      e 0 =ᵐ[(MeasureTheory.volume : Measure E3)] fun x =>
        c * Work.BoseK15.corpusBox.thetaFun ℓ x)
    {Θ : 𝕏 n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) (j : Fin n) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        star (PiF[e, ℓ, Θ, j] x) * (Θ x - sA e j Θ x)) = 0 := by
  obtain ⟨hPm, hPb⟩ := PiFun_meas_bdd hℓ hmeas hbdd hsupp hΘm hΘb j
  obtain ⟨hAm, hAb⟩ := sA_meas_bdd hmeas hbdd hsupp hΘm hΘb j
  obtain ⟨hBXm, hBXb⟩ := sA_meas_bdd hmeas hbdd hsupp hPm hPb j
  have hAi := Pi_A_absorb hℓ hmeas hbdd hsupp hml horth hc hΘm hΘb j
  have hdiff : PiF[e, ℓ, Θ, j] - sA e j PiF[e, ℓ, Θ, j] =ᵐ[μS ℓ] (0 : 𝕏 n → ℂ) := by
    have h1 : PiF[e, ℓ, Θ, j] =ᵐ[μS ℓ] PiF[e, ℓ, Θ, j] := Filter.EventuallyEq.refl _ _
    have h2 : sA e j PiF[e, ℓ, Θ, j] =ᵐ[μS ℓ] PiF[e, ℓ, Θ, j] := hAi
    refine (h1.sub h2).trans ?_
    filter_upwards with x
    simp
  have hI1 := integrableOn_star_mul hℓ hPm hPb hΘm hΘb
  have hI2 := integrableOn_star_mul hℓ hPm hPb hAm hAb
  have hI3 := integrableOn_star_mul hℓ hBXm hBXb hΘm hΘb
  calc (∫ x in Submission.BoseGases.abox n ℓ,
        star (PiF[e, ℓ, Θ, j] x) * (Θ x - sA e j Θ x))
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (star (PiF[e, ℓ, Θ, j] x) * Θ x - star (PiF[e, ℓ, Θ, j] x) * sA e j Θ x) := by
        refine int_congr_ae_box ?_
        filter_upwards with x
        ring
    _ = (∫ x in Submission.BoseGases.abox n ℓ, star (PiF[e, ℓ, Θ, j] x) * Θ x)
        - (∫ x in Submission.BoseGases.abox n ℓ, star (PiF[e, ℓ, Θ, j] x) * sA e j Θ x) :=
        integral_sub hI1 hI2
    _ = (∫ x in Submission.BoseGases.abox n ℓ, star (PiF[e, ℓ, Θ, j] x) * Θ x)
        - (∫ x in Submission.BoseGases.abox n ℓ, star (sA e j PiF[e, ℓ, Θ, j] x) * Θ x) := by
        rw [← slotProj1_box_adjoint hℓ hmeas hbdd hsupp j hPm hPb hΘm hΘb]
    _ = (∫ x in Submission.BoseGases.abox n ℓ,
          (star (PiF[e, ℓ, Θ, j] x) * Θ x - star (sA e j PiF[e, ℓ, Θ, j] x) * Θ x)) :=
        (integral_sub hI1 hI3).symm
    _ = (∫ x in Submission.BoseGases.abox n ℓ,
          star ((PiF[e, ℓ, Θ, j] - sA e j PiF[e, ℓ, Θ, j]) x) * Θ x) := by
        refine int_congr_ae_box ?_
        filter_upwards with x
        simp only [Pi.sub_apply, star_sub, sub_mul]
    _ = (∫ x in Submission.BoseGases.abox n ℓ, star ((0 : 𝕏 n → ℂ) x) * Θ x) :=
        int_star_congr_box hdiff
    _ = 0 := by simp

/-- The `j ≠ l` cross term equals the squared `L²` norm of `X_{j,l} Θ`. -/
lemma cross_int_eq {m n : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hml : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (horth : ∀ l l', (∫ z : E3, star (e l z) * e l' z) = (if l = l' then (1 : ℂ) else 0))
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      e 0 =ᵐ[(MeasureTheory.volume : Measure E3)] fun x =>
        c * Work.BoseK15.corpusBox.thetaFun ℓ x)
    {Θ : 𝕏 n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C)
    {j l : Fin n} (hjl : j ≠ l) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        star (PiF[e, ℓ, Θ, j] x) * (Θ x - sA e l Θ x))
      = ((∫ x in Submission.BoseGases.abox n ℓ, ‖XF[e, ℓ, Θ, j, l] x‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨hPm, hPb⟩ := PiFun_meas_bdd hℓ hmeas hbdd hsupp hΘm hΘb j
  obtain ⟨CP, hCP⟩ := hPb
  obtain ⟨hAlPm, hAlPb⟩ := sA_meas_bdd hmeas hbdd hsupp hPm ⟨CP, hCP⟩ l
  obtain ⟨hAlm, hAlb⟩ := sA_meas_bdd hmeas hbdd hsupp hΘm hΘb l
  obtain ⟨hXm, hXb⟩ := XFun_meas_bdd hℓ hmeas hbdd hsupp hΘm hΘb j l
  obtain ⟨CX, hCX⟩ := hXb
  obtain ⟨hAjm, hAjb⟩ := sA_meas_bdd hmeas hbdd hsupp hΘm hΘb j
  obtain ⟨hPjm, hPjb⟩ := sP_meas_bdd hℓ j hΘm hΘb
  obtain ⟨hAjXm, hAjXb⟩ := sA_meas_bdd hmeas hbdd hsupp hXm ⟨CX, hCX⟩ j
  obtain ⟨hPjXm, hPjXb⟩ := sP_meas_bdd hℓ j hXm ⟨CX, hCX⟩
  have hAzero := X_A_zero (ℓ := ℓ) hℓ hmeas hbdd hsupp horth hΘm hΘb j l
  have hAfix := X_A_fix (ℓ := ℓ) hℓ hmeas hbdd hsupp hml horth hc hΘm hΘb hjl
  have hPzero := X_P_zero (ℓ := ℓ) hℓ hmeas hbdd hsupp hml horth hc hΘm hΘb hjl
  have hI1 := integrableOn_star_mul hℓ hPm ⟨CP, hCP⟩ hΘm hΘb
  have hI2 := integrableOn_star_mul hℓ hPm ⟨CP, hCP⟩ hAlm hAlb
  have hI3 := integrableOn_star_mul hℓ hAlPm hAlPb hΘm hΘb
  have hI4 := integrableOn_star_mul hℓ hXm ⟨CX, hCX⟩ hPm ⟨CP, hCP⟩
  have hI5 := integrableOn_star_mul hℓ hXm ⟨CX, hCX⟩ hAlPm hAlPb
  have hI6 := integrableOn_star_mul hℓ hXm ⟨CX, hCX⟩ hAjm hAjb
  have hI7 := integrableOn_star_mul hℓ hXm ⟨CX, hCX⟩ hPjm hPjb
  have hI9 := integrableOn_star_mul hℓ hAjXm hAjXb hΘm hΘb
  have hI10 := integrableOn_star_mul hℓ hPjXm hPjXb hΘm hΘb
  have step1 : (∫ x in Submission.BoseGases.abox n ℓ,
        star (PiF[e, ℓ, Θ, j] x) * (Θ x - sA e l Θ x))
      = ∫ x in Submission.BoseGases.abox n ℓ, star (XF[e, ℓ, Θ, j, l] x) * Θ x := by
    calc (∫ x in Submission.BoseGases.abox n ℓ,
          star (PiF[e, ℓ, Θ, j] x) * (Θ x - sA e l Θ x))
        = ∫ x in Submission.BoseGases.abox n ℓ,
            (star (PiF[e, ℓ, Θ, j] x) * Θ x - star (PiF[e, ℓ, Θ, j] x) * sA e l Θ x) := by
          refine int_congr_ae_box ?_
          filter_upwards with x
          ring
      _ = (∫ x in Submission.BoseGases.abox n ℓ, star (PiF[e, ℓ, Θ, j] x) * Θ x)
          - (∫ x in Submission.BoseGases.abox n ℓ, star (PiF[e, ℓ, Θ, j] x) * sA e l Θ x) :=
          integral_sub hI1 hI2
      _ = (∫ x in Submission.BoseGases.abox n ℓ, star (PiF[e, ℓ, Θ, j] x) * Θ x)
          - (∫ x in Submission.BoseGases.abox n ℓ, star (sA e l PiF[e, ℓ, Θ, j] x) * Θ x) := by
          rw [← slotProj1_box_adjoint hℓ hmeas hbdd hsupp l hPm ⟨CP, hCP⟩ hΘm hΘb]
      _ = (∫ x in Submission.BoseGases.abox n ℓ,
            (star (PiF[e, ℓ, Θ, j] x) * Θ x - star (sA e l PiF[e, ℓ, Θ, j] x) * Θ x)) :=
          (integral_sub hI1 hI3).symm
      _ = ∫ x in Submission.BoseGases.abox n ℓ, star (XF[e, ℓ, Θ, j, l] x) * Θ x := by
          refine int_congr_ae_box ?_
          filter_upwards with x
          simp only [Pi.sub_apply, star_sub, sub_mul]
  have step2 : (∫ x in Submission.BoseGases.abox n ℓ,
        star (XF[e, ℓ, Θ, j, l] x) * XF[e, ℓ, Θ, j, l] x)
      = ∫ x in Submission.BoseGases.abox n ℓ, star (XF[e, ℓ, Θ, j, l] x) * Θ x := by
    calc (∫ x in Submission.BoseGases.abox n ℓ,
          star (XF[e, ℓ, Θ, j, l] x) * XF[e, ℓ, Θ, j, l] x)
        = ∫ x in Submission.BoseGases.abox n ℓ,
            (star (XF[e, ℓ, Θ, j, l] x) * PiF[e, ℓ, Θ, j] x
              - star (XF[e, ℓ, Θ, j, l] x) * sA e l PiF[e, ℓ, Θ, j] x) := by
          refine int_congr_ae_box ?_
          filter_upwards with x
          ring
      _ = (∫ x in Submission.BoseGases.abox n ℓ, star (XF[e, ℓ, Θ, j, l] x) * PiF[e, ℓ, Θ, j] x)
          - (∫ x in Submission.BoseGases.abox n ℓ,
              star (XF[e, ℓ, Θ, j, l] x) * sA e l PiF[e, ℓ, Θ, j] x) :=
          integral_sub hI4 hI5
      _ = (∫ x in Submission.BoseGases.abox n ℓ, star (XF[e, ℓ, Θ, j, l] x) * PiF[e, ℓ, Θ, j] x)
          - (∫ x in Submission.BoseGases.abox n ℓ,
              star (sA e l XF[e, ℓ, Θ, j, l] x) * PiF[e, ℓ, Θ, j] x) := by
          rw [← slotProj1_box_adjoint hℓ hmeas hbdd hsupp l hXm ⟨CX, hCX⟩ hPm ⟨CP, hCP⟩]
      _ = (∫ x in Submission.BoseGases.abox n ℓ, star (XF[e, ℓ, Θ, j, l] x) * PiF[e, ℓ, Θ, j] x)
          - (∫ x in Submission.BoseGases.abox n ℓ,
              star ((0 : 𝕏 n → ℂ) x) * PiF[e, ℓ, Θ, j] x) := by
          rw [int_star_congr_box hAzero]
      _ = ((∫ x in Submission.BoseGases.abox n ℓ, star (XF[e, ℓ, Θ, j, l] x) * sA e j Θ x)
            - (∫ x in Submission.BoseGases.abox n ℓ,
                star (XF[e, ℓ, Θ, j, l] x) * sP ℓ j Θ x)) := by
          have hzero : (∫ x in Submission.BoseGases.abox n ℓ,
              star ((0 : 𝕏 n → ℂ) x) * PiF[e, ℓ, Θ, j] x) = 0 := by simp
          have hsp : (∫ x in Submission.BoseGases.abox n ℓ,
                star (XF[e, ℓ, Θ, j, l] x) * PiF[e, ℓ, Θ, j] x)
              = ∫ x in Submission.BoseGases.abox n ℓ,
                  (star (XF[e, ℓ, Θ, j, l] x) * sA e j Θ x
                    - star (XF[e, ℓ, Θ, j, l] x) * sP ℓ j Θ x) := by
            refine int_congr_ae_box ?_
            filter_upwards with x
            ring
          rw [hzero, hsp, integral_sub hI6 hI7]
          ring
      _ = ((∫ x in Submission.BoseGases.abox n ℓ, star (sA e j XF[e, ℓ, Θ, j, l] x) * Θ x)
            - (∫ x in Submission.BoseGases.abox n ℓ,
                star (sP ℓ j XF[e, ℓ, Θ, j, l] x) * Θ x)) := by
          rw [← slotProj1_box_adjoint hℓ hmeas hbdd hsupp j hXm ⟨CX, hCX⟩ hΘm hΘb,
            ← aPC_box_adjoint hℓ j hXm ⟨CX, hCX⟩ hΘm hΘb]
      _ = ((∫ x in Submission.BoseGases.abox n ℓ, star (XF[e, ℓ, Θ, j, l] x) * Θ x)
            - (∫ x in Submission.BoseGases.abox n ℓ,
                star ((0 : 𝕏 n → ℂ) x) * Θ x)) := by
          rw [int_star_congr_box hAfix, int_star_congr_box hPzero]
      _ = ((∫ x in Submission.BoseGases.abox n ℓ, star (XF[e, ℓ, Θ, j, l] x) * Θ x) - 0) := by
          simp
      _ = ∫ x in Submission.BoseGases.abox n ℓ, star (XF[e, ℓ, Θ, j, l] x) * Θ x := by ring
  have step3 : (∫ x in Submission.BoseGases.abox n ℓ,
        star (XF[e, ℓ, Θ, j, l] x) * XF[e, ℓ, Θ, j, l] x)
      = ((∫ x in Submission.BoseGases.abox n ℓ, ‖XF[e, ℓ, Θ, j, l] x‖ ^ 2 : ℝ) : ℂ) := by
    rw [show (∫ x in Submission.BoseGases.abox n ℓ,
          star (XF[e, ℓ, Θ, j, l] x) * XF[e, ℓ, Θ, j, l] x)
        = ∫ x in Submission.BoseGases.abox n ℓ, ((‖XF[e, ℓ, Θ, j, l] x‖ ^ 2 : ℝ) : ℂ)
        from int_congr_ae_box (Filter.Eventually.of_forall
          (fun x => star_mul_self_eq (XF[e, ℓ, Θ, j, l] x)))]
    exact integral_ofReal
  rw [step1, ← step2, step3]

/-! ## 6. Integrability of the cross summands -/

/-- The `(j,l)` summand of the cross term is integrable on the box. -/
lemma integrableOn_pi_cross {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Θ : 𝕏 n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) (j l : Fin n) :
    IntegrableOn (fun x => star (PiF[e, ℓ, Θ, j] x) * (Θ x - sA e l Θ x))
      (Submission.BoseGases.abox n ℓ) := by
  have hCΘ : ∀ x : 𝕏 n, ‖Θ x‖ ≤ hΘb.choose := hΘb.choose_spec
  obtain ⟨hPm, hPb⟩ := PiFun_meas_bdd hℓ hmeas hbdd hsupp hΘm hΘb j
  obtain ⟨hAlm, hAlb⟩ := sA_meas_bdd hmeas hbdd hsupp hΘm hΘb l
  obtain ⟨CA, hCA⟩ := hAlb
  exact integrableOn_star_mul hℓ hPm hPb (hΘm.sub hAlm) ⟨hΘb.choose + CA, fun x =>
    le_trans (norm_sub_le _ _) (add_le_add (hCΘ x) (hCA x))⟩

/-- The inner `l`-sum of the cross term is integrable on the box. -/
lemma integrableOn_pi_cross_sum {m n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → E3 → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    {Θ : 𝕏 n → ℂ} (hΘm : Measurable Θ) (hΘb : ∃ C, ∀ x, ‖Θ x‖ ≤ C) (j : Fin n) :
    IntegrableOn (fun x => ∑ l : Fin n, star (PiF[e, ℓ, Θ, j] x) * (Θ x - sA e l Θ x))
      (Submission.BoseGases.abox n ℓ) :=
  integrable_finsetSum Finset.univ (fun l _ =>
    integrableOn_pi_cross hℓ hmeas hbdd hsupp hΘm hΘb j l)

/-! ## 7. The target -/

theorem nCfSecondMomentLe {m n : ℕ} [NeZero m] {ℓ : ℝ} (hℓ : 0 < ℓ)
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hmeas : ∀ l, Measurable (e l)) (hbdd : ∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (horth : ∀ l l', (∫ z : EuclideanSpace ℝ (Fin 3), star (e l z) * e l' z)
      = (if l = l' then (1 : ℂ) else 0))
    (hMemLp : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      e 0 =ᵐ[MeasureTheory.volume] fun x => c * Work.BoseK15.corpusBox.thetaFun ℓ x)
    {Θ : Submission.BoseGases.X n → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (hΘsupp : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ) :
    (∫ x in Submission.BoseGases.abox n ℓ,
        ‖∑ j : Fin n, (Work.BoseBoxFock.slotProj1 e j Θ x
          - Work.BoseBoxFock.aPC ℓ j Θ x)‖ ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, ‖nCf ℓ Θ x‖ ^ 2 := by
  classical
  set G : 𝕏 n → ℂ := fun x => ∑ j : Fin n, (sA e j Θ x - sP ℓ j Θ x) with hG
  set Hf : 𝕏 n → ℂ := nCf ℓ Θ with hH
  set Rf : 𝕏 n → ℂ := fun x => ∑ l : Fin n, (Θ x - sA e l Θ x) with hR
  have hCΘ : ∀ x : 𝕏 n, ‖Θ x‖ ≤ hΘb.choose := hΘb.choose_spec
  -- ## measurability and bounds
  have hAall : ∀ j : Fin n, Measurable (sA e j Θ) ∧ ∃ C, ∀ x, ‖sA e j Θ x‖ ≤ C :=
    fun j => sA_meas_bdd hmeas hbdd hsupp hΘm hΘb j
  have hPall : ∀ j : Fin n, Measurable (sP ℓ j Θ) ∧ ∃ C, ∀ x, ‖sP ℓ j Θ x‖ ≤ C :=
    fun j => sP_meas_bdd hℓ j hΘm hΘb
  have hmG : Measurable G := by
    rw [hG]
    exact Finset.measurable_sum Finset.univ (fun j _ => (hAall j).1.sub (hPall j).1)
  have hbG : ∃ C, ∀ x, ‖G x‖ ≤ C := by
    have h : ∀ j : Fin n, ∃ C, ∀ x, ‖sA e j Θ x - sP ℓ j Θ x‖ ≤ C := by
      intro j
      obtain ⟨CA, hCA⟩ := (hAall j).2
      obtain ⟨CP, hCP⟩ := (hPall j).2
      exact ⟨CA + CP, fun x => le_trans (norm_sub_le _ _) (add_le_add (hCA x) (hCP x))⟩
    choose C hC using h
    refine ⟨∑ j : Fin n, C j, fun x => ?_⟩
    rw [hG]
    exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun j _ => hC j x))
  have hmR : Measurable Rf := by
    rw [hR]
    exact Finset.measurable_sum Finset.univ (fun j _ => hΘm.sub (hAall j).1)
  have hbR : ∃ C, ∀ x, ‖Rf x‖ ≤ C := by
    have h : ∀ j : Fin n, ∃ C, ∀ x, ‖Θ x - sA e j Θ x‖ ≤ C := by
      intro j
      obtain ⟨CA, hCA⟩ := (hAall j).2
      exact ⟨hΘb.choose + CA, fun x => le_trans (norm_sub_le _ _) (add_le_add (hCΘ x) (hCA x))⟩
    choose C hC using h
    refine ⟨∑ j : Fin n, C j, fun x => ?_⟩
    rw [hR]
    exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun j _ => hC j x))
  have hmH : Measurable Hf := by
    rw [hH]
    exact Finset.measurable_sum Finset.univ (fun j _ => hΘm.sub (hPall j).1)
  have hbH : ∃ C, ∀ x, ‖Hf x‖ ≤ C := by
    have h : ∀ j : Fin n, ∃ C, ∀ x, ‖Θ x - sP ℓ j Θ x‖ ≤ C := by
      intro j
      obtain ⟨CP, hCP⟩ := (hPall j).2
      exact ⟨hΘb.choose + CP, fun x => le_trans (norm_sub_le _ _) (add_le_add (hCΘ x) (hCP x))⟩
    choose C hC using h
    refine ⟨∑ j : Fin n, C j, fun x => ?_⟩
    rw [hH]
    exact le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun j _ => hC j x))
  -- ## the pointwise decomposition and the key identity
  have hpt : ∀ x, Hf x = G x + Rf x := by
    intro x
    simp only [hH, hG, hR, nCf]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hkey : ∀ x, ‖Hf x‖ ^ 2 - ‖G x‖ ^ 2 = 2 * (star (G x) * Rf x).re + ‖Rf x‖ ^ 2 := by
    intro x
    have h := normSq_add_sub_normSq (G x) (Rf x)
    rwa [← hpt x] at h
  -- ## integrability
  obtain ⟨CG, hCG⟩ := hbG
  obtain ⟨CR, hCR⟩ := hbR
  obtain ⟨CH, hCH⟩ := hbH
  have hCG0 : 0 ≤ CG := le_trans (norm_nonneg _) (hCG 0)
  have hCH0 : 0 ≤ CH := le_trans (norm_nonneg _) (hCH 0)
  have hCR0 : 0 ≤ CR := le_trans (norm_nonneg _) (hCR 0)
  have hintH : IntegrableOn (fun x => ‖Hf x‖ ^ 2) (Submission.BoseGases.abox n ℓ) :=
    integrableOn_box_of_bound hℓ (hmH.norm.pow_const 2).aestronglyMeasurable
      (C := CH ^ 2) (fun x => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hCH x) 2)
  have hintG : IntegrableOn (fun x => ‖G x‖ ^ 2) (Submission.BoseGases.abox n ℓ) :=
    integrableOn_box_of_bound hℓ (hmG.norm.pow_const 2).aestronglyMeasurable
      (C := CG ^ 2) (fun x => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hCG x) 2)
  have hintR : IntegrableOn (fun x => ‖Rf x‖ ^ 2) (Submission.BoseGases.abox n ℓ) :=
    integrableOn_box_of_bound hℓ (hmR.norm.pow_const 2).aestronglyMeasurable
      (C := CR ^ 2) (fun x => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hCR x) 2)
  have hintK : IntegrableOn
      (fun x => 2 * (star (G x) * Rf x).re + ‖Rf x‖ ^ 2) (Submission.BoseGases.abox n ℓ) := by
    refine integrableOn_box_of_bound hℓ ?_ (C := 2 * (CG * CR) + CR ^ 2) (fun x => ?_)
    · exact (((hmG.aestronglyMeasurable.star.mul hmR.aestronglyMeasurable).re.const_mul 2).add
        (hmR.norm.pow_const 2).aestronglyMeasurable)
    · have h1 : ‖star (G x) * Rf x‖ ≤ CG * CR := by
        rw [norm_mul, norm_star]
        exact mul_le_mul (hCG x) (hCR x) (norm_nonneg _) hCG0
      have h3 : ‖(star (G x) * Rf x).re‖ ≤ CG * CR := by
        rw [Real.norm_eq_abs]
        exact le_trans (Complex.abs_re_le_norm _) h1
      have h4 : ‖Rf x‖ ^ 2 ≤ CR ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hCR x) 2
      have h5 : ‖2 * (star (G x) * Rf x).re‖ = 2 * ‖(star (G x) * Rf x).re‖ := by
        rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      have h6 : ‖‖Rf x‖ ^ 2‖ = ‖Rf x‖ ^ 2 := Real.norm_of_nonneg (by positivity)
      calc ‖2 * (star (G x) * Rf x).re + ‖Rf x‖ ^ 2‖
          ≤ ‖2 * (star (G x) * Rf x).re‖ + ‖‖Rf x‖ ^ 2‖ := norm_add_le _ _
        _ = 2 * ‖(star (G x) * Rf x).re‖ + ‖Rf x‖ ^ 2 := by rw [h5, h6]
        _ ≤ 2 * (CG * CR) + CR ^ 2 := by linarith
  have hintX : IntegrableOn (fun x => star (G x) * Rf x) (Submission.BoseGases.abox n ℓ) :=
    integrableOn_star_mul hℓ hmG ⟨CG, hCG⟩ hmR ⟨CR, hCR⟩
  -- ## the cross term is nonnegative
  have hcross : 0 ≤ (∫ x in Submission.BoseGases.abox n ℓ, star (G x) * Rf x).re := by
    have hsplit : (∫ x in Submission.BoseGases.abox n ℓ, star (G x) * Rf x)
        = ∑ j : Fin n, ∑ l : Fin n,
            ∫ x in Submission.BoseGases.abox n ℓ,
              star (PiF[e, ℓ, Θ, j] x) * (Θ x - sA e l Θ x) := by
      have hpt2 : ∀ x, star (G x) * Rf x
          = ∑ j : Fin n, ∑ l : Fin n,
              star (PiF[e, ℓ, Θ, j] x) * (Θ x - sA e l Θ x) := by
        intro x
        have h1 : star (G x) = ∑ j : Fin n, star (PiF[e, ℓ, Θ, j] x) := by
          rw [hG]
          simp only [star_sum]
        have h2 : Rf x = ∑ l : Fin n, (Θ x - sA e l Θ x) := by
          rw [hR]
        rw [h1, h2, Finset.sum_mul]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.mul_sum]
      calc (∫ x in Submission.BoseGases.abox n ℓ, star (G x) * Rf x)
          = ∫ x in Submission.BoseGases.abox n ℓ,
              (∑ j : Fin n, ∑ l : Fin n,
                star (PiF[e, ℓ, Θ, j] x) * (Θ x - sA e l Θ x)) :=
            int_congr_ae_box (Filter.Eventually.of_forall hpt2)
        _ = ∑ j : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
              (∑ l : Fin n, star (PiF[e, ℓ, Θ, j] x) * (Θ x - sA e l Θ x)) :=
            integral_finsetSum Finset.univ
              (fun j _ => integrableOn_pi_cross_sum hℓ hmeas hbdd hsupp hΘm hΘb j)
        _ = ∑ j : Fin n, ∑ l : Fin n,
              ∫ x in Submission.BoseGases.abox n ℓ,
                star (PiF[e, ℓ, Θ, j] x) * (Θ x - sA e l Θ x) :=
            Finset.sum_congr rfl (fun j _ => integral_finsetSum Finset.univ
              (fun l _ => integrableOn_pi_cross hℓ hmeas hbdd hsupp hΘm hΘb j l))
    rw [hsplit, Complex.re_sum]
    refine Finset.sum_nonneg (fun j _ => ?_)
    rw [Complex.re_sum]
    refine Finset.sum_nonneg (fun l _ => ?_)
    by_cases hjl : j = l
    · subst hjl
      rw [self_cross_zero hℓ hmeas hbdd hsupp hMemLp horth hc hΘm hΘb j]
      simp
    · rw [cross_int_eq hℓ hmeas hbdd hsupp hMemLp horth hc hΘm hΘb hjl]
      rw [Complex.ofReal_re]
      exact integral_nonneg (fun x => by positivity)
  -- ## assembly
  have hdiff_eq : (∫ x in Submission.BoseGases.abox n ℓ, ‖Hf x‖ ^ 2)
      - (∫ x in Submission.BoseGases.abox n ℓ, ‖G x‖ ^ 2)
      = ∫ x in Submission.BoseGases.abox n ℓ,
          (2 * (star (G x) * Rf x).re + ‖Rf x‖ ^ 2) := by
    rw [← integral_sub hintH hintG]
    exact int_congr_ae_box (n := n) (ℓ := ℓ)
      (F := fun a => ‖Hf a‖ ^ 2 - ‖G a‖ ^ 2)
      (G := fun a => 2 * (star (G a) * Rf a).re + ‖Rf a‖ ^ 2)
      (Filter.Eventually.of_forall hkey)
  have hnn : 0 ≤ ∫ x in Submission.BoseGases.abox n ℓ,
      (2 * (star (G x) * Rf x).re + ‖Rf x‖ ^ 2) := by
    have hintXre : IntegrableOn (fun x => (star (G x) * Rf x).re)
        (Submission.BoseGases.abox n ℓ) := hintX.re
    have e1 : (∫ x in Submission.BoseGases.abox n ℓ,
          (2 * (star (G x) * Rf x).re + ‖Rf x‖ ^ 2))
        = 2 * (∫ x in Submission.BoseGases.abox n ℓ, (star (G x) * Rf x).re)
          + ∫ x in Submission.BoseGases.abox n ℓ, ‖Rf x‖ ^ 2 := by
      have h2a := integral_add (hintXre.const_mul 2) hintR
      have h2b : (∫ x in Submission.BoseGases.abox n ℓ, 2 * (star (G x) * Rf x).re)
          = 2 * (∫ x in Submission.BoseGases.abox n ℓ, (star (G x) * Rf x).re) :=
        integral_const_mul 2 _
      rw [h2a, h2b]
    rw [e1]
    have h1 : 0 ≤ ∫ x in Submission.BoseGases.abox n ℓ, (star (G x) * Rf x).re := by
      have hr : (∫ x in Submission.BoseGases.abox n ℓ, (star (G x) * Rf x).re)
          = (∫ x in Submission.BoseGases.abox n ℓ, star (G x) * Rf x).re := integral_re hintX
      rw [hr]
      exact hcross
    have h2 : 0 ≤ ∫ x in Submission.BoseGases.abox n ℓ, ‖Rf x‖ ^ 2 :=
      integral_nonneg (fun x => by positivity)
    linarith
  have hmain : (∫ x in Submission.BoseGases.abox n ℓ, ‖G x‖ ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox n ℓ, ‖Hf x‖ ^ 2 := by
    linarith [hdiff_eq, hnn]
  simpa only [hG, hH] using hmain

end Work.BoseBoxFock.PotCubicLowBandAux
