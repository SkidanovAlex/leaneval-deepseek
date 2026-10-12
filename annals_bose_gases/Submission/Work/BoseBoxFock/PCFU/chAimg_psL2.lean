import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Order.Group.Lattice
import Submission.Work.BoseBoxFock.PCFU.aQ_aP_sq_le
import Submission.Work.BoseBoxFock.PCFU.taperAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.PCFU.chAimg_psL2`

The `L²`-slot bound behind the `chAimg` piece, in the form needed by the `PCFU` chain: for a
measurable, everywhere bounded state `Θ` in `L²(abox (m+1) ℓ)` and distinct slots `i ≠ j`,

    ∫_{r ∈ abox m ℓ} (∫_{u ∈ acube ℓ} |Qⱼ Pᵢ Θ (kcInsN m i (0,r)[j ↦ u])|)² ≤ ℓ³ ∫_{abox (m+1) ℓ} Θ²,

where `Pᵢ` is the corpus condensate projection (`Submission.BoseGases.aP`) and `Qᵢ = 1 − Pᵢ`.

## Proof

Set `Γ := Qⱼ Pᵢ Θ` and `G x := (∫_{u ∈ acube ℓ} |Γ (x[j ↦ u])|)²`.  The state `Γ` is constant in
the slot `i` (`aP_const_in_coord'` + `aP_const_of_const_in_coord`), hence so is `G`; the peel of a
slot-constant function (`psL2_peel_collapse`, proved here) therefore turns the target's LHS into
`(1/ℓ³)∫_{abox (m+1) ℓ} G`.  Cauchy–Schwarz in the `j`-slot
(`Work.BoseFixB1S.sq_integral_le_measure_mul_integral_sq`) gives `G ≤ ℓ³ H` with
`H x := ∫_{u ∈ acube ℓ} Γ (x[j ↦ u])²`, and the slot-constant peel applied to `H` (constant in the
slot `j`, since the update overwrites it) together with the corpus peel `abox_integral_peel` gives
`∫_{abox (m+1) ℓ} H = ℓ³ ∫_{abox (m+1) ℓ} Γ²`.  Finally `Qⱼ ∘ Pᵢ` contracts the box `L²`
(`Work.BoseBoxFock.PCFU.aQ_aP_sq_le`): `∫_{abox} Γ² ≤ ∫_{abox} Θ²`.  Chaining,
`ℓ³ · LHS = ∫ G ≤ ℓ³ ∫ H = ℓ⁶ ∫ Γ² ≤ ℓ⁶ ∫ Θ²`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock.PCFU

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-- **The peel of a slot-constant function**: if `F` does not depend on the value of its `i`-th
slot, then its integral over `abox (m+1) ℓ` is `ℓ³` times the integral, over `abox m ℓ`, of the
values of `F` at the configurations whose `i`-th slot is `0`. -/
theorem psL2_peel_collapse {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin (m + 1))
    {F : Submission.BoseGases.X (m + 1) → ℝ}
    (hindep : ∀ (x : Submission.BoseGases.X (m + 1)) (z : E3), F (Function.update x i z) = F x)
    (hF : IntegrableOn F (Submission.BoseGases.abox (m + 1) ℓ) volume) :
    (∫ x in Submission.BoseGases.abox (m + 1) ℓ, F x)
      = ℓ ^ 3 * ∫ r in Submission.BoseGases.abox m ℓ,
          F (Submission.BoseGases.kcInsN m i (0, r)) := by
  rw [Submission.BoseGases.abox_integral_peel (n := m) (ℓ := ℓ) i F hF]
  have hcongr : ∀ r : Submission.BoseGases.X m,
      (∫ y : E3 in Submission.BoseGases.acube ℓ, F (Submission.BoseGases.kcInsN m i (y, r)))
        = F (Submission.BoseGases.kcInsN m i (0, r)) * ℓ ^ 3 := by
    intro r
    rw [show (∫ y : E3 in Submission.BoseGases.acube ℓ, F (Submission.BoseGases.kcInsN m i (y, r)))
        = ∫ y : E3 in Submission.BoseGases.acube ℓ, F (Submission.BoseGases.kcInsN m i (0, r)) from by
      apply integral_congr_ae
      filter_upwards with y
      rw [kcInsN_eq_update]
      exact hindep (Submission.BoseGases.kcInsN m i (0, r)) y]
    exact Submission.BoseGases.integral_const_acube ℓ hℓ (F (Submission.BoseGases.kcInsN m i (0, r)))
  have hstep : (∫ r in Submission.BoseGases.abox m ℓ,
        (∫ y : E3 in Submission.BoseGases.acube ℓ, F (Submission.BoseGases.kcInsN m i (y, r))))
      = ∫ r in Submission.BoseGases.abox m ℓ,
          F (Submission.BoseGases.kcInsN m i (0, r)) * ℓ ^ 3 := by
    apply integral_congr_ae
    filter_upwards with r
    exact hcongr r
  rw [hstep, MeasureTheory.integral_mul_const]
  ring

/-- `(ν univ).toReal = ℓ³` for the one-particle measure `ν = volume ↾ acube ℓ`. -/
private lemma acube_univ_toReal_psL2 {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) Set.univ).toReal = ℓ ^ 3 := by
  rw [Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le,
    ENNReal.toReal_ofReal (by positivity)]

theorem chAimg_psL2 {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin (m + 1)} (hij : i ≠ j)
    {Θ : Submission.BoseGases.X (m + 1) → ℝ} (hΘm : Measurable Θ) {B : ℝ} (hB : 0 ≤ B)
    (hΘb : ∀ x, |Θ x| ≤ B)
    (hΘmem : MeasureTheory.MemLp Θ 2
      ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X (m + 1))).restrict
        (Submission.BoseGases.abox (m + 1) ℓ))) :
    (∫ r : Submission.BoseGases.X m,
        (∫ u in Submission.BoseGases.acube ℓ,
            |Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ)
              (Function.update (Submission.BoseGases.kcInsN m i (0, r)) j u)|) ^ 2
      ∂((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X m)).restrict
        (Submission.BoseGases.abox m ℓ)))
      ≤ ℓ ^ 3 * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, (Θ x) ^ 2 := by
  classical
  set Γ : Submission.BoseGases.X (m + 1) → ℝ :=
    Submission.BoseGases.aQ ℓ j (Submission.BoseGases.aP ℓ i Θ) with hΓdef
  -- ## the state `Γ = Qⱼ Pᵢ Θ`
  have hΓm : Measurable Γ := by
    rw [hΓdef]
    exact Weak.aQ_measurable j (Weak.aP_measurable i hΘm)
  have hΓb : ∀ x, |Γ x| ≤ 2 * B := by
    rw [hΓdef]
    exact Weak.aQ_abs_le hℓ j hB (Weak.aP_abs_le hℓ i hB hΘb)
  have hΓconst : ∀ (x : Submission.BoseGases.X (m + 1)) (z : E3),
      Γ (Function.update x i z) = Γ x := by
    intro x z
    have hP : ∀ (y : Submission.BoseGases.X (m + 1)) (w : E3),
        Submission.BoseGases.aP ℓ i Θ (Function.update y i w) = Submission.BoseGases.aP ℓ i Θ y :=
      fun y w => aP_const_in_coord' i Θ y w
    have hPj : Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) (Function.update x i z)
        = Submission.BoseGases.aP ℓ j (Submission.BoseGases.aP ℓ i Θ) x :=
      aP_const_of_const_in_coord (ℓ := ℓ) (i := i) (j := j) hij hP x z
    rw [hΓdef]
    simp only [Submission.BoseGases.aQ, hP x z, hPj]
  -- ## the function `G x = (∫_{acube} |Γ (x[j ↦ ·])|)²`
  set G : Submission.BoseGases.X (m + 1) → ℝ :=
    fun x => (∫ u in Submission.BoseGases.acube ℓ, |Γ (Function.update x j u)|) ^ 2 with hGdef
  have hGconst : ∀ (x : Submission.BoseGases.X (m + 1)) (z : E3),
      G (Function.update x i z) = G x := by
    intro x z
    have hinner : (fun u : E3 => |Γ (Function.update (Function.update x i z) j u)|)
        = fun u : E3 => |Γ (Function.update x j u)| := by
      funext u
      rw [Function.update_comm hij z u x, hΓconst (Function.update x j u) z]
    simp only [hGdef, hinner]
  have hGmeas : AEStronglyMeasurable G
      ((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
        (Submission.BoseGases.abox (m + 1) ℓ)) := by
    have huncurry : StronglyMeasurable
        (fun p : Submission.BoseGases.X (m + 1) × E3 => |Γ (Function.update p.1 j p.2)|) :=
      ((hΓm.comp (by fun_prop : Measurable fun p : Submission.BoseGases.X (m + 1) × E3 =>
        Function.update p.1 j p.2)).abs).stronglyMeasurable
    haveI : SFinite ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := inferInstance
    have h := huncurry.integral_prod_right'
      (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
    have hmeas : Measurable (fun x : Submission.BoseGases.X (m + 1) =>
        (∫ u in Submission.BoseGases.acube ℓ, |Γ (Function.update x j u)|) ^ 2) := by
      have h1 : Measurable (fun x : Submission.BoseGases.X (m + 1) =>
          ∫ u in Submission.BoseGases.acube ℓ, |Γ (Function.update x j u)|) := by
        simpa using h.measurable
      exact h1.pow_const 2
    rw [hGdef]
    exact hmeas.aestronglyMeasurable.restrict
  have hGb : ∀ x, |G x| ≤ (2 * B * ℓ ^ 3) ^ 2 := by
    intro x
    have h1 : (∫ u in Submission.BoseGases.acube ℓ, |Γ (Function.update x j u)|)
        ≤ 2 * B * ℓ ^ 3 := by
      have h := integral_mono_of_nonneg
        (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
        (f := fun u : E3 => |Γ (Function.update x j u)|) (g := fun _ : E3 => 2 * B)
        (ae_of_all _ (fun u => abs_nonneg _))
        (integrable_const (2 * B))
        (ae_of_all _ (fun u => hΓb _))
      rwa [Submission.BoseGases.integral_const_acube ℓ hℓ (2 * B)] at h
    have h0 : 0 ≤ (∫ u in Submission.BoseGases.acube ℓ, |Γ (Function.update x j u)|) :=
      integral_nonneg (fun u => abs_nonneg _)
    rw [hGdef]
    show |(∫ u in Submission.BoseGases.acube ℓ, |Γ (Function.update x j u)|) ^ 2|
        ≤ (2 * B * ℓ ^ 3) ^ 2
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ h0 h1 2
  have hGint : IntegrableOn G (Submission.BoseGases.abox (m + 1) ℓ) volume := by
    refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top (m + 1) ℓ hℓ.le) hGmeas
      ((2 * B * ℓ ^ 3) ^ 2) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact hGb x
  -- ## the function `H x = ∫_{acube} (Γ (x[j ↦ ·]))²`
  set H : Submission.BoseGases.X (m + 1) → ℝ :=
    fun x => ∫ u in Submission.BoseGases.acube ℓ, (Γ (Function.update x j u)) ^ 2 with hHdef
  have hHconst : ∀ (x : Submission.BoseGases.X (m + 1)) (z : E3),
      H (Function.update x j z) = H x := by
    intro x z
    simp only [hHdef]
    apply integral_congr_ae
    filter_upwards with u
    rw [Function.update_idem]
  have hHmeas : AEStronglyMeasurable H
      ((volume : Measure (Submission.BoseGases.X (m + 1))).restrict
        (Submission.BoseGases.abox (m + 1) ℓ)) := by
    have huncurry : StronglyMeasurable
        (fun p : Submission.BoseGases.X (m + 1) × E3 => (Γ (Function.update p.1 j p.2)) ^ 2) :=
      ((hΓm.comp (by fun_prop : Measurable fun p : Submission.BoseGases.X (m + 1) × E3 =>
        Function.update p.1 j p.2)).pow_const 2).stronglyMeasurable
    haveI : SFinite ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := inferInstance
    have h := huncurry.integral_prod_right'
      (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
    have hmeas : Measurable (fun x : Submission.BoseGases.X (m + 1) =>
        ∫ u in Submission.BoseGases.acube ℓ, (Γ (Function.update x j u)) ^ 2) := by
      simpa using h.measurable
    rw [hHdef]
    exact hmeas.aestronglyMeasurable.restrict
  have hHb : ∀ x, |H x| ≤ (2 * B) ^ 2 * ℓ ^ 3 := by
    intro x
    have h1 : H x ≤ (2 * B) ^ 2 * ℓ ^ 3 := by
      rw [hHdef]
      have h := integral_mono_of_nonneg
        (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
        (f := fun u : E3 => (Γ (Function.update x j u)) ^ 2)
        (g := fun _ : E3 => (2 * B) ^ 2)
        (ae_of_all _ (fun u => sq_nonneg _))
        (integrable_const ((2 * B) ^ 2))
        (ae_of_all _ (fun u => by
          calc (Γ (Function.update x j u)) ^ 2 = |Γ (Function.update x j u)| ^ 2 := (sq_abs _).symm
            _ ≤ (2 * B) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hΓb _) 2))
      rwa [Submission.BoseGases.integral_const_acube ℓ hℓ ((2 * B) ^ 2)] at h
    have h2 : 0 ≤ H x := by rw [hHdef]; exact integral_nonneg (fun u => sq_nonneg _)
    rw [abs_of_nonneg h2]
    exact h1
  have hHint : IntegrableOn H (Submission.BoseGases.abox (m + 1) ℓ) volume := by
    refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top (m + 1) ℓ hℓ.le) hHmeas
      ((2 * B) ^ 2 * ℓ ^ 3) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs]
    exact hHb x
  have hΓ2int : IntegrableOn (fun x : Submission.BoseGases.X (m + 1) => (Γ x) ^ 2)
      (Submission.BoseGases.abox (m + 1) ℓ) volume := by
    refine IntegrableOn.of_bound (Submission.BoseGases.abox_lt_top (m + 1) ℓ hℓ.le) ?_ ((2 * B) ^ 2) ?_
    · exact (hΓm.pow_const 2).aestronglyMeasurable.restrict
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hΓb x) 2
  -- ## the pointwise Cauchy–Schwarz bound `G ≤ ℓ³ H`
  have hpt : ∀ x : Submission.BoseGases.X (m + 1), G x ≤ ℓ ^ 3 * H x := by
    intro x
    haveI hfin : IsFiniteMeasure ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact Submission.BoseGases.acube_lt_top ℓ hℓ.le⟩
    have hsm : AEStronglyMeasurable (fun u : E3 => |Γ (Function.update x j u)|)
        ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
      ((hΓm.comp (by fun_prop : Measurable fun u : E3 => Function.update x j u)).abs).aestronglyMeasurable
    have hint : Integrable (fun u : E3 => (|Γ (Function.update x j u)|) ^ 2)
        ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := by
      refine Integrable.of_bound (((hΓm.comp (by fun_prop : Measurable fun u : E3 =>
        Function.update x j u)).abs.pow_const 2).aestronglyMeasurable) ((2 * B) ^ 2) ?_
      filter_upwards with u
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hΓb (Function.update x j u)) 2
    have hcs := Work.BoseFixB1S.sq_integral_le_measure_mul_integral_sq
      (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
      (g := fun u : E3 => |Γ (Function.update x j u)|) hsm hint
    rw [acube_univ_toReal_psL2 hℓ] at hcs
    have hGH : (∫ u in Submission.BoseGases.acube ℓ, (Γ (Function.update x j u)) ^ 2)
        = ∫ u, (|Γ (Function.update x j u)|) ^ 2
            ∂((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := by
      apply integral_congr_ae
      filter_upwards with u
      rw [sq_abs]
    rw [hGdef, hHdef]
    show (∫ u in Submission.BoseGases.acube ℓ, |Γ (Function.update x j u)|) ^ 2
        ≤ ℓ ^ 3 * ∫ u in Submission.BoseGases.acube ℓ, (Γ (Function.update x j u)) ^ 2
    rw [hGH]
    exact hcs
  have hB1 : (∫ x in Submission.BoseGases.abox (m + 1) ℓ, G x)
      ≤ ℓ ^ 3 * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, H x := by
    have h := integral_mono_ae hGint (hHint.const_mul (ℓ ^ 3)) (ae_of_all _ hpt)
    rwa [MeasureTheory.integral_const_mul] at h
  -- ## `∫ H = ℓ³ ∫ Γ²`
  have hH2 : (∫ x in Submission.BoseGases.abox (m + 1) ℓ, H x)
      = ℓ ^ 3 * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, (Γ x) ^ 2 := by
    have hpeelH := psL2_peel_collapse hℓ j hHconst hHint
    have h1 : (∫ x in Submission.BoseGases.abox (m + 1) ℓ, H x)
        = ℓ ^ 3 * ∫ r in Submission.BoseGases.abox m ℓ,
            (∫ u in Submission.BoseGases.acube ℓ,
              (Γ (Submission.BoseGases.kcInsN m j (u, r))) ^ 2) := by
      rw [hpeelH]
      congr 1
      apply integral_congr_ae
      filter_upwards with r
      simp only [hHdef]
      apply integral_congr_ae
      filter_upwards with u
      rw [Submission.BoseGases.update_kcInsN]
    have h2 : (∫ r in Submission.BoseGases.abox m ℓ,
          (∫ u in Submission.BoseGases.acube ℓ,
            (Γ (Submission.BoseGases.kcInsN m j (u, r))) ^ 2))
        = ∫ x in Submission.BoseGases.abox (m + 1) ℓ, (Γ x) ^ 2 :=
      (Submission.BoseGases.abox_integral_peel (n := m) (ℓ := ℓ) j
        (fun x : Submission.BoseGases.X (m + 1) => (Γ x) ^ 2) hΓ2int).symm
    rw [h1, h2]
  have hD : (∫ x in Submission.BoseGases.abox (m + 1) ℓ, (Γ x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox (m + 1) ℓ, (Θ x) ^ 2 := by
    rw [hΓdef]
    exact aQ_aP_sq_le hℓ hij hΘmem
  -- ## assembly
  have hmain : (∫ r : Submission.BoseGases.X m, G (Submission.BoseGases.kcInsN m i (0, r))
        ∂((volume : Measure (Submission.BoseGases.X m)).restrict (Submission.BoseGases.abox m ℓ)))
      ≤ ℓ ^ 3 * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, (Θ x) ^ 2 := by
    have hA : ℓ ^ 3 * (∫ r : Submission.BoseGases.X m,
          G (Submission.BoseGases.kcInsN m i (0, r))
          ∂((volume : Measure (Submission.BoseGases.X m)).restrict (Submission.BoseGases.abox m ℓ)))
        = ∫ x in Submission.BoseGases.abox (m + 1) ℓ, G x :=
      (psL2_peel_collapse hℓ i hGconst hGint).symm
    have hchain : ℓ ^ 3 * (∫ r : Submission.BoseGases.X m,
          G (Submission.BoseGases.kcInsN m i (0, r))
          ∂((volume : Measure (Submission.BoseGases.X m)).restrict (Submission.BoseGases.abox m ℓ)))
        ≤ ℓ ^ 3 * (ℓ ^ 3 * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, (Θ x) ^ 2) := by
      rw [hA]
      have h3 : (0 : ℝ) ≤ ℓ ^ 3 := by positivity
      calc ∫ x in Submission.BoseGases.abox (m + 1) ℓ, G x
          ≤ ℓ ^ 3 * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, H x := hB1
        _ = ℓ ^ 3 * (ℓ ^ 3 * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, (Γ x) ^ 2) := by rw [hH2]
        _ ≤ ℓ ^ 3 * (ℓ ^ 3 * ∫ x in Submission.BoseGases.abox (m + 1) ℓ, (Θ x) ^ 2) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD h3) h3
    exact le_of_mul_le_mul_left hchain (by positivity)
  have hbridge : (∫ r : Submission.BoseGases.X m,
        (∫ u in Submission.BoseGases.acube ℓ,
            |Γ (Function.update (Submission.BoseGases.kcInsN m i (0, r)) j u)|) ^ 2
      ∂((volume : Measure (Submission.BoseGases.X m)).restrict (Submission.BoseGases.abox m ℓ)))
      = ∫ r : Submission.BoseGases.X m, G (Submission.BoseGases.kcInsN m i (0, r))
        ∂((volume : Measure (Submission.BoseGases.X m)).restrict (Submission.BoseGases.abox m ℓ)) := by
    apply integral_congr_ae
    filter_upwards with r
    simp only [hGdef]
  rw [hbridge]
  exact hmain

end Work.BoseBoxFock.PCFU
