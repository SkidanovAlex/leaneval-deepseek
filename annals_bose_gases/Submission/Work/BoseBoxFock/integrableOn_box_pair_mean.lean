import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.blockIIDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.integrableOn_box_pair_mean`

The `L¹`-fact behind every "two-slot box mean" of the pair rows: for a state-functional `G` that is
measurable and bounded by `CG` *on the box* `abox n ℓ`, and a pair kernel `k` that is jointly
measurable and bounded by `Ck` everywhere, the two-slot mean

    x ↦ ∫_{y ∈ acube ℓ} ∫_{u ∈ acube ℓ} G (x[i := y][j := u]) · k y u

is integrable on the box `abox n ℓ`.

The point is that inserting box points in the two slots `i` and `j` keeps a box point a box point
(`Submission.BoseGases.update_mem_abox`), so the integrand of the inner double integral is bounded
by `max CG 0 * max Ck 0` on `abox × acube × acube`; the measurability of the parametric integral
comes from Fubini on the (integrable) joint function
`p ↦ G (p.1[i := p.2.1][j := p.2.2]) · k p.2.1 p.2.2` on the product
`(volume.restrict (abox n ℓ)).prod ((volume.restrict (acube ℓ)).prod (volume.restrict (acube ℓ)))`
via `MeasureTheory.Integrable.integral_prod_left`, and then `MeasureTheory.integral_prod` identifies
the product integral with the iterated one a.e.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.BoseBoxFock

open MeasureTheory

theorem integrableOn_box_pair_mean {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin n} (hij : i ≠ j)
    {G : Submission.BoseGases.X n → ℝ} (hGm : Measurable G) {CG : ℝ}
    (hGb : ∀ x ∈ Submission.BoseGases.abox n ℓ, |G x| ≤ CG)
    {k : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hkm : Measurable (Function.uncurry k)) {Ck : ℝ} (hkb : ∀ y u, |k y u| ≤ Ck) :
    MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X n =>
        ∫ y in Submission.BoseGases.acube ℓ, ∫ u in Submission.BoseGases.acube ℓ,
          G (Function.update (Function.update x i y) j u) * k y u)
      (Submission.BoseGases.abox n ℓ) MeasureTheory.volume := by
  classical
  -- unfold `IntegrableOn` and put the two box measures on a name
  let E3 := EuclideanSpace ℝ (Fin 3)
  let μA : Measure E3 := (MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)
  let νX : Measure (Submission.BoseGases.X n) :=
    (MeasureTheory.volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)
  change MeasureTheory.Integrable
    (fun x : Submission.BoseGases.X n =>
      ∫ y, (∫ u, G (Function.update (Function.update x i y) j u) * k y u ∂μA) ∂μA) νX
  -- both restricted measures are finite
  haveI hfinA : IsFiniteMeasure μA :=
    MeasureTheory.isFiniteMeasure_restrict.2 (ne_of_lt (Submission.BoseGases.acube_lt_top ℓ hℓ.le))
  haveI hfinX : IsFiniteMeasure νX :=
    MeasureTheory.isFiniteMeasure_restrict.2 (ne_of_lt (Submission.BoseGases.abox_lt_top n ℓ hℓ.le))
  -- the joint integrand on `X n × E3 × E3`
  let Φ : Submission.BoseGases.X n × E3 × E3 → ℝ :=
    fun p => G (Function.update (Function.update p.1 i p.2.1) j p.2.2) * k p.2.1 p.2.2
  haveI : MeasureTheory.SFinite (μA.prod μA) := inferInstance
  -- measurability of the joint integrand
  have hΦm : Measurable Φ := by
    have hupd1 : Measurable (fun p : Submission.BoseGases.X n × E3 × E3 =>
        (Function.update p.1 i p.2.1 : Submission.BoseGases.X n)) :=
      (measurable_update' (X := fun _ : Fin n => E3) (a := i)).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have hupd : Measurable (fun p : Submission.BoseGases.X n × E3 × E3 =>
        (Function.update (Function.update p.1 i p.2.1) j p.2.2 : Submission.BoseGases.X n)) :=
      (measurable_update' (X := fun _ : Fin n => E3) (a := j)).comp
        (hupd1.prodMk (measurable_snd.comp measurable_snd))
    exact (hGm.comp hupd).mul
      (hkm.comp ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)))
  -- a.e. the box/cube coordinates
  have hae_cube : ∀ᵐ q ∂(μA.prod μA),
      q ∈ Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ := by
    have h1 : ∀ᵐ a ∂μA, a ∈ Submission.BoseGases.acube ℓ :=
      MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.acube_measurable ℓ)
    have h2 : ∀ᵐ b ∂μA, b ∈ Submission.BoseGases.acube ℓ :=
      MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.acube_measurable ℓ)
    refine (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
      ((Submission.BoseGases.acube_measurable ℓ).prod (Submission.BoseGases.acube_measurable ℓ))).2 ?_
    exact h1.mono (fun a ha => h2.mono (fun b hb => Set.mem_prod.mpr ⟨ha, hb⟩))
  have hae_box : ∀ᵐ p ∂(νX.prod (μA.prod μA)),
      p ∈ Submission.BoseGases.abox n ℓ ×ˢ
        (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) := by
    have h1 : ∀ᵐ a ∂νX, a ∈ Submission.BoseGases.abox n ℓ :=
      MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)
    refine (MeasureTheory.Measure.ae_prod_mem_iff_ae_ae_mem
      ((Submission.BoseGases.abox_measurable n ℓ).prod
        ((Submission.BoseGases.acube_measurable ℓ).prod (Submission.BoseGases.acube_measurable ℓ)))).2 ?_
    exact h1.mono (fun a ha => hae_cube.mono (fun b hb => Set.mem_prod.mpr ⟨ha, hb⟩))
  -- the pointwise bound on the box
  have hbound : ∀ (x : Submission.BoseGases.X n), x ∈ Submission.BoseGases.abox n ℓ →
      ∀ p : E3 × E3, p.1 ∈ Submission.BoseGases.acube ℓ → p.2 ∈ Submission.BoseGases.acube ℓ →
      ‖Φ (x, p)‖ ≤ max CG 0 * max Ck 0 := by
    intro x hx p hp1 hp2
    have hmem1 : Function.update x i p.1 ∈ Submission.BoseGases.abox n ℓ :=
      Submission.BoseGases.update_mem_abox i hx hp1
    have hmem2 : Function.update (Function.update x i p.1) j p.2 ∈ Submission.BoseGases.abox n ℓ :=
      Submission.BoseGases.update_mem_abox j hmem1 hp2
    have hG' : |G (Function.update (Function.update x i p.1) j p.2)| ≤ max CG 0 :=
      le_trans (hGb _ hmem2) (le_max_left _ _)
    have hk' : |k p.1 p.2| ≤ max Ck 0 := le_trans (hkb p.1 p.2) (le_max_left _ _)
    show |G (Function.update (Function.update x i p.1) j p.2) * k p.1 p.2| ≤ max CG 0 * max Ck 0
    rw [abs_mul]
    exact mul_le_mul hG' hk' (abs_nonneg _) (le_max_right _ _)
  -- the joint integrand is integrable on the full product
  have hΦint : MeasureTheory.Integrable Φ (νX.prod (μA.prod μA)) := by
    refine MeasureTheory.Integrable.of_bound hΦm.aestronglyMeasurable (max CG 0 * max Ck 0) ?_
    filter_upwards [hae_box] with p hp
    obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
    obtain ⟨hp2a, hp2b⟩ := Set.mem_prod.mp hp2
    exact hbound p.1 hp1 p.2 hp2a hp2b
  -- hence the partial functions are integrable on the box, so Fubini applies
  have hpartial : ∀ x ∈ Submission.BoseGases.abox n ℓ,
      MeasureTheory.Integrable (fun p : E3 × E3 => Φ (x, p)) (μA.prod μA) := by
    intro x hx
    refine MeasureTheory.Integrable.of_bound ?_ (max CG 0 * max Ck 0) ?_
    · exact (hΦm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    · filter_upwards [hae_cube] with p hp
      obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
      exact hbound x hx p hp1 hp2
  -- the product integral is integrable in `x`
  have hmain : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n => ∫ p : E3 × E3, Φ (x, p) ∂(μA.prod μA)) νX :=
    hΦint.integral_prod_left
  -- identify it with the iterated integral a.e.
  have hmain' : MeasureTheory.Integrable
      (fun x : Submission.BoseGases.X n => ∫ y, (∫ u, Φ (x, (y, u)) ∂μA) ∂μA) νX := by
    refine hmain.congr ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict (Submission.BoseGases.abox_measurable n ℓ)]
      with x hx
    exact MeasureTheory.integral_prod (fun p : E3 × E3 => Φ (x, p)) (hpartial x hx)
  exact hmain'

end Work.BoseBoxFock
