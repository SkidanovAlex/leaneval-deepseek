import Mathlib
import Submission.Work.DSM5b.chartCech_cycle_iff_pairwise
import Submission.Work.DSM5c.ChartFunctor
import Submission.Work.DSM5c.Devissage.almostAcyc_span_pow

namespace Work.DSM5c.Cech

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open CategoryTheory.Limits

universe a

set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-! ## The honest chart coaugmentation is a `0`-cocycle

The degree-`0` term of the chart Čech complex `chartCech t = Č({D(t_i)}, W[J/t_i])` is the product
`∏_i W[J/t_i]` (`Work.DSM5b.ccZ`), and `chartCoaugW t` sends `w` to the family
`i ↦ w • 1`.  Its Čech differential is the alternating sum of the restrictions `locRes` along
`{i} ⊆ {i} ∪ {j}`, so its `σ`-component is
`(w • 1)_{σ 1} - (w • 1)_{σ 0} = 0` in `W_{t_{σ 0} t_{σ 1}}`.  This is
`Work.DSM5b.ccD01` plus the component formula `Work.DSM5b.ccC0_apply`/`ccCoaug_apply` for the
coaugmentation. -/

/-- **The coaugmentation of the honest chart Čech complex is a `0`-cocycle.** -/
theorem chartCoaugW_d01 {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι]
    (t : ι → W) (w : W) :
    (((cechComplexFunctor (chartIdx ι)).obj (chartPresheaf t)).d 0 1).hom
      ((chartCoaugW t).hom w) = 0 := by
  have hvar : ∀ σ : Fin 2 → ι,
      (Pi.π (Work.DSM5b.ccZ W ι 1 t) σ).hom
        ((((cechComplexFunctor (chartIdx ι)).obj (chartPresheaf t)).d 0 1).hom
          ((chartCoaugW t).hom w)) = 0 := by
    intro σ
    rw [Work.DSM5b.ccD01 W ι t ((chartCoaugW t).hom w) σ, sub_eq_zero]
    have h0 : Work.DSM5b.ccC0 W ι t ((chartCoaugW t).hom w) (Work.DSM5b.ccDel 0 σ)
        = algebraMap W ↥(chartRing t (Work.DSM5b.ccIdx (Work.DSM5b.ccDel 0 σ))) w := by
      rw [Work.DSM5b.ccC0_apply W ι t ((chartCoaugW t).hom w) (Work.DSM5b.ccDel 0 σ),
        Work.DSM5b.ccCoaug_apply W ι t w (Work.DSM5b.ccDel 0 σ)]
    have h1 : Work.DSM5b.ccC0 W ι t ((chartCoaugW t).hom w) (Work.DSM5b.ccDel 1 σ)
        = algebraMap W ↥(chartRing t (Work.DSM5b.ccIdx (Work.DSM5b.ccDel 1 σ))) w := by
      rw [Work.DSM5b.ccC0_apply W ι t ((chartCoaugW t).hom w) (Work.DSM5b.ccDel 1 σ),
        Work.DSM5b.ccCoaug_apply W ι t w (Work.DSM5b.ccDel 1 σ)]
    rw [h0, h1]
    apply Subtype.ext
    simp only [Subalgebra.coe_algebraMap, AlgHom.commutes]
  refine (Work.DSM5b.ccC1 W ι t).injective ?_
  have hz : (Work.DSM5b.ccC1 W ι t)
      ((((cechComplexFunctor (chartIdx ι)).obj (chartPresheaf t)).d 0 1).hom
        ((chartCoaugW t).hom w)) = 0 := by
    funext σ
    rw [Work.DSM5b.ccC1_apply]
    exact hvar σ
  have h0 : (Work.DSM5b.ccC1 W ι t) (0 : ↥((chartCech t).X 1)) = 0 := by
    funext σ
    simp
  rw [hz, h0]

/-! ## Transport along the chart map `η` -/

/-- The abstract form of the target statement: for any presheaf `P` of `W`-modules and any map
`η : chartPresheaf t ⟶ P` of presheaves, the coaugmentation `chartCoaugW t ≫ (Č η).f 0` is a
`0`-cocycle.  This holds because `chartCoaugW t` is a cocycle (`chartCoaugW_d01`) and `Č η` is a
chain map (`HomologicalComplex.Hom.comm`). -/
theorem cech_coaug_map_d01 {W : Type a} [CommRing W] {ι : Type a} [DecidableEq ι]
    (t : ι → W) (P : (Finset ι)ᵒᵖᵒᵖ ⥤ ModuleCat.{a} W) (η : chartPresheaf t ⟶ P) (w : W) :
    (((cechComplexFunctor (chartIdx ι)).obj P).d 0 1).hom
      ((chartCoaugW t ≫ ((cechComplexFunctor (chartIdx ι)).map η).f 0).hom w) = 0 := by
  have hcomm := HomologicalComplex.Hom.comm ((cechComplexFunctor (chartIdx ι)).map η) 0 1
  rw [ModuleCat.comp_apply, ← ModuleCat.comp_apply, hcomm, ModuleCat.comp_apply,
    chartCoaugW_d01 t w, map_zero]

/-! ## The target statement -/

/-- **The coaugmentation of the chart untilt complex is a cocycle** (the hypothesis `he` of
`Work.DSM5c.almostAcyc_span_pow` and of
`Work.DSM5c.Devissage.almostAcyc_of_surjective_kernel_v2`).

For any chart map `η : chartPresheaf t ⟶ Dp` (`Dp = Work.DSM5c.chartD …`) which sends the unit
`1 ∈ chartRing t S` to `1 ∈ D_S` (the property produced by `Work.DSM5c.Eta.exists_chartMap`), the
coaugmentation `e := chartCoaugW t ≫ (Č η).f 0 : W → Č(Dp)^0` has `d (e w) = 0` for every `w : W`.

Indeed `e.hom w = (w • 1)_i` by `W`-linearity of `η_{{i}}`, and the Čech differential at degree `0`
is the alternating sum of the restriction maps, which are `W`-linear and send `1` to `1`.  (`hη` is
in fact not needed: the honest coaugmentation `chartCoaugW t` is already a cocycle and `Č η` is a
chain map, so the proof can also proceed by rewriting with `HomologicalComplex.Hom.comm` and the
pairwise description of `d 0 1`.) -/
theorem chartCoaug_isCocycle {p : ℕ} [Fact p.Prime] {W : Type} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type} [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (η : DSMap.Mix2.chartPresheaf t ⟶
      Work.DSM5c.chartD (p := p) (W := W) Q hθ t tr htr0 htr j₀ e)
    (hη : ∀ (S : (Finset ι)ᵒᵖᵒᵖ) (w : W),
      letI := Work.DSM5c.chartDAlg (p := p) (W := W) Q hθ t tr htr0 htr j₀ e S.unop.unop
      η.app S (algebraMap W (DSMap.Mix2.chartRing t S.unop.unop) w) =
        w • (1 : Work.DSM5c.untiltOf (p := p) (W := W)
          (Work.DSM5c.tiltChart Q t tr htr0 htr j₀ e S.unop.unop)
          (Work.DSM5c.chartPhi Q t tr htr0 htr j₀ e S.unop.unop)))
    (w : W) :
    (((cechComplexFunctor (chartIdx ι)).obj
        (Work.DSM5c.chartD (p := p) (W := W) Q hθ t tr htr0 htr j₀ e)).d 0 1).hom
      ((chartCoaugW t ≫
        ((cechComplexFunctor (chartIdx ι)).map η).f 0).hom w) = 0 :=
  cech_coaug_map_d01 t _ η w

end Work.DSM5c.Cech
