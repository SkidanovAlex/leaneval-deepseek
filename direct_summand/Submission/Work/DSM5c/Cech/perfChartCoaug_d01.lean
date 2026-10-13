import Mathlib
import Submission.Work.DSM5c.Cech.LocPresheafMap
import Submission.Work.DSM5b.perfCechCoordEquiv

namespace Work.DSM5c.Cech

/-! ## Infrastructure used by the proof

The proof goes through the coordinate description `Work.DSM5b.PCAux`
(`Submission/Work/DSM5b/perfCechCoordEquiv.lean`) of the perfected chart Čech complex:
`PhiQ` identifies the degree-`0` term of `K = (cechComplexFunctor (chartIdx ι)).obj
(perfChartPresheaf p t)` with the explicit tuple module `PCX p t 0`, sending the coaugmentation to
the diagonal (`PhiQ_coaug`), and `PhiQ_d_iff` identifies the vanishing of `d 0 1` with the
vanishing of the explicit alternating coface differential `PCd p t 0`.  The only extra ingredient
is that the restriction maps `rho` between perfected chart rings commute with the structure maps
`algebraMap`, in the subtype form in which the components of the coaugmentation appear. -/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2
open CategoryTheory.Limits Opposite

/-- **The restriction maps `rho` of the perfected chart rings commute with `algebraMap`.**  This is
the subtype form of `AlgHom.commutes` for the localisation map `locRes t h`. -/
lemma perfChartRho_algebraMap {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    [PerfectRing R p] {ι : Type} [Finite ι] [DecidableEq ι] (t : ι → R) {S T : Finset ι}
    (h : S ⊆ T) (w : R) :
    Work.DSM5b.rho p t h
      ⟨algebraMap R (Localization.Away (tS t S)) w, (perfChartRing p t S).algebraMap_mem w⟩
      = ⟨algebraMap R (Localization.Away (tS t T)) w, (perfChartRing p t T).algebraMap_mem w⟩ := by
  apply Subtype.ext
  rw [Work.DSM5b.rho_coe]
  exact AlgHom.commutes (locRes t h) w

/-- **The diagonal coaugmentation of the perfected chart Čech complex is a 0-cocycle.**

Let `R` be a perfect ring of characteristic the prime `p` and `t : ι → R` a family of generators
(`ι` finite, so that the component formula `Work.DSM5b.K_d_apply` applies).  The degree-`0` term of
the perfected chart Čech complex `K = (cechComplexFunctor (chartIdx ι)).obj (perfChartPresheaf p t)`
is the product of the perfected chart rings `perfChartRing p t S` over the tuples, and the
coaugmentation `perfChartCoaug p t` is the diagonal `w ↦ (algebraMap R _ w)_S`.  Its Čech
differential `d 0 1` is the alternating sum of the restriction maps `locRes`, each of which commutes
with `algebraMap`; hence the sum vanishes.  This is the hypothesis `he` of the dévissage
`Work.DSM5c.Devissage.almostAcyc_span_of_bot`.

Route: write `z := (perfChartCoaug p t).hom w`, use the component formula
`Work.DSM5b.K_d_apply p t 0 z σ` (with `Work.DSM5b.KX p t q`/`Work.DSM5b.Kd p t q`, definitionally
equal to `X q`/`d q (q+1)` of the Čech complex) to reduce to
`∑ a : Fin 2, (-1)^a • (restriction map) (algebraMap R _ w) = 0`; each restriction map sends
`algebraMap R _ w` to `algebraMap R _ w` (`Work.DSM5c.Cech.perfChartPresheaf_map_algebraMap`,
available in `Submission/Work/DSM5c/Cech/LocPresheafMap.lean`), and the components of
`(perfChartCoaug p t).hom w` are `algebraMap R _ w` (`Limits.Pi.lift_comp_π` at the element level).
Finally `(Kd p t 0) z = 0` follows from the vanishing of all its product components (use
`ModuleCat.piIsoPi` and `ModuleCat.piIsoPi_hom_ker_subtype`). -/
theorem perfChartCoaug_d01 {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] [CharP R p]
    [PerfectRing R p] {ι : Type} [Finite ι] [DecidableEq ι] (t : ι → R) (w : R) :
    (((CategoryTheory.cechComplexFunctor (DSMap.Mix2.chartIdx ι)).obj
        (DSMap.Mix2.perfChartPresheaf p t)).d 0 1)
      ((DSMap.Mix2.perfChartCoaug p t).hom w) = 0 := by
  -- In coordinates, the coaugmentation is the diagonal `τ ↦ algebraMap R ↥(perfChartRing p t S) w`
  -- (`PhiQ_coaug`), so the alternating coface differential `PCd p t 0` sends it to the alternating
  -- sum `+ algebraMap w - algebraMap w = 0` (`rho` commutes with `algebraMap`).
  have key : Work.DSM5b.PCd p t 0
      (Work.DSM5b.PCAux.PhiQ p R t ((perfChartCoaug p t).hom w)) = 0 := by
    have hz : ∀ τ : Fin 1 → ι, Work.DSM5b.PCAux.PhiQ p R t ((perfChartCoaug p t).hom w) τ
        = ⟨algebraMap R (Localization.Away (tS t (Work.DSM5b.tupRng τ))) w,
            (perfChartRing p t (Work.DSM5b.tupRng τ)).algebraMap_mem w⟩ := fun τ =>
      congrFun (Work.DSM5b.PCAux.PhiQ_coaug p R t w) τ
    funext τ
    rw [Work.DSM5b.PCd_apply]
    have hterm : ∀ i : Fin 2, (-1 : R) ^ (i : ℕ) •
        Work.DSM5b.rho p t (Work.DSM5b.tupRng_del_subset i τ)
          (Work.DSM5b.PCAux.PhiQ p R t ((perfChartCoaug p t).hom w) (Work.DSM5b.tupDel i τ))
        = (-1 : R) ^ (i : ℕ) •
          (⟨algebraMap R (Localization.Away (tS t (Work.DSM5b.tupRng τ))) w,
            (perfChartRing p t (Work.DSM5b.tupRng τ)).algebraMap_mem w⟩ :
              ↥(perfChartRing p t (Work.DSM5b.tupRng τ))) := by
      intro i
      rw [hz (Work.DSM5b.tupDel i τ),
        perfChartRho_algebraMap t (Work.DSM5b.tupRng_del_subset i τ) w]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    rw [Fin.sum_univ_two]
    simp
  exact (Work.DSM5b.PCAux.PhiQ_d_iff p R t ((perfChartCoaug p t).hom w)).mpr key

end Work.DSM5c.Cech
