import Mathlib
import Submission.Work.DSEQP.gf_defs
import Submission.Work.DSEQP.gf_sat_aux
import Submission.Work.DSEQP.jvan_chart_eq_zero
import Submission.Work.DSEQP.chartMap_ker_transport
import Submission.Work.DSEQP.chartJ_saturation

/-!
# `Work.DSEQP.gf_sat` — the chart saturation `chartJ i S = ker (chartMap i S hS)`

This is the statement (and name) requested from this file: the kernel of the chart comparison
`chartMap i S hS : Away 𝒜 (x_S) →+* Γ(X, U_S)` of a closed immersion `i : X ⟶ ℙᴺ_A` is the chart
ideal `chartJ i S = (Jvan i)·Away 𝒜 (x_S)` of the vanishing ideal.

The proof uses three lemmas proved elsewhere in the area:

* `Work.DSEQP.jvan_chart_eq_zero` — a form of `Jvan i` vanishes on every coordinate chart, so
  `Jvan i` is contained in the "chart-vanishing" ideal of each singleton chart;
* `Work.DSEQP.chartMap_ker_transport` — quasi-coherence of `i.ker`: the kernel at a chart
  `D₊(x_T)` is the extension of the kernel at `D₊(x_S)` along `awayRes (S ⊆ T)`;
* `Work.DSEQP.chartJ_saturation` — the saturation (hard) direction at an arbitrary chart `S`:
  every `z ∈ ker (chartMap i S hS)` is `g / x_S^k` for a form `g` whose chart sections all
  vanish;

together with the `Away`-algebra of `Submission/Work/DSEQP/gf_sat_aux.lean`
(`Work.DSEQP.mk_eq_mul_awayRes`).

* the inclusion `chartJ i S ≤ ker (chartMap i S hS)` (easy direction): by
  `chartMap_ker_transport` applied to `{j} ⊆ S` (`j ∈ S` arbitrary) it suffices to show that the
  generators `f / x_S^k` of `chartJ i S` lie in the extension of the kernel at `{j}`; there
  `f / x_S^k` is a multiple of `awayRes (f / x_j^{k·|S|})`, and `f / x_j^{k·|S|} ∈ ker (chartMap i {j})`
  by `jvan_chart_eq_zero`.
* the inclusion `ker (chartMap i S hS) ≤ chartJ i S` is immediate from `chartJ_saturation`:
  its output `g` satisfies the defining condition of `Jvan i`, and `z = g / x_S^k` is then one of
  the generators of `chartJ i S`.
-/

namespace Work.DSEQP

universe a

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

theorem gf_sat (A : Type a) [CommRing A] {N : ℕ} {X : AlgebraicGeometry.Scheme.{a}}
    (i : X ⟶ DSMap.PSpace A N) (hi : AlgebraicGeometry.IsClosedImmersion i)
    (S : Finset (Fin (N + 1))) (hS : S.Nonempty) :
    Work.DSEQP.chartJ i S = RingHom.ker (Work.DSEQP.chartMap i S hS) := by
  obtain ⟨j, hj⟩ := Finset.nonempty_def.mp hS
  have hsj : ({j} : Finset (Fin (N + 1))) ⊆ S := Finset.singleton_subset_iff.mpr hj
  refine le_antisymm ?_ ?_
  · rw [chartMap_ker_transport (A := A) (N := N) i hi hsj (Finset.singleton_nonempty j) hS]
    refine Ideal.span_le.mpr ?_
    rintro z ⟨k, f, hf, hfJ, rfl⟩
    rw [mk_eq_mul_awayRes (A := A) (N := N) S hj k f hf]
    refine Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem (awayRes (A := A) (N := N) hsj) ?_)
    exact (RingHom.mem_ker).mpr
      (jvan_chart_eq_zero (A := A) (N := N) i hfJ (k * S.card) hf j)
  · intro z hz
    obtain ⟨k, g, hg, hgall, hzS⟩ :=
      chartJ_saturation (A := A) (N := N) i hi S hS z hz
    rw [hzS]
    exact Ideal.subset_span ⟨k, g, hg, Ideal.subset_span ⟨k * S.card, hg, hgall⟩, rfl⟩

end Work.DSEQP
