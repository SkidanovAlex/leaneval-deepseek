import ChallengeDeps
import Mathlib.Tactic.Have
import Submission.Work.BoseSym.Interface
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# BoseSym — integrability of the pair interaction `Vpot` on the box

The pair interaction `Vpot N v x = ∑_{i<j} v (x i - x j)` of an `L¹` potential
`v : ℝ³ → ℝ` is integrable on the box `box N L = [0,L]^{3N}`.

The proof is by reduction to the corpus lemmas of `Submission.Potential`:

* for `L > 0`, each summand `x ↦ v (x i - x j)` is integrable over the box:
  fix all coordinates but `x j` and use that `x j ↦ x i - x j` is a translation
  composed with a reflection of `ℝ³` (this is
  `Submission.BoseGases.integrableOn_pair_v` for the absolute value, plus an
  a.e. transfer to the signed function through a measurable representative of
  `v`);
* a finite sum of integrable functions is integrable (`integrable_finsetSum`);
* for arbitrary `L` we restrict from the larger box of side `max L 1 > 0`
  (`IntegrableOn.mono_set`, `Submission.BoseGases.box_mono`).

## Main results

* `integrableOn_Vpot_box`
-/

namespace Work.BoseSym.Bridge

open MeasureTheory Filter
open BoseGases Submission.BoseGases
open scoped Topology ENNReal

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Integrability of a single pair term -/

/-- For `v ∈ L¹(ℝ³)` and any pair of indices `i j`, the function
`x ↦ v (x i - x j)` is integrable over the box of finite side length. -/
lemma integrableOn_pair_signed {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ}
    (hv : IsL1 v) (i j : Fin N) :
    IntegrableOn (fun x : Conf N => v (x i - x j)) (box N L) volume := by
  by_cases hij : i = j
  · -- the integrand is the constant `v 0`
    subst j
    have hcst : (fun x : Conf N => v (x i - x i)) = fun _ : Conf N => v (0 : E3) := by
      funext x
      rw [sub_self]
    rw [hcst]
    refine Integrable.mono' (g := fun x : Conf N => |v (x i - x i)|) ?_ ?_ ?_
    · exact (integrableOn_pair_v (N := N) (L := L) hL hv i i).integrable
    · exact aestronglyMeasurable_const
    · filter_upwards with x
      simp [sub_self]
  · -- general case: transfer along a measurable representative of `v`
    have hvInt : Integrable v := memLp_one_iff_integrable.mp hv
    have hvae : AEMeasurable v := hvInt.aemeasurable
    let w : E3 → ℝ := AEMeasurable.mk v hvae
    have hwm : Measurable w := AEMeasurable.measurable_mk hvae
    have hvw : v =ᵐ[volume] w := AEMeasurable.ae_eq_mk hvae
    have hwInt : Integrable w := hvInt.congr hvw
    have hwfin : (∫⁻ y : E3, ‖w y‖ₑ) < ∞ := hwInt.hasFiniteIntegral
    have hmeas : Measurable (fun x : Conf N => w (x i - x j)) := by
      refine hwm.comp ?_
      fun_prop
    have habs : IntegrableOn (fun x : Conf N => |w (x i - x j)|) (box N L) volume :=
      integrableOn_abs_pair_of_measurable hL hwm hwfin i j hij
    have hmain : Integrable (fun x : Conf N => w (x i - x j))
        (volume.restrict (box N L)) := by
      refine Integrable.mono' (g := fun x : Conf N => |w (x i - x j)|)
        habs.integrable hmeas.aestronglyMeasurable ?_
      filter_upwards with x
      simp [Real.norm_eq_abs]
    -- the two integrands agree a.e. on the box
    have hN : volume {y : E3 | v y ≠ w y} = 0 := by
      rw [← ae_iff]
      exact hvw
    rcases exists_measurable_superset_of_null (μ := (volume : Measure E3)) hN with
      ⟨t, hNt, htm, ht0⟩
    have hpre : (volume : Measure (Conf N)).restrict (box N L)
        {x : Conf N | x i - x j ∈ t} = 0 :=
      null_preimage_pair hL htm ht0 i j hij
    have hnull : (volume : Measure (Conf N)).restrict (box N L)
        {x : Conf N | v (x i - x j) ≠ w (x i - x j)} = 0 := by
      refine le_antisymm ?_ (by positivity)
      calc (volume : Measure (Conf N)).restrict (box N L)
            {x : Conf N | v (x i - x j) ≠ w (x i - x j)}
          ≤ (volume : Measure (Conf N)).restrict (box N L)
              {x : Conf N | x i - x j ∈ t} := by
            refine measure_mono ?_
            intro x hx
            exact hNt hx
        _ = 0 := hpre
    have hmem : {x : Conf N | v (x i - x j) = w (x i - x j)} ∈
        ae (volume.restrict (box N L)) := by
      rw [mem_ae_iff]
      rw [show ({x : Conf N | v (x i - x j) = w (x i - x j)})ᶜ =
          {x : Conf N | v (x i - x j) ≠ w (x i - x j)} by ext x; simp]
      exact hnull
    have hae : (fun x : Conf N => v (x i - x j)) =ᵐ[volume.restrict (box N L)]
        (fun x : Conf N => w (x i - x j)) := by
      rw [show (fun x : Conf N => v (x i - x j)) =ᵐ[volume.restrict (box N L)]
            (fun x : Conf N => w (x i - x j)) ↔
          {x : Conf N | v (x i - x j) = w (x i - x j)} ∈
            ae (volume.restrict (box N L)) by rfl]
      exact hmem
    exact hmain.congr hae.symm

/-! ## The pair interaction -/

/-- The pair interaction of an `L¹` potential is integrable over a box of
positive side length. -/
lemma integrableOn_Vpot_box_pos {N : ℕ} {L : ℝ} (hL : 0 < L) {v : E3 → ℝ}
    (hv : IsL1 v) :
    IntegrableOn (Vpot N v) (box N L) volume := by
  change Integrable (Vpot N v) (volume.restrict (box N L))
  have hsum : Integrable
      (fun x : Conf N =>
        ∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)),
          v (x p.1 - x p.2))
      (volume.restrict (box N L)) := by
    refine integrable_finsetSum _ (fun p _ => ?_)
    exact integrableOn_pair_signed hL hv p.1 p.2
  have hV : Vpot N v = (fun x : Conf N =>
      ∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)),
        v (x p.1 - x p.2)) := by
    funext x
    rw [Vpot]
  rw [hV]
  exact hsum

end

/-- The pair interaction of an `L¹` potential is integrable on the box. -/
theorem integrableOn_Vpot_box {N : ℕ} {L : ℝ} {v : E3 → ℝ} (hv1 : IsL1 v) :
    IntOnBox N L (Vpot N v) := by
  have hL : (0 : ℝ) < max L 1 := lt_max_of_lt_right one_pos
  have hbig : IntegrableOn (Vpot N v) (box N (max L 1)) volume :=
    integrableOn_Vpot_box_pos hL hv1
  exact hbig.mono_set (box_mono (le_max_left L 1))

end Work.BoseSym.Bridge
