import Mathlib
import ChallengeDeps
import Submission.GeometryOfNumbers.ExteriorCoordinates
import Submission.Work.Lattice.MaxNorm
import Submission.GeometryOfNumbers.FlowLattice
import Submission.Commons.Analysis.InnerProductSpace.intWedge_norm_ge_one
import Submission.Commons.LinearAlgebra.ExteriorPower.iMulti_linearIndependent_of_ne_zero
import Submission.Work.Polygon.GraysonData

/-!
# The flow cannot shrink `j`-vectors below the eigenvalue `a^j`

The two-scale diagonal flow `a_t = scaleMap (twoScale a b ℓ)` with `0 < a ≤ b` acts on `⋀^jℝᵈ` with
eigenvalues `∏_{i ∈ I} s i ∈ [a^j, b^j]` (in the standard orthonormal basis `(e_I)`).  Its **smallest
singular value on `⋀^jℝᵈ` is therefore exactly `a^j`**, i.e.

  `a^j · ‖w‖ ≤ ‖⋀^j a_t w‖`   for every `w`.

This is the "no short vector" lower bound of the flow picture (de Saxcé §3: a lattice point of the
flowed lattice cannot be shorter than the contracting eigenvalue; the paper uses this in the form
"the quotient lattice contains no vector of norm less than `e^{...}`").

Proof: expand `w` in the orthonormal basis `(Bk d j I)` (`normSq_eq_sum_wcoord`) and use the
coordinate formula `wcoord (⋀^j a_t w) I = (∏_{i∈I} s i)·wcoord w I`
(`MaxNorm.wcoord_map_scaleMap`).

All declarations are sorry-free; module `Submission.Work.Lattice.FlowShrink`, namespace
`Submission.FlowShrink`.
-/

noncomputable section

open Module exteriorPower
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option linter.unnecessarySimpa false

namespace Submission.FlowShrink

open Submission.ExteriorCoordinates
open Submission.DiagonalFlow

/-- **Diagonal exterior-power lower bound.**  For a diagonal map `scaleMap s` whose coefficients
are all at least `a > 0`, the `j`-th exterior power does not shrink by more than `a^j`. -/
theorem pow_mul_norm_le_norm_map_scaleMap {d j : ℕ} {s : Fin d → ℝ} {a : ℝ} (ha : 0 < a)
    (hs : ∀ i, a ≤ s i) (w : WK d j) :
    a ^ j * ‖w‖ ≤ ‖exteriorPower.map j (scaleMap s) w‖ := by
  have hcoord : ∀ I : IDX d j,
      wcoord (d := d) (k := j) (exteriorPower.map j (scaleMap s) w) I =
        ((I : Finset (Fin d)).prod s) * wcoord (d := d) (k := j) w I :=
    fun I => Submission.MaxNorm.wcoord_map_scaleMap (d := d) s w I
  have hprod_ge : ∀ I : IDX d j, a ^ j ≤ ((I : Finset (Fin d)).prod s) := by
    intro I
    have hcard : (I : Finset (Fin d)).card = j := by
      simpa using I.2
    calc a ^ j = ((I : Finset (Fin d)).prod (fun _ => a)) := by
          rw [Finset.prod_const, hcard]
      _ ≤ (I : Finset (Fin d)).prod s :=
          Finset.prod_le_prod (fun i _ => le_of_lt ha) (fun i _ => hs i)
  have hsq : (a ^ j * ‖w‖) ^ 2 ≤ ‖exteriorPower.map j (scaleMap s) w‖ ^ 2 := by
    rw [mul_pow, normSq_eq_sum_wcoord (exteriorPower.map j (scaleMap s) w),
      normSq_eq_sum_wcoord w, Finset.mul_sum]
    refine Finset.sum_le_sum (fun I _ => ?_)
    rw [hcoord I, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) (hprod_ge I) 2)
      (sq_nonneg _)
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp hsq

/-- **Two-scale form**: for `0 < a ≤ b` the exterior power `⋀^j (scaleMap (twoScale a b ℓ))` has
`a^j` as a lower bound for its action. -/
theorem pow_mul_norm_le_norm_map_twoScale {d j ℓ : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (w : WK d j) :
    a ^ j * ‖w‖ ≤ ‖exteriorPower.map j (scaleMap (twoScale a b ℓ)) w‖ := by
  refine pow_mul_norm_le_norm_map_scaleMap (d := d) (j := j) ha (fun i => ?_) w
  rw [twoScale_apply]
  split
  · exact le_refl a
  · exact hab

/-- **The flowed lattice has no short vectors**: every element of
`flowLattice a b ℓ` is a `ℤ`-span of the flowed basis vectors, so every `j`-vector of the
`ℤ`-span of `j` lattice elements is bounded below by `a^j` times the wedge of its
integer lifts.  In particular the intrinsic covolume of the `ℤ`-span of the flowed image of an
`ℝ`-independent integer family is at least `a^j`. -/
theorem pow_le_norm_iMulti_of_mem_intPoints {d j ℓ : ℕ} {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hj : 0 < j) (m : Fin j → RD d) (hmz : ∀ i r, ∃ z : ℤ, m i r = z)
    (hmli : LinearIndependent ℝ m) :
    a ^ j ≤ ‖exteriorPower.ιMulti ℝ j
      (fun i => scaleMap (twoScale a b ℓ) (m i))‖ := by
  have h1 : (1 : ℝ) ≤ ‖exteriorPower.ιMulti ℝ j m‖ :=
    Commons.Analysis.InnerProductSpace.intWedge_norm_ge_one hj m hmz hmli
  have h2 : a ^ j * ‖exteriorPower.ιMulti ℝ j m‖ ≤
      ‖exteriorPower.map j (scaleMap (twoScale a b ℓ)) (exteriorPower.ιMulti ℝ j m)‖ :=
    pow_mul_norm_le_norm_map_twoScale (d := d) (j := j) (ℓ := ℓ) ha hab _
  have h3 : exteriorPower.map j (scaleMap (twoScale a b ℓ)) (exteriorPower.ιMulti ℝ j m) =
      exteriorPower.ιMulti ℝ j (fun i => scaleMap (twoScale a b ℓ) (m i)) :=
    exteriorPower.map_apply_ιMulti _ _
  rw [h3] at h2
  have haj : 0 < a ^ j := pow_pos ha j
  calc a ^ j = a ^ j * 1 := (mul_one _).symm
    _ ≤ a ^ j * ‖exteriorPower.ιMulti ℝ j m‖ := by
        exact mul_le_mul_of_nonneg_left h1 (le_of_lt haj)
    _ ≤ _ := h2


/-- **Covolume floor for the flowed span of an integer family.**  The intrinsic covolume of the
`ℤ`-span of the flowed image of an `ℝ`-independent integer family of size `j ≥ 1` is at least
`a^j`: this is the "no short vector in the flowed lattice" statement in the covolume form.
(`latticeCovol (span ℤ (range v)) = ‖⋀^j v‖` by `GraysonData.latticeCovol_span`.) -/
theorem pow_le_latticeCovol_span {d j ℓ : ℕ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hj : 0 < j) {m : Fin j → RD d} (hmz : ∀ i r, ∃ z : ℤ, m i r = z)
    (hmli : LinearIndependent ℝ m) :
    a ^ j ≤ Submission.GraysonData.latticeCovol (Submodule.span ℤ
      (Set.range (fun i => scaleMap (twoScale a b ℓ) (m i)))) := by
  have hnorm : a ^ j ≤
      ‖exteriorPower.ιMulti ℝ j (fun i => scaleMap (twoScale a b ℓ) (m i))‖ :=
    pow_le_norm_iMulti_of_mem_intPoints (d := d) (ℓ := ℓ) ha hab hj m hmz hmli
  have hne : exteriorPower.ιMulti ℝ j (fun i => scaleMap (twoScale a b ℓ) (m i)) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact absurd hnorm (not_le.mpr (pow_pos ha j))
  have hli : LinearIndependent ℝ (fun i => scaleMap (twoScale a b ℓ) (m i)) :=
    Commons.LinearAlgebra.ExteriorPower.iMulti_linearIndependent_of_ne_zero _ hne
  rw [Submission.GraysonData.latticeCovol_span (d := d) (r := j) hj _ hli]
  exact hnorm

end Submission.FlowShrink

end
