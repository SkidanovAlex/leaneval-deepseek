/-
# The units of `𝓞 K` which are `≡ 1 (mod 𝔪)` form a subgroup

`NK.NUV2.RouteB.RayCount.unitCongSubgroup 𝔪` is defined in `RayCount/Defs.lean` as the
subgroup of `(𝓞 K)ˣ` *generated* by the units `u` with `IsCongElem K 𝔪 ((u : 𝓞 K) : K)`.

The point of this file is that the generating set is *already* a subgroup, so the closure is the
set itself and membership in `unitCongSubgroup 𝔪` has an elementwise description:

`u ∈ unitCongSubgroup 𝔪 ↔ IsCongElem K 𝔪 ((u : 𝓞 K) : K)`.

That is what makes `unitCongSubgroup 𝔪` usable as an index for the ray-class counting: its cosets
in `(𝓞 K)ˣ` are the classes of units modulo the congruence condition `≡ 1 (mod 𝔪)` and positivity
at the real places of `𝔪.pos` (see `RayCount/NOTES.md`, Step 2).

## The mathematics

For `u : (𝓞 K)ˣ` and a prime `q` of `𝓞 K`, the finite part of `IsCongElem K 𝔪` at `q` reads
`v_q (u - 1) ≤ exp (-𝔪.exps q)`, which for a *unit* `u` is equivalent to the ideal-theoretic
statement `(u : 𝓞 K) - 1 ∈ q.asIdeal ^ (𝔪.exps q)` (`isCongElem_unit_iff_mem_ideal_pow`).  In that
form the three subgroup axioms are elementary:

* `1 - 1 = 0 ∈ q.asIdeal ^ n`;
* `(uv - 1) = (u - 1) * v + (v - 1)` lies in the ideal because `(u - 1) ∈ q.asIdeal ^ n` and
  ideals are closed under multiplication by an arbitrary ring element and under addition;
* `u⁻¹ - 1 = -((u - 1) * u⁻¹)` lies in the ideal because `(u - 1) ∈ q.asIdeal ^ n`.

The archimedean part of `IsCongElem K 𝔪` (positivity at the real places of `𝔪.pos`) is preserved
by `1`, by products and by inverses.  This is where the condition has to be imposed on *units* and
not on arbitrary elements of `K`: multiplicativity of the finite part uses `v_q v = 1`, i.e. that
the second factor is a unit at `q`.
-/
import Mathlib
import Submission.NK.NUV2.RouteB.RayCount.Defs

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain
open scoped Classical nonZeroDivisors NumberField

noncomputable section

namespace NK.NUV2.RouteB.RayCount

open NK.NUV2.RouteB

variable {K : Type} [Field K] [NumberField K]

/-- **The finite congruence condition for a unit, in ideal-theoretic form.**  For a unit `u` of
`𝓞 K` and a prime `q` of `𝓞 K` with exponent `n`, the condition `v_q (u - 1) ≤ exp (-n)` occurring
in `IsCongElem` is equivalent to `u - 1 ∈ q.asIdeal ^ n`. -/
theorem isCongElem_unit_iff_mem_ideal_pow (𝔪 : Modulus K) (u : (𝓞 K)ˣ)
    (q : HeightOneSpectrum (𝓞 K)) :
    Valued.v (algebraMap K (q.adicCompletion K) (((u : 𝓞 K) : K) - 1))
        ≤ WithZero.exp (-(𝔪.exps q : ℤ))
      ↔ (u : 𝓞 K) - 1 ∈ q.asIdeal ^ (𝔪.exps q) := by
  rw [map_sub, map_one, ← IsScalarTower.algebraMap_apply (𝓞 K) K (q.adicCompletion K) (u : 𝓞 K),
    ← map_one (algebraMap (𝓞 K) (q.adicCompletion K)), ← map_sub,
    IsScalarTower.algebraMap_apply (𝓞 K) K (q.adicCompletion K) ((u : 𝓞 K) - 1),
    Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem]

/-- The units of `𝓞 K` satisfying the congruence condition of the modulus `𝔪`: this set is a
subgroup of `(𝓞 K)ˣ`, and it is the carrier of `unitCongSubgroup 𝔪`. -/
def unitCongUnits (𝔪 : Modulus K) : Subgroup ((𝓞 K)ˣ) where
  carrier := {u : (𝓞 K)ˣ | IsCongElem K 𝔪 (((u : 𝓞 K) : K))}
  mul_mem' := by
    intro a b ha hb
    refine ⟨fun q hq => ?_, fun w hw hpos => ?_⟩
    · rw [isCongElem_unit_iff_mem_ideal_pow]
      have h1 := (isCongElem_unit_iff_mem_ideal_pow 𝔪 a q).mp (ha.1 q hq)
      have h2 := (isCongElem_unit_iff_mem_ideal_pow 𝔪 b q).mp (hb.1 q hq)
      have key : (((a * b : (𝓞 K)ˣ) : 𝓞 K)) - 1
          = ((a : 𝓞 K) - 1) * (b : 𝓞 K) + ((b : 𝓞 K) - 1) := by
        rw [Units.val_mul]; ring
      rw [key]
      exact Ideal.add_mem _ (Ideal.mul_mem_right (b : 𝓞 K) _ h1) h2
    · have h : (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
          (algebraMap K w.Completion (((a * b : (𝓞 K)ˣ) : K)))
          = (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
              (algebraMap K w.Completion (((a : (𝓞 K)ˣ) : K)))
            * (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
              (algebraMap K w.Completion (((b : (𝓞 K)ˣ) : K))) := by
        simp [Units.val_mul, map_mul]
      rw [h]
      exact mul_pos (ha.2 w hw hpos) (hb.2 w hw hpos)
  one_mem' := by
    refine ⟨fun q hq => ?_, fun w hw hpos => ?_⟩
    · rw [isCongElem_unit_iff_mem_ideal_pow]
      simp
    · simp
  inv_mem' := by
    intro a ha
    refine ⟨fun q hq => ?_, fun w hw hpos => ?_⟩
    · rw [isCongElem_unit_iff_mem_ideal_pow]
      have h1 := (isCongElem_unit_iff_mem_ideal_pow 𝔪 a q).mp (ha.1 q hq)
      have hu : (a : 𝓞 K) * ((a⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      have key : (((a⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) - 1
          = -(((a : 𝓞 K) - 1) * ((a⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) := by
        have h : ((a : 𝓞 K) - 1) * ((a⁻¹ : (𝓞 K)ˣ) : 𝓞 K)
            = 1 - ((a⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
          rw [sub_mul, one_mul, hu]
        rw [h]; ring
      rw [key]
      exact neg_mem (Ideal.mul_mem_right ((a⁻¹ : (𝓞 K)ˣ) : 𝓞 K) _ h1)
    · have h : (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
          (algebraMap K w.Completion (((a⁻¹ : (𝓞 K)ˣ) : K)))
          = ((NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw)
              (algebraMap K w.Completion (((a : (𝓞 K)ˣ) : K))))⁻¹ := by
        rw [show ((((a⁻¹ : (𝓞 K)ˣ)) : K)) = ((((a : (𝓞 K)ˣ)) : K))⁻¹ from
          eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])]
        simp
      rw [h]
      exact inv_pos.mpr (ha.2 w hw hpos)

/-- The congruence subgroup of the *units* is the set of units satisfying the elementwise
condition: the closure in the definition of `unitCongSubgroup` is redundant. -/
theorem unitCongSubgroup_eq_unitCongUnits (𝔪 : Modulus K) :
    unitCongSubgroup 𝔪 = unitCongUnits 𝔪 := by
  refine le_antisymm ?_ ?_
  · show Subgroup.closure {u : (𝓞 K)ˣ | IsCongElem K 𝔪 (((u : 𝓞 K) : K))} ≤ unitCongUnits 𝔪
    rw [Subgroup.closure_le]
    intro x hx
    exact hx
  · intro x hx
    exact Subgroup.subset_closure hx

/-- **Membership in `unitCongSubgroup 𝔪` is the elementwise congruence condition.**  A unit `u` of
`𝓞 K` lies in the congruence subgroup of `𝔪` if and only if `u ≡ 1 (mod 𝔪)`, i.e. `u - 1` is
divisible by the ideal of `𝔪` and `u` is positive at the real places of `𝔪.pos`. -/
theorem mem_unitCongSubgroup_iff (K : Type) [Field K] [NumberField K] (𝔪 : NK.NUV2.RouteB.Modulus K)
    (u : (NumberField.RingOfIntegers K)ˣ) :
    u ∈ NK.NUV2.RouteB.RayCount.unitCongSubgroup 𝔪 ↔
      NK.NUV2.RouteB.IsCongElem K 𝔪 (((u : NumberField.RingOfIntegers K)) : K) := by
  rw [unitCongSubgroup_eq_unitCongUnits]
  exact Iff.rfl

end NK.NUV2.RouteB.RayCount
