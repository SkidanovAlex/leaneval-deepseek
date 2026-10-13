import Mathlib
import Submission.Work.DSM5b.CycleDefs
import Submission.Work.DSM5b.locResAwayKernel
import Submission.Work.DSM5b.chartRing_gen_mul_eq
import Submission.Work.DSM5b.overlap_chartRing_le_adjoin
import Submission.Work.DSM5b.chartRing_overlap_pow_mul_eq

namespace Work.DSM5b

open DSMap DSMap.Mix2

universe a

set_option maxHeartbeats 1000000

/-- **The two-chart overlap is the localisation of one chart at the generator.**  Let `u ∈
chartRing t {i}` satisfy `u * algebraMap (t i) = algebraMap (t j)` in `Localization.Away (tS t {i})`
(i.e. `u = t j / t i`; such a `u` exists by `Work.DSM5b.chartRing_gen_mul_eq` and is unique because
`t i` is a nonzerodivisor in `Localization.Away (t i)`).  Then, with the `chartRing t {i}`-algebra
structure on the overlap chart `chartRing t ({i} ∪ {j})` given by the restriction map
`ccRestr t (Finset.subset_union_left)`, the overlap ring is the localisation of `chartRing t {i}` at
`u`.

Route: put `A := ↥(chartRing t {i})`, `B := ↥(chartRing t ({i} ∪ {j}))`, and use the generator
descriptions `A = W[t_k/t_i]` and `B = W[t_k/t_i, t_k/t_j]` inside `Localization.Away (tS t ({i} ∪ {j}))`,
with `t_k/t_j = (t_k/t_i) * u⁻¹` (because `u = t_j/t_i`).  Hence `B = A[u⁻¹]`.  Concretely the three
`IsLocalization` conditions:
* `map_units'`: `u` and the generator `t i / t j` of the `j`-chart are mutually inverse.
* `surj'`: an element of `B` is a sum of `A`-multiples of `∏ (t_k/t_j)`, and multiplying by a
  suitable power of `u` turns each `t_k/t_j = (t_k/t_i) * u⁻¹` into an element of `A`.
* `eq_iff_exists'`: if `x, y ∈ A` have the same image in `B` then some power of `u` kills `x - y`:
  the kernel of `Localization.Away (t i) → Localization.Away (tS t ({i} ∪ {j}))` is contained in the
  `t j`-torsion, so `t j ^ m * (x - y) = 0` in `Localization.Away (t i)`; multiplying by
  `(t i)⁻ᵐ` (i.e. using `hu`) gives `u ^ m * (x - y) = 0`. -/
theorem chartRing_overlap_isLocalization {R : Type a} [CommRing R] {ι : Type a} [DecidableEq ι]
    (t : ι → R) (i j : ι) (u : ↥(DSMap.Mix2.chartRing t {i}))
    (hu : (u : Localization.Away (DSMap.Mix2.tS t {i}))
        * algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t i)
      = algebraMap R (Localization.Away (DSMap.Mix2.tS t {i})) (t j)) :
    letI : Algebra ↥(DSMap.Mix2.chartRing t {i}) ↥(DSMap.Mix2.chartRing t ({i} ∪ {j})) :=
      (ccRestr t (Finset.subset_union_left)).toAlgebra
    IsLocalization.Away u ↥(DSMap.Mix2.chartRing t ({i} ∪ {j})) := by
  letI : Algebra ↥(DSMap.Mix2.chartRing t {i}) ↥(DSMap.Mix2.chartRing t ({i} ∪ {j})) :=
    (ccRestr t (Finset.subset_union_left)).toAlgebra
  classical
  have hST : ({i} : Finset ι) ⊆ {i} ∪ {j} := Finset.subset_union_left
  have hTj : j ∈ ({i} ∪ {j} : Finset ι) := Finset.mem_union_right _ (Finset.mem_singleton_self j)
  have hTi' : i ∈ ({i} ∪ {j} : Finset ι) :=
    Finset.mem_union_left _ (Finset.mem_singleton_self i)
  -- coercion of `algebraMap` through the subalgebra
  have hcoe : ∀ y : ↥(DSMap.Mix2.chartRing t {i}),
      (((algebraMap ↥(DSMap.Mix2.chartRing t {i}) ↥(DSMap.Mix2.chartRing t ({i} ∪ {j}))) y
        : ↥(DSMap.Mix2.chartRing t ({i} ∪ {j})))
        : Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j})))
      = DSMap.Mix2.locRes t hST (y : Localization.Away (DSMap.Mix2.tS t {i})) := fun y => rfl
  -- the element `w = t i / t j` of the overlap chart
  obtain ⟨τ, hτ⟩ : ∃ τ : (Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j})))ˣ,
      (τ : Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j})))
        = algebraMap R (Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j}))) (t j) :=
    ⟨(IsLocalization.Away.isUnit_of_dvd (DSMap.Mix2.tS t ({i} ∪ {j}))
        (Finset.dvd_prod_of_mem t hTj)).unit,
      (IsLocalization.Away.isUnit_of_dvd (DSMap.Mix2.tS t ({i} ∪ {j}))
        (Finset.dvd_prod_of_mem t hTj)).unit_spec⟩
  have hAiu : IsUnit (algebraMap R (Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j}))) (t i)) :=
    IsLocalization.Away.isUnit_of_dvd (DSMap.Mix2.tS t ({i} ∪ {j})) (Finset.dvd_prod_of_mem t hTi')
  let w : ↥(DSMap.Mix2.chartRing t ({i} ∪ {j})) :=
    ⟨algebraMap R (Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j}))) (t i) * ↑(τ⁻¹), by
      rw [DSMap.Mix2.chartRing]
      apply Algebra.subset_adjoin
      refine ⟨j, hTj, i, ?_⟩
      rw [mul_assoc, ← hτ, Units.inv_mul, mul_one]⟩
  have hw : (w : Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j})))
      * algebraMap R (Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j}))) (t j)
      = algebraMap R (Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j}))) (t i) := by
    show algebraMap R (Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j}))) (t i) * ↑(τ⁻¹)
        * algebraMap R (Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j}))) (t j)
      = algebraMap R (Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j}))) (t i)
    rw [mul_assoc, ← hτ, Units.inv_mul, mul_one]
  -- `uimg`: the image of `u` in the overlap
  have huimg_rel : DSMap.Mix2.locRes t hST (u : Localization.Away (DSMap.Mix2.tS t {i}))
      * algebraMap R (Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j}))) (t i)
      = algebraMap R (Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j}))) (t j) := by
    have h := congrArg (DSMap.Mix2.locRes t hST) hu
    simpa only [map_mul, AlgHom.commutes] using h
  -- `w * uimg = 1`
  have hrel_w : (w : Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j})))
      * DSMap.Mix2.locRes t hST (u : Localization.Away (DSMap.Mix2.tS t {i})) = 1 := by
    refine IsUnit.mul_right_cancel hAiu ?_
    rw [one_mul, mul_assoc, huimg_rel, hw]
  have hrel_w' : DSMap.Mix2.locRes t hST (u : Localization.Away (DSMap.Mix2.tS t {i}))
      * (w : Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j}))) = 1 := by
    rw [mul_comm]; exact hrel_w
  -- the unit condition
  have hunitB : IsUnit (algebraMap ↥(DSMap.Mix2.chartRing t {i})
      ↥(DSMap.Mix2.chartRing t ({i} ∪ {j})) u) := by
    rw [show algebraMap ↥(DSMap.Mix2.chartRing t {i})
        ↥(DSMap.Mix2.chartRing t ({i} ∪ {j})) u
      = ccRestr t Finset.subset_union_left u from rfl]
    exact ⟨⟨ccRestr t Finset.subset_union_left u, w, Subtype.ext hrel_w',
      Subtype.ext (by rw [mul_comm]; exact hrel_w')⟩, rfl⟩
  refine (isLocalization_iff (Submonoid.powers u)
    ↥(DSMap.Mix2.chartRing t ({i} ∪ {j}))).mpr ⟨?_, ?_, ?_⟩
  · -- `map_units'`
    intro y
    obtain ⟨n, hn⟩ :=
      (Submonoid.mem_powers_iff (y : ↥(DSMap.Mix2.chartRing t {i})) u).mp y.2
    rw [← hn]
    simpa only [map_pow] using hunitB.pow n
  · -- `surj'`
    intro z
    let Aij : Subalgebra R (Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j}))) :=
      (DSMap.Mix2.chartRing t {i}).map (DSMap.Mix2.locRes t hST)
    let uimg : Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j})) :=
      DSMap.Mix2.locRes t hST (u : Localization.Away (DSMap.Mix2.tS t {i}))
    have huimg_mem : uimg ∈ Aij := Subalgebra.mem_map.mpr ⟨u, u.2, rfl⟩
    -- the `R`-subalgebra of elements that become `A`-multiples after multiplying by `u ^ n`
    let Z : Subalgebra R (Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j}))) :=
      { carrier := {x | ∃ n : ℕ, x * uimg ^ n ∈ Aij}
        mul_mem' := by
          rintro x y ⟨n₁, hx⟩ ⟨n₂, hy⟩
          refine ⟨n₁ + n₂, ?_⟩
          have heq : (x * y) * uimg ^ (n₁ + n₂)
              = (x * uimg ^ n₁) * (y * uimg ^ n₂) := by ring
          rw [heq]
          exact Aij.mul_mem hx hy
        one_mem' := ⟨0, by rw [pow_zero, mul_one]; exact Aij.one_mem⟩
        add_mem' := by
          rintro x y ⟨n₁, hx⟩ ⟨n₂, hy⟩
          refine ⟨n₁ + n₂, ?_⟩
          have heq : (x + y) * uimg ^ (n₁ + n₂)
              = (x * uimg ^ n₁) * uimg ^ n₂ + (y * uimg ^ n₂) * uimg ^ n₁ := by ring
          rw [heq]
          exact Aij.add_mem (Aij.mul_mem hx (Aij.pow_mem huimg_mem n₂))
            (Aij.mul_mem hy (Aij.pow_mem huimg_mem n₁))
        zero_mem' := ⟨0, by rw [pow_zero, mul_one]; exact Aij.zero_mem⟩
        algebraMap_mem' := fun r =>
          ⟨0, by rw [pow_zero, mul_one]; exact Aij.algebraMap_mem r⟩ }
    have hZle : (DSMap.Mix2.chartRing t ({i} ∪ {j}) :
        Subalgebra R (Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j})))) ≤ Z := by
      refine (overlap_chartRing_le_adjoin t i j (w := (w :
        Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j})))) (by
          show (w : Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j})))
              * algebraMap R (Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j}))) (t j)
            = algebraMap R (Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j}))) (t i)
          exact hw)).trans (Algebra.adjoin_le_iff.mpr ?_)
      intro x hx
      rcases hx with hx | hx
      · exact ⟨0, by rw [pow_zero, mul_one]; exact hx⟩
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨1, by rw [pow_one]; exact (by rw [hrel_w]; exact Aij.one_mem)⟩
    obtain ⟨n, hn⟩ := hZle z.2
    obtain ⟨a, ha, hza⟩ := Subalgebra.mem_map.mp hn
    refine ⟨(⟨a, ha⟩, ⟨u ^ n, (Submonoid.mem_powers_iff (u ^ n) u).mpr ⟨n, rfl⟩⟩), ?_⟩
    apply Subtype.ext
    show (z : Localization.Away (DSMap.Mix2.tS t ({i} ∪ {j})))
        * DSMap.Mix2.locRes t hST ((u ^ n : ↥(DSMap.Mix2.chartRing t {i}))
            : Localization.Away (DSMap.Mix2.tS t {i}))
      = DSMap.Mix2.locRes t hST (a : Localization.Away (DSMap.Mix2.tS t {i}))
    rw [Subalgebra.coe_pow, map_pow, hza]
  · -- `eq_iff_exists'`
    intro x y hxy
    have hxy' : DSMap.Mix2.locRes t hST (x : Localization.Away (DSMap.Mix2.tS t {i}))
        = DSMap.Mix2.locRes t hST (y : Localization.Away (DSMap.Mix2.tS t {i})) := by
      rw [← hcoe x, ← hcoe y]
      exact congrArg Subtype.val hxy
    obtain ⟨n, hn⟩ := chartRing_overlap_pow_mul_eq t i j u hu hxy'
    exact ⟨⟨u ^ n, (Submonoid.mem_powers_iff (u ^ n) u).mpr ⟨n, rfl⟩⟩, hn⟩

end Work.DSM5b
