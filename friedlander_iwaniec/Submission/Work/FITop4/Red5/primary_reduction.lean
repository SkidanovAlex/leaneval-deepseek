/-
# `Submission.Work.FITop4.Red5.primary_reduction`

The **primary reduction** of Friedlander–Iwaniec (5.2), p. 967: for `m ≥ 1` and `n` odd,
```
Σ_{|w|² = m} Σ_{|z|² = n} F(|z|²) Z(Re wz) = 4 · Σ_{|w|² = m} Σ_{|z|² = n, z primary} F(|z|²) Z(Re wz)
```
the factor `4` "accounting for the four units `1, i, i², i³` in `ℤ[i]`".  This is the identity by
which the paper passes from the representation count `a_{mn}` of (5.1) to the bilinear form (5.6)
over primary `z`, and it is what makes `Red5.piece_reindex` produce its `1/4`.

The argument has two halves, both proved here on top of `Submission.Work.FITop4.Red5.primary_setup`:

* **the sphere splits into orbits.**  Every `z` of odd norm `n` has a *unique* primary associate
  `ẑ` (`primary_associate_exists_unique`), so `z = ẑ · u` with `u` one of the four units and the
  pair `(ẑ, u)` unique: the sphere is the disjoint union of the four-element orbits, each with
  exactly one primary element (`sphere_decomposition`);
* **the `w`-sum is unit-invariant.**  Replacing `w` by `wu` permutes the sphere `|w|² = m`, so
  `Σ_{w} Z(Re w (zu)) = Σ_{w} Z(Re wz)` (`sum_sph_mul_unit`).

Consequently every unit-invariant sum over the sphere is `4` times the same sum over primary
elements, and the reduction follows by grouping the double sum along the orbits.
-/
import Mathlib
import Submission.Work.FITop4.Defs4
import Submission.Work.FITop4.Red5.primary_setup

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The sphere is the disjoint union of the primary orbits -/

/-- **The primitive element of the sphere.**  Every `z` with `|z|² = n`, `n` odd, is a unit
multiple of a unique primary element, and that element again lies in the sphere: the pair
`(ẑ, u)` with `ẑ` primary, `u` one of the four units, `ẑ u = z`, is unique. -/
theorem sph_decomposition (n : ℕ) (hn : Odd n) {z : GaussianInt} (hz : z ∈ sph n) :
    ∃! p : GaussianInt × GaussianInt,
      p.1 ∈ sphPrim n ∧ p.2 ∈ units4 ∧ p.1 * p.2 = z := by
  have hz0 : z ≠ 0 := sph_ne_zero hn hz
  have hzn : Work.FIPlan.gnorm z = n := sph_gnorm hz
  have hodd : Odd (Work.FIPlan.gnorm z) := by rw [hzn]; exact hn
  obtain ⟨w, hwP, -⟩ :=
    Commons.NumberTheory.GaussianInt.primary_associate_exists_unique hz0 hodd
  obtain ⟨hwassoc, hwre, hwim, hwimc⟩ := hwP
  obtain ⟨u, hu⟩ := hwassoc
  have hwassoc' : Associated w z := ⟨u, hu⟩
  have hwprim : Work.FIPlan.IsPrimary w := (isPrimary_iff_zmod w).mpr ⟨hwre, hwim, hwimc⟩
  have hwgn : Work.FIPlan.gnorm w = n := by
    have h1 : Work.FIPlan.gnorm (w * ↑u) = n := by rw [hu]; exact hzn
    rwa [gnorm_mul, gnorm_unit (Units.isUnit u), mul_one] at h1
  have hwne : w ≠ 0 := by
    rintro rfl
    rw [gnorm_zero] at hwgn
    obtain ⟨k, hk⟩ := hn
    omega
  have hwu : (↑u : GaussianInt) ∈ units4 := by
    rcases (Commons.NumberTheory.GaussianInt.units_classification (↑u)).mp
      (Units.isUnit u) with h | h | h | h
    · rw [h]; simp [units4]
    · rw [h]; simp [units4]
    · rw [h]; simp [units4]
    · rw [h]; simp [units4]
  have hwmem : w ∈ sph n := Finset.mem_filter.mpr ⟨mem_gBox_of_gnorm_eq hwgn, hwgn⟩
  have hwprimmem : w ∈ sphPrim n := Finset.mem_filter.mpr ⟨hwmem, hwprim⟩
  refine ⟨(w, ↑u), ⟨hwprimmem, hwu, hu⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
  have hbu : IsUnit b := isUnit_of_mem_units4 hb
  have has : Associated a z := ⟨hbu.unit, by rw [IsUnit.unit_spec hbu]; exact hab⟩
  have haprim : Work.FIPlan.IsPrimary a := (Finset.mem_filter.mp ha).2
  have haeq : a = w := eq_of_primary_associated hz0 hodd haprim has hwprim hwassoc'
  have hab' : w * b = z := by rw [← haeq]; exact hab
  have hbeq : b = (↑u : GaussianInt) := by
    refine mul_left_cancel₀ hwne ?_
    rw [hab', hu]
  rw [haeq, hbeq]

/-! ## 2. The reduction, abstractly -/

/-- **Primary reduction, abstract form.**  Let `f` be any summand whose `w`-sum over the sphere
`|w|² = m` is invariant under `z ↦ zu` for units `u`.  Then the double sum over the full sphere
`|z|² = n` (`n` odd) is four times the same double sum restricted to primary `z`: the sphere is
partitioned into four-element unit orbits, each carrying one primary element. -/
theorem primary_reduction_aux (m n : ℕ) (f : GaussianInt → GaussianInt → ℝ) (hn : Odd n)
    (hf : ∀ z : GaussianInt, Work.FIPlan.gnorm z = n → ∀ u : GaussianInt, IsUnit u →
        (∑ w ∈ sph m, f w (z * u)) = ∑ w ∈ sph m, f w z) :
    (∑ w ∈ sph m, ∑ z ∈ sph n, f w z) = 4 * (∑ w ∈ sph m, ∑ z ∈ sphPrim n, f w z) := by
  have hbij : (∑ p ∈ sphPrim n ×ˢ units4, ∑ w ∈ sph m, f w (p.1 * p.2))
      = ∑ z ∈ sph n, ∑ w ∈ sph m, f w z := by
    refine Finset.sum_nbij (fun p : GaussianInt × GaussianInt => p.1 * p.2) ?_ ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_product] at hp
      exact mul_unit_mem_sph (Finset.mem_of_mem_filter _ hp.1) (isUnit_of_mem_units4 hp.2)
    · intro p hp q hq hpq
      rw [Finset.mem_coe, Finset.mem_product] at hp hq
      have hmem : p.1 * p.2 ∈ sph n :=
        mul_unit_mem_sph (Finset.mem_of_mem_filter _ hp.1) (isUnit_of_mem_units4 hp.2)
      obtain ⟨w, hw, huniq⟩ := sph_decomposition n hn hmem
      refine (huniq p ?_).trans (huniq q ?_).symm
      · exact ⟨hp.1, hp.2, rfl⟩
      · exact ⟨hq.1, hq.2, hpq.symm⟩
    · intro b hb
      rw [Finset.mem_coe] at hb
      obtain ⟨p, hp, -⟩ := sph_decomposition n hn hb
      refine ⟨p, ?_, hp.2.2⟩
      rw [Finset.mem_coe, Finset.mem_product]
      exact ⟨hp.1, hp.2.1⟩
    · intro p hp
      rfl
  have hL : (∑ w ∈ sph m, ∑ z ∈ sph n, f w z) = ∑ z ∈ sph n, ∑ w ∈ sph m, f w z :=
    Finset.sum_comm
  have hR : (4 : ℝ) * (∑ w ∈ sph m, ∑ z ∈ sphPrim n, f w z)
      = ∑ z ∈ sphPrim n, 4 * (∑ w ∈ sph m, f w z) := by
    rw [Finset.sum_comm, Finset.mul_sum]
  rw [hL, ← hbij, Finset.sum_product, hR]
  refine Finset.sum_congr rfl (fun z0 hz0 => ?_)
  have hz0n : Work.FIPlan.gnorm z0 = n := sph_gnorm (Finset.mem_of_mem_filter z0 hz0)
  calc ∑ u ∈ units4, ∑ w ∈ sph m, f w (z0 * u)
      = ∑ u ∈ units4, ∑ w ∈ sph m, f w z0 :=
        Finset.sum_congr rfl (fun u hu => hf z0 hz0n u (isUnit_of_mem_units4 hu))
    _ = 4 * ∑ w ∈ sph m, f w z0 := by
        rw [Finset.sum_const, units4_card, nsmul_eq_mul]
        norm_num

/-! ## 3. The primary reduction for the Friedlander–Iwaniec summand -/

set_option linter.unusedVariables false in
theorem primary_reduction (m n : ℕ) (F : ℕ → ℝ) (hm : 1 ≤ m) (hn : Odd n) :
    (∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter (fun w => Work.FIPlan.gnorm w = m),
        ∑ z ∈ (Work.FIPlan.gBox ((n : ℕ) : ℤ)).filter (fun z => Work.FIPlan.gnorm z = n),
          F (Work.FIPlan.gnorm z) * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ))
      = 4 * (∑ w ∈ (Work.FIPlan.gBox ((m : ℕ) : ℤ)).filter (fun w => Work.FIPlan.gnorm w = m),
        ∑ z ∈ ((Work.FIPlan.gBox ((n : ℕ) : ℤ)).filter (fun z => Work.FIPlan.gnorm z = n)).filter
              (fun z => Work.FIPlan.IsPrimary z),
          F (Work.FIPlan.gnorm z) * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) := by
  simpa only [sph, sphPrim] using
    primary_reduction_aux m n
      (fun w z => F (Work.FIPlan.gnorm z) * (Work.FIPlan.Zint (Work.FIPlan.cForm w z) : ℝ)) hn
      (fun z _ u hu => sum_sph_mul_unit m F hu)

end

end Work.FITop4.Red5
