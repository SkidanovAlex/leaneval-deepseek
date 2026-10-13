import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Submission.Work.LWP.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.LWP.BiotSavart

open Matrix MeasureTheory

/-- The self dot product of a nonzero vector of `Fin 3 → ℝ` is nonzero: it is a sum of
squares of the coordinates. -/
lemma dotSelf_ne_zero_three {v : Fin 3 → ℝ} (hv : v ≠ 0) : v ⬝ᵥ v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ v j * v j := fun j _ => mul_self_nonneg _
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h
  exact mul_self_eq_zero.mp (hz i (Finset.mem_univ i))

/-- The set of points `y` for which `d ⨯ (c - y) = 0` — a line, when `d ≠ 0` — is Lebesgue
null: it is contained in the affine hyperplane `{y | y - c ∈ span {d}}`. -/
theorem volume_setOf_cross_eq_zero (d c : Work.LWP.R3) (hd : d ≠ 0) :
    MeasureTheory.volume {y : Work.LWP.R3 | crossProduct d (c - y) = 0} = 0 := by
  have hd' : ((d : Work.LWP.R3) : Fin 3 → ℝ) ≠ 0 := by simpa using hd
  -- the line through `c` with direction `d` is the strict vector subspace `span {d}`, shifted by `c`
  set S : Submodule ℝ Work.LWP.R3 := Submodule.span ℝ {d} with hS
  have hSne : S ≠ ⊤ := by
    intro h
    have h1 : Module.finrank ℝ S = 1 := by
      rw [hS]; exact finrank_span_singleton (K := ℝ) hd
    have h2 : Module.finrank ℝ S = 3 := by
      rw [h, finrank_top, finrank_euclideanSpace_fin]
    omega
  -- every point of the zero set lies on the affine hyperplane `(· + -c) ⁻¹' span {d}`
  have hsub : {y : Work.LWP.R3 | crossProduct d (c - y) = 0}
      ⊆ (fun h : Work.LWP.R3 => h + (-c)) ⁻¹' (S : Set Work.LWP.R3) := by
    intro y hy
    rw [Set.mem_preimage, hS]
    refine Submodule.mem_span_singleton.mpr ?_
    -- work with the coordinate vector `v = c - y` of `Fin 3 → ℝ`
    set v : Fin 3 → ℝ := ((y - c : Work.LWP.R3) : Fin 3 → ℝ) with hv
    have hv0 : crossProduct (d : Fin 3 → ℝ) v = 0 := by
      have hcy : ((c - y : Work.LWP.R3) : Fin 3 → ℝ) = -v := by simp [v]
      have hh : crossProduct (d : Fin 3 → ℝ) (-v) = 0 := by rw [← hcy]; exact hy
      rwa [map_neg, neg_eq_zero] at hh
    -- the vector triple product identity: `d ⨯ (d ⨯ v) = (d ⬝ v) • d - (d ⬝ d) • v`
    have hkey := cross_cross_eq_smul_sub_smul' (d : Fin 3 → ℝ) (d : Fin 3 → ℝ) v
    rw [hv0, map_zero] at hkey
    have hdd : (d : Fin 3 → ℝ) ⬝ᵥ (d : Fin 3 → ℝ) ≠ 0 := dotSelf_ne_zero_three hd'
    have hA : ((d : Fin 3 → ℝ) ⬝ᵥ v) • (d : Fin 3 → ℝ)
        = ((d : Fin 3 → ℝ) ⬝ᵥ (d : Fin 3 → ℝ)) • v := sub_eq_zero.mp hkey.symm
    -- hence `v` is a multiple of `d`
    have hveq : v = (((d : Fin 3 → ℝ) ⬝ᵥ (d : Fin 3 → ℝ))⁻¹
        * ((d : Fin 3 → ℝ) ⬝ᵥ v)) • (d : Fin 3 → ℝ) := by
      rw [mul_smul, hA, smul_smul, inv_mul_cancel₀ hdd, one_smul]
    have hyc : ((y + -c : Work.LWP.R3) : Fin 3 → ℝ) = ((y - c : Work.LWP.R3) : Fin 3 → ℝ) := by
      rw [WithLp.ofLp_add, WithLp.ofLp_neg, WithLp.ofLp_sub]; rfl
    refine ⟨((d : Fin 3 → ℝ) ⬝ᵥ (d : Fin 3 → ℝ))⁻¹ * ((d : Fin 3 → ℝ) ⬝ᵥ v), ?_⟩
    rw [WithLp.ext_iff, WithLp.ofLp_smul, hyc, ← hv]
    exact hveq.symm
  -- the affine hyperplane is a translate of the null subspace `span {d}`
  refine MeasureTheory.measure_mono_null hsub ?_
  rw [MeasureTheory.measure_preimage_add_right]
  exact MeasureTheory.Measure.addHaar_submodule MeasureTheory.volume S hSne

end Work.LWP.BiotSavart
