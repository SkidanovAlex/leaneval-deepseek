import Mathlib
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_affine_directional
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_directional_deriv
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_three_swap

namespace Commons.Analysis.Calculus.FDeriv

open scoped Topology
open scoped RealInnerProductSpace BigOperators

/-- If `u` is `C³` on an open set `s`, then `z ↦ (fderiv ℝ u z) z - u z` is `C²` on `s`. -/
lemma contDiffOn_affine_three {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {u : E → ℝ} (hs : IsOpen s) (hu : ContDiffOn ℝ 3 u s) :
    ContDiffOn ℝ 2 (fun z => (fderiv ℝ u z) z - u z) s := by
  rw [hs.contDiffOn_iff]
  intro a ha
  have ha3 : ContDiffAt ℝ 3 u a := hu.contDiffAt (hs.mem_nhds ha)
  have h2 : ContDiffAt ℝ 2 u a := ha3.of_le (by norm_num)
  have hfu : ContDiffAt ℝ 2 (fderiv ℝ u) a := ha3.fderiv_right (m := 2) (by norm_num)
  have hg : ContDiffAt ℝ 2 (fun z => (fderiv ℝ u z) z) a := hfu.clm_apply contDiffAt_id
  exact hg.sub h2

open scoped RealInnerProductSpace in
open scoped BigOperators in
theorem iteratedFDeriv_two_affine_diag {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E) {s : Set E}
    {u : E → ℝ} {x : E} (hs : IsOpen s) (hx : x ∈ s) (hu : ContDiffOn ℝ 3 u s) (i : ι) :
    (iteratedFDeriv ℝ 2 (fun z => (fderiv ℝ u z) z - u z) x) ![v i, v i] =
      (iteratedFDeriv ℝ 2 u x) ![v i, v i]
        + ∑ k : ι, ⟪x, v k⟫ * (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i] := by
  classical
  set f : E → ℝ := fun z => (fderiv ℝ u z) z - u z with hf
  have hxmem : s ∈ 𝓝 x := hs.mem_nhds hx
  have huAt3 : ContDiffAt ℝ 3 u x := hu.contDiffAt hxmem
  have hu2 : ContDiffOn ℝ 2 u s := hu.of_le (by norm_num)
  have hf2 : ContDiffOn ℝ 2 f s := by rw [hf]; exact contDiffOn_affine_three hs hu
  -- differentiability of the relevant pieces at `x`
  have hinnerdiff : ∀ k : ι, DifferentiableAt ℝ (fun y : E => ⟪y, v k⟫) x := by
    intro k
    have heq : (fun y : E => ⟪y, v k⟫) = ⇑(innerSL ℝ (v k)) := by
      ext y
      rw [innerSL_apply_apply, real_inner_comm]
    rw [heq]
    exact (innerSL ℝ (v k)).differentiableAt
  have hgdiff : ∀ k : ι, DifferentiableAt ℝ
      (fun y : E => (iteratedFDeriv ℝ 2 u y) ![v i, v k]) x := by
    intro k
    have h2u : ContDiffAt ℝ 1 (iteratedFDeriv ℝ 2 u) x :=
      huAt3.iteratedFDeriv_right (m := 1) (i := 2) (by norm_num)
    have hcomp : ContDiffAt ℝ 1 (fun y => (iteratedFDeriv ℝ 2 u y) ![v i, v k]) x :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ ![v i, v k]).contDiff.contDiffAt.comp
        x h2u
    exact hcomp.differentiableAt one_ne_zero
  -- Step A : the second derivative of `f` as a derivative of the directional first derivative
  have hA : fderiv ℝ (fun y => fderiv ℝ f y (v i)) x (v i)
      = (iteratedFDeriv ℝ 2 f x) ![v i, v i] := by
    have h := iteratedFDeriv_directional_deriv (E := E) hs hx (n := 1) hf2
      (![v i] : Fin 1 → E) (v i)
    simpa [iteratedFDeriv_one_apply] using h
  -- Step B : the directional first derivative as the explicit sum
  have hfeq : (fun y => fderiv ℝ f y (v i)) =ᶠ[𝓝 x]
      fun y => ∑ k : ι, ⟪y, v k⟫ * (iteratedFDeriv ℝ 2 u y) ![v i, v k] := by
    refine Filter.eventually_of_mem hxmem (fun y hy => ?_)
    rw [hf]
    exact fderiv_affine_directional v hs hy hu2 (v i)
  -- Step C : differentiation under the finite sum, term by term
  have hterm : ∀ k : ι,
      (fderiv ℝ ((fun y : E => ⟪y, v k⟫) * (fun y : E => (iteratedFDeriv ℝ 2 u y) ![v i, v k])) x)
        (v i)
        = (iteratedFDeriv ℝ 2 u x) ![v i, v k] * ⟪v i, v k⟫
          + ⟪x, v k⟫ * (iteratedFDeriv ℝ 3 u x) ![v i, v i, v k] := by
    intro k
    rw [fderiv_mul (hinnerdiff k) (hgdiff k)]
    simp only [add_apply, smul_apply, smul_eq_mul]
    have hinner_val : fderiv ℝ (fun y : E => ⟪y, v k⟫) x (v i) = ⟪v i, v k⟫ := by
      have heq : (fun y : E => ⟪y, v k⟫) = ⇑(innerSL ℝ (v k)) := by
        ext y
        rw [innerSL_apply_apply, real_inner_comm]
      rw [heq, (innerSL ℝ (v k)).fderiv, innerSL_apply_apply, real_inner_comm]
    have hg_val : fderiv ℝ (fun y : E => (iteratedFDeriv ℝ 2 u y) ![v i, v k]) x (v i)
        = (iteratedFDeriv ℝ 3 u x) ![v i, v i, v k] := by
      have h := iteratedFDeriv_directional_deriv (E := E) hs hx (n := 2) hu
        (![v i, v k] : Fin 2 → E) (v i)
      simpa using h
    rw [hinner_val, hg_val]
    ring
  have hsumform : (fun y : E => ∑ k : ι, ⟪y, v k⟫ * (iteratedFDeriv ℝ 2 u y) ![v i, v k])
      = (∑ k : ι, (fun y : E => ⟪y, v k⟫) * (fun y : E => (iteratedFDeriv ℝ 2 u y) ![v i, v k])) := by
    funext y
    rw [Finset.sum_apply]
    simp only [Pi.mul_apply]
  have hΨ_deriv : (fderiv ℝ
        (fun y => ∑ k : ι, ⟪y, v k⟫ * (iteratedFDeriv ℝ 2 u y) ![v i, v k]) x) (v i)
      = ∑ k : ι, ((iteratedFDeriv ℝ 2 u x) ![v i, v k] * ⟪v i, v k⟫
          + ⟪x, v k⟫ * (iteratedFDeriv ℝ 3 u x) ![v i, v i, v k]) := by
    rw [hsumform,
      fderiv_sum (u := Finset.univ)
        (A := fun k => (fun y : E => ⟪y, v k⟫) * (fun y : E => (iteratedFDeriv ℝ 2 u y) ![v i, v k]))
        (fun k _ => (hinnerdiff k).mul (hgdiff k)),
      sum_apply]
    exact Finset.sum_congr rfl (fun k _ => hterm k)
  -- Step D : collapsing the two sums
  have hsumB : (∑ k : ι, (iteratedFDeriv ℝ 2 u x) ![v i, v k] * ⟪v i, v k⟫)
      = (iteratedFDeriv ℝ 2 u x) ![v i, v i] := by
    rw [Finset.sum_eq_single i]
    · rw [OrthonormalBasis.inner_eq_ite v i i, if_pos rfl, mul_one]
    · intro b _ hb
      rw [OrthonormalBasis.inner_eq_ite v i b, if_neg (fun h => hb h.symm), mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hsumA : (∑ k : ι, ⟪x, v k⟫ * (iteratedFDeriv ℝ 3 u x) ![v i, v i, v k])
      = ∑ k : ι, ⟪x, v k⟫ * (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i] := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have h1 := (iteratedFDeriv_three_swap (f := u) hs hx hu (v i) (v i) (v k)).2
    have h2 := (iteratedFDeriv_three_swap (f := u) hs hx hu (v i) (v k) (v i)).1
    rw [h1, h2]
  calc
    (iteratedFDeriv ℝ 2 f x) ![v i, v i]
        = fderiv ℝ (fun y => fderiv ℝ f y (v i)) x (v i) := hA.symm
    _ = (fderiv ℝ (fun y => ∑ k : ι, ⟪y, v k⟫ * (iteratedFDeriv ℝ 2 u y) ![v i, v k]) x) (v i) := by
          rw [Filter.EventuallyEq.fderiv_eq hfeq]
    _ = ∑ k : ι, ((iteratedFDeriv ℝ 2 u x) ![v i, v k] * ⟪v i, v k⟫
          + ⟪x, v k⟫ * (iteratedFDeriv ℝ 3 u x) ![v i, v i, v k]) := hΨ_deriv
    _ = (iteratedFDeriv ℝ 2 u x) ![v i, v i]
          + ∑ k : ι, ⟪x, v k⟫ * (iteratedFDeriv ℝ 3 u x) ![v k, v i, v i] := by
          rw [Finset.sum_add_distrib, hsumB, hsumA]

end Commons.Analysis.Calculus.FDeriv
