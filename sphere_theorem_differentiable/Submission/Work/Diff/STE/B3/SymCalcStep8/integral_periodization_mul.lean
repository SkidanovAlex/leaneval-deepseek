import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.B3.integral_unitCube_eq_centreCube

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Unfolding the periodization of a compactly supported function against a periodic weight

For `f : (ι → ℝ) → ℂ` continuous with compact support and `P : (ι → ℝ) → ℂ` continuous and
`1`-periodic, the integral over the unit cube `(0,1]^ι` of the periodization of `f` against
`star P` equals the integral of `f · star P` over the whole space:

`∫_{Q} (∑' m, f (z + m)) · star (P z) = ∫_{ℝ^ι} f x · star (P x)`.

This is the standard unfolding of an integral over `ℝ^ι` into the sum of the integrals of the
lattice translates of `f` over the fundamental domain `Q = (0,1]^ι`; because `P` is periodic the
weight can be pulled out of the lattice sum.  No smoothness is needed — only continuity, compact
support of `f`, and the periodicity of `P`.

The proof is elementary: `HasCompactSupport` bounds the support of `f`, so for all but finitely
many `m : ι → ℤ` the translate `z ↦ f (z + m)` vanishes on the whole cube; hence the lattice sum is
finite, the exchange of sum and integral is an exchange of two finite sums, and the fundamental
domain identity `IsAddFundamentalDomain.integral_eq_tsum''` supplies the unfolding.
-/

noncomputable section

namespace Work.Diff.STE.B3.SymCalcStep8

open MeasureTheory
open scoped BigOperators

theorem integral_periodization_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f P : (ι → ℝ) → ℂ) (hf : Continuous f) (hcs : HasCompactSupport f)
    (hP : Continuous P) (hPp : Work.Diff.STE.Periodic1 P) :
    (∫ z in Work.Diff.STE.unitCube,
        (∑' m : ι → ℤ, f (z + Work.Diff.STE.iVec m)) * star (P z))
      = ∫ x, f x * star (P x) := by
  classical
  -- The unit cube is measurable.
  have hQ : MeasurableSet (Work.Diff.STE.unitCube : Set (ι → ℝ)) :=
    MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ioc)
  -- The two ways of writing a lattice translate of the argument of `f`.
  have hadd : ∀ (m : ι → ℤ) (z : ι → ℝ),
      (fun i : ι => (m i : ℝ)) + z = z + Work.Diff.STE.iVec m := by
    intro m z
    ext i
    simp only [Pi.add_apply, Work.Diff.STE.iVec_apply]
    exact add_comm _ _
  -- A radius bounding the support of `f`.
  obtain ⟨R₀, hR₀⟩ := hcs.isCompact.isBounded.subset_closedBall (0 : ι → ℝ)
  set R : ℝ := |R₀| with hRdef
  have hR : tsupport f ⊆ Metric.closedBall 0 R := by
    intro x hx
    rw [hRdef]
    exact Metric.mem_closedBall.mpr
      (le_trans (Metric.mem_closedBall.mp (hR₀ hx)) (le_abs_self R₀))
  -- A box of lattice vectors such that every translate outside it misses the support.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, R + 1 < (N : ℝ) := exists_nat_gt (R + 1)
  set S : Finset (ι → ℤ) :=
    Fintype.piFinset (fun _ : ι => Finset.Icc (-(N : ℤ)) (N : ℤ)) with hSdef
  have hS_zero : ∀ m : ι → ℤ, m ∉ S → ∀ z : ι → ℝ, z ∈ Work.Diff.STE.unitCube →
      f (z + Work.Diff.STE.iVec m) = 0 := by
    intro m hm z hz
    -- some coordinate of `m` exceeds `N` in absolute value
    have hex : ∃ i : ι, (N : ℤ) < |m i| := by
      by_contra hc
      have hc' : ∀ i : ι, |m i| ≤ (N : ℤ) := by
        intro i
        by_contra h
        exact hc ⟨i, not_le.mp h⟩
      apply hm
      rw [hSdef, Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_Icc]
      exact abs_le.mp (hc' i)
    obtain ⟨i, hi⟩ := hex
    -- `0 < z i ≤ 1`
    have hzi : |z i| ≤ 1 := by
      have hmem : z i ∈ Set.Ioc (0 : ℝ) 1 :=
        Set.mem_pi.mp (show z ∈ Set.pi Set.univ (fun _ : ι => Set.Ioc (0 : ℝ) 1) from hz)
          i (Set.mem_univ i)
      rw [Set.mem_Ioc] at hmem
      rw [abs_le]
      exact ⟨by linarith [hmem.1], hmem.2⟩
    have hmi : R + 1 < |(m i : ℝ)| := by
      have h1 : ((N : ℤ) : ℝ) < ((|m i| : ℤ) : ℝ) := by exact_mod_cast hi
      rw [Int.cast_abs, Int.cast_natCast] at h1
      linarith
    have htri : |(m i : ℝ)| - |z i| ≤ |z i + (m i : ℝ)| := by
      calc |(m i : ℝ)| - |z i| = |(m i : ℝ)| - |-(z i)| := by rw [abs_neg]
        _ ≤ |(m i : ℝ) - (-(z i))| := abs_sub_abs_le_abs_sub _ _
        _ = |z i + (m i : ℝ)| := by rw [sub_neg_eq_add, add_comm]
    have hbound : R < |z i + (m i : ℝ)| := by linarith
    -- consequently `z + m` lies outside the ball containing `tsupport f`
    have hnorm : R < ‖z + Work.Diff.STE.iVec m‖ := by
      have h1 : ‖(z + Work.Diff.STE.iVec m) i‖ ≤ ‖z + Work.Diff.STE.iVec m‖ :=
        norm_le_pi_norm _ i
      rw [show ‖(z + Work.Diff.STE.iVec m) i‖ = |z i + (m i : ℝ)| from by
        simp only [Pi.add_apply, Work.Diff.STE.iVec_apply, Real.norm_eq_abs]] at h1
      linarith
    have hnot : z + Work.Diff.STE.iVec m ∉ tsupport f := by
      intro hmem
      have h2 := Metric.mem_closedBall.mp (hR hmem)
      rw [dist_eq_norm, sub_zero] at h2
      linarith
    by_contra hc
    exact hnot (subset_closure (Function.mem_support.mpr hc))
  -- The integrand of the right hand side, and the individual lattice translates.
  set F : (ι → ℝ) → ℂ := fun x => f x * star (P x) with hFdef
  set G : (ι → ℤ) → (ι → ℝ) → ℂ := fun m z => f (z + Work.Diff.STE.iVec m) * star (P z)
    with hGdef
  have hFcont : Continuous F := by
    show Continuous fun x : ι → ℝ => f x * star (P x)
    exact hf.mul hP.star
  have hFcs : HasCompactSupport F := hcs.mul_right (f' := fun x : ι → ℝ => star (P x))
  have hFint : Integrable F := hFcont.integrable_of_hasCompactSupport hFcs
  have hGcont : ∀ m : ι → ℤ, Continuous (G m) := by
    intro m
    show Continuous fun z : ι → ℝ => f (z + Work.Diff.STE.iVec m) * star (P z)
    exact (hf.comp (continuous_id.add continuous_const)).mul hP.star
  have hGcs : ∀ m : ι → ℤ, HasCompactSupport (G m) := by
    intro m
    have h1 : HasCompactSupport fun z : ι → ℝ => f (z + Work.Diff.STE.iVec m) :=
      hcs.comp_homeomorph (Homeomorph.addRight (Work.Diff.STE.iVec m))
    exact h1.mul_right (f' := fun z : ι → ℝ => star (P z))
  have hGint : ∀ m : ι → ℤ, Integrable (G m) := fun m =>
    (hGcont m).integrable_of_hasCompactSupport (hGcs m)
  -- Step 1: unfold the integral over `ℝ^ι` into the lattice sum over the unit cube.
  have hunfold : (∫ x, F x) = ∑' m : ι → ℤ, ∫ z in Work.Diff.STE.unitCube, F (m +ᵥ z) := by
    have h := MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum''
      (Work.Diff.STE.B3.isAddFundamentalDomain_cube_Ioc (ι := ι) (0 : ℝ)) F hFint
    simpa [Work.Diff.STE.unitCube, zero_add] using h
  -- Step 2: rewrite each translate of `F` as the corresponding translate `G` of `f`, using the
  -- periodicity of `P`.
  have hfold : ∀ m : ι → ℤ,
      (∫ z in Work.Diff.STE.unitCube, F (m +ᵥ z)) = ∫ z in Work.Diff.STE.unitCube, G m z := by
    intro m
    apply MeasureTheory.setIntegral_congr_fun hQ
    intro z _
    show f (m +ᵥ z) * star (P (m +ᵥ z)) = f (z + Work.Diff.STE.iVec m) * star (P z)
    rw [show m +ᵥ z = (fun i : ι => (m i : ℝ)) + z from rfl,
      Work.Diff.STE.B3.Periodic1.add_intVec hPp m z, hadd m z]
  -- Step 3: all but finitely many of the translates vanish on the cube.
  have hfin : ∀ m : ι → ℤ, m ∉ S →
      (∫ z in Work.Diff.STE.unitCube, G m z) = 0 := by
    intro m hm
    have hzero : ∀ z ∈ Work.Diff.STE.unitCube, G m z = 0 := by
      intro z hz
      show f (z + Work.Diff.STE.iVec m) * star (P z) = 0
      rw [hS_zero m hm z hz, zero_mul]
    have h1 : (∫ z in Work.Diff.STE.unitCube, G m z)
        = ∫ z in Work.Diff.STE.unitCube, (fun _ : ι → ℝ => (0 : ℂ)) z :=
      MeasureTheory.setIntegral_congr_fun hQ hzero
    simpa using h1
  -- Step 4: fold the finite sum back inside the integral.
  have hsumint : (∑ m ∈ S, ∫ z in Work.Diff.STE.unitCube, G m z)
      = ∫ z in Work.Diff.STE.unitCube, ∑ m ∈ S, G m z :=
    (MeasureTheory.integral_finsetSum (μ := (volume : Measure (ι → ℝ)).restrict
        Work.Diff.STE.unitCube) S (fun m _ => (hGint m).integrableOn)).symm
  -- Step 5: the finite sum is the product of the periodization with `star P`.
  have hpt : ∀ z ∈ Work.Diff.STE.unitCube,
      (∑ m ∈ S, G m z) = (∑' m : ι → ℤ, f (z + Work.Diff.STE.iVec m)) * star (P z) := by
    intro z hz
    have htsum : (∑' m : ι → ℤ, f (z + Work.Diff.STE.iVec m))
        = ∑ m ∈ S, f (z + Work.Diff.STE.iVec m) :=
      tsum_eq_sum (s := S) (fun m hm => hS_zero m hm z hz)
    rw [htsum, Finset.sum_mul]
  have hptint : (∫ z in Work.Diff.STE.unitCube, ∑ m ∈ S, G m z)
      = ∫ z in Work.Diff.STE.unitCube,
          (∑' m : ι → ℤ, f (z + Work.Diff.STE.iVec m)) * star (P z) :=
    MeasureTheory.setIntegral_congr_fun hQ hpt
  calc (∫ z in Work.Diff.STE.unitCube,
          (∑' m : ι → ℤ, f (z + Work.Diff.STE.iVec m)) * star (P z))
      = ∫ z in Work.Diff.STE.unitCube, ∑ m ∈ S, G m z := hptint.symm
    _ = ∑ m ∈ S, ∫ z in Work.Diff.STE.unitCube, G m z := hsumint.symm
    _ = ∑' m : ι → ℤ, ∫ z in Work.Diff.STE.unitCube, G m z :=
        (tsum_eq_sum (s := S) hfin).symm
    _ = ∑' m : ι → ℤ, ∫ z in Work.Diff.STE.unitCube, F (m +ᵥ z) :=
        tsum_congr (fun m => (hfold m).symm)
    _ = ∫ x, F x := hunfold.symm
    _ = ∫ x, f x * star (P x) := rfl

end Work.Diff.STE.B3.SymCalcStep8
