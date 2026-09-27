/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The cohomology of a contractible space vanishes in positive degrees

For a simplicial set `S` and a commutative ring `R`, the cohomology `H S R n` was defined in
`Submission/Work/Cohomology/Cohomology.lean` as *cocycles modulo coboundaries*.  Here we prove

`H (TopCat.toSSet.obj X) R n` is a subsingleton for `0 < n` when the topological space `X` is
contractible.

Equivalently, every `n`-cocycle (`n > 0`) of the singular complex of a contractible space is a
coboundary.

The proof is the classical one.  Contradictibility of `X` gives a homotopy between the identity
of `X` and a constant map, hence (via `TopCat.Homotopy.toSSet`) a simplicial homotopy between the
identity of the singular complex `S = TopCat.toSSet.obj X` and a constant simplicial map `c`. The
prism identity (`Work.Cohomology.coboundary_hcochain`) then shows that for a cocycle `u` of degree
`n = m + 1`,

`u - c^* u ∈ boundaries S R (m+1)`.

Now `c` factors as `c = π ≫ v` where `π : S ⟶ Δ[0]` collapses `S` to the point and `v : Δ[0] ⟶ S`
is the vertex corresponding to the point of `X` in which the contraction ends; explicitly
`π ≫ v = SSet.const z` by `SSet.comp_const`.  It remains to see that `c^*u = π^*(v^*u)` is a
coboundary, i.e. that the cohomology of the point `Δ[0]` vanishes in positive degrees
(`cycles_le_boundaries_stdSimplex_zero`): `Δ[0]` has exactly one simplex in each degree, so the
coboundary of a cochain of degree `n` is the alternating sum `Σ_{i<n+1} (-1)^i` times its value,
which is `0` for `n` even and `1` for `n` odd (`Fin.sum_neg_one_pow`); this makes every cocycle of
positive degree on `Δ[0]` either zero or explicitly a coboundary.  Pushing the resulting cochain
back along `π` (`pullbackCo_coboundary`) exhibits `c^*u` as a coboundary, and adding the two
pieces exhibits `u` itself as a coboundary.
-/
import Mathlib
import Submission.Work.Cohomology.Basic
import Submission.Work.Cohomology.Cup
import Submission.Work.Cohomology.coboundary_comp
import Submission.Work.Cohomology.cupOf_coboundary
import Submission.Work.Cohomology.Cohomology
import Submission.Work.Cohomology.H_map_comp
import Submission.Work.Cohomology.H_map_homotopic

open CategoryTheory Simplicial Opposite
open Submission.Cohomology

set_option linter.style.haveILetI false

namespace Work.Cohomology

/-- The standard `0`-simplex `Δ[0]`, the point (terminal) simplicial set. -/
abbrev Pt : SSet.{0} := SSet.stdSimplex.obj ⦋0⦌

/-- The (unique) `k`-simplex of the point `Δ[0]`. -/
noncomputable def ptSimplex (k : ℕ) : Pt _⦋k⦌ :=
  (SSet.stdSimplex.objEquiv (n := ⦋0⦌) (m := op ⦋k⦌)).symm default

/-- The point `Δ[0]` has a single `k`-simplex. -/
lemma subsingleton_ptSimplex_obj (k : ℕ) : Subsingleton (Pt _⦋k⦌) :=
  ⟨fun a b => (SSet.stdSimplex.objEquiv (n := ⦋0⦌) (m := op ⦋k⦌)).injective (by
    show (SSet.stdSimplex.objEquiv (n := ⦋0⦌) (m := op ⦋k⦌)) a
      = (SSet.stdSimplex.objEquiv (n := ⦋0⦌) (m := op ⦋k⦌)) b
    exact Subsingleton.elim _ _)⟩

lemma pullbackCo_id {S : SSet.{0}} (R : Type) [CommRing R] {n : ℕ} (u : Cochain S R n) :
    pullbackCo R (𝟙 S) u = u := by
  ext σ; rfl

/-- Pullback of cochains is contravariantly functorial. -/
lemma pullbackCo_comp {S T U : SSet.{0}} (R : Type) [CommRing R] (f : S ⟶ T) (g : T ⟶ U)
    {n : ℕ} (u : Cochain U R n) :
    pullbackCo R (f ≫ g) u = pullbackCo R f (pullbackCo R g u) := rfl

/-- The cohomology of the point vanishes in positive degrees: every cocycle on `Δ[0]` of degree
`m + 1` is a coboundary. -/
theorem cycles_le_boundaries_stdSimplex_zero (R : Type) [CommRing R] (m : ℕ) :
    cycles Pt R (m + 1) ≤ boundaries Pt R (m + 1) := by
  intro u hu
  rw [cycles, LinearMap.mem_ker] at hu
  rw [boundaries, LinearMap.mem_range]
  by_cases hm : Even m
  · -- degree `m + 1` is odd: the cocycle condition forces `u = 0`
    haveI := subsingleton_ptSimplex_obj (m + 1)
    have hu0 : u = 0 := by
      funext σ
      have h := congrFun hu (ptSimplex (m + 2))
      rw [coboundary_apply] at h
      simp only [Pi.zero_apply] at h
      have hsum : (∑ i : Fin (m + 3), ((-1 : ℤ) ^ (i : ℕ)) • u σ) = 0 := by
        rw [← h]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Subsingleton.elim (Pt.δ i (ptSimplex (m + 2))) σ]
      rw [← Finset.sum_smul, Fin.sum_neg_one_pow] at hsum
      have hE : ¬ Even (m + 3) := by
        rintro ⟨j, hj⟩
        obtain ⟨k, hk⟩ := hm
        omega
      rw [if_neg hE] at hsum
      simpa using hsum
    exact ⟨0, by rw [map_zero, hu0]⟩
  · -- degree `m + 1` is even: the constant cochain with the right value is a primitive
    refine ⟨fun _ => u (ptSimplex (m + 1)), ?_⟩
    haveI := subsingleton_ptSimplex_obj (m + 1)
    funext τ
    rw [coboundary_apply]
    have hsum : (∑ i : Fin (m + 2), ((-1 : ℤ) ^ (i : ℕ)) • u (ptSimplex (m + 1)))
        = u (ptSimplex (m + 1)) := by
      rw [← Finset.sum_smul, Fin.sum_neg_one_pow]
      have hE : ¬ Even (m + 2) := by
        rintro ⟨j, hj⟩
        exact hm ⟨j - 1, by omega⟩
      rw [if_neg hE]
      simp
    rw [hsum, Subsingleton.elim (ptSimplex (m + 1)) τ]

/-- Every positive-degree cocycle of the singular complex of a contractible space is a
coboundary. -/
theorem cycles_le_boundaries_of_contractible (X : TopCat.{0}) (hX : ContractibleSpace X)
    (R : Type) [CommRing R] (m : ℕ) :
    Submission.Cohomology.cycles (TopCat.toSSet.obj X) R (m + 1) ≤
      Submission.Cohomology.boundaries (TopCat.toSSet.obj X) R (m + 1) := by
  intro u hu
  rw [Submission.Cohomology.cycles, LinearMap.mem_ker] at hu
  rw [Submission.Cohomology.boundaries, LinearMap.mem_range]
  -- the contraction gives a simplicial homotopy from the identity to a constant map
  obtain ⟨x₀, hx₀⟩ : ∃ x : X, Nonempty (TopCat.Homotopy (𝟙 X) (TopCat.const (X := X) x)) :=
    let ⟨x, hx⟩ := id_nullhomotopic X
    ⟨x, ⟨hx.some⟩⟩
  obtain ⟨hT⟩ := hx₀
  have hhom : SSet.Homotopy (𝟙 (TopCat.toSSet.obj X))
      (SSet.const (X := TopCat.toSSet.obj X) (TopCat.toSSetObj₀Equiv.symm x₀)) := by
    simpa using hT.toSSet
  -- the constant map factors through the point `Δ[0]`
  set z : (TopCat.toSSet.obj X) _⦋0⦌ := TopCat.toSSetObj₀Equiv.symm x₀ with hz
  set π : TopCat.toSSet.obj X ⟶ Pt :=
    SSet.const (X := TopCat.toSSet.obj X) (ptSimplex 0) with hπ
  set v : Pt ⟶ TopCat.toSSet.obj X := SSet.const (X := Pt) z with hv
  have hcv : π ≫ v = SSet.const (X := TopCat.toSSet.obj X) z := SSet.comp_const π z
  -- the prism identity: `u - c^*u` is a coboundary
  have hstep1 : u - pullbackCo R (SSet.const (X := TopCat.toSSet.obj X) z) u
      ∈ Submission.Cohomology.boundaries (TopCat.toSSet.obj X) R (m + 1) := by
    refine ⟨- hcochain hhom m u, ?_⟩
    rw [map_neg, coboundary_hcochain hhom m u hu, pullbackCo_id R u]
    abel
  -- `c^*u = π^*(v^*u)` is a coboundary because `v^*u` already is one on the point
  have hstep2 : pullbackCo R (SSet.const (X := TopCat.toSSet.obj X) z) u
      ∈ Submission.Cohomology.boundaries (TopCat.toSSet.obj X) R (m + 1) := by
    have hw : pullbackCo R v u ∈ Submission.Cohomology.cycles Pt R (m + 1) :=
      Submission.Cohomology.pullbackCo_mem_cycles v hu
    have hw' : pullbackCo R v u ∈ LinearMap.range (Submission.Cohomology.coboundary Pt R m) :=
      cycles_le_boundaries_stdSimplex_zero R m hw
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hw'
    refine ⟨pullbackCo R π y, ?_⟩
    rw [← Submission.Cohomology.pullbackCo_coboundary R π m y, hy, ← pullbackCo_comp R π v u, hcv]
  have : u = (u - pullbackCo R (SSet.const (X := TopCat.toSSet.obj X) z) u)
      + pullbackCo R (SSet.const (X := TopCat.toSSet.obj X) z) u := by abel
  rw [this]
  exact add_mem hstep1 hstep2

/-- **The cohomology of a contractible space vanishes in positive degrees.** -/
theorem H_subsingleton_of_contractible (X : TopCat.{0}) (hX : ContractibleSpace X)
    (R : Type) [CommRing R] {n : ℕ} (hn : 0 < n) :
    Subsingleton (Submission.Cohomology.H (TopCat.toSSet.obj X) R n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Submodule.Quotient.subsingleton_iff]
  rw [Submodule.eq_top_iff']
  rintro ⟨u, hu⟩
  rw [Submission.Cohomology.boundariesInCycles, Submodule.mem_comap]
  simpa using cycles_le_boundaries_of_contractible X hX R m hu

end Work.Cohomology
