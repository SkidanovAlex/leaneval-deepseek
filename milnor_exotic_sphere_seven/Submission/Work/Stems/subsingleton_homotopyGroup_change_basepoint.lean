import Mathlib
import Submission.Work.Stems.cubeBoundaryDense
import Submission.Work.Stems.Collar.Defs
import Submission.Work.Stems.Collar.collar_collapse
import Submission.Work.Stems.Collar.collar_collapse_symm
import Submission.Work.Stems.basepoint_iso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Basepoint change for `HomotopyGroup`

Mathlib's `HomotopyGroup N X x` is the quotient of the generalised loops `Ω^N X x` (continuous maps
`N → I → X` that are `x` on the boundary `Cube.boundary N`) by homotopy relative to that boundary.
Here we prove that triviality of `π_N` is independent of the basepoint inside a path component:
if `γ : Path x y` and `HomotopyGroup N X x` is a subsingleton, then so is `HomotopyGroup N X y`.

The proof splits into three regimes.

* `N` empty: `Ω^N X x` is *all* continuous maps `N → I → X` (`I^N` is a point and there is no
  boundary condition), the homotopy relation is plain homotopy and Mathlib's
  `homotopyGroupEquivZerothHomotopyOfIsEmpty` identifies the group with `ZerothHomotopy X`,
  *uniformly in the basepoint*.

* `N` infinite: the boundary `Cube.boundary N` is dense in the cube `N → I`
  (`dense_cubeBoundary_of_infinite`), and this forces every generalised loop to be null-homotopic
  relative to the boundary — the "jump" homotopy `H (t, z) = f z` for `t = 0`,
  `H (t, z) = x` for `t ≠ 0` is continuous because every neighbourhood of any value of `f`
  contains `x`.  So both sides are subsingletons and there is nothing to prove.

* `N` finite, non-empty: the classical basepoint change, realised by the collar construction of
  `Submission.Work.Stems.Collar`: filling the collar of the cube with `γ` and shrinking the loop
  into the inner cube gives mutually inverse homotopy equivalences of loop spaces.
-/

open scoped Topology Topology.Homotopy unitInterval
open ContinuousMap
open Set Filter

namespace Work.Stems

variable {N X : Type*} [TopologicalSpace X]

/-- **Infinite index type.**  For an infinite `N` the boundary of the cube is dense, and this
forces every generalised loop at any basepoint to be null-homotopic relative to the boundary;
a fortiori `π_N` is trivial at every basepoint. -/
theorem subsingleton_homotopyGroup_of_infinite [Infinite N] (x : X) :
    Subsingleton (HomotopyGroup N X x) := by
  have hdense : Dense (Cube.boundary N : Set (N → I)) := dense_cubeBoundary_of_infinite N
  have key : ∀ (f : Ω^ N X x) (V : Set X), IsOpen V → (∃ z, f z ∈ V) → x ∈ V := by
    intro f V hV hz
    obtain ⟨z, hz⟩ := hz
    obtain ⟨z', hzb, hz'V⟩ := hdense.exists_mem_open (hV.preimage f.1.continuous) ⟨z, hz⟩
    rw [← GenLoop.boundary f z' hzb]
    exact hz'V
  have jump : ∀ f : Ω^ N X x, GenLoop.Homotopic f GenLoop.const := by
    intro f
    have hcont : Continuous (fun q : I × (N → I) => if q.1 = 0 then f q.2 else x) := by
      rw [continuous_iff_continuousAt]
      rintro ⟨t₀, z₀⟩
      by_cases ht : t₀ = 0
      · subst ht
        rw [ContinuousAt, Filter.tendsto_def]
        intro s hs
        obtain ⟨U, hUs, hUopen, hUmem⟩ := mem_nhds_iff.mp hs
        have hUmem' : f (0, z₀).2 ∈ U := by simpa using hUmem
        have hxU : x ∈ U := key f U hUopen ⟨z₀, hUmem'⟩
        have hW : {t : I | t ≠ 1} ×ˢ (f ⁻¹' U) ∈ 𝓝 ((0 : I), z₀) := by
          rw [nhds_prod_eq]
          exact Filter.prod_mem_prod
            (isOpen_ne.mem_nhds (by norm_num : (0 : I) ≠ 1))
            ((hUopen.preimage f.1.continuous).mem_nhds hUmem')
        exact Filter.mem_of_superset hW (fun q hq => by
          obtain ⟨hq1, hq2⟩ := hq
          simp only [Set.mem_ofPred_eq] at hq1
          show (if q.1 = 0 then f q.2 else x) ∈ s
          split_ifs with h
          · exact hUs hq2
          · exact hUs hxU)
      · rw [ContinuousAt]
        have h0 : (if t₀ = 0 then f z₀ else x) = x := by simp [ht]
        rw [h0, Filter.tendsto_def]
        intro s hs
        have hmem : {t : I | t ≠ 0} ×ˢ (Set.univ : Set (N → I)) ∈ 𝓝 (t₀, z₀) := by
          rw [nhds_prod_eq]
          exact Filter.prod_mem_prod (isOpen_ne.mem_nhds ht) Filter.univ_mem
        refine Filter.mem_of_superset hmem (fun q hq => ?_)
        obtain ⟨hq1, -⟩ := hq
        simp only [Set.mem_ofPred_eq] at hq1
        show (if q.1 = 0 then f q.2 else x) ∈ s
        rw [if_neg hq1]
        exact mem_of_mem_nhds hs
    exact ⟨{ toFun := fun q => if q.1 = 0 then f q.2 else x
             continuous_toFun := hcont
             map_zero_left := by intro z; simp
             map_one_left := by intro z; simp [show (1 : I) ≠ 0 by norm_num]
             prop' := by
               intro t z hz
               change (if t = 0 then f z else x) = f z
               by_cases h : t = 0
               · simp [h]
               · simp [h, GenLoop.boundary f z hz] }⟩
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | h f =>
    induction b using Quotient.inductionOn with
    | h g => exact Quotient.sound ((jump f).trans (jump g).symm)

/-- **Empty index type.**  For `IsEmpty N` both groups are `ZerothHomotopy X`. -/
theorem subsingleton_homotopyGroup_of_isEmpty [IsEmpty N] {x y : X}
    (h : Subsingleton (HomotopyGroup N X x)) : Subsingleton (HomotopyGroup N X y) := by
  let ex := homotopyGroupEquivZerothHomotopyOfIsEmpty (N := N) x
  let ey := homotopyGroupEquivZerothHomotopyOfIsEmpty (N := N) y
  refine ⟨fun a b => ey.injective ?_⟩
  have key : ex (ex.symm (ey a)) = ex (ex.symm (ey b)) :=
    congrArg ex (h.elim (ex.symm (ey a)) (ex.symm (ey b)))
  rwa [ex.apply_symm_apply, ex.apply_symm_apply] at key

/-- **Finite non-empty index type.**  Basepoint change: `Work.Stems.basepoint_iso` supplies the
group isomorphism `π_N(X,x) ≃* π_N(X,y)` along `γ` (built from the collar of the cube), and
`Subsingleton` is transported along a bijection. -/
theorem subsingleton_homotopyGroup_change_basepoint_fin [Fintype N] [Nonempty N] {x y : X}
    (γ : Path x y) (h : Subsingleton (HomotopyGroup N X x)) :
    Subsingleton (HomotopyGroup N X y) := by
  classical
  obtain ⟨e⟩ := basepoint_iso (N := N) (X := X) γ
  refine ⟨fun a b => ?_⟩
  have hh : e.symm a = e.symm b := h.elim _ _
  rw [← e.apply_symm_apply a, hh, e.apply_symm_apply b]

/-- If `π_N` is trivial at `x` then it is trivial at `y`, for `x` and `y` joined by a path. -/
theorem subsingleton_homotopyGroup_change_basepoint {N X : Type*} [TopologicalSpace X] {x y : X}
    (γ : Path x y) (h : Subsingleton (HomotopyGroup N X x)) :
    Subsingleton (HomotopyGroup N X y) := by
  by_cases hN : Nonempty N
  · by_cases hfin : Finite N
    · haveI : Fintype N := @Fintype.ofFinite N hfin
      exact subsingleton_homotopyGroup_change_basepoint_fin γ h
    · haveI : Infinite N := ⟨hfin⟩
      exact subsingleton_homotopyGroup_of_infinite y
  · haveI : IsEmpty N := not_nonempty_iff.mp hN
    exact subsingleton_homotopyGroup_of_isEmpty h

end Work.Stems
