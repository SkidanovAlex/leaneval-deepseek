import Mathlib
import Submission.Lib.Unif2.Commons.Topology.CWComplex.exists_cwComplex_univ_of_isClosed_subspace
import Submission.Lib.Unif2.Commons.Topology.CWComplex.countable_cell_of_secondCountable
import Submission.Lib.Unif2.Commons.Topology.CWComplex.exists_cwComplex_univ_lift_universe
import Submission.Lib.Unif2.Commons.AlgebraicTopology.FundamentalGroup.freeGroup_of_oneDimCWComplex
import Submission.Lib.Unif2.Commons.AlgebraicTopology.FundamentalGroup.pi1_equiv_of_homotopyEquiv
import Submission.Lib.Unif2.Commons.Topology.Homotopy.homotopyEquiv_of_deformationRetract

set_option linter.style.haveILetI false

/-!
# The one page of algebraic topology behind Hubbard 1.1.2 — assembly layer

This module contains the *elementary* part of the subproject "the one page of algebraic topology
that turns `H¹(X,ℝ) = 0` into simple connectivity of an open Riemann surface" (Hubbard,
*Teichmüller theory* Vol. 1, Theorem 1.1.2).

Everything in this file is proved.  The genuinely hard geometric input — that a connected
non-compact Riemann surface is homotopy equivalent to a one-dimensional CW complex
(Johansson/Stallings) — is stated in `Submission/Work/Spine/Spine.lean` as
`Work.Spine.exists_homotopyEquiv_oneDimCWComplex_of_noncompact`, and the two target theorems
`Work.Spine.isFreeGroup_fundamentalGroup_of_noncompact` and
`Work.Spine.simplyConnectedSpace_of_subsingleton_hom_toReal` (in `Submission/Work/Spine/Main.lean`)
are derived from it here.

The contents are:

* `pathConnectedSpace_of_chartedSpace_complex` — a connected space modelled on `ℂ` is path
  connected (it is locally path connected).
* `subsingleton_of_isFreeGroup_of_subsingleton_hom_toReal` — **the algebraic step**: a free group
  with no non-trivial homomorphism to `ℝ` is trivial.
* `simplyConnectedSpace_of_subsingleton_fundamentalGroup` — trivial `π₁` at one point plus path
  connectedness gives `SimplyConnectedSpace`.
* `isFreeGroup_fundamentalGroup_of_cwSpine` — a closed one-dimensional CW spine gives freeness.
* `isFreeGroup_fundamentalGroup_of_homotopyEquiv` — freeness of `π₁` is a homotopy invariant.
* `isFreeGroup_fundamentalGroup_of_oneDimCWComplex` — the packaging used in `Main`.
-/

open scoped ContinuousMap

namespace Work.Spine

open Path.Homotopic

/-! ## Path connectedness of a space modelled on `ℂ` -/

/-- A connected space locally homeomorphic to `ℂ` (in particular a connected Riemann surface) is
path connected. -/
theorem pathConnectedSpace_of_chartedSpace_complex
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X] [ChartedSpace ℂ X] :
    PathConnectedSpace X := by
  haveI : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace ℂ X
  exact PathConnectedSpace.of_locallyPathConnectedSpace

/-! ## The algebraic step -/

/-- **A free group with no non-trivial homomorphism to `ℝ` is trivial.**  A free group of rank
`≥ 1` carries the homomorphism sending one generator to `1 ∈ ℝ` and all others to `0`; hence
`Subsingleton (Additive G →+ ℝ)` forces the set of generators of `G` to be empty, so `G` is the
free group on the empty set, i.e. trivial. -/
theorem subsingleton_of_isFreeGroup_of_subsingleton_hom_toReal
    {G : Type*} [Group G] [IsFreeGroup G] [Subsingleton (Additive G →+ ℝ)] :
    Subsingleton G := by
  have hempty : IsEmpty (IsFreeGroup.Generators G) := by
    refine ⟨fun a => ?_⟩
    let F : G →* Multiplicative ℝ :=
      IsFreeGroup.lift (fun _ : IsFreeGroup.Generators G => Multiplicative.ofAdd (1 : ℝ))
    let φ : Additive G →+ ℝ :=
      { toFun := fun g => Multiplicative.toAdd (F (Additive.toMul g))
        map_zero' := by simp
        map_add' := fun x y => by simp }
    have hFa : F (IsFreeGroup.of a) = Multiplicative.ofAdd (1 : ℝ) := by
      simp [F, IsFreeGroup.lift_of]
    have hφa : φ (Additive.ofMul (IsFreeGroup.of a)) = 1 := by
      have h : φ (Additive.ofMul (IsFreeGroup.of a)) =
          Multiplicative.toAdd (F (IsFreeGroup.of a)) := rfl
      rw [h, hFa]
      simp
    have hzero : φ = 0 := Subsingleton.elim _ _
    rw [hzero] at hφa
    simp at hφa
  haveI : Subsingleton (FreeGroup (IsFreeGroup.Generators G)) := inferInstance
  exact Equiv.subsingleton (IsFreeGroup.toFreeGroup G).toEquiv

/-- A group which is free and carries no non-trivial real character is trivial, in the form in
which the main theorem consumes it. -/
theorem subsingleton_fundamentalGroup_of_isFreeGroup
    {X : Type*} [TopologicalSpace X] (x : X) [IsFreeGroup (FundamentalGroup X x)]
    [Subsingleton (Additive (FundamentalGroup X x) →+ ℝ)] :
    Subsingleton (FundamentalGroup X x) :=
  subsingleton_of_isFreeGroup_of_subsingleton_hom_toReal

/-! ## Trivial `π₁` implies simple connectivity -/

/-- If `X` is path connected and the fundamental group at some point is trivial, then `X` is
simply connected. -/
theorem simplyConnectedSpace_of_subsingleton_fundamentalGroup
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X] (x : X)
    [Subsingleton (FundamentalGroup X x)] : SimplyConnectedSpace X := by
  rw [simply_connected_iff_paths_homotopic]
  refine ⟨inferInstance, fun a b => ⟨fun γ₁ γ₂ => ?_⟩⟩
  have ha : Subsingleton (FundamentalGroup X a) :=
    Equiv.subsingleton
      (FundamentalGroup.fundamentalGroupMulEquivOfPath (PathConnectedSpace.somePath a x)).toEquiv
  obtain ⟨r⟩ := PathConnectedSpace.joined a b
  have key : ∀ γ : Path.Homotopic.Quotient a b, γ = Path.Homotopic.Quotient.mk r := by
    intro γ
    calc γ = γ.trans (Path.Homotopic.Quotient.refl b) := by
            rw [Path.Homotopic.Quotient.trans_refl]
      _ = γ.trans ((Path.Homotopic.Quotient.mk r).symm.trans (Path.Homotopic.Quotient.mk r)) := by
            rw [Path.Homotopic.Quotient.symm_trans]
      _ = (γ.trans (Path.Homotopic.Quotient.mk r).symm).trans (Path.Homotopic.Quotient.mk r) := by
            rw [Path.Homotopic.Quotient.trans_assoc]
      _ = (Path.Homotopic.Quotient.refl a).trans (Path.Homotopic.Quotient.mk r) := by
            have h : Subsingleton (Path.Homotopic.Quotient a a) := ha
            congr 1
            exact Subsingleton.elim _ _
      _ = Path.Homotopic.Quotient.mk r := by
            rw [Path.Homotopic.Quotient.refl_trans]
  exact (key γ₁).trans (key γ₂).symm

/-! ## From a one-dimensional CW spine to freeness of `π₁` -/

/-- **Freeness of `π₁` from a one-dimensional CW spine.**  If the space `X` contains a closed
subspace `G` carrying a CW structure with no cells of dimension `≥ 2`, and `X` is homotopy
equivalent to `G`, then `π₁(X,x)` is free.

The two ingredients are
* `Commons.Topology.CWComplex.exists_cwComplex_univ_of_isClosed_subspace`: a CW structure on a
  closed subspace `G ⊆ X` restricts to one on the subtype `↥G` (with the same cells);
* `Commons.AlgebraicTopology.FundamentalGroup.freeGroup_of_oneDimCWComplex`: `π₁` of a connected
  `T2` space homotopy equivalent to a one-dimensional CW complex is free. -/
theorem isFreeGroup_fundamentalGroup_of_cwSpine
    {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X] (x : X) {G : Set X}
    (hGc : IsClosed G) (hC : @Topology.CWComplex X _ G)
    (hdim : ∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell X _ G hC n))
    (he : Nonempty (ContinuousMap.HomotopyEquiv X ↥G)) :
    IsFreeGroup (FundamentalGroup X x) := by
  obtain ⟨hC', hcell'⟩ := Commons.Topology.CWComplex.exists_cwComplex_univ_of_isClosed_subspace hGc hC
  exact Commons.AlgebraicTopology.FundamentalGroup.freeGroup_of_oneDimCWComplex x
    ⟨↥G, inferInstance, inferInstance, hC', fun n hn => hcell' n (hdim n hn), he⟩

/-- **Freeness of `π₁` from a space-level one-dimensional CW model.**  If `Y` carries a CW
structure on all of itself with no cells of dimension `≥ 2` and `X ≃ₕ Y`, then `π₁(X,x)` is
free.  This is the form consumed by the spine theorem. -/
theorem isFreeGroup_fundamentalGroup_of_oneDimCWComplex
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
    [ConnectedSpace X]
    (x : X) (hC : @Topology.CWComplex Y _ Set.univ)
    (hdim : ∀ n : ℕ, 2 ≤ n → IsEmpty (@Topology.CWComplex.cell Y _ Set.univ hC n))
    (he : Nonempty (ContinuousMap.HomotopyEquiv X Y)) :
    IsFreeGroup (FundamentalGroup X x) :=
  Commons.AlgebraicTopology.FundamentalGroup.freeGroup_of_oneDimCWComplex x
    ⟨Y, inferInstance, inferInstance, hC, hdim, he⟩

/-- **Freeness of `π₁` is a homotopy invariant.** -/
theorem isFreeGroup_fundamentalGroup_of_homotopyEquiv
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y)
    (x : X) [IsFreeGroup (FundamentalGroup Y (e.toFun x))] :
    IsFreeGroup (FundamentalGroup X x) := by
  obtain ⟨φ⟩ := Commons.AlgebraicTopology.FundamentalGroup.pi1_equiv_of_homotopyEquiv e x
  exact IsFreeGroup.ofMulEquiv φ.symm

end Work.Spine
