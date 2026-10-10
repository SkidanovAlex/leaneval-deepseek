import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Algebra.Group.Subgroup
import Submission.Work.SSGRoute.ExtChain.deltaH2_restriction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The degree-zero connecting map `δ` commutes with restriction to a subgroup

For a short exact sequence `0 → M → N → P → 0` of discrete `G`-modules
(`Work.AbsoluteKummer.ShortExactSeq`) and a subgroup `U ≤ G`, the degree-zero connecting map
`δ : H⁰(G,P) → H¹(G,M)` (continuous model, `Work.AbsoluteKummer.ShortExactSeq.delta`) commutes with
restriction to `U`:

  `resH1 U (S.delta x) = (S|U).delta (x|U)`,

where `S|U = Work.SSGRoute.ExtChain.restrictSES S U` is the same short exact sequence with the
action restricted to `U` (`Work.SSGRoute.PT.H2Fin.resH1` is the restriction on `H¹`).

This is the degree-zero companion of `Work.SSGRoute.ExtChain.deltaH2_restriction`.  The two sides
are `H¹π` of the cocycles `u ↦ ι⁻¹(u • n - n)` for lifts `n` of `x`; the restriction map is
computed cocycle-wise (`resH1_H1π`), restricting a `G`-cocycle to `U` is literally the same
function on values (`resZ1` agrees with `cocycleOf` for the restricted sequence, because the
underlying `ι` and hence `ι⁻¹` are unchanged), and the residual difference of the two lifts is
killed by `class_eq`.
-/

namespace Work.SSGRoute.PT

/-- **The degree-zero connecting map on any lift.**  If `n : N` lifts `p ∈ H⁰(G,P)` along `S.pi`,
then `S.delta p` is the class of the cocycle `g ↦ ι⁻¹(g • n - n)`; this is the lift-independence
statement `class_eq` combined with the definition of `δ`. -/
theorem delta_eq_H1π_cocycleOf {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) (n : N)
    (hn : (S.pi n) ∈ Work.AbsoluteKummer.H0 G P) (p : ↥(Work.AbsoluteKummer.H0 G P))
    (hp : S.pi n = (p : P)) :
    S.delta p = Work.AbsoluteKummer.H1π G M (S.cocycleOf n hn) := by
  rw [S.delta_apply]
  exact S.class_eq (S.liftOf_invariant p) hn (by rw [S.pi_liftOf, hp])

/-- **The cocycle of the restriction is the restriction of the cocycle.**  For a subgroup `U ≤ G`
and `n : N` whose image in `P` is invariant, the `U`-cocycle of `n` for the restricted sequence
`S|U` is the restriction (`resZ1`) of the `G`-cocycle of `n` for `S`: both are the function
`u ↦ ι⁻¹(u • n - n)`, the two `ι⁻¹` being the same because `(S|U).iota = S.iota` and the
`U`-action on `N` is the restriction of the `G`-action. -/
theorem restrictSES_cocycleOf {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) (U : Subgroup G) (n : N)
    (hn : (S.pi n) ∈ Work.AbsoluteKummer.H0 G P)
    (hn' : ((Work.SSGRoute.ExtChain.restrictSES S U).pi n) ∈ Work.AbsoluteKummer.H0 ↥U P) :
    Work.SSGRoute.PT.H2Fin.resZ1 U M (S.cocycleOf n hn)
      = (Work.SSGRoute.ExtChain.restrictSES S U).cocycleOf n hn' :=
  Subtype.ext (funext (fun _ => rfl))

theorem delta_restrictSES {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P) (U : Subgroup G)
    (x : ↥(Work.AbsoluteKummer.H0 G P)) :
    Work.SSGRoute.PT.H2Fin.resH1 U M (S.delta x) =
      (Work.SSGRoute.ExtChain.restrictSES S U).delta ⟨x.1, fun u => x.2 (u : G)⟩ := by
  classical
  let S' : Work.AbsoluteKummer.ShortExactSeq ↥U M N P :=
    Work.SSGRoute.ExtChain.restrictSES S U
  let x' : ↥(Work.AbsoluteKummer.H0 ↥U P) := ⟨x.1, fun u => x.2 (u : G)⟩
  change Work.SSGRoute.PT.H2Fin.resH1 U M (S.delta x) = S'.delta x'
  -- the `G`-lift `S.liftOf x` is also a `U`-lift of `x'`
  have hpi : S'.pi (S.liftOf x) = x'.1 := by
    rw [show S'.pi = S.pi from rfl, S.pi_liftOf]
  have hnU : (S'.pi (S.liftOf x)) ∈ Work.AbsoluteKummer.H0 ↥U P := by
    rw [hpi]
    exact x'.2
  -- both sides are `H¹π` of the same restricted cocycle
  have hleft : Work.SSGRoute.PT.H2Fin.resH1 U M (S.delta x)
      = Work.AbsoluteKummer.H1π ↥U M (S'.cocycleOf (S.liftOf x) hnU) := by
    rw [S.delta_apply, Work.SSGRoute.PT.H2Fin.resH1_H1π,
      restrictSES_cocycleOf S U (S.liftOf x) (S.liftOf_invariant x) hnU]
  have hright : S'.delta x'
      = Work.AbsoluteKummer.H1π ↥U M (S'.cocycleOf (S.liftOf x) hnU) := by
    rw [S'.delta_apply]
    refine S'.class_eq (S'.liftOf_invariant x') hnU ?_
    rw [S'.pi_liftOf]
    exact hpi.symm
  rw [hleft, hright]

end Work.SSGRoute.PT
