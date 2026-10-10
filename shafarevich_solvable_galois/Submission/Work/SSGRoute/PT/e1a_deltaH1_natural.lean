import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.AbsoluteKummer.SES.deltaH2_exact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the connecting map `δ : H⁰(G,P) → H¹(G,M)`

The degree-zero companion of `PT.e1a_deltaH2_natural`: for a morphism `(ι, κ, π)` of short exact
sequences of discrete `G`-modules (i.e. `κ ∘ S.iota = S'.iota ∘ ι` and `π ∘ S.pi = S'.pi ∘ κ`),

`S'.delta (mapH0 π p) = mapH1 ι (S.delta p)`   for all `p : H⁰(G,P)`.

This is the ingredient the naturalisation of the `E1c` dictionary
(`Ext¹_G(X,Kˣ) ≅ H¹(Γ, Hom_ℤ(X,Ωˣ))`, node `E1a`) needs: the identification of `H¹(Γ, homCoind X)`
with the cokernel of `H⁰(homCoind F_X) → H⁰(homCoind R_X)` is `S.delta`'s surjectivity together with
`ker δ = range (π_*)`, and both are natural in `X` precisely when `delta` is.

*Proof.*  By `delta_apply` both sides are `H1π` of the cocycle `g ↦ ι'⁻¹(g • n - n)` of a lift `n`.
For the left side the lift is `n' := S'.liftOf (mapH0 π p)`; for the right side it is
`κ (S.liftOf p)`, which is another lift of `mapH0 π p` along `S'.pi` (by `h2`).  The difference
`n' - κ n` therefore lies in `ker S'.pi = range S'.iota`, and the difference of the two cocycles is
`d⁰` of `S'.iotaInv (n' - κ n)` — the computation is done after applying `S'.iota` and using that
`S'.iota ∘ ι ∘ S.iotaInv = κ`.
-/

namespace Work.SSGRoute.PT

open Work.AbsoluteKummer

noncomputable section

/-- **Naturality of the connecting map `δ : H⁰(G,P) → H¹(G,M)` under a morphism of short exact
sequences.** -/
theorem e1a_deltaH1_natural {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {M N P M' N' P' : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [AddCommGroup M'] [AddCommGroup N'] [AddCommGroup P']
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    [DistribMulAction G M'] [DistribMulAction G N'] [DistribMulAction G P']
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P)
    (S' : Work.AbsoluteKummer.ShortExactSeq G M' N' P')
    (ι : M →+ M') (κ : N →+ N') (π : P →+ P')
    (hι : Work.GroupCohomology.IsEquivariant G ι)
    (hκ : Work.GroupCohomology.IsEquivariant G κ)
    (hπ : Work.GroupCohomology.IsEquivariant G π)
    (h1 : ∀ m : M, κ (S.iota m) = S'.iota (ι m))
    (h2 : ∀ n : N, π (S.pi n) = S'.pi (κ n))
    (p : Work.AbsoluteKummer.H0 G P) :
    S'.delta (Work.GroupCohomology.mapH0 G π hπ p) =
      Work.AbsoluteKummer.mapH1 ι hι (S.delta p) := by
  rw [S'.delta_apply, S.delta_apply, Work.AbsoluteKummer.mapH1_H1π,
    Work.AbsoluteKummer.H1π_eq_iff]
  -- `κ ∘ (S.liftOf p)` is a lift of `mapH0 π p`, so `n' - κ n` lies in `ker S'.pi`
  have hker : S'.liftOf (Work.GroupCohomology.mapH0 G π hπ p) - κ (S.liftOf p) ∈ S'.pi.ker := by
    rw [AddMonoidHom.mem_ker, map_sub, S'.pi_liftOf, ← h2, S.pi_liftOf]
    exact sub_self _
  refine (Work.AbsoluteKummer.mem_B1_iff _).mpr
    ⟨S'.iotaInv (S'.liftOf (Work.GroupCohomology.mapH0 G π hπ p) - κ (S.liftOf p)), ?_⟩
  funext g
  apply S'.iota_injective
  rw [Work.GroupCohomology.d0_apply, map_sub, S'.iota_equivariant,
    S'.iota_iotaInv (S'.mem_range_of_mem_ker hker)]
  -- expand the difference of the two connecting cocycles
  have hce : ((S'.cocycleOf (S'.liftOf (Work.GroupCohomology.mapH0 G π hπ p))
        (S'.liftOf_invariant _) -
      Work.AbsoluteKummer.mapZ1 ι hι
        (S.cocycleOf (S.liftOf p) (S.liftOf_invariant p)) :
          Work.AbsoluteKummer.Z1 G M') : G → M') g =
      (S'.cocycleOf (S'.liftOf (Work.GroupCohomology.mapH0 G π hπ p))
        (S'.liftOf_invariant _) : G → M') g -
      (Work.AbsoluteKummer.mapZ1 ι hι
        (S.cocycleOf (S.liftOf p) (S.liftOf_invariant p)) : G → M') g := by
    simp only [AddSubgroup.coe_sub, Pi.sub_apply]
  rw [hce, S'.cocycleOf_apply, Work.AbsoluteKummer.mapZ1_apply, S.cocycleOf_apply, map_sub,
    S'.iota_iotaInv (S'.mem_range_of_mem_ker
      (S'.mem_ker_smul_sub (S'.liftOf (Work.GroupCohomology.mapH0 G π hπ p))
        (S'.liftOf_invariant _) g))]
  rw [← h1 (S.iotaInv (g • S.liftOf p - S.liftOf p)),
    S.iota_iotaInv (S.mem_range_of_mem_ker
      (S.mem_ker_smul_sub (S.liftOf p) (S.liftOf_invariant p) g))]
  rw [map_sub, hκ, smul_sub]
  abel

end

end Work.SSGRoute.PT
