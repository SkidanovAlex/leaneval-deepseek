import Mathlib
import Submission.Work.SSGRoute.PT.H1Transfer
import Submission.Work.SSGRoute.ExtChain.deltaH2_restriction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transfer of the low-degree connecting map `δ : H⁰(G,P) → H¹(G,M)`

`Work.SSGRoute.PT.h1TransferAddHom` is the transfer of continuous `H¹` along a homeomorphic group
isomorphism `Φ : G' ≃* G` together with a compatible coefficient isomorphism
`Ψ : M' ≃+ M` (`Ψ (g' • m') = Φ g' • Ψ m'`).  This file proves that the connecting map
`S.delta : H⁰(G,P) → H¹(G,M)` of a short exact sequence `0 → M → N → P → 0` of discrete
`G`-modules (`Work.AbsoluteKummer.ShortExactSeq`) is compatible with that transfer:

  `h1Transfer Φ hΦc (refl M) (S'.delta x') = S.delta x`

where `S'` is the *same* short exact sequence regarded as a sequence of `G'`-modules (the same
modules and the same maps `ι`, `π`; only the actions differ, related by `hM`/`hN`/`hP` through
`Φ`) and `x'` is the element of `H⁰(G',P)` with underlying element `x.1`.

The proof is the cochain computation.  With `n' = S'.liftOf x'` the lift of `x'` chosen by the
connecting map, the transferred `δ`-cocycle of `S'` is

  `g ↦ (S'.cocycleOf n' _) (Φ.symm g) = (S'.iotaInv) ((Φ.symm g) •_{G'} n' - n')`,

and `hN` converts its argument to `g •_G n' - n'`; since moreover `S'.iota = S.iota`, so that
`S'.iotaInv = S.iotaInv` (lemma `iotaInv_eq_of_iota_eq`) and also `S'.pi = S.pi`, this is exactly
the `δ`-cocycle of `S` at the lift `n'` — the cocycle comparison `z1Transfer_refl_cocycleOf`.
Two lifts of the same element of `P^G` give the same class in `H¹(G,M)`
(`Work.AbsoluteKummer.ShortExactSeq.class_eq`), which finishes the computation.
-/

namespace Work.SSGRoute.PT

open Work.AbsoluteKummer

/-- `ι⁻¹` depends only on `ι`: two short exact sequences with the same inclusion have the same
inverse-on-the-range map. -/
theorem iotaInv_eq_of_iota_eq {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
    [DistribMulAction G' M] [DistribMulAction G' N] [DistribMulAction G' P]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P)
    (S' : Work.AbsoluteKummer.ShortExactSeq G' M N P)
    (hi : S'.iota = S.iota) (b : N) : S'.iotaInv b = S.iotaInv b := by
  by_cases hb : b ∈ S.iota.range
  · have hb' : b ∈ S'.iota.range := by rwa [hi]
    apply S.iota_injective
    rw [← hi, S'.iota_iotaInv hb', hi, S.iota_iotaInv hb]
  · have hb' : b ∉ S'.iota.range := by simpa [hi] using hb
    unfold Work.AbsoluteKummer.ShortExactSeq.iotaInv
    rw [dif_neg hb', dif_neg hb]

/-- **The transferred `δ`-cocycle of `S'` is the `δ`-cocycle of `S` at the same lift.**  For a
lift `n` of an invariant element whose image in `P` is invariant for *both* actions, the transfer
of the connected cocycle `S'.cocycleOf n` (computed with the `G'`-action on `N`) is the connected
cocycle of `S` at `n`.  This is where the compatibility `hN` of the two actions on `N` and the
equality `S'.iota = S.iota` of the inclusions are used. -/
theorem z1Transfer_refl_cocycleOf {G G' : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [instM : DistribMulAction G M] [instN : DistribMulAction G N] [instP : DistribMulAction G P]
    [instM' : DistribMulAction G' M] [instN' : DistribMulAction G' N]
    [instP' : DistribMulAction G' P]
    (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (hM : ∀ (g' : G') (m : M), instM'.smul g' m = instM.smul (Φ g') m)
    (hN : ∀ (g' : G') (n : N), instN'.smul g' n = instN.smul (Φ g') n)
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P)
    (S' : Work.AbsoluteKummer.ShortExactSeq G' M N P)
    (hi : S'.iota = S.iota)
    (n : N) (hn : (S'.pi n) ∈ H0 G' P) (hn' : (S.pi n) ∈ H0 G P) :
    Work.SSGRoute.PT.z1Transfer Φ hΦc (AddEquiv.refl M) (fun g' m => hM g' m)
      (S'.cocycleOf n hn) = S.cocycleOf n hn' := by
  apply Subtype.ext
  have hcoe := Work.SSGRoute.PT.z1Transfer_coe Φ hΦc (AddEquiv.refl M) (fun g' m => hM g' m)
    (S'.cocycleOf n hn)
  rw [hcoe]
  funext g
  rw [Work.SSGRoute.PT.cochainTransfer_apply]
  rw [ShortExactSeq.cocycleOf_apply, ShortExactSeq.cocycleOf_apply]
  simp only [AddEquiv.refl_apply]
  have hN' : ∀ (g' : G') (n : N), g' • n = Φ g' • n := fun g' n => hN g' n
  rw [hN' (Φ.symm g) n, MulEquiv.apply_symm_apply]
  exact iotaInv_eq_of_iota_eq S S' hi _

theorem h1TransferAddHom_delta {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G']
    {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [instM : DistribMulAction G M] [instN : DistribMulAction G N] [instP : DistribMulAction G P]
    [instM' : DistribMulAction G' M] [instN' : DistribMulAction G' N]
    [instP' : DistribMulAction G' P]
    (Φ : G' ≃* G) (hΦc : Continuous (Φ.symm : G → G'))
    (hM : ∀ (g' : G') (m : M), instM'.smul g' m = instM.smul (Φ g') m)
    (hN : ∀ (g' : G') (n : N), instN'.smul g' n = instN.smul (Φ g') n)
    (hP : ∀ (g' : G') (p : P), instP'.smul g' p = instP.smul (Φ g') p)
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P)
    (S' : Work.AbsoluteKummer.ShortExactSeq G' M N P)
    (hi : S'.iota = S.iota) (hp : S'.pi = S.pi)
    (x : ↥(Work.AbsoluteKummer.H0 G P)) :
    Work.SSGRoute.PT.h1TransferAddHom Φ hΦc (AddEquiv.refl M)
        (fun g' m => hM g' m)
      (S'.delta ⟨x.1, fun g' => (hP g' x.1).trans (x.2 (Φ g'))⟩)
      = S.delta x := by
  set x' : ↥(H0 G' P) := ⟨x.1, fun g' => (hP g' x.1).trans (x.2 (Φ g'))⟩ with hx'
  have hxn : (x' : P) = x.1 := congrArg Subtype.val hx'
  have hpi : S.pi (S'.liftOf x') = x.1 := by
    rw [← hp, S'.pi_liftOf x', hxn]
  have hn'' : (S.pi (S'.liftOf x')) ∈ H0 G P := by rw [hpi]; exact x.2
  have hkey := z1Transfer_refl_cocycleOf Φ hΦc hM hN S S' hi (S'.liftOf x')
    (S'.liftOf_invariant x') hn''
  have step1 : Work.SSGRoute.PT.h1TransferAddHom Φ hΦc (AddEquiv.refl M)
        (fun g' m => hM g' m)
      (S'.delta x')
      = H1π G M (Work.SSGRoute.PT.z1Transfer Φ hΦc (AddEquiv.refl M) (fun g' m => hM g' m)
          (S'.cocycleOf (S'.liftOf x') (S'.liftOf_invariant x'))) :=
    Work.SSGRoute.PT.h1TransferAddHom_mk Φ hΦc (AddEquiv.refl M) (fun g' m => hM g' m)
      (S'.cocycleOf (S'.liftOf x') (S'.liftOf_invariant x'))
  exact step1.trans (((congrArg (H1π G M) hkey).trans
    (S.class_eq hn'' (S.liftOf_invariant x) (hpi.trans (S.pi_liftOf x).symm))).trans
    (S.delta_apply x).symm)

end Work.SSGRoute.PT
