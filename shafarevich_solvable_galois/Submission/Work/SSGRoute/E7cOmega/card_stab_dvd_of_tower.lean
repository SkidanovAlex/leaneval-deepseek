import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.decompK_restrict_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E7cOmega

open NK.GlobalCFT

/-- **The stabiliser of a place below divides the stabiliser of a place above.**

For a tower `k ≤ K ≤ L` of number fields with `K/k` and `L/k` finite Galois, and places
`u` of `K`, `v` of `L` with `v` lying over `u`, the stabiliser of `u` in `Gal(K/k)` embeds as
a quotient of the stabiliser of `v` in `Gal(L/k)`: the restriction map
`Gal(L/k) → Gal(K/k)` is surjective and carries `Stab(v)` onto `Stab(u)`.  Hence the order of
the former divides the order of the latter. -/
theorem card_stab_dvd_of_tower {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    (u : NK.GlobalCFT.Place K) (v : NK.GlobalCFT.Place L)
    (hv : NK.GlobalCFT.Place.LiesOver v u) :
    Nat.card (MulAction.stabilizer (K ≃ₐ[k] K) u) ∣ Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) v) := by
  -- The restriction map `galRes` sends the stabiliser of `v` into the stabiliser of `u`:
  -- `σ • v = v` implies `(galRes σ) • u = u`, by equivariance of `LiesOver` and uniqueness
  -- of the place below.
  have hmaps : ∀ σ : MulAction.stabilizer (L ≃ₐ[k] L) v,
      SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L) • u = u := by
    intro σ
    have hσ : (σ : L ≃ₐ[k] L) • v = v := (MulAction.mem_stabilizer_iff).mp σ.2
    have hlies : NK.GlobalCFT.Place.LiesOver ((σ : L ≃ₐ[k] L) • v)
        (SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L) • u) :=
      NK.HassePrinciple.liesOver_smul_of_restrict (K := k) (F := K) (L := L)
        (σ : L ≃ₐ[k] L) (SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L))
        (fun y => AlgEquiv.restrictNormal_commutes (σ : L ≃ₐ[k] L) K y) hv
    rw [hσ] at hlies
    exact NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique hlies hv
  -- The restriction homomorphism between the two stabilisers.
  let f : MulAction.stabilizer (L ≃ₐ[k] L) v →* SSGRoute.PTExt.decompK (k := k) u :=
    { toFun := fun σ => ⟨SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L),
        (MulAction.mem_stabilizer_iff).mpr (hmaps σ)⟩
      map_one' := by apply Subtype.ext; exact map_one (SSGRoute.PTExt.galRes k K L)
      map_mul' := by
        intro a b
        apply Subtype.ext
        exact map_mul (SSGRoute.PTExt.galRes k K L) (a : L ≃ₐ[k] L) (b : L ≃ₐ[k] L) }
  have hf : ∀ σ, ((f σ : SSGRoute.PTExt.decompK (k := k) u) : K ≃ₐ[k] K)
      = SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L) := fun σ => rfl
  -- It is surjective: lift `τ ∈ Stab(u)` to `Gal(L/k)`, then move `σ₀ • v` back to `v` by an
  -- element of `Gal(L/K)`, which is trivial under the restriction.
  have hsurj : Function.Surjective f :=
    Work.SSGRoute.decompK_restrict_surjective k K u L v hv f hf
  -- A surjective homomorphism onto a group makes the target's order divide the source's.
  have key : Nat.card (SSGRoute.PTExt.decompK (k := k) u) ∣
      Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) v) := by
    have h1 : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) v ⧸ MonoidHom.ker f)
        = Nat.card (SSGRoute.PTExt.decompK (k := k) u) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
    rw [← h1]
    exact Subgroup.card_quotient_dvd_card (MonoidHom.ker f)
  exact key

end Work.SSGRoute.E7cOmega
