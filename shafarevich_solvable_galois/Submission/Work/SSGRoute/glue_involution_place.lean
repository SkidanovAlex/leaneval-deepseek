import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.NK.NUV2.chebotarev_all0
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# An involution of `G_k` fixes a place of every finite Galois extension of `k`

`Work.SSGRoute.glue_involution_place`: for a number field `k`, an algebraic closure `Ω` of `k`, a
finite Galois extension `K ⊆ Ω` of `k` and any `σ ∈ G_k = Ω ≃ₐ[k] Ω` (in particular an involution,
`σ ^ 2 = 1`), there is a place `w` of `K` whose stabiliser in `Gal(K/k)` contains the image of `σ`.

The proof uses Čebotarev's theorem in its *general-base existence form*: every element `τ` of the
Galois group of a finite Galois extension `K/k` of number fields is a Frobenius element at some
prime `𝔭` of `k`; a Frobenius element fixes a prime `P` above `𝔭` (`NK.Chebotarev.IsFrobAtStabilizes`),
and the induced action of `Gal(K/k)` on the finite place `Place.ofFinite P` is exactly the action on
the prime ideal, so `τ` stabilises `Place.ofFinite P`.  If `res σ = 1` any place will do.
-/

namespace Work.SSGRoute

open scoped Pointwise NumberField

/-- **Čebotarev's theorem in existence form over an arbitrary number-field base.**

Every element of the Galois group of a finite Galois extension of number fields is a Frobenius
element at infinitely many primes of the base field.

This is the general-base form `NK.ChebotarevGeneral.ChebotarevInfinite`, assembled here from the
proven route to the *abelian* case of Čebotarev's density theorem over an arbitrary base
(`NK.NUV2.abelianChebotarevDensity_of_freeInputs`, whose two inputs are the Hecke analytic input
`NK.NUV2.heckeInput_proved` and the ideal-theoretic Artin reciprocity law
`NK.NUV2.artinReciprocityIdeal_of_auxField`), together with Deuring's transfer in existence form
(`NK.ChebotarevGeneral.infinite_frobSet_of_abelian`). -/
theorem chebotarevInfinite_type0 : NK.ChebotarevGeneral.ChebotarevInfinite :=
  NK.ChebotarevGeneral.infinite_frobSet_of_abelian
    (NK.NUV2.abelianChebotarevDensity_of_freeInputs NK.NUV2.heckeInput_proved
      (NK.NUV2.artinFrobeniusInputFree_of_artinReciprocityIdeal
        (NK.NUV2.artinReciprocityIdeal_of_auxField
          (fun K L _ _ _ _ _ _ _ _ _ m hm => NK.NUV2.ChebAux.kernelLe_of_auxField K L m hm)
          (fun K L _ _ _ _ _ _ _ _ m hm => NK.CFTLib.ARL.auxField_exists_B K L m hm))))

/-- The ring automorphism of `𝓞 L` induced by `σ : Gal(L/k)` in the sense used by the Galois
action on the places of `L` (`NK.GlobalCFT.Place.smulHeightOneSpectrum`) is the restriction of `σ`
to the ring of integers (`galRestrict`). -/
theorem ringOfIntegersEquiv_eq_galRestrict {k L : Type*} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] (σ : Gal(L/k)) :
    (NK.GlobalCFT.Place.ringOfIntegersEquiv σ : NumberField.RingOfIntegers L →+*
        NumberField.RingOfIntegers L) =
      (galRestrict (NumberField.RingOfIntegers k) k L (NumberField.RingOfIntegers L) σ :
        NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L) := by
  refine RingHom.ext fun x => ?_
  have hL : ((NK.GlobalCFT.Place.ringOfIntegersEquiv σ x : NumberField.RingOfIntegers L) : L) =
      σ ((x : L)) := by
    rw [NK.GlobalCFT.Place.ringOfIntegersEquiv_apply]
  have hR : ((galRestrict (NumberField.RingOfIntegers k) k L (NumberField.RingOfIntegers L) σ x :
      NumberField.RingOfIntegers L) : L) = σ ((x : L)) := by
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap, algebraMap_galRestrict_apply,
      ← NumberField.RingOfIntegers.coe_eq_algebraMap]
  exact NumberField.RingOfIntegers.coe_injective (by
    rw [← NumberField.RingOfIntegers.coe_eq_algebraMap,
      ← NumberField.RingOfIntegers.coe_eq_algebraMap]
    exact hL.trans hR.symm)

/-- **The stabiliser of a finite place of a Galois number field is the set of elements preserving
the underlying prime ideal.**

For a finite Galois extension `L/k` of number fields, `σ : Gal(L/k)` and a nonzero prime `q` of
`𝓞 L`, the place `Place.ofFinite q` is fixed by `σ` (`NK.GlobalCFT.Place` carries the natural
action of `Gal(L/k)`) if and only if `σ` maps the prime ideal `q` to itself. -/
theorem mem_stabilizer_ofFinite_iff {k L : Type*} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (σ : Gal(L/k)) :
    σ ∈ MulAction.stabilizer (Gal(L/k)) (NK.GlobalCFT.Place.ofFinite q) ↔
      Ideal.map (↑(galRestrict (NumberField.RingOfIntegers k) k L
        (NumberField.RingOfIntegers L) σ)) q.asIdeal = q.asIdeal := by
  rw [MulAction.mem_stabilizer_iff, NK.GlobalCFT.Place.smul_ofFinite,
    NK.GlobalCFT.Place.ofFinite_inj, IsDedekindDomain.HeightOneSpectrum.ext_iff,
    NK.GlobalCFT.Place.smulHeightOneSpectrum_asIdeal]
  exact iff_of_eq (congrArg
    (fun f : NumberField.RingOfIntegers L →+* NumberField.RingOfIntegers L =>
      Ideal.map f q.asIdeal = q.asIdeal)
    (ringOfIntegersEquiv_eq_galRestrict σ))

theorem glue_involution_place (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField K] (σ : Ω ≃ₐ[k] Ω) (hσ : σ ^ 2 = 1) :
    ∃ w : NK.GlobalCFT.Place ↥K,
      (Subgroup.zpowers σ).map (SSGRoute.res k K) ≤
        MulAction.stabilizer (↥K ≃ₐ[k] ↥K) w := by
  by_cases hτ : SSGRoute.res k K σ = 1
  · refine ⟨Sum.inl (Classical.arbitrary _), ?_⟩
    rw [MonoidHom.map_zpowers, hτ, Subgroup.zpowers_one_eq_bot]
    exact bot_le
  · have hinf : (NK.ChebotarevGeneral.frobSet (K := k) (N := ↥K)
        (SSGRoute.res k K σ)).Infinite :=
      chebotarevInfinite_type0 k ↥K (SSGRoute.res k K σ)
    obtain ⟨𝔭, h𝔭⟩ := hinf.nonempty
    rw [NK.ChebotarevGeneral.mem_frobSet] at h𝔭
    obtain ⟨P, hP, hfrob⟩ := h𝔭
    refine ⟨NK.GlobalCFT.Place.ofFinite P, ?_⟩
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le,
      mem_stabilizer_ofFinite_iff P (SSGRoute.res k K σ)]
    exact NK.Chebotarev.IsFrobAtStabilizes (K := k) (L := ↥K) hfrob

end Work.SSGRoute
