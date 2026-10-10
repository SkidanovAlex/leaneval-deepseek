import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E7cOmega.lam_zero_of_no_p_dvd_level
import Submission.Work.SSGRoute.PT.archYoneda_perfect
import Submission.Work.SSGRoute.augSES_shortExact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT.G1plusOwn

open SSGRoute.PTExt CategoryTheory

/-- **Restriction to a subgroup of order `1` or `2` kills `H¹` with coefficients of odd exponent
`p`.**  An element of `H¹(D, A)` is killed by `p` because `A` has exponent `p`, and by
`Nat.card D` by the restriction–corestriction argument; if `Nat.card D` is `1` or `2` and `p` is
an odd prime these two annihilators are coprime (or already `1`). -/
lemma extHRestrict_eq_zero_of_natCard_eq_one_or_two
    {G : Type} [Group G] (p : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (D : Subgroup G) (hD : Nat.card D = 1 ∨ Nat.card D = 2)
    (A : Rep.{0} SSGRoute.PTExt.Coeff G) (hA : ∀ a : A, p • a = 0)
    (y : SSGRoute.PTExt.extH A 1) :
    SSGRoute.PTExt.extHRestrict D y = 0 := by
  haveI hfin : Finite ↥D :=
    Nat.finite_of_card_ne_zero (by rcases hD with h | h <;> rw [h] <;> norm_num)
  haveI hft : Fintype ↥D := Fintype.ofFinite ↥D
  -- `Nat.card D` kills the restricted class (restriction–corestriction)
  have hcard : Nat.card ↥D • SSGRoute.PTExt.extHRestrict D y = 0 :=
    Work.SSGRoute.extH_natCard_smul_eq_zero (Rep.res D.subtype A) (n := 1) (by norm_num)
      (SSGRoute.PTExt.extHRestrict D y)
  rcases hD with h1 | h2
  · rw [h1, one_smul] at hcard
    exact hcard
  · -- `p` kills the restricted class because the coefficients have exponent `p`
    have hpy : p • SSGRoute.PTExt.extHRestrict D y = 0 :=
      Work.SSGRoute.E7cOmega.extH_nsmul_eq_zero_of_pTorsion (p := p)
        (Rep.res D.subtype A) (fun a => hA a) (SSGRoute.PTExt.extHRestrict D y)
    rw [h2] at hcard
    have hndvd : ¬ p ∣ 2 := by
      intro hd
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
      exact hp (le_antisymm hle (Fact.out : p.Prime).two_le)
    exact Work.SSGRoute.E7cOmega.eq_zero_of_pTorsion_of_coprime hpy
      (Nat.coprime_comm.mpr ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hndvd)) hcard

/-- The stabilizer of an archimedean place of `L` in `Gal(L/k)` has order `1` or `2`. -/
lemma nat_card_stabilizer_ofInfinite_eq_one_or_two
    (k L : Type) [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L]
    (v : NumberField.InfinitePlace L) :
    Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite v)) = 1 ∨
      Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite v)) = 2 := by
  have h : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite v) =
      MulAction.stabilizer Gal(L/k) v := by
    ext σ
    simp [MulAction.mem_stabilizer_iff]
  rw [h]
  exact NumberField.InfinitePlace.nat_card_stabilizer_eq_one_or_two k v

theorem extHRestrict_infinite_eq_zero
    (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K]
    (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (v : NumberField.InfinitePlace ↥L)
    (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k (↥K) (↥L))
        (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))) 1) :
    SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k)
        (NK.GlobalCFT.Place.ofInfinite v)) h = 0 := by
  -- the coefficient module `M^∨ ⊗ T` has exponent `p`
  have hA' : ∀ a : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T), p • a = 0 := by
    intro a
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) p a, ZMod.natCast_self, zero_smul]
  have hA : ∀ a : ↥(Rep.res (SSGRoute.PTExt.galRes k (↥K) (↥L))
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T)))), p • a = 0 :=
    fun a => hA' a
  exact extHRestrict_eq_zero_of_natCard_eq_one_or_two (G := ↥L ≃ₐ[k] ↥L) p hp
    (SSGRoute.PTExt.decompK (k := k) (NK.GlobalCFT.Place.ofInfinite v))
    (nat_card_stabilizer_ofInfinite_eq_one_or_two k ↥L v)
    (Rep.res (SSGRoute.PTExt.galRes k (↥K) (↥L))
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K)
        (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) M T))))
    hA h

end Work.SSGRoute.PT.G1plusOwn
