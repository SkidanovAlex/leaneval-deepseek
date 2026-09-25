import Mathlib
import Submission.Work.ClassFieldTower.All
import Submission.Work.ShafarevichKoch.GeneratorRank
import Submission.Work.ShafarevichKoch.GeneratorRankKc

/-!
# `Work.ShafarevichKoch.le_of_isOpen_index_two_Kc`

**Every open index-`2` subgroup of `G_∅ = Gal(Kc_∅/Kc)` contains any open normal subgroup `N`
with `G_∅ ⧸ N ≅ (ℤ/2)^5`.**

The mathematical content is that the generator rank of `G_∅` is exactly `5`, i.e.
`#ProTwoChar Kc M = 2 ^ 5 = 32` (`Work.ShafarevichKoch.card_proTwoChar_Kc_eq_thirtytwo`): since
`G_∅ ⧸ N ≅ (ℤ/2)^5` is abelian of exponent `2`, the subgroup `N` contains the commutator subgroup
and the square subgroup, hence contains the Frattini subgroup `Φ(G_∅)`, and `[G_∅ : N] = 32` forces
`N = Φ(G_∅)`; every index-`2` subgroup contains `Φ(G_∅)`.

The proof below runs the contrapositive: if some index-`2` subgroup `M'` (necessarily open, hence
`G_∅ ⧸ (N ⊓ M')` discrete) does not contain `N`, then `N ⊔ M' = ⊤` and
`A := G_∅ ⧸ (N ⊓ M')` is an abelian group of exponent `2` of order `64 = 2 · 32`; the `64`
homomorphisms `A → 𝔽₂` pull back along the quotient map to `64` distinct *continuous* characters
`G_∅ → 𝔽₂`, contradicting the count `#ProTwoChar Kc M = 32`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open scoped Classical
open scoped IsMulCommutative

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-! ## Counting homomorphisms into `𝔽₂ = Multiplicative (ZMod 2)` -/

/-- The number of additive homomorphisms from a finite `𝔽₂`-vector space to `𝔽₂` equals the order
of the space.  This is the self-duality of finite-dimensional vector spaces over `𝔽₂` in counting
form (`|V| = 2 ^ dim V = |Hom(V, 𝔽₂)|`). -/
theorem natCard_addMonoidHom_zmodTwo {A : Type*} [AddCommGroup A] [Finite A]
    (hA : ∀ x : A, x + x = 0) : Nat.card (A →+ ZMod 2) = Nat.card A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Module (ZMod 2) A :=
    AddCommGroup.zmodModule (n := 2) (fun x => by simpa [two_nsmul] using hA x)
  haveI : Module.Finite (ZMod 2) A := Module.Finite.of_finite
  haveI : Module.Finite (ZMod 2) (Module.Dual (ZMod 2) A) := inferInstance
  rw [Nat.card_congr (AddMonoidHom.toZModLinearMapEquiv 2).toEquiv]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Module.Dual (ZMod 2) A)]
  rw [Subspace.dual_finrank_eq (K := ZMod 2) (V := A)]
  exact (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := A)).symm

/-- **A finite commutative group of exponent `2` has as many homomorphisms to `𝔽₂` as it has
elements.**  (`A` is the additive group of a finite-dimensional `𝔽₂`-vector space, so this is
`natCard_addMonoidHom_zmodTwo` transported along `MonoidHom.toAdditiveLeft`.) -/
theorem natCard_monoidHom_zmodTwo {A : Type*} [Group A] [IsMulCommutative A] [Finite A]
    (hA : ∀ a : A, a * a = 1) : Nat.card (A →* Multiplicative (ZMod 2)) = Nat.card A := by
  have h2 : ∀ x : Additive A, x + x = 0 := fun x => hA x
  calc Nat.card (A →* Multiplicative (ZMod 2))
      = Nat.card (Additive A →+ ZMod 2) :=
        Nat.card_congr (MonoidHom.toAdditiveLeft (α := A) (β := ZMod 2))
    _ = Nat.card (Additive A) := natCard_addMonoidHom_zmodTwo h2
    _ = Nat.card A := rfl

theorem le_of_isOpen_index_two_Kc
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} Work.ClassFieldTower.Kc 2)
    (N : Subgroup (Work.ClassFieldTower.galoisGroup M)) [N.Normal]
    (hNopen : IsOpen (N : Set (Work.ClassFieldTower.galoisGroup M)))
    (e : (Work.ClassFieldTower.galoisGroup M) ⧸ N ≃* (Fin 5 → Multiplicative (ZMod 2)))
    {M' : Subgroup (Work.ClassFieldTower.galoisGroup M)}
    (hM'open : IsOpen (M' : Set (Work.ClassFieldTower.galoisGroup M))) (hM'idx : M'.index = 2) :
    N ≤ M' := by
  classical
  by_contra hcon
  have hM'normal : M'.Normal := Subgroup.normal_of_index_eq_two hM'idx
  haveI : M'.Normal := hM'normal
  -- ### Step 1: `N ⊔ M' = ⊤`
  have hsup : N ⊔ M' = ⊤ := by
    have hle : M' ≤ N ⊔ M' := le_sup_right
    have hdvd : (N ⊔ M').index ∣ 2 := by
      have h := Subgroup.index_dvd_of_le hle
      rwa [hM'idx] at h
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact Subgroup.index_eq_one.mp h1
    · exfalso
      have hrel := Subgroup.relIndex_mul_index hle
      rw [h2, hM'idx] at hrel
      have hr : M'.relIndex (N ⊔ M') = 1 := by omega
      exact hcon (le_trans le_sup_left (Subgroup.relIndex_eq_one.mp hr))
  -- ### Step 2: `[G : N] = 32`
  have hNidx : N.index = 32 := by
    rw [Subgroup.index_eq_card, Nat.card_congr e.toEquiv, Nat.card_fun]
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    rw [h2, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num
  -- ### Step 3: `[G : N ⊓ M'] = 64`
  have hM'relN : M'.relIndex N = 2 := by
    have h1 : M'.relIndex (M' ⊔ N) = M'.relIndex N := Subgroup.relIndex_sup_left N M'
    have h2 : M' ⊔ N = ⊤ := by rw [sup_comm]; exact hsup
    rw [← h1, h2, Subgroup.relIndex_top_right, hM'idx]
  have hinfidx : (N ⊓ M').index = 64 := by
    have h1 := Subgroup.relIndex_mul_index (H := N ⊓ M') (K := N) inf_le_left
    have h2 : (N ⊓ M').relIndex N = M'.relIndex N := Subgroup.inf_relIndex_left N M'
    rw [← h1, h2, hM'relN, hNidx]
  -- ### Step 4: `A := G ⧸ (N ⊓ M')` is abelian of exponent `2` of order `64`
  have hKopen : IsOpen ((N ⊓ M' : Subgroup (galoisGroup M)) : Set (galoisGroup M)) :=
    hNopen.inter hM'open
  have hcardA : Nat.card ((galoisGroup M) ⧸ (N ⊓ M')) = 64 := by
    rw [← Subgroup.index_eq_card (H := N ⊓ M'), hinfidx]
  haveI hfiniteA : Finite ((galoisGroup M) ⧸ (N ⊓ M')) :=
    Subgroup.index_ne_zero_iff_finite.mp (by rw [hinfidx]; norm_num)
  -- commutativity of the two smaller quotients
  have hNcomm : IsMulCommutative ((galoisGroup M) ⧸ N) :=
    IsMulCommutative.of_comm fun a b => e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
  have hM'card : Nat.card ((galoisGroup M) ⧸ M') = 2 := by
    rw [← Subgroup.index_eq_card (H := M'), hM'idx]
  have hM'comm : IsMulCommutative ((galoisGroup M) ⧸ M') :=
    IsMulCommutative.of_comm fun a b =>
      (mulEquiv_zmodTwo_of_card_two _ hM'card).injective (by rw [map_mul, map_mul]; exact mul_comm _ _)
  have hAcomm : IsMulCommutative ((galoisGroup M) ⧸ (N ⊓ M')) := by
    rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
    exact le_inf ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N)).mp hNcomm)
      ((Subgroup.Normal.quotient_commutative_iff_commutator_le (N := M')).mp hM'comm)
  -- exponent `2` of the two smaller quotients
  have hZ2 : ∀ y : Multiplicative (ZMod 2), y * y = 1 := by
    intro y
    have h : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
    simpa [h, pow_two] using pow_card_eq_one' (x := y)
  have hE5 : ∀ x : Fin 5 → Multiplicative (ZMod 2), x * x = 1 := by
    intro x; funext i; exact hZ2 (x i)
  have hN2 : ∀ g : galoisGroup M, g * g ∈ N := by
    intro g
    have key : QuotientGroup.mk' N g * QuotientGroup.mk' N g = 1 := by
      apply e.injective
      rw [map_mul, map_one]
      exact hE5 _
    rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul]
    exact key
  have hM'2 : ∀ g : galoisGroup M, g * g ∈ M' := by
    intro g
    have key : QuotientGroup.mk' M' g * QuotientGroup.mk' M' g = 1 := by
      apply (mulEquiv_zmodTwo_of_card_two _ hM'card).injective
      rw [map_mul, map_one]
      exact hZ2 _
    rw [← QuotientGroup.ker_mk' M', MonoidHom.mem_ker, map_mul]
    exact key
  have hAsq : ∀ a : (galoisGroup M) ⧸ (N ⊓ M'), a * a = 1 := by
    intro a
    refine QuotientGroup.induction_on a ?_
    intro g
    have key : QuotientGroup.mk' (N ⊓ M') g * QuotientGroup.mk' (N ⊓ M') g = 1 := by
      rw [← map_mul, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact ⟨hN2 g, hM'2 g⟩
    simpa [QuotientGroup.mk'_apply] using key
  -- ### Step 5: `64` characters of `G` from the `64` characters of `A`
  have hcountA : Nat.card (((galoisGroup M) ⧸ (N ⊓ M')) →* Multiplicative (ZMod 2)) = 64 := by
    rw [natCard_monoidHom_zmodTwo hAsq, hcardA]
  haveI : Finite (ProTwoChar Kc M) :=
    (Nat.card_ne_zero.mp (by rw [card_proTwoChar_Kc_eq_thirtytwo M]; norm_num)).2
  haveI : DiscreteTopology ((galoisGroup M) ⧸ (N ⊓ M')) := QuotientGroup.discreteTopology hKopen
  have hcont : ∀ ψ : ((galoisGroup M) ⧸ (N ⊓ M')) →* Multiplicative (ZMod 2),
      Continuous (ψ.comp (QuotientGroup.mk' (N ⊓ M'))) := by
    intro ψ
    show Continuous fun x : galoisGroup M => ψ (QuotientGroup.mk' (N ⊓ M') x)
    exact continuous_of_discreteTopology.comp QuotientGroup.continuous_mk
  let f : (((galoisGroup M) ⧸ (N ⊓ M')) →* Multiplicative (ZMod 2)) → ProTwoChar Kc M :=
    fun ψ => ⟨ψ.comp (QuotientGroup.mk' (N ⊓ M')), hcont ψ⟩
  have hinj : Function.Injective f := by
    intro ψ₁ ψ₂ h
    have h1 : ψ₁.comp (QuotientGroup.mk' (N ⊓ M')) = ψ₂.comp (QuotientGroup.mk' (N ⊓ M')) :=
      congrArg Subtype.val h
    refine MonoidHom.ext fun a => ?_
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (N ⊓ M') a
    have h2 := DFunLike.congr_fun h1 g
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply] at h2
    rwa [hg] at h2
  have hle := Nat.card_le_card_of_injective f hinj
  rw [hcountA, card_proTwoChar_Kc_eq_thirtytwo M] at hle
  omega

end Work.ShafarevichKoch
