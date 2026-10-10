import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.ZDataMup.LocalData
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The sum pairing as a bilinear form on the local-data space

The pairing `(a, b) ↦ ∑_{A ∈ T} pair (decomp k A ⊓ G_K) (a A) (b A)` of a local Tate system
`IsLocalTateSystem` is an `𝔽_p`-bilinear form on the level-`K` local-data space `localDataSpace K T`.
The local axioms give additivity in each variable; since `𝔽_p = ZMod p` is generated additively by
`1`, additivity already forces `𝔽_p`-linearity (`zmod_smul_of_add`), so the four bilinearity axioms
are immediate.  This is the pairing whose non-degeneracy (`sum_pair_eq_zero_impEqZero`) is the
input of the maximality argument of the realisation gate.
-/

open scoped Pointwise

namespace Work.SSGRoute.ZDataMup

open _root_.SSGRoute

/-- A function from a `ZMod p`-module to `ZMod p` that is additive is `ZMod p`-linear: `ZMod p` is
generated as an additive group by `1`, so every scalar is the cast of a natural number and
additivity gives the scalar rule by the `nsmul` rule for additive maps. -/
lemma zmod_smul_of_add {p : ℕ} [NeZero p] {M : Type*} [AddCommMonoid M] [Module (ZMod p) M]
    (f : M → ZMod p) (hadd : ∀ x y : M, f (x + y) = f x + f y) (c : ZMod p) (x : M) :
    f (c • x) = c • f x := by
  let g : M →+ ZMod p := AddMonoidHom.mk' f hadd
  have hgm : ∀ y : M, g y = f y := fun y => rfl
  have h := g.map_nsmul c.val x
  rw [hgm] at h
  rw [hgm] at h
  rw [← ZMod.natCast_zmod_val c]
  rw [Nat.cast_smul_eq_nsmul (ZMod p) c.val x,
      Nat.cast_smul_eq_nsmul (ZMod p) c.val (f x)]
  exact h

theorem sumPairing_bilinForm {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [Field Ω]
    [Algebra k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    {pair : Subgroup (Ω ≃ₐ[k] Ω) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ((Ω ≃ₐ[k] Ω) → ZMod p) → ZMod p}
    (hpair : Work.SSGRoute.ZDataMup.IsLocalTateSystem p k Ω K pair)
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A) :
    ∃ B : LinearMap.BilinForm (ZMod p) ↥(Work.SSGRoute.ZDataMup.localDataSpace (p := p) K T),
      ∀ (a b : ↥(Work.SSGRoute.ZDataMup.localDataSpace (p := p) K T)),
        B a b = ∑ A : {A : ValuationSubring Ω // A ∈ T},
          pair (SSGRoute.decomp k A.1 ⊓ K.fixingSubgroup) (a.1 A) (b.1 A) := by
  classical
  have hH : ∀ A : {A : ValuationSubring Ω // A ∈ T},
      ∃ A' : ValuationSubring Ω, IsFinPlace k A' ∧
        decomp k A.1 ⊓ K.fixingSubgroup = decomp k A' ⊓ K.fixingSubgroup :=
    fun A => ⟨A.1, hTfin A.1 A.2, rfl⟩
  have haddL : ∀ (b : ↥(localDataSpace (p := p) K T))
      (a a' : ↥(localDataSpace (p := p) K T)),
      (∑ A : {A : ValuationSubring Ω // A ∈ T},
        pair (decomp k A.1 ⊓ K.fixingSubgroup) ((a + a').1 A) (b.1 A)) =
      (∑ A : {A : ValuationSubring Ω // A ∈ T},
        pair (decomp k A.1 ⊓ K.fixingSubgroup) (a.1 A) (b.1 A)) +
      (∑ A : {A : ValuationSubring Ω // A ∈ T},
        pair (decomp k A.1 ⊓ K.fixingSubgroup) (a'.1 A) (b.1 A)) := by
    intro b a a'
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [Submodule.coe_add, Pi.add_apply]
    exact hpair.additive_left _ (hH A) (a.1 A) (a'.1 A) (b.1 A) (a.2 A) (a'.2 A) (b.2 A)
  have haddR : ∀ (a : ↥(localDataSpace (p := p) K T))
      (b b' : ↥(localDataSpace (p := p) K T)),
      (∑ A : {A : ValuationSubring Ω // A ∈ T},
        pair (decomp k A.1 ⊓ K.fixingSubgroup) (a.1 A) ((b + b').1 A)) =
      (∑ A : {A : ValuationSubring Ω // A ∈ T},
        pair (decomp k A.1 ⊓ K.fixingSubgroup) (a.1 A) (b.1 A)) +
      (∑ A : {A : ValuationSubring Ω // A ∈ T},
        pair (decomp k A.1 ⊓ K.fixingSubgroup) (a.1 A) (b'.1 A)) := by
    intro a b b'
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [Submodule.coe_add, Pi.add_apply]
    exact hpair.additive_right _ (hH A) (a.1 A) (b.1 A) (b'.1 A) (a.2 A) (b.2 A) (b'.2 A)
  refine ⟨LinearMap.mk₂ (ZMod p)
    (fun a b => ∑ A : {A : ValuationSubring Ω // A ∈ T},
      pair (decomp k A.1 ⊓ K.fixingSubgroup) (a.1 A) (b.1 A))
    (fun a a' b => haddL b a a')
    (fun c a b => ?_)
    (fun a b b' => haddR a b b')
    (fun c a b => ?_), ?_⟩
  · exact zmod_smul_of_add (fun a => ∑ A : {A : ValuationSubring Ω // A ∈ T},
      pair (decomp k A.1 ⊓ K.fixingSubgroup) (a.1 A) (b.1 A)) (haddL b) c a
  · exact zmod_smul_of_add (fun b => ∑ A : {A : ValuationSubring Ω // A ∈ T},
      pair (decomp k A.1 ⊓ K.fixingSubgroup) (a.1 A) (b.1 A)) (haddR a) c b
  · intro a b
    rw [LinearMap.mk₂_apply]

end Work.SSGRoute.ZDataMup
