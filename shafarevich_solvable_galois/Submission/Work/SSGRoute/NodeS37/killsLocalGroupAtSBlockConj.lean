import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.H9.swCrossedValueTwoHelpers
import Submission.Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_squareAtSBlock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `ρ`-twisted stage classes kill the local groups of the `S`-blocks

`Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_squareAtSBlock` says that the stage class `χ_{b_m}` of
the `p = 2` recursion kills the **whole local group** of every finite place that is `k`-conjugate to
`S` and is `2`-adic or non-split in `K`.  Schmidt--Wingberg's p. 16 computation (the bullet
"`σz̃ ∈ K_v^{×2}` at the dyadic and at the ramified places") needs the same statement for the
*conjugate* class `χ_{ρ b_m}` (`ρ = res k K σ`), because the second factor of the local pairing is
the conjugate class.

The proof is the Galois equivariance of the Kummer cochains
(`Work.SSGRoute.H9.CV2.swKummerCocharZMod_conj_equiv`: `χ_{ρ b}(x) = χ_b(v⁻¹ x v)` for a lift `v` of `ρ`)
together with the normality of `K.fixingSubgroup` in `G_k` (`K|k` Galois): for `u` in the local group
of `B`, the element `v⁻¹ u v` lies in the local group of the `k`-conjugate place `v⁻¹ • B`, which
again satisfies the three hypotheses of the base lemma (`IsFinPlace` and the "not split or `2`-adic"
condition are `G_k`-invariant: `not_isSplitIn_or_val_two_conj`).
-/

namespace Work.SSGRoute.NodeS37

open _root_.SSGRoute

open scoped Pointwise

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The `ρ`-twisted stage class kills the local groups of the `S`-blocks.** -/
theorem killsLocalGroupAtSBlockConj {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    {K Λ : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [IsSepClosure ↥K Ω] [FiniteDimensional k Λ] [IsGalois k Λ] (hKΛ : K ≤ Λ)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ 2) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k Λ B ∨ B.valuation (2 : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod 2)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (s : Work.SSGRoute.ZDataTwo.TwoRec.St (K := K))
    (hs : ∀ n, Work.SSGRoute.ZDataTwo.TwoRec.PreTwo (K := K) Λ ζ hζ hζK S y n s)
    (ρ : K ≃ₐ[k] K) (m : ℕ) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (2 : Ω) < 1) →
      ∀ u ∈ SSGRoute.decomp k B ⊓ K.fixingSubgroup,
        Work.SSGRoute.ZSplit.nodeKummerCocharZMod K ζ hζK hζ
          (Units.map ρ.toRingEquiv.toMonoidHom (s.f m).2) u = 0 := by
  intro B hBfin hBS hP u hu
  -- the lift of `ρ` and the translated element
  set g : Ω ≃ₐ[k] Ω := Work.SSGRoute.ZDataMup.galLift K ρ with hg
  have huK : u ∈ K.fixingSubgroup := (Subgroup.mem_inf.mp hu).2
  have huD : u ∈ SSGRoute.decomp k B := (Subgroup.mem_inf.mp hu).1
  have hgu : u • B = B := MulAction.mem_stabilizer_iff.mp huD
  have hgB : g • (g⁻¹ • B) = B := smul_inv_smul g B
  -- the three hypotheses at the translated place `g⁻¹ • B`
  have hB'fin : SSGRoute.IsFinPlace k (g⁻¹ • B) :=
    (SSGRoute.isFinPlace_smul_iff B g⁻¹).mpr hBfin
  have hB'S : ∃ A ∈ S, SSGRoute.IsConjPlace k A (g⁻¹ • B) := by
    obtain ⟨A₀, hA₀, hc⟩ := hBS
    exact ⟨A₀, hA₀, SSGRoute.isConjPlace_trans hc ⟨g⁻¹, rfl⟩⟩
  have hB'P : (¬ SSGRoute.IsSplitIn k K (g⁻¹ • B) ∨ (g⁻¹ • B).valuation (2 : Ω) < 1) :=
    (Work.SSGRoute.ZDataTwo.TwoRec.not_isSplitIn_or_val_two_conj (K := K) hgB).mpr hP
  -- the translated element lies in the local group of the translated place
  have hconjK : g⁻¹ * u * g ∈ K.fixingSubgroup := by
    have hN : (K.fixingSubgroup).Normal := inferInstance
    simpa only [inv_inv] using hN.conj_mem u huK g⁻¹
  have hconjD : g⁻¹ * u * g ∈ SSGRoute.decomp k (g⁻¹ • B) := by
    show (g⁻¹ * u * g) • (g⁻¹ • B) = g⁻¹ • B
    rw [mul_smul, mul_smul, hgB, hgu]
  -- the base lemma at the translated place
  have h0 := Work.SSGRoute.ZDataTwo.TwoRec.claimOfPreTwo_squareAtSBlock (K := K) (Λ := Λ) hKΛ
    ζ hζ hζK S hSfin hSram y hy0 s hs m (g⁻¹ • B) hB'fin hB'S hB'P (g⁻¹ * u * g)
    (Subgroup.mem_inf.mpr ⟨hconjD, hconjK⟩)
  -- the Galois equivariance of the Kummer cochain
  have htwist := Work.SSGRoute.H9.CV2.swKummerCocharZMod_conj_equiv (K := K) ζ hζ hζK (s.f m).2 ρ u
  rw [htwist, ← hg]
  rw [Work.SSGRoute.ZDataTwo.nodeKummerCocharZMod_eq_nodeKummerCochar k Ω K ζ hζK hζ (s.f m).2]
  exact h0

end Work.SSGRoute.NodeS37
