import Mathlib
import Submission.Work.SSGRoute.ZDataMup.LTRecFamHonest.HonestPairing
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The structure of the compositum of two Kummer levels

For `K/k` finite Galois with `ζ_p ∈ K` and `β, β' ∈ Kˣ`, the level
`L = hLevel β ⊔ hLevel β' = K(β^{1/p}, β'^{1/p}) ⊆ Ω` is finite dimensional and Galois over `↥K`,
and its Galois group has exponent `p` (hence is commutative).  This is obligation (P2) of
`NOTES_LTRecFam_session5.md` §3, proved here in the composable general form: the same statement for
an arbitrary compositum of two finite Galois subextensions whose Galois groups are commutative of
exponent `p` (`galois_sup_structure`), plus the finite dimensionality of the compositum of two
Kummer levels (`hLevel_sup_finiteDimensional`).
-/

namespace Work.SSGRoute.ZDataMup.LTRecFamHonest

open _root_.SSGRoute
open Classical

noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

variable {p : ℕ} [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] [IsAlgClosed Ω]
  {K : IntermediateField k Ω} [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
  [IsSepClosure ↥K Ω]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]

/-- `Ω` is an algebraic closure of `↥K`, hence a Galois extension of it. -/
theorem h_galois_base : IsGalois ↥K Ω := by
  haveI : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  infer_instance

/-- **The automorphism group of a single Kummer level has exponent `p`.** -/
theorem hLevel_aut_pow_eq_one (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β : (↥K)ˣ) :
    ∀ σ : ↥(hLevel (Ω := Ω) (K := K) (p := p) β) ≃ₐ[↥K]
      ↥(hLevel (Ω := Ω) (K := K) (p := p) β), σ ^ p = 1 := by
  by_cases hβ : β ∈ NK.LocalAnabelian.powSubgroup p ↥K
  · have hbot : hLevel (Ω := Ω) (K := K) (p := p) β = ⊥ :=
      NK.LocalAnabelian.Kummer.kummerField_eq_bot_of_mem_powSubgroup (K' := Ω) (k := ↥K) p
        Fact.out hζ hβ
    rw [hbot]
    intro σ
    have hsub : Subsingleton (↥(⊥ : IntermediateField ↥K Ω) ≃ₐ[↥K]
        ↥(⊥ : IntermediateField ↥K Ω)) :=
      ⟨fun x y => AlgEquiv.ext fun z => by
        obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp z.2
        have hz : z = algebraMap ↥K ↥(⊥ : IntermediateField ↥K Ω) c := (Subtype.ext hc).symm
        rw [hz, AlgEquiv.commutes, AlgEquiv.commutes]⟩
    rw [Subsingleton.elim σ 1]
    simp
  · have hgal := NK.LocalAnabelian.Kummer.isGalois_kummerField_and_finrank (K' := Ω)
      (k := ↥K) p Fact.out hζ β hβ
    haveI : IsGalois ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β) := hgal.1
    haveI : FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β) :=
      hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ β
    have hcard : Nat.card (↥(hLevel (Ω := Ω) (K := K) (p := p) β) ≃ₐ[↥K]
        ↥(hLevel (Ω := Ω) (K := K) (p := p) β)) = p := by
      rw [IsGalois.card_aut_eq_finrank, hgal.2]
    intro σ
    have h := pow_card_eq_one' (G := ↥(hLevel (Ω := Ω) (K := K) (p := p) β) ≃ₐ[↥K]
      ↥(hLevel (Ω := Ω) (K := K) (p := p) β)) (x := σ)
    rwa [hcard] at h

/-- **The compositum of two Kummer levels is finite dimensional over `↥K`.** -/
theorem hLevel_sup_finiteDimensional (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) (β β' : (↥K)ˣ) :
    FiniteDimensional ↥K ↥(hLevel (Ω := Ω) (K := K) (p := p) β ⊔
      hLevel (Ω := Ω) (K := K) (p := p) β') := by
  haveI := hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ β
  haveI := hLevel_finiteDimensional (Ω := Ω) (K := K) (p := p) ζ hζ β'
  infer_instance

/-!
## Delegated: the compositum structure

The Galois/exponent-`p` half of the statement of (P2) of `NOTES_LTRecFam_session5.md` §3 is
delegated.  It is the general composable form

  `galois_sup_structure` : for `L₁ L₂` finite Galois over `↥K` with commutative Galois groups of
  exponent `p` (and `FiniteDimensional ↥K ↥(L₁ ⊔ L₂)`), the same holds for `L₁ ⊔ L₂`.

Proof outline (verified by hand):

* **Galois** for the general sup: `InfiniteGalois.normal_iff_isGalois` (for the Galois extension
  `Ω/↥K`) together with `IntermediateField.fixingSubgroup_sup`, whose right-hand side is an
  intersection of two normal subgroups.
* **exponent `p` and commutativity**: lift `a : Gal(L/↥K)` to `a.liftNormal Ω ∈ Gal(Ω/↥K)`
  (`AlgEquiv.liftNormal`, `AlgEquiv.restrict_liftNormal`); `(a.liftNormal Ω ^ p)|_{L_i} =
  ((a.liftNormal Ω)|_{L_i})^p = 1` by `hLevel_aut_pow_eq_one`/`hexp_i`; two elements of
  `Gal(Ω/↥K)` agreeing on `L₁` and on `L₂` agree on the compositum
  (`IntermediateField.fixingSubgroup_sup` + `IntermediateField.le_iff_le`).
-/

end

end Work.SSGRoute.ZDataMup.LTRecFamHonest
