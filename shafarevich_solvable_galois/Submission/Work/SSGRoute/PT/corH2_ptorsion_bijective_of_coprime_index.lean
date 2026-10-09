import Mathlib
import Submission.Work.SSGRoute.PT.mkb_ld02_defs
import Submission.Work.SSGRoute.PT.corH2_resH2_eq_index
import Submission.Work.SSGRoute.PT.corH2_ptorsion_bij
import Submission.Work.SSGRoute.Nakayama.br_pTorsion
import Submission.Work.SSGRoute.PT.cardH2_units_openSubgroup_decomp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

noncomputable section

universe u

/-- Surjectivity of the corestriction on the `p`-torsion, with *no* hypothesis on the exponent of
the coefficient module: the preimage of `z` constructed in `corH2_ptorsion_surjective` is
`(Nat.gcdA [G:U] p : ℤ) • resH2 U z`, which is `p`-torsion because `resH2 U z` is. -/
theorem corH2_ptorsion_surjective_of_coprime_index
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) [U.FiniteIndex] [Fintype (G ⧸ U)]
    (C : Type u) [AddCommGroup C] [DistribMulAction G C] (p : ℕ) [Fact p.Prime]
    (hcop : (Nat.card (G ⧸ U)).Coprime p) :
    Function.Surjective
      (fun z : {x : Work.AbsoluteKummer.H2 ↥U C // p • x = 0} =>
        (⟨corH2 U hUo C z.1, by rw [← map_nsmul, z.2, map_zero]⟩ :
          {x : Work.AbsoluteKummer.H2 G C // p • x = 0})) := by
  intro z
  have hz : (Nat.card (G ⧸ U)) • z.1 = corH2 U hUo C (resH2 U z.1) :=
    (corH2_resH2 U hUo C z.1).symm
  have hpz : p • z.1 = 0 := z.2
  have hbez := Nat.gcd_eq_gcd_ab (Nat.card (G ⧸ U)) p
  have hgcd : (Nat.gcd (Nat.card (G ⧸ U)) p : ℤ) = 1 := by rw [hcop.gcd_eq_one]; rfl
  rw [hgcd] at hbez
  have hbez' : (Nat.gcdA (Nat.card (G ⧸ U)) p : ℤ) * (Nat.card (G ⧸ U) : ℤ)
      + (Nat.gcdB (Nat.card (G ⧸ U)) p : ℤ) * (p : ℤ) = 1 := by
    rw [mul_comm (Nat.gcdA (Nat.card (G ⧸ U)) p) (Nat.card (G ⧸ U) : ℤ),
      mul_comm (Nat.gcdB (Nat.card (G ⧸ U)) p) (p : ℤ)]
    exact hbez.symm
  have hcomb : ((Nat.gcdA (Nat.card (G ⧸ U)) p : ℤ) * (Nat.card (G ⧸ U) : ℤ)
      + (Nat.gcdB (Nat.card (G ⧸ U)) p : ℤ) * (p : ℤ)) • z.1 = z.1 := by
    rw [hbez', one_smul]
  have hgoal : (Nat.gcdA (Nat.card (G ⧸ U)) p : ℤ)
      • corH2 U hUo C (resH2 U z.1) = z.1 := by
    conv_rhs => rw [← hcomb]
    rw [add_zsmul, mul_zsmul, mul_zsmul, natCast_zsmul, natCast_zsmul, ← hz, hpz,
      smul_zero, add_zero]
  have hres : p • resH2 U z.1 = 0 := by rw [← map_nsmul, z.2, map_zero]
  refine ⟨⟨(Nat.gcdA (Nat.card (G ⧸ U)) p : ℤ) • resH2 U z.1, ?_⟩, ?_⟩
  · rw [nsmul_zsmul_comm, hres, smul_zero]
  · refine Subtype.ext ?_
    show corH2 U hUo C ((Nat.gcdA (Nat.card (G ⧸ U)) p : ℤ) • resH2 U z.1) = z.1
    rw [map_zsmul, hgoal]

/-- **(β)**: for coefficients with `#H²(U,C)[p] = p = #H²(G,C)[p]` and `p ∤ [G : U]`, the
corestriction restricted to the `p`-torsion is bijective.  This is `PT.corH2_ptorsion_bijective`
without the (unused) hypothesis that the coefficient module has exponent `p` — needed for the
coefficient module `\bar k_v^×` itself, which is divisible. -/
theorem corH2_ptorsion_bijective_of_card
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) [U.FiniteIndex] [Fintype (G ⧸ U)]
    (C : Type u) [AddCommGroup C] [DistribMulAction G C] (p : ℕ) [Fact p.Prime]
    (hcop : (Nat.card (G ⧸ U)).Coprime p)
    (hcardU : Nat.card {x : Work.AbsoluteKummer.H2 ↥U C // p • x = 0} = p)
    (hcardG : Nat.card {x : Work.AbsoluteKummer.H2 G C // p • x = 0} = p) :
    Function.Bijective
      (fun z : {x : Work.AbsoluteKummer.H2 ↥U C // p • x = 0} =>
        (⟨corH2 U hUo C z.1, by rw [← map_nsmul, z.2, map_zero]⟩ :
          {x : Work.AbsoluteKummer.H2 G C // p • x = 0})) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : Finite {x : Work.AbsoluteKummer.H2 ↥U C // p • x = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hcardU]; exact hp0)
  haveI : Finite {x : Work.AbsoluteKummer.H2 G C // p • x = 0} :=
    Nat.finite_of_card_ne_zero (by rw [hcardG]; exact hp0)
  haveI : Fintype {x : Work.AbsoluteKummer.H2 ↥U C // p • x = 0} :=
    Fintype.ofFinite _
  haveI : Fintype {x : Work.AbsoluteKummer.H2 G C // p • x = 0} :=
    Fintype.ofFinite _
  have hcard : Fintype.card {x : Work.AbsoluteKummer.H2 ↥U C // p • x = 0}
      = Fintype.card {x : Work.AbsoluteKummer.H2 G C // p • x = 0} := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcardU, hcardG]
  refine ⟨?_, corH2_ptorsion_surjective_of_coprime_index U hUo C p hcop⟩
  exact (corH2_ptorsion_surjective_of_coprime_index U hUo C p hcop).injective_of_finite
    (Fintype.equivOfCardEq hcard)

/-- **The corestriction on the `p`-torsion is bijective for an open subgroup of coprime index.**
Here `G = D_A = decomp k A` and `U ≤ G` is open of finite index coprime to `p`; the coefficient
module is `\bar k_v^× = Units Ω`.

Both `p`-torsion groups have `p` elements — at `D_A` this is the class-formation axiom
`Work.SSGRoute.Nakayama.br_pTorsion`, at the level `U` it is
`Work.SSGRoute.PT.cardH2_units_openSubgroup_decomp` — and `cor` is surjective on the `p`-torsion
because `cor ∘ res = [D_A : U]` with `[D_A : U]` invertible mod `p`
(`corH2_ptorsion_surjective_of_coprime_index`); a surjection between finite groups of equal
cardinality is bijective. -/
theorem corH2_ptorsion_bijective_of_coprime_index
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (U : Subgroup ↥(SSGRoute.decomp k A)) (hUo : IsOpen (U : Set ↥(SSGRoute.decomp k A)))
    [U.FiniteIndex] [Fintype (↥(SSGRoute.decomp k A) ⧸ U)]
    (hcop : (Nat.card (↥(SSGRoute.decomp k A) ⧸ U)).Coprime p) :
    Function.Bijective (fun x : {x : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)) // p • x = 0} =>
      (⟨Work.SSGRoute.PT.corH2 U hUo (Additive (Units Ω)) x.1,
        by rw [← map_nsmul, x.2, map_zero]⟩ :
        {y : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)) //
          p • y = 0})) := by
  have hcardU : Nat.card {x : Work.AbsoluteKummer.H2 ↥U (Additive (Units Ω)) // p • x = 0} = p :=
    cardH2_units_openSubgroup_decomp p k Ω A hA U hUo
  have hcardG : Nat.card {x : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
      (Additive (Units Ω)) // p • x = 0} = p :=
    Work.SSGRoute.Nakayama.br_pTorsion p k Ω A hA
  exact corH2_ptorsion_bijective_of_card U hUo (Additive (Units Ω)) p hcop hcardU hcardG

end

end Work.SSGRoute.PT
