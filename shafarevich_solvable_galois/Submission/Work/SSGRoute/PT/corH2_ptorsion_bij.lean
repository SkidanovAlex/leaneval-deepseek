import Mathlib.GroupTheory.Index
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Topology.Algebra.Group.Defs
import Submission.Work.SSGRoute.PT.alphaTwo_beta
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The corestriction on `H²` is bijective on `p`-torsion

For an open subgroup `U` of finite index of a topological group `G`, a `G`-module `C` of exponent
`p` and `p ∤ [G : U]`, the restriction–corestriction identity `cor ∘ res = [G : U] · id`
(`PT.corH2_resH2`) already gives (proved in `PT.alphaTwo_beta`):

* `corH2 U hUo C : H²(U,C) →+ H²(G,C)` is *surjective*;
* `resH2 U : H²(G,C) →+ H²(U,C)` is *injective*.

The *injectivity* of `cor` (equivalently the surjectivity of `res`) is **not** a formal consequence
of that identity: the dual identity `res ∘ cor = [G : U] · id` is false for a general coefficient
module (already in degree `0`, where `res ∘ cor` is the norm `c ↦ Σ_{s ∈ G/U} s · c`).  What *is*
formal, once the two `p`-torsion groups are known to have the same cardinality `p`, is the
bijectivity: a surjective map between finite groups of the same cardinality is injective.

The cardinality input `#H²(U,C)[p] = p = #H²(G,C)[p]` is the level-wise class-formation axiom
Milne, *ADT*, (1.1b) — for the local class formation `(D_A, \bar k_v^×)` it is
`Work.SSGRoute.Nakayama.br_pTorsion` together with `PT.br_pTorsion_openSubgroup`.  This file
isolates the formal step, so that the arithmetic can be supplied independently.
-/

namespace Work.SSGRoute.PT

noncomputable section

universe u

variable {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] (U : Subgroup G)
  [U.FiniteIndex] [Fintype (G ⧸ U)]

/-- `ℕ`-scalars commute with `ℤ`-scalars in an abelian group. -/
theorem nsmul_zsmul_comm {A : Type u} [AddCommGroup A] (n : ℕ) (a : ℤ) (x : A) :
    n • (a • x) = a • (n • x) := by
  simp only [← Nat.cast_smul_eq_nsmul ℤ n]
  rw [← mul_smul, mul_comm (n : ℤ) a, mul_smul]

/-- **The corestriction on the `p`-torsion is surjective**, for coefficients of exponent `p` and
`p ∤ [G : U]`.  This is the `p`-torsion refinement of
`PT.corH2_surjective_of_pTorsion_of_coprime`: the preimage produced there,
`(Nat.gcdA [G:U] p : ℤ) • resH2 U z`, is `p`-torsion because `resH2 U z` is. -/
theorem corH2_ptorsion_surjective (hUo : IsOpen (U : Set G)) (C : Type u) [AddCommGroup C]
    [DistribMulAction G C] (p : ℕ) [Fact p.Prime] (hexp : ∀ c : C, p • c = 0)
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

/-- **(β)**: for coefficients of exponent `p`, `p ∤ [G : U]`, and `#H²(U,C)[p] = p = #H²(G,C)[p]`,
the corestriction is bijective on the `p`-torsion.  The cardinality input is the class-formation
axiom (1.1b) at `U` and at `G`. -/
theorem corH2_ptorsion_bijective (hUo : IsOpen (U : Set G)) (C : Type u) [AddCommGroup C]
    [DistribMulAction G C] (p : ℕ) [Fact p.Prime] (hexp : ∀ c : C, p • c = 0)
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
  refine ⟨?_, corH2_ptorsion_surjective U hUo C p hexp hcop⟩
  exact (corH2_ptorsion_surjective U hUo C p hexp hcop).injective_of_finite
    (Fintype.equivOfCardEq hcard)

end

end Work.SSGRoute.PT
