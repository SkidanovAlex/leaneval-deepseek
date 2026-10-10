import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Submission.Work.SSGRoute.cyclicNormCriterion_rep
import Submission.Work.SSGRoute.groupCohomology_levelInf_nat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1600000

namespace Work.SSGRoute

open CategoryTheory
open SSGRoute.PTExt

noncomputable section

/- `ULift.module` and friends compete with the module structure stored in a representation; prefer
the structure instances, as in `powHomRepDefs.lean`. -/
attribute [local instance 10000] Rep.hV2 Rep.hV1
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero

/-! ## 1. The `N`-invariants of a `G`-module as a `G ⧸ N`-module -/

variable {G : Type} [Group G] (N : Subgroup G) [N.Normal]

/-- A `G`-fixed element of `A` is an `N`-invariant element. -/
lemma quotNormInv_mem (A : Rep Coeff G) (a : A) (hafix : ∀ σ : G, A.ρ σ a = a) :
    a ∈ Representation.invariants (A.ρ.comp N.subtype) := by
  rw [Representation.mem_invariants]
  intro n
  exact hafix (n : G)

/-- **The element of `A^N` attached to a `G`-fixed element `a : A`.** -/
def quotNormInv (A : Rep Coeff G) (a : A) (hafix : ∀ σ : G, A.ρ σ a = a) :
    A.quotientToInvariants N :=
  ⟨a, quotNormInv_mem N A a hafix⟩

@[simp] lemma quotNormInv_coe (A : Rep Coeff G) (a : A) (hafix : ∀ σ : G, A.ρ σ a = a) :
    ((quotNormInv N A a hafix : A.quotientToInvariants N) : A) = a := rfl

/-- The element `a ∈ A^N` is fixed by `G ⧸ N` when `a` is fixed by `G`. -/
lemma quotNormInv_rho (A : Rep Coeff G) (a : A) (hafix : ∀ σ : G, A.ρ σ a = a) (q : G ⧸ N) :
    (A.quotientToInvariants N).ρ q (quotNormInv N A a hafix) = quotNormInv N A a hafix := by
  apply Subtype.ext
  induction q using QuotientGroup.induction_on with
  | _ g =>
    show (A.ρ g a : A) = a
    exact hafix g

/-- **The norm of `A^N` over the quotient.**  The norm endomorphism of the `G ⧸ N`-module `A^N`
evaluated at `b` is the sum of the coset representatives. -/
lemma quotNormInv_norm_apply [Fintype G] [Fintype (G ⧸ N)] (A : Rep Coeff G)
    (b : A.quotientToInvariants N) :
    ((Rep.norm (A.quotientToInvariants N)).hom b : A) =
      ∑ x : G ⧸ N, A.ρ (Quotient.out x) (b : A) := by
  rw [CFTSide.norm_apply_eq_sum_coeff]
  rw [Submodule.coe_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  have hq : QuotientGroup.mk' N (Quotient.out x) = x := QuotientGroup.out_eq' x
  conv_lhs => rw [← hq]
  rfl

/-- **The goal's 'norm over the quotient' condition is the norm of `A^N`.** -/
lemma quotNormInv_exists_iff [Fintype G] [Fintype (G ⧸ N)] (A : Rep Coeff G) (a : A)
    (hafix : ∀ σ : G, A.ρ σ a = a) :
    (∃ b : A, (∀ n : N, A.ρ (n : G) b = b) ∧
        (∑ x : G ⧸ N, A.ρ (Quotient.out x) b) = a) ↔
      ∃ bB : A.quotientToInvariants N,
        (Rep.norm (A.quotientToInvariants N)).hom bB = quotNormInv N A a hafix := by
  constructor
  · rintro ⟨b, hbN, hsum⟩
    refine ⟨⟨b, ?_⟩, ?_⟩
    · rw [Representation.mem_invariants]
      intro n
      exact hbN n
    · apply Subtype.ext
      rw [quotNormInv_norm_apply N A]
      exact hsum
  · rintro ⟨bB, hbB⟩
    refine ⟨(bB : A), ?_, ?_⟩
    · intro n
      exact bB.2 n
    · rw [← quotNormInv_norm_apply N A bB, hbB]
      rfl

/-! ## 2. The coefficient map `1 ↦ a` as the inflation of the coefficient map `1 ↦ a` -/

/-- **The coefficient map `1 ↦ a` factors through the quotient.**  For a `G`-fixed `a : A` and
`aB ∈ A^N` its image, the `G`-linear map `ℤ → A`, `1 ↦ a`, is the restriction of the `G ⧸ N`-linear
map `ℤ → A^N`, `1 ↦ aB`, followed by the inclusion `A^N ↪ A`. -/
lemma powHomRep_eq_infl (A : Rep Coeff G) (a : A) (hafix : ∀ σ : G, A.ρ σ a = a) :
    powHomRep a hafix
      = (Rep.resFunctor (QuotientGroup.mk' N)).map
          (powHomRep (quotNormInv N A a hafix) (quotNormInv_rho N A a hafix))
        ≫ ConcreteCategory.ofHom (A.ρ.quotientToInvariants_lift N) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro n
  change (Rep.Hom.hom (powHomRep a hafix)) n =
    (Rep.Hom.hom ((Rep.resFunctor (QuotientGroup.mk' N)).map
      (powHomRep (quotNormInv N A a hafix) (quotNormInv_rho N A a hafix))
      ≫ ConcreteCategory.ofHom (A.ρ.quotientToInvariants_lift N))) n
  rw [Rep.hom_comp]
  simp only [Representation.IntertwiningMap.comp_apply]
  rw [Rep.resMap_hom_apply, powHomRep_apply, powHomRep_apply]
  show n • a = ((n • quotNormInv N A a hafix : A.quotientToInvariants N) : A)
  rw [Submodule.coe_smul, quotNormInv_coe]

/-! ## 3. Compatibility of the cup product with inflation -/

/-- Restriction along the identity is the identity on morphisms. -/
lemma resFunctor_id_map {G : Type} [Group G] {X Y : Rep Coeff G} (φ : X ⟶ Y) :
    (Rep.resFunctor (MonoidHom.id G)).map φ = φ := by
  apply Rep.hom_ext
  rfl

/-- Restriction sends identity morphisms to identity morphisms. -/
lemma resFunctor_map_id {H G : Type} [Group H] [Group G] (f : H →* G) (X : Rep Coeff G) :
    (Rep.resFunctor f).map (𝟙 X) = 𝟙 ((Rep.resFunctor f).obj X) := by
  apply Rep.hom_ext
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **(★)** The level-`G` coefficient map `1 ↦ a` is the inflation of the level-`G ⧸ N` coefficient
map against the identity of the trivial module. -/
lemma powHomRep_star {G : Type} [Group G] (N : Subgroup G) [N.Normal] (p : ℕ) [Fact p.Prime]
    (A : Rep Coeff G) (a : A) (hafix : ∀ σ : G, A.ρ σ a = a) :
    groupCohomology.map (QuotientGroup.mk' N) (A := Rep.trivial Coeff (G ⧸ N) Coeff)
        (B := Rep.res (QuotientGroup.mk' N) (Rep.trivial Coeff (G ⧸ N) Coeff))
        ((Rep.resFunctor (QuotientGroup.mk' N)).map
          (𝟙 (Rep.trivial Coeff (G ⧸ N) Coeff))) 2
      ≫ groupCohomology.map (MonoidHom.id G) (powHomRep a hafix) 2
      = groupCohomology.map (QuotientGroup.mk' N)
          (A := Rep.trivial Coeff (G ⧸ N) Coeff) (B := A) (powHomRep a hafix) 2 := by
  have hmap := groupCohomology.map_comp (k := Coeff)
    (A := Rep.trivial Coeff (G ⧸ N) Coeff)
    (B := Rep.res (QuotientGroup.mk' N) (Rep.trivial Coeff (G ⧸ N) Coeff))
    (C := A) (QuotientGroup.mk' N) (MonoidHom.id G)
    ((Rep.resFunctor (QuotientGroup.mk' N)).map
      (𝟙 (Rep.trivial Coeff (G ⧸ N) Coeff)))
    (powHomRep a hafix) 2
  rw [resFunctor_id_map] at hmap
  rw [MonoidHom.comp_id] at hmap
  rw [resFunctor_map_id] at hmap
  rw [Category.id_comp] at hmap
  exact hmap.symm

set_option backward.isDefEq.respectTransparency false in
/-- The Bockstein of an inflated character is the inflation of the Bockstein. -/
lemma powHomRep_delta {G : Type} [Group G] (N : Subgroup G) [N.Normal] (p : ℕ) [Fact p.Prime]
    (hb : groupCohomology (Rep.trivial Coeff (G ⧸ N) (ZMod p)) 1)
    (h : groupCohomology (Rep.trivial Coeff G (ZMod p)) 1)
    (hbh : (groupCohomology.map (QuotientGroup.mk' N)
      (trivResInv (QuotientGroup.mk' N) (ZMod p)) 1).hom hb = h) :
    (groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl).hom h
      = (groupCohomology.map (QuotientGroup.mk' N)
          ((Rep.resFunctor (QuotientGroup.mk' N)).map
            (𝟙 (Rep.trivial Coeff (G ⧸ N) Coeff))) 2).hom
        ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (G ⧸ N) p) 1 2 rfl).hom hb) := by
  rw [← hbh]
  exact delta_trivResInv (QuotientGroup.mk' N) p hb

set_option backward.isDefEq.respectTransparency false in
/-- **(★★)** The inflation of the level-`G ⧸ N` cup-product coefficient map composed with the
inclusion `A^N ↪ A` is the level-`G` coefficient map `1 ↦ a`. -/
lemma powHomRep_dd {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    (A : Rep Coeff G) (aB : A.quotientToInvariants N)
    (hafixB : ∀ q : G ⧸ N, (A.quotientToInvariants N).ρ q aB = aB) :
    groupCohomology.map (QuotientGroup.mk' N) (A := Rep.trivial Coeff (G ⧸ N) Coeff) (B := A)
        ((Rep.resFunctor (QuotientGroup.mk' N)).map (powHomRep aB hafixB)
          ≫ ConcreteCategory.ofHom (A.ρ.quotientToInvariants_lift N)) 2
      = groupCohomology.map (MonoidHom.id (G ⧸ N))
            (A := Rep.trivial Coeff (G ⧸ N) Coeff) (B := A.quotientToInvariants N)
            (powHomRep aB hafixB) 2
        ≫ groupCohomology.map (QuotientGroup.mk' N) (A := A.quotientToInvariants N) (B := A)
            (ConcreteCategory.ofHom (A.ρ.quotientToInvariants_lift N)) 2 := by
  have hmap := groupCohomology.map_comp (k := Coeff)
    (A := Rep.trivial Coeff (G ⧸ N) Coeff)
    (B := A.quotientToInvariants N) (C := A)
    (MonoidHom.id (G ⧸ N)) (QuotientGroup.mk' N)
    (powHomRep aB hafixB)
    (ConcreteCategory.ofHom (A.ρ.quotientToInvariants_lift N)) 2
  rwa [MonoidHom.id_comp] at hmap

set_option backward.isDefEq.respectTransparency false in
/-- **The cup-product class attached to `a` at level `G` is the inflation of the class attached to
`a` at the level `G ⧸ N`.** -/
lemma powHomRep_key {G : Type} [Group G] (N : Subgroup G) [N.Normal] (p : ℕ) [Fact p.Prime]
    (A : Rep Coeff G) (a : A) (hafix : ∀ σ : G, A.ρ σ a = a)
    (aB : A.quotientToInvariants N)
    (hafixB : ∀ q : G ⧸ N, (A.quotientToInvariants N).ρ q aB = aB)
    (hb : groupCohomology (Rep.trivial Coeff (G ⧸ N) (ZMod p)) 1)
    (h : groupCohomology (Rep.trivial Coeff G (ZMod p)) 1)
    (hbh : (groupCohomology.map (QuotientGroup.mk' N)
      (trivResInv (QuotientGroup.mk' N) (ZMod p)) 1).hom hb = h)
    (hpow : powHomRep a hafix
      = (Rep.resFunctor (QuotientGroup.mk' N)).map (powHomRep aB hafixB)
        ≫ ConcreteCategory.ofHom (A.ρ.quotientToInvariants_lift N)) :
    (groupCohomology.map (MonoidHom.id G) (powHomRep a hafix) 2).hom
        ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl).hom h)
      = (groupCohomology.map (QuotientGroup.mk' N) (A := A.quotientToInvariants N) (B := A)
          (ConcreteCategory.ofHom (A.ρ.quotientToInvariants_lift N)) 2).hom
        ((groupCohomology.map (MonoidHom.id (G ⧸ N))
            (A := Rep.trivial Coeff (G ⧸ N) Coeff) (B := A.quotientToInvariants N)
            (powHomRep aB hafixB) 2).hom
          ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (G ⧸ N) p) 1 2 rfl).hom hb)) := by
  have hA : (groupCohomology.map (MonoidHom.id G) (powHomRep a hafix) 2).hom
        ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl).hom h)
      = (groupCohomology.map (QuotientGroup.mk' N) (A := Rep.trivial Coeff (G ⧸ N) Coeff)
          (B := A) (powHomRep a hafix) 2).hom
        ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (G ⧸ N) p) 1 2 rfl).hom hb) := by
    rw [powHomRep_delta N p hb h hbh]
    exact congrArg (fun m => (ModuleCat.Hom.hom m)
      ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (G ⧸ N) p) 1 2 rfl).hom hb))
      (powHomRep_star N p A a hafix)
  have hB : (groupCohomology.map (QuotientGroup.mk' N) (A := Rep.trivial Coeff (G ⧸ N) Coeff)
        (B := A) (powHomRep a hafix) 2).hom
        ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (G ⧸ N) p) 1 2 rfl).hom hb)
      = (groupCohomology.map (QuotientGroup.mk' N) (A := A.quotientToInvariants N) (B := A)
          (ConcreteCategory.ofHom (A.ρ.quotientToInvariants_lift N)) 2).hom
        ((groupCohomology.map (MonoidHom.id (G ⧸ N))
            (A := Rep.trivial Coeff (G ⧸ N) Coeff) (B := A.quotientToInvariants N)
            (powHomRep aB hafixB) 2).hom
          ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (G ⧸ N) p) 1 2 rfl).hom hb)) := by
    rw [hpow, powHomRep_dd N A aB hafixB]
    rfl
  exact hA.trans hB



/-! ## 4. The main theorem -/

set_option backward.isDefEq.respectTransparency false in
/-- **The general-level cyclic norm criterion: the norm group of the subfield cut out by the
character.**  Let `G` be a finite group, `N ⊴ G` with `G ⧸ N` cyclic of order `p`, `A` a
`Coeff`-linear `G`-representation with `H¹(N, A) = 0` (Hilbert 90 for the pair `(N, A)`), `a : A`
fixed by `G`, and `h ∈ H¹(G, 𝔽_p)` a nonzero character inflated from `G ⧸ N` (so `N = ker h`).
Then the cup-product class `groupCohomology.map (id) (powHom a) 2 (δ h)` (with `δ` the Bockstein of
`0 → ℤ --p--> ℤ → 𝔽_p → 0`) vanishes if and only if `a` is a norm over the quotiented level, i.e.
lies in the image of the `G ⧸ N`-norm `∑_{x : G ⧸ N} A.ρ (out x)` on the `N`-fixed points of `A`.

In the local application `G = D_{w'} = Gal(L_{w'}/k_v)`, `A = L_{w'}ˣ`, `N = ker h`,
`E = L_{w'}^N`: the conclusion is `a ∈ N_{E/k_v}(Eˣ)` for `a ∈ k_vˣ`; the hypothesis `H¹(N,A) = 0`
is Hilbert 90 for the finite local Galois extension `L_{w'}/E`.

Route: `h = infl h̄` with `h̄ ∈ H¹(G ⧸ N, 𝔽_p)`, `δ h = infl δ h̄` and `a ∪ δ h = infl(a ∪ δ h̄)` in
`H²(G ⧸ N, A^N)` (the projection formula); `H¹(N,A) = 0` makes the inflation
`H²(G ⧸ N, A^N) → H²(G, A)` injective (the low-degree inflation–restriction sequence), and the
criterion at `G ⧸ N` is `Work.SSGRoute.cyclicNormCriterion_rep` applied to the `G ⧸ N`-module
`A^N`.  For the injectivity it suffices to unfold the definition of `H²` on `2`-cocycles: if the
inflation of a `2`-cocycle `c` on `G ⧸ N` is a coboundary `d₁₂ e` on `G`, then `e|_N` is a
`1`-cocycle on `N`, hence a coboundary; correcting `e` by it produces a cochain vanishing on `N`,
which descends to `G ⧸ N` and exhibits `c` as a coboundary. -/
theorem normCriterion_quotient {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal] [Fintype (G ⧸ N)] (p : ℕ) [Fact p.Prime]
    (hcyc : IsCyclic (G ⧸ N)) (hcard : Nat.card (G ⧸ N) = p)
    (A : Rep SSGRoute.PTExt.Coeff G) (a : A) (hafix : ∀ σ : G, A.ρ σ a = a)
    (hH1 : Subsingleton (groupCohomology (Rep.res N.subtype A) 1))
    (h : groupCohomology (Rep.trivial SSGRoute.PTExt.Coeff G (ZMod p)) 1)
    (hlift : ∃ hb : groupCohomology (Rep.trivial SSGRoute.PTExt.Coeff (G ⧸ N) (ZMod p)) 1,
      (groupCohomology.map (QuotientGroup.mk' N)
        (trivResInv (QuotientGroup.mk' N) (ZMod p)) 1).hom hb = h)
    (hne : h ≠ 0) :
    (groupCohomology.map (MonoidHom.id G) (Work.SSGRoute.powHomRep a hafix) 2
        ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl).hom h) = 0) ↔
      ∃ b : A, (∀ n : N, A.ρ (n : G) b = b) ∧ (∑ x : G ⧸ N, A.ρ (Quotient.out x) b) = a := by
  classical
  obtain ⟨hb, hbh⟩ := hlift
  have hbne : hb ≠ 0 := by
    intro h0
    exact hne (by rw [← hbh, h0]; exact map_zero _)
  have hafixB : ∀ q : G ⧸ N,
      (A.quotientToInvariants N).ρ q (quotNormInv N A a hafix) = quotNormInv N A a hafix :=
    quotNormInv_rho N A a hafix
  -- the inflation of a level-`G ⧸ N` class is injective
  have hinj : Function.Injective (groupCohomology.map (QuotientGroup.mk' N)
      (A := A.quotientToInvariants N) (B := A)
      (ConcreteCategory.ofHom (A.ρ.quotientToInvariants_lift N)) 2).hom :=
    Commons.RepresentationTheory.GroupCohomology.H2_inflation_injective_of_subsingleton_H1_general
      N A hH1
  -- the class is the inflation of the level-`G ⧸ N` class
  have hkey := powHomRep_key N p A a hafix (quotNormInv N A a hafix) hafixB hb h hbh
    (powHomRep_eq_infl N A a hafix)
  rw [hkey]
  constructor
  · intro hvan
    have hz : (groupCohomology.map (MonoidHom.id (G ⧸ N))
        (A := Rep.trivial Coeff (G ⧸ N) Coeff) (B := A.quotientToInvariants N)
        (powHomRep (quotNormInv N A a hafix) hafixB) 2).hom
        ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (G ⧸ N) p) 1 2 rfl).hom hb) = 0 := by
      refine hinj ?_
      rw [map_zero]
      exact hvan
    exact (quotNormInv_exists_iff N A a hafix).mpr
      ((cyclicNormCriterion_rep (G := G ⧸ N) p hcyc hcard (A.quotientToInvariants N)
        (quotNormInv N A a hafix) hafixB hb hbne).mp hz)
  · intro hrhs
    obtain ⟨w, hw⟩ := (quotNormInv_exists_iff N A a hafix).mp hrhs
    have hz : (groupCohomology.map (MonoidHom.id (G ⧸ N))
        (A := Rep.trivial Coeff (G ⧸ N) Coeff) (B := A.quotientToInvariants N)
        (powHomRep (quotNormInv N A a hafix) hafixB) 2).hom
        ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact (G ⧸ N) p) 1 2 rfl).hom hb) = 0 :=
      (cyclicNormCriterion_rep (G := G ⧸ N) p hcyc hcard (A.quotientToInvariants N)
        (quotNormInv N A a hafix) hafixB hb hbne).mpr ⟨w, hw⟩
    rw [hz]
    exact map_zero _

end

end Work.SSGRoute
