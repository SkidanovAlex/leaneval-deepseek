import Mathlib
import Submission.Work.SSGRoute.PT.corH2_ptorsion_bij
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

/-- **Post-composition with an additive map is bijective as soon as it is bijective on the
`p`-torsion, when the source has exponent `p`.**

Let `V` be an additive commutative group of exponent `p` (`∀ v, p • v = 0`) and `f : A →+ B` an
additive map whose restriction to the `p`-torsion constituents
`{a : A // p • a = 0} → {b : B // p • b = 0}` is bijective.  Then post-composition with `f`,
`φ ↦ f ∘ φ`, is a bijection `Hom(V, A) → Hom(V, B)`.

The point is that *every* homomorphism `φ : V →+ A` out of an exponent-`p` group lands in the
`p`-torsion (`p • φ v = φ (p • v) = 0`), so the `Hom`-sets are exactly the `Hom`-sets into the
`p`-torsion, where `f` is an isomorphism.  Note that no group structure on the `p`-torsion
subtypes is needed: the inverse is produced by choosing preimages along the surjectivity of the
restriction and the additivity is verified by the injectivity of the restriction. -/
theorem comp_bijective_of_ptorsion_bijective
    (p : ℕ) {V A B : Type*} [AddCommGroup V] [AddCommGroup A] [AddCommGroup B]
    (hV : ∀ v : V, p • v = 0) (f : A →+ B)
    (hf : Function.Bijective (fun z : {a : A // p • a = 0} =>
      (⟨f z.1, by rw [← map_nsmul, z.2, map_zero]⟩ : {b : B // p • b = 0}))) :
    Function.Bijective (fun φ : V →+ A => f.comp φ) := by
  set g : {a : A // p • a = 0} → {b : B // p • b = 0} :=
    fun z => ⟨f z.1, by rw [← map_nsmul, z.2, map_zero]⟩ with hgdef
  constructor
  · -- injectivity: `f ∘ φ = f ∘ ψ` forces `φ = ψ` because both sides land in the `p`-torsion
    intro φ ψ h
    ext v
    have hmemφ : p • (φ v) = 0 := by rw [← map_nsmul, hV v, map_zero]
    have hmemψ : p • (ψ v) = 0 := by rw [← map_nsmul, hV v, map_zero]
    have hg : g ⟨φ v, hmemφ⟩ = g ⟨ψ v, hmemψ⟩ := by
      apply Subtype.ext
      have hv := DFunLike.congr_fun h v
      simpa using hv
    exact congrArg Subtype.val (hf.1 hg)
  · -- surjectivity: lift a hom into `B` through the bijection on the `p`-torsion
    intro ψ
    have hψmem : ∀ v : V, p • ψ v = 0 := fun v => by rw [← map_nsmul, hV v, map_zero]
    let ψp : V → {b : B // p • b = 0} := fun v => ⟨ψ v, hψmem v⟩
    have hχ : ∀ v, g (Classical.choose (hf.2 (ψp v))) = ψp v :=
      fun v => Classical.choose_spec (hf.2 (ψp v))
    let χ : V → A := fun v => (Classical.choose (hf.2 (ψp v))).1
    have hχmem : ∀ v, p • χ v = 0 := fun v => (Classical.choose (hf.2 (ψp v))).2
    have hχval : ∀ v, f (χ v) = ψ v := by
      intro v
      have := congrArg Subtype.val (hχ v)
      simpa [χ, ψp, g] using this
    have hχzero : χ 0 = 0 := by
      have h1 : g ⟨χ 0, hχmem 0⟩ = g ⟨(0 : A), by simp⟩ := by
        apply Subtype.ext
        simp [g, χ, hχval]
      exact congrArg Subtype.val (hf.1 h1)
    have hadd : ∀ v w, χ (v + w) = χ v + χ w := by
      intro v w
      have h2 : g ⟨χ (v + w), hχmem (v + w)⟩ =
          g ⟨χ v + χ w, by rw [smul_add, hχmem v, hχmem w, add_zero]⟩ := by
        apply Subtype.ext
        simp only [g, AddMonoidHom.map_add]
        rw [hχval (v + w), hχval v, hχval w, map_add]
      exact congrArg Subtype.val (hf.1 h2)
    refine ⟨{ toFun := χ, map_zero' := hχzero, map_add' := hadd }, ?_⟩
    ext v
    simpa using hχval v

/-- **The `hcor` hypothesis of the base case of the `α²`-dévissage, from the arithmetic on the
`p`-torsion.**  `Work.SSGRoute.PT.alphaTwo_coind_bijective_of_cor` reduces the bijectivity of
`α²(G, Coind^G_U M)` to

* the bijectivity of `α²(U, M)` (the trivial-action base case over `U`), and
* `Function.Bijective (fun φ : ↥(invariants U M) →+ H²(U,C) => (corH2 U hUo C).comp φ)`

(post-composition with the corestriction `cor : H²(U,C) →+ H²(G,C)`).  This file proves the second
statement from the `p`-torsion arithmetic: if `M` has exponent `p`, `C` has exponent `p`,
`p ∤ [G : U]` and `#H²(U,C)[p] = p = #H²(G,C)[p]`, then post-composition with `cor` is bijective
on `Hom(↥(invariants U M), -)`.

Indeed `↥(invariants U M)` has exponent `p`, so every homomorphism `V →+ H²(·,C)` takes values in
the `p`-torsion; and by `PT.corH2_ptorsion_bijective` the corestriction restricted to the
`p`-torsion is an isomorphism.  (The cardinality hypotheses are the level-wise class-formation
axiom Milne, *ADT*, (1.1b): `PT.br_pTorsion_openSubgroup` at `U` and
`Work.SSGRoute.Nakayama.br_pTorsion` at `G`.) -/
theorem hcor_of_corH2_ptorsion
    (p : ℕ) [Fact p.Prime] {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (U : Subgroup G) (hUo : IsOpen (U : Set G)) [U.FiniteIndex] [Fintype (G ⧸ U)]
    {M : Type} [AddCommGroup M] [DistribMulAction U M] (hMp : ∀ m : M, p • m = 0)
    {C : Type} [AddCommGroup C] [DistribMulAction G C] (hexp : ∀ c : C, p • c = 0)
    (hcop : (Nat.card (G ⧸ U)).Coprime p)
    (hcardU : Nat.card {x : Work.AbsoluteKummer.H2 ↥U C // p • x = 0} = p)
    (hcardG : Nat.card {x : Work.AbsoluteKummer.H2 G C // p • x = 0} = p) :
    Function.Bijective
      (fun φ : ↥(Work.GroupCohomology.invariants U M) →+ Work.AbsoluteKummer.H2 ↥U C =>
        (Work.SSGRoute.PT.corH2 U hUo C).comp φ) := by
  refine comp_bijective_of_ptorsion_bijective p
    (V := ↥(Work.GroupCohomology.invariants U M)) (A := Work.AbsoluteKummer.H2 ↥U C)
    (B := Work.AbsoluteKummer.H2 G C) ?_ (Work.SSGRoute.PT.corH2 U hUo C) ?_
  · exact fun v => Subtype.ext (hMp v)
  · exact Work.SSGRoute.PT.corH2_ptorsion_bijective U hUo C p hexp hcop hcardU hcardG

end Work.SSGRoute.PT
