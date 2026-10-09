import Mathlib
import Submission.Work.Tate.All
import Submission.Work.Tate.DimensionShiftH
import Submission.Work.GroupCohomology.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the degree-`2 → 1` dimension shift

The dimension shift `Work.Tate.dimensionShiftH2H1 G A : H²(G, A) ≃+ H¹(G, A^*)` is the inverse
of the connecting map `δ¹ : H¹(G, A^*) → H²(G, A)` of the short exact sequence
`0 → A → Coind(A) → A^* → 0` (whose middle term is coinduced, hence acyclic).

A `G`-equivariant map `φ : A → B` of coefficient modules together with a compatible map
`ψ : A^* → B^*` (commuting with the projections, `hψproj`) therefore induces a commutative square

`H²(G,A) --mapH2 φ--> H²(G,B)`
`   |  ≅                     |  ≅`
`H¹(G,A^*) --mapH1 ψ--> H¹(G,B^*)`,

which is the naturality statement proved here.

The proof is the standard one: naturality of the connecting map `δ¹` under a morphism of short
exact sequences.  On the level of cocycles one compares `deltaCocycle` computed from two
different lifts of the same cocycle, using `ShortExactSeq.deltaCocycle_eq_of_lift` and the
pointwise computation `deltaCocycleOf_mapCochain1_natural`.
-/

namespace Work.CohomologicalShrinking.tate

open Work.GroupCohomology

section Auxiliary

variable {G A B C A' B' C' : Type*}
    [Group G] [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [DistribMulAction G A'] [DistribMulAction G B'] [DistribMulAction G C']

/-- **Pointwise naturality of the connecting cocycle.**  For a morphism `(α, β, ·)` of short exact
sequences, the connecting `2`-cocycle (computed from an *arbitrary* lift `b` of a `1`-cocycle `c`)
is carried by `mapZ2 α` to the connecting cocycle of the corresponding lift. -/
theorem deltaCocycleOf_mapCochain1_natural
    (S : Work.GroupCohomology.ShortExactSeq G A B C)
    (S' : Work.GroupCohomology.ShortExactSeq G A' B' C')
    (α : A →+ A') (β : B →+ B')
    (hα : Work.GroupCohomology.IsEquivariant G α)
    (hβ : Work.GroupCohomology.IsEquivariant G β)
    (hβι : ∀ a : A, β (S.iota a) = S'.iota (α a))
    (c : Work.GroupCohomology.Z1 G C) (b : G → B)
    (hb : ∀ g, S.pi (b g) = (c : G → C) g)
    (c' : Work.GroupCohomology.Z1 G C')
    (hb' : ∀ g, S'.pi (Work.GroupCohomology.mapCochain1 G β b g) = (c' : G → C') g) :
    S'.deltaCocycleOf c' (Work.GroupCohomology.mapCochain1 G β b) hb'
      = Work.GroupCohomology.mapZ2 G α hα (S.deltaCocycleOf c b hb) := by
  apply Subtype.ext
  funext p
  obtain ⟨g, h⟩ := p
  apply S'.iota_injective
  rw [Work.GroupCohomology.mapZ2_coe, Work.GroupCohomology.mapCochain2_apply,
    S'.iota_deltaCocycleOf, ← hβι, S.iota_deltaCocycleOf]
  exact (congrFun (Work.GroupCohomology.mapCochain2_d1 G β hβ b) (g, h)).symm

/-- **Naturality of the connecting map `δ¹`.**  A morphism `(α, β, γ)` of short exact sequences of
`G`-modules intertwines the connecting maps: `δ' ∘ mapH1 γ = mapH2 α ∘ δ`. -/
theorem deltaH1_natural_general
    (S : Work.GroupCohomology.ShortExactSeq G A B C)
    (S' : Work.GroupCohomology.ShortExactSeq G A' B' C')
    (α : A →+ A') (β : B →+ B') (γ : C →+ C')
    (hα : Work.GroupCohomology.IsEquivariant G α)
    (hβ : Work.GroupCohomology.IsEquivariant G β)
    (hγ : Work.GroupCohomology.IsEquivariant G γ)
    (hβι : ∀ a : A, β (S.iota a) = S'.iota (α a))
    (hγπ : ∀ b : B, S'.pi (β b) = γ (S.pi b)) :
    S'.deltaH1.comp (Work.GroupCohomology.mapH1 G γ hγ)
      = (Work.GroupCohomology.mapH2 G α hα).comp S.deltaH1 := by
  apply AddMonoidHom.ext
  intro x
  induction x using Work.GroupCohomology.H1_induction_on with
  | h c =>
    rw [AddMonoidHom.comp_apply, Work.GroupCohomology.mapH1_H1π,
        Work.GroupCohomology.ShortExactSeq.deltaH1_H1π, AddMonoidHom.comp_apply,
        Work.GroupCohomology.ShortExactSeq.deltaH1_H1π, Work.GroupCohomology.mapH2_H2π]
    set b : G → B := S.liftCochain (c : G → C) with hbdef
    have hb : ∀ g, S.pi (b g) = (c : G → C) g := fun g => S.pi_liftCochain (c : G → C) g
    set b' : G → B' := Work.GroupCohomology.mapCochain1 G β b with hb'def
    have hb' : ∀ g, S'.pi (b' g) = (Work.GroupCohomology.mapZ1 G γ hγ c : G → C') g := by
      intro g
      change S'.pi (β (b g)) = γ ((c : G → C) g)
      rw [hγπ, hb g]
    have h1 : Work.GroupCohomology.H2π G A' (S'.deltaCocycle (Work.GroupCohomology.mapZ1 G γ hγ c))
        = Work.GroupCohomology.H2π G A'
            (S'.deltaCocycleOf (Work.GroupCohomology.mapZ1 G γ hγ c) b' hb') :=
      S'.deltaCocycle_eq_of_lift (Work.GroupCohomology.mapZ1 G γ hγ c) b' hb'
    have h2 : S'.deltaCocycleOf (Work.GroupCohomology.mapZ1 G γ hγ c) b' hb'
        = Work.GroupCohomology.mapZ2 G α hα (S.deltaCocycleOf c b hb) :=
      deltaCocycleOf_mapCochain1_natural S S' α β hα hβ hβι c b hb
        (Work.GroupCohomology.mapZ1 G γ hγ c) hb'
    have h3 : Work.GroupCohomology.H2π G A'
          (Work.GroupCohomology.mapZ2 G α hα (S.deltaCocycleOf c b hb))
        = Work.GroupCohomology.H2π G A'
            (Work.GroupCohomology.mapZ2 G α hα (S.deltaCocycle c)) := by
      rw [← Work.GroupCohomology.mapH2_H2π, ← Work.GroupCohomology.mapH2_H2π]
      exact congrArg (Work.GroupCohomology.mapH2 G α hα)
        (S.deltaCocycle_eq_of_lift c b hb).symm
    rw [h1, h2, h3]

end Auxiliary

/-- **Naturality of the degree-`2 → 1` dimension shift.**  The isomorphism
`H²(G, A) ≃+ H¹(G, A^*)` is natural in the coefficient module: a `G`-equivariant `φ : A → B`
together with a compatible map `ψ : A^* → B^*` of the shift sequences makes the diagram
`H²(G,A) → H²(G,B)`, `H¹(G,A^*) → H¹(G,B^*)` commute. -/
theorem dimensionShiftH2H1_natural (p : ℕ) (G : Type*) [Group G] [Fintype G]
    (A : Type*) [AddCommGroup A] [Module (ZMod p) A] [DistribMulAction G A]
      [SMulCommClass G (ZMod p) A]
    (B : Type*) [AddCommGroup B] [Module (ZMod p) B] [DistribMulAction G B]
      [SMulCommClass G (ZMod p) B]
    (φ : A →ₗ[ZMod p] B) (hφ : ∀ (γ : G) (a : A), φ (γ • a) = γ • φ a)
    (ψ : Work.Tate.coindShift G A →+ Work.Tate.coindShift G B)
    (hψproj : ∀ x : G → A,
      ψ (Work.Tate.coindProj G A x) = Work.Tate.coindProj G B (Work.Tate.coindMap (φ.toAddMonoidHom) x))
    (hψ : ∀ (γ : G) (x : Work.Tate.coindShift G A), ψ (γ • x) = γ • ψ x) :
    (Work.GroupCohomology.mapH1 G ψ hψ).comp
        (Work.Tate.dimensionShiftH2H1 G A).toAddMonoidHom
      = (Work.Tate.dimensionShiftH2H1 G B).toAddMonoidHom.comp
          (Work.GroupCohomology.mapH2 G (φ.toAddMonoidHom) hφ) := by
  -- the two ways in which the morphism `(φ, coindMap φ, ψ)` of shift sequences is compatible:
  -- inclusions and projections
  have hβι : ∀ a : A,
      Work.Tate.coindMap (φ.toAddMonoidHom) (Work.Tate.coindUnit G A a)
        = Work.Tate.coindUnit G B (φ.toAddMonoidHom a) := by
    intro a
    funext x
    rw [Work.Tate.coindMap_apply, Work.Tate.coindUnit_apply, Work.Tate.coindUnit_apply]
    exact hφ x a
  have hγπ : ∀ b : G → A,
      (Work.Tate.coindSES G B).toShortExactSeq.pi (Work.Tate.coindMap (φ.toAddMonoidHom) b)
        = ψ ((Work.Tate.coindSES G A).toShortExactSeq.pi b) := by
    intro b
    exact (hψproj b).symm
  -- naturality of the connecting map `δ¹`
  have hnat : (Work.Tate.coindSES G B).toShortExactSeq.deltaH1.comp
        (Work.GroupCohomology.mapH1 G ψ hψ)
      = (Work.GroupCohomology.mapH2 G (φ.toAddMonoidHom) hφ).comp
          (Work.Tate.coindSES G A).toShortExactSeq.deltaH1 :=
    deltaH1_natural_general
      (S := (Work.Tate.coindSES G A).toShortExactSeq)
      (S' := (Work.Tate.coindSES G B).toShortExactSeq)
      (α := φ.toAddMonoidHom) (β := Work.Tate.coindMap (φ.toAddMonoidHom)) (γ := ψ)
      (hα := hφ) (hβ := Work.Tate.coindMap_equiv (φ.toAddMonoidHom) hφ) (hγ := hψ)
      hβι hγπ
  -- `dimensionShiftH2H1` is the inverse of `δ¹`, so both squares are inverse to the same square
  have hB : ((Work.Tate.dimensionShiftH2H1Symm G B :
        Work.GroupCohomology.H1 G (Work.Tate.coindShift G B) →+ Work.GroupCohomology.H2 G B))
      = (Work.Tate.coindSES G B).toShortExactSeq.deltaH1 := rfl
  have hA : ((Work.Tate.dimensionShiftH2H1Symm G A :
        Work.GroupCohomology.H1 G (Work.Tate.coindShift G A) →+ Work.GroupCohomology.H2 G A))
      = (Work.Tate.coindSES G A).toShortExactSeq.deltaH1 := rfl
  have hnat' : ((Work.Tate.dimensionShiftH2H1Symm G B :
        Work.GroupCohomology.H1 G (Work.Tate.coindShift G B) →+ Work.GroupCohomology.H2 G B)).comp
        (Work.GroupCohomology.mapH1 G ψ hψ)
      = (Work.GroupCohomology.mapH2 G (φ.toAddMonoidHom) hφ).comp
          (Work.Tate.dimensionShiftH2H1Symm G A :
            Work.GroupCohomology.H1 G (Work.Tate.coindShift G A) →+ Work.GroupCohomology.H2 G A) := by
    rw [hB, hA]; exact hnat
  apply AddMonoidHom.ext
  intro y
  apply (Work.Tate.dimensionShiftH2H1Symm G B).injective
  calc ((Work.Tate.dimensionShiftH2H1Symm G B :
          Work.GroupCohomology.H1 G (Work.Tate.coindShift G B) →+ Work.GroupCohomology.H2 G B))
          ((Work.GroupCohomology.mapH1 G ψ hψ) ((Work.Tate.dimensionShiftH2H1 G A) y))
      = (((Work.Tate.dimensionShiftH2H1Symm G B :
          Work.GroupCohomology.H1 G (Work.Tate.coindShift G B) →+ Work.GroupCohomology.H2 G B)).comp
            (Work.GroupCohomology.mapH1 G ψ hψ)) ((Work.Tate.dimensionShiftH2H1 G A) y) := rfl
    _ = ((Work.GroupCohomology.mapH2 G (φ.toAddMonoidHom) hφ).comp
          (Work.Tate.dimensionShiftH2H1Symm G A :
            Work.GroupCohomology.H1 G (Work.Tate.coindShift G A) →+ Work.GroupCohomology.H2 G A))
          ((Work.Tate.dimensionShiftH2H1 G A) y) := by rw [hnat']
    _ = (Work.GroupCohomology.mapH2 G (φ.toAddMonoidHom) hφ) y := by
          rw [AddMonoidHom.comp_apply]
          congr 1
          exact AddEquiv.apply_symm_apply _ y
    _ = (Work.Tate.dimensionShiftH2H1Symm G B :
          Work.GroupCohomology.H1 G (Work.Tate.coindShift G B) →+ Work.GroupCohomology.H2 G B)
          ((Work.Tate.dimensionShiftH2H1 G B)
            ((Work.GroupCohomology.mapH2 G (φ.toAddMonoidHom) hφ) y)) := by
          exact (AddEquiv.apply_symm_apply (Work.Tate.dimensionShiftH2H1Symm G B)
            ((Work.GroupCohomology.mapH2 G (φ.toAddMonoidHom) hφ) y)).symm

end Work.CohomologicalShrinking.tate
