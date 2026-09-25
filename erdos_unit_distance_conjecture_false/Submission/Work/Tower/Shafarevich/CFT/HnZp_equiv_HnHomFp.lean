import Mathlib
import Submission.Work.CFT.ClassFormation.Defs
import Submission.Work.CFT.ClassFormation.Schur.BocksteinDefs

/-!
# `H_n(G, 𝔽_p)` with `𝔽_p` coefficients: agreement of the `ℤ`- and `𝔽_p`-linear computations

The group homology `H_n(G, A)` of a trivial `G`-module `A` can be computed in two ways, depending
on which base ring one uses for the trivial representation:

* `Work.CFT.ClassFormation.HnHomFp p G n = H_n(G, 𝔽_p)` where `𝔽_p = ZMod p` is regarded as a
  *`ZMod p`-module* (`groupHomology (Rep.trivial (ZMod p) G (ZMod p)) n`, a `ModuleCat (ZMod p)`);
* `Work.CFT.ClassFormation.Schur.HnZp p G n = H_n(G, 𝔽_p)` where `𝔽_p` is regarded as a
  *`ℤ`-module* (`groupHomology (Rep.trivial ℤ G (ZMod p)) n`, a `ModuleCat ℤ`).

The point of this file is that the underlying abelian groups agree,
`HnHomFp p G n ≃+ HnZp p G n`, so that the `𝔽_p`-vector space `HnHomFp p G n` may be used
interchangeably with the abelian group `HnZp p G n` whenever only its group structure matters.

The reason is that both homologies are computed from the *complex of inhomogeneous chains*,
whose `n`-chains are the finitely supported functions `Fin n → G → 𝔽_p` and whose differential
is given by the same formula in both cases (see `groupHomology.inhomogeneousChains.d_single`):
for a trivial representation the differential only involves the additions in the abelian group
`𝔽_p` and the *sign* `(-1) ^ (i + 1)`, and the two possible module structures on `𝔽_p`
(`ZMod p`- and `ℤ`-) act by the same map.

Formally, this is implemented by pushing both complexes into `Ab` via the forgetful functor
`forget₂ (ModuleCat R) Ab`: on objects this is the identity on the underlying additive group
(`ModuleCat.forget₂_obj`), and on morphisms it is the identity on the underlying function
(`ModuleCat.forget₂_map`).  Both resulting complexes in `Ab` therefore have the same objects and
the same differentials (proved below), hence are isomorphic, and the forgetful functor preserves
homology, so the homologies are isomorphic too.
-/

namespace Work.Tower.Shafarevich.CFT

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- In `𝔽_p = ZMod p`, the action of the integer `(-1) ^ m` is the same for the `ℤ`-module
structure and for the `ZMod p`-module structure. -/
lemma neg_one_pow_smul_zmod (p m : ℕ) (a : ZMod p) :
    (-1 : ℤ) ^ m • a = (-1 : ZMod p) ^ m • a := by
  rw [zsmul_eq_mul, ← smul_eq_mul]
  push_cast
  ring

/-- The differentials of the complexes of inhomogeneous chains for the trivial
`ZMod p`-representation and the trivial `ℤ`-representation on `ZMod p` agree on the generators
`single g a` of the chains. -/
lemma inhomogeneousChains_d_single_eq (p : ℕ) (G : Type) [Group G] (n : ℕ)
    (g : Fin (n + 1) → G) (a : ZMod p) :
    ((groupHomology.inhomogeneousChains (Rep.trivial (ZMod p) G (ZMod p))).d (n + 1) n)
        (Finsupp.single g a) =
      ((groupHomology.inhomogeneousChains (Rep.trivial ℤ G (ZMod p))).d (n + 1) n)
        (Finsupp.single g a) := by
  rw [groupHomology.inhomogeneousChains.d_def, groupHomology.inhomogeneousChains.d_def,
    groupHomology.inhomogeneousChains.d_single, groupHomology.inhomogeneousChains.d_single,
    Representation.trivial_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Finsupp.smul_single, Finsupp.smul_single, ← neg_one_pow_smul_zmod]

/-- The previous statement, for the underlying additive maps of the differentials. -/
lemma inhomogeneousChains_d_addMonoidHom_eq (p : ℕ) (G : Type) [Group G] (n : ℕ) :
    (((groupHomology.inhomogeneousChains (Rep.trivial (ZMod p) G (ZMod p))).d (n + 1) n).hom.toAddMonoidHom) =
      (((groupHomology.inhomogeneousChains (Rep.trivial ℤ G (ZMod p))).d (n + 1) n).hom.toAddMonoidHom) := by
  refine AddMonoidHom.ext fun x => ?_
  induction x using Finsupp.induction with
  | zero => simp
  | single_add a b y _ _ hy =>
      have key :
          (ModuleCat.Hom.hom
              ((groupHomology.inhomogeneousChains (Rep.trivial (ZMod p) G (ZMod p))).d (n + 1) n)).toAddMonoidHom
              (Finsupp.single a b) =
            (ModuleCat.Hom.hom
              ((groupHomology.inhomogeneousChains (Rep.trivial ℤ G (ZMod p))).d (n + 1) n)).toAddMonoidHom
              (Finsupp.single a b) :=
        inhomogeneousChains_d_single_eq p G n a b
      rw [map_add, map_add, hy, key]

/-- The two complexes of inhomogeneous chains have the same differentials after forgetting the
module structure, i.e. as morphisms of abelian groups. -/
lemma inhomogeneousChains_d_ab_eq (p : ℕ) (G : Type) [Group G] (n : ℕ) :
    (((forget₂ (ModuleCat (ZMod p)) Ab).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (groupHomology.inhomogeneousChains (Rep.trivial (ZMod p) G (ZMod p)))).d (n + 1) n =
      (((forget₂ (ModuleCat ℤ) Ab).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (groupHomology.inhomogeneousChains (Rep.trivial ℤ G (ZMod p)))).d (n + 1) n := by
  rw [Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_obj_d,
    ModuleCat.forget₂_map, ModuleCat.forget₂_map]
  exact congrArg AddCommGrpCat.ofHom (inhomogeneousChains_d_addMonoidHom_eq p G n)

/-- The two complexes of inhomogeneous chains, pushed forward to `Ab`, are isomorphic: they have
the same objects and the same differentials. -/
noncomputable def inhomogeneousChainsAbIso (p : ℕ) (G : Type) [Group G] :
    ((forget₂ (ModuleCat (ZMod p)) Ab).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (groupHomology.inhomogeneousChains (Rep.trivial (ZMod p) G (ZMod p))) ≅
      ((forget₂ (ModuleCat ℤ) Ab).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (groupHomology.inhomogeneousChains (Rep.trivial ℤ G (ZMod p))) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun i j hij => by
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    have h : i = j + 1 := hij.symm
    subst h
    exact (inhomogeneousChains_d_ab_eq p G j).symm)

/-- A functor which preserves homology induces an isomorphism
`H_n(F C) ≅ F (H_n C)` on homology. -/
noncomputable def mapHomologyIsoOfPreservesHomology {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] [CategoryWithHomology C] [CategoryWithHomology D]
    (F : C ⥤ D) [F.Additive] [F.PreservesHomology]
    (K : HomologicalComplex C (ComplexShape.down ℕ)) (i : ℕ) :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj K).homology i ≅ F.obj (K.homology i) :=
  HomologicalComplex.homologyMapIso (Iso.refl _) i ≪≫ ShortComplex.mapHomologyIso (K.sc i) F

/-- The underlying abelian groups of `H_n(G, 𝔽_p)` computed with `𝔽_p`-coefficients and with
`ℤ`-coefficients agree. -/
theorem HnZp_equiv_HnHomFp (p : ℕ) [Fact p.Prime] (G : Type) [Group G] (n : ℕ) :
    Nonempty (Work.CFT.ClassFormation.HnHomFp p G n ≃+ Work.CFT.ClassFormation.Schur.HnZp p G n) := by
  have e₁ :
      (↥(groupHomology (Rep.trivial (ZMod p) G (ZMod p)) n) : Type) ≃+
        (↥((((forget₂ (ModuleCat (ZMod p)) Ab).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (groupHomology.inhomogeneousChains (Rep.trivial (ZMod p) G (ZMod p)))).homology n : Ab) : Type) :=
    (mapHomologyIsoOfPreservesHomology (forget₂ (ModuleCat (ZMod p)) Ab)
      (groupHomology.inhomogeneousChains (Rep.trivial (ZMod p) G (ZMod p))) n).symm.addCommGroupIsoToAddEquiv
  have e₂ :
      (↥((((forget₂ (ModuleCat (ZMod p)) Ab).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (groupHomology.inhomogeneousChains (Rep.trivial (ZMod p) G (ZMod p)))).homology n : Ab) : Type) ≃+
        (↥((((forget₂ (ModuleCat ℤ) Ab).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (groupHomology.inhomogeneousChains (Rep.trivial ℤ G (ZMod p)))).homology n : Ab) : Type) :=
    (HomologicalComplex.homologyMapIso (inhomogeneousChainsAbIso p G) n).addCommGroupIsoToAddEquiv
  have e₃ :
      (↥((((forget₂ (ModuleCat ℤ) Ab).mapHomologicalComplex (ComplexShape.down ℕ)).obj
          (groupHomology.inhomogeneousChains (Rep.trivial ℤ G (ZMod p)))).homology n : Ab) : Type) ≃+
        (↥(groupHomology (Rep.trivial ℤ G (ZMod p)) n) : Type) :=
    (mapHomologyIsoOfPreservesHomology (forget₂ (ModuleCat ℤ) Ab)
      (groupHomology.inhomogeneousChains (Rep.trivial ℤ G (ZMod p))) n).addCommGroupIsoToAddEquiv
  exact ⟨e₁.trans (e₂.trans e₃)⟩

end

end Work.Tower.Shafarevich.CFT
