import Mathlib
import Submission.Work.Cohomology.DualComplexMap
import Submission.Work.Cohomology.mvComp
import Submission.Work.Cohomology.CoprodMVDefs
import Submission.Work.Cohomology.inclUV_injective
import Submission.Work.Cohomology.smallLift_injective
import Submission.Work.Cohomology.smallLift_pullback
import Submission.Work.Cohomology.smallLift_cov

/-!
# The Mayer–Vietoris sequence of cochain complexes: definitions

The Mayer–Vietoris short exact sequence of chain complexes
(`Work.Cohomology.mvLeft`, `Work.Cohomology.mvRight`, `Work.Cohomology.mv_shortExact`)

`0 ⟶ C_*(U ∩ V) --mvLeft--> C_*(U) ⊞ C_*(V) --mvRight--> C^{U,V}_*(X) ⟶ 0`

dualises (`Work.Cohomology.dualComplex`) to a sequence of cochain complexes

`0 ⟶ C^*(C^{U,V}) ⟶ C^*(U) ⊞ C^*(V) ⟶ C^*(U ∩ V) ⟶ 0`,

which is the cohomological Mayer–Vietoris sequence of the problem statement
`Work.Cohomology.mvCochainShortExact`.

The dual of the *middle* map `mvRight = (smallOfU, -smallOfV)` is the pair
`(smallOfU*, -smallOfV*)`, which is the map `biprod.lift` below; the dual of the *first* map
`mvLeft = (inclUVU_*, inclUVV_*)` is `(inclUVU*, inclUVV*) = biprod.desc`.  Because the middle
term of the target is a biproduct of cochain complexes, and an element of the degree-`n` part of a
biproduct of complexes is *not* definitionally a pair of elements of the degree-`n` parts, the maps
are described here through the biproduct projections and inclusions (`mvCochainF_fst`,
`mvCochainF_snd`, `mvCochainG_inl`, `mvCochainG_inr`), which is what the degreewise computation of
`Submission/Work/Cohomology/mvCochainDegreewise.lean` uses.

Cochains are used as plain `ℤ`-linear functionals `(C.X n) →ₗ[ℤ] ℤ`: an element of the degree-`n`
part of `dualComplex ℤ C` is such a functional (the two are interchangeable up to the coercion
`↑(ModuleCat.of ℤ M) = M`), and this is the form in which the existing files of the workspace
(`AlexanderWhitney.lean`, `relCochain_shortExact.lean`) manipulate cochains.

## Main definitions and results

* `cochainU`, `cochainV`, `cochainUV` — the three dual cochain complexes;
* `chainInclU`, `chainInclV` — the chain-level inclusions `C_*(U ∩ V) ⟶ C_*(U)`, `⟶ C_*(V)`;
* `mvCochainF`, `mvCochainG` — the two maps of the cochain Mayer–Vietoris sequence;
* `mvCochainComp`, `mvCochainDegreeZero` — they compose to zero (globally and degreewise);
* `mvCochainF_fst`, `mvCochainF_snd`, `mvCochainG_inl`, `mvCochainG_inr` — their degreewise
  components along the biproduct projections/inclusions;
* `smallOfU_f`, `smallOfV_f`, `chainInclU_f`, `chainInclV_f` — the degreewise identification of
  these chain maps with `coprodMap` of the corresponding maps of singular simplices;
* `biprodX_total`, `biprodX_ext` — decomposition of an element of the degree-`n` part of a
  biproduct of cochain complexes into its two components.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable {X : TopCat}

/-- The inclusion `C_*(U ∩ V) ⟶ C_*(U)` of singular chain complexes. -/
abbrev chainInclU (U V : Set X) : singularChains ℤ (TopCat.of ↥(U ∩ V)) ⟶
    singularChains ℤ (TopCat.of U) :=
  SSet.chainComplexMap (TopCat.toSSet.map (inclUVU U V)) (ModuleCat.of ℤ ℤ)

/-- The inclusion `C_*(U ∩ V) ⟶ C_*(V)` of singular chain complexes. -/
abbrev chainInclV (U V : Set X) : singularChains ℤ (TopCat.of ↥(U ∩ V)) ⟶
    singularChains ℤ (TopCat.of V) :=
  SSet.chainComplexMap (TopCat.toSSet.map (inclUVV U V)) (ModuleCat.of ℤ ℤ)

/-- The `U`-part of the cochain Mayer–Vietoris sequence. -/
abbrev cochainU (U V : Set X) : CochainComplex (ModuleCat ℤ) ℕ :=
  dualComplex ℤ (singularChains ℤ (TopCat.of U))

/-- The `V`-part of the cochain Mayer–Vietoris sequence. -/
abbrev cochainV (U V : Set X) : CochainComplex (ModuleCat ℤ) ℕ :=
  dualComplex ℤ (singularChains ℤ (TopCat.of V))

/-- The `U ∩ V` part of the cochain Mayer–Vietoris sequence. -/
abbrev cochainUV (U V : Set X) : CochainComplex (ModuleCat ℤ) ℕ :=
  dualComplex ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V)))

/-- **The first map of the cohomological Mayer–Vietoris sequence**,
`C^*(C^{U,V}) ⟶ C^*(U) ⊞ C^*(V)`: the dual of `mvRight = (smallOfU, -smallOfV)`. -/
def mvCochainF (U V : Set X) : dualComplex ℤ (smallChains U V) ⟶ cochainU U V ⊞ cochainV U V :=
  biprod.lift
    (dualComplexMap ℤ (singularChains ℤ (TopCat.of U)) (smallChains U V) (smallOfU U V))
    (-(dualComplexMap ℤ (singularChains ℤ (TopCat.of V)) (smallChains U V) (smallOfV U V)))

/-- **The second map of the cohomological Mayer–Vietoris sequence**,
`C^*(U) ⊞ C^*(V) ⟶ C^*(U ∩ V)`: the dual of `mvLeft = (inclUVU_*, inclUVV_*)`. -/
def mvCochainG (U V : Set X) : cochainU U V ⊞ cochainV U V ⟶ cochainUV U V :=
  biprod.desc
    (dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V)))
      (singularChains ℤ (TopCat.of U)) (chainInclU U V))
    (dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V)))
      (singularChains ℤ (TopCat.of V)) (chainInclV U V))

/-- The two inclusions of the Mayer–Vietoris sequence become equal chains after mapping into
`C^{U,V}_*(X)`: this is `chainSmallOfU_comp_inclUVU` in the notation of this file. -/
lemma chainInclU_comp_smallOfU (U V : Set X) :
    chainInclU U V ≫ smallOfU U V = chainInclV U V ≫ smallOfV U V :=
  chainSmallOfU_comp_inclUVU U V

/-- **The cochain Mayer–Vietoris maps compose to zero.** -/
theorem mvCochainComp (U V : Set X) : mvCochainF U V ≫ mvCochainG U V = 0 := by
  rw [mvCochainF, mvCochainG, biprod.lift_desc, Preadditive.neg_comp, ← dualComplexMap_comp,
    ← dualComplexMap_comp, chainInclU_comp_smallOfU]
  simp

/-- **The cochain Mayer–Vietoris maps compose to zero, degreewise.** -/
theorem mvCochainDegreeZero (U V : Set X) (n : ℕ) :
    (mvCochainF U V).f n ≫ (mvCochainG U V).f n = 0 := by
  rw [← HomologicalComplex.comp_f, mvCochainComp, HomologicalComplex.zero_f]

section Components

variable (U V : Set X) (n : ℕ)

/-- The first component of `mvCochainF` at degree `n` is the dual of `smallOfU`. -/
lemma mvCochainF_fst :
    (mvCochainF U V).f n ≫ (biprod.fst : cochainU U V ⊞ cochainV U V ⟶ cochainU U V).f n
      = (dualComplexMap ℤ (singularChains ℤ (TopCat.of U)) (smallChains U V)
          (smallOfU U V)).f n :=
  HomologicalComplex.biprod_lift_fst_f _ _ n

/-- The second component of `mvCochainF` at degree `n` is minus the dual of `smallOfV`. -/
lemma mvCochainF_snd :
    (mvCochainF U V).f n ≫ (biprod.snd : cochainU U V ⊞ cochainV U V ⟶ cochainV U V).f n
      = (-(dualComplexMap ℤ (singularChains ℤ (TopCat.of V)) (smallChains U V)
          (smallOfV U V))).f n :=
  HomologicalComplex.biprod_lift_snd_f _ _ n

/-- The first component of `mvCochainG` at degree `n` is the dual of `chainInclU`. -/
lemma mvCochainG_inl :
    (biprod.inl : cochainU U V ⟶ cochainU U V ⊞ cochainV U V).f n ≫ (mvCochainG U V).f n
      = (dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V)))
          (singularChains ℤ (TopCat.of U)) (chainInclU U V)).f n :=
  HomologicalComplex.biprod_inl_desc_f _ _ n

/-- The second component of `mvCochainG` at degree `n` is the dual of `chainInclV`. -/
lemma mvCochainG_inr :
    (biprod.inr : cochainV U V ⟶ cochainU U V ⊞ cochainV U V).f n ≫ (mvCochainG U V).f n
      = (dualComplexMap ℤ (singularChains ℤ (TopCat.of ↥(U ∩ V)))
          (singularChains ℤ (TopCat.of V)) (chainInclV U V)).f n :=
  HomologicalComplex.biprod_inr_desc_f _ _ n

end Components

section Index

variable (U V : Set X) (n : ℕ)

/-- Degreewise, `smallOfU` is the coproduct map induced by `smallLiftU` on `n`-simplices. -/
lemma smallOfU_f :
    (smallOfU U V).f n = coprodMap (R:=ℤ) ((smallLiftU U V).app (Opposite.op ⦋n⦌)) := rfl

/-- Degreewise, `smallOfV` is the coproduct map induced by `smallLiftV` on `n`-simplices. -/
lemma smallOfV_f :
    (smallOfV U V).f n = coprodMap (R:=ℤ) ((smallLiftV U V).app (Opposite.op ⦋n⦌)) := rfl

/-- Degreewise, `chainInclU` is the coproduct map induced by the inclusion `U ∩ V ↪ U`. -/
lemma chainInclU_f :
    (chainInclU U V).f n =
      coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVU U V)).app (Opposite.op ⦋n⦌)) := rfl

/-- Degreewise, `chainInclV` is the coproduct map induced by the inclusion `U ∩ V ↪ V`. -/
lemma chainInclV_f :
    (chainInclV U V).f n =
      coprodMap (R:=ℤ) ((TopCat.toSSet.map (inclUVV U V)).app (Opposite.op ⦋n⦌)) := rfl

end Index

section Biprod

variable {K L : CochainComplex (ModuleCat ℤ) ℕ} {n : ℕ}

/-- Elementwise form of `HomologicalComplex.biprod_total_f` for cochain complexes: an element of
the degree-`n` part of a biproduct of cochain complexes is the sum of the `inl` of its `fst` and
the `inr` of its `snd`. -/
lemma biprodX_total (x : (K ⊞ L).X n) :
    (biprod.inl : K ⟶ K ⊞ L).f n ((biprod.fst : K ⊞ L ⟶ K).f n x)
      + (biprod.inr : L ⟶ K ⊞ L).f n ((biprod.snd : K ⊞ L ⟶ L).f n x) = x := by
  have htot := HomologicalComplex.biprod_total_f (K := K) (L := L) n
  have h := congrArg (fun (f : (K ⊞ L).X n ⟶ (K ⊞ L).X n) => f x) htot
  simpa only [ModuleCat.hom_add, LinearMap.add_apply, ConcreteCategory.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] using h

/-- Two elements of the degree-`n` part of a biproduct of cochain complexes agree as soon as
their projections do. -/
lemma biprodX_ext {x y : (K ⊞ L).X n}
    (h₁ : (biprod.fst : K ⊞ L ⟶ K).f n x = (biprod.fst : K ⊞ L ⟶ K).f n y)
    (h₂ : (biprod.snd : K ⊞ L ⟶ L).f n x = (biprod.snd : K ⊞ L ⟶ L).f n y) : x = y := by
  rw [← biprodX_total x, ← biprodX_total y, h₁, h₂]

/-- Two elements of the degree-`n` part of a biproduct of cochain complexes agree as soon as
they have the same `ℤ`-linear evaluations on both components. -/
lemma biprodX_ext_hom {x y : (K ⊞ L).X n}
    (h₁ : (biprod.fst : K ⊞ L ⟶ K).f n x = (biprod.fst : K ⊞ L ⟶ K).f n y)
    (h₂ : (biprod.snd : K ⊞ L ⟶ L).f n x = (biprod.snd : K ⊞ L ⟶ L).f n y) : x = y :=
  biprodX_ext h₁ h₂

end Biprod

section Generator

/-- The coproduct of copies of `ℤ` indexed by a type. -/
abbrev coprodMod (S : Type) : ModuleCat ℤ := ∐ (fun _ : S => ModuleCat.of ℤ ℤ)

/-- Two endomorphisms of `ℤ` are equal as soon as they agree at `1`. -/
lemma moduleZ_hom_ext {f g : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ} (h : f.hom 1 = g.hom 1) :
    f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rw [show z = z • (1 : ℤ) by simp]
  rw [map_smul, map_smul, h]

/-- The `Σ`-inclusion followed by the morphism attached to a linear functional, evaluated at
`1`. -/
lemma sigma_iota_comp_ofHom_one {S : Type} (s : S) (φ : ↥(coprodMod S) →ₗ[ℤ] ℤ) :
    (Sigma.ι (fun _ : S => ModuleCat.of ℤ ℤ) s ≫ ModuleCat.ofHom φ).hom 1
      = φ ((Sigma.ι (fun _ : S => ModuleCat.of ℤ ℤ) s).hom 1) := by
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]

/-- Two functionals on the simplicial chains of a simplicial set agree as soon as they agree on
the generators (the `ιChainComplex` inclusions). -/
lemma dual_ext_of_iota {C : SSet} {n : ℕ}
    {φ ψ : (C.chainComplex (ModuleCat.of ℤ ℤ)).X n →ₗ[ℤ] ℤ}
    (h : ∀ s : C _⦋n⦌, φ ((C.ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1)
      = ψ ((C.ιChainComplex (R := ModuleCat.of ℤ ℤ) s).hom 1)) : φ = ψ := by
  have hmor : ModuleCat.ofHom φ = ModuleCat.ofHom ψ := by
    apply SSet.chainComplex_hom_ext (R := ModuleCat.of ℤ ℤ)
    intro s
    apply moduleZ_hom_ext
    change (ModuleCat.Hom.hom (Sigma.ι (fun _ : C _⦋n⦌ => ModuleCat.of ℤ ℤ) s
        ≫ ModuleCat.ofHom φ)) 1
      = (ModuleCat.Hom.hom (Sigma.ι (fun _ : C _⦋n⦌ => ModuleCat.of ℤ ℤ) s
        ≫ ModuleCat.ofHom ψ)) 1
    rw [sigma_iota_comp_ofHom_one s φ, sigma_iota_comp_ofHom_one s ψ]
    exact h s
  have h2 := congrArg ModuleCat.Hom.hom hmor
  simpa only [ModuleCat.hom_ofHom] using h2

/-- The image of a generator under `smallOfU`: the (small) simplex of `X` it represents. -/
lemma smallOfU_iota (U V : Set X) (n : ℕ)
    (a : (TopCat.toSSet.obj (TopCat.of U)) _⦋n⦌) :
    ((smallOfU U V).f n).hom
        (((TopCat.toSSet.obj (TopCat.of U)).ιChainComplex (R := ModuleCat.of ℤ ℤ) a).hom 1)
      = ((smallSSet U V).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((smallLiftU U V).app (Opposite.op ⦋n⦌) a)).hom 1 := by
  rw [show (smallOfU U V).f n
      = (SSet.chainComplexMap (smallLiftU U V) (ModuleCat.of ℤ ℤ)).f n from rfl]
  exact congrArg (fun g => (ModuleCat.Hom.hom g) 1)
    (SSet.ι_chainComplexMap_f _ _ (smallLiftU U V) (ModuleCat.of ℤ ℤ) a)

/-- The image of a generator under `smallOfV`: the (small) simplex of `X` it represents. -/
lemma smallOfV_iota (U V : Set X) (n : ℕ)
    (b : (TopCat.toSSet.obj (TopCat.of V)) _⦋n⦌) :
    ((smallOfV U V).f n).hom
        (((TopCat.toSSet.obj (TopCat.of V)).ιChainComplex (R := ModuleCat.of ℤ ℤ) b).hom 1)
      = ((smallSSet U V).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((smallLiftV U V).app (Opposite.op ⦋n⦌) b)).hom 1 := by
  rw [show (smallOfV U V).f n
      = (SSet.chainComplexMap (smallLiftV U V) (ModuleCat.of ℤ ℤ)).f n from rfl]
  exact congrArg (fun g => (ModuleCat.Hom.hom g) 1)
    (SSet.ι_chainComplexMap_f _ _ (smallLiftV U V) (ModuleCat.of ℤ ℤ) b)

/-- The image of a generator under `chainInclU`. -/
lemma chainInclU_iota (U V : Set X) (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))) _⦋n⦌) :
    ((chainInclU U V).f n).hom
        (((TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))).ιChainComplex (R := ModuleCat.of ℤ ℤ) c).hom 1)
      = ((TopCat.toSSet.obj (TopCat.of U)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.map (inclUVU U V)).app (Opposite.op ⦋n⦌) c)).hom 1 := by
  rw [show (chainInclU U V).f n
      = (SSet.chainComplexMap (TopCat.toSSet.map (inclUVU U V))
          (ModuleCat.of ℤ ℤ)).f n from rfl]
  exact congrArg (fun g => (ModuleCat.Hom.hom g) 1)
    (SSet.ι_chainComplexMap_f _ _ (TopCat.toSSet.map (inclUVU U V)) (ModuleCat.of ℤ ℤ) c)

/-- The image of a generator under `chainInclV`. -/
lemma chainInclV_iota (U V : Set X) (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))) _⦋n⦌) :
    ((chainInclV U V).f n).hom
        (((TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))).ιChainComplex (R := ModuleCat.of ℤ ℤ) c).hom 1)
      = ((TopCat.toSSet.obj (TopCat.of V)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.map (inclUVV U V)).app (Opposite.op ⦋n⦌) c)).hom 1 := by
  rw [show (chainInclV U V).f n
      = (SSet.chainComplexMap (TopCat.toSSet.map (inclUVV U V))
          (ModuleCat.of ℤ ℤ)).f n from rfl]
  exact congrArg (fun g => (ModuleCat.Hom.hom g) 1)
    (SSet.ι_chainComplexMap_f _ _ (TopCat.toSSet.map (inclUVV U V)) (ModuleCat.of ℤ ℤ) c)

/-- The generator of a simplex of `U ∩ V` maps to the generator of the corresponding simplex of
`U` under `chainInclU`. -/
lemma iota_chainInclU (U V : Set X) (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))) _⦋n⦌) :
    (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))).ιChainComplex (R := ModuleCat.of ℤ ℤ) c
        ≫ (chainInclU U V).f n
      = (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.map (inclUVU U V)).app (Opposite.op ⦋n⦌) c) := by
  rw [show (chainInclU U V).f n = (SSet.chainComplexMap (TopCat.toSSet.map (inclUVU U V))
      (ModuleCat.of ℤ ℤ)).f n from rfl]
  exact SSet.ι_chainComplexMap_f _ _ (TopCat.toSSet.map (inclUVU U V)) (ModuleCat.of ℤ ℤ) c

/-- The generator of a simplex of `U ∩ V` maps to the generator of the corresponding simplex of
`V` under `chainInclV`. -/
lemma iota_chainInclV (U V : Set X) (n : ℕ)
    (c : (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))) _⦋n⦌) :
    (TopCat.toSSet.obj (TopCat.of ↥(U ∩ V))).ιChainComplex (R := ModuleCat.of ℤ ℤ) c
        ≫ (chainInclV U V).f n
      = (TopCat.toSSet.obj (TopCat.of V)).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.map (inclUVV U V)).app (Opposite.op ⦋n⦌) c) := by
  rw [show (chainInclV U V).f n = (SSet.chainComplexMap (TopCat.toSSet.map (inclUVV U V))
      (ModuleCat.of ℤ ℤ)).f n from rfl]
  exact SSet.ι_chainComplexMap_f _ _ (TopCat.toSSet.map (inclUVV U V)) (ModuleCat.of ℤ ℤ) c

/-- The generator of a simplex of `U` maps to the generator of the corresponding small simplex
under `smallOfU`. -/
lemma iota_smallOfU (U V : Set X) (n : ℕ)
    (a : (TopCat.toSSet.obj (TopCat.of U)) _⦋n⦌) :
    (TopCat.toSSet.obj (TopCat.of U)).ιChainComplex (R := ModuleCat.of ℤ ℤ) a
        ≫ (smallOfU U V).f n
      = (smallSSet U V).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((smallLiftU U V).app (Opposite.op ⦋n⦌) a) := by
  rw [show (smallOfU U V).f n = (SSet.chainComplexMap (smallLiftU U V)
      (ModuleCat.of ℤ ℤ)).f n from rfl]
  exact SSet.ι_chainComplexMap_f _ _ (smallLiftU U V) (ModuleCat.of ℤ ℤ) a

/-- The generator of a simplex of `V` maps to the generator of the corresponding small simplex
under `smallOfV`. -/
lemma iota_smallOfV (U V : Set X) (n : ℕ)
    (b : (TopCat.toSSet.obj (TopCat.of V)) _⦋n⦌) :
    (TopCat.toSSet.obj (TopCat.of V)).ιChainComplex (R := ModuleCat.of ℤ ℤ) b
        ≫ (smallOfV U V).f n
      = (smallSSet U V).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((smallLiftV U V).app (Opposite.op ⦋n⦌) b) := by
  rw [show (smallOfV U V).f n = (SSet.chainComplexMap (smallLiftV U V)
      (ModuleCat.of ℤ ℤ)).f n from rfl]
  exact SSet.ι_chainComplexMap_f _ _ (smallLiftV U V) (ModuleCat.of ℤ ℤ) b

open Classical in
/-- The `Σ.desc`-defined functional, evaluated on a generator. -/
lemma sigma_desc_apply {S T : Type} (γ : T → S) (w : ↥(coprodMod T) →ₗ[ℤ] ℤ) (a : S) :
    (Sigma.desc (fun a => if h : ∃ c, γ c = a then
        Sigma.ι (fun _ : T => ModuleCat.of ℤ ℤ) (Classical.choose h) ≫ ModuleCat.ofHom w
        else 0)).hom ((Sigma.ι (fun _ : S => ModuleCat.of ℤ ℤ) a).hom 1)
      = (if h : ∃ c, γ c = a then
          w ((Sigma.ι (fun _ : T => ModuleCat.of ℤ ℤ) (Classical.choose h)).hom 1)
        else 0) := by
  classical
  have h := congrArg (fun g : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ => (ModuleCat.Hom.hom g) 1)
    (Sigma.ι_desc (fun a => if h : ∃ c, γ c = a then
      Sigma.ι (fun _ : T => ModuleCat.of ℤ ℤ) (Classical.choose h) ≫ ModuleCat.ofHom w
      else 0) a)
  by_cases ha : ∃ c, γ c = a
  · rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [dif_pos ha] at h
    rw [dif_pos ha]
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] using h
  · rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [dif_neg ha] at h
    rw [dif_neg ha]
    simpa only [ModuleCat.hom_zero, LinearMap.zero_apply] using h

end Generator

end

end Work.Cohomology
