import Mathlib
import Submission.Work.SINGMV.Defs

/-!
# Auxiliary lemmas for the barycentric subdivision chain `Sd`

This file collects the elementary `gen`-naturality and affine-simplex bookkeeping needed to
compute the boundary of the barycentric subdivision `Sd (n+1)` of the fundamental simplex:

* `gen_map`: pushing a singular chain generator forward along a continuous map gives the
  generator of the composite simplex;
* `affineSimplex_vert`, `affineSimplex_coface`, `coface_comp_affineSimplex`: the vertices and
  the faces of the affine simplex with a prescribed vertex tuple;
* `coneChain_gen`: the value of the cone `coneChain` on a generator;
* `affineSpan`-closure of the cone and of the pushforward along a coface;
* `affineSimplex_eq_id`: the identity of `Δⁿ` is the affine simplex on the vertex tuple.

The main theorem `Work.SingMV.Sd_d` then computes the differential of `Sd (n+1)`.
-/

open CategoryTheory Limits Convexity
open scoped BigOperators Simplicial

noncomputable section

namespace Work.SingMV

set_option backward.isDefEq.respectTransparency false

/-! ## Naturality of `gen` -/

/-- The inclusion of the `ℤ`-summand of the singular `n`-chains of `X` attached to a simplex of
the singular simplicial set of `X`, with its type stated in terms of `singC`. -/
noncomputable def genHomSd (X : TopCat) (n : ℕ)
    (x : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n))) :
    ModuleCat.of ℤ ℤ ⟶ ((Submission.Blueprint.singC).obj X).X n :=
  (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) x

/-- `gen X n σ` is the value at `1` of the summand inclusion attached to `σ`. -/
theorem gen_eq_genHomSd (X : TopCat) (n : ℕ) (σ : singMap X n) :
    gen X n σ = genHomSd X n ((singEquiv X n).symm σ) (1 : ℤ) := rfl

/-- **Naturality of `gen`**: pushing the generator of a singular simplex `σ` forward along a
continuous map `f` gives the generator of the composite simplex `f ∘ σ`. -/
theorem gen_map (X Y : TopCat) (n : ℕ) (f : X ⟶ Y) (σ : singMap X n) :
    ((Submission.Blueprint.singC).map f).f n (gen X n σ) = gen Y n (f.hom.comp σ) := by
  have h : genHomSd X n ((singEquiv X n).symm σ) ≫ ((Submission.Blueprint.singC).map f).f n
      = genHomSd Y n ((TopCat.toSSet.map f).app (Opposite.op (SimplexCategory.mk n))
          ((singEquiv X n).symm σ)) :=
    SSet.ι_chainComplexMap_f (TopCat.toSSet.obj X) (TopCat.toSSet.obj Y)
      (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ) ((singEquiv X n).symm σ)
  have h2 := congrArg (fun m => m (1 : ℤ)) h
  rw [CategoryTheory.comp_apply] at h2
  rw [gen_eq_genHomSd, h2]
  rfl

/-! ## Vertices and faces of affine simplices -/

/-- The underlying map of the coface inclusion `coface n i` is `StdSimplex.map i.succAbove`. -/
theorem coface_hom_apply_sd (n : ℕ) (i : Fin (n+2)) (z : StdSimplex ℝ (Fin (n+1))) :
    (coface n i).hom z = Convexity.StdSimplex.map i.succAbove z := rfl

/-- The `i`-th vertex of `Δ^k` maps to the `i`-th element of the vertex tuple under the affine
simplex it determines. -/
theorem affineSimplex_vert {k N : ℕ} (q : Fin (k+1) → StdSimplex ℝ (Fin (N+1)))
    (i : Fin (k+1)) :
    affineSimplex (n := N) (k := k) q (vert (k+1) i) = q i := by
  simp [affineSimplex, vert]

/-- **The faces of an affine simplex** are the affine simplices of the corresponding vertex
tuples: composing `affineSimplex p` with the topological coface inclusion `coface k i` deletes
the `i`-th vertex of the tuple `p`. -/
theorem affineSimplex_coface {k N : ℕ} (p : Fin (k+2) → StdSimplex ℝ (Fin (N+1)))
    (i : Fin (k+2)) :
    (affineSimplex (n := N) (k := k+1) p).comp ((coface k i).hom) =
      affineSimplex (n := N) (k := k) (fun j => p (i.succAbove j)) := by
  have hch : ∀ z, (coface k i).hom z = Convexity.StdSimplex.map i.succAbove z :=
    fun z => coface_hom_apply_sd k i z
  ext t : 1
  simp only [ContinuousMap.comp_apply, affineSimplex, ContinuousMap.coe_mk,
    StdSimplex.affineMapMk_apply, hch]
  exact Convexity.iConvexComb_map t i.succAbove p

/-- The topological coface inclusion composed with an affine simplex is the affine simplex on the
image vertex tuple. -/
theorem coface_comp_affineSimplex (N k : ℕ) (i : Fin (N+2))
    (q : Fin (k+1) → StdSimplex ℝ (Fin (N+1))) :
    ((coface N i).hom).comp (affineSimplex (n := N) (k := k) q) =
      affineSimplex (n := N+1) (k := k)
        (fun j => Convexity.StdSimplex.map i.succAbove (q j)) := by
  have hch : ∀ z, (coface N i).hom z = Convexity.StdSimplex.map i.succAbove z :=
    fun z => coface_hom_apply_sd N i z
  ext t : 1
  simp only [ContinuousMap.comp_apply, affineSimplex, ContinuousMap.coe_mk,
    StdSimplex.affineMapMk_apply, hch]
  exact Convexity.map_iConvexComb t q

/-- The identity of `Δ^N` is the affine simplex on the vertex tuple. -/
theorem affineSimplex_eq_id (N : ℕ) :
    affineSimplex (n := N) (k := N) (fun i : Fin (N+1) => vert (N+1) i) =
      ContinuousMap.id (StdSimplex ℝ (Fin (N+1))) := by
  apply ContinuousMap.ext
  intro x
  simp only [affineSimplex, ContinuousMap.coe_mk, ContinuousMap.id_apply,
    StdSimplex.affineMapMk_apply]
  exact StdSimplex.iConvexComb_single x

/-! ## The cone on a generator -/

/-- **The value of `coneChain` on a generator.** -/
theorem coneChain_gen (N k : ℕ) (b : StdSimplex ℝ (Fin (N+1))) (γ : singMap (tSplx N) k) :
    coneChain N b k (gen (tSplx N) k γ) =
      gen (tSplx N) (k+1) (affineSimplex (n := N) (k := k+1)
        (Fin.snoc (fun i : Fin (k+1) => γ (vert (k+1) i)) b)) := by
  let X := TopCat.toSSet.obj (tSplx N)
  let x := (singEquiv (tSplx N) k).symm γ
  have hfac := Cofan.IsColimit.fac (X.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) k)
    (fun γ' => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
      (gen (tSplx N) (k+1) (affineSimplex (n := N) (k := k+1) (Fin.snoc
        (fun i : Fin (k+1) => (singEquiv (tSplx N) k) γ' (vert (k+1) i)) b)))))
    x
  have h := congrArg (fun f => f (1 : ℤ)) hfac
  have hdesc : Cofan.IsColimit.desc (X.isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) k)
      (fun γ' => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _
        (gen (tSplx N) (k+1) (affineSimplex (n := N) (k := k+1) (Fin.snoc
          (fun i : Fin (k+1) => (singEquiv (tSplx N) k) γ' (vert (k+1) i)) b))))) =
      coneChain N b k := rfl
  rw [hdesc] at h
  rw [CategoryTheory.comp_apply] at h
  rw [ModuleCat.ofHom_apply, LinearMap.toSpanSingleton_apply_one] at h
  have hx : (ConcreteCategory.hom ((X.chainComplexXCofan (ModuleCat.of ℤ ℤ) k).inj x)) (1 : ℤ)
      = gen (tSplx N) k γ := rfl
  simp only [hx] at h
  simp only [x, Equiv.apply_symm_apply] at h
  exact h

/-! ## Membership in `affineSpan` -/

/-- The generator of an affine simplex lies in `affineSpan`. -/
theorem gen_affineSimplex_mem (N k : ℕ) (q : Fin (k+1) → StdSimplex ℝ (Fin (N+1))) :
    gen (tSplx N) k (affineSimplex q) ∈ affineSpan N k :=
  Submodule.subset_span ⟨q, rfl⟩

/-- **The cone `coneChain` preserves `affineSpan`.** -/
theorem coneChain_mem_affineSpan (N k : ℕ) (b : StdSimplex ℝ (Fin (N+1)))
    {z : ((Submission.Blueprint.singC).obj (tSplx N)).X k} (hz : z ∈ affineSpan N k) :
    coneChain N b k z ∈ affineSpan N (k+1) := by
  have hle : affineSpan N k ≤
      Submodule.comap (coneChain N b k).hom (affineSpan N (k+1)) := by
    rw [affineSpan, Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    change coneChain N b k (gen (tSplx N) k (affineSimplex q)) ∈ affineSpan N (k+1)
    rw [coneChain_gen]
    exact Submodule.subset_span
      ⟨Fin.snoc (fun i : Fin (k+1) => affineSimplex (n := N) (k := k) q (vert (k+1) i)) b,
        rfl⟩
  exact hle hz

/-- **The pushforward along a coface preserves `affineSpan`.** -/
theorem coface_mem_affineSpan (N k : ℕ) (i : Fin (N+2))
    {z : ((Submission.Blueprint.singC).obj (tSplx N)).X k} (hz : z ∈ affineSpan N k) :
    ((Submission.Blueprint.singC).map (coface N i)).f k z ∈ affineSpan (N+1) k := by
  have hle : affineSpan N k ≤ Submodule.comap
      (((Submission.Blueprint.singC).map (coface N i)).f k).hom (affineSpan (N+1) k) := by
    rw [affineSpan, Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    change ((Submission.Blueprint.singC).map (coface N i)).f k
        (gen (tSplx N) k (affineSimplex q)) ∈ affineSpan (N+1) k
    rw [gen_map, coface_comp_affineSimplex]
    exact Submodule.subset_span ⟨(fun j => Convexity.StdSimplex.map i.succAbove (q j)), rfl⟩
  exact hle hz

/-! ## The boundary of a generator, and `Φ ⨯ Φ = 0` -/

/-- **The boundary of a singular chain generator**: the differential of the simplicial chain
complex is the alternating sum of the face maps, and the `i`-th face of `σ` is `σ` composed
with the `i`-th coface inclusion. -/
theorem gen_d_sd (X : TopCat) (n : ℕ) (σ : singMap X (n+1)) :
    (((Submission.Blueprint.singC).obj X).d (n+1) n) (gen X (n+1) σ) =
      ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) •
        gen X n (σ.comp ((coface n i).hom)) := by
  let x := (singEquiv X (n+1)).symm σ
  have hface : ∀ i : Fin (n+2),
      singEquiv X n ((TopCat.toSSet.obj X).δ i x) =
        σ.comp ((coface n i).hom) := by
    intro i
    ext z
    simp only [coface, ContinuousMap.comp_apply, singEquiv]
    rw [TopCat.toSSetObjEquiv_δ_apply]
    rfl
  have hgen : ∀ i : Fin (n+2),
      gen X n (σ.comp ((coface n i).hom)) =
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
          ((TopCat.toSSet.obj X).δ i x)) (1 : ℤ) := by
    intro i
    rw [← hface i]
    simp only [gen, Equiv.symm_apply_apply]
  have hmain : (CategoryTheory.CategoryStruct.comp
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) x)
        (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n+1) n)) (1 : ℤ) =
      (∑ i : Fin (n+2), (-1 : ℤ)^(i : ℕ) • ((TopCat.toSSet.obj X).ιChainComplex
        (R := ModuleCat.of ℤ ℤ) ((TopCat.toSSet.obj X).δ i x))) (1 : ℤ) :=
    congrArg (fun f => f (1 : ℤ))
      (SSet.ιChainComplex_d (X := TopCat.toSSet.obj X) (R := ModuleCat.of ℤ ℤ) (n := n) x)
  change (CategoryTheory.CategoryStruct.comp
        ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) x)
        (((TopCat.toSSet.obj X).chainComplex (ModuleCat.of ℤ ℤ)).d (n+1) n)) (1 : ℤ) = _
  rw [hmain]
  simp only [hgen, LinearMap.sum_apply, LinearMap.smul_apply, ModuleCat.hom_sum,
    ModuleCat.hom_smul]

/-- The singular chains of the standard simplices, as a cosimplicial object in chain complexes. -/
noncomputable abbrev singCcsSd : CosimplicialObject (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  SimplexCategory.toTop₀ ⋙ Submission.Blueprint.singC

/-- `Work.SingMV.phi n` is the `n`-th differential of the alternating coface map complex. -/
lemma phi_eq_objD_sd (n : ℕ) :
    phi n = AlgebraicTopology.AlternatingCofaceMapComplex.objD singCcsSd n := rfl

/-- **The coface sum squares to zero**: the alternating sum of the pushforwards along the
coface inclusions composes to zero. -/
theorem phi_comp_phi_sd (n : ℕ) :
    CategoryTheory.CategoryStruct.comp (phi n) (phi (n+1)) = 0 := by
  rw [phi_eq_objD_sd n, phi_eq_objD_sd (n+1)]
  exact AlgebraicTopology.AlternatingCofaceMapComplex.d_squared singCcsSd n

end Work.SingMV
