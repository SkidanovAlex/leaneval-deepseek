import Mathlib
import Submission.Work.Cohomology.SingBridge
import Submission.Work.Cohomology.Subdivision
import Submission.Work.Cohomology.sdLC_boundary
import Submission.Work.Cohomology.toChain_boundaryLC
import Submission.Work.Cohomology.sdChainMap
import Submission.Work.Cohomology.boundaryLC_coneLC
import Submission.Work.Cohomology.embedLC_boundary

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Data for the chain homotopy between barycentric subdivision and the identity

This file sets up the chain-level data underlying the statement that the barycentric subdivision
operator `sdChainMap` on the singular chains is chain homotopic to the identity.

The homotopy we construct sends a singular `n`-simplex `σ : Δⁿ ⟶ X` to the `(n+1)`-chain
`σ_*(cLC n)`, where `cLC n ∈ C_{n+1}(Δⁿ)` is the `(n+1)`-chain of the *standard* simplex defined by
the cone recursion

`cLC 0 = 0`,  `cLC (n+1) = cone_{bary (idVert (n+1))} (sdLC (n+1) - iotaLC (n+1) - ∑ᵢ (-1)ⁱ δᵢ (cLC n))`,

with `iotaLC n = [idVert n]` the identity simplex of `Δⁿ`.  The whole construction is the classical
one: the chain `cLC n` is a primitive for the difference between the subdivision of the identity
simplex and the identity simplex itself.

## Main definitions

* `iotaLC n` — the identity simplex of `Δⁿ` as an affine chain;
* `cLC n` — the `(n+1)`-chain of `Δⁿ` realising the homotopy on the standard simplices;
* `cLCarg m` — the argument of the cone in the recursion for `cLC (m+1)`;
* `tElem X n σ` — the image of the generator `σ` under the homotopy;
* `tHom X n` — the homotopy component `C_n(X) ⟶ C_{n+1}(X)`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

/-- The identity simplex of `Δⁿ`, as an affine chain. -/
def iotaLC (n : ℕ) : LinChain n n :=
  Finsupp.single (idVert n) 1

/-- The chain `cLC n ∈ C_{n+1}(Δⁿ)` which underlies the homotopy on the standard simplices. -/
def cLC (n : ℕ) : LinChain n (n + 1) :=
  match n with
  | 0 => 0
  | (n + 1) => coneLC (n + 1) (n + 1) (bary (idVert (n + 1)))
      (sdLC (n + 1) - iotaLC (n + 1)
        - ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • embedLC n (n + 1) i (cLC n))

/-- The argument of the cone in the recursion defining `cLC (m+1)`. -/
def cLCarg (m : ℕ) : LinChain (m + 1) (m + 1) :=
  sdLC (m + 1) - iotaLC (m + 1)
    - ∑ i : Fin (m + 2), ((-1 : ℤ) ^ (i : ℕ)) • embedLC m (m + 1) i (cLC m)

lemma cLC_zero : cLC 0 = 0 := rfl

lemma cLC_succ (m : ℕ) :
    cLC (m + 1) = coneLC (m + 1) (m + 1) (bary (idVert (m + 1))) (cLCarg m) := rfl

lemma sdLC_zero : sdLC 0 = iotaLC 0 := rfl

/-- The boundary of the identity simplex is the alternating sum of its faces. -/
lemma boundaryLC_iotaLC (m : ℕ) :
    boundaryLC (m + 1) m (iotaLC (m + 1)) =
      ∑ i : Fin (m + 2), ((-1 : ℤ) ^ (i : ℕ)) • embedLC m m i (iotaLC m) := by
  have key : ∀ i : Fin (m + 2),
      faceVF (N := m + 1) i (idVert (m + 1)) =
        (fun j => stdSimplex.map i.succAbove (idVert m j)) := by
    intro i; funext j
    simp [faceVF, idVert, stdSimplex.map_vertex]
  rw [iotaLC, boundaryLC_single]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iotaLC, embedLC_map_single, key i]

/-! ### The generalised simplicial identity for the two-step face embeddings -/

/-- The `ℤ`-linear map on affine `k`-chains of `Δᵐ` induced by a map of vertex sets. -/
private def sigMapG (m k : ℕ) (σ : Fin (m + 1) → Fin (m + 3)) :
    LinChain m k →ₗ[ℤ] LinChain (m + 2) k :=
  Finsupp.lmapDomain ℤ ℤ
    (fun v : Fin (k + 1) → stdSimplex ℝ (Fin (m + 1)) => fun t => stdSimplex.map σ (v t))

private lemma embedLC_comp_eq_gen (m k : ℕ) (i : Fin (m + 3)) (j : Fin (m + 2)) :
    embedLC (m + 1) k i ∘ₗ embedLC m k j
      = sigMapG m k ((Fin.succAbove i).comp (Fin.succAbove j)) := by
  simp only [sigMapG, embedLC]
  rw [← Finsupp.lmapDomain_comp]
  congr 1
  funext v t
  exact (stdSimplex.map_comp_apply (Fin.succAbove j) (Fin.succAbove i) (v t))

/-- **The generalised simplicial identity**: the alternating sum of the two-step face embeddings
`embedLC (m+1) k i ∘ embedLC m k j` vanishes, for any degree `k`. -/
theorem sum_embedLC_comp_gen (m k : ℕ) :
    (∑ p : Fin (m + 3) × Fin (m + 2),
        ((-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ))) •
          (embedLC (m + 1) k p.1 ∘ₗ embedLC m k p.2)) = 0 := by
  simp only [embedLC_comp_eq_gen]
  let f : Fin (m + 3) × Fin (m + 2) → (LinChain m k →ₗ[ℤ] LinChain (m + 2) k) :=
    fun p => ((-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ))) •
      sigMapG m k ((Fin.succAbove p.1).comp (Fin.succAbove p.2))
  let g : Fin (m + 3) × Fin (m + 2) → Fin (m + 3) × Fin (m + 2) :=
    fun p => (Fin.succAbove p.1 p.2, Fin.predAbove p.2 p.1)
  have hsign : ∀ (i : Fin (m + 3)) (j : Fin (m + 2)),
      ((-1 : ℤ) ^ ((Fin.succAbove i j : ℕ) + (Fin.predAbove j i : ℕ)))
        = -((-1 : ℤ) ^ ((i : ℕ) + (j : ℕ))) := by
    intro i j
    simpa using Fin.neg_one_pow_succAbove_add_predAbove (R := ℤ) i j
  have hsig : ∀ (i : Fin (m + 3)) (j : Fin (m + 2)),
      (Fin.succAbove (Fin.succAbove i j)).comp (Fin.succAbove (Fin.predAbove j i))
        = (Fin.succAbove i).comp (Fin.succAbove j) := by
    intro i j
    funext k
    exact Fin.succAbove_succAbove_succAbove_predAbove i j k
  have key : (∑ p : Fin (m + 3) × Fin (m + 2), f p) = 0 := by
    refine Finset.sum_ninvolution (s := Finset.univ) g ?_ ?_ ?_ ?_
    · intro a
      have h : f (g a) = -f a := by
        obtain ⟨i, j⟩ := a
        simp only [f, g]
        rw [hsign i j, hsig i j, neg_smul]
      rw [h, add_neg_cancel]
    · intro a _
      obtain ⟨i, j⟩ := a
      intro h
      have h1 : (Fin.succAbove i j) = i := by
        simpa [g] using congrArg Prod.fst h
      exact Fin.succAbove_ne i j h1
    · intro a
      exact Finset.mem_univ _
    · intro a
      obtain ⟨i, j⟩ := a
      simp only [g]
      rw [Fin.succAbove_succAbove_predAbove i j, Fin.predAbove_predAbove_succAbove i j]
  simpa [f] using key

/-- The applied form of the generalised simplicial identity. -/
theorem sum_embedLC_comp_gen_apply (m k : ℕ) (x : LinChain m k) :
    (∑ p : Fin (m + 3) × Fin (m + 2),
        ((-1 : ℤ) ^ ((p.1 : ℕ) + (p.2 : ℕ))) •
          (embedLC (m + 1) k p.1 (embedLC m k p.2 x))) = 0 := by
  have h2 := congrArg
    (fun (f : LinChain m k →ₗ[ℤ] LinChain (m + 2) k) => f x) (sum_embedLC_comp_gen m k)
  simp only [LinearMap.zero_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply] at h2
  exact h2

/-! ### The boundary of `cLC` -/

/-- Combining the boundary of the three pieces of the cone argument of `cLC (n+1)`. -/
private lemma cLCarg_combine (n : ℕ) :
    boundaryLC (n + 1) n
      (sdLC (n + 1) - iotaLC (n + 1)
        - ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • embedLC n (n + 1) i (cLC n))
      = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • embedLC n n i
          (sdLC n - iotaLC n - boundaryLC n n (cLC n)) := by
  rw [map_sub, map_sub, map_sum]
  rw [sdLC_boundary n, boundaryLC_iotaLC n]
  simp only [map_smul, embedLC_boundary]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sub, map_sub, smul_sub, smul_sub]

/-- The cone argument of `cLC (m+1)` is a cycle. -/
theorem boundaryLC_cLCarg (m : ℕ) : boundaryLC (m + 1) m (cLCarg m) = 0 := by
  induction m with
  | zero =>
    unfold cLCarg
    rw [cLCarg_combine 0]
    have hZ : sdLC 0 - iotaLC 0 - boundaryLC 0 0 (cLC 0) = 0 := by
      rw [cLC_zero, map_zero, sub_zero, sdLC_zero, sub_self]
    rw [hZ]
    simp
  | succ m ih =>
    unfold cLCarg
    rw [cLCarg_combine (m + 1)]
    have hb : boundaryLC (m + 1) (m + 1) (cLC (m + 1)) = cLCarg m := by
      rw [cLC_succ m, boundaryLC_coneLC, ih, map_zero, sub_zero]
    rw [hb]
    rw [show sdLC (m + 1) - iotaLC (m + 1) - cLCarg m
        = ∑ j : Fin (m + 2), ((-1 : ℤ) ^ (j : ℕ)) • embedLC m (m + 1) j (cLC m) from by
      unfold cLCarg; abel]
    simp only [map_sum, Finset.smul_sum, map_smul, smul_smul, ← pow_add]
    rw [← Finset.sum_product', Finset.univ_product_univ]
    exact sum_embedLC_comp_gen_apply m (m + 1) (cLC m)

/-- **The boundary of `cLC (m+1)`**: `cLC (m+1)` is a primitive for the difference between the
subdivision of the identity `(m+1)`-simplex and the identity simplex itself. -/
theorem cLC_boundary (m : ℕ) :
    boundaryLC (m + 1) (m + 1) (cLC (m + 1)) = cLCarg m := by
  rw [cLC_succ m, boundaryLC_coneLC, boundaryLC_cLCarg m, map_zero, sub_zero]

/-! ### The homotopy data on the singular chains -/

/-- The homotopy image of a singular `n`-simplex `σ`: the push-forward `σ_*(cLC n)`. -/
def tElem (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (singularChains ℤ X).X (n + 1) :=
  ((SSet.chainComplexMap (TopCat.toSSet.map (sdMap n σ)) (ModuleCat.of ℤ ℤ)).f (n + 1)).hom
    (toChain n (n + 1) (cLC n))

/-- The homotopy component `C_n(X) ⟶ C_{n+1}(X)`. -/
def tHom (X : TopCat) (n : ℕ) : (singularChains ℤ X).X n ⟶ (singularChains ℤ X).X (n + 1) :=
  ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n).desc
    (Cofan.mk ((singularChains ℤ X).X (n + 1))
      (fun σ : (TopCat.toSSet.obj X) _⦋n⦌ =>
        ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (tElem X n σ))))

lemma tHom_ι (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ ≫ tHom X n
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ (tElem X n σ)) :=
  Cofan.IsColimit.fac _ _ _

/-- `tHom` on a generator. -/
lemma tHom_gen (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (tHom X n).hom (gen X n σ) = tElem X n σ := by
  have h := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (singularChains ℤ X).X (n + 1)) =>
    g.hom (1 : ℤ)) (tHom_ι X n σ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul, gen] at h ⊢
  exact h

lemma tElem_zero (X : TopCat) (σ : (TopCat.toSSet.obj X) _⦋0⦌) : tElem X 0 σ = 0 := by
  rw [tElem, cLC_zero, map_zero, map_zero]

lemma tHom_zero (X : TopCat) : tHom X 0 = 0 := by
  apply SSet.chainComplex_hom_ext (X := TopCat.toSSet.obj X)
  intro σ
  rw [tHom_ι, tElem_zero]
  simp [LinearMap.toSpanSingleton_zero]

/-! ### The push-forward of the identity simplex -/

/-- The push-forward of the identity `n`-simplex of `Δⁿ` along `σ` is `σ` itself. -/
lemma sdMap_app_idVert (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    (TopCat.toSSet.map (sdMap n σ)).app (Opposite.op ⦋n⦌) (linSimplex (idVert n)) = σ := by
  apply (TopCat.toSSetObjEquivT X (Opposite.op ⦋n⦌)).injective
  ext z : 1
  rw [toSSetObjEquiv_map_apply, toSSetObjEquiv_linSimplex]
  rw [show affineSimplex (idVert n) z = z from affineSimplex_id z]
  simp [sdMap]

/-- The push-forward of the identity chain `iotaLC n` along a singular simplex `σ` is the
generator `gen X n σ`. -/
lemma push_id_simplex (X : TopCat) (n : ℕ) (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    ((SSet.chainComplexMap (TopCat.toSSet.map (sdMap n σ)) (ModuleCat.of ℤ ℤ)).f n).hom
      (toChain n n (iotaLC n)) = gen X n σ := by
  rw [iotaLC, toChain_apply_single, one_smul, chainComplexMap_ι_apply]
  rw [sdMap_app_idVert]
  rfl

/-- In degree `0`, the subdivision of a singular simplex is the simplex itself. -/
lemma sdElem_zero (X : TopCat) (σ : (TopCat.toSSet.obj X) _⦋0⦌) :
    sdElem X 0 σ = gen X 0 σ := by
  rw [sdElem_eq]
  exact push_id_simplex X 0 σ

/-! ### The homotopy component indexed by the relation -/

/-- The homotopy component in the shape required by `Homotopy.nullHomotopicMap'`: it is `tHom X i`
transported along the relation `i + 1 = j`. -/
def tRel (X : TopCat) (i j : ℕ) (hij : (ComplexShape.down ℕ).Rel j i) :
    (singularChains ℤ X).X i ⟶ (singularChains ℤ X).X j :=
  tHom X i ≫ eqToHom (by rw [show i + 1 = j from hij])

/-- On the pairs in the relation, `tRel X` is just `tHom X` (the transport is along an identity). -/
lemma tRel_self (X : TopCat) (i : ℕ) (h : (ComplexShape.down ℕ).Rel (i + 1) i) :
    tRel X i (i + 1) h = tHom X i := by
  simp [tRel]

end

end Work.Cohomology
