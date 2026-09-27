/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# Every cocycle is cohomologous to a normalized one

For a simplicial set `S`, a cochain `u : Cochain S ℚ p` is *normalized* when it vanishes on all
degenerate `p`-simplices (`Work.Cohomology.IsNormalized`).  The main result of this file is

`Work.Cohomology.normalized_rep` : every *cocycle* of degree `p` is cohomologous (i.e. differs by
a coboundary) to a normalized cocycle.

Equivalently, the inclusion of the normalized cochain complex into the full cochain complex
induces a surjection on cohomology.

## Strategy of the proof

The normalized cochain complex is the dual of the chain complex `N_•(S)` of "non-degenerate"
chains, and the projection `PInfty` of the Dold–Kan theory (available in Mathlib as
`AlgebraicTopology.DoldKan.PInfty` for the simplicial chain complex `S.chainComplex ℚ`) is a
chain map which is homotopic to the identity (`AlgebraicTopology.DoldKan.homotopyPInftyToId`)
and which kills degenerate simplices (`SSet.ιNormalizedChainComplex_eq_zero`).

Concretely, writing `K := S.chainComplex (ModuleCat.of ℚ ℚ)` for the simplicial chain complex:

* `Theta S n : K.X n ⟶ SChain S ℚ n` sends a chain of the simplicial set to a finitely supported
  function (an honest "measure") on the `n`-simplices; it is characterized by
  `Theta S n (ι x q) = q • single x 1` (`normTheta_apply`) and it is a chain map
  (`normTheta_comp_d`), the differential `d` corresponding to the chain boundary `sbdry`.
* For a cochain `u`, `normPhi S p u := seval S ℚ p u ∘ Theta S p` is the functional on the chain
  complex computing `u`; it satisfies `normPhi_elt : normPhi u (chElt x) = u x`, and for a
  *cocycle* `u`, `normPhi_comp_d : normPhi u (∂ y) = 0` for all `y` (this is `seval_coboundary`
  plus the cocycle condition — the cocycle condition is used exactly here).
* For a cocycle `u` of degree `n+1` we put
  `u' x := normPhi u (PInfty (chElt x))` and `v τ := normPhi u (H (chElt τ))`, where `H` is the
  degree-`(n+1)` part of the homotopy `PInfty ≃ 𝟙`.  From the chain homotopy identity
  (`normHomotopy_id`) and the two bullet points above one gets the pointwise identity
  `(δv) x = u' x - u x`; hence `u - u' = δ(-v)` is a coboundary, `u' = u + δv` is again a
  cocycle, and `u'` is normalized because `PInfty` kills degenerate simplices.
-/
import Mathlib
import Submission.Work.Cohomology.EZShuffle
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.Cohomology

open CategoryTheory Simplicial Opposite Limits HomologicalComplex

namespace Work.Cohomology

open Submission.Cohomology

noncomputable section

/-! ### The chain complex of a simplicial set and the comparison with `SChain` -/

/-- The simplicial chain complex of `S` with coefficients in `ℚ`, as a `ChainComplex`. -/
noncomputable abbrev normKC (S : SSet.{0}) : ChainComplex (ModuleCat ℚ) ℕ :=
  S.chainComplex (ModuleCat.of ℚ ℚ)

/-- The simplicial `ℚ`-module whose alternating face map complex is `normKC S`. -/
noncomputable abbrev normSimplicial (S : SSet.{0}) : SimplicialObject (ModuleCat ℚ) :=
  ((Limits.sigmaConst ⋙ SimplicialObject.whiskering (Type) (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)).obj S

/-- The homotopy from the Dold–Kan projection `PInfty` to the identity of the simplicial chain
complex of `S`. -/
noncomputable def normHPin (S : SSet.{0}) :
    Homotopy (AlgebraicTopology.DoldKan.PInfty (X := normSimplicial S)) (𝟙 (normKC S)) :=
  AlgebraicTopology.DoldKan.homotopyPInftyToId (normSimplicial S)

/-- The Dold–Kan projection `PInfty` in degree `n`, as an endomorphism of `normKC S .X n`. -/
noncomputable def normPinf (S : SSet.{0}) (n : ℕ) : (normKC S).X n ⟶ (normKC S).X n :=
  (AlgebraicTopology.DoldKan.PInfty (X := normSimplicial S)).f n

/-- The degree `(n+1)` part of the homotopy from `PInfty` to the identity. -/
noncomputable def normHty (S : SSet.{0}) (n : ℕ) : (normKC S).X n ⟶ (normKC S).X (n + 1) :=
  (normHPin S).hom n (n + 1)

/-- The chain attached to a simplex: the basis element of the coproduct corresponding to `x`. -/
noncomputable abbrev normElt (S : SSet.{0}) {n : ℕ} (x : S _⦋n⦌) : (normKC S).X n :=
  (S.ιChainComplex (R := ModuleCat.of ℚ ℚ) x) (1 : ℚ)

/-- The chain homotopy identity, evaluated on an element: `PInfty y = H (∂ y) + ∂ (H y) + y`. -/
lemma normHomotopy_id (S : SSet.{0}) (n : ℕ) (y : (normKC S).X (n + 1)) :
    ModuleCat.Hom.hom (normPinf S (n + 1)) y
      = ModuleCat.Hom.hom (normHty S n) (((normKC S).d (n + 1) n) y)
        + ((normKC S).d (n + 2) (n + 1)) (ModuleCat.Hom.hom (normHty S (n + 1)) y) + y := by
  have h := (normHPin S).comm (n + 1)
  rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
  have h2 := congrArg (fun (f : (normKC S).X (n + 1) ⟶ (normKC S).X (n + 1)) =>
    ModuleCat.Hom.hom f y) h
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply,
    LinearMap.comp_apply] at h2
  exact h2

/-- The homotopy identity in the form `PInfty y - y = H (∂ y) + ∂ (H y)`. -/
lemma normHomotopy_id' (S : SSet.{0}) (n : ℕ) (y : (normKC S).X (n + 1)) :
    ModuleCat.Hom.hom (normPinf S (n + 1)) y - y
      = ModuleCat.Hom.hom (normHty S n) (((normKC S).d (n + 1) n) y)
        + ((normKC S).d (n + 2) (n + 1)) (ModuleCat.Hom.hom (normHty S (n + 1)) y) := by
  rw [normHomotopy_id]; abel

/-- The chain complex of a simplicial set maps to the finitely supported chains on its simplices,
by sending the basis element `ι x` to the "measure" `single x 1`. -/
noncomputable def normTheta (S : SSet.{0}) (n : ℕ) :
    (normKC S).X n ⟶ ModuleCat.of ℚ (SChain S ℚ n) :=
  Limits.Cofan.IsColimit.desc (S.isColimitChainComplexXCofan (ModuleCat.of ℚ ℚ) n)
    (fun x => ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ (SChain S ℚ n) (Finsupp.single x 1)))

lemma normTheta_fac (S : SSet.{0}) (n : ℕ) (x : S _⦋n⦌) :
    S.ιChainComplex (R := ModuleCat.of ℚ ℚ) x ≫ normTheta S n
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ (SChain S ℚ n) (Finsupp.single x 1)) :=
  Limits.Cofan.IsColimit.fac _ _ x

/-- The value of `normTheta` on the basis elements. -/
lemma normTheta_apply (S : SSet.{0}) (n : ℕ) (x : S _⦋n⦌) (q : ℚ) :
    ModuleCat.Hom.hom (normTheta S n) ((S.ιChainComplex (R := ModuleCat.of ℚ ℚ) x) q)
      = q • Finsupp.single x 1 := by
  have h := congrArg (fun (f : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ (SChain S ℚ n)) => f q)
    (normTheta_fac S n x)
  simpa [LinearMap.toSpanSingleton_apply] using h

/-- The chain differential of the basis element `x`, expressed as an alternating sum of the
basis elements of the faces. -/
lemma normD_elt (S : SSet.{0}) (n : ℕ) (x : S _⦋n+1⦌) (q : ℚ) :
    ((normKC S).d (n + 1) n) ((S.ιChainComplex (R := ModuleCat.of ℚ ℚ) x) q)
      = ∑ i : Fin (n + 2),
          ((-1 : ℤ) ^ (i : ℕ)) • ((S.ιChainComplex (R := ModuleCat.of ℚ ℚ) (S.δ i x)) q) := by
  rw [← CategoryTheory.comp_apply, SSet.ιChainComplex_d]
  simp only [ModuleCat.hom_smul, ModuleCat.hom_sum, Int.reduceNeg]
  simp

/-- `normTheta` is a chain map: the simplicial differential corresponds to the chain boundary
`sbdry` (this is `sbdry_single` in disguise). -/
lemma normTheta_comp_d (S : SSet.{0}) (n : ℕ) :
    ((normKC S).d (n + 1) n ≫ normTheta S n)
      = (normTheta S (n + 1) ≫ ModuleCat.ofHom (sbdry S ℚ n)) := by
  refine Limits.Cofan.IsColimit.hom_ext
    (S.isColimitChainComplexXCofan (ModuleCat.of ℚ ℚ) (n + 1)) _ _ (fun x => ?_)
  change S.ιChainComplex (R := ModuleCat.of ℚ ℚ) x ≫ ((normKC S).d (n + 1) n ≫ normTheta S n) =
    S.ιChainComplex (R := ModuleCat.of ℚ ℚ) x ≫ (normTheta S (n + 1) ≫ ModuleCat.ofHom (sbdry S ℚ n))
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro q
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
  rw [normD_elt, normTheta_apply, map_sum]
  simp only [map_zsmul]
  rw [map_smul, sbdry_single, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [normTheta_apply]
  simp only [zsmul_eq_mul, Finsupp.smul_single]
  ring_nf

/-- `normTheta` is a chain map, evaluated on elements. -/
lemma normTheta_comp_d_apply (S : SSet.{0}) (n : ℕ) (y : (normKC S).X (n + 1)) :
    ModuleCat.Hom.hom (normTheta S n) (((normKC S).d (n + 1) n) y)
      = sbdry S ℚ n (ModuleCat.Hom.hom (normTheta S (n + 1)) y) := by
  have h := congrArg (fun (f : (normKC S).X (n + 1) ⟶ ModuleCat.of ℚ (SChain S ℚ n)) => f y)
    (normTheta_comp_d S n)
  simpa [CategoryTheory.comp_apply, ModuleCat.hom_ofHom] using h

/-! ### The functional associated with a cochain -/

/-- The functional on the chain complex of `S` in degree `p` associated with a cochain `u`:
it is "`u` applied to a chain", transported along `normTheta`. -/
noncomputable def normPhi (S : SSet.{0}) (p : ℕ) (u : Cochain S ℚ p) : (normKC S).X p →ₗ[ℚ] ℚ :=
  (seval S ℚ p u).comp (ModuleCat.Hom.hom (normTheta S p))

lemma normPhi_apply (S : SSet.{0}) (p : ℕ) (u : Cochain S ℚ p) (y : (normKC S).X p) :
    normPhi S p u y = seval S ℚ p u (ModuleCat.Hom.hom (normTheta S p) y) := rfl

/-- `normPhi` extends the cochain `u` from the basis elements. -/
lemma normPhi_elt (S : SSet.{0}) (p : ℕ) (u : Cochain S ℚ p) (x : S _⦋p⦌) :
    normPhi S p u (normElt S x) = u x := by
  rw [normPhi_apply, normTheta_apply, map_smul, seval_single]
  simp

/-- The crucial consequence of the cocycle condition: for a cocycle `u`, the functional
`normPhi u` vanishes on the image of the differential (here `y` is an arbitrary element of the
chain complex in degree `p+1`). -/
lemma normPhi_comp_d (S : SSet.{0}) (p : ℕ) (u : Cochain S ℚ p)
    (hu : coboundary S ℚ p u = 0) (y : (normKC S).X (p + 1)) :
    normPhi S p u (((normKC S).d (p + 1) p) y) = 0 := by
  rw [normPhi_apply, normTheta_comp_d_apply, ← seval_coboundary, hu]
  simp [seval]

/-- The Dold–Kan projection kills degenerate simplices. -/
lemma normPinf_elt_degenerate (S : SSet.{0}) (p : ℕ) (x : S _⦋p⦌)
    (hx : x ∈ S.degenerate p) : ModuleCat.Hom.hom (normPinf S p) (normElt S x) = 0 := by
  have hclone := SSet.toNormalizedChainComplex_fromNormalizedChainComplex S (ModuleCat.of ℚ ℚ)
  have hf : (normPinf S p) = (S.toNormalizedChainComplex (ModuleCat.of ℚ ℚ)).f p ≫
      (S.fromNormalizedChainComplex (ModuleCat.of ℚ ℚ)).f p := by
    have hh := congrArg (fun (f : normKC S ⟶ normKC S) => f.f p) hclone
    rw [HomologicalComplex.comp_f] at hh
    exact hh.symm
  have hzero : S.ιChainComplex (R := ModuleCat.of ℚ ℚ) x ≫ (normPinf S p) = 0 := by
    rw [hf, ← Category.assoc, SSet.ιChainComplex_toNormalizedChainComplex_f,
      SSet.ιNormalizedChainComplex_eq_zero S x hx, zero_comp]
  have h2 := congrArg (fun (f : ModuleCat.of ℚ ℚ ⟶ (normKC S).X p) => f (1 : ℚ)) hzero
  simpa [normElt, CategoryTheory.comp_apply] using h2

/-! ### The normalization of a cocycle of positive degree -/

/-- **Key step.**  A cocycle of degree `n+1` is cohomologous to a normalized cocycle. -/
theorem normalized_rep_succ (S : SSet.{0}) (n : ℕ) (u : Cochain S ℚ (n + 1))
    (hu : u ∈ cycles S ℚ (n + 1)) :
    ∃ u' : Cochain S ℚ (n + 1), u' ∈ cycles S ℚ (n + 1) ∧ IsNormalized u' ∧
      u - u' ∈ boundaries S ℚ (n + 1) := by
  have huc : coboundary S ℚ (n + 1) u = 0 := hu
  -- the normalized candidate and the "correcting" cochain
  let u' : Cochain S ℚ (n + 1) :=
    fun x => normPhi S (n + 1) u (ModuleCat.Hom.hom (normPinf S (n + 1)) (normElt S x))
  let v : Cochain S ℚ n :=
    fun τ => normPhi S (n + 1) u (ModuleCat.Hom.hom (normHty S n) (normElt S τ))
  have hv : v = fun τ => normPhi S (n + 1) u
      (ModuleCat.Hom.hom (normHty S n) (normElt S τ)) := rfl
  have hu'eq : u' = fun x => normPhi S (n + 1) u
      (ModuleCat.Hom.hom (normPinf S (n + 1)) (normElt S x)) := rfl
  -- `δ v` in terms of the homotopy
  have hLHS : ∀ x : S _⦋n+1⦌, (coboundary S ℚ n v) x
      = normPhi S (n + 1) u
          (ModuleCat.Hom.hom (normHty S n) (((normKC S).d (n + 1) n) (normElt S x))) := by
    intro x
    rw [coboundary_apply]
    rw [show (∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • v (S.δ i x))
        = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • normPhi S (n + 1) u
            (ModuleCat.Hom.hom (normHty S n) (normElt S (S.δ i x))) from by
      refine Finset.sum_congr rfl fun i _ => by rw [hv]]
    rw [normD_elt]
    simp only [map_sum, map_zsmul]
  -- `u' - u` in terms of the homotopy (here the cocycle condition is used)
  have hRHS : ∀ x : S _⦋n+1⦌, u' x - u x
      = normPhi S (n + 1) u
          (ModuleCat.Hom.hom (normHty S n) (((normKC S).d (n + 1) n) (normElt S x))) := by
    intro x
    rw [hu'eq, ← normPhi_elt S (n + 1) u x, ← map_sub, normHomotopy_id', map_add,
      normPhi_comp_d S (n + 1) u huc, add_zero]
  have hkey : u' - u = coboundary S ℚ n v := by
    funext x
    rw [Pi.sub_apply, hRHS x, hLHS x]
  refine ⟨u', ?_, ?_, ?_⟩
  · -- `u'` is a cocycle
    rw [mem_cycles_iff]
    have h1 : u' = u + coboundary S ℚ n v := by rw [← hkey]; abel
    rw [h1, map_add, coboundary_coboundary, add_zero, huc]
  · -- `u'` is normalized
    intro x hx
    change normPhi S (n + 1) u (ModuleCat.Hom.hom (normPinf S (n + 1)) (normElt S x)) = 0
    rw [normPinf_elt_degenerate S (n + 1) x hx, map_zero]
  · -- `u - u'` is a coboundary
    rw [mem_boundaries_succ]
    refine ⟨-v, ?_⟩
    rw [map_neg, ← hkey]
    abel

/-- **Every cocycle is cohomologous to a normalized cocycle**: the normalized cochain complex
computes the same cohomology as the full cochain complex (surjectivity part). -/
theorem normalized_rep {S : SSet.{0}} {p : ℕ} (u : Submission.Cohomology.Cochain S ℚ p)
    (hu : u ∈ Submission.Cohomology.cycles S ℚ p) :
    ∃ u' : Submission.Cohomology.Cochain S ℚ p,
      u' ∈ Submission.Cohomology.cycles S ℚ p ∧ Work.Cohomology.IsNormalized u' ∧
      u - u' ∈ Submission.Cohomology.boundaries S ℚ p := by
  rcases p with _ | n
  · -- in degree `0` there are no degenerate simplices and no coboundaries
    refine ⟨u, hu, ?_, ?_⟩
    · intro σ hσ
      rw [SSet.degenerate_zero] at hσ
      exact absurd hσ (Set.notMem_empty σ)
    · rw [show boundaries S ℚ 0 = ⊥ from rfl, Submodule.mem_bot]
      abel
  · exact normalized_rep_succ S n u hu

end

end Work.Cohomology
