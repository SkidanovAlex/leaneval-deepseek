import Mathlib
import Submission.Work.Serre.simpHomPrism
import Submission.Work.Cohomology.Crux33.ezBridge

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The chain homotopy attached to a family of homotopies of simplices

This file defines, for a family `SimpHom.G` of homotopies of singular simplices of `X` in
dimensions `≤ N`:

* `Work.Serre.hSimplex H n k σ` — the `(n+1)`-simplex of the singular simplicial set attached to
  the `k`-th prism piece of an `n`-simplex `σ`;
* `Work.Serre.gSimplex H n σ` — the "top" simplex `z ↦ G n σ (z,1)`;
* the five face identities relating them, transported from the geometric identities of
  `Submission/Work/Serre/simpHomPrism.lean`;
* `Work.Serre.prismHom H n : C_n(X) ⟶ C_{n+1}(X)` — the chain homotopy
  `σ ↦ ∑_k (-1)^{k+1} [hSimplex H n k σ]`, and `Work.Serre.topChainMap H n : C_n(X) ⟶ C_n(X)` —
  the "top" map `σ ↦ [gSimplex H n σ]`, together with their evaluation on generators.
-/

open CategoryTheory Limits AlgebraicTopology Simplicial
open scoped Simplicial
open Work.RatHurewicz.Bridge (coface coface_apply)

namespace Work.Serre

noncomputable section

/-- The singular simplicial set of `X`, as an `SSet`. -/
abbrev singX (X : Type) [TopologicalSpace X] : SSet := TopCat.toSSet.obj (TopCat.of X)

variable {X : Type} [TopologicalSpace X] {A : Set X} {N : ℕ}

/-- The type of `n`-simplices of the singular simplicial set of `X`, written without the
`SimplexCategory` notation so that statements can be delegated without opening the `Simplicial`
scope. -/
abbrev SSetSimplex (X : Type) [TopologicalSpace X] (n : ℕ) : Type :=
  (singX X).obj (Opposite.op (SimplexCategory.mk n))

/-- The *(n+1)*-simplex of the singular simplicial set attached to the `k`-th prism piece of an
`n`-simplex. -/
def hSimplex (H : SimpHom X A N) (n : ℕ) (k : Fin (n + 1)) (σ : singX X _⦋n⦌) :
    singX X _⦋n + 1⦌ :=
  ((TopCat.of X).toSSetObjEquivOld (Opposite.op ⦋n + 1⦌)).symm
    (prismSimplex H n k ((TopCat.of X).toSSetObjEquivOld (Opposite.op ⦋n⦌) σ))

/-- The `n`-simplex of the singular simplicial set which is the top of the homotopy of `σ`. -/
def gSimplex (H : SimpHom X A N) (n : ℕ) (σ : singX X _⦋n⦌) : singX X _⦋n⦌ :=
  ((TopCat.of X).toSSetObjEquivOld (Opposite.op ⦋n⦌)).symm
    (topSimplex H n ((TopCat.of X).toSSetObjEquivOld (Opposite.op ⦋n⦌) σ))

theorem toSSetObjEquiv_hSimplex (H : SimpHom X A N) (n : ℕ) (k : Fin (n + 1))
    (σ : singX X _⦋n⦌) :
    (TopCat.of X).toSSetObjEquivOld (Opposite.op ⦋n + 1⦌) (hSimplex H n k σ)
      = prismSimplex H n k ((TopCat.of X).toSSetObjEquivOld (Opposite.op ⦋n⦌) σ) :=
  Equiv.apply_symm_apply _ _

theorem toSSetObjEquiv_gSimplex (H : SimpHom X A N) (n : ℕ) (σ : singX X _⦋n⦌) :
    (TopCat.of X).toSSetObjEquivOld (Opposite.op ⦋n⦌) (gSimplex H n σ)
      = topSimplex H n ((TopCat.of X).toSSetObjEquivOld (Opposite.op ⦋n⦌) σ) :=
  Equiv.apply_symm_apply _ _

/-- Face maps of the singular simplicial set, in terms of the continuous simplices. -/
theorem toSSetObjEquiv_δ (n : ℕ) (i : Fin (n + 2)) (x : singX X _⦋n + 1⦌) :
    (TopCat.of X).toSSetObjEquivOld (Opposite.op ⦋n⦌) ((singX X).δ i x)
      = ((TopCat.of X).toSSetObjEquivOld (Opposite.op ⦋n + 1⦌) x).comp (coface n i) := by
  refine ContinuousMap.ext (fun z => ?_)
  rw [ContinuousMap.comp_apply, coface_apply]
  exact TopCat.toSSetObjEquivOld_δ_apply x i z

/-! ## The face identities at the level of the singular simplicial set -/

theorem δ_hSimplex_zero (H : SimpHom X A N) (n : ℕ) (hn : n ≤ N) (σ : singX X _⦋n⦌) :
    (singX X).δ (0 : Fin (n + 2)) (hSimplex H n 0 σ) = gSimplex H n σ := by
  apply ((TopCat.of X).toSSetObjEquivOld (Opposite.op ⦋n⦌)).injective
  rw [toSSetObjEquiv_δ, toSSetObjEquiv_gSimplex, toSSetObjEquiv_hSimplex]
  exact prismSimplex_coface_zero H n hn _

theorem δ_hSimplex_last (H : SimpHom X A N) (n : ℕ) (hn : n ≤ N) (σ : singX X _⦋n⦌) :
    (singX X).δ (Fin.last (n + 1)) (hSimplex H n (Fin.last n) σ) = σ := by
  apply ((TopCat.of X).toSSetObjEquivOld (Opposite.op ⦋n⦌)).injective
  rw [toSSetObjEquiv_δ, toSSetObjEquiv_hSimplex, prismSimplex_coface_last H n hn]

theorem δ_hSimplex_diag (H : SimpHom X A N) {m : ℕ} (hm : m + 1 ≤ N)
    (σ : singX X _⦋m + 1⦌) (j : Fin (m + 1)) :
    (singX X).δ (j.castSucc.succ) (hSimplex H (m + 1) j.castSucc σ)
      = (singX X).δ (j.castSucc.succ) (hSimplex H (m + 1) j.succ σ) := by
  apply ((TopCat.of X).toSSetObjEquivOld (Opposite.op ⦋m + 1⦌)).injective
  rw [toSSetObjEquiv_δ, toSSetObjEquiv_δ, toSSetObjEquiv_hSimplex, toSSetObjEquiv_hSimplex]
  exact prismSimplex_coface_diag H hm j _

theorem δ_hSimplex_lt (H : SimpHom X A N) {m : ℕ} (hm : m + 1 ≤ N)
    (σ : singX X _⦋m + 1⦌) (f : Fin (m + 3)) (k : Fin (m + 2))
    (hfk : (f : ℕ) < (k : ℕ)) :
    (singX X).δ f (hSimplex H (m + 1) k σ)
      = hSimplex H m ⟨(k : ℕ) - 1, by omega⟩ ((singX X).δ ⟨(f : ℕ), by omega⟩ σ) := by
  apply ((TopCat.of X).toSSetObjEquivOld (Opposite.op ⦋m + 1⦌)).injective
  rw [toSSetObjEquiv_δ, toSSetObjEquiv_hSimplex, toSSetObjEquiv_hSimplex, toSSetObjEquiv_δ]
  exact prismSimplex_coface_lt H hm k f hfk _

theorem δ_hSimplex_gt (H : SimpHom X A N) {m : ℕ} (hm : m + 1 ≤ N)
    (σ : singX X _⦋m + 1⦌) (f : Fin (m + 3)) (k : Fin (m + 2))
    (hfk : (k : ℕ) + 1 < (f : ℕ)) :
    (singX X).δ f (hSimplex H (m + 1) k σ)
      = hSimplex H m ⟨(k : ℕ), by omega⟩ ((singX X).δ ⟨(f : ℕ) - 1, by omega⟩ σ) := by
  apply ((TopCat.of X).toSSetObjEquivOld (Opposite.op ⦋m + 1⦌)).injective
  rw [toSSetObjEquiv_δ, toSSetObjEquiv_hSimplex, toSSetObjEquiv_hSimplex, toSSetObjEquiv_δ]
  exact prismSimplex_coface_gt H hm k f hfk _


/-! ## The chain homotopy and the top map -/

/-- Abbreviation for the singular chain complex of `X` with `ℤ` coefficients. -/
abbrev singChainC (X : Type) [TopologicalSpace X] : ChainComplex (ModuleCat ℤ) ℕ :=
  (singX X).chainComplex (ModuleCat.of ℤ ℤ)

/-- The value of the chain homotopy on the generator of an `n`-simplex. -/
noncomputable def prismVal (H : SimpHom X A N) (n : ℕ) (σ : singX X _⦋n⦌) :
    (singChainC X).X (n + 1) :=
  ∑ k : Fin (n + 1), ((-1 : ℤ) ^ ((k : ℕ) + 1)) •
    ((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) (hSimplex H n k σ)).hom (1 : ℤ)

/-- The value of the "top" map on the generator of an `n`-simplex. -/
noncomputable def topVal (H : SimpHom X A N) (n : ℕ) (σ : singX X _⦋n⦌) :
    (singChainC X).X n :=
  ((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) (gSimplex H n σ)).hom (1 : ℤ)

/-- **The chain homotopy** attached to the family `G` of homotopies. -/
noncomputable def prismHom (H : SimpHom X A N) (n : ℕ) :
    (singChainC X).X n ⟶ (singChainC X).X (n + 1) :=
  Cofan.IsColimit.desc ((singX X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ((singChainC X).X (n + 1))
      (prismVal H n σ)))

/-- **The "top" map** attached to the family `G`. -/
noncomputable def topChainMap (H : SimpHom X A N) (n : ℕ) :
    (singChainC X).X n ⟶ (singChainC X).X n :=
  Cofan.IsColimit.desc ((singX X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ((singChainC X).X n)
      (topVal H n σ)))

/-- The value of the chain homotopy on the generator of a simplex. -/
lemma prismHom_gen (H : SimpHom X A N) (n : ℕ) (σ : singX X _⦋n⦌) :
    (prismHom H n).hom (((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom (1 : ℤ))
      = prismVal H n σ := by
  have hfac := Cofan.IsColimit.fac ((singX X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun τ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ((singChainC X).X (n + 1))
      (prismVal H n τ))) σ
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (singChainC X).X (n + 1)) =>
    (ModuleCat.Hom.hom g) (1 : ℤ)) hfac
  rw [show (singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ
      = ((singX X).chainComplexXCofan (ModuleCat.of ℤ ℤ) n).inj σ from rfl]
  change (ModuleCat.Hom.hom (prismHom H n)) ((ModuleCat.Hom.hom
    (((singX X).chainComplexXCofan (ModuleCat.of ℤ ℤ) n).inj σ)) (1 : ℤ)) = prismVal H n σ
  simp only [prismHom, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply_one] at h2
  exact h2

/-- The value of the top map on the generator of a simplex. -/
lemma topChainMap_gen (H : SimpHom X A N) (n : ℕ) (σ : singX X _⦋n⦌) :
    (topChainMap H n).hom (((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom (1 : ℤ))
      = topVal H n σ := by
  have hfac := Cofan.IsColimit.fac ((singX X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n)
    (fun τ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ ((singChainC X).X n)
      (topVal H n τ))) σ
  have h2 := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (singChainC X).X n) =>
    (ModuleCat.Hom.hom g) (1 : ℤ)) hfac
  rw [show (singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ
      = ((singX X).chainComplexXCofan (ModuleCat.of ℤ ℤ) n).inj σ from rfl]
  change (ModuleCat.Hom.hom (topChainMap H n)) ((ModuleCat.Hom.hom
    (((singX X).chainComplexXCofan (ModuleCat.of ℤ ℤ) n).inj σ)) (1 : ℤ)) = topVal H n σ
  simp only [topChainMap, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply_one] at h2
  exact h2

/-- The differential of the simplicial chain complex on the generator attached to a simplex. -/
lemma singChain_d_gen (n : ℕ) (a : singX X _⦋n + 1⦌) :
    ((singChainC X).d (n + 1) n).hom
        (((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) a).hom (1 : ℤ))
      = ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
          (((singX X).ιChainComplex (R := ModuleCat.of ℤ ℤ) ((singX X).δ i a)).hom (1 : ℤ)) := by
  have hh := congrArg (fun (g : ModuleCat.of ℤ ℤ ⟶ (singChainC X).X n) =>
    (ModuleCat.Hom.hom g) (1 : ℤ)) (SSet.ιChainComplex_d (singX X) (ModuleCat.of ℤ ℤ) a)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_sum, ModuleCat.hom_zsmul,
    LinearMap.sum_apply] at hh
  exact hh

/-- The differential out of degree `0` vanishes. -/
lemma singChain_d_zero_zero :
    (singChainC X).d 0 (0 - 1) = 0 :=
  (singChainC X).shape 0 0 (by simp [ComplexShape.down])

/- The two chain-level identities `∂T + T∂ = 𝟙 - τ` (in positive degrees and in degree `0`) are
proved in `Submission/Work/Serre/prismHom_chain_identity.lean` and
`Submission/Work/Serre/prismHom_chain_identity_zero.lean`; they are the algebraic heart of the
relative cone construction, and reduce (through `prismHom_gen`, `topChainMap_gen` and
`singChain_d_gen`) to the face identities `δ_hSimplex_*` together with the cancellation of the
alternating sums over the pairs (piece, face). -/

end

end Work.Serre
