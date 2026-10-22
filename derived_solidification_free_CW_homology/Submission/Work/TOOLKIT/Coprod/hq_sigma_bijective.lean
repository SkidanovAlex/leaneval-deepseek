import Mathlib
import Submission.Work.TOOLKIT.Basic
import Submission.Work.TOOLKIT.Instances

/-!
AREA TOOLKIT — the quotient functor `hq : Cpx ⟶ K(LightCondAb)` preserves small coproducts.

The main result of this file, `Work.TOOLKIT.Coprod.hq_sigma_bijective`, says that for every
family of complexes `K : J → Cpx` and every object `W` of the homotopy category, the canonical
map

`Hom_K(hq (∐ K), W) ⟶ ∏ j, Hom_K(hq (K j), W)`,  `φ ↦ (hq (ι j) ≫ φ) j`

is a bijection, i.e. that `hq (∐ K)` is the coproduct of the `hq (K j)`.  In other words the
localization `Cpx ⟶ K(LightCondAb)` preserves (small) coproducts.

The proof of surjectivity is formal: `hq` is full, so a family of morphisms out of the
`hq (K j)` lifts to a family of chain maps, and `Sigma.desc` assembles them.

The proof of injectivity is the content.  A morphism `φ : hq (∐ K) ⟶ W` is the class of a chain
map `f : ∐ K ⟶ W` (via `Quot.out`), and the hypothesis says that each `ι j ≫ f` is
null-homotopic.  The key point (`homotopy_sigma_desc`) is that then `f` itself is
null-homotopic: in each degree `i` the object `(∐ K).X i` is the coproduct of the
`(K j).X i` — the cocone `(eval i).mapCocone (colimit.cocone _)` is a colimit cocone because
`eval i` preserves coproducts (`isColimitOfPreserves`) — so the degree-`i` component of the
desired homotopy is obtained by `IsColimit.desc` from the components of the given homotopies
(`sigmaEvalDesc`), and the two homotopy equations are checked after precomposing with the
coproduct inclusions using `IsColimit.hom_ext` (`sigmaEval_hom_ext`).
-/

namespace Work.TOOLKIT.Coprod

open CategoryTheory Limits HomologicalComplex
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

variable {J : Type} {K : J → Cpx}

/-! ## The coproduct of complexes is computed degreewise -/

/-- In degree `i`, the coproduct of complexes `K` is computed as the coproduct of the
`(K j).X i`: this is the cocone obtained by evaluating the colimit cocone of `∐ K` at `i`.
Its point is `(∐ K).X i` and its `j`-th leg is `(Sigma.ι K j).f i`. -/
def sigmaEvalCocone (K : J → Cpx) [HasCoproduct K] (i : ℤ) :
    Cocone (Discrete.functor K ⋙ HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) i) :=
  (HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) i).mapCocone
    (colimit.cocone (Discrete.functor K))

/-- The evaluation functor preserves coproducts, so the degreewise cocone of the coproduct is
a colimit cocone. -/
abbrev isColimit_sigmaEvalCocone (K : J → Cpx) [HasCoproduct K] (i : ℤ) :
    IsColimit (sigmaEvalCocone K i) :=
  isColimitOfPreserves (HomologicalComplex.eval LightCondAb (ComplexShape.up ℤ) i)
    (colimit.isColimit (Discrete.functor K))

/-- The map out of the degree-`i` part of a coproduct of complexes induced by maps out of the
degree-`i` parts of the factors. -/
def sigmaEvalDesc (K : J → Cpx) [HasCoproduct K] (i : ℤ) {Z : LightCondAb}
    (u : ∀ j, (K j).X i ⟶ Z) : (sigmaObj K).X i ⟶ Z :=
  (isColimit_sigmaEvalCocone K i).desc (Cocone.mk Z (Discrete.natTrans fun j => u j.as))

/-- The defining property of `sigmaEvalDesc`. -/
lemma sigmaEvalDesc_ι (K : J → Cpx) [HasCoproduct K] (i : ℤ) {Z : LightCondAb}
    (u : ∀ j, (K j).X i ⟶ Z) (j : J) : (Sigma.ι K j).f i ≫ sigmaEvalDesc K i u = u j := by
  have h := (isColimit_sigmaEvalCocone K i).fac
    (Cocone.mk Z (Discrete.natTrans fun j => u j.as)) (Discrete.mk j)
  simpa [sigmaEvalDesc, sigmaEvalCocone] using h

/-- Two maps out of the degree-`i` part of a coproduct of complexes are equal as soon as they
are equal after precomposing with the coproduct inclusions. -/
lemma sigmaEval_hom_ext (K : J → Cpx) [HasCoproduct K] (i : ℤ) {Z : LightCondAb}
    {a b : (sigmaObj K).X i ⟶ Z}
    (h : ∀ j, (Sigma.ι K j).f i ≫ a = (Sigma.ι K j).f i ≫ b) : a = b :=
  (isColimit_sigmaEvalCocone K i).hom_ext fun j => h j.as

/-! ## Null-homotopy of a coproduct of null-homotopic maps -/

/-- If each composite `ι j ≫ f` is homotopic to `ι j ≫ g`, then `f` is homotopic to `g`.

In degree `i` the homotopy is obtained by `IsColimit.desc` from the components of the given
homotopies; the two defining equations are checked after precomposing with the coproduct
inclusions. -/
def homotopy_sigma_desc {X : Cpx} {f g : sigmaObj K ⟶ X}
    (H : ∀ j, Homotopy (Sigma.ι K j ≫ f) (Sigma.ι K j ≫ g)) : Homotopy f g := by
  let h : ∀ i j, (sigmaObj K).X i ⟶ X.X j := fun i j => sigmaEvalDesc K i fun k => (H k).hom i j
  have hι : ∀ (i j : ℤ) (k : J), (Sigma.ι K k).f i ≫ h i j = (H k).hom i j :=
    fun i j k => sigmaEvalDesc_ι K i (fun k => (H k).hom i j) k
  refine { hom := h, zero := ?_, comm := ?_ }
  · intro i j hij
    apply sigmaEval_hom_ext K i
    intro k
    rw [hι i j k, (H k).zero i j hij, comp_zero]
  · intro i
    apply sigmaEval_hom_ext K i
    intro k
    have hcomm := (H k).comm i
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f] at hcomm
    have hd : (Sigma.ι K k).f i ≫ dNext i h = dNext i (H k).hom := by
      rw [show dNext i h = (sigmaObj K).d i ((ComplexShape.up ℤ).next i) ≫
            h ((ComplexShape.up ℤ).next i) i from rfl,
        show dNext i (H k).hom = (K k).d i ((ComplexShape.up ℤ).next i) ≫
            (H k).hom ((ComplexShape.up ℤ).next i) i from rfl]
      rw [← Category.assoc,
        HomologicalComplex.Hom.comm (Sigma.ι K k) i ((ComplexShape.up ℤ).next i),
        Category.assoc, hι]
    have hp : (Sigma.ι K k).f i ≫ prevD i h = prevD i (H k).hom := by
      rw [show prevD i h = h i ((ComplexShape.up ℤ).prev i) ≫
            X.d ((ComplexShape.up ℤ).prev i) i from rfl,
        show prevD i (H k).hom = (H k).hom i ((ComplexShape.up ℤ).prev i) ≫
            X.d ((ComplexShape.up ℤ).prev i) i from rfl]
      rw [← Category.assoc, hι]
    rw [Preadditive.comp_add, Preadditive.comp_add, hd, hp,
      ← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f]
    exact hcomm

/-! ## The main result -/

/-- The quotient functor `hq : Cpx ⟶ K(LightCondAb)` preserves small coproducts: the canonical
map `Hom_K(hq (∐ K), W) → ∏ j, Hom_K(hq (K j), W)`, `φ ↦ (hq (ι j) ≫ φ) j`, is a bijection for
every `W` in the homotopy category.  Surjectivity: `hq` is full, then use `Sigma.desc`.
Injectivity: for `f : ∐ K ⟶ W` with each `ι j ≫ f` null-homotopic, build a homotopy of `f` with
zero degreewise: in degree `p`, `(∐ K).X p` is the coproduct of the `(K j).X p`
(`isColimitOfPreserves (eval _ _ p)`), and the components `h j` give the homotopy by
`IsColimit.desc`; check `zero` and `comm` after precomposing with `(ι j).f p` using
`IsColimit.hom_ext`. -/
theorem hq_sigma_bijective (J : Type) (K : J → Work.TOOLKIT.Cpx)
    [CategoryTheory.Limits.HasCoproduct K] (W : Work.TOOLKIT.KCat) :
    Function.Bijective (fun (φ : (HomotopyCategory.quotient LightCondAb
        (ComplexShape.up ℤ)).obj (CategoryTheory.Limits.sigmaObj K) ⟶ W) (j : J) =>
      CategoryTheory.CategoryStruct.comp ((HomotopyCategory.quotient LightCondAb
        (ComplexShape.up ℤ)).map (CategoryTheory.Limits.Sigma.ι K j)) φ) := by
  constructor
  · -- injectivity
    intro φ ψ hl
    have hfg : ∀ j, Homotopy (Sigma.ι K j ≫ Quot.out φ) (Sigma.ι K j ≫ Quot.out ψ) := by
      intro j
      apply HomotopyCategory.homotopyOfEq
      rw [Functor.map_comp, Functor.map_comp, HomotopyCategory.quotient_map_out φ,
        HomotopyCategory.quotient_map_out ψ]
      exact congrFun hl j
    have hf : (HomotopyCategory.quotient LightCondAb (ComplexShape.up ℤ)).map (Quot.out φ) =
        (HomotopyCategory.quotient LightCondAb (ComplexShape.up ℤ)).map (Quot.out ψ) :=
      HomotopyCategory.eq_of_homotopy _ _ (homotopy_sigma_desc hfg)
    exact (HomotopyCategory.quotient_map_out φ).symm.trans
      (hf.trans (HomotopyCategory.quotient_map_out ψ))
  · -- surjectivity
    intro ψ
    refine ⟨(HomotopyCategory.quotient LightCondAb (ComplexShape.up ℤ)).map
      (Sigma.desc fun j => (ψ j).out), funext fun j => ?_⟩
    show (HomotopyCategory.quotient LightCondAb (ComplexShape.up ℤ)).map (Sigma.ι K j) ≫
        (HomotopyCategory.quotient LightCondAb (ComplexShape.up ℤ)).map
          (Sigma.desc fun j => (ψ j).out) = ψ j
    rw [← Functor.map_comp, Sigma.ι_comp_desc]
    exact HomotopyCategory.quotient_map_out (ψ j)

end

end Work.TOOLKIT.Coprod
