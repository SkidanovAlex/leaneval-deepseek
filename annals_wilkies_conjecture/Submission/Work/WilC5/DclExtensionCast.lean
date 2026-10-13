import Mathlib
import Submission.Work.WilC5.S4StepNewSetup
import Submission.Work.WilC5.S4ExpG.Glue
import Submission.Work.WilC5.DclExtension

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-!
# Transporting `LRc`-structure data along an equality of structures

The §4 layer of area C5 is stated at the `rexp`-reduct `Work.WilC5.reductStruct` of an
`LEc`-structure, whereas the `Dcl`-API of `WilC2`/`WilC4` and the model-theoretic lemmas
`Work.WilC5.DclExtension` are stated at the `LRc`-structure synthesised by Mathlib from the
ordered-field / `rexp` / constants instances.  The two structures are equal
(`Work.WilC5.reductStruct_eq_withConstants`), and this file collects the transport lemmas that
move `Dcl`, substructures and embeddings along that equality.
-/

/-- The `funMap`s of two equal `LRc`-structures agree pointwise. -/
theorem funMap_congr_LRc {M : Type} {i j : LRc.Structure M} (h : i = j) {n : ℕ}
    (f : LRc.Functions n) (x : Fin n → M) :
    @Structure.funMap LRc M j n f x = @Structure.funMap LRc M i n f x := by
  cases h; rfl

/-- `Work.WilC2.Dcl` is unchanged by an equality of `LRc`-structures. -/
theorem Dcl_congr {M : Type} {i j : LRc.Structure M} (h : i = j) (A : Set M) :
    @Work.WilC2.Dcl M i A = @Work.WilC2.Dcl M j A := by
  cases h; rfl

/-- The same substructure, carried to an equal `LRc`-structure.  The carrier is *literally* the
same set, so the subtype `↥S` is the same type as before. -/
def SubCast {M : Type} (i j : LRc.Structure M) (h : i = j)
    (S : @LRc.Substructure M i) : @LRc.Substructure M j :=
  @Substructure.mk LRc M j (S : Set M) (fun {n} f x hx => by
    have hs : @Structure.funMap LRc M i n f x ∈ (S : Set M) :=
      @Substructure.fun_mem LRc M i S n f x hx
    rwa [funMap_congr_LRc h f x])

@[simp] theorem SubCast_coe {M : Type} (i j : LRc.Structure M) (h : i = j)
    (S : @LRc.Substructure M i) : (SubCast i j h S : Set M) = (S : Set M) := rfl

/-- The `LRc`-structure induced on a substructure is unchanged by carrying the substructure to an
equal `LRc`-structure. -/
theorem induced_SubCast {M : Type} (i j : LRc.Structure M) (h : i = j)
    (S : @LRc.Substructure M i) :
    @Substructure.inducedStructure LRc M j (SubCast i j h S)
      = @Substructure.inducedStructure LRc M i S := by
  cases h
  refine Structure.ext ?_ ?_
  · funext n f x
    exact Subtype.ext rfl
  · funext n r x
    exact isEmptyElim r

/-- An `LRc`-embedding, carried to equal `LRc`-structures.  The underlying function is unchanged
definitionally. -/
def EmbCast {A B : Type} (sA tA : LRc.Structure A) (sB tB : LRc.Structure B)
    (hA : sA = tA) (hB : sB = tB) (f : @Embedding LRc A B tA tB) :
    @Embedding LRc A B sA sB :=
  @Embedding.mk LRc A B sA sB ⟨fun a => f a, fun a b h => f.toEmbedding.inj' h⟩
    (fun {n} g x => by
      show (fun a => f a) (@Structure.funMap LRc A sA n g x)
          = @Structure.funMap LRc B sB n g ((fun a => f a) ∘ x)
      have h1 : @Structure.funMap LRc A sA n g x = @Structure.funMap LRc A tA n g x :=
        (funMap_congr_LRc hA g x).symm
      have h2 := (congrArg (fun t => f.toFun t) h1).trans
        (@Embedding.map_fun' LRc A B tA tB f n g x)
      have h3 := funMap_congr_LRc hB g (f.toFun ∘ x)
      exact h2.trans h3)
    (fun {n} r x => isEmptyElim r)

end Work.WilC5
