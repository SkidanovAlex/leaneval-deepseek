/-
  WilC5 — supporting material for `Work.WilC5.StepSeqYVLe`.

  The target lemma compares the archimedean order `VLe` of `x = S.xs i` with the elements of `B`
  to that of `y = ys B τ S y0 i` with the images `τ b`.  The only thing used about the cut
  realisation `hcutB` is that it transfers the *order* comparisons with the `B`-elements
  `(n:K) * b` and `-((n:K) * b)`; the elements `±(n·b)` are produced here as the values of *terms*
  of the language `LRc` applied inside the substructure `B`, so that the `LRc`-embedding `τ`
  commutes with their construction automatically (`Embedding.map_fun`).

  This file contains:

  * `Work.WilC5.lrcFunMap_add/mul/neg/zero/one` — the alignment of the `LRc`-function symbols
    `+, *, -, 0, 1` with the field operations of a `Field` carrying a `CompatibleRing` structure
    (the ring symbols of `LRc` are `Sum.inl (Sum.inl ·)` under the two `Language.sum`s);
  * `Work.WilC5.VLeAux` — the reformulation of `VLe d z` ("`z` is bounded by a natural multiple of
    `d`") that never forms `|d|`: `z` is squeezed between `±n·d` for some `n`;
  * the elements `Bzero, Bone, Badd, Bmul, Bneg` and their natural multiples `Bnat`, `Bscale` of a
    substructure `B`, built from the `LRc`-terms.
-/
import Mathlib
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.ValueOrder

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

/-! ## 1. The `LRc`-symbols against the field operations -/

section Alignment

variable {M : Type} [Field M] [FirstOrder.Ring.CompatibleRing M]
  [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M]

theorem lrcFunMap_add (x y : M) :
    (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M inferInstance 2
      (Sum.inl (Sum.inl Ring.addFunc)) ![x,y]) = x + y := by
  trans (@FirstOrder.Language.Structure.funMap
      (FirstOrder.Language.ring.sum WilkiesDesign.CG.rexpL) M inferInstance 2
      (Sum.inl Ring.addFunc) ![x,y])
  · exact congrFun (FirstOrder.Language.funMap_sumInl
      (L₁ := FirstOrder.Language.ring.sum WilkiesDesign.CG.rexpL)
      (L₂ := FirstOrder.Language.constantsOn ℝ) (Sum.inl Ring.addFunc)) ![x,y]
  · trans (@FirstOrder.Language.Structure.funMap FirstOrder.Language.ring M inferInstance 2
        (Ring.addFunc) ![x,y])
    · exact congrFun (FirstOrder.Language.funMap_sumInl (L₁ := FirstOrder.Language.ring)
        (L₂ := WilkiesDesign.CG.rexpL) (Ring.addFunc)) ![x,y]
    · exact Ring.CompatibleRing.funMap_add ![x,y]

theorem lrcFunMap_mul (x y : M) :
    (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M inferInstance 2
      (Sum.inl (Sum.inl Ring.mulFunc)) ![x,y]) = x * y := by
  trans (@FirstOrder.Language.Structure.funMap
      (FirstOrder.Language.ring.sum WilkiesDesign.CG.rexpL) M inferInstance 2
      (Sum.inl Ring.mulFunc) ![x,y])
  · exact congrFun (FirstOrder.Language.funMap_sumInl
      (L₁ := FirstOrder.Language.ring.sum WilkiesDesign.CG.rexpL)
      (L₂ := FirstOrder.Language.constantsOn ℝ) (Sum.inl Ring.mulFunc)) ![x,y]
  · trans (@FirstOrder.Language.Structure.funMap FirstOrder.Language.ring M inferInstance 2
        (Ring.mulFunc) ![x,y])
    · exact congrFun (FirstOrder.Language.funMap_sumInl (L₁ := FirstOrder.Language.ring)
        (L₂ := WilkiesDesign.CG.rexpL) (Ring.mulFunc)) ![x,y]
    · exact Ring.CompatibleRing.funMap_mul ![x,y]

theorem lrcFunMap_neg (x : M) :
    (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M inferInstance 1
      (Sum.inl (Sum.inl Ring.negFunc)) ![x]) = -x := by
  trans (@FirstOrder.Language.Structure.funMap
      (FirstOrder.Language.ring.sum WilkiesDesign.CG.rexpL) M inferInstance 1
      (Sum.inl Ring.negFunc) ![x])
  · exact congrFun (FirstOrder.Language.funMap_sumInl
      (L₁ := FirstOrder.Language.ring.sum WilkiesDesign.CG.rexpL)
      (L₂ := FirstOrder.Language.constantsOn ℝ) (Sum.inl Ring.negFunc)) ![x]
  · trans (@FirstOrder.Language.Structure.funMap FirstOrder.Language.ring M inferInstance 1
        (Ring.negFunc) ![x])
    · exact congrFun (FirstOrder.Language.funMap_sumInl (L₁ := FirstOrder.Language.ring)
        (L₂ := WilkiesDesign.CG.rexpL) (Ring.negFunc)) ![x]
    · exact Ring.CompatibleRing.funMap_neg ![x]

theorem lrcFunMap_zero :
    (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M inferInstance 0
      (Sum.inl (Sum.inl Ring.zeroFunc)) default) = (0 : M) := by
  trans (@FirstOrder.Language.Structure.funMap
      (FirstOrder.Language.ring.sum WilkiesDesign.CG.rexpL) M inferInstance 0
      (Sum.inl Ring.zeroFunc) default)
  · exact congrFun (FirstOrder.Language.funMap_sumInl
      (L₁ := FirstOrder.Language.ring.sum WilkiesDesign.CG.rexpL)
      (L₂ := FirstOrder.Language.constantsOn ℝ) (Sum.inl Ring.zeroFunc)) default
  · trans (@FirstOrder.Language.Structure.funMap FirstOrder.Language.ring M inferInstance 0
        (Ring.zeroFunc) default)
    · exact congrFun (FirstOrder.Language.funMap_sumInl (L₁ := FirstOrder.Language.ring)
        (L₂ := WilkiesDesign.CG.rexpL) (Ring.zeroFunc)) default
    · exact Ring.CompatibleRing.funMap_zero default

theorem lrcFunMap_one :
    (@FirstOrder.Language.Structure.funMap WilkiesDesign.CG.LRc M inferInstance 0
      (Sum.inl (Sum.inl Ring.oneFunc)) default) = (1 : M) := by
  trans (@FirstOrder.Language.Structure.funMap
      (FirstOrder.Language.ring.sum WilkiesDesign.CG.rexpL) M inferInstance 0
      (Sum.inl Ring.oneFunc) default)
  · exact congrFun (FirstOrder.Language.funMap_sumInl
      (L₁ := FirstOrder.Language.ring.sum WilkiesDesign.CG.rexpL)
      (L₂ := FirstOrder.Language.constantsOn ℝ) (Sum.inl Ring.oneFunc)) default
  · trans (@FirstOrder.Language.Structure.funMap FirstOrder.Language.ring M inferInstance 0
        (Ring.oneFunc) default)
    · exact congrFun (FirstOrder.Language.funMap_sumInl (L₁ := FirstOrder.Language.ring)
        (L₂ := WilkiesDesign.CG.rexpL) (Ring.oneFunc)) default
    · exact Ring.CompatibleRing.funMap_one default

end Alignment

/-! ## 2. `VLe` in a form that only compares with the `B`-elements `±n·d` -/

/-- **`VLe d z` without absolute values.**  In an ordered field, `z` is bounded by a natural multiple
of `d` iff for some `n` it is squeezed between `n·d` and `-n·d` (which are the two elements whose
maximum is `n·|d|`): the comparison with `|d|` is replaced by a disjunction over the two signs of
`d`. -/
def VLeAux {F : Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F] (d z : F) : Prop :=
  ∃ n : ℕ, (z ≤ (n : F) * d ∨ z ≤ -((n : F) * d)) ∧
    (((n : F) * d ≤ z) ∨ -((n : F) * d) ≤ z)

/-! ## 3. The elements of a substructure `B` built from the `LRc`-terms -/

section BVec

variable {K : Type} [WilkiesDesign.CG.LRc.Structure K]

/-- The zero of the substructure `B`, as the value of the constant symbol `0`. -/
def Bzero (B : WilkiesDesign.CG.LRc.Substructure K) : ↥B :=
  @Structure.funMap WilkiesDesign.CG.LRc ↥B
    (FirstOrder.Language.Substructure.inducedStructure (S := B)) 0
    (Sum.inl (Sum.inl Ring.zeroFunc)) default

/-- The one of the substructure `B`, as the value of the constant symbol `1`. -/
def Bone (B : WilkiesDesign.CG.LRc.Substructure K) : ↥B :=
  @Structure.funMap WilkiesDesign.CG.LRc ↥B
    (FirstOrder.Language.Substructure.inducedStructure (S := B)) 0
    (Sum.inl (Sum.inl Ring.oneFunc)) default

/-- The sum of two elements of `B`, as the value of the symbol `+`. -/
def Badd (B : WilkiesDesign.CG.LRc.Substructure K) (c d : ↥B) : ↥B :=
  @Structure.funMap WilkiesDesign.CG.LRc ↥B
    (FirstOrder.Language.Substructure.inducedStructure (S := B)) 2
    (Sum.inl (Sum.inl Ring.addFunc)) ![c, d]

/-- The product of two elements of `B`, as the value of the symbol `*`. -/
def Bmul (B : WilkiesDesign.CG.LRc.Substructure K) (c d : ↥B) : ↥B :=
  @Structure.funMap WilkiesDesign.CG.LRc ↥B
    (FirstOrder.Language.Substructure.inducedStructure (S := B)) 2
    (Sum.inl (Sum.inl Ring.mulFunc)) ![c, d]

/-- The negation of an element of `B`, as the value of the symbol `-`. -/
def Bneg (B : WilkiesDesign.CG.LRc.Substructure K) (c : ↥B) : ↥B :=
  @Structure.funMap WilkiesDesign.CG.LRc ↥B
    (FirstOrder.Language.Substructure.inducedStructure (S := B)) 1
    (Sum.inl (Sum.inl Ring.negFunc)) ![c]

/-- The natural multiples of `1` inside `B`, i.e. the numerals `n`. -/
def Bnat (B : WilkiesDesign.CG.LRc.Substructure K) : ℕ → ↥B
  | 0 => Bzero B
  | (n + 1) => Badd B (Bnat B n) (Bone B)

/-- The natural multiple `n·b` inside `B`. -/
def Bscale (B : WilkiesDesign.CG.LRc.Substructure K) (n : ℕ) (b : ↥B) : ↥B :=
  Bmul B (Bnat B n) b

end BVec

end Work.WilC5
