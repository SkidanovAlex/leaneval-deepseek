/-
  WilG0 — the explicit format bound of the Ω-formula calculus.

  `oFmt F s` is the format in which every realisation of the shape `s` with data of format `F`
  lies.  It depends only on `F` and on the shape (hence on the arity and on the depth); the
  degree is not bounded but *computed* exactly by `OShape.deg`.
-/
import Submission.Work.WilG0.Defs

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG0

open WilkiesDesign
open WilkiesDesign.CG

/-- An explicit format bound for a shape: the format of the realised set depends only on the
shape and on `F` (and on the arity, which is part of the shape). -/
def oFmt (F : ℕ) : {n : ℕ} → OShape n → ℕ
  | _, .poly n => n
  | _, .mem n m _ => max (F + n) (n + m) + 1 + m + n
  | _, .neg s => oFmt F s + 1
  | _, .and s t => max (oFmt F s) (oFmt F t) + 1
  | _, .or s t => max (oFmt F s) (oFmt F t)
  | _, .ex s => oFmt F s + 1

/-- The number of logical operations of a shape (BNZ's "depth"): the extra format charged by
the connectives and quantifiers alone, on top of the formats of the atoms. -/
def oDepth : {n : ℕ} → OShape n → ℕ
  | _, .poly _ => 0
  | _, .mem _ _ _ => 0
  | _, .neg s => oDepth s + 1
  | _, .and s t => max (oDepth s) (oDepth t) + 1
  | _, .or s t => max (oDepth s) (oDepth t)
  | _, .ex s => oDepth s + 1

end Work.WilG0
