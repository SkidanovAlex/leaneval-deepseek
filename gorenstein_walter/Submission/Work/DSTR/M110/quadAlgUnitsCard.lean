import Mathlib
import Submission.Work.DSTR.M110.nonsplitAux

namespace Work.DSTR.M110

-- `letI`/`haveI` are the idiomatic way to bring typeclass instances into scope.
set_option linter.style.haveILetI false in

/-- The unit group of `AdjoinRoot f`, for `f` a monic irreducible polynomial over a finite
field `F`, has cardinality `|F| ^ f.natDegree - 1`: `AdjoinRoot f` is the finite field
extension of `F` of degree `f.natDegree`, and a finite field has one fewer unit than element. -/
theorem quadAlgUnitsCard (F : Type*) [Field F] [Fintype F] (f : Polynomial F) (hf : f.Monic)
    (hirr : Irreducible f) : Nat.card (AdjoinRoot f)ˣ = Nat.card F ^ f.natDegree - 1 := by
  -- `AdjoinRoot f` is a field since `f` is irreducible.
  letI : Fact (Irreducible f) := ⟨hirr⟩
  -- The power basis `1, root f, ..., root f ^ (f.natDegree - 1)` exhibits `AdjoinRoot f` as a
  -- finite-dimensional `F`-vector space of dimension `f.natDegree`.
  haveI : Module.Finite F (AdjoinRoot f) := (AdjoinRoot.powerBasis hf.ne_zero).finite
  have hcard : Nat.card (AdjoinRoot f) = Nat.card F ^ f.natDegree := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := AdjoinRoot f),
      (AdjoinRoot.powerBasis hf.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  -- A finite field has exactly one fewer unit than element.
  rw [Nat.card_units, hcard]

end Work.DSTR.M110
