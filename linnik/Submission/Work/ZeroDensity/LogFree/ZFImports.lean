import Mathlib
import Submission.Work.ZeroDensity.LogFree.Defs
import Submission.Work.LinnikContract.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_offAxis_uniform
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_zeroFree_uniform_realAxis
import Submission.Commons.NumberTheory.Linnik.completedL_zero_strip
import Submission.Work.A7.exists_isMin1

/-!
# `Work.ZeroDensity.LogFree.ZFImports` — the zero-free / strip inputs of L6

A thin import bundle: the uniform zero-free regions off the real axis and on the real axis of
Dirichlet `L`-functions, the critical-strip location of the zeros of the completed `L`-function,
and the bridge "zero in the working region `IsZ` ⟹ zero of `L(·, χ*)` in the strip"
(`Work.A7.isZ_LFunction_zero`).  Collected here so that the lemmas of `LogFree/boxUpgradeOfParams`
can list a single workspace module in their dependencies.
-/
