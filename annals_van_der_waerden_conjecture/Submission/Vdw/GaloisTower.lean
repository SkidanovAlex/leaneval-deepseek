import Mathlib
import Submission.Vdw.GaloisRamification

open Polynomial
open scoped NumberField

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# The tower `K_p = ℚ[x]/(p) ⊂ L = p.SplittingField` as a Galois extension

Step-(c) infrastructure (`Contraction.fiberCard`): for irreducible
`p : ℚ[X]`, the splitting field `L = p.SplittingField` is a *Galois extension
of the root field* `K_p = AdjoinRoot p` (via the canonical embedding
`kpolyAlgEmb p` / `kpolyAlgebra p`).  This module assembles the instance
data that the relative prime-counting (`Ideal.primesOver`,
`ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`, the Galois tower
identities) needs at the concrete types `AdjoinRoot p`, `p.SplittingField`:

* `kpoly_tower`: `[IsScalarTower ℚ (AdjoinRoot p) (p.SplittingField)]` under
  `[Algebra (AdjoinRoot p) (p.SplittingField)] := kpolyAlgebra p`;
* `kpoly_normal`, `kpoly_isGalois`: `IsGalois (AdjoinRoot p) (p.SplittingField)`
  (normal by `Normal.tower_top_of_normal` applied to `Normal ℚ L`, separable
  in characteristic zero);
* `intRingMap_eq_algebraMap`: with these instances, the ring-of-integers
  algebra map `𝓞 K_p →+* 𝓞 L` is `intRingMap p (kpolyAlgEmb p)` — so the
  `pullbackIdeal` contraction machinery of `Contraction.lean` coincides with
  the `Ideal.under`-relation used by Mathlib's prime-tower theory.

The instance declarations are only ever introduced with `letI`/`haveI` inside
statements (the concrete types are noncomputable `def`s that typeclass search
cannot unfold); each theorem below is written in the
"`letI : Algebra … := kpolyAlgebra p` in the statement" idiom so that its
statement elaborates, and the body re-declares the instances locally.
-/

namespace Submission.Vdw

noncomputable section

open Polynomial

private lemma lift_comp_of_emb (p : ℚ[X]) [Fact (Irreducible p)] :
    (kpolyEmb p).comp (AdjoinRoot.of p) = algebraMap ℚ p.SplittingField := by
  unfold kpolyEmb
  exact AdjoinRoot.lift_comp_of (f := p) (i := algebraMap ℚ p.SplittingField)
    (a := splRootVal p) (by simpa [Polynomial.aeval_def] using splRoot_aeval p)

/-- With `[Algebra (AdjoinRoot p) (p.SplittingField)] := kpolyAlgebra p`,
the scalar-tower `ℚ ⊂ AdjoinRoot p ⊂ p.SplittingField` holds. -/
theorem kpoly_tower (p : ℚ[X]) [Fact (Irreducible p)] :
    letI : Algebra (AdjoinRoot p) p.SplittingField := kpolyAlgebra p
    IsScalarTower ℚ (AdjoinRoot p) p.SplittingField := by
  letI : Algebra (AdjoinRoot p) p.SplittingField := kpolyAlgebra p
  apply IsScalarTower.of_algebraMap_eq
  intro x
  change (algebraMap ℚ p.SplittingField x) = kpolyEmb p (AdjoinRoot.of p x)
  rw [← RingHom.comp_apply (kpolyEmb p) (AdjoinRoot.of p)]
  rw [lift_comp_of_emb p]

/-- The splitting field is normal over the root field (normality descends to
intermediate base fields: `Normal.tower_top_of_normal`). -/
theorem kpoly_normal (p : ℚ[X]) [Fact (Irreducible p)] :
    letI : Algebra (AdjoinRoot p) p.SplittingField := kpolyAlgebra p
    Normal (AdjoinRoot p) p.SplittingField := by
  letI : Algebra (AdjoinRoot p) p.SplittingField := kpolyAlgebra p
  haveI tower : IsScalarTower ℚ (AdjoinRoot p) p.SplittingField := kpoly_tower p
  haveI : Normal ℚ p.SplittingField := Polynomial.SplittingField.instNormal p
  exact Normal.tower_top_of_normal ℚ (AdjoinRoot p) p.SplittingField

/-- **`L/K_p` is Galois** for `L = p.SplittingField`,
`K_p = AdjoinRoot p` (normal above; separable in characteristic zero). -/
theorem kpoly_isGalois (p : ℚ[X]) [Fact (Irreducible p)] :
    letI : Algebra (AdjoinRoot p) p.SplittingField := kpolyAlgebra p
    IsGalois (AdjoinRoot p) p.SplittingField := by
  letI : Algebra (AdjoinRoot p) p.SplittingField := kpolyAlgebra p
  refine { to_isSeparable := ?_ , to_normal := ?_ }
  · infer_instance
  · exact kpoly_normal p
