import Mathlib
import Submission.Work.Projective.cpn_homology
import Submission.Work.Kunneth.Basic
import Submission.Work.Cohomology.singularChains_free

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The Künneth hypotheses for `ℂPⁿ` with `ℤ` coefficients

The Künneth chapter (`Submission/Work/Kunneth/README.md`, §3) proves the cohomological Künneth
isomorphism under three hypotheses on the second factor `Y`:

```
(hYt : ∀ q, Module.Projective ℤ ↥((sChain Y).X q))
(hYf : ∀ q, Module.Free ℤ ↥((sChain Y).homology q))
(hYn : ∀ q, Module.Finite ℤ ↥((sChain Y).homology q))
```

— projectivity of the chain modules, and freeness together with finiteness of the homology in each
degree.  This file discharges them for `Y = ℂPⁿ`, the case needed for the Leray–Hirsch base case
and for the `ℂP² × ℂP²` application.

* the chain modules of `ℂPⁿ` are `ℤ`-projective because they are free:
  `C_q(X;ℤ)` is the coproduct over the `q`-simplices of copies of `ℤ`
  (`Work.Cohomology.singularChains_free`, transported along the identification
  `sChain (TopCat.toSSet.obj X) = singularChains ℤ X`);
* the homology of `ℂPⁿ` is `ℤ` in the even degrees `≤ 2n` and `0` otherwise
  (`Work.Projective.cpn_homology`), hence free of finite rank in every degree: `ℤ` and `0` are
  both free, and `ℤ` is a finitely generated `ℤ`-module while every module isomorphic to such a
  model is finite as well.

## Main result

* `Work.Kunneth.cpn_kunneth_hypotheses` — the three hypotheses for `Y = ℂPⁿ`, for every `n`.
-/

set_option linter.style.haveILetI false

namespace Work.Kunneth

noncomputable section

/-- The `q`-th chain module of `ℂPⁿ` is a free `ℤ`-module (it is the coproduct, over the singular
`q`-simplices, of copies of `ℤ`): `Work.Cohomology.singularChains_free` in the notation of the
Künneth chapter, where `sChain (TopCat.toSSet.obj X) = singularChains ℤ X` definitionally. -/
theorem cpnChains_free (n q : ℕ) :
    Module.Free ℤ ↥((sChain (TopCat.toSSet.obj (Work.Projective.CPSpace n))).X q) :=
  Work.Cohomology.singularChains_free (Work.Projective.CPSpace n) q

/-- The model `ℤ`-module of `H_q(ℂPⁿ)`: `ℤ` in the even degrees `q ≤ 2n`, `0` otherwise. -/
abbrev cpnHomModel (n q : ℕ) : Type := Fin (if Even q ∧ q ≤ 2 * n then 1 else 0) → ℤ

/-- The `q`-th homology module of `ℂPⁿ` is isomorphic to the model module `cpnHomModel n q`
(`Work.Projective.cpn_homology`). -/
noncomputable def cpnHomology_iso_model (n q : ℕ) :
    ((sChain (TopCat.toSSet.obj (Work.Projective.CPSpace n))).homology q) ≅
      ModuleCat.of ℤ (cpnHomModel n q) :=
  Classical.choice (Work.Projective.cpn_homology n q)

/-- The homology of `ℂPⁿ` is degreewise free: it is the model module `cpnHomModel n q`, which is a
finite product (possibly indexed by the empty type) of copies of `ℤ`. -/
theorem cpnHomology_free (n q : ℕ) :
    Module.Free ℤ ↥((sChain (TopCat.toSSet.obj (Work.Projective.CPSpace n))).homology q) :=
  Module.Free.of_equiv' (R := ℤ) (inferInstance : Module.Free ℤ (cpnHomModel n q))
    (cpnHomology_iso_model n q).symm.toLinearEquiv

/-- The homology of `ℂPⁿ` is degreewise finite: it is isomorphic to the model module
`cpnHomModel n q`, on which the `ℤ`-action is finitely generated. -/
theorem cpnHomology_finite (n q : ℕ) :
    Module.Finite ℤ ↥((sChain (TopCat.toSSet.obj (Work.Projective.CPSpace n))).homology q) :=
  Module.Finite.equiv (cpnHomology_iso_model n q).symm.toLinearEquiv

/-- **The Künneth hypotheses for `ℂPⁿ`.**  The chain modules of `ℂPⁿ` are projective over `ℤ`, and
its integral homology is free and finitely generated in every degree.  These are exactly the
hypotheses `hYt`, `hYf`, `hYn` of `Work.Kunneth.kunneth_cohomology` for the second factor
`ℂPⁿ`. -/
theorem cpn_kunneth_hypotheses (n q : ℕ) :
    Module.Projective ℤ ↥((Work.Kunneth.sChain (TopCat.toSSet.obj (Work.Projective.CPSpace n))).X q)
      ∧ Module.Free ℤ ↥((Work.Kunneth.sChain (TopCat.toSSet.obj (Work.Projective.CPSpace n))).homology q)
      ∧ Module.Finite ℤ ↥((Work.Kunneth.sChain (TopCat.toSSet.obj (Work.Projective.CPSpace n))).homology q) := by
  haveI : Module.Free ℤ ↥((Work.Kunneth.sChain (TopCat.toSSet.obj
    (Work.Projective.CPSpace n))).X q) := cpnChains_free n q
  exact ⟨Module.Projective.of_free, cpnHomology_free n q, cpnHomology_finite n q⟩

end

end Work.Kunneth
