import Mathlib
import Submission.Work.WingbergRoute.TotallyReal
import Submission.Work.WingbergRoute.gsM_quotient_of_maximal_continuous
import Submission.Work.WingbergRoute.gsM_aut_gsF_equiv_pi
import Submission.Work.WingbergRoute.six_le_card_of_surjective_elementaryAbelian

/-!
# `Work.WingbergRoute.Certificate` -- the genus certificate at the totally real base `gsF`

This module records the provenance of the **generator-rank clause** `6 ≤ #α` of
`Work.WingbergRoute.gsFArithmeticInput`: the multiquadratic extension

```
gsM = ℚ(√5, √13, √17, √29, √37, √41, √53)  ⊇  gsF = ℚ(√2576450045)
```

of `Submission/Work/QuadraticFields/` is unramified over `gsF` of degree `2^6 = 64`
(`Work.QuadraticFields.gs_certificate`), and its Galois group over `gsF` is elementary abelian of
rank `6` (`Work.WingbergRoute.gsM_aut_gsF_equiv_pi`, from
`Work.WingbergRoute.gsM_aut_exp_two` and the multiquadratic structure).  Hence every maximal
unramified pro-`2` extension `M` of `gsF` surjects onto `(ℤ/2)^6`, i.e. `gsF` has six independent
unramified quadratic extensions — the `d(G_∅) ≥ 6` input of the Golod--Shafarevich criterion.

Everything here is proved (no named input); the only conditional statement is
`gsF_generatorRank_ge_six`, which needs the *finiteness* of the generator rank of `G_∅` — the
Artin statement `d(G_∅) = rank₂ Cl(gsF)` — as a hypothesis, exactly as the workspace's other
generator-rank statements do.

## Main declarations

* `Work.WingbergRoute.gsF_quotient_six` : the continuous surjection `G_∅ ↠ (ℤ/2)^6`;
* `Work.WingbergRoute.six_le_card_of_presentation` : any presentation datum surjecting onto
  `(ℤ/2)^6` has at least six generators;
* `Work.WingbergRoute.gsF_generatorRank_ge_six` : `6 ≤ GeneratorRank (G_∅)` (given finite
  generation).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped Classical
open scoped NumberField
open NumberField

noncomputable section

namespace Work.WingbergRoute

/-- **The genus certificate for `gsF`.**  For every maximal unramified pro-`2` extension `M` of
`gsF`, the restriction to the unramified degree-`64` multiquadratic subextension `gsM` gives a
*continuous* surjection `Gal(M.K/gsF) ↠ (ℤ/2)^6`. -/
theorem gsF_quotient_six
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} gsF 2) :
    ∃ φ : Work.ClassFieldTower.galoisGroup M →* (Fin 6 → Multiplicative (ZMod 2)),
      Function.Surjective φ ∧ Continuous φ :=
  gsM_quotient_of_maximal_continuous M

/-- **Any presentation surjecting onto `(ℤ/2)^6` needs at least six generators.**  This is the
group-theoretic content of the genus certificate: it is what turns the existence of six
independent unramified quadratic extensions into the numerical clause `6 ≤ #α` of
`Work.WingbergRoute.gsFArithmeticInput`. -/
theorem six_le_card_of_presentation (α : Type) [Fintype α] (rel : Finset (FreeGroup α))
    (φ : (FreeGroup α ⧸ Subgroup.normalClosure (rel : Set (FreeGroup α))) →*
      (Fin 6 → Multiplicative (ZMod 2)))
    (hφ : Function.Surjective φ) : 6 ≤ Fintype.card α :=
  Work.WingbergRoute.six_le_card_of_surjective_elementaryAbelian α rel φ hφ

/-- **`d(G_∅) ≥ 6` for `gsF`.**  The generator rank of the maximal unramified pro-`2` group of
`gsF` is at least `6`; the hypothesis `hex` is the finite generation of that group (the Artin
statement `d(G_∅) = rank₂ Cl(gsF)`, which is not available in this workspace for `gsF`). -/
theorem gsF_generatorRank_ge_six
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} gsF 2)
    (hex : ∃ m : ℕ, Work.RelatorRank.HasDenseGeneratingFamily
      (Work.ClassFieldTower.galoisGroup M) m) :
    6 ≤ Work.RelatorRank.GeneratorRank (Work.ClassFieldTower.galoisGroup M) := by
  obtain ⟨φ, hφ, hcont⟩ := gsM_quotient_of_maximal_continuous M
  exact Work.RelatorRank.generatorRank_ge_of_surjective_elementaryAbelian φ hcont hφ hex

end Work.WingbergRoute
