/-
  WilE5 / Strat — `flatSemiPf` described by conditions (portable-path copy).

  WHY THIS FILE EXISTS
  --------------------
  The lemma was requested for the path `Submission/Work/WilE5/Strat/aux/flatSemiPf_set_eq.lean`,
  whose module name `Submission.Work.WilE5.Strat.aux.flatSemiPf_set_eq` cannot be built with the
  pinned toolchain (Lean 4.35.0-rc3): `Lean.Elab.checkModuleNamePortability` reports
      module name '...aux.flatSemiPf_set_eq' is not portable:
      'aux' is a reserved file name on some operating systems
  as an *error* while processing the file header, before any command is elaborated, so
  `lake build Submission.Work.WilE5.Strat.aux.flatSemiPf_set_eq` can never succeed.

  The mathematics is unaffected: the very same proof (byte-identical, modulo this comment) is in
  `Submission/Work/WilE5/Strat/aux/flatSemiPf_set_eq.lean`. This module is the *portable* location
  of that proof; it declares the identical, fully qualified name

      Work.WilE5.Strat.aux.flatSemiPf_set_eq

  so consumers may simply `import Submission.Work.WilE5.Strat.auxiliary.flatSemiPf_set_eq` and use
  `Work.WilE5.Strat.aux.flatSemiPf_set_eq` as requested.
-/
import Mathlib
import Submission.Work.WilE5.Sys
import Submission.Work.Wilkies.E.Spec

namespace Work.WilE5.Strat.aux

theorem flatSemiPf_set_eq {p q : ℕ} (X : WilkiesDesign.E.SemiPf (p + q)) (M NΦ : ℕ)
    (σ : Work.WilE5.St p q X.r) :
    (Work.WilE5.flatSemiPf X M NΦ σ).set =
      X.set ∩ {x | WilkiesDesign.E.Basic.holds X.c (Work.WilE5.stCond σ) x ∧
        ∀ f ∈ Work.WilE5.flatEqs X.c M NΦ σ, WilkiesDesign.E.eaEval X.c f x = 0} := by
  have hdef : Work.WilE5.flatSemiPf X M NΦ σ =
      Work.WilE5.semiPfAnd (Work.WilE5.semiPfAnd X (Work.WilE5.stCond σ))
        (Work.WilE5.Basic.eqsOf (Work.WilE5.flatEqs X.c M NΦ σ)) := rfl
  rw [hdef, Work.WilE5.semiPfAnd_set, Work.WilE5.semiPfAnd_set]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Work.WilE5.Basic.holds_eqsOf]
  constructor
  · rintro ⟨⟨hx, hB⟩, hC⟩
    exact ⟨hx, hB, hC⟩
  · rintro ⟨hx, hB, hC⟩
    exact ⟨⟨hx, hB⟩, hC⟩

end Work.WilE5.Strat.aux
