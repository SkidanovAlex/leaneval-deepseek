import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.LEBridge
import Submission.Work.TMComp.LEHerman
import Submission.Work.TMComp.LEFurman
import Submission.Work.TMComp.LEAlg
import Submission.Work.TMLECore.jensen_poly
import Submission.Work.TMLECore.intervalIntegrable_log_poly_circle
import Submission.Work.TMLECore.iterPoly_const_term
import Submission.Work.TMLECore.abs_iterC_eq_iterPoly
import Submission.Work.TMLECore.weyl_uniform
import Submission.Work.TMLECore.log_frob_iterC_energy_cont
import Submission.Work.TMLECore.log_frob_iterC_low_scale_bound

/-!
# `prove_LEBasics` — component C4 of the Ten Martini formalisation

`Work.TMContract.P_LEBasics` is the conjunction of

* **(1) Herman's bound** `log |λ| ≤ L(E)` for every `α`, `λ` and complex `E`
  (AJ §9, [H]), assembled in `Submission/Work/TMComp/LEHerman.lean` from
  `TMLECore/jensen_poly`, `TMLECore/intervalIntegrable_log_poly_circle`,
  `TMLECore/iterPoly_const_term` and `TMLECore/abs_iterC_eq_iterPoly`;
* **(2) the locally uniform upper bound** (AJ §9, [Fur]): for irrational `α`, `E₀ ∈ ℂ`,
  `ε > 0` there are `r > 0`, `n₀` with `log ‖A_n(x;E)‖_F ≤ n (L(E₀) + ε)` for all
  `n ≥ n₀`, `‖E - E₀‖ < r` and all `x`, assembled in
  `Submission/Work/TMComp/LEFurman.lean` from `TMLECore/weyl_uniform` (Weyl
  equidistribution of the irrational rotation, i.e. `P_UniqErg`),
  `TMLECore/log_frob_iterC_energy_cont`, `TMLECore/log_frob_iterC_low_scale_bound` and
  `TMComp/LEAlg` (`iterC_subadditive_decomp'`: writing `n = (n/k)k + n % k` and applying the
  cocycle identity plus submultiplicativity of `frob`).

The two assemblies are stated for the verbatim copy of the transfer cocycle kept by
`Work.TMC7Core`; `LEBridge` shows that its `tmC`, `iterC`, `frob` and `lyap` are the ones
of `Work.TMContract` (the two copies have identical bodies), which is the only place where
the two vocabularies meet.
-/

noncomputable section

namespace Work.TMComp

theorem prove_LEBasics : Work.TMContract.P_LEBasics := by
  refine ⟨?_, ?_⟩
  · -- (1) Herman's bound
    intro α lam E
    rw [← lyap_bridge]
    exact herman_of_pieces Work.TMLECore.jensen_poly
      Work.TMLECore.intervalIntegrable_log_poly_circle Work.TMLECore.iterPoly_const_term
      Work.TMLECore.abs_iterC_eq_iterPoly α lam E
  · -- (2) the locally uniform upper bound
    intro α lam hα E₀ ε hε
    obtain ⟨r, hr, n₀, hn⟩ := furman_of_pieces Work.TMLECore.weyl_uniform
      Work.TMLECore.log_frob_iterC_energy_cont Work.TMLECore.log_frob_iterC_low_scale_bound
      iterC_subadditive_decomp' α lam hα E₀ ε hε
    refine ⟨r, hr, n₀, fun n hn' E hE x => ?_⟩
    rw [← frob_bridge, ← iterC_bridge, ← lyap_bridge]
    exact hn n hn' E hE x

end Work.TMComp
