import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.Glauberman
import Submission.Work.BG.GlaubermanAssembly
import Submission.Work.BG.lemma18LinearIndependent
import Submission.Work.BG.CharBridge
import Submission.Work.BG.glaubMultCongruence

/-!
# Area BG: Bender–Glauberman 1981, Lemma 1.9, value form (`Work.BG.glaubValue`)

The target `Work.GW2.C16.GlaubValueProp` is X4 of the design file
`Submission/Work/BG/ThmABCCharDefs.lean`: for a 2-group `S` acting by automorphisms `φ` on a
group `U` of odd order and an `S`-invariant irreducible character `α` of `U`, there is an
irreducible character `β` of `C_U(S) = fixedSubgroupS φ` with

  `α b ≡ β b  (mod 2)`  for every `b ∈ C_U(S)`,

in the sense of `Work.BG.AlgIntModTwo` (Bender–Glauberman 1981, p. 202, "`α ≡ α*` on `B`").

The two halves of the proof live in the shared library:

* **existence of `β`** — Bender–Glauberman 1981, Lemma 1.9: the unique irreducible
  constituent of `α|_{C_U(S)}` of odd multiplicity.  This is
  `Work.BG.glauberman_general_assembled` (`Submission/Work/BG/GlaubermanAssembly.lean`),
  assembled from the seven induction leaves by strong induction on `|φ(S)|`;
* **the parity step** — `Work.BG.glaubMultCongruence`
  (`Submission/Work/BG/glaubMultCongruence.lean`): if `β ∈ Irr(K)` is the *unique* irreducible
  constituent of `α|_K` of odd multiplicity (`K ≤ U` arbitrary), then `α(b) ≡ β(b) (mod 2)`
  for every `b ∈ K`.  (`α|_K = Σ_θ m_θ θ` with `m_θ ∈ ℕ` by Clifford's theorem, so all the
  coefficients of `α|_K − β ∈ ℤ[Irr K]` are even; values of virtual characters are algebraic
  integers.)

This file is the one-line assembly: instantiate the parity step with the Glauberman
correspondent of `α` on `K = C_U(S)`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem glaubValue : Work.GW2.C16.GlaubValueProp := by
  intro S U instS instU finS finU finU' invU hS hU φ finC invC α hα hinv
  -- Bender–Glauberman 1981, Lemma 1.9: the unique odd-multiplicity constituent `β`
  obtain ⟨β, hβodd, huniq⟩ := glauberman_general_assembled hS hU φ ⟨α, hα⟩ hinv
  -- `β` is the unique `θ ∈ Irr(C_U(S))` with `⟨α|_{C_U(S)}, θ⟩` odd
  refine ⟨(β : ClassFunction ↥(fixedSubgroupS φ) ℂ), β.isIrreducible, ?_⟩
  -- its values agree with those of `α` on `C_U(S)`, modulo `2`
  exact glaubMultCongruence (fixedSubgroupS φ) α hα β
    (fun θ => ⟨fun h => huniq θ h, fun h => h ▸ hβodd⟩)

end Work.BG
