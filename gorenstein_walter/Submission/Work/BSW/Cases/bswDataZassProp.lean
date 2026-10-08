/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area BSW)

# Area BSW: the Zassenhaus conversion (Bender §3.8 + the Zassenhaus remark)

`Work.BSW.BSWDataZassProp`: Bender's conclusion (1)–(4) (`Work.BSW.IsBSWData G q`, the strengthened
form of `Submission/Work/BSW/Concl.lean`) gives a Zassenhaus action of `G` of degree `q + 1`.
The configuration and its API are in `Submission/Work/BSW/Cases/DataZass/Setup.lean`.

The single remaining content is `zass_fix` (no nonidentity element fixes three points), proved in
`Submission/Work/BSW/Cases/DataZass/zass_fix.lean`; the other four clauses are `zass_faithful`,
`zass_card`, `zass_pretransitive`, `zass_twoPoint`.
-/
import Submission.Work.BSW.Cases.DataZass.Setup
import Submission.Work.BSW.Cases.DataZass.zass_fix

namespace Work.BSW.Cases

open Subgroup Work.GW2

variable {G : Type} [Group G] [Finite G]

/-- Bender's conclusion (1)–(4) (`Work.BSW.IsBSWData G q`) gives the Zassenhaus hypotheses on the
coset space `G ⧸ N_G(Q)`: `|G : N_G(Q)| = q + 1` (from `|G| = q(q²−1)/2`, `|N_G(Q)| = q(q−1)/2`),
`N_G(Q)` acts transitively on the Sylow `p`-subgroups different from `Q` (orbit–stabilizer with
`|N_G(Q) ∩ N_G(Q')| = (q−1)/2`, using that distinct Sylow `p`-subgroups intersect trivially),
whence `G` is doubly transitive of degree `q + 1`; a nonidentity element of `Q` fixes only `Q`, an
element of `D#` fixes exactly two points, and the two-point stabilizer is a conjugate of `D`, of
order `(q−1)/2`. -/
theorem bswDataZassProp : Work.BSW.BSWDataZassProp := by
  intro G _ _ hS hnab q hdata
  obtain ⟨⟨p, k, hfact, hodd, hq⟩, h5, Q, D, hconf⟩ := IsBSWData.exists_conf hdata
  haveI : Fact p.Prime := hfact
  have hoddq : Odd q := by rw [hq]; exact hodd.pow
  refine ⟨p, k, hfact, hodd, ?_, normalizer (Q : Set G), ?_⟩
  · rw [← hq]; exact h5
  · refine ⟨zass_faithful hS h5 hoddq hconf, ?_, zass_pretransitive hfact.out hq h5 hoddq hconf,
      ?_, ?_⟩
    · rw [zass_card h5 hoddq hconf, hq]
    · intro g hg
      have := DataZass.zass_fix hfact.out hq h5 hoddq hconf (g := g) hg
      simpa using this
    · intro x y hxy
      have := zass_twoPoint (H := normalizer (Q : Set G)) hoddq
        (fun x hx => le_antisymm (card_inf_conj_le hfact.out hq h5 hoddq hconf hx)
          (card_inf_conj_ge hfact.out hq h5 hoddq hconf hx)) hxy
      rw [hq] at this
      exact this

end Work.BSW.Cases
