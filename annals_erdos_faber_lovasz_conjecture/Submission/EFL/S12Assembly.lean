import Submission.EFL.S12MainA
import Submission.EFL.S12A2Main
import Submission.EFL.S12MainB
import Submission.EFL.BigEdges
import Submission.EFL.OptColFaithful
import Submission.Work.ConeSwitch.Assembly

/-!
# §12: the final assembly of the proof of Theorem 1.1

This module combines

* `s12_step1` (Theorem 6.7 applied to the medium and large edges: the constant
  hierarchy and the Type A / Type B alternative),
* the three branches `s12_A1_main`, `s12_A2_main` (Type A, split by
  `IsFull`) and `s12_B_main` (Type B),

and concludes `eflStatement` via the reduction `eflStatement_of_bigEdges` (the
singleton edges are coloured greedily at the end).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

open Classical

noncomputable section

variable {n : ℕ}

/-- An edge has two vertices exactly when its size is at least two. -/
theorem hasTwoVertices_iff_two_le_edgeSize {e : Set (Fin n)} :
    HasTwoVertices e ↔ 2 ≤ e.ncard := by
  rw [HasTwoVertices]
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    have h : 1 < e.ncard := (Set.one_lt_ncard (Set.toFinite e)).mpr ⟨x, hx, y, hy, hxy⟩
    omega
  · intro h
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      (Set.one_lt_ncard (Set.toFinite e)).mp (by omega : 1 < e.ncard)
    exact ⟨x, y, hx, hy, hxy⟩

/-- **Theorem 1.1, §12 end to end.**  From the deep inputs of the paper
(Molloy–Reed and Kahn, through Theorem 6.7; the Nibble lemma of §7; and
Glock–Kühn–Osthus, through Corollary 10.13), every linear hypergraph on `n`
sufficiently large vertices is `n`-edge-colourable.  (The Leftover lemma
`lem:leftover` is *not* an input: it is proved from Kahn's theorem in
`Submission/EFL/LeftoverLemma.lean`.)

**Cone switch (2026-09-23).**  `hGKO : GKOStatement` is now the *faithful*
existential-threshold form of Theorem 10.8 (`Work.Deep.GKO.GKOStatementFixed`), and the
whole of §12 has been re-architected around it in `Work.ConeSwitch.Assembly`: the Type-A
density `ρ` is chosen first, the thresholds of Corollary 10.13 are read off at the density
`ρ/4` of the final graph, and the constants `ε, γ, β, ξ, ζ, η, ηr` are produced *after* them.
Both Type-A branches are parametric in `(ρ, ε)`; the three-way split is taken at that free
`(ρ, ε)` rather than at the pinned `(σ/2, σ³/10⁴²)`. -/
theorem eflStatement_of_deep (hMR : MolloyReedStatement) (hK : KahnStatement)
    (hNib : NibbleStatementFixed) (hGKO : GKOStatement) :
    eflStatement :=
  Work.ConeSwitch.eflStatement_of_deep_faithful hMR hK hNib hGKO

end

end ErdosFaberLovaszConjecture
