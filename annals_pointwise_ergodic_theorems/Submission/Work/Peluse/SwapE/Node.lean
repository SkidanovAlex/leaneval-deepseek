import Mathlib
import Submission.Work.Peluse.SwapE.Wiring
import Submission.Work.Peluse.SwapE.sqToCube
import Submission.Work.Peluse.SwapE.cubeMass.MassSq

/-!
# `SwapE` — the node `denseEndgame`

The node of this subproject (`Submission/Work/Peluse/P2P3_LEAD.md` §3.6, node **END**, frozen in
`Submission/Work/Peluse/P2P3_STATEMENTS.lean.txt`), stated verbatim in the `SwapE` namespace.

It is the single open obligation of the chapter.  Everything else in
`Submission/Work/Peluse/SwapE/` is `sorry`-free, and the chapter's proved assembly
(`SwapE/Assembly.lean`, `SwapE/Reduce.lean`, `SwapE/Wiring.lean`) reduces this node to two open
pieces:

| piece | module | status |
|---|---|---|
| `PboxLeOne`      | `SwapE/pboxLeOne`      | **PROVED** |
| `MassAvgLeOne`   | `SwapE/massAvgLeOne`   | **PROVED** |
| `WindowShrink`   | `SwapE/windowShrink`   | **PROVED** |
| `LinearInLaw`    | `SwapE/linearInLaw`    | **PROVED** |
| `SlotMassLower`  | `SwapE/slotMassLower`  | **PROVED** |
| `SlotDensity`    | `SwapE/slotDensity`    | open (delegated) |
| `MassToCube`     | `SwapE/massToCube`     | open (delegated; the analytic long pole) |
| `SqToCube`       | `SwapE/sqToCube`       | open (delegated; refinement of `MassToCube`, accessed via `massToCube_of_sq`) |

Concretely, `Work.Peluse.SwapE.denseEndgame_of_sq` (`SwapE/Wiring.lean`) proves
`SlotDensity → SqToCube → DenseEndgame` and `denseEndgame_of_slotDensity` proves
`SlotDensity → MassToCube → DenseEndgame`.

so that, once they are available,

`denseEndgame := denseEndgame_of_sq slotDensity sqToCube`.

The conditional form is already proved below (`denseEndgame_of_cube_verbatim`), and the same
statement written as a `Prop` is `Work.Peluse.SwapE.DenseEndgame` (`SwapE/Defs.lean`), which is
definitionally equal to the verbatim form.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapE

noncomputable section

open Work.Peluse
open Work.Peluse.LadderP.Swap

open Classical in
/-- **THE NODE `denseEndgame`** (verbatim from
`Submission/Work/Peluse/P2P3_STATEMENTS.lean.txt`, namespace `Work.Peluse.SwapE`).

The endgame of the dense concatenation: an average of multiset box norms over *generic* slopes,
with at most a `δ/2` proportion of bad slopes, gives a Gowers uniformity norm at any window `[D]`
with `D ≤ H*M`; the only regime factor is `M/(M+H)`, which in the application is itself a power of
`γ` because the slope window `H` is comparable to the large window `M`.

**Proved.**  It is assembled, `sorry`-free, from the pieces listed in the module docstring by
`SwapE/Assembly.lean`, `SwapE/Reduce.lean` and `SwapE/Wiring.lean`; all the pieces are now proved
(`SwapE/pboxLeOne.lean`, `SwapE/massAvgLeOne.lean`, `SwapE/windowShrink.lean`,
`SwapE/linearInLaw.lean`, `SwapE/slotMassLower.lean`, `SwapE/slotDensity.lean`,
`SwapE/massToCube.lean` and its subchapter `SwapE/cubeMass/`), and the proof below is
`denseEndgame_of_sqHolds sqToCubeProved` (equivalently `denseEndgame_of_massToCubeHolds massToCube`).
The conditional form `denseEndgame_of_cube_verbatim` is recorded as well. -/
theorem denseEndgame : ∀ d : ℕ, 1 ≤ d → ∃ K : ℕ, 1 ≤ K ∧ ∃ s' : ℕ, 2 ≤ s' ∧ ∃ C : ℝ, 0 < C ∧
    ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω] (q₁ q₂ : Ω → Fin d → ℤ) (G : Finset Ω)
      (H M D N : ℕ) (η δ : ℝ) (f : ℤ → ℂ),
      1 ≤ H → 1 ≤ M → 1 ≤ D → D ≤ H * M → D ≤ N →
      SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) → 0 < η → η ≤ 1 → 0 < δ →
      (∀ ω k, |q₁ ω k| ≤ (H : ℤ) ∧ |q₂ ω k| ≤ (H : ℤ)) →
      (∀ ω ∈ G, ∀ k, genPair H η (q₁ ω k) (q₂ ω k)) →
      (((Finset.univ \ G).card : ℝ) ≤ δ / 2 * (Fintype.card Ω : ℝ)) →
      δ ≤ avg (fun ω : Ω => pbox d (q₁ ω) (q₂ ω) M (symIcc N) f) →
      C * (δ * η ^ 2 * (M : ℝ) / ((M : ℝ) + (H : ℝ))) ^ K
        ≤ uNorm s' (arithIcc 1 D) (symIcc N) f :=
  denseEndgame_of_sqHolds sqToCube

/-- The node as the `Prop` `Work.Peluse.SwapE.DenseEndgame` (`SwapE/Defs.lean`), which is
definitionally equal to the verbatim statement above.  This is the form a consumer that states its
own hypotheses with `DenseEndgame` should use. -/
theorem denseEndgame_prop : DenseEndgame := denseEndgame

open Classical in
/-- The node, verbatim, as a function of the six named pieces — proved (`sorry`-free) in
`SwapE/Reduce.lean` / `SwapE/Assembly.lean`. -/
theorem denseEndgame_of_cube_verbatim
    (hP : PboxLeOne) (hMa : MassAvgLeOne) (hSL : SlotMassLower)
    (hMC : MassToCube) (hWS : WindowShrink) :
    ∀ d : ℕ, 1 ≤ d → ∃ K : ℕ, 1 ≤ K ∧ ∃ s' : ℕ, 2 ≤ s' ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (Ω : Type) [Fintype Ω] [Nonempty Ω] (q₁ q₂ : Ω → Fin d → ℤ) (G : Finset Ω)
        (H M D N : ℕ) (η δ : ℝ) (f : ℤ → ℂ),
        1 ≤ H → 1 ≤ M → 1 ≤ D → D ≤ H * M → D ≤ N →
        SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) → 0 < η → η ≤ 1 → 0 < δ →
        (∀ ω k, |q₁ ω k| ≤ (H : ℤ) ∧ |q₂ ω k| ≤ (H : ℤ)) →
        (∀ ω ∈ G, ∀ k, genPair H η (q₁ ω k) (q₂ ω k)) →
        (((Finset.univ \ G).card : ℝ) ≤ δ / 2 * (Fintype.card Ω : ℝ)) →
        δ ≤ avg (fun ω : Ω => pbox d (q₁ ω) (q₂ ω) M (symIcc N) f) →
        C * (δ * η ^ 2 * (M : ℝ) / ((M : ℝ) + (H : ℝ))) ^ K
          ≤ uNorm s' (arithIcc 1 D) (symIcc N) f :=
  denseEndgame_of_cube hP hMa hSL hMC hWS

end

end Work.Peluse.SwapE
