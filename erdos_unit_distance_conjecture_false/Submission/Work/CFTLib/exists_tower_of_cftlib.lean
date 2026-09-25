import Mathlib
import Submission.CFTLib.Interfaces
import Submission.Work.Defs.Basic
import Submission.Work.CFTConsumer.Defs
import Submission.Work.CFTConsumer.weakShaf_two_of_cftlib
import Submission.Work.CFTConsumer.Assembly
import Submission.Work.Tower.CyclotomicBase.Main

/-! Guidance from the project lead (the requester):

# Guidance: the erdos tower from the shared CFT interfaces (read HANDOFF.md first)

This is `Work.Interface.exists_tower` with the gap replaced by the two library hypotheses. The tower machinery
(pro-p Golod–Shafarevich endgame, tower cutting, cyclotomic base, CM adjunction, Minkowski) is all proved.
Plan:
1. Find where the endgame actually consumes the Shafarevich estimate: `Work.Tower.AssemblyProP.exists_tower_intermediateField_pos`
   (`hshaf`) and `Work.Tower.AssemblyProP.exists_tower_of_H2Estimate`, `Work.Tower.TowerCutProP.unramified_tower_gs_proP`.
   Identify the K it is applied to (the supremum of the T-split unramified 3-extensions, finite by contradiction
   hypothesis) and check that K splits T (`TowerCut.goodImages`) and is maximal.
2. Prove a variant of the endgame whose Shafarevich hypothesis only needs T-split, maximal K — i.e. exactly the
   situation of `CFTLib.ShafBound` with `CFTLib.SplitsAt F K T` and `CFTLib.IsMaximalUnramified F K 3 T`.
   Translate: erdos's `IsUnramifiedExtension` (finite primes) ↔ `differentIdeal = ⊤`; real places stay real
   automatically for odd degree; T : Finset (Ideal (𝓞 F)) of primes ↔ Finset (HeightOneSpectrum (𝓞 F));
   `SplitsCompletelyIn` ↔ inertia degree 1 given unramified. For F totally real cubic, p = 3:
   r₁+r₂−1 = 2 and δ₃(F) = 0 (F is real, so no primitive cube root of unity).
3. `CFTLib.MaximalClassCond` turns maximality into the `ClassCond` hypothesis of `ShafBound`.
Keep `H2Estimate` untouched; add new files under `Submission/Work/CFTConsumer/`.

## Implementation (this file)

* `Submission/Work/CFTConsumer/Defs.lean` fixes `EFOne` (the ramification–inertia form of complete
  splitting) and `WeakShaf C₀`, the Shafarevich estimate in the *weaker* form that `CFTLib.ShafBound`
  supplies (only `T`-split maximal `K`, and only nonzero primes of `T`).
* `Submission/Work/CFTConsumer/efOne_iSup.lean` proves that `EFOne` ascends to finite suprema
  (composita) of intermediate fields — this is what lets the tower-cutting endgame conclude that its
  maximal field `K` (the supremum of the `T`-split good images, `Work.Tower.TowerCut.goodImages`)
  splits `T` completely, which is the extra hypothesis `CFTLib.ShafBound` needs.
* `Submission/Work/CFTConsumer/weakShaf_two_of_cftlib.lean` derives `WeakShaf 2` from the two shared
  hypotheses (for totally real cubic `F` one has `r₁ + r₂ − 1 + δ₃(F) = 2`).
* `Submission/Work/CFTConsumer/Endgame.lean` and `.../Assembly.lean` are the variants of
  `Work.Tower.TowerCutProP.unramified_tower_gs_proP` and `Work.Tower.AssemblyProP` whose Shafarevich
  hypothesis has the shape of `WeakShaf`.
* The cyclotomic base `Work.Tower.exists_cubic_unramified_extension_data` supplies `hbase`. -/

open NumberField
open scoped Classical nonZeroDivisors

namespace Work.CFTLib

theorem exists_tower_of_cftlib (h1 : CFTLib.ShafBound) (h2 : CFTLib.MaximalClassCond) (H : ℝ) (hH : 0 < H) :
    ∃ (t : ℕ) (q : Fin t → ℕ) (C : ℝ), 0 < t ∧ (∀ b, Nat.Prime (q b)) ∧ Function.Injective q ∧
      (∀ b, q b % 4 = 1) ∧ 1 ≤ C ∧ (H * C * (1 + Real.log C)) ^ 2 < (2 : ℝ) ^ t ∧
      ∀ N : ℕ, ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsCMField K),
        N ≤ Module.finrank ℚ K ∧ NumberField.rootDiscr K ≤ C ∧
        (∀ b, Work.Defs.SplitsCompletely (q b) K) := by
  refine Work.CFTConsumer.exists_tower_intermediateField_pos_split ?_ ⟨2, ?_⟩ H hH
  · -- the cyclotomic base of the tower (paper Proposition 3.2), proved in the workspace
    intro ℓ hℓ r hr hr3 hrinj
    obtain ⟨M, hMF, hMN, hMA, hMG, F, h1, h2, h3, h4, _h5, h6, h7, h8, h9⟩ :=
      Work.Tower.exists_cubic_unramified_extension_data ℓ hℓ r hr hr3 hrinj
    exact ⟨M, hMF, hMN, hMA, hMG, F, h1, h2, h3, h6, h4, h7, h8, h9⟩
  · -- Shafarevich's estimate from the two shared CFT hypotheses
    exact Work.CFTConsumer.weakShaf_two_of_cftlib h1 h2

end Work.CFTLib
