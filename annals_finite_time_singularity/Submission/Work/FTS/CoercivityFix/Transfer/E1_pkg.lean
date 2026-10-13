import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.CoercivityFix.Assembly.Comm2w
import Submission.Work.FTS.CoercivityFix.Transfer.Profiles
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.HkMemE1
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.RadA
import Submission.Work.FTS.CoercivityFix.Transfer.E1Parts.ContE1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.CoercivityFix.Transfer

/--
The three facts `Assembly.Comm2w` needs about the `D_θ`-defect `E1 α f` of the transfer
`𝓛̂ → 𝓛_Γ^T` on the thin class `CoerAdm α`: membership in `ℋ^n`, continuity of the blocks of
order `≤ n` on the open quadrant, and additivity of the blocks with `𝓛̂(D_θ f)`.

* `HkMem` is `E1Parts.HkMem_E1_of`, via the angular majorant `Γ²sin(2θ)^{-η} + Γ²sin(2θ)^{-γ}`
  (`E1Parts.AngGam`) and the radial majorant `∑_{j<4}(D_z^j radA α f)²w²` (`E1Parts.RadA`);
* `BlocksCont` is `Transfer.E1_blocks`;
* `BlocksAdd` follows from `C³`-regularity of both summands on `Qd` (`E1Parts.ContE1`) and the
  finite-order block additivity of `E2pkg.blocksAdd_of_contDiffOn`.
-/
theorem E1_pkg (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (n : ℕ) (hn : n ≤ 3) :
    ∀ f : ℝ → ℝ → ℝ, Work.FTS.Nonlin.CoerAdm α f →
      Work.Spaces.HkMem α n (Work.FTS.CoercivityFix.Transfer.E1 α f) ∧
      Work.FTS.CoercivityFix.Assembly.BlocksCont n (Work.FTS.CoercivityFix.Transfer.E1 α f) ∧
      Work.FTS.CoercivityFix.Assembly.BlocksAdd n
        (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f))
        (Work.FTS.CoercivityFix.Transfer.E1 α f) := by
  intro f hf
  have hblocks : Work.FTS.CoercivityFix.Assembly.BlocksCont n
      (Work.FTS.CoercivityFix.Transfer.E1 α f) :=
    E1_blocks α hα hα1 n hn f hf
  obtain ⟨hE1c3, hLhatc3⟩ := E1Parts.ContE1 α hα hα1 f hf
  refine ⟨?_, hblocks, ?_⟩
  · exact E1Parts.HkMem_E1_of α hα hα1 n hn hblocks (E1Parts.RadA α hα hα1 f hf)
  · have hE1n : ContDiffOn ℝ n (Function.uncurry (Work.FTS.CoercivityFix.Transfer.E1 α f))
        Work.Construction.Qd :=
      hE1c3.of_le (m := ((n : ℕ) : WithTop ℕ∞)) (by exact_mod_cast hn)
    have hLhatn : ContDiffOn ℝ n
        (Function.uncurry (Work.FTS.CoercivityFix.Lhat (Work.Spaces.Dth f)))
        Work.Construction.Qd :=
      hLhatc3.of_le (m := ((n : ℕ) : WithTop ℕ∞)) (by exact_mod_cast hn)
    exact E2pkg.blocksAdd_of_contDiffOn hLhatn hE1n

end Work.FTS.CoercivityFix.Transfer
