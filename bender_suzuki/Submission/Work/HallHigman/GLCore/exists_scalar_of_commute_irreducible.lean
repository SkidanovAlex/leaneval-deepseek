import Mathlib
import Submission.Work.HallHigman.GLCore.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.HallHigman.GLCore

set_option linter.style.haveILetI false in

/-- **L6 of the GL-core design** (Step 4b(2) of the proof of Hall--Higman B, see
`NOTES_LEAD_ft_hallhigman.md` §2.2): an endomorphism of an irreducible `K`-module (`K`
algebraically closed, `V` finite dimensional) which commutes with a family of operators `S` is a
scalar.  (Take an eigenvalue `μ` of `z`; `ker (z - μ)` is `S`-invariant, hence `⊥` or `⊤`, and it
is nonzero.) -/
lemma exists_scalar_of_commute_irreducible {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [IsAlgClosed K] [FiniteDimensional K V] (S : Set (Module.End K V))
    (hS : Work.HallHigman.IsIrreducibleFor S) (z : Module.End K V)
    (hz : ∀ s ∈ S, Commute z s) :
    ∃ c : K, z = algebraMap K (Module.End K V) c := by
  haveI : Nontrivial V := hS.1
  -- Over an algebraically closed field, `z` has an eigenvalue `μ`.
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue z
  refine ⟨μ, ?_⟩
  -- `U = ker (z - μ) = eigenspace z μ`, which is `S`-invariant.
  have hUinv : ∀ s ∈ S, z.eigenspace μ ≤ (z.eigenspace μ).comap s := by
    intro s hs x hx
    rw [Submodule.mem_comap]
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    have hc : z * s = s * z := (hz s hs).eq
    calc z (s x) = (z * s) x := rfl
      _ = (s * z) x := by rw [hc]
      _ = s (z x) := rfl
      _ = s (μ • x) := by rw [hx]
      _ = μ • s x := map_smul s μ x
  rcases hS.2 (z.eigenspace μ) hUinv with h | h
  · -- `U = ⊥` would contradict that `μ` is an eigenvalue.
    exact absurd h hμ
  · -- `U = ⊤` forces `z = μ • 1`, a scalar.
    have hzero : z - μ • (1 : Module.End K V) = 0 := by
      rw [← LinearMap.ker_eq_top, ← Module.End.eigenspace_def]
      exact h
    have hz_eq : z = μ • (1 : Module.End K V) := sub_eq_zero.mp hzero
    rw [hz_eq, Algebra.algebraMap_eq_smul_one]

end Work.HallHigman.GLCore
