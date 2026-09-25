import Mathlib
import Submission.Work.CFT.ClassFormation.Defs
import Submission.Work.CFT.ClassFormation.Schur.module_finite_groupHomology

/-!
# Finiteness of mod-`p` group homology

For a finite group `G` and a prime `p`, the group homology `Hₙ(G, 𝔽ₚ)` with trivial `𝔽ₚ`
coefficients (`Work.CFT.ClassFormation.HnHomFp`) is a finite type: the degree-`n` term of the
inhomogeneous chain complex computing it is `(Fin n → G) →₀ ZMod p`, a finitely generated
`ZMod p`-module, and `ZMod p` is a Noetherian ring (it is a field), so the homology — a
subquotient of the chains — is finitely generated.  A finitely generated module over the finite
ring `ZMod p` is finite (`Module.finite_of_finite`).

This is the `ZMod p`-specialisation of
`Work.CFT.ClassFormation.Schur.module_finite_groupHomology`.
-/

namespace Work.Tower.Shafarevich.CFT

theorem HnHomFp_finite (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] (n : ℕ) :
    Finite ↥(Work.CFT.ClassFormation.HnHomFp p G n) := by
  classical
  haveI : NeZero p := ⟨Nat.Prime.ne_zero (Fact.out : Nat.Prime p)⟩
  haveI : Module.Finite (ZMod p) ↥(Work.CFT.ClassFormation.HnHomFp p G n) :=
    Work.CFT.ClassFormation.Schur.module_finite_groupHomology (ZMod p) G (V := ZMod p) n
  exact Module.finite_of_finite (ZMod p)

end Work.Tower.Shafarevich.CFT
