/-
# The Tor-level duality of JL Lemma 5.2(2) in the vocabulary of node N9 (mismatch (M4))

This file instantiates Jaikin-Zapirain--Linton Lemma 5.2(2)
(`Work.ORHomAlg.JL52.jl_5_2_2`) in the form needed by node N9's `hswap`, using the self-duality
lemmas

* `Work.ORBridgeTor.trivTensorEquiv` (`K ⊗[K] N ≅ N`),
* `Work.ORBridgeTor.dualDiagRight` (the antipode twist `(S ⊗[K] M)^* ≅ S ⊗[K] M`),
* `Work.ORBridgeTor.dualDualEquiv`, `Work.ORBridgeTor.diagDualDualEquiv` (the double dual),
* `Work.ORBridgeTor.torEquivOfEquiv` (transport of `Tor` along module isomorphisms).

## Main results

* `Work.ORBridgeTor.torAux` — `Tor₁^{K[G]}(X, C) ≅ Tor₁^{K[G]}(C^*, X^*)` (Lemma 5.2(2) with the
  trivial module).
* `Work.ORBridgeTor.torSwapIso` — `Tor₁^{K[G]}(S ⊗[K] M, C) ≅ Tor₁^{K[G]}(S ⊗[K] C, M)`, the
  duality which `Work.ORBridgeTor.hswap_of_jl52` turns into N9's `hswap`.
-/
import Submission.Work.ORBridgeTor.Defs
import Submission.Work.ORBridgeTor.TrivMod
import Submission.Work.ORBridgeTor.trivTensorEquiv
import Submission.Work.ORBridgeTor.dualDualEquiv
import Submission.Work.ORBridgeTor.dualDiagRight
import Submission.Work.ORBridgeTor.diagDualDualEquiv
import Submission.Work.ORBridgeTor.torEquivOfEquiv
import Submission.Work.ORBridgeTor.DiagRightCompat
import Submission.Work.ORHomAlg.JL52.jl_5_2_2

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open TensorProduct MulOpposite

universe u

namespace Work.ORBridgeTor

/-- **The `Tor`-level consequence of JL Lemma 5.2(2) run with the trivial module `K`**:
for a right `K[G]`-module `X` and a left `K[G]`-module `C`,
`Tor₁(X, C) ≅ Tor₁(C^*, X^*)`.

Proof: `Tor₁(X, C) ≅ Tor₁(X, K ⊗[K] C)` (`Work.ORBridgeTor.trivTensorEquiv`), then Lemma 5.2(2)
with `M := K` gives `Tor₁(X, K ⊗[K] C) ≅ Tor₁(C^*, K ⊗[K] X^*)`, and finally
`Tor₁(C^*, K ⊗[K] X^*) ≅ Tor₁(C^*, X^*)`. -/
theorem torAux {K : Type u} [Field K] {G : Type u} [Group G]
    (X : Type u) [AddCommGroup X] [Module K X] [Module (MonoidAlgebra K G)ᵐᵒᵖ X]
    [IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ X] [SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ X]
    (C : Type u) [AddCommGroup C] [Module K C] [Module (MonoidAlgebra K G) C]
    [IsScalarTower K (MonoidAlgebra K G) C] [SMulCommClass K (MonoidAlgebra K G) C] :
    Nonempty (Work.ORHomAlg.Tor (R := MonoidAlgebra K G) 1 X C ≃ₗ[ℤ]
      Work.ORHomAlg.Tor (R := MonoidAlgebra K G) 1 (Work.ORHomAlg.DualMod C)
        (Work.ORHomAlg.DualMod X)) := by
  obtain ⟨eC⟩ := trivTensorEquiv K G C
  obtain ⟨eX⟩ := trivTensorEquiv K G (Work.ORHomAlg.DualMod X)
  obtain ⟨e1⟩ := torEquivOfEquiv (R := MonoidAlgebra K G)
    (LinearEquiv.refl (MonoidAlgebra K G)ᵐᵒᵖ X) eC.symm 1
  obtain ⟨e2⟩ := Work.ORHomAlg.JL52.jl_5_2_2 K G X K C 1
  obtain ⟨e3⟩ := torEquivOfEquiv (R := MonoidAlgebra K G)
    (LinearEquiv.refl (MonoidAlgebra K G)ᵐᵒᵖ (Work.ORHomAlg.DualMod C)) eX 1
  exact ⟨e1.trans (e2.trans e3)⟩

/-- **The Tor-level duality of JL Lemma 5.2(2) in the vocabulary of N9's `hswap`**:

`Tor₁^{K[G]}(S ⊗[K] M, C) ≅ Tor₁^{K[G]}(S ⊗[K] C, M)`

for the right `K[G]`-module structure `Work.ORFlatness.diagRightModule` on both `S ⊗[K] -`.  The
proof is the chain displayed in the docstring of `Submission/Work/ORBridgeTor/HSwap.lean`: two
applications of Lemma 5.2(2), the antipode twist `Work.ORBridgeTor.dualDiagRight` and its mirror,
and the double dual `Work.ORBridgeTor.diagDualDualEquiv`. -/
theorem torSwapIso (K : Type u) [Field K] (G : Type u) [Group G]
    (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)
    [Module (MonoidAlgebra K G) S] [SMulCommClass K (MonoidAlgebra K G) S]
    (hS : ∀ (x : MonoidAlgebra K G) (s : S), x • s = φ x * s)
    (ι : AntiAut K S)
    (hι : ∀ g : G, ι (Work.ORFlatness.gElemR K G S φ g) =
      Work.ORFlatness.gElemR K G S φ g⁻¹)
    (C : Type u) [AddCommGroup C] [Module K C] [Module (MonoidAlgebra K G) C]
    [IsScalarTower K (MonoidAlgebra K G) C] [SMulCommClass K (MonoidAlgebra K G) C] :
    letI := Work.ORFlatness.diagRightModule K G S φ C
    ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := Work.ORFlatness.diagRightModule K G S φ M
      Nonempty (Work.ORHomAlg.Tor (R := MonoidAlgebra K G) 1 (S ⊗[K] M) C ≃ₗ[ℤ]
        Work.ORHomAlg.Tor (R := MonoidAlgebra K G) 1 (S ⊗[K] C) M) := by
  letI := Work.ORFlatness.diagRightModule K G S φ C
  intro M _ _ _ _ _
  letI := Work.ORFlatness.diagRightModule K G S φ M
  -- compatibility of the diagonal right structures with the `K`-scalars
  haveI hstM : IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ (S ⊗[K] M) :=
    isScalarTower_diagRightModule K G S φ M
  haveI hscM : SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ (S ⊗[K] M) :=
    smulCommClass_diagRightModule K G S φ M
  haveI hstC : IsScalarTower K (MonoidAlgebra K G)ᵐᵒᵖ (S ⊗[K] C) :=
    isScalarTower_diagRightModule K G S φ C
  haveI hscC : SMulCommClass K (MonoidAlgebra K G)ᵐᵒᵖ (S ⊗[K] C) :=
    smulCommClass_diagRightModule K G S φ C
  -- the two self-dualities `(S ⊗[K] -)^* ≅ S ⊗[K] -`
  obtain ⟨twM⟩ := dualDiagRight K G S φ hS M ι hι
  obtain ⟨twC⟩ := dualDiagRight K G S φ hS C ι hι
  -- the double dual
  obtain ⟨dd⟩ := diagDualDualEquiv K G S C
  -- the two applications of Lemma 5.2(2)
  obtain ⟨h1⟩ := torAux (K := K) (G := G) (S ⊗[K] M) C
  obtain ⟨h2⟩ := Work.ORHomAlg.JL52.jl_5_2_2 K G (Work.ORHomAlg.DualMod C) S M 1
  obtain ⟨h3⟩ := torAux (K := K) (G := G) (S ⊗[K] C) M
  -- transport along the self-dualities
  obtain ⟨t1⟩ := torEquivOfEquiv (R := MonoidAlgebra K G)
    (LinearEquiv.refl (MonoidAlgebra K G)ᵐᵒᵖ (Work.ORHomAlg.DualMod C)) twM 1
  obtain ⟨t2⟩ := torEquivOfEquiv (R := MonoidAlgebra K G)
    (LinearEquiv.refl (MonoidAlgebra K G)ᵐᵒᵖ (Work.ORHomAlg.DualMod M)) dd 1
  obtain ⟨t3⟩ := torEquivOfEquiv (R := MonoidAlgebra K G)
    (LinearEquiv.refl (MonoidAlgebra K G)ᵐᵒᵖ (Work.ORHomAlg.DualMod M)) twC.symm 1
  exact ⟨h1.trans (t1.trans (h2.trans (t2.trans (t3.trans h3.symm))))⟩

end Work.ORBridgeTor
