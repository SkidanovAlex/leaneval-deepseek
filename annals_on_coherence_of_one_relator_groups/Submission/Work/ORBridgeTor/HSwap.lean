/-
# N9's `hswap` from JL Lemma 5.2(2) (mismatch (M4))

Node N9 (`Work.ORFlatness.torTwoVanishes_diagonal_jl_right`) consumes the hypothesis

`hswap` : for every left `K[G]`-module `M`, `Tor₁^{K[G]}(S ⊗[K] M, C) = 0` iff
`Tor₁^{K[G]}(S ⊗[K] C, M) = 0`, with `S ⊗[K] M` carrying the right diagonal action
`Work.ORFlatness.diagRightModule` and `S ⊗[K] C` the caller's right `K[G]`-module structure
(`Jinst` in `Work.ORAssembly.torTwoVanishes_of_flatHyp`).

`hswap` is the duality of Jaikin-Zapirain--Linton Lemma 5.2(2)
(`Work.ORHomAlg.JL52.jl_5_2_2`), whose vocabulary (`BalancedTensor`, `Tor`, `DualMod`) differs
from N9's (`BalTensor`, `Tor1Vanishes`, `diagRightModule`).  This file closes the mismatch:

* `Work.ORBridgeTor.hswap_of_tor_iso` — the *vocabulary glue*: from the Tor-level duality (Lemma
  5.2(2) in the vocabulary of `Work.ORHomAlg`) to N9's `hswap`, via
  `Work.ORBridgeTor.tor1Vanishes_iff_tor`
  (`Submission/Work/ORBridgeTor/tor1Vanishes_iff_tor.lean`, which identifies
  `Work.ORFlatness.Tor1Vanishes R X N` with the vanishing of the genuine `Work.ORHomAlg.Tor R 1 X N`);
* `Work.ORBridgeTor.hswap_of_jl52` — the deliverable: `hswap` from JL Lemma 5.2(2) itself,
  obtained by composing the glue with `Work.ORBridgeTor.torSwapIso`
  (`Submission/Work/ORBridgeTor/torSwap.lean`), which instantiates Lemma 5.2(2) with `M := K` and
  with `(L, M, N) := (C^*, S, M)` and uses the self-dualities
  `Work.ORBridgeTor.trivTensorEquiv` (`K ⊗[K] N ≅ N`),
  `Work.ORBridgeTor.dualDiagRight` (the antipode twist `(S ⊗[K] -)^* ≅ S ⊗[K] -`),
  `Work.ORBridgeTor.dualDualEquiv` and `Work.ORBridgeTor.diagDualDualEquiv` (the double dual).
-/
import Submission.Work.ORBridgeTor.Defs
import Submission.Work.ORBridgeTor.tor1Vanishes_iff_tor
import Submission.Work.ORBridgeTor.torSwap

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open TensorProduct MulOpposite

universe u

namespace Work.ORBridgeTor

/-- **N9's `hswap` from the Tor-level duality of JL Lemma 5.2(2)** (the vocabulary glue).

`hjl52` is the Tor-level duality in the vocabulary of `Work.ORHomAlg` — the shape produced by
instantiating `Work.ORHomAlg.JL52.jl_5_2_2` as in `Work.ORBridgeTor.torSwapIso`.  The conclusion
is exactly the hypothesis `hswap` of node N9. -/
theorem hswap_of_tor_iso (K : Type u) [Field K] (G : Type u) [Group G]
    (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)
    (C : Type u) [AddCommGroup C] [Module K C] [Module (MonoidAlgebra K G) C]
    [IsScalarTower K (MonoidAlgebra K G) C] [SMulCommClass K (MonoidAlgebra K G) C]
    [Jinst : Module ((MonoidAlgebra K G)ᵐᵒᵖ) (S ⊗[K] C)]
    (hjl52 : ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := Work.ORFlatness.diagRightModule K G S φ M
      Nonempty (Work.ORHomAlg.Tor (R := MonoidAlgebra K G) 1 (S ⊗[K] M) C ≃ₗ[ℤ]
        Work.ORHomAlg.Tor (R := MonoidAlgebra K G) 1 (S ⊗[K] C) M)) :
    ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := Work.ORFlatness.diagRightModule K G S φ M
      (Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] M) C ↔
        Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] C) M) := by
  intro M _ _ _ _ _
  letI := Work.ORFlatness.diagRightModule K G S φ M
  rw [tor1Vanishes_iff_tor (R := MonoidAlgebra K G) (S ⊗[K] M) C,
    tor1Vanishes_iff_tor (R := MonoidAlgebra K G) (S ⊗[K] C) M]
  obtain ⟨e⟩ := hjl52 M
  exact ⟨fun h => ⟨fun a b => e.symm.injective (h.elim (e.symm a) (e.symm b))⟩,
    fun h => ⟨fun a b => e.injective (h.elim (e a) (e b))⟩⟩

/-- **N9's `hswap` from JL Lemma 5.2(2)** (mismatch (M4)).

The hypotheses are the setting of the one-relator case: `S` a `K`-algebra with `φ : K[G] → S`
(the paper's `S = D(G)`), `S` carrying the `K[G]`-module structure induced by `φ` (this is `hS`),
and the antipode `ι` of `S` with `ι (φ g) = (φ g)⁻¹`; `C` is a left `K[G]`-module with its right
diagonal module structure `Jinst` on `S ⊗[K] C`, which is `diagRightModule` (`hJC`).

The conclusion is exactly the `hswap` hypothesis of node N9
(`Work.ORAssembly.torTwoVanishes_of_flatHyp`). -/
theorem hswap_of_jl52 (K : Type u) [Field K] (G : Type u) [Group G]
    (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)
    [Module (MonoidAlgebra K G) S] [SMulCommClass K (MonoidAlgebra K G) S]
    (hS : ∀ (x : MonoidAlgebra K G) (s : S), x • s = φ x * s)
    (ι : AntiAut K S)
    (hι : ∀ g : G, ι (Work.ORFlatness.gElemR K G S φ g) =
      Work.ORFlatness.gElemR K G S φ g⁻¹)
    (C : Type u) [AddCommGroup C] [Module K C] [Module (MonoidAlgebra K G) C]
    [IsScalarTower K (MonoidAlgebra K G) C] [SMulCommClass K (MonoidAlgebra K G) C]
    [Jinst : Module ((MonoidAlgebra K G)ᵐᵒᵖ) (S ⊗[K] C)]
    (hJC : Jinst = Work.ORFlatness.diagRightModule K G S φ C) :
    ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := Work.ORFlatness.diagRightModule K G S φ M
      (Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] M) C ↔
        Work.ORFlatness.Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] C) M) := by
  subst hJC
  letI := Work.ORFlatness.diagRightModule K G S φ C
  refine hswap_of_tor_iso K G S φ C ?_
  intro M _ _ _ _ _
  exact torSwapIso K G S φ hS ι hι C M

end Work.ORBridgeTor
