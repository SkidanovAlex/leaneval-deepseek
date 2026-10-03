/-
# N9, final form: `Tor₂^{K[G]}(S, -) = 0` in the vocabulary of N10

The project lead asked that N9 conclude exactly `Work.ORCoherence.TorTwoVanishes f` (or
`Work.ORCoherence.TorVanishes f`), so that the assembly (N14) can feed it to N10's
`coherent_of_embeds_semisimple`.  This file provides that bridge.

The mathematical content is the conclusion of Jaikin-Zapirain--Linton, Theorem 1.7: the
right `K[G]`-module `S = D_{K[G]}` has weak dimension at most one.  It is obtained from
the flatness of the diagonal module `S ⊗[K] I` (N9's flatness theorem,
`Work.ORFlatness.leftFlat_diagonal_jl`) together with the duality of `Tor` for the
diagonal module (JL Lemma 5.2), which is taken as a hypothesis in the same way as
everywhere else in this node:

`Tor₂^{K[G]}(S, M) ≅ Tor₂^{K[G]}(S ⊗_K M*, K) ≅ Tor₁^{K[G]}(S ⊗_K M*, I) ≅
Tor₁^{K[G]}(S ⊗_K I, M) = 0`.
-/
import Submission.Work.ORFlatness.Tor2
import Submission.Work.ORFlatness.JLRightMain
import Submission.Work.ORFlatness.FlatCrit
import Submission.Work.ORCoherence.Tor
import Submission.Work.ORCoherence.Tor.torTwoVanishes_of_torVanishes

set_option autoImplicit false
set_option maxHeartbeats 1000000

open TensorProduct MulOpposite

open CategoryTheory Limits

universe u

namespace Work.ORFlatness

/-- **Jaikin-Zapirain--Linton, Theorem 1.7** in the vocabulary of N10: if the right
`K[G]`-module `J` (= `S ⊗[K] I`, the augmentation-ideal diagonal module with its right
module structure) has `Tor₁` vanishing against every left `K[G]`-module, and the duality
chain of JL Lemma 5.2 identifies `Tor₂^{K[G]}(S, M)` with `Tor₁^{K[G]}(J, M)` for every
left `K[G]`-module `M`, then the right `K[G]`-module `S` has weak dimension at most one:
`Work.ORCoherence.TorVanishes φ.toRingHom`. -/
theorem torVanishes_of_flatDiagonal
    (K : Type u) [CommRing K] (G : Type u) [Group G]
    (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)
    (J : Type u) [AddCommGroup J] [Module (MonoidAlgebra K G)ᵐᵒᵖ J]
    (hJ : ∀ (L : Type u) [AddCommGroup L] [Module (MonoidAlgebra K G) L],
      Tor1Vanishes (MonoidAlgebra K G) J L)
    (hchain : ∀ (M : ModuleCat.{u} (MonoidAlgebra K G)),
      IsZero (Work.ORCoherence.Tor φ.toRingHom 2 M) ↔
        Tor1Vanishes (MonoidAlgebra K G) J (↥M)) :
    Work.ORCoherence.TorVanishes φ.toRingHom := by
  intro M
  rw [hchain M]
  exact hJ (↥M)

/-- The same statement in the concrete form in which N10 consumes it:
`Work.ORCoherence.TorTwoVanishes φ.toRingHom`. -/
theorem torTwoVanishes_of_flatDiagonal
    (K : Type u) [CommRing K] (G : Type u) [Group G]
    (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)
    (J : Type u) [AddCommGroup J] [Module (MonoidAlgebra K G)ᵐᵒᵖ J]
    (hJ : ∀ (L : Type u) [AddCommGroup L] [Module (MonoidAlgebra K G) L],
      Tor1Vanishes (MonoidAlgebra K G) J L)
    (hchain : ∀ (M : ModuleCat.{u} (MonoidAlgebra K G)),
      IsZero (Work.ORCoherence.Tor φ.toRingHom 2 M) ↔
        Tor1Vanishes (MonoidAlgebra K G) J (↥M)) :
    Work.ORCoherence.TorTwoVanishes φ.toRingHom :=
  Work.ORCoherence.Tor.torTwoVanishes_of_torVanishes φ.toRingHom
    (torVanishes_of_flatDiagonal K G S φ J hJ hchain)

/-- **Jaikin-Zapirain--Linton, Theorem 1.7**, assembled from the right-module mirror of
Theorem 5.6 and the duality chain of their Lemma 5.2: from
* the exact sequence `0 → A →f B →g C → 0` of left `K[G]`-modules (the transposed
  Claim 5.10),
* Claim 5.8 (`hB`), Lemma 5.1 + Claim 5.9 (`hA`) and Lemma 5.2 (`hswap`), which together give
  `Tor₁^{K[G]}(S ⊗[K] C, L) = 0` for every left `K[G]`-module `L` (mirror of Theorem 5.6), and
* the duality chain of Lemma 5.2 (`hchain`) identifying `Tor₂^{K[G]}(S, M)` with
  `Tor₁^{K[G]}(S ⊗[K] C, M)`,

conclude `Tor₂^{K[G]}(S, M) = 0` for every left `K[G]`-module `M`, i.e.
`Work.ORCoherence.TorTwoVanishes φ.toRingHom`.  This is the conclusion of N9 which N10
(`Work.ORCoherence.coherent_of_embeds_semisimple`) consumes. -/
theorem torTwoVanishes_diagonal_jl_right
    (K : Type u) [CommRing K] (G : Type u) [Group G]
    (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)
    {A B C : Type u} [AddCommGroup A] [Module (MonoidAlgebra K G) A]
    [AddCommGroup B] [Module (MonoidAlgebra K G) B]
    [AddCommGroup C] [Module K C] [Module (MonoidAlgebra K G) C]
    [IsScalarTower K (MonoidAlgebra K G) C] [SMulCommClass K (MonoidAlgebra K G) C]
    [Jinst : Module ((MonoidAlgebra K G)ᵐᵒᵖ) (S ⊗[K] C)]
    (f : A →ₗ[MonoidAlgebra K G] B) (g : B →ₗ[MonoidAlgebra K G] C)
    (hg : Function.Surjective g) (hfg : f.range = g.ker)
    (hB : ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := diagRightModule K G S φ M
      Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] M) B)
    (hA : ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := diagRightModule K G S φ M
      Function.Injective (BalTensor.map (MonoidAlgebra K G)
        (LinearMap.id : (S ⊗[K] M) →ₗ[(MonoidAlgebra K G)ᵐᵒᵖ] (S ⊗[K] M)) f))
    (hswap : ∀ (M : Type u) [AddCommGroup M] [Module K M] [Module (MonoidAlgebra K G) M]
      [IsScalarTower K (MonoidAlgebra K G) M] [SMulCommClass K (MonoidAlgebra K G) M],
      letI := diagRightModule K G S φ M
      (Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] M) C ↔
        Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] C) M))
    (hchain : ∀ (M : ModuleCat.{u} (MonoidAlgebra K G)),
      IsZero (Work.ORCoherence.Tor φ.toRingHom 2 M) ↔
        Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] C) (↥M)) :
    Work.ORCoherence.TorTwoVanishes φ.toRingHom := by
  have hJ : ∀ (L : Type u) [AddCommGroup L] [Module (MonoidAlgebra K G) L],
      Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] C) L :=
    tor1Vanishes_diagonal_jl_right K G S φ f g hg hfg hB hA hswap
  exact torTwoVanishes_of_flatDiagonal K G S φ (S ⊗[K] C) hJ hchain

end Work.ORFlatness
