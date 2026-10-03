/-
# The mirror of Jaikin-Zapirain--Linton, Theorem 5.6: the right-module case

`Submission/Work/ORFlatness/JLMain.lean` proves flatness of the left `K[G]`-module
`S ⊗[K] C` from `Tor₁`-vanishing of the test modules `S ⊗[K] L` (`L` a right `K[G]`-module)
with the diagonal left-module structure of `Submission/Work/ORFlatness/Diagonal.lean`.

Here we mirror the construction on the other side, as the paper does ("by symmetry we also
have that the right `K[G]`-module `D_{K[G]} ⊗_K I_{K[G]}` is flat", proof of Theorem 1.7).
The test modules `S ⊗[K] M` now carry the diagonal *right* module structure of
`Submission.Work.ORFlatness/DiagonalRight.lean` (a left `K[G]`-module `M` in, a right
`K[G]`-module out), and the short exact sequence `0 → A → B → C → 0` is a sequence of *left*
`K[G]`-modules (the transposed Claim 5.10 of the paper).

The output `tor1Vanishes_diagonal_jl_right` is the exact mirror of the final computation of
their proof: `Tor₁^{K[G]}(D_{K[G]} ⊗_K I_{K[G]}, L) = 0` for every left `K[G]`-module `L`.
The flatness statement `RightFlat (K[G]) (S ⊗[K] C)` derived from it (via
`Work.ORFlatness.rightFlat_of_forall_tor1Vanishes`) is added in
`Submission/Work/ORFlatness/RightFlatCrit.lean`.
-/
import Submission.Work.ORFlatness.Flat
import Submission.Work.ORFlatness.Tensor
import Submission.Work.ORFlatness.DiagonalRight
import Submission.Work.ORFlatness.exists_compatibleKStructure
import Submission.Work.ORFlatness.tor1Vanishes_of_shortExact_right
import Submission.Work.ORFlatness.RightFlatCrit

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

open TensorProduct MulOpposite

universe u

namespace Work.ORFlatness

variable (K : Type u) [CommRing K] (G : Type u) [Group G]
variable (S : Type u) [Ring S] [Algebra K S] (φ : MonoidAlgebra K G →ₐ[K] S)

/-- **Jaikin-Zapirain--Linton, Theorem 5.6 (single two-cell case), right-module form.**
For every left `K[G]`-module `M`, the right `K[G]`-module `S ⊗[K] M` (with the diagonal action
of `Submission.Work.ORFlatness.DiagonalRight`) satisfies
`Tor₁^{K[G]}(S ⊗[K] C, M) = 0` (`Work.ORFlatness.Tor1Vanishes`), where `0 → A →f B →g C → 0`
is a short exact sequence of left `K[G]`-modules (the transposed Claim 5.10).

The hypotheses are the mirror images of the paper's:
* `hB` — Claim 5.8: `Tor₁^{K[G]}(S ⊗[K] M, B) = 0`;
* `hA` — Lemma 5.1 together with Claim 5.9 (Weinbaum) and `char K ∤ l`: the map
  `S ⊗[K] M → S ⊗[K] M` induced by `f` (tensored with the identity of `S ⊗[K] M`) is injective;
* `hswap` — Lemma 5.2: the duality `Tor₁^{K[G]}(S ⊗[K] M, C) ≅ Tor₁^{K[G]}(S ⊗[K] C, M)`. -/
theorem tor1Vanishes_diagonal_jl_right
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
        Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] C) M)) :
    ∀ (M : Type u) [AddCommGroup M] [Module (MonoidAlgebra K G) M],
      Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] C) M := by
  intro M _ _
  obtain ⟨inst, h1, h2⟩ := exists_compatibleKStructure K G M
  letI := inst
  haveI : IsScalarTower K (MonoidAlgebra K G) M := h1
  haveI : SMulCommClass K (MonoidAlgebra K G) M := h2
  letI := diagRightModule K G S φ M
  exact (hswap M).mp
    (tor1Vanishes_of_shortExact_right f g hg hfg (S ⊗[K] M) (hB M) (hA M))

/-- **Jaikin-Zapirain--Linton, Theorem 5.6 (single two-cell case), right-module form,
flatness version.**  Same hypotheses as `tor1Vanishes_diagonal_jl_right`; the conclusion is
that the right `K[G]`-module `S ⊗[K] C` — with the diagonal action of
`Submission.Work.ORFlatness/DiagonalRight.lean` — is right flat, i.e. tensoring on the left by
it preserves injective maps of left `K[G]`-modules.  This is the flatness of the right
`K[G]`-module `D_{K[G]} ⊗_K I_{K[G]}` obtained "by symmetry" in the proof of Theorem 1.7. -/
theorem rightFlat_diagonal_jl
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
        Tor1Vanishes (MonoidAlgebra K G) (S ⊗[K] C) M)) :
    RightFlat (MonoidAlgebra K G) (S ⊗[K] C) :=
  rightFlat_of_forall_tor1Vanishes (MonoidAlgebra K G)
    (tor1Vanishes_diagonal_jl_right K G S φ f g hg hfg hB hA hswap)

end Work.ORFlatness
