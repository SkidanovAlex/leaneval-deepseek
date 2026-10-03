/-
# Weak dimension at most one (Jaikin-Zapirain--Linton, Theorem 1.7)

N9 of the route design: from the flatness of the left `K[G]`-module `S ⊗[K] I`
(`S` = the Linnell ring `D_{K[G]}`, `I` the augmentation ideal, the diagonal module of
`Submission.Work.ORFlatness.Diagonal`) conclude that the right `K[G]`-module `S` has weak
dimension at most one, i.e. `Tor₂^{K[G]}(S, L) = 0` for every left `K[G]`-module `L`.

`Tor₂^{R}(X, N) = 0` is expressed in the standard syzygy form (`Tor2Vanishes`): every
first syzygy of the right module `X` is `Tor₁`-acyclic against `N`.  The single remaining
ingredient is the duality of `Tor` for the diagonal module (JL Lemma 5.2), which gives
`Tor₂^{K[G]}(S, L) ≅ Tor₂^{K[G]}(S ⊗_K L*, K) ≅ Tor₁^{K[G]}(S ⊗_K L*, I) ≅
Tor₁^{K[G]}(S ⊗_K I, L)`; we take that chain as a hypothesis, exactly as the route design
assigns JL Lemma 5.2 to N1.
-/
import Submission.Work.ORFlatness.Flat
import Submission.Work.ORFlatness.FlatCrit
import Submission.Work.ORFlatness.Diagonal

set_option autoImplicit false

open TensorProduct MulOpposite

universe u

namespace Work.ORFlatness

variable (R : Type u) [Ring R]

/-- `Tor2Vanishes R X N` is the statement `Tor₂^{R}(X, N) = 0`, for a right `R`-module `X`
and a left `R`-module `N`: every first syzygy of `X` is `Tor₁`-acyclic against `N`.  (By
dimension shifting this is equivalent to the vanishing of `Tor₂`.) -/
def Tor2Vanishes (X : Type u) [AddCommGroup X] [Module Rᵐᵒᵖ X]
    (N : Type u) [AddCommGroup N] [Module R N] : Prop :=
  ∀ P : ProjPres R X, Tor1Vanishes R P.K N

/-- **Jaikin-Zapirain--Linton, Theorem 1.7** (in the form used for the coherence of
`K[G]`): if the right `K[G]`-module `J` (the module `S ⊗[K] I` of the right-module
diagonal structure, `I` the augmentation ideal) has `Tor₁` vanishing against every left
`K[G]`-module — which is what its flatness gives — and the duality of `Tor` for the
diagonal module identifies `Tor₂^{K[G]}(S, L)` with `Tor₁^{K[G]}(J, L)`, then the right
`K[G]`-module `S` has weak dimension at most one. -/
theorem tor2Vanishes_of_flat_augmentation
    (K : Type u) [CommRing K] (G : Type u) [Group G]
    (S : Type u) [Ring S] [Module (MonoidAlgebra K G)ᵐᵒᵖ S]
    (J : Type u) [AddCommGroup J] [Module (MonoidAlgebra K G)ᵐᵒᵖ J]
    (hJ : ∀ (L : Type u) [AddCommGroup L] [Module (MonoidAlgebra K G) L],
      Tor1Vanishes (MonoidAlgebra K G) J L)
    (hchain : ∀ (L : Type u) [AddCommGroup L] [Module (MonoidAlgebra K G) L],
      Tor2Vanishes (MonoidAlgebra K G) S L ↔ Tor1Vanishes (MonoidAlgebra K G) J L) :
    ∀ (L : Type u) [AddCommGroup L] [Module (MonoidAlgebra K G) L],
      Tor2Vanishes (MonoidAlgebra K G) S L := by
  intro L _ _
  rw [hchain L]
  exact hJ L

end Work.ORFlatness
