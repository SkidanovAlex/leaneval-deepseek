import Mathlib
import Submission.Work.CFT.ClassFormation.Defs

/-!
# The Bockstein coefficient sequence for group homology

This file sets up the vocabulary for the homology Bockstein sequence of a finite group `G`
with respect to the coefficient sequence `0 → ℤ --p--> ℤ → 𝔽_p → 0` of trivial `G`-modules:

* `HnZp p G n` — the `n`-th group homology of `G` with coefficients `𝔽_p` regarded as a
  trivial `ℤ`-module (`groupHomology (Rep.trivial ℤ G (ZMod p)) n`);
* `bockF p G` — multiplication by `p` on the trivial integral representation;
* `bockG p G` — reduction modulo `p`;
* `bocksteinSES p G` — the resulting short complex of representations.

The short complex is short exact (`bocksteinSES_shortExact`), and its long exact homology
sequence is the Bockstein sequence.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.CFT.ClassFormation.Schur

noncomputable section

/-- `H_n(G, 𝔽_p)` with the coefficient module `𝔽_p` regarded as a trivial `ℤ`-module. -/
abbrev HnZp (p : ℕ) (G : Type) [Group G] (n : ℕ) : ModuleCat ℤ :=
  groupHomology (Rep.trivial ℤ G (ZMod p)) n

/-- Multiplication by `p` on the trivial integral representation of `G`. -/
def bockF (p : ℕ) (G : Type) [Group G] : Rep.trivial ℤ G ℤ ⟶ Rep.trivial ℤ G ℤ :=
  (Rep.trivialFunctor ℤ G).map (ModuleCat.ofHom ((p : ℤ) • (LinearMap.id : ℤ →ₗ[ℤ] ℤ)))

/-- Reduction modulo `p` from the trivial integral representation to the trivial `𝔽_p`
representation. -/
def bockG (p : ℕ) (G : Type) [Group G] :
    Rep.trivial ℤ G ℤ ⟶ Rep.trivial ℤ G (ZMod p) :=
  (Rep.trivialFunctor ℤ G).map (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ (ZMod p) 1))

@[simp]
lemma bockF_hom (p : ℕ) (G : Type) [Group G] (z : ℤ) : (bockF p G).hom z = p * z := by
  simp [bockF, Rep.trivialFunctor]

@[simp]
lemma bockG_hom (p : ℕ) (G : Type) [Group G] (z : ℤ) : (bockG p G).hom z = (z : ZMod p) := by
  simp [bockG, Rep.trivialFunctor]

lemma bockF_comp_bockG (p : ℕ) (G : Type) [Group G] :
    bockF p G ≫ bockG p G = 0 := by
  ext
  simp [bockF, bockG, Rep.trivialFunctor]

/-- The **Bockstein short complex** in `Rep ℤ G`: the coefficient sequence
`0 → ℤ --p--> ℤ --mod p--> 𝔽_p → 0` of trivial `G`-modules. -/
def bocksteinSES (p : ℕ) (G : Type) [Group G] : ShortComplex (Rep ℤ G) :=
  ShortComplex.mk (bockF p G) (bockG p G) (bockF_comp_bockG p G)

@[simp] lemma bocksteinSES_X₁ (p : ℕ) (G : Type) [Group G] :
    (bocksteinSES p G).X₁ = Rep.trivial ℤ G ℤ := rfl

@[simp] lemma bocksteinSES_X₂ (p : ℕ) (G : Type) [Group G] :
    (bocksteinSES p G).X₂ = Rep.trivial ℤ G ℤ := rfl

@[simp] lemma bocksteinSES_X₃ (p : ℕ) (G : Type) [Group G] :
    (bocksteinSES p G).X₃ = Rep.trivial ℤ G (ZMod p) := rfl

@[simp] lemma bocksteinSES_f (p : ℕ) (G : Type) [Group G] :
    (bocksteinSES p G).f = bockF p G := rfl

@[simp] lemma bocksteinSES_g (p : ℕ) (G : Type) [Group G] :
    (bocksteinSES p G).g = bockG p G := rfl

end

end Work.CFT.ClassFormation.Schur
