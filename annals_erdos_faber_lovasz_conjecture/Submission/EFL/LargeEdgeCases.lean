import Submission.EFL.LargeEdgeBlocks
import Submission.EFL.LargeEdgeCase2
import Submission.EFL.Fig3Case1

/-!
# The case split of Theorem 6.1 (`large-edge-thm`)

`LargeEdgeBlocks.lean` fires the two applications of the Reordering Lemma of
Figure 3 and records the resulting partition
`𝓗 = 𝓗₃ ⊔ W₂ ⊔ 𝓗₂^good ⊔ 𝓗₁^good` in the structure `BlocksOK`.  This module
performs the case split of the paper:

* **Case 1** (`W₂ = ∅`, so `𝓗₂^left = ∅` and `⪯₂` is good): the good ordering
  of `𝓗₁^left` is already good, and the Prop 6.9 + 6.10 assembly of
  `Fig3Case1.lean` (`largeEdge_nonExtremal_of_app1_app2`) gives the
  non-extremal alternative.  This is `case1_of_blocks`.
* **Case 2.1** (`W₂ ≠ ∅` and `r₃ < (1−δ)√n`): `LargeEdgeNonExtremal`, proved
  in `LargeEdgeCase2.lean` as `case2_nonExtremal`.
* **Case 2.2** (`W₂ ≠ ∅` and `(1−δ)√n ≤ r₃`): here the edges of `W₂` are
  *near-full* and one expects `LargeEdgeExtremal` (the FPP-extremal
  alternative), via Lemma 5.1 (`linear_nearfull_colouring`) and Vizing's
  theorem.  This branch is isolated as the explicit hypothesis `h22` of
  `largeEdge_of_blocks`; it is the only missing piece of Theorem 6.1.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- **Case 1 of Figure 3**: if the App-2 firing is good (`W₂ = ∅`), the
non-extremal alternative of Theorem 6.1 holds. -/
theorem case1_of_blocks {n r₁ r₀ : ℕ} {β γ₂ σ δ γ₁ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂}
    {r₂ r₃ : ℕ}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (hW₂ : W₂ = ∅) (hlin : 𝓗.IsLinear) (h2n : 2 ≤ n) (hr₁ : 2 ≤ r₁)
    (hβ : 0 < β) (hγ₂0 : 0 < γ₂) (hσ0 : 0 < σ) (hσ3 : 3 * σ ≤ 1) (hσ23 : σ ≤ 2 / 3)
    (hr₀ : 1 ≤ r₀) (hγ₁σ : γ₁ ≤ σ / 2) (hβn8 : 8 ≤ β * (n : ℝ))
    (hsize : ∀ e : 𝓗, r₁ < edgeSize (e : Set (Fin n)))
    (hsizeR : ∀ e : 𝓗, (r₁ : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ))
    (hβn : (r₀ : ℝ) < β * (n : ℝ) / 4)
    (hA₁ : 32 / β ^ 2 ≤ σ * (n : ℝ))
    (hA₂ : 32 / β ^ 2 + 2 * γ₂ * (n : ℝ) / 3 ≤ (1 - 2 * σ) * (n : ℝ))
    (hmargin : (2 : ℝ) * (n : ℝ) / ((β / 5) * (r₀ : ℝ)) < ((σ / 2) * (n : ℝ)) / 4)
    (hbig : ((bigFinset (β / 5) (𝓗.largeEdges r₀)).card : ℝ) < ((σ / 2) * (n : ℝ)) / 2)
    {φmed : (𝓗.medEdges r₁ r₀).Coloring (Fin n)} {Cmed : Finset (Fin n)}
    (hφmed : φmed.UsesColourSet Cmed) (hCmed : (Cmed.card : ℝ) ≤ γ₁ * (n : ℝ))
    (hmedb : ∀ c : Fin n, (φmed.classVertexCount c : ℝ) ≤ γ₁ * (n : ℝ))
    (hbudget : (Cmed.card : ℝ) + 1 ≤ (σ / 2) * (n : ℝ)) :
    LargeEdgeNonExtremal n σ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 := by
  classical
  -- `W₂ = ∅` forces the App-2 left part to be empty, so `𝓗₂^good = 𝓗₁^left`.
  have hL₂empty : Left₂ = ∅ := hB.hW₂empty hW₂
  have hdeg₂ : ∀ e : Left₁, (precedingDegree Left₁ ord₂ e : ℝ) ≤ (1 - 3 * σ) * (n : ℝ) := by
    intro e
    refine hB.hdeg₂ e ?_
    have hmem : (e : Set (Fin n)) ∈ Good₂ ∪ Left₂ := by rw [hB.hpart₂]; exact e.2
    rw [Set.mem_union] at hmem
    rcases hmem with h | h
    · exact h
    · rw [hL₂empty] at h
      exact absurd h (Set.notMem_empty _)
  exact largeEdge_nonExtremal_of_app1_app2 (n := n) (r₁ := r₁) (r₀ := r₀)
    (𝓗 := 𝓗) (β := β) (γ₂ := γ₂) (σ := σ) (γ₁ := γ₁)
    hβ hγ₂0 hσ0 hσ3 hσ23 hr₁ h2n hr₀ hβn8 hsize hsizeR hlin hγ₁σ hβn hA₁ hA₂
    ord₁ Good₁ Left₁ hB.hG₁sub hB.hL₁sub hB.hpart₁ hB.hdisj₁ hB.hdeg₁ hB.hseg₁
    ord₂ hdeg₂ hmargin hbig hφmed hCmed hmedb hbudget

end

end ErdosFaberLovaszConjecture

namespace ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- **The case split of Theorem 6.1.**  Given the Figure-3 block
decomposition (`BlocksOK`) and the whole numeric hierarchy, either the
non-extremal alternative holds (Cases 1 and 2.1: `W₂ = ∅`, or
`W₂ ≠ ∅` with `r₃ < (1−δ)√n`), or the extremal alternative holds, provided by
the hypothesis `h22` in the remaining Case 2.2 (`W₂ ≠ ∅` and
`(1−δ)√n ≤ r₃`).  Thus `h22` is exactly the outstanding obligation of the
proof of Theorem 6.1. -/
theorem largeEdge_of_blocks {Δ₀ : ℝ → ℝ}
    (hMRe : ∀ (ζ' : ℝ), 0 < ζ' → ζ' ≤ 1 → ∀ (V : Type) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℝ), Δ₀ ζ' ≤ Δ →
        (G.maxDegree : ℝ) ≤ Δ →
        (∀ v : V, (nbrEdges G v : ℝ) ≤ (1 - ζ') * Δ ^ 2 / 2) →
        ∃ k : ℕ, (k : ℝ) ≤ (1 - ζ' / Real.exp 6) * Δ ∧ G.Colorable k)
    {n r₁ r₀ : ℕ} {β γ₂ σ δ γ₁ ζ : ℝ} {B₀ : ℕ} {Δ : ℝ}
    {𝓗 Good₁ Left₁ Good₂ Left₂ W₂ H₃ : Hypergraph (Fin n)}
    {k₁ : ℕ} {ord₁ : nonHuge 𝓗 β ≃ Fin k₁} {k₂ : ℕ} {ord₂ : Left₁ ≃ Fin k₂}
    {r₂ r₃ : ℕ} {Cmed : Finset (Fin n)}
    (hB : BlocksOK n 𝓗 β γ₂ σ δ Good₁ Left₁ Good₂ Left₂ W₂ H₃ k₁ ord₁ k₂ ord₂ r₂ r₃)
    (h22 : W₂ ≠ ∅ → (1 - δ) * Real.sqrt (n : ℝ) ≤ (r₃ : ℝ) →
      LargeEdgeExtremal n δ γ₂ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗)
    (hlin : 𝓗.IsLinear) (hn : 0 < n) (h2n : 2 ≤ n) (hβ : 0 < β) (hγ₂0 : 0 < γ₂)
    (hσ0 : 0 < σ) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 256)
    (hγ₁σ : γ₁ ≤ σ / 2) (hσ31 : 3 * σ ≤ 1) (hr₀ : 1 ≤ r₀) (h2r₀ : 2 ≤ r₀)
    (h2r₁ : 2 ≤ r₁) (hR : (100000000 : ℝ) ≤ (r₁ : ℝ))
    (hsize : ∀ e : 𝓗, (r₁ : ℝ) < (edgeSize (e : Set (Fin n)) : ℝ))
    (hδV : δ ≤ volBound app3tau app3K)
    (hm : Corollary65Margins Δ₀ ζ r₃ B₀ n Δ)
    (hB₀ : sizeFactor (3 * σ) 1 * (r₃ : ℝ) ≤ (B₀ : ℝ))
    (hmarginA : ((2 : ℝ) / ((β / 5) / 2) + 1) *
      ((n : ℝ) / (((β / 5) / 2 : ℝ) * (r₀ : ℝ))) ≤ ζ * (n : ℝ) / 1000)
    (h69m : (2 : ℝ) * (n : ℝ) / ((β / 5) * ((r₀ : ℝ) - 1)) < ((1 / 6000 : ℝ) * (n : ℝ)) / 4)
    (h69b : (((bigFinset (β / 5) (case2H3med r₁ r₀ 𝓗 H₃)).card : ℕ) : ℝ) <
      ((1 / 6000 : ℝ) * (n : ℝ)) / 2)
    (h69mσ : (2 : ℝ) * (n : ℝ) / ((β / 5) * ((r₀ : ℝ) - 1)) < ((σ / 4) * (n : ℝ)) / 4)
    (h69bσ : (((bigFinset (β / 5) (case2Right r₁ r₀ 𝓗 Good₁ Good₂)).card : ℕ) : ℝ) <
      ((σ / 4) * (n : ℝ)) / 2)
    (hζdef : ζ = 1 - (r₃ : ℝ) / Real.sqrt (n : ℝ)) (hζpos : 0 < ζ)
    (hk2 : 2 * δ ^ 2 ≤ ζ / 1000 - 2 * σ)
    (hnbig : 16 / Real.sqrt δ ≤ (n : ℝ))
    (hσsmall : (2 : ℝ) * σ + 1 / (n : ℝ) ≤ 1 / 12000)
    (hsize₃ : ∀ e : case2H3med r₁ r₀ 𝓗 H₃, r₃ ≤ edgeSize (e : Set (Fin n)))
    (h2βn : (2 : ℝ) ≤ (β / 5) * (n : ℝ))
    (hroom1 : ⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ ≤ (Finset.univ \ Cmed).card)
    (hroom2 : ⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ + ⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ ≤
      (Finset.univ \ Cmed).card)
    (hbudget0 : ⌈(1 - ζ / 1000) * (n : ℝ)⌉₊ + ⌈(ζ / 1000 - 2 * σ) * (n : ℝ)⌉₊ ≤
      ⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊)
    (hβc : 8 ≤ β * (n : ℝ)) (hn1 : 1 ≤ n)
    (hσn : 32 / β ^ 2 ≤ σ * (n : ℝ))
    (hγm : (γ₂ / 3) * (n : ℝ) + 32 / β ^ 2 ≤ (1 - 2 * σ) * (n : ℝ))
    (hKroom : ⌊(1 - 3 * σ / 2) * (n : ℝ)⌋₊ + Cmed.card ≤ n)
    (hslack : 1 + 32 / β ^ 2 ≤ (σ / 4) * (n : ℝ))
    (hβn : (r₀ : ℝ) < β * (n : ℝ) / 4)
    (hA₁ : 32 / β ^ 2 ≤ σ * (n : ℝ))
    (hA₂ : 32 / β ^ 2 + 2 * γ₂ * (n : ℝ) / 3 ≤ (1 - 2 * σ) * (n : ℝ))
    (hmargin : (2 : ℝ) * (n : ℝ) / ((β / 5) * (r₀ : ℝ)) < ((σ / 2) * (n : ℝ)) / 4)
    (hbig : ((bigFinset (β / 5) (𝓗.largeEdges r₀)).card : ℝ) < ((σ / 2) * (n : ℝ)) / 2)
    (hCmed : (Cmed.card : ℝ) ≤ γ₁ * (n : ℝ))
    {φmed : (𝓗.medEdges r₁ r₀).Coloring (Fin n)} (hφmed : φmed.UsesColourSet Cmed)
    (hmedb : ∀ c : Fin n, (φmed.classVertexCount c : ℝ) ≤ γ₁ * (n : ℝ))
    (hbudget : (Cmed.card : ℝ) + 1 ≤ (σ / 2) * (n : ℝ)) :
    LargeEdgeNonExtremal n σ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 ∨
      LargeEdgeExtremal n δ γ₂ γ₁ β (r₁ : ℝ) (r₀ : ℝ) 𝓗 := by
  classical
  have hσ32 : 3 * σ / 2 ≤ 1 := by linarith only [hσ31]
  have hσ23 : σ ≤ 2 / 3 := by linarith only [hσ31]
  have hsizeN : ∀ e : 𝓗, r₁ < edgeSize (e : Set (Fin n)) := fun e => by
    exact_mod_cast hsize e
  have hsizeR : ∀ e : 𝓗, (r₁ : ℝ) ≤ (edgeSize (e : Set (Fin n)) : ℝ) :=
    fun e => le_of_lt (hsize e)
  have hβn8 : 8 ≤ β * (n : ℝ) := hβc
  by_cases hW : W₂ = ∅
  · -- Case 1: the App-2 application is good.
    refine Or.inl (case1_of_blocks (n := n) (r₁ := r₁) (r₀ := r₀) hB hW hlin h2n h2r₁ hβ
      hγ₂0 hσ0 hσ31 hσ23 hr₀ hγ₁σ hβn8 hsizeN hsizeR hβn hA₁ hA₂
      hmargin hbig hφmed hCmed hmedb hbudget)
  · by_cases hr : (r₃ : ℝ) < (1 - δ) * Real.sqrt (n : ℝ)
    · -- Case 2.1: `r₃ < (1−δ)√n`.
      refine Or.inl (case2_nonExtremal (Δ₀ := Δ₀) hMRe hB hW hlin hn h2n hβ hσ0 hγ₁σ hσ32 hr₀
        h2r₀ h2r₁ hR hsize hδ0 hδ1 hδV hm hB₀ hmarginA h69m h69b h69mσ h69bσ
        (hζdef := hζdef) (hζpos := hζpos) (hk2 := hk2) (hnbig := hnbig)
        (hσsmall := hσsmall) (hsize₃ := hsize₃) h2βn hCmed
        hroom1 hroom2 hbudget0 hβc hn1 hσn hγm hKroom hslack hβn hφmed hmedb)
    · -- Case 2.2: the outstanding obligation.
      exact Or.inr (h22 hW (not_lt.mp hr))

end

end ErdosFaberLovaszConjecture
