import Submission.Work.Deep.Nibble.AssemblyAll
import Submission.Work.Deep.Nibble.nibbleConclusion_of_assembly
import Submission.Work.Deep.Nibble.pseudorandomMatchingObj_of_embed_sparse
import Submission.Work.Deep.Nibble.sparseMatchingStatement_fintype

/-!
# The glue: the Nibble Lemma's conclusion from the margin bundle

This module assembles the whole §7 chain: from the cone's margin bundle
`NibbleMarginsStrong`, the defect-D8 field `4000 ξ ≤ γ ρ²`, the embedding lemma
`EmbedAtR r` and the sparsified matching input
`SparseMatchingAbove N₁ (r+1) (γ²/16000) (γ/4)` (i.e. `cor:sparse_egj` at the
parameters of the assembly), it produces the conclusion `NibbleConclusion` of
`lem:nibble2` — for *every* instance satisfying the hypotheses of
`NibbleStatementFixed` at those parameters.

So the only mathematical input of the whole chapter that remains is
`SparseMatchingStatement` (`cor:sparse_egj`), which this chapter derives from
`RelCoverStatement` (`Work.Deep.Nibble.sparseMatchingStatement_of_relCover`);
see `Work.Deep.Nibble.nibbleStatementFixed_of_sparseMatching` at the end of this
file for the statement the cone consumes.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

noncomputable section

variable {n : ℕ}

/-- **The §7 assembly at the pinned constants.**  Given the margins, the
embedding lemma and the sparsified matching theorem (at the assembly's
parameters), the Nibble Lemma's conclusion follows for every instance of its
hypotheses. -/
theorem nibbleConclusion_of_all
    {𝓗 𝓗' : MultiHypergraph n} {R : ErdosFaberLovaszConjecture.Hypergraph (Fin n)}
    {𝓥 : Set (Set (Fin n))} {U S : Set (Fin n)} {ρ γ β ξ ε : ℝ} {D r : ℕ}
    (M : Fin D → Set (Set (Fin n)))
    (hm : NibbleMarginsStrong n (D : ℝ) r β γ ε ρ ξ) (hD8 : 4000 * ξ ≤ γ * ρ ^ 2)
    (hr3 : 3 ≤ r) (hE : EmbedAtR r) {N₁ : ℕ}
    (hSMA : SparseMatchingAbove N₁ (r + 1) (2 * (γ ^ 2 / 32000)) (γ / 4))
    (hnN₁ : N₁ ≤ n) (hn4 : 4 ≤ n) (hn2r3 : 2 * r ^ 3 ≤ n)
    (hnβp : (r / (2 * (γ ^ 2 / 32000))) ^ 2 + 1 ≤ (n : ℝ))
    (hnκ : (30 / (γ ^ 2 / 3200)) ^ 40 + 1 ≤ (n : ℝ))
    (hne : Real.exp 2 + 1 ≤ (n : ℝ))
    (hU : U = VplusTwo (MultiHypergraph.pow2 𝓗) (1 - ε)) (hSsub : S ⊆ U)
    (hC1 : (1 - 2 * ε) * (n : ℝ) < (U.ncard : ℝ) →
      (D : ℝ) + γ * (n : ℝ) ≤ (S.ncard : ℝ))
    (hU𝓥 : U ∈ 𝓥) (huniv𝓥 : (Set.univ : Set (Fin n)) ∈ 𝓥)
    (habs : IsAbsorber (incidentTwo (MultiHypergraph.pow2 𝓗) U) R 𝓥 ρ γ ξ)
    (hlinH : 𝓗.IsLinear) (hle : 𝓗' ≤ 𝓗) (hout : ∀ e ∈ 𝓗'.edges, e ∉ R)
    (hlin' : 𝓗'.IsLinear) (hsize : ∀ e ∈ 𝓗'.edges, edgeSize e ≤ r)
    (hdeg : ∀ w : Fin n, |((𝓗'.deg w : ℝ)) - (D : ℝ)| ≤ β * (D : ℝ))
    (hMmatch : ∀ i, MultiHypergraph.IsMatching 𝓗 (M i))
    (hMdisj : ∀ i j, i ≠ j → EdgeDisjointFam (M i) (M j))
    (hMout : ∀ i, ∀ e ∈ M i, e ∉ 𝓗'.edgeSet)
    (hMR : ∀ i, ∀ e ∈ M i, e ∉ R)
    (hMsz : ∀ i, ((famVert (M i)).ncard : ℝ) ≤ β * (D : ℝ))
    (hMint : ∀ e ∈ 𝓗'.edgeSet,
      (({i : Fin D | (e ∩ famVert (M i)).Nonempty}).ncard : ℝ) ≤ β * (D : ℝ)) :
    NibbleConclusion (U := U) (S := S) (γ := γ) (β := β) (ε := ε) 𝓗 𝓗' R M := by
  classical
  have hγ0 : 0 < γ := hm.base.hγ0
  have hγ1 : γ ≤ 1 := by
    have h1 := hm.hγρ
    have h2 := hm.base.hρ1
    linarith
  -- the assembly data
  obtain ⟨P, I, hpar, hint, hcross, hIcard, hIdisj, hIuniv, hKslide, hpartdeg, hseed,
    hint'⟩ := exists_assemblyAll (r := r) 𝓗' M hm hD8 hdeg hMsz hMint
  -- `lem:pseudorandom_matching` at the pinned constants
  have hPMS : PseudorandomMatchingAtObj n r (γ ^ 2 / 32000) (γ ^ 2 / 3200) (γ / 4) :=
    pseudorandomMatchingObj_of_embed_sparse (r := r) hr3
      (β := γ ^ 2 / 32000) (κ := γ ^ 2 / 3200) (γ := γ / 4)
      (by positivity) (by positivity) (by positivity)
      (by nlinarith) (by nlinarith) (by nlinarith)
      hE (N₁ := N₁) (by simpa only [mul_assoc] using hSMA)
      hn4 hn2r3 hnN₁ (by simpa only using hnβp) (by simpa only using hnκ) hne
  exact nibbleConclusion_of_assembly M hU hSsub hC1 hU𝓥 huniv𝓥 habs hlinH hle hout hlin'
    hsize hdeg hMmatch hMdisj hMout hMR hMsz hMint hpar hint hcross P I hIcard hIdisj
    hIuniv hKslide hpartdeg hseed hint' hPMS

end

end Work.Deep.Nibble
