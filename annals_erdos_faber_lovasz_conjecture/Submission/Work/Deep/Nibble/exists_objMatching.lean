import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.asmDefs
import Submission.Work.Deep.Nibble.asmObj

/-!
# The pseudorandom matching of one part of the §7 partition

The specialization of the deep input `PseudorandomMatchingAtObj` to the part
`P.part k` of the partition of `𝓗'`, the block `I k` of colours, the seed family
`M` reindexed by `blockSeed I M k`, the shifted family
`shiftFam I M k (absorbFam Rcur U S)` of vertex sets and the family of edge
objects through the vertices.
-/

set_option autoImplicit false

namespace Work.Deep.Nibble

open ErdosFaberLovaszConjecture

theorem exists_objMatching {n D r K : ℕ}
    {𝓗 𝓗' : MultiHypergraph n}
    {R Rcur : Hyp n}
    {U S : Set (Fin n)} {M : Fin D → Set (Set (Fin n))}
    (P : EdgePartition 𝓗' K) (I : Fin K → Finset (Fin D)) (k : Fin K)
    {βp κ γp : ℝ}
    (hPMS : PseudorandomMatchingAtObj n r βp κ γp)
    (hlinH : 𝓗.IsLinear) (hle : 𝓗' ≤ 𝓗) (hlin' : 𝓗'.IsLinear)
    (hpartdeg : ∀ w, |(((P.part k).deg w : ℝ)) - (((I k).card : ℝ))| ≤
      βp * ((I k).card : ℝ))
    (hsize : ∀ e ∈ 𝓗'.edges, edgeSize e ≤ r)
    (hMmatch : ∀ i, MultiHypergraph.IsMatching 𝓗 (M i))
    (hMout : ∀ i, ∀ e ∈ M i, e ∉ 𝓗'.edgeSet)
    (hMdisj : ∀ i j, i ≠ j → EdgeDisjointFam (M i) (M j))
    (hseed : ∀ c ∈ I k, ((famVert (M c)).ncard : ℝ) ≤ βp * ((I k).card : ℝ))
    (hint' : ∀ e ∈ (P.part k).edgeSet,
      (({c : Fin D | c ∈ I k ∧ (e ∩ famVert (M c)).Nonempty}).ncard : ℝ)
        ≤ βp * ((I k).card : ℝ))
    (hDlow : (n : ℝ) ^ ((1 : ℝ) / 2) ≤ ((I k).card : ℝ))
    (hDn : ((I k).card : ℝ) ≤ (n : ℝ))
    (h𝓕V : ((shiftFam I M k (absorbFam Rcur U S)).ncard : ℝ) ≤ (n : ℝ) ^ Real.log n)
    (h𝓕E : (({objThrough (P.part k) w | w : Fin n} :
        Set (Set (EdgeObj (P.part k)))).ncard : ℝ) ≤ (n : ℝ) ^ Real.log n) :
    ∃ N : Fin (I k).card → Set (EdgeObj (P.part k)),
      (∀ i, IsObjMatching (N i)) ∧
      (∀ i j, i ≠ j → Disjoint (N i) (N j)) ∧
      (∀ i, Disjoint (objVert (N i)) (famVert (blockSeed I M k i))) ∧
      (∀ i, PseudoRandomFam (objFam (N i)) (shiftFam I M k (absorbFam Rcur U S)) γp κ) ∧
      LeftoverFamObj N {objThrough (P.part k) w | w : Fin n} γp κ := by
  classical
  have hpartlin : (P.part k).IsLinear := MultiHypergraph.isLinear_mono (P.le k) hlin'
  have hpartle : P.part k ≤ 𝓗 := MultiHypergraph.le_trans (P.le k) hle
  have hsize' : ∀ e ∈ (P.part k).edges, edgeSize e ≤ r :=
    fun e he => hsize e (MultiHypergraph.edges_mono (P.le k) he)
  have hMmatch' : ∀ i, MultiHypergraph.IsMatching 𝓗 (blockSeed I M k i) := by
    intro i; rw [blockSeed_apply]; exact hMmatch _
  have hMout' : ∀ i, ∀ e ∈ blockSeed I M k i, e ∉ (P.part k).edgeSet := by
    intro i e he
    rw [blockSeed_apply] at he
    intro hcon
    exact hMout _ e he (MultiHypergraph.edgeSet_mono (P.le k) hcon)
  have hMdisj' : ∀ i j, i ≠ j → EdgeDisjointFam (blockSeed I M k i) (blockSeed I M k j) := by
    intro i j hij
    rw [blockSeed_apply, blockSeed_apply]
    exact hMdisj _ _ (fun h => hij (blockColour_injective I k h))
  have hseed' : ∀ i, ((famVert (blockSeed I M k i)).ncard : ℝ) ≤ βp * ((I k).card : ℝ) := by
    intro i; rw [blockSeed_apply]; exact hseed _ (blockColour_mem I k i)
  have hint'' : ∀ e ∈ (P.part k).edgeSet,
      (({i : Fin (I k).card | (e ∩ famVert (blockSeed I M k i)).Nonempty} :
        Set (Fin (I k).card)).ncard : ℝ) ≤ βp * ((I k).card : ℝ) := by
    intro e he
    have h1 : ({i : Fin (I k).card | (e ∩ famVert (blockSeed I M k i)).Nonempty} :
        Set (Fin (I k).card)).ncard =
        ({c : Fin D | c ∈ I k ∧ (e ∩ famVert (M c)).Nonempty} : Set (Fin D)).ncard := by
      rw [← ncard_colour_image (I := I) k (fun c : Fin D => (e ∩ famVert (M c)).Nonempty)]
      congr 1
    rw [h1]
    exact hint' e he
  exact hPMS 𝓗 (P.part k) (shiftFam I M k (absorbFam Rcur U S))
    ({objThrough (P.part k) w | w : Fin n}) (blockSeed I M k)
    hDlow hDn hlinH hpartlin hpartle hpartdeg hsize' h𝓕V h𝓕E hMmatch' hMout' hMdisj' hseed' hint''

end Work.Deep.Nibble
