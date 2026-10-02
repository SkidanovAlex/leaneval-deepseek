import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.Defs
import Submission.Work.Deep.Kahn.sum_edgeSize_eq_sum_degree

namespace Work.Deep.Nibble

/-- **Double counting.**  In an `r`-uniform hypergraph `𝓗` on `Fin n` whose degrees are at
most `D`, the number of edges is at most `nD/r ≤ nD`: summing `|e| = r` over the edges and
`d_𝓗(v) ≤ D` over the vertices gives `r·|𝓗| = ∑_v d_𝓗(v) ≤ nD`. -/
theorem card_nat_le_of_degree_bound {n : ℕ} (𝓗 : ErdosFaberLovaszConjecture.Hypergraph (Fin n))
    {r : ℕ} {D : ℝ}
    (hr : 1 ≤ r) (hunif : ∀ e ∈ 𝓗, ErdosFaberLovaszConjecture.edgeSize e = r)
    (hdeg : ∀ v : Fin n, (ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℝ) ≤ D) :
    (Nat.card 𝓗 : ℝ) ≤ (n : ℝ) * D := by
  classical
  haveI : Fintype ↥𝓗 := Fintype.ofFinite ↥𝓗
  -- The double count `∑_e |e| = ∑_v d_𝓗(v)`, transported to `ℝ`.
  have hsum : (∑ e : ↥𝓗, (ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) : ℝ))
      = ∑ v : Fin n, (ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℝ) := by
    have hnat : (∑ e : ↥𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)))
        = ∑ v : Fin n, ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v :=
      Work.Deep.Kahn.sum_edgeSize_eq_sum_degree 𝓗
    calc (∑ e : ↥𝓗, (ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) : ℝ))
        = ((∑ e : ↥𝓗, ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) : ℕ) : ℝ) :=
          (Nat.cast_sum Finset.univ _).symm
      _ = ((∑ v : Fin n, ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℕ) : ℝ) := by
          rw [hnat]
      _ = ∑ v : Fin n, (ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℝ) :=
          Nat.cast_sum Finset.univ _
  -- Uniformity: every edge contributes `r ≥ 1`, so `#𝓗 ≤ ∑_e |e|`.
  have hedge : (Fintype.card ↥𝓗 : ℝ)
      ≤ ∑ e : ↥𝓗, (ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) : ℝ) := by
    have hone : (Fintype.card ↥𝓗 : ℝ) = ∑ _ : ↥𝓗, (1 : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ]
      norm_num
    rw [hone]
    refine Finset.sum_le_sum fun e _ => ?_
    have h1 : (1 : ℕ) ≤ ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) := by
      have h := hunif (e : Set (Fin n)) e.2
      omega
    exact_mod_cast h1
  -- The degree bound `∑_v d_𝓗(v) ≤ nD`.
  have hdeg' : (∑ v : Fin n, (ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℝ))
      ≤ (n : ℝ) * D := by
    calc ∑ v : Fin n, (ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℝ)
        ≤ ∑ _ : Fin n, D := Finset.sum_le_sum fun v _ => hdeg v
      _ = (n : ℝ) * D := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          norm_num
  calc (Nat.card ↥𝓗 : ℝ)
      = (Fintype.card ↥𝓗 : ℝ) := by rw [Nat.card_eq_fintype_card]
    _ ≤ ∑ e : ↥𝓗, (ErdosFaberLovaszConjecture.edgeSize (e : Set (Fin n)) : ℝ) := hedge
    _ = ∑ v : Fin n, (ErdosFaberLovaszConjecture.hypergraphDegree 𝓗 v : ℝ) := hsum
    _ ≤ (n : ℝ) * D := hdeg'

end Work.Deep.Nibble
