import Submission.Defs

open EquiangularLinesFixedAngle
open Filter
open scoped BigOperators

namespace Submission

/-! Basic facts about `spectralRadiusOrder`. -/

open Classical in
/-- If the spectral radius order is finite, it is witnessed by a graph on `k.toNat` vertices. -/
lemma spectralRadiusOrder_lt_top_witness {lam : ℝ} (hk : spectralRadiusOrder lam < (⊤ : ℕ∞)) :
    ∃ G : SimpleGraph (Fin (spectralRadiusOrder lam).toNat),
      spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal lam := by
  classical
  let P : ℕ → Prop := fun k => ∃ G : SimpleGraph (Fin k), spectralRadius ℝ (G.adjMatrix ℝ) = ENNReal.ofReal lam
  let ι : Type := {k : ℕ | P k}
  have hdef : spectralRadiusOrder lam = ⨅ k : ι, (k.1 : ℕ∞) := by
    change (⨅ k : ℕ, ⨅ (_ : k ∈ {k' : ℕ | P k'}), (k : ℕ∞)) = ⨅ k : {k : ℕ | P k}, (k.1 : ℕ∞)
    exact iInf_subtype' (p := fun k : ℕ => P k) (f := fun k h => (k : ℕ∞))
  have hne : Nonempty ι := by
    apply (ENat.iInf_natCast_ne_top (f := fun k : ι => k.1)).mp
    rw [← hdef]
    exact ne_of_lt hk
  have hex := ENat.exists_eq_iInf (f := fun k : ι => (k.1 : ℕ∞))
  rcases hex with ⟨a, ha⟩
  have ha' : (a.1 : ℕ∞) = spectralRadiusOrder lam := ha.trans hdef.symm
  have htoNat : a.1 = (spectralRadiusOrder lam).toNat := by
    simpa [ENat.toNat_natCast] using congrArg ENat.toNat ha'
  rw [← htoNat]
  exact a.2

end Submission
