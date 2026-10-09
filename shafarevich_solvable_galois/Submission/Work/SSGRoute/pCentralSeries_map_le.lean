import Mathlib
import Submission.Work.Shrinking.PCentral
import Submission.Work.Shrinking.map_pCentralSeries_surjective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-! ## Elementary monotonicity/naturality helpers for the `p`-central series step -/

namespace pCentralSeriesMapAux

/-- Images of `p`-th power subgroups: `(H^p).map f ≤ (H.map f)^p` (equality holds, but only
the inequality is needed). -/
theorem powSubgroup_map_le {P Q : Type*} [Group P] [Group Q] (p : ℕ) (ψ : P →* Q)
    (H : Subgroup P) :
    (Work.Shrinking.powSubgroup p H).map ψ ≤ Work.Shrinking.powSubgroup p (H.map ψ) := by
  unfold Work.Shrinking.powSubgroup
  rw [MonoidHom.map_closure]
  refine Subgroup.closure_mono ?_
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨z, hz, rfl⟩ := hx
  exact ⟨ψ z, Subgroup.mem_map_of_mem ψ hz, by rw [map_pow]⟩

/-- `H ↦ H^p` is monotone. -/
theorem powSubgroup_mono {P : Type*} [Group P] (p : ℕ) {H K : Subgroup P}
    (h : H ≤ K) : Work.Shrinking.powSubgroup p H ≤ Work.Shrinking.powSubgroup p K := by
  unfold Work.Shrinking.powSubgroup
  exact Subgroup.closure_mono (Set.image_mono h)

/-- `(⁅H, ⊤⁆).map f ≤ ⁅H.map f, ⊤⁆`. -/
theorem map_commutator_top_le {P Q : Type*} [Group P] [Group Q] (ψ : P →* Q)
    (H : Subgroup P) : (⁅H, ⊤⁆ : Subgroup P).map ψ ≤ ⁅H.map ψ, ⊤⁆ := by
  rw [Subgroup.map_commutator]
  exact Subgroup.commutator_mono le_rfl le_top

end pCentralSeriesMapAux

/-- The descending `p`-central series is functorial for *arbitrary* homomorphisms: the image
of the `n`-th term is contained in the `n`-th term of the target.

Induction on `n`.  For `n = 0` both sides are `⊤`.  In the step
`pCentralSeries p P (n+1) = (P_n)^p ⊔ ⁅P_n, ⊤⁆`, `Subgroup.map_sup` splits the image of the
supremum, `pCentralSeriesMapAux.powSubgroup_map_le` computes `(H^p).map f ≤ (H.map f)^p`, and
`pCentralSeriesMapAux.map_commutator_top_le` handles the commutator; monotonicity
(`pCentralSeriesMapAux.powSubgroup_mono`, `Subgroup.commutator_mono`) together with the
induction hypothesis finishes. -/
theorem pCentralSeries_map_le {P Q : Type*} [Group P] [Group Q] (p : ℕ) (f : P →* Q) (n : ℕ) :
    (Work.Shrinking.pCentralSeries p P n).map f ≤ Work.Shrinking.pCentralSeries p Q n := by
  induction n with
  | zero =>
    rw [Work.Shrinking.pCentralSeries_zero, Work.Shrinking.pCentralSeries_zero]
    exact le_top
  | succ n ih =>
    rw [Work.Shrinking.pCentralSeries_succ, Work.Shrinking.pCentralSeries_succ,
      Work.Shrinking.pCentralStep, Work.Shrinking.pCentralStep, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · exact (pCentralSeriesMapAux.powSubgroup_map_le p f (Work.Shrinking.pCentralSeries p P n)).trans
        ((pCentralSeriesMapAux.powSubgroup_mono p ih).trans le_sup_left)
    · exact (pCentralSeriesMapAux.map_commutator_top_le f (Work.Shrinking.pCentralSeries p P n)).trans
        ((Subgroup.commutator_mono ih le_rfl).trans le_sup_right)

end Work.SSGRoute
