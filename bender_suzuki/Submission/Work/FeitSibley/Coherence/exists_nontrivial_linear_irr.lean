import Mathlib
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# A nontrivial nilpotent group has a nontrivial linear character

A finite nilpotent group `Q` is solvable, and a nontrivial solvable group has a proper
commutator subgroup; equivalently, its abelianisation `Q ⧸ [Q, Q]` is nontrivial.  Since the
number of irreducible complex characters of degree one equals the order of the abelianisation
(`Work.CharCore.card_irr_deg_one`), a nontrivial finite nilpotent group has at least two
degree-one irreducible characters, and the second one is a nontrivial **linear** character:
it is irreducible, has degree `1`, and is not the trivial character.

The main result is `Work.FeitSibley.Coherence.exists_nontrivial_linear_irr`.
-/

namespace Work.FeitSibley.Coherence

open Work.CharCore

/-- **The commutator subgroup of a nontrivial nilpotent group is proper.**

If `[Q, Q] = Q` then the lower central series is constant `⊤` (by induction from
`Subgroup.lowerCentralSeries_succ`), contradicting the vanishing of the lower central series
that characterises nilpotency (`Subgroup.nilpotent_iff_lowerCentralSeries`). -/
theorem commutator_ne_top_of_isNilpotent_of_nontrivial (Q : Type) [Group Q]
    [Group.IsNilpotent Q] [Nontrivial Q] : commutator Q ≠ ⊤ := by
  intro h
  obtain ⟨n, hn⟩ :=
    (Subgroup.nilpotent_iff_lowerCentralSeries (G := Q)).mp ‹Group.IsNilpotent Q›
  have hall : ∀ k, (⊤ : Subgroup Q).lowerCentralSeries k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Subgroup.lowerCentralSeries_succ, ih]
        exact h
  rw [hall n] at hn
  exact absurd hn top_ne_bot

/-- **A nontrivial finite nilpotent group has a nontrivial irreducible linear character.**

The abelianisation `Q ⧸ [Q, Q]` is nontrivial, so the set of degree-one irreducible characters
of `Q` — whose cardinality is the order of the abelianisation — has at least two elements.
It contains the trivial character, so it contains a further one, and any such character has
value `1` at the identity and is different from the trivial character. -/
theorem exists_nontrivial_linear_irr (Q : Type) [Group Q] [Fintype Q] [Group.IsNilpotent Q]
    [Nontrivial Q] :
    ∃ theta ∈ Work.CharCore.Irr Q, theta 1 = 1 ∧ theta ≠ (fun _ : Q => (1 : ℂ)) := by
  classical
  -- The abelianisation is nontrivial, hence the set of degree-one irreducible characters of `Q`
  -- has at least two elements.
  have hc : commutator Q ≠ ⊤ := commutator_ne_top_of_isNilpotent_of_nontrivial Q
  have hntq : Nontrivial (Q ⧸ commutator Q) := QuotientGroup.nontrivial_iff.mpr hc
  have hcard2 : 2 ≤ Nat.card (Q ⧸ commutator Q) := by
    have := Finite.one_lt_card (α := Q ⧸ commutator Q)
    omega
  have hfilt : ((Irr Q).filter (fun χ => irrDeg χ = 1)).card = Nat.card (Q ⧸ commutator Q) :=
    Work.CharCore.card_irr_deg_one
  -- The trivial character is one of them.
  have htriv : (fun _ : Q => (1 : ℂ)) ∈ (Irr Q).filter (fun χ => irrDeg χ = 1) := by
    refine Finset.mem_filter.mpr ⟨Work.CharCore.principalChar_mem_Irr, ?_⟩
    have h := Work.CharCore.irrDeg_spec (G := Q) (Work.CharCore.principalChar_mem_Irr (G := Q))
    have h1 : ((irrDeg (fun _ : Q => (1 : ℂ))) : ℂ) = 1 := h.symm
    exact_mod_cast h1
  -- So there is another one, and it is the desired nontrivial linear character.
  have herase :
      0 < (((Irr Q).filter (fun χ => irrDeg χ = 1)).erase (fun _ : Q => (1 : ℂ))).card := by
    rw [Finset.card_erase_of_mem htriv]
    omega
  obtain ⟨θ, hθerase⟩ := Finset.card_pos.mp herase
  have hθmem : θ ∈ (Irr Q).filter (fun χ => irrDeg χ = 1) := Finset.mem_of_mem_erase hθerase
  have hθne : θ ≠ (fun _ : Q => (1 : ℂ)) := Finset.ne_of_mem_erase hθerase
  refine ⟨θ, (Finset.mem_filter.mp hθmem).1, ?_, hθne⟩
  have hdeg : irrDeg θ = 1 := (Finset.mem_filter.mp hθmem).2
  rw [Work.CharCore.irrDeg_spec (Finset.mem_filter.mp hθmem).1, hdeg]
  norm_num

end Work.FeitSibley.Coherence
