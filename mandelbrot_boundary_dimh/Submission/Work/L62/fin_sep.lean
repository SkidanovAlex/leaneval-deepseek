import Mathlib

namespace Work.L62

open Complex

/-- **Separation from `ℤ` in `ℂ`.**  A complex number which is not an integer has a positive
distance from `ℤ`. -/
private lemma exists_sep_of_not_mem_int {x : ℂ} (hx : ∀ k : ℤ, x ≠ (k : ℂ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℤ, δ ≤ ‖x - (k : ℂ)‖ := by
  -- `ℤ ↪ ℂ` is a closed embedding, so its range is closed; the conclusion then follows from
  -- the metric characterisation of the closure.
  have hS : IsClosed (Set.range (fun k : ℤ => (k : ℂ))) :=
    Complex.isClosedEmbedding_intCast.isClosed_range
  have hxS : x ∉ Set.range (fun k : ℤ => (k : ℂ)) := by
    rintro ⟨k, hk⟩
    exact hx k hk.symm
  have hnotcl : x ∉ closure (Set.range (fun k : ℤ => (k : ℂ))) := by
    rwa [hS.closure_eq]
  rw [Metric.mem_closure_iff] at hnotcl
  simp only [not_forall, not_exists] at hnotcl
  obtain ⟨ε, hε, hε'⟩ := hnotcl
  refine ⟨ε, hε, fun k => ?_⟩
  have h1 : ¬ dist x ((k : ℂ)) < ε := fun hlt => hε' (k : ℂ) ⟨⟨k, rfl⟩, hlt⟩
  have h2 : ε ≤ dist x ((k : ℂ)) := le_of_not_gt h1
  rwa [dist_eq_norm] at h2

/-- **Finite separation.**  If finitely many complex numbers `z i` (`i ≤ J`) are such that no
difference `z i - z j` (`i ≠ j`) is an integer, then there is a uniform positive lower bound
for the distance of all such differences from `ℤ`. -/
theorem fin_sep {z : ℕ → ℂ} {J : ℕ}
    (hsep : ∀ i j : ℕ, i ≤ J → j ≤ J → i ≠ j → ∀ k : ℤ, z i ≠ z j + (k : ℂ)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i j : ℕ, i ≤ J → j ≤ J → i ≠ j → ∀ k : ℤ,
      ε ≤ ‖z i - z j - (k : ℂ)‖ := by
  classical
  -- the finite set of relevant pairs of indices
  set S : Finset (ℕ × ℕ) :=
    ((Finset.range (J + 1)) ×ˢ (Finset.range (J + 1))).filter (fun p => p.1 ≠ p.2) with hSdef
  -- each pair admits its own positive separation
  have hpair : ∀ p ∈ S, ∃ δ : ℝ, 0 < δ ∧ ∀ k : ℤ, δ ≤ ‖z p.1 - z p.2 - (k : ℂ)‖ := by
    intro p hp
    rw [hSdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
    obtain ⟨⟨hi, hj⟩, hij⟩ := hp
    exact exists_sep_of_not_mem_int (fun k hk => by
      have hk' : z p.1 = z p.2 + (k : ℂ) := by
        rw [sub_eq_iff_eq_add'] at hk; exact hk
      exact hsep p.1 p.2 (Nat.lt_succ_iff.mp hi) (Nat.lt_succ_iff.mp hj) hij k hk')
  -- pick one such separation for every pair
  let g : ℕ × ℕ → ℝ := fun p => if hp : p ∈ S then Classical.choose (hpair p hp) else 1
  have hgpos : ∀ p ∈ S, 0 < g p := by
    intro p hp
    show 0 < (if hp' : p ∈ S then Classical.choose (hpair p hp') else 1)
    rw [dite_eq_left hp]
    exact (hpair p hp).choose_spec.1
  -- the (nonempty) finite set of candidate values, with `1` adjoined so that it is never empty
  let V : Finset ℝ := insert 1 (S.image g)
  have hVne : V.Nonempty := ⟨1, Finset.mem_insert_self 1 (S.image g)⟩
  have hε_le_g : ∀ p ∈ S, V.inf' hVne id ≤ g p := fun p hp =>
    Finset.inf'_le (s := V) id (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p, hp, rfl⟩))
  have hε_pos : 0 < V.inf' hVne id := by
    rw [Finset.lt_inf'_iff hVne]
    intro b hb
    change 0 < b
    rcases Finset.mem_insert.mp hb with hb1 | hb2
    · rw [hb1]; norm_num
    · rcases Finset.mem_image.mp hb2 with ⟨p, hp, rfl⟩
      exact hgpos p hp
  refine ⟨V.inf' hVne id, hε_pos, ?_⟩
  intro i j hi hj hij k
  have hmem : (i, j) ∈ S := by
    rw [hSdef, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨Nat.lt_succ_of_le hi, Nat.lt_succ_of_le hj⟩, hij⟩
  have hgle : g (i, j) ≤ ‖z i - z j - (k : ℂ)‖ := by
    show (if hp : (i, j) ∈ S then Classical.choose (hpair (i, j) hp) else 1)
        ≤ ‖z i - z j - (k : ℂ)‖
    rw [dite_eq_left hmem]
    exact (hpair (i, j) hmem).choose_spec.2 k
  exact le_trans (hε_le_g (i, j) hmem) hgle

end Work.L62
