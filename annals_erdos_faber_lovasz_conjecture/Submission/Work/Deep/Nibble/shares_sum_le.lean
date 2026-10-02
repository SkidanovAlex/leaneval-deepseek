import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.r2_var_aux

/-!
# The number of vertices sharing an edge with a fixed vertex is at most `(r-1) · d(u)`

`Work.Deep.Nibble.shares_sum_le`: for a family `𝓖` of `r`-element subsets of a finite
vertex set `V` and a vertex `u`,

`∑_{v ≠ u} 1[some edge of 𝓖 contains both u and v] ≤ (r - 1) · d_𝓖(u)`,

where `d_𝓖(u) = hd 𝓖 u` is the number of edges of `𝓖` through `u`.

The proof is the union bound: the vertices `v ≠ u` sharing an edge with `u` are covered
by the sets `e \ {u}`, `e` ranging over the edges through `u`; each of these has exactly
`r - 1` elements, so

`|{v} | ≤ |⋃_e (e \ {u})| ≤ ∑_e |e \ {u}| = d_𝓖(u) · (r - 1)`.

(Linearity of `𝓖` is not needed for this inequality: it would make it an equality.)
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.Deep.Nibble

theorem shares_sum_le {V : Type*} [Fintype V] [DecidableEq V] (𝓖 : Set (Set V)) {r : ℕ}
    (hlin : Work.Deep.Nibble.HLin 𝓖) (huni : Work.Deep.Nibble.HUnif 𝓖 r) (u : V) :
    (∑ v ∈ Finset.univ.erase u, (if ((Work.Deep.Nibble.thruF 𝓖 u)
        ∩ (Work.Deep.Nibble.thruF 𝓖 v)).Nonempty then (1 : ℝ) else 0))
      ≤ ((r : ℝ) - 1) * (Work.Deep.Nibble.hd 𝓖 u : ℝ) := by
  classical
  -- The sum of indicators is the number of vertices `v ≠ u` meeting an edge through `u`.
  have hsum_eq : (∑ v ∈ Finset.univ.erase u,
        (if ((thruF 𝓖 u) ∩ (thruF 𝓖 v)).Nonempty then (1 : ℝ) else 0))
      = (((Finset.univ.erase u).filter
          (fun v => ((thruF 𝓖 u) ∩ (thruF 𝓖 v)).Nonempty)).card : ℝ) := by
    rw [← Finset.sum_filter]
    simp
  -- The combinatorial bound, at the level of `ℕ`.
  have hnat : ((Finset.univ.erase u).filter
      (fun v => ((thruF 𝓖 u) ∩ (thruF 𝓖 v)).Nonempty)).card ≤ (r - 1) * hd 𝓖 u := by
    calc ((Finset.univ.erase u).filter
            (fun v => ((thruF 𝓖 u) ∩ (thruF 𝓖 v)).Nonempty)).card
        -- every such `v` lies in `e \ {u}` for some edge `e` through `u`
        ≤ ((thruF 𝓖 u).biUnion
            (fun e => (Finset.univ.erase u).filter (fun v => v ∈ (e : Set V)))).card := by
          apply Finset.card_le_card
          intro v hv
          rw [Finset.mem_filter] at hv
          obtain ⟨hvu, e, he⟩ := hv
          have he1 : e ∈ thruF 𝓖 u := (Finset.mem_inter.mp he).1
          have he2 : e ∈ thruF 𝓖 v := (Finset.mem_inter.mp he).2
          rw [Finset.mem_biUnion]
          refine ⟨e, he1, ?_⟩
          rw [Finset.mem_filter]
          exact ⟨hvu, (mem_thruF 𝓖).mp he2⟩
        -- union bound
      _ ≤ ∑ e ∈ thruF 𝓖 u,
            ((Finset.univ.erase u).filter (fun v => v ∈ (e : Set V))).card :=
          Finset.card_biUnion_le
        -- each edge through `u` contributes exactly `r - 1` vertices
      _ ≤ ∑ _e ∈ thruF 𝓖 u, (r - 1) := by
          apply Finset.sum_le_sum
          intro e he
          have hue : u ∈ (e : Set V) := (mem_thruF 𝓖).mp he
          have hfe : (Finset.univ.erase u).filter (fun v => v ∈ (e : Set V))
              = (Finset.univ.filter (fun v => v ∈ (e : Set V))).erase u := by
            ext v
            simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and,
              and_true]
          have hcard : (Finset.univ.filter (fun v => v ∈ (e : Set V))).card
              = ((e : Set V)).ncard := by
            rw [← natCard_setOf_eq_filter_card (fun v : V => v ∈ (e : Set V))]
            rfl
          rw [hfe, Finset.card_erase_of_mem (by simp [hue]), hcard, huni (e : Set V) e.2]
      _ = (r - 1) * hd 𝓖 u := by
          rw [Finset.sum_const_nat (s := thruF 𝓖 u) (m := r - 1)
                (f := fun _ => r - 1) (fun _ _ => rfl),
              hd_eq_card_thruF]
          exact Nat.mul_comm _ _
  rw [hsum_eq]
  by_cases hd0 : hd 𝓖 u = 0
  · -- no edge passes through `u`: both sides vanish
    have hle := hnat
    rw [hd0, mul_zero] at hle
    rw [hd0, Nat.cast_zero, mul_zero]
    exact_mod_cast hle
  · -- otherwise `u` lies in an edge, so `1 ≤ r` and the cast of `r - 1` is `(r : ℝ) - 1`
    have hr1 : 1 ≤ r := by
      have hpos : 0 < (thruF 𝓖 u).card := by
        rw [← hd_eq_card_thruF]
        exact Nat.pos_of_ne_zero hd0
      obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
      have hue : u ∈ (e : Set V) := by simpa using he
      have hlt : 0 < ((e : Set V)).ncard := (Set.ncard_pos (s := (e : Set V))).mpr ⟨u, hue⟩
      rw [huni (e : Set V) e.2] at hlt
      exact hlt
    calc (((Finset.univ.erase u).filter
            (fun v => ((thruF 𝓖 u) ∩ (thruF 𝓖 v)).Nonempty)).card : ℝ)
        ≤ (((r - 1) * hd 𝓖 u : ℕ) : ℝ) := by exact_mod_cast hnat
      _ = ((r : ℝ) - 1) * (hd 𝓖 u : ℝ) := by
          rw [Nat.cast_mul, Nat.cast_sub hr1, Nat.cast_one]

end Work.Deep.Nibble
