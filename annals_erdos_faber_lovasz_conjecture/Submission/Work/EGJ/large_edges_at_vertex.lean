import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Work.EGJ

set_option autoImplicit false

/-- **Counting the large edges through a vertex.**  For a linear edge family `𝓗` on `Fin n` (two
distinct members meet in at most one vertex), the number of edges through `w` of size `> r₀`
satisfies `|{e ∈ 𝓗 | w ∈ e, |e| > r₀}| · r₀ ≤ n - 1`: any two such edges meet exactly in `w`, so
the parts `e ∖ {w}` are pairwise disjoint subsets of `Fin n ∖ {w}` and each has at least `r₀`
elements.  (In §12 of the Erdős–Faber–Lovász paper this is what bounds the number of main
colour classes covering a vertex — the singleton case `e = {w}` of the Nibble Lemma's C4
interaction condition, which `card_cmain_meeting_le` (Claim 12.1 (EP2)) does not cover because
the large edges through `w` all share `w`.) -/
theorem large_edges_at_vertex {n : ℕ} (𝓗 : Set (Set (Fin n)))
    (hlin : 𝓗.Pairwise fun e e' => (e ∩ e').Subsingleton) {r₀ : ℕ} (hr₀ : 1 ≤ r₀) (w : Fin n) :
    (({e ∈ 𝓗 | w ∈ e ∧ r₀ < e.ncard} : Set (Set (Fin n))).ncard : ℝ) * (r₀ : ℝ)
      ≤ ((n : ℝ) - 1) := by
  -- The hypothesis `hr₀ : 1 ≤ r₀` is not needed for the counting argument below (which is
  -- valid for `r₀ = 0` as well); it is part of the fixed interface, so we record it here.
  have _hr₀ : 1 ≤ r₀ := hr₀
  classical
  -- `E` is the set of edges of `𝓗` through `w` with more than `r₀` vertices.
  set E : Set (Set (Fin n)) := {e ∈ 𝓗 | w ∈ e ∧ r₀ < e.ncard} with hE
  have hEfin : E.Finite := Set.toFinite E
  have hmem : ∀ e, e ∈ E ↔ e ∈ 𝓗 ∧ w ∈ e ∧ r₀ < e.ncard := by
    intro e; rw [hE]; rfl
  -- Each edge of `E` gives the part `e \ {w}`, a finset; its cardinality is `(e \ {w}).ncard`.
  have hpart_card : ∀ e : Set (Fin n),
      ((Set.toFinite (e \ {w})).toFinset).card = (e \ {w}).ncard := by
    intro e
    rw [← Set.ncard_coe_finset, Set.Finite.coe_toFinset]
  have hpart_coe : ∀ e : Set (Fin n),
      ((↑((Set.toFinite (e \ {w})).toFinset) : Set (Fin n))) = e \ {w} :=
    fun e => Set.Finite.coe_toFinset _
  -- Each part has at least `r₀` elements.
  have hle_size : ∀ e ∈ E, r₀ ≤ (e \ {w}).ncard := by
    intro e he
    obtain ⟨_, hwe, hlt⟩ := (hmem e).mp he
    rw [Set.ncard_sdiff_singleton_of_mem hwe]
    omega
  -- Two distinct edges of `E` meet exactly in `w`, so the parts are pairwise disjoint.
  have hdisj : (↑hEfin.toFinset : Set (Set (Fin n))).PairwiseDisjoint
      fun e => (Set.toFinite (e \ {w})).toFinset := by
    intro a ha b hb hab
    simp only [Function.onFun]
    have ha' : a ∈ E := (Set.Finite.mem_toFinset hEfin).mp ha
    have hb' : b ∈ E := (Set.Finite.mem_toFinset hEfin).mp hb
    obtain ⟨ha𝓗, hwa, -⟩ := (hmem a).mp ha'
    obtain ⟨hb𝓗, hwb, -⟩ := (hmem b).mp hb'
    have habs : a ∩ b = {w} := (hlin ha𝓗 hb𝓗 hab).eq_singleton_of_mem ⟨hwa, hwb⟩
    rw [← Finset.disjoint_coe, hpart_coe a, hpart_coe b, Set.disjoint_iff_inter_eq_empty,
      Set.eq_empty_iff_forall_notMem]
    rintro v ⟨⟨hva, hvw⟩, hvb, -⟩
    have hvab : v ∈ a ∩ b := ⟨hva, hvb⟩
    rw [habs, Set.mem_singleton_iff] at hvab
    exact hvw hvab
  -- Disjoint union: the cardinality of the union is the sum of the cardinalities of the parts.
  have hcard_biUnion : ((hEfin.toFinset.biUnion fun e => (Set.toFinite (e \ {w})).toFinset)).card
      = ∑ e ∈ hEfin.toFinset, ((Set.toFinite (e \ {w})).toFinset).card :=
    Finset.card_biUnion hdisj
  -- The union is contained in `Fin n \ {w}`.
  have hsub : (hEfin.toFinset.biUnion fun e => (Set.toFinite (e \ {w})).toFinset)
      ⊆ Finset.univ.erase w := by
    intro v hv
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ v⟩
    rw [Finset.mem_biUnion] at hv
    obtain ⟨e, -, hve⟩ := hv
    have hve' : v ∈ ((↑((Set.toFinite (e \ {w})).toFinset) : Set (Fin n))) := hve
    rw [hpart_coe e] at hve'
    exact hve'.2
  have hub : ((hEfin.toFinset.biUnion fun e => (Set.toFinite (e \ {w})).toFinset)).card ≤ n - 1 := by
    calc _ ≤ (Finset.univ.erase w).card := Finset.card_le_card hsub
      _ = n - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ w), Finset.card_univ, Fintype.card_fin]
  -- The arithmetic core: `|E| * r₀ ≤ n - 1`.
  have key : E.ncard * r₀ ≤ n - 1 := by
    rw [Set.ncard_eq_toFinset_card E hEfin]
    calc hEfin.toFinset.card * r₀
        = ∑ e ∈ hEfin.toFinset, r₀ :=
            (Finset.sum_const_nat (s := hEfin.toFinset) (m := r₀) fun _ _ => rfl).symm
      _ ≤ ∑ e ∈ hEfin.toFinset, ((Set.toFinite (e \ {w})).toFinset).card :=
            Finset.sum_le_sum fun e he => by
              rw [hpart_card e]
              exact hle_size e ((Set.Finite.mem_toFinset hEfin).mp he)
      _ = ((hEfin.toFinset.biUnion fun e => (Set.toFinite (e \ {w})).toFinset)).card :=
            hcard_biUnion.symm
      _ ≤ n - 1 := hub
  -- Transport to `ℝ`.  Note `n ≠ 0` because `w : Fin n`.
  have hn1 : 1 ≤ n := by
    have h : 0 < n := Fin.pos_iff_nonempty.mpr ⟨w⟩
    omega
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1]; norm_num
  have hfin : ((E.ncard : ℕ) : ℝ) * (r₀ : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast key
  rwa [hcast] at hfin

end Work.EGJ
