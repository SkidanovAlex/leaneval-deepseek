import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Set.Card
import Mathlib.Tactic.FinCases

namespace Commons.Combinatorics.Hypergraph

/-- Counting lemma: if a family `C` of subsets of `Fin n` each contains at least `√n/2`
points outside `Vbad`, and `C` has at least `4√n + 2` elements, then two members of `C`
share a point lying outside `Vbad`. -/
private lemma exists_pair_sharing_outside {n : ℕ} (hn : 1 ≤ n) {k : ℕ}
    (𝓗 : Set (Set (Fin n))) (Vbad : Finset (Fin n)) {B : ℝ}
    (hkB : Real.sqrt n / 2 ≤ (k : ℝ) - B)
    (C : Finset {e : Set (Fin n) // e ∈ 𝓗})
    (hCcard : 4 * Real.sqrt n + 2 ≤ (C.card : ℝ))
    (hbad : ∀ e ∈ C, (k : ℝ) - B ≤ ((e : Set (Fin n)) \ (Vbad : Set (Fin n))).ncard) :
    ∃ e ∈ C, ∃ f ∈ C, e ≠ f ∧ ∃ w, w ∈ (e : Set (Fin n)) ∧ w ∈ (f : Set (Fin n)) ∧
      w ∉ (Vbad : Set (Fin n)) := by
  classical
  by_contra hcon
  have h : ∀ e ∈ C, ∀ f ∈ C, e ≠ f → ∀ w, w ∈ (e : Set (Fin n)) → w ∈ (f : Set (Fin n)) →
      w ∈ (Vbad : Set (Fin n)) := by
    intro e he f hf hef w hwe hwf
    by_contra hw
    exact hcon ⟨e, he, f, hf, hef, w, hwe, hwf, hw⟩
  set s : {e : Set (Fin n) // e ∈ 𝓗} → Finset (Fin n) :=
    fun e => e.1.toFinite.toFinset \ Vbad with hs
  have hs_coe : ∀ e, (s e : Set (Fin n)) = e.1 \ (Vbad : Set (Fin n)) := by
    intro e
    rw [hs]
    simp only [Finset.coe_sdiff, Set.Finite.coe_toFinset]
  have hdisj : ∀ e ∈ C, ∀ f ∈ C, e ≠ f → Disjoint (s e) (s f) := by
    intro e he f hf hef
    rw [Finset.disjoint_left]
    intro x hxe hxf
    have hxe' : x ∈ e.1 \ (Vbad : Set (Fin n)) := by
      rw [← hs_coe e]; exact hxe
    have hxf' : x ∈ f.1 \ (Vbad : Set (Fin n)) := by
      rw [← hs_coe f]; exact hxf
    exact hxe'.2 (h e he f hf hef x hxe'.1 hxf'.1)
  have hcard_biUnion : (C.biUnion s).card = ∑ e ∈ C, (s e).card :=
    Finset.card_biUnion (t := s) (fun e he f hf hef => hdisj e he f hf hef)
  have hle : (∑ e ∈ C, (s e).card) ≤ n := by
    rw [← hcard_biUnion]
    simpa using Finset.card_le_univ (C.biUnion s)
  have hs_card_eq : ∀ e, (e.1 \ (Vbad : Set (Fin n))).ncard = (s e).card := by
    intro e
    rw [hs]
    rw [← Set.ncard_coe_finset (e.1.toFinite.toFinset \ Vbad)]
    congr 1
    rw [Finset.coe_sdiff, Set.Finite.coe_toFinset]
  have hsize_le : ∀ e ∈ C, Real.sqrt n / 2 ≤ ((s e).card : ℝ) := by
    intro e he
    have h1 := hbad e he
    have h3 : ((e.1 \ (Vbad : Set (Fin n))).ncard : ℝ) = ((s e).card : ℝ) := by
      rw [hs_card_eq e]
    linarith [hkB]
  have hsum_le : (∑ e ∈ C, ((s e).card : ℝ)) ≤ (n : ℝ) := by
    have h2 : ((∑ e ∈ C, (s e).card : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
    simpa using h2
  have hsum_ge : (C.card : ℝ) * (Real.sqrt n / 2) ≤ ∑ e ∈ C, ((s e).card : ℝ) := by
    have h1 : ∑ e ∈ C, (Real.sqrt n / 2 : ℝ) ≤ ∑ e ∈ C, ((s e).card : ℝ) :=
      Finset.sum_le_sum (fun e he => hsize_le e he)
    have h2 : ∑ e ∈ C, (Real.sqrt n / 2 : ℝ) = (C.card : ℝ) * (Real.sqrt n / 2) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    linarith
  have hbig : (n : ℝ) < (C.card : ℝ) * (Real.sqrt n / 2) := by
    have hsq : (Real.sqrt n)^2 = (n : ℝ) := Real.sq_sqrt (Nat.cast_nonneg n)
    have h1 : (1:ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
    nlinarith [hCcard, hsq, Real.sqrt_nonneg (n:ℝ)]
  linarith

/-- The two-vector `![a, b]` is injective when `a ≠ b`. -/
private lemma vecCons_two_injective {X : Type*} {a b : X} (hab : a ≠ b) :
    Function.Injective (![a, b] : Fin 2 → X) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all

/-- Auxiliary statement: in a family `C` of edges of size `k` each containing at least
`k - B ≥ √n/2` points outside `Vbad`, provided every pair of edges of `C` meeting outside
`Vbad` is "useful" (satisfies the counting bound), one finds `t` distinct disjoint pairs of
edges of `C`, each pair meeting and each pair "useful". -/
private theorem exists_useful_pairs_aux {n : ℕ} (𝓗 : Set (Set (Fin n))) (k : ℕ)
    (Vbad : Finset (Fin n)) {B : ℝ}
    (hkB : Real.sqrt n / 2 ≤ (k : ℝ) - B) (hn : 1 ≤ n) :
    ∀ (t : ℕ) (C : Finset {e : Set (Fin n) // e ∈ 𝓗}),
      (4 * Real.sqrt n + 2 * t ≤ (C.card : ℝ)) →
      (∀ e ∈ C, (e : Set (Fin n)).ncard = k) →
      (∀ e ∈ C, (k : ℝ) - B ≤ ((e : Set (Fin n)) \ (Vbad : Set (Fin n))).ncard) →
      (∀ e ∈ C, ∀ f ∈ C, e ≠ f →
        (∃ w ∈ (e : Set (Fin n)) ∩ (f : Set (Fin n)), w ∉ (Vbad : Set (Fin n))) →
        (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // g ≠ e ∧ g ≠ f ∧
            (g : Set (Fin n)) ∩ e ≠ (∅ : Set (Fin n)) ∧
              (g : Set (Fin n)) ∩ f ≠ (∅ : Set (Fin n))} : ℝ) ≤ (n : ℝ) - 2) →
      ∃ a : Fin t → Fin 2 → {e : Set (Fin n) // e ∈ 𝓗},
        Function.Injective (fun p : Fin t × Fin 2 => a p.1 p.2) ∧
        (∀ i : Fin t, a i 0 ∈ C ∧ a i 1 ∈ C) ∧
        (∀ i : Fin t, (((a i 0).1 : Set (Fin n)) ∩ (a i 1).1).Nonempty) ∧
        (∀ i : Fin t, (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // g ≠ a i 0 ∧ g ≠ a i 1 ∧
            (g : Set (Fin n)) ∩ (a i 0).1 ≠ (∅ : Set (Fin n)) ∧
              (g : Set (Fin n)) ∩ (a i 1).1 ≠ (∅ : Set (Fin n))} : ℝ) ≤ (n : ℝ) - 2) := by
  intro t
  induction t with
  | zero =>
    intro C _ _ _ _
    exact ⟨fun i => Fin.elim0 i, (fun p => p.1.elim0), (fun i => i.elim0),
      (fun i => i.elim0), (fun i => i.elim0)⟩
  | succ t ih =>
    classical
    intro C hCcard hsize hbad hcrit
    have hcard2 : 4 * Real.sqrt n + 2 ≤ (C.card : ℝ) := by
      have hcast : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by rw [Nat.cast_add, Nat.cast_one]
      have ht : (0:ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
      linarith [hCcard, hcast, ht]
    obtain ⟨e0, he0C, f0, hf0C, he0f0, w, hwe0, hwf0, hwbad⟩ :=
      exists_pair_sharing_outside hn 𝓗 Vbad hkB C hcard2 hbad
    have hcrit_ef : (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // g ≠ e0 ∧ g ≠ f0 ∧
        (g : Set (Fin n)) ∩ e0 ≠ (∅ : Set (Fin n)) ∧
          (g : Set (Fin n)) ∩ f0 ≠ (∅ : Set (Fin n))} : ℝ) ≤ (n : ℝ) - 2 :=
      hcrit e0 he0C f0 hf0C he0f0 ⟨w, ⟨hwe0, hwf0⟩, hwbad⟩
    set C' : Finset {e : Set (Fin n) // e ∈ 𝓗} := (C.erase e0).erase f0 with hC'def
    have hmem1 : f0 ∈ C.erase e0 := Finset.mem_erase.mpr ⟨fun hh => he0f0 hh.symm, hf0C⟩
    have hcard' : C'.card + 2 = C.card := by
      have h1 := Finset.card_erase_add_one hmem1
      have h2 := Finset.card_erase_add_one he0C
      rw [hC'def]
      omega
    have hC'card : 4 * Real.sqrt n + 2 * (t : ℝ) ≤ (C'.card : ℝ) := by
      have h2 : (C'.card : ℝ) + 2 = (C.card : ℝ) := by exact_mod_cast hcard'
      have h3 : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by rw [Nat.cast_add, Nat.cast_one]
      linarith [hCcard, h2, h3]
    have hsize' : ∀ e ∈ C', (e : Set (Fin n)).ncard = k := by
      intro e he
      rw [hC'def] at he
      exact hsize e (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he))
    have hbad' : ∀ e ∈ C', (k : ℝ) - B ≤
        ((e : Set (Fin n)) \ (Vbad : Set (Fin n))).ncard := by
      intro e he
      rw [hC'def] at he
      exact hbad e (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he))
    have hC'sub : ∀ e ∈ C', e ∈ C := by
      intro e he
      rw [hC'def] at he
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he)
    have hcrit' : ∀ e ∈ C', ∀ f ∈ C', e ≠ f →
        (∃ w ∈ (e : Set (Fin n)) ∩ (f : Set (Fin n)), w ∉ (Vbad : Set (Fin n))) →
        (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // g ≠ e ∧ g ≠ f ∧
            (g : Set (Fin n)) ∩ e ≠ (∅ : Set (Fin n)) ∧
              (g : Set (Fin n)) ∩ f ≠ (∅ : Set (Fin n))} : ℝ) ≤ (n : ℝ) - 2 := by
      intro e he f hf hef
      rw [hC'def] at he hf
      exact hcrit e (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase he)) f
        (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hf)) hef
    obtain ⟨a', hinj', hmem', hmeet', hcnt'⟩ := ih C' hC'card hsize' hbad' hcrit'
    set a : Fin (t+1) → Fin 2 → {e : Set (Fin n) // e ∈ 𝓗} :=
      Fin.cons (![e0, f0] : Fin 2 → {e : Set (Fin n) // e ∈ 𝓗}) (fun i' => a' i') with ha_def
    have ha_zero : ∀ j : Fin 2, a 0 j = ![e0, f0] j := by
      intro j; rw [ha_def]; simp
    have ha_succ : ∀ (i' : Fin t) (j : Fin 2), a i'.succ j = a' i' j := by
      intro i' j; rw [ha_def]; simp
    have ha_notmem : ∀ j : Fin 2, a 0 j ∉ C' := by
      intro j
      rw [ha_zero j]
      fin_cases j
      · rw [hC'def]; simp
      · rw [hC'def]; simp
    refine ⟨a, ?_, ?_, ?_, ?_⟩
    · intro p q hpq
      obtain ⟨i, j⟩ := p
      obtain ⟨i', j'⟩ := q
      change a i j = a i' j' at hpq
      by_cases hi : i = 0
      · subst hi
        by_cases hi' : i' = 0
        · subst hi'
          have hpq' : (![e0, f0] : Fin 2 → {e : Set (Fin n) // e ∈ 𝓗}) j = ![e0, f0] j' := by
            rw [ha_zero j, ha_zero j'] at hpq
            exact hpq
          have hjj : j = j' := vecCons_two_injective he0f0 hpq'
          subst hjj
          rfl
        · exfalso
          obtain ⟨i'', hi''⟩ := Fin.exists_succ_eq_of_ne_zero hi'
          subst hi''
          rw [ha_succ i'' j'] at hpq
          have hnm := ha_notmem j
          rw [hpq] at hnm
          rcases hmem' i'' with ⟨h0, h1⟩
          fin_cases j'
          · exact hnm h0
          · exact hnm h1
      · by_cases hi' : i' = 0
        · exfalso
          subst hi'
          obtain ⟨i'', hi''⟩ := Fin.exists_succ_eq_of_ne_zero hi
          subst hi''
          rw [ha_succ i'' j] at hpq
          have hnm := ha_notmem j'
          rw [← hpq] at hnm
          rcases hmem' i'' with ⟨h0, h1⟩
          fin_cases j
          · exact hnm h0
          · exact hnm h1
        · obtain ⟨i'', hi''⟩ := Fin.exists_succ_eq_of_ne_zero hi
          obtain ⟨i''', hi'''⟩ := Fin.exists_succ_eq_of_ne_zero hi'
          subst hi''
          subst hi'''
          rw [ha_succ i'' j, ha_succ i''' j'] at hpq
          have h2 : (i'', j) = (i''', j') := hinj' hpq
          have hi2 : i'' = i''' := congrArg Prod.fst h2
          have hj2 : j = j' := congrArg Prod.snd h2
          subst hi2
          subst hj2
          rfl
    · intro i
      by_cases hi : i = 0
      · subst hi
        have h0 : a 0 0 = e0 := by rw [ha_zero 0]; simp
        have h1 : a 0 1 = f0 := by rw [ha_zero 1]; simp
        rw [h0, h1]
        exact ⟨he0C, hf0C⟩
      · obtain ⟨i'', hi''⟩ := Fin.exists_succ_eq_of_ne_zero hi
        subst hi''
        simp only [ha_succ]
        rcases hmem' i'' with ⟨h0, h1⟩
        exact ⟨hC'sub _ h0, hC'sub _ h1⟩
    · intro i
      by_cases hi : i = 0
      · subst hi
        have h0 : a 0 0 = e0 := by rw [ha_zero 0]; simp
        have h1 : a 0 1 = f0 := by rw [ha_zero 1]; simp
        rw [h0, h1]
        exact ⟨w, hwe0, hwf0⟩
      · obtain ⟨i'', hi''⟩ := Fin.exists_succ_eq_of_ne_zero hi
        subst hi''
        simp only [ha_succ]
        exact hmeet' i''
    · intro i
      by_cases hi : i = 0
      · subst hi
        have h0 : a 0 0 = e0 := by rw [ha_zero 0]; simp
        have h1 : a 0 1 = f0 := by rw [ha_zero 1]; simp
        rw [h0, h1]
        exact hcrit_ef
      · obtain ⟨i'', hi''⟩ := Fin.exists_succ_eq_of_ne_zero hi
        subst hi''
        simp only [ha_succ]
        exact hcnt' i''

theorem exists_useful_pairs_in_clique {n : ℕ} (𝓗 : Set (Set (Fin n))) (k t : ℕ)
    (Vbad : Finset (Fin n)) {δ B : ℝ}
    (hB : Real.sqrt (δ * n) ≤ B) (hkB : Real.sqrt n / 2 ≤ (k : ℝ) - B)
    (hδ : 0 < δ) (hn : 1 ≤ n)
    (C : Finset {e : Set (Fin n) // e ∈ 𝓗})
    (hCcard : 4 * Real.sqrt n + 2 * t ≤ (C.card : ℝ))
    (hsize : ∀ e ∈ C, (e : Set (Fin n)).ncard = k)
    (hbad : ∀ e ∈ C, (k : ℝ) - B ≤ ((e : Set (Fin n)) \ (Vbad : Set (Fin n))).ncard)
    (hcrit : ∀ e ∈ C, ∀ f ∈ C, e ≠ f →
      (∃ w ∈ (e : Set (Fin n)) ∩ (f : Set (Fin n)), w ∉ (Vbad : Set (Fin n))) →
      (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // g ≠ e ∧ g ≠ f ∧
          (g : Set (Fin n)) ∩ e ≠ (∅ : Set (Fin n)) ∧
            (g : Set (Fin n)) ∩ f ≠ (∅ : Set (Fin n))} : ℝ) ≤ (n : ℝ) - 2) :
    ∃ a : Fin t → Fin 2 → {e : Set (Fin n) // e ∈ 𝓗},
      Function.Injective (fun p : Fin t × Fin 2 => a p.1 p.2) ∧
      (∀ i : Fin t, a i 0 ∈ C ∧ a i 1 ∈ C) ∧
      (∀ i : Fin t, (((a i 0).1 : Set (Fin n)) ∩ (a i 1).1).Nonempty) ∧
      (∀ i : Fin t, (Nat.card {g : {g : Set (Fin n) // g ∈ 𝓗} // g ≠ a i 0 ∧ g ≠ a i 1 ∧
          (g : Set (Fin n)) ∩ (a i 0).1 ≠ (∅ : Set (Fin n)) ∧
            (g : Set (Fin n)) ∩ (a i 1).1 ≠ (∅ : Set (Fin n))} : ℝ) ≤ (n : ℝ) - 2) := by
  exact exists_useful_pairs_aux 𝓗 k Vbad hkB hn t C hCcard hsize hbad hcrit

end Commons.Combinatorics.Hypergraph
