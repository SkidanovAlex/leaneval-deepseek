import Mathlib
import Submission.Work.WilE5.Pairwise

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilE5.Pairwise

open WilkiesDesign WilkiesDesign.E

/-- Induction principle for `Work.WilE5.uniqSets`, following its recursion.
(Strong induction on the length of the list: the recursive call is made on the filtered tail,
which is strictly shorter.) -/
theorem uniqSets_induct {p q : ℕ} {motive : List (Stratum p q) → Prop}
    (nil : motive [])
    (cons : ∀ S rest, motive (rest.filter fun T => T.X.set ≠ S.X.set) → motive (S :: rest)) :
    ∀ L, motive L := by
  have key : ∀ n, ∀ L : List (Stratum p q), L.length ≤ n → motive L := by
    intro n
    induction n with
    | zero =>
      intro L hL
      match L with
      | [] => exact nil
      | S :: rest => exact absurd hL (by simp only [List.length_cons]; omega)
    | succ n ih =>
      intro L hL
      match L with
      | [] => exact nil
      | S :: rest =>
        refine cons S rest (ih _ ?_)
        have h1 : (List.filter (fun T : Stratum p q => decide (T.X.set ≠ S.X.set)) rest).length ≤
            rest.length := List.length_filter_le _ _
        simp only [List.length_cons] at hL
        omega
  intro L
  exact key L.length L le_rfl

/-- Every entry of `uniqSets L` is an entry of `L`. -/
theorem mem_uniqSets {p q : ℕ} {L : List (Stratum p q)} {S : Stratum p q}
    (hS : S ∈ Work.WilE5.uniqSets L) : S ∈ L := by
  induction L using uniqSets_induct with
  | nil => simp [Work.WilE5.uniqSets] at hS
  | cons S0 rest ih =>
    rw [Work.WilE5.uniqSets.eq_def, List.mem_cons] at hS
    rcases hS with rfl | hS
    · exact List.mem_cons.mpr (Or.inl rfl)
    · exact List.mem_cons.mpr (Or.inr (List.mem_filter.mp (ih hS)).1)

/-- Every set met by `L` is met by `uniqSets L`. -/
theorem exists_mem_uniqSets {p q : ℕ} {L : List (Stratum p q)} {S : Stratum p q}
    (hS : S ∈ L) : ∃ T ∈ Work.WilE5.uniqSets L, T.X.set = S.X.set := by
  induction L using uniqSets_induct with
  | nil => simp at hS
  | cons S0 rest ih =>
    rw [List.mem_cons] at hS
    rcases hS with heq | hS
    · refine ⟨S0, ?_, ?_⟩
      · rw [Work.WilE5.uniqSets.eq_def]
        exact List.mem_cons.mpr (Or.inl rfl)
      · rw [heq]
    · by_cases hset : S.X.set = S0.X.set
      · exact ⟨S0, by rw [Work.WilE5.uniqSets.eq_def]; exact List.mem_cons.mpr (Or.inl rfl),
          hset.symm⟩
      · have hmem : S ∈ rest.filter fun T => T.X.set ≠ S0.X.set := by
          rw [List.mem_filter]
          exact ⟨hS, by simpa using hset⟩
        obtain ⟨T, hT, hTset⟩ := ih hmem
        exact ⟨T, by
          rw [Work.WilE5.uniqSets.eq_def]
          exact List.mem_cons.mpr (Or.inr hT), hTset⟩

/-- `uniqSets L` is pairwise disjoint, provided any two entries of `L` with intersecting
underlying sets have equal underlying sets. -/
theorem pairwise_uniqSets {p q : ℕ} {L : List (Stratum p q)}
    (h : ∀ S ∈ L, ∀ T ∈ L, (S.X.set ∩ T.X.set).Nonempty → S.X.set = T.X.set) :
    (Work.WilE5.uniqSets L).Pairwise (fun S T => Disjoint S.X.set T.X.set) := by
  induction L using uniqSets_induct with
  | nil => simp [Work.WilE5.uniqSets]
  | cons S0 rest ih =>
    rw [Work.WilE5.uniqSets.eq_def, List.pairwise_cons]
    refine ⟨?_, ?_⟩
    · intro U hU
      have hUf : U ∈ List.filter (fun T : Stratum p q => decide (T.X.set ≠ S0.X.set)) rest :=
        mem_uniqSets hU
      have hUrest : U ∈ rest := (List.mem_filter.mp hUf).1
      have hUne : U.X.set ≠ S0.X.set := by
        have h2 := (List.mem_filter.mp hUf).2
        simpa using h2
      rw [Set.disjoint_left]
      intro x hx hx'
      exact hUne (h S0 (List.mem_cons.mpr (Or.inl rfl)) U
        (List.mem_cons.mpr (Or.inr hUrest)) ⟨x, hx, hx'⟩).symm
    · refine ih ?_
      intro S hS T hT hne
      exact h S (List.mem_cons.mpr (Or.inr (List.mem_filter.mp hS).1))
        T (List.mem_cons.mpr (Or.inr (List.mem_filter.mp hT).1)) hne

/-- `uniqSets L` is no longer than `L`. -/
theorem uniqSets_length_le {p q : ℕ} (L : List (Stratum p q)) :
    (Work.WilE5.uniqSets L).length ≤ L.length := by
  induction L using uniqSets_induct with
  | nil => simp [Work.WilE5.uniqSets]
  | cons S0 rest ih =>
    rw [Work.WilE5.uniqSets.eq_def]
    simp only [List.length_cons]
    have h1 : (List.filter (fun T : Stratum p q => decide (T.X.set ≠ S0.X.set)) rest).length ≤
        rest.length := List.length_filter_le _ _
    omega

theorem filterProps {p q : ℕ} (L : List (WilkiesDesign.E.Stratum p q))
    (h : ∀ S ∈ L, ∀ T ∈ L, (S.X.set ∩ T.X.set).Nonempty → S.X.set = T.X.set) :
    (Work.WilE5.uniqSets L).length ≤ L.length ∧
    (⋃ S ∈ Work.WilE5.uniqSets L, S.X.set) = (⋃ S ∈ L, S.X.set) ∧
    (Work.WilE5.uniqSets L).Pairwise (fun S T => Disjoint S.X.set T.X.set) := by
  refine ⟨uniqSets_length_le L, ?_, pairwise_uniqSets h⟩
  ext x
  simp only [Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨S, hSL, hxS⟩
    exact ⟨S, mem_uniqSets hSL, hxS⟩
  · rintro ⟨S, hSL, hxS⟩
    obtain ⟨T, hT, hTset⟩ := exists_mem_uniqSets hSL
    refine ⟨T, hT, ?_⟩
    rw [hTset]
    exact hxS

end Work.WilE5.Pairwise
