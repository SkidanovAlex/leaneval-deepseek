import Mathlib
import Submission.Work.EQ.FanTri.fan_split_defs

namespace Work.EQ.FanTri

open Work.EQ

/-!
# `VisU` is additive over the gap/trip assembly `asm`

The walk of `Work.EQ.stp` on `ℕ` (`true` = principal step, moving `n ↦ n - 1` and stationary at
`0`; `false` = non-principal step, moving `n ↦ n + 1`) is read from state `0` along the letters
of a word, and `VisU u` counts the times `t ∈ [1, |u|]` at which the state is nonzero, while
`asm a σ` assembles the word `true^{a₀} σ₁ true^{a₁} σ₂ …` from gap lengths `a` and trips `σ`.

The main result: for such an assembled word, the count is the sum of the counts of the
individual trips, provided each trip that is followed by a nonempty gap returns to `0`.
-/

/-- Number of `t ∈ [1, |u|]` at which the walk started in state `s` (rather than `0`) is
nonzero. -/
def VisX (s : ℕ) (u : List Bool) : ℕ :=
  ((Finset.Icc 1 u.length).filter (fun t => stAux (u.take t) s ≠ 0)).card

lemma VisU_eq_VisX (u : List Bool) : VisU u = VisX 0 u := rfl

@[simp] lemma VisX_nil (s : ℕ) : VisX s [] = 0 := rfl

lemma wstate_length_eq (u : List Bool) : wstate u u.length = stAux u 0 := by
  rw [wstate, List.take_length]

/-- Peeling off the last letter of a word. -/
lemma VisX_append_singleton (s : ℕ) (u : List Bool) (c : Bool) :
    VisX s (u ++ [c]) = VisX s u + (if stp c (stAux u s) ≠ 0 then 1 else 0) := by
  have hlen : (u ++ [c]).length = u.length + 1 := by simp
  have hIcc : Finset.Icc 1 (u.length + 1) = insert (u.length + 1) (Finset.Icc 1 u.length) := by
    ext t; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  have htake : (u ++ [c]).take (u.length + 1) = u ++ [c] :=
    List.take_of_length_le (by simp)
  have hQ : stAux ((u ++ [c]).take (u.length + 1)) s ≠ 0 ↔ stp c (stAux u s) ≠ 0 := by
    rw [htake, stAux_append]; rfl
  have hfil : (Finset.Icc 1 u.length).filter (fun t => stAux ((u ++ [c]).take t) s ≠ 0)
      = (Finset.Icc 1 u.length).filter (fun t => stAux (u.take t) s ≠ 0) := by
    apply Finset.filter_congr
    intro t ht
    rw [Finset.mem_Icc] at ht
    rw [List.take_append_of_le_length ht.2]
  have hnotmem :
      (u.length + 1) ∉ (Finset.Icc 1 u.length).filter (fun t => stAux (u.take t) s ≠ 0) := by
    intro hmem
    rw [Finset.mem_filter, Finset.mem_Icc] at hmem
    omega
  simp only [VisX, hlen, hIcc, Finset.filter_insert, hfil]
  by_cases h : stp c (stAux u s) ≠ 0
  · rw [if_pos (show stAux ((u ++ [c]).take (u.length + 1)) s ≠ 0 from hQ.mpr h),
      if_pos h, Finset.card_insert_of_notMem hnotmem]
  · rw [if_neg (show ¬ (stAux ((u ++ [c]).take (u.length + 1)) s ≠ 0) from fun hh => h (hQ.mp hh)),
      if_neg h, add_zero]

/-- **Additivity of `VisX`.** -/
lemma VisX_append (s : ℕ) (u v : List Bool) :
    VisX s (u ++ v) = VisX s u + VisX (stAux u s) v := by
  induction v using List.reverseRecOn with
  | nil => simp
  | append_singleton v' c ih =>
      rw [← List.append_assoc, VisX_append_singleton, ih, VisX_append_singleton, stAux_append]
      omega

/-- Additivity of `VisU` itself, for a prefix ending in state `0`. -/
lemma VisU_append_of_state_zero (u v : List Bool) (h : stAux u 0 = 0) :
    VisU (u ++ v) = VisU u + VisU v := by
  rw [VisU_eq_VisX, VisX_append, h]
  rfl

lemma VisX_replicate_true (n : ℕ) : VisX 0 (List.replicate n true) = 0 :=
  VisU_replicate_true n

/-- A gap block of `true`s read from state `0` contributes nothing. -/
lemma VisU_replicate_true_append (n : ℕ) (v : List Bool) :
    VisU (List.replicate n true ++ v) = VisU v := by
  rw [VisU_append_of_state_zero _ _ (by simp [stAux_replicate_true]), VisU_replicate_true,
    zero_add]

/-- Auxiliary form of `VisU_asm`, by induction on the list of trips. -/
theorem VisU_asm_aux : ∀ (σ : List (List Bool)) (a : List ℕ),
    a.length = σ.length + 1 →
    (∀ (i : ℕ) (τ : List Bool), σ[i]? = some τ → i + 1 < σ.length →
        stAux τ 0 = 0) →
    (∀ (τ : List Bool), σ.getLast? = some τ →
        stAux τ 0 = 0 ∨ a.getLast? = some 0) →
    VisU (asm a σ) = (σ.map VisU).sum := by
  intro σ
  induction σ with
  | nil =>
      intro a hlen _ _
      rcases a with _ | ⟨g, gs⟩
      · simp only [List.length_nil] at hlen; omega
      rcases gs with _ | ⟨g0, gs'⟩
      · show VisU (List.replicate g true) = 0
        exact VisU_replicate_true g
      · simp only [List.length_cons, List.length_nil] at hlen; omega
  | cons τ σ' ih =>
      intro a hlen h1 h2
      rcases a with _ | ⟨g, gs⟩
      · simp only [List.length_cons, List.length_nil] at hlen; omega
      have hgs : gs.length = σ'.length + 1 := by
        simp only [List.length_cons] at hlen ⊢; omega
      show VisU (List.replicate g true ++ τ ++ asm gs σ') = VisU τ + (σ'.map VisU).sum
      rw [List.append_assoc, VisU_eq_VisX, VisX_append, VisX_replicate_true]
      rw [stAux_replicate_true, Nat.zero_sub]
      simp only [Nat.zero_add]
      rw [VisX_append, ← VisU_eq_VisX]
      have key : VisX (stAux τ 0) (asm gs σ') = (σ'.map VisU).sum := by
        by_cases hσ' : σ' = []
        · subst hσ'
          have hgs1 : gs.length = 1 := by simpa using hgs
          obtain ⟨g0, rfl⟩ := List.length_eq_one_iff.mp hgs1
          show VisX (stAux τ 0) (List.replicate g0 true) = 0
          by_cases h0 : stAux τ 0 = 0
          · rw [h0]; exact VisX_replicate_true g0
          · rcases h2 τ (by simp) with hl | hl
            · exact absurd hl h0
            · have hz : g0 = 0 := by
                rw [show (g :: [g0]).getLast? = some g0 from rfl] at hl
                simpa using hl
              rw [hz]
              simp
        · have hτ : stAux τ 0 = 0 := by
            refine h1 0 τ (by simp) ?_
            rw [List.length_cons]
            have hp := List.length_pos_iff.mpr hσ'
            omega
          have h1' : ∀ (i : ℕ) (τ' : List Bool), σ'[i]? = some τ' → i + 1 < σ'.length →
              stAux τ' 0 = 0 := by
            intro i τ' hi hlt
            refine h1 (i + 1) τ' (by rwa [List.getElem?_cons_succ]) ?_
            rw [List.length_cons]
            omega
          have h2' : ∀ (τ' : List Bool), σ'.getLast? = some τ' →
              stAux τ' 0 = 0 ∨ gs.getLast? = some 0 := by
            intro τ' hgl
            have hgl' : (τ :: σ').getLast? = some τ' := by
              obtain ⟨τ'', σ'', rfl⟩ := List.exists_cons_of_ne_nil hσ'
              rw [List.getLast?_cons_cons]
              exact hgl
            rcases h2 τ' hgl' with h | h
            · exact Or.inl h
            · have hgsne : gs ≠ [] := by
                intro hc; rw [hc] at hgs; simp only [List.length_nil] at hgs; omega
              obtain ⟨g0, gs', rfl⟩ := List.exists_cons_of_ne_nil hgsne
              rw [List.getLast?_cons_cons] at h
              exact Or.inr h
          rw [hτ, ← VisU_eq_VisX, ih gs hgs h1' h2']
      rw [key]

theorem VisU_asm (a : List ℕ) (σ : List (List Bool))
    (hlen : a.length = σ.length + 1)
    (hclosed : ∀ (i : ℕ) (τ : List Bool), σ[i]? = some τ → i + 1 < σ.length →
        Work.EQ.FanTri.wstate τ τ.length = 0)
    (hlast : ∀ (τ : List Bool), σ.getLast? = some τ →
        Work.EQ.FanTri.wstate τ τ.length = 0 ∨ a.getLast? = some 0) :
    Work.EQ.FanTri.VisU (Work.EQ.FanTri.asm a σ) = (σ.map Work.EQ.FanTri.VisU).sum := by
  refine VisU_asm_aux σ a hlen ?_ ?_
  · intro i τ hi hlt
    have hh := hclosed i τ hi hlt
    rw [wstate_length_eq] at hh
    exact hh
  · intro τ h
    rcases hlast τ h with h | h
    · refine Or.inl ?_
      rwa [wstate_length_eq] at h
    · exact Or.inr h

end Work.EQ.FanTri
