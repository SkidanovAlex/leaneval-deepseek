import Mathlib
import Submission.Work.Resample.buQWscalDefs

namespace Work.Resample

open HvdH

/-- Membership in a `zipWith` peels one factor from each argument. -/
lemma mem_zipWith_exists {α β γ : Type*} {f : α → β → γ} {l₁ : List α} {l₂ : List β} {x : γ}
    (h : x ∈ List.zipWith f l₁ l₂) : ∃ a ∈ l₁, ∃ b ∈ l₂, f a b = x := by
  induction l₁ generalizing l₂ with
  | nil => simp at h
  | cons a as ih =>
    cases l₂ with
    | nil => simp at h
    | cons b bs =>
      rw [List.zipWith_cons_cons, List.mem_cons] at h
      rcases h with h | h
      · exact ⟨a, List.mem_cons_self, b, List.mem_cons_self, h.symm⟩
      · obtain ⟨a', ha', b', hb', he⟩ := ih h
        exact ⟨a', List.mem_cons.mpr (Or.inr ha'), b', List.mem_cons.mpr (Or.inr hb'), he⟩

/-- Every entry of the key list `buScKeys s t` is `Val.int` of a natural number. -/
lemma buScKeys_mem {s t : ℕ} {a : Val} (ha : a ∈ buScKeys s t) :
    ∃ k : ℕ, a = Val.int (k : ℤ) := by
  rw [buScKeys, List.mem_map] at ha
  obtain ⟨z, hz, rfl⟩ := ha
  rw [List.mem_ofFn] at hz
  obtain ⟨i, rfl⟩ := hz
  exact ⟨egKeyS s t (i : ℕ), rfl⟩

/-- The key list of the scaling stage is injective (`egKeyS_inj`), so its entries are distinct and
cover `{0,…,s-1}` (`egKeyS_surj`); the records all have the shape `cons (int k) v`. -/
theorem buScKeysFacts (s t : ℕ) (hs : 2 ≤ s) (hcop : Nat.Coprime s t) (d : List (ℤ × ℤ)) :
    (List.ofFn (fun i : Fin s => ((egKeyS s t (i : ℕ) : ℕ) : ℤ))).Nodup ∧
    (∀ ℓ < s, ∃ i < s, egKeyS s t i = ℓ) ∧
    (∀ x ∈ buScRecs s t d, ∃ (k : ℕ) (v : Val), x = Val.cons (Val.int (k : ℤ)) v) := by
  have hs0 : 0 < s := by omega
  have hcs : Nat.Coprime t s := hcop.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [List.nodup_ofFn]
    intro i j hij
    have hij' : egKeyS s t (i : ℕ) = egKeyS s t (j : ℕ) := Int.ofNat.inj hij
    exact Fin.ext (egKeyS_inj s t hs0 hcs i.isLt j.isLt hij')
  · intro ℓ hℓ
    obtain ⟨i, hi⟩ := egKeyS_surj s t hs0 hcs ⟨ℓ, hℓ⟩
    exact ⟨i, i.isLt, hi⟩
  · intro x hx
    rw [buScRecs] at hx
    obtain ⟨a, ha, b, hb, he⟩ := mem_zipWith_exists hx
    obtain ⟨k, rfl⟩ := buScKeys_mem ha
    exact ⟨k, b, he.symm⟩

end Work.Resample
