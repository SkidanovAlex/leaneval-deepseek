import Mathlib.Data.Finsupp.Lex
import Mathlib.Data.Sum.Order

namespace Commons.Data.Finsupp

section Helpers

variable {σ τ : Type*}

/-- The `inr`-part of a finitely supported function on a sum, evaluated at an `inl` index. -/
lemma lexSumMapDomain_inr_apply_inl (f : τ →₀ ℕ) (s : σ) :
    (Finsupp.mapDomain (Sum.inrₗ : τ → σ ⊕ₗ τ) f) (Sum.inlₗ s) = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  simp [Set.mem_range, Sum.inlₗ, Sum.inrₗ]

/-- The `inl`-part of a finitely supported function on a sum, evaluated at an `inr` index. -/
lemma lexSumMapDomain_inl_apply_inr (e : σ →₀ ℕ) (t : τ) :
    (Finsupp.mapDomain (Sum.inlₗ : σ → σ ⊕ₗ τ) e) (Sum.inrₗ t) = 0 := by
  apply Finsupp.mapDomain_of_notMem_range
  simp [Set.mem_range, Sum.inlₗ, Sum.inrₗ]

/-- `mapDomain inl e + mapDomain inr f` evaluated at an `inl` index is `e`. -/
lemma lexSumMapDomain_add_inl_apply (e : σ →₀ ℕ) (f : τ →₀ ℕ) (s : σ) :
    (Finsupp.mapDomain (Sum.inlₗ : σ → σ ⊕ₗ τ) e +
      Finsupp.mapDomain (Sum.inrₗ : τ → σ ⊕ₗ τ) f) (Sum.inlₗ s) = e s := by
  rw [Finsupp.add_apply, lexSumMapDomain_inr_apply_inl, add_zero]
  exact Finsupp.mapDomain_apply_of_injective Sum.inl_injective e s

/-- `mapDomain inl e + mapDomain inr f` evaluated at an `inr` index is `f`. -/
lemma lexSumMapDomain_add_inr_apply (e : σ →₀ ℕ) (f : τ →₀ ℕ) (t : τ) :
    (Finsupp.mapDomain (Sum.inlₗ : σ → σ ⊕ₗ τ) e +
      Finsupp.mapDomain (Sum.inrₗ : τ → σ ⊕ₗ τ) f) (Sum.inrₗ t) = f t := by
  rw [Finsupp.add_apply, lexSumMapDomain_inl_apply_inr, zero_add]
  exact Finsupp.mapDomain_apply_of_injective Sum.inr_injective f t

end Helpers

theorem lex_mapDomain_lexSum_lt_iff {σ τ : Type*} [DecidableEq σ] [LinearOrder σ]
    [DecidableEq τ] [LinearOrder τ] (e e₁ : σ →₀ ℕ) (f f₁ : τ →₀ ℕ) :
    toLex (Finsupp.mapDomain Sum.inlₗ e + Finsupp.mapDomain Sum.inrₗ f) <
      toLex (Finsupp.mapDomain Sum.inlₗ e₁ + Finsupp.mapDomain Sum.inrₗ f₁) ↔
      toLex e < toLex e₁ ∨ (e = e₁ ∧ toLex f < toLex f₁) := by
  constructor
  · intro h
    rw [Finsupp.Lex.lt_iff] at h
    obtain ⟨i, hagree, hlt⟩ := h
    obtain ⟨a, rfl⟩ : ∃ a : σ ⊕ τ, toLex a = i := ⟨ofLex i, toLex_ofLex i⟩
    rcases a with s | t
    · left
      rw [Finsupp.Lex.lt_iff]
      refine ⟨s, ?_, ?_⟩
      · intro s' hs'
        have hlt' : (Sum.inlₗ s' : σ ⊕ₗ τ) < Sum.inlₗ s :=
          (Sum.Lex.inl_lt_inl_iff (a := s') (b := s)).2 hs'
        have h1 := hagree (Sum.inlₗ s') hlt'
        simp only [ofLex_toLex, lexSumMapDomain_add_inl_apply] at h1
        exact h1
      · have h1 := hlt
        simp only [ofLex_toLex, lexSumMapDomain_add_inl_apply] at h1
        exact h1
    · right
      refine ⟨?_, ?_⟩
      · ext s
        have hlt' : (Sum.inlₗ s : σ ⊕ₗ τ) < Sum.inrₗ t := Sum.Lex.inl_lt_inr s t
        have h1 := hagree (Sum.inlₗ s) hlt'
        simp only [ofLex_toLex, lexSumMapDomain_add_inl_apply] at h1
        exact h1
      · rw [Finsupp.Lex.lt_iff]
        refine ⟨t, ?_, ?_⟩
        · intro t' ht'
          have hlt' : (Sum.inrₗ t' : σ ⊕ₗ τ) < Sum.inrₗ t :=
            (Sum.Lex.inr_lt_inr_iff (a := t') (b := t)).2 ht'
          have h1 := hagree (Sum.inrₗ t') hlt'
          simp only [ofLex_toLex, lexSumMapDomain_add_inr_apply] at h1
          exact h1
        · have h1 := hlt
          simp only [ofLex_toLex, lexSumMapDomain_add_inr_apply] at h1
          exact h1
  · intro h
    rcases h with h | ⟨heq, hf⟩
    · rw [Finsupp.Lex.lt_iff] at h
      obtain ⟨s, hs, hlt⟩ := h
      rw [Finsupp.Lex.lt_iff]
      refine ⟨Sum.inlₗ s, ?_, ?_⟩
      · intro j hj
        obtain ⟨b, rfl⟩ : ∃ b : σ ⊕ τ, toLex b = j := ⟨ofLex j, toLex_ofLex j⟩
        rcases b with s' | t
        · have hy : s' < s := Sum.Lex.inl_lt_inl_iff.mp hj
          simp only [ofLex_toLex, lexSumMapDomain_add_inl_apply]
          simpa only [ofLex_toLex] using hs s' hy
        · exact absurd hj Sum.Lex.not_inr_lt_inl
      · simp only [ofLex_toLex, lexSumMapDomain_add_inl_apply]
        exact hlt
    · rw [Finsupp.Lex.lt_iff] at hf
      obtain ⟨t, ht, hlt⟩ := hf
      rw [Finsupp.Lex.lt_iff]
      refine ⟨Sum.inrₗ t, ?_, ?_⟩
      · intro j hj
        obtain ⟨b, rfl⟩ : ∃ b : σ ⊕ τ, toLex b = j := ⟨ofLex j, toLex_ofLex j⟩
        rcases b with s | t'
        · simp only [ofLex_toLex, lexSumMapDomain_add_inl_apply, heq]
        · have hy : t' < t := Sum.Lex.inr_lt_inr_iff.mp hj
          simp only [ofLex_toLex, lexSumMapDomain_add_inr_apply]
          simpa only [ofLex_toLex] using ht t' hy
      · simp only [ofLex_toLex, lexSumMapDomain_add_inr_apply]
        exact hlt

end Commons.Data.Finsupp