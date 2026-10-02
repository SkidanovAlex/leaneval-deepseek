import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

namespace Work.Algebra

/-- Linear-algebra core of `span_pair_one_tmul`: in a finite dimensional `ℚ`-vector space of
dimension at most `2`, any spanning set contains two elements that already span. -/
private theorem exists_pair_mem_span_eq_top {V : Type*} [AddCommGroup V] [Module ℚ V]
    [Module.Finite ℚ V] {s : Set V} (hs : Submodule.span ℚ s = ⊤) (hsne : s.Nonempty)
    (h2 : Module.finrank ℚ V ≤ 2) :
    ∃ x1 ∈ s, ∃ x2 ∈ s, Submodule.span ℚ ({x1, x2} : Set V) = ⊤ := by
  by_cases hV : Subsingleton V
  · haveI := hV
    obtain ⟨x, hx⟩ := hsne
    exact ⟨x, hx, x, hx, Subsingleton.elim _ _⟩
  · haveI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
    by_contra hc
    push_neg at hc
    have h1 : ∃ x1 ∈ s, x1 ≠ 0 := by
      by_contra hc1
      push_neg at hc1
      have hle : (⊤ : Submodule ℚ V) ≤ ⊥ := by
        rw [← hs]
        exact Submodule.span_le.mpr fun x hx => by
          rw [hc1 x hx]; exact Submodule.zero_mem ⊥
      have htopbot : (⊤ : Submodule ℚ V) = ⊥ := le_bot_iff.mp hle
      have hsub : Subsingleton V := ⟨fun x y => by
        have hx : x = 0 := by
          simpa using (show x ∈ (⊥ : Submodule ℚ V) from htopbot ▸ Submodule.mem_top)
        have hy : y = 0 := by
          simpa using (show y ∈ (⊥ : Submodule ℚ V) from htopbot ▸ Submodule.mem_top)
        rw [hx, hy]⟩
      exact hV hsub
    obtain ⟨x1, hx1s, hx1ne⟩ := h1
    have hN1 : Submodule.span ℚ ({x1} : Set V) ≠ ⊤ := by
      have hh := hc x1 hx1s x1 hx1s
      rwa [show ({x1, x1} : Set V) = {x1} by ext y; simp] at hh
    have h2ex : ∃ x2 ∈ s, x2 ∉ Submodule.span ℚ ({x1} : Set V) := by
      by_contra hc2
      push_neg at hc2
      have hle : (⊤ : Submodule ℚ V) ≤ Submodule.span ℚ ({x1} : Set V) := by
        rw [← hs]
        exact Submodule.span_le.mpr hc2
      exact hN1 (top_le_iff.mp hle)
    obtain ⟨x2, hx2s, hx2notin⟩ := h2ex
    have hN2 : Submodule.span ℚ ({x1, x2} : Set V) ≠ ⊤ := hc x1 hx1s x2 hx2s
    have h3ex : ∃ x3 ∈ s, x3 ∉ Submodule.span ℚ ({x1, x2} : Set V) := by
      by_contra hc3
      push_neg at hc3
      have hle : (⊤ : Submodule ℚ V) ≤ Submodule.span ℚ ({x1, x2} : Set V) := by
        rw [← hs]
        exact Submodule.span_le.mpr hc3
      exact hN2 (top_le_iff.mp hle)
    obtain ⟨x3, hx3s, hx3notin⟩ := h3ex
    have hlt1 : (⊥ : Submodule ℚ V) < Submodule.span ℚ ({x1} : Set V) :=
      bot_lt_iff_ne_bot.mpr ((Submodule.ne_bot_iff _).mpr
        ⟨x1, Submodule.subset_span (by simp), hx1ne⟩)
    have hlt2 : Submodule.span ℚ ({x1} : Set V) < Submodule.span ℚ ({x1, x2} : Set V) := by
      refine lt_of_le_of_ne (Submodule.span_mono ?_) ?_
      · rintro y (rfl : y = x1); simp
      · intro heq
        exact hx2notin (heq ▸ Submodule.subset_span (by simp))
    have hlt3 : Submodule.span ℚ ({x1, x2} : Set V) <
        Submodule.span ℚ ({x1, x2, x3} : Set V) := by
      refine lt_of_le_of_ne (Submodule.span_mono ?_) ?_
      · rintro y (rfl | rfl) <;> simp
      · intro heq
        exact hx3notin (heq ▸ Submodule.subset_span (by simp))
    have e1 := Submodule.finrank_lt_finrank_of_lt hlt1
    have e2 := Submodule.finrank_lt_finrank_of_lt hlt2
    have e3 := Submodule.finrank_lt_finrank_of_lt hlt3
    have e4 : Module.finrank ℚ ↥(Submodule.span ℚ ({x1, x2, x3} : Set V)) ≤
        Module.finrank ℚ V := Submodule.finrank_le _
    omega

theorem span_pair_one_tmul (A : Type) [AddCommGroup A] (hfin : Module.Finite ℤ A) (h : Module.finrank ℚ (TensorProduct ℤ ℚ A) ≤ 2) : ∃ a1 a2 : A, Submodule.span ℚ ({(TensorProduct.tmul ℤ (1 : ℚ) a1), (TensorProduct.tmul ℤ (1 : ℚ) a2)} : Set (TensorProduct ℤ ℚ A)) = ⊤ := by
  -- `ℚ ⊗[ℤ] A` is spanned over `ℚ` by the elements `1 ⊗ a`, `a : A`.
  have hspan : Submodule.span ℚ (Set.range (fun a : A => (1 : ℚ) ⊗ₜ[ℤ] a)) = ⊤ := by
    have h1 : Submodule.span ℚ ((↑(Submodule.map (TensorProduct.mk ℤ ℚ A (1 : ℚ))
        (⊤ : Submodule ℤ A))) : Set (TensorProduct ℤ ℚ A)) = ⊤ := by
      rw [← Submodule.baseChange_eq_span ℚ (⊤ : Submodule ℤ A), Submodule.baseChange_top]
    convert h1 using 2
    ext y
    simp
  obtain ⟨x1, hx1, x2, hx2, hx⟩ :=
    exists_pair_mem_span_eq_top hspan (Set.range_nonempty _) h
  obtain ⟨a1, ha1⟩ := hx1
  obtain ⟨a2, ha2⟩ := hx2
  refine ⟨a1, a2, ?_⟩
  rw [← ha1, ← ha2] at hx
  exact hx

end Work.Algebra
