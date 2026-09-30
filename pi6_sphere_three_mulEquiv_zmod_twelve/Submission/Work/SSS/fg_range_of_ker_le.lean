import Mathlib

namespace Work.SSS

/-- **Lifting generators through a linear map.**  If the range of `f` is finitely generated,
then `ker f` together with finitely many explicit elements of the source spans everything:
there is a finite `T` with `ker f ⊔ span T = ⊤`.  Equivalently, `M ⧸ ker f` is finitely
generated whenever `f.range` is. -/
lemma exists_finset_sup_ker_eq_top {R M P : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] P) (h : f.range.FG) :
    ∃ T : Finset M, f.ker ⊔ Submodule.span R (T : Set M) = ⊤ := by
  classical
  obtain ⟨S, hS⟩ := h
  -- `hS : Submodule.span R ↑S = f.range`
  have hpre : ∀ y ∈ S, ∃ x : M, f x = y := by
    intro y hy
    have : y ∈ f.range := by
      rw [← hS]
      exact Submodule.subset_span hy
    exact LinearMap.mem_range.mp this
  have hge : ∃ g : P → M, ∀ y ∈ S, f (g y) = y := by
    choose g0 hg0 using hpre
    refine ⟨fun y => if hy : y ∈ S then g0 y hy else 0, ?_⟩
    intro y hy
    simpa only [dif_pos hy] using hg0 y hy
  obtain ⟨g, hg⟩ := hge
  refine ⟨S.image g, ?_⟩
  have himg : (f '' ((S.image g : Finset M) : Set M)) = (S : Set P) := by
    rw [Finset.coe_image, Set.image_image]
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [hg y hy] using hy
    · intro hz
      exact ⟨z, hz, hg z hz⟩
  rw [eq_top_iff]
  intro x _
  have hxmem : f x ∈ Submodule.map f
      (Submodule.span R ((S.image g : Finset M) : Set M)) := by
    rw [Submodule.map_span, himg, hS]
    exact LinearMap.mem_range_self f x
  obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hxmem
  rw [Submodule.mem_sup]
  refine ⟨x - y, ?_, y, hy, sub_add_cancel x y⟩
  rw [LinearMap.mem_ker, map_sub, hyx, sub_self]

/-- Serre-style finiteness for a "three-for-two" situation: if `φ.ker ⊆ M + ker γ`, and both
`φ.range` and `γ(M)` are finitely generated, then so is `γ.range`.  (Over a Noetherian base
this is the standard extension-of-finitely-generated-modules argument applied to the exact
sequence `0 → A/(M + ker γ) → γ.range/γ(M) → 0`.) -/
theorem fg_range_of_ker_le {A X E : Type*} [AddCommGroup A] [Module ℤ A]
    [AddCommGroup X] [Module ℤ X] [AddCommGroup E] [Module ℤ E]
    (γ : A →ₗ[ℤ] X) (φ : A →ₗ[ℤ] E) (M : Submodule ℤ A) (h : φ.ker ≤ M ⊔ γ.ker)
    (hφ : (φ.range).FG) (hM : (Submodule.map γ M).FG) : (γ.range).FG := by
  obtain ⟨T, hT⟩ := exists_finset_sup_ker_eq_top φ hφ
  -- `hT : φ.ker ⊔ span ℤ ↑T = ⊤`
  have hkerbot : Submodule.map γ γ.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
    rw [LinearMap.mem_ker] at hy
    rw [← hyx, hy]
  have htop : M ⊔ γ.ker ⊔ Submodule.span ℤ (T : Set A) = ⊤ := by
    apply le_antisymm le_top
    rw [← hT]
    exact sup_le (le_trans h le_sup_left) le_sup_right
  rw [LinearMap.range_eq_map, ← htop]
  rw [Submodule.map_sup, Submodule.map_sup, hkerbot, sup_bot_eq]
  exact hM.sup ((Submodule.fg_span T.finite_toSet).map γ)

end Work.SSS
