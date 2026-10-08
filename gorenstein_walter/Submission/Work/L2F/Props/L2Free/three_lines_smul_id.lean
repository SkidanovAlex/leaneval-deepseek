import Mathlib

namespace Work.L2F.Props.L2Free

/-- A linear endomorphism of `F²` preserving three lines that are pairwise distinct is a scalar
multiple of the identity. -/
theorem three_lines_smul_id {F : Type*} [Field F]
    (f : (Fin 2 → F) →ₗ[F] (Fin 2 → F)) (u v w : Fin 2 → F)
    (huv : LinearIndependent F ![u, v])
    (huw : ¬ (w ∈ Submodule.span F {u}))
    (hwv : ¬ (w ∈ Submodule.span F {v}))
    (hu : f u ∈ Submodule.span F {u})
    (hv : f v ∈ Submodule.span F {v})
    (hw : f w ∈ Submodule.span F {w}) :
    ∃ c : F, f = c • 1 := by
  -- Write the three eigenvalue relations `f u = a • u`, `f v = b • v`, `f w = c • w`.
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hu
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
  -- Linear independence of the pair `u, v` in the two linear-coordinate form.
  have hpair := LinearIndependent.pair_iff.mp huv
  -- `u` and `v` span `F²`, so `w` is a combination `α • u + β • v`.
  have hrange :
      (Set.range (![u, v] : Fin 2 → Fin 2 → F)) = ({u, v} : Set (Fin 2 → F)) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have hspan : Submodule.span F ({u, v} : Set (Fin 2 → F)) = ⊤ := by
    have h := huv.span_eq_top_of_card_eq_finrank (by simp)
    rwa [hrange] at h
  have hw_mem : w ∈ Submodule.span F ({u, v} : Set (Fin 2 → F)) := by
    rw [hspan]; exact Submodule.mem_top
  obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hw_mem
  -- `w` is not on the line spanned by `u` (resp. `v`), so both coefficients are nonzero:
  -- otherwise `w` would lie in `F ∙ v` (resp. `F ∙ u`).
  have hα : α ≠ 0 := by
    intro h0
    exact hwv (Submodule.mem_span_singleton.mpr ⟨β, by simpa [h0] using hαβ⟩)
  have hβ : β ≠ 0 := by
    intro h0
    exact huw (Submodule.mem_span_singleton.mpr ⟨α, by simpa [h0] using hαβ⟩)
  -- Compute `f w` two ways: via the basis and via the eigenvector relation.
  have e1 : f w = (α * a) • u + (β * b) • v := by
    rw [← hαβ, map_add, map_smul, map_smul, ← ha, ← hb]
    rw [mul_smul, mul_smul]
  have e2 : c • w = (c * α) • u + (c * β) • v := by
    rw [← hαβ, smul_add, smul_smul, smul_smul]
  have h1 : (α * a) • u + (β * b) • v = (c * α) • u + (c * β) • v :=
    e1.symm.trans (hc.symm.trans e2)
  -- Hence `(α a - c α) • u + (β b - c β) • v = 0`, and independence forces both
  -- coefficients to vanish.
  have hlin : (α * a - c * α) • u + (β * b - c * β) • v = 0 := by
    have key : (α * a - c * α) • u + (β * b - c * β) • v
        = ((α * a) • u + (β * b) • v) - ((c * α) • u + (c * β) • v) := by
      rw [sub_smul, sub_smul]
      abel
    rw [key, h1, sub_self]
  obtain ⟨h1', h2'⟩ := hpair (α * a - c * α) (β * b - c * β) hlin
  have hac : α * a = c * α := sub_eq_zero.mp h1'
  have hbc : β * b = c * β := sub_eq_zero.mp h2'
  -- Since `α` and `β` are nonzero, `a = c` and `b = c`.
  have ha_eq : a = c := by
    rw [mul_comm c α] at hac
    exact mul_left_cancel₀ hα hac
  have hb_eq : b = c := by
    rw [mul_comm c β] at hbc
    exact mul_left_cancel₀ hβ hbc
  -- `f` and `a • 1` agree on `u` and `v`, hence on their span, which is everything.
  refine ⟨a, LinearMap.ext_on hspan ?_⟩
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hxu | hxv
  · rw [hxu]
    show f u = a • u
    exact ha.symm
  · rw [hxv]
    show f v = a • v
    rw [← hb, hb_eq, ← ha_eq]

end Work.L2F.Props.L2Free
