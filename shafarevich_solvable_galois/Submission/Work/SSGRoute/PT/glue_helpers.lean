import Mathlib.GroupTheory.GroupAction.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Helpers for `glue_realiser_abstract`

A transversal of the orbits of a group action containing a prescribed set of pairwise
non-equivalent elements.  This is the construction of
`Work.SSGRoute.E7cOmega.exists_transversal_mem_of_mulAction` (the single-point case) generalised
to a prescribed set; it is used with the action of `Gal(Ω/k)` on the finite places of `Ω` (where
the orbit relation is `SSGRoute.IsConjPlace`) and with the prescribed set `S₁`.
-/

namespace Work.SSGRoute.PT

open scoped Pointwise

/-- **A transversal of the orbits of a group action containing a prescribed set.**

If `S` is a set of pairwise non-equivalent elements of `α` (no two distinct elements of `S` lie in
the same orbit), then there is a set `R ⊇ S` meeting every orbit in exactly one point. -/
theorem exists_transversal_containing_set {G α : Type} [Group G] [MulAction G α]
    (S : Set α) (hS : ∀ a ∈ S, ∀ b ∈ S, (∃ σ : G, σ • a = b) → a = b) :
    ∃ R : Set α, S ⊆ R ∧ (∀ w : α, ∃! w' : R, ∃ σ : G, σ • w = w'.1) := by
  classical
  -- two elements of `S` in the orbit of the same point are equal
  have hSuniq : ∀ w : α, ∀ a b : α, a ∈ S → b ∈ S →
      (∃ σ : G, σ • w = a) → (∃ σ : G, σ • w = b) → a = b := by
    intro w a b ha hb ⟨σ, hσ⟩ ⟨τ, hτ⟩
    have h1 : (τ * σ⁻¹) • a = b := calc
      (τ * σ⁻¹) • a = (τ * σ⁻¹) • (σ • w) := by rw [hσ]
      _ = ((τ * σ⁻¹) * σ) • w := (mul_smul _ _ _).symm
      _ = (τ * (σ⁻¹ * σ)) • w := by rw [mul_assoc]
      _ = (τ * 1) • w := by rw [inv_mul_cancel]
      _ = τ • w := by rw [mul_one]
      _ = b := hτ
    exact hS a ha b hb ⟨τ * σ⁻¹, h1⟩
  -- the normalized section: `S` if the orbit meets `S`, `Quotient.out` otherwise
  let rep : α → α := fun w =>
    if h : ∃ a ∈ S, ∃ σ : G, σ • w = a then h.choose
    else Quotient.out (Quotient.mk (MulAction.orbitRel G α) w)
  have hrep_def : ∀ w : α,
      rep w = if h : ∃ a ∈ S, ∃ σ : G, σ • w = a then h.choose
        else Quotient.out (Quotient.mk (MulAction.orbitRel G α) w) := fun w => rfl
  -- `rep w` always lies in the orbit of `w`
  have hrep_orbit : ∀ w : α, ∃ σ : G, σ • w = rep w := by
    intro w
    by_cases h : ∃ a ∈ S, ∃ σ : G, σ • w = a
    · rw [hrep_def, dif_pos h]
      exact h.choose_spec.2
    · rw [hrep_def, dif_neg h]
      have hrel : (Quotient.out (Quotient.mk (MulAction.orbitRel G α) w)) ∈
          MulAction.orbit G w :=
        MulAction.orbitRel_apply.mp
          (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel G α) w)))
      exact MulAction.mem_orbit_iff.mp hrel
  -- `rep` is constant on orbits
  have hrep_const : ∀ z w : α, (∃ σ : G, σ • w = rep z) → rep z = rep w := by
    intro z w hzw
    by_cases hz : ∃ a ∈ S, ∃ σ : G, σ • z = a
    · have hz' : rep z = hz.choose := by rw [hrep_def, dif_pos hz]
      have hw : ∃ a ∈ S, ∃ σ : G, σ • w = a := ⟨rep z, hz' ▸ hz.choose_spec.1, hzw⟩
      have hw' : rep w = hw.choose := by rw [hrep_def, dif_pos hw]
      rw [hz', hw']
      exact hSuniq w hz.choose hw.choose hz.choose_spec.1 hw.choose_spec.1 (hz' ▸ hzw)
        hw.choose_spec.2
    · -- the orbit of `w` also avoids `S`, since it is the orbit of `z`
      have hw : ¬ ∃ a ∈ S, ∃ σ : G, σ • w = a := by
        rintro ⟨a, ha, τ, hτ⟩
        obtain ⟨ρ, hρ⟩ := hzw
        obtain ⟨σ₀, hσ₀⟩ := hrep_orbit z
        refine hz ⟨a, ha, τ * ρ⁻¹ * σ₀, ?_⟩
        calc (τ * ρ⁻¹ * σ₀) • z = (τ * ρ⁻¹) • (σ₀ • z) := mul_smul _ _ _
          _ = (τ * ρ⁻¹) • rep z := by rw [hσ₀]
          _ = ((τ * ρ⁻¹) * ρ) • w := by rw [← hρ]; exact (mul_smul _ _ _).symm
          _ = (τ * (ρ⁻¹ * ρ)) • w := by rw [mul_assoc]
          _ = (τ * 1) • w := by rw [inv_mul_cancel]
          _ = τ • w := by rw [mul_one]
          _ = a := hτ
      have hz'' : rep z = Quotient.out (Quotient.mk (MulAction.orbitRel G α) z) := by
        rw [hrep_def, dif_neg hz]
      have hw'' : rep w = Quotient.out (Quotient.mk (MulAction.orbitRel G α) w) := by
        rw [hrep_def, dif_neg hw]
      have hmk : Quotient.mk (MulAction.orbitRel G α) z
          = Quotient.mk (MulAction.orbitRel G α) w := by
        refine Quotient.sound (MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ?_))
        obtain ⟨ρ, hρ⟩ := hzw
        obtain ⟨σ₀, hσ₀⟩ := hrep_orbit z
        refine ⟨σ₀⁻¹ * ρ, ?_⟩
        calc (σ₀⁻¹ * ρ) • w = σ₀⁻¹ • (ρ • w) := mul_smul _ _ _
          _ = σ₀⁻¹ • rep z := by rw [hρ]
          _ = σ₀⁻¹ • (σ₀ • z) := by rw [hσ₀]
          _ = z := inv_smul_smul σ₀ z
      rw [hz'', hw'', hmk]
  refine ⟨Set.range rep, ?_, ?_⟩
  · intro a ha
    refine ⟨a, ?_⟩
    have h : ∃ b ∈ S, ∃ σ : G, σ • a = b := ⟨a, ha, 1, one_smul G a⟩
    have h1 : rep a = h.choose := by rw [hrep_def, dif_pos h]
    rw [h1]
    exact hSuniq a h.choose a h.choose_spec.1 ha h.choose_spec.2 ⟨1, one_smul G a⟩
  · intro w
    refine ⟨⟨rep w, w, rfl⟩, hrep_orbit w, ?_⟩
    intro y hy
    obtain ⟨z, hz⟩ := y.2
    refine Subtype.ext ?_
    rw [← hz]
    exact hrep_const z w (hz ▸ hy)

end Work.SSGRoute.PT
